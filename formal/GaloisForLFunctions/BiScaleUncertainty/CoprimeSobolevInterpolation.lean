import GaloisForLFunctions.BiScaleUncertainty.SobolevTraceEnergy
import GaloisForLFunctions.BiScaleUncertainty.CoprimeShearAndMultiplicativeGraphUncertainty

/-!
# Constructed Sobolev interpolation of coprime divisor traces

Finite prescribed slopes define an actual L2 step velocity. Its primitive
interpolates all prescribed nodal differences and has exactly the discrete
Dirichlet energy. Masking traces to positive multiples of a divisor at least two
gives a nonvacuous continuum realization of coprime successor coercivity.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators NNReal Topology

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

def cellStep (s : ℕ → ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  (Ioc (j : ℝ) (j+1)).indicator (fun _ => s j) t

def finiteStep (s : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range N, cellStep s j t

theorem memLp_cellStep (s : ℕ → ℝ) (j : ℕ) : MemLp (cellStep s j) 2 volume := by
  exact memLp_indicator_const 2 measurableSet_Ioc (s j)
    (Or.inr (measure_Ioc_lt_top.ne))

theorem memLp_finiteStep (s : ℕ → ℝ) (N : ℕ) : MemLp (finiteStep s N) 2 volume :=
  memLp_finsetSum (Finset.range N) (fun j _ => memLp_cellStep s j)

def stepVelocity (s : ℕ → ℝ) (N : ℕ) : Velocity :=
  (memLp_finiteStep s N).toLp (finiteStep s N)

theorem ae_stepVelocity (s : ℕ → ℝ) (N : ℕ) :
    (fun t => stepVelocity s N t) =ᵐ[volume] finiteStep s N :=
  (memLp_finiteStep s N).coeFn_toLp

private theorem unit_cells_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (Ioc (i : ℝ) (i+1)) (Ioc (j : ℝ) (j+1)) := by
  rw [Set.disjoint_left]
  intro t hi hj
  rcases lt_or_gt_of_ne hij with h | h
  · have hh : (i : ℝ)+1 ≤ j := by exact_mod_cast Nat.succ_le_of_lt h
    linarith [hi.2, hj.1]
  · have hh : (j : ℝ)+1 ≤ i := by exact_mod_cast Nat.succ_le_of_lt h
    linarith [hj.2, hi.1]

theorem finiteStep_on_cell (s : ℕ → ℝ) (N j : ℕ) (hj : j < N)
    {t : ℝ} (ht : t ∈ Ioc (j : ℝ) (j+1)) : finiteStep s N t = s j := by
  unfold finiteStep
  rw [Finset.sum_eq_single j]
  · exact Set.indicator_of_mem ht _
  · intro i _ hij
    exact Set.indicator_of_notMem
      (fun hi => (Set.disjoint_left.mp (unit_cells_disjoint hij)) hi ht) _
  · intro h
    exact (h (Finset.mem_range.mpr hj)).elim

theorem cell_increment_stepVelocity (s : ℕ → ℝ) (N : ℕ) (j : Fin N) :
    primitive (stepVelocity s N) (j+1) - primitive (stepVelocity s N) j = s j := by
  rw [primitive_sub]
  calc
    _ = ∫ _t in (j : ℝ)..(j+1), s j := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_stepVelocity s N] with t ht
      intro hj
      rw [ht]
      apply finiteStep_on_cell s N j j.isLt
      simpa only [uIoc_of_le (by linarith : (j : ℝ) ≤ j+1)] using hj
    _ = _ := by simp

theorem cell_energy_stepVelocity (s : ℕ → ℝ) (N : ℕ) (j : Fin N) :
    energy (stepVelocity s N) j (j+1) = (s j)^2 := by
  unfold energy
  calc
    _ = ∫ _t in (j : ℝ)..(j+1), (s j)^2 := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_stepVelocity s N] with t ht
      intro hj
      rw [ht, finiteStep_on_cell s N j j.isLt
        (by simpa only [uIoc_of_le (by linarith : (j : ℝ) ≤ j+1)] using hj)]
    _ = _ := by simp

/-- Exact energy of the constructed finite step extension. -/
theorem energy_stepVelocity (s : ℕ → ℝ) (N : ℕ) :
    energy (stepVelocity s N) 0 N = ∑ j ∈ Finset.range N, (s j)^2 := by
  have he := sum_cell_energy (stepVelocity s N) 0 1 N
  simp only [zero_add, one_mul] at he
  rw [← he]
  apply Finset.sum_congr rfl
  intro j hj
  exact cell_energy_stepVelocity s N ⟨j, Finset.mem_range.mp hj⟩

private theorem primitive_stepVelocity_nat (s : ℕ → ℝ) (N m : ℕ) (hm : m ≤ N) :
    primitive (stepVelocity s N) m = ∑ j ∈ Finset.range m, s j := by
  induction m with
  | zero => simp [primitive]
  | succ m ih =>
    have hd := cell_increment_stepVelocity s N ⟨m, by omega⟩
    have hi := ih (by omega)
    rw [Finset.sum_range_succ]
    push_cast
    linarith

theorem primitive_stepVelocity_trace (v : ℕ → ℝ) (N : ℕ) (m : Fin (N+1)) :
    v 0 + primitive (stepVelocity (addDiff v) N) m = v m := by
  rw [primitive_stepVelocity_nat (addDiff v) N m (by omega)]
  have h := telescope_addDiff v 0 m
  simp only [zero_add] at h
  linarith

/-- Interior traces on multiples of `d+2`; the endpoints and forbidden nodes are zero. -/
def divisorTrace (v : ℕ → ℝ) (d N j : ℕ) : ℝ :=
  if 0 < j ∧ j < N ∧ d+2 ∣ j then v j else 0

theorem divisorTrace_zero (v : ℕ → ℝ) (d N : ℕ) : divisorTrace v d N 0 = 0 := by
  simp [divisorTrace]

theorem divisorTrace_end (v : ℕ → ℝ) (d N : ℕ) : divisorTrace v d N N = 0 := by
  simp [divisorTrace]

theorem divisorTrace_one (v : ℕ → ℝ) (d N : ℕ) : divisorTrace v d N 1 = 0 := by
  have h := not_dvd_succ_of_dvd (by omega : 2 ≤ d+2) (dvd_zero (d+2))
  simp only [zero_add] at h
  simp [divisorTrace, h]

theorem divisorTrace_mul_succ (v : ℕ → ℝ) (d N j : ℕ) :
    divisorTrace v d N j * divisorTrace v d N (j+1) = 0 := by
  by_cases hj : d+2 ∣ j
  · have hn := not_dvd_succ_of_dvd (by omega : 2 ≤ d+2) hj
    simp [divisorTrace, hn]
  · simp [divisorTrace, hj]

theorem divisorTrace_discrete_energy (v : ℕ → ℝ) (d N : ℕ) :
    (∑ j ∈ Finset.range N, (addDiff (divisorTrace v d N) j)^2) =
      2 * ∑ j ∈ Finset.range N, (divisorTrace v d N j)^2 := by
  have he (j : ℕ) : (addDiff (divisorTrace v d N) j)^2 =
      (divisorTrace v d N (j+1))^2 + (divisorTrace v d N j)^2 := by
    have h := divisorTrace_mul_succ v d N j
    unfold addDiff
    nlinarith
  simp_rw [he]
  rw [Finset.sum_add_distrib]
  have h := telescope_addDiff (fun j => (divisorTrace v d N j)^2) 0 N
  simp only [zero_add, addDiff, divisorTrace_zero, divisorTrace_end, zero_pow (by decide : 2 ≠ 0),
    sub_self, Finset.sum_sub_distrib] at h
  linarith

def divisorVelocity (v : ℕ → ℝ) (d N : ℕ) : Velocity :=
  stepVelocity (addDiff (divisorTrace v d N)) N

/-- Actual Sobolev representatives of every finite coprime trace, without a support premise. -/
theorem divisorVelocity_trace (v : ℕ → ℝ) (d N : ℕ) (m : Fin (N+1)) :
    primitive (divisorVelocity v d N) m = divisorTrace v d N m := by
  have h := primitive_stepVelocity_trace (divisorTrace v d N) N m
  simpa only [divisorTrace_zero, zero_add, divisorVelocity] using h

/-- Sharp continuum coprime successor energy, attained by a constructed L2 velocity. -/
theorem divisorVelocity_energy (v : ℕ → ℝ) (d N : ℕ) :
    energy (divisorVelocity v d N) 0 N =
      2 * ∑ j ∈ Finset.range N, (divisorTrace v d N j)^2 := by
  unfold divisorVelocity
  rw [energy_stepVelocity, divisorTrace_discrete_energy]

/-- Every amplitude is realized at the first active divisor node. -/
theorem divisorVelocity_active_trace (v : ℕ → ℝ) (d : ℕ) :
    primitive (divisorVelocity v d (d+3)) (d+2) = v (d+2) := by
  calc
    _ = divisorTrace v d (d+3) (d+2) :=
      by simpa using divisorVelocity_trace v d (d+3) ⟨d+2, by omega⟩
    _ = _ := by
      unfold divisorTrace
      rw [if_pos ⟨by omega, by omega, dvd_refl _⟩]

theorem finiteStep_zero_after (s : ℕ → ℝ) (N : ℕ) {t : ℝ} (ht : (N : ℝ) < t) :
    finiteStep s N t = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  apply Set.indicator_of_notMem
  intro h
  have hj' : (j : ℝ)+1 ≤ N := by exact_mod_cast Nat.succ_le_of_lt (Finset.mem_range.mp hj)
  linarith [h.2]

theorem energy_stepVelocity_tail (s : ℕ → ℝ) (N : ℕ) :
    energy (stepVelocity s N) N (N+1) = 0 := by
  unfold energy
  calc
    _ = ∫ _t in (N : ℝ)..(N+1), (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_stepVelocity s N] with t ht
      intro h
      rw [uIoc_of_le (by linarith : (N : ℝ) ≤ N+1)] at h
      rw [ht, finiteStep_zero_after s N h.1, zero_pow (by norm_num : 2 ≠ 0)]
    _ = _ := by simp

theorem finiteStep_divisor_first_cell (v : ℕ → ℝ) (d N : ℕ)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) :
    finiteStep (addDiff (divisorTrace v d N)) N t = 0 := by
  apply Finset.sum_eq_zero
  intro j _
  by_cases hj : j = 0
  · subst j
    simp [cellStep, addDiff, divisorTrace_zero, divisorTrace_one]
  · apply Set.indicator_of_notMem
    intro h
    have hj' : (1 : ℝ) ≤ j := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hj
    linarith [h.1, ht.2]

theorem divisorVelocity_energy_first_cell (v : ℕ → ℝ) (d N : ℕ) :
    energy (divisorVelocity v d N) 0 1 = 0 := by
  unfold energy
  calc
    _ = ∫ _t in (0 : ℝ)..1, (0 : ℝ) := by
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_stepVelocity (addDiff (divisorTrace v d N)) N] with t ht
      intro h
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h
      change (stepVelocity (addDiff (divisorTrace v d N)) N t)^2 = 0
      rw [ht, finiteStep_divisor_first_cell v d N h, zero_pow (by norm_num : 2 ≠ 0)]
    _ = _ := by simp

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
