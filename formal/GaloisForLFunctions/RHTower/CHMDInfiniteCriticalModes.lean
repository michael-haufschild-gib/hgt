import GaloisForLFunctions.RHTower.CHMDThetaCriticalModes
import GaloisForLFunctions.RHTower.ThetaArithmeticTerminalCusp

/-!
# Infinite critical multiplicity in the actual CHMD graph

Decreasing positive theta shifts give a countable independent family in the
exact signed radical. Independence comes from the literal full-theta cusp
separation, after graph admission and the full-domain radical identity.
-/

open MeasureTheory Set Filter Topology
open scoped InnerProductSpace BigOperators
noncomputable section
namespace RHTower.CHMDThetaTranslate
open CHMDDoobGraph

def shifts (n : ℕ) : ℝ := radius / ((n : ℝ)+1)

theorem shifts_pos (n : ℕ) : 0 < shifts n := div_pos radius_pos (by positivity)

theorem shifts_le_radius (n : ℕ) : shifts n ≤ radius :=
  div_le_self radius_pos.le (by linarith [Nat.cast_nonneg (α := ℝ) n])

theorem shifts_strictAnti : StrictAnti shifts := by
  intro i j hij
  exact div_lt_div_of_pos_left radius_pos (by positivity) (by exact_mod_cast Nat.add_lt_add_right hij 1)

theorem shifts_admissible (n : ℕ) : 1 < 2 * Real.exp (-2 * |shifts n|) :=
  small_shift (by rw [abs_of_pos (shifts_pos n)]; exact shifts_le_radius n)

def sequence (n : ℕ) : SourceGraph := critical (shifts n) (shifts_admissible n)

def polarSource (a x : ℝ) : ℝ :=
  riemannKernelReal (x-a) + riemannKernelReal (x+a) - 2 * Real.cosh (a/2) * riemannKernelReal x

theorem theta_ratio_tendsto {a b : ℝ} (hab : b < a) :
    Tendsto (fun x => riemannKernelReal (x-b) / riemannKernelReal (x-a)) atTop (𝓝 0) := by
  have hh := thetaCuspFullSource_add_div_add_tendsto_zero
    (u := -b) (v := -a) (by linarith)
  simpa only [thetaCuspFullSource_eq_riemannKernelReal, sub_eq_add_neg] using hh

theorem polarSource_normalized_self {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x => polarSource a x / riemannKernelReal (x-a)) atTop (𝓝 1) := by
  have hp := theta_ratio_tendsto (a := a) (b := -a) (by linarith)
  have h0 := theta_ratio_tendsto (a := a) (b := 0) ha
  have hh := (tendsto_const_nhds (x := (1 : ℝ)) |>.add hp).sub
    (h0.const_mul (2 * Real.cosh (a/2)))
  norm_num only [sub_zero, add_zero, mul_zero] at hh
  convert hh using 1
  funext x
  unfold polarSource
  rw [sub_div, add_div, div_self (riemannKernelReal_pos _).ne']
  simp only [sub_neg_eq_add]
  ring

theorem polarSource_normalized_smaller {a b : ℝ} (hb : 0 < b) (hba : b < a) :
    Tendsto (fun x => polarSource b x / riemannKernelReal (x-a)) atTop (𝓝 0) := by
  have hp := theta_ratio_tendsto hba
  have hm := theta_ratio_tendsto (a := a) (b := -b) (by linarith)
  have h0 := theta_ratio_tendsto (a := a) (b := 0) (by linarith)
  have hh := (hp.add hm).sub (h0.const_mul (2 * Real.cosh (b/2)))
  norm_num only [sub_zero, add_zero, mul_zero] at hh
  convert hh using 1
  funext x
  unfold polarSource
  simp only [sub_div, add_div, sub_neg_eq_add]
  ring

theorem critical_normalization (a b x : ℝ) :
    criticalFunction b x / ratio a x = polarSource b x / riemannKernelReal (x-a) := by
  unfold criticalFunction ratio polarSource
  simp only [sub_neg_eq_add]
  field_simp [(riemannKernelReal_pos x).ne', (riemannKernelReal_pos (x-a)).ne']

theorem normalized_sequence_limit {i j : ℕ} (hij : i ≤ j) :
    Tendsto (fun x => criticalFunction (shifts j) x / ratio (shifts i) x) atTop
      (𝓝 (if j = i then 1 else 0)) := by
  simp only [critical_normalization]
  by_cases he : j = i
  · subst j
    simpa using polarSource_normalized_self (shifts_pos i)
  · rw [if_neg he]
    exact polarSource_normalized_smaller (shifts_pos j)
      (shifts_strictAnti (lt_of_le_of_ne hij (Ne.symm he)))

theorem criticalFunctions_linearIndependent :
    LinearIndependent ℝ (fun n : ℕ => criticalFunction (shifts n)) := by
  classical
  rw [linearIndependent_iff]
  intro d hd
  by_contra hne
  have hs := Finsupp.support_nonempty_iff.mpr hne
  let i := d.support.min' hs
  have hi : i ∈ d.support := Finset.min'_mem _ _
  have hn : d i ≠ 0 := Finsupp.mem_support_iff.mp hi
  have ht (j : ℕ) (hj : j ∈ d.support) :
      Tendsto (fun x => d j * (criticalFunction (shifts j) x / ratio (shifts i) x)) atTop
        (𝓝 (if j = i then d i else 0)) := by
    have hh := (normalized_sequence_limit (i := i) (j := j)
      (Finset.min'_le d.support j hj)).const_mul (d j)
    by_cases he : j = i <;> simpa [he] using hh
  have hsum := tendsto_finsetSum d.support ht
  have heq : (∑ j ∈ d.support, if j = i then d i else 0) = d i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · exact fun hh => (hh hi).elim
  rw [heq] at hsum
  have hz (x : ℝ) : ∑ j ∈ d.support,
      d j * (criticalFunction (shifts j) x / ratio (shifts i) x) = 0 := by
    have hh := congrFun hd x
    simp only [Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hh
    calc
      _ = (∑ j ∈ d.support, d j * criticalFunction (shifts j) x) / ratio (shifts i) x := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = 0 := by rw [hh, zero_div]
  exact hn (tendsto_nhds_unique hsum (by simp only [hz]; exact tendsto_const_nhds))

theorem sequence_linearIndependent : LinearIndependent ℝ sequence := by
  classical
  rw [linearIndependent_iff']
  intro s c hs i hi
  have hLp : ∑ j ∈ s, c j • (sequence j).val.fst = 0 := by
    have hh := congrArg sourceMap hs
    simp only [map_sum, map_smul, map_zero] at hh
    exact hh
  have ht (j : ℕ) :
      ((c j • (sequence j).val.fst : Lp ℝ 2 massMeasure) : ℝ → ℝ) =ᵐ[massMeasure]
        fun x => c j * criticalFunction (shifts j) x := by
    filter_upwards [Lp.coeFn_smul (c j) (sequence j).val.fst,
      critical_source_ae (shifts j) (shifts_admissible j)] with x h1 h2
    rw [h1, Pi.smul_apply]
    change c j * (sequence j).val.fst x = _
    change (sequence j).val.fst x = criticalFunction (shifts j) x at h2
    rw [h2]
  have hae : (fun x => ∑ j ∈ s, c j * criticalFunction (shifts j) x) =ᵐ[massMeasure] 0 := by
    filter_upwards [Lp.coeFn_finsetSum s (fun j => c j • (sequence j).val.fst),
      ae_all_iff.mpr ht, Lp.coeFn_zero ℝ 2 massMeasure] with x hsum hterm hzero
    rw [hLp] at hsum
    change (∑ j ∈ s, c j * criticalFunction (shifts j) x) = 0
    calc
      _ = ∑ j ∈ s, (c j • (sequence j).val.fst : Lp ℝ 2 massMeasure) x :=
        Finset.sum_congr rfl (fun j _ => (hterm j).symm)
      _ = (0 : Lp ℝ 2 massMeasure) x := by simpa only [Finset.sum_apply] using hsum.symm
      _ = 0 := hzero
  have hcont : Continuous (fun x => ∑ j ∈ s, c j * criticalFunction (shifts j) x) := by
    apply continuous_finsetSum
    intro j _
    exact continuous_const.mul
      (((continuous_ratio (shifts j)).add (continuous_ratio (-shifts j))).sub continuous_const)
  have hraw : ∑ j ∈ s, c j • criticalFunction (shifts j) = 0 := by
    have hh : (fun x => ∑ j ∈ s, c j * criticalFunction (shifts j) x) = (fun _ : ℝ => (0 : ℝ)) :=
      (hcont.ae_eq_iff_eq (μ := (volume : Measure ℝ)) continuous_const).mp
        (volume_absolutelyContinuous_mass.ae_eq hae)
    funext x
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using congrFun hh x
  exact (linearIndependent_iff'.mp criticalFunctions_linearIndependent) s c hraw i hi

/-- The full jump form has infinitely many independent primitive weak modes at one. -/
theorem exists_infinite_exact_primitive_critical :
    ∃ p : ℕ → SourceGraph, LinearIndependent ℝ p ∧ ∀ n,
      p n ∈ compactCore ∧ ⟪(p n).val.fst, (constantLift 1).val.fst⟫_ℝ = 0 ∧
      ∀ q : SourceGraph, ⟪(p n).val.snd, q.val.snd⟫_ℝ = ⟪(p n).val.fst, q.val.fst⟫_ℝ := by
  refine ⟨sequence, sequence_linearIndependent, fun n => ?_⟩
  exact ⟨by rw [compactCore_eq_top]; trivial,
    critical_primitive (shifts n) (shifts_admissible n),
    critical_jump_identity (shifts n) (shifts_admissible n)⟩

end RHTower.CHMDThetaTranslate
