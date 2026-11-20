import GaloisForLFunctions.ArithmeticPositiveDuality.TheDiagonalEnergyOfSignedHalfOrderRows
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Logarithmic residue and finite part of a measured half-order pairing

Cut each atom off at distance ε from its own endpoint, then multiply the
two resulting fields and integrate. Every common positive site contributes
the product of its weights to the logarithmic residue. The finite part
retains the exact mixed Gram interactions and the site-dependent diagonal.
-/

noncomputable section
open Finset Set Filter MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancy

def cutoffHalfAtom (ε : ℝ) (i : ℕ) : ℝ → ℝ :=
  (Set.Ioc 0 ((i:ℝ)-ε)).indicator (halfAtom i)

def cutoffHalfRow (ε : ℝ) (S : Finset ℕ) (w : ℕ → ℝ) (t : ℝ) :=
  ∑ i ∈ S, w i*cutoffHalfAtom ε i t

/-- Coefficient of log(1/ε) in the integrated product of two rows. -/
def halfRowResidue (S : Finset ℕ) (w v : ℕ → ℝ) :=
  ∑ i ∈ S, if i=0 then 0 else w i*v i

def halfRowFinitePart (S : Finset ℕ) (w v : ℕ → ℝ) :=
  ∑ i ∈ S, ∑ j ∈ S, (w i*v j)*(if j=i then Real.log i else offDiagonalKernel i j)

private theorem measurable_cutoff (ε : ℝ) (i : ℕ) : Measurable (cutoffHalfAtom ε i) :=
  (measurable_halfAtom _).indicator measurableSet_Ioc

private theorem cutoff_dominated (ε : ℝ) (i j : ℕ) (t : ℝ) :
    ‖cutoffHalfAtom ε i t*cutoffHalfAtom ε j t‖ ≤ ‖halfAtom i t*halfAtom j t‖ := by
  by_cases hi : t∈Set.Ioc 0 ((i:ℝ)-ε) <;> by_cases hj : t∈Set.Ioc 0 ((j:ℝ)-ε) <;>
    simp [cutoffHalfAtom,hi,hj]

private theorem cutoff_eventually (i : ℕ) (t : ℝ) :
    ∀ᶠ ε in 𝓝[>] (0:ℝ), cutoffHalfAtom ε i t=halfAtom i t := by
  by_cases ht : 0<t ∧ t<(i:ℝ)
  · filter_upwards [(gt_mem_nhds (sub_pos.mpr ht.2)).filter_mono nhdsWithin_le_nhds] with ε he
    exact indicator_of_mem (show t∈Set.Ioc 0 ((i:ℝ)-ε) from ⟨ht.1,by linarith only [he]⟩) _
  · have hz : halfAtom i t=0 := by
      by_cases hp : 0<t
      · simp [halfAtom,cutPower,hp,sub_pos,show ¬t<(i:ℝ) from fun h => ht ⟨hp,h⟩]
      · simp [halfAtom,hp]
    exact Eventually.of_forall fun ε => by
      by_cases h : t∈Set.Ioc 0 ((i:ℝ)-ε) <;> simp [cutoffHalfAtom,h,hz]

private theorem cutoff_cross_limit {i j : ℕ} (h : i≠j) :
    Tendsto (fun ε => ∫ t, cutoffHalfAtom ε i t*cutoffHalfAtom ε j t) (𝓝[>] (0:ℝ))
      (𝓝 (offDiagonalKernel i j)) := by
  rw [←halfAtom_mixed_integral h]
  apply tendsto_integral_filter_of_dominated_convergence (fun t => ‖halfAtom i t*halfAtom j t‖)
  · exact Eventually.of_forall fun ε => ((measurable_cutoff ε i).mul (measurable_cutoff ε j)).aestronglyMeasurable
  · exact Eventually.of_forall fun ε => ae_of_all _ (cutoff_dominated ε i j)
  · exact (halfAtom_mixed_integrable h).norm
  · apply ae_of_all
    intro t
    apply tendsto_nhds_of_eventually_eq
    filter_upwards [cutoff_eventually i t,cutoff_eventually j t] with ε hi hj
    rw [hi,hj]

private theorem cutoff_diagonal {i : ℕ} (hi : 0<i) {ε : ℝ} (he : 0<ε) (hε : ε≤i) :
    (∫ t, cutoffHalfAtom ε i t*cutoffHalfAtom ε i t)=Real.log i-Real.log ε := by
  have hid (t : ℝ) : cutoffHalfAtom ε i t*cutoffHalfAtom ε i t =
      (Set.Ioc 0 ((i:ℝ)-ε)).indicator (fun t => halfAtom i t^2) t := by
    by_cases h : t∈Set.Ioc 0 ((i:ℝ)-ε) <;> simp [cutoffHalfAtom,h,pow_two]
  simp_rw [hid]
  rw [integral_indicator measurableSet_Ioc,←intervalIntegral.integral_of_le (sub_nonneg.mpr hε),
    halfAtom_diagonal_truncation he hε,Real.log_div (Nat.cast_pos.mpr hi).ne' he.ne']

private lemma cutoff_zero_site (ε t : ℝ) : cutoffHalfAtom ε 0 t=0 := by
  by_cases h : t∈Set.Ioc 0 ((0:ℝ)-ε) <;> simp [cutoffHalfAtom,h,halfAtom_zero_site]

private theorem cutoff_pair_integrable {ε : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1) (i j : ℕ) :
    Integrable (fun t => cutoffHalfAtom ε i t*cutoffHalfAtom ε j t) := by
  by_cases h : i=j
  · subst j
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · simp [cutoff_zero_site]
    · have hlt := hε.2.trans_le (Nat.one_le_cast.mpr hi)
      by_contra hn
      have he := cutoff_diagonal hi hε.1 hlt.le
      rw [integral_undef hn] at he
      exact (sub_pos.mpr (Real.log_lt_log hε.1 hlt)).ne he
  · exact (halfAtom_mixed_integrable h).mono
      ((measurable_cutoff ε i).mul (measurable_cutoff ε j)).aestronglyMeasurable
      (ae_of_all _ (cutoff_dominated ε i j))

theorem integral_cutoff_pairing {ε : ℝ} (hε : ε ∈ Set.Ioo (0:ℝ) 1) (S : Finset ℕ) (w v : ℕ → ℝ) :
    (∫ t, cutoffHalfRow ε S w t*cutoffHalfRow ε S v t)=
      ∑ i ∈ S, ∑ j ∈ S, (w i*v j)*(∫ t, cutoffHalfAtom ε i t*cutoffHalfAtom ε j t) := by
  have hi (i j : ℕ) := (cutoff_pair_integrable hε i j).const_mul (w i*v j)
  have he (t : ℝ) : cutoffHalfRow ε S w t*cutoffHalfRow ε S v t =
      ∑ i ∈ S, ∑ j ∈ S, (w i*v j)*(cutoffHalfAtom ε i t*cutoffHalfAtom ε j t) := by
    rw [cutoffHalfRow,cutoffHalfRow,Finset.sum_mul]
    apply sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    exact sum_congr rfl fun j _ => by ring
  simp_rw [he]
  rw [integral_finsetSum S (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  refine sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum S (fun j _ => hi i j)]
  exact sum_congr rfl fun j _ => integral_const_mul _ _

private def diagonalSubtraction (ε : ℝ) (i j : ℕ) :=
  if j=i then (if i=0 then 0 else Real.log (1/ε)) else 0

private theorem regularized_pair_limit (i j : ℕ) :
    Tendsto (fun ε => (∫ t, cutoffHalfAtom ε i t*cutoffHalfAtom ε j t)-diagonalSubtraction ε i j)
      (𝓝[>] (0:ℝ)) (𝓝 (if j=i then Real.log i else offDiagonalKernel i j)) := by
  by_cases h : j=i
  · subst j
    apply tendsto_nhds_of_eventually_eq
    rcases Nat.eq_zero_or_pos i with rfl | hi
    · exact Eventually.of_forall fun ε => by simp [cutoff_zero_site,diagonalSubtraction]
    · filter_upwards [self_mem_nhdsWithin,(gt_mem_nhds (zero_lt_one' ℝ)).filter_mono nhdsWithin_le_nhds]
        with ε (hpos : 0<ε) hlt
      rw [cutoff_diagonal hi hpos (hlt.le.trans (Nat.one_le_cast.mpr hi))]
      simp only [diagonalSubtraction,if_pos rfl,if_neg hi.ne',one_div,Real.log_inv,sub_neg_eq_add]
      ring
  · simpa only [diagonalSubtraction,if_neg h,sub_zero] using cutoff_cross_limit h.symm

/-- The common cutoff tends to zero through arbitrary positive reals.
Oppositely signed shared sites can cancel in the total logarithmic residue. -/
theorem cutoff_half_pairing_finite_part (S : Finset ℕ) (w v : ℕ → ℝ) :
    Tendsto (fun ε => (∫ t, cutoffHalfRow ε S w t*cutoffHalfRow ε S v t)-
      Real.log (1/ε)*halfRowResidue S w v) (𝓝[>] (0:ℝ)) (𝓝 (halfRowFinitePart S w v)) := by
  have h := tendsto_finsetSum S fun i _ => tendsto_finsetSum S fun j _ =>
    (regularized_pair_limit i j).const_mul (w i*v j)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,(gt_mem_nhds (zero_lt_one' ℝ)).filter_mono nhdsWithin_le_nhds]
    with ε (hpos : 0<ε) hlt
  rw [integral_cutoff_pairing ⟨hpos,hlt⟩]
  simp only [mul_sub,sum_sub_distrib]
  congr 1
  rw [halfRowResidue,mul_sum]
  refine sum_congr rfl fun i hi => ?_
  have he (j : ℕ) : w i*v j*diagonalSubtraction ε i j =
      (if j=i then Real.log (1/ε)*(if i=0 then 0 else w i*v i) else 0) := by
    by_cases hj : j=i <;> by_cases h0 : i=0 <;> simp [diagonalSubtraction,hj,h0,mul_comm]
  simp_rw [he]
  simp [hi]

#print axioms integral_cutoff_pairing
#print axioms cutoff_half_pairing_finite_part

private theorem cutoff_log_atTop : Tendsto (fun ε : ℝ => Real.log (1/ε)) (𝓝[>] 0) atTop := by
  simpa only [one_div,Real.log_inv,Function.comp_def] using
    (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)

/-- Dividing a measured pairing by its logarithmic resolution extracts
the inner product of the weights at the common positive sites. -/
theorem cutoff_half_pairing_residue (S : Finset ℕ) (w v : ℕ → ℝ) :
    Tendsto (fun ε => (∫ t, cutoffHalfRow ε S w t*cutoffHalfRow ε S v t)/Real.log (1/ε))
      (𝓝[>] 0) (𝓝 (halfRowResidue S w v)) := by
  have h := ((cutoff_half_pairing_finite_part S w v).div_atTop cutoff_log_atTop).add_const
    (halfRowResidue S w v)
  rw [zero_add] at h
  apply h.congr'
  filter_upwards [cutoff_log_atTop.eventually_gt_atTop 0] with ε he
  simp only [sub_div,mul_div_cancel_left₀ _ he.ne',sub_add_cancel]

/-- The unrenormalized signed cutoff pairing has a finite limit exactly
when the weighted common sites have zero total residue. -/
theorem cutoff_half_pairing_converges_iff (S : Finset ℕ) (w v : ℕ → ℝ) :
    (∃ c : ℝ, Tendsto (fun ε => ∫ t, cutoffHalfRow ε S w t*cutoffHalfRow ε S v t)
      (𝓝[>] 0) (𝓝 c)) ↔ halfRowResidue S w v=0 := by
  constructor
  · rintro ⟨c,hc⟩
    exact tendsto_nhds_unique (cutoff_half_pairing_residue S w v) (hc.div_atTop cutoff_log_atTop)
  · intro h
    exact ⟨_,by simpa only [h,mul_zero,sub_zero] using cutoff_half_pairing_finite_part S w v⟩

#print axioms cutoff_half_pairing_residue
#print axioms cutoff_half_pairing_converges_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.FractionalDiscrepancy
