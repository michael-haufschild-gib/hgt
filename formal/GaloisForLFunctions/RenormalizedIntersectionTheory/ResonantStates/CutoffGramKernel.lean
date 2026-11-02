import GaloisForLFunctions.RHTower.EisensteinHeckeSecondMoment
import GaloisForLFunctions.RHTower.EisensteinResonantPartnerAngle

/-!
# The joint cutoff Gram kernel of resonant states

Changing the cutoff adds a constant Fourier mode on a cusp band. This mode is
orthogonal to the already truncated state. Consequently the mixed-height pairing
is the Maass–Selberg pairing at the smaller height, including for distinct states.
-/

open Complex MeasureTheory Set UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

private theorem integrable_cutoff_product (u v : ℂ) {Y Z : ℝ}
    (hY : 1 ≤ Y) (hZ : 1 ≤ Z) :
    IntegrableOn (fun z : ℍ => truncatedLineModel u Y z * truncatedLineModel v Z z) fd := by
  refine Measure.integrableOn_of_bounded volume_fd_ne_top
    ((measurable_truncatedLineModel u Y).mul
      (measurable_truncatedLineModel v Z)).aestronglyMeasurable
    (M := truncBound' u Y * truncBound' v Z) ?_
  refine (ae_restrict_iff' isClosed_fd.measurableSet).mpr
    (Filter.Eventually.of_forall fun z hz => ?_)
  rw [norm_mul]
  have hu := norm_truncatedLineModel_le_truncBound' u hY hz
  exact mul_le_mul hu (norm_truncatedLineModel_le_truncBound' v hZ hz)
    (norm_nonneg _) ((norm_nonneg _).trans hu)

/-- A new cutoff band is orthogonal to every state truncated below that band. -/
theorem cutoff_pairing_of_le (u v : ℂ) {Y Z : ℝ} (hY : 1 ≤ Y) (hYZ : Y ≤ Z) :
    (∫ z in fd, truncatedLineModel u Y z * truncatedLineModel v Z z) =
      truncatedPairing Y u v := by
  have hdiff : (fun z : ℍ =>
      truncatedLineModel u Y z * truncatedLineModel v Z z -
        truncatedLineModel u Y z * truncatedLineModel v Y z) =
      (fun z : ℍ => if Y < z.im ∧ z.im ≤ Z then
        d4BMCompletedEisensteinCuspConstantPart .scalar v z.im *
          d4BMCompletedEisensteinCuspTailPart .scalar u z.re z.im else 0) := by
    funext z
    unfold truncatedLineModel eisensteinLineModel d4BMCompletedEisensteinCuspLeg
    by_cases hy : Y < z.im
    · by_cases hz : Z < z.im
      · simp only [hy, hz, not_le_of_gt hz, and_false, if_true, if_false]
        ring
      · simp only [hy, hz, le_of_not_gt hz, and_self, if_true, if_false]
        ring
    · have hz : ¬ Z < z.im := fun hz => hy (lt_of_le_of_lt hYZ hz)
      simp only [hy, hz, false_and, if_false]
      ring
  have hz : (∫ z in fd,
      truncatedLineModel u Y z * truncatedLineModel v Z z -
        truncatedLineModel u Y z * truncatedLineModel v Y z) = 0 := by
    rw [hdiff]
    exact setIntegral_band_mul_tail_eq_zero u hY _
      (continuousOn_cuspConstantPart_height v (by linarith))
  rw [integral_sub (integrable_cutoff_product u v hY (hY.trans hYZ))
    (integrable_cutoff_product u v hY hY)] at hz
  exact sub_eq_zero.mp hz

/-- All mixed-height pairings are determined by the smaller cutoff. -/
theorem cutoff_pairing_min (u v : ℂ) {Y Z : ℝ} (hY : 1 ≤ Y) (hZ : 1 ≤ Z) :
    (∫ z in fd, truncatedLineModel u Y z * truncatedLineModel v Z z) =
      truncatedPairing (min Y Z) u v := by
  rcases le_total Y Z with h | h
  · rw [min_eq_left h]
    exact cutoff_pairing_of_le u v hY h
  · rw [min_eq_right h]
    calc
      _ = ∫ z in fd, truncatedLineModel v Z z * truncatedLineModel u Y z := by
        congr 1; funext z; exact mul_comm _ _
      _ = truncatedPairing Z v u := cutoff_pairing_of_le v u hZ h
      _ = truncatedPairing Z u v := by
        unfold truncatedPairing
        congr 1; funext z; exact mul_comm _ _

/-- The Gram kernel for any two resonant parameters, at any two cutoff heights. -/
theorem resonant_cutoff_gram {u v : ℂ}
    (hu : u ∈ eisensteinLineDomain) (hv : v ∈ eisensteinLineDomain)
    (hur : u.re < 0) (hvr : v.re < 0) (hAu : msA u = 0) (hAv : msA v = 0)
    {Y Z : ℝ} (hY : 1 ≤ Y) (hZ : 1 ≤ Z) :
    (∫ z in fd, truncatedLineModel u Y z *
      (starRingEnd ℂ) (truncatedLineModel v Z z)) =
      -(msB u * (starRingEnd ℂ) (msB v) *
        ((min Y Z : ℝ) : ℂ) ^ (-u - (starRingEnd ℂ) v)) /
          (u + (starRingEnd ℂ) v) := by
  have hvi : ((starRingEnd ℂ) v).im ≠ 0 := by simp; exact hv.2.ne'
  have hp : (∫ z in fd, truncatedLineModel u Y z *
      (starRingEnd ℂ) (truncatedLineModel v Z z)) =
      truncatedPairing (min Y Z) u (-(starRingEnd ℂ) v) := by
    simp_rw [truncatedLineModel_conj, ← truncatedLineModel_neg hvi Z]
    exact cutoff_pairing_min u _ hY hZ
  rw [hp]
  have hsum : u + (starRingEnd ℂ) v ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at he
    linarith
  have hsub : u - (starRingEnd ℂ) v ≠ 0 := by
    intro h
    have he := congrArg Complex.im h
    simp only [Complex.sub_im, Complex.conj_im, Complex.zero_im] at he
    linarith [hu.2, hv.2]
  have h := maassSelberg_lineModel hu
    (neg_conj_mem_eisensteinLineDomain hv (by linarith)) (le_min hY hZ)
  rw [msRight, hAu, msA_neg_conj hv.2.ne', msB_neg_conj hv.2.ne', hAv,
    map_zero] at h
  have he1 : u - -(starRingEnd ℂ) v = u + (starRingEnd ℂ) v := by ring
  have he2 : u + -(starRingEnd ℂ) v = u - (starRingEnd ℂ) v := by ring
  have he3 : -(starRingEnd ℂ) v - u = -u - (starRingEnd ℂ) v := by ring
  rw [he1, he2, he3] at h
  simp only [zero_mul, mul_zero, zero_add, sub_zero, zero_sub] at h
  apply (eq_div_iff hsum).mpr
  apply mul_left_cancel₀ hsub
  linear_combination h

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
