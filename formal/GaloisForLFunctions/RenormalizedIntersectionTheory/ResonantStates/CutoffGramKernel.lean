import GaloisForLFunctions.RHTower.EisensteinHeckeMaassSelberg
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

/-- Elementary cusp powers, square integrable for every parameter with negative real part. -/
def cuspCutoff (u : ℂ) (Y y : ℝ) : ℂ :=
  if y ∈ Ioc 0 Y then msB u * (y : ℂ) ^ (-u - 1 / 2) else 0

private theorem cusp_product (u v : ℂ) (Y Z : ℝ) :
    (fun y => cuspCutoff u Y y * (starRingEnd ℂ) (cuspCutoff v Z y)) =
      (Ioc 0 (min Y Z)).indicator (fun y : ℝ =>
        (msB u * (starRingEnd ℂ) (msB v)) *
          (y : ℂ) ^ (-u - (starRingEnd ℂ) v - 1)) := by
  funext y
  by_cases hY : y ∈ Ioc 0 Y
  · by_cases hZ : y ∈ Ioc 0 Z
    · rw [cuspCutoff, cuspCutoff, if_pos hY, if_pos hZ,
        Set.indicator_of_mem (show y ∈ Ioc 0 (min Y Z) from ⟨hY.1, le_min hY.2 hZ.2⟩),
        map_mul, conj_cpow_of_pos hY.1]
      simp only [map_sub, map_neg, map_div₀, map_one, map_ofNat]
      have he : (-u - (1 : ℂ) / 2) + (-(starRingEnd ℂ) v - 1 / 2) =
          -u - (starRingEnd ℂ) v - 1 := by ring
      rw [← he, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hY.1.ne')]
      ring
    · have hn : y ∉ Ioc 0 (min Y Z) := fun h => hZ ⟨h.1, h.2.trans (min_le_right _ _)⟩
      simp only [cuspCutoff, if_neg hZ, map_zero, mul_zero, Set.indicator_of_notMem hn]
  · have hn : y ∉ Ioc 0 (min Y Z) := fun h => hY ⟨h.1, h.2.trans (min_le_left _ _)⟩
    simp only [cuspCutoff, if_neg hY, zero_mul, Set.indicator_of_notMem hn]

private theorem cusp_exponent_re {u v : ℂ} (hu : u.re < 0) (hv : v.re < 0) :
    -1 < (-u - (starRingEnd ℂ) v - 1).re := by
  simp only [Complex.sub_re, Complex.neg_re, Complex.conj_re, Complex.one_re]
  linarith

/-- Integrability of every cross product in the elementary model. -/
theorem integrable_cusp_product {u v : ℂ} (hu : u.re < 0) (hv : v.re < 0)
    {Y Z : ℝ} (hY : 0 ≤ Y) (hZ : 0 ≤ Z) :
    Integrable (fun y => cuspCutoff u Y y * (starRingEnd ℂ) (cuspCutoff v Z y)) := by
  rw [cusp_product]
  have hi := (intervalIntegrable_iff_integrableOn_Ioc_of_le (le_min hY hZ)).mp
    (intervalIntegral.intervalIntegrable_cpow' (cusp_exponent_re hu hv))
  exact IntegrableOn.integrable_indicator (hi.const_mul _) measurableSet_Ioc

/-- The same Gram kernel exists for all negative real parts, without a resonance condition. -/
theorem cusp_cutoff_gram {u v : ℂ} (hu : u.re < 0) (hv : v.re < 0)
    {Y Z : ℝ} (hY : 0 ≤ Y) (hZ : 0 ≤ Z) :
    (∫ y, cuspCutoff u Y y * (starRingEnd ℂ) (cuspCutoff v Z y)) =
      -(msB u * (starRingEnd ℂ) (msB v) *
        ((min Y Z : ℝ) : ℂ) ^ (-u - (starRingEnd ℂ) v)) /
          (u + (starRingEnd ℂ) v) := by
  have hn : -u - (starRingEnd ℂ) v ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.neg_re, Complex.conj_re, Complex.zero_re] at he
    linarith
  rw [cusp_product, integral_indicator measurableSet_Ioc, integral_const_mul,
    ← intervalIntegral.integral_of_le (le_min hY hZ),
    integral_cpow (Or.inl (cusp_exponent_re hu hv)), sub_add_cancel,
    Complex.ofReal_zero, Complex.zero_cpow hn, sub_zero]
  rw [show -u - (starRingEnd ℂ) v = -(u + (starRingEnd ℂ) v) by ring, div_neg]
  ring

/-- Every mixed resonant pairing agrees with the elementary cusp model. -/
theorem resonant_pairing_eq_cusp_pairing {u v : ℂ}
    (hu : u ∈ eisensteinLineDomain) (hv : v ∈ eisensteinLineDomain)
    (hur : u.re < 0) (hvr : v.re < 0) (hAu : msA u = 0) (hAv : msA v = 0)
    {Y Z : ℝ} (hY : 1 ≤ Y) (hZ : 1 ≤ Z) :
    (∫ z in fd, truncatedLineModel u Y z *
      (starRingEnd ℂ) (truncatedLineModel v Z z)) =
        ∫ y, cuspCutoff u Y y * (starRingEnd ℂ) (cuspCutoff v Z y) := by
  rw [resonant_cutoff_gram hu hv hur hvr hAu hAv hY hZ,
    cusp_cutoff_gram hur hvr (by linarith) (by linarith)]

private theorem integral_norm_sum {α ι : Type*} [MeasurableSpace α]
    (μ : Measure α) (S : Finset ι) (f : ι → α → ℂ) (c : ι → ℂ)
    (hf : ∀ i ∈ S, ∀ j ∈ S, Integrable (fun x => f i x * (starRingEnd ℂ) (f j x)) μ) :
    (∫ x, ((‖∑ i ∈ S, c i * f i x‖ ^ 2 : ℝ) : ℂ) ∂μ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * (starRingEnd ℂ) (c j)) *
        (∫ x, f i x * (starRingEnd ℂ) (f j x) ∂μ) := by
  have he : ∀ x, ((‖∑ i ∈ S, c i * f i x‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * (starRingEnd ℂ) (c j)) *
        (f i x * (starRingEnd ℂ) (f j x)) := by
    intro x
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    simp only [map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  simp_rw [he]
  rw [integral_finsetSum S (fun i hi =>
    integrable_finsetSum S (fun j hj => (hf i hi j hj).const_mul _))]
  apply Finset.sum_congr rfl
  intro i hi
  rw [integral_finsetSum S (fun j hj => (hf i hi j hj).const_mul _)]
  apply Finset.sum_congr rfl
  intro j hj
  exact integral_const_mul _ _

/-- The elementary cusp model preserves the norm of every finite combination of
resonant states, allowing a different cutoff for each state. -/
theorem resonant_finite_combination_isometry {ι : Type*} (S : Finset ι)
    (u : ι → ℂ) (Y : ι → ℝ) (c : ι → ℂ)
    (hu : ∀ i ∈ S, u i ∈ eisensteinLineDomain)
    (hur : ∀ i ∈ S, (u i).re < 0) (hAu : ∀ i ∈ S, msA (u i) = 0)
    (hY : ∀ i ∈ S, 1 ≤ Y i) :
    (∫ z in fd, ‖∑ i ∈ S, c i * truncatedLineModel (u i) (Y i) z‖ ^ 2) =
      ∫ y, ‖∑ i ∈ S, c i * cuspCutoff (u i) (Y i) y‖ ^ 2 := by
  have hactual : ∀ i ∈ S, ∀ j ∈ S, IntegrableOn (fun z : ℍ =>
      truncatedLineModel (u i) (Y i) z *
        (starRingEnd ℂ) (truncatedLineModel (u j) (Y j) z)) fd := by
    intro i hi j hj
    simp_rw [truncatedLineModel_conj]
    exact integrable_cutoff_product _ _ (hY i hi) (hY j hj)
  have hmodel : ∀ i ∈ S, ∀ j ∈ S, Integrable (fun y =>
      cuspCutoff (u i) (Y i) y * (starRingEnd ℂ) (cuspCutoff (u j) (Y j) y)) := by
    intro i hi j hj
    exact integrable_cusp_product (hur i hi) (hur j hj)
      (zero_le_one.trans (hY i hi)) (zero_le_one.trans (hY j hj))
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal, ← integral_complex_ofReal,
    integral_norm_sum _ S _ c hactual, integral_norm_sum _ S _ c hmodel]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [resonant_pairing_eq_cusp_pairing (hu i hi) (hu j hj) (hur i hi) (hur j hj)
    (hAu i hi) (hAu j hj) (hY i hi) (hY j hj)]

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
