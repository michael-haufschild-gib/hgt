import GaloisForLFunctions.RHTower.WeilLogShiftFixedMinorant
import GaloisForLFunctions.RHTower.WeilWorkExposingRayTailAsymptotic

/-!
# A uniform inward-shift gain on the truncated autocorrelation tail

A central integration interval gives a lower envelope that survives every
cutoff whose unshifted kernel is visible. The corpus's sharp full-kernel upper
envelope then gives arbitrarily large inward-shift gain, uniformly in the cutoff.
-/

open MeasureTheory Filter Topology Set Real

noncomputable section

namespace RHTower

/-- A central interval of length two supplies an explicit lower envelope inside
the cutoff plateau. -/
theorem truncatedRiemannAutocorr_central_lower {L z : ℝ} (hz : 0 ≤ z)
    (hL : z / 2 + 2 ≤ L) :
    (2 * (2 * π ^ 2) ^ 2) * exp (-(2 * π * exp (z + 2))) ≤
      truncatedRiemannAutocorr L z := by
  have hpoint : ∀ t ∈ Ioc (z / 2 - 1) (z / 2 + 1),
      (2 * π ^ 2) ^ 2 * exp (-(2 * π * exp (z + 2))) ≤
        truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - z) := by
    intro t ht
    have ht1 : |t| ≤ z / 2 + 1 := by
      rw [abs_le]
      constructor <;> linarith only [ht.1, ht.2, hz]
    have ht2 : |t - z| ≤ z / 2 + 1 := by
      rw [abs_le]
      constructor <;> linarith only [ht.1, ht.2, hz]
    have hc1 : |t| ≤ L - 1 := by linarith only [ht1, hL]
    have hc2 : |t - z| ≤ L - 1 := by linarith only [ht2, hL]
    simp only [truncatedRiemannKernelReal, bulkCutoff_eq_one hc1,
      bulkCutoff_eq_one hc2, mul_one]
    have h1 := exp_le_exp.mpr (show 2 * |t| ≤ z + 2 by linarith only [ht1])
    have h2 := exp_le_exp.mpr (show 2 * |t - z| ≤ z + 2 by linarith only [ht2])
    have hs : π * (exp (2 * |t|) + exp (2 * |t - z|)) ≤ 2 * π * exp (z + 2) := by
      have h := mul_le_mul_of_nonneg_left (add_le_add h1 h2) pi_pos.le
      nlinarith only [h]
    have heq (U V : ℝ) : (2 * π ^ 2 * exp U) * (2 * π ^ 2 * exp V) =
        (2 * π ^ 2) ^ 2 * exp (U + V) := by rw [exp_add]; ring
    have hprod : (2 * π ^ 2) ^ 2 * exp (-(2 * π * exp (z + 2))) ≤
        (2 * π ^ 2 * exp (-(π * exp (2 * |t|)))) *
          (2 * π ^ 2 * exp (-(π * exp (2 * |t - z|)))) := by
      rw [heq]
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      apply exp_le_exp.mpr
      linarith only [hs]
    exact hprod.trans (mul_le_mul (ExposingRayTail.phi_lower t)
      (ExposingRayTail.phi_lower (t - z)) (by positivity) (riemannKernelReal_pos _).le)
  have hi := setIntegral_mono_on (integrableOn_const (by simp))
    (integrable_truncatedRiemannKernel_prod L z).integrableOn measurableSet_Ioc hpoint
  have hconst : (∫ t in Ioc (z / 2 - 1) (z / 2 + 1),
      (2 * π ^ 2) ^ 2 * exp (-(2 * π * exp (z + 2)))) =
      (2 * (2 * π ^ 2) ^ 2) * exp (-(2 * π * exp (z + 2))) := by
    rw [setIntegral_const, Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    simp only [smul_eq_mul]
    ring
  rw [hconst] at hi
  exact hi.trans (setIntegral_le_integral (integrable_truncatedRiemannKernel_prod L z)
    (Eventually.of_forall fun t => mul_nonneg (truncatedRiemannKernelReal_nonneg L t)
      (truncatedRiemannKernelReal_nonneg L (t - z))))

/-- Every fixed inward shift of size at least four gives any prescribed tail
gain, uniformly over all real cutoffs. -/
theorem exists_truncatedRiemannAutocorr_tail_shift_gain {c : ℝ} (hc : 4 ≤ c) (A : ℝ) :
    ∃ Y : ℝ, ∀ y : ℝ, Y ≤ y → ∀ L : ℝ,
      A * truncatedRiemannAutocorr L y ≤ truncatedRiemannAutocorr L (y - c) := by
  obtain ⟨C, hC0, hC⟩ := ExposingRayTail.autocorr_upper (c := π / 2)
    (by positivity) (by linarith only [pi_pos])
  let D := 2 * (2 * π ^ 2) ^ 2
  have hD : 0 < D := by dsimp only [D]; positivity
  have hE : Tendsto (fun y : ℝ => exp (-((π / 2) * exp y))) atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul, Function.comp_def] using
      (tendsto_pow_mul_exp_neg_atTop_nhds_zero 0).comp
        (tendsto_exp_atTop.const_mul_atTop (show 0 < π / 2 by positivity))
  have hlim := hE.const_mul (|A| * C)
  rw [mul_zero] at hlim
  obtain ⟨Y, hY⟩ := eventually_atTop.mp ((tendsto_order.mp hlim).2 D hD)
  refine ⟨max c Y, fun y hy L => ?_⟩
  have hyc : c ≤ y := (le_max_left _ _).trans hy
  have hy0 : 0 ≤ y := by linarith only [hc, hyc]
  by_cases hz : 2 * L ≤ y
  · rw [truncatedRiemannAutocorr_eq_zero (by rwa [abs_of_nonneg hy0]), mul_zero]
    exact truncatedRiemannAutocorr_nonneg _ _
  have hcentral := truncatedRiemannAutocorr_central_lower
    (L := L) (z := y - c) (by linarith only [hyc]) (by linarith only [hc, hz])
  have he2 : 4 ≤ exp (2 : ℝ) := by
    rw [show (2 : ℝ) = 1 + 1 by ring, exp_add]
    nlinarith [Real.exp_one_gt_two, sq_nonneg (exp 1 - 2)]
  have hmult : exp (y - c + 2) * exp 2 ≤ exp y := by
    rw [← exp_add]
    exact exp_le_exp.mpr (by linarith only [hc])
  have hscale : 4 * exp (y - c + 2) ≤ exp y := by
    have h := mul_le_mul_of_nonneg_left he2 (exp_pos (y - c + 2)).le
    nlinarith only [h, hmult]
  have hrate : 2 * π * exp (y - c + 2) ≤ (π / 2) * exp y := by
    have h := mul_le_mul_of_nonneg_left hscale pi_pos.le
    nlinarith only [h]
  let E := exp (-((π / 2) * exp y))
  have hElower : D * E ≤ truncatedRiemannAutocorr L (y - c) := by
    refine le_trans ?_ hcentral
    apply mul_le_mul_of_nonneg_left _ hD.le
    apply exp_le_exp.mpr
    linarith only [hrate]
  have hfull : riemannAutocorr y ≤ C * (E * E) := by
    have h := hC y
    change riemannAutocorr y ≤ _ at h
    rw [abs_of_nonneg hy0, show 2 * (π / 2) = π by ring] at h
    have heq : exp (-(π * exp y)) = E * E := by
      dsimp only [E]
      rw [← exp_add]
      congr 1
      ring
    rwa [heq] at h
  have hsmall : |A| * C * E < D := hY y ((le_max_right _ _).trans hy)
  calc A * truncatedRiemannAutocorr L y ≤ |A| * truncatedRiemannAutocorr L y :=
      mul_le_mul_of_nonneg_right (le_abs_self A) (truncatedRiemannAutocorr_nonneg _ _)
    _ ≤ |A| * riemannAutocorr y :=
      mul_le_mul_of_nonneg_left (truncatedRiemannAutocorr_le_riemannAutocorr L y) (abs_nonneg A)
    _ ≤ |A| * (C * (E * E)) := mul_le_mul_of_nonneg_left hfull (abs_nonneg A)
    _ = (|A| * C * E) * E := by ring
    _ ≤ D * E := mul_le_mul_of_nonneg_right hsmall.le (exp_pos _).le
    _ ≤ truncatedRiemannAutocorr L (y - c) := hElower

end RHTower
