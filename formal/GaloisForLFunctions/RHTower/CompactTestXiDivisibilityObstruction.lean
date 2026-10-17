import GaloisForLFunctions.RHTower.FiniteDirichletCriticalNonannihilation
import GaloisForLFunctions.RHTower.GammaHardyPhaseRateLevyKhintchine
import Zeta23.WeilEF.VerticalLine

/-!
# No compactly supported test is `Ξ`-divisible

The transform `f̂(z) = ∫ f(u) e^{izu} du` of a compactly supported test is entire of exponential type
(`norm_paperFT_le_exp`), so it has `O(R)` zeros in `|z| ≤ R`, while `Ξ` has `≍ R log R` simple real
zeros there.  Hence `f̂` cannot vanish at every real zero of `Ξ` unless `f = 0`
(`eq_zero_of_paperFT_eq_zero_of_XiC_eq_zero`); in particular no nonzero compactly supported test
has a transform divisible by `Ξ`, or by `Ξ²` (`not_exists_paperFT_eq_XiC_sq_mul`).
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real FourierTransform
open Zeta23

namespace RHTower.CompactTestXiDivisibility

noncomputable section

/-- Exponential type of the transform of a test supported in `[−R, R]`. -/
theorem norm_paperFT_le_exp {f : ℝ → ℂ} (hf : Integrable f) {R : ℝ}
    (hsupp : ∀ u, f u ≠ 0 → |u| ≤ R) (z : ℂ) :
    ‖paperFT f z‖ ≤ (∫ u, ‖f u‖) * Real.exp (R * ‖z‖) := by
  unfold paperFT
  rw [← integral_mul_const]
  refine norm_integral_le_of_norm_le (hf.norm.mul_const _) (Eventually.of_forall fun u => ?_)
  rw [norm_mul, Complex.norm_exp]
  by_cases hu : f u = 0
  · rw [hu, norm_zero, zero_mul, zero_mul]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have hre : (I * z * (u : ℂ)).re = -(z.im * u) := by simp
  rw [hre]
  have h1 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
  have h2 := hsupp u hu
  calc -(z.im * u) ≤ |z.im * u| := neg_le_abs _
    _ = |z.im| * |u| := abs_mul _ _
    _ ≤ ‖z‖ * R := mul_le_mul h1 h2 (abs_nonneg _) (norm_nonneg _)
    _ = R * ‖z‖ := mul_comm _ _

/-- A continuous integrable test with vanishing transform on the real line is zero. -/
theorem eq_zero_of_paperFT_real_eq_zero {f : ℝ → ℂ} (hf : Continuous f) (hfi : Integrable f)
    (h : ∀ r : ℝ, paperFT f r = 0) : f = 0 := by
  have hF : 𝓕 f = 0 := by
    funext ξ
    rw [fourier_eq_paperFT_neg_two_pi_mul, Pi.zero_apply]
    exact_mod_cast h _
  have := hf.fourierInv_fourier_eq hfi (by rw [hF]; exact integrable_zero _ _ _)
  rw [← this, hF]
  funext v
  rw [Real.fourierInv_eq']
  simp

/-- The exponential-type bound with a constant `≥ 1`. -/
theorem exists_paperFT_exponentialType {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) :
    ∃ A C : ℝ, 0 ≤ A ∧ 1 ≤ C ∧ ∀ z : ℂ, ‖paperFT f z‖ ≤ C * Real.exp (A * ‖z‖) := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  have hsupp : ∀ u, f u ≠ 0 → |u| ≤ max R 0 := fun u hu => by
    have := hR (subset_tsupport _ hu)
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
    exact this.trans (le_max_left _ _)
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
  refine ⟨max R 0, max (∫ u, ‖f u‖) 1, le_max_right _ _, le_max_right _ _, fun z => ?_⟩
  exact (norm_paperFT_le_exp hfi hsupp z).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)

/-- `Ξ` at a real point is `ξ` on the critical line. -/
theorem XiC_ofReal_eq_xi_linePt (t : ℝ) : XiC (t : ℂ) = xi (linePt t) := by
  simp only [XiC, linePt]
  push_cast
  ring_nf

/-- **No compactly supported test annihilates the real zeros of `Ξ`.**  If the transform of a
continuous compactly supported `f` vanishes at every real zero of `Ξ`, then `f = 0`. -/
theorem eq_zero_of_paperFT_eq_zero_of_XiC_eq_zero {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hvan : ∀ t : ℝ, XiC (t : ℂ) = 0 → paperFT f t = 0) : f = 0 := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport hfc
  by_contra hne
  have hFne : paperFT f ≠ 0 := fun h0 =>
    hne (eq_zero_of_paperFT_real_eq_zero hf hfi fun r => congrFun h0 r)
  obtain ⟨A, C, hA, hC, hgrow⟩ := exists_paperFT_exponentialType hf hfc
  obtain ⟨t, -, -, hxi, -, hnz⟩ := exists_simpleCritical_nonzero_of_exponentialType
    (WeilEF.differentiable_paperFT hf hfc) hFne hA hC hgrow ∅
  exact hnz (hvan t (by rw [XiC_ofReal_eq_xi_linePt, hxi]))

/-- **No compactly supported test is `Ξ`-divisible.** -/
theorem not_exists_paperFT_eq_XiC_mul {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hne : f ≠ 0) : ¬ ∃ q : ℂ → ℂ, ∀ z : ℂ, paperFT f z = XiC z * q z := by
  rintro ⟨q, hq⟩
  exact hne (eq_zero_of_paperFT_eq_zero_of_XiC_eq_zero hf hfc fun t ht => by rw [hq, ht, zero_mul])

/-- **No compactly supported test is `Ξ²`-divisible.** -/
theorem not_exists_paperFT_eq_XiC_sq_mul {f : ℝ → ℂ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (hne : f ≠ 0) :
    ¬ ∃ q : ℂ → ℂ, ∀ z : ℂ, paperFT f z = XiC z ^ 2 * q z := by
  rintro ⟨q, hq⟩
  exact not_exists_paperFT_eq_XiC_mul hf hfc hne ⟨fun z => XiC z * q z, fun z => by rw [hq]; ring⟩

end

end RHTower.CompactTestXiDivisibility
