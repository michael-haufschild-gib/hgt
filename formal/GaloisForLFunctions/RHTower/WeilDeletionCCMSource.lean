import GaloisForLFunctions.RHTower.WeilSinglePrimeDeletionUniform
import GaloisForLFunctions.RHTower.SuzukiPolarTranslateMultiplier
import GaloisForLFunctions.RHTower.ConstrainedWeilTwistedOddTest
import GaloisForLFunctions.HTGeometry.CompactTestTransform

/-!
# The two-bump test as a Connes–Consani–Moscovici source

The odd two-bump `f(x) = φ(x − u₀/2) − φ(x + u₀/2)` built from the smooth kernel `φ = phiN n` is
smooth with compact support, hence a smooth interior source at every aperture `a > u₀/2 + s`.
Its literal restricted Weil source quadratic is the real part of the zero-side sum

`Σ_q  k̂(γ_q)`,   `k = f ⋆ f̃`,   `k̂(z) = ∫ k(u) e^{izu} du`,

because the ray coefficients of the derivative test are `∓iγ` times the Fourier transform of `f`
and the screw form divides by `γ²`.  Consequently the source quadratic is bounded in absolute value
by the same explicit constant as the explicit-formula functional of the two-bump autocorrelation.
-/

open Complex MeasureTheory Set
open scoped Convolution

namespace RHTower.WeilDeletion

/-! ## Smoothness of the kernel and of the two-bump -/

theorem smoothBump_contDiff_top {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (smoothBump r hr) :=
  ContDiffBump.contDiff_normed _ (n := ⊤)

theorem phi_contDiff_top {r : ℝ} (hr : 0 < r) (w : ℝ) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (phi r hr w n) :=
  HasCompactSupport.contDiff_convolution_left _ (smoothBump_hasCompactSupport hr)
    (smoothBump_contDiff_top hr) (integrable_upow w n).locallyIntegrable

theorem phiN_contDiff_top (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (phiN n) := phi_contDiff_top _ _ _

theorem twoBump_contDiff_top {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (u₀ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (twoBump φ u₀) := by
  unfold twoBump
  exact (hφ.comp (contDiff_id.sub contDiff_const)).sub (hφ.comp (contDiff_id.add contDiff_const))

/-! ## The two-bump as a smooth interior source -/

/-- The complex-valued two-bump `x ↦ φ(x − u₀/2) − φ(x + u₀/2)` with `φ = phiN n`, viewed as a
smooth interior source at any aperture exceeding `u₀/2 + s_n`. -/
noncomputable def twoBumpSource (n : ℕ) {u₀ : ℝ} (hu : 0 ≤ u₀) (a : SuzukiPositiveAperture)
    (ha : u₀ / 2 + sN n < a.1) : CCMComplexSmoothInteriorSource a where
  toFun := fun x => (twoBump (phiN n) u₀ x : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp (twoBump_contDiff_top (phiN_contDiff_top n) u₀)
  hasCompactSupport :=
    (twoBump_hasCompactSupport (support_phiN_subset n) hu).comp_left Complex.ofReal_zero
  tsupport_subset := by
    have h1 : Function.support (fun x => (twoBump (phiN n) u₀ x : ℂ)) ⊆
        Icc (-(u₀ / 2 + sN n)) (u₀ / 2 + sN n) := by
      intro x hx
      apply support_twoBump_subset (support_phiN_subset n) hu
      rw [Function.mem_support] at hx ⊢
      exact fun h => hx (by rw [h]; simp)
    refine (closure_minimal h1 isClosed_Icc).trans ?_
    exact Icc_subset_Ioo (by linarith) ha

theorem twoBumpSource_apply (n : ℕ) {u₀ : ℝ} (hu : 0 ≤ u₀) (a : SuzukiPositiveAperture)
    (ha : u₀ / 2 + sN n < a.1) (x : ℝ) :
    (twoBumpSource n hu a ha : ℝ → ℂ) x = (twoBump (phiN n) u₀ x : ℂ) := rfl

/-! ## Ray coefficients of the derivative test of a real source -/

/-- For a real-valued smooth compactly supported source `g`, the product of the two ray
coefficients of its derivative test, divided by `γ²`, is the Fourier transform of the
autocorrelation of `g` at `γ`. -/
theorem rayCoef_product_derivative_eq_paperFT_autocorr {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) {g : ℝ → ℝ} (hug : ∀ x, (u : ℝ → ℂ) x = (g x : ℂ))
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {c d : ℝ} (hgs : Function.support g ⊆ Icc c d) (q : XiZeroCopy) :
    suzukiTestRayCoefBar u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q *
        suzukiTestRayCoef u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q /
          xiSpectralPoint q ^ (2 : ℕ) =
      Zeta23.paperFT (fun x => (autocorr g x : ℂ)) (xiSpectralPoint q) := by
  set γ : ℂ := xiSpectralPoint q with hγ
  have hγ0 : γ ≠ 0 := xiSpectralPoint_ne_zero q
  have hufun : (u : ℝ → ℂ) = fun x => (g x : ℂ) := funext hug
  have hu1 : ContDiff ℝ 1 (u : ℝ → ℂ) := u.smooth.of_le (by exact_mod_cast le_top)
  have hus : HasCompactSupport (u : ℝ → ℂ) := u.hasCompactSupport
  -- the derivative of a real source is real
  have hderiv_real : ∀ t : ℝ, deriv (u : ℝ → ℂ) t = ((deriv g t : ℝ) : ℂ) := by
    intro t
    rw [hufun]
    exact ((hg.differentiable (by simp)) t).hasDerivAt.ofReal_comp.deriv
  have hconj : ∀ t : ℝ, (starRingEnd ℂ) (deriv (u : ℝ → ℂ) t) = deriv (u : ℝ → ℂ) t := by
    intro t
    rw [hderiv_real t, Complex.conj_ofReal]
  -- the derivative test is the derivative of the source
  have hcoe : (u.toSuzukiSmoothCompactTest.toDerivativeZeroMean : ℝ → ℂ) = deriv (u : ℝ → ℂ) := rfl
  -- the ray coefficients as transforms of the derivative
  have hcoef : suzukiTestRayCoef u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q =
      GaloisForLFunctions.HTGeometry.testTransform (deriv (u : ℝ → ℂ)) (-γ) := by
    rw [suzukiTestRayCoef_eq_integral, hcoe]
    unfold GaloisForLFunctions.HTGeometry.testTransform
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [mul_comm]
    congr 2
    ring
  have hbar : suzukiTestRayCoefBar u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q =
      GaloisForLFunctions.HTGeometry.testTransform (deriv (u : ℝ → ℂ)) γ := by
    rw [suzukiTestRayCoefBar_eq_integral, hcoe]
    unfold GaloisForLFunctions.HTGeometry.testTransform
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [hconj t, mul_comm]
  -- integration by parts
  have hibp1 := GaloisForLFunctions.HTGeometry.testTransform_ibp hu1 hus (-γ)
  have hibp2 := GaloisForLFunctions.HTGeometry.testTransform_ibp hu1 hus γ
  -- transforms of the source are the paper Fourier transforms of `g`
  have hT : ∀ z : ℂ, GaloisForLFunctions.HTGeometry.testTransform (u : ℝ → ℂ) z =
      Zeta23.paperFT (fun x => (g x : ℂ)) z := by
    intro z
    unfold GaloisForLFunctions.HTGeometry.testTransform Zeta23.paperFT
    rw [hufun]
  have hgint : Integrable g :=
    hg.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hgs)
  have hd1 : GaloisForLFunctions.HTGeometry.testTransform (deriv (u : ℝ → ℂ)) (-γ) =
      -(GaloisForLFunctions.HTGeometry.testTransform (u : ℝ → ℂ) (-γ) * (I * -γ)) := by
    rw [hibp1, neg_neg]
  have hd2 : GaloisForLFunctions.HTGeometry.testTransform (deriv (u : ℝ → ℂ)) γ =
      -(GaloisForLFunctions.HTGeometry.testTransform (u : ℝ → ℂ) γ * (I * γ)) := by
    rw [hibp2, neg_neg]
  rw [hbar, hcoef, hd1, hd2, hT, hT, paperFT_autocorr hgint hgs]
  field_simp
  linear_combination (-(Zeta23.paperFT (fun x => (g x : ℂ)) γ *
    Zeta23.paperFT (fun x => (g x : ℂ)) (-γ))) * Complex.I_sq

/-! ## The source quadratic of the two-bump as a zero-side sum -/

theorem ccmRestrictedWeilSourceQuadratic_twoBumpSource_eq_tsum (n : ℕ) {u₀ : ℝ} (hu : 0 ≤ u₀)
    (a : SuzukiPositiveAperture) (ha : u₀ / 2 + sN n < a.1) :
    ccmRestrictedWeilSourceQuadratic a (twoBumpSource n hu a ha).toCCMFormVector =
      (∑' q : XiZeroCopy,
        Zeta23.paperFT (fun x => (autocorr (twoBump (phiN n) u₀) x : ℂ)) (xiSpectralPoint q)).re := by
  rw [ccmRestrictedWeilSourceQuadratic_toCCMFormVector_eq_smoothForm, suzukiScrewSmoothForm_eq_tsum]
  congr 1
  refine tsum_congr fun q => ?_
  exact rayCoef_product_derivative_eq_paperFT_autocorr (twoBumpSource n hu a ha)
    (fun x => rfl) (twoBump_contDiff_top (phiN_contDiff_top n) u₀)
    (support_twoBump_subset (support_phiN_subset n) hu) q

/-! ## Spectral points have modulus squared above `41/2` -/

theorem fortyOne_div_two_lt_normSq_spectralPoint (q : XiZeroCopy) :
    (41 / 2 : ℝ) < ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
  have him := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have hre : (xiSpectralPoint q).re = ((q.1 : ℂ)).im := by
    simp [xiSpectralPoint, Complex.mul_re]
  rw [Complex.sq_norm, Complex.normSq_apply, hre]
  nlinarith [sq_nonneg (xiSpectralPoint q).im]

/-! ## The explicit bound on the source quadratic -/

/-- With the parameters of the uniform deletion theorem the source quadratic of the two-bump
source is bounded by the explicit zero-side constant. -/
theorem abs_ccmRestrictedWeilSourceQuadratic_twoBumpSource_le (n : ℕ) {u₀ p : ℝ} (hu : 0 ≤ u₀)
    (hexp_half : Real.exp (u₀ / 2) = Real.sqrt p) (a : SuzukiPositiveAperture)
    (ha : u₀ / 2 + sN n < a.1) :
    |ccmRestrictedWeilSourceQuadratic a (twoBumpSource n hu a ha).toCCMFormVector| ≤
      (4 * Real.sqrt p * (3 / 2) * ((1081 / 780) ^ (2 * (n + 1)) * (2 / 41) ^ n)) * (33 / 100) := by
  rw [ccmRestrictedWeilSourceQuadratic_twoBumpSource_eq_tsum]
  set C : ℝ := 4 * Real.sqrt p * (3 / 2) * ((1081 / 780) ^ (2 * (n + 1)) * (2 / 41) ^ n) with hC
  have hC0 : 0 ≤ C := by rw [hC]; positivity
  set F : XiZeroCopy → ℂ := fun q =>
    Zeta23.paperFT (fun x => (autocorr (twoBump (phiN n) u₀) x : ℂ)) (xiSpectralPoint q) with hF
  have hterm : ∀ q : XiZeroCopy, ‖F q‖ ≤ C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := fun q =>
    norm_paperFT_autocorr_twoBump_le n hu hexp_half (xiSpectralPoint_ne_zero q)
      (abs_xiSpectralPoint_im_lt_half q).le (fortyOne_div_two_lt_normSq_spectralPoint q)
  have hg_summ : Summable (fun q : XiZeroCopy => C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) :=
    xiSpectralPoint_inv_sq_summable.mul_left _
  have hnorm_summ : Summable (fun q : XiZeroCopy => ‖F q‖) :=
    Summable.of_nonneg_of_le (fun q => norm_nonneg _) hterm hg_summ
  have h1 : |(∑' q, F q).re| ≤ ‖∑' q, F q‖ := Complex.abs_re_le_norm _
  have h2 : ‖∑' q, F q‖ ≤ ∑' q, ‖F q‖ := norm_tsum_le_tsum_norm hnorm_summ
  have h3 : ∑' q, ‖F q‖ ≤ ∑' q : XiZeroCopy, C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) :=
    hnorm_summ.tsum_le_tsum hterm hg_summ
  have h4 : ∑' q : XiZeroCopy, C * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) ≤ C * (33 / 100) := by
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left tsum_inv_normSq_spectralPoint_lt.le hC0
  linarith

end RHTower.WeilDeletion
