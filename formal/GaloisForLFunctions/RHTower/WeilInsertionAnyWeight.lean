import GaloisForLFunctions.RHTower.WeilDeletionZeroCrossing
import GaloisForLFunctions.RHTower.WeilPrimeFreeTest
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarBombieriYoshidaQuantitative
import GaloisForLFunctions.RHTower.ScrewCurvatureSumOfSquares

/-!
# Any nonzero change of one prime weight forces a zero crossing

The restricted Weil operator with the block `w·x^{-1/2}(τ_{log x} + τ_{-log x})` added to its
finite prime block has negative ground energy at some aperture as soon as `w ≠ 0`, for every scale
`x ≥ 2`, and for every scale `x > 1` when `w > 0`.  No threshold on the weight is needed.

The witness is the modulated wide bump `φ(u/L) e^{iζu}`.  Its transform is `L·φ̂(L(z + ζ))`,
concentrated at the frequency `−ζ`, which is chosen strictly below the first Xi zero.  Under the
Riemann hypothesis the zero-side sum of the literal form on this test is therefore `O(L⁻⁴)`, while
the correlation of the test with its own translate by `log x` equals `cos(ζ log x)` times an
overlap of size `L`.  The choice `ζ = 0` for `w > 0` and `ζ = 2π/(3 log x)` for `w < 0` makes the
block term negative of size `L`, so the Rayleigh quotient is negative for large `L`.  If the
Riemann hypothesis fails, the literal ground energy is unbounded below and the inserted block is
a bounded perturbation, so negativity is immediate.
-/

open MeasureTheory Set Filter Topology Complex
open scoped ENNReal InnerProduct
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilDeletion

/-! ## The modulated wide bump -/

/-- The modulated wide bump `φ₂(u/L) e^{iζu}`. -/
def modulatedBump (L ζ : ℝ) : ℝ → ℂ :=
  fun x => (phiN 2 (x / L) : ℂ) * Complex.exp (Complex.I * (ζ : ℂ) * (x : ℂ))

theorem support_modulatedBump_subset (L : ℝ) (hL : 1 ≤ L) (ζ : ℝ) :
    Function.support (modulatedBump L ζ) ⊆ Icc (-(L * sTwo)) (L * sTwo) := by
  intro x hx
  apply support_wideBump_subset L hL
  rw [Function.mem_support] at hx ⊢
  intro h0
  apply hx
  unfold modulatedBump
  rw [h0, zero_mul]

theorem modulatedBump_contDiff (L ζ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (modulatedBump L ζ) := by
  unfold modulatedBump
  apply ContDiff.mul
  · exact Complex.ofRealCLM.contDiff.comp ((phiN_contDiff_top 2).comp (contDiff_id.div_const L))
  · exact Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)

/-- The modulated wide bump as a smooth interior source at the wide-bump aperture. -/
def modulatedBumpSource (L : ℝ) (hL : 1 ≤ L) (ζ : ℝ) :
    CCMComplexSmoothInteriorSource (wideBumpAperture L hL) where
  toFun := modulatedBump L ζ
  smooth := modulatedBump_contDiff L ζ
  hasCompactSupport :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc
      (support_modulatedBump_subset L hL ζ)
  tsupport_subset := by
    refine (closure_minimal (support_modulatedBump_subset L hL ζ) isClosed_Icc).trans ?_
    have := sTwo_pos
    exact Icc_subset_Ioo (by show -(L * sTwo + 1) < -(L * sTwo); linarith)
      (by show L * sTwo < L * sTwo + 1; linarith)

/-! ## The transform of the modulated bump -/

theorem paperFT_modulatedBump {L : ℝ} (hL : 0 < L) (ζ : ℝ) (z : ℂ) :
    Zeta23.paperFT (modulatedBump L ζ) z =
      (L : ℂ) * Zeta23.paperFT phiTwoC ((L : ℂ) * (z + ζ)) := by
  unfold Zeta23.paperFT modulatedBump phiTwoC
  have hL0 : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
  have hfun : (fun x : ℝ => (phiN 2 (x / L) : ℂ) * Complex.exp (Complex.I * ζ * x) *
      Complex.exp (Complex.I * z * x)) =
      fun x : ℝ => (fun v : ℝ => (phiN 2 v : ℂ) *
        Complex.exp (Complex.I * ((L : ℂ) * (z + ζ)) * v)) (x / L) := by
    funext x
    simp only
    rw [mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast
    field_simp
    ring
  rw [hfun, Measure.integral_comp_div
    (fun v : ℝ => (phiN 2 v : ℂ) * Complex.exp (Complex.I * ((L : ℂ) * (z + ζ)) * v)) L,
    abs_of_pos hL, Complex.real_smul]

/-- The cubic decay constant of the base bump transform. -/
def kappaThree : ℝ := Real.exp (1 / 5) * (1081 / 780) ^ 3

theorem kappaThree_pos : 0 < kappaThree := by unfold kappaThree; positivity

theorem norm_paperFT_phiTwoC_real_le {t : ℝ} (ht : t ≠ 0) :
    ‖Zeta23.paperFT phiTwoC (t : ℂ)‖ ≤ kappaThree / |t| ^ 3 := by
  have h := norm_paperFT_phiN_le 2 (z := (t : ℂ)) (by exact_mod_cast ht) (by simp)
  rw [Complex.norm_real, Real.norm_eq_abs] at h
  unfold kappaThree phiTwoC
  refine h.trans (le_of_eq ?_)
  rw [div_pow]
  ring

theorem norm_paperFT_modulatedBump_le {L : ℝ} (hL : 1 ≤ L) {ζ r : ℝ} (hr : r + ζ ≠ 0) :
    ‖Zeta23.paperFT (modulatedBump L ζ) (r : ℂ)‖ ≤ kappaThree / (L ^ 2 * |r + ζ| ^ 3) := by
  have hLpos : 0 < L := by linarith
  rw [paperFT_modulatedBump hLpos, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hLpos]
  have hcast : ((L : ℂ) * ((r : ℂ) + (ζ : ℂ))) = ((L * (r + ζ) : ℝ) : ℂ) := by push_cast; ring
  rw [hcast]
  have hne : L * (r + ζ) ≠ 0 := mul_ne_zero hLpos.ne' hr
  have h := norm_paperFT_phiTwoC_real_le hne
  have hab : 0 < |r + ζ| := abs_pos.mpr hr
  calc L * ‖Zeta23.paperFT phiTwoC ((L * (r + ζ) : ℝ) : ℂ)‖
      ≤ L * (kappaThree / |L * (r + ζ)| ^ 3) := by gcongr
    _ = kappaThree / (L ^ 2 * |r + ζ| ^ 3) := by
        rw [abs_mul, abs_of_pos hLpos, mul_pow]
        field_simp

/-! ## The zero side at real spectral points -/

/-- At a real spectral point the ray product of the derivative test is the squared modulus of the
transform of the source. -/
theorem rayCoef_product_derivative_eq_normSq {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (q : XiZeroCopy) (hq : (xiSpectralPoint q).im = 0) :
    suzukiTestRayCoefBar u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q *
        suzukiTestRayCoef u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q /
          xiSpectralPoint q ^ 2 =
      ((‖Zeta23.paperFT (u : ℝ → ℂ) (-xiSpectralPoint q)‖ ^ 2 : ℝ) : ℂ) := by
  set γ : ℂ := xiSpectralPoint q with hγ
  have hγ0 : γ ≠ 0 := xiSpectralPoint_ne_zero q
  have hγre : γ = ((γ.re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simp [hq]
  have hu1 : ContDiff ℝ 1 (u : ℝ → ℂ) := u.smooth.of_le (by exact_mod_cast le_top)
  have hus : HasCompactSupport (u : ℝ → ℂ) := u.hasCompactSupport
  have hcoe : (u.toSuzukiSmoothCompactTest.toDerivativeZeroMean : ℝ → ℂ) = deriv (u : ℝ → ℂ) := rfl
  have hcoef : suzukiTestRayCoef u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q =
      testTransform (deriv (u : ℝ → ℂ)) (-γ) := by
    rw [suzukiTestRayCoef_eq_integral, hcoe]
    unfold testTransform
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [mul_comm]
    congr 2
    ring
  have hbar : suzukiTestRayCoefBar u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q =
      (starRingEnd ℂ) (suzukiTestRayCoef u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q) := by
    rw [suzukiTestRayCoefBar_eq_integral, suzukiTestRayCoef_eq_integral, ← integral_conj]
    refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
    simp only
    rw [map_mul, ← Complex.exp_conj]
    congr 2
    rw [← hγ, hγre]
    simp [Complex.conj_I]
  have hibp := testTransform_ibp hu1 hus (-γ)
  have hd : testTransform (deriv (u : ℝ → ℂ)) (-γ) =
      testTransform (u : ℝ → ℂ) (-γ) * (Complex.I * γ) := by
    linear_combination hibp
  have hT : testTransform (u : ℝ → ℂ) (-γ) = Zeta23.paperFT (u : ℝ → ℂ) (-γ) := rfl
  rw [hbar, hcoef, hd, hT]
  have hP : (starRingEnd ℂ) (Zeta23.paperFT (u : ℝ → ℂ) (-γ)) * Zeta23.paperFT (u : ℝ → ℂ) (-γ) =
      ((‖Zeta23.paperFT (u : ℝ → ℂ) (-γ)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  have hconjγ : (starRingEnd ℂ) γ = γ := Complex.conj_eq_iff_im.mpr hq
  rw [map_mul, map_mul, Complex.conj_I, hconjγ]
  rw [div_eq_iff (pow_ne_zero 2 hγ0), ← hP]
  linear_combination (-((starRingEnd ℂ) (Zeta23.paperFT (u : ℝ → ℂ) (-γ)) *
    Zeta23.paperFT (u : ℝ → ℂ) (-γ) * γ ^ 2)) * Complex.I_sq

/-- Under real spectral points the source quadratic of a smooth interior source is the sum of the
squared moduli of its transform at the negated spectral points. -/
theorem ccmRestrictedWeilSourceQuadratic_eq_tsum_normSq_of_real
    (hreal : ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0)
    {a : SuzukiPositiveAperture} (u : CCMComplexSmoothInteriorSource a) :
    ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector =
      ∑' q : XiZeroCopy, ‖Zeta23.paperFT (u : ℝ → ℂ) (-xiSpectralPoint q)‖ ^ 2 := by
  rw [ccmRestrictedWeilSourceQuadratic_toCCMFormVector_eq_smoothForm, suzukiScrewSmoothForm_eq_tsum]
  have hterm : ∀ q : XiZeroCopy,
      suzukiTestRayCoefBar u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q *
        suzukiTestRayCoef u.toSuzukiSmoothCompactTest.toDerivativeZeroMean q /
          xiSpectralPoint q ^ 2 =
      ((‖Zeta23.paperFT (u : ℝ → ℂ) (-xiSpectralPoint q)‖ ^ 2 : ℝ) : ℂ) :=
    fun q => rayCoef_product_derivative_eq_normSq u q (hreal q)
  rw [tsum_congr hterm, ← Complex.ofReal_tsum, Complex.ofReal_re]

/-! ## The zero side of the modulated bump -/

theorem normSq_paperFT_modulatedBump_le_of_real {L : ℝ} (hL : 1 ≤ L) {ζ : ℝ}
    (hζ : |ζ| ≤ 31 / 10) (q : XiZeroCopy) (hq : (xiSpectralPoint q).im = 0) :
    ‖Zeta23.paperFT (modulatedBump L ζ) (-xiSpectralPoint q)‖ ^ 2 ≤
      kappaThree ^ 2 * 16384 / 1681 / L ^ 4 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  set r : ℝ := (xiSpectralPoint q).re with hr
  have hz : -xiSpectralPoint q = ((-r : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [hr]
    · simp [hq]
  have hnormsq : ‖xiSpectralPoint q‖ ^ 2 = r ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hq, hr]
    ring
  have hr2 : 41 / 2 < r ^ 2 := by
    rw [← hnormsq]
    exact fortyOne_div_two_lt_normSq_spectralPoint q
  have habsr : 4134 / 1000 ≤ |r| := by
    have h1 : (4134 / 1000 : ℝ) ^ 2 < |r| ^ 2 := by rw [sq_abs]; linarith
    have h2 : 0 ≤ |r| := abs_nonneg r
    nlinarith
  have hζr : |r| / 4 ≤ |-r + ζ| := by
    have h1 : |-r| - |-ζ| ≤ |-r - -ζ| := abs_sub_abs_le_abs_sub (-r) (-ζ)
    rw [abs_neg, abs_neg, sub_neg_eq_add] at h1
    linarith
  have hne : -r + ζ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hζr
    linarith
  rw [hz]
  have hb := norm_paperFT_modulatedBump_le hL (r := -r) hne
  have hpos : 0 < |-r + ζ| := abs_pos.mpr hne
  have hrpos : 0 < |r| := by linarith
  have hkey : 1 / |r| ^ 6 ≤ 4 / 1681 * (1 / r ^ 2) := by
    have h6 : |r| ^ 6 = r ^ 2 * (r ^ 2) ^ 2 := by
      rw [show (6 : ℕ) = 2 * 3 by norm_num, pow_mul, sq_abs]
      ring
    have h4 : (41 / 2 : ℝ) ^ 2 ≤ (r ^ 2) ^ 2 := by gcongr
    have hr2pos : 0 < r ^ 2 := by linarith
    rw [h6, div_le_iff₀ (by positivity)]
    have hid : 4 / 1681 * (1 / r ^ 2) * (r ^ 2 * (r ^ 2) ^ 2) = 4 / 1681 * (r ^ 2) ^ 2 := by
      field_simp
    rw [hid]
    nlinarith [h4]
  calc ‖Zeta23.paperFT (modulatedBump L ζ) ((-r : ℝ) : ℂ)‖ ^ 2
      ≤ (kappaThree / (L ^ 2 * |-r + ζ| ^ 3)) ^ 2 := by gcongr
    _ ≤ (kappaThree / (L ^ 2 * (|r| / 4) ^ 3)) ^ 2 := by
        have hk := kappaThree_pos
        gcongr
    _ = kappaThree ^ 2 * 4096 / L ^ 4 * (1 / |r| ^ 6) := by
        field_simp
        ring
    _ ≤ kappaThree ^ 2 * 4096 / L ^ 4 * (4 / 1681 * (1 / r ^ 2)) := by
        have hk := kappaThree_pos
        gcongr
    _ = kappaThree ^ 2 * 16384 / 1681 / L ^ 4 * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        rw [hnormsq]
        ring

/-- The zero-side constant of the modulated bump. -/
def zeroSideConstant : ℝ := kappaThree ^ 2 * 16384 / 1681 * (33 / 100)

theorem zeroSideConstant_pos : 0 < zeroSideConstant := by
  unfold zeroSideConstant
  have := kappaThree_pos
  positivity

theorem tsum_normSq_paperFT_modulatedBump_le
    (hreal : ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0)
    {L : ℝ} (hL : 1 ≤ L) {ζ : ℝ} (hζ : |ζ| ≤ 31 / 10) :
    ∑' q : XiZeroCopy, ‖Zeta23.paperFT (modulatedBump L ζ) (-xiSpectralPoint q)‖ ^ 2 ≤
      zeroSideConstant / L ^ 4 := by
  have hsum : Summable (fun q : XiZeroCopy =>
      kappaThree ^ 2 * 16384 / 1681 / L ^ 4 * (1 / ‖xiSpectralPoint q‖ ^ 2)) :=
    xiSpectralPoint_inv_sq_summable.mul_left _
  have hle : ∀ q : XiZeroCopy,
      ‖Zeta23.paperFT (modulatedBump L ζ) (-xiSpectralPoint q)‖ ^ 2 ≤
        kappaThree ^ 2 * 16384 / 1681 / L ^ 4 * (1 / ‖xiSpectralPoint q‖ ^ 2) :=
    fun q => normSq_paperFT_modulatedBump_le_of_real hL hζ q (hreal q)
  have hsum' : Summable (fun q : XiZeroCopy =>
      ‖Zeta23.paperFT (modulatedBump L ζ) (-xiSpectralPoint q)‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun q => by positivity) hle hsum
  have hL4 : 0 < L ^ 4 := by positivity
  have hk := kappaThree_pos
  calc ∑' q : XiZeroCopy, ‖Zeta23.paperFT (modulatedBump L ζ) (-xiSpectralPoint q)‖ ^ 2
      ≤ ∑' q : XiZeroCopy, kappaThree ^ 2 * 16384 / 1681 / L ^ 4 * (1 / ‖xiSpectralPoint q‖ ^ 2) :=
        Summable.tsum_le_tsum hle hsum' hsum
    _ = kappaThree ^ 2 * 16384 / 1681 / L ^ 4 * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 :=
        tsum_mul_left
    _ ≤ kappaThree ^ 2 * 16384 / 1681 / L ^ 4 * (33 / 100) := by
        gcongr
        exact tsum_inv_normSq_spectralPoint_lt.le
    _ = zeroSideConstant / L ^ 4 := by
        unfold zeroSideConstant
        ring

/-! ## The correlation of the modulated bump with its translates -/

/-- The overlap of the wide bump with its translate by `h`. -/
def bumpOverlap (L h : ℝ) : ℝ := ∫ x : ℝ, phiN 2 ((x + h) / L) * phiN 2 (x / L)

theorem norm_logTranslationCLM_apply (h : ℝ) (f : SoninL2) : ‖logTranslationCLM h f‖ = ‖f‖ :=
  LinearIsometry.norm_map (MellinL2.additiveTranslationUnitary h).toLinearIsometry f

theorem inner_logTranslation_modulatedBump (f : SoninL2) {L ζ : ℝ}
    (hf : (f : ℝ → ℂ) =ᵐ[volume] modulatedBump L ζ) (h : ℝ) :
    inner ℂ (logTranslationCLM h f) f =
      Complex.exp (-(Complex.I * ζ * h)) * ((bumpOverlap L h : ℝ) : ℂ) := by
  rw [L2.inner_def]
  have hT := logTranslationCLM_ae h f
  have hshift : (fun x : ℝ => (f : ℝ → ℂ) (x + h)) =ᵐ[volume] fun x => modulatedBump L ζ (x + h) :=
    (measurePreserving_add_right volume h).quasiMeasurePreserving.ae_eq_comp hf
  have hpt : (fun x : ℝ => inner ℂ ((logTranslationCLM h f : ℝ → ℂ) x) ((f : ℝ → ℂ) x)) =ᵐ[volume]
      fun x : ℝ => Complex.exp (-(Complex.I * ζ * h)) *
        ((phiN 2 ((x + h) / L) * phiN 2 (x / L) : ℝ) : ℂ) := by
    filter_upwards [hT, hshift, hf] with x h1 h2 h3
    rw [h1, h2, h3, RCLike.inner_apply]
    unfold modulatedBump
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    have hc : (starRingEnd ℂ) (Complex.I * ζ * ((x + h : ℝ) : ℂ)) =
        -(Complex.I * ζ * ((x + h : ℝ) : ℂ)) := by
      simp [Complex.conj_I]
    rw [hc]
    push_cast
    have hexp : Complex.exp (-(Complex.I * ζ * ((x : ℂ) + (h : ℂ)))) *
        Complex.exp (Complex.I * ζ * (x : ℂ)) = Complex.exp (-(Complex.I * ζ * h)) := by
      rw [← Complex.exp_add]
      congr 1
      ring
    linear_combination ((phiN 2 ((x + h) / L) : ℂ) * (phiN 2 (x / L) : ℂ)) * hexp
  rw [integral_congr_ae hpt, integral_const_mul, integral_complex_ofReal]
  rfl

theorem bumpOverlap_neg (L h : ℝ) : bumpOverlap L (-h) = bumpOverlap L h := by
  unfold bumpOverlap
  have hsub := integral_add_right_eq_self (μ := volume)
    (fun x : ℝ => phiN 2 ((x + -h) / L) * phiN 2 (x / L)) h
  rw [← hsub]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [mul_comm]
  congr 2
  ring

theorem re_inner_symmetric_modulatedBump (f : SoninL2) {L ζ : ℝ}
    (hf : (f : ℝ → ℂ) =ᵐ[volume] modulatedBump L ζ) (h : ℝ) :
    (inner ℂ (logTranslationCLM h f) f + inner ℂ (logTranslationCLM (-h) f) f).re =
      2 * Real.cos (ζ * h) * bumpOverlap L h := by
  rw [inner_logTranslation_modulatedBump f hf h, inner_logTranslation_modulatedBump f hf (-h),
    bumpOverlap_neg]
  have hre : ∀ s : ℝ, (Complex.exp (-(Complex.I * ζ * s)) * ((bumpOverlap L h : ℝ) : ℂ)).re =
      Real.cos (ζ * s) * bumpOverlap L h := by
    intro s
    have hcast : -(Complex.I * ζ * s) = ((-(ζ * s) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [hcast, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
      Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  rw [Complex.add_re, hre h, hre (-h), mul_neg, Real.cos_neg]
  ring

/-! ## A lower bound for the overlap -/

theorem exists_lipschitz_phiTwo : ∃ M : ℝ, 0 ≤ M ∧
    ∀ s t : ℝ, |phiN 2 s - phiN 2 t| ≤ M * |s - t| := by
  have hd : Continuous (deriv (phiN 2)) := (phiN_contDiff_top 2).continuous_deriv (by simp)
  have hcs : HasCompactSupport (deriv (phiN 2)) := (phiN_hasCompactSupport 2).deriv
  obtain ⟨M, hM⟩ := hd.bounded_above_of_compact_support hcs
  refine ⟨max M 0, le_max_right _ _, fun s t => ?_⟩
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := phiN 2) (s := Set.univ) (C := max M 0)
    (fun x _ => ((phiN_contDiff_top 2).differentiable (by simp)) x)
    (fun x _ => (hM x).trans (le_max_left M 0)) convex_univ (Set.mem_univ t) (Set.mem_univ s)
  simpa [Real.norm_eq_abs] using this

theorem bumpOverlap_ge {L : ℝ} (hL : 0 < L) (h : ℝ) {M : ℝ}
    (hM : ∀ s t : ℝ, |phiN 2 s - phiN 2 t| ≤ M * |s - t|) :
    L * (∫ x, phiN 2 x ^ 2) - M * |h| ≤ bumpOverlap L h := by
  unfold bumpOverlap
  have hsub : ∫ x : ℝ, phiN 2 ((x + h) / L) * phiN 2 (x / L) =
      L * ∫ v : ℝ, phiN 2 (v + h / L) * phiN 2 v := by
    have := Measure.integral_comp_div (fun v : ℝ => phiN 2 (v + h / L) * phiN 2 v) L
    rw [abs_of_pos hL, smul_eq_mul] at this
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    congr 2
    field_simp
  rw [hsub]
  have hpt : ∀ v : ℝ, phiN 2 v ^ 2 - M * |h / L| * phiN 2 v ≤ phiN 2 (v + h / L) * phiN 2 v := by
    intro v
    have h1 := hM (v + h / L) v
    have h2 : |(v + h / L) - v| = |h / L| := by congr 1; ring
    rw [h2] at h1
    have hnn := phiN_nonneg 2 v
    have h3 : phiN 2 v - M * |h / L| ≤ phiN 2 (v + h / L) := by
      have := (abs_le.mp h1).1
      linarith
    nlinarith [hnn, h3]
  have hint1 : Integrable (fun v : ℝ => phiN 2 v ^ 2 - M * |h / L| * phiN 2 v) :=
    (integrable_phiN_sq 2).sub ((integrable_phiN 2).const_mul _)
  have hint2 : Integrable (fun v : ℝ => phiN 2 (v + h / L) * phiN 2 v) := by
    have hc : Continuous (fun v : ℝ => phiN 2 (v + h / L) * phiN 2 v) :=
      ((phiN_contDiff_top 2).continuous.comp (continuous_id.add continuous_const)).mul
        (phiN_contDiff_top 2).continuous
    exact hc.integrable_of_hasCompactSupport ((phiN_hasCompactSupport 2).mul_left)
  have hmono := integral_mono hint1 hint2 hpt
  rw [integral_sub (integrable_phiN_sq 2) ((integrable_phiN 2).const_mul _), integral_const_mul,
    integral_phiN, mul_one] at hmono
  have habs : |h / L| = |h| / L := by rw [abs_div, abs_of_pos hL]
  rw [habs] at hmono
  have hL0 : L ≠ 0 := hL.ne'
  calc L * (∫ x, phiN 2 x ^ 2) - M * |h| = L * ((∫ x, phiN 2 x ^ 2) - M * (|h| / L)) := by
        rw [mul_sub, show L * (M * (|h| / L)) = M * |h| by field_simp]
    _ ≤ L * ∫ v : ℝ, phiN 2 (v + h / L) * phiN 2 v := mul_le_mul_of_nonneg_left hmono hL.le

/-! ## The literal family and the bounded perturbation estimate -/

/-- The literal remainders as an aperture-compatible family. -/
def literalFamily : CCMRemainderFamily where
  B a := ccmRestrictedWeilBoundedRemainder a
  selfAdjoint a := ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a
  compat := by
    intro a b hab u v hvu
    exact literal_diagonal_eq_of_val_eq hab hvu

theorem literalFamily_energy (a : SuzukiPositiveAperture) :
    literalFamily.energy a = ccmRestrictedWeilGroundEnergy a := rfl

/-- A family whose quadratic form exceeds another's by at most `δ` times the Hilbert mass has ground
energy at most `δ` larger. -/
theorem CCMRemainderFamily.energy_le_energy_add_of_Q_le (F G : CCMRemainderFamily)
    (a : SuzukiPositiveAperture) {δ : ℝ}
    (h : ∀ u : CCMArchimedeanFormDomain a,
      G.Q a u ≤ F.Q a u + δ * ‖ccmArchimedeanFormToAperture a u‖ ^ 2) :
    G.energy a ≤ F.energy a + δ := by
  refine le_of_forall_pos_lt_add fun η hη => ?_
  obtain ⟨u, hJu, hray⟩ := F.exists_smoothRayleigh_lt_energy_add a hη
  have hmass : 0 < ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 :=
    pow_pos (norm_pos_iff.mpr hJu) 2
  have h1 := G.energy_mul_formNorm_sq_le a u.toCCMFormVector
  have h2 := h u.toCCMFormVector
  have h3 : G.energy a ≤ F.rayleigh a u.toCCMFormVector + δ := by
    have hprod : G.energy a * ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 ≤
        (F.rayleigh a u.toCCMFormVector + δ) *
          ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 := by
      rw [CCMRemainderFamily.rayleigh, add_mul, div_mul_cancel₀ _ hmass.ne']
      linarith
    exact le_of_mul_le_mul_right hprod hmass
  linarith

theorem abs_re_inner_insertedBlock_le (a : SuzukiPositiveAperture) (x w : ℝ) (hx : 0 < x)
    (f : suzukiApertureHilbert a) :
    |(inner ℂ (ccmInsertedBlock a x w f) f).re| ≤ |w| * (2 / Real.sqrt x) * ‖f‖ ^ 2 := by
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  by_cases hvis : x ≤ Real.exp (2 * a.1)
  · rw [re_inner_insertedBlock_eq a x w f hvis]
    have hb : ∀ h : ℝ, ‖inner ℂ (logTranslationCLM h f.1) f.1‖ ≤ ‖f‖ ^ 2 := by
      intro h
      calc ‖inner ℂ (logTranslationCLM h f.1) f.1‖
          ≤ ‖logTranslationCLM h f.1‖ * ‖f.1‖ := norm_inner_le_norm _ _
        _ = ‖f‖ ^ 2 := by rw [norm_logTranslationCLM_apply, Submodule.norm_coe]; ring
    have h1 : |(inner ℂ (logTranslationCLM (Real.log x) f.1) f.1 +
        inner ℂ (logTranslationCLM (-Real.log x) f.1) f.1).re| ≤ 2 * ‖f‖ ^ 2 := by
      calc |(inner ℂ (logTranslationCLM (Real.log x) f.1) f.1 +
            inner ℂ (logTranslationCLM (-Real.log x) f.1) f.1).re|
          ≤ ‖inner ℂ (logTranslationCLM (Real.log x) f.1) f.1 +
            inner ℂ (logTranslationCLM (-Real.log x) f.1) f.1‖ := Complex.abs_re_le_norm _
        _ ≤ ‖inner ℂ (logTranslationCLM (Real.log x) f.1) f.1‖ +
            ‖inner ℂ (logTranslationCLM (-Real.log x) f.1) f.1‖ := norm_add_le _ _
        _ ≤ ‖f‖ ^ 2 + ‖f‖ ^ 2 := add_le_add (hb _) (hb _)
        _ = 2 * ‖f‖ ^ 2 := by ring
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / Real.sqrt x)]
    calc |w| * (1 / Real.sqrt x) * |(inner ℂ (logTranslationCLM (Real.log x) f.1) f.1 +
            inner ℂ (logTranslationCLM (-Real.log x) f.1) f.1).re|
        ≤ |w| * (1 / Real.sqrt x) * (2 * ‖f‖ ^ 2) := by gcongr
      _ = |w| * (2 / Real.sqrt x) * ‖f‖ ^ 2 := by ring
  · rw [ccmInsertedBlock_of_invisible a w hvis]
    simp only [zero_apply, inner_zero_left, Complex.zero_re, abs_zero]
    positivity

theorem insertedFamily_Q_le (x w : ℝ) (hx : 0 < x) (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    (insertedFamily x w).Q a u ≤
      literalFamily.Q a u + |w| * (2 / Real.sqrt x) * ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  rw [CCMRemainderFamily.Q_eq_form_re, CCMRemainderFamily.Q_eq_form_re]
  show (inner ℂ u u + inner ℂ ((ccmRestrictedWeilBoundedRemainder a - ccmInsertedBlock a x w)
      (ccmArchimedeanFormToAperture a u)) (ccmArchimedeanFormToAperture a u)).re ≤
    (inner ℂ u u + inner ℂ (ccmRestrictedWeilBoundedRemainder a (ccmArchimedeanFormToAperture a u))
      (ccmArchimedeanFormToAperture a u)).re + _
  rw [sub_apply, inner_sub_left, Complex.add_re, Complex.add_re, Complex.sub_re]
  have hb := abs_re_inner_insertedBlock_le a x w hx (ccmArchimedeanFormToAperture a u)
  have := neg_abs_le (inner ℂ (ccmInsertedBlock a x w (ccmArchimedeanFormToAperture a u))
    (ccmArchimedeanFormToAperture a u)).re
  linarith

/-- The inserted ground energy exceeds the literal one by at most the operator norm of the
inserted block. -/
theorem ccmInsertedGroundEnergy_le_literal_add (a : SuzukiPositiveAperture) (x w : ℝ)
    (hx : 0 < x) :
    ccmInsertedGroundEnergy a x w ≤ ccmRestrictedWeilGroundEnergy a + |w| * (2 / Real.sqrt x) := by
  rw [← insertedFamily_energy, ← literalFamily_energy]
  exact CCMRemainderFamily.energy_le_energy_add_of_Q_le literalFamily (insertedFamily x w) a
    (insertedFamily_Q_le x w hx a)

/-! ## Failure of the Riemann hypothesis: the literal ground energy is unbounded below -/

theorem exists_ccmRestrictedWeilGroundEnergy_lt_of_not_riemannHypothesis
    (hRH : ¬ RiemannHypothesis) {C : ℝ} (hC : 0 ≤ C) :
    ∃ a : SuzukiPositiveAperture, ccmRestrictedWeilGroundEnergy a < -C := by
  by_contra hcon
  simp only [not_exists, not_lt] at hcon
  apply hRH
  apply riemannHypothesis_of_polarGroundEnergy_subexponential
  intro ε hε
  refine ⟨C, hC, fun B => ?_⟩
  have h1 : -C ≤ ccmRestrictedWeilGroundEnergy B := hcon B
  have h2 := ccmRestrictedWeilGroundEnergy_le_polar B
  have h3 : -(C * Real.exp (ε * B.1)) ≤ -C := by
    have : 1 ≤ Real.exp (ε * B.1) := Real.one_le_exp (by have := B.2; positivity)
    nlinarith
  linarith

/-! ## The Riemann hypothesis branch: the modulated bump has negative Rayleigh quotient -/

theorem ccmInsertedGroundEnergy_neg_of_riemannHypothesis (hRH : RiemannHypothesis) {x : ℝ}
    (hx : 1 < x) {ζ : ℝ} (hζ : |ζ| ≤ 31 / 10) {w : ℝ}
    (hwc : 0 < w * Real.cos (ζ * Real.log x)) :
    ∃ a : SuzukiPositiveAperture, ccmInsertedGroundEnergy a x w < 0 := by
  have hreal : ∀ q : XiZeroCopy, (xiSpectralPoint q).im = 0 :=
    xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH
  obtain ⟨M, hM0, hM⟩ := exists_lipschitz_phiTwo
  have hlogpos : 0 < Real.log x := Real.log_pos hx
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
  set c₂ : ℝ := ∫ v, phiN 2 v ^ 2 with hc₂
  have hc₂pos : 0 < c₂ := by
    have := integral_phiN_sq_ge 2
    have := sN_pos 2
    have h0 : 0 < 1 / (2 * sN 2) := by positivity
    linarith
  set κ : ℝ := w * Real.cos (ζ * Real.log x) * (2 / Real.sqrt x) with hκ
  have hκpos : 0 < κ := mul_pos hwc (by positivity)
  set C : ℝ := zeroSideConstant with hC
  have hCpos : 0 < C := zeroSideConstant_pos
  set L : ℝ := max (max 1 (Real.log x)) (max (2 * M * Real.log x / c₂) (2 * C / (κ * c₂) + 1))
    with hLdef
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) (le_max_left _ _)
  have hLlog : Real.log x ≤ L := le_trans (le_max_right _ _) (le_max_left _ _)
  have hLM : 2 * M * Real.log x / c₂ ≤ L := le_trans (le_max_left _ _) (le_max_right _ _)
  have hLC : 2 * C / (κ * c₂) + 1 ≤ L := le_trans (le_max_right _ _) (le_max_right _ _)
  have hLpos : 0 < L := by linarith
  refine ⟨wideBumpAperture L hL1, ?_⟩
  set a := wideBumpAperture L hL1 with ha
  set u := modulatedBumpSource L hL1 ζ with hu
  have hvis : x ≤ Real.exp (2 * a.1) := by
    rw [← Real.log_le_iff_le_exp (by linarith)]
    show Real.log x ≤ 2 * (L * sTwo + 1)
    have := sTwo_pos
    have hs : 1 ≤ sTwo := by rw [sTwo_val]; norm_num
    nlinarith
  have hfloor := ccmInsertedGroundEnergy_mul_formNorm_sq_le a x w u.toCCMFormVector
  have hQ : ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector ≤ C / L ^ 4 := by
    rw [ccmRestrictedWeilSourceQuadratic_eq_tsum_normSq_of_real hreal u]
    exact tsum_normSq_paperFT_modulatedBump_le hreal hL1 hζ
  have hfae : ((ccmArchimedeanFormToAperture a u.toCCMFormVector : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      modulatedBump L ζ := u.toCCMFormVector_physical_coeFn
  have hblock : (inner ℂ (ccmInsertedBlock a x w (ccmArchimedeanFormToAperture a u.toCCMFormVector))
      (ccmArchimedeanFormToAperture a u.toCCMFormVector)).re =
      κ * bumpOverlap L (Real.log x) := by
    rw [re_inner_insertedBlock_eq a x w _ hvis, re_inner_symmetric_modulatedBump _ hfae, hκ]
    ring
  have hover : c₂ * L / 2 ≤ bumpOverlap L (Real.log x) := by
    have h1 : L * c₂ - M * |Real.log x| ≤ bumpOverlap L (Real.log x) :=
      bumpOverlap_ge hLpos (Real.log x) hM
    rw [abs_of_pos hlogpos] at h1
    have h2 : 2 * M * Real.log x ≤ c₂ * L := by
      rw [div_le_iff₀ hc₂pos] at hLM
      linarith
    linarith
  have hneg : ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector -
      (inner ℂ (ccmInsertedBlock a x w (ccmArchimedeanFormToAperture a u.toCCMFormVector))
        (ccmArchimedeanFormToAperture a u.toCCMFormVector)).re < 0 := by
    rw [hblock]
    have hL4 : C / L ^ 4 ≤ C := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 ≤ L ^ 4 := one_le_pow₀ hL1
      nlinarith
    have hbig : 2 * C < κ * c₂ * L := by
      have hkc : 0 < κ * c₂ := mul_pos hκpos hc₂pos
      have hLC' : 2 * C / (κ * c₂) ≤ L - 1 := by linarith
      rw [div_le_iff₀ hkc] at hLC'
      nlinarith
    have hκover : κ * (c₂ * L / 2) ≤ κ * bumpOverlap L (Real.log x) :=
      mul_le_mul_of_nonneg_left hover hκpos.le
    linarith
  have hprod : ccmInsertedGroundEnergy a x w *
      ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 < 0 := lt_of_le_of_lt hfloor hneg
  by_contra hge
  rw [not_lt] at hge
  have : 0 ≤ ccmInsertedGroundEnergy a x w *
      ‖ccmArchimedeanFormToAperture a u.toCCMFormVector‖ ^ 2 := mul_nonneg hge (by positivity)
  linarith

/-! ## Negativity for every nonzero weight -/

/-- **Any weight of the right sign at a chosen modulation frequency gives negative ground energy.**
For `x > 1`, `|ζ| ≤ 31/10` and `w cos(ζ log x) > 0`, the inserted ground energy is negative at some
aperture. -/
theorem exists_ccmInsertedGroundEnergy_neg_of_cos_pos {x : ℝ} (hx : 1 < x) {ζ : ℝ}
    (hζ : |ζ| ≤ 31 / 10) {w : ℝ} (hwc : 0 < w * Real.cos (ζ * Real.log x)) :
    ∃ a : SuzukiPositiveAperture, ccmInsertedGroundEnergy a x w < 0 := by
  by_cases hRH : RiemannHypothesis
  · exact ccmInsertedGroundEnergy_neg_of_riemannHypothesis hRH hx hζ hwc
  · have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr (by linarith)
    obtain ⟨a, ha⟩ := exists_ccmRestrictedWeilGroundEnergy_lt_of_not_riemannHypothesis hRH
      (C := |w| * (2 / Real.sqrt x)) (by positivity)
    exact ⟨a, by linarith [ccmInsertedGroundEnergy_le_literal_add a x w (by linarith)]⟩

/-- **Inserting any positive weight at any scale `x > 1` gives negative ground energy.** -/
theorem exists_ccmInsertedGroundEnergy_neg_of_pos {x : ℝ} (hx : 1 < x) {w : ℝ} (hw : 0 < w) :
    ∃ a : SuzukiPositiveAperture, ccmInsertedGroundEnergy a x w < 0 :=
  exists_ccmInsertedGroundEnergy_neg_of_cos_pos hx (ζ := 0) (by norm_num) (by simpa using hw)

/-- **Removing any positive weight at any scale `x ≥ 2` gives negative ground energy.** -/
theorem exists_ccmInsertedGroundEnergy_neg_of_neg {x : ℝ} (hx : 2 ≤ x) {w : ℝ} (hw : w < 0) :
    ∃ a : SuzukiPositiveAperture, ccmInsertedGroundEnergy a x w < 0 := by
  have hlog2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hl2 := Real.log_two_gt_d9
  have hlogpos : 0 < Real.log x := by linarith
  have hπ := Real.pi_lt_d2
  have hπ0 := Real.pi_pos
  set ζ : ℝ := 2 * Real.pi / (3 * Real.log x) with hζdef
  have hζpos : 0 < ζ := by positivity
  have hζ : |ζ| ≤ 31 / 10 := by
    rw [abs_of_pos hζpos, hζdef, div_le_iff₀ (by positivity)]
    nlinarith
  have hcos : Real.cos (ζ * Real.log x) = -(1 / 2) := by
    have h23 : ζ * Real.log x = Real.pi - Real.pi / 3 := by
      rw [hζdef]
      field_simp
      ring
    rw [h23, Real.cos_pi_sub, Real.cos_pi_div_three]
  exact exists_ccmInsertedGroundEnergy_neg_of_cos_pos (by linarith) hζ (by rw [hcos]; linarith)

/-! ## Zero crossings for every nonzero weight -/

theorem exists_inserted_zero_crossing_of_exists_neg {x w : ℝ} (hx : 1 < x)
    (hneg : ∃ a : SuzukiPositiveAperture, ccmInsertedGroundEnergy a x w < 0) :
    ∃ a : SuzukiPositiveAperture, ccmInsertedGroundEnergy a x w = 0 ∧
      ∃ y : ((insertedFamily x w).operator a).domain,
        (y : suzukiApertureHilbert a) ≠ 0 ∧ (insertedFamily x w).operator a y = 0 := by
  obtain ⟨δ, hδ, hpos⟩ := exists_small_aperture_ccmInsertedGroundEnergy_pos hx w
  obtain ⟨a₁, hneg⟩ := hneg
  let a₀ : SuzukiPositiveAperture := ⟨min (δ / 2) a₁.1, lt_min (by linarith) a₁.2⟩
  have h01 : a₀.1 ≤ a₁.1 := min_le_right _ _
  have h0 : 0 < (insertedFamily x w).energy a₀ := by
    rw [insertedFamily_energy]
    exact hpos a₀ (lt_of_le_of_lt (min_le_left _ _) (by linarith))
  have h1 : (insertedFamily x w).energy a₁ < 0 := by
    rw [insertedFamily_energy]
    exact hneg
  obtain ⟨a, -, -, hzero⟩ := (insertedFamily x w).exists_energy_eq_zero h01 h0 h1
  refine ⟨a, by rw [← insertedFamily_energy]; exact hzero, ?_⟩
  exact (insertedFamily x w).exists_kernel_of_energy_eq_zero hzero

/-- **Every nonzero change of the prime weight at a scale `x ≥ 2` forces a zero crossing.**  The
restricted Weil operator with `w·x^{-1/2}(τ_{log x} + τ_{-log x})` added to its prime block, `w ≠ 0`,
has a zero ground energy with a nonzero kernel element at some aperture. -/
theorem exists_inserted_zero_crossing_of_ne_zero {x : ℝ} (hx : 2 ≤ x) {w : ℝ} (hw : w ≠ 0) :
    ∃ a : SuzukiPositiveAperture, ccmInsertedGroundEnergy a x w = 0 ∧
      ∃ y : ((insertedFamily x w).operator a).domain,
        (y : suzukiApertureHilbert a) ≠ 0 ∧ (insertedFamily x w).operator a y = 0 := by
  apply exists_inserted_zero_crossing_of_exists_neg (by linarith)
  rcases lt_or_gt_of_ne hw with hneg | hpos
  · exact exists_ccmInsertedGroundEnergy_neg_of_neg hx hneg
  · exact exists_ccmInsertedGroundEnergy_neg_of_pos (by linarith) hpos

/-- **Every positive insertion at any scale `x > 1` forces a zero crossing.** -/
theorem exists_inserted_zero_crossing_of_pos {x : ℝ} (hx : 1 < x) {w : ℝ} (hw : 0 < w) :
    ∃ a : SuzukiPositiveAperture, ccmInsertedGroundEnergy a x w = 0 ∧
      ∃ y : ((insertedFamily x w).operator a).domain,
        (y : suzukiApertureHilbert a) ≠ 0 ∧ (insertedFamily x w).operator a y = 0 :=
  exists_inserted_zero_crossing_of_exists_neg hx (exists_ccmInsertedGroundEnergy_neg_of_pos hx hw)

/-- **Reducing the weight of any prime by any positive amount forces a zero crossing.**  For every
prime `p` and every `ε > 0`, the restricted Weil operator whose prime block carries the weight
`log p − ε` at `p` instead of `log p` has a zero ground energy with a nonzero kernel element at
some aperture. -/
theorem exists_partial_deletion_zero_crossing {p : ℕ} (hp : p.Prime) {ε : ℝ} (hε : 0 < ε) :
    ∃ a : SuzukiPositiveAperture, ccmInsertedGroundEnergy a p (-ε) = 0 ∧
      ∃ y : ((insertedFamily p (-ε)).operator a).domain,
        (y : suzukiApertureHilbert a) ≠ 0 ∧ (insertedFamily p (-ε)).operator a y = 0 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  exact exists_inserted_zero_crossing_of_ne_zero h2 (neg_ne_zero.mpr hε.ne')

end RHTower.WeilDeletion

end
