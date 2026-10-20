import GaloisForLFunctions.ArithmeticCriticalityTheory.ShortProfilePoleFreeVariationInequality
import GaloisForLFunctions.ArithmeticCriticalityTheory.NonnegativeConeZeroFormCriterion
import GaloisForLFunctions.RHTower.PoleVanishingWeilPositivityPrimeTwo
import GaloisForLFunctions.RHTower.CCMZetaWeilSmoothIdentity
import GaloisForLFunctions.RHTower.CCMRestrictedWeilPolarGroundEnergy

/-!
# The variation inequality on mean-zero profiles, past the prime 2

On the ground-state family the zeros are visible only on `μ_a`-mean-zero profiles
(`profileMoment a u = 0`): there the pole term of the variation inequality vanishes, and the odd test
`m_a u` has both pole moments `∫ m_a u e^{±x/2}` equal to zero. Such tests are exactly the
pole-vanishing vectors of the restricted Weil form of Connes–Consani–Moscovici, whose ground energy
`μ₀(A)` on the aperture `[−A, A]` is bounded below by trace certificates.

* **The pole-vanishing floor for the full zero form** (`polarGroundEnergy_mul_le_fullZeroForm`). For
  every real smooth `F` supported inside `(−A, A)` with `∫ F cosh(x/2) = ∫ F sinh(x/2) = 0`,
  `μ₀(A) ∫ F² ≤ Ẑ(F)`. The CCM quadratic of a smooth source is `Re W_ζ` of that source, and on real
  tests `Re W_ζ` is the full zero form.
* **The mean-zero variation inequality** (`reflectedDifferenceEnergy_add_le_poleFree_of_meanZero`). For
  every shift `a > 0` and every smooth even `μ_a`-mean-zero profile `u` supported inside `(−A, A)`,
  `D_a(u) + μ₀(A) ∫ (m_a u)² ≤ 2 S_a(u) + V_a(u)`.
* **Two explicit regimes.** Profiles on `[−1/3, 1/3]` (test support of length `2/3 < log 2`, no prime
  enters) have margin `1/10` (`…_of_support_le_third`); profiles on `[−7/20, 7/20]` (length
  `7/10 > log 2`, the prime `2` enters the form) have margin `1/20` (`…_of_support_le_seven_twentieths`).

Against the short-profile theorem (`reflectedDifferenceEnergy_add_le_poleFree_of_support_le`, all
profiles on `[−21/200, 21/200]`), the mean-zero sector reaches `10/3` times further and is the first
region of the frontier inequality in which a prime contributes.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The squared `L²` norm is the integral of the squared pointwise norm. -/
theorem soninL2_norm_sq_eq_integral (g : SoninL2) :
    ‖g‖ ^ 2 = ∫ x : ℝ, ‖(g : ℝ → ℂ) x‖ ^ 2 := by
  have h2 := MeasureTheory.L2.inner_def (𝕜 := ℂ) g g
  rw [inner_self_eq_norm_sq_to_K] at h2
  have hpoint : ∀ x : ℝ, inner ℂ ((g : ℝ → ℂ) x) ((g : ℝ → ℂ) x) =
      ((‖(g : ℝ → ℂ) x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  simp_rw [hpoint] at h2
  rw [integral_complex_ofReal] at h2
  exact Complex.ofReal_injective (by rw [Complex.ofReal_pow]; exact h2)

/-- A real smooth test supported inside the aperture, as a smooth interior source. -/
def realInteriorSource (A : SuzukiPositiveAperture) {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFc : HasCompactSupport F) (hFs : tsupport F ⊆ Ioo (-A.1) A.1) :
    CCMComplexSmoothInteriorSource A where
  toFun x := (F x : ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp hF
  hasCompactSupport := hFc.comp_left Complex.ofReal_zero
  tsupport_subset := (tsupport_comp_subset Complex.ofReal_zero F).trans hFs

section Floor

variable (A : SuzukiPositiveAperture) {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
  (hFc : HasCompactSupport F) (hFs : tsupport F ⊆ Ioo (-A.1) A.1)

/-- The CCM quadratic of a real smooth source is its full zero form. -/
theorem ccmRestrictedWeilSourceQuadratic_realInteriorSource :
    ccmRestrictedWeilSourceQuadratic A (realInteriorSource A hF hFc hFs).toCCMFormVector =
      fullZeroForm F := by
  have hv2 : ContDiff ℝ 2 fun x => (F x : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (hF.of_le (WithTop.coe_le_coe.mpr le_top))
  rw [ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil]
  change (zetaZeroConfig.W (fun x => (F x : ℂ)) (fun x => (F x : ℂ))).re = _
  rw [zeta_W_eq_weilFullFunctional hv2 (hFc.comp_left Complex.ofReal_zero),
    GaloisForLFunctions.ArithmeticPositivityTheory.fullZeroForm_eq_re_weilFullFunctional hF.continuous
      hFc]

/-- The aperture norm of a real smooth source is its `L²` norm. -/
theorem norm_sq_realInteriorSource :
    ‖ccmArchimedeanFormToAperture A (realInteriorSource A hF hFc hFs).toCCMFormVector‖ ^ 2 =
      ∫ x, F x ^ 2 := by
  change ‖(ccmArchimedeanFormToAperture A (realInteriorSource A hF hFc hFs).toCCMFormVector :
    SoninL2)‖ ^ 2 = _
  rw [soninL2_norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [(realInteriorSource A hF hFc hFs).toCCMFormVector_physical_coeFn] with x hx
  rw [hx]
  change ‖(F x : ℂ)‖ ^ 2 = F x ^ 2
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The pole coefficients of a real smooth source are its exponential moments. -/
theorem inner_ccmPolarApertureVector_realInteriorSource (s : ℝ) :
    inner ℂ (ccmPolarApertureVector A s)
        (ccmArchimedeanFormToAperture A (realInteriorSource A hF hFc hFs).toCCMFormVector) =
      ((∫ x, F x * Real.exp (s * x) : ℝ) : ℂ) := by
  rw [inner_ccmPolarApertureVector_ccmComplexSmoothFormVector, ← integral_complex_ofReal]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  change (Real.exp (s * x) : ℂ) * (F x : ℂ) = _
  push_cast
  ring

include hF hFc hFs in
/-- **The pole-vanishing floor for the full zero form.** -/
theorem polarGroundEnergy_mul_le_fullZeroForm (hC : evenPoleMoment F = 0)
    (hS : oddPoleMoment F = 0) :
    ccmRestrictedWeilPolarGroundEnergy A * ∫ x, F x ^ 2 ≤ fullZeroForm F := by
  have hplus : (∫ x, F x * Real.exp (1 / 2 * x)) = 0 := by
    have h := expHalfMoment_eq hF.continuous hFc
    unfold expHalfMoment at h
    simp only [show ∀ x : ℝ, 1 / 2 * x = x / 2 from fun x => by ring]
    rw [h, hC, hS, add_zero]
  have hminus : (∫ x, F x * Real.exp (-1 / 2 * x)) = 0 := by
    have h := expNegHalfMoment_eq hF.continuous hFc
    unfold expNegHalfMoment at h
    simp only [show ∀ x : ℝ, -1 / 2 * x = -(x / 2) from fun x => by ring]
    rw [h, hC, hS, sub_zero]
  have hpol : IsPolarConstrained A (realInteriorSource A hF hFc hFs).toCCMFormVector := by
    refine ⟨?_, ?_⟩
    · rw [inner_ccmPolarApertureVector_realInteriorSource, hplus, Complex.ofReal_zero]
    · rw [inner_ccmPolarApertureVector_realInteriorSource, hminus, Complex.ofReal_zero]
  have h := ccmRestrictedWeilPolarGroundEnergy_mul_le A _ hpol
  rwa [norm_sq_realInteriorSource, ccmRestrictedWeilSourceQuadratic_realInteriorSource] at h

end Floor

/-! ### The mean-zero sector of the ground-state family -/

section MeanZero

variable {a : ℝ} {u : ℝ → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) (huc : HasCompactSupport u)
  (heven : ∀ x, u (-x) = u x) (hmean : profileMoment a u = 0)

theorem phiDoobTest_shiftedGroundState_eq (a : ℝ) (u : ℝ → ℝ) :
    phiDoobTest (fun y => shiftedGroundState a y * u y) = fun x => shiftDifference a x * u x :=
  funext fun x => by
    unfold phiDoobTest shiftedGroundState
    field_simp [(riemannKernelReal_pos x).ne']

include hu huc heven hmean in
/-- **The mean-zero variation inequality**: on `μ_a`-mean-zero smooth even profiles supported inside
`(−A, A)`, the pole-free variation inequality holds with margin `μ₀(A) ∫ (m_a u)²`. -/
theorem reflectedDifferenceEnergy_add_le_poleFree_of_meanZero (ha : 0 < a) (A : SuzukiPositiveAperture)
    (hsupp : tsupport u ⊆ Ioo (-A.1) A.1) :
    reflectedDifferenceEnergy (shiftedGroundState a) u +
        ccmRestrictedWeilPolarGroundEnergy A *
          ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 ≤
      2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u := by
  have hu2 : ContDiff ℝ 2 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  set F := phiDoobTest (fun y => shiftedGroundState a y * u y) with hFdef
  have hFe := phiDoobTest_shiftedGroundState_eq a u
  have hFd : ContDiff ℝ (⊤ : ℕ∞) F := by
    rw [hFdef, hFe]
    exact ((contDiff_riemannKernelReal.comp (contDiff_id.sub contDiff_const)).sub
      (contDiff_riemannKernelReal.comp (contDiff_id.add contDiff_const))).mul hu
  have hFc : HasCompactSupport F := by
    rw [hFdef, hFe]
    exact huc.mul_left
  have hFs : tsupport F ⊆ Ioo (-A.1) A.1 := by
    rw [hFdef, hFe]
    exact (tsupport_mul_subset_right).trans hsupp
  have hodd : ∀ x, F (-x) = -F x := fun x => by
    simp only [hFdef, phiDoobTest]
    rw [riemannKernelReal_neg', shiftedGroundState_neg, heven]
    ring
  have hS : oddPoleMoment F = 0 := by
    rw [hFdef, oddPoleMoment_phiDoob_shiftedGroundState hu.continuous huc heven, hmean, mul_zero]
  have h := polarGroundEnergy_mul_le_fullZeroForm A hFd hFc hFs
    (evenPoleMoment_eq_zero_of_odd hodd) hS
  rw [← zeroForm_eq_fullZeroForm_of_odd hodd, hFdef,
    ← poleFreeForm_eq_zeroForm ha hu2 huc heven] at h
  linarith

include hu huc heven hmean in
/-- **Prime-free regime**: margin `1/10` for mean-zero profiles on `[−1/3, 1/3]`. -/
theorem reflectedDifferenceEnergy_add_le_poleFree_of_support_le_third (ha : 0 < a)
    (hsupp : ∀ x, 1 / 3 < |x| → u x = 0) :
    reflectedDifferenceEnergy (shiftedGroundState a) u +
        1 / 10 * ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 ≤
      2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u := by
  have hlog := Real.log_two_gt_d9
  have hIcc : tsupport u ⊆ Icc (-(1 / 3)) (1 / 3) :=
    closure_minimal (fun x hx => abs_le.mp (not_lt.mp fun h => hx (hsupp x h))) isClosed_Icc
  have hts : tsupport u ⊆ Ioo (-halfLogTwoAperture.1) halfLogTwoAperture.1 := hIcc.trans fun x hx => by
    change x ∈ Ioo (-(Real.log 2 / 2)) (Real.log 2 / 2)
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h := reflectedDifferenceEnergy_add_le_poleFree_of_meanZero hu huc heven hmean ha _ hts
  have hI : 0 ≤ ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  nlinarith [one_tenth_le_ccmRestrictedWeilPolarGroundEnergy_halfLogTwo]

include hu huc heven hmean in
/-- **Past the prime `2`**: margin `1/20` for mean-zero profiles on `[−7/20, 7/20]`, where the test
support has length `7/10 > log 2`. -/
theorem reflectedDifferenceEnergy_add_le_poleFree_of_support_le_seven_twentieths (ha : 0 < a)
    (hsupp : ∀ x, 7 / 20 < |x| → u x = 0) :
    reflectedDifferenceEnergy (shiftedGroundState a) u +
        1 / 20 * ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 ≤
      2 * sameSideEnergy (shiftedGroundState a) u + profileVariance a u := by
  have hlog := Real.log_two_gt_d9
  have hIcc : tsupport u ⊆ Icc (-(7 / 20)) (7 / 20) :=
    closure_minimal (fun x hx => abs_le.mp (not_lt.mp fun h => hx (hsupp x h))) isClosed_Icc
  have hts : tsupport u ⊆ Ioo (-primeTwoAperture.1) primeTwoAperture.1 := hIcc.trans fun x hx => by
    change x ∈ Ioo (-((Real.log 2 + 1 / 50) / 2)) ((Real.log 2 + 1 / 50) / 2)
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h := reflectedDifferenceEnergy_add_le_poleFree_of_meanZero hu huc heven hmean ha _ hts
  have hI : 0 ≤ ∫ x, phiDoobTest (fun y => shiftedGroundState a y * u y) x ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  nlinarith [one_twentieth_le_ccmRestrictedWeilPolarGroundEnergy_primeTwo]

end MeanZero

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
