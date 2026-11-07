import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePoleSelfEnergyIsSharpBelowTheOnset
import GaloisForLFunctions.SquareRootThreshold.TheRoutesMeasureOneAperture
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPolarSourceCancellation
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilPoleCompression
import GaloisForLFunctions.RHTower.CCM.CCMFiniteTriangleBound
import GaloisForLFunctions.ArithmeticCriticalityTheory.MeanZeroProfileVariationInequalityPastPrimeTwo

/-!
# The pole cross pairing is compressed by the sharp genus below the onset

At aperture `a` let `p_a = e^{x/2} 1_{[−a,a]}` be the positive exponential pole. Its Weil cross
pairing with a real smooth source `F` inside `(−a, a)` is an explicit integral
(`ccmWeilRealPolar_pole_realInteriorSource`):

`Q_a(p_a, F) = ∫_{−a}^{a} P_a(x) F(x) dx`,
`P_a(x) = e^{x/2}(B(a−x, a+x) − (ψ(e^{a−x}) − e^{a−x}) − E_M(a+x)) − (γ + log 2π)e^{x/2} − e^{−a}e^{−x/2}`

(`poleCrossProfile`): the Gamma boundary kernel `B`, the Chebyshev error and the
reciprocal-Mangoldt error, after exact cancellation of the radius and exponential main terms.

* **Two-pole compression** (`sq_integral_poleCrossProfile_le`): window positivity at `a` gives
  `(∫ P_a F)² ≤ D(a) Ẑ(F)`, `D(a)` the pole self-energy.
* **Sharp compression below the onset** (`exists_sq_integral_poleCrossProfile_le_sharp`):
  for `K(2a + 2) ≤ a*(ζ)`, `(∫ P_a F)² ≤ e^{a}(κ₀ + C e^{−a/2}) Ẑ(F)`, with `κ₀ = 2 + γ − log 4π`.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open _root_.Zeta23 _root_.RHTower GaloisForLFunctions.SquareRootThreshold
  GaloisForLFunctions.WindowVisibilityLaw GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticPositivityTheory

/-- The real pole cross profile at aperture `a`: the Weil image of the positive exponential pole,
Gamma boundary kernel minus the Chebyshev and reciprocal-Mangoldt errors, plus the two
constraint-visible exponentials. -/
def poleCrossProfile (a x : ℝ) : ℝ :=
  Real.exp (x / 2) * (ccmGammaPolarBoundary (a - x) (a + x) -
      (Chebyshev.psi (Real.exp (a - x)) - Real.exp (a - x)) - ccmReciprocalMangoldtError (a + x)) +
    ((-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) * Real.exp (x / 2) -
      Real.exp (-a) * Real.exp (-(x / 2)))

/-- Cauchy–Schwarz for a nonnegative restricted Weil form. -/
theorem sq_ccmWeilRealPolar_le_of_groundEnergy_nonneg (a : SuzukiPositiveAperture)
    (hμ : 0 ≤ ccmRestrictedWeilGroundEnergy a) (u v : CCMArchimedeanFormDomain a) :
    ccmWeilRealPolar a u v ^ 2 ≤
      ccmRestrictedWeilSourceQuadratic a u * ccmRestrictedWeilSourceQuadratic a v := by
  have hQ : ∀ w : CCMArchimedeanFormDomain a, 0 ≤ ccmRestrictedWeilSourceQuadratic a w :=
    fun w => (mul_nonneg hμ (sq_nonneg _)).trans
      (ccmRestrictedWeilGroundEnergy_mul_formNorm_sq_le_source a w)
  have hquad : ∀ t : ℝ, 0 ≤ ccmRestrictedWeilSourceQuadratic a u * (t * t) +
      2 * ccmWeilRealPolar a u v * t + ccmRestrictedWeilSourceQuadratic a v := by
    intro t
    have h := hQ ((t : ℂ) • u + ((1 : ℝ) : ℂ) • v + ((0 : ℝ) : ℂ) • u)
    rw [ccmRestrictedWeilSourceQuadratic_real_three] at h
    nlinarith [h]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  nlinarith [hd]

/-- **The pole cross pairing is an explicit integral.** For a real smooth source `F` inside the
aperture, `Q_a(p_a, F) = ∫ 1_{[−a,a]} P_a F`. -/
theorem ccmWeilRealPolar_pole_realInteriorSource (a : SuzukiPositiveAperture) {F : ℝ → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hFs : tsupport F ⊆ Ioo (-a.1) a.1) :
    ccmWeilRealPolar a (ccmPolarFormVector a (1 / 2))
        (realInteriorSource a hF hFc hFs).toCCMFormVector =
      ∫ x, (centralInterval a.1).indicator (poleCrossProfile a.1) x * F x := by
  set v := (realInteriorSource a hF hFc hFs).toCCMFormVector
  -- the real polarization is the real part of the Hermitian form
  have hsymm : ccmRestrictedWeilForm a v (ccmPolarFormVector a (1 / 2)) =
      (starRingEnd ℂ) (ccmRestrictedWeilForm a (ccmPolarFormVector a (1 / 2)) v) := by
    unfold ccmRestrictedWeilForm
    rw [map_add]
    have h1 : inner ℂ v (ccmPolarFormVector a (1 / 2)) =
        (starRingEnd ℂ) (inner ℂ (ccmPolarFormVector a (1 / 2)) v) :=
      (inner_conj_symm v _).symm
    have h2 : inner ℂ (ccmRestrictedWeilBoundedRemainder a (ccmArchimedeanFormToAperture a v))
        (ccmArchimedeanFormToAperture a (ccmPolarFormVector a (1 / 2))) =
        (starRingEnd ℂ) (inner ℂ (ccmRestrictedWeilBoundedRemainder a
          (ccmArchimedeanFormToAperture a (ccmPolarFormVector a (1 / 2))))
            (ccmArchimedeanFormToAperture a v)) := by
      rw [inner_conj_symm (ccmArchimedeanFormToAperture a v)
        (ccmRestrictedWeilBoundedRemainder a
          (ccmArchimedeanFormToAperture a (ccmPolarFormVector a (1 / 2))))]
      exact (ccmRestrictedWeilBoundedRemainder_isSelfAdjoint a).isSymmetric _ _
    rw [h1, h2]
  rw [ccmWeilRealPolar_eq_form, hsymm, Complex.conj_re, ← two_mul,
    mul_div_cancel_left₀ _ (two_ne_zero' ℝ), ccmPolarWeilRepresentative_represents_form]
  -- the representative is the explicit profile
  have hfull := ccmRestrictedWeilOperator_polarPlus_coeFn a
  rw [ccmRestrictedWeilOperator_polar_apply] at hfull
  have hv : ((ccmArchimedeanFormToAperture a v : SoninL2) : ℝ → ℂ) =ᵐ[volume]
      (realInteriorSource a hF hFc hFs) := (realInteriorSource a hF hFc hFs).toCCMFormVector_physical_coeFn
  change (inner ℂ ((ccmPolarWeilRepresentative a (1 / 2) : suzukiApertureHilbert a) : SoninL2)
    ((ccmArchimedeanFormToAperture a v : suzukiApertureHilbert a) : SoninL2)).re = _
  rw [L2.inner_def]
  have hcongr : (fun x => inner ℂ
      (((ccmPolarWeilRepresentative a (1 / 2) : suzukiApertureHilbert a) : SoninL2) x)
      (((ccmArchimedeanFormToAperture a v : suzukiApertureHilbert a) : SoninL2) x)) =ᵐ[volume]
      fun x => (((centralInterval a.1).indicator (poleCrossProfile a.1) x * F x : ℝ) : ℂ) := by
    filter_upwards [hfull, hv] with x h1 h2
    rw [h1, h2]
    change inner ℂ ((centralInterval a.1).indicator _ x) (F x : ℂ) = _
    by_cases hx : x ∈ centralInterval a.1
    · rw [indicator_of_mem hx, indicator_of_mem hx]
      have hre : (realInteriorSource a hF hFc hFs : ℝ → ℂ) x = (F x : ℂ) := rfl
      rw [hre]
      unfold ccmPolarBoundaryArithmeticProfile poleCrossProfile
      rw [← Complex.ofReal_add, RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul]
      congr 1
      ring
    · simp [indicator_of_notMem hx]
  rw [integral_congr_ae hcongr, integral_complex_ofReal, Complex.ofReal_re]

/-- The pole self-energy is the Weil quadratic of the positive pole. -/
theorem ccmRestrictedWeilSourceQuadratic_pole (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilSourceQuadratic a (ccmPolarFormVector a (1 / 2)) = ccmWeilPoleDiagonal a := by
  have h := ccmWeilPoleCompression_quadratic a 1 0
  simp only [one_smul, zero_smul, add_zero, norm_one, norm_zero, one_pow, map_one,
    Complex.zero_re, mul_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at h
  simpa using h

/-- **Two-pole compression.** Window positivity at `a` bounds the pole cross pairing of every real
smooth source by the pole self-energy: `(∫ P_a F)² ≤ D(a) Ẑ(F)`. -/
theorem sq_integral_poleCrossProfile_le (a : SuzukiPositiveAperture) (hW : ZetaWindowPositive a.1)
    {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (hFs : tsupport F ⊆ Ioo (-a.1) a.1) :
    (∫ x, (centralInterval a.1).indicator (poleCrossProfile a.1) x * F x) ^ 2 ≤
      ccmWeilPoleDiagonal a * fullZeroForm F := by
  have hμ := ccmRestrictedWeilGroundEnergy_nonneg_of_zetaWindowPositive a hW
  have h := sq_ccmWeilRealPolar_le_of_groundEnergy_nonneg a hμ (ccmPolarFormVector a (1 / 2))
    (realInteriorSource a hF hFc hFs).toCCMFormVector
  rwa [ccmWeilRealPolar_pole_realInteriorSource, ccmRestrictedWeilSourceQuadratic_pole,
    ccmRestrictedWeilSourceQuadratic_realInteriorSource] at h

/-- **Sharp compression below the onset.** There are `K > 0`, `a₁`, `C ≥ 0` such that at every
aperture `a ≥ 1` with `max(a₁, K(2a + 2)) ≤ a*(ζ)` and every real smooth source `F` inside
`(−a, a)`: `(∫ P_a F)² ≤ e^{a}(κ₀ + C e^{−a/2}) Ẑ(F)`. -/
theorem exists_sq_integral_poleCrossProfile_le_sharp :
    ∃ K a₁ C : ℝ, 0 < K ∧ 0 ≤ C ∧ ∀ a : SuzukiPositiveAperture, 1 ≤ a.1 →
      ((max a₁ (K * (2 * a.1 + 2)) : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig →
      ∀ {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F),
        tsupport F ⊆ Ioo (-a.1) a.1 →
        (∫ x, (centralInterval a.1).indicator (poleCrossProfile a.1) x * F x) ^ 2 ≤
          Real.exp a.1 * (poleSharpConstant + C * Real.exp (-(a.1 / 2))) * fullZeroForm F := by
  obtain ⟨K, a₁, C, hK, hC, hsharp⟩ := exists_abs_poleDiagonal_sharp_of_le_onsetAperture
  set K' : ℝ := max 1 K
  have hK'1 : 1 ≤ K' := le_max_left 1 K
  have hK'K : K ≤ K' := le_max_right 1 K
  refine ⟨K', a₁, C, by positivity, hC, fun a ha hle F hF hFc hFs => ?_⟩
  have h1 : (1 : ℝ) ≤ a.1 := ha
  have hKK' : max a₁ (K * (2 * a.1 + 2)) ≤ max a₁ (K' * (2 * a.1 + 2)) :=
    max_le_max_left a₁ (mul_le_mul_of_nonneg_right hK'K (by linarith))
  have hleK : ((max a₁ (K * (2 * a.1 + 2)) : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig :=
    (EReal.coe_le_coe_iff.mpr hKK').trans hle
  -- window positivity at the aperture itself
  have ha0 : 0 ≤ max a₁ (K' * (2 * a.1 + 2)) :=
    (by positivity : (0 : ℝ) ≤ K' * (2 * a.1 + 2)).trans (le_max_right _ _)
  have hWbig : ZetaWindowPositive (max a₁ (K' * (2 * a.1 + 2))) :=
    (windowPositiveAt_zeta_iff _).mp
      ((windowPositiveAt_iff_le_onsetAperture temperedConfig_zetaZeroConfig ha0).mpr hle)
  have haK : a.1 ≤ max a₁ (K' * (2 * a.1 + 2)) := by
    refine le_trans ?_ (le_max_right _ _)
    nlinarith [hK'1, h1]
  have hW : ZetaWindowPositive a.1 := zetaWindowPositive_antitone haK hWbig
  have hcomp := sq_integral_poleCrossProfile_le a hW hF hFc hFs
  have hZ : 0 ≤ fullZeroForm F :=
    hW F (hF.of_le (WithTop.coe_le_coe.mpr le_top)) hFc fun x hx =>
      image_eq_zero_of_notMem_tsupport fun hmem => by
        have := hFs hmem
        exact absurd (abs_lt.mpr this) (not_lt.mpr hx.le)
  have hD := hsharp a h1 hleK
  have he := Real.exp_pos a.1
  have hDle : ccmWeilPoleDiagonal a ≤
      Real.exp a.1 * (poleSharpConstant + C * Real.exp (-(a.1 / 2))) := by
    have h2 := (abs_le.mp hD).2
    have h3 : ccmWeilPoleDiagonal a / Real.exp a.1 ≤
        poleSharpConstant + C * Real.exp (-(a.1 / 2)) := by linarith
    rw [div_le_iff₀ he] at h3
    linarith
  exact hcomp.trans (mul_le_mul_of_nonneg_right hDle hZ)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
