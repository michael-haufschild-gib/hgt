import GaloisForLFunctions.RHTower.ThetaCuspHawkingBifurcationSchwarzianTiltRigidity
import GaloisForLFunctions.RHTower.SuzukiLagariasMeromorphicInner
import GaloisForLFunctions.RHTower.SlabFullWidthAdmissibility

/-!
# Optical-cusp scattering incidence for theta Hawking sectors

For the modular surface `PSL₂(ℤ)\ℍ`, the Eisenstein constant term has scattering coefficient

`phi(s) = Lambda(2*s - 1) / Lambda(2*s)`.

Since `xi(u) = u*(u-1)*Lambda(u)/2`, removing the elementary kinematic gauge `s/(s-1)` gives
the normalized coefficient `xi(2*s-1)/xi(2*s)`.  In the resonance coordinate

`s(z) = 1/4 + I*z/2`,

this is exactly

`S_cusp(z) = XiC(z + I) / XiC(z)`.

This module formalizes that literature formula in the corpus coordinate and proves the missing
divisor incidence.  Every actual Xi divisor point `z` is a genuine negative-meromorphic-order pole
of `S_cusp`, because `XiC z = 0` while the shifted numerator is outside the critical strip and is
nonzero.  The functional-equation shadow `-z-I` is a regular analytic zero.  Thus the divisor is
not a source-dressed all-pass zero: it is a pole/zero pair of an actual automorphic scattering
coefficient.

Combining this incidence with the exact Davies--Fulling bifurcation theorem gives an unconditional
classification: a Xi divisor lies on the critical line, or it is a genuine optical-cusp resonance
pole whose reflected theta Hawking mirrors have unequal Schwarzian flux at some safe coupling.

**[LITERATURE-FORMALIZED]** The modular Eisenstein scattering formula is classical.  Near-horizon
optical geometry of nonextremal black holes is asymptotically hyperbolic (Gibbons--Warnick,
arXiv:0809.1571), and hyperbolic black-hole/BTZ work relates Selberg scattering divisors to QNMs
(Aros--Diaz, arXiv:0910.0029; Keeler--Martin--Svesko, arXiv:1811.08433, arXiv:1910.07607).

**[PAPER-PROVED] [LEAN-PROVED]** Pole/zero incidence, shadow inversion, resonance-coordinate law,
and the critical-or-pole-with-flux-asymmetry classification below are unconditional.

**[OPEN CORE]** No result here derives the exact arithmetic quotient `PSL₂(ℤ)\ℍ` from four-
dimensional Einstein--Klein--Gordon/Teukolsky evolution.  The RH-bearing producer remains a
black-hole dynamics theorem forcing the arithmetic optical channel and converting every off-line
pole/flux asymmetry into forbidden horizon mass memory or unavoidable cross-sector mixing.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Numerator of normalized modular Eisenstein scattering in the Xi resonance coordinate. -/
def thetaCuspHawkingOpticalCuspNumerator (z : ℂ) : ℂ :=
  XiC (z + Complex.I)

/-- Denominator of normalized modular Eisenstein scattering in the Xi resonance coordinate. -/
def thetaCuspHawkingOpticalCuspDenominator (z : ℂ) : ℂ :=
  XiC z

/-- Pole-filled normalization of the scalar modular cusp scattering coefficient. -/
def thetaCuspHawkingOpticalCuspScattering (z : ℂ) : ℂ :=
  thetaCuspHawkingOpticalCuspNumerator z /
    thetaCuspHawkingOpticalCuspDenominator z

/-- Functional-equation shadow induced by `s ↦ 1-s` in the `z` coordinate. -/
def thetaCuspHawkingOpticalCuspShadow (z : ℂ) : ℂ :=
  -z - Complex.I

/-- Automorphic resonance parameter for a centered Xi spectral coordinate. -/
def thetaCuspHawkingOpticalCuspResonanceParameter (z : ℂ) : ℂ :=
  (1 / 4 : ℂ) + Complex.I * z / 2

/-- The scattering denominator is exactly `xi(2s)` in resonance coordinates. -/
lemma thetaCuspHawkingOpticalCuspDenominator_eq_xi (z : ℂ) :
    thetaCuspHawkingOpticalCuspDenominator z =
      xi (2 * thetaCuspHawkingOpticalCuspResonanceParameter z) := by
  unfold thetaCuspHawkingOpticalCuspDenominator
    thetaCuspHawkingOpticalCuspResonanceParameter XiC
  congr 1
  ring

/-- The scattering numerator is exactly `xi(2s-1)` in resonance coordinates. -/
lemma thetaCuspHawkingOpticalCuspNumerator_eq_xi (z : ℂ) :
    thetaCuspHawkingOpticalCuspNumerator z =
      xi (2 * thetaCuspHawkingOpticalCuspResonanceParameter z - 1) := by
  unfold thetaCuspHawkingOpticalCuspNumerator
    thetaCuspHawkingOpticalCuspResonanceParameter XiC
  congr 1
  rw [add_mul, Complex.I_mul_I]
  ring

/-- Xi tilt is exactly displacement of the automorphic resonance decay rate from `1/4`. -/
lemma thetaCuspHawkingOpticalCuspResonanceParameter_re (z : ℂ) :
    (thetaCuspHawkingOpticalCuspResonanceParameter z).re =
      1 / 4 - z.im / 2 := by
  simp [thetaCuspHawkingOpticalCuspResonanceParameter]
  ring

/-- The automorphic scattering shadow is an involution. -/
lemma thetaCuspHawkingOpticalCuspShadow_involutive (z : ℂ) :
    thetaCuspHawkingOpticalCuspShadow
        (thetaCuspHawkingOpticalCuspShadow z) = z := by
  simp [thetaCuspHawkingOpticalCuspShadow]

/-- Functional-equation shadow exchanges scattering numerator with denominator. -/
lemma thetaCuspHawkingOpticalCuspNumerator_shadow (z : ℂ) :
    thetaCuspHawkingOpticalCuspNumerator
        (thetaCuspHawkingOpticalCuspShadow z) =
      thetaCuspHawkingOpticalCuspDenominator z := by
  unfold thetaCuspHawkingOpticalCuspNumerator
    thetaCuspHawkingOpticalCuspShadow
    thetaCuspHawkingOpticalCuspDenominator
  rw [show -z - Complex.I + Complex.I = -z by ring, XiC_even]

/-- Functional-equation shadow exchanges scattering denominator with numerator. -/
lemma thetaCuspHawkingOpticalCuspDenominator_shadow (z : ℂ) :
    thetaCuspHawkingOpticalCuspDenominator
        (thetaCuspHawkingOpticalCuspShadow z) =
      thetaCuspHawkingOpticalCuspNumerator z := by
  unfold thetaCuspHawkingOpticalCuspDenominator
    thetaCuspHawkingOpticalCuspShadow
    thetaCuspHawkingOpticalCuspNumerator
  rw [show -z - Complex.I = -(z + Complex.I) by ring, XiC_even]

/-- Away from its divisor, normalized cusp scattering obeys exact shadow inversion. -/
lemma thetaCuspHawkingOpticalCuspScattering_shadow_mul
    {z : ℂ}
    (hnum : thetaCuspHawkingOpticalCuspNumerator z ≠ 0)
    (hden : thetaCuspHawkingOpticalCuspDenominator z ≠ 0) :
    thetaCuspHawkingOpticalCuspScattering
        (thetaCuspHawkingOpticalCuspShadow z) *
      thetaCuspHawkingOpticalCuspScattering z = 1 := by
  rw [thetaCuspHawkingOpticalCuspScattering,
    thetaCuspHawkingOpticalCuspNumerator_shadow,
    thetaCuspHawkingOpticalCuspDenominator_shadow,
    thetaCuspHawkingOpticalCuspScattering]
  field_simp

lemma thetaCuspHawkingOpticalCuspNumerator_analyticAt (z : ℂ) :
    AnalyticAt ℂ thetaCuspHawkingOpticalCuspNumerator z := by
  unfold thetaCuspHawkingOpticalCuspNumerator
  change AnalyticAt ℂ (XiC ∘ fun w : ℂ => w + Complex.I) z
  exact (XiC_differentiable.comp
    (by fun_prop : Differentiable ℂ (fun w : ℂ => w + Complex.I))).analyticAt z

lemma thetaCuspHawkingOpticalCuspDenominator_analyticAt (z : ℂ) :
    AnalyticAt ℂ thetaCuspHawkingOpticalCuspDenominator z := by
  unfold thetaCuspHawkingOpticalCuspDenominator
  exact XiC_differentiable.analyticAt z

/-- Every Xi divisor point zeros the scattering denominator. -/
theorem thetaCuspHawkingOpticalCuspDenominator_xiSpectralPoint_eq_zero
    (q : XiZeroCopy) :
    thetaCuspHawkingOpticalCuspDenominator (xiSpectralPoint q) = 0 := by
  exact XiC_xiSpectralPoint_eq_zero q

/-- The unit imaginary shift moves every Xi divisor beyond the strip, so no pole cancels. -/
theorem thetaCuspHawkingOpticalCuspNumerator_xiSpectralPoint_ne_zero
    (q : XiZeroCopy) :
    thetaCuspHawkingOpticalCuspNumerator (xiSpectralPoint q) ≠ 0 := by
  apply SlabFullWidthAdmissibility.XiC_ne_zero_of_half_le_abs_im
  have hstrip := abs_im_xiSpectralPoint_lt_half q
  have hlower : -(1 / 2 : ℝ) < (xiSpectralPoint q).im := (abs_lt.mp hstrip).1
  have hshift : 1 / 2 < (xiSpectralPoint q + Complex.I).im := by
    simp only [add_im, I_im]
    linarith
  rw [abs_of_pos (lt_trans (by norm_num) hshift)]
  exact le_of_lt hshift

/-- **Divisor incidence:** every Xi divisor is a genuine scattering pole, not a zero. -/
theorem thetaCuspHawkingOpticalCusp_xiSpectralPoint_isPole
    (q : XiZeroCopy) :
    meromorphicOrderAt thetaCuspHawkingOpticalCuspScattering
        (xiSpectralPoint q) < 0 := by
  apply meromorphicOrderAt_div_neg_of_analyticAt_num_ne_den_zero
  · exact thetaCuspHawkingOpticalCuspNumerator_analyticAt _
  · exact thetaCuspHawkingOpticalCuspDenominator_analyticAt _
  · exact thetaCuspHawkingOpticalCuspNumerator_xiSpectralPoint_ne_zero q
  · exact thetaCuspHawkingOpticalCuspDenominator_xiSpectralPoint_eq_zero q
  · intro htop
    have hevent : XiC =ᶠ[nhds (xiSpectralPoint q)] 0 :=
      analyticOrderAt_eq_top.mp htop
    have hglobal : AnalyticOnNhd ℂ XiC Set.univ :=
      fun z _ => XiC_differentiable.analyticAt z
    have hzero : Set.EqOn XiC 0 (Set.univ : Set ℂ) :=
      hglobal.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_univ (Set.mem_univ _) hevent
    exact thetaCuspHawkingOpticalCuspNumerator_xiSpectralPoint_ne_zero q
      (hzero (Set.mem_univ (xiSpectralPoint q + Complex.I)))

/-- The functional-equation shadow of every Xi divisor is a regular analytic scattering zero. -/
theorem thetaCuspHawkingOpticalCuspShadow_xiSpectralPoint_isZero
    (q : XiZeroCopy) :
    AnalyticAt ℂ thetaCuspHawkingOpticalCuspScattering
        (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) ∧
      thetaCuspHawkingOpticalCuspScattering
        (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) = 0 := by
  have hnumZero : thetaCuspHawkingOpticalCuspNumerator
      (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) = 0 := by
    rw [thetaCuspHawkingOpticalCuspNumerator_shadow]
    exact thetaCuspHawkingOpticalCuspDenominator_xiSpectralPoint_eq_zero q
  have hdenNe : thetaCuspHawkingOpticalCuspDenominator
      (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) ≠ 0 := by
    rw [thetaCuspHawkingOpticalCuspDenominator_shadow]
    exact thetaCuspHawkingOpticalCuspNumerator_xiSpectralPoint_ne_zero q
  constructor
  · unfold thetaCuspHawkingOpticalCuspScattering
    exact (thetaCuspHawkingOpticalCuspNumerator_analyticAt _).div
      (thetaCuspHawkingOpticalCuspDenominator_analyticAt _) hdenNe
  · unfold thetaCuspHawkingOpticalCuspScattering
    rw [hnumZero]
    exact zero_div _

/-- Every Xi divisor is critical, or is simultaneously an automorphic optical pole and an
off-tilt theta Hawking flux bifurcation. -/
theorem thetaCuspHawkingXiDivisor_criticalOrOpticalPoleWithFluxAsymmetry
    (q : XiZeroCopy) :
    (xiSpectralPoint q).im = 0 ∨
      (meromorphicOrderAt thetaCuspHawkingOpticalCuspScattering
          (xiSpectralPoint q) < 0 ∧
        AnalyticAt ℂ thetaCuspHawkingOpticalCuspScattering
          (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) ∧
        thetaCuspHawkingOpticalCuspScattering
          (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) = 0 ∧
        ∃ lambda : ℝ,
          |lambda| < thetaCuspHawkingBifurcationCommonCouplingRadius
            (xiSpectralPoint q).im ∧
          thetaCuspHawkingSchwarzian (xiSpectralPoint q).im lambda 0 ≠
            thetaCuspHawkingSchwarzian (-(xiSpectralPoint q).im) lambda 0) := by
  by_cases hcritical : (xiSpectralPoint q).im = 0
  · exact Or.inl hcritical
  · right
    refine ⟨thetaCuspHawkingOpticalCusp_xiSpectralPoint_isPole q, ?_⟩
    rcases thetaCuspHawkingOpticalCuspShadow_xiSpectralPoint_isZero q with
      ⟨han, hzero⟩
    refine ⟨han, hzero, ?_⟩
    have hstrip : |(xiSpectralPoint q).im| < 1 := by
      linarith [abs_im_xiSpectralPoint_lt_half q]
    exact exists_thetaCuspHawkingBifurcationSchwarzian_reflection_ne_of_tilt_ne_zero
      hstrip hcritical

end

end RHTower
