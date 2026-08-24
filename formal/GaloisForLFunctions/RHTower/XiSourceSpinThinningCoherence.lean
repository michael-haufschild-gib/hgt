import GaloisForLFunctions.RHTower.FrankensteinGammaCompositionScaleZeroDescent
import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureBalance
import GaloisForLFunctions.HTGeometry.ConstitutiveExchangeableFormationSelection

open Complex

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-!
# Xi source spin and thinning coherence

The literal theta source is a half-density spinor: one full logarithmic turn multiplies it by
`-1`.  Coupling it to the actual centered Xi character exposes an additional Hurwitz monodromy.
This module proves that preserving the ambient theta spin sector is exactly reporter-faithful
three-slot thinning coherence.

The first theta atom is nonzero, so this comparison cannot be made true by observing only the
vanishing Xi value.  The resulting coherence is equivalent to descent of the centered logarithmic
character and to isometry of the first nonzero Xi multiplicity jet.  Globally it is equivalent to
RH.  Thus the remaining source theorem has a precise topological form: a closed Xi error fibre must
inherit the ambient theta spin sector.
-/

/-- The actual centered Xi logarithmic character coupled to one literal theta source atom. -/
def xiCenteredThetaDeformedSourceTerm
    (rho : XiDivisorSupport) (z : ℂ) (n : ℕ) : ℂ :=
  xiCenteredLogCharacter rho z * thetaCuspComplexSourceTerm z n

/-- A complex phase reported by its two coefficient-faithful real coordinates. -/
def complexPhaseReporter (z : ℂ) : Bool → ℝ
  | false => z.re
  | true => z.im

theorem complexPhaseReporter_injective : Function.Injective complexPhaseReporter := by
  intro z w h
  apply Complex.ext
  · exact congrFun h false
  · exact congrFun h true

/-- The centered deformation changes the theta half-density spin by exactly the centered
Hurwitz monodromy. -/
theorem xiCenteredThetaDeformedSourceTerm_add_two_pi_I
    (rho : XiDivisorSupport) (z : ℂ) (n : ℕ) :
    xiCenteredThetaDeformedSourceTerm rho
        (z + 2 * (Real.pi : ℂ) * Complex.I) n =
      -(HurwitzOrbit.monoScalar (primeDepthBVWoldXiCenteredRate rho : ℂ)) *
        xiCenteredThetaDeformedSourceTerm rho z n := by
  rw [xiCenteredThetaDeformedSourceTerm,
    xiCenteredLogCharacter_add_two_pi_I,
    thetaCuspComplexSourceTerm_add_two_pi_I,
    xiCenteredThetaDeformedSourceTerm]
  ring

/-- Preservation of the ambient theta half-density spin sector by the centered Xi deformation. -/
def XiCenteredThetaSpinCoherent (rho : XiDivisorSupport) : Prop :=
  ∀ z : ℂ, ∀ n : ℕ,
    xiCenteredThetaDeformedSourceTerm rho
        (z + 2 * (Real.pi : ℂ) * Complex.I) n =
      -xiCenteredThetaDeformedSourceTerm rho z n

/-- Reporterwise three-slot thinning between actual centered monodromy and the neutral ambient
theta spin. -/
def XiCenteredThetaSpinThinningCoherent (rho : XiDivisorSupport) : Prop :=
  PhaseAveragedThinningConsistent
    (complexPhaseReporter
      (HurwitzOrbit.monoScalar (primeDepthBVWoldXiCenteredRate rho : ℂ)))
    (complexPhaseReporter 1)

theorem xiCenteredThetaSpinThinningCoherent_iff_monoScalar_eq_one
    (rho : XiDivisorSupport) :
    XiCenteredThetaSpinThinningCoherent rho ↔
      HurwitzOrbit.monoScalar (primeDepthBVWoldXiCenteredRate rho : ℂ) = 1 := by
  rw [XiCenteredThetaSpinThinningCoherent,
    phaseAveragedThinningConsistent_iff_laws_eq]
  exact ⟨fun h => complexPhaseReporter_injective h,
    fun h => congrArg complexPhaseReporter h⟩

/-- The literal theta atom supplies a noncensoring source reporter at the modular seam. -/
theorem thetaCuspComplexSourceTerm_zero_one_ne_zero :
    thetaCuspComplexSourceTerm 0 1 ≠ 0 := by
  have hpos : 0 < thetaCuspSourceTerm 0 1 :=
    thetaCuspSourceTerm_one_zero_pos
  rw [show (0 : ℂ) = ((0 : ℝ) : ℂ) by norm_num,
    thetaCuspComplexSourceTerm_ofReal]
  exact_mod_cast hpos.ne'

theorem xiCenteredThetaSpinCoherent_iff_monoScalar_eq_one
    (rho : XiDivisorSupport) :
    XiCenteredThetaSpinCoherent rho ↔
      HurwitzOrbit.monoScalar (primeDepthBVWoldXiCenteredRate rho : ℂ) = 1 := by
  constructor
  · intro h
    have hspin := h 0 1
    rw [xiCenteredThetaDeformedSourceTerm_add_two_pi_I] at hspin
    have hterm : xiCenteredThetaDeformedSourceTerm rho 0 1 ≠ 0 := by
      simpa [xiCenteredThetaDeformedSourceTerm, xiCenteredLogCharacter] using
        thetaCuspComplexSourceTerm_zero_one_ne_zero
    have hfactor :
        (HurwitzOrbit.monoScalar (primeDepthBVWoldXiCenteredRate rho : ℂ) - 1) *
          xiCenteredThetaDeformedSourceTerm rho 0 1 = 0 := by
      linear_combination -hspin
    exact sub_eq_zero.mp ((mul_eq_zero.mp hfactor).resolve_right hterm)
  · intro hmono z n
    rw [xiCenteredThetaDeformedSourceTerm_add_two_pi_I, hmono, neg_mul, one_mul]

/-- Source spin preservation and reporter-faithful thinning are the same condition. -/
theorem xiCenteredThetaSpinCoherent_iff_thinningCoherent
    (rho : XiDivisorSupport) :
    XiCenteredThetaSpinCoherent rho ↔
      XiCenteredThetaSpinThinningCoherent rho := by
  rw [xiCenteredThetaSpinCoherent_iff_monoScalar_eq_one,
    xiCenteredThetaSpinThinningCoherent_iff_monoScalar_eq_one]

/-- Three-slot thinning is exactly descent through the complex logarithmic cover. -/
theorem xiCenteredThetaSpinThinningCoherent_iff_logCharacterDescends
    (rho : XiDivisorSupport) :
    XiCenteredThetaSpinThinningCoherent rho ↔
      XiCenteredLogCharacterDescends rho := by
  rw [xiCenteredThetaSpinThinningCoherent_iff_monoScalar_eq_one]
  constructor
  · intro hmono L
    rw [xiCenteredLogCharacter_add_two_pi_I, hmono, one_mul]
  · intro hdesc
    have hzero := hdesc 0
    rw [xiCenteredLogCharacter_add_two_pi_I] at hzero
    simpa [xiCenteredLogCharacter] using hzero

/-- The open critical strip turns spin-sector coherence into exact horizontal neutrality. -/
theorem xiCenteredThetaSpinThinningCoherent_iff_re_eq_half
    (rho : XiDivisorSupport) :
    XiCenteredThetaSpinThinningCoherent rho ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [xiCenteredThetaSpinThinningCoherent_iff_logCharacterDescends,
    xiCenteredLogCharacterDescends_iff_centeredRate_eq_zero,
    primeDepthBVWoldXiCenteredRate_eq_zero_iff]

/-- Phase-thinning coherence is the unit-circle continuation of the already constructed
noncensoring terminal-multiplicity-jet descent. -/
theorem xiCenteredThetaSpinThinningCoherent_iff_terminalMultiplicityJetDescends
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    XiCenteredThetaSpinThinningCoherent rho ↔
      FrankensteinXiPrimeThetaTerminalMultiplicityJetDescendsAt p rho := by
  rw [xiCenteredThetaSpinThinningCoherent_iff_re_eq_half,
    frankensteinXiPrimeThetaTerminalMultiplicityJetDescendsAt_iff]

/-- Proposition that the complete Xi divisor inherits ambient theta spin under three-slot
thinning. -/
def EveryXiCenteredThetaSpinThinningCoherent : Prop :=
  ∀ rho : XiDivisorSupport, XiCenteredThetaSpinThinningCoherent rho

/-- Exact global audit: spin-sector thinning inheritance is sufficient for RH and, on the actual
Xi divisor, equivalent to it.  Missing upstream theorem is inheritance of ambient theta spin by a
closed Xi error fibre, not another separating reporter. -/
theorem everyXiCenteredThetaSpinThinningCoherent_iff_riemannHypothesis :
    EveryXiCenteredThetaSpinThinningCoherent ↔ RiemannHypothesis := by
  rw [← everyFrankensteinXiTwoOrientationUnitalScaleZeroDescends_iff_riemannHypothesis]
  unfold EveryXiCenteredThetaSpinThinningCoherent
    EveryFrankensteinXiTwoOrientationUnitalScaleZeroDescends
  apply forall_congr'
  intro rho
  rw [xiCenteredThetaSpinThinningCoherent_iff_re_eq_half,
    frankensteinXiTwoOrientationUnitalScaleZeroDescendsAt_iff]

end

end RHTower
