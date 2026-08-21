import GaloisForLFunctions.HTGeometry.NoOutsideOperationalSquareCausality
import GaloisForLFunctions.HTGeometry.SeibergWittenAbelianSpinor

/-!
# Causal-spin-flip complement of a finite Seiberg--Witten invariant

The corpus's antilinear two-channel spin flip sends a spinor outer square to its adjugate. Applied
to the finite Seiberg--Witten invariant, it gives a second exact curvature equation whose direct
and complementary curvature records annihilate one another and add to a scalar identity. Both
records are invariant under the common gauge phase and retain the same scalar time/Born weight.

This produces a finite algebraic polarity pair of curvature records. It does not choose a physical
causal orientation or turn the pair into two continuum Seiberg--Witten solutions on a manifold.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Finite Seiberg--Witten invariant of the antilinear causal-spin-flipped spinor. -/
def seibergWittenCausalComplement (psi : SeibergWittenSpinor) : SeibergWittenCurvature :=
  seibergWittenInvariant (causalSpinFlip psi)

/-- The complementary finite invariant is the adjugate of the direct invariant. -/
theorem seibergWittenCausalComplement_eq_adjugate (psi : SeibergWittenSpinor) :
    seibergWittenCausalComplement psi = (seibergWittenInvariant psi).adjugate :=
  higgsSpinorEventMatrix_causalSpinFlip_eq_adjugate psi

/-- The complementary record solves the finite curvature equation for the flipped spinor. -/
theorem seibergWittenCausalComplement_solvesEquation (psi : SeibergWittenSpinor) :
    seibergWittenEquation (seibergWittenCausalComplement psi) (causalSpinFlip psi) :=
  seibergWittenEquation_inducedCurvature _

/-- Direct and complementary finite curvature records mutually annihilate. -/
theorem seibergWittenInvariant_mul_causalComplement_eq_zero (psi : SeibergWittenSpinor) :
    seibergWittenInvariant psi * seibergWittenCausalComplement psi = 0 :=
  higgsSpinorEventMatrix_mul_causalSpinFlip_eq_zero psi

/-- The direct and complementary records resolve a scalar identity. -/
theorem seibergWittenInvariant_add_causalComplement (psi : SeibergWittenSpinor) :
    seibergWittenInvariant psi + seibergWittenCausalComplement psi =
      ((twoSpinorNormSq psi : ℂ) • (1 : SeibergWittenCurvature)) :=
  higgsSpinorEventMatrix_add_spinFlip_eq_smul_one psi

/-- The complementary record is invariant under every common gauge phase. -/
theorem seibergWittenCausalComplement_gaugeInvariant (u : Circle) (psi : SeibergWittenSpinor) :
    seibergWittenCausalComplement (u • psi) = seibergWittenCausalComplement psi := by
  rw [seibergWittenCausalComplement_eq_adjugate,
    seibergWittenCausalComplement_eq_adjugate,
    seibergWittenInvariant_gaugeInvariant]

/-- The causal-spin-flip complement preserves the scalar time/Born-weight coordinate. -/
theorem seibergWittenCausalComplement_time (psi : SeibergWittenSpinor) :
    higgsSpinorTime (causalSpinFlip psi) = higgsSpinorTime psi :=
  higgsSpinorTime_causalSpinFlip psi

/-- The direct and complementary records can be distinct even with equal scalar weight. -/
theorem seibergWittenCausalComplement_ne_at_north :
    seibergWittenInvariant causalPolarityNorthSpinor ≠
      seibergWittenCausalComplement causalPolarityNorthSpinor :=
  higgsSpinorEventMatrix_causalSpinFlip_ne_at_north

end GaloisForLFunctions.HTGeometry
