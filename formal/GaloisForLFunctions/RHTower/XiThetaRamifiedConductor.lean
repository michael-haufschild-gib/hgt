import GaloisForLFunctions.HTGeometry.RamifiedNodeConductor
import GaloisForLFunctions.RHTower.XiThetaNodalConductorDegeneration

/-!
# Multiplicity-faithful Xi conductor coefficient invariants

The Legendre coefficient model uses twice the actual Xi multiplicity as its shear exponent.
Its invariant module has exactly the conductor line over characteristic-zero domains and an
additional coefficient-torsion channel in general. The existing nonzero terminal Xi coefficient
is fixed at the corrected exponent.

No analytic nearby-cycle realization or horizontal arithmetic equivariance is asserted.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- The ramified coefficient model with the Legendre factor two and actual Xi multiplicity. -/
def xiThetaRamifiedCoefficientInvariants (A : Type*) [CommRing A]
    (rho : XiDivisorSupport) : Submodule A (A × A) :=
  ramifiedNodeMonodromyInvariants A (2 * xiSupportMultiplicity rho)

/-- Actual multiplicity determines the entire transverse coefficient-torsion channel. -/
def xiThetaRamifiedCoefficientInvariantEquiv (A : Type*) [CommRing A]
    (rho : XiDivisorSupport) :
    xiThetaRamifiedCoefficientInvariants A rho ≃ₗ[A]
      A × nodeCoefficientTorsion A (2 * xiSupportMultiplicity rho) :=
  ramifiedNodeInvariantEquiv A (2 * xiSupportMultiplicity rho)

/-- Integral and complex coefficients both retain exactly the conductor line. -/
theorem xiThetaConductorSpecialization_range_eq_ramified
    (A : Type*) [CommRing A] [IsDomain A] [CharZero A] (rho : XiDivisorSupport) :
    LinearMap.range (universalNodeConductorSpecialization A) =
      xiThetaRamifiedCoefficientInvariants A rho := by
  rw [xiThetaRamifiedCoefficientInvariants,
    universalNodeConductorSpecialization_range_eq_ramified_iff]
  intro b hb
  have hm : (xiSupportMultiplicity rho : A) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt (xiSupportMultiplicity_pos rho))
  apply (mul_eq_zero.mp hb).resolve_left
  rw [Nat.cast_mul]
  exact mul_ne_zero two_ne_zero hm

/-- Reducing coefficients modulo twice the actual multiplicity fixes every vector. -/
theorem xiThetaRamifiedCoefficientInvariants_mod_multiplicity (rho : XiDivisorSupport) :
    xiThetaRamifiedCoefficientInvariants (ZMod (2 * xiSupportMultiplicity rho)) rho = ⊤ :=
  ramifiedNodeMonodromyInvariants_zmod (2 * xiSupportMultiplicity rho)

/-- The actual nonzero terminal coefficient survives the multiplicity-corrected shear. -/
theorem xiThetaTerminalNearbyInvariantClass_ramified
    (rho : XiDivisorSupport) (x : ℝ) :
    xiThetaTerminalNearbyInvariantClass rho x ≠ 0 ∧
      (universalNodePicardLefschetzMonodromy ℂ ^ (2 * xiSupportMultiplicity rho))
          (xiThetaTerminalNearbyInvariantClass rho x) =
        xiThetaTerminalNearbyInvariantClass rho x := by
  exact ⟨xiThetaTerminalNearbyInvariantClass_ne_zero rho x,
    universalNodeConductorSpecialization_ramified_fixed ℂ
      (2 * xiSupportMultiplicity rho) (xiThetaTerminalConductorCoefficient rho x)⟩

end

end RHTower
