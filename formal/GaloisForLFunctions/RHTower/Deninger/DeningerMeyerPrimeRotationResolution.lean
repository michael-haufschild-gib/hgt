import GaloisForLFunctions.HTGeometry.RotationInducedFiniteFreeResolution
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerPrimeRotationModule

/-!
# Finite free resolution of the actual prime-rotation Xi packet

The relation uses literal centered prime dilation on every multiplicity-bounded
jet. It presents the equivariant quotient of the actual Meyer Poisson source.
The quotient is not asserted to be projective, and no Chern identity is assumed.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry
open scoped Classical

/-- V I minus the complete centered prime-flow matrix, retaining all Xi Jordan jets. -/
def deningerMeyerXiClockRelation (p : Nat.Primes) (q : ℕ) (S : Finset XiDivisorSupport) :
    Module.End ℂ (DeningerMeyerFiniteXiJetSlot S →
      paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1))) :=
  rotationInducedFreeRelation _ (Pi.basisFun ℂ _) (deningerMeyerXiPacketPrimeIntegerFlow p S)

/-- The actual Xi clock quotient has a proved finite free resolution, with no source
realization or multiplicity equality supplied as an extra premise. -/
theorem deningerMeyerXiClockResolution_exact (p : Nat.Primes) (q : ℕ)
    (S : Finset XiDivisorSupport) :
    Function.Injective (deningerMeyerXiClockRelation p q S) ∧
      LinearMap.range (deningerMeyerXiClockRelation p q S) =
        LinearMap.ker (deningerMeyerXiClockFreeCover p q S) ∧
      Function.Surjective (deningerMeyerXiClockFreeCover p q S) :=
  rotationInducedFiniteFreeResolution_exact _ _ _ _

/-- The relation is a homomorphism for the actual left rotation-algebra action. -/
theorem deningerMeyerXiClockRelation_equivariant (p : Nat.Primes) (q : ℕ)
    (S : Finset XiDivisorSupport)
    (A : paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1)))
    (C : DeningerMeyerFiniteXiJetSlot S →
      paperRotationPolynomialAlgebra (paperPrimeRotationFrequency p (q + 1))) :
    deningerMeyerXiClockRelation p q S (fun i => A * C i) =
      fun i => A * deningerMeyerXiClockRelation p q S C i :=
  rotationInducedFreeRelation_equivariant _ _ _ _ _

end
end RHTower
