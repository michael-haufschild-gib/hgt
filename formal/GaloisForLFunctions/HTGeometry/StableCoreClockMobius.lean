import GaloisForLFunctions.HTGeometry.StableCoreClockSemilinear
import GaloisForLFunctions.HTGeometry.ClockSemilinearOrderZeroMobius

/-!
# The restricted clock is Möbius on the persistent core generator

Assembling §3(a) at the persistent core.  The clock restricted to the core `T = stableRangeCore φ`
is a semilinear automorphism (previous file), so — once the differential Lüroth theorem produces a
single differential generator `q` of `T` (`T = C⟨q⟩`) — the semilinear order-zero rigidity
(`clockSemilinearAlgEquiv_generator_mobius`) makes it act by a Möbius transform on `q`.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

/-- **§3(a) at the core.**  With the base field `C` carrying the zero derivation, the restricted clock
`ρ|T` acts on a differential generator `q` of the persistent core by a Möbius transform. -/
theorem stableRangeCoreSymmetry_generator_mobius
    {C F : Type*} [Field C] [Field F] [CharZero F] [Algebra C F]
    [Differential C] [Differential F] [DifferentialAlgebra C F]
    (φ : F →ₐ[C] F) (hφ : ∀ x : F, φ x′ = (φ x)′)
    (ρ : F ≃ₐ[C] F) (hcomm : ∀ x, φ (ρ x) = ρ (φ x))
    {lam : C} (hlam : lam ≠ 0) (hCzero : (lam : C)′ = 0)
    (hsemiF : ∀ x : F, ρ x′ = algebraMap C F lam * (ρ x)′) :
    letI : Differential (stableRangeCore φ) :=
      derivationClosedDifferential _ (derivationClosed_stableRangeCore φ hφ)
    ∀ {q : stableRangeCore φ}, HypertranscendentalOver C q →
      differentialAdjoin C ({q} : Set (stableRangeCore φ)) = ⊤ →
      ∃ a b c d : C, a * d - b * c ≠ 0 ∧
        (stableRangeCoreSymmetryAlgEquiv φ ρ hcomm) q
            * (algebraMap C (stableRangeCore φ) c * q + algebraMap C (stableRangeCore φ) d)
          = algebraMap C (stableRangeCore φ) a * q + algebraMap C (stableRangeCore φ) b := by
  letI : Differential (stableRangeCore φ) :=
    derivationClosedDifferential _ (derivationClosed_stableRangeCore φ hφ)
  haveI : DifferentialAlgebra C (stableRangeCore φ) := by
    refine ⟨fun c => ?_⟩
    apply Subtype.ext
    rw [derivationClosedDifferential_apply]
    show ((algebraMap C F c))′ = ((algebraMap C F c′))
    exact DifferentialAlgebra.deriv_algebraMap c
  have hconstT : (algebraMap C (stableRangeCore φ) lam)′ = 0 := by
    apply Subtype.ext
    rw [derivationClosedDifferential_apply]
    show ((algebraMap C (stableRangeCore φ) lam : stableRangeCore φ) : F)′ = _
    rw [show ((algebraMap C (stableRangeCore φ) lam : stableRangeCore φ) : F) = algebraMap C F lam from by
      rw [IsScalarTower.algebraMap_apply C (stableRangeCore φ) F]; rfl,
      DifferentialAlgebra.deriv_algebraMap, hCzero]
    simp
  intro q hq hqtop
  exact clockSemilinearAlgEquiv_generator_mobius (stableRangeCoreSymmetryAlgEquiv φ ρ hcomm)
    hlam hconstT hq hqtop
    (stableRangeCoreSymmetry_semilinear φ hφ ρ hcomm hsemiF)

end GaloisForLFunctions.HTGeometry
