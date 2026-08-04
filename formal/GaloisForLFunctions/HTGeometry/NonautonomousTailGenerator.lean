import GaloisForLFunctions.HTGeometry.DifferentialLurothSingleGenerator
import GaloisForLFunctions.HTGeometry.NonautonomousStableCore

/-!
# A single generator for a nonautonomous phase tail

The phase tail of a sequence of derivation-compatible injections is a derivation-closed intermediate
field of the ambient free differential field.  By the differential Lüroth theorem it is therefore
generated, as a differential field, by one element as soon as it is not the base field.

Together with the transport identity between successive tails this is the phase coordinate of the
projective time law: each phase carries a generator, and the transition between two phases is a map
between one-generator differential fields.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

noncomputable section

/-- **Each nontrivial phase tail has a single differential generator.** -/
theorem exists_nonautonomousTail_generator
    {C F : Type*} [Field C] [Field F] [Differential C] [Differential F] [Algebra C F]
    [DifferentialAlgebra C F] [CharZero C] [CharZero F]
    {y : F} (hy : DifferentialIndependent C (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin C ({y} : Set F) = ⊤)
    (φ : ℕ → F →ₐ[C] F) (hφ : ∀ i x, φ i x′ = (φ i x)′) (i : ℕ)
    (hTne : nonautonomousTail φ i ≠ ⊥) :
    ∃ u : F, differentialAdjoin C ({u} : Set F) = nonautonomousTail φ i := by
  refine GaloisForLFunctions.differentialLuroth (nonautonomousTail φ i)
    (derivationClosed_nonautonomousTail φ hφ i) ?_ hy hTne
  rw [hytop]
  exact le_top

/-- **Every phase of a nontrivial protocol has a generator.**  If one tail is nontrivial then all
of them are, so the whole time line carries phase coordinates. -/
theorem exists_nonautonomousTail_generator_forall
    {C F : Type*} [Field C] [Field F] [Differential C] [Differential F] [Algebra C F]
    [DifferentialAlgebra C F] [CharZero C] [CharZero F]
    {y : F} (hy : DifferentialIndependent C (fun _ : Unit ↦ y))
    (hytop : differentialAdjoin C ({y} : Set F) = ⊤)
    (φ : ℕ → F →ₐ[C] F) (hφ : ∀ i x, φ i x′ = (φ i x)′)
    (hne : ∀ i : ℕ, nonautonomousTail φ i ≠ ⊥) :
    ∀ i : ℕ, ∃ u : F, differentialAdjoin C ({u} : Set F) = nonautonomousTail φ i :=
  fun i => exists_nonautonomousTail_generator hy hytop φ hφ i (hne i)

end

end GaloisForLFunctions.HTGeometry
