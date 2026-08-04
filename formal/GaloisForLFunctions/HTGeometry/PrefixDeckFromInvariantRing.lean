import GaloisForLFunctions.HTGeometry.DeckDegreeCriterion
import GaloisForLFunctions.HTGeometry.InvariantFractionRing

/-!
# The deck description of a prefix, from a ring-level quotient statement

The tail theorems consume one fact per depth: the prefix image is the fixed field of the translations
by that prefix's kernel.  Half of it is equivariance and costs nothing.  The other half is the
statement that an invariant *function* comes from the quotient, and that reduces to the same statement
for the *ring* of regular functions, because an invariant fraction is a ratio of invariants.

So the deck description follows from the definition of the quotient — invariant regular functions are
pulled back from the target — with no degree count, no descent, and no Galois theory.
-/

namespace GaloisForLFunctions.HTGeometry

open IntermediateField

noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {G : ℕ → Type*} [∀ j, CommGroup (G j)]

/-- **The depthwise deck description from the ring-level quotient statement.**  If the coordinate ring
has the prefix kernel acting compatibly with its action on the field, invariant ring elements are
pulled back from the prefix, and the protocol is equivariant, then the prefix image is exactly the
fixed field of the kernel translations. -/
theorem prefixImage_eq_fixedField_of_invariant_ring
    (φ : ℕ → F →ₐ[K] F) (i n : ℕ) (a : ∀ j, G j →* G (j + 1)) (ρ : ∀ j, G j →* (F ≃ₐ[K] F))
    (B : Type*) [CommRing B] [IsDomain B] [Algebra B F] [IsFractionRing B F]
    [MulSemiringAction (prefixKernel a i n) B] [MulSemiringAction (prefixKernel a i n) F]
    [Finite (prefixKernel a i n)]
    (hcompat : ∀ (g : prefixKernel a i n) (b : B),
      g • algebraMap B F b = algebraMap B F (g • b))
    (hact : ∀ (g : prefixKernel a i n) (x : F), g • x = ρ i (g : G i) x)
    (hring : ∀ b : B, (∀ g : prefixKernel a i n, g • b = b) →
      algebraMap B F b ∈ IntermediateField.map (forwardPrefix φ i n) ⊤)
    (hequiv : ∀ (g : G i) (y : F), ρ i g (forwardPrefix φ i n y)
      = forwardPrefix φ i n (ρ (prefixIndex i n) (prefixHom a i n g) y)) :
    IntermediateField.map (forwardPrefix φ i n) ⊤
      = fixedField ((prefixKernel a i n).map (ρ i)) := by
  classical
  haveI := Fintype.ofFinite (prefixKernel a i n)
  refine le_antisymm (prefixImage_le_fixedField_of_equivariant φ i n a ρ hequiv) ?_
  intro x hx
  refine mem_of_invariant_of_invariant_ring_le (B := B) hcompat _ hring x ?_
  intro g
  rw [hact g x]
  rw [mem_fixedField_iff] at hx
  exact hx (ρ i (g : G i)) ⟨(g : G i), g.2, rfl⟩

end

end GaloisForLFunctions.HTGeometry
