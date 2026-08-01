import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.Galois.Basic

/-!
# Automorphisms permute the roots

An automorphism over the base field commutes with evaluating a polynomial with base-field
coefficients, so it carries a root to a root.  Being injective on a finite root set, it permutes it.

This is the hypothesis that the discriminant argument needs of the Galois action: every automorphism
acts on the roots by a permutation.
-/

namespace GaloisForLFunctions.HTGeometry

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- **An automorphism carries a root to a root.** -/
theorem aeval_algEquiv_eq_zero (σ : E ≃ₐ[F] E) {p : Polynomial F} {x : E}
    (hx : Polynomial.aeval x p = 0) : Polynomial.aeval (σ x) p = 0 := by
  rw [Polynomial.aeval_algHom_apply σ.toAlgHom x, hx]
  exact map_zero _

/-- **An automorphism maps the root set into itself.** -/
theorem mem_rootSet_algEquiv (σ : E ≃ₐ[F] E) {p : Polynomial F} {x : E}
    (hx : x ∈ p.rootSet E) : σ x ∈ p.rootSet E := by
  rw [Polynomial.mem_rootSet'] at hx ⊢
  exact ⟨hx.1, aeval_algEquiv_eq_zero σ hx.2⟩

/-- **A root indexing is carried to a root indexing.**  If a family enumerates the roots
bijectively, an automorphism permutes the indices. -/
theorem exists_perm_of_root_enumeration {d : ℕ} {p : Polynomial F} (v : Fin d → E)
    (hv : Function.Injective v) (hrange : ∀ x : E, x ∈ p.rootSet E ↔ ∃ i, v i = x)
    (σ : E ≃ₐ[F] E) : ∃ e : Equiv.Perm (Fin d), ∀ i, σ (v i) = v (e i) := by
  classical
  have hmem : ∀ i, ∃ j, v j = σ (v i) := by
    intro i
    exact (hrange _).1 (mem_rootSet_algEquiv σ ((hrange (v i)).2 ⟨i, rfl⟩))
  choose f hf using hmem
  have hfinj : Function.Injective f := by
    intro i j hij
    have h := (hf i).trans (hij ▸ (hf j)).symm
    exact hv (σ.injective h)
  refine ⟨Equiv.ofBijective f ⟨hfinj, Finite.injective_iff_surjective.1 hfinj⟩, fun i => ?_⟩
  exact (hf i).symm

end GaloisForLFunctions.HTGeometry
