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
  have h : Polynomial.aeval (σ.toAlgHom x) p = σ.toAlgHom (Polynomial.aeval x p) :=
    Polynomial.aeval_algHom_apply _ _ _
  rw [hx, map_zero] at h
  exact h

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
    have h1 : σ (v i) = σ (v j) := by rw [← hf i, ← hf j, hij]
    exact hv (σ.injective h1)
  refine ⟨Equiv.ofBijective f ⟨hfinj, Finite.injective_iff_surjective.1 hfinj⟩, fun i => ?_⟩
  exact (hf i).symm

/-- **A surjective action on the roots contains an odd element.**  With at least two roots, a
transposition is realised, and a transposition is odd. -/
theorem exists_odd_aut_of_surjective {d : ℕ} (hd : 2 ≤ d) (v : Fin d → E)
    (hsurj : ∀ e : Equiv.Perm (Fin d), ∃ σ : E ≃ₐ[F] E, ∀ i, σ (v i) = v (e i)) :
    ∃ (σ : E ≃ₐ[F] E) (e : Equiv.Perm (Fin d)),
      (∀ i, σ (v i) = v (e i)) ∧ Equiv.Perm.sign e = -1 := by
  have hne : (⟨0, by omega⟩ : Fin d) ≠ (⟨1, by omega⟩ : Fin d) := by
    intro hcon
    exact absurd (congrArg Fin.val hcon) (by norm_num)
  obtain ⟨σ, hσ⟩ := hsurj (Equiv.swap (⟨0, by omega⟩ : Fin d) (⟨1, by omega⟩ : Fin d))
  exact ⟨σ, _, hσ, Equiv.Perm.sign_swap hne⟩

end GaloisForLFunctions.HTGeometry
