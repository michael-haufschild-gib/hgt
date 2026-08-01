import GaloisForLFunctions.HTGeometry.SymmetricQuadraticUnique
import GaloisForLFunctions.HTGeometry.EvenKummerObstruction
import GaloisForLFunctions.HTGeometry.IntermediateFieldComap

/-!
# The even case of the exclusion condition

A square root of a base element lying in an extension with symmetric Galois group generates the
unique quadratic subextension, so its radicand differs from that of a fixed such square root by a
square.  Square classes therefore transfer, and the exclusion from a cyclic extension follows from a
single square-class computation on the fixed square root.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped IntermediateField

variable {F L : Type*} [Field F] [CharZero F] [Field L] [Algebra F L]

omit [CharZero F] in
theorem ne_zero_of_sq_eq {δ : L} {e : F} (hδsq : δ * δ = algebraMap F L e)
    (hδbot : δ ∉ (⊥ : IntermediateField F L)) : e ≠ 0 := by
  intro hcon
  refine hδbot ?_
  rw [hcon, map_zero] at hδsq
  rcases mul_eq_zero.1 hδsq with h | h <;>
    · rw [h]
      exact zero_mem _

omit [CharZero F] [Field L] [Algebra F L] in
/-- **Square classes transfer.**  If `e * d` is a square and `d * c` is not, then `e * c` is not. -/
theorem not_sq_mul_of_sq_mul {c d e : F} (he : e ≠ 0) (htd : ∃ t : F, e * d = t * t)
    (hdc : ¬ ∃ t : F, d * c = t * t) : ¬ ∃ t : F, e * c = t * t := by
  rintro ⟨s, hs⟩
  obtain ⟨t, ht⟩ := htd
  have hkey : d * c * (e * e) = (t * s) * (t * s) := by
    calc d * c * (e * e) = (e * d) * (e * c) := by ring
      _ = (t * t) * (s * s) := by rw [ht, hs]
      _ = (t * s) * (t * s) := by ring
  refine hdc ⟨t * s / e, ?_⟩
  field_simp
  linear_combination hkey

/-- **The even case of the exclusion condition.** -/
theorem notMem_of_permGal_of_isCyclic {E M : IntermediateField F L}
    [FiniteDimensional F E] [IsGalois F E] [FiniteDimensional F M] [IsGalois F M]
    {γ : Type*} [Fintype γ] [DecidableEq γ] [Nontrivial γ]
    (φ : (E ≃ₐ[F] E) ≃* Equiv.Perm γ) (hcyc : IsCyclic (M ≃ₐ[F] M))
    {β : L} {d : F} (hβE : β ∈ E) (hβsq : β * β = algebraMap F L d)
    (hβbot : β ∉ (⊥ : IntermediateField F L))
    {α₀ : L} {c : F} (hα₀sq : α₀ * α₀ = algebraMap F L c) (hα₀M : α₀ ∈ M)
    (hα₀bot : α₀ ∉ (⊥ : IntermediateField F L))
    (hclass : ¬ ∃ t : F, d * c = t * t) :
    ∀ (δ : L) (e : F), δ ∈ E → δ * δ = algebraMap F L e →
      δ ∉ (⊥ : IntermediateField F L) → δ ∉ M := by
  intro δ e hδE hδsq hδbot
  have hleδ : F⟮δ⟯ ≤ E := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact hδE
  have hleβ : F⟮β⟯ ≤ E := by
    rw [IntermediateField.adjoin_simple_le_iff]
    exact hβE
  have h1 : Module.finrank F (IntermediateField.comap E.val F⟮δ⟯) = 2 := by
    rw [finrank_comap_val hleδ]
    exact finrank_adjoin_eq_two hδsq hδbot
  have h2 : Module.finrank F (IntermediateField.comap E.val F⟮β⟯) = 2 := by
    rw [finrank_comap_val hleβ]
    exact finrank_adjoin_eq_two hβsq hβbot
  have hK : IntermediateField.comap E.val F⟮δ⟯ = IntermediateField.comap E.val F⟮β⟯ :=
    eq_of_finrank_eq_two_of_permGal φ h1 h2
  have hmem : (⟨δ, hδE⟩ : E) ∈ IntermediateField.comap E.val F⟮δ⟯ :=
    IntermediateField.mem_adjoin_simple_self F δ
  rw [hK] at hmem
  have hδβ : δ ∈ F⟮β⟯ := hmem
  have hed : ∃ t : F, e * d = t * t :=
    sq_mul_eq_sq_of_mem_adjoin_sqrt hβsq hβbot hδβ hδsq hδbot
  exact notMem_of_isCyclic_of_square_class hcyc hα₀sq hα₀M hα₀bot hδsq hδbot
    (not_sq_mul_of_sq_mul (ne_zero_of_sq_eq hδsq hδbot) hed hclass)

end GaloisForLFunctions.HTGeometry
