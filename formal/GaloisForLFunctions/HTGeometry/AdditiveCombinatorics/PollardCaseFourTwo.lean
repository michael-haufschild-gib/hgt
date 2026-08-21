import GaloisForLFunctions.HTGeometry.AdditiveCombinatorics.PollardCaseFourOne

/-!
# CASE 4.2 of Grynkiewicz's proof: the periodicity of the Dyson small part

In CASE 4.2 the structural witnesses for the Dyson pair are the whole pair, `A' = X = A ∪ B` and
`B' = Y = A ∩ B`, and `X ·_t Y = X · Y`.  The first step shows that `Y` must be periodic for
`H = S(X · Y)`: otherwise a point of `(Y · H) \ Y` can be adjoined to whichever of `A`, `B` is
missing it without changing any `A ·_i B` with `i ≤ t`, and the induction hypothesis applies to
the enlarged pair.
-/

open scoped Pointwise
open Finset

namespace GaloisForLFunctions.HTGeometry.AddComb

variable {G : Type*} [CommGroup G] [DecidableEq G] [Fintype G]

/-- Every product of a point of `Y · H` with a point of `X` lies in `X · Y`. -/
theorem mem_mul_of_mem_mulStab {X Y : Finset G} {α z : G}
    (hα : α ∈ Y * mulStab (X * Y)) (hz : z ∈ X) : α * z ∈ X * Y := by
  obtain ⟨y, hy, h, hh, rfl⟩ := mem_mul.1 hα
  have hmem : (z * y) * h ∈ X * Y * mulStab (X * Y) :=
    Finset.mul_mem_mul (Finset.mul_mem_mul hz hy) hh
  rw [mul_mulStab] at hmem
  have heq : y * h * z = z * y * h := by
    rw [mul_comm (y * h) z, mul_assoc]
  rw [heq]
  exact hmem

/-- **CASE 4.2, first step.**  If the Dyson small part is not periodic for `H`, the conclusion of
Grynkiewicz's theorem descends from the enlarged pair. -/
theorem case42_notPeriodic {A B : Finset G} {t : ℕ} (ht : 1 ≤ t)
    (hA : t ≤ A.card) (hB : t ≤ B.card)
    (hsub : (A ∪ B) * (A ∩ B) ⊆ repSet A B t)
    {α : G} (hα : α ∈ (A ∩ B) * mulStab ((A ∪ B) * (A ∩ B))) (hαY : α ∉ A ∩ B)
    (hIHA : α ∉ A → PollardConclusion (insert α A) B t)
    (hIHB : α ∉ B → PollardConclusion A (insert α B) t) :
    PollardConclusion A B t := by
  classical
  have hrepA : ∀ b ∈ B, t ≤ rep A B (α * b) := by
    intro b hb
    have h1 : α * b ∈ (A ∪ B) * (A ∩ B) :=
      mem_mul_of_mem_mulStab hα (Finset.mem_union_right _ hb)
    exact mem_repSet.1 (hsub h1)
  have hrepB : ∀ a ∈ A, t ≤ rep A B (a * α) := by
    intro a ha
    have h1 : α * a ∈ (A ∪ B) * (A ∩ B) :=
      mem_mul_of_mem_mulStab hα (Finset.mem_union_left _ ha)
    rw [mul_comm a α]
    exact mem_repSet.1 (hsub h1)
  by_cases hαA : α ∈ A
  · have hαB : α ∉ B := fun h => hαY (Finset.mem_inter.2 ⟨hαA, h⟩)
    exact pollardConclusion_of_insert_right ht hA hB hαB hrepB (hIHB hαB)
  · exact pollardConclusion_of_insert_left ht hA hB hαA hrepA (hIHA hαA)

omit [Fintype G] in
/-- **The `(cue)` consequence.**  If `Y = A ∩ B` is `H`-periodic then every `H`-translate of the
Dyson witness still has `Y` inside its small part. -/
theorem subset_dysonSmall_of_periodic {A B H : Finset G}
    (hper : (A ∩ B) * H = A ∩ B) {y : G} (hy : y⁻¹ ∈ H) :
    A ∩ B ⊆ dysonSmall A B y := by
  intro z hz
  have h1 : z * y⁻¹ ∈ A ∩ B := by
    rw [← hper]
    exact Finset.mul_mem_mul hz hy
  refine Finset.mem_inter.2 ⟨mem_smul_finset_iff.2 ?_, (Finset.mem_inter.1 hz).1⟩
  rw [mul_comm y⁻¹ z]
  exact (Finset.mem_inter.1 h1).2

end GaloisForLFunctions.HTGeometry.AddComb
