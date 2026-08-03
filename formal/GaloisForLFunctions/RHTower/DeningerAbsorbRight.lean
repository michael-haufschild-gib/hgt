import GaloisForLFunctions.RHTower.DeningerPrefixConj

/-!
# Absorbing the base group into the last letter

An element of the base group multiplying a nonempty word on the right is absorbed into its last
letter, changing neither the indices nor reducedness.  This is the mirror of absorbing on the left,
and it is what keeps the cyclic reduction recursion inside the class of reduced alternating words
when a merged letter falls into the base group.

* `deningerLetterProd_mul_base_snoc` : the absorption.
* `deningerAbsorbRight_reduced` : reducedness is preserved.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **Absorbing the base group into the last letter.** -/
theorem deningerLetterProd_mul_base_snoc (M : List (Σ i, G i)) (p : Σ i, G i) (k : H) :
    deningerLetterProd (φ := φ) (M ++ [p]) * PushoutI.base φ k =
      deningerLetterProd (φ := φ) (M ++ [(⟨p.1, p.2 * φ p.1 k⟩ : Σ i, G i)]) := by
  rw [deningerLetterProd_snoc, deningerLetterProd_snoc, mul_assoc, ← PushoutI.of_apply_eq_base,
    ← map_mul]

/-- Absorbing on the right preserves reducedness. -/
theorem deningerAbsorbRight_reduced (M : List (Σ i, G i)) (p : Σ i, G i) (k : H)
    (hred : ∀ r ∈ M ++ [p], r.2 ∉ (φ r.1).range) :
    ∀ r ∈ M ++ [(⟨p.1, p.2 * φ p.1 k⟩ : Σ i, G i)], r.2 ∉ (φ r.1).range := by
  intro r hr
  rcases List.mem_append.1 hr with hr | hr
  · exact hred r (List.mem_append.2 (Or.inl hr))
  · rw [List.mem_singleton] at hr
    subst hr
    rintro ⟨y, hy⟩
    refine hred p (List.mem_append.2 (Or.inr (by simp))) ⟨y * k⁻¹, ?_⟩
    rw [map_mul, hy, map_inv]
    group

/-- Absorbing on the right preserves the sequence of indices. -/
theorem deningerAbsorbRight_map_fst (M : List (Σ i, G i)) (p : Σ i, G i) (k : H) :
    (M ++ [(⟨p.1, p.2 * φ p.1 k⟩ : Σ i, G i)]).map Sigma.fst = (M ++ [p]).map Sigma.fst := by
  simp

end RHTower
