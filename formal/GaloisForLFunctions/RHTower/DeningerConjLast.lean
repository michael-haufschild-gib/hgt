import GaloisForLFunctions.RHTower.DeningerConjHead
import GaloisForLFunctions.RHTower.DeningerWordMerge

/-!
# Cancellation at the back

Conjugating by a letter of the back factor which the last letter cancels into the base group rotates
the word the other way: the last letter moves to the front.  This is the mirror of cancellation at
the front, and with it the one letter trichotomy is complete.

* `deningerConj_last_merge` : cancellation at the back rotates the word backwards.
* `deningerLen_conj_last_ne` : incomplete cancellation at the back lengthens by one.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
/-- **Cancellation at the back rotates the word backwards.**  If conjugating by a letter of the back
factor cancels the last letter into the base group, the conjugate is the rotation that moves the
last letter to the front, conjugated by the base group element that the cancellation produced. -/
theorem deningerConj_last_merge (i : ι) (uℓ : G i) (U₀ : List (Σ i, G i))
    (x : G i) (k : H) (hk : uℓ * x⁻¹ = φ i k) :
    PushoutI.of (φ := φ) i x *
        deningerLetterProd (φ := φ) (U₀ ++ [(⟨i, uℓ⟩ : Σ i, G i)]) *
        (PushoutI.of (φ := φ) i x)⁻¹ =
      PushoutI.base φ k⁻¹ *
        deningerLetterProd (φ := φ)
          ((U₀ ++ [(⟨i, uℓ⟩ : Σ i, G i)]).rotate U₀.length) *
        (PushoutI.base φ k⁻¹)⁻¹ := by
  have hrot : (U₀ ++ [(⟨i, uℓ⟩ : Σ i, G i)]).rotate U₀.length =
      (⟨i, uℓ⟩ : Σ i, G i) :: U₀ := by
    rw [List.rotate_eq_drop_append_take (by simp), List.drop_left, List.take_left]
    rfl
  have huℓ : PushoutI.of (φ := φ) i uℓ =
      PushoutI.base φ k * PushoutI.of (φ := φ) i x := by
    have hx : uℓ = φ i k * x := by rw [← hk]; group
    rw [hx, map_mul, PushoutI.of_apply_eq_base]
  rw [hrot]
  show PushoutI.of (φ := φ) i x * deningerLetterProd (φ := φ) (U₀ ++ [(⟨i, uℓ⟩ : Σ i, G i)]) *
      (PushoutI.of (φ := φ) i x)⁻¹ =
    PushoutI.base φ k⁻¹ * (PushoutI.of (φ := φ) i uℓ *
      deningerLetterProd (φ := φ) U₀) * (PushoutI.base φ k⁻¹)⁻¹
  rw [deningerLetterProd_snoc]
  show PushoutI.of (φ := φ) i x * (deningerLetterProd (φ := φ) U₀ *
      PushoutI.of (φ := φ) i uℓ) * (PushoutI.of (φ := φ) i x)⁻¹ = _
  rw [huℓ, map_inv]
  group

include d in
/-- **Incomplete cancellation at the back lengthens by one.** -/
theorem deningerLen_conj_last_ne (i : ι) (uℓ : G i) (U₀ : List (Σ i, G i)) (hU₀ne : U₀ ≠ [])
    (hred : ∀ p ∈ U₀ ++ [(⟨i, uℓ⟩ : Σ i, G i)], p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (U₀ ++ [(⟨i, uℓ⟩ : Σ i, G i)]))
    (hhead : ∀ q ∈ U₀.head?, i ≠ q.1)
    (x : G i) (hx : x ∉ (φ i).range) (hux : uℓ * (x : G i)⁻¹ ∉ (φ i).range) :
    deningerLen d (PushoutI.of (φ := φ) i x *
        deningerLetterProd (φ := φ) (U₀ ++ [(⟨i, uℓ⟩ : Σ i, G i)]) *
        (PushoutI.of (φ := φ) i x)⁻¹) = U₀.length + 2 := by
  obtain ⟨hU₀alt, _, hjunc⟩ := List.isChain_append.1 halt
  set W : List (Σ i, G i) :=
    (⟨i, x⟩ : Σ i, G i) :: (U₀ ++ [(⟨i, uℓ * (x : G i)⁻¹⟩ : Σ i, G i)]) with hW
  have hprod : deningerLetterProd (φ := φ) W =
      PushoutI.of (φ := φ) i x * deningerLetterProd (φ := φ) (U₀ ++ [(⟨i, uℓ⟩ : Σ i, G i)]) *
        (PushoutI.of (φ := φ) i x)⁻¹ := by
    rw [hW, deningerLetterProd_cons, deningerLetterProd_snoc, deningerLetterProd_snoc]
    show PushoutI.of (φ := φ) i x * (deningerLetterProd (φ := φ) U₀ *
        PushoutI.of (φ := φ) i (uℓ * (x : G i)⁻¹)) =
      PushoutI.of (φ := φ) i x * (deningerLetterProd (φ := φ) U₀ *
        PushoutI.of (φ := φ) i uℓ) * (PushoutI.of (φ := φ) i x)⁻¹
    rw [map_mul, map_inv]
    group
  have hWred : ∀ p ∈ W, p.2 ∉ (φ p.1).range := by
    intro p hp
    rw [hW, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hx
    · rcases List.mem_append.1 hp with hp | hp
      · exact hred p (List.mem_append.2 (Or.inl hp))
      · rw [List.mem_singleton] at hp
        subst hp
        exact hux
  have hWalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) W := by
    rw [hW]
    refine List.isChain_cons.2 ⟨fun q hq => ?_, ?_⟩
    · rw [List.head?_append_of_ne_nil _ hU₀ne] at hq
      exact hhead q hq
    · refine List.isChain_append.2 ⟨hU₀alt, List.isChain_singleton _, fun p hp q hq => ?_⟩
      rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
      subst hq
      exact hjunc p hp (⟨i, uℓ⟩ : Σ i, G i) rfl
  have hlen := congrArg List.length (deningerNormalWord_map_fst (d := d) W hWred hWalt)
  rw [List.length_map, List.length_map] at hlen
  show ((_ • (NormalWord.empty : NormalWord d)) : NormalWord d).toList.length = _
  rw [← hprod, hlen, hW]
  simp

end RHTower
