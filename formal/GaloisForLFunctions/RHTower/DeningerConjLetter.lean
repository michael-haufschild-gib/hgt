import GaloisForLFunctions.RHTower.DeningerRotateCycRed
import GaloisForLFunctions.RHTower.DeningerWordIndices

/-!
# Conjugating by a letter from a new factor

Conjugating a reduced alternating word by a letter whose factor occurs neither at its front nor at
its back creates no cancellation at either end, so the length grows by two.  A conjugation that does
not lengthen must therefore use a letter from one of the two extreme factors.

Conjugating by a letter of the front factor which the front letter cancels rotates the word instead,
up to the base group.

* `deningerLen_conj_letter_ne` : the length of such a conjugate.
* `deningerConj_head_merge` : cancellation at the front rotates the word.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **Conjugating by a letter from a new factor lengthens by two.** -/
theorem deningerLen_conj_letter_ne (U : List (Σ i, G i)) (hne : U ≠ [])
    (hred : ∀ p ∈ U, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U)
    (i : ι) (x : G i) (hx : x ∉ (φ i).range)
    (hhead : ∀ q ∈ U.head?, i ≠ q.1) (hlast : ∀ p ∈ U.getLast?, p.1 ≠ i) :
    deningerLen d (PushoutI.of (φ := φ) i x * deningerLetterProd (φ := φ) U *
      (PushoutI.of (φ := φ) i x)⁻¹) = U.length + 2 := by
  set W : List (Σ i, G i) :=
    (⟨i, x⟩ : Σ i, G i) :: (U ++ [(⟨i, x⁻¹⟩ : Σ i, G i)]) with hW
  have hxinv : (x : G i)⁻¹ ∉ (φ i).range := by
    rintro ⟨w, hw⟩
    exact hx ⟨w⁻¹, by rw [map_inv, hw, inv_inv]⟩
  have hprod : deningerLetterProd (φ := φ) W =
      PushoutI.of (φ := φ) i x * deningerLetterProd (φ := φ) U *
        (PushoutI.of (φ := φ) i x)⁻¹ := by
    rw [hW, deningerLetterProd_cons, deningerLetterProd_append, deningerLetterProd_cons,
      deningerLetterProd_nil, mul_one, ← mul_assoc]
    show PushoutI.of (φ := φ) i x * _ * PushoutI.of (φ := φ) i x⁻¹ = _
    rw [map_inv]
  have hWred : ∀ p ∈ W, p.2 ∉ (φ p.1).range := by
    intro p hp
    rw [hW, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hx
    · rcases List.mem_append.1 hp with hp | hp
      · exact hred p hp
      · rw [List.mem_singleton] at hp
        subst hp
        exact hxinv
  have htail : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1)
      (U ++ [(⟨i, x⁻¹⟩ : Σ i, G i)]) := by
    refine List.isChain_append.2 ⟨halt, List.isChain_singleton _, fun p hp q hq => ?_⟩
    rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
    subst hq
    exact hlast p hp
  have hWalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) W := by
    rw [hW]
    refine List.isChain_cons.2 ⟨fun q hq => ?_, htail⟩
    rw [List.head?_append_of_ne_nil _ hne] at hq
    exact hhead q hq
  have hlen := congrArg List.length (deningerNormalWord_map_fst (d := d) W hWred hWalt)
  rw [List.length_map, List.length_map] at hlen
  show ((_ • (NormalWord.empty : NormalWord d)) : NormalWord d).toList.length = _
  rw [← hprod, hlen, hW]
  simp

omit [DecidableEq ι] [∀ i, DecidableEq (G i)] in
/-- **Cancellation at the front rotates the word.**  If conjugating by a letter of the front factor
cancels the front letter into the base group, the conjugate is the rotation by one, conjugated by
the base group element that the cancellation produced. -/
theorem deningerConj_head_merge (i : ι) (u₁ : G i) (U' : List (Σ i, G i))
    (x : G i) (k : H) (hk : x * u₁ = φ i k) :
    PushoutI.of (φ := φ) i x * deningerLetterProd (φ := φ) ((⟨i, u₁⟩ : Σ i, G i) :: U') *
        (PushoutI.of (φ := φ) i x)⁻¹ =
      PushoutI.base φ k * deningerLetterProd (φ := φ) (((⟨i, u₁⟩ : Σ i, G i) :: U').rotate 1) *
        (PushoutI.base φ k)⁻¹ := by
  have hrot : ((⟨i, u₁⟩ : Σ i, G i) :: U').rotate 1 = U' ++ [(⟨i, u₁⟩ : Σ i, G i)] := by
    rw [List.rotate_cons_succ, List.rotate_zero]
  have hxinv : (x : G i)⁻¹ = u₁ * (φ i k)⁻¹ := by
    rw [← hk]
    group
  have hleft : PushoutI.of (φ := φ) i x * PushoutI.of (φ := φ) i u₁ = PushoutI.base φ k := by
    rw [← map_mul, hk, PushoutI.of_apply_eq_base]
  have hright : (PushoutI.of (φ := φ) i x)⁻¹ =
      PushoutI.of (φ := φ) i u₁ * (PushoutI.base φ k)⁻¹ := by
    rw [← map_inv, hxinv, map_mul, ← map_inv, PushoutI.of_apply_eq_base, map_inv]
  rw [hrot, deningerLetterProd_cons, deningerLetterProd_append, deningerLetterProd_cons,
    deningerLetterProd_nil, mul_one, hright]
  have hassoc : PushoutI.of (φ := φ) i x * (PushoutI.of (φ := φ) i u₁ *
      deningerLetterProd (φ := φ) U') =
      PushoutI.of (φ := φ) i x * PushoutI.of (φ := φ) i u₁ * deningerLetterProd (φ := φ) U' :=
    (mul_assoc _ _ _).symm
  rw [hassoc, hleft]
  show _ = PushoutI.base φ k * (deningerLetterProd (φ := φ) U' *
    PushoutI.of (φ := φ) i u₁) * (PushoutI.base φ k)⁻¹
  group

end RHTower
