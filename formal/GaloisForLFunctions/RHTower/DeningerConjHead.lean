import GaloisForLFunctions.RHTower.DeningerConjLetter

/-!
# Incomplete cancellation, and conjugation by the base group

Conjugating a cyclically reduced word by a letter of its front factor which the front letter does
not cancel into the base group lengthens it by one: the front merges but survives, and nothing
cancels at the back.

* `deningerLen_conj_head_ne` : incomplete cancellation lengthens by one.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **Incomplete cancellation at the front lengthens by one.** -/
theorem deningerLen_conj_head_ne (i : ι) (u₁ : G i) (U' : List (Σ i, G i)) (hU'ne : U' ≠ [])
    (hred : ∀ p ∈ (⟨i, u₁⟩ : Σ i, G i) :: U', p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) ((⟨i, u₁⟩ : Σ i, G i) :: U'))
    (hlast : ∀ p ∈ U'.getLast?, p.1 ≠ i)
    (x : G i) (hx : x ∉ (φ i).range) (hxu : x * u₁ ∉ (φ i).range) :
    deningerLen d (PushoutI.of (φ := φ) i x *
        deningerLetterProd (φ := φ) ((⟨i, u₁⟩ : Σ i, G i) :: U') *
        (PushoutI.of (φ := φ) i x)⁻¹) = U'.length + 2 := by
  have hxinv : (x : G i)⁻¹ ∉ (φ i).range := by
    rintro ⟨w, hw⟩
    exact hx ⟨w⁻¹, by rw [map_inv, hw, inv_inv]⟩
  set W : List (Σ i, G i) :=
    (⟨i, x * u₁⟩ : Σ i, G i) :: (U' ++ [(⟨i, x⁻¹⟩ : Σ i, G i)]) with hW
  have hprod : deningerLetterProd (φ := φ) W =
      PushoutI.of (φ := φ) i x * deningerLetterProd (φ := φ) ((⟨i, u₁⟩ : Σ i, G i) :: U') *
        (PushoutI.of (φ := φ) i x)⁻¹ := by
    rw [hW, deningerLetterProd_cons, deningerLetterProd_append, deningerLetterProd_cons,
      deningerLetterProd_cons, deningerLetterProd_nil, mul_one]
    show PushoutI.of (φ := φ) i (x * u₁) * (deningerLetterProd (φ := φ) U' *
        PushoutI.of (φ := φ) i x⁻¹) =
      PushoutI.of (φ := φ) i x * (PushoutI.of (φ := φ) i u₁ * deningerLetterProd (φ := φ) U') *
        (PushoutI.of (φ := φ) i x)⁻¹
    rw [map_mul, map_inv]
    group
  have hWred : ∀ p ∈ W, p.2 ∉ (φ p.1).range := by
    intro p hp
    rw [hW, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact hxu
    · rcases List.mem_append.1 hp with hp | hp
      · exact hred p (List.mem_cons_of_mem _ hp)
      · rw [List.mem_singleton] at hp
        subst hp
        exact hxinv
  have hWalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) W := by
    rw [hW]
    refine List.isChain_cons.2 ⟨fun q hq => ?_, ?_⟩
    · rw [List.head?_append_of_ne_nil _ hU'ne] at hq
      exact (List.isChain_cons.1 halt).1 q hq
    · refine List.isChain_append.2 ⟨(List.isChain_cons.1 halt).2, List.isChain_singleton _,
        fun p hp q hq => ?_⟩
      rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
      subst hq
      exact hlast p hp
  have hlen := congrArg List.length (deningerNormalWord_map_fst (d := d) W hWred hWalt)
  rw [List.length_map, List.length_map] at hlen
  show ((_ • (NormalWord.empty : NormalWord d)) : NormalWord d).toList.length = _
  rw [← hprod, hlen, hW]
  simp

end RHTower
