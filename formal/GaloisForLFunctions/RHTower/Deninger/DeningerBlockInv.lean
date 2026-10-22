import GaloisForLFunctions.RHTower.Deninger.DeningerShiftFixed

/-!
# The block data of a power decomposes

The block data of a power is unique: the head and the word are read off the normal form, and the
length says where the last block begins.  So the data at one exponent higher is the data at the
lower exponent with one shift block prepended and the head multiplied by the shift.  Inverting the
recursion this way is what lets an induction descend from an equality of powers to the stages below
it.

* `deningerBlock_succ_inv` : the decomposition.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **The block data of a power decomposes.**  The word of the data one exponent higher is a shift
block followed by the word below, and its head is the base head times the shift. -/
theorem deningerBlock_succ_inv (hφ : ∀ i, Function.Injective (φ i))
    (M : List (Σ i, G i)) (hMne : M ≠ [])
    (hMset : ∀ p ∈ M, p.2 ∈ d.set p.1) (hMred : ∀ p ∈ M, p.2 ∉ (φ p.1).range)
    (hMalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) M)
    (hMcyc : ∀ p ∈ M.getLast?, ∀ q ∈ M.head?, p.1 ≠ q.1)
    (j : H) (n : ℕ) (h : H) (N : List (Σ i, G i))
    (hNlen : N.length = (n + 1) * M.length)
    (hNset : ∀ p ∈ N ++ M, p.2 ∈ d.set p.1) (hNred : ∀ p ∈ N ++ M, p.2 ∉ (φ p.1).range)
    (hNalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (N ++ M))
    (hNeq : (PushoutI.base φ j * deningerLetterProd (φ := φ) M) ^ (n + 2) =
      PushoutI.base φ h * deningerLetterProd (φ := φ) (N ++ M)) :
    ∃ (g s : H) (P W : List (Σ i, G i)),
      P.length = n * M.length ∧
      (∀ p ∈ P ++ M, p.2 ∈ d.set p.1) ∧ (∀ p ∈ P ++ M, p.2 ∉ (φ p.1).range) ∧
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (P ++ M) ∧
      (P ++ M).head?.map Sigma.fst = M.head?.map Sigma.fst ∧
      (PushoutI.base φ j * deningerLetterProd (φ := φ) M) ^ (n + 1) =
        PushoutI.base φ g * deningerLetterProd (φ := φ) (P ++ M) ∧
      deningerLetterProd (φ := φ) M * PushoutI.base φ g =
        PushoutI.base φ s * deningerLetterProd (φ := φ) W ∧
      W.map Sigma.fst = M.map Sigma.fst ∧
      h = j * s ∧ N = W ++ P := by
  classical
  obtain ⟨g, P, hPlen, hPset, hPred, hPalt, hPhead, hPeq⟩ :=
    deningerBaseHead_pow_word (d := d) M hMne hMset hMred hMalt hMcyc j n
  obtain ⟨s, W, hmapW, hsetW, hredW, hshift⟩ :=
    deningerShift_transversal (d := d) M hMne hMred g
  have hWne : W ≠ [] := by
    intro hnil
    have := congrArg List.length hmapW
    rw [hnil] at this
    simp only [List.map_nil, List.length_nil, List.length_map] at this
    exact hMne (List.length_eq_zero_iff.1 this.symm)
  have hWlen : W.length = M.length := by
    have := congrArg List.length hmapW
    simpa using this
  have haltW : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) W :=
    deningerIsChain_of_map_fst M W hmapW hMalt
  have hjunc : ∀ p ∈ W.getLast?, ∀ q ∈ (P ++ M).head?, p.1 ≠ q.1 :=
    deningerCyc_of_map_fst_cross M W (P ++ M) hmapW hPhead hMcyc
  have hsetWP : ∀ p ∈ (W ++ P) ++ M, p.2 ∈ d.set p.1 := by
    rw [List.append_assoc]
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hsetW p hp
    · exact hPset p hp
  have hredWP : ∀ p ∈ (W ++ P) ++ M, p.2 ∉ (φ p.1).range := by
    rw [List.append_assoc]
    intro p hp
    rcases List.mem_append.1 hp with hp | hp
    · exact hredW p hp
    · exact hPred p hp
  have haltWP : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) ((W ++ P) ++ M) := by
    rw [List.append_assoc]
    exact List.isChain_append.2 ⟨haltW, hPalt, hjunc⟩
  have hstep : (PushoutI.base φ j * deningerLetterProd (φ := φ) M) ^ (n + 2) =
      PushoutI.base φ (j * s) * deningerLetterProd (φ := φ) ((W ++ P) ++ M) := by
    rw [pow_succ', hPeq, ← mul_assoc, mul_assoc (PushoutI.base φ j), hshift, List.append_assoc]
    simp only [deningerLetterProd_append, map_mul]
    group
  obtain ⟨hhead, hwords⟩ :=
    deningerBaseWord_head_eq (d := d) hφ h (j * s) (N ++ M) ((W ++ P) ++ M)
      hNset hNred hNalt hsetWP hredWP haltWP (by rw [← hNeq, hstep])
  refine ⟨g, s, P, W, hPlen, hPset, hPred, hPalt, hPhead, hPeq, hshift, hmapW, hhead, ?_⟩
  refine List.append_inj_left hwords ?_
  rw [hNlen, List.length_append, hWlen, hPlen]
  ring

end RHTower
