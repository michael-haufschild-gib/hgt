import GaloisForLFunctions.RHTower.Deninger.DeningerMergeDichotomy

/-!
# The leading letter survives a short factor

If a reduced alternating word is multiplied on the right by an element strictly shorter than the
word, the normal form of the product still begins in the factor of the first letter: the
cancellation cannot reach the front.

* `deningerFstIdx_letterProd_mul` : the leading letter survives.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

/-- **The leading letter survives a short factor.** -/
theorem deningerFstIdx_letterProd_mul (L : List (Σ i, G i)) (b : PushoutI φ)
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hlt : deningerLen d b < L.length) (p : Σ i, G i) (hp : p ∈ L.head?) :
    (((deningerLetterProd (φ := φ) L * b) • (NormalWord.empty : NormalWord d)) :
      NormalWord d).fstIdx = some p.1 := by
  classical
  suffices Hn : ∀ n : ℕ, ∀ (L : List (Σ i, G i)) (b : PushoutI φ), L.length ≤ n →
      (∀ p ∈ L, p.2 ∉ (φ p.1).range) →
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L →
      deningerLen d b < L.length → ∀ p ∈ L.head?,
      (((deningerLetterProd (φ := φ) L * b) • (NormalWord.empty : NormalWord d)) :
        NormalWord d).fstIdx = some p.1 from
    Hn L.length L b le_rfl hred halt hlt p hp
  intro n
  induction n with
  | zero =>
    intro L b hn _ _ hb p _
    omega
  | succ n ih =>
    intro L b hn hred halt hb p hp
    by_cases hcase : ∀ q ∈ L.getLast?,
        ((b • (NormalWord.empty : NormalWord d)) : NormalWord d).fstIdx ≠ some q.1
    · exact (deningerLen_prepend (d := d) L b hred halt hcase).2 p hp
    push Not at hcase
    obtain ⟨q, hq, hqb⟩ := hcase
    rw [Option.mem_def] at hq
    obtain ⟨L', hL'⟩ : ∃ L', L = L' ++ [q] :=
      ⟨L.dropLast, (List.dropLast_append_getLast? _ hq).symm⟩
    subst hL'
    have hbpos : 0 < deningerLen d b := by
      by_contra hzero
      have h0 : deningerLen d b = 0 := by omega
      obtain ⟨h, hh⟩ := (deningerLen_eq_zero_iff (d := d) b).1 h0
      rw [← hh, NormalWord.base_smul_def] at hqb
      simp [Word.fstIdx, NormalWord.empty] at hqb
    have hlenL : (L' ++ [q]).length = L'.length + 1 := by simp
    have hL'ne : L' ≠ [] := by
      intro hnil
      rw [hnil] at hb
      simp at hb
      omega
    have hL'pos : 0 < L'.length := List.length_pos_iff.2 hL'ne
    have hredL' : ∀ r ∈ L', r.2 ∉ (φ r.1).range := fun r hr =>
      hred r (List.mem_append.2 (Or.inl hr))
    have hchain := List.isChain_append.1 halt
    have hsplit : deningerLetterProd (φ := φ) (L' ++ [q]) * b =
        deningerLetterProd (φ := φ) L' * (PushoutI.of q.1 q.2 * b) := by
      rw [deningerLetterProd_snoc, mul_assoc]
    have hphead : p ∈ L'.head? := by
      rwa [List.head?_append_of_ne_nil _ hL'ne] at hp
    rcases deningerMerge_dichotomy (d := d) q.1 q.2 b hqb with hA | hB
    · have hnc : ∀ r ∈ L'.getLast?,
          (((PushoutI.of q.1 q.2 * b) • (NormalWord.empty : NormalWord d)) :
            NormalWord d).fstIdx ≠ some r.1 := by
        intro r hr hc
        rw [hA] at hc
        exact hchain.2.2 r hr q (by simp) (Option.some.inj hc).symm
      rw [hsplit]
      exact (deningerLen_prepend (d := d) L' _ hredL' hchain.1 hnc).2 p hphead
    · rw [hsplit]
      rw [hlenL] at hb hn
      exact ih L' (PushoutI.of q.1 q.2 * b) (by omega) hredL' hchain.1 (by omega) p hphead

end RHTower
