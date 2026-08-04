import GaloisForLFunctions.RHTower.DeningerFlattenTake
import GaloisForLFunctions.RHTower.DeningerConjugacyCriterion

/-!
# Conjugates of powers of a cyclically reduced word

A conjugate of a power of a cyclically reduced word which is no longer than that power is obtained
from it by conjugating with a prefix of one period, up to the base group: the conjugacy criterion
returns a rotation by an arbitrary amount, and the whole periods in that rotation commute with the
power and drop out.

* `deningerConj_pow_cycRed` : the normal form of such a conjugate.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **A conjugate of a power of a cyclically reduced word, no longer than that power, is a
conjugate by a prefix of one period, up to the base group.** -/
theorem deningerConj_pow_cycRed (V A : List (Σ i, G i)) (hV2 : 2 ≤ V.length)
    (hVred : ∀ p ∈ V, p.2 ∉ (φ p.1).range)
    (hValt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V)
    (hVcyc : ∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1)
    (hAred : ∀ p ∈ A, p.2 ∉ (φ p.1).range)
    (hAalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) A)
    (n : ℕ) (hn : 0 < n)
    (hshort : deningerLen d (deningerLetterProd (φ := φ) A *
      (deningerLetterProd (φ := φ) V) ^ n * (deningerLetterProd (φ := φ) A)⁻¹) ≤
      n * V.length) :
    ∃ (r : ℕ) (m : H), r ≤ V.length ∧
      deningerLetterProd (φ := φ) A * (deningerLetterProd (φ := φ) V) ^ n *
          (deningerLetterProd (φ := φ) A)⁻¹ =
        PushoutI.base φ m * ((deningerLetterProd (φ := φ) (V.take r))⁻¹ *
          (deningerLetterProd (φ := φ) V) ^ n * deningerLetterProd (φ := φ) (V.take r)) *
          (PushoutI.base φ m)⁻¹ := by
  classical
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  set U := deningerFlatten (G := G) V (n' + 1) with hU
  have hVne : V ≠ [] := by
    intro hc
    rw [hc] at hV2
    simp at hV2
  have hUlen : U.length = (n' + 1) * V.length := deningerFlatten_length V (n' + 1)
  have hUred : ∀ p ∈ U, p.2 ∉ (φ p.1).range := fun p hp =>
    hVred p (deningerFlatten_mem V (n' + 1) p hp)
  have hUalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U :=
    deningerFlatten_isChain V hValt hVcyc (n' + 1)
  have hUcyc : ∀ p ∈ U.getLast?, ∀ q ∈ U.head?, p.1 ≠ q.1 := by
    intro p hp q hq
    rw [hU, deningerFlatten_getLast V hVne n'] at hp
    rw [hU, deningerFlatten_head V n' hVne] at hq
    exact hVcyc p hp q hq
  have hUprod : deningerLetterProd (φ := φ) U = (deningerLetterProd (φ := φ) V) ^ (n' + 1) :=
    deningerLetterProd_flatten V (n' + 1)
  have hU2 : 2 ≤ U.length := by
    rw [hUlen]
    nlinarith
  obtain ⟨t, m, -, ht, heq, -⟩ := deningerConj_cycRed_rotate (d := d) A U hAred hAalt hU2 hUred hUalt
    hUcyc (by rw [hUprod]; rw [hUlen] at *; exact hshort)
  obtain ⟨q, r, hrle, hqlt, hqr⟩ : ∃ q r, r ≤ V.length ∧ q < n' + 1 ∧
      U.rotate t = U.rotate (q * V.length + r) := by
    rcases eq_or_lt_of_le ht with heqt | hltt
    · refine ⟨0, 0, by omega, by omega, ?_⟩
      rw [heqt, List.rotate_length]
      simp
    · have hlt : t < (n' + 1) * V.length := by rw [← hUlen]; exact hltt
      refine ⟨t / V.length, t % V.length, le_of_lt (Nat.mod_lt _ (by omega)), ?_, ?_⟩
      · rw [Nat.div_lt_iff_lt_mul (by omega)]
        exact hlt
      · rw [Nat.div_add_mod']
  refine ⟨r, m, hrle, ?_⟩
  rw [← hUprod, heq, hqr, deningerRotate_flatten_conj V r hrle q (n' + 1) hqlt, hUprod]

end RHTower
