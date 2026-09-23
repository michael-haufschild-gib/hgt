import Mathlib

/-!
# Active-path counting after odd-window resonance exclusion

The arithmetic window argument must charge coherent prime vertices to either
source-displacement mismatches or intervening proper prime-power vertices.
This finite path inequality is the exact combinatorial conversion; no
asymptotic prime-density or source estimate is assumed.
-/

namespace RHTower

/-- No adjacent prime-labeled vertices are both coherent. -/
def sourceActiveNoCoherentPrimeEdge {α : Type*}
    (P M : α → Prop) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: xs =>
      (P a → P b → M a ∨ M b) ∧
        sourceActiveNoCoherentPrimeEdge P M (b :: xs)

private theorem sourceActiveNoCoherentPrimeEdge_tail {α : Type*}
    {P M : α → Prop} {a : α} {xs : List α}
    (h : sourceActiveNoCoherentPrimeEdge P M (a :: xs)) :
    sourceActiveNoCoherentPrimeEdge P M xs := by
  cases xs with
  | nil => trivial
  | cons b rest => exact h.2

/-- On a finite active path, forbidding adjacent coherent prime nodes forces
at least half the primes, up to nonprime separators and one boundary node,
to be mismatches. -/
theorem sourceActivePath_prime_count_le_twice_mismatch_add_nonprime
    {α : Type*} (P M : α → Prop) [DecidablePred P] [DecidablePred M]
    (xs : List α)
    (h : sourceActiveNoCoherentPrimeEdge P M xs) :
    xs.countP (fun a => decide (P a)) ≤
      2 * xs.countP (fun a => decide (M a)) +
        xs.countP (fun a => decide (¬ P a)) + 1 := by
  classical
  have aux : ∀ n : ℕ, ∀ ys : List α, ys.length = n →
      sourceActiveNoCoherentPrimeEdge P M ys →
      ys.countP (fun a => decide (P a)) ≤
        2 * ys.countP (fun a => decide (M a)) +
          ys.countP (fun a => decide (¬ P a)) + 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro ys hlen hchain
      cases ys with
      | nil => simp
      | cons a tail =>
        have htail := sourceActiveNoCoherentPrimeEdge_tail hchain
        by_cases hMa : M a
        · have hsmaller : tail.length < n := by simp at hlen; omega
          have hbound := ih tail.length hsmaller tail rfl htail
          by_cases hPa : P a
          · simp [hMa, hPa] at *
            omega
          · simp [hMa, hPa] at *
            omega
        · by_cases hPa : P a
          · cases tail with
            | nil =>
              simp [hMa, hPa]
            | cons b rest =>
              have hsmaller : rest.length < n := by simp at hlen; omega
              have hrest : sourceActiveNoCoherentPrimeEdge P M rest :=
                sourceActiveNoCoherentPrimeEdge_tail
                  (sourceActiveNoCoherentPrimeEdge_tail hchain)
              have hbound := ih rest.length hsmaller rest rfl hrest
              have hpair : P a → P b → M a ∨ M b := hchain.1
              by_cases hPb : P b
              · have hMb : M b := (hpair hPa hPb).resolve_left hMa
                simp [hPa, hPb, hMa, hMb] at *
                omega
              · by_cases hMb : M b
                · simp [hPa, hPb, hMa, hMb] at *
                  omega
                · simp [hPa, hPb, hMa, hMb] at *
                  omega
          · have hsmaller : tail.length < n := by simp at hlen; omega
            have hbound := ih tail.length hsmaller tail rfl htail
            simp [hPa, hMa] at *
            omega
  exact aux xs.length xs rfl h

end RHTower
