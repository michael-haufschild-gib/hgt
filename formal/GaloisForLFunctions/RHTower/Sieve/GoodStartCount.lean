import GaloisForLFunctions.RHTower.Sieve.MoebiusSignLower

/-!
# Counting the starts where both signs occur

Assembling the two exceptional-set bounds with the sign-count conclusion: if outside `Bad₁` the
Möbius sum is small and outside `Bad₂` the squarefree count is large, then every start outside both
carries at least `(3/16)DL` integers of each Möbius sign, so

`#S ≤ #{good starts} + #Bad₁ + #Bad₂`.

The statement is phrased as a covering inequality in `ℕ`, so no truncated subtraction appears; in the
application `Bad₁` comes from the mean-square input through Markov and `Bad₂` from the elementary
squarefree count.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **Starts outside both exceptional sets are good.** -/
theorem card_le_good_add_bad {S Bad₁ Bad₂ : Finset ℕ} {L : ℕ} {D : ℝ}
    (h1 : ∀ t ∈ S, t ∉ Bad₁ →
      |∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ)| ≤ (1 / 8) * D * (L : ℝ))
    (h2 : ∀ t ∈ S, t ∉ Bad₂ →
      (1 / 2) * D * (L : ℝ) ≤ ∑ n ∈ Finset.Ioc t (t + L), ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)) :
    S.card
      ≤ (S.filter (fun t =>
          (3 / 16) * D * (L : ℝ)
              ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = 1)).card : ℝ)
            ∧ (3 / 16) * D * (L : ℝ)
              ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = -1)).card : ℝ))).card
        + Bad₁.card + Bad₂.card := by
  classical
  set G := S.filter (fun t =>
      (3 / 16) * D * (L : ℝ)
          ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = 1)).card : ℝ)
        ∧ (3 / 16) * D * (L : ℝ)
          ≤ (((Finset.Ioc t (t + L)).filter (fun n => moebius n = -1)).card : ℝ)) with hG
  have hcover : S ⊆ (G ∪ Bad₁) ∪ Bad₂ := by
    intro t ht
    by_cases hb1 : t ∈ Bad₁
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hb1)
    by_cases hb2 : t ∈ Bad₂
    · exact Finset.mem_union_right _ hb2
    refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
    rw [hG, Finset.mem_filter]
    exact ⟨ht, card_moebius_sign_ge (h2 t ht hb2) (h1 t ht hb1)⟩
  calc S.card ≤ ((G ∪ Bad₁) ∪ Bad₂).card := Finset.card_le_card hcover
    _ ≤ (G ∪ Bad₁).card + Bad₂.card := Finset.card_union_le _ _
    _ ≤ (G.card + Bad₁.card) + Bad₂.card :=
        Nat.add_le_add_right (Finset.card_union_le _ _) _

end RHTower.Sieve
