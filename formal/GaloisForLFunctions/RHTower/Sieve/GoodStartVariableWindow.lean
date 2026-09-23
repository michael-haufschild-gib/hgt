import GaloisForLFunctions.RHTower.Sieve.GoodStartMarkov

/-!
# Step 1 with a window length that varies with the starting point
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- **Starts outside both exceptional sets are good, at a start-dependent window length.** -/
theorem card_le_good_add_bad_var {S Bad₁ Bad₂ : Finset ℕ} {Lf : ℕ → ℕ} {D : ℝ}
    (h1 : ∀ t ∈ S, t ∉ Bad₁ →
      |∑ n ∈ Finset.Ioc t (t + Lf t), ((moebius n : ℤ) : ℝ)| ≤ (1 / 8) * D * (Lf t : ℝ))
    (h2 : ∀ t ∈ S, t ∉ Bad₂ →
      (1 / 2) * D * (Lf t : ℝ) ≤ ∑ n ∈ Finset.Ioc t (t + Lf t), ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)) :
    S.card
      ≤ (S.filter (fun t =>
          (3 / 16) * D * (Lf t : ℝ)
              ≤ (((Finset.Ioc t (t + Lf t)).filter (fun n => moebius n = 1)).card : ℝ)
            ∧ (3 / 16) * D * (Lf t : ℝ)
              ≤ (((Finset.Ioc t (t + Lf t)).filter (fun n => moebius n = -1)).card : ℝ))).card
        + Bad₁.card + Bad₂.card := by
  classical
  set G := S.filter (fun t =>
      (3 / 16) * D * (Lf t : ℝ)
          ≤ (((Finset.Ioc t (t + Lf t)).filter (fun n => moebius n = 1)).card : ℝ)
        ∧ (3 / 16) * D * (Lf t : ℝ)
          ≤ (((Finset.Ioc t (t + Lf t)).filter (fun n => moebius n = -1)).card : ℝ)) with hG
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

/-- **Step 1 at a start-dependent window length.**  This is the form the *fibre* mean square can
feed: the fibre above `a` is a window whose length varies with `a`, so the fixed-length hypothesis of
`card_le_good_add_meanSquare` is replaced by a uniform threshold `δ` below every `(1/8)D·L t`. -/
theorem card_le_good_add_meanSquare_var {S Bad₂ : Finset ℕ} {Lf : ℕ → ℕ} {D V δ : ℝ}
    (hδ : 0 < δ)
    (hδL : ∀ t ∈ S, δ ≤ (1 / 8) * D * (Lf t : ℝ))
    (hms : ∑ t ∈ S, (∑ n ∈ Finset.Ioc t (t + Lf t), ((moebius n : ℤ) : ℝ)) ^ (2 : ℕ) ≤ V)
    (h2 : ∀ t ∈ S, t ∉ Bad₂ →
      (1 / 2) * D * (Lf t : ℝ) ≤ ∑ n ∈ Finset.Ioc t (t + Lf t), ((moebius n : ℤ) : ℝ) ^ (2 : ℕ)) :
    (S.card : ℝ)
      ≤ ((S.filter (fun t =>
          (3 / 16) * D * (Lf t : ℝ)
              ≤ (((Finset.Ioc t (t + Lf t)).filter (fun n => moebius n = 1)).card : ℝ)
            ∧ (3 / 16) * D * (Lf t : ℝ)
              ≤ (((Finset.Ioc t (t + Lf t)).filter (fun n => moebius n = -1)).card : ℝ))).card : ℝ)
        + V / δ ^ (2 : ℕ) + (Bad₂.card : ℝ) := by
  classical
  set M : ℕ → ℝ := fun t => ∑ n ∈ Finset.Ioc t (t + Lf t), ((moebius n : ℤ) : ℝ) with hM
  set Bad₁ : Finset ℕ := S.filter (fun t => δ ≤ |M t|) with hBad₁
  have h1 : ∀ t ∈ S, t ∉ Bad₁ →
      |M t| ≤ (1 / 8) * D * (Lf t : ℝ) := by
    intro t ht hnot
    have hlt : ¬ (δ ≤ |M t|) := by
      intro hc
      exact hnot (by rw [hBad₁, Finset.mem_filter]; exact ⟨ht, hc⟩)
    have := not_le.mp hlt
    linarith [hδL t ht]
  have hcover := card_le_good_add_bad_var (S := S) (Bad₁ := Bad₁) (Bad₂ := Bad₂)
    (Lf := Lf) (D := D) h1 h2
  have hmarkov : (Bad₁.card : ℝ) ≤ V / δ ^ (2 : ℕ) := by
    rw [hBad₁]
    exact RHTower.card_large_le_of_sum_sq_le hδ hms
  have hcast : (S.card : ℝ)
      ≤ ((S.filter (fun t =>
          (3 / 16) * D * (Lf t : ℝ)
              ≤ (((Finset.Ioc t (t + Lf t)).filter (fun n => moebius n = 1)).card : ℝ)
            ∧ (3 / 16) * D * (Lf t : ℝ)
              ≤ (((Finset.Ioc t (t + Lf t)).filter (fun n => moebius n = -1)).card : ℝ))).card : ℝ)
        + (Bad₁.card : ℝ) + (Bad₂.card : ℝ) := by
    exact_mod_cast hcover
  linarith

end RHTower.Sieve
