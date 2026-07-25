import Mathlib
open Finset

private lemma geom_le_two {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1/2) :
    ∀ m : ℕ, ∑ j ∈ Finset.range m, r ^ j ≤ 2 := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      rw [geom_sum_succ]
      nlinarith [Finset.sum_nonneg (fun j (_ : j ∈ Finset.range m) => pow_nonneg hr0 j)]

theorem log_coeff_bound {A B : ℕ → ℂ} {C R : ℝ} (hC : 1 ≤ C) (hR : 1 ≤ R)
    (hA0 : A 0 = 1)
    (hrec : ∀ n : ℕ, 1 ≤ n →
      (n : ℂ) * A n = ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℂ) * B (n - j) * A j)
    (hAb : ∀ n : ℕ, ‖A n‖ ≤ C * R ^ n) :
    ∀ n : ℕ, 1 ≤ n → ‖B n‖ ≤ (4 * C * R) ^ n := by
  set M : ℝ := 4 * C * R with hM
  have hM4 : (4:ℝ) ≤ M := by rw [hM]; nlinarith
  have hMpos : (0:ℝ) < M := by linarith
  have hRM : R / M ≤ 1/2 := by
    rw [div_le_iff₀ hMpos]; rw [hM]; nlinarith
  have hRM0 : (0:ℝ) ≤ R / M := by positivity
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    have h0 : (0:ℕ) ∈ Finset.range n := by simp [Nat.pos_of_ne_zero, hn]; omega
    have hsplit : ∑ j ∈ Finset.range n, ((n - j : ℕ) : ℂ) * B (n - j) * A j
        = (n : ℂ) * B n * A 0 + ∑ j ∈ Finset.Ico 1 n, ((n - j : ℕ) : ℂ) * B (n - j) * A j := by
      rw [← Finset.add_sum_erase _ _ h0]
      have herase : (Finset.range n).erase 0 = Finset.Ico 1 n := by
        ext j
        simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Ico]
        omega
      rw [herase]
      simp
    have hkey : (n : ℂ) * B n
        = (n : ℂ) * A n - ∑ j ∈ Finset.Ico 1 n, ((n - j : ℕ) : ℂ) * B (n - j) * A j := by
      have := hrec n hn
      rw [hsplit, hA0, mul_one] at this
      linear_combination -this
    have hterm : ∀ j ∈ Finset.Ico 1 n,
        ‖((n - j : ℕ) : ℂ) * B (n - j) * A j‖ ≤ (n : ℝ) * C * (M ^ (n-1) * R) * (R / M) ^ (j - 1) := by
      intro j hj
      simp only [Finset.mem_Ico] at hj
      obtain ⟨hj1, hj2⟩ := hj
      have hnj : 1 ≤ n - j := by omega
      have hnjn : n - j < n := by omega
      have hB : ‖B (n - j)‖ ≤ M ^ (n - j) := ih _ hnjn hnj
      have hA : ‖A j‖ ≤ C * R ^ j := hAb j
      have hpow : M ^ (n - j) * R ^ j = M ^ (n-1) * R * (R / M) ^ (j - 1) := by
        have e1 : (n - j) + (j - 1) = n - 1 := by omega
        have e2 : 1 + (j - 1) = j := by omega
        rw [div_pow, ← e2, pow_add, pow_one, ← e1, pow_add]
        field_simp
        ring
      calc ‖((n - j : ℕ) : ℂ) * B (n - j) * A j‖
          = ((n - j : ℕ) : ℝ) * ‖B (n - j)‖ * ‖A j‖ := by simp
        _ ≤ (n : ℝ) * M ^ (n - j) * (C * R ^ j) := by
            have h1 : ((n - j : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.sub_le n j
            have h2 : (0:ℝ) ≤ ‖B (n-j)‖ := norm_nonneg _
            have h3 : (0:ℝ) ≤ ‖A j‖ := norm_nonneg _
            have h4 : (0:ℝ) ≤ M ^ (n-j) := by positivity
            have h5 : (0:ℝ) ≤ C * R ^ j := by positivity
            have h6 : (0:ℝ) ≤ ((n-j:ℕ):ℝ) := by positivity
            nlinarith
        _ = (n : ℝ) * C * (M ^ (n - j) * R ^ j) := by ring
        _ = (n : ℝ) * C * (M ^ (n-1) * R * (R / M) ^ (j - 1)) := by rw [hpow]
        _ = (n : ℝ) * C * (M ^ (n-1) * R) * (R / M) ^ (j - 1) := by ring
    sorry
