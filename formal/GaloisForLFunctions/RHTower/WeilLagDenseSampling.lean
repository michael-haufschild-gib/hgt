import GaloisForLFunctions.RHTower.WeilLagFunctionPrimeGap

/-!
# Lag sampling on dense sets: every syndetic set decides the Riemann hypothesis

The integer lags `a_n = Φ(log n)` vary slowly: for `k ≤ n ≤ 2k`,
`|a_n − a_k| ≤ 8 (n − k + 1)(log n + 2)²/√k` (`abs_integerLag_sub_le`). So a one-sided bound on the lags
along any set `A` that meets every window `[n − g, n]` with `(g + 1)(log n + 2)² ≤ C√n` bounds all
integer lags (`integerLag_le_of_dense_samples`, `le_integerLag_of_dense_samples`).

**Theorem** (`riemannHypothesis_iff_integerLag_bddAbove_of_syndetic`). If `A ⊆ ℕ` has bounded gaps,
the Riemann hypothesis holds iff the lags `a_k`, `k ∈ A`, are bounded above (equivalently below). In
particular every arithmetic progression `qn + r` decides the Riemann hypothesis
(`riemannHypothesis_iff_integerLag_progression_bddAbove`).

The lag thinning is governed by the gap scale `√n`, not by arithmetic: unlike Li's criterion, which
fails abstractly along the odd numbers, the lag criterion holds along every syndetic set.
-/

open Real Filter

namespace RHTower

noncomputable section

/-- `(log n + 2)²/√k ≤ 36√2` for `k ≤ n ≤ 2k`, `2 ≤ k`. -/
theorem sq_log_add_two_div_sqrt_le {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) (hn2k : n ≤ 2 * k) :
    (Real.log n + 2) ^ 2 ≤ 36 * Real.sqrt 2 * Real.sqrt k := by
  have h1 := sq_log_add_two_le (n := n) (by omega)
  have hn : (n : ℝ) ≤ 2 * k := by exact_mod_cast hn2k
  have h2 : Real.sqrt n ≤ Real.sqrt 2 * Real.sqrt k := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hn
  nlinarith [Real.sqrt_nonneg (n : ℝ)]

/-- **Upper bounds transfer from dense samples.** -/
theorem integerLag_le_of_dense_samples {A : Set ℕ} {M C : ℝ} {N₀ : ℕ}
    (hA : ∀ k ∈ A, 2 ≤ k → integerLag k ≤ M)
    (hdense : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, 2 ≤ k ∧ k ≤ n ∧ n ≤ 2 * k ∧
      (((n - k : ℕ) : ℝ) + 1) * (Real.log n + 2) ^ 2 ≤ C * Real.sqrt k) :
    ∃ M' : ℝ, ∀ n : ℕ, 2 ≤ n → integerLag n ≤ M' := by
  classical
  set B : ℝ := (Finset.range (N₀ + 2)).sup' ⟨0, by simp⟩ fun n => integerLag n with hB
  refine ⟨max B (M + 8 * C), fun n hn => ?_⟩
  rcases lt_or_ge n N₀ with hlt | hge
  · exact le_max_of_le_left (Finset.le_sup' (fun n => integerLag n)
      (Finset.mem_range.mpr (by omega)))
  · refine le_max_of_le_right ?_
    obtain ⟨k, hkA, hk2, hkn, hn2k, hgap⟩ := hdense n hge
    have hd := abs_integerLag_sub_le hk2 hkn hn2k
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < k))
    have hle : 8 * (((n - k : ℕ) : ℝ) + 1) * (Real.log n + 2) ^ 2 / Real.sqrt k ≤ 8 * C := by
      rw [div_le_iff₀ hsk]
      nlinarith
    have := (abs_le.mp hd).2
    linarith [hA k hkA hk2]

/-- **Lower bounds transfer from dense samples.** -/
theorem le_integerLag_of_dense_samples {A : Set ℕ} {M C : ℝ} {N₀ : ℕ}
    (hA : ∀ k ∈ A, 2 ≤ k → M ≤ integerLag k)
    (hdense : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, 2 ≤ k ∧ k ≤ n ∧ n ≤ 2 * k ∧
      (((n - k : ℕ) : ℝ) + 1) * (Real.log n + 2) ^ 2 ≤ C * Real.sqrt k) :
    ∃ M' : ℝ, ∀ n : ℕ, 2 ≤ n → M' ≤ integerLag n := by
  classical
  set B : ℝ := (Finset.range (N₀ + 2)).inf' ⟨0, by simp⟩ fun n => integerLag n with hB
  refine ⟨min B (M - 8 * C), fun n hn => ?_⟩
  rcases lt_or_ge n N₀ with hlt | hge
  · exact min_le_of_left_le (Finset.inf'_le (fun n => integerLag n)
      (Finset.mem_range.mpr (by omega)))
  · refine min_le_of_right_le ?_
    obtain ⟨k, hkA, hk2, hkn, hn2k, hgap⟩ := hdense n hge
    have hd := abs_integerLag_sub_le hk2 hkn hn2k
    have hsk : 0 < Real.sqrt k := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < k))
    have hle : 8 * (((n - k : ℕ) : ℝ) + 1) * (Real.log n + 2) ^ 2 / Real.sqrt k ≤ 8 * C := by
      rw [div_le_iff₀ hsk]
      nlinarith
    have := (abs_le.mp hd).1
    linarith [hA k hkA hk2]

/-- A set with gaps at most `G` beyond `N₀` meets every window with the dense-sample bound. -/
theorem dense_samples_of_syndetic {A : Set ℕ} {G N₀ : ℕ}
    (hsyn : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ n ≤ k + G) :
    ∃ C : ℝ, ∃ N₁ : ℕ, ∀ n : ℕ, N₁ ≤ n → ∃ k ∈ A, 2 ≤ k ∧ k ≤ n ∧ n ≤ 2 * k ∧
      (((n - k : ℕ) : ℝ) + 1) * (Real.log n + 2) ^ 2 ≤ C * Real.sqrt k := by
  refine ⟨(G + 1) * (36 * Real.sqrt 2), N₀ + 2 * G + 4, fun n hn => ?_⟩
  obtain ⟨k, hkA, hkn, hnk⟩ := hsyn n (by omega)
  have hk2 : 2 ≤ k := by omega
  have hn2k : n ≤ 2 * k := by omega
  refine ⟨k, hkA, hk2, hkn, hn2k, ?_⟩
  have hg : ((n - k : ℕ) : ℝ) ≤ G := by exact_mod_cast (by omega : n - k ≤ G)
  have hl := sq_log_add_two_div_sqrt_le hk2 hkn hn2k
  have hl0 : 0 ≤ (Real.log n + 2) ^ 2 := sq_nonneg _
  have hs0 : 0 ≤ 36 * Real.sqrt 2 * Real.sqrt k := by positivity
  calc (((n - k : ℕ) : ℝ) + 1) * (Real.log n + 2) ^ 2
      ≤ ((G : ℝ) + 1) * (36 * Real.sqrt 2 * Real.sqrt k) := by
        apply mul_le_mul (by linarith) hl hl0 (by positivity)
    _ = (G + 1) * (36 * Real.sqrt 2) * Real.sqrt k := by ring

/-- **Syndetic lag criterion.** If `A ⊆ ℕ` has bounded gaps, RH holds iff the lags along `A` are
bounded above. -/
theorem riemannHypothesis_iff_integerLag_bddAbove_of_syndetic {A : Set ℕ} {G N₀ : ℕ}
    (hsyn : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ n ≤ k + G) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ k ∈ A, 2 ≤ k → integerLag k ≤ M := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_integerLag_bddAbove.mp h
    exact ⟨M, fun k _ hk => hM k hk⟩
  · rintro ⟨M, hM⟩
    obtain ⟨C, N₁, hdense⟩ := dense_samples_of_syndetic hsyn
    exact riemannHypothesis_iff_integerLag_bddAbove.mpr (integerLag_le_of_dense_samples hM hdense)

/-- **Syndetic lag criterion, lower form.** -/
theorem riemannHypothesis_iff_integerLag_bddBelow_of_syndetic {A : Set ℕ} {G N₀ : ℕ}
    (hsyn : ∀ n : ℕ, N₀ ≤ n → ∃ k ∈ A, k ≤ n ∧ n ≤ k + G) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ k ∈ A, 2 ≤ k → M ≤ integerLag k := by
  constructor
  · intro h
    obtain ⟨M, hM⟩ := riemannHypothesis_iff_integerLag_bddBelow.mp h
    exact ⟨M, fun k _ hk => hM k hk⟩
  · rintro ⟨M, hM⟩
    obtain ⟨C, N₁, hdense⟩ := dense_samples_of_syndetic hsyn
    exact riemannHypothesis_iff_integerLag_bddBelow.mpr (le_integerLag_of_dense_samples hM hdense)

/-- **The lag criterion along an arithmetic progression.** For `q ≥ 1` and any `r`, RH holds iff
`a_{qn+r}` is bounded above. -/
theorem riemannHypothesis_iff_integerLag_progression_bddAbove {q r : ℕ} (hq : 1 ≤ q) :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ n : ℕ, 2 ≤ q * n + r → integerLag (q * n + r) ≤ M := by
  have hsyn : ∀ n : ℕ, r ≤ n → ∃ k ∈ {k : ℕ | ∃ j, k = q * j + r}, k ≤ n ∧ n ≤ k + q := by
    intro n hn
    refine ⟨q * ((n - r) / q) + r, ⟨(n - r) / q, rfl⟩, ?_, ?_⟩
    · have := Nat.div_mul_le_self (n - r) q
      rw [mul_comm] at this
      omega
    · have := Nat.lt_div_mul_add (a := n - r) (by omega : 0 < q)
      rw [mul_comm] at this
      omega
  rw [riemannHypothesis_iff_integerLag_bddAbove_of_syndetic hsyn]
  constructor
  · rintro ⟨M, hM⟩
    exact ⟨M, fun n hn => hM _ ⟨n, rfl⟩ hn⟩
  · rintro ⟨M, hM⟩
    refine ⟨M, fun k ⟨j, hj⟩ hk => ?_⟩
    subst hj
    exact hM j hk

end

end RHTower
