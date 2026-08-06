import GaloisForLFunctions.RHTower.Sieve.DirichletBlockWindow

/-!
# The standard saving `ρ = 2^{-k}`

Setting `ρ = 2^{-k}` in the window collapses its two ends to

```text
M^{k − 3/2}  ≤  T  ≤  M^{k − 1 + 2/2^k} / (4k)^k ,
```

and the window is non-empty as soon as `(4k)^k ≤ M^{1/2}` — the order's own weight must not exceed
the square root of the block's scale.  That is the constraint which pins `k` at roughly
`log M / log log M` and makes the saving `2^{-k}` decay only that slowly.
-/

namespace RHTower.Sieve

/-- **The window is non-empty at the standard saving.**  The order's weight `(4k)^k` must stay
below `M^{1/2}`. -/
theorem window_nonempty_of_weight {M : ℝ} {k : ℕ} (hk : 2 ≤ k) (hM : 1 ≤ M)
    (hsize : ((4 * (k : ℝ)) ^ k) ^ 2 ≤ M) :
    M ^ ((k : ℝ) - 3 / 2) ≤ M ^ ((k : ℝ) - 1 + 2 / (2 : ℝ) ^ k) / (4 * (k : ℝ)) ^ k := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hA0 : (0 : ℝ) < (4 * (k : ℝ)) ^ k := by positivity
  have hK0 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hKpos : (0 : ℝ) < 2 / (2 : ℝ) ^ k := by positivity
  rw [le_div_iff₀ hA0]
  -- `(4k)^k ≤ M^{1/2} ≤ M^{1/2 + 2/2^k}`
  have hhalf : (4 * (k : ℝ)) ^ k ≤ M ^ ((1 : ℝ) / 2) := by
    have h := Real.rpow_le_rpow (by positivity) hsize (by norm_num : (0 : ℝ) ≤ (1 : ℝ) / 2)
    rwa [← Real.rpow_natCast (((4 * (k : ℝ)) ^ k)) 2, ← Real.rpow_mul hA0.le,
      show (2 : ℕ) * ((1 : ℝ) / 2) = 1 by norm_num, Real.rpow_one] at h
  have hgrow : M ^ ((1 : ℝ) / 2) ≤ M ^ ((1 : ℝ) / 2 + 2 / (2 : ℝ) ^ k) :=
    Real.rpow_le_rpow_of_exponent_le hM (by linarith)
  have hsplit : M ^ ((k : ℝ) - 3 / 2) * M ^ ((1 : ℝ) / 2 + 2 / (2 : ℝ) ^ k)
      = M ^ ((k : ℝ) - 1 + 2 / (2 : ℝ) ^ k) := by
    rw [← Real.rpow_add hM0]
    congr 1
    ring
  calc M ^ ((k : ℝ) - 3 / 2) * (4 * (k : ℝ)) ^ k
      ≤ M ^ ((k : ℝ) - 3 / 2) * M ^ ((1 : ℝ) / 2 + 2 / (2 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (le_trans hhalf hgrow) (Real.rpow_nonneg hM0.le _)
    _ = M ^ ((k : ℝ) - 1 + 2 / (2 : ℝ) ^ k) := hsplit

/-- **A block saves `M^{-2^{-k}}` on the standard window.** -/
theorem dirichlet_block_saves_standard {t : ℝ} (ht : 0 < t) {k N L : ℕ} (hk : 2 ≤ k)
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hspan : N + L ≤ 2 * N + 1)
    (hcond : t / (2 * Real.pi) * (k : ℝ) ^ k ≤ (2 * (N : ℝ)) ^ k)
    (hup : t / (2 * Real.pi) * (4 * (k : ℝ)) ^ k
      ≤ (2 * (N : ℝ)) ^ ((k : ℝ) - 1 + 2 / (2 : ℝ) ^ k))
    (hlow : (2 * (N : ℝ)) ^ ((k : ℝ) - 3 / 2) ≤ t / (2 * Real.pi)) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 512 * (2 * (N : ℝ)) ^ (1 - 1 / (2 : ℝ) ^ k) := by
  have hK0 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hupe : (k : ℝ) - 1 / (2 : ℝ) ^ k * ((2 : ℝ) ^ k - 2)
      = (k : ℝ) - 1 + 2 / (2 : ℝ) ^ k := by
    field_simp
    ring
  have hlowe : (k : ℝ) - 2 + 1 / (2 : ℝ) ^ k * (2 : ℝ) ^ k / 2 = (k : ℝ) - 3 / 2 := by
    field_simp
    ring
  refine dirichlet_block_saves_power ht hk hN hL hspan hcond ?_ ?_
  · rw [hupe]; exact hup
  · rw [hlowe]; exact hlow

/-! ## Halving the saving to make the window integral

At `ρ = 2^{-k}` the window, read as a condition on `k` for a fixed height, has length only about
`1/2` — so it need not contain an integer, and the order cannot always be chosen.  Halving to
`ρ = 2^{-(k+1)}` widens it to about `5/4`, which always does.  The ends become

```text
M^{k − 7/4}  ≤  T  ≤  M^{k − 1/2 + 2^{-k}} / (4k)^k ,
```

and non-emptiness needs only `(4k)^k ≤ M`, not `(4k)^k ≤ M^{1/2}`. -/

/-- **The halved window is non-empty under the weaker weight condition.** -/
theorem window_nonempty_of_weight_half {M : ℝ} {k : ℕ} (hk : 2 ≤ k) (hM : 1 ≤ M)
    (hsize : (4 * (k : ℝ)) ^ k ≤ M) :
    M ^ ((k : ℝ) - 7 / 4) ≤ M ^ ((k : ℝ) - 1 / 2 + 1 / (2 : ℝ) ^ k) / (4 * (k : ℝ)) ^ k := by
  have hM0 : (0 : ℝ) < M := by linarith
  have hA0 : (0 : ℝ) < (4 * (k : ℝ)) ^ k := by
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    positivity
  have hKpos : (0 : ℝ) < 1 / (2 : ℝ) ^ k := by positivity
  rw [le_div_iff₀ hA0]
  have hgrow : M ≤ M ^ ((5 : ℝ) / 4 + 1 / (2 : ℝ) ^ k) := by
    nth_rewrite 1 [show M = M ^ (1 : ℝ) by rw [Real.rpow_one]]
    exact Real.rpow_le_rpow_of_exponent_le hM (by linarith)
  have hsplit : M ^ ((k : ℝ) - 7 / 4) * M ^ ((5 : ℝ) / 4 + 1 / (2 : ℝ) ^ k)
      = M ^ ((k : ℝ) - 1 / 2 + 1 / (2 : ℝ) ^ k) := by
    rw [← Real.rpow_add hM0]
    congr 1
    ring
  calc M ^ ((k : ℝ) - 7 / 4) * (4 * (k : ℝ)) ^ k
      ≤ M ^ ((k : ℝ) - 7 / 4) * M ^ ((5 : ℝ) / 4 + 1 / (2 : ℝ) ^ k) :=
        mul_le_mul_of_nonneg_left (le_trans hsize hgrow) (Real.rpow_nonneg hM0.le _)
    _ = M ^ ((k : ℝ) - 1 / 2 + 1 / (2 : ℝ) ^ k) := hsplit

/-- **A block saves `M^{-2^{-(k+1)}}` on the halved window.**  This is the form in which an integer
order can always be chosen for a given height. -/
theorem dirichlet_block_saves_half {t : ℝ} (ht : 0 < t) {k N L : ℕ} (hk : 2 ≤ k)
    (hN : 1 ≤ N) (hL : 1 ≤ L) (hspan : N + L ≤ 2 * N + 1)
    (hcond : t / (2 * Real.pi) * (k : ℝ) ^ k ≤ (2 * (N : ℝ)) ^ k)
    (hup : t / (2 * Real.pi) * (4 * (k : ℝ)) ^ k
      ≤ (2 * (N : ℝ)) ^ ((k : ℝ) - 1 / 2 + 1 / (2 : ℝ) ^ k))
    (hlow : (2 * (N : ℝ)) ^ ((k : ℝ) - 7 / 4) ≤ t / (2 * Real.pi)) :
    ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
      ≤ 512 * (2 * (N : ℝ)) ^ (1 - 1 / (2 * (2 : ℝ) ^ k)) := by
  have hK0 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hupe : (k : ℝ) - 1 / (2 * (2 : ℝ) ^ k) * ((2 : ℝ) ^ k - 2)
      = (k : ℝ) - 1 / 2 + 1 / (2 : ℝ) ^ k := by
    field_simp
    ring
  have hlowe : (k : ℝ) - 2 + 1 / (2 * (2 : ℝ) ^ k) * (2 : ℝ) ^ k / 2 = (k : ℝ) - 7 / 4 := by
    field_simp
    ring
  refine dirichlet_block_saves_power ht hk hN hL hspan hcond ?_ ?_
  · rw [hupe]; exact hup
  · rw [hlowe]; exact hlow

end RHTower.Sieve
