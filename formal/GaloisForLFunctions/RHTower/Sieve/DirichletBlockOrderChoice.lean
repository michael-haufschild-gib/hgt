import GaloisForLFunctions.RHTower.Sieve.DirichletOrderExists

/-!
# Choosing the order for a given block

Combining the window's integrality (`exists_order_in_window`) with the transfer between powers of
the block's scale and the ratio `u = log T / log M` (`rpow_le_of_le_log_div` and friends) produces,
for every block whose scale is small enough against the height, an order at which the block saves
a power.

The order's own weight is bounded uniformly over the window: since `k ≤ u + 7/4`, the weight
`k·log(4k)` never exceeds `w·log(4w)` with `w = u + 7/4`, so a single hypothesis on `w` suffices
and the circularity between `k` and its weight disappears.
-/

namespace RHTower.Sieve

/-- **An order exists at which the block saves a power.** -/
theorem exists_order_block_saves {t : ℝ} (ht : 0 < t) {N L : ℕ} (hN : 1 ≤ N) (hL : 1 ≤ L)
    (hspan : N + L ≤ 2 * N + 1) (hM : 1 < 2 * (N : ℝ))
    (hu : 1 ≤ Real.log (t / (2 * Real.pi)) / Real.log (2 * (N : ℝ)))
    (hweight : (Real.log (t / (2 * Real.pi)) / Real.log (2 * (N : ℝ)) + 7 / 4)
        * Real.log (4 * (Real.log (t / (2 * Real.pi)) / Real.log (2 * (N : ℝ)) + 7 / 4))
        / Real.log (2 * (N : ℝ)) ≤ 1 / 4) :
    ∃ k : ℕ, 2 ≤ k ∧
      ‖∑ j ∈ Finset.range L, ((N + j : ℕ) : ℂ) ^ (-(Complex.I * (t : ℂ)))‖
        ≤ 512 * (2 * (N : ℝ)) ^ (1 - 1 / (2 * (2 : ℝ) ^ k)) := by
  have hπ := Real.pi_pos
  have hT0 : (0 : ℝ) < t / (2 * Real.pi) := div_pos ht (by positivity)
  have hM0 : (0 : ℝ) < 2 * (N : ℝ) := by linarith
  have hlogM : (0 : ℝ) < Real.log (2 * (N : ℝ)) := Real.log_pos hM
  set M : ℝ := 2 * (N : ℝ) with hMdef
  set T : ℝ := t / (2 * Real.pi) with hTdef
  set u : ℝ := Real.log T / Real.log M with hudef
  set w : ℝ := u + 7 / 4 with hwdef
  have hw0 : (0 : ℝ) < w := by rw [hwdef]; linarith
  have he0 : (0 : ℝ) ≤ w * Real.log (4 * w) / Real.log M := by
    have hlog4w : (0 : ℝ) ≤ Real.log (4 * w) := by
      refine Real.log_nonneg ?_
      rw [hwdef]; linarith
    positivity
  obtain ⟨k, hk2, hklow, hkup⟩ :=
    exists_order_in_window (u := u) (e := w * Real.log (4 * w) / Real.log M) hu he0 hweight
  refine ⟨k, hk2, ?_⟩
  -- the order's weight is below the uniform bound
  have hkR2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hA0 : (0 : ℝ) < (4 * (k : ℝ)) ^ k := by positivity
  have hlogA : Real.log ((4 * (k : ℝ)) ^ k) = (k : ℝ) * Real.log (4 * (k : ℝ)) := by
    rw [Real.log_pow]
  have hmonolog : Real.log (4 * (k : ℝ)) ≤ Real.log (4 * w) :=
    Real.log_le_log (by linarith) (by linarith [hkup])
  have hlog4k : (0 : ℝ) ≤ Real.log (4 * (k : ℝ)) := Real.log_nonneg (by linarith)
  have hweightk : (k : ℝ) * Real.log (4 * (k : ℝ)) ≤ w * Real.log (4 * w) := by
    have h1 : (k : ℝ) * Real.log (4 * (k : ℝ)) ≤ (k : ℝ) * Real.log (4 * w) :=
      mul_le_mul_of_nonneg_left hmonolog (by linarith)
    have h2 : (k : ℝ) * Real.log (4 * w) ≤ w * Real.log (4 * w) := by
      refine mul_le_mul_of_nonneg_right (by linarith [hkup]) ?_
      exact le_trans hlog4k hmonolog
    linarith
  have hAdiv : Real.log ((4 * (k : ℝ)) ^ k) / Real.log M ≤ w * Real.log (4 * w) / Real.log M := by
    rw [hlogA]
    exact div_le_div_of_nonneg_right hweightk hlogM.le
  -- the window's lower end
  have hlow : M ^ ((k : ℝ) - 7 / 4) ≤ T :=
    rpow_le_of_le_log_div hM hT0 (by rw [← hudef]; linarith [hkup])
  -- the window's upper end
  have hup : T * (4 * (k : ℝ)) ^ k ≤ M ^ ((k : ℝ) - 1 / 2 + 1 / (2 : ℝ) ^ k) := by
    refine mul_le_rpow_of_log_div_le hM hT0 hA0 ?_
    have hpos : (0 : ℝ) < 1 / (2 : ℝ) ^ k := by positivity
    rw [← hudef]
    linarith [hAdiv, hklow, hpos]
  -- admissibility
  have hkk : (k : ℝ) ^ k ≤ (4 * (k : ℝ)) ^ k :=
    pow_le_pow_left₀ (by linarith) (by linarith) k
  have hsmall : (-(1 : ℝ) / 2 + 1 / (2 : ℝ) ^ k) ≤ 0 := by
    have h4 : (4 : ℝ) ≤ (2 : ℝ) ^ k := by
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := pow_le_pow_right₀ one_le_two hk2
    have : 1 / (2 : ℝ) ^ k ≤ 1 / 4 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith
    linarith
  have hshrink : M ^ ((k : ℝ) - 1 / 2 + 1 / (2 : ℝ) ^ k) ≤ M ^ k := by
    rw [← Real.rpow_natCast M k]
    exact Real.rpow_le_rpow_of_exponent_le hM.le (by linarith)
  have hcond : T * (k : ℝ) ^ k ≤ M ^ k := by
    have hstep : T * (k : ℝ) ^ k ≤ T * (4 * (k : ℝ)) ^ k :=
      mul_le_mul_of_nonneg_left hkk hT0.le
    linarith [hstep, hup, hshrink]
  exact dirichlet_block_saves_half ht hk2 hN hL hspan hcond hup hlow

end RHTower.Sieve
