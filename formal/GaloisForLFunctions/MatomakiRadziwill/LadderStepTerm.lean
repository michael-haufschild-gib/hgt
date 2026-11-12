import GaloisForLFunctions.MatomakiRadziwill.LadderHBounds

/-!
# The moment steps of the concrete ladder

For the configuration `ladderConfig L X` with thresholds `c_j(v) = e^{-αv/H_j}`, `α = 6/25`, and
exponents `momentExp`, the `j`-th step (`1 ≤ j < J`) of the master inequality is at most
(`step_term_le`)

`C_1 b^{66} e^{-1.52 b}`,   `b = b_{j−1}`,   `C_1 = 144e · 2^{48}`.

`moment_step_le` gives `#V_j² #V_{j−1} e^{2αb} · 144 e^{-(a_j − 1/H_j)/b}`; here `a_j = 2b²`, so the
exponential is at most `e · e^{-2b}`, `#V_j ≤ 2a_j^{10} = 2^{11} b^{20}` and `#V_{j−1} ≤ (2b)^{26}`.
-/

open Finset MeasureTheory Set RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- The exponent `α = 6/25 = 1/4 − 1/100`. -/
def ladderAlpha : ℝ := 6 / 25

/-- The thresholds `c_j(v) = e^{-αv/H_j}`. -/
def ladderC (L : ℝ) (j v : ℕ) : ℝ := Real.exp (-ladderAlpha * v / seqH L j)

/-- The moment exponents of the concrete ladder. -/
def ladderEll (L : ℝ) (j u v : ℕ) : ℕ := momentExp (seqH L j) (seqH L (j - 1)) u v

/-- `#V_j ≤ H_j (b_j − a_j) + 2` for `j < J`. -/
theorem card_blocks_ladder_le {L : ℝ} (hL : 2 ^ 20 ≤ L) (X : ℝ) (j : ℕ) :
    (((ladderScale hL X j).image (blk (seqH L j))).card : ℝ)
      ≤ seqH L j * (seqB L j - seqA L j) + 2 := by
  obtain ⟨hH3, -, -⟩ := seqH_props hL j
  have ha := one_le_seqA hL j
  have hab := seqA_add_one_le_seqB hL j
  have h := card_blocks_le (Pr := ladderScale hL X j) (H := seqH L j) (by linarith)
    (P := Real.exp (seqA L j)) (Q := Real.exp (seqB L j))
    (Real.one_le_exp (by linarith)) (Real.exp_le_exp.mpr (by linarith))
    (fun p hp => mem_ladderScale_bounds hL X hp)
  rwa [Real.log_exp, Real.log_exp] at h

/-- `#V_j ≤ 2^{11} b_{j−1}^{20}` for `j ≥ 1`. -/
theorem card_blocks_succ_le {L : ℝ} (hL : 2 ^ 20 ≤ L) (X : ℝ) (j : ℕ) :
    (((ladderScale hL X (j + 1)).image (blk (seqH L (j + 1)))).card : ℝ)
      ≤ 2 ^ 11 * seqB L j ^ 20 := by
  have h := card_blocks_ladder_le hL X (j + 1)
  have ha : seqA L (j + 1) = 2 * seqB L j ^ 2 := rfl
  have hH : seqH L (j + 1) = seqA L (j + 1) ^ 8 := rfl
  have hb : seqB L (j + 1) = seqA L (j + 1) ^ 2 := seqB_succ_eq L j
  have hb1 := one_le_seqB (by linarith : (2 : ℝ) ≤ L) j
  have ha1 := one_le_seqA hL (j + 1)
  rw [hH, hb] at h
  have h2 : seqA L (j + 1) ^ 8 * (seqA L (j + 1) ^ 2 - seqA L (j + 1)) + 2
      ≤ 2 * seqA L (j + 1) ^ 10 := by
    have : 2 ≤ seqA L (j + 1) ^ 10 := by
      have : (2 : ℝ) ≤ seqA L (j + 1) := by rw [ha]; nlinarith
      calc (2 : ℝ) ≤ seqA L (j + 1) := this
        _ = seqA L (j + 1) ^ 1 := (pow_one _).symm
        _ ≤ seqA L (j + 1) ^ 10 := pow_le_pow_right₀ ha1 (by norm_num)
    have h8 : 0 ≤ seqA L (j + 1) ^ 8 * seqA L (j + 1) := by positivity
    nlinarith
  have h3 : 2 * seqA L (j + 1) ^ 10 = 2 ^ 11 * seqB L j ^ 20 := by rw [ha]; ring
  linarith

/-- `#V_j ≤ (2b_j)^{26}` for every `j`. -/
theorem card_blocks_le_two_b {L : ℝ} (hL : 2 ^ 20 ≤ L) (X : ℝ) (j : ℕ) :
    (((ladderScale hL X j).image (blk (seqH L j))).card : ℝ) ≤ (2 * seqB L j) ^ 26 := by
  have h := card_blocks_ladder_le hL X j
  have hb1 := one_le_seqB (by linarith : (2 : ℝ) ≤ L) j
  cases j with
  | zero =>
    simp only [seqH, seqB, seqA] at h ⊢
    have hL1 : (1 : ℝ) ≤ L := by linarith
    have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
    have h1 : L ^ 25 * (L / 2 - 200 * Real.log L) + 2 ≤ L ^ 26 := by
      have : L ^ 25 * (L / 2 - 200 * Real.log L) ≤ L ^ 25 * (L / 2) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      have h26 : L ^ 26 = L ^ 25 * L := by ring
      have : (2 : ℝ) ≤ L ^ 25 * (L / 2) := by
        have : (1 : ℝ) ≤ L ^ 25 := one_le_pow₀ hL1
        nlinarith
      nlinarith
    calc _ ≤ L ^ 25 * (L / 2 - 200 * Real.log L) + 2 := h
      _ ≤ L ^ 26 := h1
      _ = (2 * (L / 2)) ^ 26 := by ring
  | succ j =>
    have hH : seqH L (j + 1) = seqA L (j + 1) ^ 8 := rfl
    have hb : seqB L (j + 1) = seqA L (j + 1) ^ 2 := seqB_succ_eq L j
    have ha1 := one_le_seqA hL (j + 1)
    rw [hH, hb] at h
    rw [hb]
    have h2 : seqA L (j + 1) ^ 8 * (seqA L (j + 1) ^ 2 - seqA L (j + 1)) + 2
        ≤ 2 * seqA L (j + 1) ^ 10 := by
      have : 2 ≤ seqA L (j + 1) ^ 10 := by
        have h2a : (2 : ℝ) ≤ seqA L (j + 1) := by
          have := seqA_succ_ge (by linarith : (2 : ℝ) ≤ L) j; nlinarith
        calc (2 : ℝ) ≤ seqA L (j + 1) := h2a
          _ = seqA L (j + 1) ^ 1 := (pow_one _).symm
          _ ≤ seqA L (j + 1) ^ 10 := pow_le_pow_right₀ ha1 (by norm_num)
      have h8 : 0 ≤ seqA L (j + 1) ^ 8 * seqA L (j + 1) := by positivity
      nlinarith
    have h3 : 2 * seqA L (j + 1) ^ 10 ≤ (2 * seqA L (j + 1) ^ 2) ^ 26 := by
      have h20 : seqA L (j + 1) ^ 10 ≤ (seqA L (j + 1) ^ 2) ^ 26 := by
        rw [← pow_mul]; exact pow_le_pow_right₀ ha1 (by norm_num)
      have h2pow : (2 : ℝ) ≤ 2 ^ 26 := by norm_num
      calc 2 * seqA L (j + 1) ^ 10 ≤ 2 ^ 26 * (seqA L (j + 1) ^ 2) ^ 26 :=
            mul_le_mul h2pow h20 (by positivity) (by positivity)
        _ = (2 * seqA L (j + 1) ^ 2) ^ 26 := by rw [mul_pow]
    linarith

end

end GaloisForLFunctions.MatomakiRadziwill
