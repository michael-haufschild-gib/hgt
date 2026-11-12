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
  have hval : seqH L (j + 1) * (seqB L (j + 1) - seqA L (j + 1)) + 2
      = seqA L (j + 1) ^ 8 * (seqA L (j + 1) ^ 2 - seqA L (j + 1)) + 2 := by rw [hH, hb]
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
    have hval : seqH L (j + 1) * (seqB L (j + 1) - seqA L (j + 1)) + 2
        = seqA L (j + 1) ^ 8 * (seqA L (j + 1) ^ 2 - seqA L (j + 1)) + 2 := by rw [hH, hb]
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

/-- `e^{b_j} ≤ X` below the top scale (`log X ≥ 1`). -/
theorem exp_seqB_le_X {L : ℝ} (hL : 2 ^ 20 ≤ L) {X : ℝ} (hX : Real.exp 1 ≤ X) {j : ℕ}
    (hj : j < ladderJ hL X) : Real.exp (seqB L j) ≤ X := by
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hlogX : 1 ≤ Real.log X := by rw [Real.le_log_iff_exp_le hX0]; exact hX
  have h1 := seqB_le_of_lt_ladderJ hL X hj
  have h2 : ladderTopLow X ≤ Real.log X := by
    unfold ladderTopLow
    calc Real.log X ^ (93 / 100 : ℝ) ≤ Real.log X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hlogX (by norm_num)
      _ = Real.log X := Real.rpow_one _
  calc Real.exp (seqB L j) ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr (by linarith)
    _ = X := Real.exp_log hX0

/-- **A moment step of the concrete ladder.** -/
theorem step_term_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {L : ℝ} (hL : 2 ^ 20 ≤ L) {X : ℕ}
    (hX : Real.exp 1 ≤ (X : ℝ)) {W : ℝ} (hW : 1 ≤ W) (hWX : W ≤ X) {j : ℕ}
    (hj : j + 1 < ladderJ hL (X : ℝ)) (rest : ℕ → Prop) [DecidablePred rest] :
    (((ladderScale hL X (j + 1)).image (blk (seqH L (j + 1)))).card : ℝ)
        * ∑ v ∈ (ladderScale hL X (j + 1)).image (blk (seqH L (j + 1))),
          ∑ u ∈ (ladderScale hL X j).image (blk (seqH L j)),
          ladderC L (j + 1) v ^ 2 / ladderC L j u ^ (2 * ladderEll L (j + 1) u v)
          * (∫ w in Icc (-W) W, ‖blockQ f (ladderScale hL X j) (seqH L j) u w ^ ladderEll L (j + 1) u v
              * blockR f (ladderScale hL X (j + 1)) rest X (seqH L (j + 1)) v w‖ ^ 2)
      ≤ 144 * Real.exp 1 * 2 ^ 48 * seqB L j ^ 66 * Real.exp (-(152 / 100) * seqB L j) := by
  have hj0 : j < ladderJ hL (X : ℝ) := by omega
  obtain ⟨hH3, hHa, hHe⟩ := seqH_props hL j
  obtain ⟨hH3', hHa', hHe'⟩ := seqH_props hL (j + 1)
  have ha0 := one_le_seqA hL j
  have ha1 := one_le_seqA hL (j + 1)
  have hb0 := one_le_seqB (by linarith : (2 : ℝ) ≤ L) j
  have hX1 : 1 ≤ X := by
    have : (1 : ℝ) ≤ X := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hX
    exact_mod_cast this
  have hell : ∀ u v, ladderEll L (j + 1) u v = momentExp (seqH L (j + 1)) (seqH L j) u v := by
    intro u v; simp [ladderEll]
  simp only [hell, ladderC]
  have hmom := moment_step_le hf (Pr' := ladderScale hL X j) ((ladderConfig hL X).prime_scale j)
    hH3 (P' := Real.exp (seqA L j)) (Q' := Real.exp (seqB L j)) (Real.one_le_exp (by linarith))
    (fun p hp => mem_ladderScale_bounds hL X hp) hHe (by rw [Real.log_exp]; linarith) rest
    (Pr := ladderScale hL X (j + 1)) (X := X) (H := seqH L (j + 1)) (by linarith)
    (P := Real.exp (seqA L (j + 1))) (Q := Real.exp (seqB L (j + 1)))
    (Real.one_le_exp (by linarith)) (fun p hp => mem_ladderScale_bounds hL X hp)
    (exp_seqB_le_X hL hX hj) (by rw [Real.log_exp]; linarith) (α := ladderAlpha)
    (by unfold ladderAlpha; norm_num) hW hWX (Real.one_le_exp (by linarith))
    (by rw [Real.log_exp, Real.log_exp]; exact seq_step_condition hL j)
  refine le_trans hmom ?_
  rw [Real.log_exp, Real.log_exp]
  -- the numerical evaluation
  set b := seqB L j with hbdef
  have hcV1 := card_blocks_succ_le hL (X : ℝ) j
  have hcV0 := card_blocks_le_two_b hL (X : ℝ) j
  rw [← hbdef] at hcV1 hcV0
  have hexp1 : Real.exp (-((seqA L (j + 1) - 1 / seqH L (j + 1)) / b))
      ≤ Real.exp 1 * Real.exp (-2 * b) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have ha : seqA L (j + 1) = 2 * b ^ 2 := rfl
    have hinv : 1 / seqH L (j + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have hb0' : 0 < b := by linarith
    rw [ha]
    have : 2 * b - 1 ≤ (2 * b ^ 2 - 1 / seqH L (j + 1)) / b := by
      rw [le_div_iff₀ hb0']
      nlinarith
    linarith
  have hpow : Real.exp b ^ (2 * ladderAlpha) = Real.exp (2 * ladderAlpha * b) := by
    rw [← Real.exp_mul]; ring_nf
  rw [hpow]
  have hV0 : (0 : ℝ) ≤ (((ladderScale hL X j).image (blk (seqH L j))).card : ℝ) := Nat.cast_nonneg _
  have hV1 : (0 : ℝ) ≤ (((ladderScale hL X (j + 1)).image (blk (seqH L (j + 1)))).card : ℝ) :=
    Nat.cast_nonneg _
  have hE0 : 0 ≤ Real.exp (2 * ladderAlpha * b) := (Real.exp_pos _).le
  have hfac : 0 ≤ 144 * Real.exp (-((seqA L (j + 1) - 1 / seqH L (j + 1)) / b)) := by positivity
  calc (((ladderScale hL X (j + 1)).image (blk (seqH L (j + 1)))).card : ℝ) ^ 2
        * (((ladderScale hL X j).image (blk (seqH L j))).card : ℝ) * Real.exp (2 * ladderAlpha * b)
        * (144 * Real.exp (-((seqA L (j + 1) - 1 / seqH L (j + 1)) / b)))
      ≤ (2 ^ 11 * b ^ 20) ^ 2 * (2 * b) ^ 26 * Real.exp (2 * ladderAlpha * b)
        * (144 * (Real.exp 1 * Real.exp (-2 * b))) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul
          (pow_le_pow_left₀ hV1 hcV1 2) hcV0 hV0 (by positivity)) hE0)
          (mul_le_mul_of_nonneg_left hexp1 (by norm_num)) hfac (by positivity)
    _ = 144 * Real.exp 1 * 2 ^ 48 * b ^ 66 * Real.exp (-(152 / 100) * b) := by
        have : Real.exp (2 * ladderAlpha * b) * Real.exp (-2 * b) = Real.exp (-(152 / 100) * b) := by
          rw [← Real.exp_add]; unfold ladderAlpha; congr 1; ring
        rw [← this]
        ring

end

end GaloisForLFunctions.MatomakiRadziwill
