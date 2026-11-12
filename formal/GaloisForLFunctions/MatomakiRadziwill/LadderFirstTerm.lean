import GaloisForLFunctions.MatomakiRadziwill.LadderStepTerm

/-!
# The first step of the concrete ladder

For `W ≤ X e^{-L/2}` (frequencies up to `X/√h`), the first step of the master inequality is at most
(`first_term_le`)

`L^{52} (10π e^{-αL} + 40e² e^{-96 log L})`,   `α = 6/25`.

`first_step_le` gives `#V_0² (10π (W/X) Q_0^{1−2α} + 40e² P_0^{-2α})` with `P_0 = e^{a_0} = L^{200}`,
`Q_0 = e^{L/2}`, and `#V_0 ≤ (2b_0)^{26} = L^{26}`.
-/

open Finset MeasureTheory Set RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- **The first step of the concrete ladder.** -/
theorem first_term_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {L : ℝ} (hL : 2 ^ 20 ≤ L) {X : ℕ}
    (hX : Real.exp 1 ≤ (X : ℝ)) (hJ : 0 < ladderJ hL (X : ℝ)) {W : ℝ} (hW : 1 ≤ W)
    (hWX : W ≤ X * Real.exp (-(L / 2))) (rest : ℕ → Prop) [DecidablePred rest] :
    (((ladderScale hL X 0).image (blk (seqH L 0))).card : ℝ)
        * ∑ v ∈ (ladderScale hL X 0).image (blk (seqH L 0)), ladderC L 0 v ^ 2
          * (∫ w in Icc (-W) W, ‖blockR f (ladderScale hL X 0) rest X (seqH L 0) v w‖ ^ 2)
      ≤ L ^ 52 * (10 * Real.pi * Real.exp (-(6 / 25) * L)
          + 40 * Real.exp 1 * Real.exp 1 * Real.exp (-96 * Real.log L)) := by
  obtain ⟨hH3, -, -⟩ := seqH_props hL 0
  have ha0 := one_le_seqA hL 0
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hX1 : 1 ≤ X := by
    have : (1 : ℝ) ≤ X := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hX
    exact_mod_cast this
  have hbase := first_step_le hf (Pr := ladderScale hL X 0) rest hX1 (H := seqH L 0)
    (by linarith) (P := Real.exp (seqA L 0)) (Q := Real.exp (seqB L 0))
    (Real.one_le_exp (by linarith)) (fun p hp => mem_ladderScale_bounds hL X hp)
    (exp_seqB_le_X hL hX hJ) (α := ladderAlpha) (by unfold ladderAlpha; norm_num)
    (by unfold ladderAlpha; norm_num) hW
  simp only [ladderC]
  refine le_trans hbase ?_
  -- the numerical evaluation
  have hcV := card_blocks_le_two_b hL (X : ℝ) 0
  have hb0 : seqB L 0 = L / 2 := rfl
  have ha0' : seqA L 0 = 200 * Real.log L := rfl
  rw [hb0] at hcV
  have hcV' : (((ladderScale hL X 0).image (blk (seqH L 0))).card : ℝ) ^ 2 ≤ L ^ 52 := by
    calc _ ≤ ((2 * (L / 2)) ^ 26) ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hcV 2
      _ = L ^ 52 := by ring
  have hQ : Real.exp (seqB L 0) ^ (1 - 2 * ladderAlpha) = Real.exp ((1 - 2 * ladderAlpha) * (L / 2)) := by
    rw [← Real.exp_mul, hb0]; ring_nf
  have hP : Real.exp (seqA L 0) ^ (-(2 * ladderAlpha)) = Real.exp (-96 * Real.log L) := by
    rw [← Real.exp_mul, ha0']; unfold ladderAlpha; ring_nf
  rw [hQ, hP]
  have hWX' : W / X ≤ Real.exp (-(L / 2)) := by
    rw [div_le_iff₀ hX0]; linarith
  have hfirst : 10 * Real.pi * (W / X) * Real.exp ((1 - 2 * ladderAlpha) * (L / 2))
      ≤ 10 * Real.pi * Real.exp (-(6 / 25) * L) := by
    have h1 : (W / X) * Real.exp ((1 - 2 * ladderAlpha) * (L / 2))
        ≤ Real.exp (-(L / 2)) * Real.exp ((1 - 2 * ladderAlpha) * (L / 2)) :=
      mul_le_mul_of_nonneg_right hWX' (Real.exp_pos _).le
    have h2 : Real.exp (-(L / 2)) * Real.exp ((1 - 2 * ladderAlpha) * (L / 2))
        = Real.exp (-(6 / 25) * L) := by
      rw [← Real.exp_add]; unfold ladderAlpha; congr 1; ring
    have := Real.pi_pos
    nlinarith
  have hinner0 : 0 ≤ 10 * Real.pi * (W / X) * Real.exp ((1 - 2 * ladderAlpha) * (L / 2))
      + 40 * Real.exp 1 * Real.exp 1 * Real.exp (-96 * Real.log L) := by
    have := Real.pi_pos; have : 0 ≤ W / X := by positivity
    positivity
  calc (((ladderScale hL X 0).image (blk (seqH L 0))).card : ℝ) ^ 2
        * (10 * Real.pi * (W / X) * Real.exp ((1 - 2 * ladderAlpha) * (L / 2))
          + 40 * Real.exp 1 * Real.exp 1 * Real.exp (-96 * Real.log L))
      ≤ L ^ 52 * (10 * Real.pi * (W / X) * Real.exp ((1 - 2 * ladderAlpha) * (L / 2))
          + 40 * Real.exp 1 * Real.exp 1 * Real.exp (-96 * Real.log L)) :=
        mul_le_mul_of_nonneg_right hcV' hinner0
    _ ≤ L ^ 52 * (10 * Real.pi * Real.exp (-(6 / 25) * L)
          + 40 * Real.exp 1 * Real.exp 1 * Real.exp (-96 * Real.log L)) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        linarith

end

end GaloisForLFunctions.MatomakiRadziwill
