import GaloisForLFunctions.MatomakiRadziwill.LadderMaster

/-!
# Numerical bounds for the terms of the master inequality

For a scale of primes in `[P, Q]` (reals, `P ≥ 1`), block width `H > 0` and thresholds
`c(v) = e^{-αv/H}`, `0 < α ≤ 1/2`:

* `ramErr W X H P ≤ 256 (10/H + 16/P)` for `W ≤ X` (`ramErr_le`);
* the blocks satisfy `H log P − 1 ≤ v ≤ H log Q`, and there are at most `H(log Q − log P) + 2`
  of them (`blk_bounds`, `card_blocks_le`);
* the first step: `#V Σ_v c(v)² (10πW/lo_v + 40e) ≤ #V² (10π(W/X)Q^{1−2α} + 40e²P^{-2α})`
  (`first_step_le`), `lo_v = Xe^{-v/H}`;
* the moment step is bounded in `LadderNumericsMoment`.
-/

open Finset MeasureTheory Set RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

/-- **The Ramaré error is `O(1/H + 1/P)`.** -/
theorem ramErr_le {W : ℝ} {X : ℕ} (hX : 1 ≤ X) (hW0 : 0 ≤ W) (hWX : W ≤ X) {H : ℝ} (hH : 0 < H)
    {P : ℕ} (hP : 0 < P) : ramErr W X H P ≤ 256 * (10 / H + 16 / P) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hP0 : (0 : ℝ) < P := by exact_mod_cast hP
  have hpi : Real.pi ≤ 16 / 5 := by linarith [Real.pi_lt_d2]
  have he : Real.exp 1 ≤ 14 / 5 := by linarith [Real.exp_one_lt_d9]
  have h1 : 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((8 * X : ℕ) : ℝ) ≤ 64 * X := by
    push_cast
    have ha : 5 * Real.pi / 2 * W ≤ 8 * X := by
      have h5 : 5 * Real.pi / 2 ≤ 8 := by linarith
      calc 5 * Real.pi / 2 * W ≤ 8 * W := mul_le_mul_of_nonneg_right h5 hW0
        _ ≤ 8 * X := by linarith
    have hb : 5 * Real.exp 1 / 2 * (8 * (X : ℝ)) ≤ 56 * X := by nlinarith
    linarith
  have h2 : 4 / (X : ℝ) ^ 2 * (10 * X / H + 16 * X / P) = 4 / X * (10 / H + 16 / P) := by
    field_simp
  have h3 : 0 ≤ 4 / (X : ℝ) ^ 2 * (10 * X / H + 16 * X / P) := by positivity
  rw [ramErr]
  calc (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((8 * X : ℕ) : ℝ))
        * (4 / (X : ℝ) ^ 2 * (10 * X / H + 16 * X / P))
      ≤ 64 * X * (4 / (X : ℝ) ^ 2 * (10 * X / H + 16 * X / P)) :=
        mul_le_mul_of_nonneg_right h1 h3
    _ = 256 * (10 / H + 16 / P) := by rw [h2]; field_simp; ring

/-- The block of a prime in `[P, Q]` lies between `H log P − 1` and `H log Q`. -/
theorem blk_bounds {H : ℝ} (hH : 0 < H) {P Q : ℝ} (hP : 1 ≤ P) {p : ℕ} (hpP : P ≤ p)
    (hpQ : (p : ℝ) ≤ Q) : H * Real.log P - 1 ≤ (blk H p : ℝ) ∧ (blk H p : ℝ) ≤ H * Real.log Q := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hlogp : Real.log P ≤ Real.log p := Real.log_le_log (by linarith) hpP
  have hlogq : Real.log p ≤ Real.log Q := Real.log_le_log hp0 hpQ
  have hnn : 0 ≤ H * Real.log p := mul_nonneg hH.le (Real.log_nonneg (by linarith))
  have h1 : (blk H p : ℝ) ≤ H * Real.log p := Nat.floor_le hnn
  have h2 : H * Real.log p < (blk H p : ℝ) + 1 := Nat.lt_floor_add_one _
  constructor
  · nlinarith
  · nlinarith

/-- **The number of blocks of a scale.** -/
theorem card_blocks_le {Pr : Finset ℕ} {H : ℝ} (hH : 0 < H) {P Q : ℝ} (hP : 1 ≤ P) (hPQ : P ≤ Q)
    (hPr : ∀ p ∈ Pr, P ≤ p ∧ (p : ℝ) ≤ Q) :
    ((Pr.image (blk H)).card : ℝ) ≤ H * (Real.log Q - Real.log P) + 2 := by
  classical
  have hlogPQ : Real.log P ≤ Real.log Q := Real.log_le_log (by linarith) hPQ
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg hP
  have hRHS : 2 ≤ H * (Real.log Q - Real.log P) + 2 := by
    have : 0 ≤ H * (Real.log Q - Real.log P) := mul_nonneg hH.le (by linarith)
    linarith
  set lo : ℕ := ⌈H * Real.log P - 1⌉₊ with hlo
  set hi : ℕ := ⌊H * Real.log Q⌋₊ with hhi
  have hsub : Pr.image (blk H) ⊆ Finset.Icc lo hi := by
    intro v hv
    rw [Finset.mem_image] at hv
    obtain ⟨p, hp, rfl⟩ := hv
    obtain ⟨h1, h2⟩ := blk_bounds hH hP (hPr p hp).1 (hPr p hp).2
    rw [Finset.mem_Icc]
    exact ⟨Nat.ceil_le.mpr h1, Nat.le_floor h2⟩
  have hcard := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcard
  have hQ : 0 ≤ H * Real.log Q := mul_nonneg hH.le (by linarith)
  have hhi' : (hi : ℝ) ≤ H * Real.log Q := Nat.floor_le hQ
  have hlo' : H * Real.log P - 1 ≤ (lo : ℝ) := Nat.le_ceil _
  have h2 : ((Pr.image (blk H)).card : ℝ) ≤ (((hi + 1 - lo : ℕ)) : ℝ) := by exact_mod_cast hcard
  rcases le_total lo (hi + 1) with h | h
  · rw [Nat.cast_sub h] at h2
    push_cast at h2
    nlinarith
  · rw [Nat.sub_eq_zero_of_le h, Nat.cast_zero] at h2
    linarith

/-- **The first step, numerically.** -/
theorem first_step_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {Pr : Finset ℕ}
    (rest : ℕ → Prop) [DecidablePred rest] {X : ℕ} (hX : 1 ≤ X) {H : ℝ} (hH1 : 1 ≤ H) {P Q : ℝ}
    (hP : 1 ≤ P)
    (hPr : ∀ p ∈ Pr, P ≤ p ∧ (p : ℝ) ≤ Q) (hQX : Q ≤ X) {α : ℝ} (hα0 : 0 < α)
    (hα : α ≤ 1 / 2) {W : ℝ} (hW : 1 ≤ W) :
    ((Pr.image (blk H)).card : ℝ) * ∑ v ∈ Pr.image (blk H), Real.exp (-α * v / H) ^ 2
        * (∫ w in Icc (-W) W, ‖blockR f Pr rest X H v w‖ ^ 2)
      ≤ ((Pr.image (blk H)).card : ℝ) ^ 2
          * (10 * Real.pi * (W / X) * Q ^ (1 - 2 * α)
            + 40 * Real.exp 1 * Real.exp 1 * P ^ (-(2 * α))) := by
  classical
  have hH : 0 < H := by linarith
  set V := Pr.image (blk H) with hV
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hterm : ∀ v ∈ V, Real.exp (-α * v / H) ^ 2
      * (∫ w in Icc (-W) W, ‖blockR f Pr rest X H v w‖ ^ 2)
      ≤ 10 * Real.pi * (W / X) * Q ^ (1 - 2 * α)
          + 40 * Real.exp 1 * Real.exp 1 * P ^ (-(2 * α)) := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hb1, hb2⟩ := blk_bounds hH hP (hPr p hp).1 (hPr p hp).2
    have hQ1 : 1 ≤ Q := le_trans hP (le_trans (hPr p hp).1 (hPr p hp).2)
    set u : ℝ := (blk H p : ℝ) / H with hu
    have hu1 : u ≤ Real.log Q := by rw [hu, div_le_iff₀ hH]; linarith
    have hu2 : Real.log P - 1 / H ≤ u := by
      rw [hu, le_div_iff₀ hH]; field_simp; linarith
    have hlo : 1 ≤ cofLo X H (blk H p) := by
      rw [cofLo, show -((blk H p : ℕ) : ℝ) / H = -u by rw [hu]; ring, Real.exp_neg,
        ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _), one_mul]
      calc Real.exp u ≤ Real.exp (Real.log Q) := Real.exp_le_exp.mpr hu1
        _ = Q := Real.exp_log (by linarith)
        _ ≤ X := hQX
    have hR := integral_normSq_blockR_le hf Pr rest X H (blk H p) hlo hW
    have hc2 : Real.exp (-α * (blk H p : ℝ) / H) ^ 2 = Real.exp (-(2 * α) * u) := by
      rw [← Real.exp_nat_mul, hu]; congr 1; push_cast; ring
    have hlo_eq : cofLo X H (blk H p) = X * Real.exp (-u) := by
      rw [cofLo, hu]; congr 2; ring
    have hexp0 : 0 ≤ Real.exp (-(2 * α) * u) := (Real.exp_pos _).le
    rw [hc2]
    calc Real.exp (-(2 * α) * u) * (∫ w in Icc (-W) W, ‖blockR f Pr rest X H (blk H p) w‖ ^ 2)
        ≤ Real.exp (-(2 * α) * u) * (10 * Real.pi * W / cofLo X H (blk H p) + 40 * Real.exp 1) :=
          mul_le_mul_of_nonneg_left hR hexp0
      _ = 10 * Real.pi * (W / X) * Real.exp ((1 - 2 * α) * u)
            + 40 * Real.exp 1 * Real.exp (-(2 * α) * u) := by
          have hsplit : Real.exp (-(2 * α) * u) = Real.exp ((1 - 2 * α) * u) * Real.exp (-u) := by
            rw [← Real.exp_add]; congr 1; ring
          have hne : Real.exp (-u) ≠ 0 := (Real.exp_pos _).ne'
          rw [hlo_eq, hsplit]
          field_simp
      _ ≤ 10 * Real.pi * (W / X) * Q ^ (1 - 2 * α)
            + 40 * Real.exp 1 * Real.exp 1 * P ^ (-(2 * α)) := by
          have hQ0 : 0 < Q := by linarith
          have hP0 : 0 < P := by linarith
          have e1 : Real.exp ((1 - 2 * α) * u) ≤ Q ^ (1 - 2 * α) := by
            rw [Real.rpow_def_of_pos hQ0]
            exact Real.exp_le_exp.mpr (by nlinarith)
          have e2 : Real.exp (-(2 * α) * u) ≤ Real.exp 1 * P ^ (-(2 * α)) := by
            rw [Real.rpow_def_of_pos hP0, ← Real.exp_add]
            refine Real.exp_le_exp.mpr ?_
            have h1H : 2 * α * (1 / H) ≤ 1 :=
              mul_le_one₀ (by linarith) (by positivity) (by rw [div_le_one hH]; exact hH1)
            have h2 : -(2 * α) * u ≤ -(2 * α) * (Real.log P - 1 / H) := by nlinarith
            nlinarith
          have hW0 : 0 ≤ W / X := by positivity
          have := Real.pi_pos
          have he0 := Real.exp_pos 1
          nlinarith [mul_le_mul_of_nonneg_left e1 (by positivity : (0 : ℝ) ≤ 10 * Real.pi * (W / X)),
            mul_le_mul_of_nonneg_left e2 (by positivity : (0 : ℝ) ≤ 40 * Real.exp 1)]
  have hsum := sum_le_sum hterm
  rw [sum_const, nsmul_eq_mul] at hsum
  calc (V.card : ℝ) * ∑ v ∈ V, Real.exp (-α * v / H) ^ 2
        * (∫ w in Icc (-W) W, ‖blockR f Pr rest X H v w‖ ^ 2)
      ≤ (V.card : ℝ) * ((V.card : ℝ) * (10 * Real.pi * (W / X) * Q ^ (1 - 2 * α)
          + 40 * Real.exp 1 * Real.exp 1 * P ^ (-(2 * α)))) :=
        mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = (V.card : ℝ) ^ 2 * (10 * Real.pi * (W / X) * Q ^ (1 - 2 * α)
          + 40 * Real.exp 1 * Real.exp 1 * P ^ (-(2 * α))) := by ring

end

end GaloisForLFunctions.MatomakiRadziwill
