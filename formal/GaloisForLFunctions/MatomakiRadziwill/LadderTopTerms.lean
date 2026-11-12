import GaloisForLFunctions.MatomakiRadziwill.LadderLastScale
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicProductCostBounds

/-!
# The top-scale terms of the concrete ladder

For `X` with `ℓ = log X ≥ 1` and frequencies `W ≤ X`:

* the top scale has at most `ℓ² + 2` blocks (`card_topBlocks_le`), and each top cofactor range
  starts at `lo ≥ e^{ℓ − ℓ^{0.96}} ≥ 1` (`top_cofLo_bounds`);
* the Halász–Montgomery kernel constant is at most `60000 ℓ e^{ℓ/2}` (`kernel_far_le`);
* the exceptional set of the last ladder scale has measure `≤ (2ℓ)^{26} · 144 e^{0.48ℓ} e^{ℓ^{0.96}}`
  (Markov), so the exceptional term is at most (`top_exceptional_le`)

  `(ℓ² + 2)² ρ² (6 + C ℓ^{27} e^{-ℓ/50 + 2ℓ^{0.96}} + 384(ℓ + 3))`,   `C = 4 · 60000 · 144 · 2^{26}`;

  the gain `e^{-ℓ/50} = X^{-1/50}` is `√X · X^{0.48} / X`;
* the top Ramaré error is `≤ 256(10/ℓ + 16 e^{-ℓ^{0.93}})` (`top_ramErr_le`) and the harmonic mass
  of the top scale is `≥ 0.03 log ℓ − C_M` (`top_density_ge`);
* with at most `X` primes per scale, the integers outside the rough set contribute at most
  `216 (Σ_j 1/A_j + 1/A*)` for lower bounds `A` of the harmonic masses (`LadderScales.nonrough_le`).
-/

open Finset MeasureTheory Set RHTower.Sieve

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

theorem one_le_log_of_exp_le {X : ℝ} (hX : Real.exp 1 ≤ X) : 1 ≤ Real.log X := by
  rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 1) hX)]; exact hX

theorem twenty_le_exp_three : (20 : ℝ) ≤ Real.exp 3 := by
  have h := Real.exp_one_gt_d9
  have e : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
  have h3 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h.le 3
  rw [e]; norm_num at h3 ⊢; linarith

theorem ladderTop_le {X : ℝ} (hX : 1 ≤ Real.log X) :
    ladderTopLow X ≤ ladderTopHigh X ∧ ladderTopHigh X ≤ Real.log X := by
  unfold ladderTopLow ladderTopHigh
  refine ⟨Real.rpow_le_rpow_of_exponent_le hX (by norm_num), ?_⟩
  calc Real.log X ^ (96 / 100 : ℝ) ≤ Real.log X ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hX (by norm_num)
    _ = Real.log X := Real.rpow_one _

theorem ladderTopLow_nonneg {X : ℝ} (hX : 0 ≤ Real.log X) : 0 ≤ ladderTopLow X :=
  Real.rpow_nonneg hX _

/-- The top scale has at most `ℓ² + 2` blocks. -/
theorem card_topBlocks_le {X : ℝ} (hX : 1 ≤ Real.log X) :
    (((topScale X).image (blk (Real.log X))).card : ℝ) ≤ Real.log X ^ 2 + 2 := by
  obtain ⟨hlh, hhX⟩ := ladderTop_le hX
  have hlo0 := ladderTopLow_nonneg (by linarith : 0 ≤ Real.log X)
  have h := card_blocks_le (Pr := topScale X) (H := Real.log X) (by linarith)
    (P := Real.exp (ladderTopLow X)) (Q := Real.exp (ladderTopHigh X))
    (Real.one_le_exp hlo0) (Real.exp_le_exp.mpr hlh) (fun p hp => mem_topScale_bounds hp)
  rw [Real.log_exp, Real.log_exp] at h
  have : Real.log X * (ladderTopHigh X - ladderTopLow X) ≤ Real.log X * Real.log X :=
    mul_le_mul_of_nonneg_left (by linarith) (by linarith)
  nlinarith

/-- **The far kernel constant at frequencies up to `X`.** -/
theorem kernel_far_le {X : ℕ} (hX : Real.exp 1 ≤ (X : ℝ)) {W : ℝ} (hW : 1 ≤ W) (hWX : W ≤ X) :
    plainKernelFarConst (4 * X) (2 * Real.pi * W)
      ≤ 60000 * Real.log X * Real.exp (Real.log X / 2) := by
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hX1 : (1 : ℝ) ≤ X := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hX
  have hlogX := one_le_log_of_exp_le hX
  have hN : 1 ≤ 4 * X := by
    have : 1 ≤ X := by exact_mod_cast hX1
    omega
  have hpi := Real.pi_gt_three
  have hpi4 : Real.pi < 3.15 := Real.pi_lt_d2
  have hT : (1 : ℝ) ≤ 2 * Real.pi * W := by nlinarith
  have hbase := plainKernelFarConst_le_log hN hT
  have hsqX : Real.sqrt X = Real.exp (Real.log X / 2) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hX0]; congr 1; ring
  have hsq : Real.sqrt (2 * (2 * Real.pi * W)) ≤ 4 * Real.exp (Real.log X / 2) := by
    have h1 : 2 * (2 * Real.pi * W) ≤ 16 * X := by nlinarith
    calc Real.sqrt (2 * (2 * Real.pi * W)) ≤ Real.sqrt (16 * X) := Real.sqrt_le_sqrt h1
      _ = 4 * Real.sqrt X := by
        rw [Real.sqrt_mul (by norm_num), show (16 : ℝ) = 4 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num)]
      _ = 4 * Real.exp (Real.log X / 2) := by rw [hsqX]
  have he3 := twenty_le_exp_three
  have hlogT : Real.log (2 * (2 * Real.pi * W) + 1) ≤ 4 * Real.log X := by
    have h1 : 2 * (2 * Real.pi * W) + 1 ≤ 14 * X := by nlinarith
    have h14 : Real.log 14 ≤ 3 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
    calc Real.log (2 * (2 * Real.pi * W) + 1) ≤ Real.log (14 * X) :=
          Real.log_le_log (by positivity) h1
      _ = Real.log 14 + Real.log X := Real.log_mul (by norm_num) hX0.ne'
      _ ≤ 4 * Real.log X := by linarith
  have hlogN : Real.log ((4 * X : ℕ) : ℝ) ≤ 3 * Real.log X := by
    push_cast
    rw [Real.log_mul (by norm_num) hX0.ne']
    have : Real.log 4 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.exp_one_gt_d9
      have e : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]; nlinarith
    linarith
  have hE1 : 1 ≤ Real.exp (Real.log X / 2) := Real.one_le_exp (by linarith)
  have hf1 : 1 + 2 * Real.log (2 * (2 * Real.pi * W) + 1) ≤ 9 * Real.log X := by linarith
  have hprod : (1 + 2 * Real.log (2 * (2 * Real.pi * W) + 1))
        * (214 * Real.sqrt (2 * (2 * Real.pi * W)))
      ≤ (9 * Real.log X) * (214 * (4 * Real.exp (Real.log X / 2))) :=
    mul_le_mul hf1 (by linarith) (by positivity) (by linarith)
  have hlE : Real.log X ≤ Real.log X * Real.exp (Real.log X / 2) :=
    le_mul_of_one_le_right (by linarith) hE1
  have hEl : Real.exp (Real.log X / 2) ≤ Real.log X * Real.exp (Real.log X / 2) :=
    le_mul_of_one_le_left (by positivity) hlogX
  linarith [hprod, hsq, hlogN, hlE, hEl, hbase]

/-- The cofactor ranges of the top scale start between `e^{ℓ − ℓ^{0.96}} ≥ 1` and `X`. -/
theorem top_cofLo_bounds {X : ℕ} (hX : Real.exp 1 ≤ (X : ℝ)) {v : ℕ}
    (hv : v ∈ (topScale (X : ℝ)).image (blk (Real.log X))) :
    Real.exp (Real.log X - ladderTopHigh X) ≤ cofLo X (Real.log X) v
      ∧ 1 ≤ cofLo X (Real.log X) v ∧ cofLo X (Real.log X) v ≤ X := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
  obtain ⟨hp1, hp2⟩ := mem_topScale_bounds hp
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hlogX := one_le_log_of_exp_le hX
  obtain ⟨hlh, hhX⟩ := ladderTop_le hlogX
  have hl0 : 0 < Real.log (X : ℝ) := by linarith
  have hlo0 := ladderTopLow_nonneg hl0.le
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (Real.exp_pos _) hp1
  have hlogp0 : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (le_trans (Real.one_le_exp hlo0) hp1)
  have hlogp : Real.log (p : ℝ) ≤ ladderTopHigh X := by
    rw [Real.log_le_iff_le_exp hp0]; exact hp2
  have hblk : (blk (Real.log X) p : ℝ) ≤ Real.log X * ladderTopHigh X :=
    le_trans (Nat.floor_le (mul_nonneg hl0.le hlogp0)) (mul_le_mul_of_nonneg_left hlogp hl0.le)
  have hblk0 : (0 : ℝ) ≤ (blk (Real.log X) p : ℝ) := Nat.cast_nonneg _
  have hlow : Real.exp (Real.log X - ladderTopHigh X) ≤ cofLo X (Real.log X) (blk (Real.log X) p) := by
    have h1 : -ladderTopHigh X ≤ -(blk (Real.log X) p : ℝ) / Real.log X := by
      rw [neg_div, neg_le_neg_iff, div_le_iff₀ hl0]; linarith
    unfold cofLo
    calc Real.exp (Real.log X - ladderTopHigh X) = X * Real.exp (-ladderTopHigh X) := by
          rw [sub_eq_add_neg, Real.exp_add, Real.exp_log hX0]
      _ ≤ X * Real.exp (-(blk (Real.log X) p : ℝ) / Real.log X) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h1) hX0.le
  refine ⟨hlow, le_trans (Real.one_le_exp (by linarith)) hlow, ?_⟩
  unfold cofLo
  have : Real.exp (-(blk (Real.log X) p : ℝ) / Real.log X) ≤ 1 := by
    rw [Real.exp_le_one_iff, neg_div, neg_nonpos]; positivity
  calc (X : ℝ) * Real.exp (-(blk (Real.log X) p : ℝ) / Real.log X) ≤ X * 1 :=
        mul_le_mul_of_nonneg_left this hX0.le
    _ = X := mul_one _

/-- **The exceptional term of the concrete ladder.** -/
theorem top_exceptional_le {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {L : ℝ} (hL : 2 ^ 20 ≤ L) {X : ℕ}
    (hX : Real.exp 1 ≤ (X : ℝ)) (hJ : 2 ≤ ladderJ hL (X : ℝ))
    (hlarge : 864 * Real.log X
      ≤ (Real.log X ^ (93 / 100 : ℝ) / 4) ^ (1 / 8 : ℝ) * Real.log X ^ (93 / 100 : ℝ))
    {W : ℝ} (hWe : Real.exp 1 ≤ W) (hWX : W ≤ X) (ρ : ℝ) :
    (((ladderConfig hL (X : ℝ)).topBlocks (Real.log X)).card : ℝ) * ρ ^ 2
      * ∑ v ∈ (ladderConfig hL (X : ℝ)).topBlocks (Real.log X),
        (∫ w in Icc (-W) W ∩ ((ladderConfig hL (X : ℝ)).smallSet f (seqH L) (ladderC L)
            ((ladderConfig hL (X : ℝ)).J - 1))ᶜ,
          ‖blockR f (ladderConfig hL (X : ℝ)).top (ladderConfig hL (X : ℝ)).restTop X
            (Real.log X) v w‖ ^ 2)
      ≤ (Real.log X ^ 2 + 2) ^ 2 * ρ ^ 2
        * (6 + 4 * 60000 * 144 * 2 ^ 26 * Real.log X ^ 27
            * Real.exp (-(Real.log X / 50) + 2 * ladderTopHigh X)
          + 384 * (Real.log X + 3)) := by
  classical
  set C := ladderConfig hL (X : ℝ) with hC
  have hX0 : (0 : ℝ) < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hX1 : (1 : ℝ) ≤ X := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hX
  have hlogX := one_le_log_of_exp_le hX
  obtain ⟨hlh, hhX⟩ := ladderTop_le hlogX
  have hW1 : 1 ≤ W := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hWe
  have hW0 : 0 < W := by linarith
  set j := ladderJ hL (X : ℝ) - 1 with hj
  have hjJ : j < ladderJ hL (X : ℝ) := by omega
  -- the exceptional set and its measure (Markov at the last ladder scale)
  set E := Icc (-W) W ∩ (C.smallSet f (seqH L) (ladderC L) (C.J - 1))ᶜ with hE
  have hEm : MeasurableSet E := measurableSet_Icc.inter (C.measurableSet_smallSet f _ _ _).compl
  have hEs : E ⊆ Icc (-W) W := inter_subset_left
  obtain ⟨hH3, hHa, hHe⟩ := seqH_props hL j
  have ha1 := one_le_seqA hL j
  have hab := seqA_add_one_le_seqB hL j
  have hvol0 := exceptional_volume_le hf (Pr := ladderScale hL X j) (C.prime_scale j) hH3
    (P := Real.exp (seqA L j)) (Q := Real.exp (seqB L j)) (Real.one_le_exp (by linarith))
    (fun p hp => mem_ladderScale_bounds hL X hp) hHe (by rw [Real.log_exp]; linarith)
    (Real.one_le_exp (by linarith)) (α := ladderAlpha) (by unfold ladderAlpha; norm_num) hWe
    (by rw [Real.log_exp]; exact last_scale_condition hL hX1 hJ hlarge hW1 hWX)
  have hvolE : volume.real E ≤ _ := hvol0
  have hcard := card_blocks_le_two_b hL (X : ℝ) j
  have hbj : seqB L j ≤ ladderTopLow X := seqB_le_of_lt_ladderJ hL X hjJ
  have hb1 := one_le_seqB (by linarith : (2 : ℝ) ≤ L) j
  have hcard' : (((ladderScale hL X j).image (blk (seqH L j))).card : ℝ) ≤ (2 * Real.log X) ^ 26 :=
    le_trans hcard (pow_le_pow_left₀ (by linarith) (by linarith) 26)
  have hWa : W ^ (2 * ladderAlpha) ≤ Real.exp (Real.log X * (2 * ladderAlpha)) := by
    rw [← Real.rpow_def_of_pos hX0]
    exact Real.rpow_le_rpow hW0.le hWX (by unfold ladderAlpha; norm_num)
  have hQa : Real.exp (seqB L j) ^ (2 * ladderAlpha) ≤ Real.exp (ladderTopHigh X) := by
    rw [← Real.exp_mul]
    refine Real.exp_le_exp.mpr ?_
    unfold ladderAlpha
    nlinarith
  have hvol : volume.real E ≤ (2 * Real.log X) ^ 26
      * (144 * Real.exp (Real.log X * (2 * ladderAlpha)) * Real.exp (ladderTopHigh X)) := by
    refine le_trans hvolE (mul_le_mul hcard' ?_ (by positivity) (by positivity))
    have hQ0 := Real.rpow_nonneg (Real.exp_pos (seqB L j)).le (2 * ladderAlpha)
    have hW0' := Real.rpow_nonneg hW0.le (2 * ladderAlpha)
    have h1 : W ^ (2 * ladderAlpha) * Real.exp (seqB L j) ^ (2 * ladderAlpha)
        ≤ Real.exp (Real.log X * (2 * ladderAlpha)) * Real.exp (ladderTopHigh X) :=
      mul_le_mul hWa hQa hQ0 (Real.exp_pos _).le
    nlinarith
  -- the kernel and the logarithm of the frequency range
  have hK := kernel_far_le hX hW1 hWX
  have hlog2W : Real.log (2 + 2 * (2 * Real.pi * W)) ≤ Real.log X + 3 := by
    have hpi4 : Real.pi < 3.15 := Real.pi_lt_d2
    have h1 : 2 + 2 * (2 * Real.pi * W) ≤ 15 * X := by nlinarith
    have h15 : Real.log 15 ≤ 3 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]; linarith [twenty_le_exp_three]
    calc Real.log (2 + 2 * (2 * Real.pi * W)) ≤ Real.log (15 * X) :=
          Real.log_le_log (by positivity) h1
      _ = Real.log 15 + Real.log X := Real.log_mul (by norm_num) hX0.ne'
      _ ≤ Real.log X + 3 := by linarith
  -- Halász–Montgomery for each top cofactor
  set B := 6 + 4 * 60000 * 144 * 2 ^ 26 * Real.log X ^ 27
      * Real.exp (-(Real.log X / 50) + 2 * ladderTopHigh X) + 384 * (Real.log X + 3) with hB
  have hl0 : 0 ≤ Real.log (X : ℝ) := by linarith
  have hv : ∀ v ∈ C.topBlocks (Real.log X),
      (∫ w in E, ‖blockR f C.top C.restTop X (Real.log X) v w‖ ^ 2) ≤ B := by
    intro v hv
    obtain ⟨hlo, hlo1, hloX⟩ := top_cofLo_bounds hX hv
    have hHM := exceptional_HM_le hf C.top C.restTop X (Real.log X) v hlo1 hloX hEm hW1 hEs
    refine le_trans hHM ?_
    have hE0 : 0 ≤ volume.real E := measureReal_nonneg
    have hlo0 : 0 < cofLo X (Real.log X) v := by linarith
    have hc0 : 0 ≤ 4 * 60000 * 144 * 2 ^ 26 * Real.log X ^ 27
        * Real.exp (-(Real.log X / 50) + 2 * ladderTopHigh X) :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hl0 27)) (Real.exp_pos _).le
    have hkey : 4 * plainKernelFarConst (4 * X) (2 * Real.pi * W) * volume.real E
          / cofLo X (Real.log X) v
        ≤ 4 * 60000 * 144 * 2 ^ 26 * Real.log X ^ 27
          * Real.exp (-(Real.log X / 50) + 2 * ladderTopHigh X) := by
      rw [div_le_iff₀ hlo0]
      have h1 : 4 * plainKernelFarConst (4 * X) (2 * Real.pi * W) * volume.real E
          ≤ 4 * (60000 * Real.log X * Real.exp (Real.log X / 2)) * ((2 * Real.log X) ^ 26
            * (144 * Real.exp (Real.log X * (2 * ladderAlpha)) * Real.exp (ladderTopHigh X))) := by
        have := mul_le_mul hK hvol hE0
          (mul_nonneg (mul_nonneg (by norm_num) hl0) (Real.exp_pos _).le)
        linarith
      have e : Real.exp (Real.log X / 2) * Real.exp (Real.log X * (2 * ladderAlpha))
            * Real.exp (ladderTopHigh X)
          = Real.exp (-(Real.log X / 50) + 2 * ladderTopHigh X)
            * Real.exp (Real.log X - ladderTopHigh X) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; congr 1; unfold ladderAlpha; ring
      have hid : 4 * (60000 * Real.log X * Real.exp (Real.log X / 2)) * ((2 * Real.log X) ^ 26
            * (144 * Real.exp (Real.log X * (2 * ladderAlpha)) * Real.exp (ladderTopHigh X)))
          = 4 * 60000 * 144 * 2 ^ 26 * Real.log X ^ 27
            * Real.exp (-(Real.log X / 50) + 2 * ladderTopHigh X)
            * Real.exp (Real.log X - ladderTopHigh X) := by
        calc _ = 4 * 60000 * 144 * 2 ^ 26 * Real.log X ^ 27
              * (Real.exp (Real.log X / 2) * Real.exp (Real.log X * (2 * ladderAlpha))
                * Real.exp (ladderTopHigh X)) := by ring
          _ = _ := by rw [e]; ring
      calc _ ≤ _ := h1
        _ = _ := hid
        _ ≤ _ := mul_le_mul_of_nonneg_left hlo hc0
    linarith
  have hcardV : ((C.topBlocks (Real.log X)).card : ℝ) ≤ Real.log X ^ 2 + 2 :=
    card_topBlocks_le hlogX
  have hB0 : 0 ≤ B := by
    have := mul_nonneg (by norm_num : (0 : ℝ) ≤ 384) (by linarith : 0 ≤ Real.log (X : ℝ) + 3)
    have hc0 : 0 ≤ 4 * 60000 * 144 * 2 ^ 26 * Real.log X ^ 27
        * Real.exp (-(Real.log X / 50) + 2 * ladderTopHigh X) :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hl0 27)) (Real.exp_pos _).le
    linarith
  have hsum : ∑ v ∈ C.topBlocks (Real.log X),
        (∫ w in E, ‖blockR f C.top C.restTop X (Real.log X) v w‖ ^ 2)
      ≤ (C.topBlocks (Real.log X)).card * B := by
    calc _ ≤ ∑ _v ∈ C.topBlocks (Real.log X), B := sum_le_sum hv
      _ = _ := by rw [sum_const, nsmul_eq_mul]
  have hcard0 : (0 : ℝ) ≤ (C.topBlocks (Real.log X)).card := Nat.cast_nonneg _
  calc ((C.topBlocks (Real.log X)).card : ℝ) * ρ ^ 2
        * ∑ v ∈ C.topBlocks (Real.log X),
          (∫ w in E, ‖blockR f C.top C.restTop X (Real.log X) v w‖ ^ 2)
      ≤ ((C.topBlocks (Real.log X)).card : ℝ) * ρ ^ 2 * ((C.topBlocks (Real.log X)).card * B) :=
        mul_le_mul_of_nonneg_left hsum (mul_nonneg hcard0 (sq_nonneg ρ))
    _ = ((C.topBlocks (Real.log X)).card : ℝ) ^ 2 * ρ ^ 2 * B := by ring
    _ ≤ (Real.log X ^ 2 + 2) ^ 2 * ρ ^ 2 * B :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hcard0 hcardV 2) (sq_nonneg ρ)) hB0

/-- **The Ramaré error of the top scale.** -/
theorem top_ramErr_le {X : ℕ} (hX : Real.exp 1 ≤ (X : ℝ)) {W : ℝ} (hW0 : 0 ≤ W) (hWX : W ≤ X) :
    ramErr W X (Real.log X) (⌊Real.exp (ladderTopLow X)⌋₊ + 1)
      ≤ 256 * (10 / Real.log X + 16 * Real.exp (-ladderTopLow X)) := by
  have hX1 : (1 : ℝ) ≤ X := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hX
  have hX1' : 1 ≤ X := by exact_mod_cast hX1
  have hlogX := one_le_log_of_exp_le hX
  refine le_trans (ramErr_le hX1' hW0 hWX (by linarith) (Nat.succ_pos _)) ?_
  have hP : Real.exp (ladderTopLow X) ≤ ((⌊Real.exp (ladderTopLow X)⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast; exact (Nat.lt_floor_add_one _).le
  have h16 : 16 / ((⌊Real.exp (ladderTopLow X)⌋₊ + 1 : ℕ) : ℝ)
      ≤ 16 * Real.exp (-ladderTopLow X) := by
    rw [Real.exp_neg, div_le_iff₀ (lt_of_lt_of_le (Real.exp_pos _) hP)]
    have e : 16 * (Real.exp (ladderTopLow X))⁻¹ * Real.exp (ladderTopLow X) = 16 := by
      field_simp
    calc (16 : ℝ) = 16 * (Real.exp (ladderTopLow X))⁻¹ * Real.exp (ladderTopLow X) := e.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hP (by positivity)
  linarith

/-- **The harmonic mass of the top scale.** -/
theorem top_density_ge {X : ℝ} (hlog : 0 < Real.log X) (h1 : 1 ≤ ladderTopLow X)
    (h2 : ladderTopLow X + 1 ≤ ladderTopHigh X) :
    3 / 100 * Real.log (Real.log X) - mertensScaleConst
      ≤ ∑ p ∈ topScale X, (1 : ℝ) / (p : ℝ) := by
  have h := sum_primesIoc_exp_ge h1 h2
  have e : Real.log (ladderTopHigh X / ladderTopLow X) = 3 / 100 * Real.log (Real.log X) := by
    unfold ladderTopHigh ladderTopLow
    rw [← Real.rpow_sub hlog, Real.log_rpow hlog]; norm_num
  rw [e] at h
  exact h

/-- A prime interval up to `e^b` has at most `e^b` elements. -/
theorem card_primesIoc_exp_le (a b : ℝ) :
    ((primesIoc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).card : ℝ) ≤ Real.exp b := by
  have h1 : (primesIoc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).card ≤ ⌊Real.exp b⌋₊ := by
    calc _ ≤ (Finset.Ioc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).card := card_filter_le _ _
      _ = ⌊Real.exp b⌋₊ - ⌊Real.exp a⌋₊ := Nat.card_Ioc _ _
      _ ≤ ⌊Real.exp b⌋₊ := Nat.sub_le _ _
  calc ((primesIoc ⌊Real.exp a⌋₊ ⌊Real.exp b⌋₊).card : ℝ) ≤ (⌊Real.exp b⌋₊ : ℝ) := by
        exact_mod_cast h1
    _ ≤ Real.exp b := Nat.floor_le (Real.exp_pos b).le

theorem card_ladderScale_le {L : ℝ} (hL : 2 ^ 20 ≤ L) {X : ℝ} (hX : Real.exp 1 ≤ X) (j : ℕ) :
    ((ladderScale hL X j).card : ℝ) ≤ X := by
  unfold ladderScale
  split_ifs with hj
  · exact le_trans (card_primesIoc_exp_le _ _) (exp_seqB_le_X hL hX hj)
  · simp only [card_empty, Nat.cast_zero]; linarith [Real.exp_pos 1]

theorem card_topScale_le {X : ℝ} (hX : Real.exp 1 ≤ X) : ((topScale X).card : ℝ) ≤ X := by
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  obtain ⟨-, hhX⟩ := ladderTop_le (one_le_log_of_exp_le hX)
  calc ((topScale X).card : ℝ) ≤ Real.exp (ladderTopHigh X) := card_primesIoc_exp_le _ _
    _ ≤ Real.exp (Real.log X) := Real.exp_le_exp.mpr hhX
    _ = X := Real.exp_log hX0

/-- **The integers outside the rough set**, with lower bounds `A` for the harmonic masses. -/
theorem LadderScales.nonrough_le (L : LadderScales) {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1) {X : ℕ}
    (hX : 1 ≤ X) {W : ℝ} (hW : 1 ≤ W) (hWX : W ≤ X)
    (hcard : ∀ j ∈ range L.J, ((L.scale j).card : ℝ) ≤ X) (hcardtop : (L.top.card : ℝ) ≤ X)
    {A : ℕ → ℝ} (hApos : ∀ j ∈ range L.J, 0 < A j)
    (hA : ∀ j ∈ range L.J, A j ≤ ∑ p ∈ L.scale j, (1 : ℝ) / (p : ℝ))
    {Atop : ℝ} (hAtop : 0 < Atop) (hAtop' : Atop ≤ ∑ p ∈ L.top, (1 : ℝ) / (p : ℝ)) :
    (∫ w in Set.Icc (-W) W, ‖fullPoly f X w - logPoly (coefA f) (L.ladderS X) w‖ ^ 2)
      ≤ 216 * (∑ j ∈ range L.J, 1 / A j + 1 / Atop) := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hbase := L.integral_normSq_full_sub_rough_le hf hX hW
    (fun j hj => lt_of_lt_of_le (hApos j hj) (hA j hj)) (lt_of_lt_of_le hAtop hAtop')
  refine le_trans hbase ?_
  have hpi : Real.pi ≤ 16 / 5 := by linarith [Real.pi_lt_d2]
  have he : Real.exp 1 ≤ 14 / 5 := by linarith [Real.exp_one_lt_d9]
  have hfac : (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * ((4 * X : ℕ) : ℝ)) / (X : ℝ) ^ 2
      ≤ 36 / X := by
    rw [div_le_div_iff₀ (by positivity) hX0]
    push_cast
    have h1 : 5 * Real.pi / 2 * W ≤ 8 * X := by nlinarith
    have h2 : 5 * Real.exp 1 / 2 * (4 * (X : ℝ)) ≤ 28 * X := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_right (add_le_add h1 h2) hX0.le]
  have hterm : ∀ (Pr : Finset ℕ) (a : ℝ), 0 < a → a ≤ ∑ p ∈ Pr, (1 : ℝ) / (p : ℝ) →
      (Pr.card : ℝ) ≤ X →
      (((4 * X : ℕ) : ℝ) + 2 * Pr.card) / (∑ p ∈ Pr, (1 : ℝ) / (p : ℝ)) ≤ 6 * X * (1 / a) := by
    intro Pr a ha haS hcPr
    have hS : 0 < ∑ p ∈ Pr, (1 : ℝ) / (p : ℝ) := lt_of_lt_of_le ha haS
    rw [div_le_iff₀ hS]
    push_cast
    have h2 : 6 * (X : ℝ) * (1 / a) * a = 6 * X := by field_simp
    have h3 : 6 * (X : ℝ) * (1 / a) * a ≤ 6 * X * (1 / a) * ∑ p ∈ Pr, (1 : ℝ) / (p : ℝ) :=
      mul_le_mul_of_nonneg_left haS (by positivity)
    linarith
  have hsum : ∑ j ∈ range L.J, (((4 * X : ℕ) : ℝ) + 2 * (L.scale j).card)
        / (∑ p ∈ L.scale j, (1 : ℝ) / (p : ℝ))
      ≤ ∑ j ∈ range L.J, 6 * X * (1 / A j) :=
    sum_le_sum fun j hj => hterm _ _ (hApos j hj) (hA j hj) (hcard j hj)
  have htop := hterm L.top Atop hAtop hAtop' hcardtop
  rw [← mul_sum] at hsum
  have hS0 : 0 ≤ ∑ j ∈ range L.J, (((4 * X : ℕ) : ℝ) + 2 * (L.scale j).card)
        / (∑ p ∈ L.scale j, (1 : ℝ) / (p : ℝ))
      + (((4 * X : ℕ) : ℝ) + 2 * L.top.card) / (∑ p ∈ L.top, (1 : ℝ) / (p : ℝ)) := by
    positivity
  have hAsum : 0 ≤ ∑ j ∈ range L.J, 1 / A j :=
    sum_nonneg fun j hj => (one_div_pos.mpr (hApos j hj)).le
  calc _ ≤ 36 / (X : ℝ) * (∑ j ∈ range L.J, (((4 * X : ℕ) : ℝ) + 2 * (L.scale j).card)
          / (∑ p ∈ L.scale j, (1 : ℝ) / (p : ℝ))
        + (((4 * X : ℕ) : ℝ) + 2 * L.top.card) / (∑ p ∈ L.top, (1 : ℝ) / (p : ℝ))) :=
        mul_le_mul_of_nonneg_right hfac hS0
    _ ≤ 36 / (X : ℝ) * (6 * X * ∑ j ∈ range L.J, 1 / A j + 6 * X * (1 / Atop)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = 216 * (∑ j ∈ range L.J, 1 / A j + 1 / Atop) := by field_simp; ring

end

end GaloisForLFunctions.MatomakiRadziwill
