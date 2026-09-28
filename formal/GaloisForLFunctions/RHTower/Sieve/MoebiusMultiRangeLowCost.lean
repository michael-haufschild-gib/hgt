import GaloisForLFunctions.RHTower.Sieve.MoebiusMultiRangeCofactorBounds

/-!
# The Möbius window over prime ranges with power thresholds

Every block of range `j` is thresholded at a power of its own scale, `V_{j,v} = S_v^{1-α_j}`.  On
the first-small set of range `0` the cofactor is paid by the mean value theorem: when the whole
range lies below `M/W`,

`V_{0,v}²·∫_{T_0} ‖C_{0,v}‖² ≤ 15·M²·S_v^{-2α_0}`;

on the first-small set of range `j + 1` it is amplified by the previous range.  Substituting both
into the ladder decomposition gives the window bound with every cofactor term in closed form.
-/

namespace RHTower.Sieve

open Finset MeasureTheory
open scoped ArithmeticFunction.Moebius

noncomputable section

/-- **The cofactor of the first range, by the mean value theorem.** -/
theorem rangeZero_block_cost_le (P : ℕ → Finset ℕ) (R η : ℕ → ℝ) (L : ℕ → ℕ)
    (V : ℕ → ℕ → ℝ) (M : ℕ) {W α : ℝ} (hW : 1 ≤ W) (v : ℕ) (hR : 0 < R 0) (hη : 0 ≤ η 0)
    (hWS : W * (R 0 * (1 + η 0) ^ v) ≤ M)
    (hV : V 0 v = (R 0 * (1 + η 0) ^ v) ^ (1 - α)) :
    V 0 v ^ (2 : ℕ) * (∫ w in rangeFirstSmall P R η L V W 0,
        ‖logPoly (ramareCofactorCoeff (P 0)) (geomCofactorBlock M (R 0) (η 0) v) w‖ ^ (2 : ℕ))
      ≤ 15 * (M : ℝ) ^ 2 * (R 0 * (1 + η 0) ^ v) ^ (-2 * α) := by
  set S := R 0 * (1 + η 0) ^ v with hSdef
  have hS : 0 < S := by
    have : (0 : ℝ) < 1 + η 0 := by linarith
    positivity
  set N := ⌊(M : ℝ) / S⌋₊ with hNdef
  have hN : (N : ℝ) ≤ (M : ℝ) / S := Nat.floor_le (by positivity)
  have hsupp := geomCofactorBlock_subset_Icc M hR hη v
  have hs0 : (0 : ℕ) ∉ geomCofactorBlock M (R 0) (η 0) v := fun h => by
    have := Finset.mem_Icc.mp (hsupp h)
    omega
  have hcard : ((geomCofactorBlock M (R 0) (η 0) v).card : ℝ) ≤ N := by
    have := Finset.card_le_card hsupp
    rw [Nat.card_Icc, add_tsub_cancel_right] at this
    exact_mod_cast this
  have hpi : Real.pi < 3.15 := Real.pi_lt_d2
  have he : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hpi0 := Real.pi_pos
  have he0 := Real.exp_pos 1
  have hW0 : (0 : ℝ) < W := by linarith
  have hcoef0 : (0 : ℝ) ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ) := by positivity
  have hcont : Continuous fun w : ℝ =>
      ‖logPoly (ramareCofactorCoeff (P 0)) (geomCofactorBlock M (R 0) (η 0) v) w‖ ^ (2 : ℕ) :=
    ((continuous_logPoly _ _).norm).pow 2
  have hint : (∫ w in rangeFirstSmall P R η L V W 0,
        ‖logPoly (ramareCofactorCoeff (P 0)) (geomCofactorBlock M (R 0) (η 0) v) w‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (N : ℝ)) * N := by
    refine (setIntegral_mono_set hcont.integrableOn_Icc
      (Filter.Eventually.of_forall fun w => by positivity)
      (Filter.Eventually.of_forall ((rangeFirstSmall_subset P R η L V W 0).trans
        (rangeAllSmall_subset P R η L V W 0)))).trans ?_
    refine (integral_Icc_normSq_logPoly_le_support _ hs0 (M := N)
      (fun n hn => (Finset.mem_Icc.mp (hsupp hn)).2) (norm_ramareCofactorCoeff_le_one _) hW).trans ?_
    exact mul_le_mul_of_nonneg_left hcard hcoef0
  have hV2 : V 0 v ^ (2 : ℕ) = S ^ (-2 * α) * S ^ (2 : ℕ) := by
    rw [hV, ← Real.rpow_natCast, ← Real.rpow_mul hS.le, ← Real.rpow_natCast S 2,
      ← Real.rpow_add hS]
    congr 1; push_cast; ring
  have hSa : 0 < S ^ (-2 * α) := Real.rpow_pos_of_pos hS _
  have hMS : S * (M / S) = M := by field_simp
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hWSM : W * S * (M / S) ≤ (M : ℝ) * (M / S) := by
    have : (0 : ℝ) ≤ M / S := by positivity
    nlinarith
  calc V 0 v ^ (2 : ℕ) * (∫ w in rangeFirstSmall P R η L V W 0,
        ‖logPoly (ramareCofactorCoeff (P 0)) (geomCofactorBlock M (R 0) (η 0) v) w‖ ^ (2 : ℕ))
      ≤ S ^ (-2 * α) * S ^ (2 : ℕ)
          * ((5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M / S)) * (M / S)) := by
        rw [hV2]
        refine mul_le_mul_of_nonneg_left (hint.trans ?_) (by positivity)
        gcongr
    _ = S ^ (-2 * α) * (5 * Real.pi / 2 * (W * S * (S * (M / S)))
          + 5 * Real.exp 1 / 2 * ((S * (M / S)) * (S * (M / S)))) := by ring
    _ ≤ S ^ (-2 * α) * (5 * Real.pi / 2 * (M : ℝ) ^ 2 + 5 * Real.exp 1 / 2 * (M : ℝ) ^ 2) := by
        rw [hMS]
        refine mul_le_mul_of_nonneg_left ?_ hSa.le
        have : W * S * (M : ℝ) ≤ (M : ℝ) ^ 2 := by nlinarith
        nlinarith
    _ ≤ 15 * (M : ℝ) ^ 2 * S ^ (-2 * α) := by
        have hM2 : (0 : ℝ) ≤ (M : ℝ) ^ 2 := by positivity
        have hc : 5 * Real.pi / 2 * (M : ℝ) ^ 2 + 5 * Real.exp 1 / 2 * (M : ℝ) ^ 2
            ≤ 15 * (M : ℝ) ^ 2 := by nlinarith
        have := mul_le_mul_of_nonneg_left hc hSa.le
        linarith

/-- The closed-form cofactor cost of block `v` of range `j`. -/
def rangeCofactorCost (R η : ℕ → ℝ) (L : ℕ → ℕ) (α : ℕ → ℝ) (M : ℕ) : ℕ → ℕ → ℝ
  | 0, v => 15 * (M : ℝ) ^ 2 * (R 0 * (1 + η 0) ^ v) ^ (-2 * α 0)
  | j + 1, v => ∑ r ∈ Finset.range (L j),
      15 * (8 * ⌈Real.log (R (j + 1) * (1 + η (j + 1)) ^ v)
            / Real.log (R j * (1 + η j) ^ r)⌉₊ + 8 : ℝ)
          ^ ⌈Real.log (R (j + 1) * (1 + η (j + 1)) ^ v) / Real.log (R j * (1 + η j) ^ r)⌉₊
        * (R j * (1 + η j) ^ r) * (M : ℝ) ^ 2
        * (R (j + 1) * (1 + η (j + 1)) ^ v) ^ (2 * α j - 2 * α (j + 1))

/-- The power thresholds `V_{j,v} = (R_j(1+η_j)^v)^{1-α_j}`. -/
def powerThreshold (R η α : ℕ → ℝ) (j v : ℕ) : ℝ := (R j * (1 + η j) ^ v) ^ (1 - α j)

theorem powerThreshold_pos {R η α : ℕ → ℝ} {j : ℕ} (hR : 0 < R j) (hη : 0 ≤ η j) (v : ℕ) :
    0 < powerThreshold R η α j v := by
  rw [powerThreshold]
  have : (0 : ℝ) < 1 + η j := by linarith
  exact Real.rpow_pos_of_pos (by positivity) _

/-- **Every block's cofactor cost on its first-small set.** -/
theorem range_block_cost_le (P : ℕ → Finset ℕ) (R η α : ℕ → ℝ) (L : ℕ → ℕ) (M : ℕ)
    (hM : 0 < M) {W : ℝ} (hW : 1 ≤ W) (hWM : W ≤ M) (J : ℕ)
    (hR : ∀ j ∈ Finset.range J, 1 < R j) (hη : ∀ j ∈ Finset.range J, 0 ≤ η j ∧ η j ≤ 1)
    (hα : ∀ j ∈ Finset.range J, α j ≤ 1 / 2)
    (hPprime : ∀ j ∈ Finset.range J, ∀ q ∈ P j, q.Prime)
    (hW0 : ∀ v ∈ Finset.range (L 0), W * (R 0 * (1 + η 0) ^ v) ≤ M) :
    ∀ j ∈ Finset.range J, ∀ v ∈ Finset.range (L j),
      powerThreshold R η α j v ^ (2 : ℕ)
          * (∫ w in rangeFirstSmall P R η L (powerThreshold R η α) W j,
            ‖logPoly (ramareCofactorCoeff (P j)) (geomCofactorBlock M (R j) (η j) v) w‖ ^ (2 : ℕ))
        ≤ rangeCofactorCost R η L α M j v := by
  intro j hj v hv
  cases j with
  | zero =>
    exact rangeZero_block_cost_le P R η L (powerThreshold R η α) M hW v
      (by linarith [hR 0 hj]) (hη 0 hj).1 (hW0 v hv) rfl
  | succ j =>
    have hjJ : j ∈ Finset.range J :=
      Finset.mem_range.mpr (Nat.lt_of_succ_lt (Finset.mem_range.mp hj))
    exact rangeSucc_block_cost_le P R η L (powerThreshold R η α) M hM hW hWM (hα j hjJ) j v
      (hR j hjJ) (hη j hjJ).1 (hη j hjJ).2 (hR (j + 1) hj) (hη (j + 1) hj).1 (hPprime j hjJ)
      (fun r => rfl) rfl

/-- **The Möbius window over prime ranges with power thresholds.**  The cofactor terms of every
range are in closed form; the Cauchy–Schwarz weight is `δ = 1`. -/
theorem integral_Icc_normSq_logPoly_moebius_le_powerRanges (P : ℕ → Finset ℕ) (R η α : ℕ → ℝ)
    (L : ℕ → ℕ) (M J : ℕ) (hM : 0 < M) {P' : Finset ℕ} {R' η' W w₀ Bdisc : ℝ}
    (hW : 1 ≤ W) (hWM : W ≤ M)
    (hR : ∀ j ∈ Finset.range J, 1 < R j) (hη : ∀ j ∈ Finset.range J, 0 ≤ η j ∧ η j ≤ 1)
    (hL : ∀ j ∈ Finset.range J, 1 ≤ L j) (hα : ∀ j ∈ Finset.range J, α j ≤ 1 / 2)
    (hPprime : ∀ j ∈ Finset.range J, ∀ q ∈ P j, q.Prime)
    (hP : ∀ j ∈ Finset.range J, ∀ p ∈ P j, R j < (p : ℝ) ∧ (p : ℝ) ≤ R j * (1 + η j) ^ L j)
    (hW0 : ∀ v ∈ Finset.range (L 0), W * (R 0 * (1 + η 0) ^ v) ≤ M)
    (hR' : 0 < R') (hη' : 0 ≤ η') (hwW : w₀ ≤ W) {L' : ℕ} (hL' : 1 ≤ L')
    (hP'prime : ∀ q ∈ P', q.Prime)
    (hP' : ∀ p ∈ P', R' < (p : ℝ) ∧ (p : ℝ) ≤ R' * (1 + η') ^ L') (V' : ℕ → ℝ)
    (hNj : ∀ j ∈ Finset.range L', 1 ≤ ⌊(M : ℝ) / (R' * (1 + η') ^ j)⌋₊)
    (hbound' : ∀ j ∈ Finset.range L',
      ∀ w ∈ annulusLarge (rangeUnionSmall P R η L (powerThreshold R η α) W J) W w₀,
        ‖primeBlockPoly (geomBlock P' R' (1 + η') j) w‖ ≤ V' j)
    (hdisc : (∫ w in Set.Icc (-w₀) w₀,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2) ≤ Bdisc) :
    (∫ w in Set.Icc (-W) W,
        ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (Finset.Icc 1 M) w‖ ^ 2)
      ≤ Bdisc
        + ∑ j ∈ Finset.range J,
            (2 * (2 * (L j : ℝ) * ∑ v ∈ Finset.range (L j), rangeCofactorCost R η L α M j v
                + 2 * ∫ w in Set.Icc (-W) W, ‖ramareLadderError (P j) M (R j) (η j) (L j) w‖ ^ 2)
              + 2 * (∫ w in Set.Icc (-W) W,
                    ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet (P j) M) w‖ ^ 2))
        + (2 * (2 * (L' : ℝ) * ∑ j ∈ Finset.range L',
                V' j ^ 2 * ladderHMBoundRecip M R' η' W
                    (volume.real (annulusLarge
                      (rangeUnionSmall P R η L (powerThreshold R η α) W J) W w₀)) j
              + 2 * ∫ w in Set.Icc (-W) W, ‖ramareLadderError P' M R' η' L' w‖ ^ 2)
          + 2 * (∫ w in Set.Icc (-W) W,
                  ‖logPoly (fun n => ((μ n : ℤ) : ℂ)) (supportMeanSquareRoughSet P' M) w‖ ^ 2)) := by
  set V := powerThreshold R η α with hVdef
  have hVpos : ∀ j ∈ Finset.range J, ∀ v, 0 < V j v := fun j hj v =>
    powerThreshold_pos (by linarith [hR j hj]) (hη j hj).1 v
  have hcost := range_block_cost_le P R η α L M hM hW hWM J hR hη hα hPprime hW0
  set I : ℕ → ℕ → ℝ := fun j v => (V j v ^ (2 : ℕ))⁻¹ * rangeCofactorCost R η L α M j v with hIdef
  have hI : ∀ j ∈ Finset.range J, ∀ v ∈ Finset.range (L j),
      (∫ w in rangeFirstSmall P R η L V W j,
        ‖logPoly (ramareCofactorCoeff (P j)) (geomCofactorBlock M (R j) (η j) v) w‖ ^ (2 : ℕ))
        ≤ I j v := by
    intro j hj v hv
    have hV2 : 0 < V j v ^ (2 : ℕ) := pow_pos (hVpos j hj v) 2
    rw [hIdef, le_inv_mul_iff₀ hV2]
    exact hcost j hj v hv
  have hVI : ∀ j ∈ Finset.range J, ∀ v, V j v ^ (2 : ℕ) * I j v
      = rangeCofactorCost R η L α M j v := by
    intro j hj v
    have hV2 : V j v ^ (2 : ℕ) ≠ 0 := (pow_pos (hVpos j hj v) 2).ne'
    rw [hIdef, ← mul_assoc, mul_inv_cancel₀ hV2, one_mul]
  have hmain := integral_Icc_normSq_logPoly_moebius_le_multiRange P R η L V M J
    (fun j hj => by linarith [hR j hj]) (fun j hj => (hη j hj).1) hL hPprime hP I hI hR' hη' hW
    hwW hL' one_pos hP'prime hP' V' hNj hbound' hdisc
  refine hmain.trans (le_of_eq ?_)
  congr 1
  · congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.sum_congr rfl fun v _ => hVI j hj v]
    norm_num
  · norm_num

end

end RHTower.Sieve
