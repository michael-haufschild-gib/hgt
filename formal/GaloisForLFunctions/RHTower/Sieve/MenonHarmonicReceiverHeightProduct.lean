import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFinalProductSchedule

/-!
# Harmonic product cost at the actual receiver height

The dyadic-window receiver only integrates to a height `W ≤ x`.  Retaining that height in the
reciprocal kernel replaces the coarse `sqrt x` far-kernel factor by `sqrt W`, while preserving the
literal final-range cofactor geometry and every endpoint rounding.
-/

namespace RHTower.Sieve

open Filter Finset MeasureTheory

noncomputable section

/-- Uniform reciprocal-kernel bound at an arbitrary receiver height between `1` and the final
shell scale. -/
theorem plainKernelFarConst_finalRange_receiver_le
    {x W : ℝ} (hx : Real.exp 1 ≤ x) (hW : 1 ≤ W) (hWx : W ≤ x)
    {N : ℕ} (hN : 1 ≤ N) (hNx : (N : ℝ) ≤ 3 * x) :
    plainKernelFarConst N (2 * Real.pi * W) ≤
      80000 * Real.sqrt W * Real.log x := by
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hlogx : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hx
    rwa [Real.log_exp] at h
  have hT : 1 ≤ 2 * Real.pi * W := by
    nlinarith [Real.pi_gt_three]
  have hsqrtW : 1 ≤ Real.sqrt W := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hW
  have hsqrt : Real.sqrt (2 * (2 * Real.pi * W)) ≤ 4 * Real.sqrt W := by
    calc
      Real.sqrt (2 * (2 * Real.pi * W)) ≤ Real.sqrt (16 * W) := by
        apply Real.sqrt_le_sqrt
        nlinarith [Real.pi_lt_four]
      _ = 4 * Real.sqrt W := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16)]
        norm_num
  have harg : 2 * (2 * Real.pi * W) + 1 ≤ 17 * x := by
    nlinarith [Real.pi_lt_four]
  have harg0 : 0 < 2 * (2 * Real.pi * W) + 1 := by positivity
  have hlogArgRaw : Real.log (2 * (2 * Real.pi * W) + 1) ≤ Real.log (17 * x) :=
    Real.log_le_log harg0 harg
  have hlog17 : Real.log (17 : ℝ) ≤ 16 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 17)
    norm_num at h ⊢
    exact h
  have hlogArg : Real.log (2 * (2 * Real.pi * W) + 1) ≤ 17 * Real.log x := by
    rw [Real.log_mul (by norm_num : (17 : ℝ) ≠ 0) (ne_of_gt hx0)] at hlogArgRaw
    linarith
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hlogNRaw : Real.log (N : ℝ) ≤ Real.log (3 * x) :=
    Real.log_le_log hNpos hNx
  have hlog3 : Real.log (3 : ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h ⊢
    exact h
  have hlogN : Real.log (N : ℝ) ≤ 3 * Real.log x := by
    rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (ne_of_gt hx0)] at hlogNRaw
    linarith
  have hlogArg0 : 0 ≤ Real.log (2 * (2 * Real.pi * W) + 1) :=
    Real.log_nonneg (by nlinarith [hW, Real.pi_gt_three])
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  calc
    plainKernelFarConst N (2 * Real.pi * W) ≤
        (1 + 2 * Real.log (2 * (2 * Real.pi * W) + 1)) *
            (214 * Real.sqrt (2 * (2 * Real.pi * W))) +
          12288 * Real.sqrt (2 * (2 * Real.pi * W)) +
          (1 + 2 * Real.log (N : ℝ)) := plainKernelFarConst_le_log hN hT
    _ ≤ (35 * Real.log x) * (214 * (4 * Real.sqrt W)) +
          12288 * (4 * Real.sqrt W) + 7 * Real.log x := by
      gcongr <;> linarith
    _ ≤ 80000 * Real.sqrt W * Real.log x := by
      nlinarith

/-- Final-range reciprocal HM mass with the actual receiver height retained. -/
theorem hmMassRecip_finalRange_receiver_mul_stepRatio_le_explicit
    {x q W volE : ℝ} (hx : Real.exp 1 ≤ x) (hW : 1 ≤ W) (hWx : W ≤ x)
    (hq : 1 ≤ q) (hvolE : 0 ≤ volE)
    (hN : 1 ≤ ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊) :
    hmMassRecip ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊
        (2 * Real.pi * W) (2 * Real.pi * volE) * q / x ≤
      6 + 80000 * Real.sqrt W * Real.log x * (2 * Real.pi * volE) * q / x +
        144 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W)) := by
  have hx1 : 1 ≤ x :=
    (by have := Real.exp_one_gt_d9; linarith : (1 : ℝ) ≤ Real.exp 1).trans hx
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  let N : ℕ := ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊
  have htop : ((menonFinalRangeTopNat x : ℕ) : ℝ) ≤ 3 * x := by
    rw [menonFinalRangeTopNat]
    exact Nat.floor_le (by positivity)
  have hfloor : (N : ℝ) ≤ (menonFinalRangeTopNat x : ℝ) / q := by
    dsimp only [N]
    exact Nat.floor_le (by positivity)
  have hdiv : (menonFinalRangeTopNat x : ℝ) / q ≤ 3 * x := by
    calc
      (menonFinalRangeTopNat x : ℝ) / q ≤ 3 * x / q :=
        div_le_div_of_nonneg_right htop hq0.le
      _ ≤ 3 * x := by
        rw [div_le_iff₀ hq0]
        nlinarith
  have hNreal : (N : ℝ) ≤ 3 * x := hfloor.trans hdiv
  have hfar := plainKernelFarConst_finalRange_receiver_le hx hW hWx
    (N := N) (by simpa only [N] using hN) hNreal
  have hbase := hmMassRecip_finalRange_mul_stepRatio_le
    hx1 hq0 (by nlinarith [Real.pi_gt_three] : 1 ≤ 2 * Real.pi * W)
    (volE := 2 * Real.pi * volE)
  calc
    hmMassRecip ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊
        (2 * Real.pi * W) (2 * Real.pi * volE) * q / x ≤
      6 + plainKernelFarConst ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊
          (2 * Real.pi * W) * (2 * Real.pi * volE) * q / x +
        144 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W)) := hbase
    _ ≤ 6 + 80000 * Real.sqrt W * Real.log x * (2 * Real.pi * volE) * q / x +
        144 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W)) := by
      have hfac : 0 ≤ (2 * Real.pi * volE) * q / x := by positivity
      gcongr

/-- Complete one-product bound at the actual receiver height. -/
theorem menonFinalReceiverProductCostVolume_le_explicit
    {P : Finset ℕ} {x Q eta W V volE : ℝ} (hx : Real.exp 1 ≤ x)
    (hW : 1 ≤ W) (hWx : W ≤ x) (hQ : 0 < Q) (heta : 0 ≤ eta)
    (heta1 : eta ≤ 1) (hvolE : 0 ≤ volE)
    (j : ℕ) (hQjOne : 1 ≤ Q * (1 + eta) ^ j)
    (hQjTop : Q * (1 + eta) ^ j ≤ 3 * x)
    (hN : 1 ≤ ⌊(menonFinalRangeTopNat x : ℝ) / (Q * (1 + eta) ^ j)⌋₊) :
    menonHarmonicProductCostVolume P ⌈x⌉₊ (menonFinalRangeTopNat x)
        Q eta W V volE j ≤
      V ^ (2 : ℕ) * ((2 * Real.pi)⁻¹ *
        (24 * (6 +
          80000 * Real.sqrt W * Real.log x * (2 * Real.pi * volE) *
            (Q * (1 + eta) ^ j) / x +
          144 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W))))) := by
  have hx1 : 1 ≤ x :=
    (by have := Real.exp_one_gt_d9; linarith : (1 : ℝ) ≤ Real.exp 1).trans hx
  let q : ℝ := Q * (1 + eta) ^ j
  have hq0 : 0 < q := by dsimp only [q]; positivity
  have hbase := menonFinalRangeProductCostVolume_le
    (P := P) (V := V) (volE := volE) hx1 hQ heta heta1 hW hvolE j hQjTop
  have hmass := hmMassRecip_finalRange_receiver_mul_stepRatio_le_explicit
    hx hW hWx (q := q) (volE := volE) (by simpa only [q] using hQjOne) hvolE
      (by simpa only [q] using hN)
  calc
    menonHarmonicProductCostVolume P ⌈x⌉₊ (menonFinalRangeTopNat x)
        Q eta W V volE j ≤
      V ^ (2 : ℕ) * ((2 * Real.pi)⁻¹ *
        (hmMassRecip ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊
          (2 * Real.pi * W) (2 * Real.pi * volE) * (24 * q / x))) := by
            simpa only [q] using hbase
    _ = V ^ (2 : ℕ) * ((2 * Real.pi)⁻¹ *
        (24 * (hmMassRecip ⌊(menonFinalRangeTopNat x : ℝ) / q⌋₊
          (2 * Real.pi * W) (2 * Real.pi * volE) * q / x))) := by ring
    _ ≤ V ^ (2 : ℕ) * ((2 * Real.pi)⁻¹ *
        (24 * (6 +
          80000 * Real.sqrt W * Real.log x * (2 * Real.pi * volE) * q / x +
          144 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W))))) := by
      gcongr
    _ = V ^ (2 : ℕ) * ((2 * Real.pi)⁻¹ *
        (24 * (6 +
          80000 * Real.sqrt W * Real.log x * (2 * Real.pi * volE) *
            (Q * (1 + eta) ^ j) / x +
          144 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W))))) := by rfl

/-- Menon's literal final ladder satisfies the receiver-height product bound uniformly over every
receiver height in `[1,x]`. -/
theorem eventually_menonFinalReceiverProductCostVolume_le_explicit :
    ∀ᶠ x : ℝ in atTop, ∀ W : ℝ, 1 ≤ W → W ≤ x →
      ∀ (P : Finset ℕ) (V volE : ℝ) (j : ℕ),
      j ∈ Finset.range (menonFinalRangeLadderSteps x) → 0 ≤ volE →
      menonHarmonicProductCostVolume P ⌈x⌉₊ (menonFinalRangeTopNat x)
          (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x) W V volE j ≤
        V ^ (2 : ℕ) * ((2 * Real.pi)⁻¹ *
          (24 * (6 +
            80000 * Real.sqrt W * Real.log x * (2 * Real.pi * volE) *
              (menonFinalRangeLadderBase x *
                (1 + menonFinalRangeLadderEta x) ^ j) / x +
            144 * Real.pi * Real.log (2 + 2 * (2 * Real.pi * W))))) := by
  filter_upwards [eventually_menonFinalRangeProductCost_conditions] with x hx
  intro W hW hWx P V volE j hj hvolE
  rcases hx with ⟨hx, hQ, heta, heta1, hsteps⟩
  rcases hsteps j hj with ⟨hQjOne, hQjTop, hN⟩
  exact menonFinalReceiverProductCostVolume_le_explicit
    hx hW hWx hQ heta heta1 hvolE j hQjOne hQjTop hN

end

end RHTower.Sieve
