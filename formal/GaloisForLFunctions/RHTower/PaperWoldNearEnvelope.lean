import GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalNearIncrementBudget

/-! # Power envelopes for the literal Wold near-window interactions

The compact-operator budget is `2*t+eta<2`. No sign or cancellation hypothesis
is imposed on the actual prime increments.
-/

namespace RHTower
noncomputable section
open Filter Topology

structure PaperWoldNearParameters where
  t : ℝ
  eta : ℝ
  t_nonneg : 0 ≤ t
  eta_nonneg : 0 ≤ eta
  budget : 2 * t + eta < 2

def paperWoldSlack (p : PaperWoldNearParameters) : ℝ := (2 - 2 * p.t - p.eta) / 4
def paperWoldEnvelopeConstant (p : PaperWoldNearParameters) : ℝ := 1 / paperWoldSlack p + 2
def paperWoldDecay (p : PaperWoldNearParameters) : ℝ := 2 - 2 * p.t - 2 * paperWoldSlack p
def paperWoldLagWidth (p : PaperWoldNearParameters) : ℝ := (p.eta + paperWoldDecay p) / 2
def paperWoldLagExponent (p : PaperWoldNearParameters) : ℝ := paperWoldDecay p / paperWoldLagWidth p

theorem paperWoldSlack_bounds (p : PaperWoldNearParameters) :
    0 < paperWoldSlack p ∧ paperWoldSlack p ≤ 1 / 2 := by
  dsimp [paperWoldSlack]
  constructor <;> linarith [p.budget, p.t_nonneg, p.eta_nonneg]

theorem paperWoldEnvelopeConstant_pos (p : PaperWoldNearParameters) :
    0 < paperWoldEnvelopeConstant p := by
  have h := (paperWoldSlack_bounds p).1
  unfold paperWoldEnvelopeConstant
  positivity

theorem paperWoldDecay_gt (p : PaperWoldNearParameters) : p.eta < paperWoldDecay p := by
  dsimp [paperWoldDecay, paperWoldSlack]
  linarith [p.budget]

theorem paperWoldDecay_pos (p : PaperWoldNearParameters) : 0 < paperWoldDecay p :=
  p.eta_nonneg.trans_lt (paperWoldDecay_gt p)

theorem paperWoldLagWidth_bounds (p : PaperWoldNearParameters) :
    p.eta < paperWoldLagWidth p ∧ paperWoldLagWidth p < paperWoldDecay p := by
  dsimp [paperWoldLagWidth]
  constructor <;> linarith [paperWoldDecay_gt p]

theorem paperWoldLagWidth_pos (p : PaperWoldNearParameters) : 0 < paperWoldLagWidth p :=
  p.eta_nonneg.trans_lt (paperWoldLagWidth_bounds p).1

theorem paperWoldLagExponent_gt_one (p : PaperWoldNearParameters) :
    1 < paperWoldLagExponent p :=
  (one_lt_div (paperWoldLagWidth_pos p)).mpr (paperWoldLagWidth_bounds p).2

theorem paperWold_increment_power_bound (p : PaperWoldNearParameters) (n : ℕ) :
    |xiHeatCassiniWoldNatIncrement n| ≤
      paperWoldEnvelopeConstant p * ((n : ℝ) + 1) ^ (paperWoldSlack p - 1) := by
  have hx : 0 < (n : ℝ) + 1 := by positivity
  have hx1 : 1 ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have he := (paperWoldSlack_bounds p).1
  have hlog := Real.log_le_rpow_div hx.le he
  have hpow := Real.one_le_rpow hx1 he.le
  have hbound : Real.log ((n : ℝ) + 1) + 2 ≤
      paperWoldEnvelopeConstant p * ((n : ℝ) + 1) ^ paperWoldSlack p := by
    dsimp [paperWoldEnvelopeConstant]
    simp only [one_div]
    rw [div_eq_mul_inv] at hlog
    nlinarith
  calc
    _ ≤ (Real.log ((n : ℝ) + 1) + 2) / ((n : ℝ) + 1) :=
      xiHeatCassiniWoldNatIncrement_abs_le n
    _ ≤ (paperWoldEnvelopeConstant p * ((n : ℝ) + 1) ^ paperWoldSlack p) /
        ((n : ℝ) + 1) := div_le_div_of_nonneg_right hbound hx.le
    _ = _ := by rw [Real.rpow_sub hx, Real.rpow_one]; ring

def paperWoldInteraction (p : PaperWoldNearParameters) (n j : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ (2 * p.t) * xiHeatCassiniWoldNatIncrement n * xiHeatCassiniWoldNatIncrement j

theorem paperWoldInteraction_bound (p : PaperWoldNearParameters) {n j : ℕ} (hnj : n ≤ j) :
    |paperWoldInteraction p n j| ≤
      paperWoldEnvelopeConstant p ^ 2 * ((n : ℝ) + 1) ^ (-paperWoldDecay p) := by
  have hx : 0 < (n : ℝ) + 1 := by positivity
  have hmono : ((j : ℝ) + 1) ^ (paperWoldSlack p - 1) ≤
      ((n : ℝ) + 1) ^ (paperWoldSlack p - 1) :=
    Real.rpow_le_rpow_of_nonpos hx (by exact_mod_cast Nat.add_le_add_right hnj 1)
      (by linarith [(paperWoldSlack_bounds p).2])
  have hj := (paperWold_increment_power_bound p j).trans
    (mul_le_mul_of_nonneg_left hmono (paperWoldEnvelopeConstant_pos p).le)
  have hbase := mul_le_mul (paperWold_increment_power_bound p n) hj
    (abs_nonneg _) (by positivity [paperWoldEnvelopeConstant_pos p])
  have h := mul_le_mul_of_nonneg_left hbase (Real.rpow_nonneg hx.le (2 * p.t))
  calc
    |paperWoldInteraction p n j| =
        ((n : ℝ) + 1) ^ (2 * p.t) *
          (|xiHeatCassiniWoldNatIncrement n| * |xiHeatCassiniWoldNatIncrement j|) := by
      simp only [paperWoldInteraction, abs_mul, abs_of_nonneg (Real.rpow_nonneg hx.le _)]
      ring
    _ ≤ _ := h
    _ = _ := by
      rw [show ((n : ℝ) + 1) ^ (2 * p.t) *
          (paperWoldEnvelopeConstant p * ((n : ℝ) + 1) ^ (paperWoldSlack p - 1) *
            (paperWoldEnvelopeConstant p * ((n : ℝ) + 1) ^ (paperWoldSlack p - 1))) =
          paperWoldEnvelopeConstant p ^ 2 *
            (((n : ℝ) + 1) ^ (2 * p.t) * ((n : ℝ) + 1) ^ (paperWoldSlack p - 1) *
              ((n : ℝ) + 1) ^ (paperWoldSlack p - 1)) by ring,
        ← Real.rpow_add hx, ← Real.rpow_add hx]
      congr 2
      dsimp [paperWoldDecay]
      ring

def paperWoldLagCoeff (p : PaperWoldNearParameters) (k n : ℕ) : ℂ :=
  if k + 1 ≤ ⌊((n : ℝ) + 1) ^ p.eta⌋₊ then (paperWoldInteraction p n (n + k + 1) : ℂ) else 0

theorem paperWoldLagCoeff_row_bound (p : PaperWoldNearParameters) (k n : ℕ) :
    ‖paperWoldLagCoeff p k n‖ ≤
      paperWoldEnvelopeConstant p ^ 2 * ((n : ℝ) + 1) ^ (-paperWoldDecay p) := by
  unfold paperWoldLagCoeff
  split_ifs
  · simpa only [Complex.norm_real, Real.norm_eq_abs] using paperWoldInteraction_bound p (by omega : n ≤ n+k+1)
  · simp only [norm_zero]
    positivity

def paperWoldLagMajorant (p : PaperWoldNearParameters) (k : ℕ) : ℝ :=
  paperWoldEnvelopeConstant p ^ 2 * ((k : ℝ) + 1) ^ (-paperWoldLagExponent p)

theorem paperWoldLagMajorant_nonneg (p : PaperWoldNearParameters) (k : ℕ) :
    0 ≤ paperWoldLagMajorant p k := by unfold paperWoldLagMajorant; positivity

theorem paperWoldLagCoeff_bound (p : PaperWoldNearParameters) (k n : ℕ) :
    ‖paperWoldLagCoeff p k n‖ ≤ paperWoldLagMajorant p k := by
  by_cases hk : k + 1 ≤ ⌊((n : ℝ) + 1) ^ p.eta⌋₊
  · have hx : 0 < (n : ℝ) + 1 := by positivity
    have hkx : (k : ℝ) + 1 ≤ ((n : ℝ) + 1) ^ paperWoldLagWidth p := by
      calc
        _ ≤ ((n : ℝ) + 1) ^ p.eta := by
          have hnat : (k : ℝ) + 1 ≤ (⌊((n : ℝ) + 1) ^ p.eta⌋₊ : ℝ) := by exact_mod_cast hk
          exact hnat.trans (Nat.floor_le (Real.rpow_nonneg hx.le _))
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le
          (by linarith [Nat.cast_nonneg (α := ℝ) n]) (paperWoldLagWidth_bounds p).1.le
    have hq := (paperWoldLagExponent_gt_one p).le
    have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (k : ℝ) + 1) hkx (by linarith : 0 ≤ paperWoldLagExponent p)
    rw [← Real.rpow_mul hx.le, show paperWoldLagWidth p * paperWoldLagExponent p =
      paperWoldDecay p by
        unfold paperWoldLagExponent
        field_simp [(paperWoldLagWidth_pos p).ne']] at hpow
    have hinv := one_div_le_one_div_of_le (Real.rpow_pos_of_pos (by positivity : 0 < (k : ℝ) + 1) _) hpow
    have hdecay : ((n : ℝ) + 1) ^ (-paperWoldDecay p) ≤
        ((k : ℝ) + 1) ^ (-paperWoldLagExponent p) := by
      simpa only [Real.rpow_neg hx.le, Real.rpow_neg (by positivity : 0 ≤ (k : ℝ) + 1), one_div] using hinv
    exact (paperWoldLagCoeff_row_bound p k n).trans (mul_le_mul_of_nonneg_left hdecay (sq_nonneg _))
  · simpa only [paperWoldLagCoeff, if_neg hk, norm_zero] using paperWoldLagMajorant_nonneg p k

theorem paperWoldLagCoeff_tendsto (p : PaperWoldNearParameters) (k : ℕ) :
    Tendsto (fun n => ‖paperWoldLagCoeff p k n‖) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) (tendsto_natCast_atTop_atTop (R := ℝ))
  have h := ((tendsto_rpow_neg_atTop (paperWoldDecay_pos p)).comp hn).const_mul
    (paperWoldEnvelopeConstant p ^ 2)
  simp only [mul_zero, Function.comp_def] at h
  exact squeeze_zero (fun n => norm_nonneg _) (paperWoldLagCoeff_row_bound p k) h

theorem paperWoldLagMajorant_summable (p : PaperWoldNearParameters) : Summable (paperWoldLagMajorant p) := by
  unfold paperWoldLagMajorant
  have hs := ((Real.summable_nat_rpow).mpr (by linarith [paperWoldLagExponent_gt_one p] :
    -paperWoldLagExponent p < -1)).comp_injective Nat.succ_injective
  simpa only [Function.comp_def, Nat.cast_succ] using
    hs.mul_left (paperWoldEnvelopeConstant p ^ 2)

end
end RHTower
