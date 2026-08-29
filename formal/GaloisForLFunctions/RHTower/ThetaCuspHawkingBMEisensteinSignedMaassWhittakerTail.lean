import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinMixedConstantWhittakerTail

/-!
# Full signed-frequency completed Eisenstein Maass tails

The preceding literal Whittaker word covered positive Fourier frequency.  This module restores
the full source-faithful Fourier carrier.  The canonical phases

`exp(+-2*pi*i*n*x)`

have norm one, so the actual divisor-coefficient Tannery majorant survives at every horocycle
coordinate `x`.  Lean proves signed polynomial, square-root-normalized, and arbitrary-complex-
power tails vanish at the cusp.

Fourier sign also swaps the radial Maass words exactly: negative-frequency raising at weight `k`
is positive-frequency lowering at weight `-k`, and conversely.  Thus the full signed weight `+4`
tail is positive-frequency `R_2 R_0` plus negative-frequency `L_(-2) L_0`; the weight `-4` tail
has the opposite pairing.  Both vanish after every complex constant-term power.

This closes full Fourier-sign cusp admission needed for exhaustive Stokes-sector decomposition.
It does not identify the regularized modular integral by definition.

`[BRIDGE] [PAPER-PROVED] [LEAN-PROVED] [HC94] [SIGNED MAASS WHITTAKER TAIL]`
-/

open Complex Real Finset Filter Topology
open scoped BigOperators NNReal

namespace RHTower
noncomputable section

def d4BMFourierSign (negative : Bool) : ℝ := if negative then -1 else 1

def d4BMCompletedEisensteinFourierPhase (negative : Bool) (N : ℕ) (x : ℝ) : ℂ :=
  Complex.exp
    (((d4BMFourierSign negative * (2 * Real.pi * ((N : ℝ) + 1) * x) : ℝ) : ℂ) * I)

theorem d4BM_norm_completedEisensteinFourierPhase (negative : Bool) (N : ℕ) (x : ℝ) :
    ‖d4BMCompletedEisensteinFourierPhase negative N x‖ = 1 := by
  rw [d4BMCompletedEisensteinFourierPhase, Complex.norm_exp]
  simp [mul_re]

def d4BMCompletedEisensteinSignedPolynomialBesselJetTail
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (indexDegree heightDegree : ℕ) (Y : ℝ) : ℂ :=
  ∑' N : ℕ,
    (d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
      ((N + 1 : ℕ) : ℂ) ^ indexDegree * d4BMCompletedEisensteinFourierPhase negative N x) *
      (Y : ℂ) ^ heightDegree *
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
        (2 * Real.pi * ((N : ℝ) + 1) * Y) nu

theorem tendsto_d4BMCompletedEisensteinSignedPolynomialBesselJetTail_atTop_zero
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (indexDegree heightDegree : ℕ) :
    Tendsto (d4BMCompletedEisensteinSignedPolynomialBesselJetTail u nu negative x indexDegree heightDegree)
      atTop (𝓝 0) := by
  let coefficient : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
      ((N + 1 : ℕ) : ℂ) ^ indexDegree * d4BMCompletedEisensteinFourierPhase negative N x
  let C : ℝ := Real.exp (‖nu‖ ^ 2 / 2)
  have hsum0 := d4BM_completedEisensteinPolynomialWhittakerCoefficient_weightedSummable
    u indexDegree heightDegree
  have hsum : Summable (fun N : ℕ =>
      ‖coefficient N‖ * (heightDegree.factorial : ℝ) *
        (2 / ((N : ℝ) + 1)) ^ heightDegree *
        Real.exp (-(((N : ℝ) + 1) / 2))) := by
    convert hsum0 using 1
    funext N
    dsimp [coefficient]
    rw [norm_mul, d4BM_norm_completedEisensteinFourierPhase, mul_one]
  apply GaloisForLFunctions.HTGeometry.tendsto_tsum_zero_of_pointwise_damping_of_summable_majorant
    (hsum.mul_left C)
  · intro N
    apply GaloisForLFunctions.HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp
      (C := C * ‖coefficient N‖) (δ := (N : ℝ) + 1)
      (N := heightDegree) (by positivity)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    let n : D4BMPositiveIndex := ⟨N + 1, by omega⟩
    let Yp : {y : ℝ // 1 ≤ y} := ⟨Y, hY⟩
    have hK := d4BM_norm_modifiedBesselKOrder_cusp_le n Yp nu
    have hK' :
        ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          (2 * Real.pi * ((N : ℝ) + 1) * Y) nu‖ ≤
            C * Real.exp (-(((N : ℝ) + 1) * Y)) := by
      simpa [n, Yp, d4BMCuspBesselArgument, C, Nat.cast_add, Nat.cast_one] using hK
    dsimp [d4BMCompletedEisensteinSignedPolynomialBesselJetTail, coefficient, n, Yp]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hY)]
    calc
      ‖(d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          (↑(N + 1) : ℂ) ^ indexDegree) * d4BMCompletedEisensteinFourierPhase negative N x‖ *
          Y ^ heightDegree *
          ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
            (2 * Real.pi * (↑N + 1) * Y) nu‖
        ≤ ‖(d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          (↑(N + 1) : ℂ) ^ indexDegree) * d4BMCompletedEisensteinFourierPhase negative N x‖ *
          Y ^ heightDegree * (C * Real.exp (-((↑N + 1) * Y))) := by gcongr
      _ = C * ‖(d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          (↑(N + 1) : ℂ) ^ indexDegree) * d4BMCompletedEisensteinFourierPhase negative N x‖ *
          Y ^ heightDegree * Real.exp (-((↑N + 1) * Y)) := by ring
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    intro N
    let n : D4BMPositiveIndex := ⟨N + 1, by omega⟩
    let Yp : {y : ℝ // 1 ≤ y} := ⟨Y, hY⟩
    have hK := d4BM_norm_modifiedBesselKOrder_cusp_le n Yp nu
    have hK' :
        ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          (2 * Real.pi * ((N : ℝ) + 1) * Y) nu‖ ≤
            Real.exp (‖nu‖ ^ 2 / 2) * Real.exp (-(((N : ℝ) + 1) * Y)) := by
      simpa [n, Yp, d4BMCuspBesselArgument, Nat.cast_add, Nat.cast_one] using hK
    have hY0 : 0 ≤ Y := zero_le_one.trans hY
    have ha : 0 < (N : ℝ) + 1 := by positivity
    have habsorb := pow_mul_exp_neg_le_absorb_half ha hY0 heightDegree
    dsimp [d4BMCompletedEisensteinSignedPolynomialBesselJetTail, coefficient, C, n, Yp]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hY0]
    calc
      ‖(d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          (↑(N + 1) : ℂ) ^ indexDegree) * d4BMCompletedEisensteinFourierPhase negative N x‖ *
          Y ^ heightDegree *
          ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
            (2 * Real.pi * (↑N + 1) * Y) nu‖
        ≤ ‖(d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          (↑(N + 1) : ℂ) ^ indexDegree) * d4BMCompletedEisensteinFourierPhase negative N x‖ *
          Y ^ heightDegree *
          (Real.exp (‖nu‖ ^ 2 / 2) * Real.exp (-((↑N + 1) * Y))) := by gcongr
      _ = Real.exp (‖nu‖ ^ 2 / 2) *
          (‖(d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
            (↑(N + 1) : ℂ) ^ indexDegree) * d4BMCompletedEisensteinFourierPhase negative N x‖ *
            (Y ^ heightDegree * Real.exp (-((↑N + 1) * Y)))) := by ring
      _ ≤ Real.exp (‖nu‖ ^ 2 / 2) *
          (‖(d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
            (↑(N + 1) : ℂ) ^ indexDegree) * d4BMCompletedEisensteinFourierPhase negative N x‖ *
            ((heightDegree.factorial : ℝ) *
              (2 / ((N : ℝ) + 1)) ^ heightDegree *
              Real.exp (-(((N : ℝ) + 1) * Y / 2)))) := by gcongr
      _ ≤ Real.exp (‖nu‖ ^ 2 / 2) *
          (‖(d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
            (↑(N + 1) : ℂ) ^ indexDegree) * d4BMCompletedEisensteinFourierPhase negative N x‖ *
            ((heightDegree.factorial : ℝ) *
              (2 / ((N : ℝ) + 1)) ^ heightDegree *
              Real.exp (-(((N : ℝ) + 1) / 2)))) := by
            gcongr
            nlinarith
      _ = Real.exp (‖nu‖ ^ 2 / 2) *
          (‖(d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
            (↑(N + 1) : ℂ) ^ indexDegree) * d4BMCompletedEisensteinFourierPhase negative N x‖ *
            (heightDegree.factorial : ℝ) *
            (2 / ((N : ℝ) + 1)) ^ heightDegree *
            Real.exp (-(((N : ℝ) + 1) / 2))) := by ring

def d4BMCompletedEisensteinSignedSqrtWhittakerTail
    (u nu : ℂ) (negative : Bool) (x : ℝ)
    (indexDegree heightDegree : ℕ) (Y : ℝ) : ℂ :=
  ∑' N : ℕ,
    (d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
      ((N + 1 : ℕ) : ℂ) ^ indexDegree * d4BMCompletedEisensteinFourierPhase negative N x) *
      (Real.sqrt Y : ℂ) * (Y : ℂ) ^ heightDegree *
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
        (2 * Real.pi * ((N : ℝ) + 1) * Y) nu

theorem d4BM_signedSqrtWhittakerTail_eq_ratio_mul
    (u nu : ℂ) (negative : Bool) (x : ℝ) (j m : ℕ)
    {Y : ℝ} (hY : 0 < Y) :
    d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu negative x j m Y =
      ((Real.sqrt Y / Y : ℝ) : ℂ) *
        d4BMCompletedEisensteinSignedPolynomialBesselJetTail u nu negative x j (m + 1) Y := by
  rw [d4BMCompletedEisensteinSignedSqrtWhittakerTail, d4BMCompletedEisensteinSignedPolynomialBesselJetTail, ← tsum_mul_left]
  apply tsum_congr
  intro N
  rw [pow_succ]
  push_cast
  field_simp [hY.ne']

theorem tendsto_d4BMCompletedEisensteinSignedSqrtWhittakerTail_atTop_zero
    (u nu : ℂ) (negative : Bool) (x : ℝ) (j m : ℕ) :
    Tendsto (d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu negative x j m) atTop (𝓝 0) := by
  have hratio : Tendsto (fun Y : ℝ => ((Real.sqrt Y / Y : ℝ) : ℂ)) atTop (𝓝 0) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp d4BM_tendsto_sqrt_div_self_atTop_zero
  have htail := tendsto_d4BMCompletedEisensteinSignedPolynomialBesselJetTail_atTop_zero u nu negative x j (m + 1)
  have hprod := hratio.mul htail
  simp only [mul_zero] at hprod
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  exact (d4BM_signedSqrtWhittakerTail_eq_ratio_mul u nu negative x j m hY).symm

def d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail
    (u nu w : ℂ) (negative : Bool) (x : ℝ) (j m : ℕ) (Y : ℝ) : ℂ :=
  (Y : ℂ) ^ w * d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu negative x j m Y

theorem d4BM_signedSqrtWhittakerTail_heightDegree_add
    (u nu : ℂ) (negative : Bool) (x : ℝ) (j m M : ℕ) (Y : ℝ) :
    d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu negative x j (m + M) Y =
      (Y : ℂ) ^ M * d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu negative x j m Y := by
  rw [d4BMCompletedEisensteinSignedSqrtWhittakerTail, d4BMCompletedEisensteinSignedSqrtWhittakerTail, ← tsum_mul_left]
  apply tsum_congr
  intro N
  rw [pow_add]
  ring

theorem d4BM_complexPowerSignedSqrtWhittakerTail_eq_boundedQuotient
    (u nu w : ℂ) (negative : Bool) (x : ℝ) (j m M : ℕ)
    {Y : ℝ} (hY : 0 < Y) :
    d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail u nu w negative x j m Y =
      (((Y : ℂ) ^ w) / ((Y : ℂ) ^ M)) *
        d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu negative x j (m + M) Y := by
  rw [d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail, d4BM_signedSqrtWhittakerTail_heightDegree_add]
  have hYC : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  field_simp

theorem tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero
    (u nu w : ℂ) (negative : Bool) (x : ℝ) (j m : ℕ) :
    Tendsto (d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail u nu w negative x j m) atTop (𝓝 0) := by
  let M : ℕ := Nat.ceil |w.re|
  have hbound : ∀ᶠ Y : ℝ in atTop,
      ‖((Y : ℂ) ^ w) / ((Y : ℂ) ^ M)‖ ≤ 1 := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    have hY0 : 0 < Y := zero_lt_one.trans_le hY
    have hw : w.re ≤ (M : ℝ) := by
      dsimp [M]
      exact le_trans (le_abs_self w.re) (Nat.le_ceil |w.re|)
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos hY0,
      norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hY0.le,
      ← Real.rpow_natCast]
    rw [div_le_one (Real.rpow_pos_of_pos hY0 _)]
    exact Real.rpow_le_rpow_of_exponent_le hY hw
  have htail := tendsto_d4BMCompletedEisensteinSignedSqrtWhittakerTail_atTop_zero u nu negative x j (m + M)
  have hprod := d4BM_tendsto_eventually_norm_le_one_mul_zero hbound htail
  apply hprod.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with Y hY
  exact (d4BM_complexPowerSignedSqrtWhittakerTail_eq_boundedQuotient u nu w negative x j m M hY).symm

def d4BMSignedFrequencyMaassRaiseAt
    (negative : Bool) (k : ℤ) (c : D4BMPositiveReal) (Y : D4BMPositiveReal)
    (value deriv : ℂ) : ℂ :=
  (Y : ℂ) * deriv -
    (d4BMFourierSign negative : ℂ) * (c : ℂ) * (Y : ℂ) * value +
    (k : ℂ) / 2 * value

def d4BMSignedFrequencyMaassLowerAt
    (negative : Bool) (k : ℤ) (c : D4BMPositiveReal) (Y : D4BMPositiveReal)
    (value deriv : ℂ) : ℂ :=
  (Y : ℂ) * deriv +
    (d4BMFourierSign negative : ℂ) * (c : ℂ) * (Y : ℂ) * value -
    (k : ℂ) / 2 * value

theorem d4BM_negativeFrequencyMaassRaiseAt_eq_positiveLower
    (k : ℤ) (c : D4BMPositiveReal) (Y : D4BMPositiveReal) (value deriv : ℂ) :
    d4BMSignedFrequencyMaassRaiseAt true k c Y value deriv =
      d4BMPositiveFrequencyMaassLowerAt (-k) c Y value deriv := by
  simp [d4BMSignedFrequencyMaassRaiseAt, d4BMPositiveFrequencyMaassLowerAt,
    d4BMFourierSign]
  ring

theorem d4BM_negativeFrequencyMaassLowerAt_eq_positiveRaise
    (k : ℤ) (c : D4BMPositiveReal) (Y : D4BMPositiveReal) (value deriv : ℂ) :
    d4BMSignedFrequencyMaassLowerAt true k c Y value deriv =
      d4BMPositiveFrequencyMaassRaiseAt (-k) c Y value deriv := by
  simp [d4BMSignedFrequencyMaassLowerAt, d4BMPositiveFrequencyMaassRaiseAt,
    d4BMFourierSign]
  ring

def d4BMCompletedEisensteinPhasedMaassWord
    (raise negative : Bool) (u nu : ℂ) (x Y : ℝ) : ℂ :=
  (3 / 4 : ℂ) * d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu negative x 0 0 Y +
    (if raise then -(3 * (2 * Real.pi : ℂ)) else 3 * (2 * Real.pi : ℂ)) *
      d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu negative x 1 1 Y -
    ((3 / 2 : ℂ) * (2 * Real.pi : ℂ)) *
      (d4BMCompletedEisensteinSignedSqrtWhittakerTail u (nu + 1) negative x 1 1 Y +
        d4BMCompletedEisensteinSignedSqrtWhittakerTail u (nu - 1) negative x 1 1 Y) +
    ((3 / 2 : ℂ) * (2 * Real.pi : ℂ) ^ 2) *
      d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu negative x 2 2 Y +
    (if raise then (2 * Real.pi : ℂ) ^ 2 else -(2 * Real.pi : ℂ) ^ 2) *
      (d4BMCompletedEisensteinSignedSqrtWhittakerTail u (nu + 1) negative x 2 2 Y +
        d4BMCompletedEisensteinSignedSqrtWhittakerTail u (nu - 1) negative x 2 2 Y) +
    ((1 / 4 : ℂ) * (2 * Real.pi : ℂ) ^ 2) *
      (d4BMCompletedEisensteinSignedSqrtWhittakerTail u (nu + 2) negative x 2 2 Y +
        d4BMCompletedEisensteinSignedSqrtWhittakerTail u (nu - 2) negative x 2 2 Y)

def d4BMCompletedEisensteinComplexPowerPhasedMaassWord
    (raise negative : Bool) (u nu w : ℂ) (x Y : ℝ) : ℂ :=
  (Y : ℂ) ^ w * d4BMCompletedEisensteinPhasedMaassWord raise negative u nu x Y

theorem tendsto_d4BMCompletedEisensteinComplexPowerPhasedMaassWord_atTop_zero
    (raise negative : Bool) (u nu w : ℂ) (x : ℝ) :
    Tendsto (d4BMCompletedEisensteinComplexPowerPhasedMaassWord raise negative u nu w x)
      atTop (𝓝 0) := by
  have h00 := tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero u nu w negative x 0 0
  have h10 := tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero u nu w negative x 1 1
  have h1p := tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero u (nu + 1) w negative x 1 1
  have h1m := tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero u (nu - 1) w negative x 1 1
  have h20 := tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero u nu w negative x 2 2
  have h2p := tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero u (nu + 1) w negative x 2 2
  have h2m := tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero u (nu - 1) w negative x 2 2
  have h2pp := tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero u (nu + 2) w negative x 2 2
  have h2mm := tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero u (nu - 2) w negative x 2 2
  have hword := (((((h00.const_mul (3 / 4 : ℂ)).add
      (h10.const_mul
        (if raise then -(3 * (2 * Real.pi : ℂ)) else 3 * (2 * Real.pi : ℂ)))).sub
      ((h1p.add h1m).const_mul ((3 / 2 : ℂ) * (2 * Real.pi : ℂ)))).add
      (h20.const_mul ((3 / 2 : ℂ) * (2 * Real.pi : ℂ) ^ 2))).add
      ((h2p.add h2m).const_mul
        (if raise then (2 * Real.pi : ℂ) ^ 2 else -(2 * Real.pi : ℂ) ^ 2))).add
      ((h2pp.add h2mm).const_mul ((1 / 4 : ℂ) * (2 * Real.pi : ℂ) ^ 2))
  simp only [mul_zero, add_zero, sub_zero] at hword
  convert hword using 1
  funext Y
  simp only [d4BMCompletedEisensteinComplexPowerPhasedMaassWord, d4BMCompletedEisensteinPhasedMaassWord,
    d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail]
  ring

def d4BMCompletedEisensteinFullSignedRaiseWord (u nu : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinPhasedMaassWord true false u nu x Y +
    d4BMCompletedEisensteinPhasedMaassWord false true u nu x Y

def d4BMCompletedEisensteinFullSignedLowerWord (u nu : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinPhasedMaassWord false false u nu x Y +
    d4BMCompletedEisensteinPhasedMaassWord true true u nu x Y

def d4BMCompletedEisensteinComplexPowerFullSignedRaiseWord (u nu w : ℂ) (x Y : ℝ) : ℂ :=
  (Y : ℂ) ^ w * d4BMCompletedEisensteinFullSignedRaiseWord u nu x Y

def d4BMCompletedEisensteinComplexPowerFullSignedLowerWord (u nu w : ℂ) (x Y : ℝ) : ℂ :=
  (Y : ℂ) ^ w * d4BMCompletedEisensteinFullSignedLowerWord u nu x Y

theorem tendsto_d4BMCompletedEisensteinComplexPowerFullSignedRaiseWord_atTop_zero (u nu w : ℂ) (x : ℝ) :
    Tendsto (d4BMCompletedEisensteinComplexPowerFullSignedRaiseWord u nu w x) atTop (𝓝 0) := by
  have hp := tendsto_d4BMCompletedEisensteinComplexPowerPhasedMaassWord_atTop_zero true false u nu w x
  have hn := tendsto_d4BMCompletedEisensteinComplexPowerPhasedMaassWord_atTop_zero false true u nu w x
  have h := hp.add hn
  simp only [add_zero] at h
  convert h using 1
  funext Y
  simp [d4BMCompletedEisensteinComplexPowerFullSignedRaiseWord, d4BMCompletedEisensteinFullSignedRaiseWord,
    d4BMCompletedEisensteinComplexPowerPhasedMaassWord, mul_add]

theorem tendsto_d4BMCompletedEisensteinComplexPowerFullSignedLowerWord_atTop_zero (u nu w : ℂ) (x : ℝ) :
    Tendsto (d4BMCompletedEisensteinComplexPowerFullSignedLowerWord u nu w x) atTop (𝓝 0) := by
  have hp := tendsto_d4BMCompletedEisensteinComplexPowerPhasedMaassWord_atTop_zero false false u nu w x
  have hn := tendsto_d4BMCompletedEisensteinComplexPowerPhasedMaassWord_atTop_zero true true u nu w x
  have h := hp.add hn
  simp only [add_zero] at h
  convert h using 1
  funext Y
  simp [d4BMCompletedEisensteinComplexPowerFullSignedLowerWord, d4BMCompletedEisensteinFullSignedLowerWord,
    d4BMCompletedEisensteinComplexPowerPhasedMaassWord, mul_add]

/-- Full signed nonconstant weight-zero completed Eisenstein Whittaker tail. -/
def d4BMCompletedEisensteinFullSignedZeroWord (u nu : ℂ) (x Y : ℝ) : ℂ :=
  d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu false x 0 0 Y +
    d4BMCompletedEisensteinSignedSqrtWhittakerTail u nu true x 0 0 Y

/-- Arbitrary complex constant power multiplying the full signed weight-zero tail. -/
def d4BMCompletedEisensteinComplexPowerFullSignedZeroWord
    (u nu w : ℂ) (x Y : ℝ) : ℂ :=
  (Y : ℂ) ^ w * d4BMCompletedEisensteinFullSignedZeroWord u nu x Y

/-- Every complex-power-weighted full signed weight-zero tail vanishes at the cusp. -/
theorem tendsto_d4BMCompletedEisensteinComplexPowerFullSignedZeroWord_atTop_zero
    (u nu w : ℂ) (x : ℝ) :
    Tendsto (d4BMCompletedEisensteinComplexPowerFullSignedZeroWord u nu w x)
      atTop (𝓝 0) := by
  have hp :=
    tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero
      u nu w false x 0 0
  have hn :=
    tendsto_d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail_atTop_zero
      u nu w true x 0 0
  have h := hp.add hn
  simp only [add_zero] at h
  convert h using 1
  funext Y
  simp [d4BMCompletedEisensteinComplexPowerFullSignedZeroWord,
    d4BMCompletedEisensteinFullSignedZeroWord,
    d4BMCompletedEisensteinComplexPowerSignedSqrtWhittakerTail, mul_add]

end
end RHTower
