import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIActualBlockParameters

/-!
# Menon harmonic Case II: explicit polylogarithmic constants

Scalar bookkeeping for the Case-II large-value count of Menon's harmonic prime blocks `(a, Y]` with
`a < Y ≤ 2a`. The module fixes explicit numerical constants and bounds each factor of the Case-II
measure estimate by a power of `log a`: the divisor-count factor
`D = 3 (log₂(4Y) + 1)^3 (log₂ a + 1)^3`, the polylog envelope `maynardLongPolylogEnvelope (4Y)`, the
complement height `Hmax`, and the core exponent term. The end result bounds the full measure
expression by `menonHarmonicCaseIIMeasureConstant · ((log a)^1241 / T + 1)`.

## Main results

- `menonHarmonicCaseII_D_cast_le`: `D ≤ 3 · 17^6 · (log a)^6`.
- `maynardLongPolylogEnvelope_caseII_le`: `maynardLongPolylogEnvelope (4Y) ≤ 8 log a`.
- `menonHarmonicCaseII_Hmax_le`: the Case-II complement height is at most
  `menonHarmonicCaseIIComplementConstant · (log a)^1035 · (T + 1)`.
- `menonHarmonicCaseII_VexpCore_lower`: `a^e / (C_core (log a)^307)` is a lower bound for the
  exponent-core quantity, with `e = menonHarmonicCaseIICoreExponent`.
- `menonHarmonicCaseII_measureEnvelope_le`: the Case-II measure envelope is at most
  `menonHarmonicCaseIIMeasureConstant · ((log a)^1241 / T + 1)`.

## Hypotheses

All results are unconditional elementary inequalities. They assume the block-scale ranges
`8 ≤ a` or `256 ≤ a`, `1 ≤ log a`, `a < Y ≤ 2a`, and, where `T` appears, `0 ≤ T` or `1 ≤ T`; the
measure bound also assumes that `T` is at most the exponent-core quantity.
-/

namespace RHTower.Sieve

noncomputable section

/-- Constant `12 · 32^2 · 3^1035` in the polylogarithmic bound for the Case-II complement height. -/
def menonHarmonicCaseIIComplementConstant : ℝ :=
  12 * 32 ^ (2 : ℕ) * 3 ^ (1035 : ℕ)

/-- Constant `C_core` in the lower bound `a^e / (C_core (log a)^307)` for the exponent core. -/
def menonHarmonicCaseIICoreDenominatorConstant : ℝ :=
  5120 * 8 * (3 * 17 ^ (6 : ℕ)) * 8 / 2

/-- Core exponent `e = (1/8) · maynardDerivativeDeficit 26 = 1/(24 · 2^26)`. -/
def menonHarmonicCaseIICoreExponent : ℝ :=
  (1 / 8 : ℝ) * maynardDerivativeDeficit 26

def menonHarmonicCaseIIMeasureNumeratorConstant : ℝ :=
  2 * (3 * 17 ^ (6 : ℕ)) * 12 * menonHarmonicCaseIIComplementConstant

/-- Final constant of the Case-II measure bound: `16 · (measure numerator constant) + 8`. -/
def menonHarmonicCaseIIMeasureConstant : ℝ :=
  16 * menonHarmonicCaseIIMeasureNumeratorConstant + 8

/-- For `8 ≤ a`, `1 ≤ log a` and `a < Y ≤ 2a`, the dyadic divisor-count factor satisfies
`3 (log₂(4Y) + 1)^3 (log₂ a + 1)^3 ≤ 3 · 17^6 · (log a)^6`. -/
theorem menonHarmonicCaseII_D_cast_le
    {a Y : ℕ} (ha : 8 ≤ a) (hlog : 1 ≤ Real.log (a : ℝ))
    (haY : a < Y) (hYa : Y ≤ 2 * a) :
    ((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ) ≤
      3 * 17 ^ (6 : ℕ) * (Real.log (a : ℝ)) ^ (6 : ℕ) := by
  let X : ℕ := 4 * Y
  let la : ℝ := Real.log (a : ℝ)
  have ha0 : (0 : ℝ) < (a : ℝ) := by positivity
  have hX : 1 ≤ X := by dsimp only [X]; omega
  have hXle : (X : ℝ) ≤ 8 * (a : ℝ) := by
    dsimp only [X]
    push_cast
    have hYaR : (Y : ℝ) ≤ 2 * (a : ℝ) := by exact_mod_cast hYa
    nlinarith
  have hlog8 : Real.log (8 : ℝ) ≤ 7 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8) using 1 <;> norm_num
  have hlogX : Real.log (X : ℝ) ≤ 8 * la := by
    have hmono := Real.log_le_log (by positivity : (0 : ℝ) < (X : ℝ)) hXle
    rw [Real.log_mul (by norm_num : (8 : ℝ) ≠ 0) (ne_of_gt ha0)] at hmono
    dsimp only [la]
    nlinarith
  have hcountX : ((Nat.log 2 X + 1 : ℕ) : ℝ) ≤ 17 * la := by
    have hnat := natLogTwo_add_one_cast_le hX
    dsimp only [la] at hnat hlogX ⊢
    nlinarith
  have hcountA : ((Nat.log 2 a + 1 : ℕ) : ℝ) ≤ 17 * la := by
    have hnat := natLogTwo_add_one_cast_le (show 1 ≤ a by omega)
    dsimp only [la] at hnat ⊢
    nlinarith
  push_cast
  simp only [Nat.cast_add, Nat.cast_one] at hcountX hcountA
  change (3 : ℝ) * (((Nat.log 2 X : ℕ) : ℝ) + 1) ^ (3 : ℕ) *
      ((((Nat.log 2 a : ℕ) : ℝ) + 1) ^ (3 : ℕ)) ≤ _
  calc
    (3 : ℝ) * ((((Nat.log 2 X : ℕ) : ℝ) + 1) ^ (3 : ℕ)) *
        ((((Nat.log 2 a : ℕ) : ℝ) + 1) ^ (3 : ℕ)) ≤
      3 * (17 * la) ^ (3 : ℕ) * (17 * la) ^ (3 : ℕ) := by gcongr
    _ = 3 * 17 ^ (6 : ℕ) * la ^ (6 : ℕ) := by ring

/-- For `8 ≤ a`, `1 ≤ log a` and `a < Y ≤ 2a`, the long-factor polylog envelope at `4Y` is at most
`8 log a`. -/
theorem maynardLongPolylogEnvelope_caseII_le
    {a Y : ℕ} (ha : 8 ≤ a) (hlog : 1 ≤ Real.log (a : ℝ))
    (haY : a < Y) (hYa : Y ≤ 2 * a) :
    maynardLongPolylogEnvelope (4 * Y) ≤ 8 * Real.log (a : ℝ) := by
  apply maynardLongPolylogEnvelope_le_eight_log (show 1 ≤ 4 * Y by omega)
    (by exact_mod_cast (show 0 < a by omega)) hlog (by norm_num : (2 : ℝ) ≤ 19 / 9)
  have h8a : 8 * a ≤ a ^ 2 := by nlinarith
  have h4Y : 4 * Y ≤ 8 * a := by omega
  have : 4 * Y ≤ a ^ 2 := h4Y.trans h8a
  exact_mod_cast this

/-- For `256 ≤ a`, `1 ≤ log a`, `a < Y ≤ 2a` and `T ≥ 0`, the Case-II complement height
`12 W^2 (1 + log(W·4Y))^(P+2) (T + 1) (a/64)^(2 - 2σ)` (width `W = 32`, polylog exponent `P`) is at
most `menonHarmonicCaseIIComplementConstant · (log a)^1035 · (T + 1)`, using `σ > 1`. -/
theorem menonHarmonicCaseII_Hmax_le
    {a Y : ℕ} (ha : 256 ≤ a) (hlog : 1 ≤ Real.log (a : ℝ))
    (haY : a < Y) (hYa : Y ≤ 2 * a) {T : ℝ} (hT : 0 ≤ T) :
    (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
          (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
            (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
        (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * menonHarmonicCaseIISigma Y)) ≤
      menonHarmonicCaseIIComplementConstant *
        (Real.log (a : ℝ)) ^ (1035 : ℕ) * (T + 1) := by
  let la : ℝ := Real.log (a : ℝ)
  have ha0 : (0 : ℝ) < (a : ℝ) := by positivity
  have hbase : (1 : ℝ) ≤ (a : ℝ) / 64 := by
    rw [one_le_div (by norm_num)]
    exact_mod_cast (show 64 ≤ a by omega)
  have hsigma := menonHarmonicCaseIISigma_gt_one (show 0 < Y by omega)
  have hpow : ((a : ℝ) / 64) ^ (2 - 2 * menonHarmonicCaseIISigma Y) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hbase (by linarith)
  have hargNat : menonHeathBrownCaseIIComplementWidthConstant * ((4 * Y : ℕ) : ℝ) =
      ((128 * Y : ℕ) : ℝ) := by
    rw [menonHeathBrownCaseIIComplementWidthConstant]
    push_cast
    ring
  have harg : ((128 * Y : ℕ) : ℝ) ≤ (a : ℝ) ^ (2 : ℕ) := by
    have h256a : 256 * a ≤ a ^ 2 := by nlinarith
    have h128Y : 128 * Y ≤ 256 * a := by omega
    have hnat : 128 * Y ≤ a ^ 2 := h128Y.trans h256a
    exact_mod_cast hnat
  have harg0 : (0 : ℝ) < ((128 * Y : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 128 * Y by omega)
  have hlogArgRaw := Real.log_le_log harg0 harg
  rw [Real.log_pow] at hlogArgRaw
  have hlogArg : 1 + Real.log ((128 * Y : ℕ) : ℝ) ≤ 3 * la := by
    dsimp only [la] at hlogArgRaw hlog ⊢
    norm_num at hlogArgRaw
    norm_num only [Nat.cast_mul, Nat.cast_ofNat] at hlogArgRaw ⊢
    nlinarith
  have hlogArg0 : 0 ≤ 1 + Real.log ((128 * Y : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ ((128 * Y : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ 128 * Y by omega)
    exact add_nonneg zero_le_one (Real.log_nonneg this)
  rw [hargNat]
  rw [menonHeathBrownCaseIIComplementWidthConstant,
    menonHeathBrownCaseIIComplementPolylogExponent,
    menonHarmonicCaseIIComplementConstant]
  norm_num only [Nat.reducePow, Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat]
  calc
    (12288 : ℝ) *
          (1 + Real.log ((128 * Y : ℕ) : ℝ)) ^ (1035 : ℕ) *
        (T + 1) * ((a : ℝ) / 64) ^ (2 - 2 * menonHarmonicCaseIISigma Y) ≤
      12288 * (3 * la) ^ (1035 : ℕ) * (T + 1) * 1 := by
        gcongr
    _ = 12288 * 3 ^ (1035 : ℕ) *
        la ^ (1035 : ℕ) * (T + 1) := by ring

/-- For `256 ≤ a`, `1 ≤ log a` and `a < Y ≤ 2a`, the exponent-core quantity is bounded below by
`a^e / (menonHarmonicCaseIICoreDenominatorConstant · (log a)^307)`. -/
theorem menonHarmonicCaseII_VexpCore_lower
    {a Y : ℕ} (ha : 256 ≤ a) (hlog : 1 ≤ Real.log (a : ℝ))
    (haY : a < Y) (hYa : Y ≤ 2 * a) :
    ((a : ℝ) ^ menonHarmonicCaseIICoreExponent) /
        (menonHarmonicCaseIICoreDenominatorConstant *
          (Real.log (a : ℝ)) ^ (307 : ℕ)) ≤
      (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
          (5120 * maynardLongPolylogEnvelope (4 * Y)) *
        ((2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)) /
          (((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 *
              (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ) * 8)) := by
  let la : ℝ := Real.log (a : ℝ)
  let E : ℝ := maynardLongPolylogEnvelope (4 * Y)
  let D : ℝ := ((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 *
    (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ)
  let num : ℝ := (a : ℝ) ^ menonHarmonicCaseIICoreExponent
  have ha0 : (0 : ℝ) < (a : ℝ) := by positivity
  have hla0 : 0 < la := by dsimp only [la]; linarith
  have hEpos : 0 < E := by
    dsimp only [E]
    exact lt_of_lt_of_le zero_lt_one (one_le_maynardLongPolylogEnvelope _)
  have hDpos : 0 < D := by
    dsimp only [D]
    positivity
  have hE : E ≤ 8 * la := by
    simpa only [E, la] using maynardLongPolylogEnvelope_caseII_le
      (show 8 ≤ a by omega) hlog haY hYa
  have hD : D ≤ 3 * 17 ^ (6 : ℕ) * la ^ (6 : ℕ) := by
    simpa only [D, la] using menonHarmonicCaseII_D_cast_le
      (show 8 ≤ a by omega) hlog haY hYa
  have hnum0 : 0 ≤ num := by dsimp only [num]; positivity
  have hnumEq : num =
      ((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26 := by
    dsimp only [num, menonHarmonicCaseIICoreExponent]
    exact Real.rpow_mul ha0.le _ _
  have hrpow : la ^ (-300 : ℝ) = 1 / la ^ (300 : ℕ) := by
    rw [Real.rpow_neg hla0.le]
    rw [show la ^ (300 : ℝ) = la ^ (300 : ℕ) by
      simpa only [Nat.cast_ofNat] using Real.rpow_natCast la 300]
    simp only [one_div]
  let den : ℝ := 5120 * E * (D * 8) * la ^ (300 : ℕ) / 2
  have hden0 : 0 < den := by dsimp only [den]; positivity
  have hden : den ≤ menonHarmonicCaseIICoreDenominatorConstant * la ^ (307 : ℕ) := by
    calc
      den ≤ 5120 * (8 * la) *
          ((3 * 17 ^ (6 : ℕ) * la ^ (6 : ℕ)) * 8) *
            la ^ (300 : ℕ) / 2 := by
        dsimp only [den]
        gcongr
      _ = menonHarmonicCaseIICoreDenominatorConstant * la ^ (307 : ℕ) := by
        rw [menonHarmonicCaseIICoreDenominatorConstant]
        ring
  have hrewrite :
      (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
          (5120 * maynardLongPolylogEnvelope (4 * Y)) *
        ((2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)) /
          (((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 *
              (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ) * 8)) = num / den := by
    rw [← hnumEq]
    change num / (5120 * E) * ((2 * la ^ (-300 : ℝ)) / (D * 8)) = num / den
    rw [hrpow]
    dsimp only [den]
    field_simp [hEpos.ne', hDpos.ne', hla0.ne']
  rw [hrewrite]
  exact div_le_div_of_nonneg_left hnum0 hden0 hden

set_option maxRecDepth 10000 in
/-- For `256 ≤ a`, `1 ≤ log a`, `a < Y ≤ 2a`, `1 ≤ T` and `T` at most the exponent-core quantity,
the Case-II measure expression `2 (2π)⁻¹ · 4 (cells · D · 12 · Hmax / Vexp^2 + 1)` is at most
`menonHarmonicCaseIIMeasureConstant · ((log a)^1241 / T + 1)`. -/
theorem menonHarmonicCaseII_measureEnvelope_le
    {a Y : ℕ} (ha : 256 ≤ a) (hlog : 1 ≤ Real.log (a : ℝ))
    (haY : a < Y) (hYa : Y ≤ 2 * a) {T : ℝ} (hT : 1 ≤ T)
    (hcore : T ≤
      (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
          (5120 * maynardLongPolylogEnvelope (4 * Y)) *
        ((2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)) /
          (((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 *
              (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ) * 8))) :
    let cells := menonHarmonicCaseIICells a
    let D : ℕ := 3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
    let Vexp : ℝ :=
      min T ((((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
          (5120 * maynardLongPolylogEnvelope (4 * Y)) *
        ((2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)) / ((D : ℝ) * 8)))
    let Hmax : ℝ :=
      (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
          (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
            (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
        (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * menonHarmonicCaseIISigma Y))
    2 * (2 * Real.pi)⁻¹ *
        (4 * (((cells : ℝ) * (D : ℝ) * 12) * Hmax / Vexp ^ 2 + 1)) ≤
      menonHarmonicCaseIIMeasureConstant *
        ((Real.log (a : ℝ)) ^ (1241 : ℕ) / T + 1) := by
  dsimp only
  let la : ℝ := Real.log (a : ℝ)
  let cells := menonHarmonicCaseIICells a
  let D : ℝ := ((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 *
    (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ)
  let Hmax : ℝ :=
    (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
        (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
          (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
      (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * menonHarmonicCaseIISigma Y))
  let core : ℝ :=
    (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
        (5120 * maynardLongPolylogEnvelope (4 * Y)) *
      ((2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)) / (D * 8))
  have hla0 : 0 < la := by dsimp only [la]; linarith
  have hcells := menonHarmonicCaseIICells_cast_bounds hlog
  have hcells' : (cells : ℝ) ≤ 2 * la ^ (200 : ℕ) := by
    simpa only [cells, la] using hcells.2
  have hD : D ≤ 3 * 17 ^ (6 : ℕ) * la ^ (6 : ℕ) := by
    simpa only [D, la] using menonHarmonicCaseII_D_cast_le
      (show 8 ≤ a by omega) hlog haY hYa
  have hHmax : Hmax ≤ menonHarmonicCaseIIComplementConstant *
      la ^ (1035 : ℕ) * (T + 1) := by
    simpa only [Hmax, la] using
      menonHarmonicCaseII_Hmax_le ha hlog haY hYa (zero_le_one.trans hT)
  have hcore' : T ≤ core := by simpa only [core, D] using hcore
  have hmin : min T core = T := min_eq_left hcore'
  have hinv : (2 * Real.pi)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hpowT : 0 < T ^ (2 : ℕ) := pow_pos hT0 _
  have hTH : (T + 1) / T ^ (2 : ℕ) ≤ 2 / T := by
    rw [div_le_div_iff₀ hpowT hT0]
    nlinarith
  have hnum0 : 0 ≤ menonHarmonicCaseIIMeasureNumeratorConstant := by
    rw [menonHarmonicCaseIIMeasureNumeratorConstant,
      menonHarmonicCaseIIComplementConstant]
    positivity
  have hlaTerm0 : 0 ≤ la ^ (1241 : ℕ) / T := by positivity
  have hcells0 : 0 ≤ (cells : ℝ) := by positivity
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hcellsBound0 : 0 ≤ 2 * la ^ (200 : ℕ) := by positivity
  have hDBound0 : 0 ≤ 3 * 17 ^ (6 : ℕ) * la ^ (6 : ℕ) := by positivity
  have hcellD : (cells : ℝ) * D ≤
      (2 * la ^ (200 : ℕ)) * (3 * 17 ^ (6 : ℕ) * la ^ (6 : ℕ)) := by
    calc
      (cells : ℝ) * D ≤ (2 * la ^ (200 : ℕ)) * D :=
        mul_le_mul_of_nonneg_right hcells' hD0
      _ ≤ (2 * la ^ (200 : ℕ)) *
          (3 * 17 ^ (6 : ℕ) * la ^ (6 : ℕ)) :=
        mul_le_mul_of_nonneg_left hD hcellsBound0
  have hcellD12 : (cells : ℝ) * D * 12 ≤
      (2 * la ^ (200 : ℕ)) *
        (3 * 17 ^ (6 : ℕ) * la ^ (6 : ℕ)) * 12 :=
    mul_le_mul_of_nonneg_right hcellD (by norm_num)
  have harg1 : (1 : ℝ) ≤
      menonHeathBrownCaseIIComplementWidthConstant * ((4 * Y : ℕ) : ℝ) := by
    rw [menonHeathBrownCaseIIComplementWidthConstant]
    norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.reducePow]
    exact_mod_cast (show 1 ≤ 32 * (4 * Y) by omega)
  have hlogArg0 : 0 ≤ Real.log
      (menonHeathBrownCaseIIComplementWidthConstant * ((4 * Y : ℕ) : ℝ)) :=
    Real.log_nonneg harg1
  have hpolyBase0 : 0 ≤ 1 + Real.log
      (menonHeathBrownCaseIIComplementWidthConstant * ((4 * Y : ℕ) : ℝ)) :=
    add_nonneg zero_le_one hlogArg0
  have hprefactor0 : 0 ≤
      12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
        (1 + Real.log
          (menonHeathBrownCaseIIComplementWidthConstant * ((4 * Y : ℕ) : ℝ))) ^
            (menonHeathBrownCaseIIComplementPolylogExponent + 2) :=
    mul_nonneg (by positivity) (pow_nonneg hpolyBase0 _)
  have hTplus0 : 0 ≤ T + 1 := by linarith
  have hHmax0 : 0 ≤ Hmax := by
    dsimp only [Hmax]
    exact mul_nonneg (mul_nonneg hprefactor0 hTplus0)
      (Real.rpow_nonneg (by positivity) _)
  have hcellD12Bound0 : 0 ≤
      (2 * la ^ (200 : ℕ)) *
        (3 * 17 ^ (6 : ℕ) * la ^ (6 : ℕ)) * 12 := by positivity
  have hCDH : (((cells : ℝ) * D * 12) * Hmax) ≤
      menonHarmonicCaseIIMeasureNumeratorConstant *
        la ^ (1241 : ℕ) * (T + 1) := by
    calc
      (((cells : ℝ) * D * 12) * Hmax) ≤
          (((2 * la ^ (200 : ℕ)) *
            (3 * 17 ^ (6 : ℕ) * la ^ (6 : ℕ)) * 12) *
              (menonHarmonicCaseIIComplementConstant *
                la ^ (1035 : ℕ) * (T + 1))) := by
        calc
          ((cells : ℝ) * D * 12) * Hmax ≤
              ((2 * la ^ (200 : ℕ)) *
                (3 * 17 ^ (6 : ℕ) * la ^ (6 : ℕ)) * 12) * Hmax :=
            mul_le_mul_of_nonneg_right hcellD12 hHmax0
          _ ≤ ((2 * la ^ (200 : ℕ)) *
                (3 * 17 ^ (6 : ℕ) * la ^ (6 : ℕ)) * 12) *
              (menonHarmonicCaseIIComplementConstant *
                la ^ (1035 : ℕ) * (T + 1)) :=
            mul_le_mul_of_nonneg_left hHmax hcellD12Bound0
      _ = menonHarmonicCaseIIMeasureNumeratorConstant *
          la ^ (1241 : ℕ) * (T + 1) := by
        rw [menonHarmonicCaseIIMeasureNumeratorConstant]
        ring
  have hfrac : (((cells : ℝ) * D * 12) * Hmax) / T ^ 2 ≤
      menonHarmonicCaseIIMeasureNumeratorConstant *
        la ^ (1241 : ℕ) * (T + 1) / T ^ 2 :=
    div_le_div_of_nonneg_right hCDH hpowT.le
  have hcellD120 : 0 ≤ (cells : ℝ) * D * 12 := by
    exact mul_nonneg (mul_nonneg hcells0 hD0) (by norm_num)
  have hmeasureQuotient0 : 0 ≤
      ((cells : ℝ) * D * 12) * Hmax / T ^ 2 :=
    div_nonneg (mul_nonneg hcellD120 hHmax0) hpowT.le
  have hmeasureBracket0 : 0 ≤
      4 * (((cells : ℝ) * D * 12) * Hmax / T ^ 2 + 1) :=
    mul_nonneg (by norm_num) (add_nonneg hmeasureQuotient0 zero_le_one)
  have htwoInv : 2 * (2 * Real.pi)⁻¹ ≤ 2 * 1 :=
    mul_le_mul_of_nonneg_left hinv (by norm_num)
  rw [hmin]
  calc
    2 * (2 * Real.pi)⁻¹ *
        (4 * (((cells : ℝ) * D * 12) * Hmax / T ^ 2 + 1)) ≤
      2 * 1 * (4 * (((cells : ℝ) * D * 12) * Hmax / T ^ 2 + 1)) := by
        exact mul_le_mul_of_nonneg_right htwoInv hmeasureBracket0
    _ = 8 * ((((cells : ℝ) * D * 12) * Hmax / T ^ 2) + 1) := by ring
    _ ≤ 8 * (menonHarmonicCaseIIMeasureNumeratorConstant *
          la ^ (1241 : ℕ) * (T + 1) / T ^ 2 + 1) := by gcongr
    _ = 8 * (menonHarmonicCaseIIMeasureNumeratorConstant *
          la ^ (1241 : ℕ) * ((T + 1) / T ^ 2) + 1) := by
      ring
    _ ≤ 8 * (menonHarmonicCaseIIMeasureNumeratorConstant *
          la ^ (1241 : ℕ) * (2 / T) + 1) := by gcongr
    _ = 16 * menonHarmonicCaseIIMeasureNumeratorConstant *
          (la ^ (1241 : ℕ) / T) + 8 := by ring
    _ ≤ (16 * menonHarmonicCaseIIMeasureNumeratorConstant + 8) *
          (la ^ (1241 : ℕ) / T + 1) := by
      have hA : 0 ≤ 16 * menonHarmonicCaseIIMeasureNumeratorConstant := by positivity
      have hB : 0 ≤ 8 * (la ^ (1241 : ℕ) / T) := by positivity
      nlinarith
    _ = menonHarmonicCaseIIMeasureConstant * (la ^ (1241 : ℕ) / T + 1) := by
      rw [menonHarmonicCaseIIMeasureConstant]

end

end RHTower.Sieve

