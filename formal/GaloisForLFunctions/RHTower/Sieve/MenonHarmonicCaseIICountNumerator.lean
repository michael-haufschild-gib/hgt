import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIScalarBounds

namespace RHTower.Sieve

noncomputable section

open Filter Finset

/-- The exact multiplicative loss following the raw `min` in the Case-II amplitude retains 307
inverse logarithmic powers. -/
theorem menonHarmonicCaseII_VexpFactor_lower
    {a Y : ℕ} (ha : 256 ≤ a) (hlog : 1 ≤ Real.log (a : ℝ))
    (haY : a < Y) (hYa : Y ≤ 2 * a) :
    1 / (menonHarmonicCaseIICoreDenominatorConstant *
          (Real.log (a : ℝ)) ^ (307 : ℕ)) ≤
      1 / (5120 * maynardLongPolylogEnvelope (4 * Y)) *
        ((2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)) /
          (((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 *
              (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ) * 8)) := by
  let P : ℝ := (a : ℝ) ^ menonHarmonicCaseIICoreExponent
  have ha0 : (0 : ℝ) < (a : ℝ) := by positivity
  have hP0 : 0 < P := by dsimp only [P]; positivity
  have hPraw : P =
      ((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26 := by
    dsimp only [P, menonHarmonicCaseIICoreExponent]
    exact Real.rpow_mul ha0.le _ _
  have hbase := menonHarmonicCaseII_VexpCore_lower ha hlog haY hYa
  rw [← hPraw] at hbase
  have hmul :
      P * (1 / (menonHarmonicCaseIICoreDenominatorConstant *
          (Real.log (a : ℝ)) ^ (307 : ℕ))) ≤
        P * (1 / (5120 * maynardLongPolylogEnvelope (4 * Y)) *
          ((2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)) /
            (((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 *
                (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ) * 8))) := by
    calc
      P * (1 / (menonHarmonicCaseIICoreDenominatorConstant *
          (Real.log (a : ℝ)) ^ (307 : ℕ))) =
        P / (menonHarmonicCaseIICoreDenominatorConstant *
          (Real.log (a : ℝ)) ^ (307 : ℕ)) := by ring
      _ ≤ P / (5120 * maynardLongPolylogEnvelope (4 * Y)) *
          ((2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)) /
            (((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 *
                (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ) * 8)) := hbase
      _ = P * (1 / (5120 * maynardLongPolylogEnvelope (4 * Y)) *
          ((2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)) /
            (((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 *
                (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ) * 8))) := by ring
  nlinarith

set_option maxRecDepth 10000 in
/-- The literal Case-II cardinal numerator is bounded by its explicit logarithmic envelope. -/
theorem menonHarmonicCaseII_countNumerator_le
    {a Y : ℕ} (ha : 256 ≤ a) (hlog : 1 ≤ Real.log (a : ℝ))
    (haY : a < Y) (hYa : Y ≤ 2 * a) {T : ℝ} (hT : 0 ≤ T) :
    let cells := menonHarmonicCaseIICells a
    let D : ℕ := 3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
    let Hmax : ℝ :=
      (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
          (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
            (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
        (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * menonHarmonicCaseIISigma Y))
    (((cells : ℝ) * (D : ℝ) * 12) * Hmax) ≤
      menonHarmonicCaseIIMeasureNumeratorConstant *
        (Real.log (a : ℝ)) ^ (1241 : ℕ) * (T + 1) := by
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
  have hcells := menonHarmonicCaseIICells_cast_bounds hlog
  have hcells' : (cells : ℝ) ≤ 2 * la ^ (200 : ℕ) := by
    simpa only [cells, la] using hcells.2
  have hD : D ≤ 3 * 17 ^ (6 : ℕ) * la ^ (6 : ℕ) := by
    simpa only [D, la] using menonHarmonicCaseII_D_cast_le
      (show 8 ≤ a by omega) hlog haY hYa
  have hHmax : Hmax ≤ menonHarmonicCaseIIComplementConstant *
      la ^ (1035 : ℕ) * (T + 1) := by
    simpa only [Hmax, la] using
      menonHarmonicCaseII_Hmax_le ha hlog haY hYa hT
  have hcells0 : 0 ≤ (cells : ℝ) := by positivity
  have hD0 : 0 ≤ D := by dsimp only [D]; positivity
  have hcellsBound0 : 0 ≤ 2 * la ^ (200 : ℕ) := by positivity
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
  have hcellD12Bound0 : 0 ≤
      (2 * la ^ (200 : ℕ)) *
        (3 * 17 ^ (6 : ℕ) * la ^ (6 : ℕ)) * 12 := by positivity
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

/-- Above the explicit polylogarithmic crossover, the Case-II cardinal numerator is strictly
smaller than the square of the physical band scale. -/
theorem menonHarmonicCaseII_countNumerator_lt_sq
    {a Y : ℕ} (ha : 256 ≤ a) (hlog : 1 ≤ Real.log (a : ℝ))
    (haY : a < Y) (hYa : Y ≤ 2 * a) {T : ℝ} (hT : 1 ≤ T)
    (hcross : 2 * menonHarmonicCaseIIMeasureNumeratorConstant *
      (Real.log (a : ℝ)) ^ (1241 : ℕ) < T) :
    let cells := menonHarmonicCaseIICells a
    let D : ℕ := 3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
    let Hmax : ℝ :=
      (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
          (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
            (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
        (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * menonHarmonicCaseIISigma Y))
    (((cells : ℝ) * (D : ℝ) * 12) * Hmax) < T ^ 2 := by
  dsimp only
  let la : ℝ := Real.log (a : ℝ)
  let cells := menonHarmonicCaseIICells a
  let D : ℕ := 3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
  let Hmax : ℝ :=
    (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
        (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
          (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
      (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * menonHarmonicCaseIISigma Y))
  have hbase : (((cells : ℝ) * (D : ℝ) * 12) * Hmax) ≤
      menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) * (T + 1) := by
    simpa only [cells, D, Hmax, la] using
      menonHarmonicCaseII_countNumerator_le ha hlog haY hYa (zero_le_one.trans hT)
  have hconst0 : 0 ≤ menonHarmonicCaseIIMeasureNumeratorConstant := by
    rw [menonHarmonicCaseIIMeasureNumeratorConstant,
      menonHarmonicCaseIIComplementConstant]
    positivity
  have hla0 : 0 ≤ la := by dsimp only [la]; linarith
  have hpoly0 : 0 ≤ menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) :=
    mul_nonneg hconst0 (pow_nonneg hla0 _)
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  calc
    (((cells : ℝ) * (D : ℝ) * 12) * Hmax) ≤
        menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) * (T + 1) := hbase
    _ ≤ menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) * (2 * T) := by
      gcongr
      linarith
    _ = (2 * menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ)) * T := by ring
    _ < T * T := mul_lt_mul_of_pos_right hcross hT0
    _ = T ^ 2 := by ring

/-- The literal cardinal numerator is smaller than the square of the order-four-hundred amplitude
after its full 307-logarithm multiplicative loss. -/
theorem menonHarmonicCaseII_countNumerator_lt_scaledSq
    {a Y : ℕ} (ha : 256 ≤ a) (hlog : 1 ≤ Real.log (a : ℝ))
    (haY : a < Y) (hYa : Y ≤ 2 * a) {T : ℝ} (hT : 1 ≤ T)
    (hcross : 2 * menonHarmonicCaseIIMeasureNumeratorConstant *
        menonHarmonicCaseIICoreDenominatorConstant ^ (2 : ℕ) *
        (Real.log (a : ℝ)) ^ (1855 : ℕ) < T) :
    let cells := menonHarmonicCaseIICells a
    let D : ℕ := 3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
    let Hmax : ℝ :=
      (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
          (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
            (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
        (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * menonHarmonicCaseIISigma Y))
    (((cells : ℝ) * (D : ℝ) * 12) * Hmax) <
      (T / (menonHarmonicCaseIICoreDenominatorConstant *
        (Real.log (a : ℝ)) ^ (307 : ℕ))) ^ 2 := by
  dsimp only
  let la : ℝ := Real.log (a : ℝ)
  let K : ℝ := menonHarmonicCaseIICoreDenominatorConstant
  let den : ℝ := K * la ^ (307 : ℕ)
  let cells := menonHarmonicCaseIICells a
  let D : ℕ := 3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
  let Hmax : ℝ :=
    (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
        (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
          (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
      (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * menonHarmonicCaseIISigma Y))
  have hK0 : 0 < K := by
    dsimp only [K, menonHarmonicCaseIICoreDenominatorConstant]
    positivity
  have hla0 : 0 < la := by dsimp only [la]; linarith
  have hden0 : 0 < den := by dsimp only [den]; positivity
  have hT0 : 0 < T := zero_lt_one.trans_le hT
  have hC0 : 0 ≤ menonHarmonicCaseIIMeasureNumeratorConstant := by
    rw [menonHarmonicCaseIIMeasureNumeratorConstant,
      menonHarmonicCaseIIComplementConstant]
    positivity
  have hpoly0 : 0 ≤
      menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) := by
    positivity
  have hbase : (((cells : ℝ) * (D : ℝ) * 12) * Hmax) ≤
      menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) * (T + 1) := by
    simpa only [cells, D, Hmax, la] using
      menonHarmonicCaseII_countNumerator_le ha hlog haY hYa (zero_le_one.trans hT)
  have hupper :
      menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) * (T + 1) ≤
        2 * menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) * T := by
    nlinarith
  have hdenIdentity :
      2 * menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) * den ^ 2 =
        2 * menonHarmonicCaseIIMeasureNumeratorConstant * K ^ (2 : ℕ) *
          la ^ (1855 : ℕ) := by
    dsimp only [den]
    ring
  have hcross' :
      2 * menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) * den ^ 2 < T := by
    rw [hdenIdentity]
    simpa only [K, la] using hcross
  have hmul :
      (2 * menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) * T) * den ^ 2 <
        T ^ 2 := by
    have h := mul_lt_mul_of_pos_right hcross' hT0
    nlinarith
  have hdiv :
      2 * menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) * T <
        T ^ 2 / den ^ 2 := by
    rw [lt_div_iff₀ (sq_pos_of_pos hden0)]
    exact hmul
  calc
    (((cells : ℝ) * (D : ℝ) * 12) * Hmax) ≤
        menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) * (T + 1) := hbase
    _ ≤ 2 * menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) * T := hupper
    _ < T ^ 2 / den ^ 2 := hdiv
    _ = (T / den) ^ 2 := by ring

/-- Generic strict comparison with a selected raw Case-II amplitude. This form covers both sides
of the `min T a^delta` crossover without changing the literal amplitude. -/
theorem menonHarmonicCaseII_countNumerator_lt_scaledAmplitude
    {a Y : ℕ} (ha : 256 ≤ a) (hlog : 1 ≤ Real.log (a : ℝ))
    (haY : a < Y) (hYa : Y ≤ 2 * a) {T M : ℝ} (hT : 1 ≤ T)
    (hcross : menonHarmonicCaseIIMeasureNumeratorConstant *
        menonHarmonicCaseIICoreDenominatorConstant ^ (2 : ℕ) *
        (Real.log (a : ℝ)) ^ (1855 : ℕ) * (T + 1) < M ^ 2) :
    let cells := menonHarmonicCaseIICells a
    let D : ℕ := 3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
    let Hmax : ℝ :=
      (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
          (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
            (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
        (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * menonHarmonicCaseIISigma Y))
    (((cells : ℝ) * (D : ℝ) * 12) * Hmax) <
      (M / (menonHarmonicCaseIICoreDenominatorConstant *
        (Real.log (a : ℝ)) ^ (307 : ℕ))) ^ 2 := by
  dsimp only
  let la : ℝ := Real.log (a : ℝ)
  let K : ℝ := menonHarmonicCaseIICoreDenominatorConstant
  let den : ℝ := K * la ^ (307 : ℕ)
  let cells := menonHarmonicCaseIICells a
  let D : ℕ := 3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
  let Hmax : ℝ :=
    (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
        (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
          (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
      (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * menonHarmonicCaseIISigma Y))
  have hK0 : 0 < K := by
    dsimp only [K, menonHarmonicCaseIICoreDenominatorConstant]
    positivity
  have hla0 : 0 < la := by dsimp only [la]; linarith
  have hden0 : 0 < den := by dsimp only [den]; positivity
  have hbase : (((cells : ℝ) * (D : ℝ) * 12) * Hmax) ≤
      menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) * (T + 1) := by
    simpa only [cells, D, Hmax, la] using
      menonHarmonicCaseII_countNumerator_le ha hlog haY hYa (zero_le_one.trans hT)
  have hdenIdentity :
      menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) *
          (T + 1) * den ^ 2 =
        menonHarmonicCaseIIMeasureNumeratorConstant * K ^ (2 : ℕ) *
          la ^ (1855 : ℕ) * (T + 1) := by
    dsimp only [den]
    ring
  have hmul :
      (menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) *
          (T + 1)) * den ^ 2 < M ^ 2 := by
    rw [hdenIdentity]
    simpa only [K, la] using hcross
  have hdiv :
      menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) * (T + 1) <
        M ^ 2 / den ^ 2 := by
    rw [lt_div_iff₀ (sq_pos_of_pos hden0)]
    exact hmul
  calc
    (((cells : ℝ) * (D : ℝ) * 12) * Hmax) ≤
        menonHarmonicCaseIIMeasureNumeratorConstant * la ^ (1241 : ℕ) * (T + 1) := hbase
    _ < M ^ 2 / den ^ 2 := hdiv
    _ = (M / den) ^ 2 := by ring

set_option maxHeartbeats 800000 in
/-- Structural order-four-hundred Case-II cardinal estimate for a narrow block and an arbitrary
positive smoothing width. -/
theorem exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_orderFourHundred_narrow_smoothing_realFinset :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ a : ℕ in atTop,
        ∀ {Y cells : ℕ} {H B sigma T : ℝ} {E : Finset ℝ},
        a < Y → Y ≤ 2 * a → 0 < H → H ≤ 3 * (Y : ℝ) →
        1 < sigma → 0 ≤ B → 0 < cells →
        1 ≤ T → (cells : ℝ) / 4 ≤ T →
        (∀ u ∈ E, ∀ v ∈ E, u ≠ v → 2 ≤ |u - v|) →
        (∀ u ∈ E, T + (cells : ℝ) / 2 ≤ u ∧
          u ≤ 2 * T - (cells : ℝ) / 2) →
        2 * T ≤ (a : ℝ) ^ (3 : ℕ) →
        let C : ℝ := menonWideIntervalAmbientKernelMajorant C0 (4 * Y) H sigma
        let Q : ℝ :=
          (B - heathBrownWindowRelevantFixedPolylogBound a (4 * Y) 3 (a : ℝ) sigma * C *
              (Real.pi - 2 * Real.arctan ((cells : ℝ) / 2))) /
            ((cells : ℝ) * C)
        (Real.log (a : ℝ)) ^ (-300 : ℝ) < Q →
        (∀ u ∈ E,
          (((B + menonWideIntervalTransitionEnvelope (4 * Y) H) +
                primePowerDefectIoc a Y) /
              Real.log ((a + 1 : ℕ) : ℝ)) /
                ((a + 1 : ℕ) : ℝ) <
            ‖harmonicPrimeBlockPoly (primesRange a Y)
              (-u / (2 * Real.pi))‖) →
        let D : ℕ :=
          3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
        let Vexp : ℝ :=
          min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
              (5120 * maynardLongPolylogEnvelope (4 * Y)) * (Q / ((D : ℝ) * 8))
        let Hmax : ℝ :=
          (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
              (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
        (E.card : ℝ) * Vexp ^ 2 ≤ (((cells * D * 12 : ℕ) : ℝ)) * Hmax := by
  obtain ⟨C0, hC0, hmain⟩ :=
    exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_wide_orderFourHundred_realFinset
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hmain, eventually_ge_atTop ((64 : ℕ) ^ 8)] with a ha ha64
  intro Y cells H B sigma T E haY hYa hH hHY hsigma hB hcells hT hcellsT hsep hband h2T
  dsimp only
  intro hQ hlarge
  have ha1 : 1 ≤ a := by omega
  have hX : 1 ≤ 4 * Y := by omega
  have ha3 : 3 ≤ a := by omega
  have h8leSq : 8 ≤ a ^ 2 := by
    have hsq : 3 ^ 2 ≤ a ^ 2 := Nat.pow_le_pow_left ha3 2
    omega
  have h8Mul : 8 * a ≤ a ^ 3 := by
    calc
      8 * a ≤ a ^ 2 * a := Nat.mul_le_mul_right a h8leSq
      _ = a ^ 3 := by ring
  have hXL : 4 * Y < (a + 1) ^ 3 := by
    have h8a : 4 * Y ≤ 8 * a := by omega
    have hcubic : a ^ 3 < (a + 1) ^ 3 :=
      pow_lt_pow_left₀ (by omega : a < a + 1) (Nat.zero_le a) (by norm_num)
    exact lt_of_le_of_lt (h8a.trans h8Mul) hcubic
  have hLX : a ≤ 4 * Y := by omega
  have hXaNat : 4 * Y ≤ a ^ 3 := by
    have h8a : 4 * Y ≤ 8 * a := by omega
    exact h8a.trans h8Mul
  have hXa : ((4 * Y : ℕ) : ℝ) ≤ (a : ℝ) ^ (3 : ℕ) := by exact_mod_cast hXaNat
  have hYX : (Y : ℝ) + H ≤ ((4 * Y : ℕ) : ℝ) := by
    push_cast
    linarith
  have hscale : ((2 ^ 6 : ℕ) : ℝ) * (2 : ℝ) ^ (0 : ℝ) ≤ (a : ℝ) := by
    norm_num
    exact_mod_cast (show (64 : ℕ) ≤ a by omega)
  have hV : (0 : ℝ) ≤ (cells : ℝ) / 2 := by positivity
  have hgrid : 2 * ((cells : ℝ) / 2) = (cells : ℝ) * 1 := by ring
  have hhalfT : (1 : ℝ) / 2 ≤ T := by linarith
  have hQ' : (Real.log (a : ℝ)) ^ (-300 : ℝ) <
      (B - heathBrownWindowRelevantFixedPolylogBound a (4 * Y) 3 (a : ℝ) sigma *
          menonWideIntervalAmbientKernelMajorant C0 (4 * Y) H sigma *
            (Real.pi - 2 * Real.arctan ((cells : ℝ) / 2))) /
        ((cells : ℝ) * 1 *
          menonWideIntervalAmbientKernelMajorant C0 (4 * Y) H sigma) := by
    simpa only [mul_one] using hQ
  have hbound := ha (L := a) (X := 4 * Y) (Y := Y) (cells := cells)
    (T0 := 2) (t := 0) (H := H) (B := B) (sigma := sigma)
    (V := (cells : ℝ) / 2) (Δ := 1) (T := T) (E := E)
    hX haY hXL (by norm_num) hscale (by exact_mod_cast ha64) ha1 hLX hXa hH hYX hsigma hB hV
    (by norm_num) hcells hgrid (by simpa using hsep) hT hhalfT hband h2T hQ' hlarge
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_one] using hbound

set_option maxHeartbeats 800000 in
/-- Every actual final-range block inherits the scheduled order-four-hundred Case-II cardinal
estimate on a literal finite separated set. -/
theorem exists_absolute_eventually_card_mul_sq_le_menonFinalRangeActualBlock_caseII_scheduled_realFinset :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ j ∈ Finset.range (menonFinalRangeLadderSteps x),
        ∀ {T : ℝ} {E : Finset ℝ},
        1 ≤ T → (menonHarmonicCaseIICells (menonFinalRangeBlockLowerNat x j) : ℝ) / 4 ≤ T →
        (∀ u ∈ E, ∀ v ∈ E, u ≠ v → 2 ≤ |u - v|) →
        (∀ u ∈ E,
          T + (menonHarmonicCaseIICells (menonFinalRangeBlockLowerNat x j) : ℝ) / 2 ≤ u ∧
          u ≤ 2 * T -
            (menonHarmonicCaseIICells (menonFinalRangeBlockLowerNat x j) : ℝ) / 2) →
        2 * T ≤ (menonFinalRangeBlockLowerNat x j : ℝ) ^ (3 : ℕ) →
        let a := menonFinalRangeBlockLowerNat x j
        let Y := menonFinalRangeActualBlockUpperNat x j
        let cells := menonHarmonicCaseIICells a
        let H := menonHarmonicCaseIISmoothingWidth a
        let sigma := menonHarmonicCaseIISigma Y
        let B := menonHarmonicCaseIIBudget C0 a Y
        let Q := 2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)
        (∀ u ∈ E,
          (((B + menonWideIntervalTransitionEnvelope (4 * Y) H) +
                primePowerDefectIoc a Y) /
              Real.log ((a + 1 : ℕ) : ℝ)) /
                ((a + 1 : ℕ) : ℝ) <
            ‖harmonicPrimeBlockPoly (primesRange a Y)
              (-u / (2 * Real.pi))‖) →
        let D : ℕ :=
          3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
        let Vexp : ℝ :=
          min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26) /
              (5120 * maynardLongPolylogEnvelope (4 * Y)) * (Q / ((D : ℝ) * 8))
        let Hmax : ℝ :=
          (12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
              (1 + Real.log (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma))
        (E.card : ℝ) * Vexp ^ 2 ≤ (((cells * D * 12 : ℕ) : ℝ)) * Hmax := by
  obtain ⟨C0, hC0, hcase⟩ :=
    exists_absolute_eventually_card_mul_sq_le_menonHarmonicPrimeBlock_caseII_orderFourHundred_narrow_smoothing_realFinset
  rw [eventually_atTop] at hcase
  obtain ⟨a0, hcase⟩ := hcase
  have hbase := tendsto_menonFinalRangePrimeCutoffNat_atTop.eventually_ge_atTop a0
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [eventually_menonFinalRangeActualBlock_caseII_endpoints, hbase,
    eventually_two_le_menonFinalRangePrimeCutoffNat,
    eventually_menonFinalRangeLadder_basic] with x hx hbaseX hbaseTwo hbasic
  intro j hj T E hT hcellsT hsep hband h2T
  have hend := hx j hj
  rcases hend with ⟨_ha64, haY, hYa⟩
  let a := menonFinalRangeBlockLowerNat x j
  let Y := menonFinalRangeActualBlockUpperNat x j
  let cells := menonHarmonicCaseIICells a
  let H := menonHarmonicCaseIISmoothingWidth a
  let sigma := menonHarmonicCaseIISigma Y
  let B := menonHarmonicCaseIIBudget C0 a Y
  have hbaseLe : menonFinalRangePrimeCutoffNat x ≤ a := by
    have hbase0 : 0 < menonFinalRangeLadderBase x := by
      rw [menonFinalRangeLadderBase]
      exact_mod_cast (show 0 < menonFinalRangePrimeCutoffNat x by omega)
    have hstep : 1 ≤ 1 + menonFinalRangeLadderEta x := by
      rcases hbasic with ⟨_, _, _, _, heta, _⟩
      linarith
    have hq : menonFinalRangeLadderBase x ≤
        menonFinalRangeLadderBase x * (1 + menonFinalRangeLadderEta x) ^ j :=
      le_mul_of_one_le_right hbase0.le (one_le_pow₀ hstep)
    change menonFinalRangePrimeCutoffNat x ≤ menonFinalRangeBlockLowerNat x j
    rw [menonFinalRangeBlockLowerNat,
      ← Nat.floor_natCast (R := ℝ) (menonFinalRangePrimeCutoffNat x)]
    exact Nat.floor_mono hq
  have ha0 : a0 ≤ a := hbaseX.trans hbaseLe
  have ha : 1 < a := hbaseTwo.trans hbaseLe
  have hH : 0 < H := menonHarmonicCaseIISmoothingWidth_pos ha
  have hlogOne : 1 ≤ Real.log (a : ℝ) := by
    have haThree : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast (show 3 ≤ a by omega)
    have hexpThree : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    have hexp : Real.exp 1 ≤ (a : ℝ) := hexpThree.le.trans haThree
    have hlog := Real.log_le_log (Real.exp_pos 1) hexp
    simpa using hlog
  have hHle : H ≤ 3 * (Y : ℝ) := by
    simp only [H, menonHarmonicCaseIISmoothingWidth]
    have hden : 1 ≤ (Real.log (a : ℝ)) ^ (20 : ℕ) := one_le_pow₀ hlogOne
    have hdiv : (a : ℝ) / (Real.log (a : ℝ)) ^ (20 : ℕ) ≤ (a : ℝ) :=
      div_le_self (Nat.cast_nonneg a) hden
    have haYR : (a : ℝ) ≤ (Y : ℝ) := by exact_mod_cast haY.le
    linarith
  have hsigma : 1 < sigma :=
    menonHarmonicCaseIISigma_gt_one (show 0 < Y by omega)
  have hYpos : 0 < Y := Nat.zero_lt_of_lt haY
  have hB : 0 ≤ B := menonHarmonicCaseIIBudget_nonneg hC0 ha hYpos
  have hcells : 0 < cells := menonHarmonicCaseIICells_pos ha
  have hQeq := menonHarmonicCaseII_quotient_eq
    (C0 := C0) (a := a) (Y := Y) hC0 ha hYpos
  have hlog : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast ha)
  have hQlt : (Real.log (a : ℝ)) ^ (-300 : ℝ) <
      2 * (Real.log (a : ℝ)) ^ (-300 : ℝ) := by
    have := Real.rpow_pos_of_pos hlog (-300 : ℝ)
    linarith
  dsimp only
  intro hlarge
  have hbound := hcase a ha0 (Y := Y) (cells := cells) (H := H) (B := B)
    (sigma := sigma) (T := T) (E := E)
    (by simpa only [a, Y] using haY) (by simpa only [a, Y] using hYa)
    hH hHle hsigma hB hcells hT (by simpa only [cells] using hcellsT)
    (by simpa only [cells] using hsep) (by simpa only [cells] using hband)
    (by simpa only [a] using h2T) (by rw [hQeq]; exact hQlt)
    (by simpa only [a, Y, H, B] using hlarge)
  rw [hQeq] at hbound
  simpa only [a, Y, cells, H, sigma, B] using hbound

set_option maxHeartbeats 800000 in
/-- In the scheduled Case-II band, a singleton violating the exact wide-smoothed threshold would
contradict the strict scalar cardinal budget. -/
theorem exists_absolute_eventually_norm_menonFinalRangeActualBlock_le_threshold_of_caseII :
    ∃ C0 : ℝ, 0 ≤ C0 ∧
      ∀ᶠ x : ℝ in atTop,
        ∀ j ∈ Finset.range (menonFinalRangeLadderSteps x),
        ∀ {T u : ℝ},
        1 ≤ T → (menonHarmonicCaseIICells (menonFinalRangeBlockLowerNat x j) : ℝ) / 4 ≤ T →
        T + (menonHarmonicCaseIICells (menonFinalRangeBlockLowerNat x j) : ℝ) / 2 ≤ u →
        u ≤ 2 * T -
          (menonHarmonicCaseIICells (menonFinalRangeBlockLowerNat x j) : ℝ) / 2 →
        2 * T ≤ (menonFinalRangeBlockLowerNat x j : ℝ) ^ (3 : ℕ) →
        let a := menonFinalRangeBlockLowerNat x j
        let Y := menonFinalRangeActualBlockUpperNat x j
        let cells := menonHarmonicCaseIICells a
        let H := menonHarmonicCaseIISmoothingWidth a
        let sigma := menonHarmonicCaseIISigma Y
        let B := menonHarmonicCaseIIBudget C0 a Y
        let Q := 2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)
        let D : ℕ :=
          3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
        menonHarmonicCaseIIMeasureNumeratorConstant *
            menonHarmonicCaseIICoreDenominatorConstant ^ (2 : ℕ) *
            (Real.log (a : ℝ)) ^ (1855 : ℕ) * (T + 1) <
          (min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26)) ^ 2 →
        ‖harmonicPrimeBlockPoly (primesRange a Y)
              (-u / (2 * Real.pi))‖ ≤
          (((B + menonWideIntervalTransitionEnvelope (4 * Y) H) +
                primePowerDefectIoc a Y) /
              Real.log ((a + 1 : ℕ) : ℝ)) /
                ((a + 1 : ℕ) : ℝ) := by
  obtain ⟨C0, hC0, hscheduled⟩ :=
    exists_absolute_eventually_card_mul_sq_le_menonFinalRangeActualBlock_caseII_scheduled_realFinset
  refine ⟨C0, hC0, ?_⟩
  filter_upwards [hscheduled, eventually_menonFinalRangeActualBlock_caseII_endpoints]
      with x hsched hendpoints
  intro j hj T u hT hcellsT hbandLo hbandHi h2T
  let a := menonFinalRangeBlockLowerNat x j
  let Y := menonFinalRangeActualBlockUpperNat x j
  let cells := menonHarmonicCaseIICells a
  let H := menonHarmonicCaseIISmoothingWidth a
  let sigma := menonHarmonicCaseIISigma Y
  let B := menonHarmonicCaseIIBudget C0 a Y
  let Q := 2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)
  let D : ℕ := 3 * (Nat.log 2 (4 * Y) + 1) ^ 3 * (Nat.log 2 a + 1) ^ 3
  dsimp only
  intro hcross
  have hend := hendpoints j hj
  rcases hend with ⟨ha64, haY, hYa⟩
  have ha256 : 256 ≤ a := by
    dsimp only [a]
    omega
  have hlog : 1 ≤ Real.log (a : ℝ) := by
    have haThree : (3 : ℝ) ≤ (a : ℝ) := by
      exact_mod_cast (show 3 ≤ a by omega)
    have hexpThree : Real.exp 1 < (3 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num)
    have hexp : Real.exp 1 ≤ (a : ℝ) := hexpThree.le.trans haThree
    have hlog' := Real.log_le_log (Real.exp_pos 1) hexp
    simpa using hlog'
  by_contra hnot
  have hlarge :
      (((B + menonWideIntervalTransitionEnvelope (4 * Y) H) +
            primePowerDefectIoc a Y) /
          Real.log ((a + 1 : ℕ) : ℝ)) /
            ((a + 1 : ℕ) : ℝ) <
        ‖harmonicPrimeBlockPoly (primesRange a Y) (-u / (2 * Real.pi))‖ :=
    lt_of_not_ge hnot
  have hcount := hsched j hj (T := T) (E := {u}) hT
    (by simpa only [a, cells] using hcellsT)
    (by
      intro v hv z hz hvz
      simp only [Finset.mem_singleton] at hv hz
      exact absurd (hv.trans hz.symm) hvz)
    (by
      intro v hv
      simp only [Finset.mem_singleton] at hv
      subst v
      exact ⟨by simpa only [a, cells] using hbandLo,
        by simpa only [a, cells] using hbandHi⟩)
    (by simpa only [a] using h2T)
    (by
      intro v hv
      simp only [Finset.mem_singleton] at hv
      subst v
      simpa only [a, Y, H, B] using hlarge)
  have hcount0 := hcount
  dsimp only at hcount0
  have hfactor := menonHarmonicCaseII_VexpFactor_lower ha256 hlog
    (by simpa only [a, Y] using haY) (by simpa only [a, Y] using hYa)
  let M : ℝ := min T (((a : ℝ) ^ (1 / 8 : ℝ)) ^ maynardDerivativeDeficit 26)
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hM0 : 0 ≤ M := by
    dsimp only [M]
    exact le_min hT0 (by positivity)
  have hvLower :
      M / (menonHarmonicCaseIICoreDenominatorConstant *
          (Real.log (a : ℝ)) ^ (307 : ℕ)) ≤
        M / (5120 * maynardLongPolylogEnvelope (4 * Y)) *
          ((2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)) /
            (((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 *
                (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ) * 8)) := by
    have hm := mul_le_mul_of_nonneg_left hfactor hM0
    simpa only [Y, div_eq_mul_inv, one_mul, mul_assoc] using hm
  have hden0 : 0 < menonHarmonicCaseIICoreDenominatorConstant *
      (Real.log (a : ℝ)) ^ (307 : ℕ) := by
    rw [menonHarmonicCaseIICoreDenominatorConstant]
    positivity
  have hvLower0 : 0 ≤
      M / (menonHarmonicCaseIICoreDenominatorConstant *
          (Real.log (a : ℝ)) ^ (307 : ℕ)) := div_nonneg hM0 hden0.le
  have hsqLower :
      (M / (menonHarmonicCaseIICoreDenominatorConstant *
          (Real.log (a : ℝ)) ^ (307 : ℕ))) ^ 2 ≤
        (M / (5120 * maynardLongPolylogEnvelope (4 * Y)) *
          ((2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)) /
            (((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 *
                (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ) * 8))) ^ 2 :=
    pow_le_pow_left₀ hvLower0 hvLower 2
  have hcountAmp :
      (M / (5120 * maynardLongPolylogEnvelope (4 * Y)) *
          ((2 * (Real.log (a : ℝ)) ^ (-300 : ℝ)) /
            (((3 * (Nat.log 2 (4 * Y) + 1) ^ 3 *
                (Nat.log 2 a + 1) ^ 3 : ℕ) : ℝ) * 8))) ^ 2 ≤
      (((cells : ℝ) * (D : ℝ) * 12) *
        ((12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
              (1 + Real.log
                (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma)))) := by
    simpa only [Finset.card_singleton, Nat.cast_one, one_mul, Nat.cast_mul,
      Nat.cast_ofNat, a, Y, cells, H, sigma, B, Q, D, M] using hcount0
  have hcount' :
      (M / (menonHarmonicCaseIICoreDenominatorConstant *
          (Real.log (a : ℝ)) ^ (307 : ℕ))) ^ 2 ≤
      (((cells : ℝ) * (D : ℝ) * 12) *
        ((12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
              (1 + Real.log
                (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma)))) :=
    hsqLower.trans hcountAmp
  have hstrict := menonHarmonicCaseII_countNumerator_lt_scaledAmplitude ha256 hlog
    (by simpa only [a, Y] using haY) (by simpa only [a, Y] using hYa) hT
    (M := M) (by simpa only [a, M] using hcross)
  have hstrict' :
      (((cells : ℝ) * (D : ℝ) * 12) *
        ((12 * menonHeathBrownCaseIIComplementWidthConstant ^ 2 *
              (1 + Real.log
                (menonHeathBrownCaseIIComplementWidthConstant * (4 * Y : ℕ))) ^
                (menonHeathBrownCaseIIComplementPolylogExponent + 2)) *
            (T + 1) * (((a : ℝ) / 64) ^ (2 - 2 * sigma)))) <
        (M / (menonHarmonicCaseIICoreDenominatorConstant *
          (Real.log (a : ℝ)) ^ (307 : ℕ))) ^ 2 := by
    simpa only [a, Y, cells, D, sigma] using hstrict
  exact (not_lt_of_ge hcount') hstrict'

end

end RHTower.Sieve
