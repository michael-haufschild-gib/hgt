import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicPrimePowerMeasure
import GaloisForLFunctions.RHTower.Sieve.KubalalikaFibreCondition
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicCaseIIMeasure

/-!
# Direct adapted-moment bound for Menon's harmonic Case II

Menon's literal Case-II prime interval is narrow: `X < (L+1)³` and `L ≤ a^(1/3)` imply
`X-a ≤ 7a^(2/3)`.  The actual harmonic prime polynomial on `(a,X]` is prime-supported and has
coefficient energy at most `(X-a)/a²`.  Its eighth moment therefore bounds the already-defined
literal exceptional-frequency set directly.  This bypasses reverse Abel selection and every
sharp-interval smoothing loss while preserving the exact exceptional set and threshold.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- Menon's source constraints force the literal selected prime interval to have width
`O(a^(2/3))`. -/
theorem natSub_cast_le_seven_rpow_twoThird
    {a L X : ℕ} (ha : 1 ≤ a) (haX : a < X) (hXL : X < (L + 1) ^ 3)
    (hL : (L : ℝ) ≤ (a : ℝ) ^ (1 / 3 : ℝ)) :
    ((X - a : ℕ) : ℝ) ≤ 7 * (a : ℝ) ^ (2 / 3 : ℝ) := by
  let r : ℝ := (a : ℝ) ^ (1 / 3 : ℝ)
  have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  have hr0 : 0 < r := by dsimp only [r]; positivity
  have hr1 : 1 ≤ r := by
    dsimp only [r]
    exact Real.one_le_rpow (by exact_mod_cast ha) (by norm_num)
  have hr3 : r ^ 3 = (a : ℝ) := rpow_third_cube ha0
  have hr2 : r ^ 2 = (a : ℝ) ^ (2 / 3 : ℝ) := by
    dsimp only [r]
    rw [← Real.rpow_natCast ((a : ℝ) ^ (1 / 3 : ℝ)) 2,
      ← Real.rpow_mul ha0.le]
    norm_num
  have hL0 : (0 : ℝ) ≤ L := by positivity
  have hL2 : (L : ℝ) ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ hL0 (by simpa only [r] using hL) 2
  have hL3 : (L : ℝ) ^ 3 ≤ r ^ 3 :=
    pow_le_pow_left₀ hL0 (by simpa only [r] using hL) 3
  have hLr2 : (L : ℝ) ≤ r ^ 2 := by
    calc
      (L : ℝ) ≤ r := by simpa only [r] using hL
      _ ≤ r ^ 2 := by nlinarith
  have hone : (1 : ℝ) ≤ r ^ 2 := by nlinarith
  have hXreal : (X : ℝ) < ((L : ℝ) + 1) ^ 3 := by exact_mod_cast hXL
  have hsub : ((X - a : ℕ) : ℝ) = (X : ℝ) - (a : ℝ) := by
    rw [Nat.cast_sub (Nat.le_of_lt haX)]
  rw [hsub, ← hr2]
  rw [← hr3]
  nlinarith [hL2, hL3, hLr2, hone]

/-- Direct eighth-moment bound for the exact Case-II exceptional set.  Every parameter occurring
in the set is retained; no discretization or smoothing majorant is introduced. -/
theorem volume_menonHarmonicPrimeBlockExceptionalSet_direct_eighth_le
    {a X : ℕ} {B T V : ℝ}
    (ha : 0 < a) (hX : 1 ≤ X) (hB : 0 ≤ B) (hT : 0 ≤ T) (hV : 0 ≤ V) :
    let U : ℝ :=
      ((B + primePowerDefectIoc a X) / Real.log ((a + 1 : ℕ) : ℝ)) /
        ((a + 1 : ℕ) : ℝ)
    U ^ 8 * volume.real (menonHarmonicPrimeBlockExceptionalSet a X B T V) ≤
      2 * (((2 * T) + 4 * ((X ^ 4 : ℕ) : ℝ) *
              (1 + Real.log ((X ^ 4 : ℕ) : ℝ))) *
        (256 * (((X - a : ℕ) : ℝ) / (a : ℝ) ^ 2) ^ 4)) := by
  dsimp only
  let U : ℝ :=
    ((B + primePowerDefectIoc a X) / Real.log ((a + 1 : ℕ) : ℝ)) /
      ((a + 1 : ℕ) : ℝ)
  have ha1 : (1 : ℝ) < ((a + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.lt_add_one_iff.mpr ha)
  have hU : 0 ≤ U := by
    dsimp only [U]
    exact div_nonneg
      (div_nonneg (add_nonneg hB (primePowerDefectIoc_nonneg a X))
        (Real.log_pos ha1).le)
      (by positivity)
  let E : Set ℝ :=
    {x ∈ Set.Icc (-(2 * T)) (2 * T) |
      U ≤ ‖harmonicPrimeBlockPoly (primesRange a X) (-x / (2 * Real.pi))‖}
  have hsub : menonHarmonicPrimeBlockExceptionalSet a X B T V ⊆ E := by
    intro x hx
    rcases hx with ⟨hxband, hxlarge⟩
    refine ⟨⟨?_, ?_⟩, hxlarge.le⟩
    · linarith [hxband.1]
    · linarith [hxband.2]
  have hmeasure : volume.real (menonHarmonicPrimeBlockExceptionalSet a X B T V)
      ≤ volume.real E := by
    apply ENNReal.toReal_mono
    · have hEvol : volume E ≤ volume (Set.Icc (-(2 * T)) (2 * T)) :=
        measure_mono (by intro x hx; exact hx.1)
      exact ne_of_lt (hEvol.trans_lt (by simp))
    · exact measure_mono hsub
  have hbase := volume_harmonicPrimesRange_largeValues_eighth_le
    ha hX (show 0 ≤ 2 * T by positivity) hU
  change U ^ 8 * volume.real E ≤ _ at hbase
  exact (mul_le_mul_of_nonneg_left hmeasure (by positivity)).trans hbase

/-- Under Menon's literal narrow-block and height constraints, the entire eighth-moment right side
is bounded by a fixed constant times `a^(-1/3)`. -/
theorem menonHarmonicCaseIIDirectEighthRhs_le
    {a L X : ℕ} {T : ℝ}
    (ha : 1 ≤ a) (haX : a < X) (hXL : X < (L + 1) ^ 3)
    (hL : (L : ℝ) ≤ (a : ℝ) ^ (1 / 3 : ℝ))
    (hT : 0 ≤ T) (h2T : 2 * T ≤ (a : ℝ) ^ 3) :
    2 * (((2 * T) + 4 * ((X ^ 4 : ℕ) : ℝ) *
              (1 + Real.log ((X ^ 4 : ℕ) : ℝ))) *
        (256 * (((X - a : ℕ) : ℝ) / (a : ℝ) ^ 2) ^ 4)) ≤
      (2 * 540673 * 256 * 7 ^ 4 : ℝ) /
        ((a : ℝ) ^ (1 / 3 : ℝ)) := by
  let A : ℝ := (a : ℝ)
  let Y : ℝ := (X : ℝ)
  let d : ℝ := ((X - a : ℕ) : ℝ)
  let r : ℝ := A ^ (1 / 3 : ℝ)
  have hA0 : 0 < A := by dsimp only [A]; exact_mod_cast ha
  have hA1 : 1 ≤ A := by dsimp only [A]; exact_mod_cast ha
  have hY0 : 0 < Y := by
    dsimp only [Y]
    exact_mod_cast (lt_trans (Nat.zero_lt_of_lt ha) haX)
  have hr0 : 0 < r := by dsimp only [r]; positivity
  have hr1 : 1 ≤ r := by
    dsimp only [r, A]
    exact Real.one_le_rpow (by exact_mod_cast ha) (by norm_num)
  have hr3 : r ^ 3 = A := by
    dsimp only [r]
    exact rpow_third_cube hA0
  have hr2 : r ^ 2 = A ^ (2 / 3 : ℝ) := by
    dsimp only [r]
    rw [← Real.rpow_natCast (A ^ (1 / 3 : ℝ)) 2, ← Real.rpow_mul hA0.le]
    norm_num
  have hd : d ≤ 7 * r ^ 2 := by
    dsimp only [d]
    rw [hr2]
    exact natSub_cast_le_seven_rpow_twoThird ha haX hXL hL
  have hd0 : 0 ≤ d := by dsimp only [d]; positivity
  have hdA : d ≤ 7 * A := by
    rw [← hr3]
    nlinarith
  have hYeq : Y = A + d := by
    dsimp only [Y, A, d]
    rw [Nat.cast_sub (Nat.le_of_lt haX)]
    ring
  have hY8 : Y ≤ 8 * A := by nlinarith
  have hY4 : Y ^ 4 ≤ 4096 * A ^ 4 := by
    have hp := pow_le_pow_left₀ (le_of_lt hY0) hY8 4
    nlinarith
  have hcast4 : (((X ^ 4 : ℕ) : ℝ)) = Y ^ 4 := by simp [Y]
  have hlogY : Real.log Y ≤ Y - 1 := Real.log_le_sub_one_of_pos hY0
  have hlog4 : Real.log (((X ^ 4 : ℕ) : ℝ)) ≤ 32 * A := by
    rw [hcast4, Real.log_pow]
    norm_num
    nlinarith [hlogY, hY8]
  have hlog4nonneg : 0 ≤ Real.log (((X ^ 4 : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    have hXne : X ≠ 0 := by omega
    have hXpow : 1 ≤ X ^ 4 := Nat.one_le_iff_ne_zero.mpr (pow_ne_zero 4 hXne)
    exact_mod_cast hXpow
  have hfac : 0 ≤ 1 + Real.log (((X ^ 4 : ℕ) : ℝ)) := by linarith
  have hfacUpper : 1 + Real.log (((X ^ 4 : ℕ) : ℝ)) ≤ 33 * A := by
    nlinarith
  have hprod :
      ((X ^ 4 : ℕ) : ℝ) * (1 + Real.log (((X ^ 4 : ℕ) : ℝ))) ≤
        4096 * A ^ 4 * (33 * A) := by
    rw [hcast4] at hfac hfacUpper ⊢
    exact mul_le_mul hY4 hfacUpper hfac (by positivity)
  have hA35 : A ^ 3 ≤ A ^ 5 := by
    calc
      A ^ 3 = A ^ 3 * 1 := by ring
      _ ≤ A ^ 3 * A ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith [sq_nonneg A]) (by positivity)
      _ = A ^ 5 := by ring
  have h2TA : 2 * T ≤ A ^ 3 := by simpa only [A] using h2T
  have hmean :
      2 * T + 4 * ((X ^ 4 : ℕ) : ℝ) *
          (1 + Real.log (((X ^ 4 : ℕ) : ℝ))) ≤ 540673 * A ^ 5 := by
    nlinarith [hprod, hA35, h2TA]
  have hfrac : d / A ^ 2 ≤ 7 / r ^ 4 := by
    calc
      d / A ^ 2 ≤ (7 * r ^ 2) / A ^ 2 :=
        div_le_div_of_nonneg_right hd (sq_nonneg A)
      _ = 7 / r ^ 4 := by
        rw [← hr3]
        field_simp [ne_of_gt hr0]
  have hfrac0 : 0 ≤ d / A ^ 2 := div_nonneg hd0 (sq_nonneg A)
  have hfracPow : (d / A ^ 2) ^ 4 ≤ (7 / r ^ 4) ^ 4 :=
    pow_le_pow_left₀ hfrac0 hfrac 4
  have henergy0 : 0 ≤ 256 * (d / A ^ 2) ^ 4 := by positivity
  have henergy : 256 * (d / A ^ 2) ^ 4 ≤ 256 * (7 / r ^ 4) ^ 4 :=
    mul_le_mul_of_nonneg_left hfracPow (by norm_num)
  have hmean0 : 0 ≤ 2 * T + 4 * ((X ^ 4 : ℕ) : ℝ) *
      (1 + Real.log (((X ^ 4 : ℕ) : ℝ))) := by positivity
  change
    2 * ((2 * T + 4 * ((X ^ 4 : ℕ) : ℝ) *
          (1 + Real.log (((X ^ 4 : ℕ) : ℝ)))) *
        (256 * (d / A ^ 2) ^ 4)) ≤
      (2 * 540673 * 256 * 7 ^ 4 : ℝ) / r
  calc
    2 * ((2 * T + 4 * ((X ^ 4 : ℕ) : ℝ) *
          (1 + Real.log (((X ^ 4 : ℕ) : ℝ)))) *
        (256 * (d / A ^ 2) ^ 4))
      ≤ 2 * (540673 * A ^ 5) * (256 * (7 / r ^ 4) ^ 4) := by
        have hmul := mul_le_mul hmean henergy henergy0
          (by positivity : 0 ≤ 540673 * A ^ 5)
        nlinarith
    _ = (2 * 540673 * 256 * 7 ^ 4 : ℝ) / r := by
      rw [← hr3]
      field_simp [ne_of_gt hr0]
    _ = (2 * 540673 * 256 * 7 ^ 4 : ℝ) /
        ((a : ℝ) ^ (1 / 3 : ℝ)) := by rfl

/-- At the canonical `(log a)^(-8)` Case-II threshold, the exact exceptional set has the
power-saving measure bound `O((log a)^64 / a^(1/3))`. -/
theorem volume_menonHarmonicPrimeBlockExceptionalSet_direct_logPow_le
    {a L X : ℕ} {B T V : ℝ}
    (ha : 3 ≤ a) (haX : a < X) (hXL : X < (L + 1) ^ 3)
    (hL : (L : ℝ) ≤ (a : ℝ) ^ (1 / 3 : ℝ))
    (hB : 0 ≤ B) (hT : 0 ≤ T) (hV : 0 ≤ V)
    (h2T : 2 * T ≤ (a : ℝ) ^ 3)
    (hUlower :
      (Real.log (a : ℝ)) ^ (-8 : ℝ) <
        ((B + primePowerDefectIoc a X) /
            Real.log ((a + 1 : ℕ) : ℝ)) /
          ((a + 1 : ℕ) : ℝ)) :
    volume.real (menonHarmonicPrimeBlockExceptionalSet a X B T V) ≤
      (2 * 540673 * 256 * 7 ^ 4 : ℝ) * (Real.log (a : ℝ)) ^ 64 /
        ((a : ℝ) ^ (1 / 3 : ℝ)) := by
  let U : ℝ :=
    ((B + primePowerDefectIoc a X) / Real.log ((a + 1 : ℕ) : ℝ)) /
      ((a + 1 : ℕ) : ℝ)
  let C : ℝ := 2 * 540673 * 256 * 7 ^ 4
  let l : ℝ := Real.log (a : ℝ)
  let r : ℝ := (a : ℝ) ^ (1 / 3 : ℝ)
  have ha1 : 1 ≤ a := by omega
  have ha0 : 0 < a := by omega
  have hX1 : 1 ≤ X := by omega
  have hl : 0 < l := by
    dsimp only [l]
    exact Real.log_pos (by exact_mod_cast (show 1 < a by omega))
  have hr : 0 < r := by dsimp only [r]; positivity
  have hthreshold : 0 ≤ l ^ (-8 : ℝ) := Real.rpow_nonneg hl.le _
  have hUlower' : l ^ (-8 : ℝ) < U := by simpa only [l, U] using hUlower
  have hU8 : (l ^ (-8 : ℝ)) ^ 8 < U ^ 8 :=
    pow_lt_pow_left₀ hUlower' hthreshold (by norm_num)
  have hpowid : (l ^ (-8 : ℝ)) ^ 8 = 1 / l ^ 64 := by
    rw [Real.rpow_neg hl.le]
    field_simp [ne_of_gt hl]
    simpa using (pow_mul l 8 8)
  have hdirect := volume_menonHarmonicPrimeBlockExceptionalSet_direct_eighth_le
    ha0 hX1 hB hT hV
  dsimp only at hdirect
  have hrhs := menonHarmonicCaseIIDirectEighthRhs_le ha1 haX hXL hL hT h2T
  have hbound : U ^ 8 *
      volume.real (menonHarmonicPrimeBlockExceptionalSet a X B T V) ≤ C / r := by
    simpa only [U, C, r] using hdirect.trans hrhs
  have hvol : 0 ≤ volume.real (menonHarmonicPrimeBlockExceptionalSet a X B T V) :=
    ENNReal.toReal_nonneg
  have hscaled : (1 / l ^ 64) *
      volume.real (menonHarmonicPrimeBlockExceptionalSet a X B T V) ≤ C / r := by
    calc
      (1 / l ^ 64) * volume.real (menonHarmonicPrimeBlockExceptionalSet a X B T V) =
          (l ^ (-8 : ℝ)) ^ 8 *
            volume.real (menonHarmonicPrimeBlockExceptionalSet a X B T V) := by
              rw [hpowid]
      _ ≤ U ^ 8 * volume.real (menonHarmonicPrimeBlockExceptionalSet a X B T V) :=
        mul_le_mul_of_nonneg_right hU8.le hvol
      _ ≤ C / r := hbound
  rw [one_div_mul_eq_div] at hscaled
  have hfinal := (div_le_iff₀ (pow_pos hl 64)).mp hscaled
  change volume.real (menonHarmonicPrimeBlockExceptionalSet a X B T V) ≤ C * l ^ 64 / r
  calc
    volume.real (menonHarmonicPrimeBlockExceptionalSet a X B T V)
        ≤ C / r * l ^ 64 := hfinal
    _ = C * l ^ 64 / r := by ring

/-- The explicit direct Case-II majorant tends to zero. -/
theorem tendsto_menonHarmonicCaseIIDirectMajorant_zero :
    Filter.Tendsto
      (fun x : ℝ =>
        (2 * 540673 * 256 * 7 ^ 4 : ℝ) * (Real.log x) ^ 64 /
          x ^ (1 / 3 : ℝ))
      Filter.atTop (nhds 0) := by
  have h := Real.tendsto_pow_log_div_pow_atTop (1 / 3 : ℝ) 64 (by norm_num)
  have h' : Filter.Tendsto
      (fun x : ℝ => (Real.log x) ^ 64 / x ^ (1 / 3 : ℝ))
      Filter.atTop (nhds 0) := by
    convert h using 1
    funext x
    rw [show (64 : ℝ) = ((64 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  simpa only [mul_div_assoc, mul_zero] using
    h'.const_mul (2 * 540673 * 256 * 7 ^ 4 : ℝ)

end

end RHTower.Sieve
