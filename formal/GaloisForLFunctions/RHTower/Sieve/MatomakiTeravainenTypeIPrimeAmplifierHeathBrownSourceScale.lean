import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierHeathBrownSchedule
import GaloisForLFunctions.RHTower.Sieve.PolylogRpowDomination

/-!
# Source-scale routing for the Heath--Brown Type-I prime amplifier

The paper varies the prime exponent in a compact interval around `1.1`.  Uniformly on the larger
interval `[1, 2]`, upward rounding of `(log X)^a` remains below `X^(1/10)`.  The source frequency
range `X^(1/4) ≤ T` therefore implies the exact support-routing condition `P ≤ T^(2/5)`.
-/

namespace RHTower.Sieve

open Filter Topology

noncomputable section

/-- The paper's rounded prime scale is uniformly below every fixed positive power over its
exponent interval. -/
theorem eventually_mtTypeIPrimeScale_le_rpow
    {beta : ℝ} (hbeta : 0 < beta) :
    ∀ᶠ X : ℝ in atTop, ∀ a : ℝ, 1 ≤ a → a ≤ 2 →
      (mtTypeIPrimeScale X a : ℝ) ≤ X ^ beta := by
  have hdom := eventually_const_mul_rpow_polylog_le_rpow
    (C := (2 : ℝ)) (α := (0 : ℝ)) (β := beta) 2 hbeta
  filter_upwards [hdom, Filter.eventually_ge_atTop (Real.exp 1)] with X hdomX hX
  intro a ha1 ha2
  have hXone : (1 : ℝ) ≤ X := by
    exact (by norm_num : (1 : ℝ) ≤ Real.exp 1).trans hX
  have hlog : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1)
      (zero_lt_one.trans_le hXone) hX
  have hpow0 : 0 ≤ (Real.log X) ^ a := Real.rpow_nonneg (by positivity) _
  have hpowLe : (Real.log X) ^ a ≤ (Real.log X) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hlog ha2
  have hpowTwo : (Real.log X) ^ (2 : ℝ) = (Real.log X) ^ 2 := by
    rw [Real.rpow_two]
  have honeLe : 1 ≤ (Real.log X) ^ 2 := one_le_pow₀ hlog
  have hceil : (mtTypeIPrimeScale X a : ℝ) < (Real.log X) ^ a + 1 := by
    simpa only [mtTypeIPrimeScale] using Nat.ceil_lt_add_one hpow0
  have hscale : (mtTypeIPrimeScale X a : ℝ) ≤ 2 * (Real.log X) ^ 2 := by
    rw [hpowTwo] at hpowLe
    linarith
  have hlog0 : 0 ≤ Real.log X := zero_le_one.trans hlog
  have habs : |Real.log X| = Real.log X := abs_of_nonneg hlog0
  have hpoly : 2 * (Real.log X) ^ 2 ≤ X ^ beta := by
    calc
      2 * (Real.log X) ^ 2 ≤ 2 * (1 + Real.log X) ^ 2 := by nlinarith
      _ ≤ X ^ beta := by simpa [Real.rpow_zero, habs] using hdomX
  exact hscale.trans hpoly

/-- Tenth-power specialization used by the complete-support schedule. -/
theorem eventually_mtTypeIPrimeScale_le_rpow_tenth :
    ∀ᶠ X : ℝ in atTop, ∀ a : ℝ, 1 ≤ a → a ≤ 2 →
      (mtTypeIPrimeScale X a : ℝ) ≤ X ^ (1 / 10 : ℝ) := by
  simpa only using
    (eventually_mtTypeIPrimeScale_le_rpow (beta := (1 / 10 : ℝ)) (by norm_num))

/-- In the paper height range, the rounded prime scale satisfies the support-routing power. -/
theorem eventually_mtTypeIPrimeScale_le_height_two_fifths :
    ∀ᶠ X : ℝ in atTop, ∀ a T : ℝ, 1 ≤ a → a ≤ 2 →
      X ^ (1 / 4 : ℝ) ≤ T →
      (mtTypeIPrimeScale X a : ℝ) ≤ T ^ (2 / 5 : ℝ) := by
  filter_upwards [eventually_mtTypeIPrimeScale_le_rpow_tenth,
    Filter.eventually_ge_atTop (1 : ℝ)] with X hscale hX
  intro a T ha1 ha2 hXT
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hbase : 0 ≤ X ^ (1 / 4 : ℝ) := Real.rpow_nonneg hX0 _
  have hpow := Real.rpow_le_rpow hbase hXT (by norm_num : (0 : ℝ) ≤ 2 / 5)
  have hid : (X ^ (1 / 4 : ℝ)) ^ (2 / 5 : ℝ) = X ^ (1 / 10 : ℝ) := by
    rw [← Real.rpow_mul hX0]
    norm_num
  rw [hid] at hpow
  exact (hscale a ha1 ha2).trans hpow

/-- The rounded prime scale is eventually at least two, uniformly above exponent one. -/
theorem eventually_mtTypeIPrimeScale_two_le :
    ∀ᶠ X : ℝ in atTop, ∀ a : ℝ, 1 ≤ a → 2 ≤ mtTypeIPrimeScale X a := by
  have hlog := Real.tendsto_log_atTop.eventually_ge_atTop (Real.exp 2)
  have hXlarge : ∀ᶠ X : ℝ in atTop, Real.exp 2 ≤ X :=
    Filter.eventually_ge_atTop _
  filter_upwards [hlog, hXlarge] with X hlogX hX
  intro a ha
  have hlogOne : (1 : ℝ) ≤ Real.log X :=
    (by norm_num : (1 : ℝ) ≤ Real.exp 2).trans hlogX
  have hscaleReal : Real.exp 2 ≤ (Real.log X) ^ a := by
    calc
      Real.exp 2 ≤ Real.log X := hlogX
      _ = (Real.log X) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Real.log X) ^ a := Real.rpow_le_rpow_of_exponent_le hlogOne ha
  exact mtTypeIPrimeScale_two_le hscaleReal

/-- A stronger source-height scale used to retain the sparse-moment power saving. -/
theorem eventually_mtTypeIPrimeScale_le_height_one_twenty_fifth :
    ∀ᶠ X : ℝ in atTop, ∀ a T : ℝ, 1 ≤ a → a ≤ 2 →
      X ^ (1 / 4 : ℝ) ≤ T →
      (mtTypeIPrimeScale X a : ℝ) ≤ T ^ (1 / 25 : ℝ) := by
  filter_upwards
    [eventually_mtTypeIPrimeScale_le_rpow (beta := (1 / 100 : ℝ)) (by norm_num),
      Filter.eventually_ge_atTop (1 : ℝ)] with X hscale hX
  intro a T ha1 ha2 hXT
  have hX0 : 0 ≤ X := zero_le_one.trans hX
  have hbase : 0 ≤ X ^ (1 / 4 : ℝ) := Real.rpow_nonneg hX0 _
  have hpow := Real.rpow_le_rpow hbase hXT (by norm_num : (0 : ℝ) ≤ 1 / 25)
  have hid : (X ^ (1 / 4 : ℝ)) ^ (1 / 25 : ℝ) = X ^ (1 / 100 : ℝ) := by
    rw [← Real.rpow_mul hX0]
    norm_num
  rw [hid] at hpow
  exact (hscale a ha1 ha2).trans hpow

/-- The lower powered-prime scale is at most `T^(7/50)` on the strengthened source schedule. -/
theorem mtTypeIPrimeDegree_base_pow_le_height_seven_fiftieth
    {P : ℕ} {T : ℝ} (hP : 2 ≤ P) (hT : 1 ≤ T)
    (hPT : (P : ℝ) ≤ T ^ (1 / 25 : ℝ)) :
    (((P ^ mtTypeIPrimeDegree P T : ℕ) : ℝ)) ≤ T ^ (7 / 50 : ℝ) := by
  have hwindow := (mtTypeIPrimeDegree_power_window hP hT).2
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  calc
    (((P ^ mtTypeIPrimeDegree P T : ℕ) : ℝ)) ≤
        (P : ℝ) * T ^ (1 / 10 : ℝ) := hwindow
    _ ≤ T ^ (1 / 25 : ℝ) * T ^ (1 / 10 : ℝ) := by gcongr
    _ = T ^ (7 / 50 : ℝ) := by
      rw [← Real.rpow_add hTpos]
      norm_num

/-- The complete powered-prime support is at most `T^(7/25)`, retaining a fixed saving below
height rather than merely fitting below height. -/
theorem mtTypeIPrimeDegree_fullSupport_le_height_seven_twenty_fifths
    {P : ℕ} {T : ℝ} (hP : 2 ≤ P) (hT : 1 ≤ T)
    (hPT : (P : ℝ) ≤ T ^ (1 / 25 : ℝ)) :
    (((((2 * P) ^ mtTypeIPrimeDegree P T : ℕ) : ℝ))) ≤ T ^ (7 / 25 : ℝ) := by
  let ell := mtTypeIPrimeDegree P T
  have htwoP : 2 ^ ell ≤ P ^ ell := Nat.pow_le_pow_left hP ell
  have hbase := mtTypeIPrimeDegree_base_pow_le_height_seven_fiftieth hP hT hPT
  calc
    (((((2 * P) ^ ell : ℕ) : ℝ))) =
        (((2 ^ ell : ℕ) : ℝ)) * (((P ^ ell : ℕ) : ℝ)) := by
          norm_cast
          exact mul_pow 2 P ell
    _ ≤ (((P ^ ell : ℕ) : ℝ)) * (((P ^ ell : ℕ) : ℝ)) := by
      gcongr
    _ ≤ T ^ (7 / 50 : ℝ) * T ^ (7 / 50 : ℝ) := by gcongr
    _ = T ^ (7 / 25 : ℝ) := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hT)]
      norm_num

/-- Every literal Watt block inherits the same fixed sub-height support power. -/
theorem mtTypeIPrimeHeathBrownBlockLength_le_height_seven_twenty_fifths
    {P : ℕ} {T : ℝ} (hP : 2 ≤ P) (hT : 1 ≤ T)
    (hPT : (P : ℝ) ≤ T ^ (1 / 25 : ℝ))
    (r : Fin (mtTypeIPrimeDegree P T)) :
    (mtTypeIPrimeHeathBrownBlockLength P (mtTypeIPrimeDegree P T) r : ℝ) ≤
      T ^ (7 / 25 : ℝ) := by
  let ell := mtTypeIPrimeDegree P T
  have hr : (r : ℕ) ≤ ell := Nat.le_of_lt r.isLt
  have htwo : 2 ^ (r : ℕ) ≤ 2 ^ ell := Nat.pow_le_pow_right (by norm_num) hr
  have hblock : mtTypeIPrimeHeathBrownBlockLength P ell r ≤ (2 * P) ^ ell := by
    rw [mtTypeIPrimeHeathBrownBlockLength, mul_pow]
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left (P ^ ell) htwo
  have hblockR :
      (mtTypeIPrimeHeathBrownBlockLength P ell r : ℝ) ≤ (((2 * P) ^ ell : ℕ) : ℝ) := by
    exact_mod_cast hblock
  exact hblockR.trans
    (mtTypeIPrimeDegree_fullSupport_le_height_seven_twenty_fifths hP hT hPT)

/-- Uniform source-scale form of the fixed sub-height block reserve. -/
theorem eventually_mtTypeIPrimeHeathBrownBlockLength_le_height_seven_twenty_fifths :
    ∀ᶠ X : ℝ in atTop, ∀ (a T : ℝ), 1 ≤ a → a ≤ 2 →
      X ^ (1 / 4 : ℝ) ≤ T →
      ∀ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X a) T),
        (mtTypeIPrimeHeathBrownBlockLength
          (mtTypeIPrimeScale X a)
          (mtTypeIPrimeDegree (mtTypeIPrimeScale X a) T) r : ℝ) ≤
            T ^ (7 / 25 : ℝ) := by
  have hquarter :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop 1
  filter_upwards [eventually_mtTypeIPrimeScale_two_le,
    eventually_mtTypeIPrimeScale_le_height_one_twenty_fifth,
    hquarter] with X hP hPT hquarterX
  intro a T ha1 ha2 hXT r
  exact mtTypeIPrimeHeathBrownBlockLength_le_height_seven_twenty_fifths
    (hP a ha1) (hquarterX.trans hXT) (hPT a T ha1 ha2 hXT) r

/-- A block below `T^(7/25)` contributes at most `T^(24/25)` to the sparse fourth-moment
term `B^(3/4) T^(3/4)`. -/
theorem rpow_three_fourths_mul_height_three_fourths_le_height_twenty_four_twenty_fifths
    {B T : ℝ} (hB : 0 ≤ B) (hT : 1 ≤ T) (hBT : B ≤ T ^ (7 / 25 : ℝ)) :
    B ^ (3 / 4 : ℝ) * T ^ (3 / 4 : ℝ) ≤ T ^ (24 / 25 : ℝ) := by
  have hT0 : 0 ≤ T := zero_le_one.trans hT
  have hBpow : B ^ (3 / 4 : ℝ) ≤ T ^ (21 / 100 : ℝ) := by
    calc
      B ^ (3 / 4 : ℝ) ≤ (T ^ (7 / 25 : ℝ)) ^ (3 / 4 : ℝ) :=
        Real.rpow_le_rpow hB hBT (by norm_num)
      _ = T ^ (21 / 100 : ℝ) := by
        rw [← Real.rpow_mul hT0]
        norm_num
  calc
    B ^ (3 / 4 : ℝ) * T ^ (3 / 4 : ℝ) ≤
        T ^ (21 / 100 : ℝ) * T ^ (3 / 4 : ℝ) := by gcongr
    _ = T ^ (24 / 25 : ℝ) := by
      rw [← Real.rpow_add (zero_lt_one.trans_le hT)]
      norm_num

/-- Literal sparse fourth-moment term for every Heath--Brown block retains the fixed
`T^(-1/25)` saving. -/
theorem mtTypeIPrimeHeathBrownSparseTerm_le_height_twenty_four_twenty_fifths
    {P : ℕ} {T : ℝ} (hP : 2 ≤ P) (hT : 1 ≤ T)
    (hPT : (P : ℝ) ≤ T ^ (1 / 25 : ℝ))
    (r : Fin (mtTypeIPrimeDegree P T)) :
    (mtTypeIPrimeHeathBrownBlockLength P (mtTypeIPrimeDegree P T) r : ℝ) ^
          (3 / 4 : ℝ) *
        T ^ (3 / 4 : ℝ) ≤ T ^ (24 / 25 : ℝ) :=
  rpow_three_fourths_mul_height_three_fourths_le_height_twenty_four_twenty_fifths
    (by positivity) hT
    (mtTypeIPrimeHeathBrownBlockLength_le_height_seven_twenty_fifths hP hT hPT r)

/-- Uniform source-scale form of the sparse fourth-moment saving. -/
theorem eventually_mtTypeIPrimeHeathBrownSparseTerm_le_height_twenty_four_twenty_fifths :
    ∀ᶠ X : ℝ in atTop, ∀ (a T : ℝ), 1 ≤ a → a ≤ 2 →
      X ^ (1 / 4 : ℝ) ≤ T →
      ∀ r : Fin (mtTypeIPrimeDegree (mtTypeIPrimeScale X a) T),
        (mtTypeIPrimeHeathBrownBlockLength
            (mtTypeIPrimeScale X a)
            (mtTypeIPrimeDegree (mtTypeIPrimeScale X a) T) r : ℝ) ^
              (3 / 4 : ℝ) *
          T ^ (3 / 4 : ℝ) ≤ T ^ (24 / 25 : ℝ) := by
  have hquarter :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop 1
  filter_upwards [eventually_mtTypeIPrimeScale_two_le,
    eventually_mtTypeIPrimeScale_le_height_one_twenty_fifth,
    hquarter] with X hP hPT hquarterX
  intro a T ha1 ha2 hXT r
  exact mtTypeIPrimeHeathBrownSparseTerm_le_height_twenty_four_twenty_fifths
    (hP a ha1) (hquarterX.trans hXT) (hPT a T ha1 ha2 hXT) r

end

end RHTower.Sieve
