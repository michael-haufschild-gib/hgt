import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierHeathBrownLayerSourceHeight
import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenPrimeAmplifierHeathBrownSqrtBTMoment
import GaloisForLFunctions.RHTower.MobiusSparseForbiddenDeletion

/-!
# Prime-density saving in the powered Type-I threshold layers

The diagonal layer mass is the number of ordered prime tuples, not the ambient interval length.
Brun--Titchmarsh makes the unraised prime alphabet at most half the ambient length once its
logarithm is large, yielding the exact density factor `2^{-ell}` after raising.
-/

namespace RHTower.Sieve

noncomputable section

/-- At a fixed explicit logarithmic threshold, the prime-amplifier alphabet occupies at most half
of its ambient interval length. -/
theorem card_mtTypeIPrimeCoeffSupport_le_half
    {P : ℕ} (hP : 4 ≤ P) (hlogP : 1168 ≤ Real.log (P : ℝ)) :
    ((mtTypeIPrimeCoeffSupport P).card : ℝ) ≤ (P : ℝ) / 2 := by
  have hPtwo : 2 ≤ P := by omega
  have hPR : (1 : ℝ) < P := by exact_mod_cast hPtwo
  have hsqrt : (1 : ℝ) < Real.sqrt (P : ℝ) := by
    rw [← Real.sqrt_one]
    exact Real.sqrt_lt_sqrt (by norm_num) hPR
  have hbt := card_mtTypeIPrimeCoeffSupport_le_bt P hsqrt
  have hbase := mtTypeIPrimeSqrtBTBase_le P 0 hPtwo
  norm_num only [Nat.cast_zero, add_zero] at hbase
  have hlogPos : 0 < Real.log (P : ℝ) := by linarith
  have hmain : 292 * (P : ℝ) / Real.log P ≤ (P : ℝ) / 4 := by
    rw [div_le_iff₀ hlogPos]
    have hP0 : (0 : ℝ) ≤ P := by positivity
    nlinarith
  have hone : (1 : ℝ) ≤ (P : ℝ) / 4 := by
    have hP4 : (4 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
    linarith
  calc
    ((mtTypeIPrimeCoeffSupport P).card : ℝ) ≤
        2 * (P : ℝ) / Real.log (Real.sqrt P) +
          6 * Real.sqrt P * (1 + Real.log (Real.sqrt P)) ^ 3 + 1 := hbt
    _ ≤ 292 * (P : ℝ) / Real.log P + 1 := hbase
    _ ≤ (P : ℝ) / 2 := by linarith

/-- The exact raised prime-tuple density is at most `2^{-ell}`. -/
theorem mtTypeIPrimeRaisedPrimeDensity_le_halfPow
    {P ell : ℕ} (hP : 4 ≤ P) (hlogP : 1168 ≤ Real.log (P : ℝ)) :
    (((mtTypeIPrimeCoeffSupport P).card ^ ell : ℕ) : ℝ) /
        (((P ^ ell : ℕ) : ℝ)) ≤
      (1 / 2 : ℝ) ^ ell := by
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (by omega : 1 ≤ P))
  have hcard := card_mtTypeIPrimeCoeffSupport_le_half hP hlogP
  have hratio :
      ((mtTypeIPrimeCoeffSupport P).card : ℝ) / (P : ℝ) ≤ (1 / 2 : ℝ) := by
    rw [div_le_iff₀ hP0]
    linarith
  have hratio0 : 0 ≤ ((mtTypeIPrimeCoeffSupport P).card : ℝ) / (P : ℝ) := by
    positivity
  push_cast
  rw [← div_pow]
  exact pow_le_pow_left₀ hratio0 hratio ell

/-- The ceiling degree is large enough to transfer the half-base to the literal logarithmic
degree. -/
theorem halfPow_mtTypeIPrimeDegree_le_logb
    {P : ℕ} {T : ℝ} (hP : 2 ≤ P) (hT : 1 ≤ T) :
    (1 / 2 : ℝ) ^ mtTypeIPrimeDegree P T ≤
      (1 / 2 : ℝ) ^ (Real.log T / (10 * Real.log (P : ℝ))) := by
  let q : ℝ := Real.logb (P : ℝ) (T ^ (1 / 10 : ℝ))
  have hceil : q ≤ (mtTypeIPrimeDegree P T : ℝ) := by
    simpa only [mtTypeIPrimeDegree, q] using (Nat.le_ceil q)
  have hhalfPos : (0 : ℝ) < 1 / 2 := by norm_num
  have hhalfOne : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hanti := Real.rpow_le_rpow_of_exponent_ge hhalfPos hhalfOne hceil
  have hTpos : (0 : ℝ) < T := zero_lt_one.trans_le hT
  have hlogP : 0 < Real.log (P : ℝ) :=
    Real.log_pos (by exact_mod_cast hP : (1 : ℝ) < P)
  have hq : q = Real.log T / (10 * Real.log (P : ℝ)) := by
    dsimp only [q]
    rw [Real.logb, Real.log_rpow hTpos]
    field_simp
  rw [hq] at hanti
  simpa only [Real.rpow_natCast] using hanti

/-- Uniform logarithmic upper bound for the rounded source prime scale. -/
theorem log_mtTypeIPrimeScale_le_three_logLog
    {X alpha : ℝ} (halpha0 : 0 ≤ alpha) (halpha2 : alpha ≤ 2)
    (hX : Real.exp (Real.exp 1) ≤ X) :
    Real.log (mtTypeIPrimeScale X alpha : ℝ) ≤
      3 * Real.log (Real.log X) := by
  have hXpos : 0 < X := (Real.exp_pos _).trans_le hX
  have hlogX : Real.exp 1 ≤ Real.log X := by
    rw [← Real.log_exp (Real.exp 1)]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos _) hXpos hX
  have hlogXone : (1 : ℝ) ≤ Real.log X :=
    (Real.one_le_exp (by norm_num)).trans hlogX
  have hlogXpos : 0 < Real.log X := zero_lt_one.trans_le hlogXone
  have hll : 1 ≤ Real.log (Real.log X) := by
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos 1) hlogXpos hlogX
  have hy1 : 1 ≤ (Real.log X) ^ alpha :=
    Real.one_le_rpow hlogXone halpha0
  have hypos : 0 < (Real.log X) ^ alpha :=
    Real.rpow_pos_of_pos hlogXpos _
  have hceil : (mtTypeIPrimeScale X alpha : ℝ) <
      (Real.log X) ^ alpha + 1 := by
    simpa only [mtTypeIPrimeScale] using
      (Nat.ceil_lt_add_one (Real.rpow_nonneg hlogXpos.le alpha))
  have hPupper : (mtTypeIPrimeScale X alpha : ℝ) ≤
      2 * (Real.log X) ^ alpha := by linarith
  have hPlower := mtTypeIPrimeScale_lower X alpha
  have hPpos : (0 : ℝ) < mtTypeIPrimeScale X alpha :=
    hypos.trans_le hPlower
  have hlogUpper := Real.strictMonoOn_log.monotoneOn hPpos
    (mul_pos (by norm_num) hypos) hPupper
  have hlogTwo : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  rw [Real.log_mul (by norm_num) hypos.ne', Real.log_rpow hlogXpos] at hlogUpper
  have halphaMul : alpha * Real.log (Real.log X) ≤
      2 * Real.log (Real.log X) := by nlinarith
  linarith

/-- Uniform explicit lower threshold for the rounded source prime scale. -/
theorem eventually_log_mtTypeIPrimeScale_ge_1168 :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ alpha : ℝ, (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
        4 ≤ mtTypeIPrimeScale X alpha ∧
          1168 ≤ Real.log (mtTypeIPrimeScale X alpha : ℝ) := by
  let alpha₀ : ℝ := 10999 / 10000
  have halpha₀ : 0 < alpha₀ := by norm_num [alpha₀]
  filter_upwards
    [Filter.eventually_ge_atTop
      (Real.exp (Real.exp (1168 / alpha₀)))] with X hX
  intro alpha halpha _halpha2
  have hXpos : 0 < X := (Real.exp_pos _).trans_le hX
  have hlogX : Real.exp (1168 / alpha₀) ≤ Real.log X := by
    rw [← Real.log_exp (Real.exp (1168 / alpha₀))]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos _) hXpos hX
  have hlogXpos : 0 < Real.log X := (Real.exp_pos _).trans_le hlogX
  have hll : 1168 / alpha₀ ≤ Real.log (Real.log X) := by
    rw [← Real.log_exp (1168 / alpha₀)]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos _) hlogXpos hlogX
  have hll0 : 0 ≤ Real.log (Real.log X) := by
    have : 0 < 1168 / alpha₀ := div_pos (by norm_num) halpha₀
    linarith
  have halpha0 : 0 ≤ alpha := halpha₀.le.trans halpha
  have hlogPower : 1168 ≤ Real.log ((Real.log X) ^ alpha) := by
    rw [Real.log_rpow hlogXpos]
    have hmul : alpha₀ * (1168 / alpha₀) = 1168 := by field_simp
    nlinarith
  have hscalePos : 0 < (mtTypeIPrimeScale X alpha : ℝ) :=
    (Real.rpow_pos_of_pos hlogXpos _).trans_le (mtTypeIPrimeScale_lower X alpha)
  have hlogScale : Real.log ((Real.log X) ^ alpha) ≤
      Real.log (mtTypeIPrimeScale X alpha : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (Real.rpow_pos_of_pos hlogXpos _)
      hscalePos (mtTypeIPrimeScale_lower X alpha)
  have hlogP : 1168 ≤ Real.log (mtTypeIPrimeScale X alpha : ℝ) :=
    hlogPower.trans hlogScale
  have hP4real : (4 : ℝ) < (mtTypeIPrimeScale X alpha : ℝ) := by
    have hexp : (4 : ℝ) < Real.exp 1168 := by
      nlinarith [Real.add_one_lt_exp (show (1168 : ℝ) ≠ 0 by norm_num)]
    have hlogExp : Real.exp 1168 ≤ (mtTypeIPrimeScale X alpha : ℝ) := by
      rw [← Real.exp_log hscalePos]
      exact Real.exp_le_exp.mpr hlogP
    exact hexp.trans_le hlogExp
  exact ⟨by exact_mod_cast hP4real.le, hlogP⟩

/-- The logarithmic Type-I degree turns the half-density saving into the paper's sixth-power
iterated-logarithmic saving, uniformly over the full source range. -/
theorem eventually_halfPow_mtTypeIPrimeDegree_le_exp_neg_logLogSix :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ alpha T : ℝ, (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
        X ^ (1 / 4 : ℝ) ≤ T →
          (1 / 2 : ℝ) ^ mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T ≤
            Real.exp (-(Real.log (Real.log X)) ^ 6) := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsmall := (RHTower.tendsto_logLog_rpow_div_log_rpow (7 : ℝ)
    (show (0 : ℝ) < 1 by norm_num)).eventually_le_const
      (show (0 : ℝ) < Real.log 2 / 240 by positivity)
  have hlarge := Filter.eventually_ge_atTop (Real.exp (Real.exp 1))
  filter_upwards [hsmall, hlarge, eventually_log_mtTypeIPrimeScale_ge_1168]
    with X hsmallX hX hscaleX
  intro alpha T halpha0 halpha2 hXT
  have hXpos : 0 < X := (Real.exp_pos _).trans_le hX
  have hlogX : Real.exp 1 ≤ Real.log X := by
    rw [← Real.log_exp (Real.exp 1)]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos _) hXpos hX
  have hlogXpos : 0 < Real.log X := (Real.exp_pos _).trans_le hlogX
  have hlogXone : (1 : ℝ) ≤ Real.log X :=
    (Real.one_le_exp (by norm_num)).trans hlogX
  have hll : 1 ≤ Real.log (Real.log X) := by
    rw [← Real.log_exp 1]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos _) hlogXpos hlogX
  have hllpos : 0 < Real.log (Real.log X) := zero_lt_one.trans_le hll
  have halphaNonneg : 0 ≤ alpha := by norm_num at halpha0 ⊢; linarith
  have hlogPupper :=
    log_mtTypeIPrimeScale_le_three_logLog halphaNonneg halpha2 hX
  obtain ⟨hPfour, _hlogPthreshold⟩ := hscaleX alpha halpha0 halpha2
  have hPtwo : 2 ≤ mtTypeIPrimeScale X alpha := by omega
  have hlogPpos : 0 < Real.log (mtTypeIPrimeScale X alpha : ℝ) :=
    Real.log_pos (by exact_mod_cast hPtwo : (1 : ℝ) < mtTypeIPrimeScale X alpha)
  have hquarterPos : 0 < X ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hXpos _
  have hTpos : 0 < T := hquarterPos.trans_le hXT
  have hXone : (1 : ℝ) ≤ X :=
    (Real.one_le_exp (by positivity : (0 : ℝ) ≤ Real.exp 1)).trans hX
  have hquarterOne : (1 : ℝ) ≤ X ^ (1 / 4 : ℝ) :=
    Real.one_le_rpow hXone (by norm_num)
  have hTone : (1 : ℝ) ≤ T := hquarterOne.trans hXT
  have hlogTlower : Real.log X / 4 ≤ Real.log T := by
    have hmono := Real.strictMonoOn_log.monotoneOn hquarterPos hTpos hXT
    rw [Real.log_rpow hXpos] at hmono
    norm_num at hmono ⊢
    nlinarith
  have hdegreeLower :
      Real.log X / (120 * Real.log (Real.log X)) ≤
        Real.log T / (10 * Real.log (mtTypeIPrimeScale X alpha : ℝ)) := by
    calc
      Real.log X / (120 * Real.log (Real.log X)) ≤
          Real.log X / (40 * Real.log (mtTypeIPrimeScale X alpha : ℝ)) := by
        apply div_le_div_of_nonneg_left hlogXpos.le
          (by positivity : 0 < 40 * Real.log (mtTypeIPrimeScale X alpha : ℝ))
        nlinarith
      _ = (Real.log X / 4) /
          (10 * Real.log (mtTypeIPrimeScale X alpha : ℝ)) := by
        field_simp
        norm_num
      _ ≤ Real.log T /
          (10 * Real.log (mtTypeIPrimeScale X alpha : ℝ)) := by
        exact div_le_div_of_nonneg_right hlogTlower (by positivity)
  norm_num only [Real.rpow_natCast, Real.rpow_one] at hsmallX
  have hasymptotic :
      240 * (Real.log (Real.log X)) ^ 7 ≤ Real.log 2 * Real.log X := by
    have hmul := (div_le_iff₀ hlogXpos).mp hsmallX
    have hrpow : (Real.log (Real.log X)) ^ (7 : ℝ) =
        (Real.log (Real.log X)) ^ (7 : ℕ) :=
      Real.rpow_natCast _ 7
    rw [hrpow] at hmul
    calc
      240 * (Real.log (Real.log X)) ^ 7 ≤
          240 * (Real.log 2 / 240 * Real.log X) :=
        mul_le_mul_of_nonneg_left hmul (by norm_num)
      _ = Real.log 2 * Real.log X := by ring
  have hdecayBase :
      (Real.log (Real.log X)) ^ 6 ≤
        Real.log 2 * (Real.log X / (120 * Real.log (Real.log X))) := by
    calc
      (Real.log (Real.log X)) ^ 6 ≤
          Real.log 2 * Real.log X / (120 * Real.log (Real.log X)) := by
        rw [le_div_iff₀ (by positivity : 0 < 120 * Real.log (Real.log X))]
        nlinarith
      _ = Real.log 2 * (Real.log X / (120 * Real.log (Real.log X))) := by ring
  have hdecay :
      (Real.log (Real.log X)) ^ 6 ≤
        Real.log 2 *
          (Real.log T / (10 * Real.log (mtTypeIPrimeScale X alpha : ℝ))) :=
    hdecayBase.trans (mul_le_mul_of_nonneg_left hdegreeLower hlogTwo.le)
  refine (halfPow_mtTypeIPrimeDegree_le_logb hPtwo hTone).trans ?_
  rw [Real.rpow_def_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
  have hlogHalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
    ring
  rw [hlogHalf]
  exact Real.exp_le_exp.mpr (by nlinarith)

/-- The exact ordered-prime tuple mass in every powered Type-I source layer has the sixth-power
iterated-logarithmic density saving used in the paper. -/
theorem eventually_mtTypeIPrimeRaisedPrimeDensity_le_exp_neg_logLogSix :
    ∀ᶠ X : ℝ in Filter.atTop,
      ∀ alpha T : ℝ, (10999 / 10000 : ℝ) ≤ alpha → alpha ≤ 2 →
        X ^ (1 / 4 : ℝ) ≤ T →
          (((mtTypeIPrimeCoeffSupport (mtTypeIPrimeScale X alpha)).card ^
              mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) : ℝ) /
              (((mtTypeIPrimeScale X alpha ^
                mtTypeIPrimeDegree (mtTypeIPrimeScale X alpha) T : ℕ) : ℝ)) ≤
            Real.exp (-(Real.log (Real.log X)) ^ 6) := by
  filter_upwards [eventually_log_mtTypeIPrimeScale_ge_1168,
    eventually_halfPow_mtTypeIPrimeDegree_le_exp_neg_logLogSix] with X hscale hdegree
  intro alpha T halpha0 halpha2 hXT
  obtain ⟨hPfour, hlogP⟩ := hscale alpha halpha0 halpha2
  exact (mtTypeIPrimeRaisedPrimeDensity_le_halfPow hPfour hlogP).trans
    (hdegree alpha T halpha0 halpha2 hXT)

end

end RHTower.Sieve
