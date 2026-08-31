import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIPrimeAmplifierEnergy

/-!
# Source schedule for the Matomäki--Teräväinen Type-I prime amplifier

This is the literal Section 5.1 choice
`k = ceil (log (T^(1/10)) / log P₁)` with `P₁ = (log X)^a`, rounded upward to a
natural dyadic endpoint.  It constructs the power window and discharges the coefficient-energy
condition used in equation (5.4).
-/

namespace RHTower.Sieve

noncomputable section

/-- Literal Section 5.1 raising degree. -/
def mtTypeIPrimeDegree (P : ℕ) (T : ℝ) : ℕ :=
  ⌈Real.logb (P : ℝ) (T ^ (1 / 10 : ℝ))⌉₊

/-- Natural dyadic base attached to the paper's real scale `P₁ = (log X)^a`. -/
def mtTypeIPrimeScale (X a : ℝ) : ℕ :=
  ⌈(Real.log X) ^ a⌉₊

/-- The canonical raising degree is positive on the source height range. -/
theorem mtTypeIPrimeDegree_pos
    {P : ℕ} {T : ℝ} (hP : 2 ≤ P) (hT : 1 < T) :
    0 < mtTypeIPrimeDegree P T := by
  rw [mtTypeIPrimeDegree, Nat.ceil_pos]
  rw [Real.logb]
  have hlogP : 0 < Real.log (P : ℝ) := Real.log_pos (by exact_mod_cast hP)
  have hpow : 1 < T ^ (1 / 10 : ℝ) := Real.one_lt_rpow hT (by norm_num)
  exact div_pos (Real.log_pos hpow) hlogP

/-- Consecutive powers give the exact source window
`T^(1/10) ≤ P^k ≤ P T^(1/10)`. -/
theorem mtTypeIPrimeDegree_power_window
    {P : ℕ} {T : ℝ} (hP : 2 ≤ P) (hT : 1 ≤ T) :
    T ^ (1 / 10 : ℝ) ≤ ((P ^ mtTypeIPrimeDegree P T : ℕ) : ℝ) ∧
      ((P ^ mtTypeIPrimeDegree P T : ℕ) : ℝ) ≤
        (P : ℝ) * T ^ (1 / 10 : ℝ) := by
  let q : ℝ := Real.logb (P : ℝ) (T ^ (1 / 10 : ℝ))
  have hPone : (1 : ℝ) < P := by exact_mod_cast hP
  have hPpos : (0 : ℝ) < P := zero_lt_one.trans hPone
  have hPne : (P : ℝ) ≠ 1 := ne_of_gt hPone
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hTpowpos : 0 < T ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos hTpos _
  have hTpowone : 1 ≤ T ^ (1 / 10 : ℝ) :=
    Real.one_le_rpow hT (by norm_num)
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    rw [Real.logb]
    exact div_nonneg (Real.log_nonneg hTpowone) (Real.log_nonneg hPone.le)
  have hceil : q ≤ (mtTypeIPrimeDegree P T : ℝ) := by
    simpa only [mtTypeIPrimeDegree, q] using (Nat.le_ceil q)
  have hceilUpper : (mtTypeIPrimeDegree P T : ℝ) < q + 1 := by
    simpa only [mtTypeIPrimeDegree, q] using Nat.ceil_lt_add_one hq0
  have hqpow : (P : ℝ) ^ q = T ^ (1 / 10 : ℝ) := by
    dsimp only [q]
    exact Real.rpow_logb hPpos hPne hTpowpos
  constructor
  · rw [← hqpow]
    calc
      (P : ℝ) ^ q ≤ (P : ℝ) ^ (mtTypeIPrimeDegree P T : ℝ) :=
        (Real.strictMono_rpow_of_base_gt_one hPone).monotone hceil
      _ = ((P ^ mtTypeIPrimeDegree P T : ℕ) : ℝ) := by
        rw [Real.rpow_natCast]
        norm_num
  · have hpowlt : (P : ℝ) ^ (mtTypeIPrimeDegree P T : ℝ) <
        (P : ℝ) ^ (q + 1) :=
      (Real.strictMono_rpow_of_base_gt_one hPone) hceilUpper
    have hadd : (P : ℝ) ^ (q + 1) = (P : ℝ) * T ^ (1 / 10 : ℝ) := by
      rw [Real.rpow_add hPpos, hqpow, Real.rpow_one]
      ring
    rw [hadd] at hpowlt
    simpa only [Real.rpow_natCast, Nat.cast_pow] using hpowlt.le

/-- The paper-scale identity `P₁ = (log X)^a` forces `k ≤ P₁^(1/a)`, exactly the
coefficient-energy exponent in equation (5.4). -/
theorem mtTypeIPrimeDegree_le_source_power
    {X T a : ℝ} {P : ℕ}
    (ha : 0 < a) (hX : Real.exp 2 ≤ X) (hTX : T ≤ X)
    (hT : 1 ≤ T) (hP : 2 ≤ P)
    (hlogP : 2 ≤ Real.log (P : ℝ))
    (hscale : (Real.log X) ^ a ≤ (P : ℝ)) :
    (mtTypeIPrimeDegree P T : ℝ) ≤ (P : ℝ) ^ (1 / a) := by
  let q : ℝ := Real.logb (P : ℝ) (T ^ (1 / 10 : ℝ))
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hX
  have hlogX : 2 ≤ Real.log X := by
    rw [← Real.log_exp 2]
    exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos 2) hXpos hX
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  have hlogT : Real.log T ≤ Real.log X :=
    Real.strictMonoOn_log.monotoneOn hTpos hXpos hTX
  have hPone : (1 : ℝ) < P := by exact_mod_cast hP
  have hq0 : 0 ≤ q := by
    dsimp only [q]
    rw [Real.logb, Real.log_rpow hTpos]
    exact div_nonneg (mul_nonneg (by norm_num) (Real.log_nonneg hT))
      ((show (0 : ℝ) ≤ 2 by norm_num).trans hlogP)
  have hceil : (mtTypeIPrimeDegree P T : ℝ) < q + 1 := by
    simpa only [mtTypeIPrimeDegree, q] using Nat.ceil_lt_add_one hq0
  have hq : q ≤ Real.log X / 20 := by
    dsimp only [q]
    rw [Real.logb, Real.log_rpow hTpos]
    have hden : 0 < Real.log (P : ℝ) := lt_of_lt_of_le zero_lt_two hlogP
    rw [div_le_iff₀ hden]
    have hlogX0 : 0 ≤ Real.log X := zero_le_two.trans hlogX
    calc
      (1 / 10 : ℝ) * Real.log T ≤ (1 / 10 : ℝ) * Real.log X := by gcongr
      _ ≤ (Real.log X / 20) * Real.log (P : ℝ) := by
        nlinarith
  have hklog : (mtTypeIPrimeDegree P T : ℝ) ≤ Real.log X := by
    exact hceil.le.trans (by nlinarith [hlogX])
  have hlogXpos : 0 < Real.log X := zero_lt_two.trans_le hlogX
  have hpowScale := Real.rpow_le_rpow
    (Real.rpow_nonneg hlogXpos.le a) hscale (by positivity : 0 ≤ 1 / a)
  have hcancel : ((Real.log X) ^ a) ^ (1 / a) = Real.log X := by
    rw [← Real.rpow_mul hlogXpos.le]
    rw [show a * (1 / a) = 1 by field_simp, Real.rpow_one]
  rw [hcancel] at hpowScale
  exact hklog.trans hpowScale

/-- Upward rounding preserves the paper's lower base scale. -/
theorem mtTypeIPrimeScale_lower
    (X a : ℝ) :
    (Real.log X) ^ a ≤ (mtTypeIPrimeScale X a : ℝ) := by
  exact Nat.le_ceil ((Real.log X) ^ a)

/-- The canonical natural prime scale is at least two once the real scale exceeds `e²`. -/
theorem mtTypeIPrimeScale_two_le
    {X a : ℝ} (hscale : Real.exp 2 ≤ (Real.log X) ^ a) :
    2 ≤ mtTypeIPrimeScale X a := by
  have hexp : (2 : ℝ) < Real.exp 2 := by
    nlinarith [Real.add_one_lt_exp (show (2 : ℝ) ≠ 0 by norm_num)]
  have hcast : (2 : ℝ) ≤ (mtTypeIPrimeScale X a : ℝ) :=
    hexp.le.trans (hscale.trans (mtTypeIPrimeScale_lower X a))
  exact_mod_cast hcast

/-- The same scale threshold gives the logarithmic denominator used by the ceiling estimate. -/
theorem mtTypeIPrimeScale_log_two_le
    {X a : ℝ} (hscale : Real.exp 2 ≤ (Real.log X) ^ a) :
    2 ≤ Real.log (mtTypeIPrimeScale X a : ℝ) := by
  have hPpos : (0 : ℝ) < mtTypeIPrimeScale X a := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two (mtTypeIPrimeScale_two_le hscale))
  rw [← Real.log_exp 2]
  exact Real.strictMonoOn_log.monotoneOn (Real.exp_pos 2) hPpos
    (hscale.trans (mtTypeIPrimeScale_lower X a))

/-- Complete literal Section 5.1 source schedule: natural base, canonical ceiling degree, power
window, and equation-(5.4) exponent. -/
theorem mtTypeIPrimeDegree_source_schedule
    {X T a : ℝ} (ha : 0 < a)
    (hX : Real.exp 2 ≤ X) (hscale : Real.exp 2 ≤ (Real.log X) ^ a)
    (hT : 1 < T) (hTX : T ≤ X) :
    let P := mtTypeIPrimeScale X a
    let ell := mtTypeIPrimeDegree P T
    0 < ell ∧
      T ^ (1 / 10 : ℝ) ≤ ((P ^ ell : ℕ) : ℝ) ∧
      ((P ^ ell : ℕ) : ℝ) ≤ (P : ℝ) * T ^ (1 / 10 : ℝ) ∧
      (ell : ℝ) ≤ (P : ℝ) ^ (1 / a) := by
  dsimp only
  have hP := mtTypeIPrimeScale_two_le hscale
  have hwindow := mtTypeIPrimeDegree_power_window hP hT.le
  exact ⟨mtTypeIPrimeDegree_pos hP hT, hwindow.1, hwindow.2,
    mtTypeIPrimeDegree_le_source_power ha hX hTX hT.le hP
      (mtTypeIPrimeScale_log_two_le hscale) (mtTypeIPrimeScale_lower X a)⟩

/-- Equation (5.4) on every literal Watt block, with base and raising degree constructed from the
paper's `P₁ = (log X)^a` schedule. -/
theorem sum_Ioc_normSq_mtTypeIPrimeRaisedCoeff_source_schedule
    {X T a : ℝ} (B : ℕ) (ha : 0 < a)
    (hX : Real.exp 2 ≤ X) (hscale : Real.exp 2 ≤ (Real.log X) ^ a)
    (hT : 1 < T) (hTX : T ≤ X) :
    let P := mtTypeIPrimeScale X a
    let ell := mtTypeIPrimeDegree P T
    ∑ m ∈ Finset.Ioc B (2 * B), ‖mtTypeIPrimeRaisedCoeff P ell m‖ ^ 2 ≤
      (((P ^ ell : ℕ) : ℝ)) ^ (1 + 1 / a) := by
  dsimp only
  have hschedule := mtTypeIPrimeDegree_source_schedule ha hX hscale hT hTX
  exact sum_Ioc_normSq_mtTypeIPrimeRaisedCoeff_le_rpow
    (show 1 ≤ mtTypeIPrimeScale X a from
      one_le_two.trans (mtTypeIPrimeScale_two_le hscale)) hschedule.2.2.2

end

end RHTower.Sieve
