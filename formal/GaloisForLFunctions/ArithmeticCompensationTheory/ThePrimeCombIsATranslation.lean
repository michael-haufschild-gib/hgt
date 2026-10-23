import GaloisForLFunctions.RHTower.PrimeRpowLogSumAsymptotic
import GaloisForLFunctions.RHTower.ZetaOneLineDeficit
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeCombEnergyReduction
import GaloisForLFunctions.ArithmeticIncidencePositivity.PrimeTowerLedgerReduction
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The prime comb is a translation: the sharp exponential rate of the raw comb energy

The cost side of the incidence ledger is the first-power charge `Σ_p w_p A_F(log p)`, and
Cauchy–Schwarz bounds it by `A_F(0)` times the **raw comb energy**
`E_r(F) = ‖C_r F‖² = Σ_{p,q ≤ e^{2r}} w_p w_q A_F(log(q/p))`, `C_r F = Σ_p w_p F(· + log p)`, with
the Euler weights `w_p = √p log p/(p − 1)` (`ArithmeticIncidencePositivity.PrimeCombEnergyReduction`).
Whether that energy, or its cross-prime part, is polynomial in the aperture was the open
alternative of the comb reduction. It is not: on the slowly varying tests `F_r(x) = r^{−1/2} f(x/r)`
the energy is as large as the universal bound allows.

**Concentration at the horizon.**

* `tendsto_combMass_div_exp`: the comb mass `S_r = Σ_{p ≤ e^{2r}} w_p` satisfies `S_r ∼ 2e^r` — the
  prime number theorem through Abel summation; `w_p − p^{−1/2} log p` has a bounded sum.
* `tendsto_tailMass_div_combMass`: the primes `p ≤ e^{(2−δ)r}` carry a vanishing fraction of it.
* `tendsto_combAverage`, `tendsto_combPairAverage`: the rescaled shifts `log p/r` concentrate at
  `2` and their differences at `0`, against every bounded test continuous at that point.

**The comb on the slowly varying family.**

* `combEnergy_le_combMass_sq_mul`: `E_r(F) ≤ S_r² A_F(0)` for every test.
* `tendsto_combEnergy_rescaledTest_div_exp`: `E_r(F_r) ∼ 4 e^{2r} A_f(0)`, so the rate `2` of the
  raw energy is sharp; `tendsto_combCross_rescaledTest_div_exp`: the cross-prime aggregate alone is
  `∼ 4 e^{2r} A_f(0)`, because the diagonal `Σ w_p²` is `O(r³)`.
* `tendsto_testPairing_normalizedComb_sub_translate` — **the positive survivor**: the normalized
  comb is a translation, `(√r/S_r)(C_r F_r)(r ·) → f(· + 2)` in `L²`. The comb is not a rank-one
  object; it moves the whole slowly varying profile to the horizon.
* `tendsto_combCharge_rescaledTest_div_combMass_zero`: the first-power charge itself is `o(S_r)`
  when `f` lives in `[−1, 1]`: `S_r^{−1} Σ_p w_p A_{F_r}(log p) → A_f(2) = 0`, since the translate
  `f(· + 2)` is supported in `[−3, −1]`. Enormous energy is no adverse charge: the Cauchy–Schwarz
  step discards exactly the geometry of the translation.
* `exists_odd_smooth_family_sharp_comb_rate`: all of this on an explicit smooth odd family of unit
  mass supported in `[−r, r]`, the ledger's own test class.
-/

open Filter Topology Finset MeasureTheory
open GaloisForLFunctions.ArithmeticCriticalityTheory GaloisForLFunctions.ArithmeticIncidencePositivity

noncomputable section

namespace GaloisForLFunctions.ArithmeticCompensationTheory

/-! ## The weights, the comb primes and the comb mass -/

/-- The Euler comb weight `w_p = √p log p/(p − 1)`. -/
def combWeight (p : ℕ) : ℝ := Real.sqrt p * Real.log p / ((p : ℝ) - 1)

/-- The comb primes at aperture `r`: the primes `p ≤ e^{2r}`. -/
def combPrimes (r : ℝ) : Finset ℕ := Nat.primesLE ⌊Real.exp (2 * r)⌋₊

/-- The comb mass `S_r = Σ_{p ≤ e^{2r}} w_p`. -/
def combMass (r : ℝ) : ℝ := ∑ p ∈ combPrimes r, combWeight p

theorem combWeight_nonneg (p : ℕ) : 0 ≤ combWeight p := by
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · simp [combWeight]
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (Real.log_nonneg hp1)) (by linarith)

theorem combMass_nonneg (r : ℝ) : 0 ≤ combMass r :=
  sum_nonneg fun p _ => combWeight_nonneg p

theorem mem_combPrimes {r : ℝ} {p : ℕ} :
    p ∈ combPrimes r ↔ p.Prime ∧ (p : ℝ) ≤ Real.exp (2 * r) := by
  rw [combPrimes, Nat.primesLE, Nat.primesBelow, mem_filter, mem_range, Nat.lt_succ_iff,
    Nat.le_floor_iff (Real.exp_pos _).le, and_comm]

theorem log_le_of_mem_combPrimes {r : ℝ} {p : ℕ} (hp : p ∈ combPrimes r) :
    Real.log p ≤ 2 * r := by
  obtain ⟨hpr, hle⟩ := mem_combPrimes.mp hp
  have h0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
  have := Real.log_le_log h0 hle
  rwa [Real.log_exp] at this

theorem combPrimes_mono {r r' : ℝ} (h : r ≤ r') : combPrimes r ⊆ combPrimes r' := by
  intro p hp
  obtain ⟨hpr, hle⟩ := mem_combPrimes.mp hp
  exact mem_combPrimes.mpr ⟨hpr, hle.trans (Real.exp_le_exp.mpr (by linarith))⟩

/-! ## The comb mass is `2e^r` -/

/-- The weight splits into the prime-number-theorem part `p^{−1/2} log p` and a correction. -/
theorem combWeight_eq {p : ℕ} (hp : 2 ≤ p) :
    combWeight p = (p : ℝ) ^ ((1 / 2 : ℝ) - 1) * Real.log p +
      Real.log p / (Real.sqrt p * ((p : ℝ) - 1)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by
    have : (2 : ℝ) ≤ p := by exact_mod_cast hp
    linarith
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hpow : (p : ℝ) ^ ((1 / 2 : ℝ) - 1) = (Real.sqrt p)⁻¹ := by
    rw [show (1 / 2 : ℝ) - 1 = -(1 / 2) by norm_num, Real.rpow_neg hp0.le, ← Real.sqrt_eq_rpow]
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  rw [combWeight, hpow]
  field_simp
  rw [Real.sq_sqrt hp0.le]
  ring

/-- The correction `log p/(√p (p − 1))` is at most `2 p^{−3/2} log p`. -/
theorem correction_le {p : ℕ} (hp : 2 ≤ p) :
    Real.log p / (Real.sqrt p * ((p : ℝ) - 1)) ≤ 2 * ((p : ℝ) ^ (-(1 + 1 / 2 : ℝ)) * Real.log p) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hpow : (p : ℝ) ^ (-(1 + 1 / 2 : ℝ)) = ((p : ℝ) * Real.sqrt p)⁻¹ := by
    rw [Real.rpow_neg hp0.le, Real.rpow_add hp0, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hpow, div_le_iff₀ (by nlinarith)]
  have hkey : (p : ℝ) * Real.sqrt p * Real.log p ≤
      2 * Real.log p * (Real.sqrt p * ((p : ℝ) - 1)) := by
    have : (p : ℝ) ≤ 2 * ((p : ℝ) - 1) := by linarith
    nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg hs.le hlog)]
  calc 2 * (((p : ℝ) * Real.sqrt p)⁻¹ * Real.log p) * (Real.sqrt p * ((p : ℝ) - 1))
      = (2 * Real.log p * (Real.sqrt p * ((p : ℝ) - 1))) / ((p : ℝ) * Real.sqrt p) := by
        field_simp
    _ ≥ (p : ℝ) * Real.sqrt p * Real.log p / ((p : ℝ) * Real.sqrt p) :=
        div_le_div_of_nonneg_right hkey (by positivity)
    _ = Real.log p := by field_simp

/-- The prime-number-theorem part of the comb mass. -/
def combMainMass (r : ℝ) : ℝ :=
  ∑ p ∈ combPrimes r, (p : ℝ) ^ ((1 / 2 : ℝ) - 1) * Real.log p

/-- The correction part of the comb mass. -/
def combCorrectionMass (r : ℝ) : ℝ :=
  ∑ p ∈ combPrimes r, Real.log p / (Real.sqrt p * ((p : ℝ) - 1))

theorem combMass_eq_main_add_correction (r : ℝ) :
    combMass r = combMainMass r + combCorrectionMass r := by
  rw [combMass, combMainMass, combCorrectionMass, ← sum_add_distrib]
  exact sum_congr rfl fun p hp => combWeight_eq (mem_combPrimes.mp hp).1.two_le

theorem combCorrectionMass_nonneg (r : ℝ) : 0 ≤ combCorrectionMass r := by
  refine sum_nonneg fun p hp => ?_
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (mem_combPrimes.mp hp).1.two_le
  have hs : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
  exact div_nonneg (Real.log_nonneg (by linarith)) (mul_nonneg hs (by linarith))

/-- The correction part of the comb mass is bounded. -/
theorem combCorrectionMass_le (r : ℝ) :
    combCorrectionMass r ≤ 2 * (1 / (1 / 2) + RHTower.tiltedPrimeLogTotalConst) := by
  have h := RHTower.sum_primesLE_rpowLog_le (δ := 1 / 2) (by norm_num) (by norm_num)
    ⌊Real.exp (2 * r)⌋₊
  calc combCorrectionMass r
      ≤ ∑ p ∈ combPrimes r, 2 * ((p : ℝ) ^ (-(1 + 1 / 2 : ℝ)) * Real.log p) :=
        sum_le_sum fun p hp => correction_le (mem_combPrimes.mp hp).1.two_le
    _ = 2 * ∑ p ∈ Nat.primesLE ⌊Real.exp (2 * r)⌋₊, (p : ℝ) ^ (-(1 + 1 / 2 : ℝ)) * Real.log p := by
        rw [mul_sum]; rfl
    _ ≤ _ := by linarith

/-- The main part is `2^{−1/2} log 2` plus the Abel-summed prime sum over `(2, e^{2r}]`. -/
theorem combMainMass_eq {r : ℝ} (hr : 2 ≤ Real.exp (2 * r)) :
    combMainMass r = (2 : ℝ) ^ ((1 / 2 : ℝ) - 1) * Real.log 2 +
      RHTower.primeRpowLogSumIoc (1 / 2) (Real.exp (2 * r)) := by
  set N := ⌊Real.exp (2 * r)⌋₊ with hN
  have hN2 : 2 ≤ N := Nat.le_floor (by exact_mod_cast hr)
  rw [combMainMass, combPrimes, ← hN, Nat.primesLE, Nat.primesBelow, sum_filter,
    RHTower.primeRpowLogSumIoc, ← hN,
    ← sum_range_add_sum_Ico _ (show 3 ≤ N + 1 by omega)]
  rw [show Ico 3 (N + 1) = Ioc 2 N by ext k; simp only [mem_Ico, mem_Ioc]; omega]
  congr 1
  rw [show (range 3 : Finset ℕ) = {0, 1, 2} by decide, sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  simp [Nat.prime_two]

/-- **The comb mass is `2e^r`.** `S_r/e^r → 2`. -/
theorem tendsto_combMass_div_exp :
    Tendsto (fun r => combMass r / Real.exp r) atTop (𝓝 2) := by
  have hX : Tendsto (fun r : ℝ => Real.exp (2 * r)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by norm_num))
  have hmain := (RHTower.tendsto_primeRpowLogSumIoc (a := 1 / 2) (by norm_num)).comp hX
  have hpow : ∀ r : ℝ, Real.exp (2 * r) ^ (1 / 2 : ℝ) = Real.exp r := fun r => by
    rw [← Real.exp_mul]; ring_nf
  have hexp : Tendsto (fun r : ℝ => (Real.exp r)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_exp_atTop
  -- the constant `2^{−1/2} log 2` and the bounded correction vanish against `e^r`
  set K : ℝ := (2 : ℝ) ^ ((1 / 2 : ℝ) - 1) * Real.log 2
  set B : ℝ := 2 * (1 / (1 / 2) + RHTower.tiltedPrimeLogTotalConst)
  have hK : Tendsto (fun r : ℝ => K / Real.exp r) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using hexp.const_mul K
  have hC : Tendsto (fun r : ℝ => combCorrectionMass r / Real.exp r) atTop (𝓝 0) := by
    have hB : Tendsto (fun r : ℝ => B / Real.exp r) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using hexp.const_mul B
    refine squeeze_zero (fun r => div_nonneg (combCorrectionMass_nonneg r) (Real.exp_pos r).le)
      (fun r => div_le_div_of_nonneg_right (combCorrectionMass_le r) (Real.exp_pos r).le) hB
  have hsum := (hK.add hmain).add hC
  rw [zero_add, add_zero, show (1 : ℝ) / (1 / 2) = 2 by norm_num] at hsum
  refine hsum.congr' ?_
  filter_upwards [hX.eventually_ge_atTop 2] with r hr
  simp only [Function.comp_apply, hpow]
  rw [combMass_eq_main_add_correction, combMainMass_eq hr]
  ring

/-- Eventually the comb mass exceeds `e^r`; in particular it is positive. -/
theorem eventually_exp_le_combMass : ∀ᶠ r in atTop, Real.exp r ≤ combMass r := by
  filter_upwards [tendsto_combMass_div_exp.eventually (eventually_ge_nhds (by norm_num :
    (1 : ℝ) < 2))] with r hr
  rwa [le_div_iff₀ (Real.exp_pos r), one_mul] at hr

/-- Eventually the comb mass is below `3e^r`. -/
theorem eventually_combMass_le : ∀ᶠ r in atTop, combMass r ≤ 3 * Real.exp r := by
  filter_upwards [tendsto_combMass_div_exp.eventually (eventually_le_nhds (by norm_num :
    (2 : ℝ) < 3))] with r hr
  rwa [div_le_iff₀ (Real.exp_pos r)] at hr

theorem eventually_combMass_pos : ∀ᶠ r in atTop, 0 < combMass r := by
  filter_upwards [eventually_exp_le_combMass] with r hr
  exact (Real.exp_pos r).trans_le hr

/-! ## The tail below the horizon carries no mass -/

/-- **The tail is negligible.** For `0 < δ < 2` the primes `p ≤ e^{(2−δ)r}` carry the mass
`S_{(1−δ/2)r}`, a vanishing fraction of `S_r`. -/
theorem tendsto_tailMass_div_combMass {δ : ℝ} (hδ : 0 < δ) (hδ2 : δ < 2) :
    Tendsto (fun r => combMass ((1 - δ / 2) * r) / combMass r) atTop (𝓝 0) := by
  have hc : 0 < 1 - δ / 2 := by linarith
  have hlin : Tendsto (fun r : ℝ => (1 - δ / 2) * r) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  have hdecay : Tendsto (fun r : ℝ => 3 * Real.exp (-(δ / 2) * r)) atTop (𝓝 0) := by
    have h := Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by linarith :
      (0 : ℝ) < δ / 2))
    have h' := (tendsto_inv_atTop_zero.comp h).const_mul 3
    rw [mul_zero] at h'
    refine h'.congr fun r => ?_
    simp only [Function.comp_apply, id]
    rw [← Real.exp_neg]; ring_nf
  refine squeeze_zero' ?_ ?_ hdecay
  · filter_upwards [eventually_combMass_pos] with r hr
    exact div_nonneg (combMass_nonneg _) hr.le
  · filter_upwards [eventually_exp_le_combMass, hlin.eventually eventually_combMass_le] with r hr hr'
    have hpos : 0 < combMass r := (Real.exp_pos r).trans_le hr
    rw [div_le_iff₀ hpos]
    calc combMass ((1 - δ / 2) * r) ≤ 3 * Real.exp ((1 - δ / 2) * r) := hr'
      _ = 3 * Real.exp (-(δ / 2) * r) * Real.exp r := by
          rw [mul_assoc, ← Real.exp_add]; ring_nf
      _ ≤ 3 * Real.exp (-(δ / 2) * r) * combMass r :=
          mul_le_mul_of_nonneg_left hr (by positivity)

/-- A comb prime outside the tail has rescaled shift within `δ` of `2`. -/
theorem abs_log_div_sub_two_lt {r δ : ℝ} (hr : 0 < r) {p : ℕ} (hp : p ∈ combPrimes r)
    (hpT : p ∉ combPrimes ((1 - δ / 2) * r)) : |Real.log p / r - 2| < δ := by
  obtain ⟨hpr, _⟩ := mem_combPrimes.mp hp
  have hup := log_le_of_mem_combPrimes hp
  have hlow : (2 - δ) * r < Real.log p := by
    by_contra h
    push Not at h
    apply hpT
    refine mem_combPrimes.mpr ⟨hpr, ?_⟩
    have h0 : (0 : ℝ) < p := by exact_mod_cast hpr.pos
    calc (p : ℝ) = Real.exp (Real.log p) := (Real.exp_log h0).symm
      _ ≤ Real.exp (2 * ((1 - δ / 2) * r)) := Real.exp_le_exp.mpr (by linarith)
  rw [abs_lt, lt_sub_iff_add_lt, sub_lt_iff_lt_add, lt_div_iff₀ hr, div_lt_iff₀ hr]
  constructor <;> nlinarith

/-! ## Concentration of the rescaled shifts -/

/-- The mass of a sub-comb, written as an indicator sum over the comb. -/
theorem sum_indicator_eq {r r' : ℝ} (h : r' ≤ r) :
    ∑ p ∈ combPrimes r, combWeight p * (if p ∈ combPrimes r' then 1 else 0) = combMass r' := by
  simp only [mul_ite, mul_one, mul_zero]
  rw [sum_ite_mem, inter_eq_right.mpr (combPrimes_mono h), combMass]

/-- **The rescaled shifts concentrate at `2`.** For every bounded `g` continuous at `2`,
`S_r^{−1} Σ_{p ≤ e^{2r}} w_p g(log p/r) → g(2)`. -/
theorem tendsto_combAverage {g : ℝ → ℝ} {M : ℝ} (hg : ∀ t, |g t| ≤ M) (hg2 : ContinuousAt g 2) :
    Tendsto (fun r => (∑ p ∈ combPrimes r, combWeight p * g (Real.log p / r)) / combMass r)
      atTop (𝓝 (g 2)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg 0)
  obtain ⟨δ₀, hδ₀, hcont⟩ := Metric.continuousAt_iff.mp hg2 (ε / 2) (by positivity)
  set δ := min δ₀ 1 with hδdef
  have hδ : 0 < δ := lt_min hδ₀ one_pos
  have hδ2 : δ < 2 := (min_le_right _ _).trans_lt (by norm_num)
  have htail := (tendsto_tailMass_div_combMass hδ hδ2).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / (8 * (M + 1)) by positivity))
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (htail.and (eventually_combMass_pos.and (eventually_gt_atTop 0)))
  refine ⟨R, fun r hr => ?_⟩
  obtain ⟨hT, hS, hr0⟩ := hR r hr
  set S := combMass r
  set T := combMass ((1 - δ / 2) * r)
  have hTS : T / S < ε / (8 * (M + 1)) := hT
  have hT0 : 0 ≤ T := combMass_nonneg _
  have hsub : (1 - δ / 2) * r ≤ r := by nlinarith
  -- pointwise: near the horizon by continuity, in the tail by the bound `2M`
  have hpt : ∀ p ∈ combPrimes r, combWeight p * |g (Real.log p / r) - g 2| ≤
      combWeight p * (ε / 2) + 2 * M * (combWeight p *
        (if p ∈ combPrimes ((1 - δ / 2) * r) then 1 else 0)) := by
    intro p hp
    have hw := combWeight_nonneg p
    by_cases hpT : p ∈ combPrimes ((1 - δ / 2) * r)
    · simp only [hpT, if_true, mul_one]
      have : |g (Real.log p / r) - g 2| ≤ 2 * M := by
        have := abs_sub (g (Real.log p / r)) (g 2)
        linarith [hg (Real.log p / r), hg 2]
      nlinarith [mul_le_mul_of_nonneg_left this hw]
    · simp only [hpT, if_false, mul_zero, add_zero]
      have hclose : dist (Real.log p / r) 2 < δ₀ := by
        rw [Real.dist_eq]
        exact (abs_log_div_sub_two_lt hr0 hp hpT).trans_le (min_le_left _ _)
      have := hcont hclose
      rw [Real.dist_eq] at this
      exact mul_le_mul_of_nonneg_left this.le hw
  have hsum : |∑ p ∈ combPrimes r, combWeight p * g (Real.log p / r) - S * g 2| ≤
      S * (ε / 2) + 2 * M * T := by
    have heq : ∑ p ∈ combPrimes r, combWeight p * g (Real.log p / r) - S * g 2 =
        ∑ p ∈ combPrimes r, combWeight p * (g (Real.log p / r) - g 2) := by
      simp only [S, combMass, sum_mul, ← sum_sub_distrib, mul_sub]
    rw [heq]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ p ∈ combPrimes r, |combWeight p * (g (Real.log p / r) - g 2)|
        = ∑ p ∈ combPrimes r, combWeight p * |g (Real.log p / r) - g 2| :=
          sum_congr rfl fun p _ => by rw [abs_mul, abs_of_nonneg (combWeight_nonneg p)]
      _ ≤ ∑ p ∈ combPrimes r, (combWeight p * (ε / 2) + 2 * M * (combWeight p *
            (if p ∈ combPrimes ((1 - δ / 2) * r) then 1 else 0))) := sum_le_sum hpt
      _ = S * (ε / 2) + 2 * M * T := by
          rw [sum_add_distrib, ← sum_mul, ← mul_sum, sum_indicator_eq hsub]; rfl
  rw [Real.dist_eq, div_sub' hS.ne', abs_div, abs_of_pos hS, div_lt_iff₀ hS]
  have hTle : T ≤ ε / (8 * (M + 1)) * S := by
    rw [div_lt_iff₀ hS] at hTS; linarith
  have hfrac : M / (M + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have h2M : 2 * M * T ≤ ε / 4 * S := by
    calc 2 * M * T ≤ 2 * M * (ε / (8 * (M + 1)) * S) := mul_le_mul_of_nonneg_left hTle (by positivity)
      _ = ε / 4 * S * (M / (M + 1)) := by field_simp; ring
      _ ≤ ε / 4 * S * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = ε / 4 * S := by ring
  refine lt_of_le_of_lt hsum ?_
  nlinarith

/-- **The shift differences concentrate at `0`.** For every bounded `g` continuous at `0`,
`S_r^{−2} Σ_{p,q ≤ e^{2r}} w_p w_q g((log q − log p)/r) → g(0)`. -/
theorem tendsto_combPairAverage {g : ℝ → ℝ} {M : ℝ} (hg : ∀ t, |g t| ≤ M)
    (hg0 : ContinuousAt g 0) :
    Tendsto (fun r => (∑ p ∈ combPrimes r, ∑ q ∈ combPrimes r,
        combWeight p * combWeight q * g ((Real.log q - Real.log p) / r)) / combMass r ^ 2)
      atTop (𝓝 (g 0)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hM : 0 ≤ M := (abs_nonneg _).trans (hg 0)
  obtain ⟨δ₀, hδ₀, hcont⟩ := Metric.continuousAt_iff.mp hg0 (ε / 2) (by positivity)
  set δ := min (δ₀ / 2) 1 with hδdef
  have hδ : 0 < δ := lt_min (by positivity) one_pos
  have hδ2 : δ < 2 := (min_le_right _ _).trans_lt (by norm_num)
  have htail := (tendsto_tailMass_div_combMass hδ hδ2).eventually
    (gt_mem_nhds (show (0 : ℝ) < ε / (16 * (M + 1)) by positivity))
  obtain ⟨R, hR⟩ := eventually_atTop.mp
    (htail.and (eventually_combMass_pos.and (eventually_gt_atTop 0)))
  refine ⟨R, fun r hr => ?_⟩
  obtain ⟨hT, hS, hr0⟩ := hR r hr
  set S := combMass r
  set T := combMass ((1 - δ / 2) * r)
  set I : ℕ → ℝ := fun p => if p ∈ combPrimes ((1 - δ / 2) * r) then 1 else 0 with hIdef
  have hTS : T / S < ε / (16 * (M + 1)) := hT
  have hT0 : 0 ≤ T := combMass_nonneg _
  have hsub : (1 - δ / 2) * r ≤ r := by nlinarith
  have hI0 : ∀ p, 0 ≤ I p := fun p => by simp only [hIdef]; split_ifs <;> norm_num
  have hpt : ∀ p ∈ combPrimes r, ∀ q ∈ combPrimes r,
      |g ((Real.log q - Real.log p) / r) - g 0| ≤ ε / 2 + 2 * M * (I p + I q) := by
    intro p hp q hq
    by_cases hpq : p ∈ combPrimes ((1 - δ / 2) * r) ∨ q ∈ combPrimes ((1 - δ / 2) * r)
    · have hb : |g ((Real.log q - Real.log p) / r) - g 0| ≤ 2 * M := by
        have := abs_sub (g ((Real.log q - Real.log p) / r)) (g 0)
        linarith [hg ((Real.log q - Real.log p) / r), hg 0]
      have h1 : 1 ≤ I p + I q := by
        rcases hpq with h | h
        · have : I p = 1 := by simp only [hIdef, h, if_true]
          linarith [hI0 q]
        · have : I q = 1 := by simp only [hIdef, h, if_true]
          linarith [hI0 p]
      nlinarith
    · push Not at hpq
      have hp' := abs_log_div_sub_two_lt hr0 hp hpq.1
      have hq' := abs_log_div_sub_two_lt hr0 hq hpq.2
      have hclose : dist ((Real.log q - Real.log p) / r) 0 < δ₀ := by
        rw [Real.dist_eq, sub_zero, sub_div]
        have : |Real.log q / r - Real.log p / r| ≤ |Real.log q / r - 2| + |Real.log p / r - 2| := by
          have := abs_sub_le (Real.log q / r) 2 (Real.log p / r)
          rwa [abs_sub_comm 2] at this
        have hδle : δ ≤ δ₀ / 2 := min_le_left _ _
        linarith
      have := hcont hclose
      rw [Real.dist_eq] at this
      linarith [hI0 p, hI0 q, mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM)
        (add_nonneg (hI0 p) (hI0 q))]
  have hIsum : ∑ p ∈ combPrimes r, combWeight p * I p = T := sum_indicator_eq hsub
  have hsum : |∑ p ∈ combPrimes r, ∑ q ∈ combPrimes r,
      combWeight p * combWeight q * g ((Real.log q - Real.log p) / r) - S ^ 2 * g 0| ≤
      S ^ 2 * (ε / 2) + 4 * M * T * S := by
    have heq : ∑ p ∈ combPrimes r, ∑ q ∈ combPrimes r,
        combWeight p * combWeight q * g ((Real.log q - Real.log p) / r) - S ^ 2 * g 0 =
        ∑ p ∈ combPrimes r, ∑ q ∈ combPrimes r,
          combWeight p * combWeight q * (g ((Real.log q - Real.log p) / r) - g 0) := by
      have hS2 : S ^ 2 * g 0 = ∑ p ∈ combPrimes r, ∑ q ∈ combPrimes r,
          combWeight p * combWeight q * g 0 := by
        simp only [S, combMass, sq, sum_mul, mul_sum]
        exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring
      rw [hS2, ← sum_sub_distrib]
      exact sum_congr rfl fun p _ => by rw [← sum_sub_distrib]; simp only [mul_sub]
    rw [heq]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ p ∈ combPrimes r, |∑ q ∈ combPrimes r,
          combWeight p * combWeight q * (g ((Real.log q - Real.log p) / r) - g 0)|
        ≤ ∑ p ∈ combPrimes r, ∑ q ∈ combPrimes r,
          combWeight p * combWeight q * (ε / 2 + 2 * M * (I p + I q)) := by
          refine sum_le_sum fun p hp => (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun q hq => ?_)
          rw [abs_mul, abs_of_nonneg (mul_nonneg (combWeight_nonneg p) (combWeight_nonneg q))]
          exact mul_le_mul_of_nonneg_left (hpt p hp q hq)
            (mul_nonneg (combWeight_nonneg p) (combWeight_nonneg q))
      _ = S ^ 2 * (ε / 2) + 2 * M * ((∑ p ∈ combPrimes r, combWeight p * I p) * S +
            S * ∑ q ∈ combPrimes r, combWeight q * I q) := by
          simp only [S, combMass, sq, sum_mul, mul_sum, ← sum_add_distrib]
          exact sum_congr rfl fun p _ => sum_congr rfl fun q _ => by ring
      _ = S ^ 2 * (ε / 2) + 4 * M * T * S := by rw [hIsum]; ring
  have hS2 : 0 < S ^ 2 := by positivity
  rw [Real.dist_eq, div_sub' hS2.ne', abs_div, abs_of_pos hS2, div_lt_iff₀ hS2]
  have hTle : T ≤ ε / (16 * (M + 1)) * S := by
    rw [div_lt_iff₀ hS] at hTS; linarith
  have hfrac : M / (M + 1) ≤ 1 := by rw [div_le_one (by positivity)]; linarith
  have h4M : 4 * M * T * S ≤ ε / 4 * S ^ 2 := by
    calc 4 * M * T * S ≤ 4 * M * (ε / (16 * (M + 1)) * S) * S := by
          have := mul_le_mul_of_nonneg_left hTle (by positivity : (0 : ℝ) ≤ 4 * M)
          nlinarith
      _ = ε / 4 * S ^ 2 * (M / (M + 1)) := by field_simp; ring
      _ ≤ ε / 4 * S ^ 2 * 1 := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = ε / 4 * S ^ 2 := by ring
  refine lt_of_le_of_lt hsum ?_
  nlinarith

variable {f : ℝ → ℝ}

/-! ## Two facts about the autocorrelation -/

/-- The autocorrelation of a continuous compactly supported test is continuous. -/
theorem continuous_autoCorr (hf : Continuous f) (hfc : HasCompactSupport f) :
    Continuous (autoCorr f) := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hfc
  have hint : Integrable (fun x => C * ‖f x‖) :=
    (hf.integrable_of_hasCompactSupport hfc).norm.const_mul C
  refine continuous_of_dominated (F := fun t x => f x * f (x + t)) (bound := fun x => C * ‖f x‖)
    (fun t => (hf.mul (hf.comp (continuous_id.add continuous_const))).aestronglyMeasurable)
    (fun t => Eventually.of_forall fun x => ?_) hint
    (Eventually.of_forall fun x => continuous_const.mul (hf.comp (continuous_const.add continuous_id)))
  rw [norm_mul, mul_comm C]
  exact mul_le_mul_of_nonneg_left (hC _) (norm_nonneg _)

/-- The autocorrelation is even. -/
theorem autoCorr_neg (f : ℝ → ℝ) (t : ℝ) : autoCorr f (-t) = autoCorr f t := by
  have h := integral_add_right_eq_self (μ := volume) (fun x => f x * f (x + -t)) t
  simp only [add_neg_cancel_right] at h
  rw [autoCorr, ← h, autoCorr]
  exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)

/-! ## The slowly varying family -/

/-- The rescaled test `F_r(x) = r^{−1/2} f(x/r)`: the profile `f` spread over aperture `r` with
its mass kept. -/
def rescaledTest (f : ℝ → ℝ) (r : ℝ) (x : ℝ) : ℝ := (Real.sqrt r)⁻¹ * f (x / r)

/-- Rescaling commutes with the autocorrelation: `A_{F_r}(t) = A_f(t/r)`. -/
theorem autoCorr_rescaledTest {r : ℝ} (hr : 0 < r) (t : ℝ) :
    autoCorr (rescaledTest f r) t = autoCorr f (t / r) := by
  have hs : Real.sqrt r * Real.sqrt r = r := Real.mul_self_sqrt hr.le
  have hcomp := Measure.integral_comp_div (fun y => f y * f (y + t / r)) r
  have hinv : (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ = r⁻¹ := by rw [← mul_inv, hs]
  have hpt : ∀ x, rescaledTest f r x * rescaledTest f r (x + t) =
      r⁻¹ * ((fun y => f y * f (y + t / r)) (x / r)) := fun x => by
    simp only [rescaledTest, add_div]
    rw [← hinv]; ring
  rw [autoCorr, integral_congr_ae (Eventually.of_forall hpt), integral_const_mul, hcomp,
    abs_of_pos hr, smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul, autoCorr]

theorem continuous_rescaledTest (hf : Continuous f) (r : ℝ) : Continuous (rescaledTest f r) :=
  continuous_const.mul (hf.comp (continuous_id.div_const r))

/-- A profile supported in `[−1, 1]` gives a test supported in `[−r, r]`. -/
theorem rescaledTest_eq_zero {r : ℝ} (hr : 0 < r) (hsupp : ∀ x, 1 < |x| → f x = 0) {x : ℝ}
    (hx : r < |x|) : rescaledTest f r x = 0 := by
  have : 1 < |x / r| := by rw [abs_div, abs_of_pos hr, one_lt_div hr]; exact hx
  simp [rescaledTest, hsupp _ this]

theorem hasCompactSupport_rescaledTest {r : ℝ} (hr : 0 < r) (hfc : HasCompactSupport f) :
    HasCompactSupport (rescaledTest f r) := by
  have h1 : HasCompactSupport (fun x => f (x / r)) := by
    have := hfc.comp_homeomorph (Homeomorph.mulRight₀ r⁻¹ (inv_ne_zero hr.ne'))
    simpa [Function.comp_def, div_eq_mul_inv] using this
  exact h1.mul_left

/-! ## The universal bound -/

/-- **The universal comb bound.** `E_r(F) ≤ S_r² A_F(0)` for every continuous compactly supported
test, since `|A_F(t)| ≤ A_F(0)` and the weights are nonnegative. -/
theorem combEnergy_le_combMass_sq_mul {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F)
    (r : ℝ) :
    combEnergy F (combPrimes r) combWeight ≤ combMass r ^ 2 * autoCorr F 0 := by
  rw [combEnergy, combMass, sq, sum_mul, sum_mul]
  refine sum_le_sum fun p _ => ?_
  rw [mul_sum, sum_mul]
  refine sum_le_sum fun q _ => ?_
  have hA := (abs_le.mp (abs_autoCorr_le_autoCorr_zero hF hFc (Real.log q - Real.log p))).2
  have hw := mul_nonneg (combWeight_nonneg p) (combWeight_nonneg q)
  calc combWeight p * combWeight q * autoCorr F (Real.log q - Real.log p)
      ≤ combWeight p * combWeight q * autoCorr F 0 := mul_le_mul_of_nonneg_left hA hw
    _ = _ := by ring

/-! ## The energy of the slowly varying family -/

theorem combEnergy_rescaledTest {r : ℝ} (hr : 0 < r) :
    combEnergy (rescaledTest f r) (combPrimes r) combWeight =
      ∑ p ∈ combPrimes r, ∑ q ∈ combPrimes r,
        combWeight p * combWeight q * autoCorr f ((Real.log q - Real.log p) / r) := by
  simp only [combEnergy, autoCorr_rescaledTest hr]

/-- The energy of the family fills the universal bound: `E_r(F_r)/S_r² → A_f(0)`. -/
theorem tendsto_combEnergy_rescaledTest_div_combMass_sq (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    Tendsto (fun r => combEnergy (rescaledTest f r) (combPrimes r) combWeight / combMass r ^ 2)
      atTop (𝓝 (autoCorr f 0)) := by
  have h := tendsto_combPairAverage (abs_autoCorr_le_autoCorr_zero hf hfc)
    (continuous_autoCorr hf hfc).continuousAt
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  rw [combEnergy_rescaledTest hr]

/-- **The raw comb energy has the sharp rate `4e^{2r}`.** `E_r(F_r)/e^{2r} → 4 A_f(0)`. -/
theorem tendsto_combEnergy_rescaledTest_div_exp (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun r => combEnergy (rescaledTest f r) (combPrimes r) combWeight / Real.exp (2 * r))
      atTop (𝓝 (4 * autoCorr f 0)) := by
  have h := (tendsto_combEnergy_rescaledTest_div_combMass_sq hf hfc).mul
    (tendsto_combMass_div_exp.pow 2)
  rw [show autoCorr f 0 * 2 ^ 2 = 4 * autoCorr f 0 by ring] at h
  refine h.congr' ?_
  filter_upwards [eventually_combMass_pos] with r hr
  have he : Real.exp (2 * r) = Real.exp r ^ 2 := by rw [← Real.exp_nat_mul]; ring_nf
  rw [he, div_pow]
  field_simp

/-! ## The diagonal is polynomial -/

/-- The diagonal of the comb energy, `Σ_{p ≤ e^{2r}} w_p²`. -/
def combDiagonal (r : ℝ) : ℝ := ∑ p ∈ combPrimes r, combWeight p ^ 2

theorem combWeight_le {p : ℕ} (hp : 2 ≤ p) : combWeight p ≤ 2 * Real.log p / Real.sqrt p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  rw [combWeight, div_le_div_iff₀ (by linarith) hs]
  nlinarith [mul_nonneg hlog (by linarith : (0 : ℝ) ≤ (p : ℝ) - 2)]

/-- `Σ_{p ≤ e^{2r}} w_p² ≤ 16 r² (1 + 2r)`. -/
theorem combDiagonal_le {r : ℝ} (hr : 0 ≤ r) : combDiagonal r ≤ 16 * r ^ 2 * (1 + 2 * r) := by
  set N := ⌊Real.exp (2 * r)⌋₊
  have hN : (N : ℝ) ≤ Real.exp (2 * r) := Nat.floor_le (Real.exp_pos _).le
  have hlogN : Real.log N ≤ 2 * r := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0, Nat.cast_zero, Real.log_zero]; linarith
    · have := Real.log_le_log (by exact_mod_cast h0) hN
      rwa [Real.log_exp] at this
  have hterm : ∀ p ∈ combPrimes r, combWeight p ^ 2 ≤ 16 * r ^ 2 * (p : ℝ)⁻¹ := by
    intro p hp
    have hp2 := (mem_combPrimes.mp hp).1.two_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (show 0 < p by omega)
    have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast (show 1 ≤ p by omega))
    have hlog := log_le_of_mem_combPrimes hp
    have hw := combWeight_le hp2
    have hw0 := combWeight_nonneg p
    have hsq : (2 * Real.log p / Real.sqrt p) ^ 2 = 4 * Real.log p ^ 2 / p := by
      rw [div_pow, Real.sq_sqrt hp0.le]; ring
    calc combWeight p ^ 2 ≤ (2 * Real.log p / Real.sqrt p) ^ 2 := pow_le_pow_left₀ hw0 hw 2
      _ = 4 * Real.log p ^ 2 * (p : ℝ)⁻¹ := by rw [hsq, div_eq_mul_inv]
      _ ≤ 4 * (2 * r) ^ 2 * (p : ℝ)⁻¹ := by
          gcongr
      _ = 16 * r ^ 2 * (p : ℝ)⁻¹ := by ring
  have hsub : combPrimes r ⊆ Icc 1 N := by
    intro p hp
    obtain ⟨hpr, hle⟩ := mem_combPrimes.mp hp
    exact mem_Icc.mpr ⟨hpr.one_lt.le, Nat.le_floor hle⟩
  have hharm : ∑ i ∈ Icc 1 N, (i : ℝ)⁻¹ ≤ 1 + Real.log N := by
    have h := harmonic_le_one_add_log N
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    exact h
  calc combDiagonal r ≤ ∑ p ∈ combPrimes r, 16 * r ^ 2 * (p : ℝ)⁻¹ := sum_le_sum hterm
    _ = 16 * r ^ 2 * ∑ p ∈ combPrimes r, (p : ℝ)⁻¹ := by rw [mul_sum]
    _ ≤ 16 * r ^ 2 * ∑ i ∈ Icc 1 N, (i : ℝ)⁻¹ := by
        exact mul_le_mul_of_nonneg_left
          (sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity) (by positivity)
    _ ≤ 16 * r ^ 2 * (1 + 2 * r) := by gcongr; linarith

/-- The diagonal is negligible against `e^{2r}`. -/
theorem tendsto_combDiagonal_div_exp :
    Tendsto (fun r => combDiagonal r / Real.exp (2 * r)) atTop (𝓝 0) := by
  have h2 : Tendsto (fun r : ℝ => r ^ 2 * Real.exp (-r)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
  have h3 : Tendsto (fun r : ℝ => r ^ 3 * Real.exp (-r)) atTop (𝓝 0) :=
    Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 3
  have hmaj := (h2.const_mul 16).add (h3.const_mul 32)
  rw [mul_zero, mul_zero, add_zero] at hmaj
  refine squeeze_zero' ?_ ?_ hmaj
  · exact Eventually.of_forall fun r =>
      div_nonneg (sum_nonneg fun p _ => sq_nonneg _) (Real.exp_pos _).le
  · filter_upwards [eventually_ge_atTop 0] with r hr
    have hexp : Real.exp r ≤ Real.exp (2 * r) := Real.exp_le_exp.mpr (by linarith)
    rw [div_le_iff₀ (Real.exp_pos _)]
    have hmul : (16 * (r ^ 2 * Real.exp (-r)) + 32 * (r ^ 3 * Real.exp (-r))) * Real.exp (2 * r)
        ≥ 16 * r ^ 2 * (1 + 2 * r) := by
      have he : Real.exp (-r) * Real.exp (2 * r) = Real.exp r := by
        rw [← Real.exp_add]; ring_nf
      have hpos : 0 ≤ 16 * r ^ 2 * (1 + 2 * r) := by positivity
      have hone : 1 ≤ Real.exp r := Real.one_le_exp hr
      calc (16 * (r ^ 2 * Real.exp (-r)) + 32 * (r ^ 3 * Real.exp (-r))) * Real.exp (2 * r)
          = 16 * r ^ 2 * (1 + 2 * r) * (Real.exp (-r) * Real.exp (2 * r)) := by ring
        _ = 16 * r ^ 2 * (1 + 2 * r) * Real.exp r := by rw [he]
        _ ≥ 16 * r ^ 2 * (1 + 2 * r) * 1 := mul_le_mul_of_nonneg_left hone hpos
        _ = 16 * r ^ 2 * (1 + 2 * r) := mul_one _
    linarith [combDiagonal_le hr]

/-! ## The cross-prime aggregate -/

/-- The cross-prime aggregate `Σ_{p ≠ q ≤ e^{2r}} w_p w_q A_F(log q − log p)`. -/
def combCross (F : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∑ p ∈ combPrimes r, ∑ q ∈ (combPrimes r).erase p,
    combWeight p * combWeight q * autoCorr F (Real.log q - Real.log p)

/-- **The cross-prime aggregate is `4e^{2r}`.** On the slowly varying family the aggregate whose
nonpositivity or polynomial size the comb reduction needed is `∼ 4 e^{2r} A_f(0)`. -/
theorem tendsto_combCross_rescaledTest_div_exp (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun r => combCross (rescaledTest f r) r / Real.exp (2 * r)) atTop
      (𝓝 (4 * autoCorr f 0)) := by
  have hE := tendsto_combEnergy_rescaledTest_div_exp hf hfc
  have hD := tendsto_combDiagonal_div_exp.mul_const (autoCorr f 0)
  rw [zero_mul] at hD
  have h := hE.sub hD
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  have hsplit := combEnergy_eq_diagonal_add_cross (F := rescaledTest f r) (combPrimes r) combWeight
  rw [autoCorr_rescaledTest hr, zero_div] at hsplit
  rw [hsplit, combCross, combDiagonal]
  ring

/-! ## The first-power charge vanishes against the mass -/

/-- The first-power charge of the comb, `Σ_{p ≤ e^{2r}} w_p A_F(log p)`. -/
def combCharge (F : ℝ → ℝ) (r : ℝ) : ℝ :=
  ∑ p ∈ combPrimes r, combWeight p * autoCorr F (Real.log p)

/-- The normalized charge of the family tends to `A_f(2)`. -/
theorem tendsto_combCharge_rescaledTest_div_combMass (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    Tendsto (fun r => combCharge (rescaledTest f r) r / combMass r) atTop (𝓝 (autoCorr f 2)) := by
  have h := tendsto_combAverage (abs_autoCorr_le_autoCorr_zero hf hfc)
    (continuous_autoCorr hf hfc).continuousAt
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with r hr
  simp only [combCharge, autoCorr_rescaledTest hr]

/-- **Enormous energy, no adverse charge.** For a profile supported in `[−1, 1]` the first-power
charge is `o(S_r)`, although the comb energy is `∼ S_r² A_f(0)`. -/
theorem tendsto_combCharge_rescaledTest_div_combMass_zero (hf : Continuous f)
    (hfc : HasCompactSupport f) (hsupp : ∀ x, 1 < |x| → f x = 0) :
    Tendsto (fun r => combCharge (rescaledTest f r) r / combMass r) atTop (𝓝 0) := by
  have h0 : autoCorr f 2 = 0 :=
    autoCorr_eq_zero_of_support_le hsupp (by norm_num : (2 : ℝ) * 1 ≤ |(2 : ℝ)|)
  simpa [h0] using tendsto_combCharge_rescaledTest_div_combMass hf hfc

/-! ## The translation limit -/

/-- The normalized rescaled comb `S_r^{−1} Σ_{p ≤ e^{2r}} w_p f(· + log p/r)`. -/
def normalizedComb (f : ℝ → ℝ) (r : ℝ) : ℝ → ℝ :=
  finsetComb f (combPrimes r) (fun p => combWeight p / combMass r) (fun p => Real.log p / r)

/-- The normalized comb is the actual comb of the family, read at scale `r`:
`N_r(x) = (√r/S_r) (C_r F_r)(r x)`. -/
theorem normalizedComb_eq {r : ℝ} (hr : 0 < r) (x : ℝ) :
    normalizedComb f r x =
      Real.sqrt r / combMass r * primeComb (rescaledTest f r) (combPrimes r) combWeight (r * x) := by
  have hs : Real.sqrt r ≠ 0 := (Real.sqrt_pos.mpr hr).ne'
  simp only [normalizedComb, finsetComb, primeComb, rescaledTest, mul_sum]
  refine sum_congr rfl fun p _ => ?_
  rw [show (r * x + Real.log p) / r = x + Real.log p / r by field_simp]
  field_simp

/-- **The comb is a translation.** `‖(√r/S_r)(C_r F_r)(r ·) − f(· + 2)‖² → 0`. -/
theorem tendsto_testPairing_normalizedComb_sub_translate (hf : Continuous f)
    (hfc : HasCompactSupport f) :
    Tendsto (fun r => testPairing (fun x => normalizedComb f r x - f (x + 2))
      (fun x => normalizedComb f r x - f (x + 2))) atTop (𝓝 0) := by
  have hN : ContCompact f := ⟨hf, hfc⟩
  have hY : ContCompact (fun x => f (x + 2)) := hN.translate 2
  have hNN := tendsto_combEnergy_rescaledTest_div_combMass_sq hf hfc
  -- the cross pairing with the translate: `S_r^{−1} Σ_p w_p A_f(log p/r − 2) → A_f(0)`
  have hg : ∀ t, |autoCorr f (t - 2)| ≤ autoCorr f 0 := fun t =>
    abs_autoCorr_le_autoCorr_zero hf hfc _
  have hgc : ContinuousAt (fun t => autoCorr f (t - 2)) 2 :=
    ((continuous_autoCorr hf hfc).comp (continuous_id.sub continuous_const)).continuousAt
  have hNY := tendsto_combAverage hg hgc
  simp only [sub_self] at hNY
  have hlim := (hNN.sub (hNY.const_mul 2)).add_const (autoCorr f 0)
  rw [show autoCorr f 0 - 2 * autoCorr f 0 + autoCorr f 0 = 0 by ring] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0, eventually_combMass_pos] with r hr hS
  have hC : ContCompact (normalizedComb f r) := contCompact_finsetComb hN _ _ _
  rw [testPairing_sub_sub hC hY hC hY]
  have h1 : testPairing (normalizedComb f r) (normalizedComb f r) =
      combEnergy (rescaledTest f r) (combPrimes r) combWeight / combMass r ^ 2 := by
    rw [normalizedComb, testPairing_finsetComb hN, combEnergy_rescaledTest hr, sum_div]
    refine sum_congr rfl fun p _ => ?_
    rw [sum_div]
    refine sum_congr rfl fun q _ => ?_
    rw [← sub_div]
    field_simp
  have h2 : testPairing (fun x => f (x + 2)) (normalizedComb f r) =
      (∑ p ∈ combPrimes r, combWeight p * autoCorr f (Real.log p / r - 2)) / combMass r := by
    rw [normalizedComb, testPairing_single_finsetComb hN, sum_div]
    exact sum_congr rfl fun p _ => by ring
  have h3 : testPairing (fun x => f (x + 2)) (fun x => f (x + 2)) = autoCorr f 0 := by
    rw [testPairing_translate f f 2, testPairing_self_eq_autoCorr_zero]
  rw [h1, testPairing_comm (normalizedComb f r), h2, h3]
  ring

/-! ## An explicit smooth odd profile -/

/-- The smooth odd profile `x · e^{−1/(1 − x²)}` on `(−1, 1)`, zero outside. -/
def oddBump (x : ℝ) : ℝ := x * expNegInvGlue (1 - x ^ 2)

theorem contDiff_oddBump (n : ℕ) : ContDiff ℝ n oddBump :=
  contDiff_id.mul (expNegInvGlue.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2)))

theorem continuous_oddBump : Continuous oddBump := (contDiff_oddBump 0).continuous

theorem oddBump_neg (x : ℝ) : oddBump (-x) = -oddBump x := by
  simp [oddBump, neg_sq]

theorem oddBump_eq_zero {x : ℝ} (hx : 1 < |x|) : oddBump x = 0 := by
  have h : 1 - x ^ 2 ≤ 0 := by
    have := sq_lt_sq' (by linarith [neg_abs_le x]) hx
    nlinarith [sq_abs x]
  simp [oddBump, expNegInvGlue.zero_of_nonpos h]

theorem hasCompactSupport_oddBump : HasCompactSupport oddBump := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 1) fun x hx => oddBump_eq_zero ?_
  simpa [Metric.mem_closedBall, Real.dist_eq] using hx

theorem autoCorr_oddBump_zero_pos : 0 < autoCorr oddBump 0 := by
  have hcont : Continuous fun x => oddBump x * oddBump x :=
    continuous_oddBump.mul continuous_oddBump
  have hhalf : oddBump (1 / 2) * oddBump (1 / 2) ≠ 0 := by
    have : 0 < oddBump (1 / 2) := by
      rw [oddBump]; exact mul_pos (by norm_num) (expNegInvGlue.pos_of_pos (by norm_num))
    positivity
  have h := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume)
    hasCompactSupport_oddBump.mul_left (fun x => mul_self_nonneg _) hhalf
  simpa [autoCorr] using h

/-- The unit-mass odd profile `oddBump / √A(0)`. -/
def unitOddBump (x : ℝ) : ℝ := (Real.sqrt (autoCorr oddBump 0))⁻¹ * oddBump x

theorem autoCorr_unitOddBump (t : ℝ) :
    autoCorr unitOddBump t = (autoCorr oddBump 0)⁻¹ * autoCorr oddBump t := by
  set c := autoCorr oddBump 0
  have hs : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt autoCorr_oddBump_zero_pos.le
  have hinv : (Real.sqrt c)⁻¹ * (Real.sqrt c)⁻¹ = c⁻¹ := by rw [← mul_inv, hs]
  have hpt : ∀ x, unitOddBump x * unitOddBump (x + t) = c⁻¹ * (oddBump x * oddBump (x + t)) :=
    fun x => by simp only [unitOddBump]; rw [← hinv]; ring
  calc autoCorr unitOddBump t = ∫ x, c⁻¹ * (oddBump x * oddBump (x + t)) :=
        integral_congr_ae (Eventually.of_forall hpt)
    _ = c⁻¹ * autoCorr oddBump t := by rw [integral_const_mul]; rfl

theorem autoCorr_unitOddBump_zero : autoCorr unitOddBump 0 = 1 := by
  rw [autoCorr_unitOddBump, inv_mul_cancel₀ autoCorr_oddBump_zero_pos.ne']

theorem continuous_unitOddBump : Continuous unitOddBump :=
  continuous_const.mul continuous_oddBump

theorem hasCompactSupport_unitOddBump : HasCompactSupport unitOddBump :=
  hasCompactSupport_oddBump.mul_left

/-- **The sharp comb rate on the ledger's own test class.** The tests `F_r = rescaledTest
unitOddBump r` are smooth, odd, supported in `[−r, r]` and of unit mass; on them the raw comb energy
and the cross-prime aggregate are both `∼ 4e^{2r}`, which is the universal bound `S_r² A(0)`
asymptotically, while the first-power charge is `o(S_r)` and the normalized comb converges to the
translate of the profile by `2`. -/
theorem exists_odd_smooth_family_sharp_comb_rate :
    (∀ r : ℝ, 0 < r → (∀ n : ℕ, ContDiff ℝ n (rescaledTest unitOddBump r)) ∧
      HasCompactSupport (rescaledTest unitOddBump r) ∧
      (∀ x, rescaledTest unitOddBump r (-x) = -rescaledTest unitOddBump r x) ∧
      (∀ x, r < |x| → rescaledTest unitOddBump r x = 0) ∧
      autoCorr (rescaledTest unitOddBump r) 0 = 1) ∧
    Tendsto (fun r => combEnergy (rescaledTest unitOddBump r) (combPrimes r) combWeight /
      Real.exp (2 * r)) atTop (𝓝 4) ∧
    Tendsto (fun r => combCross (rescaledTest unitOddBump r) r / Real.exp (2 * r)) atTop (𝓝 4) ∧
    Tendsto (fun r => combCharge (rescaledTest unitOddBump r) r / combMass r) atTop (𝓝 0) ∧
    Tendsto (fun r => testPairing (fun x => normalizedComb unitOddBump r x - unitOddBump (x + 2))
      (fun x => normalizedComb unitOddBump r x - unitOddBump (x + 2))) atTop (𝓝 0) ∧
    (∀ r : ℝ, ∀ F : ℝ → ℝ, Continuous F → HasCompactSupport F →
      combEnergy F (combPrimes r) combWeight ≤ combMass r ^ 2 * autoCorr F 0) := by
  have hc := continuous_unitOddBump
  have hcs := hasCompactSupport_unitOddBump
  have hsupp : ∀ x, 1 < |x| → unitOddBump x = 0 := fun x hx => by
    simp [unitOddBump, oddBump_eq_zero hx]
  have h4 : 4 * autoCorr unitOddBump 0 = 4 := by rw [autoCorr_unitOddBump_zero, mul_one]
  refine ⟨fun r hr => ⟨fun n => ?_, hasCompactSupport_rescaledTest hr hcs, fun x => ?_,
      fun x hx => rescaledTest_eq_zero hr hsupp hx, ?_⟩, ?_, ?_,
    tendsto_combCharge_rescaledTest_div_combMass_zero hc hcs hsupp,
    tendsto_testPairing_normalizedComb_sub_translate hc hcs,
    fun r F hF hFc => combEnergy_le_combMass_sq_mul hF hFc r⟩
  · exact contDiff_const.mul (contDiff_const.mul ((contDiff_oddBump n).comp
      (contDiff_id.div_const r)))
  · simp only [rescaledTest, unitOddBump, neg_div, oddBump_neg]; ring
  · rw [autoCorr_rescaledTest hr, zero_div, autoCorr_unitOddBump_zero]
  · simpa [h4] using tendsto_combEnergy_rescaledTest_div_exp hc hcs
  · simpa [h4] using tendsto_combCross_rescaledTest_div_exp hc hcs

end GaloisForLFunctions.ArithmeticCompensationTheory
