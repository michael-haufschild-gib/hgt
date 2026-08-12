import GaloisForLFunctions.RHTower.Sieve.VinogradovReciprocalApproximation
import GaloisForLFunctions.RHTower.Sieve.VinogradovUsefulCoordinates
import GaloisForLFunctions.RHTower.Sieve.VinogradovRouteTBilinear

namespace RHTower.Sieve

noncomputable section

/-- Magnitude of the degree-`j+1` Taylor coefficient of
`(t/2π) log x`. -/
def logTaylorMagnitude {k : ℕ} (t x : ℝ) (j : Fin k) : ℝ :=
  t / (2 * Real.pi * (j.val + 1) * x ^ (j.val + 1))

theorem logTaylorMagnitude_pos
    {k : ℕ} {t x : ℝ} (ht : 0 < t) (hx : 0 < x) (j : Fin k) :
    0 < logTaylorMagnitude t x j := by
  unfold logTaylorMagnitude
  positivity

/-- Simultaneous reduced reciprocal-scale approximants for every
logarithmic Taylor coefficient.  Simultaneity costs nothing because the
coordinates are chosen independently, as in MV24.11. -/
theorem exists_logTaylor_rationalApproximants
    {k : ℕ} {t x : ℝ} (ht : 0 < t) (hx : 0 < x) :
    ∃ a q : Fin k → ℕ, ∀ j,
      0 < q j ∧ Nat.Coprime (a j) (q j) ∧
      |logTaylorMagnitude t x j - (a j : ℝ) / (q j : ℝ)| ≤
        1 / (q j : ℝ) ^ 2 ∧
      1 / logTaylorMagnitude t x j - 1 / 2 ≤ (q j : ℝ) ∧
      (q j : ℝ) < 2 / logTaylorMagnitude t x j + 1 := by
  have hpoint : ∀ j : Fin k, ∃ a q : ℕ,
      0 < q ∧ Nat.Coprime a q ∧
      |logTaylorMagnitude t x j - (a : ℝ) / (q : ℝ)| ≤
        1 / (q : ℝ) ^ 2 ∧
      1 / logTaylorMagnitude t x j - 1 / 2 ≤ (q : ℝ) ∧
      (q : ℝ) < 2 / logTaylorMagnitude t x j + 1 := by
    intro j
    exact exists_reciprocal_rational_approximation
      (logTaylorMagnitude_pos ht hx j)
  choose a q hdata using hpoint
  exact ⟨a, q, hdata⟩

theorem vinogradovCoordinateSavingExponent_le_degree
    {k : ℕ} (j : Fin k) :
    vinogradovCoordinateSavingExponent j ≤ j.val + 1 := by
  unfold vinogradovCoordinateSavingExponent
  exact Nat.div_le_self _ _

/-- Denominator-window producer.  It turns the reciprocal size window
for logarithmic Taylor coefficients into exactly the two natural-number
inequalities consumed by the finite Route-T bridge. -/
theorem exists_logTaylor_rationalApproximants_in_window
    {k P : ℕ} {t x : ℝ} (ht : 0 < t) (hx : 0 < x)
    (U : Fin k → Prop)
    (hlower : ∀ j, U j →
      ((P ^ (2 * vinogradovCoordinateSavingExponent j) : ℕ) : ℝ) + 1 / 2 ≤
        1 / logTaylorMagnitude t x j)
    (hupper : ∀ j, U j →
      2 / logTaylorMagnitude t x j + 1 ≤
        ((P ^ (2 * ((j.val + 1) -
          vinogradovCoordinateSavingExponent j)) : ℕ) : ℝ)) :
    ∃ a q : Fin k → ℕ,
      (∀ j, U j → 0 < q j) ∧
      (∀ j, U j → Nat.Coprime (a j) (q j)) ∧
      (∀ j, U j →
        |logTaylorMagnitude t x j - (a j : ℝ) / (q j : ℝ)| ≤
          1 / (q j : ℝ) ^ 2) ∧
      (∀ j, U j →
        P ^ (2 * vinogradovCoordinateSavingExponent j) ≤ q j) ∧
      (∀ j, U j →
        q j * P ^ (2 * vinogradovCoordinateSavingExponent j) ≤
          (P ^ (j.val + 1)) ^ 2) := by
  obtain ⟨a, q, hdata⟩ := exists_logTaylor_rationalApproximants ht hx
  refine ⟨a, q, ?_, ?_, ?_, ?_, ?_⟩
  · intro j _
    exact (hdata j).1
  · intro j _
    exact (hdata j).2.1
  · intro j _
    exact (hdata j).2.2.1
  · intro j hj
    have hlow := (hdata j).2.2.2.1
    have hreal :
        ((P ^ (2 * vinogradovCoordinateSavingExponent j) : ℕ) : ℝ) ≤
          (q j : ℝ) := by
      linarith [hlower j hj]
    exact_mod_cast hreal
  · intro j hj
    let e := vinogradovCoordinateSavingExponent j
    let d := j.val + 1
    have hed : e ≤ d := vinogradovCoordinateSavingExponent_le_degree j
    have hupp := (hdata j).2.2.2.2
    have hqpowReal :
        (q j : ℝ) < ((P ^ (2 * (d - e)) : ℕ) : ℝ) :=
      hupp.trans_le (hupper j hj)
    have hqpow : q j ≤ P ^ (2 * (d - e)) := by
      exact Nat.le_of_lt (by exact_mod_cast hqpowReal)
    calc
      q j * P ^ (2 * e) ≤ P ^ (2 * (d - e)) * P ^ (2 * e) :=
        Nat.mul_le_mul_right _ hqpow
      _ = P ^ (2 * d) := by
        rw [← pow_add]
        congr 1
        omega
      _ = (P ^ d) ^ 2 := by rw [← pow_mul]; congr 1; omega

/-- A polynomial denominator window makes the explicit large-sieve
logarithm only linear in `P`. -/
theorem one_add_log_denominator_le_linear
    {P q d : ℕ} (hP : 1 ≤ P) (hd : 1 ≤ d)
    (hq : q ≤ P ^ (2 * d)) :
    1 + Real.log ((q : ℝ) + 1) ≤ 5 * (d : ℝ) * P := by
  have hpow : 1 ≤ P ^ (2 * d) := one_le_pow₀ hP
  have hqadd : q + 1 ≤ 2 * P ^ (2 * d) := by omega
  have hlogmono :
      Real.log ((q : ℝ) + 1) ≤
        Real.log ((2 * P ^ (2 * d) : ℕ) : ℝ) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast hqadd)
  have hlogexpand :
      Real.log ((2 * P ^ (2 * d) : ℕ) : ℝ) =
        Real.log 2 + (2 * d : ℕ) * Real.log (P : ℝ) := by
    push_cast
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    norm_num
  have hlogtwo : Real.log 2 ≤ 2 := Real.log_le_self (by norm_num)
  have hlogP : Real.log (P : ℝ) ≤ P := Real.log_le_self (by positivity)
  rw [hlogexpand] at hlogmono
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hPR : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have hdP : (1 : ℝ) ≤ (d : ℝ) * P := by nlinarith
  have htwoD : (0 : ℝ) ≤ (2 * d : ℕ) := by positivity
  have hterm : ((2 * d : ℕ) : ℝ) * Real.log (P : ℝ) ≤
      ((2 * d : ℕ) : ℝ) * (P : ℝ) :=
    mul_le_mul_of_nonneg_left hlogP htwoD
  calc
    1 + Real.log ((q : ℝ) + 1) ≤
        1 + (Real.log 2 + (2 * d : ℕ) * Real.log (P : ℝ)) := by linarith
    _ ≤ 3 + (2 * d : ℕ) * (P : ℝ) := by
      linarith
    _ ≤ 5 * (d : ℝ) * P := by
      push_cast
      nlinarith

/-- Explicit absorption threshold for the one-log loss in the formal
large-sieve block estimate. -/
theorem vinogradov_largeSieveLog_absorbed
    {P b q k : ℕ} (hP : 1 ≤ P)
    (hthreshold : 160 * b ^ 2 * k ≤ P)
    (j : Fin k) (he : 2 ≤ vinogradovCoordinateSavingExponent j)
    (hq : q ≤ P ^ (2 * (j.val + 1))) :
    32 * (b : ℝ) ^ 2 * (1 + Real.log ((q : ℝ) + 1)) ≤
      (P : ℝ) ^ vinogradovCoordinateSavingExponent j := by
  let e := vinogradovCoordinateSavingExponent j
  let d := j.val + 1
  have hlog := one_add_log_denominator_le_linear hP (by omega : 1 ≤ d) hq
  have hleft :
      32 * (b : ℝ) ^ 2 * (1 + Real.log ((q : ℝ) + 1)) ≤
        160 * (b : ℝ) ^ 2 * d * P := by
    calc
      _ ≤ 32 * (b : ℝ) ^ 2 * (5 * (d : ℝ) * P) := by
        gcongr
      _ = 160 * (b : ℝ) ^ 2 * d * P := by ring
  have hdle : d ≤ k := by unfold d; omega
  have hthresholdReal : 160 * (b : ℝ) ^ 2 * k ≤ P := by
    exact_mod_cast hthreshold
  have hlinear : 160 * (b : ℝ) ^ 2 * d * P ≤ (P : ℝ) ^ 2 := by
    have hdReal : (d : ℝ) ≤ k := by exact_mod_cast hdle
    have hscale : 160 * (b : ℝ) ^ 2 * d ≤ P := by
      nlinarith [sq_nonneg (b : ℝ)]
    nlinarith
  have hpower : (P : ℝ) ^ 2 ≤ (P : ℝ) ^ e :=
    pow_le_pow_right₀ (by exact_mod_cast hP) he
  exact hleft.trans (hlinear.trans hpower)

/-- Complete Route-T denominator producer for logarithmic Taylor
coefficients, including the explicit large-sieve logarithm. -/
theorem exists_routeT_logTaylor_approximants
    {u P : ℕ} {t x : ℝ} (hu : 141 ≤ u) (ht : 0 < t) (hx : 0 < x)
    (hthreshold :
      160 * vinogradovRouteTMoment (4 * u) ^ 2 *
          vinogradovRouteTOrder (4 * u) ≤ P)
    (hlower : ∀ j : Fin (vinogradovRouteTOrder (4 * u)),
      vinogradovUsefulCoordinate u j →
      ((P ^ (2 * vinogradovCoordinateSavingExponent j) : ℕ) : ℝ) + 1 / 2 ≤
        1 / logTaylorMagnitude t x j)
    (hupper : ∀ j : Fin (vinogradovRouteTOrder (4 * u)),
      vinogradovUsefulCoordinate u j →
      2 / logTaylorMagnitude t x j + 1 ≤
        ((P ^ (2 * ((j.val + 1) -
          vinogradovCoordinateSavingExponent j)) : ℕ) : ℝ)) :
    ∃ a q : Fin (vinogradovRouteTOrder (4 * u)) → ℕ,
      (∀ j, vinogradovUsefulCoordinate u j → 0 < q j) ∧
      (∀ j, vinogradovUsefulCoordinate u j → Nat.Coprime (a j) (q j)) ∧
      (∀ j, vinogradovUsefulCoordinate u j →
        |logTaylorMagnitude t x j - (a j : ℝ) / (q j : ℝ)| ≤
          1 / (q j : ℝ) ^ 2) ∧
      (∀ j, vinogradovUsefulCoordinate u j →
        P ^ (2 * vinogradovCoordinateSavingExponent j) ≤ q j) ∧
      (∀ j, vinogradovUsefulCoordinate u j →
        q j * P ^ (2 * vinogradovCoordinateSavingExponent j) ≤
          (P ^ (j.val + 1)) ^ 2) ∧
      (∀ j, vinogradovUsefulCoordinate u j →
        32 * (vinogradovRouteTMoment (4 * u) : ℝ) ^ 2 *
            (1 + Real.log ((q j : ℝ) + 1)) ≤
          (P : ℝ) ^ vinogradovCoordinateSavingExponent j) := by
  let k := vinogradovRouteTOrder (4 * u)
  let b := vinogradovRouteTMoment (4 * u)
  have hb : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr
    (vinogradovRouteTMoment_ne_zero (by omega))
  have hk : 1 ≤ k := by unfold k vinogradovRouteTOrder; omega
  have hfactor : 1 ≤ 160 * b ^ 2 * k := by nlinarith
  have hP : 1 ≤ P := hfactor.trans (by simpa [b, k] using hthreshold)
  obtain ⟨a, q, hq, hcop, happrox, hRq, hqR⟩ :=
    exists_logTaylor_rationalApproximants_in_window ht hx
      (vinogradovUsefulCoordinate u) hlower hupper
  refine ⟨a, q, hq, hcop, happrox, hRq, hqR, ?_⟩
  intro j hj
  let e := vinogradovCoordinateSavingExponent j
  let d := j.val + 1
  have hpowOne : 1 ≤ P ^ (2 * e) := one_le_pow₀ hP
  have hqNatural : q j ≤ q j * P ^ (2 * e) := by
    simpa only [mul_one] using Nat.mul_le_mul_left (q j) hpowOne
  have hqPower : q j ≤ P ^ (2 * d) := by
    calc
      q j ≤ q j * P ^ (2 * e) := hqNatural
      _ ≤ (P ^ d) ^ 2 := hqR j hj
      _ = P ^ (2 * d) := by rw [← pow_mul]; congr 1; omega
  have heU : u ≤ e := by
    exact vinogradovCoordinateSavingExponent_ge u ⟨j, hj⟩
  have heTwo : 2 ≤ e := by omega
  exact vinogradov_largeSieveLog_absorbed hP
    (by simpa [b, k] using hthreshold) j heTwo (by simpa [d] using hqPower)

end

end RHTower.Sieve
