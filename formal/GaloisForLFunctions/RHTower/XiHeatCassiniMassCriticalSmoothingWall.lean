import GaloisForLFunctions.HTGeometry.CompactTailDensePrimeShiftJet
import GaloisForLFunctions.RHTower.XiHeatCassiniReflectedPhaseSourceJet
import GaloisForLFunctions.RHTower.XiMassValuationOnePrimeQuotient

/-!
# Compact-smoothing wall between Cassini Fisher energy and the Route-T prime current

The depth-one BV--Wold coefficient is not the critical half-density coefficient carried by the
Route-T valuation-one mass current.  It is that coefficient after diagonal multiplication by

`κ(p)=(1-1/p)^3/sqrt(p)`.

The multiplier is positive but tends to zero along ordinary primes.  Consequently the Wold vector
is square summable while the unsmoothed critical prime vector is not, and no positive lower frame
bound can recover the Route-T current from Cassini Fisher energy.  This is the exact functional-
analytic reason the new positive receiver cannot close the timelike/glancing producer frontier.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Scalar coefficient of one valuation-one Route-T critical prime atom. -/
def xiMassValuationOneCriticalCoefficient (p : Nat.Primes) : ℝ :=
  Real.log (p : ℝ) / Real.sqrt (p : ℝ)

/-- Diagonal smoothing which turns the Route-T critical prime coefficient into the Wold
depth-one coefficient. -/
def xiHeatCassiniWoldCriticalSmoothingMultiplier (p : Nat.Primes) : ℝ :=
  (1 - 1 / (p : ℝ)) ^ 3 / Real.sqrt (p : ℝ)

/-- The coefficient used by the Route-T mass current is exactly the critical half-density
coefficient above. -/
theorem criticalMellinAtomWeight_prime_eq_xiMassValuationOneCriticalCoefficient
    (p : Nat.Primes) :
    criticalMellinAtomWeight (p : ℕ) =
      xiMassValuationOneCriticalCoefficient p := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  rw [criticalMellinAtomWeight,
    ArithmeticFunction.vonMangoldt_apply_prime p.2]
  unfold xiMassValuationOneCriticalCoefficient
  have hrpow : ((p : ℝ) ^ (-1 / 2 : ℝ)) = 1 / Real.sqrt (p : ℝ) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
      Real.rpow_neg hp.le, ← Real.sqrt_eq_rpow]
    simp only [one_div]
  rw [hrpow]
  ring

/-- Exact compact diagonal factorization of depth-one Wold data through the Route-T coefficient. -/
theorem woldCoeff_one_eq_smoothing_mul_criticalCoefficient
    (p : Nat.Primes) :
    woldCoeff 1 p =
      xiHeatCassiniWoldCriticalSmoothingMultiplier p *
        xiMassValuationOneCriticalCoefficient p := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hs : 0 < Real.sqrt (p : ℝ) := Real.sqrt_pos.mpr hp
  rw [woldCoeff]
  simp only [pow_one]
  unfold xiHeatCassiniWoldCriticalSmoothingMultiplier
    xiMassValuationOneCriticalCoefficient
  calc
    (1 - 1 / (p : ℝ)) ^ 3 * Real.log (p : ℝ) / (p : ℝ) =
        (1 - 1 / (p : ℝ)) ^ 3 * Real.log (p : ℝ) /
          (Real.sqrt (p : ℝ) * Real.sqrt (p : ℝ)) := by
            rw [Real.mul_self_sqrt hp.le]
    _ = ((1 - 1 / (p : ℝ)) ^ 3 / Real.sqrt (p : ℝ)) *
          (Real.log (p : ℝ) / Real.sqrt (p : ℝ)) := by
            field_simp [hs.ne']

/-- Smoothing multiplier is strictly positive at every ordinary prime. -/
theorem xiHeatCassiniWoldCriticalSmoothingMultiplier_pos
    (p : Nat.Primes) :
    0 < xiHeatCassiniWoldCriticalSmoothingMultiplier p := by
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hfac : 0 < 1 - 1 / (p : ℝ) := by
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := two_le_prime_cast p
    rw [sub_pos, div_lt_one hp]
    linarith
  unfold xiHeatCassiniWoldCriticalSmoothingMultiplier
  exact div_pos (pow_pos hfac 3) (Real.sqrt_pos.mpr hp)

/-- The Wold/Cassini diagonal multiplier vanishes cofinally along ordinary primes. -/
theorem tendsto_xiHeatCassiniWoldCriticalSmoothingMultiplier_cofinite_zero :
    Tendsto xiHeatCassiniWoldCriticalSmoothingMultiplier cofinite (𝓝 0) := by
  have hp : Tendsto (fun p : Nat.Primes => (p : ℝ)) cofinite atTop :=
    GaloisForLFunctions.HTGeometry.tendsto_primeReal_cofinite_atTop
  have hinv : Tendsto (fun p : Nat.Primes => ((p : ℝ))⁻¹) cofinite (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hp
  have hfactor : Tendsto (fun p : Nat.Primes => (1 - ((p : ℝ))⁻¹) ^ 3)
      cofinite (𝓝 ((1 - 0) ^ 3)) :=
    ((tendsto_const_nhds.sub hinv).pow 3)
  have hsqrt : Tendsto (fun p : Nat.Primes => Real.sqrt (p : ℝ))
      cofinite atTop := Real.tendsto_sqrt_atTop.comp hp
  have hsqrtInv : Tendsto (fun p : Nat.Primes => (Real.sqrt (p : ℝ))⁻¹)
      cofinite (𝓝 0) := tendsto_inv_atTop_zero.comp hsqrt
  rw [show xiHeatCassiniWoldCriticalSmoothingMultiplier =
      fun p : Nat.Primes =>
        (1 - ((p : ℝ))⁻¹) ^ 3 * (Real.sqrt (p : ℝ))⁻¹ by
    funext p
    simp only [xiHeatCassiniWoldCriticalSmoothingMultiplier,
      div_eq_mul_inv, one_mul]]
  simpa using hfactor.mul hsqrtInv

/-- No positive lower frame bound survives: arbitrarily remote prime coordinates are attenuated
below any prescribed positive scale. -/
theorem exists_smoothingMultiplier_lt
    {c : ℝ} (hc : 0 < c) :
    ∃ p : Nat.Primes, xiHeatCassiniWoldCriticalSmoothingMultiplier p < c := by
  have hevent : ∀ᶠ p : Nat.Primes in cofinite,
      xiHeatCassiniWoldCriticalSmoothingMultiplier p < c :=
    (tendsto_order.1
      tendsto_xiHeatCassiniWoldCriticalSmoothingMultiplier_cofinite_zero).2 c hc
  exact hevent.exists

/-- Critical half-density coefficient has exact squared profile `log(p)^2/p`. -/
theorem xiMassValuationOneCriticalCoefficient_sq
    (p : Nat.Primes) :
    xiMassValuationOneCriticalCoefficient p ^ 2 =
      Real.log (p : ℝ) ^ 2 / (p : ℝ) := by
  have hp : 0 ≤ (p : ℝ) := by positivity
  rw [xiMassValuationOneCriticalCoefficient, div_pow,
    Real.sq_sqrt hp]

/-- The unsmoothed Route-T critical valuation-one coefficient is not square summable. -/
theorem not_summable_xiMassValuationOneCriticalCoefficient_sq :
    ¬ Summable (fun p : Nat.Primes =>
      xiMassValuationOneCriticalCoefficient p ^ 2) := by
  intro hsum
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlow : ∀ p : Nat.Primes,
      Real.log 2 ^ 2 * (1 / (p : ℝ)) ≤
        xiMassValuationOneCriticalCoefficient p ^ 2 := by
    intro p
    have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := two_le_prime_cast p
    have hlog : Real.log 2 ≤ Real.log (p : ℝ) :=
      Real.log_le_log (by norm_num) hp2
    have hsq : Real.log 2 ^ 2 ≤ Real.log (p : ℝ) ^ 2 :=
      (sq_le_sq₀ hlog2.le (hlog2.le.trans hlog)).2 hlog
    rw [xiMassValuationOneCriticalCoefficient_sq]
    calc
      Real.log 2 ^ 2 * (1 / (p : ℝ)) =
          Real.log 2 ^ 2 / (p : ℝ) := by ring
      _ ≤ Real.log (p : ℝ) ^ 2 / (p : ℝ) :=
        div_le_div_of_nonneg_right hsq hp.le
  have hscaled : Summable (fun p : Nat.Primes =>
      Real.log 2 ^ 2 * (1 / (p : ℝ))) :=
    Summable.of_nonneg_of_le (fun p => by positivity) hlow hsum
  have hone : Summable (fun p : Nat.Primes => 1 / (p : ℝ)) :=
    (summable_mul_left_iff (sq_pos_of_pos hlog2).ne').1 hscaled
  exact Nat.Primes.not_summable_one_div hone

/-- In contrast, the compactly smoothed Wold coefficient is square summable. -/
theorem summable_woldCoeff_one_sq_again :
    Summable (fun p : Nat.Primes => woldCoeff 1 p ^ 2) :=
  summable_woldCoeff_one_sq

/-- **No-coercivity wall.**  There is no positive constant lower-bounding Wold energy coordinate
by the unsmoothed Route-T critical coordinate at every prime. -/
theorem no_uniform_positive_wold_to_routeTCritical_lower_bound :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ p : Nat.Primes,
      c * xiMassValuationOneCriticalCoefficient p ≤ woldCoeff 1 p := by
  rintro ⟨c, hc, hbound⟩
  obtain ⟨p, hpSmall⟩ := exists_smoothingMultiplier_lt hc
  have hp : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hcrit : 0 < xiMassValuationOneCriticalCoefficient p := by
    exact div_pos (log_prime_pos p) (Real.sqrt_pos.mpr hp)
  have hfac := hbound p
  rw [woldCoeff_one_eq_smoothing_mul_criticalCoefficient] at hfac
  exact (not_lt_of_ge hfac) (mul_lt_mul_of_pos_right hpSmall hcrit)

end

end RHTower
