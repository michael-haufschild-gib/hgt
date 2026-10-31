import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.WeightedBaseCollapse
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheNearGammaAndDownwardPrimeRowsCancel
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheWeilEnergiesOfTheArithmeticModes
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.EveryFiniteFlipSetHasAnExactResolutionThreshold
import GaloisForLFunctions.BezoutValuationIncidence.DilationJumpValuationClock
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanMoment
import GaloisForLFunctions.HTGeometry.FiniteShiftedHarmonicAbelBounds
import GaloisForLFunctions.SignedArithmeticHodgeTheory.OneArithmeticRemainderControlsEveryRamanujanResidual

/-!
# Ramanujan divisor means and harmonic tails

The downward divisor jet has complete-period mean `Λ(m)`. After subtracting
this mean, its normalized row is periodic with an explicit amplitude bound.
The nonpolar harmonic moment has limit `−Λ(m)/sqrt(φ(m))` and a uniform
`1/N` remainder. These equal and opposite charges retain the signed polar
cancellation in a mixed top-band witness.
-/

open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory CriticalArithmeticCorrelationTheory
  BezoutValuationIncidence ArithmeticFunction
noncomputable section


theorem ramanujanLogDivisorJet_periodic (m : ℕ) :
    Function.Periodic (ramanujanLogDivisorJet m) m := by
  intro n
  unfold ramanujanLogDivisorJet
  apply sum_congr rfl
  intro d hd
  simp only [Nat.dvd_add_left (Nat.dvd_of_mem_divisors hd)]

/-- The logarithmic divisor jet has exactly the Mangoldt mean. -/
theorem periodMean_ramanujanLogDivisorJet {m : ℕ} (hm : 0 < m) :
    (∑ n ∈ range m, ramanujanLogDivisorJet m n) / (m : ℝ) = vonMangoldt m := by
  unfold ramanujanLogDivisorJet
  rw [sum_comm, sum_div]
  calc
    _ = ∑ d ∈ m.divisors, (moebius (m / d) : ℝ) * Real.log d := by
      apply sum_congr rfl
      intro d hd
      have hd0 := Nat.pos_of_mem_divisors hd
      have hmean := periodMean_dvd_indicator hd0 (Nat.dvd_of_mem_divisors hd) hm
      have he : (∑ n ∈ range m,
          if d ∣ n then (moebius (m / d) : ℝ) * d * Real.log d else 0) =
          ((moebius (m / d) : ℝ) * d * Real.log d) *
            ∑ n ∈ range m, if d ∣ n then (1 : ℝ) else 0 := by
        rw [mul_sum]
        apply sum_congr rfl
        intro n _
        split_ifs <;> ring
      rw [he, mul_div_assoc, hmean]
      have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0.ne'
      field_simp
    _ = _ := ArithmeticEffectivityTheory.sum_divisors_moebius_log hm

/-- The centered divisor jet is periodic with zero complete-period sum. -/
theorem sum_range_centered_ramanujanLogDivisorJet {m : ℕ} (hm : 0 < m) :
    ∑ n ∈ range m, (ramanujanLogDivisorJet m n - vonMangoldt m) = 0 := by
  have h := periodMean_ramanujanLogDivisorJet hm
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [div_eq_iff hmR] at h
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul, h]
  ring

/-- The normalized nonconstant part of the downward divisor correction. -/
def centeredRamanujanJet (m n : ℕ) : ℝ :=
  (ramanujanLogDivisorJet m n - vonMangoldt m) / Real.sqrt (m.totient : ℝ)

def ramanujanJetAmplitude (m : ℕ) : ℝ :=
  (ramanujanJetBound m + vonMangoldt m) / Real.sqrt (m.totient : ℝ)

theorem centeredRamanujanJet_periodic (m : ℕ) :
    Function.Periodic (centeredRamanujanJet m) m := by
  intro n
  rw [centeredRamanujanJet, centeredRamanujanJet, ramanujanLogDivisorJet_periodic]

theorem sum_range_centeredRamanujanJet {m : ℕ} (hm : 0 < m) :
    ∑ n ∈ range m, centeredRamanujanJet m n = 0 := by
  simp only [centeredRamanujanJet, ← sum_div,
    sum_range_centered_ramanujanLogDivisorJet hm, zero_div]

theorem abs_centeredRamanujanJet_le (m n : ℕ) :
    |centeredRamanujanJet m n| ≤ ramanujanJetAmplitude m := by
  rw [centeredRamanujanJet, ramanujanJetAmplitude, abs_div,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
  calc
    _ ≤ |ramanujanLogDivisorJet m n| + |vonMangoldt m| := abs_sub _ _
    _ ≤ ramanujanJetBound m + vonMangoldt m := by
      rw [abs_of_nonneg vonMangoldt_nonneg]
      exact add_le_add (abs_ramanujanLogDivisorJet_le m n) le_rfl

/-- Below twice the horizon the only omitted divisor is the zero Mangoldt term. -/
theorem horizonDivisorCoefficient_ramanujan_eq {m ℓ N : ℕ}
    (hm : 0 < m) (hℓ : 0 < ℓ) (hℓN : ℓ ≤ 2 * N) :
    horizonDivisorCoefficient (normalizedRamanujanMode m) N ℓ =
      Real.log ℓ * normalizedRamanujanMode m ℓ -
        ramanujanLogDivisorJet m ℓ / Real.sqrt (m.totient : ℝ) := by
  have he : horizonDivisorCoefficient (normalizedRamanujanMode m) N ℓ =
      (∑ d ∈ ℓ.divisors, vonMangoldt d * ramanujanLagCoefficient m (ℓ / d)) /
        Real.sqrt (m.totient : ℝ) := by
    rw [horizonDivisorCoefficient, sum_filter, sum_div]
    apply sum_congr rfl
    intro d _
    by_cases h : ℓ / d ≤ N
    · rw [if_pos h, normalizedRamanujanMode_eq_coefficient hm]
      ring
    · rw [if_neg h]
      have hd : d < 2 := by
        by_contra hd
        have hmul := Nat.mul_le_mul_left (ℓ / d) (show 2 ≤ d by omega)
        have hdiv := Nat.div_mul_le_self ℓ d
        omega
      interval_cases d <;> simp
  rw [he, sum_vonMangoldt_mul_ramanujan_eq_log_sub_jet m hℓ,
    normalizedRamanujanMode_eq_coefficient hm]
  ring

/-- The nonpolar harmonic moment retains its finite Mangoldt limit. -/
theorem tendsto_normalizedRamanujan_harmonic {m : ℕ} (hm : 2 ≤ m) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, normalizedRamanujanMode m n / (n : ℝ))
      atTop (𝓝 (-vonMangoldt m / Real.sqrt (m.totient : ℝ))) := by
  have h := (_root_.RHTower.tendsto_pm_ramanujan_harmonic (by omega : 1 < m)).div_const
    (Real.sqrt (m.totient : ℝ))
  refine h.congr fun N => ?_
  rw [sum_div]
  apply sum_congr rfl
  intro n _
  rw [ramanujanNaturalCoefficient_re_eq_lagCoefficient,
    normalizedRamanujanMode_eq_coefficient (by omega : 0 < m)]
  ring

/-- Periodic cancellation makes the exact harmonic remainder of order `1/N`. -/
theorem abs_normalizedRamanujan_harmonic_add_vonMangoldt_le {m : ℕ}
    (hm : 2 ≤ m) (N : ℕ) :
    |(∑ n ∈ Icc 1 N, normalizedRamanujanMode m n / (n : ℝ)) +
        vonMangoldt m / Real.sqrt (m.totient : ℝ)| ≤
      2 * m * Real.sqrt (m.totient : ℝ) / ((N : ℝ) + 1) := by
  let a := normalizedRamanujanMode m
  have hm0 : 0 < m := by omega
  have hB (l k : ℕ) (hlk : l ≤ k) :
      |∑ n ∈ Ico l k, a n| ≤ 2 * m * Real.sqrt (m.totient : ℝ) := by
    have h := HTGeometry.abs_sum_Ico_le_of_periodic hm0
      (normalizedRamanujanMode_periodic hm0) (sum_range_normalizedRamanujanMode hm) l k hlk
    refine h.trans ?_
    have hsum : (∑ n ∈ range m, |normalizedRamanujanMode m n|) ≤
        m * Real.sqrt (m.totient : ℝ) := by
      calc
        _ ≤ ∑ _n ∈ range m, Real.sqrt (m.totient : ℝ) :=
          sum_le_sum fun n _ =>
            SignedArithmeticHodgeTheory.abs_normalizedRamanujanMode_le_sqrt_totient hm0 n
        _ = _ := by rw [sum_const, card_range, nsmul_eq_mul]
    linarith only [hsum]
  have htail (M : ℕ) (hNM : N ≤ M) :
      |(∑ n ∈ Icc 1 M, a n / (n : ℝ)) -
          ∑ n ∈ Icc 1 N, a n / (n : ℝ)| ≤
        2 * m * Real.sqrt (m.totient : ℝ) / ((N : ℝ) + 1) := by
    have h := HTGeometry.abs_sum_Ico_div_add_le (r := 0) hB (N + 1) (M + 1)
      (by positivity)
    have he := Finset.sum_Ico_consecutive (f := fun n => a n / (n : ℝ))
      (show 1 ≤ N + 1 by omega) (show N + 1 ≤ M + 1 by omega)
    simp only [Ico_add_one_right_eq_Icc] at he h
    have he' : (∑ n ∈ Icc 1 M, a n / (n : ℝ)) -
        ∑ n ∈ Icc 1 N, a n / (n : ℝ) =
        ∑ n ∈ Icc (N + 1) M, a n / (n : ℝ) := by linarith only [he]
    rw [he']
    simpa only [zero_add, Nat.cast_add, Nat.cast_one] using h
  have hlim := ((tendsto_normalizedRamanujan_harmonic hm).sub_const
    (∑ n ∈ Icc 1 N, a n / (n : ℝ))).abs
  have h := le_of_tendsto hlim (by
    filter_upwards [eventually_ge_atTop N] with M hNM
    exact htail M hNM)
  have he : -vonMangoldt m / Real.sqrt (m.totient : ℝ) -
      (∑ n ∈ Icc 1 N, a n / (n : ℝ)) =
      -((∑ n ∈ Icc 1 N, a n / (n : ℝ)) +
        vonMangoldt m / Real.sqrt (m.totient : ℝ)) := by ring
  rwa [he, abs_neg] at h

#print axioms ramanujanLogDivisorJet_periodic
#print axioms periodMean_ramanujanLogDivisorJet
#print axioms horizonDivisorCoefficient_ramanujan_eq
#print axioms abs_normalizedRamanujan_harmonic_add_vonMangoldt_le
end
end GaloisForLFunctions.SuccessorShellArithmetic
