import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanModesAreValuationSteps
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRamanujanPrimeRowsHaveAdjunctionEnergy
import GaloisForLFunctions.BiScaleUncertainty.SieveCoordinateSupNorm

/-!
# A uniform summable majorant for Ramanujan prime corrections

Only primes dividing the conductor can change its Ramanujan mode. Their
Mangoldt reciprocal masses are summable, uniformly in the row index.
-/

noncomputable section

open Filter Topology Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction BezoutValuationIncidence

/-- The nonnegative reciprocal Mangoldt mass on the powers of one prime. -/
def localMangoldtMass (p t : ℕ) : ℝ := if p ∣ t then Λ t / (t : ℝ) else 0

theorem localMangoldtMass_nonneg (p t : ℕ) : 0 ≤ localMangoldtMass p t := by
  unfold localMangoldtMass
  split_ifs
  · exact div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg t)
  · exact le_rfl

theorem summable_localMangoldtMass {p : ℕ} (hp : p.Prime) : Summable (localMangoldtMass p) :=
  summable_of_sum_le (localMangoldtMass_nonneg p) (sum_dvd_vonMangoldt_div_le hp)

/-- A conductor-dependent bound for every upward correction row. -/
def ramanujanCorrectionMajorant (m t : ℕ) : ℝ :=
  (2 * (m.totient : ℝ)) * ∑ p ∈ m.primeFactors, localMangoldtMass p t

theorem ramanujanCorrectionMajorant_nonneg (m t : ℕ) :
    0 ≤ ramanujanCorrectionMajorant m t := by
  exact mul_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    (sum_nonneg fun p _ => localMangoldtMass_nonneg p t)

theorem summable_ramanujanCorrectionMajorant (m : ℕ) :
    Summable (ramanujanCorrectionMajorant m) := by
  have hsum := hasSum_sum (s := m.primeFactors) fun p hp =>
    (summable_localMangoldtMass (Nat.prime_of_mem_primeFactors hp)).hasSum
  exact hsum.summable.mul_left (2 * (m.totient : ℝ))

/-- Every row has the same summable majorant; coprime prime jumps contribute zero. -/
theorem abs_ramanujan_up_difference_le {m : ℕ} (hm : 0 < m) (n t : ℕ) :
    |(ramanujanLagCoefficient m (n * t) - ramanujanLagCoefficient m n) * Λ t / (t : ℝ)| ≤
      ramanujanCorrectionMajorant m t := by
  by_cases hΛ : Λ t = 0
  · rw [hΛ, mul_zero, zero_div, abs_zero]
    exact ramanujanCorrectionMajorant_nonneg m t
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff t).mp (vonMangoldt_ne_zero_iff.mp hΛ)
  by_cases hpm : p ∣ m
  · have hmem : p ∈ m.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpm, hm.ne'⟩
    have hdelta : |ramanujanLagCoefficient m (n * p ^ k) - ramanujanLagCoefficient m n| ≤
        2 * (m.totient : ℝ) := by
      calc
        _ ≤ |ramanujanLagCoefficient m (n * p ^ k)| + |ramanujanLagCoefficient m n| :=
          abs_sub _ _
        _ ≤ (m.totient : ℝ) + (m.totient : ℝ) := add_le_add
          (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m _)
          (BiScaleUncertainty.SieveMoments.abs_ramanujanLagCoefficient_le_totient m _)
        _ = _ := by ring
    have hweight : Λ (p ^ k) / ((p ^ k : ℕ) : ℝ) ≤
        ∑ q ∈ m.primeFactors, localMangoldtMass q (p ^ k) := by
      have h := single_le_sum (fun q _ => localMangoldtMass_nonneg q (p ^ k)) hmem
      simpa only [localMangoldtMass, if_pos (dvd_pow_self p hk.ne')] using h
    calc
      _ = |ramanujanLagCoefficient m (n * p ^ k) - ramanujanLagCoefficient m n| *
          (Λ (p ^ k) / ((p ^ k : ℕ) : ℝ)) := by
        rw [abs_div, abs_mul,
          abs_of_nonneg (show 0 ≤ Λ (p ^ k) from vonMangoldt_nonneg),
          abs_of_nonneg (show 0 ≤ ((p ^ k : ℕ) : ℝ) from Nat.cast_nonneg _)]
        ring
      _ ≤ (2 * (m.totient : ℝ)) * (Λ (p ^ k) / ((p ^ k : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hdelta (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg _))
      _ ≤ ramanujanCorrectionMajorant m (p ^ k) :=
        mul_le_mul_of_nonneg_left hweight (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  · have hmp : m.Coprime p := (hp.coprime_iff_not_dvd.mpr hpm).symm
    rw [ramanujanCoefficient_mul_lag_of_coprime (hmp.pow_right k), sub_self,
      zero_mul, zero_div, abs_zero]
    exact ramanujanCorrectionMajorant_nonneg m _

theorem summable_ramanujan_up_difference {m : ℕ} (hm : 0 < m) (n : ℕ) :
    Summable (fun t : ℕ =>
      (ramanujanLagCoefficient m (n * t) - ramanujanLagCoefficient m n) * Λ t / (t : ℝ)) := by
  exact Summable.of_norm_bounded (summable_ramanujanCorrectionMajorant m)
    (fun t => by simpa only [Real.norm_eq_abs] using abs_ramanujan_up_difference_le hm n t)

/-- The remaining majorant mass after the inclusive horizon. -/
def ramanujanCorrectionTail (m N : ℕ) : ℝ :=
  (∑' t, ramanujanCorrectionMajorant m t) -
    ∑ t ∈ range (N + 1), ramanujanCorrectionMajorant m t

theorem ramanujanCorrectionTail_nonneg (m N : ℕ) : 0 ≤ ramanujanCorrectionTail m N := by
  exact sub_nonneg.mpr ((summable_ramanujanCorrectionMajorant m).sum_le_tsum _
    (fun t _ => ramanujanCorrectionMajorant_nonneg m t))

/-- The common row-error tail vanishes as the complementary horizon grows. -/
theorem tendsto_ramanujanCorrectionTail (m : ℕ) :
    Tendsto (ramanujanCorrectionTail m) atTop (𝓝 0) := by
  change Tendsto (fun N : ℕ => (∑' t, ramanujanCorrectionMajorant m t) -
    ∑ t ∈ range (N + 1), ramanujanCorrectionMajorant m t) atTop (𝓝 0)
  have hsum := (summable_ramanujanCorrectionMajorant m).hasSum.tendsto_sum_nat
  have hshift := (tendsto_add_atTop_iff_nat 1).mpr hsum
  simpa only [sub_self] using
    hshift.const_sub (∑' t, ramanujanCorrectionMajorant m t)

/-- The exact completed row and the uniform majorant control every truncated correction. -/
theorem abs_ramanujan_correction_error_le_tail {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) (N : ℕ) :
    |(∑ t ∈ Icc 1 N, ramanujanUpCorrectionTerm m n t) +
      (Real.log m + ArithmeticIntersectionTheory.tameDifferent m) * ramanujanLagCoefficient m n +
        ramanujanDownCorrection m n| ≤ ramanujanCorrectionTail m N := by
  have hw := summable_ramanujanCorrectionMajorant m
  have hs := hasSum_ramanujan_correction m hm n hn
  have hprefix : (∑ t ∈ range (N + 1), ramanujanUpCorrectionTerm m n t) =
      ∑ t ∈ Icc 1 N, ramanujanUpCorrectionTerm m n t := by
    have hset : range (N + 1) = insert 0 (Icc 1 N) := by
      ext t
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    rw [hset, sum_insert (by simp)]
    simp only [ramanujanUpCorrectionTerm, Nat.cast_zero, div_zero, zero_add]
  have hminus0 (t : ℕ) : 0 ≤ ramanujanCorrectionMajorant m t - ramanujanUpCorrectionTerm m n t :=
    sub_nonneg.mpr ((le_abs_self _).trans (abs_ramanujan_up_difference_le hm n t))
  have hplus0 (t : ℕ) : 0 ≤ ramanujanCorrectionMajorant m t + ramanujanUpCorrectionTerm m n t := by
    have h := (abs_le.mp (abs_ramanujan_up_difference_le hm n t)).1
    change -ramanujanCorrectionMajorant m t ≤ ramanujanUpCorrectionTerm m n t at h
    linarith only [h]
  have hminus := (hw.hasSum.sub hs).summable.sum_le_tsum (range (N + 1)) (fun t _ => hminus0 t)
  have hplus := (hw.hasSum.add hs).summable.sum_le_tsum (range (N + 1)) (fun t _ => hplus0 t)
  rw [(hw.hasSum.sub hs).tsum_eq] at hminus
  rw [(hw.hasSum.add hs).tsum_eq] at hplus
  simp only [sum_sub_distrib, sum_add_distrib, hprefix] at hminus hplus
  unfold ramanujanCorrectionTail
  exact abs_le.mpr ⟨by linarith only [hminus], by linarith only [hplus]⟩

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

