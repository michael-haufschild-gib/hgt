import GaloisForLFunctions.SuccessorShellArithmetic.TopBand.RamanujanDivisorSpectrum
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheDifferentOfATorsionOrbit

/-!
# Complete-period Plancherel for the logarithmic divisor jet

The exact conductor expansion and Ramanujan orthogonality identify the jet's
quadratic mass with a finite prime-power divisor sum. The normalized centered
jet has mean square at most twice the square of the conductor logarithm.
Cauchy–Schwarz gives period absolute-mass bounds for both the jet and the
normalized Ramanujan mode.
-/

open Finset ArithmeticFunction
namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory ArithmeticIntersectionTheory RenormalizedBiarithmeticGeometry
noncomputable section


theorem sum_range_ramanujanLagCoefficient_mul {k l q : ℕ}
    (hk : 0 < k) (hl : 0 < l) (hkq : k ∣ q) (hlq : l ∣ q) :
    ∑ n ∈ range q, ramanujanLagCoefficient k n * ramanujanLagCoefficient l n =
      if k = l then (q : ℝ) * l.totient else 0 := by
  simpa only [TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hk,
    TransThresholdPairCorrelation.ramanujanMode_eq_ramanujanLagCoefficient hl] using
    sum_ramanujanMode_mul hk hl hkq hlq

private theorem sum_sq_packet_eq_gram (S : Finset ℕ) (b : ℕ → ℝ)
    (f : ℕ → ℕ → ℝ) (q : ℕ) :
    (∑ n ∈ range q, (∑ k ∈ S, b k * f k n) ^ 2) =
      ∑ k ∈ S, ∑ l ∈ S, b k * b l * (∑ n ∈ range q, f k n * f l n) := by
  calc
    _ = ∑ n ∈ range q, ∑ k ∈ S, ∑ l ∈ S, b k * b l * (f k n * f l n) := by
      apply sum_congr rfl
      intro n _
      rw [pow_two, sum_mul]
      apply sum_congr rfl
      intro k _
      rw [mul_sum]
      apply sum_congr rfl
      intro l _
      ring
    _ = ∑ k ∈ S, ∑ l ∈ S, ∑ n ∈ range q, b k * b l * (f k n * f l n) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro k _
      rw [sum_comm]
    _ = _ := by simp only [mul_sum]

/-- Exact Plancherel for any finite conductor packet over a common period. -/
theorem sum_range_ramanujan_packet_sq (S : Finset ℕ) (b : ℕ → ℝ) (q : ℕ)
    (hS : ∀ k ∈ S, 0 < k) (hSq : ∀ k ∈ S, k ∣ q) :
    (∑ n ∈ range q, (∑ k ∈ S, b k * ramanujanLagCoefficient k n) ^ 2) =
      (q : ℝ) * ∑ k ∈ S, b k ^ 2 * k.totient := by
  rw [sum_sq_packet_eq_gram, mul_sum]
  apply sum_congr rfl
  intro k hk
  calc
    _ = ∑ l ∈ S, if l = k then (q : ℝ) * (b k ^ 2 * k.totient) else 0 := by
      apply sum_congr rfl
      intro l hl
      rw [sum_range_ramanujanLagCoefficient_mul (hS k hk) (hS l hl) (hSq k hk) (hSq l hl)]
      by_cases hlk : l = k
      · subst l
        simp only [ite_true]
        ring
      · simp only [if_neg hlk, if_neg (Ne.symm hlk), mul_zero]
    _ = _ := by rw [sum_ite_eq', if_pos hk]

/-- The coefficient of each conductor in the divisor jet. -/
def ramanujanJetConductorWeight (m k : ℕ) : ℝ :=
  (if k = m then Real.log m else 0) + vonMangoldt (m / k)

theorem ramanujanJetConductorWeight_nonneg (m k : ℕ) :
    0 ≤ ramanujanJetConductorWeight m k := by
  have hlog := Real.log_natCast_nonneg m
  have hΛ : 0 ≤ vonMangoldt (m / k) := vonMangoldt_nonneg
  unfold ramanujanJetConductorWeight
  split_ifs <;> positivity

theorem ramanujanLogDivisorJet_eq_weighted_conductors {m : ℕ} (hm : 0 < m) (n : ℕ) :
    ramanujanLogDivisorJet m n =
      ∑ k ∈ m.divisors, ramanujanJetConductorWeight m k * ramanujanLagCoefficient k n := by
  have hm_mem : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hm.ne'⟩
  have hflip := (Nat.sum_divisorsAntidiagonal
    (fun d k => vonMangoldt d * ramanujanLagCoefficient k n) (n := m)).symm.trans
      (Nat.sum_divisorsAntidiagonal'
        (fun d k => vonMangoldt d * ramanujanLagCoefficient k n) (n := m))
  rw [ramanujanLogDivisorJet_eq_conductor_sum, hflip]
  simp only [ramanujanJetConductorWeight, add_mul, sum_add_distrib, ite_mul,
    zero_mul, sum_ite_eq', if_pos hm_mem]

theorem sum_ramanujanJetConductorWeight_sq {m : ℕ} (hm : 0 < m) :
    (∑ k ∈ m.divisors, ramanujanJetConductorWeight m k ^ 2 * k.totient) =
      (m.totient : ℝ) * (Real.log m) ^ 2 +
        ∑ d ∈ m.divisors, vonMangoldt d ^ 2 * (m / d).totient := by
  have hm_mem : m ∈ m.divisors := Nat.mem_divisors.mpr ⟨dvd_rfl, hm.ne'⟩
  have hterm (k : ℕ) : ramanujanJetConductorWeight m k ^ 2 * k.totient =
      (if k = m then (m.totient : ℝ) * (Real.log m) ^ 2 else 0) +
        vonMangoldt (m / k) ^ 2 * k.totient := by
    by_cases hkm : k = m
    · subst k
      simp [ramanujanJetConductorWeight, Nat.div_self hm, mul_comm]
    · simp only [ramanujanJetConductorWeight, if_neg hkm, zero_add]
  simp_rw [hterm]
  rw [sum_add_distrib, sum_ite_eq', if_pos hm_mem]
  congr 1
  exact (Nat.sum_divisorsAntidiagonal'
    (fun d k => vonMangoldt d ^ 2 * (k.totient : ℝ)) (n := m)).symm.trans
      (Nat.sum_divisorsAntidiagonal
        (fun d k => vonMangoldt d ^ 2 * (k.totient : ℝ)) (n := m))

/-- Plancherel retains every prime-power divisor of the logarithmic jet. -/
theorem sum_range_ramanujanLogDivisorJet_sq {m : ℕ} (hm : 0 < m) :
    (∑ n ∈ range m, ramanujanLogDivisorJet m n ^ 2) =
      (m : ℝ) * ((m.totient : ℝ) * (Real.log m) ^ 2 +
        ∑ d ∈ m.divisors, vonMangoldt d ^ 2 * (m / d).totient) := by
  simp_rw [ramanujanLogDivisorJet_eq_weighted_conductors hm]
  rw [sum_range_ramanujan_packet_sq _ _ _ (fun k hk => Nat.pos_of_mem_divisors hk)
    (fun k hk => Nat.dvd_of_mem_divisors hk), sum_ramanujanJetConductorWeight_sq hm]

/-- The normalized jet variance has an exact finite prime-power divisor expression. -/
theorem periodMean_centeredRamanujanJet_sq {m : ℕ} (hm : 0 < m) :
    (∑ n ∈ range m, centeredRamanujanJet m n ^ 2) / (m : ℝ) =
      (Real.log m) ^ 2 +
        ((∑ d ∈ m.divisors, vonMangoldt d ^ 2 * (m / d).totient) - vonMangoldt m ^ 2) /
          (m.totient : ℝ) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hmean := periodMean_ramanujanLogDivisorJet hm
  rw [div_eq_iff hmR] at hmean
  have hcenter : (∑ n ∈ range m, (ramanujanLogDivisorJet m n - vonMangoldt m) ^ 2) =
      (∑ n ∈ range m, ramanujanLogDivisorJet m n ^ 2) -
        (2 * vonMangoldt m) * (∑ n ∈ range m, ramanujanLogDivisorJet m n) +
        (m : ℝ) * vonMangoldt m ^ 2 := by
    have hterm (n : ℕ) : (ramanujanLogDivisorJet m n - vonMangoldt m) ^ 2 =
        ramanujanLogDivisorJet m n ^ 2 - (2 * vonMangoldt m) * ramanujanLogDivisorJet m n +
          vonMangoldt m ^ 2 := by ring
    simp_rw [hterm]
    rw [sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_range, nsmul_eq_mul]
  have hnorm : (∑ n ∈ range m, centeredRamanujanJet m n ^ 2) =
      (∑ n ∈ range m, (ramanujanLogDivisorJet m n - vonMangoldt m) ^ 2) / (m.totient : ℝ) := by
    simp only [centeredRamanujanJet, div_pow, Real.sq_sqrt hφ.le, ← sum_div]
  rw [hnorm, hcenter, hmean, sum_range_ramanujanLogDivisorJet_sq hm]
  field_simp [hmR, hφ.ne']
  ring

theorem sum_vonMangoldt_sq_mul_totient_le {m : ℕ} (hm : 0 < m) :
    (∑ d ∈ m.divisors, vonMangoldt d ^ 2 * (m / d).totient) ≤
      (m.totient : ℝ) * (Real.log m) ^ 2 := by
  have hlog : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have htot : (∑ d ∈ m.divisors, vonMangoldt d * ((m / d).totient : ℝ)) =
      (m.totient : ℝ) * tameDifferent m := by
    simpa only [mul_comm] using totient_mul_vonMangoldt_eq m
  calc
    _ ≤ ∑ d ∈ m.divisors, Real.log m * (vonMangoldt d * ((m / d).totient : ℝ)) := by
      apply sum_le_sum
      intro d hd
      have hdlog : vonMangoldt d ≤ Real.log m := by
        rw [← vonMangoldt_sum]
        exact single_le_sum (f := fun i => vonMangoldt i)
          (fun i _ => (show 0 ≤ vonMangoldt i from vonMangoldt_nonneg)) hd
      have hsq : vonMangoldt d ^ 2 ≤ Real.log m * vonMangoldt d := by
        simpa only [pow_two] using mul_le_mul_of_nonneg_right hdlog
          (show 0 ≤ vonMangoldt d from vonMangoldt_nonneg)
      exact (mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg _)).trans_eq (by ring)
    _ = Real.log m * ((m.totient : ℝ) * tameDifferent m) := by rw [← mul_sum, htot]
    _ ≤ Real.log m * ((m.totient : ℝ) * Real.log m) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (tameDifferent_le_log hm) (Nat.cast_nonneg _)) hlog
    _ = _ := by ring

/-- Complete-period quadratic mass removes the square-root totient from the jet cost. -/
theorem periodMean_centeredRamanujanJet_sq_le {m : ℕ} (hm : 0 < m) :
    (∑ n ∈ range m, centeredRamanujanJet m n ^ 2) / (m : ℝ) ≤ 2 * (Real.log m) ^ 2 := by
  have hφ : (0 : ℝ) < m.totient := by exact_mod_cast Nat.totient_pos.mpr hm
  have hquad := sum_vonMangoldt_sq_mul_totient_le hm
  have hquot :
      ((∑ d ∈ m.divisors, vonMangoldt d ^ 2 * (m / d).totient) - vonMangoldt m ^ 2) /
        (m.totient : ℝ) ≤ (Real.log m) ^ 2 := by
    rw [div_le_iff₀ hφ]
    nlinarith only [hquad, sq_nonneg (vonMangoldt m)]
  rw [periodMean_centeredRamanujanJet_sq hm]
  linarith only [hquot]

/-- The centered divisor jet has period absolute mass at most `2m log m`. -/
theorem sum_range_abs_centeredRamanujanJet_le {m : ℕ} (hm : 0 < m) :
    (∑ n ∈ range m, |centeredRamanujanJet m n|) ≤ 2 * m * Real.log m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : 0 ≤ Real.log m := Real.log_natCast_nonneg m
  have hmass := (div_le_iff₀ hmR).mp (periodMean_centeredRamanujanJet_sq_le hm)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (range m)
    (fun n => |centeredRamanujanJet m n|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, sq_abs] at hcs
  set B := 2 * (m : ℝ) * Real.log m
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hsq : (∑ n ∈ range m, |centeredRamanujanJet m n|) ^ 2 ≤ B ^ 2 := by
    calc
      _ ≤ (∑ n ∈ range m, centeredRamanujanJet m n ^ 2) * m := hcs
      _ ≤ (2 * (Real.log m) ^ 2 * m) * m := mul_le_mul_of_nonneg_right hmass hmR.le
      _ ≤ B ^ 2 := by
        dsimp only [B]
        nlinarith only [sq_nonneg ((m : ℝ) * Real.log m)]
  nlinarith only [hsq, hB]

/-- A normalized Ramanujan mode has unit complete-period quadratic mass. -/
theorem periodMean_normalizedRamanujanMode_sq {m : ℕ} (hm : 0 < m) :
    (∑ n ∈ range m, normalizedRamanujanMode m n ^ 2) / (m : ℝ) = 1 := by
  simpa only [periodMean, ite_true, pow_two] using
    periodMean_normalizedRamanujanMode_mul hm hm dvd_rfl dvd_rfl hm

/-- Complete-period orthogonality bounds the absolute mass independently of the totient. -/
theorem sum_range_abs_normalizedRamanujanMode_le {m : ℕ} (hm : 0 < m) :
    (∑ n ∈ range m, |normalizedRamanujanMode m n|) ≤ (m : ℝ) := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hmass := periodMean_normalizedRamanujanMode_sq hm
  rw [div_eq_iff hmR, one_mul] at hmass
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (range m)
    (fun n => |normalizedRamanujanMode m n|) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, sq_abs, hmass] at hcs
  nlinarith only [hcs, show (0 : ℝ) ≤ m from Nat.cast_nonneg _]

#print axioms sum_range_ramanujan_packet_sq
#print axioms sum_range_ramanujanLogDivisorJet_sq
#print axioms periodMean_centeredRamanujanJet_sq
#print axioms periodMean_centeredRamanujanJet_sq_le
#print axioms sum_range_abs_centeredRamanujanJet_le
#print axioms sum_range_abs_normalizedRamanujanMode_le
end
end GaloisForLFunctions.SuccessorShellArithmetic
