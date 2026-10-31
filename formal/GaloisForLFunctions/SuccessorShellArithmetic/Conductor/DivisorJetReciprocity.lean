import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.RamanujanJetAdjunctionGap

/-!
# The reciprocal divisor Ramanujan transform

Complementary divisor lags have the same reduced modulus. Their Ramanujan
coefficients are symmetric after totient weighting, while the antisymmetric
jet pairing is exactly their adjunction-energy difference.

Counting gcd classes transfers complete-period orthogonality to the divisor
lattice. The reciprocal transform squares to multiplication by the period,
giving an exact expansion of every real divisor profile.
-/

open Finset ArithmeticFunction
namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence CriticalArithmeticCorrelationTheory ArithmeticIntersectionTheory
noncomputable section


/-- Complementary divisor lags have exactly the same reduced modulus. -/
theorem divisor_lag_quotient_eq {M d k : ℕ} (hM : 0 < M) (hd : d ∣ M) (hk : k ∣ M) :
    d / Nat.gcd d (M / k) = k / Nat.gcd k (M / d) := by
  have hd0 := Nat.pos_of_dvd_of_pos hd hM
  have hk0 := Nat.pos_of_dvd_of_pos hk hM
  have hg1 : 0 < Nat.gcd d (M / k) := Nat.gcd_pos_of_pos_left _ hd0
  have hg2 : 0 < Nat.gcd k (M / d) := Nat.gcd_pos_of_pos_left _ hk0
  have he : Nat.gcd d (M / k) * k = Nat.gcd k (M / d) * d := by
    rw [← Nat.gcd_mul_right, Nat.div_mul_cancel hk,
      ← Nat.gcd_mul_right, Nat.div_mul_cancel hd, Nat.mul_comm d k]
  apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hg1 hg2)
  calc
    (d / Nat.gcd d (M / k)) * (Nat.gcd d (M / k) * Nat.gcd k (M / d)) =
        d * Nat.gcd k (M / d) := by
      rw [← Nat.mul_assoc, Nat.div_mul_cancel (Nat.gcd_dvd_left d (M / k))]
    _ = k * Nat.gcd d (M / k) := by simpa only [Nat.mul_comm] using he.symm
    _ = (k / Nat.gcd k (M / d)) * Nat.gcd k (M / d) * Nat.gcd d (M / k) := by
      rw [Nat.div_mul_cancel (Nat.gcd_dvd_left k (M / d))]
    _ = _ := by ring

/-- The finite divisor Ramanujan transform is symmetric after totient weighting. -/
theorem divisor_ramanujan_reciprocity {M d k : ℕ}
    (hM : 0 < M) (hd : d ∣ M) (hk : k ∣ M) :
    (k.totient : ℝ) * ramanujanLagCoefficient d (M / k) =
      (d.totient : ℝ) * ramanujanLagCoefficient k (M / d) := by
  have hq := divisor_lag_quotient_eq hM hd hk
  have hl := sieveLagMultiplier_eq_moebius_totient_quotient d (M / k)
  have hr := sieveLagMultiplier_eq_moebius_totient_quotient k (M / d)
  rw [hq] at hl
  have he := hl.trans hr.symm
  change ramanujanLagCoefficient d (M / k) / (d.totient : ℝ) =
    ramanujanLagCoefficient k (M / d) / (k.totient : ℝ) at he
  have hdphi : (d.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_dvd_of_pos hd hM)).ne'
  have hkphi : (k.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_dvd_of_pos hk hM)).ne'
  simpa only [mul_comm] using (div_eq_div_iff hdphi hkphi).mp he

/-- The antisymmetric divisor-jet pairing is exactly the adjunction-energy difference. -/
theorem divisor_jet_reciprocity {M d k : ℕ}
    (hM : 0 < M) (hd : d ∣ M) (hk : k ∣ M) :
    (k.totient : ℝ) * ramanujanLogDivisorJet d (M / k) -
      (d.totient : ℝ) * ramanujanLogDivisorJet k (M / d) =
        ((Real.log d + tameDifferent d) - (Real.log k + tameDifferent k)) *
          (k.totient : ℝ) * ramanujanLagCoefficient d (M / k) := by
  have he := divisor_ramanujan_reciprocity hM hd hk
  rw [ramanujanLogDivisorJet_eq_adjunction_gap (Nat.pos_of_dvd_of_pos hd hM),
    ramanujanLogDivisorJet_eq_adjunction_gap (Nat.pos_of_dvd_of_pos hk hM),
    divisor_lag_quotient_eq hM hd hk]
  linear_combination ((Real.log k + tameDifferent k) -
    (Real.log (k / Nat.gcd k (M / d) : ℕ) + tameDifferent (k / Nat.gcd k (M / d)))) * he

#print axioms divisor_lag_quotient_eq
#print axioms divisor_ramanujan_reciprocity
#print axioms divisor_jet_reciprocity

/-- A complete period weights each gcd class by its exact totient cardinality. -/
theorem sum_range_gcd_profile {M : ℕ} (hM : 0 < M) (F : ℕ → ℝ) :
    (∑ n ∈ range M, F (Nat.gcd M n)) =
      ∑ d ∈ M.divisors, ((M / d).totient : ℝ) * F d := by
  have hmaps : ∀ n ∈ range M, Nat.gcd M n ∈ M.divisors :=
    fun n _ => Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_left M n, hM.ne'⟩
  rw [← sum_fiberwise_of_maps_to hmaps]
  apply sum_congr rfl
  intro d hd
  calc
    _ = ∑ n ∈ (range M).filter (fun n => Nat.gcd M n = d), F d := by
      apply sum_congr rfl
      intro n hn
      rw [(mem_filter.mp hn).2]
    _ = _ := by
      rw [sum_const, nsmul_eq_mul, ← Nat.totient_div_of_dvd (Nat.dvd_of_mem_divisors hd)]

/-- Every conductor dividing the period is constant on its gcd classes. -/
theorem ramanujanLagCoefficient_gcd_period {M d : ℕ} (hd : d ∣ M) (n : ℕ) :
    ramanujanLagCoefficient d (Nat.gcd M n) = ramanujanLagCoefficient d n := by
  rw [ramanujanLagCoefficient_eq_gcd_divisor_sum,
    ramanujanLagCoefficient_eq_gcd_divisor_sum, ← Nat.gcd_assoc, Nat.gcd_eq_left hd]

/-- Exact orthogonality on the finite divisor lattice with totient measure. -/
theorem sum_divisors_totient_ramanujan_mul {M d k : ℕ}
    (hM : 0 < M) (hd : d ∣ M) (hk : k ∣ M) :
    (∑ r ∈ M.divisors, (r.totient : ℝ) *
      ramanujanLagCoefficient d (M / r) * ramanujanLagCoefficient k (M / r)) =
        if d = k then (M : ℝ) * k.totient else 0 := by
  have hp := sum_range_gcd_profile hM
    (fun n => ramanujanLagCoefficient d n * ramanujanLagCoefficient k n)
  simp only [ramanujanLagCoefficient_gcd_period hd,
    ramanujanLagCoefficient_gcd_period hk] at hp
  have he : (∑ r ∈ M.divisors, (r.totient : ℝ) *
      ramanujanLagCoefficient d (M / r) * ramanujanLagCoefficient k (M / r)) =
      ∑ r ∈ M.divisors, ((M / r).totient : ℝ) *
        (ramanujanLagCoefficient d r * ramanujanLagCoefficient k r) := by
    rw [← Nat.sum_div_divisors M (fun r => ((M / r).totient : ℝ) *
      (ramanujanLagCoefficient d r * ramanujanLagCoefficient k r))]
    apply sum_congr rfl
    intro r hr
    rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hr) hM.ne']
    ring
  rw [he, ← hp]
  exact sum_range_ramanujanLagCoefficient_mul (Nat.pos_of_dvd_of_pos hd hM)
    (Nat.pos_of_dvd_of_pos hk hM) hd hk

/-- Applying the reciprocal divisor Ramanujan transform twice multiplies by its period. -/
theorem sum_divisors_ramanujan_reciprocal {M d k : ℕ}
    (hM : 0 < M) (hd : d ∣ M) (hk : k ∣ M) :
    (∑ r ∈ M.divisors,
      ramanujanLagCoefficient d (M / r) * ramanujanLagCoefficient r (M / k)) =
        if d = k then (M : ℝ) else 0 := by
  have hkphi : (k.totient : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_dvd_of_pos hk hM)).ne'
  apply mul_left_cancel₀ hkphi
  calc
    _ = ∑ r ∈ M.divisors, (r.totient : ℝ) *
        ramanujanLagCoefficient d (M / r) * ramanujanLagCoefficient k (M / r) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro r hr
      have he := divisor_ramanujan_reciprocity hM (Nat.dvd_of_mem_divisors hr) hk
      calc
        _ = ramanujanLagCoefficient d (M / r) *
            ((k.totient : ℝ) * ramanujanLagCoefficient r (M / k)) := by ring
        _ = _ := by rw [he]; ring
    _ = _ := by
      rw [sum_divisors_totient_ramanujan_mul hM hd hk]
      by_cases hdk : d = k
      · subst d
        simp only [ite_true, mul_comm]
      · simp only [if_neg hdk, mul_zero]

/-- Every real divisor profile has an exact finite reciprocal Ramanujan expansion. -/
theorem divisor_profile_ramanujan_expansion {M k : ℕ}
    (hM : 0 < M) (hk : k ∈ M.divisors) (f : ℕ → ℝ) :
    f k = (1 / M) * ∑ d ∈ M.divisors,
      (∑ j ∈ M.divisors, f j * ramanujanLagCoefficient j (M / d)) *
        ramanujanLagCoefficient d (M / k) := by
  have hMR : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  symm
  calc
    _ = (1 / M) * ∑ j ∈ M.divisors, f j *
        (∑ d ∈ M.divisors,
          ramanujanLagCoefficient j (M / d) * ramanujanLagCoefficient d (M / k)) := by
      congr 1
      simp only [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      rw [mul_sum]
      apply sum_congr rfl
      intro d _
      ring
    _ = (1 / M) * ∑ j ∈ M.divisors, if j = k then f k * (M : ℝ) else 0 := by
      congr 1
      apply sum_congr rfl
      intro j hj
      rw [sum_divisors_ramanujan_reciprocal hM (Nat.dvd_of_mem_divisors hj)
        (Nat.dvd_of_mem_divisors hk)]
      by_cases hjk : j = k
      · subst j
        simp only [ite_true]
      · simp only [if_neg hjk, mul_zero]
    _ = f k := by
      rw [sum_ite_eq', if_pos hk]
      field_simp [hMR]

#print axioms sum_divisors_totient_ramanujan_mul
#print axioms sum_divisors_ramanujan_reciprocal
#print axioms divisor_profile_ramanujan_expansion
end
end GaloisForLFunctions.SuccessorShellArithmetic
