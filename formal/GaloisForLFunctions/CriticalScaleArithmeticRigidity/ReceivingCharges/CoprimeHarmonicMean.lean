import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.CoprimePrimeChargeMoments
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.ReceivingCharges.PrimeChargePoleCoefficient
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFlipThresholdIsSetByTheConductorsOfThePrime
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheHorizonCountertermIsPolar

/-!
# Exact harmonic means under coprime dilation

Dilation-invariant profiles turn prime incidence means into terminal
harmonic tails, bounded by the reciprocal logarithmic prime charge.
-/

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.CriticalScaleArithmeticRigidity
open Finset
open scoped Classical
open GaloisForLFunctions
open CriticalScaleArithmeticRigidity ArithmeticCouplingTheory SelectiveMultiscaleArithmeticPositivity
open RenormalizedArithmeticPotentialTheory
open _root_.RHTower.Sieve

private theorem mean_harmonic_cast (N : ℕ) : (harmonic N : ℝ) = harmonicMass N := by
  simpa only [harmonicMass, one_div] using
    _root_.RHTower.RegularizedDivisorHarmonic.harmonic_cast_eq_sum N

/-- Quotient truncation loses at most one prime logarithm and an absolute constant. -/
theorem harmonic_quotient_loss_le {N p : ℕ} (hN : 1 ≤ N) (hp : 1 ≤ p) :
    harmonicMass N - harmonicMass (N / p) ≤ Real.log p + 8 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  by_cases hpN : p ≤ N
  · have h1 := _root_.RHTower.RegularizedDivisorHarmonic.abs_harmonic_sub_log_div_le
      (by omega : 1 ≤ (1 : ℕ)) hN
    have h2 := _root_.RHTower.RegularizedDivisorHarmonic.abs_harmonic_sub_log_div_le hp hpN
    simp only [Nat.div_one, Nat.cast_one, div_one, mul_one, mean_harmonic_cast] at h1
    rw [mean_harmonic_cast, Real.log_div hN0.ne' hp0.ne'] at h2
    have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hpNr : (p : ℝ) ≤ N := by exact_mod_cast hpN
    have hsmall : 4 / (N : ℝ) ≤ 4 := (div_le_iff₀ hN0).mpr (by linarith only [hN1])
    have hlarge : 4 * (p : ℝ) / N ≤ 4 := (div_le_iff₀ hN0).mpr
      (by linarith only [hpNr])
    have hu := (abs_le.mp h1).2
    have hl := (abs_le.mp h2).1
    linarith only [hu, hl, hsmall, hlarge]
  · have hNp : N < p := Nat.lt_of_not_ge hpN
    have hz : harmonicMass 0 = 0 := by simp only [harmonicMass, Icc_eq_empty_of_lt (by omega : (0 : ℕ) < 1), sum_empty]
    rw [Nat.div_eq_of_lt hNp, hz, sub_zero]
    have h := harmonic_le_one_add_log N
    rw [mean_harmonic_cast] at h
    have hlog : Real.log N ≤ Real.log p := Real.log_le_log hN0 (by exact_mod_cast hNp.le)
    linarith only [h, hlog]

/-- Dilation invariance turns a weighted prime incidence mean into its exact terminal harmonic tail. -/
theorem unit_invariant_harmonic_incidence {p : ℕ} (hp : 0 < p)
    (G : ℕ → ℝ) (hG : ∀ n, G (p * n) = G n) (N : ℕ) :
    (∑ n ∈ Icc 1 N, G n * ((if p ∣ n then (1 : ℝ) else 0) - 1 / p) / (n : ℝ)) =
      -(1 / (p : ℝ)) * ∑ n ∈ Ioc (N / p) N, G n / (n : ℝ) := by
  simp only [mul_sub, sub_div, sum_sub_distrib, mul_ite, mul_one, mul_zero, ite_div, zero_div]
  rw [← sum_filter, sum_filter_dvd_eq_sum_scaled hp]
  have hscaled : (∑ n ∈ Icc 1 (N / p), G (p * n) / (p * n : ℕ)) =
      (∑ n ∈ Icc 1 (N / p), G n / (n : ℝ)) / p := by
    rw [sum_div]
    exact sum_congr rfl fun n _ => by rw [hG n, Nat.cast_mul]; ring
  have hconstant : (∑ n ∈ Icc 1 N, G n * (1 / (p : ℝ)) / n) =
      (∑ n ∈ Icc 1 N, G n / (n : ℝ)) / p := by
    rw [sum_div]
    exact sum_congr rfl fun n _ => by ring
  rw [hscaled, hconstant]
  have hsplit := sum_Ioc_consecutive (fun n : ℕ => G n / (n : ℝ))
    (Nat.zero_le (N / p)) (Nat.div_le_self N p)
  change (∑ n ∈ Icc 1 (N / p), G n / (n : ℝ)) +
    (∑ n ∈ Ioc (N / p) N, G n / (n : ℝ)) =
      ∑ n ∈ Icc 1 N, G n / (n : ℝ) at hsplit
  rw [← hsplit]
  ring

/-- A bounded unit-invariant mode has a centering cost paid by the logarithmic prime charge. -/
theorem abs_unit_invariant_harmonic_incidence_le {N p : ℕ}
    (hN : 1 ≤ N) (hp : 0 < p) (G : ℕ → ℝ) (hG : ∀ n, G (p * n) = G n)
    {V : ℝ} (hV : 0 ≤ V) (hbound : ∀ n, |G n| ≤ V) :
    |∑ n ∈ Icc 1 N, G n * ((if p ∣ n then (1 : ℝ) else 0) - 1 / p) / (n : ℝ)| ≤
      V * (Real.log p + 8) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [unit_invariant_harmonic_incidence hp G hG N, abs_mul, abs_neg,
    abs_of_nonneg (by positivity : 0 ≤ 1 / (p : ℝ))]
  have htail : |∑ n ∈ Ioc (N / p) N, G n / (n : ℝ)| ≤
      V * (harmonicMass N - harmonicMass (N / p)) := by
    calc
      _ ≤ ∑ n ∈ Ioc (N / p) N, |G n / (n : ℝ)| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ Ioc (N / p) N, V / (n : ℝ) := by
        apply sum_le_sum
        intro n _
        rw [abs_div, abs_of_nonneg (Nat.cast_nonneg n)]
        exact div_le_div_of_nonneg_right (hbound n) (Nat.cast_nonneg n)
      _ = _ := by
        have hsplit := sum_Ioc_consecutive (fun n : ℕ => 1 / (n : ℝ))
          (Nat.zero_le (N / p)) (Nat.div_le_self N p)
        change harmonicMass (N / p) + (∑ n ∈ Ioc (N / p) N, 1 / (n : ℝ)) = harmonicMass N at hsplit
        have htailEq : (∑ n ∈ Ioc (N / p) N, 1 / (n : ℝ)) =
            harmonicMass N - harmonicMass (N / p) := by linarith only [hsplit]
        rw [show (∑ n ∈ Ioc (N / p) N, V / (n : ℝ)) =
          V * (∑ n ∈ Ioc (N / p) N, 1 / (n : ℝ)) by simp only [mul_sum, mul_one_div],
          htailEq]
  have h := htail.trans (mul_le_mul_of_nonneg_left (harmonic_quotient_loss_le hN hp) hV)
  exact (mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 1 / (p : ℝ))).trans_eq (by ring)

/-- A coherent prime band keeps a centering bound in its reciprocal logarithmic mass. -/
theorem abs_unit_invariant_prime_band_mean_le {N : ℕ} (hN : 1 ≤ N)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (G : ℕ → ℝ)
    (hG : ∀ p ∈ P, ∀ n, G (p * n) = G n) (s : ℝ)
    {V : ℝ} (hV : 0 ≤ V) (hbound : ∀ n, |G n| ≤ V) :
    |∑ n ∈ Icc 1 N, G n * incidencePacket P (fun _ => s) n / (n : ℝ)| ≤
      V * |s| * ∑ p ∈ P, (Real.log p + 8) / (p : ℝ) := by
  have hexpand :
      (∑ n ∈ Icc 1 N, G n * incidencePacket P (fun _ => s) n / (n : ℝ)) =
      s * ∑ p ∈ P, ∑ n ∈ Icc 1 N,
        G n * ((if p ∣ n then (1 : ℝ) else 0) - 1 / p) / (n : ℝ) := by
    simp only [incidencePacket, mul_sum, sum_div]
    rw [sum_comm]
    apply sum_congr rfl
    intro p _
    exact sum_congr rfl fun n _ => by ring
  rw [hexpand, abs_mul]
  calc
    _ ≤ |s| * ∑ p ∈ P,
        |∑ n ∈ Icc 1 N, G n * ((if p ∣ n then (1 : ℝ) else 0) - 1 / p) / (n : ℝ)| :=
      mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) (abs_nonneg s)
    _ ≤ |s| * ∑ p ∈ P, V * (Real.log p + 8) / (p : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg s)
      exact sum_le_sum fun p hp => abs_unit_invariant_harmonic_incidence_le hN
        (hP p hp).pos G (hG p hp) hV hbound
    _ = _ := by
      simp only [mul_sum]
      exact sum_congr rfl fun p _ => by ring

#print axioms abs_unit_invariant_prime_band_mean_le

#print axioms harmonic_quotient_loss_le
#print axioms unit_invariant_harmonic_incidence
#print axioms abs_unit_invariant_harmonic_incidence_le

/-- Exact harmonic centering of a unit-invariant prime band costs its logarithmic charge divided by the horizon logarithm. -/
theorem abs_unit_invariant_prime_band_center_le {N : ℕ} (hN : 1 ≤ N)
    (hL : 0 < Real.log N) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (G : ℕ → ℝ)
    (hG : ∀ p ∈ P, ∀ n, G (p * n) = G n) (s : ℝ)
    {V : ℝ} (hV : 0 ≤ V) (hbound : ∀ n, |G n| ≤ V) :
    |(∑ n ∈ Icc 1 N, G n * incidencePacket P (fun _ => s) n / (n : ℝ)) / harmonicMass N| ≤
      V * |s| * (1 + 8 / Real.log 2) * (∑ p ∈ P, Real.log p / (p : ℝ)) / Real.log N := by
  have htwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hsum : (∑ p ∈ P, (Real.log p + 8) / (p : ℝ)) ≤
      (1 + 8 / Real.log 2) * ∑ p ∈ P, Real.log p / (p : ℝ) := by
    rw [mul_sum]
    apply sum_le_sum
    intro p hp
    have hlower : Real.log 2 ≤ Real.log p :=
      Real.log_le_log (by norm_num) (by exact_mod_cast (hP p hp).two_le)
    have h8 : 8 ≤ (8 / Real.log 2) * Real.log p := by
      calc
        _ = (8 / Real.log 2) * Real.log 2 := by field_simp [htwo.ne']
        _ ≤ _ := mul_le_mul_of_nonneg_left hlower (div_nonneg (by norm_num) htwo.le)
    have hnum : Real.log p + 8 ≤ (1 + 8 / Real.log 2) * Real.log p := by
      nlinarith only [h8]
    exact (div_le_div_of_nonneg_right hnum (Nat.cast_nonneg p)).trans_eq (by ring)
  have hnum := (abs_unit_invariant_prime_band_mean_le hN P hP G hG s hV hbound).trans
    (mul_le_mul_of_nonneg_left hsum (mul_nonneg hV (abs_nonneg s)))
  have hH := harmonicMass_pos hN
  have hLH : Real.log N ≤ harmonicMass N :=
    RenormalizedArithmeticPotentialTheory.log_le_harmonicSum N
  have hC : 0 ≤ 1 + 8 / Real.log 2 :=
    add_nonneg zero_le_one (div_nonneg (by norm_num) htwo.le)
  have hB : 0 ≤ ∑ p ∈ P, Real.log p / (p : ℝ) :=
    sum_nonneg fun p _ => div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
  rw [abs_div, abs_of_pos hH]
  refine (div_le_div_of_nonneg_right hnum hH.le).trans ?_
  exact (div_le_div_of_nonneg_left
    (mul_nonneg (mul_nonneg hV (abs_nonneg s)) (mul_nonneg hC hB)) hL hLH).trans_eq (by ring)

#print axioms abs_unit_invariant_prime_band_center_le

end GaloisForLFunctions.CriticalScaleArithmeticRigidity
