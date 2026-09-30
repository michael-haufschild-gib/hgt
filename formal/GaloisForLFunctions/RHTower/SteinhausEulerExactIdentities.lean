import GaloisForLFunctions.RHTower.SteinhausEulerSecondMoment

/-!
# Literal finite Euler density and centered logarithmic field

BAG C20.11a. Identify the concrete coordinate tilt with the existing finite Euler
product, for every sample and cutoff. Nonprime coordinates contribute weight one
and centered log zero. The density is squared Euler norm divided by the critical
partition; the centered tilted sum is log Euler norm minus log partition.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section
namespace RHTower
open SteinhausModel GaloisForLFunctions.RHTower

/-- The literal critical Euler prime argument is the exact tilted coordinate argument. -/
theorem steinhausEulerPrimeTerm_half_eq {p : ℕ} (hp : p.Prime) (ω : Omega) :
    steinhausEulerPrimeTerm (1 / 2) ω p =
      (steinhausCriticalPrimeRadius p : ℂ) * circleMap 0 1 (2 * Real.pi * ω p) := by
  have hpow : (p : ℂ) ^ (-(1 / 2 : ℂ)) = (steinhausCriticalPrimeRadius p : ℂ) := by
    rw [steinhausCriticalPrimeRadius, randomEulerRadius, if_pos hp,
      Complex.ofReal_cpow (by positivity)]
    norm_num
  rw [steinhausEulerPrimeTerm, steinhausCharacter_prime_eq_circleMap hp ω, hpow, mul_comm]

private theorem critical_coeff_pos {p : ℕ} (hp : p.Prime) : 0 < 1 - (p : ℝ)⁻¹ := by
  have hsq := steinhausCriticalPrimeRadius_sq p
  rw [if_pos hp] at hsq
  have hr0 := steinhausCriticalPrimeRadius_nonneg p
  have hr1 := steinhausCriticalPrimeRadius_le p
  nlinarith

private theorem tiltWeight_nonprime {n : ℕ} (hn : ¬n.Prime) (ω : Omega) :
    steinhausEulerTiltWeight (steinhausCriticalPrimeRadius n) (ω n) = 1 := by
  simp [steinhausCriticalPrimeRadius, randomEulerRadius, hn, steinhausEulerTiltWeight]

private theorem tiltVariable_nonprime {n : ℕ} (hn : ¬n.Prime) (ω : Omega) :
    steinhausEulerTiltPrimeVariable n ω = 0 := by
  simp [steinhausEulerTiltPrimeVariable, steinhausEulerTiltPrimeTerm,
    steinhausEulerTiltCenteredLog, steinhausEulerTiltLog,
    steinhausCriticalPrimeRadius, randomEulerRadius, hn]

private theorem tiltWeight_prime {p : ℕ} (hp : p.Prime) (ω : Omega) :
    steinhausEulerTiltWeight (steinhausCriticalPrimeRadius p) (ω p) =
      (1 - (p : ℝ)⁻¹) * ‖(1 - steinhausEulerPrimeTerm (1 / 2) ω p)⁻¹‖ ^ 2 := by
  unfold steinhausEulerTiltWeight
  rw [steinhausCriticalPrimeRadius_sq, if_pos hp, ← steinhausEulerPrimeTerm_half_eq hp ω]
  simp only [norm_inv, inv_pow, div_eq_mul_inv]

private theorem tiltVariable_prime {p : ℕ} (hp : p.Prime) (ω : Omega) :
    steinhausEulerTiltPrimeVariable p ω =
      -Real.log ‖1 - steinhausEulerPrimeTerm (1 / 2) ω p‖ + Real.log (1 - (p : ℝ)⁻¹) := by
  unfold steinhausEulerTiltPrimeVariable steinhausEulerTiltPrimeTerm
    steinhausEulerTiltCenteredLog steinhausEulerTiltLog
  rw [steinhausCriticalPrimeRadius_sq, if_pos hp, ← steinhausEulerPrimeTerm_half_eq hp ω]

/-- The concrete finite coordinate density is the normalized literal Euler energy. -/
theorem steinhausEulerTiltFiniteDensity_eq_norm_sq (N : ℕ) (ω : Omega) :
    steinhausEulerTiltFiniteDensity N ω =
      ENNReal.ofReal (‖steinhausFiniteEulerProduct (Nat.primesBelow N) (1 / 2) ω‖ ^ 2 /
        steinhausEulerPartition (Nat.primesBelow N) (1 / 2)) := by
  let W : ℕ → ℝ := fun n => steinhausEulerTiltWeight (steinhausCriticalPrimeRadius n) (ω n)
  have hW (n : ℕ) : 0 ≤ W n := by
    have h := steinhausEulerTiltWeight_lower (steinhausCriticalPrimeRadius_nonneg n)
      (steinhausCriticalPrimeRadius_le n) (ω n)
    dsimp [W]
    linarith
  have hfilter : (∏ n ∈ Finset.range N, W n) = ∏ p ∈ Nat.primesBelow N, W p := by
    symm
    apply Finset.prod_filter_of_ne
    intro n hn hne
    by_contra hnp
    exact hne (tiltWeight_nonprime hnp ω)
  have hcoeff : (∏ p ∈ Nat.primesBelow N, (1 - (p : ℝ)⁻¹)) =
      (steinhausEulerPartition (Nat.primesBelow N) (1 / 2))⁻¹ := by
    rw [steinhausEulerPartition_half, Finset.prod_inv_distrib, inv_inv]
  change (∏ i : Fin N, ENNReal.ofReal (W i)) = _
  rw [Fin.prod_univ_eq_prod_range (fun n : ℕ => ENNReal.ofReal (W n)) N,
    ← ENNReal.ofReal_prod_of_nonneg (fun n _ => hW n), hfilter]
  congr 1
  calc
    _ = (∏ p ∈ Nat.primesBelow N, (1 - (p : ℝ)⁻¹)) *
        ∏ p ∈ Nat.primesBelow N, ‖(1 - steinhausEulerPrimeTerm (1 / 2) ω p)⁻¹‖ ^ 2 := by
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro p hp
      exact tiltWeight_prime (Nat.mem_primesBelow.mp hp).2 ω
    _ = (steinhausEulerPartition (Nat.primesBelow N) (1 / 2))⁻¹ *
        ‖steinhausFiniteEulerProduct (Nat.primesBelow N) (1 / 2) ω‖ ^ 2 := by
      rw [hcoeff, Finset.prod_pow, ← norm_prod]
      rfl
    _ = _ := by simp only [div_eq_mul_inv, mul_comm]

/-- The concrete centered tilted sum is exactly the log-field minus its critical partition. -/
theorem steinhausEulerTiltPrimeSum_eq_log_norm (N : ℕ) (ω : Omega) :
    steinhausEulerTiltPrimeSum (Finset.range N) ω =
      Real.log ‖steinhausFiniteEulerProduct (Nat.primesBelow N) (1 / 2) ω‖ -
        Real.log (steinhausEulerPartition (Nat.primesBelow N) (1 / 2)) := by
  have hfilter : (∑ n ∈ Finset.range N, steinhausEulerTiltPrimeVariable n ω) =
      ∑ p ∈ Nat.primesBelow N, steinhausEulerTiltPrimeVariable p ω := by
    symm
    apply Finset.sum_filter_of_ne
    intro n hn hne
    by_contra hnp
    exact hne (tiltVariable_nonprime hnp ω)
  have hlogM : Real.log (steinhausEulerPartition (Nat.primesBelow N) (1 / 2)) =
      -(∑ p ∈ Nat.primesBelow N, Real.log (1 - (p : ℝ)⁻¹)) := by
    rw [steinhausEulerPartition_half,
      Real.log_prod (fun p hp => inv_ne_zero (critical_coeff_pos (Nat.mem_primesBelow.mp hp).2).ne')]
    simp only [Real.log_inv, Finset.sum_neg_distrib]
  have hlogF := log_norm_steinhausFiniteEulerProduct (Nat.primesBelow N)
    (fun _ hp => (Nat.mem_primesBelow.mp hp).2) (s := (1 / 2 : ℂ)) (by norm_num) ω
  simp only [Complex.re_sum, Complex.neg_re, Complex.log_re] at hlogF
  rw [steinhausEulerTiltPrimeSum, hfilter, hlogF, hlogM, sub_neg_eq_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  exact tiltVariable_prime (Nat.mem_primesBelow.mp hp).2 ω

end RHTower
