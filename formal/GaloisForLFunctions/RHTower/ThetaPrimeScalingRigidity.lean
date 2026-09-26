import GaloisForLFunctions.RHTower.ThetaPrimeShiftNoetherArctan
import GaloisForLFunctions.RHTower.TwoDilationDivisorMetric

/-!
# Rigidity of zero-energy local prime scalings

The full positive prime-link measure defines a finite quadratic energy for
every bounded continuous scaling profile. Its nullspace consists exactly
of constants. Zero energy forces periods `log 2` and `log 3`; unique prime
factorization makes their ratio irrational, and continuity propagates
these periods to the whole real line. Thus every nonconstant local scaling
has strictly positive energy, while global reciprocal scaling is the
exact zero mode.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped BoundedContinuousFunction

namespace RHTower.ThetaSourceWard

def thetaPrimeScalingEnergyDensity (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) (p : ℕ × ℝ) : ℝ :=
  ‖thetaPrimeProfileIncrement chi p‖ ^ 2 * (thetaPrimeLinkDensity S T p).re

def thetaPrimeScalingEnergy (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) : ℝ :=
  ∫ p, thetaPrimeScalingEnergyDensity S T chi p ∂thetaPrimeLinkMeasure

theorem continuous_thetaPrimeScalingEnergyDensity (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    Continuous (thetaPrimeScalingEnergyDensity S T chi) :=
  ((continuous_thetaPrimeProfileIncrement chi).norm.pow 2).mul
    (Complex.continuous_re.comp (continuous_thetaPrimeLinkDensity S T))

theorem thetaPrimeScalingEnergyDensity_nonneg (S T : ThetaSource) (chi : ℝ →ᵇ ℂ)
    (p : ℕ × ℝ) : 0 ≤ thetaPrimeScalingEnergyDensity S T chi p :=
  mul_nonneg (sq_nonneg _) (thetaPrimeLinkDensity_re_nonneg S T p)

theorem integrable_thetaPrimeScalingEnergyDensity (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    Integrable (thetaPrimeScalingEnergyDensity S T chi) thetaPrimeLinkMeasure := by
  apply (integrable_thetaPrimeLinkDensity S T).re.bdd_mul
    ((continuous_thetaPrimeProfileIncrement chi).norm.pow 2).aestronglyMeasurable
    (c := (2 * ‖chi‖) ^ 2)
  filter_upwards with p
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_thetaPrimeProfileIncrement_le chi p) 2

theorem thetaPrimeScalingEnergy_nonneg (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    0 ≤ thetaPrimeScalingEnergy S T chi :=
  integral_nonneg (thetaPrimeScalingEnergyDensity_nonneg S T chi)

theorem thetaPrimeScalingEnergy_add_const (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) (c : ℂ) :
    thetaPrimeScalingEnergy S T (chi + BoundedContinuousFunction.const ℝ c) =
      thetaPrimeScalingEnergy S T chi := by
  simp [thetaPrimeScalingEnergy, thetaPrimeScalingEnergyDensity, thetaPrimeProfileIncrement]

private theorem thetaPrimeLinkDensity_prime_re_pos (S T : ThetaSource) {n : ℕ}
    (hn : n.Prime) (x : ℝ) : 0 < (thetaPrimeLinkDensity S T (n, x)).re := by
  rw [thetaPrimeLinkDensity_eq_real, Complex.ofReal_re,
    ArithmeticFunction.vonMangoldt_apply_prime hn]
  apply mul_pos (mul_pos _ (T.pos x)) (S.pos _)
  exact div_pos (Real.log_pos (by exact_mod_cast hn.one_lt))
    (Real.sqrt_pos.mpr (by exact_mod_cast hn.pos))

private theorem thetaPrimeScalingEnergy_periodic (S T : ThetaSource) (chi : ℝ →ᵇ ℂ)
    (h : thetaPrimeScalingEnergy S T chi = 0) {n : ℕ} (hn : n.Prime) :
    Function.Periodic chi (Real.log n) := by
  letI : (Measure.count : Measure ℕ).IsOpenPosMeasure :=
    ⟨fun _ _ h => Measure.count_ne_zero h⟩
  have hae := (integral_eq_zero_iff_of_nonneg
    (thetaPrimeScalingEnergyDensity_nonneg S T chi)
    (integrable_thetaPrimeScalingEnergyDensity S T chi)).mp h
  have he := ((continuous_thetaPrimeScalingEnergyDensity S T chi).ae_eq_iff_eq
    thetaPrimeLinkMeasure continuous_zero).mp hae
  intro x
  have hp := congrFun he (n, x)
  change ‖chi (x + Real.log n) - chi x‖ ^ 2 * (thetaPrimeLinkDensity S T (n, x)).re = 0 at hp
  have hz := (mul_eq_zero.mp hp).resolve_right (thetaPrimeLinkDensity_prime_re_pos S T hn x).ne'
  exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hz))

private theorem thetaPrimeProfile_constant_of_two_periods (chi : ℝ →ᵇ ℂ)
    (h₂ : Function.Periodic chi (Real.log 2)) (h₃ : Function.Periodic chi (Real.log 3)) :
    chi = BoundedContinuousFunction.const ℝ (chi 0) := by
  ext x
  apply eq_of_two_dilation_invariance chi.continuous (r := 2) (s := 3)
    (by norm_num) (by norm_num) _ h₂ h₃ x 0
  intro m n hm _ he
  have hd : 2 ∣ 3 ^ n := by rw [← he]; exact dvd_pow_self 2 hm.ne'
  have hf := Nat.prime_two.dvd_of_dvd_pow hd
  norm_num at hf

/-- Global reciprocal scaling is the entire nullspace of the full prime-link energy. -/
theorem thetaPrimeScalingEnergy_eq_zero_iff (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    thetaPrimeScalingEnergy S T chi = 0 ↔
      chi = BoundedContinuousFunction.const ℝ (chi 0) := by
  constructor
  · intro h
    exact thetaPrimeProfile_constant_of_two_periods chi
      (thetaPrimeScalingEnergy_periodic S T chi h Nat.prime_two)
      (thetaPrimeScalingEnergy_periodic S T chi h Nat.prime_three)
  · intro h
    have he : ∀ x, chi x = chi 0 := fun x => congrArg (fun f : ℝ →ᵇ ℂ => f x) h
    simp [thetaPrimeScalingEnergy, thetaPrimeScalingEnergyDensity,
      thetaPrimeProfileIncrement, he]

/-- Every nonconstant bounded continuous local scaling costs strictly positive prime energy. -/
theorem thetaPrimeScalingEnergy_pos_iff (S T : ThetaSource) (chi : ℝ →ᵇ ℂ) :
    0 < thetaPrimeScalingEnergy S T chi ↔
      chi ≠ BoundedContinuousFunction.const ℝ (chi 0) := by
  constructor
  · intro h he
    exact h.ne' ((thetaPrimeScalingEnergy_eq_zero_iff S T chi).mpr he)
  · intro h
    exact lt_of_le_of_ne (thetaPrimeScalingEnergy_nonneg S T chi)
      (fun he => h ((thetaPrimeScalingEnergy_eq_zero_iff S T chi).mp he.symm))

end RHTower.ThetaSourceWard
