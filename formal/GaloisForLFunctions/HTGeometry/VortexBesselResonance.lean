import GaloisForLFunctions.HTGeometry.VortexClassicalSeries

/-!
# Resonant Bessel solutions of vortex Ward equations

Applying the coefficient recurrence of Brunner–Cheng–Jockers, arXiv:2609.09298,
equation (2.120), to the existing reciprocal-Gamma Bessel coefficients exposes a failure of
degree-zero determination at every positive integral resonance. Integral-order reflection
shifts the regular series to the resonant degree and supplies a nonzero solution with zero
constant coefficient. These are formal-series consequences of the Ward-operator application.
-/

open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
open GaloisForLFunctions PowerSeries
noncomputable section

/-- Positive integral order has the symmetric two-factorial coefficient formula. -/
theorem vortexBessel_nat_coeff (a : ℝ) (m n : ℕ) :
    coeff n (vortexBesselSeries a (m : ℂ)) =
      (a : ℂ) ^ (2 * n) / ((n.factorial : ℂ) * ((m + n).factorial : ℂ)) := by
  simp only [vortexBesselSeries, coeff_mk, modifiedBesselIOrderCoreTerm]
  rw [show (m : ℂ) + ((n + 1 : ℕ) : ℂ) = ((m + n + 1 : ℕ) : ℂ) by push_cast; ring,
    reciprocalGammaEntire_nat_succ]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- At negative integral order, reciprocal-Gamma zeros remove precisely the initial
coefficient range; the remaining coefficients have a two-factorial expression. -/
theorem vortexBessel_negative_coeff (a : ℝ) (m n : ℕ) :
    coeff n (vortexBesselSeries a (-(m : ℂ))) =
      if m ≤ n then (a : ℂ) ^ (2 * n) /
        ((n.factorial : ℂ) * ((n - m).factorial : ℂ)) else 0 := by
  simp only [vortexBesselSeries, coeff_mk, modifiedBesselIOrderCoreTerm]
  split_ifs with h
  · have heq : -(m : ℂ) + ((n + 1 : ℕ) : ℂ) = ((n - m + 1 : ℕ) : ℂ) := by
      simp only [Nat.cast_add, Nat.cast_sub h, Nat.cast_one]
      ring
    rw [heq, reciprocalGammaEntire_nat_succ]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  · have hm : n + 1 ≤ m := by omega
    have heq : -(m : ℂ) + ((n + 1 : ℕ) : ℂ) = -((m - (n + 1) : ℕ) : ℂ) := by
      rw [Nat.cast_sub hm]
      ring
    rw [heq]
    simp [reciprocalGammaEntire, Complex.Gamma_neg_nat_eq_zero]

/-- Integral-order reflection is an exact degree shift of the entire formal series. -/
theorem vortexBessel_integral_reflection (a : ℝ) (m : ℕ) :
    vortexBesselSeries a (-(m : ℂ)) =
      X ^ m * (C ((a : ℂ) ^ (2 * m)) * vortexBesselSeries a (m : ℂ)) := by
  ext n
  rw [vortexBessel_negative_coeff, PowerSeries.coeff_X_pow_mul']
  split_ifs with h
  · rw [PowerSeries.coeff_C_mul, vortexBessel_nat_coeff,
      show m + (n - m) = n by omega]
    rw [show 2 * n = 2 * m + 2 * (n - m) by omega, pow_add]
    ring
  · rfl

/-- The coefficient at the resonant degree is explicit. -/
theorem vortexBessel_resonant_coeff (a : ℝ) (m : ℕ) :
    coeff m (vortexBesselSeries a (-(m : ℂ))) =
      (a : ℂ) ^ (2 * m) / (m.factorial : ℂ) := by
  simp [vortexBessel_negative_coeff]

/-- Every positive integral resonance admits a nonzero Ward solution with zero constant
coefficient: degree-zero normalization alone cannot determine the solution there. -/
theorem vortexBessel_resonant_zero_initial_solution (u : ℝ) (m : ℕ) :
    ∃ F : PowerSeries ℂ, F ≠ 0 ∧ coeff 0 F = 0 ∧
      vortexWard (fun n => (n : ℂ) * ((n : ℂ) - ((m + 1 : ℕ) : ℂ)))
        (fun _ => (Real.exp u : ℂ) ^ (2 : ℕ)) F = 0 := by
  refine ⟨vortexBesselSeries (Real.exp u) (-((m + 1 : ℕ) : ℂ)), ?_, ?_, ?_⟩
  · intro hzero
    have hc := congrArg (coeff (m + 1)) hzero
    rw [vortexBessel_resonant_coeff, map_zero] at hc
    exact (div_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero u)))
      (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m + 1)))) hc
  · rw [vortexBessel_negative_coeff]
    simp
  · have ha : (fun n : ℕ => (n : ℂ) * ((n : ℂ) - ((m + 1 : ℕ) : ℂ))) =
        (fun n : ℕ => (n : ℂ) * (-((m + 1 : ℕ) : ℂ) + (n : ℂ))) := by
      funext n
      ring
    rw [ha]
    exact vortexBessel_ward (Real.exp u) (-((m + 1 : ℕ) : ℂ))

end
end GaloisForLFunctions.HTGeometry
