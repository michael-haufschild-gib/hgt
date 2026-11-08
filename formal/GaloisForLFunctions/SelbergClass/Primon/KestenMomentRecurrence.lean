import GaloisForLFunctions.SelbergClass.Primon.SemicircleMoments

/-!
# The quadratic transformation from prime phases to the semicircle law

In the Hecke coordinate `x = 2 cos(πt)`, multiplication of the prime phase
density by `(p+1)² - p x²` gives `p(p+1)` times the semicircle phase density.
The multiplier is strictly positive on the spectral interval. Integrating
this identity transfers arbitrary continuous observables and yields an
exact two-step recurrence for all prime-phase moments, driven by Catalan
numbers in even degree.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The quadratic multiplier stays positive throughout the phase coordinate. -/
theorem kestenQuadraticMultiplier_pos (p : Nat.Primes) (t : ℝ) :
    0 < ((p : ℝ) + 1) ^ 2 - (p : ℝ) * (2 * Real.cos (Real.pi * t)) ^ 2 := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hs := Real.sin_sq_add_cos_sq (Real.pi * t)
  have hprod : 0 ≤ 4 * (p : ℝ) * Real.sin (Real.pi * t) ^ 2 := by positivity
  have hsq := sq_pos_of_pos (show 0 < (p : ℝ) - 1 by linarith only [hp])
  nlinarith only [hs, hprod, hsq]

/-- A positive quadratic reweighting of the prime phase density is exactly semicircular. -/
theorem kestenDensity_quadratic_transform (p : Nat.Primes) (t : ℝ) :
    (((p : ℝ) + 1) ^ 2 - (p : ℝ) * (2 * Real.cos (Real.pi * t)) ^ 2) *
      kestenMcKayDensity p t = (p : ℝ) * ((p : ℝ) + 1) * semicirclePhaseDensity t := by
  have hd : ((p : ℝ) + 1) ^ 2 - (p : ℝ) * (2 * Real.cos (Real.pi * t)) ^ 2 =
      ((p : ℝ) - 1) ^ 2 + 4 * (p : ℝ) * Real.sin (Real.pi * t) ^ 2 := by
    nlinarith only [Real.sin_sq_add_cos_sq (Real.pi * t)]
  have hn : ((p : ℝ) - 1) ^ 2 + 4 * (p : ℝ) * Real.sin (Real.pi * t) ^ 2 ≠ 0 := by
    rw [← hd]
    exact (kestenQuadraticMultiplier_pos p t).ne'
  rw [hd, kestenMcKayDensity_eq_sine_square, semicirclePhaseDensity]
  rw [mul_comm _ (_ / _), div_mul_cancel₀ _ hn]
  ring

/-- Quadratic reweighting transfers every continuous phase observable exactly. -/
theorem kestenObservable_quadratic_transform (p : Nat.Primes) (f : C(ℝ, ℝ)) :
    ((p : ℝ) + 1) ^ 2 * kestenObservableAverage p f -
      (p : ℝ) * kestenObservableAverage p (phasePowerObservable 2 * f) =
        (p : ℝ) * ((p : ℝ) + 1) * semicircleObservableAverage f := by
  have hi : IntegrableOn (fun t : ℝ => kestenMcKayDensity p t * f t) (Ioo 0 1) :=
    ((continuous_kestenMcKayDensity p).mul f.continuous).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hx : Continuous (fun t : ℝ => (2 * Real.cos (Real.pi * t)) ^ 2) := by fun_prop
  have hj : IntegrableOn (fun t : ℝ => kestenMcKayDensity p t *
      ((2 * Real.cos (Real.pi * t)) ^ 2 * f t)) (Ioo 0 1) :=
    ((continuous_kestenMcKayDensity p).mul (hx.mul f.continuous)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have he : (fun t : ℝ => ((p : ℝ) + 1) ^ 2 * (kestenMcKayDensity p t * f t) -
      (p : ℝ) * (kestenMcKayDensity p t * ((2 * Real.cos (Real.pi * t)) ^ 2 * f t))) =
      fun t => ((p : ℝ) * ((p : ℝ) + 1)) * (semicirclePhaseDensity t * f t) := by
    funext t
    calc
      _ = ((((p : ℝ) + 1) ^ 2 - (p : ℝ) * (2 * Real.cos (Real.pi * t)) ^ 2) *
          kestenMcKayDensity p t) * f t := by ring
      _ = _ := by rw [kestenDensity_quadratic_transform]; ring
  have h := congrArg (fun g : ℝ → ℝ => ∫ t in Ioo (0 : ℝ) 1, g t) he
  rw [integral_sub (hi.const_mul _) (hj.const_mul _), integral_const_mul,
    integral_const_mul, integral_const_mul] at h
  exact h

/-- The quadratic density relation gives an exact shift equation for every coordinate moment. -/
theorem kestenMoment_shift_relation (p : Nat.Primes) (n : ℕ) :
    ((p : ℝ) + 1) ^ 2 * kestenMoment p n - (p : ℝ) * kestenMoment p (n + 2) =
      (p : ℝ) * ((p : ℝ) + 1) * semicircleMoment n := by
  have he : phasePowerObservable 2 * phasePowerObservable n = phasePowerObservable (n + 2) := by
    ext t
    change (2 * Real.cos (Real.pi * t)) ^ 2 * (2 * Real.cos (Real.pi * t)) ^ n =
      (2 * Real.cos (Real.pi * t)) ^ (n + 2)
    rw [pow_add]
    ring
  have h := kestenObservable_quadratic_transform p (phasePowerObservable n)
  rw [he, kestenObservableAverage_phasePower, kestenObservableAverage_phasePower] at h
  exact h

/-- Every prime-phase moment follows a linear recurrence driven by semicircle moments. -/
theorem kestenMoment_add_two (p : Nat.Primes) (n : ℕ) :
    kestenMoment p (n + 2) = ((p : ℝ) + 1) ^ 2 / (p : ℝ) * kestenMoment p n -
      ((p : ℝ) + 1) * semicircleMoment n := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have h := kestenMoment_shift_relation p n
  field_simp [hp]
  nlinarith only [h]

@[simp] theorem kestenMoment_one (p : Nat.Primes) : kestenMoment p 1 = 0 := by
  have h := phaseCharacterAverage_odd p 0
  simpa only [Nat.mul_zero, zero_add, phaseCharacterAverage, phaseCharacter_one,
    kestenMoment, pow_one] using h

/-- All odd coordinate moments of the prime phase law vanish. -/
theorem kestenMoment_odd (p : Nat.Primes) (n : ℕ) : kestenMoment p (2 * n + 1) = 0 := by
  induction n with
  | zero => simpa only [Nat.mul_zero, zero_add] using kestenMoment_one p
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega,
      kestenMoment_add_two, ih, semicircleMoment_odd]
    ring

/-- Even prime-phase moments satisfy a Catalan-forced recurrence at each fixed prime. -/
theorem kestenMoment_even_succ (p : Nat.Primes) (n : ℕ) :
    kestenMoment p (2 * (n + 1)) =
      ((p : ℝ) + 1) ^ 2 / (p : ℝ) * kestenMoment p (2 * n) -
        ((p : ℝ) + 1) * (catalan n : ℝ) := by
  rw [show 2 * (n + 1) = 2 * n + 2 by omega, kestenMoment_add_two, semicircleMoment_even]

end
end GaloisForLFunctions.SelbergClass.Primon
