import GaloisForLFunctions.HTGeometry.MeromorphicGammaReflection

/-!
# The entire reflection core of the signed Beta kernel

Dividing the three signed Beta terms by `Γ(r)Γ(t)Γ(1-r-t)`
produces a sum of reciprocal-Gamma products. This expression is entire,
including at the poles of the original Beta terms. Euler reflection and
the trigonometric identity in Li--Liu, Lemma 4.2, factor it globally into
two sine factors and one cosine factor.
-/

namespace GaloisForLFunctions.Goldbach

open Complex

noncomputable section

/-- The reciprocal-Gamma regularization of the signed Beta combination. -/
def signedBetaReflectionCore (r t : ℂ) : ℂ :=
  reciprocalGammaEntire t * reciprocalGammaEntire (r + (1 - r - t)) +
    reciprocalGammaEntire r * reciprocalGammaEntire (t + (1 - r - t)) -
      reciprocalGammaEntire (1 - r - t) * reciprocalGammaEntire (r + t)

/-- Euler reflection removes all Gamma factors from the regularized kernel. -/
theorem signedBetaReflectionCore_eq_sine_sum (r t : ℂ) :
    signedBetaReflectionCore r t =
      (sin ((Real.pi : ℂ) * r) + sin ((Real.pi : ℂ) * t) -
        sin ((Real.pi : ℂ) * (1 - r - t))) / (Real.pi : ℂ) := by
  unfold signedBetaReflectionCore
  rw [show r + (1 - r - t) = 1 - t by ring,
    show t + (1 - r - t) = 1 - r by ring,
    show r + t = 1 - (1 - r - t) by ring,
    reciprocalGammaEntire_mul_one_sub, reciprocalGammaEntire_mul_one_sub,
    reciprocalGammaEntire_mul_one_sub]
  ring

private theorem signed_sine_factorization (a b : ℂ) :
    sin a + sin b - sin (a + b) =
      4 * sin (a / 2) * sin (b / 2) * sin ((a + b) / 2) := by
  have hs := sin_two_mul ((a + b) / 2)
  rw [show 2 * ((a + b) / 2) = a + b by ring] at hs
  have hc := cos_sub_cos ((a - b) / 2) ((a + b) / 2)
  rw [show ((a - b) / 2 + (a + b) / 2) / 2 = a / 2 by ring,
    show ((a - b) / 2 - (a + b) / 2) / 2 = -(b / 2) by ring,
    sin_neg] at hc
  rw [sin_add_sin, hs]
  calc
    _ = 2 * sin ((a + b) / 2) * (cos ((a - b) / 2) - cos ((a + b) / 2)) := by ring
    _ = _ := by rw [hc]; ring

/-- The signed-Beta trigonometric factorization holds globally after regularization. -/
theorem signedBetaReflectionCore_factorization (r t : ℂ) :
    signedBetaReflectionCore r t =
      (4 / (Real.pi : ℂ)) * sin ((Real.pi : ℂ) * r / 2) *
        sin ((Real.pi : ℂ) * t / 2) * cos ((Real.pi : ℂ) * (1 - r - t) / 2) := by
  simp only [signedBetaReflectionCore_eq_sine_sum,
    show (Real.pi : ℂ) * (1 - r - t) =
      (Real.pi : ℂ) - ((Real.pi : ℂ) * r + (Real.pi : ℂ) * t) by ring,
    sin_pi_sub, signed_sine_factorization,
    show ((Real.pi : ℂ) - ((Real.pi : ℂ) * r + (Real.pi : ℂ) * t)) / 2 =
      (Real.pi : ℂ) / 2 - ((Real.pi : ℂ) * r + (Real.pi : ℂ) * t) / 2 by ring,
    cos_pi_div_two_sub]
  ring

/-- The regularized kernel is entire in its first variable. -/
theorem signedBetaReflectionCore_differentiable_left (t : ℂ) :
    Differentiable ℂ (fun r => signedBetaReflectionCore r t) := by
  simp only [signedBetaReflectionCore_factorization]
  fun_prop

/-- The regularized kernel is entire in its second variable. -/
theorem signedBetaReflectionCore_differentiable_right (r : ℂ) :
    Differentiable ℂ (signedBetaReflectionCore r) := by
  simp only [signedBetaReflectionCore_factorization]
  fun_prop

/-- The three trigonometric factors account for every zero of the entire core. -/
theorem signedBetaReflectionCore_eq_zero_iff (r t : ℂ) :
    signedBetaReflectionCore r t = 0 ↔
      sin ((Real.pi : ℂ) * r / 2) = 0 ∨ sin ((Real.pi : ℂ) * t / 2) = 0 ∨
        cos ((Real.pi : ℂ) * (1 - r - t) / 2) = 0 := by
  have hpi : (Real.pi : ℂ) ≠ 0 := ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [signedBetaReflectionCore_factorization]
  simp only [mul_eq_zero, div_eq_zero_iff, hpi, false_or, or_false,
    show (4 : ℂ) ≠ 0 by norm_num]
  tauto

end

end GaloisForLFunctions.Goldbach

-- Temporary dependency audit.
#print axioms GaloisForLFunctions.Goldbach.signedBetaReflectionCore
#print axioms GaloisForLFunctions.Goldbach.signedBetaReflectionCore_eq_sine_sum
#print axioms GaloisForLFunctions.Goldbach.signedBetaReflectionCore_factorization
#print axioms GaloisForLFunctions.Goldbach.signedBetaReflectionCore_differentiable_left
#print axioms GaloisForLFunctions.Goldbach.signedBetaReflectionCore_differentiable_right
#print axioms GaloisForLFunctions.Goldbach.signedBetaReflectionCore_eq_zero_iff
