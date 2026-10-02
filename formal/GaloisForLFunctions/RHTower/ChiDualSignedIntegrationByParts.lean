import GaloisForLFunctions.RHTower.VanDerCorputIBP

open Complex Set Filter Topology MeasureTheory
noncomputable section
namespace RHTower


/-- The exact signed oscillatory integration-by-parts split, before taking
separate endpoint norms. This retains cancellation between opposite Fourier modes. -/
theorem integral_cexp_eq_of_antiderivative
    {a b : ℝ} {φ φ' : ℝ → ℝ} {A B B' : ℝ → ℂ}
    (hφ : ∀ x ∈ uIcc a b, HasDerivAt φ (φ' x) x)
    (hB : ∀ x ∈ uIcc a b, HasDerivAt B (B' x) x)
    (hB'c : ContinuousOn B' (uIcc a b)) (hAc : ContinuousOn A (uIcc a b))
    (hrel : ∀ x ∈ uIcc a b, B x * (I * (φ' x : ℂ)) = A x) :
    (∫ t in a..b, A t * Complex.exp (I * φ t)) =
      B b * Complex.exp (I * φ b) - B a * Complex.exp (I * φ a) -
        ∫ t in a..b, B' t * Complex.exp (I * φ t) := by
  have hφc : ContinuousOn φ (uIcc a b) := fun x hx =>
    (hφ x hx).continuousAt.continuousWithinAt
  have hVc : ContinuousOn (fun t : ℝ => Complex.exp (I * φ t)) (uIcc a b) :=
    Complex.continuous_exp.comp_continuousOn
      (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn hφc))
  have hVd (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun t : ℝ => Complex.exp (I * φ t))
        (Complex.exp (I * φ x) * (I * (φ' x : ℂ))) x :=
    (((hφ x hx).ofReal_comp).const_mul I).cexp
  have hprod (x : ℝ) (hx : x ∈ uIcc a b) :
      HasDerivAt (fun t : ℝ => B t * Complex.exp (I * φ t))
        (B' x * Complex.exp (I * φ x) + A x * Complex.exp (I * φ x)) x := by
    have hp := (hB x hx).mul (hVd x hx)
    have he : B' x * Complex.exp (I * φ x) +
        B x * (Complex.exp (I * φ x) * (I * (φ' x : ℂ))) =
        B' x * Complex.exp (I * φ x) + A x * Complex.exp (I * φ x) := by
      rw [← hrel x hx]
      ring
    exact he ▸ hp
  have hi1 : IntervalIntegrable (fun t : ℝ => B' t * Complex.exp (I * φ t)) volume a b :=
    (hB'c.mul hVc).intervalIntegrable
  have hi2 : IntervalIntegrable (fun t : ℝ => A t * Complex.exp (I * φ t)) volume a b :=
    (hAc.mul hVc).intervalIntegrable
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hprod (hi1.add hi2)
  rw [intervalIntegral.integral_add hi1 hi2] at hftc
  linear_combination hftc

/-- Two exact integrations by parts keep the combined signed boundary and
the entire final remainder. No endpoint or Fourier mode is discarded. -/
theorem integral_cexp_eq_of_two_antiderivatives
    {a b : ℝ} {φ φ' : ℝ → ℝ} {A B B' C C' : ℝ → ℂ}
    (hφ : ∀ x ∈ uIcc a b, HasDerivAt φ (φ' x) x)
    (hB : ∀ x ∈ uIcc a b, HasDerivAt B (B' x) x)
    (hC : ∀ x ∈ uIcc a b, HasDerivAt C (C' x) x)
    (hAc : ContinuousOn A (uIcc a b)) (hB'c : ContinuousOn B' (uIcc a b))
    (hC'c : ContinuousOn C' (uIcc a b))
    (hrelB : ∀ x ∈ uIcc a b, B x * (I * (φ' x : ℂ)) = A x)
    (hrelC : ∀ x ∈ uIcc a b, C x * (I * (φ' x : ℂ)) = B' x) :
    (∫ t in a..b, A t * Complex.exp (I * φ t)) =
      (B b - C b) * Complex.exp (I * φ b) -
        (B a - C a) * Complex.exp (I * φ a) +
          ∫ t in a..b, C' t * Complex.exp (I * φ t) := by
  rw [integral_cexp_eq_of_antiderivative hφ hB hB'c hAc hrelB,
    integral_cexp_eq_of_antiderivative hφ hC hC'c hB'c hrelC]
  ring

end RHTower
