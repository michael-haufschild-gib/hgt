import GaloisForLFunctions.RHTower.SelbergScatteringPolynomialReality
import GaloisForLFunctions.HTGeometry.ExponentialPolynomialZeroBound

/-!
# Divergent separation of polynomially transformed scattering energies

For every nonconstant complex polynomial, the imaginary part along the native
critical scattering parabola is a nonconstant real polynomial. Its absolute
value tends to infinity, giving a lower bound uniform over the entire real axis.
-/

open Complex Polynomial Set Filter
open GaloisForLFunctions.HTGeometry.ExpZeroBound

namespace RHTower.SelbergScatteringPolynomialReality
noncomputable section


/-- A nonconstant polynomial of the native critical Casimir has nonconstant imaginary part. -/
theorem imaginary_polynomial_degree_pos (P : Polynomial ℂ) (hP : 0 < P.natDegree) :
    0 < (imPoly (P.comp casimirPolynomial)).degree := by
  by_contra hdeg
  let b : ℝ := (imPoly (P.comp casimirPolynomial)).coeff 0
  have hR : imPoly (P.comp casimirPolynomial) = C b :=
    Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hdeg)
  have hvalue (t : ℝ) : (P.eval (criticalCasimir t)).im = b := by
    have h := eval_imPoly (P.comp casimirPolynomial) t
    rw [hR, Polynomial.eval_C] at h
    simpa only [Polynomial.eval_comp, eval_casimirPolynomial] using h.symm
  have hreal (t : ℝ) :
      ((P - C (I * (b : ℂ))).eval (criticalCasimir t)).im = 0 := by
    simp [hvalue]
  have hinf : Set.Infinite {t : ℝ |
      ((P - C (I * (b : ℂ))).eval (criticalCasimir t)).im = 0} := by
    simpa only [hreal, Set.setOf_true] using
      (Set.infinite_univ : Set.Infinite (Set.univ : Set ℝ))
  obtain ⟨c, hc⟩ := constant_of_infinite_real_locus (P - C (I * (b : ℂ))) hinf
  have hconst : P = C ((c : ℂ) + I * (b : ℂ)) := by
    calc P = (P - C (I * (b : ℂ))) + C (I * (b : ℂ)) := by ring
      _ = C ((c : ℂ) + I * (b : ℂ)) := by rw [hc, Polynomial.C_add]
  rw [hconst, Polynomial.natDegree_C] at hP
  omega

/-- The imaginary part grows unboundedly in absolute value along the native critical scattering parabola. -/
theorem abs_imaginary_tendsto_atTop (P : Polynomial ℂ) (hP : 0 < P.natDegree) :
    Tendsto (fun t : ℝ => |(P.eval (criticalCasimir t)).im|) atTop atTop := by
  have h := Polynomial.abs_tendsto_atTop (imPoly (P.comp casimirPolynomial))
    (imaginary_polynomial_degree_pos P hP)
  simpa only [eval_imPoly, Polynomial.eval_comp, eval_casimirPolynomial] using h

/-- Every fixed error budget eventually fails uniformly against every real spectral value. -/
theorem eventually_far_from_real (P : Polynomial ℂ) (hP : 0 < P.natDegree) (M : ℝ) :
    ∃ B : ℝ, ∀ t : ℝ, B ≤ t → ∀ r : ℝ,
      M < ‖P.eval (criticalCasimir t) - (r : ℂ)‖ := by
  have he := (abs_imaginary_tendsto_atTop P hP).eventually (eventually_gt_atTop M)
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.mp he
  refine ⟨B, fun t ht r => (hB t ht).trans_le ?_⟩
  simpa only [Complex.sub_im, Complex.ofReal_im, sub_zero] using
    Complex.abs_im_le_norm (P.eval (criticalCasimir t) - (r : ℂ))

end
end RHTower.SelbergScatteringPolynomialReality
