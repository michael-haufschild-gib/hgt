import GaloisForLFunctions.HTGeometry.FokasLenellsRawOddPrimitives

/-!
# Reflection identities for the actual odd-data scattering primitives

Only the odd part of the third coefficient and the even part of the fourth
coefficient enter the symmetrized fifth integrand. Spatial differentiation
identifies these parts exactly, without evaluating any nested improper integral.
-/

open Complex Matrix MeasureTheory Filter Topology
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section

private theorem equal_from_zero_derivative (f g : ℝ → ℂ)
    (hd : ∀ x, HasDerivAt (fun y => f y-g y) 0 x) (h0 : f 0 = g 0) (x : ℝ) : f x = g x := by
  have hh := is_const_of_deriv_eq_zero (fun y => (hd y).differentiableAt) (fun y => (hd y).deriv) x 0
  change f x-g x = f 0-g 0 at hh
  rw [h0,sub_self] at hh
  exact sub_eq_zero.mp hh

/-- The odd part of the actual third lower primitive is a local cube. -/
theorem rawThirdSlope_oddInitialPart_reflection_difference (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    (rawThirdSlope (oddInitialPart q) 0 (1,0) x).2-
      (rawThirdSlope (oddInitialPart q) 0 (1,0) (-x)).2 = I*(oddInitialPart q x)^3/3 := by
  have h3 (y : ℝ) : HasDerivAt (fun z => (rawThirdSlope (oddInitialPart q) 0 (1,0) z).2)
      (rawThirdIntegrand (oddInitialPart q) 0 (1,0) y).2 y :=
    (ContinuousLinearMap.snd ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt y
      (rawThirdSlope_hasDerivAt (oddInitialPart q) 0 (1,0) y)
  have hz : oddInitialPart q 0 = 0 := by simp
  apply equal_from_zero_derivative
    (fun y => (rawThirdSlope (oddInitialPart q) 0 (1,0) y).2-
      (rawThirdSlope (oddInitialPart q) 0 (1,0) (-y)).2)
    (fun y => I*(oddInitialPart q y)^3/3) ?_ ?_ x
  · intro y
    have hg := ((((oddInitialPart q).hasDerivAt y).pow 3).const_mul I).div_const 3
    have hh := ((h3 y).sub ((h3 (-y)).scomp y (hasDerivAt_id y).neg)).sub hg
    convert! hh using 1
    simp only [rawThirdIntegrand_zero_lower,rawMixedPrimitive_oddInitialPart,
      oddInitialPart_reflection,deriv_oddInitialPart_reflection,hz,
      Complex.ofReal_neg,neg_one_smul]
    ring
  · simp [hz]

/-- The actual fourth upper component exposes exactly the lower third primitive. -/
theorem rawFourthIntegrand_oddInitialPart_zero_first (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    (rawFourthIntegrand (oddInitialPart q) 0 (1,0) x).1 =
      -I*deriv (oddInitialPart q) x*(rawThirdSlope (oddInitialPart q) 0 (1,0) x).2-
        2*I*(x : ℂ)*deriv (oddInitialPart q) x*oddInitialPart q x := by
  have hz : oddInitialPart q 0 = 0 := by simp
  simp only [rawFourthIntegrand,Complex.ofReal_zero,zero_smul,add_zero,rawSolutionSlope_zero,
    rawLinearCoefficient,rawLinearPrimitive,rawDividedOperator_apply,rawCubicOperator_zero_apply,
    Prod.fst_add,Prod.snd_sub,reflectedDerivative_oddInitialPart,hz,
    zero_pow (by omega : 2 ≠ 0),mul_zero,neg_zero,FDNLS.staggerPhase,
    zero_mul,Complex.exp_zero,mul_one]
  ring

/-- The even part of the genuine fourth primitive is a local fourth power. -/
theorem rawFourthSlope_oddInitialPart_reflection_sum (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    (rawFourthSlope (oddInitialPart q) 0 (1,0) x).1+
      (rawFourthSlope (oddInitialPart q) 0 (1,0) (-x)).1 = (oddInitialPart q x)^4/12 := by
  have h4 (y : ℝ) : HasDerivAt (fun z => (rawFourthSlope (oddInitialPart q) 0 (1,0) z).1)
      (rawFourthIntegrand (oddInitialPart q) 0 (1,0) y).1 y :=
    (ContinuousLinearMap.fst ℝ ℂ ℂ).hasFDerivAt.comp_hasDerivAt y
      (rawFourthSlope_hasDerivAt (oddInitialPart q) 0 (1,0) y)
  apply equal_from_zero_derivative
    (fun y => (rawFourthSlope (oddInitialPart q) 0 (1,0) y).1+
      (rawFourthSlope (oddInitialPart q) 0 (1,0) (-y)).1)
    (fun y => (oddInitialPart q y)^4/12) ?_ ?_ x
  · intro y
    have he := congrArg (fun z : ℂ => -I*deriv (oddInitialPart q) y*z)
      (rawThirdSlope_oddInitialPart_reflection_difference q y)
    have hi : -I*deriv (oddInitialPart q) y*(I*(oddInitialPart q y)^3/3) =
        (oddInitialPart q y)^3*deriv (oddInitialPart q) y/3 := by
      ring_nf
      simp only [I_sq]
      ring
    rw [hi,mul_sub] at he
    have hg := (((oddInitialPart q).hasDerivAt y).pow 4).div_const 12
    have hh := ((h4 y).add ((h4 (-y)).scomp y (hasDerivAt_id y).neg)).sub hg
    convert! hh using 1
    simp only [rawFourthIntegrand_oddInitialPart_zero_first,Complex.ofReal_neg,
      oddInitialPart_reflection,deriv_oddInitialPart_reflection,neg_one_smul]
    linear_combination -he
  · simp [rawFourthSlope]

/-- Symmetrization removes every nested fifth-order term, leaving only two local densities. -/
theorem rawFifthIntegrand_oddInitialPart_symmetrization (q : SchwartzMap ℝ ℂ) (x : ℝ) :
    (rawFifthIntegrand (oddInitialPart q) 0 (1,0) x).2+
      (rawFifthIntegrand (oddInitialPart q) 0 (1,0) (-x)).2 =
      I*(oddInitialPart q x)^4*deriv (oddInitialPart q) x/12-
        4*I*(x : ℂ)^2*deriv (oddInitialPart q) x := by
  have he := congrArg (fun z : ℂ => I*deriv (oddInitialPart q) x*z)
    (rawFourthSlope_oddInitialPart_reflection_sum q x)
  simp only [rawFifthIntegrand,rawDividedOperator_apply,rawCubicOperator_zero_apply,
    rawQuinticOperator_zero_apply,rawSecondSlope_oddInitialPart_zero,
    rawInteractionSolution_zero_frequency,Prod.snd_add,
    zero_pow (by omega : 2 ≠ 0),mul_zero,neg_zero,FDNLS.staggerPhase,
    Complex.ofReal_zero,zero_mul,Complex.exp_zero,mul_one,
    SchwartzMap.derivCLM_apply,deriv_oddInitialPart_reflection,oddInitialPart_reflection,
    Complex.ofReal_neg]
  have hs (c : ℂ) : ((c • ((1 : ℂ),0) : SpectralVector)).1 = c := by
    change c*1 = c
    exact mul_one c
  simp only [hs]
  change I*deriv (oddInitialPart q) x*(rawFourthSlope (oddInitialPart q) 0 (1,0) x).1+
    -2*(x : ℂ)*deriv (oddInitialPart q) x*((oddInitialPart q x)^2/2)+
    -2*I*(x : ℂ)^2*deriv (oddInitialPart q) x+
    (I*deriv (oddInitialPart q) x*(rawFourthSlope (oddInitialPart q) 0 (1,0) (-x)).1+
    -2*(-(x : ℂ))*deriv (oddInitialPart q) x*((-oddInitialPart q x)^2/2)+
    -2*I*(-(x : ℂ))^2*deriv (oddInitialPart q) x) = _
  linear_combination he

end
end GaloisForLFunctions.HTGeometry.FokasLenells
