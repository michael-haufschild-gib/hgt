import GaloisForLFunctions.HTGeometry.FiniteOPUCReversal
import Mathlib.MeasureTheory.Integral.CircleAverage

/-!
# The positive real-analytic Bernstein--Szegő density

The stable reversed finite OPUC polynomial now yields the literal reciprocal-square density from
the manuscript.  This module proves strict positivity on the multiplicative unit circle and real
analyticity of its angular parametrization.  Normalization and exact finite-moment reproduction
are deliberately left to the next module.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix Polynomial
open scoped ComplexOrder InnerProductSpace ComplexConjugate

noncomputable section

/-- The standard angular parametrization of the multiplicative unit circle. -/
def multiplicativeCircleParam (θ : ℝ) : Circle :=
  ⟨circleMap 0 1 θ, circleMap_mem_sphere 0 zero_le_one θ⟩

@[simp]
theorem multiplicativeCircleParam_coe (θ : ℝ) :
    (multiplicativeCircleParam θ : ℂ) = circleMap 0 1 θ := rfl

/-- The reciprocal-square Bernstein--Szegő density on the unit circle. -/
def bernsteinSzegoDensity {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) (z : Circle) : ℝ :=
  (Complex.normSq ((finiteOPUCReversedPolynomial c hG).eval (z : ℂ)))⁻¹

/-- The same density in the standard angular coordinate. -/
def bernsteinSzegoAngularDensity {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) (θ : ℝ) : ℝ :=
  (Complex.normSq
    ((finiteOPUCReversedPolynomial c hG).eval (circleMap 0 1 θ)))⁻¹

@[simp]
theorem bernsteinSzegoDensity_param {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) (θ : ℝ) :
    bernsteinSzegoDensity c hG (multiplicativeCircleParam θ) =
      bernsteinSzegoAngularDensity c hG θ := rfl

/-- Polynomial evaluation preserves real analyticity under a real-analytic complex-valued
parameter. -/
theorem polynomial_eval_comp_analyticAt (p : Polynomial ℂ) {g : ℝ → ℂ} {x : ℝ}
    (hg : AnalyticAt ℝ g x) :
    AnalyticAt ℝ (fun y => p.eval (g y)) x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simpa only [Polynomial.eval_add] using hp.add hq
  | monomial n a =>
      simpa only [Polynomial.eval_monomial] using
        (analyticAt_const.mul (hg.pow n))

/-- The squared modulus of a polynomial along the standard circle is real analytic. -/
theorem polynomial_normSq_circleMap_analyticOnNhd (p : Polynomial ℂ) :
    AnalyticOnNhd ℝ
      (fun θ : ℝ => Complex.normSq (p.eval (circleMap 0 1 θ))) Set.univ := by
  intro x hx
  simp only [Complex.normSq_apply]
  have hg : AnalyticAt ℝ (fun θ : ℝ => p.eval (circleMap 0 1 θ)) x :=
    polynomial_eval_comp_analyticAt p
      ((analyticOnNhd_circleMap 0 1) x (Set.mem_univ x))
  have hre : AnalyticAt ℝ (fun θ : ℝ => (p.eval (circleMap 0 1 θ)).re) x := by
    simpa [Function.comp_def] using (Complex.reCLM.analyticAt _).comp hg
  have him : AnalyticAt ℝ (fun θ : ℝ => (p.eval (circleMap 0 1 θ)).im) x := by
    simpa [Function.comp_def] using (Complex.imCLM.analyticAt _).comp hg
  exact (hre.mul hre).add (him.mul him)

/-- The Bernstein--Szegő density is strictly positive at every point of the unit circle. -/
theorem bernsteinSzegoDensity_pos {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) (z : Circle) :
    0 < bernsteinSzegoDensity c hG z := by
  apply inv_pos.mpr
  apply Complex.normSq_pos.mpr
  apply finiteOPUCReversedPolynomial_ne_zero_on_closedBall c hG
  simp

/-- The angular Bernstein--Szegő density is globally real analytic. -/
theorem bernsteinSzegoAngularDensity_analyticOnNhd {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) :
    AnalyticOnNhd ℝ (bernsteinSzegoAngularDensity c hG) Set.univ := by
  apply AnalyticOnNhd.inv
  · exact polynomial_normSq_circleMap_analyticOnNhd
      (finiteOPUCReversedPolynomial c hG)
  · intro θ hθ
    exact Complex.normSq_eq_zero.not.mpr
      (finiteOPUCReversedPolynomial_ne_zero_on_closedBall c hG (by simp [norm_circleMap_zero]))

/-- In particular, the density is continuous in the angular coordinate. -/
theorem bernsteinSzegoAngularDensity_continuous {N : ℕ} (c : ℤ → ℂ)
    (hG : (circleToeplitzGram N c).PosDef) :
    Continuous (bernsteinSzegoAngularDensity c hG) :=
  (bernsteinSzegoAngularDensity_analyticOnNhd c hG).continuous

end

end GaloisForLFunctions.HTGeometry
