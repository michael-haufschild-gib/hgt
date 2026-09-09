import GaloisForLFunctions.HTGeometry.ConservativeDissipativeOperator
import GaloisForLFunctions.HTGeometry.MvPolynomialGradient
import Mathlib.Analysis.InnerProductSpace.PiL2
import GaloisForLFunctions.HTGeometry.PolynomialZeroSetDimension

open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Polynomial directional derivatives expressed through the corpus Kähler gradient. -/
theorem hasDerivAt_polynomial_line (P : MvPolynomial ι ℝ)
    (x v : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s => MvPolynomial.aeval (fun i => x i + s * v i) P)
      (∑ i, mvPolynomialGradientEval (fun j => x j + t * v j) P i * v i) t := by
  classical
  have hd := hasDerivAt_mvPolynomial_eval_curve_real P
    (fun i s => x i + s * v i) v t
    (fun i => by simpa using ((hasDerivAt_id t).mul_const (v i)).const_add (x i))
  simpa only [mvPolynomialGradientEval_apply, MvPolynomial.aeval_eq_eval] using hd


/-- The finite real realization of the existing finitely supported polynomial gradient. -/
def polynomialForce (P : MvPolynomial ι ℝ) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun i => mvPolynomialGradientEval (fun j => x j) P i)

/-- A dissipative vector field for every real multivariate polynomial, of any degree. -/
def polynomialField (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (P : MvPolynomial ι ℝ) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  generator A B (polynomialForce P x)

/-- Every polynomial has an exact, nonpositive directional derivative along its field. -/
theorem polynomial_directional_dissipation
    (A B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (P : MvPolynomial ι ℝ) (x : EuclideanSpace ℝ ι) :
    HasDerivAt
      (fun t => MvPolynomial.aeval (fun i => x i + t * polynomialField A B P x i) P)
      (-‖B (polynomialForce P x)‖ ^ 2) 0 := by
  have hd := hasDerivAt_polynomial_line P (fun i => x i)
    (fun i => polynomialField A B P x i) 0
  have hp := generator_power A B (polynomialForce P x)
  simp only [RCLike.re_to_real] at hp
  have hi : (∑ i, mvPolynomialGradientEval (fun j => x j) P i *
      polynomialField A B P x i) =
      ⟪polynomialForce P x, generator A B (polynomialForce P x)⟫_ℝ := by
    simp [PiLp.inner_apply, polynomialForce, polynomialField, mul_comm]
  simpa only [zero_mul, add_zero, hi, hp] using hd

/-- Polynomial equilibria satisfy an exact intersection-of-kernels condition. -/
theorem polynomialField_eq_zero_iff
    (A B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (P : MvPolynomial ι ℝ) (x : EuclideanSpace ℝ ι) :
    polynomialField A B P x = 0 ↔
      B (polynomialForce P x) = 0 ∧ conservative A (polynomialForce P x) = 0 :=
  generator_eq_zero_iff A B (polynomialForce P x)

/-- An arbitrary constant offset is invisible to polynomial dynamics. -/
theorem polynomialField_add_constant
    (A B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (P : MvPolynomial ι ℝ) (c : ℝ) (x : EuclideanSpace ℝ ι) :
    polynomialField A B (P + MvPolynomial.C c) x = polynomialField A B P x := by
  simp [polynomialField, polynomialForce, mvPolynomialGradientEval_add]

/-- Additive energies yield additive fields, including mixed quadratic–higher-order models. -/
theorem polynomialField_add
    (A B : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)
    (P Q : MvPolynomial ι ℝ) (x : EuclideanSpace ℝ ι) :
    polynomialField A B (P + Q) x = polynomialField A B P x + polynomialField A B Q x := by
  unfold polynomialField
  rw [show polynomialForce (P + Q) x = polynomialForce P x + polynomialForce Q x from by
    ext i; simp [polynomialForce, mvPolynomialGradientEval_add]]
  exact map_add _ _ _

end
end GaloisForLFunctions.HTGeometry.SchafferExl
