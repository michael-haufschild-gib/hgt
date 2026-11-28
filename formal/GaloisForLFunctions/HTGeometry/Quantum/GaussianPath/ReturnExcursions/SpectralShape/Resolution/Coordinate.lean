import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.ReturnExcursions.SpectralShape.MomentPolynomial
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.ClockAdjustment.GaussianPair

/-! # Coordinate derivatives of the physical cubic shape constraint -/

open Matrix Finset Polynomial Function WithLp
namespace GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
open Dephasing.PairedFields Dephasing.PairedFields.ClockAdjustment
open private generator_at trace_generator_zero update_squareTrace from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.ClockAdjustment.SitePair
noncomputable section

private abbrev mat {n : ℕ} (p : PathLabel n) := finitePauliMatrix (pathWord p)

/-- Partial derivative of the normalized cubic trace in one Pauli coefficient. -/
def cubicSlope {n : ℕ} (h : Coeff n) (p : PathLabel n) : ℝ :=
  3*squareTrace h p/(2:ℝ)^(n+2)

/-- Partial derivative of the sextic shape constraint, with the target held fixed. -/
def shapeSlope {n : ℕ} (c : ℝ) (h : Coeff n) (p : PathLabel n) : ℝ :=
  2*thirdMoment (toLp 2 h)*cubicSlope h p-6*c*h p*(‖toLp 2 h‖^2)^2

private theorem slope_at {n : ℕ} (h : Coeff n) (p : PathLabel n) (x : ℝ) :
    cubicSlope (update h p x) p=cubicSlope (update h p 0) p := by
  simp only [cubicSlope,update_squareTrace h p p x rfl,finitePauliMatrix_mul_self,mul_one,
    trace_generator_zero,Complex.zero_re,mul_zero,add_zero]

private theorem moment_at {n : ℕ} (h : Coeff n) (p : PathLabel n) (x : ℝ) :
    thirdMoment (toLp 2 (update h p x))=thirdMoment (toLp 2 (update h p 0))+x*cubicSlope (update h p 0) p := by
  let A := (generator (update h p 0)).val
  let P := mat p
  let D := (2:ℝ)^(n+2)
  have hP : P*P=1 := finitePauliMatrix_mul_self _
  have htP : P.trace=0 := finitePauliMatrix_trace_eq_zero_of_ne_identity _ (pathWord_ne_identity p)
  have htA : A.trace=0 := trace_generator_zero _
  have h₁ : (P*A*A).trace=(A*A*P).trace := by rw [mul_assoc,Matrix.trace_mul_comm P (A*A)]
  have h₂ : (A*P*A).trace=(A*A*P).trace := by rw [Matrix.trace_mul_comm (A*P) A,←mul_assoc]
  have h₃ : (P*A*P).trace=0 := by rw [Matrix.trace_mul_comm (P*A) P,←mul_assoc,hP,one_mul,htA]
  have h₄ : (A*P*P).trace=0 := by rw [mul_assoc,hP,mul_one,htA]
  change (((generator (update h p x)).val^3).trace.re/D)=
    (A^3).trace.re/D+x*(3*(A^2*P).trace.re/D)
  rw [generator_at]
  change ((A+(x:ℂ) • P)^3).trace.re/D=_
  simp only [pow_succ,pow_zero,one_mul,add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.trace_add,Matrix.trace_smul,hP,htA,htP,h₁,h₂,h₃,h₄,
    Complex.add_re,smul_eq_mul,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,mul_zero,sub_zero,add_zero]
  ring

private theorem variance_at {n : ℕ} (h : Coeff n) (p : PathLabel n) (x : ℝ) :
    ‖toLp 2 (update h p x)‖^2=‖toLp 2 (update h p 0)‖^2+x^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  have hi (i : PathLabel n) : update h p x i^2=update h p 0 i^2+(if i=p then x^2 else 0) := by
    by_cases he : i=p
    · subst i; simp
    · simp [he]
  change (∑ i, update h p x i^2)=(∑ i, update h p 0 i^2)+x^2
  simp only [hi,sum_add_distrib]
  simp

/-- On every resampled physical coordinate the polynomial and its formal
derivative give the exact discrepancy and the exact coordinate slope. -/
theorem coordinate_polynomial {n : ℕ} (c : ℝ) (h : Coeff n) (p : PathLabel n) :
    ∃ Q : ℂ[X], Q.natDegree≤6 ∧ ∀ x : ℝ,
      Q.eval (x:ℂ)=(skewConstraint c (toLp 2 (update h p x)):ℂ) ∧
      Q.derivative.eval (x:ℂ)=(shapeSlope c (update h p x) p:ℂ) := by
  let y := update h p 0
  let a := cubicSlope y p
  let b := thirdMoment (toLp 2 y)
  let d := ‖toLp 2 y‖^2
  let M : ℂ[X] := C (b:ℂ)+C (a:ℂ)*X
  let V : ℂ[X] := C (d:ℂ)+X^2
  refine ⟨M^2-C (c:ℂ)*V^3,?_,?_⟩
  · dsimp only [M,V]
    compute_degree
  · intro x
    constructor
    · simp [M,V,skewConstraint,moment_at h p x,variance_at h p x,a,b,d,y]
      ring
    · simp only [shapeSlope,Function.update_self,moment_at h p x,slope_at h p x,variance_at h p x,
        M,V,derivative_sub,derivative_pow,derivative_add,derivative_C,
        derivative_X,derivative_C_mul,eval_sub,eval_add,eval_mul,eval_pow,eval_C,eval_X,
        Nat.cast_ofNat,zero_add,Nat.reduceSub,pow_one,mul_one]
      dsimp only [a,b,d,y]
      push_cast
      ring

/-- The derivative along rotation of the two onsite fields cancels all dependence
on the proposed shape. Its residue is the product of two observed physical traces. -/
theorem rotation_slope {n : ℕ} (c : ℝ) (h : Coeff n) (e : Fin (n+1)) :
    let p := leftSite e 0
    let q := rightSite e 0
    h p*shapeSlope c h q-h q*shapeSlope c h p=
      6*thirdMoment (toLp 2 h)*edgeResponse h e 0 0/(2:ℝ)^(n+2) := by
  intro p q
  dsimp only [shapeSlope,cubicSlope,edgeResponse,p,q]
  ring

#print axioms coordinate_polynomial
#print axioms rotation_slope
end
end GaloisForLFunctions.HTGeometry.ReturnExcursions.SpectralShape
