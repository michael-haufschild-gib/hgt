import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.Coefficients
import Mathlib.FieldTheory.Separable
import Mathlib.RingTheory.Algebraic.Integral

/-! # A simple specialized root controlling a real polynomial incidence -/
open Polynomial
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section
variable {A : Type*} [CommRing A]

private theorem eval_specialize (φ : A →+* ℝ) (p : A[X]) (y : ℝ) :
    aeval y (p.map (specialize φ)) = p.eval₂ φ y := by
  rw [aeval_def, Polynomial.eval₂_map]
  rfl

/-- At a root of a nonzero specialization, a single new base equation
ensures that every nearby root of a lifted simple factor solves the
original equation. The denominator must stay nonzero. -/
theorem simple_factor_certificate (φ : A →+* ℝ) (p : A[X]) (y : ℝ)
    (hp : p.eval₂ φ y = 0) (hn : p.map (specialize φ) ≠ 0) :
    ∃ g d : A, ∃ P : A[X], φ g = 0 ∧ φ d ≠ 0 ∧ P.eval₂ φ y = 0 ∧
      P.derivative.eval₂ φ y ≠ 0 ∧ ∀ (ψ : A →+* ℝ) (z : ℝ),
        ψ g = 0 → ψ d ≠ 0 → P.eval₂ ψ z = 0 → p.eval₂ ψ z = 0 := by
  let F := valueField φ
  let M := minpoly F y
  have hr : aeval y (p.map (specialize φ)) = 0 := (eval_specialize ..).trans hp
  have hi : IsIntegral F y := IsAlgebraic.isIntegral ⟨_,hn,hr⟩
  obtain ⟨q,hq⟩ := minpoly.dvd F y hr
  obtain ⟨a,ha,P,hP⟩ := clear_polynomial φ M
  obtain ⟨b,hb,Q,hQ⟩ := clear_polynomial φ q
  let R := C (a*b)*p-P*Q
  have hmul : R.map (specialize φ) = 0 := by
    dsimp only [R]
    rw [Polynomial.map_sub,Polynomial.map_mul,Polynomial.map_C,Polynomial.map_mul,hP,hQ,hq,map_mul,map_mul]
    ring
  have hreal : R.map φ = 0 := by
    change R.map ((valueField φ).subtype.comp (specialize φ)) = 0
    rw [←Polynomial.map_map,hmul,Polynomial.map_zero]
  refine ⟨coefficientSquares R,a*b,P,(coefficientSquares_zero_iff ..).2 hreal,?_,?_,?_,?_⟩
  · rw [map_mul]; exact mul_ne_zero ha hb
  · rw [←eval_specialize,hP,map_mul,minpoly.aeval,mul_zero]
  · rw [←eval_specialize,←Polynomial.derivative_map,hP,Polynomial.derivative_C_mul,map_mul,aeval_C]
    exact mul_ne_zero ha ((minpoly.irreducible hi).separable.aeval_derivative_ne_zero (minpoly.aeval F y))
  · intro ψ z hg hd hz
    have hmap := (coefficientSquares_zero_iff ..).1 hg
    have he := congrArg (Polynomial.eval z) hmap
    rw [eval_map,eval_zero] at he
    simp only [R,eval₂_sub,eval₂_mul,eval₂_C,hz,zero_mul,sub_zero] at he
    exact (mul_eq_zero.mp he).resolve_left hd

end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
