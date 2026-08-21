import GaloisForLFunctions.HTGeometry.BorelWeil.RegularFunctions
import Mathlib.Algebra.Polynomial.AlgebraMap

/-!
# Regular functions along polynomial curves

A regular function on `SL(n,k)` restricted to a curve whose matrix entries depend polynomially on
a parameter is a polynomial in that parameter.  The affine case `M s = A + s • B` is the only one
needed for the rank-one analysis of Borel–Weil sections.

## Main results

* `GaloisForLFunctions.HTGeometry.BorelWeil.exists_poly_of_matrixPoly`
* `GaloisForLFunctions.HTGeometry.BorelWeil.exists_poly_of_affine`
-/

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {k : Type*} [CommRing k]

/-- A regular function evaluated along a curve with polynomial matrix entries is a polynomial. -/
theorem exists_poly_of_matrixPoly {f : SpecialLinearGroup n k → k} (hf : f ∈ regularFun n k)
    (P : Matrix n n (Polynomial k)) (M : k → SpecialLinearGroup n k)
    (hM : ∀ s : k, ∀ a b : n, (M s : Matrix n n k) a b = (P a b).eval s) :
    ∃ q : Polynomial k, ∀ s : k, f (M s) = q.eval s := by
  obtain ⟨p, rfl⟩ := hf
  refine ⟨MvPolynomial.aeval (fun ab : n × n => P ab.1 ab.2) p, fun s => ?_⟩
  have h1 : (coordEval n k) p (M s)
      = MvPolynomial.aeval (fun ab : n × n => (M s : Matrix n n k) ab.1 ab.2) p := by
    have := MvPolynomial.comp_aeval (R := k)
      (fun ab : n × n => (coordFun ab.1 ab.2 : SpecialLinearGroup n k → k))
      (Pi.evalAlgHom k (fun _ : SpecialLinearGroup n k => k) (M s))
    exact congrFun (congrArg (fun φ : MvPolynomial (n × n) k →ₐ[k] k => (φ : _ → k)) this) p
  have h2 : (Polynomial.aeval s)
      (MvPolynomial.aeval (fun ab : n × n => P ab.1 ab.2) p)
      = MvPolynomial.aeval (fun ab : n × n => (P ab.1 ab.2).eval s) p := by
    have := MvPolynomial.comp_aeval (R := k) (fun ab : n × n => P ab.1 ab.2)
      (Polynomial.aeval (R := k) s)
    have h3 := congrFun (congrArg (fun φ : MvPolynomial (n × n) k →ₐ[k] k => (φ : _ → k)) this) p
    simpa [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map] using h3
  have hgoal : ((coordEval n k).toRingHom p) (M s) = (coordEval n k) p (M s) := rfl
  rw [hgoal, h1]
  have h4 : (Polynomial.aeval s) (MvPolynomial.aeval (fun ab : n × n => P ab.1 ab.2) p)
      = (MvPolynomial.aeval (fun ab : n × n => P ab.1 ab.2) p).eval s := by
    simp [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map]
  rw [← h4, h2]
  exact congrArg (fun F : n × n → k => MvPolynomial.aeval F p)
    (funext fun ab : n × n => hM s ab.1 ab.2)

/-- The affine case: a regular function along `s ↦ A + s • B` is a polynomial in `s`. -/
theorem exists_poly_of_affine {f : SpecialLinearGroup n k → k} (hf : f ∈ regularFun n k)
    (A B : Matrix n n k) (M : k → SpecialLinearGroup n k)
    (hM : ∀ s : k, (M s : Matrix n n k) = A + s • B) :
    ∃ q : Polynomial k, ∀ s : k, f (M s) = q.eval s := by
  refine exists_poly_of_matrixPoly hf
    (Matrix.of fun a b => Polynomial.C (A a b) + Polynomial.C (B a b) * Polynomial.X) M ?_
  intro s a b
  rw [hM s]
  simp only [Matrix.of_apply, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end GaloisForLFunctions.HTGeometry.BorelWeil
