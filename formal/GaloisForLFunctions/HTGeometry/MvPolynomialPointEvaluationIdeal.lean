import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.Polynomial.Ideal
import Mathlib.Tactic

/-!
# Point-evaluation ideals over a polynomial base

An ideal of `MvPolynomial J ℂ[X]` containing the base parameter `X` and every shifted coordinate
`X j - d j` contains the complete kernel of evaluation at `(0,d)`. The proof is constructive,
using polynomial divisibility and induction over multivariate polynomials.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {J : Type*}

/-- Evaluate the polynomial base at zero and the multivariate coordinates at `d`. -/
def mvPolynomialBaseZeroPointEval (d : J → ℂ) :
    MvPolynomial J (Polynomial ℂ) →+* ℂ :=
  MvPolynomial.eval₂Hom (Polynomial.evalRingHom 0) d

/-- Reduction modulo the point generators to the constant point value. -/
theorem mvPolynomial_sub_baseZeroPointEval_mem
    (d : J → ℂ) (Q : Ideal (MvPolynomial J (Polynomial ℂ)))
    (hu : MvPolynomial.C Polynomial.X ∈ Q)
    (hX : ∀ j, MvPolynomial.X j - MvPolynomial.C (Polynomial.C (d j)) ∈ Q)
    (f : MvPolynomial J (Polynomial ℂ)) :
    f - MvPolynomial.C (Polynomial.C (mvPolynomialBaseZeroPointEval d f)) ∈ Q := by
  induction f using MvPolynomial.induction_on with
  | C r =>
      obtain ⟨s, hs⟩ := Polynomial.X_sub_C_dvd_sub_C_eval (p := r) (a := 0)
      have hdiv : Polynomial.X ∣ r - Polynomial.C (r.eval 0) := by
        refine ⟨s, ?_⟩
        simpa using hs
      obtain ⟨s, hs⟩ := hdiv
      have hm := Q.mul_mem_right (MvPolynomial.C s) hu
      rw [← map_mul, ← hs] at hm
      simpa [mvPolynomialBaseZeroPointEval] using hm
  | add p q hp hq =>
      have h := Q.add_mem hp hq
      have heval :
          mvPolynomialBaseZeroPointEval d (p + q) =
            mvPolynomialBaseZeroPointEval d p + mvPolynomialBaseZeroPointEval d q :=
        (mvPolynomialBaseZeroPointEval d).map_add p q
      rw [heval, Polynomial.C_add, MvPolynomial.C_add]
      (convert h using 1; abel)
  | mul_X p j hp =>
      have h1 := Q.mul_mem_right (MvPolynomial.X j) hp
      have h2 := Q.mul_mem_left
        (MvPolynomial.C (Polynomial.C (mvPolynomialBaseZeroPointEval d p))) (hX j)
      have h := Q.add_mem h1 h2
      have heval :
          mvPolynomialBaseZeroPointEval d (p * MvPolynomial.X j) =
            mvPolynomialBaseZeroPointEval d p * d j := by
        simp [mvPolynomialBaseZeroPointEval]
      rw [heval, Polynomial.C_mul, MvPolynomial.C_mul]
      (convert h using 1; ring)

/-- Every polynomial vanishing at `(0,d)` belongs to an ideal containing the point generators. -/
theorem mvPolynomial_mem_of_baseZeroPointEval_eq_zero
    (d : J → ℂ) (Q : Ideal (MvPolynomial J (Polynomial ℂ)))
    (hu : MvPolynomial.C Polynomial.X ∈ Q)
    (hX : ∀ j, MvPolynomial.X j - MvPolynomial.C (Polynomial.C (d j)) ∈ Q)
    {f : MvPolynomial J (Polynomial ℂ)}
    (hf : mvPolynomialBaseZeroPointEval d f = 0) : f ∈ Q := by
  simpa [hf] using mvPolynomial_sub_baseZeroPointEval_mem d Q hu hX f

end

end GaloisForLFunctions.HTGeometry
