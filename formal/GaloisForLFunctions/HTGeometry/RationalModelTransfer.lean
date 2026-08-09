import GaloisForLFunctions.HTGeometry.PolynomialCascadeModel
import GaloisForLFunctions.HTGeometry.ProductLawFractionModel

/-!
# The analytic transfer for a law with denominators

The polynomial-model transfer needs the cascade's law to be polynomial in the states.  A first-order
equation with *rational* coefficients gives a law with denominators, and its jets are rational
functions of the states.

What survives is the cleared form: each jet has a numerator and a common denominator, both
polynomial, with

`B(states(z))·(d^i/dz^i)(Y_N)(z) = A_i(states(z))`

pointwise, and `B·v_i = A_i` in the rational model.  A polynomial expression in the jets then clears
by a power of `B`, by an induction whose three cases are exactly the three cases of a polynomial
induction — and the cleared numerator is nonzero as soon as the jets are algebraically independent.
That is all the transfer needs.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {Y : ℕ → ℂ → ℂ}

/-- **Clearing denominators in a polynomial expression of rational jets.**  A power of the common
denominator turns it into a polynomial in the states, compatibly with both the model and the
pointwise values. -/
theorem exists_clear {K : ℕ} {A : Fin K → MvPolynomial ℕ ℂ} {B : MvPolynomial ℕ ℂ}
    {v : Fin K → CascadeField} {w : ℂ → Fin K → ℂ}
    (hv : ∀ j, algebraMap (MvPolynomial ℕ ℂ) CascadeField B * v j
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField (A j))
    (hw : ∀ (j : Fin K) (z : ℂ), evalAt Y z B * w z j = evalAt Y z (A j))
    (P : MvPolynomial (Fin K) ℂ) :
    ∃ (C : MvPolynomial ℕ ℂ) (k : ℕ),
      algebraMap (MvPolynomial ℕ ℂ) CascadeField C
          = algebraMap (MvPolynomial ℕ ℂ) CascadeField (B ^ k) * MvPolynomial.aeval v P
        ∧ ∀ z : ℂ, (evalAt Y z B) ^ k * MvPolynomial.eval (w z) P = evalAt Y z C := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      refine ⟨MvPolynomial.C a, 0, ?_, ?_⟩
      · rw [pow_zero, map_one, one_mul, MvPolynomial.aeval_C]
        rfl
      · intro z
        rw [pow_zero, one_mul, MvPolynomial.eval_C]
        simp [evalAt]
  | add p q hp hq =>
      obtain ⟨Cp, kp, hp1, hp2⟩ := hp
      obtain ⟨Cq, kq, hq1, hq2⟩ := hq
      refine ⟨B ^ (max kp kq - kp) * Cp + B ^ (max kp kq - kq) * Cq, max kp kq, ?_, ?_⟩
      · rw [map_add, map_mul, map_mul, hp1, hq1, map_add, ← mul_assoc, ← mul_assoc,
          ← map_mul, ← map_mul, ← pow_add, ← pow_add,
          show max kp kq - kp + kp = max kp kq by omega,
          show max kp kq - kq + kq = max kp kq by omega]
        ring
      · intro z
        have h1 : evalAt Y z (B ^ (max kp kq - kp) * Cp)
            = (evalAt Y z B) ^ (max kp kq) * MvPolynomial.eval (w z) p := by
          rw [map_mul, map_pow, ← hp2 z, ← mul_assoc, ← pow_add,
            show max kp kq - kp + kp = max kp kq by omega]
        have h2 : evalAt Y z (B ^ (max kp kq - kq) * Cq)
            = (evalAt Y z B) ^ (max kp kq) * MvPolynomial.eval (w z) q := by
          rw [map_mul, map_pow, ← hq2 z, ← mul_assoc, ← pow_add,
            show max kp kq - kq + kq = max kp kq by omega]
        rw [map_add (evalAt Y z) (B ^ (max kp kq - kp) * Cp) (B ^ (max kp kq - kq) * Cq),
          h1, h2, map_add (MvPolynomial.eval (w z)) p q, mul_add]
  | mul_X p j hp =>
      obtain ⟨Cp, kp, hp1, hp2⟩ := hp
      refine ⟨Cp * A j, kp + 1, ?_, ?_⟩
      · rw [map_mul (algebraMap (MvPolynomial ℕ ℂ) CascadeField) Cp (A j), hp1, ← hv j,
          map_mul (MvPolynomial.aeval v) p (MvPolynomial.X j), MvPolynomial.aeval_X,
          pow_succ, map_mul (algebraMap (MvPolynomial ℕ ℂ) CascadeField) (B ^ kp) B]
        ring
      · intro z
        have h1 : evalAt Y z (Cp * A j)
            = (evalAt Y z B) ^ (kp + 1) * (MvPolynomial.eval (w z) p * w z j) := by
          rw [map_mul, ← hp2 z, ← hw j z, pow_succ]
          ring
        rw [map_mul (MvPolynomial.eval (w z)) p (MvPolynomial.X j), MvPolynomial.eval_X, h1]

/-- **The analytic transfer for a law with denominators.** -/
theorem not_differentiallyAlgebraicOfOrder_of_ratModel {N m : ℕ}
    {A : Fin (m + 2) → MvPolynomial ℕ ℂ} {B : MvPolynomial ℕ ℂ} (hB : B ≠ 0)
    {v : Fin (m + 2) → CascadeField}
    (hv : ∀ j, algebraMap (MvPolynomial ℕ ℂ) CascadeField B * v j
      = algebraMap (MvPolynomial ℕ ℂ) CascadeField (A j))
    (hw : ∀ (j : Fin (m + 2)) (z : ℂ),
      evalAt Y z B
        * (Fin.cons z (fun i : Fin (m + 1) => iteratedDeriv (i : ℕ) (Y N) z) : Fin (m + 2) → ℂ) j
        = evalAt Y z (A j))
    (hind : ∀ Q : MvPolynomial ℕ ℂ, Q ≠ 0 → ∃ z : ℂ, evalAt Y z Q ≠ 0)
    (hindep : AlgebraicIndependent ℂ v) :
    ¬ DifferentiallyAlgebraicOfOrder (Y N) m := by
  rintro ⟨P, hP0, hPz⟩
  obtain ⟨C, k, hC1, hC2⟩ :=
    exists_clear (Y := Y) (w := fun z => (Fin.cons z
      (fun i : Fin (m + 1) => iteratedDeriv (i : ℕ) (Y N) z) : Fin (m + 2) → ℂ)) hv hw P
  have haev : MvPolynomial.aeval v P ≠ 0 := by
    intro h0
    exact hP0 (hindep (by rw [h0, map_zero]))
  have hBne : algebraMap (MvPolynomial ℕ ℂ) CascadeField (B ^ k) ≠ 0 := by
    simpa using (IsFractionRing.injective (MvPolynomial ℕ ℂ) CascadeField).ne (pow_ne_zero k hB)
  have hC0 : C ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hC1
    exact (mul_ne_zero hBne haev) hC1.symm
  obtain ⟨z, hz⟩ := hind C hC0
  refine hz ?_
  rw [← hC2 z, hPz z, mul_zero]

end GaloisForLFunctions.HTGeometry
