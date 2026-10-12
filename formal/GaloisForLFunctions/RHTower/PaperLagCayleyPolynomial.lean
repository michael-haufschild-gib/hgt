import GaloisForLFunctions.RHTower.PaperLagCayleyQuotient

/-! # Polynomial faithfulness of the literal lag-source unitary

Pointwise polynomial observations agree with operator polynomial evaluation.
Every nonzero operator polynomial survives the compact quotient and has infinite
compact-ideal cost, because the actual source retains all recurring prime phases.
-/

noncomputable section
open GaloisForLFunctions GaloisForLFunctions.HTGeometry
namespace RHTower.PaperLagCayley

theorem polynomialPhase_aeval (P : Polynomial ℂ) :
    observable (polynomialPhase P) = Polynomial.aeval sourceOperator P := by
  have hpow : ∀ k (x : Space) n, (sourceOperator ^ k) x n = (phase n : ℂ) ^ k * x n := by
    intro k
    induction k with
    | zero => intro x n; change x n = _; simp
    | succ k ih =>
      intro x n
      rw [pow_succ']
      change sourceOperator ((sourceOperator ^ k) x) n = _
      rw [sourceOperator_apply, ih, pow_succ']
      ring
  have heval : ∀ Q : Polynomial ℂ, ∀ (x : Space) n,
      (Polynomial.aeval sourceOperator Q) x n = Q.eval (phase n : ℂ) * x n := by
    intro Q
    induction Q using Polynomial.induction_on' with
    | add P Q hP hQ =>
      intro x n
      rw [Polynomial.aeval_add, Polynomial.eval_add]
      change (Polynomial.aeval sourceOperator P) x n + (Polynomial.aeval sourceOperator Q) x n = _
      rw [hP, hQ]
      ring
    | monomial k c =>
      intro x n
      rw [Polynomial.aeval_monomial, Polynomial.eval_monomial]
      change c * ((sourceOperator ^ k) x) n = _
      rw [hpow]
      ring
  ext x n
  exact (heval P x n).symm

theorem polynomial_sourceOperator_compact_iff (P : Polynomial ℂ) :
    IsCompactOperator (Polynomial.aeval sourceOperator P) ↔ P = 0 := by
  rw [← polynomialPhase_aeval, polynomial_observable_compact_iff]

theorem polynomial_sourceOperator_ideal_cost (P : Polynomial ℂ) :
    compactOperatorTraceCost Space (Polynomial.aeval sourceOperator P) =
      if P = 0 then 0 else ⊤ := by
  rw [← polynomialPhase_aeval, polynomial_observable_ideal_cost]

end RHTower.PaperLagCayley
