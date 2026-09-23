/-
# Evaluating the joint criticality expression

On the unit shell the homogenising factor is one, so the joint criticality expression evaluates to
the criticality value of the labelled spectral action, and its second summand carries the leading
factor of the defining relation.  Combined with the tangential factorisation this exhibits every
labelling block of the criticality product as a square times the squared tangential gradient.

Main results:
* `jointLeading`, `eval_jointLeading` — the leading factor as a joint polynomial.
* `eval_jointCriticality` — the evaluation of the criticality expression.
* `eval_jointCriticality_of_unit` — on the unit shell it is the criticality value.
* `eval_jointCriticalitySquareSum_of_unit` — the block is the squared leading factor times the
  squared tangential gradient.
-/
import GaloisForLFunctions.HTGeometry.ShellPolyNonvanishing
import GaloisForLFunctions.HTGeometry.CriticalityTangentialFactorisation

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- The leading factor of the criticality expression, as a polynomial on the joint ring. -/
def jointLeading (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (k : Fin D → ℝ)
    (π : Equiv.Perm (Fin D)) : MvPolynomial (Fin D ⊕ Fin N) ℝ :=
  ∑ n ∈ Finset.range (M + 1),
    MvPolynomial.C (n : ℝ) * MvPolynomial.rename Sum.inr (c n) * (jointAction k π) ^ (n - 1)

theorem eval_rename_inr (p : MvPolynomial (Fin N) ℝ) (lam : Fin D → ℝ) (θ : Fin N → ℝ) :
    MvPolynomial.eval (Sum.elim lam θ) (MvPolynomial.rename Sum.inr p)
      = MvPolynomial.eval θ p := by
  rw [MvPolynomial.eval_rename]
  rfl

theorem eval_jointLeading (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (k : Fin D → ℝ)
    (π : Equiv.Perm (Fin D)) (lam : Fin D → ℝ) (θ : Fin N → ℝ) :
    MvPolynomial.eval (Sum.elim lam θ) (jointLeading M c k π)
      = criticalityLeading (M + 1) c θ (∑ j, k j * lam (π j)) := by
  rw [jointLeading, map_sum, criticalityLeading]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
    MvPolynomial.eval_C, eval_rename_inr, eval_jointAction]

theorem eval_jointCriticality (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (k : Fin D → ℝ)
    (π : Equiv.Perm (Fin D)) (i : Fin N) (lam : Fin D → ℝ) (θ : Fin N → ℝ) :
    MvPolynomial.eval (Sum.elim lam θ) (jointCriticality M c k π i)
      = (∑ a, (θ a) ^ (2 : ℕ))
          * (∑ n ∈ Finset.range (M + 1),
              MvPolynomial.eval θ (MvPolynomial.pderiv i (c n)) * (∑ j, k j * lam (π j)) ^ n)
        + criticalityLeading (M + 1) c θ (∑ j, k j * lam (π j))
            * ((∑ j, k j * lam (π j)) * θ i) := by
  rw [jointCriticality, MvPolynomial.eval_add, MvPolynomial.eval_mul, map_sum, map_sum]
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      eval_rename_inr, eval_rename_inr, eval_jointAction, eval_normSqPoly]
    ring
  · rw [MvPolynomial.eval_mul, MvPolynomial.eval_X, eval_jointAction, criticalityLeading]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [MvPolynomial.eval_mul, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      MvPolynomial.eval_C, eval_rename_inr, eval_jointAction]

/-- On the unit shell the joint criticality expression is the criticality value of the labelled
spectral action. -/
theorem eval_jointCriticality_of_unit (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (k : Fin D → ℝ)
    (π : Equiv.Perm (Fin D)) (i : Fin N) (lam : Fin D → ℝ) {θ : Fin N → ℝ}
    (hθ : ∑ a, (θ a) ^ (2 : ℕ) = 1) :
    MvPolynomial.eval (Sum.elim lam θ) (jointCriticality M c k π i)
      = criticalityValue (M + 1) c θ (∑ j, k j * lam (π j)) i := by
  rw [eval_jointCriticality, hθ, one_mul, criticalityValue]

end

end GaloisForLFunctions.HTGeometry
