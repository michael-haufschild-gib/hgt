/-
# The spectral action and the shell coefficients on the joint ring

On the joint variable set the spectral action of a labelling is a linear form in the spectral
variables, hence homogeneous of degree one, and the shell coefficients of the action polynomial --
now known to be homogeneous of the complementary degree -- embed as homogeneous polynomials in the
coordinate variables.  These are the graded pieces from which the criticality construction is
assembled.

Main results:
* `isHomogeneous_shellCoeff` — **the shell coefficients are homogeneous**.
* `jointAction`, `isHomogeneous_jointAction`, `eval_jointAction` — the spectral action on the joint
  ring.
* `isHomogeneous_rename_inr` — coordinate polynomials embed homogeneously.
-/
import GaloisForLFunctions.HTGeometry.JointGradingBridge
import GaloisForLFunctions.HTGeometry.HomogeneousEvalCriterion

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- **The shell coefficients of the action polynomial are homogeneous** of the complementary
degree. -/
theorem isHomogeneous_shellCoeff {P : Fin N → Matrix (Fin D) (Fin D) ℂ}
    (hP : ∀ a, (P a).IsHermitian) (k : Fin D → ℝ) (c : ℕ → MvPolynomial (Fin N) ℝ)
    (hc : ∀ (n : ℕ) (θ : Fin N → ℝ),
      MvPolynomial.eval
          (fun i => (isHermitian_spectralEnsembleMatrix hP θ).eigenvalues i)
          ((labeledActionPoly k).coeff n)
        = MvPolynomial.eval θ (c n)) (n : ℕ) :
    (c n).IsHomogeneous ((Finset.univ : Finset (Equiv.Perm (Fin D))).card - n) :=
  isHomogeneous_of_eval_smul fun t θ => eval_shellCoeff_smul hP k c hc n t θ

/-- Coordinate polynomials embed homogeneously into the joint ring. -/
theorem isHomogeneous_rename_inr {p : MvPolynomial (Fin N) ℝ} {d : ℕ} (hp : p.IsHomogeneous d) :
    ((MvPolynomial.rename (Sum.inr : Fin N → Fin D ⊕ Fin N)) p).IsHomogeneous d :=
  (MvPolynomial.IsHomogeneous.rename_isHomogeneous_iff Sum.inr_injective).mpr hp

/-- The spectral action of one labelling, as a linear form on the joint ring. -/
def jointAction (k : Fin D → ℝ) (π : Equiv.Perm (Fin D)) : MvPolynomial (Fin D ⊕ Fin N) ℝ :=
  ∑ j, MvPolynomial.C (k j) * MvPolynomial.X (Sum.inl (π j))

theorem isHomogeneous_jointAction (k : Fin D → ℝ) (π : Equiv.Perm (Fin D)) :
    (jointAction (N := N) k π).IsHomogeneous 1 := by
  rw [jointAction]
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun j _ => ?_
  simpa using (MvPolynomial.isHomogeneous_C (Fin D ⊕ Fin N) (k j)).mul
    (MvPolynomial.isHomogeneous_X ℝ (Sum.inl (π j) : Fin D ⊕ Fin N))

theorem eval_jointAction (k : Fin D → ℝ) (π : Equiv.Perm (Fin D)) (lam : Fin D → ℝ)
    (θ : Fin N → ℝ) :
    MvPolynomial.eval (Sum.elim lam θ) (jointAction (N := N) k π) = ∑ j, k j * lam (π j) := by
  rw [jointAction, map_sum]
  exact Finset.sum_congr rfl fun j _ => by simp

end

end GaloisForLFunctions.HTGeometry
