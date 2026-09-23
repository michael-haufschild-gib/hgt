/-
# The symmetrised criticality product on the joint ring

Squaring the criticality expression, summing over the coordinate directions and multiplying over
all labellings of the spectrum gives a single homogeneous polynomial on the joint variable set.
Its evaluation therefore scales by a fixed power under simultaneous scaling of the coordinates and
of the spectrum -- which is the scaling hypothesis of the shell sublevel bound.

Main results:
* `jointCriticalitySquareSum`, `jointCriticalProduct` — the symmetrised construction.
* `isHomogeneous_jointCriticalProduct` — **it is homogeneous**.
* `eval_jointCriticalProduct_smul` — **its evaluation scales by a fixed power**.
-/
import GaloisForLFunctions.HTGeometry.JointCriticalityHomogeneous

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- The sum over the coordinate directions of the squared criticality expressions, on the joint
ring. -/
def jointCriticalitySquareSum (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (k : Fin D → ℝ)
    (π : Equiv.Perm (Fin D)) : MvPolynomial (Fin D ⊕ Fin N) ℝ :=
  ∑ i : Fin N, (jointCriticality M c k π i) ^ (2 : ℕ)

theorem isHomogeneous_jointCriticalitySquareSum (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ)
    (hc : ∀ n, (c n).IsHomogeneous (M - n)) (k : Fin D → ℝ) (π : Equiv.Perm (Fin D)) :
    (jointCriticalitySquareSum M c k π).IsHomogeneous ((M + 1) * 2) := by
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
  exact (isHomogeneous_jointCriticality M c hc k π i).pow 2

/-- The product over all labellings of the spectrum, on the joint ring. -/
def jointCriticalProduct (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (k : Fin D → ℝ) :
    MvPolynomial (Fin D ⊕ Fin N) ℝ :=
  ∏ π : Equiv.Perm (Fin D), jointCriticalitySquareSum M c k π

/-- **The symmetrised criticality product is homogeneous.** -/
theorem isHomogeneous_jointCriticalProduct (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ)
    (hc : ∀ n, (c n).IsHomogeneous (M - n)) (k : Fin D → ℝ) :
    (jointCriticalProduct M c k).IsHomogeneous
      ((Finset.univ : Finset (Equiv.Perm (Fin D))).card * ((M + 1) * 2)) := by
  classical
  have hprod := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Equiv.Perm (Fin D)))
    (fun π => jointCriticalitySquareSum M c k π) (fun _ => (M + 1) * 2)
    (fun π _ => isHomogeneous_jointCriticalitySquareSum M c hc k π)
  have hsum : (∑ _π ∈ (Finset.univ : Finset (Equiv.Perm (Fin D))), (M + 1) * 2)
      = (Finset.univ : Finset (Equiv.Perm (Fin D))).card * ((M + 1) * 2) := by
    rw [Finset.sum_const, smul_eq_mul]
  rw [hsum] at hprod
  exact hprod

/-- **The evaluation of the symmetrised criticality product scales by a fixed power.** -/
theorem eval_jointCriticalProduct_smul (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ)
    (hc : ∀ n, (c n).IsHomogeneous (M - n)) (k : Fin D → ℝ)
    (θ : Fin N → ℝ) (lam : Fin D → ℝ) (t : ℝ) :
    MvPolynomial.eval (Sum.elim (fun i => t * lam i) (fun a => t * θ a))
        (jointCriticalProduct M c k)
      = t ^ ((Finset.univ : Finset (Equiv.Perm (Fin D))).card * ((M + 1) * 2))
        * MvPolynomial.eval (Sum.elim lam θ) (jointCriticalProduct M c k) := by
  have hfun : Sum.elim (fun i => t * lam i) (fun a => t * θ a)
      = fun x => t * Sum.elim lam θ x := by
    funext x
    rcases x with i | a <;> rfl
  rw [hfun]
  exact eval_smul_of_isHomogeneous_general (isHomogeneous_jointCriticalProduct M c hc k) t _

end

end GaloisForLFunctions.HTGeometry
