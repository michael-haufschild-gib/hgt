/-
# The joint grading of the spectral construction

Polynomials in the spectral variables with coordinate-ring coefficients are polynomials in the
disjoint union of the two variable sets, and the total grading of the former is ordinary
homogeneity of the latter.  Working on the joint ring makes every closure property -- sums,
products, constants, variables -- immediate from mathlib's `IsHomogeneous` API, and the
simultaneous scaling law is a single application of the homogeneous scaling identity.

Main results:
* `eval_smul_of_isHomogeneous_general` — the scaling identity over an arbitrary variable set.
* `eval_sumAlgEquiv_jointGradingBridge` — **the iterated evaluation is the joint evaluation**.
* `eval₂_smul_of_joint_isHomogeneous` — **a jointly homogeneous object scales by its degree**.
-/
import GaloisForLFunctions.HTGeometry.Bihomogeneous
import Mathlib.Algebra.MvPolynomial.Equiv

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

/-- The homogeneous scaling identity over an arbitrary variable set. -/
theorem eval_smul_of_isHomogeneous_general {σ : Type*} {P : MvPolynomial σ ℝ} {d : ℕ}
    (hP : P.IsHomogeneous d) (r : ℝ) (x : σ → ℝ) :
    MvPolynomial.eval (fun i => r * x i) P = r ^ d * MvPolynomial.eval x P := by
  classical
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t ht => ?_
  have hw := hP (MvPolynomial.mem_support_iff.mp ht)
  have hdeg : ∑ i ∈ t.support, t i = d := by
    rw [← hw, Finsupp.weight_apply]
    simp [Finsupp.sum]
  have hprod : (∏ i ∈ t.support, (r * x i) ^ t i)
      = r ^ d * ∏ i ∈ t.support, (x i) ^ t i := by
    rw [← hdeg, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => mul_pow r (x i) (t i)
  rw [hprod]
  ring

/-- **The iterated evaluation is the joint evaluation.** -/
theorem eval_sumAlgEquiv_jointGradingBridge (θ : Fin N → ℝ) (lam : Fin D → ℝ)
    (B : MvPolynomial (Fin D ⊕ Fin N) ℝ) :
    MvPolynomial.eval₂ (MvPolynomial.eval θ) lam
        ((MvPolynomial.sumAlgEquiv ℝ (Fin D) (Fin N)) B)
      = MvPolynomial.eval (Sum.elim lam θ) B := by
  induction B using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p x hp =>
      rcases x with i | a
      · simp [hp]
      · simp [hp]

/-- **A jointly homogeneous object scales by its degree** under simultaneous scaling of the
coordinates and of the spectrum. -/
theorem eval₂_smul_of_joint_isHomogeneous {d : ℕ} {B : MvPolynomial (Fin D ⊕ Fin N) ℝ}
    (hB : B.IsHomogeneous d) (θ : Fin N → ℝ) (lam : Fin D → ℝ) (t : ℝ) :
    MvPolynomial.eval₂ (MvPolynomial.eval (fun a => t * θ a)) (fun i => t * lam i)
        ((MvPolynomial.sumAlgEquiv ℝ (Fin D) (Fin N)) B)
      = t ^ d * MvPolynomial.eval₂ (MvPolynomial.eval θ) lam
          ((MvPolynomial.sumAlgEquiv ℝ (Fin D) (Fin N)) B) := by
  rw [eval_sumAlgEquiv_jointGradingBridge, eval_sumAlgEquiv_jointGradingBridge]
  have hfun : Sum.elim (fun i => t * lam i) (fun a => t * θ a)
      = fun x => t * Sum.elim lam θ x := by
    funext x
    rcases x with i | a <;> rfl
  rw [hfun]
  exact eval_smul_of_isHomogeneous_general hB t _

end

end GaloisForLFunctions.HTGeometry
