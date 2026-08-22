import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Multivariate polynomial evaluation is smooth
-/

namespace GaloisForLFunctions.HTGeometry

open Metric Set

variable {ι : Type*} [Fintype ι]

open scoped BigOperators

/-- Evaluation of a multivariate polynomial is `C^∞` in the point. -/
theorem contDiff_mvPolynomial_eval (P : MvPolynomial ι ℂ) :
    ContDiff ℂ (⊤ : ℕ∞) (fun x : ι → ℂ => MvPolynomial.eval x P) := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      have hfun : (fun x : ι → ℂ => MvPolynomial.eval x (MvPolynomial.C a : MvPolynomial ι ℂ))
          = fun _ : ι → ℂ => a := by
        funext x
        simp
      rw [hfun]
      exact contDiff_const
  | add p q hp hq =>
      have hfun : (fun x : ι → ℂ => MvPolynomial.eval x (p + q))
          = (fun x : ι → ℂ => MvPolynomial.eval x p) + fun x : ι → ℂ => MvPolynomial.eval x q := by
        funext x
        simp
      rw [hfun]
      exact ContDiff.add hp hq
  | mul_X p i hp =>
      have hproj : ContDiff ℂ (⊤ : ℕ∞) fun x : ι → ℂ => x i :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : ι => ℂ) i).contDiff
      have hfun : (fun x : ι → ℂ => MvPolynomial.eval x (p * MvPolynomial.X i))
          = (fun x : ι → ℂ => MvPolynomial.eval x p) * fun x : ι → ℂ => x i := by
        funext x
        simp
      rw [hfun]
      exact ContDiff.mul hp hproj

/-- Evaluation of a multivariate polynomial is holomorphic in the point. -/
theorem differentiable_mvPolynomial_eval (P : MvPolynomial ι ℂ) :
    Differentiable ℂ (fun x : ι → ℂ => MvPolynomial.eval x P) :=
  (contDiff_mvPolynomial_eval P).differentiable (by simp)

/-- A multivariate polynomial evaluation is bounded on every closed ball. -/
theorem exists_bound_mvPolynomial_eval (P : MvPolynomial ι ℂ) (c : ι → ℂ) (r : ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ x ∈ closedBall c r, ‖MvPolynomial.eval x P‖ ≤ M := by
  have hcont : ContinuousOn (fun x : ι → ℂ => MvPolynomial.eval x P) (closedBall c r) :=
    (differentiable_mvPolynomial_eval P).continuous.continuousOn
  obtain ⟨M, hM⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hcont
  refine ⟨max M 0, le_max_right _ _, fun x hx => ?_⟩
  exact le_trans (hM x hx) (le_max_left _ _)

/-- A multivariate polynomial evaluation is Lipschitz on every closed ball. -/
theorem exists_lipschitz_mvPolynomial_eval (P : MvPolynomial ι ℂ) (c : ι → ℂ) (r : ℝ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ x ∈ closedBall c r, ∀ y ∈ closedBall c r,
      ‖MvPolynomial.eval x P - MvPolynomial.eval y P‖ ≤ L * ‖x - y‖ := by
  have hcd : ContDiff ℂ (⊤ : ℕ∞) (fun x : ι → ℂ => MvPolynomial.eval x P) :=
    contDiff_mvPolynomial_eval P
  have hfd : Continuous fun x : ι → ℂ => fderiv ℂ (fun y : ι → ℂ => MvPolynomial.eval y P) x :=
    hcd.continuous_fderiv (by simp)
  obtain ⟨L, hL⟩ := (isCompact_closedBall c r).exists_bound_of_continuousOn hfd.continuousOn
  refine ⟨max L 0, le_max_right _ _, fun x hx y hy => ?_⟩
  exact Convex.norm_image_sub_le_of_norm_fderiv_le
    (fun z _ => (differentiable_mvPolynomial_eval P) z)
    (fun z hz => le_trans (hL z hz) (le_max_left _ _)) (convex_closedBall c r) hy hx

/-- **The chain rule for a multivariate polynomial along a holomorphic curve.** -/
theorem hasDerivAt_mvPolynomial_eval_comp [DecidableEq ι] (P : MvPolynomial ι ℂ)
    {v : ℂ → ι → ℂ} {v' : ι → ℂ} {z : ℂ} (hv : HasDerivAt v v' z) :
    HasDerivAt (fun t => MvPolynomial.eval (v t) P)
      (∑ i, MvPolynomial.eval (v z) (MvPolynomial.pderiv i P) * v' i) z := by
  induction P using MvPolynomial.induction_on with
  | C a =>
      have hfun : (fun t : ℂ => MvPolynomial.eval (v t) (MvPolynomial.C a : MvPolynomial ι ℂ))
          = fun _ : ℂ => a := by
        funext t
        simp
      have hsum : (∑ i, MvPolynomial.eval (v z)
          (MvPolynomial.pderiv i (MvPolynomial.C a : MvPolynomial ι ℂ)) * v' i) = 0 := by
        refine Finset.sum_eq_zero fun i _ => ?_
        simp
      rw [hfun, hsum]
      exact hasDerivAt_const z a
  | add p q hp hq =>
      have hfun : (fun t : ℂ => MvPolynomial.eval (v t) (p + q))
          = fun t : ℂ => MvPolynomial.eval (v t) p + MvPolynomial.eval (v t) q := by
        funext t
        simp
      have hsum : (∑ i, MvPolynomial.eval (v z) (MvPolynomial.pderiv i (p + q)) * v' i)
          = (∑ i, MvPolynomial.eval (v z) (MvPolynomial.pderiv i p) * v' i)
            + ∑ i, MvPolynomial.eval (v z) (MvPolynomial.pderiv i q) * v' i := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [map_add]
        ring
      rw [hfun, hsum]
      exact hp.add hq
  | mul_X p j hp =>
      have hproj : HasDerivAt (fun t : ℂ => v t j) (v' j) z := (hasDerivAt_pi.mp hv) j
      have hfun : (fun t : ℂ => MvPolynomial.eval (v t) (p * MvPolynomial.X j))
          = fun t : ℂ => MvPolynomial.eval (v t) p * v t j := by
        funext t
        simp
      have hsum : (∑ i, MvPolynomial.eval (v z) (MvPolynomial.pderiv i (p * MvPolynomial.X j))
            * v' i)
          = (∑ i, MvPolynomial.eval (v z) (MvPolynomial.pderiv i p) * v' i) * v z j
            + MvPolynomial.eval (v z) p * v' j := by
        have hterm : ∀ i : ι, MvPolynomial.eval (v z)
            (MvPolynomial.pderiv i (p * MvPolynomial.X j)) * v' i
            = (MvPolynomial.eval (v z) (MvPolynomial.pderiv i p) * v' i) * v z j
              + MvPolynomial.eval (v z) p * (if i = j then v' i else 0) := by
          intro i
          rw [MvPolynomial.pderiv_mul]
          by_cases hij : i = j
          · subst hij
            simp
            ring
          · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm hij)]
            simp [hij]
            ring
        rw [Finset.sum_congr rfl (fun i _ => hterm i), Finset.sum_add_distrib,
          ← Finset.sum_mul]
        congr 1
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_ite_eq' Finset.univ j (fun i => v' i)]
        simp
      rw [hfun, hsum]
      exact hp.mul hproj

end GaloisForLFunctions.HTGeometry
