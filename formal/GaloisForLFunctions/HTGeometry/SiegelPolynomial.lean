import GaloisForLFunctions.HTGeometry.SiegelCountingStep
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# From a coefficient vector to a genuine polynomial relation

The counting step produces a nonzero vector of coefficients indexed by the exponent box.  This
module turns such a vector into a nonzero multivariable polynomial and identifies the associated
function with the evaluation of that polynomial at the given functions.

Distinct boxes give distinct monomials, so a nonzero coefficient vector gives a nonzero polynomial:
that is what makes the relation produced by the count nontrivial, and hence what makes it witness
algebraic — and, through `differentialAlgebraicOver_of_aeval_eq_zero`, differential-algebraic —
dependence.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

variable {n m : ℕ}

/-- The exponent multi-index attached to a point of the box. -/
noncomputable def siegelExp (β : Fin (n + 1) → Fin (m + 1)) : (Fin (n + 1)) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun k => (β k : ℕ))

@[simp]
theorem siegelExp_apply (β : Fin (n + 1) → Fin (m + 1)) (k : Fin (n + 1)) :
    siegelExp β k = (β k : ℕ) := rfl

theorem siegelExp_injective : Function.Injective (siegelExp (n := n) (m := m)) := by
  intro β γ h
  funext k
  have := congrArg (fun s : (Fin (n + 1)) →₀ ℕ => s k) h
  simp only [siegelExp_apply] at this
  exact Fin.val_injective this

/-- The polynomial attached to a coefficient vector on the exponent box. -/
noncomputable def siegelPoly (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) :
    MvPolynomial (Fin (n + 1)) ℂ :=
  ∑ β : Fin (n + 1) → Fin (m + 1), MvPolynomial.monomial (siegelExp β) (a β)

theorem coeff_siegelPoly (a : (Fin (n + 1) → Fin (m + 1)) → ℂ)
    (β₀ : Fin (n + 1) → Fin (m + 1)) :
    MvPolynomial.coeff (siegelExp β₀) (siegelPoly a) = a β₀ := by
  classical
  rw [siegelPoly, MvPolynomial.coeff_sum, Finset.sum_eq_single β₀]
  · rw [MvPolynomial.coeff_monomial, if_pos rfl]
  · intro β _ hne
    rw [MvPolynomial.coeff_monomial, if_neg]
    intro hc
    exact hne (siegelExp_injective hc)
  · intro hmem
    exact absurd (Finset.mem_univ β₀) hmem

/-- **A nonzero coefficient vector gives a nonzero polynomial.** -/
theorem siegelPoly_ne_zero {a : (Fin (n + 1) → Fin (m + 1)) → ℂ} (ha : a ≠ 0) :
    siegelPoly a ≠ 0 := by
  intro h
  refine ha ?_
  funext β
  have := coeff_siegelPoly a β
  rw [h, MvPolynomial.coeff_zero] at this
  exact this.symm

/-- **Evaluating the polynomial is the coefficient combination.** -/
theorem eval_siegelPoly (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) (x : Fin (n + 1) → ℂ) :
    MvPolynomial.eval x (siegelPoly a)
      = ∑ β : Fin (n + 1) → Fin (m + 1), a β * ∏ k, (x k) ^ (β k : ℕ) := by
  classical
  rw [siegelPoly, map_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [MvPolynomial.eval_monomial]
  congr 1
  refine Finsupp.prod_fintype _ _ ?_
  intro k
  rw [pow_zero]

/-- The function attached to a coefficient vector and a family of functions. -/
noncomputable def siegelCombination {E : Type*} (f : Fin (n + 1) → E → ℂ)
    (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) : E → ℂ :=
  fun w => ∑ β : Fin (n + 1) → Fin (m + 1), a β * ∏ k, (f k w) ^ (β k : ℕ)

theorem eval_siegelPoly_eq_siegelCombination {E : Type*} (f : Fin (n + 1) → E → ℂ)
    (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) (w : E) :
    MvPolynomial.eval (fun k => f k w) (siegelPoly a) = siegelCombination f a w :=
  eval_siegelPoly a _

theorem siegelCombination_add {E : Type*} (f : Fin (n + 1) → E → ℂ)
    (a b : (Fin (n + 1) → Fin (m + 1)) → ℂ) :
    siegelCombination f (a + b) = siegelCombination f a + siegelCombination f b := by
  funext w
  simp only [siegelCombination, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

theorem siegelCombination_smul {E : Type*} (f : Fin (n + 1) → E → ℂ) (c : ℂ)
    (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) :
    siegelCombination f (c • a) = c • siegelCombination f a := by
  funext w
  simp only [siegelCombination, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

theorem continuous_siegelCombination {E : Type*} [TopologicalSpace E]
    {f : Fin (n + 1) → E → ℂ} (hf : ∀ k, Continuous (f k))
    (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) : Continuous (siegelCombination f a) := by
  refine continuous_finsetSum _ fun β _ => ?_
  refine continuous_const.mul ?_
  exact continuous_finsetProd _ fun k _ => (hf k).pow _

theorem contDiff_siegelCombination {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : Fin (n + 1) → E → ℂ} (hf : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (f k))
    (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) : ContDiff ℂ (⊤ : ℕ∞) (siegelCombination f a) := by
  refine ContDiff.sum fun β _ => ?_
  refine contDiff_const.mul ?_
  exact contDiff_prod fun k _ => (hf k).pow _

theorem differentiable_siegelCombination {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : Fin (n + 1) → E → ℂ} (hf : ∀ k, ContDiff ℂ (⊤ : ℕ∞) (f k))
    (a : (Fin (n + 1) → Fin (m + 1)) → ℂ) : Differentiable ℂ (siegelCombination f a) :=
  (contDiff_siegelCombination hf a).differentiable (by simp)

end GaloisForLFunctions.HTGeometry
