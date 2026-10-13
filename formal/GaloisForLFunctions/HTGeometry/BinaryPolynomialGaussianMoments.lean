import GaloisForLFunctions.HTGeometry.QuadraticExponentialMoments
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Algebra.BigOperators.Fin

/-! Every bivariate polynomial restricted to the diagonal lies in Gaussian L2. -/

open MeasureTheory ProbabilityTheory

namespace GaloisForLFunctions.HTGeometry

theorem binaryPolynomial_eval_monomial (e : Fin 2 →₀ ℕ) (c : ℝ) (z : Fin 2 → ℝ) :
    MvPolynomial.eval z (MvPolynomial.monomial e c) =
      c * (z 0 ^ e 0 * z 1 ^ e 1) := by
  rw [MvPolynomial.eval_monomial,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fin.prod_univ_two]

theorem gaussianZero_integrable_binaryPolynomial_diagonal
    (v : NNReal) (p : MvPolynomial (Fin 2) ℝ) :
    Integrable (fun x : ℝ => MvPolynomial.eval (fun _ => x) p) (gaussianReal 0 v) := by
  induction p using MvPolynomial.induction_on' with
  | monomial e c =>
      simpa only [binaryPolynomial_eval_monomial, ← pow_add] using
        (gaussianZero_integrable_nat_pow v (e 0 + e 1)).const_mul c
  | add p q hp hq =>
      simp only [MvPolynomial.eval_add]
      exact hp.add hq

theorem gaussianZero_memLp_two_binaryPolynomial_diagonal
    (v : NNReal) (p : MvPolynomial (Fin 2) ℝ) :
    MemLp (fun x : ℝ => MvPolynomial.eval (fun _ => x) p) 2 (gaussianReal 0 v) := by
  apply (memLp_two_iff_integrable_sq
    (gaussianZero_integrable_binaryPolynomial_diagonal v p).aestronglyMeasurable).mpr
  have hpow : (fun x : ℝ => MvPolynomial.eval (fun _ => x) (p ^ 2)) =
      (fun x : ℝ => MvPolynomial.eval (fun _ => x) p ^ 2) := by
    funext x
    exact MvPolynomial.eval_pow 2
  rw [← hpow]
  exact gaussianZero_integrable_binaryPolynomial_diagonal v (p ^ 2)

end GaloisForLFunctions.HTGeometry
