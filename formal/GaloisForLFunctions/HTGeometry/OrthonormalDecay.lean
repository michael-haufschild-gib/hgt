import GaloisForLFunctions.HTGeometry.ChristoffelLimitFormula
import GaloisForLFunctions.HTGeometry.OrthonormalMomentPolynomials

/-!
# Decay of the orthonormal polynomials

The kernel series is `∑ₖ pₖ(x)²` in the orthonormal normalisation, since `pₖ = Qₖ / √hₖ`.  So
positivity of the limit Christoffel function says exactly that this series converges, and its terms
must then tend to zero: the orthonormal polynomials decay at every point where `λ` is positive.

This restates the condition in the classical language and replaces the moment-theoretic
quantities by
a statement purely about the sequence `k ↦ pₖ(x)`.
-/

open scoped BigOperators
open Polynomial Filter

namespace HTGeometry

variable {s : ℕ → ℝ}

/-- The kernel series terms are the squared orthonormal polynomials. -/
theorem orthonormalPoly_eval_sq (h : PositiveMomentForm s) (k : ℕ) (x : ℝ) :
    ((orthonormalPoly s k).eval x) ^ 2
      = ((monicOrtho s k).eval x) ^ 2 / momentInner s (monicOrtho s k) (monicOrtho s k) := by
  rw [orthonormalPoly, Polynomial.eval_smul, smul_eq_mul, mul_pow, ← monicOrthoNorm_sq h k,
    inv_pow, div_eq_inv_mul]

/-- **Positivity of the Christoffel limit is summability of the squared orthonormal
polynomials.** -/
theorem summable_orthonormalPoly_sq_of_christoffelLimit_pos (h : PositiveMomentForm s) (x : ℝ)
    (hsum : Summable fun k => ((monicOrtho s k).eval x) ^ 2 /
      momentInner s (monicOrtho s k) (monicOrtho s k)) :
    Summable fun k => ((orthonormalPoly s k).eval x) ^ 2 := by
  refine hsum.congr fun k => ?_
  rw [orthonormalPoly_eval_sq h k x]

/-- **The orthonormal polynomials decay** wherever the kernel series converges. -/
theorem tendsto_orthonormalPoly_eval_zero (h : PositiveMomentForm s) (x : ℝ)
    (hsum : Summable fun k => ((monicOrtho s k).eval x) ^ 2 /
      momentInner s (monicOrtho s k) (monicOrtho s k)) :
    Tendsto (fun k => (orthonormalPoly s k).eval x) atTop (nhds 0) := by
  have hsq : Tendsto (fun k => ((orthonormalPoly s k).eval x) ^ 2) atTop (nhds 0) :=
    (summable_orthonormalPoly_sq_of_christoffelLimit_pos h x hsum).tendsto_atTop_zero
  have hroot := (Real.continuous_sqrt.tendsto 0).comp hsq
  rw [Real.sqrt_zero] at hroot
  refine tendsto_zero_iff_norm_tendsto_zero.mpr ?_
  refine hroot.congr fun k => ?_
  rw [Function.comp_apply, Real.sqrt_sq_eq_abs, Real.norm_eq_abs]

end HTGeometry
