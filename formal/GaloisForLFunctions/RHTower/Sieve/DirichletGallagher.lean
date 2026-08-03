import GaloisForLFunctions.RHTower.Sieve.DirichletPoly

/-!
# Gallagher's reduction for Dirichlet polynomials

The Sobolev bound of `GallagherSobolev.lean` applies to `|F|²` for a Dirichlet polynomial exactly as
it did in the trigonometric case, and the windows around `δ`-separated points are disjoint, so

`∑_{r ≤ R} |F(t_r)|² ≤ δ^{-1} ∫_A^{t_R + δ/2} |F|² + ∫_A^{t_R + δ/2} 2|F||F'|`.

The right-hand side depends on the points only through the enclosing interval.  This is the standard
first step of a large-values argument: it trades a discrete sum for a continuous mean.

What it does *not* do is evaluate the two integrals.  For trigonometric polynomials Parseval does
that exactly; for Dirichlet polynomials no such identity holds on a finite interval, and supplying
one is the separate — and open — Montgomery–Vaughan obligation.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- **Gallagher's bound at a point, for a Dirichlet polynomial.** -/
theorem gallagher_dirPoly_at_point (N : ℕ) (a : Fin N → ℂ) (x : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ‖dirPoly N a x‖ ^ 2
      ≤ (1 / δ) * (∫ t in (x - δ / 2)..(x + δ / 2), ‖dirPoly N a t‖ ^ 2)
        + (∫ t in (x - δ / 2)..(x + δ / 2),
            2 * ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖) := by
  have hh : (0 : ℝ) < δ / 2 := by linarith
  have hab : x - δ / 2 ≤ x + δ / 2 := by linarith
  have hcontg : Continuous (fun s : ℝ =>
      (inner ℝ (dirPoly N a s) (dirPoly N (dirDerivCoeff N a) s) : ℝ)
        + (inner ℝ (dirPoly N (dirDerivCoeff N a) s) (dirPoly N a s) : ℝ)) :=
    (Continuous.inner (𝕜 := ℝ) (continuous_dirPoly N a)
        (continuous_dirPoly N (dirDerivCoeff N a))).add
      (Continuous.inner (𝕜 := ℝ) (continuous_dirPoly N (dirDerivCoeff N a))
        (continuous_dirPoly N a))
  have hbase := gallagher_sobolev (f := fun s => ‖dirPoly N a s‖ ^ 2)
    (f' := fun s => (inner ℝ (dirPoly N a s) (dirPoly N (dirDerivCoeff N a) s) : ℝ)
      + (inner ℝ (dirPoly N (dirDerivCoeff N a) s) (dirPoly N a s) : ℝ))
    (a := x) (h := δ / 2) hh (fun y _ => hasDerivAt_normSq_dirPoly N a y) hcontg.continuousOn
  have habs1 : (∫ t in (x - δ / 2)..(x + δ / 2), |‖dirPoly N a t‖ ^ 2|)
      = ∫ t in (x - δ / 2)..(x + δ / 2), ‖dirPoly N a t‖ ^ 2 :=
    intervalIntegral.integral_congr (fun t _ => abs_of_nonneg (sq_nonneg _))
  have habs0 : |‖dirPoly N a x‖ ^ 2| = ‖dirPoly N a x‖ ^ 2 := abs_of_nonneg (sq_nonneg _)
  have hderivbound : (∫ t in (x - δ / 2)..(x + δ / 2),
        |(inner ℝ (dirPoly N a t) (dirPoly N (dirDerivCoeff N a) t) : ℝ)
          + (inner ℝ (dirPoly N (dirDerivCoeff N a) t) (dirPoly N a t) : ℝ)|)
      ≤ ∫ t in (x - δ / 2)..(x + δ / 2),
          2 * ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖ := by
    refine intervalIntegral.integral_mono_on hab
      (hcontg.abs.intervalIntegrable _ _) ?_ (fun t _ => abs_deriv_normSq_dirPoly_le N a t)
    exact (((continuous_const.mul (continuous_dirPoly N a).norm).mul
      (continuous_dirPoly N (dirDerivCoeff N a)).norm)).intervalIntegrable _ _
  have hlen : (1 : ℝ) / (2 * (δ / 2)) = 1 / δ := by
    congr 1
    ring
  rw [habs0, habs1, hlen] at hbase
  linarith

/-- **Gallagher's bound over a separated family, for a Dirichlet polynomial.** -/
theorem gallagher_dirPoly_sum (N : ℕ) (a : Fin N → ℂ) {lam : ℕ → ℝ} {δ A : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hA : A ≤ lam 0 - δ / 2) (R : ℕ) :
    ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ ^ 2
      ≤ (1 / δ) * (∫ t in A..(lam R + δ / 2), ‖dirPoly N a t‖ ^ 2)
        + (∫ t in A..(lam R + δ / 2),
            2 * ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖) := by
  have hcont1 : Continuous (fun t : ℝ => ‖dirPoly N a t‖ ^ 2) :=
    ((continuous_dirPoly N a).norm).pow 2
  have hcont2 : Continuous (fun t : ℝ =>
      2 * ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖) :=
    (continuous_const.mul (continuous_dirPoly N a).norm).mul
      (continuous_dirPoly N (dirDerivCoeff N a)).norm
  have hnn1 : ∀ t : ℝ, (0 : ℝ) ≤ ‖dirPoly N a t‖ ^ 2 := fun t => sq_nonneg _
  have hnn2 : ∀ t : ℝ,
      (0 : ℝ) ≤ 2 * ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖ := by
    intro t
    positivity
  have hterm : ∀ r ∈ Finset.range (R + 1),
      ‖dirPoly N a (lam r)‖ ^ 2
        ≤ (1 / δ) * (∫ t in (lam r - δ / 2)..(lam r + δ / 2), ‖dirPoly N a t‖ ^ 2)
          + (∫ t in (lam r - δ / 2)..(lam r + δ / 2),
              2 * ‖dirPoly N a t‖ * ‖dirPoly N (dirDerivCoeff N a) t‖) :=
    fun r _ => gallagher_dirPoly_at_point N a (lam r) hδ
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  have h1 := sum_window_le hcont1 hnn1 hδ hgap hA R
  have h2 := sum_window_le hcont2 hnn2 hδ hgap hA R
  have hδinv : (0 : ℝ) ≤ 1 / δ := by positivity
  have h1' := mul_le_mul_of_nonneg_left h1 hδinv
  linarith

end RHTower.Sieve
