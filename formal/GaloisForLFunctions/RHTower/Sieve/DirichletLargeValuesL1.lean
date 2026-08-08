import GaloisForLFunctions.RHTower.Sieve.DirichletLargeValuesCount
import Mathlib.Algebra.Order.Chebyshev

/-!
# The first-moment form of the large-value bound

The mean-value theorem controls `∑_r ‖F(λ_r)‖²` on a spaced set of points.  Cauchy–Schwarz turns
that into a bound on the first moment `∑_r ‖F(λ_r)‖`, which is the shape a coefficient extraction
consumes, and dividing by `V²` turns it into a bound on the *number* of points where `F` is large.

Both are immediate from the corpus's mean-value theorem; they are recorded because the first moment
and the large-value count, not the mean square, are what the bilinear method uses.
-/

namespace RHTower.Sieve

open Finset

/-- **First-moment form.**  On a `δ`-spaced set the first moment is at most the square root of the
point count times the mean-value bound. -/
theorem sum_norm_dirPoly_le_sqrt_of_bound (N : ℕ) (a : Fin N → ℂ) {lam : ℕ → ℝ} {B : ℝ} (R : ℕ)
    (hmv : ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ ^ 2 ≤ B) :
    ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖
      ≤ Real.sqrt (((R : ℝ) + 1) * B) := by
  classical
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range (R + 1))
    (f := fun r => ‖dirPoly N a (lam r)‖)
  have hcard : ((Finset.range (R + 1)).card : ℝ) = (R : ℝ) + 1 := by
    rw [Finset.card_range]
    push_cast
    ring
  rw [hcard] at hcs
  have hmul : ((R : ℝ) + 1) * ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ ^ 2
      ≤ ((R : ℝ) + 1) * B := by
    refine mul_le_mul_of_nonneg_left hmv ?_
    positivity
  have hsq : (∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖) ^ 2 ≤ ((R : ℝ) + 1) * B :=
    le_trans hcs hmul
  have hnn : 0 ≤ ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ :=
    Finset.sum_nonneg fun r _ => norm_nonneg _
  have hstep : Real.sqrt ((∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖) ^ 2)
      ≤ Real.sqrt (((R : ℝ) + 1) * B) := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hnn] at hstep

/-- **The first moment over a separated set.**  The instance at the mean value theorem. -/
theorem sum_norm_dirPoly_le_sqrt (N : ℕ) (hN : 2 ≤ N) (a : Fin N → ℂ) {lam : ℕ → ℝ} {δ T : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ T) :
    ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖
      ≤ Real.sqrt (((R : ℝ) + 1)
          * ((T + 4 * (N : ℝ) * (1 + Real.log N)) * (1 / δ + 2 * Real.log N)
            * ∑ m : Fin N, ‖a m‖ ^ 2)) :=
  sum_norm_dirPoly_le_sqrt_of_bound N a R (largeValues_dirPoly N hN a hδ hT hgap hlow R hhigh)

/-- **Large values are few.**  The number of spaced points where the polynomial exceeds `V` is at
most the mean-value bound divided by `V²`. -/
theorem card_largeValues_div_le (N : ℕ) (hN : 2 ≤ N) (a : Fin N → ℂ) {lam : ℕ → ℝ} {δ T V : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T) (hV : 0 < V)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ T)
    (hbig : ∀ r ∈ Finset.range (R + 1), V ≤ ‖dirPoly N a (lam r)‖) :
    (R : ℝ) + 1
      ≤ (T + 4 * (N : ℝ) * (1 + Real.log N)) * (1 / δ + 2 * Real.log N)
          * (∑ m : Fin N, ‖a m‖ ^ 2) / V ^ 2 := by
  have hcount := card_largeValues_le N hN a hδ hT hV hgap hlow R hhigh hbig
  have hV2 : (0 : ℝ) < V ^ 2 := by positivity
  rw [le_div_iff₀ hV2]
  linarith [hcount]

end RHTower.Sieve
