import GaloisForLFunctions.RHTower.Sieve.DirichletCubeCoefficients
import GaloisForLFunctions.RHTower.Sieve.DirichletLargeValuesCount

/-!
# The sixth moment of a Dirichlet polynomial at separated frequencies

Applying the mean-value theorem to the cube of `F` replaces the square by the sixth power:

    ∑_r |F(λ_r)|⁶ ≤ (T + 4N³(1 + log N³))(δ^{-1} + 2 log N³) · D · (∑_n |a_n|²)³ ,

where `D` bounds the number of triples `(n,m,k) ∈ [1,N]³` with a given product.  Dividing by `V⁶`
caps the number of frequencies at which `F` exceeds `V`.

The gain over the second-moment bound is the exponent: the spread `T` is now divided by `V⁶` rather
than `V²`, which is what makes the estimate useful when `V` is close to the trivial size.
-/

namespace RHTower.Sieve

open Finset

/-- **The sixth moment at separated frequencies.** -/
theorem sixthMoment_dirPoly (N : ℕ) (hN : 2 ≤ N) (a : Fin N → ℂ) {lam : ℕ → ℝ} {δ T D : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ T)
    (hD : ∀ j : Fin (N ^ (3 : ℕ)), ((cubeFibre N j).card : ℝ) ≤ D) :
    ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ ^ (6 : ℕ)
      ≤ (T + 4 * ((N ^ (3 : ℕ) : ℕ) : ℝ) * (1 + Real.log ((N ^ (3 : ℕ) : ℕ) : ℝ)))
          * (1 / δ + 2 * Real.log ((N ^ (3 : ℕ) : ℕ) : ℝ))
          * (D * (∑ n : Fin N, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
  classical
  have hN3 : 2 ≤ N ^ (3 : ℕ) := le_trans hN (Nat.le_self_pow (by norm_num) N)
  have hmv := largeValues_dirPoly (N ^ (3 : ℕ)) hN3 (convCube N a) hδ hT hgap hlow R hhigh
  have hrewrite : ∀ r : ℕ,
      ‖dirPoly (N ^ (3 : ℕ)) (convCube N a) (lam r)‖ ^ (2 : ℕ) = ‖dirPoly N a (lam r)‖ ^ (6 : ℕ) := by
    intro r
    rw [dirPoly_convCube, norm_pow, ← pow_mul]
  simp only [hrewrite] at hmv
  refine le_trans hmv ?_
  have hlogN3 : (0 : ℝ) ≤ Real.log ((N ^ (3 : ℕ) : ℕ) : ℝ) := by
    refine Real.log_nonneg ?_
    have : (1 : ℕ) ≤ N ^ (3 : ℕ) := by omega
    exact_mod_cast this
  have hfactor : (0 : ℝ)
      ≤ (T + 4 * ((N ^ (3 : ℕ) : ℕ) : ℝ) * (1 + Real.log ((N ^ (3 : ℕ) : ℕ) : ℝ)))
          * (1 / δ + 2 * Real.log ((N ^ (3 : ℕ) : ℕ) : ℝ)) := by
    have hcast : (0 : ℝ) ≤ ((N ^ (3 : ℕ) : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ T + 4 * ((N ^ (3 : ℕ) : ℕ) : ℝ) * (1 + Real.log ((N ^ (3 : ℕ) : ℕ) : ℝ)) := by
      nlinarith
    have h2 : (0 : ℝ) ≤ 1 / δ + 2 * Real.log ((N ^ (3 : ℕ) : ℕ) : ℝ) := by
      have : (0 : ℝ) < 1 / δ := by positivity
      linarith
    exact mul_nonneg h1 h2
  exact mul_le_mul_of_nonneg_left (sum_normSq_convCube_le N a hD) hfactor

/-- **A cap on the number of large values, sixth-power form.** -/
theorem card_largeValues_sixth_le (N : ℕ) (hN : 2 ≤ N) (a : Fin N → ℂ) {lam : ℕ → ℝ}
    {δ T V D : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hV : 0 < V)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ T)
    (hD : ∀ j : Fin (N ^ (3 : ℕ)), ((cubeFibre N j).card : ℝ) ≤ D)
    (hbig : ∀ r ∈ Finset.range (R + 1), V ≤ ‖dirPoly N a (lam r)‖) :
    ((R : ℝ) + 1) * V ^ (6 : ℕ)
      ≤ (T + 4 * ((N ^ (3 : ℕ) : ℕ) : ℝ) * (1 + Real.log ((N ^ (3 : ℕ) : ℕ) : ℝ)))
          * (1 / δ + 2 * Real.log ((N ^ (3 : ℕ) : ℕ) : ℝ))
          * (D * (∑ n : Fin N, ‖a n‖ ^ (2 : ℕ)) ^ (3 : ℕ)) := by
  have hterm : ∀ r ∈ Finset.range (R + 1), V ^ (6 : ℕ) ≤ ‖dirPoly N a (lam r)‖ ^ (6 : ℕ) := by
    intro r hr
    exact pow_le_pow_left₀ hV.le (hbig r hr) 6
  have hcount : ((R : ℝ) + 1) * V ^ (6 : ℕ)
      ≤ ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ ^ (6 : ℕ) := by
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hterm)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    push_cast
    ring
  exact le_trans hcount (sixthMoment_dirPoly N hN a hδ hT hgap hlow R hhigh hD)

end RHTower.Sieve
