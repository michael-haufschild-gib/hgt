import GaloisForLFunctions.RHTower.Sieve.DirichletFirstMomentShift
import GaloisForLFunctions.RHTower.Sieve.LorentzianLSeriesLine
import GaloisForLFunctions.RHTower.Sieve.LogPolyDirPoly
/-!
# The first moment of a finitely supported Dirichlet series, by large values

A finitely supported series is a Dirichlet polynomial in the Gallagher variable, and the substitution is a
reflection which a symmetric interval absorbs.  So the large-values first moment applies to it directly:

`∫_{|y| ≤ nΔ} ‖L(a, σ+iy)‖ dy ≤ 2Δ·√(n·((2n+1)Δ + 4M(1+log M))(1/Δ + 2 log M)·∑_i ‖a_{i+1}(i+1)^{−σ}‖²)`,

the `ℓ²` mass being that of the damped coefficients.  This is the estimate the Perron passage needs on its
truncated range, and it contains no window, no measure and no trivial size multiplying a length.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Finset

/-- **The first moment of a finitely supported Dirichlet series on a vertical segment, by large values.**  The
series is a Dirichlet polynomial in the Gallagher variable, so the large-values first moment applies to it; the
`ℓ²` mass on the right is that of the damped coefficients. -/
theorem integral_norm_LSeries_le_largeValues {a : ℕ → ℂ} {M : ℕ} (hM : 2 ≤ M)
    (hsupp : ∀ k : ℕ, a k ≠ 0 → k ∈ Finset.Icc 1 M) (σ : ℝ) {Δ : ℝ} (hΔ : 0 < Δ) (n : ℕ)
    (hn : 1 ≤ n) :
    (∫ y in (-(((2 * n : ℕ) : ℝ) * Δ / 2))..(((2 * n : ℕ) : ℝ) * Δ / 2),
        ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖)
      ≤ 2 * Δ * Real.sqrt ((n : ℝ)
          * ((((2 * n + 1 : ℕ) : ℝ) * Δ + 4 * (M : ℝ) * (1 + Real.log M))
              * (1 / Δ + 2 * Real.log M)
              * ∑ i : Fin M, ‖a ((i : ℕ) + 1) * (((((i : ℕ) + 1 : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2)) := by
  classical
  have hs0 : (0 : ℕ) ∉ Finset.Icc 1 M := by simp
  set c : ℕ → ℂ := fun k => a k * ((((k : ℝ) ^ (-σ) : ℝ)) : ℂ) with hc
  set c' : Fin M → ℂ := fun i => c ((i : ℕ) + 1) with hc'
  -- the series is the polynomial in the Gallagher variable, reflected
  have hpt : ∀ y : ℝ, ‖LSeries a ((σ : ℂ) + (y : ℝ) * I)‖ = ‖dirPoly M c' (-y)‖ := by
    intro y
    rw [LSeries_eq_logPoly_of_support hs0 hsupp σ y, ← hc,
      logPoly_eq_dirPoly c M (-y / (2 * Real.pi)), ← hc']
    congr 1
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
  rw [intervalIntegral.integral_congr (g := fun y => ‖dirPoly M c' (-y)‖) (fun y _ => hpt y)]
  -- undo the reflection on the symmetric interval
  have hrefl : (∫ y in (-(((2 * n : ℕ) : ℝ) * Δ / 2))..(((2 * n : ℕ) : ℝ) * Δ / 2),
        ‖dirPoly M c' (-y)‖)
      = ∫ t in (-(((2 * n : ℕ) : ℝ) * Δ / 2))..(((2 * n : ℕ) : ℝ) * Δ / 2),
          ‖dirPoly M c' t‖ := by
    have h := intervalIntegral.integral_comp_neg
      (a := -(((2 * n : ℕ) : ℝ) * Δ / 2)) (b := ((2 * n : ℕ) : ℝ) * Δ / 2)
      (fun t => ‖dirPoly M c' t‖)
    rw [h]
    congr 1
    ring
  rw [hrefl]
  -- the shifted large-values bound at `t₀ = −nΔ`
  have hshift := integral_norm_dirPoly_le_largeValues_shift M hM c' hΔ n hn
    (-(((2 * n : ℕ) : ℝ) * Δ / 2))
  have hend : -(((2 * n : ℕ) : ℝ) * Δ / 2) + ((2 * n : ℕ) : ℝ) * Δ
      = ((2 * n : ℕ) : ℝ) * Δ / 2 := by ring
  rw [hend] at hshift
  exact hshift

end RHTower.Sieve
end
