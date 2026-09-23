import GaloisForLFunctions.RHTower.Sieve.DirichletFirstMomentLargeValues
/-!
# The first moment on an arbitrary interval

Translating the frequency of a Dirichlet polynomial twists its coefficients by unimodular factors, so the `ℓ²` mass
is unchanged and the large-values first-moment bound holds on *every* interval of a given length, not only on the
canonical one:

`∫_{t₀}^{t₀+2nΔ} ‖D(t)‖ dt ≤ 2Δ·√(n·((2n+1)Δ + 4N(1+log N))(1/Δ + 2 log N)·∑‖a_i‖²)`.

In particular it applies to `[−T, T]` with `t₀ = −T` and `2nΔ = 2T`, which is the range a Perron integral runs over.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Finset

/-- **Translating the frequency of a Dirichlet polynomial twists its coefficients.**  The twist is unimodular, so
the `ℓ²` mass is unchanged. -/
theorem dirPoly_translate (N : ℕ) (a : Fin N → ℂ) (t₀ t : ℝ) :
    dirPoly N a (t₀ + t)
      = dirPoly N (fun i => a i
          * Complex.exp (((t₀ * Real.log (((i : ℕ) : ℝ) + 1) : ℝ) : ℂ) * I)) t := by
  rw [dirPoly, dirPoly]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [mul_assoc, ← Complex.exp_add]
  congr 1
  push_cast
  ring_nf

theorem norm_dirPoly_twist_coeff (N : ℕ) (a : Fin N → ℂ) (t₀ : ℝ) (i : Fin N) :
    ‖a i * Complex.exp (((t₀ * Real.log (((i : ℕ) : ℝ) + 1) : ℝ) : ℂ) * I)‖ = ‖a i‖ := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **The first moment on an arbitrary interval.**  The bound of the large-values composition holds on every
interval of the same length: translating the frequency twists the coefficients without changing their `ℓ²` mass. -/
theorem integral_norm_dirPoly_le_largeValues_shift (N : ℕ) (hN : 2 ≤ N) (a : Fin N → ℂ) {Δ : ℝ}
    (hΔ : 0 < Δ) (n : ℕ) (hn : 1 ≤ n) (t₀ : ℝ) :
    (∫ t in t₀..(t₀ + ((2 * n : ℕ) : ℝ) * Δ), ‖dirPoly N a t‖)
      ≤ 2 * Δ * Real.sqrt ((n : ℝ)
          * ((((2 * n + 1 : ℕ) : ℝ) * Δ + 4 * (N : ℝ) * (1 + Real.log N))
              * (1 / Δ + 2 * Real.log N) * ∑ i : Fin N, ‖a i‖ ^ (2 : ℕ))) := by
  classical
  set s : ℝ := t₀ - Δ / 2 with hs
  set ã : Fin N → ℂ := fun i => a i
    * Complex.exp (((s * Real.log (((i : ℕ) : ℝ) + 1) : ℝ) : ℂ) * I) with hã
  have hmass : ∑ i : Fin N, ‖ã i‖ ^ (2 : ℕ) = ∑ i : Fin N, ‖a i‖ ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hã]
    simp only
    rw [norm_dirPoly_twist_coeff N a s i]
  have hshift : ∀ t : ℝ, ‖dirPoly N a (s + t)‖ = ‖dirPoly N ã t‖ := by
    intro t
    rw [dirPoly_translate N a s t]
  -- move the interval to the canonical position
  have hint : (∫ t in t₀..(t₀ + ((2 * n : ℕ) : ℝ) * Δ), ‖dirPoly N a t‖)
      = ∫ u in (Δ / 2)..(Δ / 2 + ((2 * n : ℕ) : ℝ) * Δ), ‖dirPoly N ã u‖ := by
    have hcomp := intervalIntegral.integral_comp_add_left
      (a := Δ / 2) (b := Δ / 2 + ((2 * n : ℕ) : ℝ) * Δ) (fun t => ‖dirPoly N a t‖) s
    rw [show s + Δ / 2 = t₀ by rw [hs]; ring,
      show s + (Δ / 2 + ((2 * n : ℕ) : ℝ) * Δ) = t₀ + ((2 * n : ℕ) : ℝ) * Δ by rw [hs]; ring] at hcomp
    rw [← hcomp]
    exact intervalIntegral.integral_congr (fun u _ => hshift u)
  rw [hint, ← hmass]
  exact integral_norm_dirPoly_le_largeValues N hN ã hΔ n hn

end RHTower.Sieve
end
