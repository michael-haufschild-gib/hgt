import GaloisForLFunctions.RHTower.Sieve.FejerIntegralPair

/-!
# The short-interval localisation

Composing the pairing identity with the localisation bound states the whole construction in terms of
the polynomial itself:

`‖∫_0^T F(t)(1 - t/T) dt + ∫_0^T F(-t)(1 - t/T) dt - a_1 T‖ ≤ ∑_{n ≥ 2} |a_n| · 4/(T (log n)²)`.

The symmetrised Fejér average of a Dirichlet polynomial over `[0,T]` is its first coefficient times
`T`, up to an error that is `O(T^{-1})` for fixed coefficients.  Nothing here is asymptotic or
conditional: it is an inequality valid for every `N`, every coefficient vector and every `T > 0`.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

/-- **The short-interval localisation of a Dirichlet polynomial.** -/
theorem norm_fejer_integral_sub_main_le (N : ℕ) (hN : 0 < N) (a : Fin N → ℂ) {T : ℝ}
    (hT : 0 < T) :
    ‖(∫ t in (0 : ℝ)..T, dirPoly N a t * ((1 - t / T : ℝ) : ℂ))
        + (∫ t in (0 : ℝ)..T, dirPoly N a (-t) * ((1 - t / T : ℝ) : ℂ))
        - a ⟨0, hN⟩ * (T : ℂ)‖
      ≤ ∑ n ∈ (Finset.univ : Finset (Fin N)).erase ⟨0, hN⟩,
          ‖a n‖ * (4 / (T * (Real.log (((n : ℕ) : ℝ) + 1)) ^ 2)) := by
  rw [integral_fejer_pair_eq N a T]
  exact norm_fejer_dirPoly_sub_main_le N hN a hT

end RHTower.Sieve
