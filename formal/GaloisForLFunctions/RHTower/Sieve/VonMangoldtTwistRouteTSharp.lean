import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistBalancedBound
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistPrimeSum

/-!
# The sharp twisted prime sum on the Route-T contour

Three transports separate the contour estimate from the object Matomäki--Radziwiłł consume.  The
first removes the factor `2π` of the Perron normalisation.  The second removes the smoothing, at the
cost of the window width times the largest von Mangoldt value it meets.  The third removes the
proper prime powers, at a cost that is exactly the *untwisted* `ψ - θ`, because the twist has
modulus one and therefore cannot interfere with a discrepancy that is already real and nonnegative.

None of the three sees the twist.  All the twist-dependence lives in the contour bound, where it
enters through the height `3|τ|/2` at which the zero-free width is read.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- The Perron normalisation, undone. -/
theorem norm_smul_two_pi (X : ℂ) :
    ‖(2 * Real.pi : ℝ) • X‖ = (2 * Real.pi) * ‖X‖ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]

/-- **The sharp twisted Chebyshev sum on the Route-T contour.** -/
theorem exists_norm_partialSum_vonMangoldtTwist_routeT_le :
    ∃ A Creg delta Ctot τ₀ : ℝ, 0 < Creg ∧ 0 < delta ∧ 0 < Ctot ∧ 2 ≤ τ₀ ∧
      ∀ (K : ℕ) (H τ : ℝ), Real.exp 9 ≤ (K : ℝ) → 0 < H → H ≤ (K : ℝ) → τ₀ ≤ |τ| →
        ‖∑ n ∈ Finset.range (K + 1), vonMangoldtTwist τ n‖
          ≤ Ctot * (K : ℝ) * ((K : ℝ) / H) ^ 2
                * ((Real.log (K : ℝ)) ^ 2 / |τ|
                    + (1 / |τ| + Real.log (3 * |τ| / 2)
                        / routeTZeroFreeWidth A (3 * |τ| / 2 + 1))
                      * ((3 * (K : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
                          + 1 / |τ| ^ 2))
              / (2 * Real.pi)
            + Real.log ((K : ℝ) + H) * H := by
  obtain ⟨A, Creg, delta, Ctot, τ₀, hCreg, hdelta, hCtot, hτ₀, hbound⟩ :=
    exists_norm_tsum_vonMangoldtTwist_routeT_balanced
  refine ⟨A, Creg, delta, Ctot, τ₀, hCreg, hdelta, hCtot, hτ₀, ?_⟩
  intro K H τ hK hH0 hHK hτ
  have hK0 : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hK
  have hK1 : (1 : ℝ) ≤ (K : ℝ) := by
    have h := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 9)
    linarith
  have hKH : (1 : ℝ) ≤ (K : ℝ) + H := by linarith
  have hb := hbound (K : ℝ) H τ hK hH0 hHK hτ
  rw [norm_smul_two_pi] at hb
  exact norm_partialSum_vonMangoldtTwist_le_of_smoothed_bound τ hH0 hKH hb

/-- **The sharp twisted prime sum on the Route-T contour.**  The last term is the untwisted
prime-power mass; it is `O(√K log²K)` and never competes with the contour saving. -/
theorem exists_norm_partialSum_vonMangoldtPrimeTwist_routeT_le :
    ∃ A Creg delta Ctot τ₀ : ℝ, 0 < Creg ∧ 0 < delta ∧ 0 < Ctot ∧ 2 ≤ τ₀ ∧
      ∀ (K : ℕ) (H τ : ℝ), Real.exp 9 ≤ (K : ℝ) → 0 < H → H ≤ (K : ℝ) → τ₀ ≤ |τ| →
        ‖∑ n ∈ Finset.range (K + 1), vonMangoldtPrimeTwist τ n‖
          ≤ Ctot * (K : ℝ) * ((K : ℝ) / H) ^ 2
                * ((Real.log (K : ℝ)) ^ 2 / |τ|
                    + (1 / |τ| + Real.log (3 * |τ| / 2)
                        / routeTZeroFreeWidth A (3 * |τ| / 2 + 1))
                      * ((3 * (K : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
                          + 1 / |τ| ^ 2))
              / (2 * Real.pi)
            + Real.log ((K : ℝ) + H) * H
            + primePowerDefect K := by
  obtain ⟨A, Creg, delta, Ctot, τ₀, hCreg, hdelta, hCtot, hτ₀, hbound⟩ :=
    exists_norm_partialSum_vonMangoldtTwist_routeT_le
  refine ⟨A, Creg, delta, Ctot, τ₀, hCreg, hdelta, hCtot, hτ₀, ?_⟩
  intro K H τ hK hH0 hHK hτ
  exact norm_partialSum_vonMangoldtPrimeTwist_le τ K (hbound K H τ hK hH0 hHK hτ)

end RHTower.Sieve
