import GaloisForLFunctions.RHTower.Sieve.ConvolutionMasses
import GaloisForLFunctions.RHTower.Sieve.GhsInnerFirstMoment
/-!
# The first moment of a product of two finitely supported series

The product of two Dirichlet series is the series of their convolution, and a convolution of finitely supported
sequences is finitely supported, so the large-values first moment applies to the product **directly**:

`∫_{|y| ≤ nΔ} ‖L(a,σ+iy)L(b,σ+iy)‖ dy
    ≤ 2Δ·√(n·((2n+1)Δ + 4M²(1+log M²))(1/Δ + 2 log M²)·((ℓ¹a)(ℓ¹b))²)`.

No Cauchy–Schwarz splitting into two mean squares, no trivial size of either factor, and the mass is the square of
the product of the two damped `ℓ¹` masses.  Summability at every point is immediate for finite support, which is what
lets `LSeries_convolution'` be applied without a half-plane restriction.
-/

noncomputable section
namespace RHTower.Sieve
open Complex Finset

/-- A finitely supported Dirichlet series is summable at every point. -/
theorem LSeriesSummable_of_support {c : ℕ → ℂ} {s : Finset ℕ}
    (hc : ∀ k : ℕ, c k ≠ 0 → k ∈ s) (t : ℂ) : LSeriesSummable c t := by
  classical
  refine summable_of_ne_finset_zero (s := s) fun k hk => ?_
  rcases eq_or_ne k 0 with rfl | hk0
  · rw [LSeries.term_def, if_pos rfl]
  · have hzero : c k = 0 := by
      by_contra hne
      exact hk (hc k hne)
    rw [LSeries.term_def, if_neg hk0, hzero, zero_div]

/-- **The first moment of a product of two finitely supported series.**  The product is the series of the
convolution, which is finitely supported, so the large-values first moment applies to it directly — no
Cauchy–Schwarz splitting, and the mass is the square of the product of the two damped `ℓ¹` masses. -/
theorem integral_norm_LSeries_mul_le_largeValues {a b : ℕ → ℂ} {M : ℕ} (hM : 2 ≤ M * M)
    (ha : ∀ k : ℕ, a k ≠ 0 → k ∈ Finset.Icc 1 M) (hb : ∀ k : ℕ, b k ≠ 0 → k ∈ Finset.Icc 1 M)
    (σ : ℝ) {Δ : ℝ} (hΔ : 0 < Δ) (n : ℕ) (hn : 1 ≤ n) :
    (∫ y in (-(((2 * n : ℕ) : ℝ) * Δ / 2))..(((2 * n : ℕ) : ℝ) * Δ / 2),
        ‖LSeries a ((σ : ℂ) + (y : ℝ) * I) * LSeries b ((σ : ℂ) + (y : ℝ) * I)‖)
      ≤ 2 * Δ * Real.sqrt ((n : ℝ)
          * ((((2 * n + 1 : ℕ) : ℝ) * Δ + 4 * ((M * M : ℕ) : ℝ) * (1 + Real.log ((M * M : ℕ) : ℝ)))
              * (1 / Δ + 2 * Real.log ((M * M : ℕ) : ℝ))
              * ((∑ d ∈ Finset.Icc 1 M, ‖a d‖ * (d : ℝ) ^ (-σ))
                  * ∑ e ∈ Finset.Icc 1 M, ‖b e‖ * (e : ℝ) ^ (-σ)) ^ 2)) := by
  classical
  set c : ℕ → ℂ := LSeries.convolution a b with hcdef
  have hcsupp : ∀ k : ℕ, c k ≠ 0 → k ∈ Finset.Icc 1 (M * M) := by
    intro k hk
    rw [hcdef] at hk
    exact convolution_mem_Icc_of_support ha hb hk
  -- the product of the two series is the series of the convolution
  have hprod : ∀ y : ℝ, LSeries a ((σ : ℂ) + (y : ℝ) * I) * LSeries b ((σ : ℂ) + (y : ℝ) * I)
      = LSeries c ((σ : ℂ) + (y : ℝ) * I) := by
    intro y
    rw [hcdef]
    exact (LSeries_convolution' (LSeriesSummable_of_support ha _)
      (LSeriesSummable_of_support hb _)).symm
  rw [intervalIntegral.integral_congr (g := fun y => ‖LSeries c ((σ : ℂ) + (y : ℝ) * I)‖)
    (fun y _ => by rw [hprod y])]
  refine le_trans (integral_norm_LSeries_le_largeValues hM hcsupp σ hΔ n hn) ?_
  refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by positivity)
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [sum_fin_normSq_damped_eq]
  have hmass := sum_normSq_convolution_le ha hb σ
  refine le_trans (le_of_eq ?_) hmass
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hcdef]
  ring

end RHTower.Sieve
end
