import GaloisForLFunctions.RHTower.Sieve.DirichletTruncationError
import GaloisForLFunctions.RHTower.Sieve.DistanceAbscissaBridge
import GaloisForLFunctions.RHTower.Sieve.DirichletMeasureLargeValues
import GaloisForLFunctions.RHTower.Sieve.HalaszFullSeriesSum

/-!
# The truncated twisted series is a Dirichlet polynomial

The corpus's mean-square estimates are stated for `dirPoly N a t = ∑_{n < N} aₙ (n+1)^{it}`.  A truncated
twisted series is such a polynomial: the polar split `n^{-s} = n^{-σ}·n^{-it}` puts the abscissa into the
coefficients and leaves the frequency `-t`, so

`∑_{n ≤ L} f(n) n^{-(σ+it)} = dirPoly L (fun k ↦ f(k+1)(k+1)^{-σ}) (-t)`.

The coefficient square-sum is bounded by `∑_n n^{-2σ}` uniformly in `L`, which is the quantity the
mean-value and large-values estimates consume.
-/

namespace RHTower.Sieve

open Complex Finset

/-- The coefficients of the truncated twisted series. -/
noncomputable def twistedTruncCoeff (f : ℕ → ℂ) (σ : ℝ) (L : ℕ) : Fin L → ℂ :=
  fun k => f ((k : ℕ) + 1) * (((((k : ℕ) + 1 : ℝ)) ^ (-σ) : ℝ) : ℂ)

theorem norm_twistedTruncCoeff_le {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1) (σ : ℝ) (L : ℕ)
    (k : Fin L) :
    ‖twistedTruncCoeff f σ L k‖ ≤ ((((k : ℕ) + 1 : ℝ))) ^ (-σ) := by
  rw [twistedTruncCoeff, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by positivity) _)]
  exact mul_le_of_le_one_left (Real.rpow_nonneg (by positivity) _) (hbdd _)

/-- **The truncated twisted series is a Dirichlet polynomial.** -/
theorem sum_range_twistedSummand_eq_dirPoly {f : ℕ → ℂ} (hf0 : f 0 = 0) (σ t : ℝ) (L : ℕ) :
    ∑ n ∈ Finset.range (L + 1),
        twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) n
      = dirPoly L (twistedTruncCoeff f σ L) (-t) := by
  have hzero : twistedSummand f (((σ : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I) 0 = 0 := by
    rw [twistedSummand, hf0, zero_mul]
  have hpoly : dirPoly L (twistedTruncCoeff f σ L) (-t)
      = ∑ k ∈ Finset.range L,
          (f (k + 1) * (((((k : ℕ) + 1 : ℝ)) ^ (-σ) : ℝ) : ℂ)) *
            Complex.exp (((-t * Real.log ((k : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := by
    rw [dirPoly]
    exact Fin.sum_univ_eq_sum_range (fun k : ℕ =>
      (f (k + 1) * (((((k : ℕ) + 1 : ℝ)) ^ (-σ) : ℝ) : ℂ)) *
        Complex.exp (((-t * Real.log ((k : ℕ) + 1) : ℝ) : ℂ) * Complex.I)) L
  rw [Finset.sum_range_succ', hzero, add_zero, hpoly]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [twistedSummand, natCast_cpow_neg_eq_mul _ (by omega : 0 < k + 1),
    re_ofReal_add_mul_I, im_ofReal_add_mul_I, conj_charFn]
  push_cast
  ring_nf

/-- The coefficient square-sum is bounded uniformly in the length. -/
theorem sum_norm_sq_twistedTruncCoeff_le {f : ℕ → ℂ} (hbdd : ∀ n, ‖f n‖ ≤ 1)
    {σ : ℝ} (hσ : 1 < 2 * σ) (L : ℕ) :
    ∑ k : Fin L, ‖twistedTruncCoeff f σ L k‖ ^ 2 ≤ ∑' n : ℕ, ((n : ℝ)) ^ (-(2 * σ)) := by
  classical
  have hσ0 : (0 : ℝ) < σ := by linarith
  have hterm : ∀ k : Fin L,
      ‖twistedTruncCoeff f σ L k‖ ^ 2 ≤ ((((k : ℕ) + 1 : ℝ))) ^ (-(2 * σ)) := by
    intro k
    have h1 := norm_twistedTruncCoeff_le hbdd σ L k
    have h0 : (0 : ℝ) ≤ ‖twistedTruncCoeff f σ L k‖ := norm_nonneg _
    have hpow : ((((k : ℕ) + 1 : ℝ))) ^ (-(2 * σ))
        = (((((k : ℕ) + 1 : ℝ))) ^ (-σ)) ^ 2 := by
      rw [← Real.rpow_natCast (((((k : ℕ) + 1 : ℝ))) ^ (-σ)) 2,
        ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      ring
    rw [hpow]
    nlinarith [h1, h0]
  refine le_trans (Finset.sum_le_sum fun k _ => hterm k) ?_
  have hrange : ∑ k : Fin L, ((((k : ℕ) + 1 : ℝ))) ^ (-(2 * σ))
      = ∑ k ∈ Finset.range L, ((((k : ℕ) + 1 : ℝ))) ^ (-(2 * σ)) :=
    Fin.sum_univ_eq_sum_range (fun k : ℕ => ((((k : ℕ) + 1 : ℝ))) ^ (-(2 * σ))) L
  rw [hrange]
  have himage : ∑ k ∈ Finset.range L, ((((k : ℕ) + 1 : ℝ))) ^ (-(2 * σ))
      = ∑ n ∈ (Finset.range L).image (fun k : ℕ => k + 1), ((n : ℝ)) ^ (-(2 * σ)) := by
    rw [Finset.sum_image]
    · refine Finset.sum_congr rfl fun k _ => ?_
      push_cast
      ring_nf
    · intro a _ b _ h
      simp only [] at h
      omega
  rw [himage]
  exact (summable_nat_rpow_neg hσ).sum_le_tsum _
    (fun n _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)

end RHTower.Sieve
