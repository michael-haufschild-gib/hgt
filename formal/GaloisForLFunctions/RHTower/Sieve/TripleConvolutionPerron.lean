import GaloisForLFunctions.RHTower.Sieve.VonMangoldtPerron
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# The Perron passage for a triple Dirichlet convolution

The smoothed Perron identity applies to any absolutely convergent Dirichlet series, so it applies to a
threefold convolution, whose series is the product of the three factors:

`2π ∑ₙ (a ⍟ (b ⍟ c))(n) w(n) = ∫_ℝ L(a,s_y)·L(b,s_y)·L(c,s_y)·W(s_y) dy`,   `s_y = σ + iy`, `σ > 1`,

where `w` is the smoothing weight and `W` its Mellin transform.  The only hypotheses are that each factor
is `LSeriesSummable` at `σ` — no boundedness of the coefficients, which is essential here: the
convolution produced by two applications of the log recursion carries two logarithms.

This is the outer passage of the Granville–Harper–Soundararajan step 4: it converts the triple
multiplicative convolution into a vertical integral in which one factor is estimated pointwise (the Euler
product) and the other two in mean square.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- **The Perron passage for a triple Dirichlet convolution.**  The smoothed sum of a threefold
convolution is the vertical integral of the product of the three Dirichlet series against the smoothing
kernel. -/
theorem tsum_mul_smoothWeight_convolution_eq_integral {a b c : ℕ → ℂ} {N H : ℝ}
    (hN : 0 < N) (hH : 0 < H) {σ : ℝ} (hσ : 1 < σ)
    (hsa : LSeriesSummable a (σ : ℂ)) (hsb : LSeriesSummable b (σ : ℂ))
    (hsc : LSeriesSummable c (σ : ℂ)) :
    (2 * Real.pi : ℝ) •
        (∑' n : ℕ, (LSeries.convolution a (LSeries.convolution b c)) n
          * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ∫ y : ℝ, (LSeries a ((σ : ℂ) + (y : ℝ) * I) * LSeries b ((σ : ℂ) + (y : ℝ) * I)
            * LSeries c ((σ : ℂ) + (y : ℝ) * I))
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((σ : ℂ) + (y : ℝ) * I) := by
  set d : ℕ → ℂ := LSeries.convolution a (LSeries.convolution b c) with hd
  have hd0 : d 0 = 0 := LSeries.convolution_map_zero _ _
  have hsd : LSeriesSummable d (σ : ℂ) := hsa.convolution (hsb.convolution hsc)
  have hsum := summable_norm_mul_rpow_of_LSeriesSummable (by linarith : (0:ℝ) < σ) hsd
  have hmain := tsum_mul_smoothWeight_eq_integral_summable (a := d) hd0 hN hH hσ hsum
  rw [hmain]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  -- identify the inner Dirichlet series with the product
  have hre : ((σ : ℂ) + (y : ℝ) * I).re = σ := by
    simp
  have hsa' : LSeriesSummable a ((σ : ℂ) + (y : ℝ) * I) :=
    LSeriesSummable.of_re_le_re (by rw [hre]; simp) hsa
  have hsb' : LSeriesSummable b ((σ : ℂ) + (y : ℝ) * I) :=
    LSeriesSummable.of_re_le_re (by rw [hre]; simp) hsb
  have hsc' : LSeriesSummable c ((σ : ℂ) + (y : ℝ) * I) :=
    LSeriesSummable.of_re_le_re (by rw [hre]; simp) hsc
  have hprod : LSeries d ((σ : ℂ) + (y : ℝ) * I)
      = LSeries a ((σ : ℂ) + (y : ℝ) * I) * LSeries b ((σ : ℂ) + (y : ℝ) * I)
        * LSeries c ((σ : ℂ) + (y : ℝ) * I) := by
    rw [hd, LSeries_convolution' hsa' (hsb'.convolution hsc'),
      LSeries_convolution' hsb' hsc', mul_assoc]
  have hterm : (∑' n : ℕ, d n * (n : ℂ) ^ (-((σ : ℂ) + (y : ℝ) * I)))
      = LSeries d ((σ : ℂ) + (y : ℝ) * I) := by
    rw [LSeries]
    refine tsum_congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · rw [LSeries.term_def, if_pos rfl, hd0, zero_mul]
    · rw [LSeries.term_def, if_neg hn, Complex.cpow_neg, div_eq_mul_inv]
  rw [hterm, hprod]

end RHTower.Sieve
end
