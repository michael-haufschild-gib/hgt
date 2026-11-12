import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.PowerTailContactGrowthDetectsZeros
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.OrderedDirichletMellinPairing
import GaloisForLFunctions.ArithmeticCorrespondencePositivity.ThePrimeErrorEnergyPaysTheCriticalZeros
import Mathlib.NumberTheory.LSeries.Convolution

/-!
# The Dirichlet symbol of weighted prime contacts

The literal contact convolution has symbol
`ζ(s+2a)(-ζ′(s+a)/ζ(s+a)-ζ(s+a))` on its absolute half-plane.
Power twisting shifts the exponent; arithmetic convolution multiplies
these two actual Dirichlet series.
-/

noncomputable section

open Complex Finset Filter Topology
open scoped ArithmeticFunction.zeta

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

/-- Twisting an arithmetic source by a real power shifts each Dirichlet term. -/
theorem term_powerTailTwist (a : ℝ) (f : ArithmeticFunction ℝ) (s : ℂ) (n : ℕ) :
    LSeries.term (fun k => (powerTailTwist a f k : ℂ)) s n =
      LSeries.term (fun k => (f k : ℂ)) (s + (a : ℂ)) n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [LSeries.term_zero]
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnc : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  rw [LSeries.term_of_ne_zero (ne_of_gt hn),
    LSeries.term_of_ne_zero (ne_of_gt hn), powerTailTwist_apply,
    powerTailWeight, Complex.ofReal_mul, Complex.ofReal_cpow hn0.le]
  simp only [Complex.ofReal_neg, Complex.ofReal_natCast]
  rw [Complex.cpow_add s (a : ℂ) hnc, Complex.cpow_neg]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem LSeriesSummable_powerTailTwist_iff (a : ℝ) (f : ArithmeticFunction ℝ) (s : ℂ) :
    LSeriesSummable (fun n => (powerTailTwist a f n : ℂ)) s ↔
      LSeriesSummable (fun n => (f n : ℂ)) (s + (a : ℂ)) := by
  unfold LSeriesSummable
  rw [show LSeries.term (fun n => (powerTailTwist a f n : ℂ)) s =
      LSeries.term (fun n => (f n : ℂ)) (s + (a : ℂ)) from
    funext (term_powerTailTwist a f s)]

theorem LSeries_powerTailTwist (a : ℝ) (f : ArithmeticFunction ℝ) (s : ℂ) :
    LSeries (fun n => (powerTailTwist a f n : ℂ)) s =
      LSeries (fun n => (f n : ℂ)) (s + (a : ℂ)) := by
  exact tsum_congr (term_powerTailTwist a f s)

private theorem ofReal_arithmetic_convolution (f g : ArithmeticFunction ℝ) :
    (fun n => ((f * g) n : ℂ)) =
      LSeries.convolution (fun n => (f n : ℂ)) (fun n => (g n : ℂ)) := by
  funext n
  simp only [ArithmeticFunction.mul_apply, LSeries.convolution_def,
    Complex.ofReal_sum, Complex.ofReal_mul]

private theorem zeta_source_eq_one {n : ℕ} (hn : n ≠ 0) :
    (((ζ : ArithmeticFunction ℝ) n : ℝ) : ℂ) = (1 : ℕ → ℂ) n := by
  simp [hn]

private theorem prime_deviation_source {n : ℕ} (hn : n ≠ 0) :
    (((ArithmeticFunction.vonMangoldt - (ζ : ArithmeticFunction ℝ)) n : ℝ) : ℂ) =
      ((fun k => (ArithmeticFunction.vonMangoldt k : ℂ)) - 1) n := by
  change ((ArithmeticFunction.vonMangoldt n - (ζ : ArithmeticFunction ℝ) n : ℝ) : ℂ) =
    (ArithmeticFunction.vonMangoldt n : ℂ) - 1
  rw [Complex.ofReal_sub, zeta_source_eq_one hn, Pi.one_apply]

/-- Absolute convergence of both factors on the initial half-plane. -/
theorem LSeriesSummable_powerContacts {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 1 < s.re + a) :
    LSeriesSummable (fun n => ((powerTailZeta (2 * a) * powerTailPrimeDeviation a) n : ℂ)) s := by
  have hsa : 1 < (s + (a : ℂ)).re := by simpa only [add_re, ofReal_re] using hs
  have hs2a : 1 < (s + ((2 * a : ℝ) : ℂ)).re := by
    simp only [add_re, ofReal_re]
    linarith only [hs, ha]
  have hz : LSeriesSummable (fun n => (powerTailZeta (2 * a) n : ℂ)) s := by
    rw [powerTailZeta, LSeriesSummable_powerTailTwist_iff]
    exact (LSeriesSummable_congr _ (fun {n} hn => zeta_source_eq_one hn)).mpr
      (LSeriesSummable_one_iff.mpr hs2a)
  have hp : LSeriesSummable (fun n => (powerTailPrimeDeviation a n : ℂ)) s := by
    rw [powerTailPrimeDeviation, LSeriesSummable_powerTailTwist_iff]
    exact (LSeriesSummable_congr _ (fun {n} hn => prime_deviation_source hn)).mpr
      ((ArithmeticFunction.LSeriesSummable_vonMangoldt hsa).sub
        (LSeriesSummable_one_iff.mpr hsa))
  rw [ofReal_arithmetic_convolution]
  exact hz.convolution hp

/-- Exact symbol of the actual weighted prime-contact convolution. -/
theorem LSeries_powerContacts {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs : 1 < s.re + a) :
    LSeries (fun n => ((powerTailZeta (2 * a) * powerTailPrimeDeviation a) n : ℂ)) s =
      riemannZeta (s + ((2 * a : ℝ) : ℂ)) *
        (-deriv riemannZeta (s + (a : ℂ)) / riemannZeta (s + (a : ℂ)) -
          riemannZeta (s + (a : ℂ))) := by
  have hsa : 1 < (s + (a : ℂ)).re := by simpa only [add_re, ofReal_re] using hs
  have hs2a : 1 < (s + ((2 * a : ℝ) : ℂ)).re := by
    simp only [add_re, ofReal_re]
    linarith only [hs, ha]
  have hz : LSeriesSummable (fun n => (powerTailZeta (2 * a) n : ℂ)) s := by
    rw [powerTailZeta, LSeriesSummable_powerTailTwist_iff]
    exact (LSeriesSummable_congr _ (fun {n} hn => zeta_source_eq_one hn)).mpr
      (LSeriesSummable_one_iff.mpr hs2a)
  have hp : LSeriesSummable (fun n => (powerTailPrimeDeviation a n : ℂ)) s := by
    rw [powerTailPrimeDeviation, LSeriesSummable_powerTailTwist_iff]
    exact (LSeriesSummable_congr _ (fun {n} hn => prime_deviation_source hn)).mpr
      ((ArithmeticFunction.LSeriesSummable_vonMangoldt hsa).sub
        (LSeriesSummable_one_iff.mpr hsa))
  rw [ofReal_arithmetic_convolution, LSeries_convolution' hz hp,
    powerTailZeta, LSeries_powerTailTwist, powerTailPrimeDeviation, LSeries_powerTailTwist,
    LSeries_congr (fun {n} hn => zeta_source_eq_one hn),
    LSeries_congr (fun {n} hn => prime_deviation_source hn),
    LSeries_one_eq_riemannZeta hs2a,
    LSeries_sub (ArithmeticFunction.LSeriesSummable_vonMangoldt hsa)
      (LSeriesSummable_one_iff.mpr hsa),
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hsa,
    LSeries_one_eq_riemannZeta hsa]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
