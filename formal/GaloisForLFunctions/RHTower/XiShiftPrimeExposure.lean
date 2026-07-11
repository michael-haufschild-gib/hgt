/-
# The even shift exposes the completed xi prime source

On the absolute-convergence half-plane, the logarithmic derivative of `xi` splits into
the archimedean/boundary logarithmic derivative and `ζ'/ζ`.  Translation by two has two
compatible effects:

* the Gamma recurrence makes the archimedean difference rational;
* the von Mangoldt term at `n` is multiplied by `n⁻²`.

Subtracting the rational archimedean difference therefore exposes the exact filtered
von Mangoldt series with coefficient `Λ(n)(1-n⁻²)`.  This file proves the analytic identity
only.  It does not formalize Ostrowski's theorem or infer hypertranscendence from the infinite
prime support.
-/
import GaloisForLFunctions.RHTower.XiRelativeResolventFlux
import GaloisForLFunctions.ArchimedeanGamma
import Mathlib.NumberTheory.LSeries.Linearity

open Complex Function

namespace RHTower

noncomputable section

open GaloisForLFunctions

/-- Closed form of the completed archimedean/boundary logarithmic derivative on the
positive-real-part half-plane. -/
theorem logDeriv_archFactor_closed {s : ℂ} (hs : 0 < s.re)
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    logDeriv archFactor s =
      1 / s + 1 / (s - 1) + gammaRealLogConnection s := by
  have hG : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hs
  rw [logDeriv_apply, (hasDerivAt_archFactor_of_re_pos hs).deriv]
  unfold archFactorDeriv archFactor gammaRealLogConnection
  field_simp [h0, sub_ne_zero.mpr h1, hG]
  ring

/-- Translation by two removes the common digamma mode from the completed archimedean
factor and leaves an explicit rational function. -/
theorem logDeriv_archFactor_shift_two {s : ℂ} (hs : 1 < s.re) :
    logDeriv archFactor (s + 2) - logDeriv archFactor s =
      1 / (s + 2) + 1 / (s + 1) - 1 / (s - 1) := by
  have hspos : 0 < s.re := lt_trans zero_lt_one hs
  have hsp2 : 0 < (s + 2).re := by
    norm_num [Complex.add_re]
    linarith
  have hs0 : s ≠ 0 := by intro h; subst s; norm_num at hs
  have hs1 : s ≠ 1 := by intro h; subst s; norm_num at hs
  have hs2 : s + 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re] at hre
    linarith
  have hs3 : s + 2 ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num [Complex.add_re] at hre
    linarith
  have hdig : ∀ m : ℕ, s / 2 ≠ -(m : ℂ) := by
    intro m h
    have hre := congrArg Complex.re h
    norm_num [Complex.div_re] at hre
    have hm : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  rw [logDeriv_archFactor_closed hsp2 hs2 hs3,
    logDeriv_archFactor_closed hspos hs0 hs1]
  rw [show (s + 2) - 1 = s + 1 by ring]
  unfold gammaRealLogConnection
  rw [show (s + 2) / 2 = s / 2 + 1 by ring,
    GaloisForLFunctions.digamma_half_add_one hdig]
  field_simp [hs0, hs1, hs2, sub_ne_zero.mpr hs1]
  ring

/-- Translating an ordinary L-series by two is coefficientwise multiplication by `n⁻²`. -/
theorem LSeries_shift_two (f : ℕ → ℂ) (s : ℂ) :
    LSeries f (s + 2) = LSeries (fun n => f n * (n : ℂ) ^ (-(2 : ℂ))) s := by
  unfold LSeries
  apply tsum_congr
  intro n
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
  rw [Complex.cpow_add s (2 : ℂ) (Nat.cast_ne_zero.mpr hn)]
  simp only [Complex.cpow_neg]
  field_simp [Nat.cast_ne_zero.mpr hn]

/-- The difference of the von Mangoldt series at `s` and `s+2` is the L-series with
coefficient `Λ(n)(1-n⁻²)`. -/
theorem filtered_vonMangoldt_shift_two {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) s -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (s + 2) =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (1 - (n : ℂ) ^ (-(2 : ℂ)))) s := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let g : ℕ → ℂ := fun n => f n * (n : ℂ) ^ (-(2 : ℂ))
  have hf : LSeriesSummable f s := ArithmeticFunction.LSeriesSummable_vonMangoldt hs
  have hsp : 1 < (s + 2).re := by
    norm_num [Complex.add_re]
    linarith
  have hgshift : LSeriesSummable f (s + 2) :=
    ArithmeticFunction.LSeriesSummable_vonMangoldt hsp
  have hterm : ∀ n : ℕ, LSeries.term f (s + 2) n = LSeries.term g s n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
      rw [Complex.cpow_add s (2 : ℂ) (Nat.cast_ne_zero.mpr hn)]
      simp only [g, Complex.cpow_neg]
      field_simp [Nat.cast_ne_zero.mpr hn]
  have hg : LSeriesSummable g s := by
    unfold LSeriesSummable at hgshift ⊢
    exact hgshift.congr hterm
  have hsub := LSeries_sub hf hg
  rw [LSeries_shift_two f s]
  rw [← hsub]
  apply LSeries_congr
  intro n hn
  simp only [Pi.sub_apply, f, g]
  ring

/-- **Even-shift prime exposure for the actual Riemann xi function.**  After subtracting
the explicit rational archimedean/boundary difference, the shift defect of `xi'/xi` is
exactly the filtered von Mangoldt L-series `Σ Λ(n)(1-n⁻²)n⁻ˢ`. -/
theorem xi_logDeriv_shift_two_exposes_prime_source {s : ℂ} (hs : 1 < s.re) :
    logDeriv xi (s + 2) - logDeriv xi s -
        (1 / (s + 2) + 1 / (s + 1) - 1 / (s - 1)) =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) *
        (1 - (n : ℂ) ^ (-(2 : ℂ)))) s := by
  have hsp : 1 < (s + 2).re := by
    norm_num [Complex.add_re]
    linarith
  have hsplit := seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re hs
  have hsplit2 := seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re hsp
  rw [seamFluxCochain] at hsplit hsplit2
  have hp := filtered_vonMangoldt_shift_two hs
  rw [infinitePrimeFlux_eq_vonMangoldtLSeries hs] at hsplit
  rw [infinitePrimeFlux_eq_vonMangoldtLSeries hsp] at hsplit2
  have harch := logDeriv_archFactor_shift_two hs
  linear_combination hsplit - hsplit2 + harch + hp

end

end RHTower
