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
import GaloisForLFunctions.RHTower.ArchimedeanGamma
import Mathlib.NumberTheory.LSeries.Linearity
import Mathlib.NumberTheory.LSeries.Positivity

open Complex Function
open scoped ComplexOrder

namespace RHTower

noncomputable section

open GaloisForLFunctions

/-- Closed form of the completed archimedean/boundary logarithmic derivative on the
positive-real-part half-plane. -/
theorem logDeriv_archFactor_closed_off_poles {s : ℂ}
    (hpole : ∀ m : ℕ, s / 2 ≠ -(m : ℂ)) (h0 : s ≠ 0) (h1 : s ≠ 1) :
    logDeriv archFactor s =
      1 / s + 1 / (s - 1) + gammaRealLogConnection s := by
  have hG : Complex.Gammaℝ s ≠ 0 := by
    intro hzero
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.mp hzero
    exact hpole n (by rw [hn]; ring)
  rw [logDeriv_apply, (hasDerivAt_archFactor_off_poles hpole).deriv]
  unfold archFactorDeriv archFactor gammaRealLogConnection
  field_simp [h0, sub_ne_zero.mpr h1, hG]
  ring

/-- Closed form of the completed archimedean/boundary logarithmic derivative on the
positive-real-part half-plane. -/
theorem logDeriv_archFactor_closed {s : ℂ} (hs : 0 < s.re)
    (h0 : s ≠ 0) (h1 : s ≠ 1) :
    logDeriv archFactor s =
      1 / s + 1 / (s - 1) + gammaRealLogConnection s :=
  logDeriv_archFactor_closed_off_poles (div_two_ne_neg_nat_of_re_pos hs) h0 h1

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

/-- The coefficient exposed by the `+2` shift of the completed logarithmic derivative. -/
def filteredVonMangoldtCoeff (n : ℕ) : ℂ :=
  (ArithmeticFunction.vonMangoldt n : ℂ) *
    (1 - (n : ℂ) ^ (-(2 : ℂ)))

/-- Every coefficient of the filtered von Mangoldt source is nonnegative. -/
theorem filteredVonMangoldtCoeff_nonneg (n : ℕ) :
    0 ≤ filteredVonMangoldtCoeff n := by
  rcases lt_trichotomy n 1 with hn | hn | hn
  · have : n = 0 := by omega
    subst n
    simp [filteredVonMangoldtCoeff]
  · subst n
    simp [filteredVonMangoldtCoeff]
  · have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn.le
    have hpowR : (n : ℝ) ^ (-(2 : ℝ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hnR (by norm_num)
    have hcpow : (n : ℂ) ^ (-(2 : ℂ)) = ((n : ℝ) ^ (-(2 : ℝ)) : ℝ) := by
      simpa using (Complex.ofReal_cpow (Nat.cast_nonneg n) (-(2 : ℝ))).symm
    have hfac : 0 ≤ (1 - (n : ℂ) ^ (-(2 : ℂ))) := by
      rw [hcpow]
      exact_mod_cast sub_nonneg.mpr hpowR
    exact mul_nonneg (by exact_mod_cast
      (ArithmeticFunction.vonMangoldt_nonneg (n := n))) hfac

/-- The coefficient at the first prime is strictly positive. -/
theorem filteredVonMangoldtCoeff_two_pos :
    0 < filteredVonMangoldtCoeff 2 := by
  rw [filteredVonMangoldtCoeff,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  have hlog : 0 < (Real.log 2 : ℂ) := by
    exact_mod_cast Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hcpow : (2 : ℂ) ^ (-(2 : ℂ)) = ((2 : ℝ) ^ (-(2 : ℝ)) : ℝ) := by
    simpa using (Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2) (-(2 : ℝ))).symm
  have hpowR : (2 : ℝ) ^ (-(2 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hfacR : 0 < (1 : ℝ) - (2 : ℝ) ^ (-(2 : ℝ)) := sub_pos.mpr hpowR
  have hfacC : 0 < ((1 - (2 : ℝ) ^ (-(2 : ℝ)) : ℝ) : ℂ) := by
    exact_mod_cast hfacR
  change 0 < (Real.log 2 : ℂ) * (1 - (2 : ℂ) ^ (-(2 : ℂ)))
  rw [hcpow]
  apply mul_pos hlog
  simpa using hfacC

/-- The filtered von Mangoldt source is summable throughout its Euler half-plane. -/
theorem LSeriesSummable_filteredVonMangoldtCoeff {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable filteredVonMangoldtCoeff s := by
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
  have hfg : f - g = filteredVonMangoldtCoeff := by
    funext n
    simp only [Pi.sub_apply, f, g, filteredVonMangoldtCoeff]
    ring
  rw [← hfg]
  exact hf.sub hg

/-- On every real Euler anchor, the actual filtered von Mangoldt source is strictly positive. -/
theorem LSeries_filteredVonMangoldtCoeff_pos {σ : ℝ} (hσ : 1 < σ) :
    0 < LSeries filteredVonMangoldtCoeff σ := by
  rw [LSeries]
  exact (LSeriesSummable_filteredVonMangoldtCoeff
    (s := (σ : ℂ)) (by simpa using hσ)).tsum_pos
      (fun n => LSeries.term_nonneg (filteredVonMangoldtCoeff_nonneg n) σ)
      2 (LSeries.term_pos (by norm_num) filteredVonMangoldtCoeff_two_pos σ)

/-- **Strict Euler-anchor sign for the actual completed source.**  On every real
`σ > 1`, the rationally renormalized `+2` shift defect of `xi'/xi` is strictly positive. -/
theorem xi_logDeriv_shift_two_filtered_source_pos {σ : ℝ} (hσ : 1 < σ) :
    0 < logDeriv xi (σ + 2) - logDeriv xi σ -
        (1 / (σ + 2) + 1 / (σ + 1) - 1 / (σ - 1)) := by
  have h := xi_logDeriv_shift_two_exposes_prime_source
    (s := (σ : ℂ)) (by simpa using hσ)
  rw [show LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (1 - (n : ℂ) ^ (-(2 : ℂ)))) (σ : ℂ) =
      LSeries filteredVonMangoldtCoeff (σ : ℂ) by rfl] at h
  rw [h]
  exact LSeries_filteredVonMangoldtCoeff_pos hσ

end

end RHTower
