import GaloisForLFunctions.RHTower.XiEndpointCompletedValueBound
import GaloisForLFunctions.RHTower.XiHadamardSharpRegion
import GaloisForLFunctions.RHTower.EulerMascheroniCorrectedUpper
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# The reciprocal square sum over the real zeros of `Ξ`

Let `Z = {t ∈ ℝ : Ξ(t) = 0}`, the ordinates of the zeros of `ζ` on the critical line, where
`Ξ(t) = ξ(1/2 + it)`.  For every finite set `s ⊆ Z`,

`Σ_{t ∈ s} 1/(1/4 + t²) ≤ 2 + γ − log 4π`   and   `Σ_{t ∈ s} 4/t² ≤ 3/8`.

**Proof.**
- The Hadamard product gives `Σ_ρ Re(1/ρ + 1/(1−ρ)) = 2 + γ − log 4π`
  (`xiEndpointCompletedCurvature`).
- Every term is nonnegative, because `0 < Re ρ < 1`.
- A zero `ρ = 1/2 + it` on the line contributes `1/(1/4 + t²)`.
- Every zero has `|Im ρ| > 4.5`, so `4/t² ≤ (4 · 82/81)/(1/4 + t²)`.
- The value `2 + γ − log 4π` is below `0.0924`, from `γ < 0.577216`, `log 2 > 0.693147` and
  `log π > log 3 > 1.098612`.
-/

open Complex

namespace RHTower.WeilExcess

noncomputable section

/-- A real zero of `XiC` is the spectral point of a divisor copy on the critical line. -/
theorem xiZeroCopy_eq_half_add_of_spectral {q : XiZeroCopy} {t : ℝ}
    (h : xiSpectralPoint q = t) : (q.1 : ℂ) = 1 / 2 + t * I := by
  have h1 : ((q.1 : ℂ) - 1 / 2) * (-I) = t := by simpa [xiSpectralPoint] using h
  have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
  have h2 : (q.1 : ℂ) - 1 / 2 = t * I := by
    calc (q.1 : ℂ) - 1 / 2 = ((q.1 : ℂ) - 1 / 2) * ((-I) * I) := by rw [hI, mul_one]
      _ = (((q.1 : ℂ) - 1 / 2) * (-I)) * I := by ring
      _ = t * I := by rw [h1]
  linear_combination h2

/-- The endpoint cross term of a copy on the critical line is `1/(1/4 + t²)`. -/
theorem endpoint_cross_term_re_of_spectral {q : XiZeroCopy} {t : ℝ}
    (h : xiSpectralPoint q = t) :
    (xiRawReciprocalCoordinate q *
      (starRingEnd ℂ) (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv q))).re =
      1 / (1 / 4 + t ^ 2) := by
  have hq := xiZeroCopy_eq_half_add_of_spectral h
  have hre : (q.1 : ℂ).re = 1 / 2 := by rw [hq]; simp
  have him : (q.1 : ℂ).im = t := by rw [hq]; simp
  rw [endpoint_cross_term_re_eq, hre, him]
  have hpos : (0 : ℝ) < 1 / 4 + t ^ 2 := by positivity
  field_simp
  ring

/-- Every real zero of `XiC` has ordinate larger than `4.5` in absolute value. -/
theorem four_half_lt_abs_of_XiC_eq_zero {t : ℝ} (ht : XiC t = 0) : 4.5 < |t| := by
  obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy (t : ℂ)).mp ht
  have h := four_half_lt_abs_im_of_xiZeroCopy q
  rw [xiZeroCopy_eq_half_add_of_spectral hq] at h
  simpa using h

/-- **The Hadamard budget over real zeros.** -/
theorem sum_inv_quarter_add_sq_le (s : Finset ℝ) (hs : ∀ t ∈ s, XiC t = 0) :
    ∑ t ∈ s, 1 / (1 / 4 + t ^ 2) ≤ xiEndpointCompletedCurvature := by
  classical
  rcases s.eq_empty_or_nonempty with h0 | ⟨t₀, ht₀⟩
  · rw [h0, Finset.sum_empty]; exact xiEndpointCompletedCurvature_nonneg
  haveI : Nonempty XiZeroCopy :=
    ⟨((XiC_eq_zero_iff_exists_xiZeroCopy (t₀ : ℂ)).mp (hs t₀ ht₀)).choose⟩
  have hex : ∀ t ∈ s, ∃ q : XiZeroCopy, xiSpectralPoint q = t := fun t ht =>
    (XiC_eq_zero_iff_exists_xiZeroCopy (t : ℂ)).mp (hs t ht)
  choose! q hq using hex
  set c : XiZeroCopy → ℝ := fun p =>
    (xiRawReciprocalCoordinate p *
      (starRingEnd ℂ) (xiRawReciprocalCoordinate (xiZeroCopyLineConjEquiv p))).re with hc
  have hsum : Summable c := Summable.of_norm_bounded summable_xiEndpointCrossTerm.norm
    (fun p => by rw [Real.norm_eq_abs]; exact abs_re_le_norm _)
  have hinj : Set.InjOn q s := by
    intro t₁ h₁ t₂ h₂ he
    have e1 := hq t₁ h₁
    have e2 := hq t₂ h₂
    rw [he] at e1
    exact_mod_cast e1.symm.trans e2
  have hterm : ∀ t ∈ s, 1 / (1 / 4 + t ^ 2) = c (q t) := fun t ht =>
    (endpoint_cross_term_re_of_spectral (hq t ht)).symm
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_image hinj, xiEndpointCompletedCurvature_eq_cross_re,
    Complex.re_tsum summable_xiEndpointCrossTerm]
  exact hsum.sum_le_tsum _ (fun p _ => endpoint_cross_term_re_nonneg p)

/-- `2 + γ − log 4π < 0.0924`. -/
theorem xiEndpointCompletedCurvature_lt : xiEndpointCompletedCurvature < 924 / 10000 := by
  rw [xiEndpointCompletedCurvature_eq_eulerMascheroni_log,
    Real.log_mul (by norm_num) Real.pi_pos.ne', show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have hγ := eulerMascheroniConstant_lt_fiveHundredSeventySevenThousandTwoHundredSixteen_over_oneMillion
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  have hπ : Real.log 3 < Real.log Real.pi :=
    Real.log_lt_log (by norm_num) Real.pi_gt_three
  push_cast
  linarith

/-- **The Fejér budget over real zeros.** For every finite set `s` of real zeros of `XiC`,
`Σ_{t ∈ s} 4/t² ≤ 3/8`. -/
theorem sum_four_div_sq_le (s : Finset ℝ) (hs : ∀ t ∈ s, XiC t = 0) :
    ∑ t ∈ s, 4 / t ^ 2 ≤ 3 / 8 := by
  have hpt : ∀ t ∈ s, 4 / t ^ 2 ≤ (4 * 82 / 81) * (1 / (1 / 4 + t ^ 2)) := by
    intro t ht
    have h45 := four_half_lt_abs_of_XiC_eq_zero (hs t ht)
    have hsq : (81 / 4 : ℝ) ≤ t ^ 2 := by
      have := mul_self_le_mul_self (by norm_num) h45.le
      rw [← sq, ← sq, sq_abs] at this
      linarith
    have ht2 : (0 : ℝ) < t ^ 2 := by linarith
    rw [div_le_iff₀ ht2, mul_one_div, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  calc ∑ t ∈ s, 4 / t ^ 2 ≤ ∑ t ∈ s, (4 * 82 / 81) * (1 / (1 / 4 + t ^ 2)) :=
        Finset.sum_le_sum hpt
    _ = (4 * 82 / 81) * ∑ t ∈ s, 1 / (1 / 4 + t ^ 2) := by rw [Finset.mul_sum]
    _ ≤ (4 * 82 / 81) * xiEndpointCompletedCurvature :=
        mul_le_mul_of_nonneg_left (sum_inv_quarter_add_sq_le s hs) (by norm_num)
    _ ≤ 3 / 8 := by nlinarith [xiEndpointCompletedCurvature_lt]

end

end RHTower.WeilExcess
