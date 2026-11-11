import GaloisForLFunctions.RHTower.FourierPlancherelIntegral
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
# A diagonal atom forces pair density above one

Write a total pair measure as `A δ₀ + (1-g) dx`. Its prescribed Fourier data
on `[-1,1]` say that `ĝ(α) = A - |α|`. Parseval forces an explicit amount of
negative-part energy in `g` when `A ≥ 13/10`. Thus a deficit between zero and
one cannot provide a seventy-percent obstruction; density above one is necessary.
-/

open MeasureTheory Set FourierTransform

noncomputable section
namespace GaloisForLFunctions.TransThresholdPairCorrelation

/-- Quadratic and linear mass of the part of the pair density above one. -/
def pairDensityExcess (g : ℝ → ℝ) : ℝ :=
  ∫ x : ℝ, max (-g x) 0 ^ 2 + max (-g x) 0

private theorem integral_linear_band_sq (A : ℝ) :
    (∫ x in (-1 : ℝ)..1, (A - |x|) ^ 2) = 2*A^2 - 2*A + 2/3 := by
  have hc : Continuous fun x : ℝ => (A - |x|)^2 := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (-1) 0) (hc.intervalIntegrable 0 1)]
  have hn : (∫ x in (-1 : ℝ)..0, (A - |x|)^2) =
      ∫ x in (-1 : ℝ)..0, A^2 + (2*A)*x + x^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 0)] at hx
    dsimp only
    rw [abs_of_nonpos hx.2]
    ring
  have hp : (∫ x in (0 : ℝ)..1, (A - |x|)^2) =
      ∫ x in (0 : ℝ)..1, A^2 - (2*A)*x + x^2 := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
    dsimp only
    rw [abs_of_nonneg hx.1]
    ring
  rw [hn, hp]
  have hi {a b : ℝ} : IntervalIntegrable (fun x : ℝ => (2*A)*x) volume a b :=
    (by fun_prop : Continuous fun x : ℝ => (2*A)*x).intervalIntegrable a b
  have hn' {a b : ℝ} : IntervalIntegrable (fun x : ℝ => A^2 + (2*A)*x) volume a b :=
    intervalIntegrable_const.add hi
  have hp' {a b : ℝ} : IntervalIntegrable (fun x : ℝ => A^2 - (2*A)*x) volume a b :=
    intervalIntegrable_const.sub hi
  rw [intervalIntegral.integral_add hn' ((continuous_pow 2).intervalIntegrable _ _),
    intervalIntegral.integral_add hp' ((continuous_pow 2).intervalIntegrable _ _),
    intervalIntegral.integral_add intervalIntegrable_const hi,
    intervalIntegral.integral_sub intervalIntegrable_const hi]
  rw [intervalIntegral.integral_const_mul (2*A) (fun x : ℝ => x),
    intervalIntegral.integral_const_mul (2*A) (fun x : ℝ => x)]
  simp only [intervalIntegral.integral_const,
    integral_id, integral_pow, smul_eq_mul]
  norm_num
  ring

private theorem mass_of_fourier_band {g : ℝ → ℝ} {A : ℝ}
    (hband : ∀ α ∈ Icc (-1 : ℝ) 1,
      𝓕 (fun x => (g x : ℂ)) α = ((A - |α| : ℝ) : ℂ)) :
    (∫ x, g x) = A := by
  have h := hband 0 (by norm_num)
  rw [Real.fourier_real_eq_integral_exp_smul] at h
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero,
    one_smul, abs_zero, sub_zero] at h
  rw [integral_complex_ofReal] at h
  exact Complex.ofReal_inj.mp h

/-- Exact low-frequency data impose a quadratic lower bound on total deficit energy. -/
theorem deficit_energy_ge_of_fourier_band {g : ℝ → ℝ} {A : ℝ}
    (hg : Integrable g) (hg2 : Integrable fun x => g x ^ 2)
    (hband : ∀ α ∈ Icc (-1 : ℝ) 1,
      𝓕 (fun x => (g x : ℂ)) α = ((A - |α| : ℝ) : ℂ)) :
    2*A^2 - 2*A + 2/3 ≤ ∫ x, g x ^ 2 := by
  have hgc : Integrable (fun x => (g x : ℂ)) := hg.ofReal
  have hgc2 : MemLp (fun x => (g x : ℂ)) 2 := by
    rw [memLp_two_iff_integrable_sq_norm hgc.aestronglyMeasurable]
    simpa only [Complex.norm_real, Real.norm_eq_abs, sq_abs] using hg2
  have hF := GaloisForLFunctions.RHTower.integrable_norm_sq_fourier hgc hgc2
  have hP := GaloisForLFunctions.RHTower.integral_norm_sq_fourier_eq hgc hgc2
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at hP
  have hlow : (∫ α in Icc (-1 : ℝ) 1,
      ‖𝓕 (fun x => (g x : ℂ)) α‖^2) = 2*A^2 - 2*A + 2/3 := by
    rw [setIntegral_congr_fun measurableSet_Icc (fun α hα => by
      rw [hband α hα, Complex.norm_real, Real.norm_eq_abs, sq_abs])]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
    exact integral_linear_band_sq A
  rw [← hP, ← hlow]
  exact setIntegral_le_integral hF (Filter.Eventually.of_forall fun α => sq_nonneg _)

private theorem integrable_negative_part {g : ℝ → ℝ} (hg : Integrable g) :
    Integrable fun x => max (-g x) 0 :=
  hg.neg.sup (integrable_zero _ _ _)

private theorem integrable_negative_part_sq {g : ℝ → ℝ} (hg : Integrable g)
    (hg2 : Integrable fun x => g x ^ 2) :
    Integrable fun x => max (-g x) 0 ^ 2 := by
  refine hg2.mono' ((integrable_negative_part hg).aestronglyMeasurable.pow 2) ?_
  filter_upwards with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  rcases le_total (g x) 0 with hx | hx
  · rw [max_eq_left (neg_nonneg.mpr hx), neg_sq]
  · rw [max_eq_right (neg_nonpos.mpr hx), zero_pow (by decide)]
    exact sq_nonneg _

/-- Pair-density positivity forces negative-deficit energy to pay the Parseval gap. -/
theorem pairDensityExcess_ge_of_fourier_band {g : ℝ → ℝ} {A : ℝ}
    (hg : Integrable g) (hg2 : Integrable fun x => g x ^ 2)
    (hle : ∀ᵐ x, g x ≤ 1)
    (hband : ∀ α ∈ Icc (-1 : ℝ) 1,
      𝓕 (fun x => (g x : ℂ)) α = ((A - |α| : ℝ) : ℂ)) :
    2*A^2 - 3*A + 2/3 ≤ pairDensityExcess g := by
  have hpoint : (fun x => g x ^ 2 - g x) ≤ᵐ[volume]
      (fun x => max (-g x) 0 ^ 2 + max (-g x) 0) := by
    filter_upwards [hle] with x hx
    rcases le_total (g x) 0 with hn | hp
    · rw [max_eq_left (neg_nonneg.mpr hn), neg_sq]
      linarith
    · rw [max_eq_right (neg_nonpos.mpr hp)]
      nlinarith only [mul_nonneg hp (sub_nonneg.mpr hx)]
  have hi := integral_mono_ae (hg2.sub hg)
    ((integrable_negative_part_sq hg hg2).add (integrable_negative_part hg)) hpoint
  simp only [Pi.sub_apply, Pi.add_apply] at hi
  rw [integral_sub hg2 hg, mass_of_fourier_band hband] at hi
  have hP := deficit_energy_ge_of_fourier_band hg hg2 hband
  dsimp only [pairDensityExcess]
  linarith only [hi, hP]

/-- At diagonal mass at least `13/10`, the required excess energy is at least `11/75`. -/
theorem pairDensityExcess_ge_eleven_seventy_fifths {g : ℝ → ℝ} {A : ℝ}
    (hg : Integrable g) (hg2 : Integrable fun x => g x ^ 2)
    (hle : ∀ᵐ x, g x ≤ 1) (hA : 13/10 ≤ A)
    (hband : ∀ α ∈ Icc (-1 : ℝ) 1,
      𝓕 (fun x => (g x : ℂ)) α = ((A - |α| : ℝ) : ℂ)) :
    11/75 ≤ pairDensityExcess g := by
  have h := pairDensityExcess_ge_of_fourier_band hg hg2 hle hband
  nlinarith only [h, hA, sq_nonneg (A-13/10)]

/-- A deficit in `[0,1]` has the explicit mass ceiling imposed by Parseval. -/
theorem diagonalMass_le_of_nonnegative_deficit {g : ℝ → ℝ} {A : ℝ}
    (hg : Integrable g) (hbounds : ∀ᵐ x, 0 ≤ g x ∧ g x ≤ 1)
    (hband : ∀ α ∈ Icc (-1 : ℝ) 1,
      𝓕 (fun x => (g x : ℂ)) α = ((A - |α| : ℝ) : ℂ)) :
    A ≤ (3 + Real.sqrt (11/3)) / 4 := by
  have hg2 : Integrable fun x => g x ^ 2 := by
    refine hg.mono' (hg.aestronglyMeasurable.pow 2) ?_
    filter_upwards [hbounds] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith only [mul_nonneg hx.1 (sub_nonneg.mpr hx.2)]
  have hz : pairDensityExcess g = 0 := by
    unfold pairDensityExcess
    apply integral_eq_zero_of_ae
    filter_upwards [hbounds] with x hx
    rw [max_eq_right (neg_nonpos.mpr hx.1)]
    norm_num
  have h := pairDensityExcess_ge_of_fourier_band hg hg2
    (hbounds.mono fun _ hx => hx.2) hband
  rw [hz] at h
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 11/3)
  have hs0 := Real.sqrt_nonneg (11/3 : ℝ)
  by_contra hn
  have hA : (3 + Real.sqrt (11/3))/4 < A := lt_of_not_ge hn
  have hp := mul_pos
    (show 0 < 4*A-3-Real.sqrt (11/3) by linarith only [hA])
    (show 0 < 4*A-3+Real.sqrt (11/3) by linarith only [hA, hs0])
  nlinarith only [h, hs, hp]

/-- No nonnegative deficit with exact low-frequency data reaches diagonal mass `13/10`. -/
theorem no_nonnegative_deficit_at_seventy_percent :
    ¬ ∃ (g : ℝ → ℝ) (A : ℝ), Integrable g ∧
      (∀ᵐ x, 0 ≤ g x ∧ g x ≤ 1) ∧ 13/10 ≤ A ∧
      (∀ α ∈ Icc (-1 : ℝ) 1,
        𝓕 (fun x => (g x : ℂ)) α = ((A - |α| : ℝ) : ℂ)) := by
  rintro ⟨g, A, hg, hbounds, hA, hband⟩
  have h := diagonalMass_le_of_nonnegative_deficit hg hbounds hband
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 11/3)
  nlinarith only [h, hA, hs, Real.sqrt_nonneg (11/3 : ℝ)]

end GaloisForLFunctions.TransThresholdPairCorrelation
