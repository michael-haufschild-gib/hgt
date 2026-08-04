import GaloisForLFunctions.RHTower.BandKaiserBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The tail mass of the Kaiser–Bessel trial is bounded by an absolute constant

Beyond the band edge the trial transform is at most `2 min(1, 1/sqrt(omega² - c²))`, and
`omega² - c² >= (|omega| - c)²`, so its square is dominated by the Cauchy envelope

```text
8/(1 + (|omega| - c)²),
```

whose tail integral is `4 pi` — independent of the aperture.  The trial's out-of-band spectral mass is
therefore bounded by an absolute constant while its in-band mass grows like `e^(2c)/c²`, which is the
quantitative content of the leakage envelope.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open MeasureTheory Set intervalIntegral

/-- The elementary envelope inequality: `min(4, 4/t²) <= 8/(1+t²)`. -/
theorem min_four_le_cauchy (t : ℝ) : min 4 (4 / t ^ 2) ≤ 8 / (1 + t ^ 2) := by
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  rcases le_or_gt (t ^ 2) 1 with ht | ht
  · refine le_trans (min_le_left _ _) ?_
    rw [le_div_iff₀ hpos]
    linarith
  · refine le_trans (min_le_right _ _) ?_
    have ht0 : (0 : ℝ) < t ^ 2 := by linarith
    rw [div_le_div_iff₀ ht0 hpos]
    linarith

/-- **The tail envelope of the trial transform.** -/
theorem sq_integral_kaiserTrial_cos_le {c ω : ℝ} (hc : 0 ≤ c) (h : c ^ 2 < ω ^ 2) :
    (∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (ω * x)) ^ 2
      ≤ 8 / (1 + (|ω| - c) ^ 2) := by
  have habs := abs_integral_kaiserTrial_cos_le h
  have hpos : 0 < ω ^ 2 - c ^ 2 := by linarith
  have hupos : 0 < Real.sqrt (ω ^ 2 - c ^ 2) := Real.sqrt_pos.mpr hpos
  have hsq : Real.sqrt (ω ^ 2 - c ^ 2) ^ 2 = ω ^ 2 - c ^ 2 := Real.sq_sqrt hpos.le
  -- the square of the transform is at most `min 4 (4/(omega² - c²))`
  have hsq_le : (∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (ω * x)) ^ 2
      ≤ min 4 (4 / (ω ^ 2 - c ^ 2)) := by
    have h1 : (∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (ω * x)) ^ 2
        = |∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (ω * x)| ^ 2 := (sq_abs _).symm
    rw [h1]
    refine le_min ?_ ?_
    · have h2 := habs.trans (min_le_left _ _)
      nlinarith [abs_nonneg (∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (ω * x))]
    · have h2 := habs.trans (min_le_right _ _)
      have h3 : |∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (ω * x)| ^ 2
          ≤ (2 / Real.sqrt (ω ^ 2 - c ^ 2)) ^ 2 := by
        refine pow_le_pow_left₀ (abs_nonneg _) h2 2
      refine h3.trans ?_
      rw [div_pow, hsq]
      norm_num
  -- and `omega² - c² >= (|omega| - c)²`
  have hge : (|ω| - c) ^ 2 ≤ ω ^ 2 - c ^ 2 := by
    have habsω : |ω| ^ 2 = ω ^ 2 := sq_abs ω
    have hle : c ≤ |ω| := by
      nlinarith [abs_nonneg ω, sq_abs ω]
    nlinarith [hle, hc, habsω]
  refine hsq_le.trans (le_trans ?_ (min_four_le_cauchy (|ω| - c)))
  rcases le_or_gt ((|ω| - c) ^ 2) 0 with hz | hz
  · -- the degenerate case cannot occur beyond the band edge
    have hzz : (|ω| - c) ^ 2 = 0 := le_antisymm hz (sq_nonneg _)
    have hzero : |ω| - c = 0 := by
      exact pow_eq_zero_iff (two_ne_zero) |>.mp hzz
    have habsc : |ω| = c := by linarith
    have hcontra : ω ^ 2 = c ^ 2 := by
      rw [← sq_abs ω, habsc]
    linarith
  · refine min_le_min le_rfl ?_
    gcongr

/-- The tail integral of the Cauchy envelope is `4 pi`, independent of the aperture. -/
theorem integral_Ioi_cauchy_envelope (c : ℝ) :
    (∫ ω in Ioi c, 8 / (1 + (ω - c) ^ 2)) = 4 * Real.pi := by
  have hderiv : ∀ ω ∈ Ioi c,
      HasDerivAt (fun t : ℝ => 8 * Real.arctan (t - c)) (8 / (1 + (ω - c) ^ 2)) ω := by
    intro ω _
    have hshift : HasDerivAt (fun t : ℝ => t - c) 1 ω := (hasDerivAt_id ω).sub_const c
    have harctan : HasDerivAt Real.arctan (1 / (1 + (ω - c) ^ 2)) (ω - c) := by
      have h := Real.hasDerivAt_arctan (ω - c)
      refine h.congr_deriv ?_
      rw [one_div]
    have hcomp := (harctan.comp ω hshift).const_mul (8 : ℝ)
    refine hcomp.congr_deriv ?_
    rw [mul_one]
    ring
  have hcont : ContinuousWithinAt (fun t : ℝ => 8 * Real.arctan (t - c)) (Ici c) c :=
    ((Real.continuous_arctan.comp (continuous_id.sub continuous_const)).continuousAt.const_mul
      (8 : ℝ)).continuousWithinAt
  have hnonneg : ∀ ω ∈ Ioi c, 0 ≤ 8 / (1 + (ω - c) ^ 2) := by
    intro ω _
    positivity
  have hlim : Filter.Tendsto (fun t : ℝ => 8 * Real.arctan (t - c)) Filter.atTop
      (nhds (8 * (Real.pi / 2))) := by
    have hshift : Filter.Tendsto (fun t : ℝ => t - c) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ (-c) Filter.tendsto_id
    have harc : Filter.Tendsto Real.arctan Filter.atTop (nhds (Real.pi / 2)) :=
      Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds
    exact (harc.comp hshift).const_mul (8 : ℝ)
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnonneg hlim
  rw [h]
  have harc : Real.arctan (c - c) = 0 := by
    rw [sub_self, Real.arctan_zero]
  rw [harc]
  ring

end GaloisForLFunctions.RHTower

end
