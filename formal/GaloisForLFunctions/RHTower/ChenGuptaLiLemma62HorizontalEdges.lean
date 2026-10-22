import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62HorizontalDecay
import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62ContourIntegrability

/-!
# Chen--Gupta--Li Lemma 6.2: nonprincipal horizontal contour edges

The first-shift kernel has uniform fifth-order decay throughout
`-1 ≤ Re(s) ≤ 2`; the induced nonprincipal character has a cubic strip
envelope.  Their product is uniformly `O(|Im(s)|⁻²)` along the finite
horizontal edge, so both edge integrals vanish.  All constants and strip
memberships are constructed internally.
-/

open Complex MeasureTheory Filter Set Asymptotics
open scoped Topology

namespace RHTower

noncomputable section

/-- The closed cubic strip constant selected from the induced-character
envelope.  Its positivity and bounding property are discharged internally by
the two horizontal-tail theorems below. -/
noncomputable def cglLemma62InducedLStripBudget (B : CGLLemma62InducedCharacter) : ℝ :=
  Classical.choose (cglLemma62_exists_bound_inducedLFunction_strip B)

private theorem cglLemma62InducedLStripBudget_pos (B : CGLLemma62InducedCharacter) :
    0 < cglLemma62InducedLStripBudget B :=
  (Classical.choose_spec (cglLemma62_exists_bound_inducedLFunction_strip B)).1

private theorem cglLemma62InducedLStripBudget_bound (B : CGLLemma62InducedCharacter) (v x : ℝ)
    (hxlo : -1 ≤ x) (hxhi : x ≤ 2) :
    ‖DirichletCharacter.LFunction B.character ((x : ℂ) + (v : ℂ) * I)‖ ≤
      cglLemma62InducedLStripBudget B * (2 + |v|) ^ 3 :=
  (Classical.choose_spec (cglLemma62_exists_bound_inducedLFunction_strip B)).2 v x hxlo hxhi


private theorem cglLemma62_nonprincipalHorizontal_point_bound
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t y x : ℝ)
    (hxlo : -1 ≤ x) (hxhi : x ≤ 2) (hy : 1 ≤ |y|) :
    ‖cglLemma62ContourIntegrand w N B t ((x : ℂ) + (y : ℂ) * I)‖ ≤
      (8 * (N.value : ℝ) ^ (2 : ℝ) * cglLemma62InducedLStripBudget B * (2 + |t|) ^ 3 *
        cglLemma62MellinFirstShiftQuinticBudget w) / |y| ^ 2 := by
  have hNpos : (0 : ℝ) < N.value := by exact_mod_cast N.positive
  have hNone : 1 ≤ (N.value : ℝ) := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt N.positive))
  have hypos : 0 < |y| := lt_of_lt_of_le zero_lt_one hy
  have hQ : 0 ≤ cglLemma62MellinFirstShiftQuinticBudget w := by
    dsimp [cglLemma62MellinFirstShiftQuinticBudget]
    apply integral_nonneg
    intro u
    dsimp [deningerMeyerQuinticStripMajorant]
    positivity
  have hE : 0 ≤ cglLemma62InducedLStripBudget B := (cglLemma62InducedLStripBudget_pos B).le
  have hT : 0 ≤ (2 + |t|) ^ 3 := by positivity
  have hNtwo : 0 ≤ (N.value : ℝ) ^ (2 : ℝ) := by positivity
  let sigma : CGLLemma62FirstShiftAbscissa := ⟨x, hxlo, hxhi⟩
  have hkernel0 := cglLemma62_mellinTransform_firstShift_uniformQuinticDecay w sigma y
  have hkernel : ‖cglLemma62MellinTransform w ((x : ℂ) + (y : ℂ) * I)‖ ≤
      cglLemma62MellinFirstShiftQuinticBudget w / |y| ^ 5 := by
    apply (le_div_iff₀ (pow_pos hypos 5)).mpr
    simpa [sigma, mul_comm] using hkernel0
  have hL0 := cglLemma62InducedLStripBudget_bound B (y - t) x hxlo hxhi
  have hL : ‖DirichletCharacter.LFunction B.character
      (((x : ℂ) + (y : ℂ) * I) - (t : ℂ) * I)‖ ≤
      cglLemma62InducedLStripBudget B * (2 + |t|) ^ 3 * (1 + |y|) ^ 3 := by
    have harg : ((x : ℂ) + ((y - t : ℝ) : ℂ) * I) =
        ((x : ℂ) + (y : ℂ) * I) - (t : ℂ) * I := by
      push_cast
      ring
    rw [harg] at hL0
    calc
      _ ≤ cglLemma62InducedLStripBudget B * (2 + |y - t|) ^ 3 := hL0
      _ ≤ cglLemma62InducedLStripBudget B * ((2 + |t|) ^ 3 * (1 + |y|) ^ 3) :=
        mul_le_mul_of_nonneg_left (cglLemma62_shifted_cubic_le t y) hE
      _ = _ := by ring
  have hNpow : (N.value : ℝ) ^ x ≤ (N.value : ℝ) ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hNone hxhi
  have hcube : (1 + |y|) ^ 3 ≤ 8 * |y| ^ 3 := by
    have hbase : 1 + |y| ≤ 2 * |y| := by linarith
    calc
      (1 + |y|) ^ 3 ≤ (2 * |y|) ^ 3 := pow_le_pow_left₀ (by positivity) hbase 3
      _ = 8 * |y| ^ 3 := by ring
  unfold cglLemma62ContourIntegrand
  have hNcast : (N.value : ℂ) = ((N.value : ℝ) : ℂ) := by norm_cast
  rw [norm_mul, norm_mul, hNcast,
    Complex.norm_cpow_eq_rpow_re_of_pos hNpos]
  have hre : ((x : ℂ) + (y : ℂ) * I).re = x := by simp
  rw [hre]
  calc
    ‖cglLemma62MellinTransform w (↑x + ↑y * I)‖ * (N.value : ℝ) ^ x *
        ‖DirichletCharacter.LFunction B.character (↑x + ↑y * I - ↑t * I)‖ ≤
      (cglLemma62MellinFirstShiftQuinticBudget w / |y| ^ 5) *
        (N.value : ℝ) ^ x *
        ‖DirichletCharacter.LFunction B.character (↑x + ↑y * I - ↑t * I)‖ := by
          gcongr
    _ ≤ (cglLemma62MellinFirstShiftQuinticBudget w / |y| ^ 5) *
        (N.value : ℝ) ^ (2 : ℝ) *
        ‖DirichletCharacter.LFunction B.character (↑x + ↑y * I - ↑t * I)‖ := by
          gcongr
    _ ≤ (cglLemma62MellinFirstShiftQuinticBudget w / |y| ^ 5) *
        (N.value : ℝ) ^ (2 : ℝ) *
        (cglLemma62InducedLStripBudget B * (2 + |t|) ^ 3 * (1 + |y|) ^ 3) := by
          gcongr
    _ ≤ (cglLemma62MellinFirstShiftQuinticBudget w / |y| ^ 5) *
        (N.value : ℝ) ^ (2 : ℝ) *
        (cglLemma62InducedLStripBudget B * (2 + |t|) ^ 3 * (8 * |y| ^ 3)) := by
          gcongr
    _ = (8 * (N.value : ℝ) ^ (2 : ℝ) * cglLemma62InducedLStripBudget B * (2 + |t|) ^ 3 *
        cglLemma62MellinFirstShiftQuinticBudget w) / |y| ^ 2 := by
          field_simp [ne_of_gt hypos]

/-- The upper horizontal side of CGL's nonprincipal first-shift rectangle
vanishes without a caller-supplied growth or decay premise. -/
theorem cglLemma62_nonprincipalContourIntegrand_horizontal_top
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) :
    Tendsto (fun y : ℝ =>
      ∫ x in (-1 : ℝ)..2,
        cglLemma62ContourIntegrand w N B t ((x : ℂ) + (y : ℂ) * I))
      atTop (𝓝 0) := by
  let C : ℝ := 8 * (N.value : ℝ) ^ (2 : ℝ) * cglLemma62InducedLStripBudget B * (2 + |t|) ^ 3 *
    cglLemma62MellinFirstShiftQuinticBudget w
  have hdecay : Tendsto (fun y : ℝ => C / y ^ 2) atTop (𝓝 0) := by
    have hpow : Tendsto (fun y : ℝ => y ^ (-(2 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have hscaled : Tendsto (fun y : ℝ => C * y ^ (-(2 : ℝ))) atTop (𝓝 0) := by
      simpa using hpow.const_mul C
    refine Filter.Tendsto.congr' ?_ hscaled
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    rw [Real.rpow_neg hy, Real.rpow_two, div_eq_mul_inv]
  apply GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
    (M := fun y : ℝ => C / y ^ 2) (hgt := fun y : ℝ => y)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy x hx
    have hx' : x ∈ Icc (-1 : ℝ) 2 := by
      simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] using (uIoc_subset_uIcc hx)
    have hpoint := cglLemma62_nonprincipalHorizontal_point_bound w N B t y x hx'.1 hx'.2
      (by simpa [abs_of_nonneg (by linarith : 0 ≤ y)] using hy)
    simpa [C, abs_of_nonneg (by linarith : 0 ≤ y)] using hpoint
  · exact hdecay

/-- The lower horizontal side of CGL's nonprincipal first-shift rectangle
vanishes without a caller-supplied growth or decay premise. -/
theorem cglLemma62_nonprincipalContourIntegrand_horizontal_bottom
    (w : CGLRealSmoothBump) (N : CGLPositiveLength)
    (B : CGLLemma62InducedCharacter) (t : ℝ) :
    Tendsto (fun y : ℝ =>
      ∫ x in (-1 : ℝ)..2,
        cglLemma62ContourIntegrand w N B t ((x : ℂ) + (y : ℂ) * I))
      atBot (𝓝 0) := by
  let C : ℝ := 8 * (N.value : ℝ) ^ (2 : ℝ) * cglLemma62InducedLStripBudget B * (2 + |t|) ^ 3 *
    cglLemma62MellinFirstShiftQuinticBudget w
  have hdecay : Tendsto (fun y : ℝ => C / y ^ 2) atTop (𝓝 0) := by
    have hpow : Tendsto (fun y : ℝ => y ^ (-(2 : ℝ))) atTop (𝓝 0) :=
      tendsto_rpow_neg_atTop (by norm_num)
    have hscaled : Tendsto (fun y : ℝ => C * y ^ (-(2 : ℝ))) atTop (𝓝 0) := by
      simpa using hpow.const_mul C
    refine Filter.Tendsto.congr' ?_ hscaled
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    rw [Real.rpow_neg hy, Real.rpow_two, div_eq_mul_inv]
  have hneg : Tendsto (fun y : ℝ =>
      ∫ x in (-1 : ℝ)..2,
        cglLemma62ContourIntegrand w N B t ((x : ℂ) + ((-y : ℝ) : ℂ) * I))
      atTop (𝓝 0) := by
    apply GaloisForLFunctions.HTGeometry.tendsto_intervalIntegral_of_tendsto_bound
      (M := fun y : ℝ => C / y ^ 2) (hgt := fun y : ℝ => -y)
    · filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy x hx
      have hx' : x ∈ Icc (-1 : ℝ) 2 := by
        simpa [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2)] using (uIoc_subset_uIcc hx)
      have hpoint := cglLemma62_nonprincipalHorizontal_point_bound w N B t (-y) x hx'.1 hx'.2
        (by rw [abs_neg, abs_of_nonneg (by linarith : 0 ≤ y)]; exact hy)
      simpa [C, abs_neg, abs_of_nonneg (by linarith : 0 ≤ y)] using hpoint
    · exact hdecay
  refine Filter.Tendsto.congr' ?_ (hneg.comp tendsto_neg_atBot_atTop)
  filter_upwards with y
  apply intervalIntegral.integral_congr_ae
  filter_upwards [] with x
  intro _
  congr 1
  push_cast
  ring

end

end RHTower
