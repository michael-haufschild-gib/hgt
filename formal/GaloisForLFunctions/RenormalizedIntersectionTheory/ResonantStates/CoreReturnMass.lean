import GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates.AutomorphicHeckeReturn
import GaloisForLFunctions.RHTower.EisensteinResonantStateNorm

/-!
# A fixed core region with a single dyadic return

On `|x|≤1/4`, `7/4≤y≤15/8`, only the central return disk contributes.
Its modulus therefore cannot be reduced by interference between return phases.
-/

open Complex MeasureTheory Set UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry RHTower

namespace GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates

noncomputable section

/-- A fixed rectangle in the interior of the modular fundamental domain. -/
def coreRectangle : Set ℍ := {z | |z.re| ≤ 1 / 4 ∧ 7 / 4 ≤ z.im ∧ z.im ≤ 15 / 8}

theorem coreRectangle_subset_fd : coreRectangle ⊆ fd := by
  intro z hz
  have hx := abs_le.mp hz.1
  refine ⟨?_, by change |z.re| ≤ 1 / 2; linarith [hz.1]⟩
  rw [Complex.normSq_apply]
  change 1 ≤ z.re * z.re + z.im * z.im
  nlinarith [hz.2.1, sq_nonneg z.re]

/-- Exactly the central disk returns on the core rectangle. -/
theorem coreRectangle_returns {z : ℍ} (hz : z ∈ coreRectangle) :
    1 < returnHeight 0 z ∧ returnHeight 1 z ≤ 1 ∧ returnHeight (-1) z ≤ 1 := by
  have hx := abs_le.mp hz.1
  have hylo := hz.2.1
  have hyhi := hz.2.2
  have hx2 : z.re ^ 2 ≤ 1 / 16 := by nlinarith
  have hy2 : (z.im - 1) ^ 2 ≤ 49 / 64 := by nlinarith
  have hy2lo : 9 / 16 ≤ (z.im - 1) ^ 2 := by nlinarith
  refine ⟨(returnHeight_gt_one_iff 0 z).mpr ?_, ?_, ?_⟩
  · norm_num only [Int.cast_zero, add_zero]
    linarith
  · apply le_of_not_gt
    rw [returnHeight_gt_one_iff]
    norm_num only [Int.cast_one]
    nlinarith
  · apply le_of_not_gt
    rw [returnHeight_gt_one_iff]
    norm_num only [Int.cast_neg, Int.cast_one]
    nlinarith

/-- Difference between coordinate and automorphic Hecke truncation at height one. -/
def dyadicReturnDefect (u : ℂ) (z : ℍ) : ℂ :=
  heckeTruncated 2 u 1 z - dyadicHecke (automorphicTruncation u 1) z

theorem dyadicReturnDefect_on_core {u : ℂ} (hAu : msA u = 0)
    {z : ℍ} (hz : z ∈ coreRectangle) :
    dyadicReturnDefect u z = (((Real.sqrt 2)⁻¹ : ℝ) : ℂ) * msB u *
      (returnHeight 0 z : ℂ) ^ (1 / 2 - u) := by
  obtain ⟨h0, h1, hm⟩ := coreRectangle_returns hz
  rw [dyadicReturnDefect, resonant_automorphic_dyadic_correction hAu
    (coreRectangle_subset_fd hz), if_pos h0, if_neg (not_lt.mpr h1),
    if_neg (not_lt.mpr hm)]
  ring

theorem dyadicReturnDefect_norm_sq_on_core {u : ℂ} (hAu : msA u = 0)
    {z : ℍ} (hz : z ∈ coreRectangle) :
    ‖dyadicReturnDefect u z‖ ^ 2 = ‖msB u‖ ^ 2 / 2 *
      ((returnHeight 0 z) ^ (1 / 2 - u.re)) ^ 2 := by
  have h0 := (coreRectangle_returns hz).1
  have hn : ‖(((Real.sqrt 2)⁻¹ : ℝ) : ℂ)‖ ^ 2 = 1 / 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  have hre : (1 / 2 - u : ℂ).re = 1 / 2 - u.re := by simp
  rw [dyadicReturnDefect_on_core hAu hz]
  simp only [norm_mul, mul_pow, hn,
    Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans h0), hre]
  ring

/-- The local return has a fixed positive squared modulus, independent of frequency. -/
theorem dyadicReturnDefect_norm_sq_lower {u : ℂ} (hur : u.re < 0)
    (hAu : msA u = 0) {z : ℍ} (hz : z ∈ coreRectangle) :
    ‖msB u‖ ^ 2 / 2 ≤ ‖dyadicReturnDefect u z‖ ^ 2 := by
  have h0 := (coreRectangle_returns hz).1
  rw [dyadicReturnDefect_norm_sq_on_core hAu hz]
  have hp : 1 ≤ (returnHeight 0 z) ^ (1 / 2 - u.re) :=
    Real.one_le_rpow h0.le (by linarith)
  have hps : 1 ≤ ((returnHeight 0 z) ^ (1 / 2 - u.re)) ^ 2 := by
    nlinarith only [hp]
  nlinarith only [mul_nonneg (sq_nonneg ‖msB u‖) (sub_nonneg.mpr hps)]

private def coreRect : Set (ℝ × ℝ) :=
  Icc (-(1 / 4)) (1 / 4) ×ˢ Icc (7 / 4) (15 / 8)

private theorem coreRect_pos {p : ℝ × ℝ} (hp : p ∈ coreRect) : 0 < p.2 := by
  have := hp.2.1
  linarith

private theorem coreRectangle_eq_coord :
    coreRectangle = {z : ℍ | (z.re, z.im) ∈ coreRect} := by
  ext z
  simp only [coreRectangle, coreRect, mem_setOf_eq, mem_prod, mem_Icc, abs_le, and_assoc]

private def coreDensity (u : ℂ) (p : ℝ × ℝ) : ℝ :=
  ‖msB u‖ ^ 2 / 2 * ((2 * p.2 / (p.1 ^ 2 + p.2 ^ 2)) ^ (1 / 2 - u.re)) ^ 2 /
    p.2 ^ 2

private theorem coreDensity_eq {u : ℂ} (hAu : msA u = 0) {p : ℝ × ℝ}
    (hp : p ∈ coreRect) :
    coreDensity u p = ‖dyadicReturnDefect u (ofComplex ⟨p.1, p.2⟩)‖ ^ 2 / p.2 ^ 2 := by
  let z : ℍ := ⟨⟨p.1, p.2⟩, coreRect_pos hp⟩
  have he : ofComplex (⟨p.1, p.2⟩ : ℂ) = z := by
    rw [ofComplex_apply_of_im_pos (coreRect_pos hp)]
  have hz : z ∈ coreRectangle := ⟨abs_le.mpr hp.1, hp.2⟩
  rw [he, dyadicReturnDefect_norm_sq_on_core hAu hz]
  simp [coreDensity, returnHeight, z]

private theorem coreDensity_lower {u : ℂ} (hur : u.re < 0) (hAu : msA u = 0)
    {p : ℝ × ℝ} (hp : p ∈ coreRect) : ‖msB u‖ ^ 2 / 8 ≤ coreDensity u p := by
  let z : ℍ := ⟨⟨p.1, p.2⟩, coreRect_pos hp⟩
  have he : ofComplex (⟨p.1, p.2⟩ : ℂ) = z := by
    rw [ofComplex_apply_of_im_pos (coreRect_pos hp)]
  have hz : z ∈ coreRectangle := ⟨abs_le.mpr hp.1, hp.2⟩
  rw [coreDensity_eq hAu hp, he, le_div_iff₀ (sq_pos_of_pos (coreRect_pos hp))]
  have hy2 : p.2 ^ 2 ≤ 4 := by
    have hlo := hp.2.1
    have hhi := hp.2.2
    nlinarith only [hlo, hhi]
  have hlow := dyadicReturnDefect_norm_sq_lower hur hAu hz
  nlinarith only [hlow, mul_nonneg (sq_nonneg ‖msB u‖) (sub_nonneg.mpr hy2)]

private theorem coreDensity_continuousOn (u : ℂ) : ContinuousOn (coreDensity u) coreRect := by
  have hd (p : ℝ × ℝ) (hp : p ∈ coreRect) : 0 < p.1 ^ 2 + p.2 ^ 2 :=
    add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_pos (coreRect_pos hp))
  have hb : ContinuousOn (fun p : ℝ × ℝ => 2 * p.2 / (p.1 ^ 2 + p.2 ^ 2)) coreRect :=
    (continuous_const.mul continuous_snd).continuousOn.div
      ((continuous_fst.pow 2).add (continuous_snd.pow 2)).continuousOn
      (fun p hp => (hd p hp).ne')
  have hr := hb.rpow_const (p := 1 / 2 - u.re) (fun p hp =>
    Or.inl (div_pos (mul_pos (by norm_num) (coreRect_pos hp)) (hd p hp)).ne')
  exact (continuousOn_const.mul (hr.pow 2)).div (continuous_snd.pow 2).continuousOn
    (fun p hp => (sq_pos_of_pos (coreRect_pos hp)).ne')

/-- A frequency-independent amount of the return correction lies in a fixed compact core. -/
theorem dyadicReturnDefect_core_mass_lower {u : ℂ} (hur : u.re < 0) (hAu : msA u = 0) :
    ‖msB u‖ ^ 2 / 128 ≤ ∫ z in coreRectangle, ‖dyadicReturnDefect u z‖ ^ 2 := by
  have hA : MeasurableSet coreRect := measurableSet_Icc.prod measurableSet_Icc
  have hK : IsCompact coreRect := isCompact_Icc.prod isCompact_Icc
  let F : ℝ × ℝ → ℝ := fun p => ‖dyadicReturnDefect u (ofComplex ⟨p.1, p.2⟩)‖ ^ 2
  have hF : (fun z : ℍ => F (z.re, z.im)) = fun z => ‖dyadicReturnDefect u z‖ ^ 2 := by
    funext z
    have he : (⟨z.re, z.im⟩ : ℂ) = (z : ℂ) := Complex.ext rfl rfl
    simp only [F, he, ofComplex_apply]
  rw [← hF, coreRectangle_eq_coord, setIntegral_coord_eq_real hA (fun p hp => coreRect_pos hp)]
  have heq : (∫ p in coreRect, F p / p.2 ^ 2) = ∫ p in coreRect, coreDensity u p :=
    setIntegral_congr_fun hA (fun p hp => (coreDensity_eq hAu hp).symm)
  rw [heq]
  have hm := setIntegral_mono_on
    (ContinuousOn.integrableOn_compact (μ := volume) hK
      (f := fun _ => ‖msB u‖ ^ 2 / 8) continuousOn_const)
    (ContinuousOn.integrableOn_compact (μ := volume) hK (coreDensity_continuousOn u)) hA
    (fun p hp => coreDensity_lower hur hAu hp)
  have hv : (volume : Measure (ℝ × ℝ)).real coreRect = 1 / 16 := by
    change ((volume : Measure (ℝ × ℝ))
      (Icc (-(1 / 4 : ℝ)) (1 / 4) ×ˢ Icc (7 / 4 : ℝ) (15 / 8))).toReal = 1 / 16
    rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Icc, Real.volume_Icc]
    norm_num
  simpa only [setIntegral_const, hv, smul_eq_mul, show (1 / 16 : ℝ) *
    (‖msB u‖ ^ 2 / 8) = ‖msB u‖ ^ 2 / 128 by ring] using hm

/-- Relative core mass cannot vanish with frequency while the real parameter stays negative. -/
theorem dyadicReturnDefect_relative_mass_lower {u : ℂ}
    (hu : u ∈ eisensteinLineDomain) (hur : u.re < 0) (hAu : msA u = 0) :
    (-2 * u.re) / 128 * (∫ z in fd, ‖truncatedLineModel u 1 z‖ ^ 2) ≤
      ∫ z in coreRectangle, ‖dyadicReturnDefect u z‖ ^ 2 := by
  have he : (-2 * u.re) / 128 * (∫ z in fd, ‖truncatedLineModel u 1 z‖ ^ 2) =
      ‖msB u‖ ^ 2 / 128 := by
    rw [integral_norm_sq_of_msA_eq_zero hu hur hAu (by norm_num)]
    simp only [Real.one_rpow, mul_one]
    have hne : u.re ≠ 0 := hur.ne
    field_simp
  rw [he]
  exact dyadicReturnDefect_core_mass_lower hur hAu

end

end GaloisForLFunctions.RenormalizedIntersectionTheory.ResonantStates
