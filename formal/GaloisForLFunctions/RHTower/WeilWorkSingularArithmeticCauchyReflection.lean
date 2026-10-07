import GaloisForLFunctions.HTGeometry.VerticalStripResidueShift

/-!
# A reflected Cauchy pairing on the critical strip

The real part of a right-line Cauchy integral is half its residue when the
left-line numerator is its complex conjugate. This supplies the boundary
evaluation used to pair a Weil source's regularized Herglotz kernel.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry
open scoped ComplexConjugate

noncomputable section

namespace RHTower.WeilSingularArithmetic

/-- Reflection makes the Cauchy pairing a real boundary evaluation. -/
theorem re_integral_reflected_cauchy {f : ℂ → ℂ} {C : ℝ}
    (hf : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 → DifferentiableAt ℂ f s)
    (hsym : ∀ t : ℝ, f ((1 / 4 : ℂ) + t * I) =
      conj (f ((3 / 4 : ℂ) + t * I)))
    (hdec : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 →
      ‖f s‖ ≤ C * (1 + s.im ^ 2)⁻¹) (r : ℝ) :
    (∫ t : ℝ, f ((3 / 4 : ℂ) + t * I) /
      ((1 / 4 : ℂ) + (t - r) * I)).re =
        Real.pi * (f ((1 / 2 : ℂ) + r * I)).re := by
  let p : ℂ := (1 / 2 : ℂ) + r * I
  let F : ℂ → ℂ := fun s => f s / (s - p)
  have hpr : p.re = 1 / 2 := by simp [p]
  have hpi : p.im = r := by simp [p]
  have hres : Tendsto (fun s => (s - p) * F s) (𝓝[≠] p) (𝓝 (f p)) := by
    have hc := (hf p (by rw [hpr]; norm_num) (by rw [hpr]; norm_num)).continuousAt
    refine hc.tendsto.mono_left nhdsWithin_le_nhds |>.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    dsimp [F]
    field_simp [sub_ne_zero.mpr hs]
  have hbound : ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 →
      |r| + 1 ≤ |s.im| → ‖F s‖ ≤ C * (1 + s.im ^ 2)⁻¹ := by
    intro s hs1 hs2 ht
    have hd : 1 ≤ ‖s - p‖ := by
      have htriangle : |s.im| ≤ |s.im - r| + |r| := by
        simpa using abs_add_le (s.im - r) r
      have him := Complex.abs_im_le_norm (s - p)
      rw [Complex.sub_im, hpi] at him
      linarith
    exact (show ‖F s‖ ≤ ‖f s‖ by
      dsimp [F]
      rw [norm_div]
      exact div_le_self (norm_nonneg _) hd).trans (hdec s hs1 hs2)
  have hshift := integral_line_sub_integral_line_eq
    (a := 1 / 4) (b := 3 / 4) (p := p) (A := f p)
    (by rw [hpr]; norm_num) (by rw [hpr]; norm_num)
    (fun s hs1 hs2 hsp => (hf s hs1 hs2).div
      (differentiableAt_id.sub_const p) (sub_ne_zero.mpr hsp)) hres hbound
  have hright (t : ℝ) : F ((3 / 4 : ℂ) + t * I) =
      f ((3 / 4 : ℂ) + t * I) / ((1 / 4 : ℂ) + (t - r) * I) := by
    dsimp [F, p]
    congr 1
    ring
  have hleft (t : ℝ) : F ((1 / 4 : ℂ) + t * I) =
      -conj (F ((3 / 4 : ℂ) + t * I)) := by
    rw [hright]
    dsimp [F, p]
    rw [hsym, map_div₀, ← div_neg]
    congr 1
    simp only [map_add, map_mul, map_sub, map_div₀, map_ofNat, map_one,
      conj_ofReal, conj_I]
    ring
  push_cast at hshift
  change (∫ t : ℝ, F ((3 / 4 : ℂ) + t * I)) -
    (∫ t : ℝ, F ((1 / 4 : ℂ) + t * I)) = 2 * Real.pi * f p at hshift
  simp_rw [hleft] at hshift
  rw [integral_neg, integral_conj] at hshift
  have hre := congrArg Complex.re hshift
  simp only [Complex.sub_re, Complex.neg_re, conj_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat,
    mul_zero, zero_mul, add_zero, sub_zero] at hre
  simp_rw [hright] at hre
  change _ = Real.pi * (f p).re
  linarith

end RHTower.WeilSingularArithmetic
