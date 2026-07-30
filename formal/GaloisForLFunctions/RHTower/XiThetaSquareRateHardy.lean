import GaloisForLFunctions.RHTower.XiThetaSquareRateBoundary
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.EulerSineProd
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import GaloisForLFunctions.HTGeometry.PerronKernelBound

/-!
# Holomorphy of the explicit theta square-rate reader

`XiThetaSquareRateBoundary` computes the reader's exact boundary `L²` energy.  This module supplies
the other half of its Hardy certificate directly: the dimensionless reader and its physical-rate
rescaling are holomorphic on the open right half-plane, including the selected removable node.
No Hardy-membership proposition is introduced.
-/

open Complex Real Set Filter Topology MeasureTheory

noncomputable section

namespace RHTower

private lemma sinh_pi_sqrt_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) :
    Complex.sinh ((Real.pi : ℂ) * Complex.sqrt z) ≠ 0 := by
  intro hsinh
  let w := (Real.pi : ℂ) * Complex.sqrt z
  have hsin : Complex.sin (w * I) = 0 := by
    rw [Complex.sin_mul_I, show Complex.sinh w = 0 by exact hsinh, zero_mul]
  rcases Complex.sin_eq_zero_iff.mp hsin with ⟨k, hk⟩
  have him := congrArg Complex.im hk
  have hwre : w.re = 0 := by
    simp only [mul_im, I_re, I_im, mul_zero, mul_one] at him
    simp at him
    exact him
  have hsqrtRe : (Complex.sqrt z).re = 0 := by
    dsimp [w] at hwre
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero] at hwre
    exact (mul_eq_zero.mp hwre).resolve_left Real.pi_ne_zero
  have hsquare := congrArg Complex.re (complex_sqrt_sq z)
  simp [pow_two, Complex.mul_re, hsqrtRe] at hsquare
  nlinarith [sq_nonneg (Complex.sqrt z).im]

/-- The canonical square-zero quotient is holomorphic on the open right half-plane. -/
theorem thetaSquareBlaschkeSymbol_differentiableOn_rightHalfPlane :
    DifferentiableOn ℂ thetaSquareBlaschkeSymbol {z : ℂ | 0 < z.re} := by
  intro z hz
  have hslit : z ∈ Complex.slitPlane := Complex.mem_slitPlane_iff.mpr (Or.inl hz)
  have hsqrt : DifferentiableAt ℂ Complex.sqrt z :=
    Complex.differentiableAt_sqrt hslit
  have harg : DifferentiableAt ℂ (fun q : ℂ => (Real.pi : ℂ) * Complex.sqrt q) z :=
    (differentiableAt_const (c := (Real.pi : ℂ))).mul hsqrt
  exact (harg.csin.div harg.csinh
    (sinh_pi_sqrt_ne_zero_of_re_pos hz)).differentiableWithinAt

/-- The normalized removable difference quotient selecting a positive square remains holomorphic
on the whole right half-plane, including its selected node. -/
theorem thetaSquareBlaschkeReaderSymbol_differentiableOn_rightHalfPlane {n : ℕ} (hn : 1 ≤ n) :
    DifferentiableOn ℂ (thetaSquareBlaschkeReaderSymbol n) {z : ℂ | 0 < z.re} := by
  let S : Set ℂ := {z : ℂ | 0 < z.re}
  have hopen : IsOpen S := isOpen_lt continuous_const continuous_re
  have hnode : thetaSquare n ∈ S := by
    dsimp [S]
    norm_num [thetaSquare, pow_two, Complex.mul_re]
    omega
  have hsymbol : DifferentiableOn ℂ thetaSquareBlaschkeSymbol S :=
    thetaSquareBlaschkeSymbol_differentiableOn_rightHalfPlane
  have hdslope : DifferentiableOn ℂ
      (dslope thetaSquareBlaschkeSymbol (thetaSquare n)) S :=
    (differentiableOn_dslope (hopen.mem_nhds hnode)).2 hsymbol
  change DifferentiableOn ℂ
    (fun z => (thetaSquareBlaschkeNodeSlope n)⁻¹ *
      dslope thetaSquareBlaschkeSymbol (thetaSquare n) z) S
  exact (differentiableOn_const (c := (thetaSquareBlaschkeNodeSlope n)⁻¹)).mul hdslope

/-- After restoring the physical heat-rate scale, the explicit infinite reader is holomorphic on
the open right half-plane. -/
theorem thetaHeatRateReaderSymbol_differentiableOn_rightHalfPlane {n : ℕ} (hn : 1 ≤ n) :
    DifferentiableOn ℂ (thetaHeatRateReaderSymbol n) {s : ℂ | 0 < s.re} := by
  intro s hs
  have hdiv : DifferentiableAt ℂ (fun z : ℂ => z / (Real.pi : ℂ)) s := by
    fun_prop
  have hre : 0 < (s / (Real.pi : ℂ)).re := by
    rw [div_re]
    simp only [ofReal_re, ofReal_im, mul_zero, normSq_ofReal]
    have hp2 : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
    simpa [pow_two] using div_pos (mul_pos hs Real.pi_pos) hp2
  have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
  have hreader :=
    (thetaSquareBlaschkeReaderSymbol_differentiableOn_rightHalfPlane hn)
      (s / (Real.pi : ℂ)) hre
  have hat : DifferentiableAt ℂ (thetaSquareBlaschkeReaderSymbol n)
      (s / (Real.pi : ℂ)) := hreader.differentiableAt (hopen.mem_nhds hre)
  exact (hat.comp s hdiv).differentiableWithinAt

/-! ## Euler product and the selected-zero Cauchy majorant -/

/-- The finite Euler--Blaschke product over the first `N` square nodes. -/
def thetaSquareBlaschkeFinite (N : ℕ) (z : ℂ) : ℂ :=
  ∏ j ∈ Finset.range N,
    ((1 : ℂ) - z / ((j : ℂ) + 1) ^ 2) /
      ((1 : ℂ) + z / ((j : ℂ) + 1) ^ 2)

private lemma norm_thetaSquareBlaschkeFactor_le_one {z : ℂ} (hz : 0 ≤ z.re) (j : ℕ) :
    ‖((1 : ℂ) - z / ((j : ℂ) + 1) ^ 2) /
        ((1 : ℂ) + z / ((j : ℂ) + 1) ^ 2)‖ ≤ 1 := by
  let a : ℝ := ((j : ℝ) + 1) ^ 2
  have ha : 0 < a := by dsimp [a]; positivity
  have ha0 : (a : ℂ) ≠ 0 := ofReal_ne_zero.mpr ha.ne'
  have hrewrite :
      ((1 : ℂ) - z / ((j : ℂ) + 1) ^ 2) /
          ((1 : ℂ) + z / ((j : ℂ) + 1) ^ 2) =
        ((a : ℂ) - z) / ((a : ℂ) + z) := by
    dsimp [a]
    push_cast
    field_simp
  rw [hrewrite]
  have hden : (a : ℂ) + z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp at hre
    nlinarith
  rw [norm_div, div_le_one (norm_pos_iff.mpr hden)]
  rw [← sq_le_sq₀ (norm_nonneg _) (norm_nonneg _),
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, sub_re, ofReal_re, sub_im, ofReal_im, zero_sub,
    add_re, add_im, zero_add]
  nlinarith

/-- Euler's product for complex hyperbolic sine, in the normalization used by the square reader. -/
theorem tendsto_euler_sinh_prod (z : ℂ) :
    Tendsto
      (fun N : ℕ => (Real.pi : ℂ) * z *
        ∏ j ∈ Finset.range N, ((1 : ℂ) + z ^ 2 / ((j : ℂ) + 1) ^ 2))
      atTop (𝓝 (Complex.sinh ((Real.pi : ℂ) * z))) := by
  have h := (Complex.tendsto_euler_sin_prod (z * I)).const_mul (-I)
  have hseq :
      (fun N : ℕ => -I * ((Real.pi : ℂ) * (z * I) *
        ∏ j ∈ Finset.range N,
          ((1 : ℂ) - (z * I) ^ 2 / ((j : ℂ) + 1) ^ 2))) =
      (fun N : ℕ => (Real.pi : ℂ) * z *
        ∏ j ∈ Finset.range N,
          ((1 : ℂ) + z ^ 2 / ((j : ℂ) + 1) ^ 2)) := by
    funext N
    have hzI : (z * I) ^ 2 = -z ^ 2 := by
      rw [mul_pow, I_sq]
      ring
    rw [hzI]
    simp only [neg_div, sub_neg_eq_add]
    calc
      -I * ((Real.pi : ℂ) * (z * I) *
          ∏ j ∈ Finset.range N, ((1 : ℂ) + z ^ 2 / ((j : ℂ) + 1) ^ 2)) =
          ((Real.pi : ℂ) * z *
            ∏ j ∈ Finset.range N, ((1 : ℂ) + z ^ 2 / ((j : ℂ) + 1) ^ 2)) *
              (-(I * I)) := by ring
      _ = (Real.pi : ℂ) * z *
          ∏ j ∈ Finset.range N, ((1 : ℂ) + z ^ 2 / ((j : ℂ) + 1) ^ 2) := by
            rw [I_mul_I]
            ring
  have hlim : -I * Complex.sin ((Real.pi : ℂ) * (z * I)) =
      Complex.sinh ((Real.pi : ℂ) * z) := by
    rw [show (Real.pi : ℂ) * (z * I) = ((Real.pi : ℂ) * z) * I by ring,
      Complex.sin_mul_I]
    calc
      -I * (Complex.sinh ((Real.pi : ℂ) * z) * I) =
          Complex.sinh ((Real.pi : ℂ) * z) * (-(I * I)) := by ring
      _ = Complex.sinh ((Real.pi : ℂ) * z) := by rw [I_mul_I]; ring
  rw [hseq, hlim] at h
  exact h

/-- The finite square-node Blaschke products converge throughout the open right half-plane. -/
theorem tendsto_thetaSquareBlaschkeFinite {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun N => thetaSquareBlaschkeFinite N z) atTop
      (𝓝 (thetaSquareBlaschkeSymbol z)) := by
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz
  have hsqrt0 : Complex.sqrt z ≠ 0 := by
    intro h
    have hsquare := complex_sqrt_sq z
    rw [h] at hsquare
    norm_num at hsquare
    exact hz0 hsquare.symm
  have hnum := Complex.tendsto_euler_sin_prod (Complex.sqrt z)
  have hden := tendsto_euler_sinh_prod (Complex.sqrt z)
  have hsinh : Complex.sinh ((Real.pi : ℂ) * Complex.sqrt z) ≠ 0 :=
    sinh_pi_sqrt_ne_zero_of_re_pos hz
  have hdiv := hnum.div hden hsinh
  rw [thetaSquareBlaschkeSymbol]
  convert hdiv using 1
  ext N
  rw [thetaSquareBlaschkeFinite]
  have hroot : (Complex.sqrt z) ^ 2 = z := complex_sqrt_sq z
  rw [hroot, Finset.prod_div_distrib]
  have hc : (Real.pi : ℂ) * Complex.sqrt z ≠ 0 :=
    mul_ne_zero (ofReal_ne_zero.mpr Real.pi_ne_zero) hsqrt0
  change
    (∏ j ∈ Finset.range N, ((1 : ℂ) - z / ((j : ℂ) + 1) ^ 2)) /
        (∏ j ∈ Finset.range N, ((1 : ℂ) + z / ((j : ℂ) + 1) ^ 2)) =
      (((Real.pi : ℂ) * Complex.sqrt z) *
          ∏ j ∈ Finset.range N, ((1 : ℂ) - z / ((j : ℂ) + 1) ^ 2)) /
        (((Real.pi : ℂ) * Complex.sqrt z) *
          ∏ j ∈ Finset.range N, ((1 : ℂ) + z / ((j : ℂ) + 1) ^ 2))
  exact (mul_div_mul_left _ _ hc).symm

private lemma norm_thetaSquareBlaschkeFinite_le_selectedFactor {z : ℂ} (hz : 0 ≤ z.re)
    {n N : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    ‖thetaSquareBlaschkeFinite N z‖ ≤
      ‖((1 : ℂ) - z / (n : ℂ) ^ 2) / ((1 : ℂ) + z / (n : ℂ) ^ 2)‖ := by
  let f : ℕ → ℂ := fun j =>
    ((1 : ℂ) - z / ((j : ℂ) + 1) ^ 2) /
      ((1 : ℂ) + z / ((j : ℂ) + 1) ^ 2)
  have hi : n - 1 ∈ Finset.range N := by
    rw [Finset.mem_range]
    omega
  have hrest :
      ∏ j ∈ (Finset.range N).erase (n - 1), ‖f j‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) fun j _ =>
      norm_thetaSquareBlaschkeFactor_le_one hz j
  have hsplit :
      ‖thetaSquareBlaschkeFinite N z‖ =
        ‖f (n - 1)‖ * ∏ j ∈ (Finset.range N).erase (n - 1), ‖f j‖ := by
    rw [thetaSquareBlaschkeFinite, norm_prod]
    change (∏ j ∈ Finset.range N, ‖f j‖) = _
    exact (Finset.mul_prod_erase (Finset.range N) (fun j => ‖f j‖) hi).symm
  rw [hsplit]
  calc
    ‖f (n - 1)‖ * ∏ j ∈ (Finset.range N).erase (n - 1), ‖f j‖ ≤
        ‖f (n - 1)‖ * 1 := mul_le_mul_of_nonneg_left hrest (norm_nonneg _)
    _ = ‖((1 : ℂ) - z / (n : ℂ) ^ 2) / ((1 : ℂ) + z / (n : ℂ) ^ 2)‖ := by
      simp only [mul_one]
      congr 1
      dsimp [f]
      rw [Nat.cast_sub hn, Nat.cast_one, sub_add_cancel]

/-- **The selected-zero inner-factor estimate.** Euler's sine product writes the explicit
square-rate quotient as the limit of finite right-half-plane Blaschke products. Removing any
selected zero leaves a contractive product, so the full symbol is bounded by that one factor. -/
theorem norm_thetaSquareBlaschkeSymbol_le_selectedFactor {z : ℂ} (hz : 0 < z.re)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖thetaSquareBlaschkeSymbol z‖ ≤
      ‖((1 : ℂ) - z / (n : ℂ) ^ 2) / ((1 : ℂ) + z / (n : ℂ) ^ 2)‖ := by
  have hlim := (tendsto_thetaSquareBlaschkeFinite hz).norm
  exact le_of_tendsto hlim (eventually_atTop.2 ⟨n, fun N hN =>
    norm_thetaSquareBlaschkeFinite_le_selectedFactor hz.le hn hN⟩)

/-- After removing its selected zero, the normalized reader has the sharp Cauchy majorant on the
open right half-plane. -/
theorem norm_thetaSquareBlaschkeReaderSymbol_le_cauchy {z : ℂ} (hz : 0 < z.re)
    {n : ℕ} (hn : 1 ≤ n) (hznode : z ≠ thetaSquare n) :
    ‖thetaSquareBlaschkeReaderSymbol n z‖ ≤
      ‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ / ‖thetaSquare n + z‖ := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hnode : thetaSquare n = (n : ℂ) ^ 2 := by
    simp [thetaSquare]
  have hplus : thetaSquare n + z ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hnode] at hre
    norm_num [pow_two, Complex.mul_re] at hre
    nlinarith
  have hfac :
      ‖((1 : ℂ) - z / (n : ℂ) ^ 2) / ((1 : ℂ) + z / (n : ℂ) ^ 2)‖ =
        ‖thetaSquare n - z‖ / ‖thetaSquare n + z‖ := by
    have heq :
        ((1 : ℂ) - z / (n : ℂ) ^ 2) / ((1 : ℂ) + z / (n : ℂ) ^ 2) =
          (thetaSquare n - z) / (thetaSquare n + z) := by
      rw [hnode]
      field_simp
    rw [heq, norm_div]
  have hB := norm_thetaSquareBlaschkeSymbol_le_selectedFactor hz hn
  rw [hfac] at hB
  rw [thetaSquareBlaschkeReaderSymbol,
    dslope_of_ne _ hznode, slope_def_field, thetaSquareBlaschkeSymbol_zero,
    sub_zero, norm_mul, norm_div]
  calc
    ‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ *
        (‖thetaSquareBlaschkeSymbol z‖ / ‖z - thetaSquare n‖) ≤
      ‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ *
        ((‖thetaSquare n - z‖ / ‖thetaSquare n + z‖) /
          ‖z - thetaSquare n‖) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hB (norm_nonneg _))
          (norm_nonneg _)
    _ = ‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ / ‖thetaSquare n + z‖ := by
      rw [norm_sub_rev]
      have hminus : ‖z - thetaSquare n‖ ≠ 0 :=
        norm_ne_zero_iff.mpr (sub_ne_zero.mpr hznode)
      have hplusNorm : ‖thetaSquare n + z‖ ≠ 0 := norm_ne_zero_iff.mpr hplus
      field_simp

lemma sq_norm_thetaSquareBlaschkeReaderSymbol_add_mul_I_le_cauchy
    {n : ℕ} (hn : 1 ≤ n) {x t : ℝ} (hx : 0 < x) (ht : t ≠ 0) :
    ‖thetaSquareBlaschkeReaderSymbol n ((x : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
      ‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ ^ 2 *
        ((((n : ℝ) ^ 2 + x) ^ 2 + t ^ 2)⁻¹) := by
  have hzre : 0 < ((x : ℂ) + (t : ℂ) * I).re := by simpa using hx
  have hznode : (x : ℂ) + (t : ℂ) * I ≠ thetaSquare n := by
    intro h
    have him := congrArg Complex.im h
    norm_num [thetaSquare, pow_two, Complex.mul_im] at him
    exact ht him
  have hbound := norm_thetaSquareBlaschkeReaderSymbol_le_cauchy hzre hn hznode
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  have hden :
      ‖thetaSquare n + ((x : ℂ) + (t : ℂ) * I)‖ ^ 2 =
        ((n : ℝ) ^ 2 + x) ^ 2 + t ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    norm_num [thetaSquare, pow_two, Complex.mul_re, Complex.mul_im]
  rw [div_pow, hden] at hsq
  rw [div_eq_mul_inv] at hsq
  exact hsq

/-- The squared dimensionless reader is integrable on every interior vertical line, with its exact
Cauchy majorant integrated explicitly. -/
theorem integral_sq_norm_thetaSquareBlaschkeReaderSymbol_line_le_cauchy
    {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ, ‖thetaSquareBlaschkeReaderSymbol n ((x : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      ‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ ^ 2 *
        (Real.pi / ((n : ℝ) ^ 2 + x)) := by
  let f : ℝ → ℝ := fun t =>
    ‖thetaSquareBlaschkeReaderSymbol n ((x : ℂ) + (t : ℂ) * I)‖ ^ 2
  let g : ℝ → ℝ := fun t =>
    ‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ ^ 2 *
      ((((n : ℝ) ^ 2 + x) ^ 2 + t ^ 2)⁻¹)
  have ha : 0 < (n : ℝ) ^ 2 + x := by positivity
  have hgInt : Integrable g := by
    exact (HTGeometry.integrable_inv_sq_add_sq ha).const_mul _
  have hfCont : Continuous f := by
    apply continuous_iff_continuousAt.2
    intro t
    have hzre : 0 < ((x : ℂ) + (t : ℂ) * I).re := by simpa using hx
    have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
    have hreaderAt : ContinuousAt (thetaSquareBlaschkeReaderSymbol n)
        ((x : ℂ) + (t : ℂ) * I) :=
      ((thetaSquareBlaschkeReaderSymbol_differentiableOn_rightHalfPlane hn)
        ((x : ℂ) + (t : ℂ) * I) hzre).differentiableAt
          (hopen.mem_nhds hzre) |>.continuousAt
    have hlineAt : ContinuousAt (fun u : ℝ => (x : ℂ) + (u : ℂ) * I) t := by
      fun_prop
    have hcomp := hreaderAt.comp_of_eq hlineAt rfl
    simpa [f, Function.comp_def] using! hcomp.norm.pow 2
  have ht0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
  have hfg : ∀ᵐ t : ℝ, f t ≤ g t := by
    filter_upwards [ht0] with t ht
    exact sq_norm_thetaSquareBlaschkeReaderSymbol_add_mul_I_le_cauchy hn hx ht
  have hfInt : Integrable f := by
    refine hgInt.mono' hfCont.aestronglyMeasurable ?_
    filter_upwards [hfg] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · exact ht
    · dsimp [f]
      positivity
  change (∫ t : ℝ, f t) ≤ _
  calc
    (∫ t : ℝ, f t) ≤ ∫ t : ℝ, g t :=
      integral_mono_ae hfInt hgInt hfg
    _ = ‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ ^ 2 *
        (Real.pi / ((n : ℝ) ^ 2 + x)) := by
      dsimp [g]
      rw [integral_const_mul, integral_inv_sq_add_sq_univ ha]

/-- **Uniform interior Hardy bound.** Every positive vertical line has squared reader energy at
most the exact boundary energy; no Hardy-membership proposition remains. -/
theorem integral_sq_norm_thetaSquareBlaschkeReaderSymbol_line_le_boundary
    {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ, ‖thetaSquareBlaschkeReaderSymbol n ((x : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      (4 / Real.pi) * Real.sinh (Real.pi * n) ^ 2 := by
  refine (integral_sq_norm_thetaSquareBlaschkeReaderSymbol_line_le_cauchy hn hx).trans ?_
  rw [norm_inv, norm_thetaSquareBlaschkeNodeSlope hn]
  have hnR : (0 : ℝ) < n := by positivity
  have hsinh : 0 < Real.sinh (Real.pi * n) :=
    Real.sinh_pos_iff.mpr (mul_pos Real.pi_pos hnR)
  have hden : 0 < (n : ℝ) ^ 2 + x := by positivity
  rw [inv_div]
  field_simp
  nlinarith [sq_nonneg (n : ℝ)]

/-- **Physical-rate uniform interior Hardy bound.** Restoring the heat-rate scale multiplies the
dimensionless line energy by `pi`, giving the exact physical boundary-energy ceiling on every
positive vertical line. -/
theorem integral_sq_norm_thetaHeatRateReaderSymbol_line_le_boundary
    {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    (∫ t : ℝ, ‖thetaHeatRateReaderSymbol n ((x : ℂ) + (t : ℂ) * I)‖ ^ 2) ≤
      4 * Real.sinh (Real.pi * n) ^ 2 := by
  let g : ℝ → ℝ := fun u =>
    ‖thetaSquareBlaschkeReaderSymbol n (((x / Real.pi : ℝ) : ℂ) + (u : ℂ) * I)‖ ^ 2
  have heq :
      (fun t : ℝ => ‖thetaHeatRateReaderSymbol n ((x : ℂ) + (t : ℂ) * I)‖ ^ 2) =
        fun t => g (t / Real.pi) := by
    funext t
    dsimp [g, thetaHeatRateReaderSymbol]
    congr 2
    push_cast
    field_simp
  rw [heq]
  have hscale := MeasureTheory.Measure.integral_comp_div g Real.pi
  rw [hscale, abs_of_pos Real.pi_pos]
  have hxpi : 0 < x / Real.pi := div_pos hx Real.pi_pos
  have hdim := integral_sq_norm_thetaSquareBlaschkeReaderSymbol_line_le_boundary hn hxpi
  calc
    Real.pi * ∫ u : ℝ, g u ≤
        Real.pi * ((4 / Real.pi) * Real.sinh (Real.pi * n) ^ 2) :=
      mul_le_mul_of_nonneg_left hdim Real.pi_pos.le
    _ = 4 * Real.sinh (Real.pi * n) ^ 2 := by field_simp

/-! ## Boundary approach and exact Hardy supremum -/

/-- Away from the origin, the removable square-rate reader is continuous at every point of the
imaginary boundary. -/
lemma thetaSquareBlaschkeReaderSymbol_continuousAt_mul_I {n : ℕ} (hn : 1 ≤ n)
    {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt (thetaSquareBlaschkeReaderSymbol n) ((t : ℂ) * I) := by
  have hslit : (t : ℂ) * I ∈ Complex.slitPlane := by
    rw [Complex.mem_slitPlane_iff]
    right
    norm_num
    exact ht
  have hsqrt : DifferentiableAt ℂ Complex.sqrt ((t : ℂ) * I) :=
    Complex.differentiableAt_sqrt hslit
  have harg : DifferentiableAt ℂ
      (fun q : ℂ => (Real.pi : ℂ) * Complex.sqrt q) ((t : ℂ) * I) :=
    (differentiableAt_const (c := (Real.pi : ℂ))).mul hsqrt
  have hsymbol : DifferentiableAt ℂ thetaSquareBlaschkeSymbol ((t : ℂ) * I) :=
    harg.csin.div harg.csinh (sinh_pi_sqrt_pureImag_ne_zero ht)
  have hnode : (t : ℂ) * I ≠ thetaSquare n := pureImag_ne_thetaSquare hn t
  unfold thetaSquareBlaschkeReaderSymbol
  exact continuousAt_const.mul ((continuousAt_dslope_of_ne hnode).2 hsymbol.continuousAt)

private lemma integrable_reader_boundary_majorant {n : ℕ} (hn : 1 ≤ n) :
    Integrable (fun t : ℝ =>
      ‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ ^ 2 *
        ((((n : ℝ) ^ 2) ^ 2 + t ^ 2)⁻¹)) := by
  have hnR : (0 : ℝ) < n := by positivity
  exact (HTGeometry.integrable_inv_sq_add_sq (sq_pos_of_pos hnR)).const_mul _

/-- The interior line energies along `x = 1/(k+1)` converge to the already-computed exact boundary
energy. This is the lower half of the Hardy-supremum identity. -/
theorem tendsto_integral_sq_norm_thetaSquareBlaschkeReaderSymbol_line_zero
    {n : ℕ} (hn : 1 ≤ n) :
    Tendsto
      (fun k : ℕ => ∫ t : ℝ,
        ‖thetaSquareBlaschkeReaderSymbol n
          (((1 / ((k : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
      atTop
      (𝓝 ((4 / Real.pi) * Real.sinh (Real.pi * n) ^ 2)) := by
  let F : ℕ → ℝ → ℝ := fun k t =>
    ‖thetaSquareBlaschkeReaderSymbol n
      (((1 / ((k : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2
  let f : ℝ → ℝ := fun t =>
    ‖thetaSquareBlaschkeReaderSymbol n ((t : ℂ) * I)‖ ^ 2
  let bound : ℝ → ℝ := fun t =>
    ‖(thetaSquareBlaschkeNodeSlope n)⁻¹‖ ^ 2 *
      ((((n : ℝ) ^ 2) ^ 2 + t ^ 2)⁻¹)
  have hFmeas : ∀ k, AEStronglyMeasurable (F k) := by
    intro k
    have hx : 0 < 1 / ((k : ℝ) + 1) := by positivity
    have hcont : Continuous (F k) := by
      apply continuous_iff_continuousAt.2
      intro t
      have hzre : 0 <
          ((((1 / ((k : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)).re := by
        rw [add_re, ofReal_re]
        have hit : ((t : ℂ) * I).re = 0 := by norm_num
        rw [hit, add_zero]
        exact hx
      have hopen : IsOpen {z : ℂ | 0 < z.re} := isOpen_lt continuous_const continuous_re
      have hreaderAt : ContinuousAt (thetaSquareBlaschkeReaderSymbol n)
          (((1 / ((k : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I) :=
        ((thetaSquareBlaschkeReaderSymbol_differentiableOn_rightHalfPlane hn)
          (((1 / ((k : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I) hzre).differentiableAt
            (hopen.mem_nhds hzre) |>.continuousAt
      have hlineAt : ContinuousAt
          (fun u : ℝ => (((1 / ((k : ℝ) + 1) : ℝ) : ℂ) + (u : ℂ) * I)) t := by
        fun_prop
      have hcomp := hreaderAt.comp_of_eq hlineAt rfl
      simpa [F, Function.comp_def] using! hcomp.norm.pow 2
    exact hcont.aestronglyMeasurable
  have hboundInt : Integrable bound := integrable_reader_boundary_majorant hn
  have ht0 : ∀ᵐ t : ℝ, t ≠ 0 := by simp [ae_iff, measure_singleton]
  have hbound : ∀ k, ∀ᵐ t : ℝ, ‖F k t‖ ≤ bound t := by
    intro k
    filter_upwards [ht0] with t ht
    have hx : 0 < 1 / ((k : ℝ) + 1) := by positivity
    have hfirst :=
      sq_norm_thetaSquareBlaschkeReaderSymbol_add_mul_I_le_cauchy hn hx ht
    rw [Real.norm_eq_abs, abs_of_nonneg]
    · refine hfirst.trans ?_
      dsimp [bound]
      apply mul_le_mul_of_nonneg_left
      · apply inv_anti₀
        · positivity
        · nlinarith [sq_nonneg ((n : ℝ) ^ 2), sq_nonneg (1 / ((k : ℝ) + 1))]
      · positivity
    · dsimp [F]
      positivity
  have hlim : ∀ᵐ t : ℝ, Tendsto (fun k => F k t) atTop (𝓝 (f t)) := by
    filter_upwards [ht0] with t ht
    have hx0 : Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hx0c : Tendsto (fun k : ℕ => ((1 / ((k : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝 0) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp hx0
    have hpoint : Tendsto
        (fun k : ℕ => ((1 / ((k : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)
        atTop (𝓝 ((t : ℂ) * I)) := by
      simpa using hx0c.add_const ((t : ℂ) * I)
    have hreader :=
      (thetaSquareBlaschkeReaderSymbol_continuousAt_mul_I hn ht).tendsto.comp hpoint
    simpa [F, f] using hreader.norm.pow 2
  have hDCT := tendsto_integral_of_dominated_convergence bound hFmeas hboundInt hbound hlim
  rw [integral_sq_norm_thetaSquareBlaschkeReaderSymbol_boundary hn] at hDCT
  simpa [F, f] using hDCT

/-- **Exact dimensionless Hardy norm.** The supremum of the squared interior vertical-line energies
equals the exact boundary energy. Both halves are proved directly: the selected-factor Cauchy
majorant supplies the upper bound and dominated boundary approach supplies equality. -/
theorem csSup_integral_sq_norm_thetaSquareBlaschkeReaderSymbol_line
    {n : ℕ} (hn : 1 ≤ n) :
    sSup {E : ℝ | ∃ x : ℝ, 0 < x ∧
      E = ∫ t : ℝ,
        ‖thetaSquareBlaschkeReaderSymbol n ((x : ℂ) + (t : ℂ) * I)‖ ^ 2} =
      (4 / Real.pi) * Real.sinh (Real.pi * n) ^ 2 := by
  let S : Set ℝ := {E : ℝ | ∃ x : ℝ, 0 < x ∧
    E = ∫ t : ℝ,
      ‖thetaSquareBlaschkeReaderSymbol n ((x : ℂ) + (t : ℂ) * I)‖ ^ 2}
  let B : ℝ := (4 / Real.pi) * Real.sinh (Real.pi * n) ^ 2
  have hSne : S.Nonempty := by
    refine ⟨∫ t : ℝ,
      ‖thetaSquareBlaschkeReaderSymbol n ((1 : ℂ) + (t : ℂ) * I)‖ ^ 2, ?_⟩
    exact ⟨1, by norm_num, rfl⟩
  have hBdd : BddAbove S := by
    refine ⟨B, ?_⟩
    intro E hE
    rcases hE with ⟨x, hx, rfl⟩
    exact integral_sq_norm_thetaSquareBlaschkeReaderSymbol_line_le_boundary hn hx
  apply le_antisymm
  · apply csSup_le hSne
    intro E hE
    rcases hE with ⟨x, hx, rfl⟩
    exact integral_sq_norm_thetaSquareBlaschkeReaderSymbol_line_le_boundary hn hx
  · have hlim := tendsto_integral_sq_norm_thetaSquareBlaschkeReaderSymbol_line_zero hn
    change Tendsto (fun k : ℕ => ∫ t : ℝ,
      ‖thetaSquareBlaschkeReaderSymbol n
        (((1 / ((k : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) atTop (𝓝 B) at hlim
    apply le_of_tendsto hlim
    exact Filter.Eventually.of_forall fun k => le_csSup hBdd
      ⟨1 / ((k : ℝ) + 1), by positivity, rfl⟩

/-- Exact change of variables from a dimensionless vertical line to its physical heat-rate line. -/
lemma integral_sq_norm_thetaHeatRateReaderSymbol_pi_mul_line
    (n : ℕ) (x : ℝ) :
    (∫ t : ℝ,
      ‖thetaHeatRateReaderSymbol n (((Real.pi * x : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) =
      Real.pi * ∫ u : ℝ,
        ‖thetaSquareBlaschkeReaderSymbol n ((x : ℂ) + (u : ℂ) * I)‖ ^ 2 := by
  let g : ℝ → ℝ := fun u =>
    ‖thetaSquareBlaschkeReaderSymbol n ((x : ℂ) + (u : ℂ) * I)‖ ^ 2
  have heq :
      (fun t : ℝ =>
        ‖thetaHeatRateReaderSymbol n (((Real.pi * x : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) =
        fun t => g (t / Real.pi) := by
    funext t
    dsimp [g, thetaHeatRateReaderSymbol]
    congr 2
    push_cast
    field_simp
  rw [heq]
  have hscale := MeasureTheory.Measure.integral_comp_div g Real.pi
  rw [hscale, abs_of_pos Real.pi_pos]
  simp [g, smul_eq_mul]

/-- The physical-rate interior energies converge to the exact physical boundary energy. -/
theorem tendsto_integral_sq_norm_thetaHeatRateReaderSymbol_line_zero
    {n : ℕ} (hn : 1 ≤ n) :
    Tendsto
      (fun k : ℕ => ∫ t : ℝ,
        ‖thetaHeatRateReaderSymbol n
          ((((Real.pi / ((k : ℝ) + 1)) : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2)
      atTop
      (𝓝 (4 * Real.sinh (Real.pi * n) ^ 2)) := by
  have hdim := tendsto_integral_sq_norm_thetaSquareBlaschkeReaderSymbol_line_zero hn
  have hmul := hdim.const_mul Real.pi
  convert hmul using 1
  · ext k
    rw [show Real.pi / ((k : ℝ) + 1) = Real.pi * (1 / ((k : ℝ) + 1)) by ring,
      integral_sq_norm_thetaHeatRateReaderSymbol_pi_mul_line]
  · field_simp

/-- **Exact physical Hardy norm.** The supremum of all positive physical-rate vertical-line
energies equals `4 sinh(pi n)^2`. -/
theorem csSup_integral_sq_norm_thetaHeatRateReaderSymbol_line
    {n : ℕ} (hn : 1 ≤ n) :
    sSup {E : ℝ | ∃ x : ℝ, 0 < x ∧
      E = ∫ t : ℝ,
        ‖thetaHeatRateReaderSymbol n ((x : ℂ) + (t : ℂ) * I)‖ ^ 2} =
      4 * Real.sinh (Real.pi * n) ^ 2 := by
  let S : Set ℝ := {E : ℝ | ∃ x : ℝ, 0 < x ∧
    E = ∫ t : ℝ,
      ‖thetaHeatRateReaderSymbol n ((x : ℂ) + (t : ℂ) * I)‖ ^ 2}
  let B : ℝ := 4 * Real.sinh (Real.pi * n) ^ 2
  have hSne : S.Nonempty := by
    refine ⟨∫ t : ℝ,
      ‖thetaHeatRateReaderSymbol n ((1 : ℂ) + (t : ℂ) * I)‖ ^ 2, ?_⟩
    exact ⟨1, by norm_num, rfl⟩
  have hBdd : BddAbove S := by
    refine ⟨B, ?_⟩
    intro E hE
    rcases hE with ⟨x, hx, rfl⟩
    exact integral_sq_norm_thetaHeatRateReaderSymbol_line_le_boundary hn hx
  apply le_antisymm
  · apply csSup_le hSne
    intro E hE
    rcases hE with ⟨x, hx, rfl⟩
    exact integral_sq_norm_thetaHeatRateReaderSymbol_line_le_boundary hn hx
  · have hlim := tendsto_integral_sq_norm_thetaHeatRateReaderSymbol_line_zero hn
    change Tendsto (fun k : ℕ => ∫ t : ℝ,
      ‖thetaHeatRateReaderSymbol n
        ((((Real.pi / ((k : ℝ) + 1)) : ℝ) : ℂ) + (t : ℂ) * I)‖ ^ 2) atTop (𝓝 B) at hlim
    apply le_of_tendsto hlim
    exact Filter.Eventually.of_forall fun k => le_csSup hBdd
      ⟨Real.pi / ((k : ℝ) + 1), by positivity, rfl⟩

/-- The exact physical reader energy in the standard right-half-plane Hardy normalization. -/
theorem normalized_csSup_integral_sq_norm_thetaHeatRateReaderSymbol_line
    {n : ℕ} (hn : 1 ≤ n) :
    (1 / (2 * Real.pi)) *
      sSup {E : ℝ | ∃ x : ℝ, 0 < x ∧
        E = ∫ t : ℝ,
          ‖thetaHeatRateReaderSymbol n ((x : ℂ) + (t : ℂ) * I)‖ ^ 2} =
      (2 / Real.pi) * Real.sinh (Real.pi * n) ^ 2 := by
  rw [csSup_integral_sq_norm_thetaHeatRateReaderSymbol_line hn]
  field_simp
  norm_num

end RHTower
