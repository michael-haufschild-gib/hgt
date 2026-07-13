import GaloisForLFunctions.RHTower.XiGuinandWeilVerticalCauchy
import GaloisForLFunctions.RHTower.XiRelativeResolventTrace
import GaloisForLFunctions.RHTower.XiThreeHalvesSummability
import GaloisForLFunctions.RHTower.SawtoothModeSum

/-!
# Integrated Xi resolvent decay on the sharp rectangular vertical edge

The pointwise logarithmic derivative can be arbitrarily large on a vertical line close to a Xi
zero.  The integrated Cauchy estimate removes this false loss.  This module first proves the
per-divisor-copy estimate needed to sum the centered relative resolvent on the edge.
-/

open Complex Filter intervalIntegral MeasureTheory Set

namespace RHTower

noncomputable section

/-- One raw relative-resolvent summand, already multiplied by the squared rectangular test, on the
right vertical edge. -/
def xiRectangularVerticalRawTerm (L a R : ℝ) (q : XiZeroCopy) (y : ℝ) : ℂ :=
  let z : ℂ := (R : ℂ) + y * I
  xiRectangularTwoEdgeTransform L a z ^ 2 *
    (-z / (xiSpectralPoint q * (xiSpectralPoint q - z)))

/-- Explicit numerator in the integrated per-copy vertical-resolvent estimate. -/
def xiRectangularVerticalIntegratedNumerator (L a R : ℝ) : ℝ :=
  ((rectangularTransformStripBound L a 1 ^ 2 / R ^ 2) * (|R| + 1)) *
      xiVerticalCauchyKernelBound +
    2 * (((8 * rectangularTransformStripBound L a (3 / 2) ^ 2 / R ^ 2) *
      (|R| + 1)) + rectangularTransformStripBound L a 1 ^ 2 / R ^ 2)

theorem xiRectangularVerticalIntegratedNumerator_nonneg (L a R : ℝ) :
    0 ≤ xiRectangularVerticalIntegratedNumerator L a R := by
  unfold xiRectangularVerticalIntegratedNumerator
  have hC := xiVerticalCauchyKernelBound_nonneg
  have hA : 0 ≤ rectangularTransformStripBound L a 1 ^ 2 / R ^ 2 := by positivity
  have hB : 0 ≤ 8 * rectangularTransformStripBound L a (3 / 2) ^ 2 / R ^ 2 := by
    positivity
  exact add_nonneg (mul_nonneg (mul_nonneg hA (by positivity)) hC)
    (mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hB (by positivity)) hA))

private theorem norm_verticalPoint_le (R y : ℝ) (hy : |y| ≤ 1) :
    ‖(R : ℂ) + y * I‖ ≤ |R| + 1 := by
  calc
    ‖(R : ℂ) + y * I‖ ≤ ‖(R : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
    _ = |R| + |y| := by simp
    _ ≤ |R| + 1 := add_le_add_right hy |R|

/-- The integrated contribution of one Xi divisor copy is `O(1/(R*|p|))`, uniformly even when
the vertical edge approaches the pole horizontally. -/
theorem norm_integral_xiRectangularVerticalRawTerm_le
    (L a R : ℝ) (hR : 2 ≤ |R|) (q : XiZeroCopy)
    (havoid : R ≠ (xiSpectralPoint q).re) :
    ‖∫ y in (-1 : ℝ)..1, xiRectangularVerticalRawTerm L a R q y‖ ≤
      xiRectangularVerticalIntegratedNumerator L a R / ‖xiSpectralPoint q‖ := by
  let p : ℂ := xiSpectralPoint q
  let z : ℝ → ℂ := fun y => (R : ℂ) + y * I
  let g : ℂ → ℂ := fun w => xiRectangularTwoEdgeTransform L a w ^ 2
  let h : ℝ → ℂ := fun y => g (z y) * z y / p
  let M : ℝ :=
    (((8 * rectangularTransformStripBound L a (3 / 2) ^ 2 / R ^ 2) *
      (|R| + 1)) + rectangularTransformStripBound L a 1 ^ 2 / R ^ 2) / ‖p‖
  have hRpos : 0 < |R| := lt_of_lt_of_le (by norm_num) hR
  have hp0 : p ≠ 0 := xiSpectralPoint_ne_zero q
  have hpNorm : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  have hpim := xiSpectralPoint_im_mem_openHalf q
  have hpimAbs : |p.im| ≤ 1 := by
    rw [abs_le]
    constructor <;> linarith [hpim.1, hpim.2]
  have hgdiff : Differentiable ℂ g := by
    intro w
    simpa only [g, differentiableWithinAt_univ] using
      (xiRectangularTwoEdgeTransform_sq_analyticOnNhd L a).differentiableOn
        w (Set.mem_univ w)
  have hzDeriv (y : ℝ) : HasDerivAt z I y := by
    dsimp only [z]
    have hmul : HasDerivAt (fun t : ℝ => (t : ℂ) * I) I y := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
    simpa using hmul.const_add (R : ℂ)
  have hhDeriv (y : ℝ) : HasDerivAt h
      (((deriv g (z y) * I) * z y + g (z y) * I) / p) y := by
    dsimp only [h]
    exact (((hgdiff (z y)).hasDerivAt.comp y (hzDeriv y)).mul (hzDeriv y)).div_const p
  have hM : 0 ≤ M := by
    dsimp only [M]
    positivity
  have hdiff : ∀ y ∈ Icc (-1 : ℝ) 1, DifferentiableAt ℝ h y := by
    intro y hy
    exact (hhDeriv y).differentiableAt
  have hderiv : ∀ y ∈ Icc (-1 : ℝ) 1, ‖deriv h y‖ ≤ M := by
    intro y hy
    have hyAbs : |y| ≤ 1 := (abs_le).2 hy
    have hgValue := norm_xiRectangularTwoEdgeTransform_vertical_sq_le
      L a R y hRpos hyAbs
    have hgDeriv := norm_deriv_xiRectangularTwoEdgeTransform_sq_vertical_le
      L a R y hR hyAbs
    have hzNorm := norm_verticalPoint_le R y hyAbs
    rw [(hhDeriv y).deriv, norm_div]
    calc
      ‖(deriv g (z y) * I) * z y + g (z y) * I‖ / ‖p‖ ≤
          ((‖deriv g (z y)‖ * ‖I‖) * ‖z y‖ + ‖g (z y)‖ * ‖I‖) / ‖p‖ := by
        apply div_le_div_of_nonneg_right _ (norm_nonneg p)
        calc
          ‖(deriv g (z y) * I) * z y + g (z y) * I‖ ≤
              ‖(deriv g (z y) * I) * z y‖ + ‖g (z y) * I‖ := norm_add_le _ _
          _ = (‖deriv g (z y)‖ * ‖I‖) * ‖z y‖ + ‖g (z y)‖ * ‖I‖ := by
            rw [norm_mul, norm_mul, norm_mul]
      _ = (‖deriv g (z y)‖ * ‖z y‖ + ‖g (z y)‖) / ‖p‖ := by
        rw [norm_I, mul_one, mul_one]
      _ ≤ (((8 * rectangularTransformStripBound L a (3 / 2) ^ 2 / R ^ 2) *
          (|R| + 1)) + rectangularTransformStripBound L a 1 ^ 2 / R ^ 2) /
            ‖p‖ := by
        apply div_le_div_of_nonneg_right _ (norm_nonneg p)
        apply add_le_add
        · exact mul_le_mul hgDeriv hzNorm (norm_nonneg _) (by positivity)
        · simpa only [g, z] using hgValue
      _ = M := rfl
  have hhValue : ‖h p.im‖ ≤
      ((rectangularTransformStripBound L a 1 ^ 2 / R ^ 2) * (|R| + 1)) / ‖p‖ := by
    dsimp only [h]
    rw [norm_div, norm_mul]
    have hgValue := norm_xiRectangularTwoEdgeTransform_vertical_sq_le
      L a R p.im hRpos hpimAbs
    have hzNorm := norm_verticalPoint_le R p.im hpimAbs
    apply div_le_div_of_nonneg_right _ (norm_nonneg p)
    exact mul_le_mul (by simpa only [g, z] using hgValue) hzNorm
      (norm_nonneg _) (by positivity)
  have hweighted := norm_integral_mul_vertical_cauchyKernel_le
    hM hdiff hderiv hpim (R := R) (by simpa only [p] using havoid)
  have hrewrite : ∀ y : ℝ,
      xiRectangularVerticalRawTerm L a R q y =
        h y * ((z y - p)⁻¹) := by
    intro y
    have hzp : z y - p ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      simp only [z, p, sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        zero_mul, mul_zero, sub_zero, add_zero, zero_re] at hre
      exact havoid (sub_eq_zero.mp hre)
    dsimp only [xiRectangularVerticalRawTerm, h, g, z, p]
    rw [show xiSpectralPoint q - ((R : ℂ) + y * I) =
        -(((R : ℂ) + y * I) - xiSpectralPoint q) by ring,
      mul_neg, div_neg]
    simp only [neg_div, neg_neg]
    field_simp [hp0, hzp]
  calc
    ‖∫ y in (-1 : ℝ)..1, xiRectangularVerticalRawTerm L a R q y‖ =
        ‖∫ y in (-1 : ℝ)..1, h y * ((z y - p)⁻¹)‖ := by
      congr 1
      apply integral_congr
      intro y hy
      exact hrewrite y
    _ ≤ ‖h p.im‖ * xiVerticalCauchyKernelBound + 2 * M := hweighted
    _ ≤ ((((rectangularTransformStripBound L a 1 ^ 2 / R ^ 2) * (|R| + 1)) /
          ‖p‖) * xiVerticalCauchyKernelBound) + 2 * M := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hhValue xiVerticalCauchyKernelBound_nonneg) le_rfl
    _ = xiRectangularVerticalIntegratedNumerator L a R / ‖xiSpectralPoint q‖ := by
      dsimp only [M, p]
      unfold xiRectangularVerticalIntegratedNumerator
      field_simp

/-- `R`-independent constant in the integrated per-copy `1/(|R|*|p|)` estimate. -/
def xiRectangularVerticalIntegratedConstant (L a : ℝ) : ℝ :=
  (3 / 2) * rectangularTransformStripBound L a 1 ^ 2 *
      xiVerticalCauchyKernelBound +
    24 * rectangularTransformStripBound L a (3 / 2) ^ 2 +
    rectangularTransformStripBound L a 1 ^ 2

theorem xiRectangularVerticalIntegratedConstant_nonneg (L a : ℝ) :
    0 ≤ xiRectangularVerticalIntegratedConstant L a := by
  unfold xiRectangularVerticalIntegratedConstant
  have hC := xiVerticalCauchyKernelBound_nonneg
  positivity

/-- The explicit per-copy numerator is uniformly `O(1/|R|)`. -/
theorem xiRectangularVerticalIntegratedNumerator_le
    (L a R : ℝ) (hR : 2 ≤ |R|) :
    xiRectangularVerticalIntegratedNumerator L a R ≤
      xiRectangularVerticalIntegratedConstant L a / |R| := by
  let A₁ : ℝ := rectangularTransformStripBound L a 1 ^ 2
  let A₃ : ℝ := rectangularTransformStripBound L a (3 / 2) ^ 2
  have hRpos : 0 < |R| := lt_of_lt_of_le (by norm_num) hR
  have hA₁ : 0 ≤ A₁ := by dsimp [A₁]; positivity
  have hA₃ : 0 ≤ A₃ := by dsimp [A₃]; positivity
  have hplus : |R| + 1 ≤ (3 / 2 : ℝ) * |R| := by linarith
  have hbase (A : ℝ) (hA : 0 ≤ A) :
      (A / R ^ 2) * (|R| + 1) ≤ ((3 / 2 : ℝ) * A) / |R| := by
    rw [← sq_abs]
    calc
      A / |R| ^ 2 * (|R| + 1) = A * (|R| + 1) / |R| ^ 2 := by ring
      _ ≤ A * ((3 / 2 : ℝ) * |R|) / |R| ^ 2 :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hplus hA) (sq_nonneg _)
      _ = ((3 / 2 : ℝ) * A) / |R| := by field_simp
  have hsmall (A : ℝ) (hA : 0 ≤ A) :
      2 * (A / R ^ 2) ≤ A / |R| := by
    rw [← sq_abs]
    calc
      2 * (A / |R| ^ 2) = A * (2 / |R| ^ 2) := by ring
      _ ≤ A * (|R| / |R| ^ 2) := by
        gcongr
      _ = A / |R| := by field_simp
  have hfirst :
      ((A₁ / R ^ 2) * (|R| + 1)) * xiVerticalCauchyKernelBound ≤
        (((3 / 2 : ℝ) * A₁) * xiVerticalCauchyKernelBound) / |R| := by
    calc
      ((A₁ / R ^ 2) * (|R| + 1)) * xiVerticalCauchyKernelBound ≤
          (((3 / 2 : ℝ) * A₁) / |R|) * xiVerticalCauchyKernelBound :=
        mul_le_mul_of_nonneg_right (hbase A₁ hA₁) xiVerticalCauchyKernelBound_nonneg
      _ = (((3 / 2 : ℝ) * A₁) * xiVerticalCauchyKernelBound) / |R| := by ring
  have hmiddle :
      2 * (((8 * A₃ / R ^ 2) * (|R| + 1))) ≤ 24 * A₃ / |R| := by
    have hb := hbase (8 * A₃) (mul_nonneg (by norm_num) hA₃)
    calc
      2 * ((8 * A₃ / R ^ 2) * (|R| + 1)) ≤
          2 * (((3 / 2 : ℝ) * (8 * A₃)) / |R|) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = 24 * A₃ / |R| := by ring
  have hlast : 2 * (A₁ / R ^ 2) ≤ A₁ / |R| := hsmall A₁ hA₁
  have hsecond :
      2 * (((8 * A₃ / R ^ 2) * (|R| + 1)) + A₁ / R ^ 2) ≤
        24 * A₃ / |R| + A₁ / |R| := by
    rw [mul_add]
    exact add_le_add hmiddle hlast
  unfold xiRectangularVerticalIntegratedNumerator
  unfold xiRectangularVerticalIntegratedConstant
  change ((A₁ / R ^ 2) * (|R| + 1)) * xiVerticalCauchyKernelBound +
      2 * (((8 * A₃ / R ^ 2) * (|R| + 1)) + A₁ / R ^ 2) ≤ _
  calc
    ((A₁ / R ^ 2) * (|R| + 1)) * xiVerticalCauchyKernelBound +
        2 * (((8 * A₃ / R ^ 2) * (|R| + 1)) + A₁ / R ^ 2) ≤
      ((((3 / 2 : ℝ) * A₁) * xiVerticalCauchyKernelBound) / |R|) +
        (24 * A₃ / |R| + A₁ / |R|) := add_le_add hfirst hsecond
    _ = ((3 / 2) * A₁ * xiVerticalCauchyKernelBound + 24 * A₃ + A₁) / |R| := by
      ring

/-- Uniform integrated per-copy estimate in its summation-ready form. -/
theorem norm_integral_xiRectangularVerticalRawTerm_le_inv_norm
    (L a R : ℝ) (hR : 2 ≤ |R|) (q : XiZeroCopy)
    (havoid : R ≠ (xiSpectralPoint q).re) :
    ‖∫ y in (-1 : ℝ)..1, xiRectangularVerticalRawTerm L a R q y‖ ≤
      xiRectangularVerticalIntegratedConstant L a /
        (|R| * ‖xiSpectralPoint q‖) := by
  have hp : 0 < ‖xiSpectralPoint q‖ :=
    norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  calc
    ‖∫ y in (-1 : ℝ)..1, xiRectangularVerticalRawTerm L a R q y‖ ≤
        xiRectangularVerticalIntegratedNumerator L a R / ‖xiSpectralPoint q‖ :=
      norm_integral_xiRectangularVerticalRawTerm_le L a R hR q havoid
    _ ≤ (xiRectangularVerticalIntegratedConstant L a / |R|) /
        ‖xiSpectralPoint q‖ :=
      div_le_div_of_nonneg_right
        (xiRectangularVerticalIntegratedNumerator_le L a R hR) (norm_nonneg _)
    _ = xiRectangularVerticalIntegratedConstant L a /
        (|R| * ‖xiSpectralPoint q‖) := by rw [div_div]

/-- Reciprocal `3/2` summability makes every bounded part of the exact Xi spectrum finite. -/
theorem xiSpectralPoint_finite_norm_le {B : ℝ} (hB : 0 < B) :
    {q : XiZeroCopy | ‖xiSpectralPoint q‖ ≤ B}.Finite := by
  let w : XiZeroCopy → ℝ := fun q =>
    1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)
  let c : ℝ := 1 / (B * Real.sqrt B)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hev : ∀ᶠ q : XiZeroCopy in Filter.cofinite, w q < c :=
    xiSpectralPoint_inv_three_halves_summable.tendsto_cofinite_zero.eventually_lt_const hc
  have hfinite : {q : XiZeroCopy | c ≤ w q}.Finite := by
    have hcofinite := Filter.mem_cofinite.mp (Filter.eventually_iff.mp hev)
    simpa only [Set.compl_setOf, Set.mem_setOf_eq, not_lt] using hcofinite
  refine hfinite.subset ?_
  intro q hq
  have hp : 0 < ‖xiSpectralPoint q‖ :=
    norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hsqrt : Real.sqrt ‖xiSpectralPoint q‖ ≤ Real.sqrt B :=
    Real.sqrt_le_sqrt hq
  have hden :
      ‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖ ≤
        B * Real.sqrt B :=
    mul_le_mul hq hsqrt (Real.sqrt_nonneg _) hB.le
  dsimp only [c, w]
  exact one_div_le_one_div_of_le (mul_pos hp (Real.sqrt_pos.2 hp)) hden

/-- Away from the radial scale of the edge, the raw integrand regains inverse-square spectral
decay.  This is the absolutely summable half of the near/far decomposition. -/
theorem norm_xiRectangularVerticalRawTerm_le_inv_sq
    (L a R : ℝ) (hR : 2 ≤ |R|) (q : XiZeroCopy)
    (hfar : 3 * |R| ≤ ‖xiSpectralPoint q‖) {y : ℝ} (hy : |y| ≤ 1) :
    ‖xiRectangularVerticalRawTerm L a R q y‖ ≤
      3 * rectangularTransformStripBound L a 1 ^ 2 /
        (|R| * ‖xiSpectralPoint q‖ ^ 2) := by
  let p : ℂ := xiSpectralPoint q
  let z : ℂ := (R : ℂ) + y * I
  let A : ℝ := rectangularTransformStripBound L a 1 ^ 2
  have hRpos : 0 < |R| := lt_of_lt_of_le (by norm_num) hR
  have hp : 0 < ‖p‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hz : ‖z‖ ≤ |R| + 1 := norm_verticalPoint_le R y hy
  have hz' : ‖z‖ ≤ (3 / 2 : ℝ) * |R| := by linarith
  have hzhalf : ‖z‖ ≤ ‖p‖ / 2 := by
    dsimp only [p] at hfar ⊢
    linarith
  have hdiff : ‖p‖ / 2 ≤ ‖p - z‖ := by
    have hrev := norm_sub_norm_le p z
    linarith
  have hg : ‖xiRectangularTwoEdgeTransform L a z ^ 2‖ ≤ A / |R| ^ 2 := by
    have hraw := norm_xiRectangularTwoEdgeTransform_vertical_sq_le
      L a R y hRpos hy
    simpa only [z, A, sq_abs] using hraw
  have hnum :
      ‖xiRectangularTwoEdgeTransform L a z ^ 2‖ * ‖z‖ ≤
        (A / |R| ^ 2) * ((3 / 2 : ℝ) * |R|) :=
    mul_le_mul hg hz' (norm_nonneg _) (by positivity)
  have hden : ‖p‖ * (‖p‖ / 2) ≤ ‖p‖ * ‖p - z‖ :=
    mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)
  unfold xiRectangularVerticalRawTerm
  dsimp only [z, p, A]
  rw [norm_mul, norm_div, norm_neg, norm_mul]
  rw [← mul_div_assoc]
  calc
    ‖xiRectangularTwoEdgeTransform L a z ^ 2‖ * ‖z‖ /
        (‖p‖ * ‖p - z‖) ≤
      ((A / |R| ^ 2) * ((3 / 2 : ℝ) * |R|)) /
        (‖p‖ * ‖p - z‖) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ ((A / |R| ^ 2) * ((3 / 2 : ℝ) * |R|)) /
        (‖p‖ * (‖p‖ / 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 3 * (A / (|R| * ‖p‖ ^ 2)) := by field_simp
    _ = 3 * rectangularTransformStripBound L a 1 ^ 2 /
        (|R| * ‖xiSpectralPoint q‖ ^ 2) := by dsimp only [A, p]; ring

/-- A vertical raw summand is continuous on the integration segment whenever the edge avoids its
spectral real coordinate. -/
theorem continuousOn_xiRectangularVerticalRawTerm
    (L a R : ℝ) (q : XiZeroCopy)
    (havoid : R ≠ (xiSpectralPoint q).re) :
    ContinuousOn (xiRectangularVerticalRawTerm L a R q) (Icc (-1 : ℝ) 1) := by
  let p : ℂ := xiSpectralPoint q
  let z : ℝ → ℂ := fun y => (R : ℂ) + y * I
  have hp0 : p ≠ 0 := xiSpectralPoint_ne_zero q
  have hz : Continuous z := by
    dsimp only [z]
    fun_prop
  have hpz : ∀ y ∈ Icc (-1 : ℝ) 1, p - z y ≠ 0 := by
    intro y hy hzero
    have hre := congrArg Complex.re hzero
    simp only [p, z, sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      zero_mul, mul_zero, sub_zero, add_zero, zero_re] at hre
    exact havoid (sub_eq_zero.mp hre).symm
  have hg : ContinuousOn
      (fun y : ℝ => xiRectangularTwoEdgeTransform L a (z y) ^ 2)
      (Icc (-1 : ℝ) 1) :=
    (xiRectangularTwoEdgeTransform_sq_analyticOnNhd L a).continuousOn.comp
      hz.continuousOn (fun y hy => Set.mem_univ (z y))
  have hquot : ContinuousOn
      (fun y : ℝ => -(z y) / (p * (p - z y))) (Icc (-1 : ℝ) 1) := by
    apply hz.continuousOn.neg.div
      (continuousOn_const.mul (continuousOn_const.sub hz.continuousOn))
    intro y hy
    exact mul_ne_zero hp0 (hpz y hy)
  unfold xiRectangularVerticalRawTerm
  dsimp only [z, p]
  exact hg.mul hquot

/-- The far spectral contribution is absolutely integrable with inverse-square spectral size. -/
theorem integral_norm_xiRectangularVerticalRawTerm_le_inv_sq
    (L a R : ℝ) (hR : 2 ≤ |R|) (q : XiZeroCopy)
    (hfar : 3 * |R| ≤ ‖xiSpectralPoint q‖) :
    (∫ y in (-1 : ℝ)..1, ‖xiRectangularVerticalRawTerm L a R q y‖) ≤
      6 * rectangularTransformStripBound L a 1 ^ 2 /
        (|R| * ‖xiSpectralPoint q‖ ^ 2) := by
  have hRpos : 0 < |R| := lt_of_lt_of_le (by norm_num) hR
  have him := xiSpectralPoint_im_mem_openHalf q
  have himAbs : |(xiSpectralPoint q).im| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith [him.1, him.2]
  have havoid : R ≠ (xiSpectralPoint q).re := by
    intro heq
    have hnorm := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
    rw [← heq] at hnorm
    linarith
  have hcont := continuousOn_xiRectangularVerticalRawTerm L a R q havoid
  have hfint : IntervalIntegrable (xiRectangularVerticalRawTerm L a R q)
      volume (-1 : ℝ) 1 := by
    have hcontu : ContinuousOn (xiRectangularVerticalRawTerm L a R q)
        (uIcc (-1 : ℝ) 1) := by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hcont
    exact hcontu.intervalIntegrable
  let C : ℝ := 3 * rectangularTransformStripBound L a 1 ^ 2 /
    (|R| * ‖xiSpectralPoint q‖ ^ 2)
  have hmono :
      (∫ y in (-1 : ℝ)..1, ‖xiRectangularVerticalRawTerm L a R q y‖) ≤
        ∫ _y in (-1 : ℝ)..1, C := by
    apply intervalIntegral.integral_mono_on (by norm_num) hfint.norm
      (continuous_const.intervalIntegrable _ _)
    intro y hy
    exact norm_xiRectangularVerticalRawTerm_le_inv_sq L a R hR q hfar
      ((abs_le).2 hy)
  calc
    (∫ y in (-1 : ℝ)..1, ‖xiRectangularVerticalRawTerm L a R q y‖) ≤
        ∫ _y in (-1 : ℝ)..1, C := hmono
    _ = 6 * rectangularTransformStripBound L a 1 ^ 2 /
        (|R| * ‖xiSpectralPoint q‖ ^ 2) := by
      rw [intervalIntegral.integral_const]
      dsimp only [C]
      norm_num
      ring

/-- On a bounded spectral ball, reciprocal `3/2` weight dominates reciprocal `1` weight with the
sharp square-root loss. -/
theorem one_div_norm_le_sqrt_mul_one_div_norm_sqrt_norm
    (q : XiZeroCopy) {B : ℝ} (hq : ‖xiSpectralPoint q‖ ≤ B) :
    1 / ‖xiSpectralPoint q‖ ≤
      Real.sqrt B *
        (1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)) := by
  have hp : 0 < ‖xiSpectralPoint q‖ :=
    norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hs : Real.sqrt ‖xiSpectralPoint q‖ ≤ Real.sqrt B :=
    Real.sqrt_le_sqrt hq
  have hspos : 0 < Real.sqrt ‖xiSpectralPoint q‖ := Real.sqrt_pos.2 hp
  rw [div_eq_mul_inv, div_eq_mul_inv]
  field_simp
  exact hs

end
end RHTower
