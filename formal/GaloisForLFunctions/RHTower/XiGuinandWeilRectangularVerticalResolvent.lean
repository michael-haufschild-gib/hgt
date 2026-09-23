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

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

/-- One raw relative-resolvent summand, already multiplied by the squared rectangular test, on the
right vertical edge. -/
def xiRectangularVerticalRawTerm (L a R : ℝ) (q : XiZeroCopy) (y : ℝ) : ℂ :=
  let z : ℂ := (R : ℂ) + y * I
  xiRectangularTwoEdgeTransform L a z ^ (2 : ℕ) *
    (-z / (xiSpectralPoint q * (xiSpectralPoint q - z)))

/-- Explicit numerator in the integrated per-copy vertical-resolvent estimate. -/
def xiRectangularVerticalIntegratedNumerator (L a R : ℝ) : ℝ :=
  ((rectangularTransformStripBound L a 1 ^ (2 : ℕ) / R ^ (2 : ℕ)) * (|R| + 1)) *
      xiVerticalCauchyKernelBound +
    2 * (((8 * rectangularTransformStripBound L a (3 / 2) ^ (2 : ℕ) / R ^ (2 : ℕ)) *
      (|R| + 1)) + rectangularTransformStripBound L a 1 ^ (2 : ℕ) / R ^ (2 : ℕ))

theorem xiRectangularVerticalIntegratedNumerator_nonneg (L a R : ℝ) :
    0 ≤ xiRectangularVerticalIntegratedNumerator L a R := by
  unfold xiRectangularVerticalIntegratedNumerator
  have hC := xiVerticalCauchyKernelBound_nonneg
  have hA : 0 ≤ rectangularTransformStripBound L a 1 ^ (2 : ℕ) / R ^ (2 : ℕ) := by positivity
  have hB : 0 ≤ 8 * rectangularTransformStripBound L a (3 / 2) ^ (2 : ℕ) / R ^ (2 : ℕ) := by
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
  let g : ℂ → ℂ := fun w => xiRectangularTwoEdgeTransform L a w ^ (2 : ℕ)
  let h : ℝ → ℂ := fun y => g (z y) * z y / p
  let M : ℝ :=
    (((8 * rectangularTransformStripBound L a (3 / 2) ^ (2 : ℕ) / R ^ (2 : ℕ)) *
      (|R| + 1)) + rectangularTransformStripBound L a 1 ^ (2 : ℕ) / R ^ (2 : ℕ)) / ‖p‖
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
      _ ≤ (((8 * rectangularTransformStripBound L a (3 / 2) ^ (2 : ℕ) / R ^ (2 : ℕ)) *
          (|R| + 1)) + rectangularTransformStripBound L a 1 ^ (2 : ℕ) / R ^ (2 : ℕ)) /
            ‖p‖ := by
        apply div_le_div_of_nonneg_right _ (norm_nonneg p)
        apply add_le_add
        · exact mul_le_mul hgDeriv hzNorm (norm_nonneg _) (by positivity)
        · simpa only [g, z] using hgValue
      _ = M := rfl
  have hhValue : ‖h p.im‖ ≤
      ((rectangularTransformStripBound L a 1 ^ (2 : ℕ) / R ^ (2 : ℕ)) * (|R| + 1)) / ‖p‖ := by
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
    _ ≤ ((((rectangularTransformStripBound L a 1 ^ (2 : ℕ) / R ^ (2 : ℕ)) * (|R| + 1)) /
          ‖p‖) * xiVerticalCauchyKernelBound) + 2 * M := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hhValue xiVerticalCauchyKernelBound_nonneg) le_rfl
    _ = xiRectangularVerticalIntegratedNumerator L a R / ‖xiSpectralPoint q‖ := by
      dsimp only [M, p]
      unfold xiRectangularVerticalIntegratedNumerator
      field_simp

/-- `R`-independent constant in the integrated per-copy `1/(|R|*|p|)` estimate. -/
def xiRectangularVerticalIntegratedConstant (L a : ℝ) : ℝ :=
  (3 / 2) * rectangularTransformStripBound L a 1 ^ (2 : ℕ) *
      xiVerticalCauchyKernelBound +
    24 * rectangularTransformStripBound L a (3 / 2) ^ (2 : ℕ) +
    rectangularTransformStripBound L a 1 ^ (2 : ℕ)

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
  let A₁ : ℝ := rectangularTransformStripBound L a 1 ^ (2 : ℕ)
  let A₃ : ℝ := rectangularTransformStripBound L a (3 / 2) ^ (2 : ℕ)
  have hRpos : 0 < |R| := lt_of_lt_of_le (by norm_num) hR
  have hA₁ : 0 ≤ A₁ := by dsimp [A₁]; positivity
  have hA₃ : 0 ≤ A₃ := by dsimp [A₃]; positivity
  have hplus : |R| + 1 ≤ (3 / 2 : ℝ) * |R| := by linarith
  have hbase (A : ℝ) (hA : 0 ≤ A) :
      (A / R ^ (2 : ℕ)) * (|R| + 1) ≤ ((3 / 2 : ℝ) * A) / |R| := by
    rw [← sq_abs]
    calc
      A / |R| ^ (2 : ℕ) * (|R| + 1) = A * (|R| + 1) / |R| ^ (2 : ℕ) := by ring
      _ ≤ A * ((3 / 2 : ℝ) * |R|) / |R| ^ (2 : ℕ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hplus hA) (sq_nonneg _)
      _ = ((3 / 2 : ℝ) * A) / |R| := by field_simp
  have hsmall (A : ℝ) (hA : 0 ≤ A) :
      2 * (A / R ^ (2 : ℕ)) ≤ A / |R| := by
    rw [← sq_abs]
    calc
      2 * (A / |R| ^ (2 : ℕ)) = A * (2 / |R| ^ (2 : ℕ)) := by ring
      _ ≤ A * (|R| / |R| ^ (2 : ℕ)) := by
        gcongr
      _ = A / |R| := by field_simp
  have hfirst :
      ((A₁ / R ^ (2 : ℕ)) * (|R| + 1)) * xiVerticalCauchyKernelBound ≤
        (((3 / 2 : ℝ) * A₁) * xiVerticalCauchyKernelBound) / |R| := by
    calc
      ((A₁ / R ^ (2 : ℕ)) * (|R| + 1)) * xiVerticalCauchyKernelBound ≤
          (((3 / 2 : ℝ) * A₁) / |R|) * xiVerticalCauchyKernelBound :=
        mul_le_mul_of_nonneg_right (hbase A₁ hA₁) xiVerticalCauchyKernelBound_nonneg
      _ = (((3 / 2 : ℝ) * A₁) * xiVerticalCauchyKernelBound) / |R| := by ring
  have hmiddle :
      2 * (((8 * A₃ / R ^ (2 : ℕ)) * (|R| + 1))) ≤ 24 * A₃ / |R| := by
    have hb := hbase (8 * A₃) (mul_nonneg (by norm_num) hA₃)
    calc
      2 * ((8 * A₃ / R ^ (2 : ℕ)) * (|R| + 1)) ≤
          2 * (((3 / 2 : ℝ) * (8 * A₃)) / |R|) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = 24 * A₃ / |R| := by ring
  have hlast : 2 * (A₁ / R ^ (2 : ℕ)) ≤ A₁ / |R| := hsmall A₁ hA₁
  have hsecond :
      2 * (((8 * A₃ / R ^ (2 : ℕ)) * (|R| + 1)) + A₁ / R ^ (2 : ℕ)) ≤
        24 * A₃ / |R| + A₁ / |R| := by
    rw [mul_add]
    exact add_le_add hmiddle hlast
  unfold xiRectangularVerticalIntegratedNumerator
  unfold xiRectangularVerticalIntegratedConstant
  change ((A₁ / R ^ (2 : ℕ)) * (|R| + 1)) * xiVerticalCauchyKernelBound +
      2 * (((8 * A₃ / R ^ (2 : ℕ)) * (|R| + 1)) + A₁ / R ^ (2 : ℕ)) ≤ _
  calc
    ((A₁ / R ^ (2 : ℕ)) * (|R| + 1)) * xiVerticalCauchyKernelBound +
        2 * (((8 * A₃ / R ^ (2 : ℕ)) * (|R| + 1)) + A₁ / R ^ (2 : ℕ)) ≤
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
      3 * rectangularTransformStripBound L a 1 ^ (2 : ℕ) /
        (|R| * ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  let p : ℂ := xiSpectralPoint q
  let z : ℂ := (R : ℂ) + y * I
  let A : ℝ := rectangularTransformStripBound L a 1 ^ (2 : ℕ)
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
  have hg : ‖xiRectangularTwoEdgeTransform L a z ^ (2 : ℕ)‖ ≤ A / |R| ^ (2 : ℕ) := by
    have hraw := norm_xiRectangularTwoEdgeTransform_vertical_sq_le
      L a R y hRpos hy
    simpa only [z, A, sq_abs] using hraw
  have hnum :
      ‖xiRectangularTwoEdgeTransform L a z ^ (2 : ℕ)‖ * ‖z‖ ≤
        (A / |R| ^ (2 : ℕ)) * ((3 / 2 : ℝ) * |R|) :=
    mul_le_mul hg hz' (norm_nonneg _) (by positivity)
  have hden : ‖p‖ * (‖p‖ / 2) ≤ ‖p‖ * ‖p - z‖ :=
    mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)
  unfold xiRectangularVerticalRawTerm
  dsimp only [z, p, A]
  rw [norm_mul, norm_div, norm_neg, norm_mul]
  rw [← mul_div_assoc]
  calc
    ‖xiRectangularTwoEdgeTransform L a z ^ (2 : ℕ)‖ * ‖z‖ /
        (‖p‖ * ‖p - z‖) ≤
      ((A / |R| ^ (2 : ℕ)) * ((3 / 2 : ℝ) * |R|)) /
        (‖p‖ * ‖p - z‖) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ ((A / |R| ^ (2 : ℕ)) * ((3 / 2 : ℝ) * |R|)) /
        (‖p‖ * (‖p‖ / 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 3 * (A / (|R| * ‖p‖ ^ (2 : ℕ))) := by field_simp
    _ = 3 * rectangularTransformStripBound L a 1 ^ (2 : ℕ) /
        (|R| * ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by dsimp only [A, p]; ring

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
      (fun y : ℝ => xiRectangularTwoEdgeTransform L a (z y) ^ (2 : ℕ))
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
      6 * rectangularTransformStripBound L a 1 ^ (2 : ℕ) /
        (|R| * ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
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
  let C : ℝ := 3 * rectangularTransformStripBound L a 1 ^ (2 : ℕ) /
    (|R| * ‖xiSpectralPoint q‖ ^ (2 : ℕ))
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
    _ = 6 * rectangularTransformStripBound L a 1 ^ (2 : ℕ) /
        (|R| * ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
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

/-- **Quantitative vertical-edge spectral law.**  After integration, the complete exact-
multiplicity Xi resolvent is absolutely summable.  Its norm is controlled by an `R⁻¹/²`
reciprocal-`3/2` near-spectrum term plus an `R⁻¹` reciprocal-square far-spectrum term. -/
theorem summable_integral_xiRectangularVerticalRawTerm_and_norm_tsum_le
    (L a R : ℝ) (hR : 2 ≤ |R|)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    Summable (fun q : XiZeroCopy =>
        ∫ y in (-1 : ℝ)..1, xiRectangularVerticalRawTerm L a R q y) ∧
      ‖∑' q : XiZeroCopy,
          ∫ y in (-1 : ℝ)..1, xiRectangularVerticalRawTerm L a R q y‖ ≤
        (xiRectangularVerticalIntegratedConstant L a * Real.sqrt (3 * |R|) / |R|) *
            (∑' q : XiZeroCopy,
              1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)) +
          (6 * rectangularTransformStripBound L a 1 ^ (2 : ℕ) / |R|) *
            (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
  let T : XiZeroCopy → ℂ := fun q =>
    ∫ y in (-1 : ℝ)..1, xiRectangularVerticalRawTerm L a R q y
  let w₃ : XiZeroCopy → ℝ := fun q =>
    1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)
  let w₂ : XiZeroCopy → ℝ := fun q => 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)
  let K : ℝ := xiRectangularVerticalIntegratedConstant L a
  let A : ℝ := rectangularTransformStripBound L a 1 ^ (2 : ℕ)
  let c₃ : ℝ := K * Real.sqrt (3 * |R|) / |R|
  let c₂ : ℝ := 6 * A / |R|
  have hRpos : 0 < |R| := lt_of_lt_of_le (by norm_num) hR
  have hK : 0 ≤ K := by
    dsimp only [K]
    exact xiRectangularVerticalIntegratedConstant_nonneg L a
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hc₃ : 0 ≤ c₃ := by dsimp only [c₃]; positivity
  have hc₂ : 0 ≤ c₂ := by dsimp only [c₂]; positivity
  have hw₃ : Summable w₃ := by
    simpa only [w₃] using xiSpectralPoint_inv_three_halves_summable
  have hw₂ : Summable w₂ := by
    simpa only [w₂] using xiSpectralPoint_inv_sq_summable
  have hsum₃ : Summable (fun q => c₃ * w₃ q) := hw₃.mul_left c₃
  have hsum₂ : Summable (fun q => c₂ * w₂ q) := hw₂.mul_left c₂
  have hmajorant : Summable (fun q => c₃ * w₃ q + c₂ * w₂ q) :=
    hsum₃.add hsum₂
  have hbound : ∀ q : XiZeroCopy, ‖T q‖ ≤ c₃ * w₃ q + c₂ * w₂ q := by
    intro q
    have hp : 0 < ‖xiSpectralPoint q‖ :=
      norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
    by_cases hnear : ‖xiSpectralPoint q‖ ≤ 3 * |R|
    · have hinv := one_div_norm_le_sqrt_mul_one_div_norm_sqrt_norm q hnear
      have hscale : 0 ≤ K / |R| := div_nonneg hK hRpos.le
      calc
        ‖T q‖ ≤ K / (|R| * ‖xiSpectralPoint q‖) := by
          simpa only [T, K] using
            norm_integral_xiRectangularVerticalRawTerm_le_inv_norm
              L a R hR q (havoid q)
        _ = (K / |R|) * (1 / ‖xiSpectralPoint q‖) := by ring
        _ ≤ (K / |R|) *
            (Real.sqrt (3 * |R|) * w₃ q) := by
          exact mul_le_mul_of_nonneg_left (by simpa only [w₃] using hinv) hscale
        _ = c₃ * w₃ q := by dsimp only [c₃]; ring
        _ ≤ c₃ * w₃ q + c₂ * w₂ q :=
          le_add_of_nonneg_right (mul_nonneg hc₂ (by dsimp only [w₂]; positivity))
    · have hfar : 3 * |R| ≤ ‖xiSpectralPoint q‖ := le_of_lt (lt_of_not_ge hnear)
      calc
        ‖T q‖ ≤
            ∫ y in (-1 : ℝ)..1, ‖xiRectangularVerticalRawTerm L a R q y‖ := by
          simpa only [T] using
            (intervalIntegral.norm_integral_le_integral_norm
              (show (-1 : ℝ) ≤ 1 by norm_num) :
              ‖∫ y in (-1 : ℝ)..1, xiRectangularVerticalRawTerm L a R q y‖ ≤
                ∫ y in (-1 : ℝ)..1, ‖xiRectangularVerticalRawTerm L a R q y‖)
        _ ≤ 6 * A / (|R| * ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
          simpa only [A] using
            integral_norm_xiRectangularVerticalRawTerm_le_inv_sq L a R hR q hfar
        _ = c₂ * w₂ q := by dsimp only [c₂, w₂]; ring
        _ ≤ c₃ * w₃ q + c₂ * w₂ q :=
          le_add_of_nonneg_left (mul_nonneg hc₃ (by dsimp only [w₃]; positivity))
  have hT : Summable T := hmajorant.of_norm_bounded hbound
  refine ⟨by simpa only [T] using hT, ?_⟩
  calc
    ‖∑' q : XiZeroCopy, ∫ y in (-1 : ℝ)..1,
        xiRectangularVerticalRawTerm L a R q y‖ = ‖∑' q, T q‖ := by rfl
    _ ≤ ∑' q, ‖T q‖ := norm_tsum_le_tsum_norm hT.norm
    _ ≤ ∑' q, (c₃ * w₃ q + c₂ * w₂ q) :=
      Summable.tsum_mono hT.norm hmajorant hbound
    _ = c₃ * (∑' q, w₃ q) + c₂ * (∑' q, w₂ q) := by
      rw [hsum₃.tsum_add hsum₂, tsum_mul_left, tsum_mul_left]
    _ =
        (xiRectangularVerticalIntegratedConstant L a * Real.sqrt (3 * |R|) / |R|) *
            (∑' q : XiZeroCopy,
              1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)) +
          (6 * rectangularTransformStripBound L a 1 ^ (2 : ℕ) / |R|) *
            (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
      rfl

/-- The explicit mixed reciprocal-moment majorant for the integrated vertical edge tends to zero
at positive infinity. -/
theorem tendsto_xiRectangularVerticalIntegratedMajorant_atTop (L a : ℝ) :
    Tendsto
      (fun R : ℝ =>
        (xiRectangularVerticalIntegratedConstant L a * Real.sqrt (3 * R) / R) *
            (∑' q : XiZeroCopy,
              1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)) +
          (6 * rectangularTransformStripBound L a 1 ^ (2 : ℕ) / R) *
            (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)))
      atTop (𝓝 0) := by
  let S₃ : ℝ := ∑' q : XiZeroCopy,
    1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)
  let S₂ : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)
  let K : ℝ := xiRectangularVerticalIntegratedConstant L a
  let A : ℝ := rectangularTransformStripBound L a 1 ^ (2 : ℕ)
  have hsqrtInv : Tendsto (fun R : ℝ => (Real.sqrt R)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hsqrtRate : Tendsto (fun R : ℝ => Real.sqrt (3 * R) / R) atTop (𝓝 0) := by
    have hlim : Tendsto (fun R : ℝ => Real.sqrt 3 * (Real.sqrt R)⁻¹)
        atTop (𝓝 0) := by
      simpa using tendsto_const_nhds.mul hsqrtInv
    apply hlim.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    field_simp [Real.sqrt_ne_zero'.mpr hR]
    rw [Real.sq_sqrt hR.le]
  have hone : Tendsto (fun R : ℝ => 1 / R) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_inv_atTop_zero :
      Tendsto (fun R : ℝ => R⁻¹) atTop (𝓝 0))
  have hfirst : Tendsto
      (fun R : ℝ => (K * (Real.sqrt (3 * R) / R)) * S₃) atTop (𝓝 0) := by
    simpa using (hsqrtRate.const_mul K).mul_const S₃
  have hsecond : Tendsto
      (fun R : ℝ => ((6 * A) * (1 / R)) * S₂) atTop (𝓝 0) := by
    simpa using (hone.const_mul (6 * A)).mul_const S₂
  dsimp only [K, A, S₃, S₂] at hfirst hsecond ⊢
  convert hfirst.add hsecond using 1
  · funext R
    ring
  · norm_num

/-- Every nondegenerate real interval contains a vertical coordinate avoiding every Xi spectral
real coordinate, with exact multiplicity irrelevant to the avoidance set. -/
theorem exists_real_avoiding_all_xiSpectralPoint_re {u v : ℝ} (huv : u < v) :
    ∃ R ∈ Ioo u v, ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re := by
  let S : Set ℝ := Set.range (fun q : XiZeroCopy => (xiSpectralPoint q).re)
  have hScount : S.Countable := Set.countable_range _
  have hex : ∃ R ∈ Ioo u v, R ∉ S := by
    by_contra hnone
    push Not at hnone
    have hIcount : (Ioo u v).Countable := hScount.mono (fun R hR => hnone R hR)
    have hle : v ≤ u :=
      (Cardinal.Real.Ioo_countable_iff (x := u) (y := v)).mp hIcount
    exact not_le.mpr huv hle
  obtain ⟨R, hRI, hRavoid⟩ := hex
  refine ⟨R, hRI, ?_⟩
  intro q heq
  exact hRavoid ⟨q, heq.symm⟩

/-- **Cofinal integrated vertical-edge vanishing.**  Beyond every requested height, there is an
edge avoiding the Xi divisor on which the complete integrated relative-resolvent contribution is
absolutely summable and smaller than any prescribed positive tolerance. -/
theorem exists_large_integrated_xiRectangularVerticalRawTerm_tsum_lt
    (L a X : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ R : ℝ,
      X < R ∧
      2 ≤ R ∧
      (∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) ∧
      Summable (fun q : XiZeroCopy =>
        ∫ y in (-1 : ℝ)..1, xiRectangularVerticalRawTerm L a R q y) ∧
      ‖∑' q : XiZeroCopy,
          ∫ y in (-1 : ℝ)..1, xiRectangularVerticalRawTerm L a R q y‖ < epsilon := by
  have hevent :=
    (tendsto_xiRectangularVerticalIntegratedMajorant_atTop L a).eventually_lt_const
      hepsilon
  obtain ⟨M, hM⟩ := eventually_atTop.1 hevent
  let u : ℝ := max (max X 2) M
  obtain ⟨R, hRI, havoid⟩ :=
    exists_real_avoiding_all_xiSpectralPoint_re
      (show u < u + 1 by linarith)
  have hXu : X ≤ u := by
    dsimp only [u]
    exact le_trans (le_max_left X 2) (le_max_left (max X 2) M)
  have h2u : 2 ≤ u := by
    dsimp only [u]
    exact le_trans (le_max_right X 2) (le_max_left (max X 2) M)
  have hMu : M ≤ u := by
    dsimp only [u]
    exact le_max_right (max X 2) M
  have hXR : X < R := lt_of_le_of_lt hXu hRI.1
  have hR : 2 ≤ R := le_trans h2u (le_of_lt hRI.1)
  have hMR : M ≤ R := le_trans hMu (le_of_lt hRI.1)
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  obtain ⟨hsum, hbound⟩ :=
    summable_integral_xiRectangularVerticalRawTerm_and_norm_tsum_le
      L a R (by simpa only [abs_of_pos hRpos] using hR) havoid
  have hsmall :
      ‖∑' q : XiZeroCopy,
          ∫ y in (-1 : ℝ)..1, xiRectangularVerticalRawTerm L a R q y‖ < epsilon := by
    rw [abs_of_pos hRpos] at hbound
    exact lt_of_le_of_lt hbound (hM R hMR)
  exact ⟨R, hXR, hR, havoid, hsum, hsmall⟩

/-- On every divisor-avoiding edge, absolute integrability of the far spectrum and finiteness of
the near spectrum justify exchanging the exact-multiplicity Xi sum with the vertical integral. -/
theorem integral_tsum_xiRectangularVerticalRawTerm_eq_tsum_integral
    (L a R : ℝ) (hR : 2 ≤ |R|)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    (∫ y in (-1 : ℝ)..1,
        ∑' q : XiZeroCopy, xiRectangularVerticalRawTerm L a R q y) =
      ∑' q : XiZeroCopy,
        ∫ y in (-1 : ℝ)..1, xiRectangularVerticalRawTerm L a R q y := by
  let A : ℝ := rectangularTransformStripBound L a 1 ^ (2 : ℕ)
  let b : XiZeroCopy → ℝ := fun q =>
    6 * A / (|R| * ‖xiSpectralPoint q‖ ^ (2 : ℕ))
  have hRpos : 0 < |R| := lt_of_lt_of_le (by norm_num) hR
  have hb : Summable b := by
    have hscaled := xiSpectralPoint_inv_sq_summable.mul_left (6 * A / |R|)
    refine hscaled.congr (fun q => ?_)
    dsimp only [b]
    ring
  have hfarEventually :
      ∀ᶠ q : XiZeroCopy in Filter.cofinite,
        3 * |R| ≤ ‖xiSpectralPoint q‖ := by
    have hfinite := xiSpectralPoint_finite_norm_le
      (B := 3 * |R|) (by positivity)
    have houtside :
        ∀ᶠ q : XiZeroCopy in Filter.cofinite,
          3 * |R| < ‖xiSpectralPoint q‖ := by
      simpa only [Set.compl_setOf, Set.mem_setOf_eq, not_le] using!
        hfinite.compl_mem_cofinite
    filter_upwards [houtside] with q hq
    exact le_of_lt hq
  have hnormSum : Summable (fun q : XiZeroCopy =>
      ∫ y in (-1 : ℝ)..1, ‖xiRectangularVerticalRawTerm L a R q y‖) := by
    apply hb.of_norm_bounded_eventually
    filter_upwards [hfarEventually] with q hfar
    have hnonneg : 0 ≤
        ∫ y in (-1 : ℝ)..1, ‖xiRectangularVerticalRawTerm L a R q y‖ :=
      intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simpa only [b, A] using
      integral_norm_xiRectangularVerticalRawTerm_le_inv_sq L a R hR q hfar
  have hFint : ∀ q : XiZeroCopy,
      Integrable (xiRectangularVerticalRawTerm L a R q)
        (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    intro q
    have hcont := continuousOn_xiRectangularVerticalRawTerm L a R q (havoid q)
    have hcontu : ContinuousOn (xiRectangularVerticalRawTerm L a R q)
        (uIcc (-1 : ℝ) 1) := by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hcont
    have hint : IntervalIntegrable (xiRectangularVerticalRawTerm L a R q)
        volume (-1 : ℝ) 1 := hcontu.intervalIntegrable
    rw [intervalIntegrable_iff] at hint
    simpa only [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using! hint
  have hnormSumRestrict : Summable (fun q : XiZeroCopy =>
      ∫ y in Ioc (-1 : ℝ) 1, ‖xiRectangularVerticalRawTerm L a R q y‖) := by
    apply hnormSum.congr
    intro q
    exact intervalIntegral.integral_of_le (by norm_num)
  rw [intervalIntegral.integral_of_le (by norm_num)]
  calc
    (∫ y in Ioc (-1 : ℝ) 1,
        ∑' q : XiZeroCopy, xiRectangularVerticalRawTerm L a R q y) =
      ∑' q : XiZeroCopy,
        ∫ y in Ioc (-1 : ℝ) 1, xiRectangularVerticalRawTerm L a R q y :=
      (MeasureTheory.integral_tsum_of_summable_integral_norm hFint
        hnormSumRestrict).symm
    _ = ∑' q : XiZeroCopy,
        ∫ y in (-1 : ℝ)..1, xiRectangularVerticalRawTerm L a R q y := by
      apply tsum_congr
      intro q
      exact (intervalIntegral.integral_of_le (by norm_num)).symm

/-- Pointwise on a divisor-avoiding edge, the raw spectral sum is exactly the squared rectangular
test multiplied by the canonical Xi relative-resolvent trace. -/
theorem tsum_xiRectangularVerticalRawTerm_eq_mul_relativeResolventTrace
    (L a R y : ℝ)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    (∑' q : XiZeroCopy, xiRectangularVerticalRawTerm L a R q y) =
      xiRectangularTwoEdgeTransform L a ((R : ℂ) + y * I) ^ (2 : ℕ) *
        xiRelativeResolventTrace ((R : ℂ) + y * I) := by
  let z : ℂ := (R : ℂ) + y * I
  let g : ℂ := xiRectangularTwoEdgeTransform L a z ^ (2 : ℕ)
  let t : XiZeroCopy → ℂ := fun q =>
    -z / (xiSpectralPoint q * (xiSpectralPoint q - z))
  have hzq : ∀ q : XiZeroCopy, z ≠ xiSpectralPoint q := by
    intro q heq
    have hre := congrArg Complex.re heq
    simp only [z, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, zero_mul,
      mul_zero, sub_self, add_zero] at hre
    exact havoid q hre
  have hterm : ∀ q : XiZeroCopy, xiRelativeResolventTerm z q = t q := by
    intro q
    have hp := xiSpectralPoint_ne_zero q
    have hpz : xiSpectralPoint q - z ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hzq q))
    rw [xiRelativeResolventTerm, inv_eq_one_div]
    dsimp only [t]
    field_simp [hp, hpz]
    ring
  have htrace : (∑' q : XiZeroCopy, t q) = xiRelativeResolventTrace z := by
    rw [xiRelativeResolventTrace]
    apply tsum_congr
    intro q
    exact (hterm q).symm
  calc
    (∑' q : XiZeroCopy, xiRectangularVerticalRawTerm L a R q y) =
        ∑' q : XiZeroCopy, g * t q := by
      apply tsum_congr
      intro q
      rfl
    _ = g * (∑' q : XiZeroCopy, t q) := tsum_mul_left
    _ = g * xiRelativeResolventTrace z := by rw [htrace]
    _ = xiRectangularTwoEdgeTransform L a ((R : ℂ) + y * I) ^ (2 : ℕ) *
        xiRelativeResolventTrace ((R : ℂ) + y * I) := by rfl

/-- Exact integrated vertical-edge identity for the full Xi relative trace. -/
theorem integral_mul_xiRelativeResolventTrace_eq_tsum_integral_rawTerm
    (L a R : ℝ) (hR : 2 ≤ |R|)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    (∫ y in (-1 : ℝ)..1,
        xiRectangularTwoEdgeTransform L a ((R : ℂ) + y * I) ^ (2 : ℕ) *
          xiRelativeResolventTrace ((R : ℂ) + y * I)) =
      ∑' q : XiZeroCopy,
        ∫ y in (-1 : ℝ)..1, xiRectangularVerticalRawTerm L a R q y := by
  calc
    (∫ y in (-1 : ℝ)..1,
        xiRectangularTwoEdgeTransform L a ((R : ℂ) + y * I) ^ (2 : ℕ) *
          xiRelativeResolventTrace ((R : ℂ) + y * I)) =
      ∫ y in (-1 : ℝ)..1,
        ∑' q : XiZeroCopy, xiRectangularVerticalRawTerm L a R q y := by
      apply integral_congr
      intro y hy
      exact (tsum_xiRectangularVerticalRawTerm_eq_mul_relativeResolventTrace
        L a R y havoid).symm
    _ = ∑' q : XiZeroCopy,
        ∫ y in (-1 : ℝ)..1, xiRectangularVerticalRawTerm L a R q y :=
      integral_tsum_xiRectangularVerticalRawTerm_eq_tsum_integral
        L a R hR havoid

/-- **Full cofinal vertical-edge vanishing theorem.**  The actual squared-rectangular Xi relative
trace, not merely its termwise surrogate, has arbitrarily remote divisor-avoiding vertical edges
whose integrated contribution is arbitrarily small. -/
theorem exists_large_integral_rectangular_mul_xiRelativeResolventTrace_norm_lt
    (L a X : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ R : ℝ,
      X < R ∧
      2 ≤ R ∧
      (∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) ∧
      ‖∫ y in (-1 : ℝ)..1,
          xiRectangularTwoEdgeTransform L a ((R : ℂ) + y * I) ^ (2 : ℕ) *
            xiRelativeResolventTrace ((R : ℂ) + y * I)‖ < epsilon := by
  obtain ⟨R, hXR, hR, havoid, hsum, hsmall⟩ :=
    exists_large_integrated_xiRectangularVerticalRawTerm_tsum_lt
      L a X hepsilon
  have hRpos : 0 < R := lt_of_lt_of_le (by norm_num) hR
  have hedge := integral_mul_xiRelativeResolventTrace_eq_tsum_integral_rawTerm
    L a R (by simpa only [abs_of_pos hRpos] using hR) havoid
  refine ⟨R, hXR, hR, havoid, ?_⟩
  rw [hedge]
  exact hsmall

/-- Avoiding every spectral real coordinate makes `XiC` nonzero at every point of the vertical
edge. -/
theorem XiC_ne_zero_on_avoiding_vertical
    (R y : ℝ) (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    XiC ((R : ℂ) + y * I) ≠ 0 := by
  intro hzero
  obtain ⟨q, hq⟩ :=
    (XiC_eq_zero_iff_exists_xiZeroCopy ((R : ℂ) + y * I)).mp hzero
  have hre := congrArg Complex.re hq
  simp only [add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, zero_mul,
    mul_zero, sub_self, add_zero] at hre
  exact havoid q hre.symm

/-- On a divisor-avoiding edge, the actual centered Xi logarithmic derivative equals its
canonical relative-resolvent trace under the vertical integral. -/
theorem integral_rectangular_mul_logDeriv_XiC_eq_relativeResolventTrace
    (L a R : ℝ) (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    (∫ y in (-1 : ℝ)..1,
        xiRectangularTwoEdgeTransform L a ((R : ℂ) + y * I) ^ (2 : ℕ) *
          logDeriv XiC ((R : ℂ) + y * I)) =
      ∫ y in (-1 : ℝ)..1,
        xiRectangularTwoEdgeTransform L a ((R : ℂ) + y * I) ^ (2 : ℕ) *
          xiRelativeResolventTrace ((R : ℂ) + y * I) := by
  apply integral_congr
  intro y hy
  dsimp only
  rw [logDeriv_XiC_eq_relativeResolventTrace
    (XiC_ne_zero_on_avoiding_vertical R y havoid)]

/-- **Logarithmic-derivative vertical hypothesis discharged.**  The exact vertical term in the
symmetric Guinand--Weil Xi contour has arbitrarily remote divisor-avoiding edges of arbitrarily
small norm. -/
theorem exists_large_integral_rectangular_mul_logDeriv_XiC_norm_lt
    (L a X : ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∃ R : ℝ,
      X < R ∧
      2 ≤ R ∧
      (∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) ∧
      ‖∫ y in (-1 : ℝ)..1,
          xiRectangularTwoEdgeTransform L a ((R : ℂ) + y * I) ^ (2 : ℕ) *
            logDeriv XiC ((R : ℂ) + y * I)‖ < epsilon := by
  obtain ⟨R, hXR, hR, havoid, hsmall⟩ :=
    exists_large_integral_rectangular_mul_xiRelativeResolventTrace_norm_lt
      L a X hepsilon
  refine ⟨R, hXR, hR, havoid, ?_⟩
  rw [integral_rectangular_mul_logDeriv_XiC_eq_relativeResolventTrace
    L a R havoid]
  exact hsmall

end
end RHTower
