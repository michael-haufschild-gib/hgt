import GaloisForLFunctions.RHTower.XiGaussianCompletedSourceFormula
import GaloisForLFunctions.RHTower.XiGuinandWeilRectangularVerticalResolvent

/-!
# Gaussian Xi resolvent decay on divisor-avoiding vertical edges

Pointwise control of `logDeriv XiC` cannot survive an edge approaching a Xi zero.  This module
instead integrates each centered relative-resolvent summand against the Gaussian--Hermite test.
The uniform integrated Cauchy estimate controls the near spectrum with reciprocal-`3/2`
summability; Gaussian decay controls the far spectrum with reciprocal-square summability.
-/

open Complex Filter intervalIntegral MeasureTheory Set Topology

namespace RHTower

noncomputable section

theorem hasDerivAt_xiGaussianTestC (t : ℝ) (k : ℕ) (z : ℂ) :
    HasDerivAt (xiGaussianTestC t k)
      (((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) * Complex.exp (-(t : ℂ) * z ^ 2) +
        z ^ (2 * k) *
          (Complex.exp (-(t : ℂ) * z ^ 2) * (-(t : ℂ) * (2 * z)))) z := by
  unfold xiGaussianTestC
  have hpow := (hasDerivAt_id z).pow (2 * k)
  have hsq := (hasDerivAt_id z).pow 2
  have hinner := (hasDerivAt_const z (-(t : ℂ))).mul hsq
  have hexp := (Complex.hasDerivAt_exp (-(t : ℂ) * z ^ 2)).comp z hinner
  let F : ℂ → ℂ :=
    (id ^ (2 * k)) * (Complex.exp ∘ ((fun _ : ℂ => -(t : ℂ)) * id ^ 2))
  have hF : F = fun w : ℂ => w ^ (2 * k) * Complex.exp (-(t : ℂ) * w ^ 2) := by
    funext w
    simp [F, Function.comp_apply]
  rw [← hF]
  have hraw := hpow.mul hexp
  change HasDerivAt F _ z at hraw
  convert hraw using 1
  simp [Function.comp_apply]

private theorem norm_xiGaussianVerticalPoint_le (R y : ℝ) (hy : |y| ≤ 1) :
    ‖(R : ℂ) + y * I‖ ≤ 1 + |R| := by
  calc
    ‖(R : ℂ) + y * I‖ ≤ ‖(R : ℂ)‖ + ‖(y : ℂ) * I‖ := norm_add_le _ _
    _ = |R| + |y| := by simp
    _ ≤ 1 + |R| := by linarith

theorem norm_xiGaussianTestC_vertical_le
    {t : ℝ} (ht : 0 < t) (k : ℕ) (R y : ℝ) (hy : |y| ≤ 1) :
    ‖xiGaussianTestC t k ((R : ℂ) + y * I)‖ ≤
      Real.exp t * (1 + |R|) ^ (2 * k) * Real.exp (-(t * R ^ 2)) := by
  rw [norm_xiGaussianTestC_eq_norm_rotated]
  have hbound := norm_xiGaussianTest_le_of_strip ht k (R := 1)
    (s := (((1 / 2 - y : ℝ) : ℂ) + (R : ℂ) * I))
    (by norm_num) (by simpa [abs_le] using hy)
  simpa [Complex.add_im, Complex.mul_im, mul_comm, mul_left_comm, mul_assoc] using hbound

theorem norm_deriv_xiGaussianTestC_vertical_le
    {t : ℝ} (ht : 0 < t) (k : ℕ) (R y : ℝ) (hy : |y| ≤ 1) :
    ‖deriv (xiGaussianTestC t k) ((R : ℂ) + y * I)‖ ≤
      Real.exp t * (((2 * k : ℕ) : ℝ) + 2 * t) *
        (1 + |R|) ^ (2 * k + 1) * Real.exp (-(t * R ^ 2)) := by
  let z : ℂ := (R : ℂ) + y * I
  let B : ℝ := 1 + |R|
  let E : ℝ := Real.exp t * Real.exp (-(t * R ^ 2))
  have hB : 1 ≤ B := by dsimp only [B]; linarith [abs_nonneg R]
  have hz : ‖z‖ ≤ B := by
    simpa only [z, B] using norm_xiGaussianVerticalPoint_le R y hy
  have hexp : ‖Complex.exp (-(t : ℂ) * z ^ 2)‖ ≤ E := by
    have hzero := norm_xiGaussianTestC_vertical_le ht 0 R y hy
    simpa [xiGaussianTestC, z, E] using hzero
  rw [(hasDerivAt_xiGaussianTestC t k z).deriv]
  calc
    ‖(((2 * k : ℕ) : ℂ) * z ^ (2 * k - 1) *
          Complex.exp (-(t : ℂ) * z ^ 2) +
        z ^ (2 * k) *
          (Complex.exp (-(t : ℂ) * z ^ 2) * (-(t : ℂ) * (2 * z))))‖ ≤
        ((((2 * k : ℕ) : ℝ) * B ^ (2 * k - 1) * E) +
          (B ^ (2 * k) * (E * (t * (2 * B))))) := by
      apply (norm_add_le _ _).trans
      apply add_le_add
      · rw [norm_mul, norm_mul, norm_natCast, norm_pow]
        gcongr
      · rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_pow, norm_neg,
          norm_real, Real.norm_eq_abs, norm_ofNat, abs_of_nonneg ht.le]
        gcongr
    _ ≤ (((2 * k : ℕ) : ℝ) + 2 * t) * B ^ (2 * k + 1) * E := by
      have hpowLow : B ^ (2 * k - 1) ≤ B ^ (2 * k + 1) := by
        exact (pow_le_pow_right₀ hB (Nat.sub_le (2 * k) 1)).trans
          (pow_le_pow_right₀ hB (by omega))
      have hE : 0 ≤ E := by dsimp only [E]; positivity
      calc
        ((2 * k : ℕ) : ℝ) * B ^ (2 * k - 1) * E +
            B ^ (2 * k) * (E * (t * (2 * B))) ≤
          ((2 * k : ℕ) : ℝ) * B ^ (2 * k + 1) * E +
            B ^ (2 * k) * (E * (t * (2 * B))) := by
              gcongr
        _ = ((2 * k : ℕ) : ℝ) * B ^ (2 * k + 1) * E +
            (2 * t) * B ^ (2 * k + 1) * E := by
              rw [pow_succ']
              ring
        _ = (((2 * k : ℕ) : ℝ) + 2 * t) * B ^ (2 * k + 1) * E := by ring
    _ = Real.exp t * (((2 * k : ℕ) : ℝ) + 2 * t) *
        (1 + |R|) ^ (2 * k + 1) * Real.exp (-(t * R ^ 2)) := by
      dsimp only [B, E]
      ring

/-- One centered relative-resolvent summand weighted by a Gaussian--Hermite test. -/
def xiGaussianVerticalRawTerm (t : ℝ) (k : ℕ) (R : ℝ)
    (q : XiZeroCopy) (y : ℝ) : ℂ :=
  let z : ℂ := (R : ℂ) + y * I
  xiGaussianTestC t k z *
    (-z / (xiSpectralPoint q * (xiSpectralPoint q - z)))

/-- Gaussian numerator in the uniform integrated per-copy Cauchy estimate. -/
def xiGaussianVerticalIntegratedNumerator (t : ℝ) (k : ℕ) (R : ℝ) : ℝ :=
  Real.exp t *
    (xiVerticalCauchyKernelBound + 2 * (((2 * k : ℕ) : ℝ) + 2 * t + 1)) *
    (1 + |R|) ^ (2 * k + 2) * Real.exp (-(t * R ^ 2))

theorem xiGaussianVerticalIntegratedNumerator_nonneg
    {t : ℝ} (ht : 0 < t) (k : ℕ) (R : ℝ) :
    0 ≤ xiGaussianVerticalIntegratedNumerator t k R := by
  unfold xiGaussianVerticalIntegratedNumerator
  have hC := xiVerticalCauchyKernelBound_nonneg
  positivity

/-- Uniform integrated Cauchy control for one exact Xi divisor copy. -/
theorem norm_integral_xiGaussianVerticalRawTerm_le
    {t : ℝ} (ht : 0 < t) (k : ℕ) (R : ℝ) (q : XiZeroCopy)
    (havoid : R ≠ (xiSpectralPoint q).re) :
    ‖∫ y in (-1 : ℝ)..1, xiGaussianVerticalRawTerm t k R q y‖ ≤
      xiGaussianVerticalIntegratedNumerator t k R / ‖xiSpectralPoint q‖ := by
  let p : ℂ := xiSpectralPoint q
  let z : ℝ → ℂ := fun y => (R : ℂ) + y * I
  let g : ℂ → ℂ := xiGaussianTestC t k
  let h : ℝ → ℂ := fun y => g (z y) * z y / p
  let B : ℝ := 1 + |R|
  let E : ℝ := Real.exp t * Real.exp (-(t * R ^ 2))
  let A : ℝ := ((2 * k : ℕ) : ℝ) + 2 * t
  let M : ℝ := E * (A + 1) * B ^ (2 * k + 2) / ‖p‖
  have hp0 : p ≠ 0 := xiSpectralPoint_ne_zero q
  have hpNorm : 0 < ‖p‖ := norm_pos_iff.mpr hp0
  have hpim := xiSpectralPoint_im_mem_openHalf q
  have hB : 1 ≤ B := by dsimp only [B]; linarith [abs_nonneg R]
  have hB0 : 0 ≤ B := le_trans (by norm_num) hB
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hgdiff : Differentiable ℂ g := differentiable_xiGaussianTestC t k
  have hzDeriv (y : ℝ) : HasDerivAt z I y := by
    dsimp only [z]
    have hmul : HasDerivAt (fun x : ℝ => (x : ℂ) * I) I y := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const I
    simpa using hmul.const_add (R : ℂ)
  have hhDeriv (y : ℝ) : HasDerivAt h
      (((deriv g (z y) * I) * z y + g (z y) * I) / p) y := by
    dsimp only [h]
    exact (((hgdiff (z y)).hasDerivAt.comp y (hzDeriv y)).mul (hzDeriv y)).div_const p
  have hdiff : ∀ y ∈ Icc (-1 : ℝ) 1, DifferentiableAt ℝ h y := by
    intro y hy
    exact (hhDeriv y).differentiableAt
  have hderiv : ∀ y ∈ Icc (-1 : ℝ) 1, ‖deriv h y‖ ≤ M := by
    intro y hy
    have hyAbs : |y| ≤ 1 := (abs_le).2 hy
    have hgValue0 := norm_xiGaussianTestC_vertical_le ht k R y hyAbs
    have hgValue : ‖g (z y)‖ ≤ E * B ^ (2 * k) := by
      dsimp only [g, z, E, B]
      nlinarith
    have hgDeriv0 := norm_deriv_xiGaussianTestC_vertical_le ht k R y hyAbs
    have hgDeriv : ‖deriv g (z y)‖ ≤ E * A * B ^ (2 * k + 1) := by
      dsimp only [g, z, E, A, B]
      nlinarith
    have hzNorm : ‖z y‖ ≤ B := by
      simpa only [z, B] using norm_xiGaussianVerticalPoint_le R y hyAbs
    have hpow : B ^ (2 * k) ≤ B ^ (2 * k + 2) :=
      pow_le_pow_right₀ hB (by omega)
    rw [(hhDeriv y).deriv, norm_div]
    calc
      ‖(deriv g (z y) * I) * z y + g (z y) * I‖ / ‖p‖ ≤
          (‖deriv g (z y)‖ * ‖z y‖ + ‖g (z y)‖) / ‖p‖ := by
        apply div_le_div_of_nonneg_right _ (norm_nonneg p)
        calc
          ‖(deriv g (z y) * I) * z y + g (z y) * I‖ ≤
              ‖(deriv g (z y) * I) * z y‖ + ‖g (z y) * I‖ := norm_add_le _ _
          _ = ‖deriv g (z y)‖ * ‖z y‖ + ‖g (z y)‖ := by simp
      _ ≤ (E * A * B ^ (2 * k + 1) * B + E * B ^ (2 * k)) / ‖p‖ := by
        apply div_le_div_of_nonneg_right _ (norm_nonneg p)
        exact add_le_add
          (mul_le_mul hgDeriv hzNorm (norm_nonneg _) (by positivity)) hgValue
      _ ≤ (E * (A + 1) * B ^ (2 * k + 2)) / ‖p‖ := by
        apply div_le_div_of_nonneg_right _ (norm_nonneg p)
        calc
          E * A * B ^ (2 * k + 1) * B + E * B ^ (2 * k) ≤
              E * A * B ^ (2 * k + 1) * B + E * B ^ (2 * k + 2) := by
            gcongr
          _ = E * (A + 1) * B ^ (2 * k + 2) := by
            rw [pow_succ']
            ring
      _ = M := rfl
  have hhValue : ‖h p.im‖ ≤ E * B ^ (2 * k + 2) / ‖p‖ := by
    have hpimAbs : |p.im| ≤ 1 := by
      rw [abs_le]
      constructor <;> linarith [hpim.1, hpim.2]
    have hgValue0 := norm_xiGaussianTestC_vertical_le ht k R p.im hpimAbs
    have hgValue : ‖g (z p.im)‖ ≤ E * B ^ (2 * k) := by
      dsimp only [g, z, E, B]
      nlinarith
    have hzNorm : ‖z p.im‖ ≤ B := by
      simpa only [z, B] using norm_xiGaussianVerticalPoint_le R p.im hpimAbs
    have hpow : B ^ (2 * k + 1) ≤ B ^ (2 * k + 2) :=
      pow_le_pow_right₀ hB (by omega)
    dsimp only [h]
    rw [norm_div, norm_mul]
    apply div_le_div_of_nonneg_right _ (norm_nonneg p)
    calc
      ‖g (z p.im)‖ * ‖z p.im‖ ≤ E * B ^ (2 * k) * B :=
        mul_le_mul hgValue hzNorm (norm_nonneg _) (by positivity)
      _ = E * B ^ (2 * k + 1) := by rw [pow_succ']; ring
      _ ≤ E * B ^ (2 * k + 2) := mul_le_mul_of_nonneg_left hpow hE
  have hweighted := norm_integral_mul_vertical_cauchyKernel_le
    hM hdiff hderiv hpim (R := R) (by simpa only [p] using havoid)
  have hrewrite : ∀ y : ℝ,
      xiGaussianVerticalRawTerm t k R q y = h y * ((z y - p)⁻¹) := by
    intro y
    have hzp : z y - p ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      simp only [z, p, sub_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
        zero_mul, mul_zero, sub_zero, add_zero, zero_re] at hre
      exact havoid (sub_eq_zero.mp hre)
    dsimp only [xiGaussianVerticalRawTerm, h, g, z, p]
    rw [show xiSpectralPoint q - ((R : ℂ) + y * I) =
        -(((R : ℂ) + y * I) - xiSpectralPoint q) by ring,
      mul_neg, div_neg]
    simp only [neg_div, neg_neg]
    field_simp [hp0, hzp]
  calc
    ‖∫ y in (-1 : ℝ)..1, xiGaussianVerticalRawTerm t k R q y‖ =
        ‖∫ y in (-1 : ℝ)..1, h y * ((z y - p)⁻¹)‖ := by
      congr 1
      apply integral_congr
      intro y hy
      exact hrewrite y
    _ ≤ ‖h p.im‖ * xiVerticalCauchyKernelBound + 2 * M := hweighted
    _ ≤ (E * B ^ (2 * k + 2) / ‖p‖) * xiVerticalCauchyKernelBound +
        2 * M := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hhValue xiVerticalCauchyKernelBound_nonneg) le_rfl
    _ = xiGaussianVerticalIntegratedNumerator t k R / ‖xiSpectralPoint q‖ := by
      dsimp only [M, A, B, E, p]
      unfold xiGaussianVerticalIntegratedNumerator
      ring

/-- A Gaussian raw summand is continuous on every divisor-avoiding vertical segment. -/
theorem continuousOn_xiGaussianVerticalRawTerm
    (t : ℝ) (k : ℕ) (R : ℝ) (q : XiZeroCopy)
    (havoid : R ≠ (xiSpectralPoint q).re) :
    ContinuousOn (xiGaussianVerticalRawTerm t k R q) (Icc (-1 : ℝ) 1) := by
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
  have hg : ContinuousOn (fun y : ℝ => xiGaussianTestC t k (z y))
      (Icc (-1 : ℝ) 1) :=
    (analyticOnNhd_xiGaussianTestC t k).continuousOn.comp
      hz.continuousOn (fun y hy => Set.mem_univ (z y))
  have hquot : ContinuousOn
      (fun y : ℝ => -(z y) / (p * (p - z y))) (Icc (-1 : ℝ) 1) := by
    apply hz.continuousOn.neg.div
      (continuousOn_const.mul (continuousOn_const.sub hz.continuousOn))
    intro y hy
    exact mul_ne_zero hp0 (hpz y hy)
  unfold xiGaussianVerticalRawTerm
  dsimp only [z, p]
  exact hg.mul hquot

/-- Far from the edge scale, Gaussian raw summands recover inverse-square spectral decay. -/
theorem norm_xiGaussianVerticalRawTerm_le_inv_sq
    {t : ℝ} (ht : 0 < t) (k : ℕ) (R : ℝ) (q : XiZeroCopy)
    (hfar : 3 * (1 + |R|) ≤ ‖xiSpectralPoint q‖)
    {y : ℝ} (hy : |y| ≤ 1) :
    ‖xiGaussianVerticalRawTerm t k R q y‖ ≤
      2 * Real.exp t * (1 + |R|) ^ (2 * k + 1) *
        Real.exp (-(t * R ^ 2)) / ‖xiSpectralPoint q‖ ^ 2 := by
  let p : ℂ := xiSpectralPoint q
  let z : ℂ := (R : ℂ) + y * I
  let B : ℝ := 1 + |R|
  let E : ℝ := Real.exp t * Real.exp (-(t * R ^ 2))
  have hp : 0 < ‖p‖ := norm_pos_iff.mpr (xiSpectralPoint_ne_zero q)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hz : ‖z‖ ≤ B := by
    simpa only [z, B] using norm_xiGaussianVerticalPoint_le R y hy
  have hzhalf : ‖z‖ ≤ ‖p‖ / 2 := by
    dsimp only [p, B] at hfar ⊢
    linarith
  have hdiff : ‖p‖ / 2 ≤ ‖p - z‖ := by
    have hrev := norm_sub_norm_le p z
    linarith
  have hg0 := norm_xiGaussianTestC_vertical_le ht k R y hy
  have hg : ‖xiGaussianTestC t k z‖ ≤ E * B ^ (2 * k) := by
    dsimp only [z, E, B]
    nlinarith
  have hnum : ‖xiGaussianTestC t k z‖ * ‖z‖ ≤ E * B ^ (2 * k + 1) := by
    calc
      ‖xiGaussianTestC t k z‖ * ‖z‖ ≤ E * B ^ (2 * k) * B :=
        mul_le_mul hg hz (norm_nonneg _) (by positivity)
      _ = E * B ^ (2 * k + 1) := by rw [pow_succ']; ring
  have hden : ‖p‖ * (‖p‖ / 2) ≤ ‖p‖ * ‖p - z‖ :=
    mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)
  unfold xiGaussianVerticalRawTerm
  dsimp only [z, p, B, E]
  rw [norm_mul, norm_div, norm_neg, norm_mul, ← mul_div_assoc]
  calc
    ‖xiGaussianTestC t k z‖ * ‖z‖ / (‖p‖ * ‖p - z‖) ≤
        (E * B ^ (2 * k + 1)) / (‖p‖ * ‖p - z‖) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ ≤ (E * B ^ (2 * k + 1)) / (‖p‖ * (‖p‖ / 2)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 2 * Real.exp t * (1 + |R|) ^ (2 * k + 1) *
        Real.exp (-(t * R ^ 2)) / ‖xiSpectralPoint q‖ ^ 2 := by
      dsimp only [E, B, p]
      field_simp

theorem integral_norm_xiGaussianVerticalRawTerm_le_inv_sq
    {t : ℝ} (ht : 0 < t) (k : ℕ) (R : ℝ) (q : XiZeroCopy)
    (hfar : 3 * (1 + |R|) ≤ ‖xiSpectralPoint q‖) :
    (∫ y in (-1 : ℝ)..1, ‖xiGaussianVerticalRawTerm t k R q y‖) ≤
      4 * Real.exp t * (1 + |R|) ^ (2 * k + 1) *
        Real.exp (-(t * R ^ 2)) / ‖xiSpectralPoint q‖ ^ 2 := by
  have him := xiSpectralPoint_im_mem_openHalf q
  have himAbs : |(xiSpectralPoint q).im| < 1 / 2 := by
    rw [abs_lt]
    constructor <;> linarith [him.1, him.2]
  have havoid : R ≠ (xiSpectralPoint q).re := by
    intro heq
    have hnorm := Complex.norm_le_abs_re_add_abs_im (xiSpectralPoint q)
    rw [← heq] at hnorm
    linarith [abs_nonneg R]
  have hcont := continuousOn_xiGaussianVerticalRawTerm t k R q havoid
  have hfint : IntervalIntegrable (xiGaussianVerticalRawTerm t k R q)
      volume (-1 : ℝ) 1 := by
    have hcontu : ContinuousOn (xiGaussianVerticalRawTerm t k R q)
        (uIcc (-1 : ℝ) 1) := by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hcont
    exact hcontu.intervalIntegrable
  let C : ℝ := 2 * Real.exp t * (1 + |R|) ^ (2 * k + 1) *
    Real.exp (-(t * R ^ 2)) / ‖xiSpectralPoint q‖ ^ 2
  have hmono :
      (∫ y in (-1 : ℝ)..1, ‖xiGaussianVerticalRawTerm t k R q y‖) ≤
        ∫ _y in (-1 : ℝ)..1, C := by
    apply intervalIntegral.integral_mono_on (by norm_num) hfint.norm
      (continuous_const.intervalIntegrable _ _)
    intro y hy
    exact norm_xiGaussianVerticalRawTerm_le_inv_sq ht k R q hfar ((abs_le).2 hy)
  calc
    (∫ y in (-1 : ℝ)..1, ‖xiGaussianVerticalRawTerm t k R q y‖) ≤
        ∫ _y in (-1 : ℝ)..1, C := hmono
    _ = 4 * Real.exp t * (1 + |R|) ^ (2 * k + 1) *
        Real.exp (-(t * R ^ 2)) / ‖xiSpectralPoint q‖ ^ 2 := by
      rw [intervalIntegral.integral_const]
      dsimp only [C]
      norm_num
      ring

private theorem sqrt_three_mul_one_add_abs_le (R : ℝ) :
    Real.sqrt (3 * (1 + |R|)) ≤ 2 * (1 + |R|) := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · have hB : 1 ≤ 1 + |R| := by linarith [abs_nonneg R]
    nlinarith

/-- Explicit summation-ready majorant for the complete Gaussian vertical edge. -/
def xiGaussianVerticalTsumMajorant (t : ℝ) (k : ℕ) (R : ℝ) : ℝ :=
  (2 * xiGaussianVerticalIntegratedNumerator t k R * (1 + |R|)) *
      (∑' q : XiZeroCopy,
        1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)) +
    (4 * Real.exp t * (1 + |R|) ^ (2 * k + 1) *
        Real.exp (-(t * R ^ 2))) *
      (∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2)

theorem summable_integral_xiGaussianVerticalRawTerm_and_norm_tsum_le
    {t : ℝ} (ht : 0 < t) (k : ℕ) (R : ℝ)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    Summable (fun q : XiZeroCopy =>
        ∫ y in (-1 : ℝ)..1, xiGaussianVerticalRawTerm t k R q y) ∧
      ‖∑' q : XiZeroCopy,
          ∫ y in (-1 : ℝ)..1, xiGaussianVerticalRawTerm t k R q y‖ ≤
        xiGaussianVerticalTsumMajorant t k R := by
  let T : XiZeroCopy → ℂ := fun q =>
    ∫ y in (-1 : ℝ)..1, xiGaussianVerticalRawTerm t k R q y
  let w₃ : XiZeroCopy → ℝ := fun q =>
    1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)
  let w₂ : XiZeroCopy → ℝ := fun q => 1 / ‖xiSpectralPoint q‖ ^ 2
  let N : ℝ := xiGaussianVerticalIntegratedNumerator t k R
  let B : ℝ := 1 + |R|
  let F : ℝ := 4 * Real.exp t * B ^ (2 * k + 1) * Real.exp (-(t * R ^ 2))
  let c₃ : ℝ := 2 * N * B
  have hN : 0 ≤ N := xiGaussianVerticalIntegratedNumerator_nonneg ht k R
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hc₃ : 0 ≤ c₃ := by dsimp only [c₃]; positivity
  have hw₃ : Summable w₃ := by
    simpa only [w₃] using xiSpectralPoint_inv_three_halves_summable
  have hw₂ : Summable w₂ := by
    simpa only [w₂] using xiSpectralPoint_inv_sq_summable
  have hmajorant : Summable (fun q => c₃ * w₃ q + F * w₂ q) :=
    (hw₃.mul_left c₃).add (hw₂.mul_left F)
  have hbound : ∀ q : XiZeroCopy, ‖T q‖ ≤ c₃ * w₃ q + F * w₂ q := by
    intro q
    by_cases hnear : ‖xiSpectralPoint q‖ ≤ 3 * B
    · have hinv := one_div_norm_le_sqrt_mul_one_div_norm_sqrt_norm q hnear
      have hsqrt := sqrt_three_mul_one_add_abs_le R
      have hsqrtw : Real.sqrt (3 * B) * w₃ q ≤ 2 * B * w₃ q := by
        exact mul_le_mul_of_nonneg_right
          (by simpa only [B] using hsqrt) (by dsimp only [w₃]; positivity)
      calc
        ‖T q‖ ≤ N / ‖xiSpectralPoint q‖ := by
          simpa only [T, N] using norm_integral_xiGaussianVerticalRawTerm_le
            ht k R q (havoid q)
        _ = N * (1 / ‖xiSpectralPoint q‖) := by ring
        _ ≤ N * (Real.sqrt (3 * B) * w₃ q) :=
          mul_le_mul_of_nonneg_left (by simpa only [w₃] using hinv) hN
        _ ≤ N * (2 * B * w₃ q) := mul_le_mul_of_nonneg_left hsqrtw hN
        _ = c₃ * w₃ q := by dsimp only [c₃]; ring
        _ ≤ c₃ * w₃ q + F * w₂ q :=
          le_add_of_nonneg_right (mul_nonneg hF (by dsimp only [w₂]; positivity))
    · have hfar : 3 * B ≤ ‖xiSpectralPoint q‖ := le_of_lt (lt_of_not_ge hnear)
      calc
        ‖T q‖ ≤
            ∫ y in (-1 : ℝ)..1, ‖xiGaussianVerticalRawTerm t k R q y‖ := by
          simpa only [T] using
            (intervalIntegral.norm_integral_le_integral_norm
              (show (-1 : ℝ) ≤ 1 by norm_num) :
              ‖∫ y in (-1 : ℝ)..1, xiGaussianVerticalRawTerm t k R q y‖ ≤
                ∫ y in (-1 : ℝ)..1, ‖xiGaussianVerticalRawTerm t k R q y‖)
        _ ≤ F / ‖xiSpectralPoint q‖ ^ 2 := by
          simpa only [F, B] using
            integral_norm_xiGaussianVerticalRawTerm_le_inv_sq ht k R q hfar
        _ = F * w₂ q := by dsimp only [w₂]; ring
        _ ≤ c₃ * w₃ q + F * w₂ q :=
          le_add_of_nonneg_left (mul_nonneg hc₃ (by dsimp only [w₃]; positivity))
  have hT : Summable T := hmajorant.of_norm_bounded hbound
  refine ⟨by simpa only [T] using hT, ?_⟩
  calc
    ‖∑' q : XiZeroCopy, ∫ y in (-1 : ℝ)..1,
        xiGaussianVerticalRawTerm t k R q y‖ = ‖∑' q, T q‖ := by rfl
    _ ≤ ∑' q, ‖T q‖ := norm_tsum_le_tsum_norm hT.norm
    _ ≤ ∑' q, (c₃ * w₃ q + F * w₂ q) :=
      Summable.tsum_mono hT.norm hmajorant hbound
    _ = c₃ * (∑' q, w₃ q) + F * (∑' q, w₂ q) := by
      rw [(hw₃.mul_left c₃).tsum_add (hw₂.mul_left F), tsum_mul_left, tsum_mul_left]
    _ = xiGaussianVerticalTsumMajorant t k R := by
      rfl

theorem tendsto_xiGaussianVerticalTsumMajorant_atTop
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Tendsto (xiGaussianVerticalTsumMajorant t k) atTop (nhds 0) := by
  let S₃ : ℝ := ∑' q : XiZeroCopy,
    1 / (‖xiSpectralPoint q‖ * Real.sqrt ‖xiSpectralPoint q‖)
  let S₂ : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  let K : ℝ := Real.exp t *
    (xiVerticalCauchyKernelBound + 2 * (((2 * k : ℕ) : ℝ) + 2 * t + 1))
  have hfirst0 := tendsto_polyGaussian_atTop ht (2 * k + 3) 1
  have hfirst : Tendsto
      (fun R : ℝ => (2 * K * (1 + |R|) ^ (2 * k + 3) *
        Real.exp (-(t * R ^ 2))) * S₃) atTop (nhds 0) := by
    convert (hfirst0.const_mul (2 * K)).mul_const S₃ using 1
    · funext R
      ring
    · norm_num
  have hsecond0 := tendsto_polyGaussian_atTop ht (2 * k + 1) 1
  have hsecond : Tendsto
      (fun R : ℝ => (4 * Real.exp t * (1 + |R|) ^ (2 * k + 1) *
        Real.exp (-(t * R ^ 2))) * S₂) atTop (nhds 0) := by
    convert (hsecond0.const_mul (4 * Real.exp t)).mul_const S₂ using 1
    · funext R
      ring
    · norm_num
  have hsum := hfirst.add hsecond
  dsimp only [K, S₃, S₂] at hsum ⊢
  convert hsum using 1
  · funext R
    unfold xiGaussianVerticalTsumMajorant xiGaussianVerticalIntegratedNumerator
    rw [show (1 + |R|) ^ (2 * k + 3) =
        (1 + |R|) ^ (2 * k + 2) * (1 + |R|) by
      rw [pow_succ]]
    ring
  · norm_num

/-- Cofinal Gaussian vertical edges avoid the exact divisor and have arbitrarily small summed
relative-resolvent contribution. -/
theorem exists_large_integrated_xiGaussianVerticalRawTerm_tsum_lt
    {t : ℝ} (ht : 0 < t) (k : ℕ) (X : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ R : ℝ,
      X < R ∧
      (∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) ∧
      Summable (fun q : XiZeroCopy =>
        ∫ y in (-1 : ℝ)..1, xiGaussianVerticalRawTerm t k R q y) ∧
      ‖∑' q : XiZeroCopy,
          ∫ y in (-1 : ℝ)..1, xiGaussianVerticalRawTerm t k R q y‖ < epsilon := by
  have hevent := (tendsto_xiGaussianVerticalTsumMajorant_atTop ht k).eventually_lt_const
    hepsilon
  obtain ⟨M, hM⟩ := eventually_atTop.1 hevent
  let u : ℝ := max X M
  obtain ⟨R, hRI, havoid⟩ := exists_real_avoiding_all_xiSpectralPoint_re
    (show u < u + 1 by linarith)
  have hXR : X < R := lt_of_le_of_lt (le_max_left X M) hRI.1
  have hMR : M ≤ R := le_trans (le_max_right X M) hRI.1.le
  obtain ⟨hsum, hbound⟩ :=
    summable_integral_xiGaussianVerticalRawTerm_and_norm_tsum_le ht k R havoid
  exact ⟨R, hXR, havoid, hsum, lt_of_le_of_lt hbound (hM R hMR)⟩

/-- Absolute far-spectrum control justifies exchanging the exact Xi divisor sum with the Gaussian
vertical integral. -/
theorem integral_tsum_xiGaussianVerticalRawTerm_eq_tsum_integral
    {t : ℝ} (ht : 0 < t) (k : ℕ) (R : ℝ)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    (∫ y in (-1 : ℝ)..1,
        ∑' q : XiZeroCopy, xiGaussianVerticalRawTerm t k R q y) =
      ∑' q : XiZeroCopy,
        ∫ y in (-1 : ℝ)..1, xiGaussianVerticalRawTerm t k R q y := by
  let B : ℝ := 1 + |R|
  let F : ℝ := 4 * Real.exp t * B ^ (2 * k + 1) * Real.exp (-(t * R ^ 2))
  let b : XiZeroCopy → ℝ := fun q => F / ‖xiSpectralPoint q‖ ^ 2
  have hB : 0 < B := by dsimp only [B]; positivity
  have hb : Summable b := by
    have hscaled := xiSpectralPoint_inv_sq_summable.mul_left F
    refine hscaled.congr (fun q => ?_)
    dsimp only [b]
    ring
  have hfarEventually :
      ∀ᶠ q : XiZeroCopy in Filter.cofinite,
        3 * B ≤ ‖xiSpectralPoint q‖ := by
    have hfinite := xiSpectralPoint_finite_norm_le
      (B := 3 * B) (by positivity)
    have houtside :
        ∀ᶠ q : XiZeroCopy in Filter.cofinite,
          3 * B < ‖xiSpectralPoint q‖ := by
      simpa only [Set.compl_setOf, Set.mem_setOf_eq, not_le] using!
        hfinite.compl_mem_cofinite
    filter_upwards [houtside] with q hq
    exact le_of_lt hq
  have hnormSum : Summable (fun q : XiZeroCopy =>
      ∫ y in (-1 : ℝ)..1, ‖xiGaussianVerticalRawTerm t k R q y‖) := by
    apply hb.of_norm_bounded_eventually
    filter_upwards [hfarEventually] with q hfar
    have hnonneg : 0 ≤
        ∫ y in (-1 : ℝ)..1, ‖xiGaussianVerticalRawTerm t k R q y‖ :=
      intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => norm_nonneg _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    simpa only [b, F, B] using
      integral_norm_xiGaussianVerticalRawTerm_le_inv_sq ht k R q hfar
  have hFint : ∀ q : XiZeroCopy,
      Integrable (xiGaussianVerticalRawTerm t k R q)
        (volume.restrict (Ioc (-1 : ℝ) 1)) := by
    intro q
    have hcont := continuousOn_xiGaussianVerticalRawTerm t k R q (havoid q)
    have hcontu : ContinuousOn (xiGaussianVerticalRawTerm t k R q)
        (uIcc (-1 : ℝ) 1) := by
      simpa only [uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using hcont
    have hint : IntervalIntegrable (xiGaussianVerticalRawTerm t k R q)
        volume (-1 : ℝ) 1 := hcontu.intervalIntegrable
    rw [intervalIntegrable_iff] at hint
    simpa only [uIoc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] using! hint
  have hnormSumRestrict : Summable (fun q : XiZeroCopy =>
      ∫ y in Ioc (-1 : ℝ) 1, ‖xiGaussianVerticalRawTerm t k R q y‖) := by
    apply hnormSum.congr
    intro q
    exact intervalIntegral.integral_of_le (by norm_num)
  rw [intervalIntegral.integral_of_le (by norm_num)]
  calc
    (∫ y in Ioc (-1 : ℝ) 1,
        ∑' q : XiZeroCopy, xiGaussianVerticalRawTerm t k R q y) =
      ∑' q : XiZeroCopy,
        ∫ y in Ioc (-1 : ℝ) 1, xiGaussianVerticalRawTerm t k R q y :=
      (MeasureTheory.integral_tsum_of_summable_integral_norm hFint
        hnormSumRestrict).symm
    _ = ∑' q : XiZeroCopy,
        ∫ y in (-1 : ℝ)..1, xiGaussianVerticalRawTerm t k R q y := by
      apply tsum_congr
      intro q
      exact (intervalIntegral.integral_of_le (by norm_num)).symm

/-- Pointwise on a divisor-avoiding edge, the raw Gaussian spectral sum is the Gaussian test
times the canonical Xi relative-resolvent trace. -/
theorem tsum_xiGaussianVerticalRawTerm_eq_mul_relativeResolventTrace
    (t : ℝ) (k : ℕ) (R y : ℝ)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    (∑' q : XiZeroCopy, xiGaussianVerticalRawTerm t k R q y) =
      xiGaussianTestC t k ((R : ℂ) + y * I) *
        xiRelativeResolventTrace ((R : ℂ) + y * I) := by
  let z : ℂ := (R : ℂ) + y * I
  let g : ℂ := xiGaussianTestC t k z
  let a : XiZeroCopy → ℂ := fun q =>
    -z / (xiSpectralPoint q * (xiSpectralPoint q - z))
  have hzq : ∀ q : XiZeroCopy, z ≠ xiSpectralPoint q := by
    intro q heq
    have hre := congrArg Complex.re heq
    simp only [z, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im, zero_mul,
      mul_zero, sub_self, add_zero] at hre
    exact havoid q hre
  have hterm : ∀ q : XiZeroCopy, xiRelativeResolventTerm z q = a q := by
    intro q
    have hp := xiSpectralPoint_ne_zero q
    have hpz : xiSpectralPoint q - z ≠ 0 :=
      sub_ne_zero.mpr (Ne.symm (hzq q))
    rw [xiRelativeResolventTerm, inv_eq_one_div]
    dsimp only [a]
    field_simp [hp, hpz]
    ring
  have htrace : (∑' q : XiZeroCopy, a q) = xiRelativeResolventTrace z := by
    rw [xiRelativeResolventTrace]
    apply tsum_congr
    intro q
    exact (hterm q).symm
  calc
    (∑' q : XiZeroCopy, xiGaussianVerticalRawTerm t k R q y) =
        ∑' q : XiZeroCopy, g * a q := by
      apply tsum_congr
      intro q
      rfl
    _ = g * (∑' q : XiZeroCopy, a q) := tsum_mul_left
    _ = g * xiRelativeResolventTrace z := by rw [htrace]
    _ = xiGaussianTestC t k ((R : ℂ) + y * I) *
        xiRelativeResolventTrace ((R : ℂ) + y * I) := by rfl

theorem integral_mul_xiGaussian_relativeResolventTrace_eq_tsum_integral_rawTerm
    {t : ℝ} (ht : 0 < t) (k : ℕ) (R : ℝ)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    (∫ y in (-1 : ℝ)..1,
        xiGaussianTestC t k ((R : ℂ) + y * I) *
          xiRelativeResolventTrace ((R : ℂ) + y * I)) =
      ∑' q : XiZeroCopy,
        ∫ y in (-1 : ℝ)..1, xiGaussianVerticalRawTerm t k R q y := by
  calc
    (∫ y in (-1 : ℝ)..1,
        xiGaussianTestC t k ((R : ℂ) + y * I) *
          xiRelativeResolventTrace ((R : ℂ) + y * I)) =
      ∫ y in (-1 : ℝ)..1,
        ∑' q : XiZeroCopy, xiGaussianVerticalRawTerm t k R q y := by
      apply integral_congr
      intro y hy
      exact (tsum_xiGaussianVerticalRawTerm_eq_mul_relativeResolventTrace
        t k R y havoid).symm
    _ = ∑' q : XiZeroCopy,
        ∫ y in (-1 : ℝ)..1, xiGaussianVerticalRawTerm t k R q y :=
      integral_tsum_xiGaussianVerticalRawTerm_eq_tsum_integral ht k R havoid

theorem integral_xiGaussian_mul_logDeriv_XiC_eq_relativeResolventTrace
    (t : ℝ) (k : ℕ) (R : ℝ)
    (havoid : ∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) :
    (∫ y in (-1 : ℝ)..1,
        xiGaussianTestC t k ((R : ℂ) + y * I) *
          logDeriv XiC ((R : ℂ) + y * I)) =
      ∫ y in (-1 : ℝ)..1,
        xiGaussianTestC t k ((R : ℂ) + y * I) *
          xiRelativeResolventTrace ((R : ℂ) + y * I) := by
  apply integral_congr
  intro y hy
  dsimp only
  rw [logDeriv_XiC_eq_relativeResolventTrace
    (XiC_ne_zero_on_avoiding_vertical R y havoid)]

/-- Full Gaussian logarithmic-derivative vertical edge vanishes cofinally, with no separation
hypothesis from the Xi divisor. -/
theorem exists_large_integral_xiGaussian_mul_logDeriv_XiC_norm_lt
    {t : ℝ} (ht : 0 < t) (k : ℕ) (X : ℝ) {epsilon : ℝ}
    (hepsilon : 0 < epsilon) :
    ∃ R : ℝ,
      X < R ∧
      (∀ q : XiZeroCopy, R ≠ (xiSpectralPoint q).re) ∧
      ‖∫ y in (-1 : ℝ)..1,
          xiGaussianTestC t k ((R : ℂ) + y * I) *
            logDeriv XiC ((R : ℂ) + y * I)‖ < epsilon := by
  obtain ⟨R, hXR, havoid, hsum, hsmall⟩ :=
    exists_large_integrated_xiGaussianVerticalRawTerm_tsum_lt ht k X hepsilon
  have hedge := integral_mul_xiGaussian_relativeResolventTrace_eq_tsum_integral_rawTerm
    ht k R havoid
  refine ⟨R, hXR, havoid, ?_⟩
  rw [integral_xiGaussian_mul_logDeriv_XiC_eq_relativeResolventTrace
    t k R havoid, hedge]
  exact hsmall

end
end RHTower
