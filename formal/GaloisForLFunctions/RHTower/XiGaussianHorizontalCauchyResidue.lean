import GaloisForLFunctions.RHTower.XiGaussianExplicitFormulaRectangle
import GaloisForLFunctions.RHTower.RectangleCauchyFormula

/-!
# Horizontal Cauchy wall crossing for Gaussian--Hermite tests

The centered Gaussian--Hermite test has enough real-direction decay to pass Cauchy's rectangle
formula to infinite horizontal lines.  If a pole lies strictly between two horizontal lines, the
lower-line integral minus the upper-line integral is exactly its Cauchy residue.  This is the
literal polar term required by the polynomial-Gaussian prime--Gamma explicit formula; no finite
packet, numerical approximation, or limiting hypothesis remains in the statement.
-/

open Complex Filter MeasureTheory Set Topology intervalIntegral

namespace RHTower

noncomputable section

/-- Rotation identifies the centered Gaussian test with the vertical-strip test already carrying
the corpus's Gaussian integrability estimates. -/
theorem xiGaussianTest_rotated_eq
    (t : ℝ) (n : ℕ) (x y : ℝ) :
    xiGaussianTest t n (((1 / 2 - y : ℝ) : ℂ) + (x : ℂ) * I) =
      ((-1 : ℂ) ^ n) * xiGaussianTestC t n ((x : ℂ) + (y : ℂ) * I) := by
  rw [xiGaussianTest, xiGaussianTestC]
  have hcenter :
      (((1 / 2 - y : ℝ) : ℂ) + (x : ℂ) * I) - 1 / 2 =
        I * ((x : ℂ) + (y : ℂ) * I) := by
    calc
      (((1 / 2 - y : ℝ) : ℂ) + (x : ℂ) * I) - 1 / 2 =
          -(y : ℂ) + (x : ℂ) * I := by push_cast; ring
      _ = I * ((x : ℂ) + (y : ℂ) * I) := by
        calc
          -(y : ℂ) + (x : ℂ) * I = I * (x : ℂ) + (-1 : ℂ) * (y : ℂ) := by ring
          _ = I * (x : ℂ) + (I * I) * (y : ℂ) := by rw [Complex.I_mul_I]
          _ = I * ((x : ℂ) + (y : ℂ) * I) := by ring
  let z : ℂ := (x : ℂ) + (y : ℂ) * I
  have hbase : (I * z) ^ (2 : ℕ) = -(z ^ (2 : ℕ)) := by
    rw [mul_pow, Complex.I_sq]
    ring
  have hpow : (I * z) ^ (2 * n) = (-1 : ℂ) ^ n * z ^ (2 * n) := by
    rw [pow_mul, hbase, neg_pow, ← pow_mul]
  rw [hcenter]
  change (I * z) ^ (2 * n) * Complex.exp ((t : ℂ) * (I * z) ^ (2 : ℕ)) =
    (-1 : ℂ) ^ n * (z ^ (2 * n) * Complex.exp (-(t : ℂ) * z ^ (2 : ℕ)))
  rw [hpow, hbase]
  have hexp : (t : ℂ) * -(z ^ (2 : ℕ)) = -(t : ℂ) * z ^ (2 : ℕ) := by ring
  rw [hexp]
  ring

theorem norm_xiGaussianTestC_eq_norm_rotated
    (t : ℝ) (n : ℕ) (x y : ℝ) :
    ‖xiGaussianTestC t n ((x : ℂ) + (y : ℂ) * I)‖ =
      ‖xiGaussianTest t n (((1 / 2 - y : ℝ) : ℂ) + (x : ℂ) * I)‖ := by
  rw [xiGaussianTest_rotated_eq, norm_mul, norm_pow, norm_neg, norm_one, one_pow,
    one_mul]

/-- Every horizontal restriction of the centered Gaussian--Hermite test is integrable. -/
theorem integrable_xiGaussianTestC_horizontal
    {t : ℝ} (ht : 0 < t) (n : ℕ) (y : ℝ) :
    Integrable (fun x : ℝ =>
      xiGaussianTestC t n ((x : ℂ) + (y : ℂ) * I)) := by
  have hrot := integrable_xiGaussianTest_vertical ht n (1 / 2 - y)
  have hsign : ((-1 : ℂ) ^ n) * ((-1 : ℂ) ^ n) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have hscaled := hrot.const_mul ((-1 : ℂ) ^ n)
  apply hscaled.congr
  filter_upwards with x
  rw [xiGaussianTest_rotated_eq]
  rw [← mul_assoc, hsign, one_mul]

private theorem integrable_xiGaussianTestC_horizontal_cauchy
    {t : ℝ} (ht : 0 < t) (n : ℕ) {y : ℝ} {p : ℂ}
    (hyp : y ≠ p.im) :
    Integrable (fun x : ℝ =>
      xiGaussianTestC t n ((x : ℂ) + (y : ℂ) * I) *
        (((x : ℂ) + (y : ℂ) * I) - p)⁻¹) := by
  let d : ℝ := |y - p.im|
  have hd : 0 < d := abs_pos.mpr (sub_ne_zero.mpr hyp)
  have hprofile := integrable_xiGaussianTestC_horizontal ht n y
  have hmajor : Integrable (fun x : ℝ =>
      d⁻¹ * ‖xiGaussianTestC t n ((x : ℂ) + (y : ℂ) * I)‖) :=
    hprofile.norm.const_mul d⁻¹
  refine Integrable.mono' hmajor ?_ (Filter.Eventually.of_forall fun x => ?_)
  · have hprofileCont : Continuous (fun x : ℝ =>
        xiGaussianTestC t n ((x : ℂ) + (y : ℂ) * I)) := by
      unfold xiGaussianTestC
      fun_prop
    have hdenCont : Continuous (fun x : ℝ =>
        ((x : ℂ) + (y : ℂ) * I) - p) := by fun_prop
    have hne : ∀ x : ℝ, ((x : ℂ) + (y : ℂ) * I) - p ≠ 0 := by
      intro x hx
      have him := congrArg Complex.im (sub_eq_zero.mp hx)
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, Complex.I_re, zero_mul, mul_one, zero_add] at him
      exact hyp (by simpa using him)
    exact (hprofileCont.mul (hdenCont.inv₀ hne)).aestronglyMeasurable
  · rw [norm_mul, norm_inv]
    have himle := Complex.abs_im_le_norm (((x : ℂ) + (y : ℂ) * I) - p)
    have him : (((x : ℂ) + (y : ℂ) * I) - p).im = y - p.im := by simp
    rw [him] at himle
    have hinv : ‖((x : ℂ) + (y : ℂ) * I) - p‖⁻¹ ≤ d⁻¹ :=
      inv_anti₀ hd (by simpa only [d] using himle)
    calc
      ‖xiGaussianTestC t n ((x : ℂ) + (y : ℂ) * I)‖ *
          ‖((x : ℂ) + (y : ℂ) * I) - p‖⁻¹
        ≤ ‖xiGaussianTestC t n ((x : ℂ) + (y : ℂ) * I)‖ * d⁻¹ :=
          mul_le_mul_of_nonneg_left hinv (norm_nonneg _)
      _ = d⁻¹ * ‖xiGaussianTestC t n ((x : ℂ) + (y : ℂ) * I)‖ := by ring

private theorem abs_le_abs_add_abs_of_mem_uIoc
    {a b y : ℝ} (hy : y ∈ Set.uIoc a b) :
    |y| ≤ |a| + |b| := by
  have hy' : min a b ≤ y ∧ y ≤ max a b := by
    change y ∈ Set.uIcc a b
    exact Set.uIoc_subset_uIcc hy
  rw [abs_le]
  constructor
  · calc
      -(|a| + |b|) ≤ min a b := by
        apply le_min <;> linarith [neg_abs_le a, neg_abs_le b, abs_nonneg a, abs_nonneg b]
      _ ≤ y := hy'.1
  · calc
      y ≤ max a b := hy'.2
      _ ≤ |a| + |b| := by
        apply max_le <;> linarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b]

private theorem norm_xiGaussianTestC_le_on_horizontal_strip
    {t : ℝ} (ht : 0 < t) (n : ℕ) {a b x y : ℝ}
    (hy : y ∈ Set.uIoc a b) :
    ‖xiGaussianTestC t n ((x : ℂ) + (y : ℂ) * I)‖ ≤
      (|a| + |b| + |x|) ^ (2 * n) * Real.exp (t * (|a| + |b|) ^ (2 : ℕ)) *
        Real.exp (-(t * x ^ (2 : ℕ))) := by
  rw [norm_xiGaussianTestC_eq_norm_rotated]
  have hyabs := abs_le_abs_add_abs_of_mem_uIoc hy
  have hbound := norm_xiGaussianTest_le_of_strip ht n
    (show 0 ≤ |a| + |b| by positivity)
    (s := (((1 / 2 - y : ℝ) : ℂ) + (x : ℂ) * I))
    (by simpa using hyabs)
  simpa [add_assoc, add_comm, add_left_comm] using hbound

private theorem tendsto_xiGaussianTestC_cauchy_vertical_right
    {t : ℝ} (ht : 0 < t) (n : ℕ) (a b : ℝ) (p : ℂ) :
    Tendsto (fun R : ℝ => ∫ y : ℝ in a..b,
      xiGaussianTestC t n ((R : ℂ) + (y : ℂ) * I) *
        (((R : ℂ) + (y : ℂ) * I) - p)⁻¹) atTop (nhds 0) := by
  let D : ℝ := |a| + |b|
  let K : ℝ := |b - a| * Real.exp (t * D ^ (2 : ℕ))
  have hbase := tendsto_polyGaussian_atTop ht (2 * n) D
  have hmajor : Tendsto (fun R : ℝ =>
      K * ((D + |R|) ^ (2 * n) * Real.exp (-(t * R ^ (2 : ℕ))))) atTop (nhds 0) := by
    simpa using hbase.const_mul K
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (|p.re| + 1)] with R hR
  have hpoint : ∀ y ∈ Set.uIoc a b,
      ‖xiGaussianTestC t n ((R : ℂ) + (y : ℂ) * I) *
          (((R : ℂ) + (y : ℂ) * I) - p)⁻¹‖ ≤
        (D + |R|) ^ (2 * n) * Real.exp (t * D ^ (2 : ℕ)) *
          Real.exp (-(t * R ^ (2 : ℕ))) := by
    intro y hy
    rw [norm_mul, norm_inv]
    have hprofile := norm_xiGaussianTestC_le_on_horizontal_strip ht n (x := R) hy
    have hrele := Complex.abs_re_le_norm (((R : ℂ) + (y : ℂ) * I) - p)
    have hre : (((R : ℂ) + (y : ℂ) * I) - p).re = R - p.re := by simp
    rw [hre, abs_of_nonneg (by linarith [le_abs_self p.re])] at hrele
    have hreal : 1 ≤ R - p.re := by linarith [le_abs_self p.re]
    have hden : 1 ≤ ‖((R : ℂ) + (y : ℂ) * I) - p‖ := hreal.trans hrele
    have hinv : ‖((R : ℂ) + (y : ℂ) * I) - p‖⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hden
    calc
      ‖xiGaussianTestC t n ((R : ℂ) + (y : ℂ) * I)‖ *
          ‖((R : ℂ) + (y : ℂ) * I) - p‖⁻¹
        ≤ ‖xiGaussianTestC t n ((R : ℂ) + (y : ℂ) * I)‖ := by
          simpa using mul_le_of_le_one_right (norm_nonneg _) hinv
      _ ≤ (D + |R|) ^ (2 * n) * Real.exp (t * D ^ (2 : ℕ)) *
          Real.exp (-(t * R ^ (2 : ℕ))) := by simpa only [D] using hprofile
  calc
    ‖∫ y : ℝ in a..b,
        xiGaussianTestC t n ((R : ℂ) + (y : ℂ) * I) *
          (((R : ℂ) + (y : ℂ) * I) - p)⁻¹‖
      ≤ ((D + |R|) ^ (2 * n) * Real.exp (t * D ^ (2 : ℕ)) *
          Real.exp (-(t * R ^ (2 : ℕ)))) * |b - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = K * ((D + |R|) ^ (2 * n) * Real.exp (-(t * R ^ (2 : ℕ)))) := by
      simp only [K]
      ring

private theorem tendsto_xiGaussianTestC_cauchy_vertical_left
    {t : ℝ} (ht : 0 < t) (n : ℕ) (a b : ℝ) (p : ℂ) :
    Tendsto (fun R : ℝ => ∫ y : ℝ in a..b,
      xiGaussianTestC t n ((-R : ℂ) + (y : ℂ) * I) *
        (((-R : ℂ) + (y : ℂ) * I) - p)⁻¹) atTop (nhds 0) := by
  let D : ℝ := |a| + |b|
  let K : ℝ := |b - a| * Real.exp (t * D ^ (2 : ℕ))
  have hbase := tendsto_polyGaussian_atTop ht (2 * n) D
  have hmajor : Tendsto (fun R : ℝ =>
      K * ((D + |R|) ^ (2 * n) * Real.exp (-(t * R ^ (2 : ℕ))))) atTop (nhds 0) := by
    simpa using hbase.const_mul K
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards [eventually_ge_atTop (|p.re| + 1)] with R hR
  have hpoint : ∀ y ∈ Set.uIoc a b,
      ‖xiGaussianTestC t n ((-R : ℂ) + (y : ℂ) * I) *
          (((-R : ℂ) + (y : ℂ) * I) - p)⁻¹‖ ≤
        (D + |R|) ^ (2 * n) * Real.exp (t * D ^ (2 : ℕ)) *
          Real.exp (-(t * R ^ (2 : ℕ))) := by
    intro y hy
    rw [norm_mul, norm_inv]
    have hprofile := norm_xiGaussianTestC_le_on_horizontal_strip ht n (x := -R) hy
    have hrele := Complex.abs_re_le_norm (((-R : ℂ) + (y : ℂ) * I) - p)
    have hre : (((-R : ℂ) + (y : ℂ) * I) - p).re = -R - p.re := by simp
    rw [hre, abs_of_nonpos (by linarith [neg_abs_le p.re])] at hrele
    have hreal : 1 ≤ -(-R - p.re) := by linarith [neg_abs_le p.re]
    have hden : 1 ≤ ‖((-R : ℂ) + (y : ℂ) * I) - p‖ := hreal.trans hrele
    have hinv : ‖((-R : ℂ) + (y : ℂ) * I) - p‖⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ hden
    calc
      ‖xiGaussianTestC t n ((-R : ℂ) + (y : ℂ) * I)‖ *
          ‖((-R : ℂ) + (y : ℂ) * I) - p‖⁻¹
        ≤ ‖xiGaussianTestC t n ((-R : ℂ) + (y : ℂ) * I)‖ := by
          simpa using mul_le_of_le_one_right (norm_nonneg _) hinv
      _ ≤ (D + |R|) ^ (2 * n) * Real.exp (t * D ^ (2 : ℕ)) *
          Real.exp (-(t * R ^ (2 : ℕ))) := by
        simpa only [D, abs_neg, neg_sq, Complex.ofReal_neg] using hprofile
  calc
    ‖∫ y : ℝ in a..b,
        xiGaussianTestC t n ((-R : ℂ) + (y : ℂ) * I) *
          (((-R : ℂ) + (y : ℂ) * I) - p)⁻¹‖
      ≤ ((D + |R|) ^ (2 * n) * Real.exp (t * D ^ (2 : ℕ)) *
          Real.exp (-(t * R ^ (2 : ℕ)))) * |b - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = K * ((D + |R|) ^ (2 * n) * Real.exp (-(t * R ^ (2 : ℕ)))) := by
      simp only [K]
      ring

/-- **Exact Gaussian horizontal Cauchy wall crossing.**  The lower-line integral minus the
upper-line integral equals the literal residue for every positive heat time and every Hermite
degree. -/
theorem integral_xiGaussianTestC_horizontal_cauchy_residue
    {t : ℝ} (ht : 0 < t) (n : ℕ) {a b : ℝ} {p : ℂ}
    (ha : a < p.im) (hb : p.im < b) :
    (∫ x : ℝ,
        xiGaussianTestC t n ((x : ℂ) + (a : ℂ) * I) *
          (((x : ℂ) + (a : ℂ) * I) - p)⁻¹) -
      (∫ x : ℝ,
        xiGaussianTestC t n ((x : ℂ) + (b : ℂ) * I) *
          (((x : ℂ) + (b : ℂ) * I) - p)⁻¹) =
      2 * Real.pi * I * xiGaussianTestC t n p := by
  let F : ℂ → ℂ := fun z => xiGaussianTestC t n z * (z - p)⁻¹
  have hbottomInt : Integrable (fun x : ℝ => F ((x : ℂ) + (a : ℂ) * I)) := by
    exact integrable_xiGaussianTestC_horizontal_cauchy ht n (ne_of_lt ha)
  have htopInt : Integrable (fun x : ℝ => F ((x : ℂ) + (b : ℂ) * I)) := by
    exact integrable_xiGaussianTestC_horizontal_cauchy ht n (ne_of_gt hb)
  have hbottom := MeasureTheory.intervalIntegral_tendsto_integral hbottomInt
    tendsto_neg_atTop_atBot tendsto_id
  have htop := MeasureTheory.intervalIntegral_tendsto_integral htopInt
    tendsto_neg_atTop_atBot tendsto_id
  have hright := tendsto_xiGaussianTestC_cauchy_vertical_right ht n a b p
  have hleft := tendsto_xiGaussianTestC_cauchy_vertical_left ht n a b p
  have hlim := ((hbottom.sub htop).add (hright.const_smul I)).sub
    (hleft.const_smul I)
  have hrect : ∀ᶠ R : ℝ in atTop,
      rectIntegral F (((-R : ℝ) : ℂ) + (a : ℂ) * I)
          ((R : ℂ) + (b : ℂ) * I) =
        2 * Real.pi * I * xiGaussianTestC t n p := by
    filter_upwards [eventually_ge_atTop (|p.re| + 1)] with R hR
    apply rectIntegral_cauchyFormula_entire (analyticOnNhd_xiGaussianTestC t n)
    · simp only [Complex.add_re, Complex.ofReal_neg, Complex.neg_re,
        Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
      linarith [neg_abs_le p.re]
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
      linarith [le_abs_self p.re]
    · simpa using ha
    · simpa using hb
  have hlim' : Tendsto (fun R : ℝ =>
      rectIntegral F (((-R : ℝ) : ℂ) + (a : ℂ) * I)
        ((R : ℂ) + (b : ℂ) * I)) atTop
      (nhds ((∫ x : ℝ, F ((x : ℂ) + (a : ℂ) * I)) -
        ∫ x : ℝ, F ((x : ℂ) + (b : ℂ) * I))) := by
    simpa [rectIntegral, F, sub_eq_add_neg] using hlim
  have hconst : Tendsto (fun _ : ℝ =>
      2 * Real.pi * I * xiGaussianTestC t n p) atTop
      (nhds (2 * Real.pi * I * xiGaussianTestC t n p)) := tendsto_const_nhds
  have hconst' := hconst.congr' (hrect.mono fun _ h => h.symm)
  have huniq := tendsto_nhds_unique hlim' hconst'
  simpa only [F] using huniq

/-- The pole crossed by the completed Xi factor contributes the expected Gaussian--Hermite value
at `-i/2`. -/
theorem integral_xiGaussianTestC_completedPolar_residue
    {t c : ℝ} (ht : 0 < t) (hc : 1 / 2 < c) (n : ℕ) :
    (∫ x : ℝ,
        xiGaussianTestC t n ((x : ℂ) - (c : ℂ) * I) *
          (((x : ℂ) - (c : ℂ) * I) + I / 2)⁻¹) -
      (∫ x : ℝ,
        xiGaussianTestC t n (x : ℂ) * (((x : ℂ) + I / 2)⁻¹)) =
      2 * Real.pi * I * xiGaussianTestC t n (-I / 2) := by
  have h := integral_xiGaussianTestC_horizontal_cauchy_residue ht n
    (a := -c) (b := 0) (p := -I / 2)
    (by simp; linarith) (by norm_num)
  have hbottomPoint (x : ℝ) :
      xiGaussianTestC t n ((x : ℂ) + ((-c : ℝ) : ℂ) * I) *
          (((x : ℂ) + ((-c : ℝ) : ℂ) * I) - (-I / 2))⁻¹ =
        xiGaussianTestC t n ((x : ℂ) - (c : ℂ) * I) *
          (((x : ℂ) - (c : ℂ) * I) + I / 2)⁻¹ := by
    congr 2 <;> push_cast <;> ring
  have htopPoint (x : ℝ) :
      xiGaussianTestC t n ((x : ℂ) + ((0 : ℝ) : ℂ) * I) *
          (((x : ℂ) + ((0 : ℝ) : ℂ) * I) - (-I / 2))⁻¹ =
        xiGaussianTestC t n (x : ℂ) * (((x : ℂ) + I / 2)⁻¹) := by
    congr 2 <;> push_cast <;> ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hbottomPoint),
    integral_congr_ae (Filter.Eventually.of_forall htopPoint)] at h
  exact h

@[simp]
theorem xiGaussianTestC_neg_I_half (t : ℝ) (n : ℕ) :
    xiGaussianTestC t n (-I / 2) =
      ((-1 / 4 : ℂ) ^ n) * Complex.exp ((t / 4 : ℝ) : ℂ) := by
  rw [xiGaussianTestC]
  have hsq : (-I / 2 : ℂ) ^ (2 : ℕ) = -1 / 4 := by
    rw [div_pow, neg_sq, Complex.I_sq]
    norm_num
  rw [show 2 * n = 2 * n by rfl, pow_mul, hsq]
  congr 1
  congr 1
  push_cast
  ring

@[simp]
theorem xiGaussianTestC_neg (t : ℝ) (n : ℕ) (z : ℂ) :
    xiGaussianTestC t n (-z) = xiGaussianTestC t n z := by
  rw [xiGaussianTestC, xiGaussianTestC, neg_sq, neg_pow]
  have heven : Even (2 * n) := by simp
  rw [Even.neg_one_pow heven, one_mul]

/-- **Completed polar pair, already folded.**  On the absolute-Euler bottom line, the two rational
terms of the completed factor combine to the single crossed pole at `-i/2`.  Their full integral is
exactly `2π` times the Gaussian--Hermite value at that pole. -/
theorem integral_xiGaussianTestC_completedPolarPair
    {t c : ℝ} (ht : 0 < t) (hc : 1 / 2 < c) (n : ℕ) :
    (∫ x : ℝ,
      xiGaussianTestC t n ((x : ℂ) - (c : ℂ) * I) *
        (((1 / 2 : ℂ) + I * ((x : ℂ) - (c : ℂ) * I))⁻¹ +
          ((-1 / 2 : ℂ) + I * ((x : ℂ) - (c : ℂ) * I))⁻¹)) =
      2 * Real.pi * xiGaussianTestC t n (-I / 2) := by
  let Lminus : ℝ → ℂ := fun x =>
    xiGaussianTestC t n ((x : ℂ) - (c : ℂ) * I) *
      (((x : ℂ) - (c : ℂ) * I) - I / 2)⁻¹
  let Lplus : ℝ → ℂ := fun x =>
    xiGaussianTestC t n ((x : ℂ) - (c : ℂ) * I) *
      (((x : ℂ) - (c : ℂ) * I) + I / 2)⁻¹
  let Uplus : ℝ → ℂ := fun x =>
    xiGaussianTestC t n ((x : ℂ) + (c : ℂ) * I) *
      (((x : ℂ) + (c : ℂ) * I) + I / 2)⁻¹
  have hminusInt : Integrable Lminus := by
    have hbase := integrable_xiGaussianTestC_horizontal_cauchy ht n
      (y := -c) (p := I / 2) (by simp; linarith)
    apply hbase.congr
    filter_upwards with x
    dsimp only [Lminus]
    congr 2 <;> push_cast <;> ring
  have hplusInt : Integrable Lplus := by
    have hbase := integrable_xiGaussianTestC_horizontal_cauchy ht n
      (y := -c) (p := -I / 2) (by simp; linarith)
    apply hbase.congr
    filter_upwards with x
    dsimp only [Lplus]
    congr 2 <;> push_cast <;> ring
  have hUplusInt : Integrable Uplus := by
    have hbase := integrable_xiGaussianTestC_horizontal_cauchy ht n
      (y := c) (p := -I / 2) (by simp; linarith)
    apply hbase.congr
    filter_upwards with x
    dsimp only [Uplus]
    congr 2 <;> ring
  have hreflect (x : ℝ) : Lminus x = -Uplus (-x) := by
    dsimp only [Lminus, Uplus]
    rw [show ((-x : ℝ) : ℂ) + (c : ℂ) * I =
        -((x : ℂ) - (c : ℂ) * I) by push_cast; ring,
      xiGaussianTestC_neg, show
        -((x : ℂ) - (c : ℂ) * I) + I / 2 =
          -(((x : ℂ) - (c : ℂ) * I) - I / 2) by ring,
      inv_neg]
    ring
  have hminusIntegral : (∫ x : ℝ, Lminus x) = -(∫ x : ℝ, Uplus x) := by
    calc
      (∫ x : ℝ, Lminus x) = ∫ x : ℝ, -Uplus (-x) :=
        integral_congr_ae (Filter.Eventually.of_forall hreflect)
      _ = -(∫ x : ℝ, Uplus (-x)) := by rw [MeasureTheory.integral_neg]
      _ = -(∫ x : ℝ, Uplus x) := by rw [MeasureTheory.integral_neg_eq_self]
  have hres := integral_xiGaussianTestC_horizontal_cauchy_residue ht n
    (a := -c) (b := c) (p := -I / 2)
    (by simp; linarith) (by simp; linarith)
  have hres' : (∫ x : ℝ, Lplus x) - (∫ x : ℝ, Uplus x) =
      2 * Real.pi * I * xiGaussianTestC t n (-I / 2) := by
    have hbottomPoint (x : ℝ) :
        xiGaussianTestC t n ((x : ℂ) + ((-c : ℝ) : ℂ) * I) *
            (((x : ℂ) + ((-c : ℝ) : ℂ) * I) - (-I / 2))⁻¹ = Lplus x := by
      dsimp only [Lplus]
      congr 2 <;> push_cast <;> ring
    have htopPoint (x : ℝ) :
        xiGaussianTestC t n ((x : ℂ) + (c : ℂ) * I) *
            (((x : ℂ) + (c : ℂ) * I) - (-I / 2))⁻¹ = Uplus x := by
      dsimp only [Uplus]
      congr 2 <;> ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hbottomPoint),
      integral_congr_ae (Filter.Eventually.of_forall htopPoint)] at hres
    exact hres
  have hpolarPoint (x : ℝ) :
      xiGaussianTestC t n ((x : ℂ) - (c : ℂ) * I) *
          (((1 / 2 : ℂ) + I * ((x : ℂ) - (c : ℂ) * I))⁻¹ +
            ((-1 / 2 : ℂ) + I * ((x : ℂ) - (c : ℂ) * I))⁻¹) =
        -I * (Lminus x + Lplus x) := by
    dsimp only [Lminus, Lplus]
    have hfirst :
        ((1 / 2 : ℂ) + I * ((x : ℂ) - (c : ℂ) * I)) =
          I * (((x : ℂ) - (c : ℂ) * I) - I / 2) := by
      have hIhalf : I * (I / 2) = (-1 / 2 : ℂ) := by
        rw [mul_div, Complex.I_mul_I]
      calc
        ((1 / 2 : ℂ) + I * ((x : ℂ) - (c : ℂ) * I)) =
            I * (x : ℂ) - I * ((c : ℂ) * I) + 1 / 2 := by ring
        _ = I * (x : ℂ) - I * ((c : ℂ) * I) - I * (I / 2) := by
          rw [hIhalf]
          ring
        _ = I * (((x : ℂ) - (c : ℂ) * I) - I / 2) := by ring
    have hsecond :
        ((-1 / 2 : ℂ) + I * ((x : ℂ) - (c : ℂ) * I)) =
          I * (((x : ℂ) - (c : ℂ) * I) + I / 2) := by
      have hIhalf : I * (I / 2) = (-1 / 2 : ℂ) := by
        rw [mul_div, Complex.I_mul_I]
      rw [mul_add, hIhalf]
      ring
    rw [hfirst, hsecond, mul_inv, mul_inv, Complex.inv_I]
    ring
  calc
    (∫ x : ℝ,
        xiGaussianTestC t n ((x : ℂ) - (c : ℂ) * I) *
          (((1 / 2 : ℂ) + I * ((x : ℂ) - (c : ℂ) * I))⁻¹ +
            ((-1 / 2 : ℂ) + I * ((x : ℂ) - (c : ℂ) * I))⁻¹)) =
        ∫ x : ℝ, -I * (Lminus x + Lplus x) :=
      integral_congr_ae (Filter.Eventually.of_forall hpolarPoint)
    _ = -I * (∫ x : ℝ, Lminus x + Lplus x) := by
      rw [MeasureTheory.integral_const_mul]
    _ = -I * ((∫ x : ℝ, Lminus x) + ∫ x : ℝ, Lplus x) := by
      rw [MeasureTheory.integral_add hminusInt hplusInt]
    _ = -I * (-(∫ x : ℝ, Uplus x) + ∫ x : ℝ, Lplus x) := by
      rw [hminusIntegral]
    _ = -I * ((∫ x : ℝ, Lplus x) - ∫ x : ℝ, Uplus x) := by ring
    _ = -I * (2 * Real.pi * I * xiGaussianTestC t n (-I / 2)) := by rw [hres']
    _ = 2 * Real.pi * xiGaussianTestC t n (-I / 2) := by
      rw [show -I * (2 * Real.pi * I * xiGaussianTestC t n (-I / 2)) =
        2 * Real.pi * (-(I * I)) * xiGaussianTestC t n (-I / 2) by ring,
        Complex.I_mul_I]
      ring

end

end RHTower
