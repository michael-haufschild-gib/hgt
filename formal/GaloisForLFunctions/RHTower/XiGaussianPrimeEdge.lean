import GaloisForLFunctions.RHTower.XiGaussianHorizontalCauchyResidue
import GaloisForLFunctions.RHTower.XiMassBottomPrimeAtomization

/-!
# Exact von-Mangoldt edge for Gaussian--Hermite tests

The Euler depth on each von-Mangoldt atom is erased by a genuine Gaussian horizontal contour
shift.  Absolute summability on every legal Euler line then permits the Bochner integral and the
Dirichlet series to interchange.  The result is the literal half-density prime Fourier series,
with no truncation and no numerical certification.
-/

open Complex Filter MeasureTheory Set Topology intervalIntegral

namespace RHTower

noncomputable section

/-- Unnormalized Fourier transform of one centered Gaussian--Hermite monomial. -/
def xiGaussianHermiteFourier (t : ℝ) (k : ℕ) (w : ℝ) : ℂ :=
  ∫ x : ℝ, xiGaussianTestC t k (x : ℂ) *
    Complex.exp (-(I * (w : ℂ) * (x : ℂ)))

private theorem integrable_xiGaussianTestC_fourier_horizontal
    {t : ℝ} (ht : 0 < t) (k : ℕ) (w y : ℝ) :
    Integrable (fun x : ℝ =>
      xiGaussianTestC t k ((x : ℂ) + (y : ℂ) * I) *
        Complex.exp (-(I * (w : ℂ) * ((x : ℂ) + (y : ℂ) * I)))) := by
  have hprofile := integrable_xiGaussianTestC_horizontal ht k y
  let C : ℝ := Real.exp (|w| * |y|)
  have hmajor : Integrable (fun x : ℝ =>
      C * ‖xiGaussianTestC t k ((x : ℂ) + (y : ℂ) * I)‖) :=
    hprofile.norm.const_mul C
  refine Integrable.mono' hmajor ?_ (Filter.Eventually.of_forall fun x => ?_)
  · have hprofileCont : Continuous (fun x : ℝ =>
        xiGaussianTestC t k ((x : ℂ) + (y : ℂ) * I)) := by
      unfold xiGaussianTestC
      fun_prop
    exact (hprofileCont.mul (Complex.continuous_exp.comp (by fun_prop))).aestronglyMeasurable
  · rw [norm_mul, Complex.norm_exp]
    have hphase : (-(I * (w : ℂ) * ((x : ℂ) + (y : ℂ) * I))).re = w * y := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hphase]
    have hwy : w * y ≤ |w| * |y| := by
      calc
        w * y ≤ |w * y| := le_abs_self _
        _ = |w| * |y| := abs_mul _ _
    have hexp := Real.exp_le_exp.mpr hwy
    calc
      ‖xiGaussianTestC t k ((x : ℂ) + (y : ℂ) * I)‖ * Real.exp (w * y)
        ≤ ‖xiGaussianTestC t k ((x : ℂ) + (y : ℂ) * I)‖ * C :=
          mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ = C * ‖xiGaussianTestC t k ((x : ℂ) + (y : ℂ) * I)‖ := by ring

private theorem norm_xiGaussianTestC_fourier_le_on_lower_strip
    {t : ℝ} (ht : 0 < t) (k : ℕ) {c x y w : ℝ}
    (hc : 0 ≤ c) (hy : y ∈ Set.uIoc (-c) 0) :
    ‖xiGaussianTestC t k ((x : ℂ) + (y : ℂ) * I) *
        Complex.exp (-(I * (w : ℂ) * ((x : ℂ) + (y : ℂ) * I)))‖ ≤
      Real.exp (t * c ^ 2 + |w| * c) *
        ((c + |x|) ^ (2 * k) * Real.exp (-(t * x ^ 2))) := by
  have hyIcc : -c ≤ y ∧ y ≤ 0 := by
    rw [Set.uIoc_of_le (by linarith)] at hy
    exact ⟨hy.1.le, hy.2⟩
  have hyabs : |y| ≤ c := by rw [abs_le]; constructor <;> linarith
  have hprofile :
      ‖xiGaussianTestC t k ((x : ℂ) + (y : ℂ) * I)‖ ≤
        (c + |x|) ^ (2 * k) * Real.exp (t * c ^ 2) *
          Real.exp (-(t * x ^ 2)) := by
    rw [norm_xiGaussianTestC_eq_norm_rotated]
    have h := norm_xiGaussianTest_le_of_strip ht k hc
      (s := (((1 / 2 - y : ℝ) : ℂ) + (x : ℂ) * I)) (by simpa using hyabs)
    simpa [add_assoc, add_comm, add_left_comm] using h
  rw [norm_mul, Complex.norm_exp]
  have hphase : (-(I * (w : ℂ) * ((x : ℂ) + (y : ℂ) * I))).re = w * y := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hphase]
  have hwy : w * y ≤ |w| * c := by
    calc
      w * y ≤ |w * y| := le_abs_self _
      _ = |w| * |y| := abs_mul _ _
      _ ≤ |w| * c := mul_le_mul_of_nonneg_left hyabs (abs_nonneg _)
  have hphaseBound := Real.exp_le_exp.mpr hwy
  calc
    ‖xiGaussianTestC t k ((x : ℂ) + (y : ℂ) * I)‖ * Real.exp (w * y)
      ≤ ((c + |x|) ^ (2 * k) * Real.exp (t * c ^ 2) *
          Real.exp (-(t * x ^ 2))) * Real.exp (|w| * c) :=
        mul_le_mul hprofile hphaseBound (Real.exp_nonneg _) (by positivity)
    _ = Real.exp (t * c ^ 2 + |w| * c) *
        ((c + |x|) ^ (2 * k) * Real.exp (-(t * x ^ 2))) := by
      rw [Real.exp_add]
      ring

private theorem tendsto_xiGaussianTestC_fourier_vertical_right
    {t : ℝ} (ht : 0 < t) (k : ℕ) (c w : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun R : ℝ => ∫ y : ℝ in (-c)..0,
      xiGaussianTestC t k ((R : ℂ) + (y : ℂ) * I) *
        Complex.exp (-(I * (w : ℂ) * ((R : ℂ) + (y : ℂ) * I))))
      atTop (nhds 0) := by
  let K : ℝ := c * Real.exp (t * c ^ 2 + |w| * c)
  have hbase := tendsto_polyGaussian_atTop ht (2 * k) c
  have hmajor : Tendsto (fun R : ℝ =>
      K * ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ 2)))) atTop (nhds 0) := by
    simpa using hbase.const_mul K
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards with R
  have hpoint : ∀ y ∈ Set.uIoc (-c) 0,
      ‖xiGaussianTestC t k ((R : ℂ) + (y : ℂ) * I) *
          Complex.exp (-(I * (w : ℂ) * ((R : ℂ) + (y : ℂ) * I)))‖ ≤
        Real.exp (t * c ^ 2 + |w| * c) *
          ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ 2))) :=
    fun y hy => norm_xiGaussianTestC_fourier_le_on_lower_strip ht k hc hy
  calc
    ‖∫ y : ℝ in (-c)..0,
        xiGaussianTestC t k ((R : ℂ) + (y : ℂ) * I) *
          Complex.exp (-(I * (w : ℂ) * ((R : ℂ) + (y : ℂ) * I)))‖
      ≤ (Real.exp (t * c ^ 2 + |w| * c) *
          ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ 2)))) * |0 - (-c)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = K * ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ 2))) := by
      have habs : |(0 : ℝ) - -c| = c := by
        rw [sub_neg_eq_add, zero_add, abs_of_nonneg hc]
      rw [habs]
      simp only [K]
      ring

private theorem tendsto_xiGaussianTestC_fourier_vertical_left
    {t : ℝ} (ht : 0 < t) (k : ℕ) (c w : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun R : ℝ => ∫ y : ℝ in (-c)..0,
      xiGaussianTestC t k ((-R : ℂ) + (y : ℂ) * I) *
        Complex.exp (-(I * (w : ℂ) * ((-R : ℂ) + (y : ℂ) * I))))
      atTop (nhds 0) := by
  let K : ℝ := c * Real.exp (t * c ^ 2 + |w| * c)
  have hbase := tendsto_polyGaussian_atTop ht (2 * k) c
  have hmajor : Tendsto (fun R : ℝ =>
      K * ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ 2)))) atTop (nhds 0) := by
    simpa using hbase.const_mul K
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards with R
  have hpoint : ∀ y ∈ Set.uIoc (-c) 0,
      ‖xiGaussianTestC t k ((-R : ℂ) + (y : ℂ) * I) *
          Complex.exp (-(I * (w : ℂ) * ((-R : ℂ) + (y : ℂ) * I)))‖ ≤
        Real.exp (t * c ^ 2 + |w| * c) *
          ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ 2))) := by
    intro y hy
    have h := norm_xiGaussianTestC_fourier_le_on_lower_strip ht k hc
      (x := -R) (w := w) hy
    simpa only [abs_neg, neg_sq, Complex.ofReal_neg] using h
  calc
    ‖∫ y : ℝ in (-c)..0,
        xiGaussianTestC t k ((-R : ℂ) + (y : ℂ) * I) *
          Complex.exp (-(I * (w : ℂ) * ((-R : ℂ) + (y : ℂ) * I)))‖
      ≤ (Real.exp (t * c ^ 2 + |w| * c) *
          ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ 2)))) * |0 - (-c)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = K * ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ 2))) := by
      have habs : |(0 : ℝ) - -c| = c := by
        rw [sub_neg_eq_add, zero_add, abs_of_nonneg hc]
      rw [habs]
      simp only [K]
      ring

/-- **Gaussian Fourier horizontal shift.**  Every finite lower shift has the same Fourier integral
after the Fourier character is evaluated on the shifted complex point. -/
theorem integral_xiGaussianTestC_fourier_horizontal_shift
    {t : ℝ} (ht : 0 < t) (k : ℕ) {c : ℝ} (hc : 0 ≤ c) (w : ℝ) :
    (∫ x : ℝ,
      xiGaussianTestC t k ((x : ℂ) - (c : ℂ) * I) *
        Complex.exp (-(I * (w : ℂ) * ((x : ℂ) - (c : ℂ) * I)))) =
      xiGaussianHermiteFourier t k w := by
  let F : ℂ → ℂ := fun z =>
    xiGaussianTestC t k z * Complex.exp (-(I * (w : ℂ) * z))
  have hbottomInt : Integrable (fun x : ℝ => F ((x : ℂ) - (c : ℂ) * I)) := by
    have hbase := integrable_xiGaussianTestC_fourier_horizontal ht k w (-c)
    apply hbase.congr
    filter_upwards with x
    dsimp only [F]
    congr 2 <;> push_cast <;> ring
  have htopInt : Integrable (fun x : ℝ => F (x : ℂ)) := by
    have hbase := integrable_xiGaussianTestC_fourier_horizontal ht k w 0
    apply hbase.congr
    filter_upwards with x
    dsimp only [F]
    congr 2 <;> push_cast <;> ring
  have hbottom := MeasureTheory.intervalIntegral_tendsto_integral hbottomInt
    tendsto_neg_atTop_atBot tendsto_id
  have htop := MeasureTheory.intervalIntegral_tendsto_integral htopInt
    tendsto_neg_atTop_atBot tendsto_id
  have hright := tendsto_xiGaussianTestC_fourier_vertical_right ht k c w hc
  have hleft := tendsto_xiGaussianTestC_fourier_vertical_left ht k c w hc
  have hlim := ((hbottom.sub htop).add (hright.const_smul I)).sub
    (hleft.const_smul I)
  have hrect : ∀ R : ℝ,
      rectIntegral F (((-R : ℝ) : ℂ) - (c : ℂ) * I) (R : ℂ) = 0 := by
    intro R
    apply rectIntegral_eq_zero_of_analyticOnNhd (U := Set.univ) (by simp)
    exact (differentiable_xiGaussianTestC t k).mul
      (Complex.differentiable_exp.comp (by fun_prop) ) |>.differentiableOn.analyticOnNhd isOpen_univ
  have hlim' : Tendsto (fun R : ℝ =>
      rectIntegral F (((-R : ℝ) : ℂ) - (c : ℂ) * I) (R : ℂ)) atTop
      (nhds ((∫ x : ℝ, F ((x : ℂ) - (c : ℂ) * I)) - ∫ x : ℝ, F (x : ℂ))) := by
    simpa [rectIntegral, F, sub_eq_add_neg] using hlim
  have hzero : Tendsto (fun _ : ℝ => (0 : ℂ)) atTop (nhds 0) := tendsto_const_nhds
  have hzero' := hzero.congr' (Filter.Eventually.of_forall fun R => (hrect R).symm)
  have huniq := tendsto_nhds_unique hlim' hzero'
  have heq : (∫ x : ℝ, F ((x : ℂ) - (c : ℂ) * I)) = ∫ x : ℝ, F (x : ℂ) :=
    sub_eq_zero.mp (by simpa using huniq)
  simpa only [F, xiGaussianHermiteFourier] using heq

end

end RHTower
