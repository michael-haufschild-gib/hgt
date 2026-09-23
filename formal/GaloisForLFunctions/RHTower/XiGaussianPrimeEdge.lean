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

theorem integrable_xiGaussianTestC_fourier_horizontal
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
      Real.exp (t * c ^ (2 : ℕ) + |w| * c) *
        ((c + |x|) ^ (2 * k) * Real.exp (-(t * x ^ (2 : ℕ)))) := by
  have hyIcc : -c ≤ y ∧ y ≤ 0 := by
    rw [Set.uIoc_of_le (by linarith)] at hy
    exact ⟨hy.1.le, hy.2⟩
  have hyabs : |y| ≤ c := by rw [abs_le]; constructor <;> linarith
  have hprofile :
      ‖xiGaussianTestC t k ((x : ℂ) + (y : ℂ) * I)‖ ≤
        (c + |x|) ^ (2 * k) * Real.exp (t * c ^ (2 : ℕ)) *
          Real.exp (-(t * x ^ (2 : ℕ))) := by
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
      ≤ ((c + |x|) ^ (2 * k) * Real.exp (t * c ^ (2 : ℕ)) *
          Real.exp (-(t * x ^ (2 : ℕ)))) * Real.exp (|w| * c) :=
        mul_le_mul hprofile hphaseBound (Real.exp_nonneg _) (by positivity)
    _ = Real.exp (t * c ^ (2 : ℕ) + |w| * c) *
        ((c + |x|) ^ (2 * k) * Real.exp (-(t * x ^ (2 : ℕ)))) := by
      rw [Real.exp_add]
      ring

private theorem tendsto_xiGaussianTestC_fourier_vertical_right
    {t : ℝ} (ht : 0 < t) (k : ℕ) (c w : ℝ) (hc : 0 ≤ c) :
    Tendsto (fun R : ℝ => ∫ y : ℝ in (-c)..0,
      xiGaussianTestC t k ((R : ℂ) + (y : ℂ) * I) *
        Complex.exp (-(I * (w : ℂ) * ((R : ℂ) + (y : ℂ) * I))))
      atTop (nhds 0) := by
  let K : ℝ := c * Real.exp (t * c ^ (2 : ℕ) + |w| * c)
  have hbase := tendsto_polyGaussian_atTop ht (2 * k) c
  have hmajor : Tendsto (fun R : ℝ =>
      K * ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ))))) atTop (nhds 0) := by
    simpa using hbase.const_mul K
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards with R
  have hpoint : ∀ y ∈ Set.uIoc (-c) 0,
      ‖xiGaussianTestC t k ((R : ℂ) + (y : ℂ) * I) *
          Complex.exp (-(I * (w : ℂ) * ((R : ℂ) + (y : ℂ) * I)))‖ ≤
        Real.exp (t * c ^ (2 : ℕ) + |w| * c) *
          ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ)))) :=
    fun y hy => norm_xiGaussianTestC_fourier_le_on_lower_strip ht k hc hy
  calc
    ‖∫ y : ℝ in (-c)..0,
        xiGaussianTestC t k ((R : ℂ) + (y : ℂ) * I) *
          Complex.exp (-(I * (w : ℂ) * ((R : ℂ) + (y : ℂ) * I)))‖
      ≤ (Real.exp (t * c ^ (2 : ℕ) + |w| * c) *
          ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ))))) * |0 - (-c)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = K * ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ)))) := by
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
  let K : ℝ := c * Real.exp (t * c ^ (2 : ℕ) + |w| * c)
  have hbase := tendsto_polyGaussian_atTop ht (2 * k) c
  have hmajor : Tendsto (fun R : ℝ =>
      K * ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ))))) atTop (nhds 0) := by
    simpa using hbase.const_mul K
  refine squeeze_zero_norm' ?_ hmajor
  filter_upwards with R
  have hpoint : ∀ y ∈ Set.uIoc (-c) 0,
      ‖xiGaussianTestC t k ((-R : ℂ) + (y : ℂ) * I) *
          Complex.exp (-(I * (w : ℂ) * ((-R : ℂ) + (y : ℂ) * I)))‖ ≤
        Real.exp (t * c ^ (2 : ℕ) + |w| * c) *
          ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ)))) := by
    intro y hy
    have h := norm_xiGaussianTestC_fourier_le_on_lower_strip ht k hc
      (x := -R) (w := w) hy
    simpa only [abs_neg, neg_sq, Complex.ofReal_neg] using h
  calc
    ‖∫ y : ℝ in (-c)..0,
        xiGaussianTestC t k ((-R : ℂ) + (y : ℂ) * I) *
          Complex.exp (-(I * (w : ℂ) * ((-R : ℂ) + (y : ℂ) * I)))‖
      ≤ (Real.exp (t * c ^ (2 : ℕ) + |w| * c) *
          ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ))))) * |0 - (-c)| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = K * ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ)))) := by
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

/-- One literal von-Mangoldt atom on the Gaussian bottom edge. -/
def xiGaussianBottomPrimeAtomIntegrand
    (t : ℝ) (k : ℕ) (c : ℝ) (n : ℕ) (x : ℝ) : ℂ :=
  xiGaussianTestC t k ((x : ℂ) - (c : ℂ) * I) *
    LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      (xiMassBottomEulerPoint c x) n

/-- Depth-free critical half-density atom read by the Gaussian Fourier transform. -/
def xiGaussianCenteredPrimeAtom
    (t : ℝ) (k : ℕ) (n : ℕ) : ℂ :=
  LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ)) (1 / 2 : ℂ) n *
    xiGaussianHermiteFourier t k (Real.log n)

/-- Full literal von-Mangoldt series on the Gaussian bottom edge. -/
def xiGaussianBottomPrimeIntegrand
    (t : ℝ) (k : ℕ) (c : ℝ) (x : ℝ) : ℂ :=
  xiGaussianTestC t k ((x : ℂ) - (c : ℂ) * I) *
    LSeries (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
      (xiMassBottomEulerPoint c x)

/-- Exact atomwise Euler-depth erasure for every Gaussian--Hermite degree. -/
theorem integral_xiGaussianBottomPrimeAtom_eq_centered
    {t c : ℝ} (ht : 0 < t) (hc : 0 ≤ c) (k n : ℕ) :
    (∫ x : ℝ, xiGaussianBottomPrimeAtomIntegrand t k c n x) =
      xiGaussianCenteredPrimeAtom t k n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [xiGaussianBottomPrimeAtomIntegrand, xiGaussianCenteredPrimeAtom,
      LSeries.term_zero]
  · let F : ℂ → ℂ := fun z =>
      xiGaussianTestC t k z * Complex.exp (-(I * (Real.log n : ℂ) * z))
    have hshift := integral_xiGaussianTestC_fourier_horizontal_shift
      ht k hc (Real.log n)
    have hpoint (x : ℝ) :
        xiGaussianBottomPrimeAtomIntegrand t k c n x =
          LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (1 / 2 : ℂ) n * F ((x : ℂ) - (c : ℂ) * I) := by
      rw [xiGaussianBottomPrimeAtomIntegrand,
        xiMassBottomLSeriesTerm_eq_centered_mul_fourierPhase hn]
      dsimp only [F]
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
      MeasureTheory.integral_const_mul, hshift]
    rfl

private theorem integrable_xiGaussianBottomPrimeAtomIntegrand
    {t c : ℝ} (ht : 0 < t) (k n : ℕ) :
    Integrable (xiGaussianBottomPrimeAtomIntegrand t k c n) := by
  rcases eq_or_ne n 0 with rfl | hn
  · rw [show xiGaussianBottomPrimeAtomIntegrand t k c 0 = fun _ : ℝ => (0 : ℂ) by
      funext x
      rw [xiGaussianBottomPrimeAtomIntegrand, LSeries.term_zero, mul_zero]]
    exact integrable_zero ℝ ℂ MeasureTheory.volume
  · let F : ℝ → ℂ := fun x =>
      xiGaussianTestC t k ((x : ℂ) - (c : ℂ) * I) *
        Complex.exp (-(I * (Real.log n : ℂ) * ((x : ℂ) - (c : ℂ) * I)))
    have hF : Integrable F := by
      have hbase := integrable_xiGaussianTestC_fourier_horizontal ht k (Real.log n) (-c)
      apply hbase.congr
      filter_upwards with x
      dsimp only [F]
      congr 2 <;> push_cast <;> ring
    have hpoint (x : ℝ) :
        xiGaussianBottomPrimeAtomIntegrand t k c n x =
          LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
              (1 / 2 : ℂ) n * F x := by
      rw [xiGaussianBottomPrimeAtomIntegrand,
        xiMassBottomLSeriesTerm_eq_centered_mul_fourierPhase hn]
      dsimp only [F]
      ring
    apply (hF.const_mul
      (LSeries.term (fun m => (ArithmeticFunction.vonMangoldt m : ℂ))
        (1 / 2 : ℂ) n)).congr
    filter_upwards with x
    exact (hpoint x).symm

private theorem norm_xiGaussianBottomPrimeAtomIntegrand
    {t c : ℝ} (k n : ℕ) (x : ℝ) :
    ‖xiGaussianBottomPrimeAtomIntegrand t k c n x‖ =
      xiMassBottomPrimeAtomWeight c n *
        ‖xiGaussianTestC t k ((x : ℂ) - (c : ℂ) * I)‖ := by
  rw [xiGaussianBottomPrimeAtomIntegrand, norm_mul, mul_comm]
  congr 1
  unfold xiMassBottomPrimeAtomWeight
  rw [LSeries.norm_term_eq, LSeries.norm_term_eq]
  simp [xiMassBottomEulerPoint, Complex.mul_re]

private theorem summable_integral_norm_xiGaussianBottomPrimeAtomIntegrand
    {t c : ℝ} (hhalf : 1 / 2 < c) (k : ℕ) :
    Summable (fun n : ℕ =>
      ∫ x : ℝ, ‖xiGaussianBottomPrimeAtomIntegrand t k c n x‖) := by
  let J : ℝ := ∫ x : ℝ,
    ‖xiGaussianTestC t k ((x : ℂ) - (c : ℂ) * I)‖
  have hnormIntegral (n : ℕ) :
      (∫ x : ℝ, ‖xiGaussianBottomPrimeAtomIntegrand t k c n x‖) =
        xiMassBottomPrimeAtomWeight c n * J := by
    rw [show (fun x : ℝ => ‖xiGaussianBottomPrimeAtomIntegrand t k c n x‖) =
        fun x : ℝ => xiMassBottomPrimeAtomWeight c n *
          ‖xiGaussianTestC t k ((x : ℂ) - (c : ℂ) * I)‖ by
      funext x
      exact norm_xiGaussianBottomPrimeAtomIntegrand k n x,
      MeasureTheory.integral_const_mul]
  rw [show (fun n : ℕ =>
      ∫ x : ℝ, ‖xiGaussianBottomPrimeAtomIntegrand t k c n x‖) =
        fun n => xiMassBottomPrimeAtomWeight c n * J by
    funext n
    exact hnormIntegral n]
  exact (summable_xiMassBottomPrimeAtomWeight hhalf).mul_right J

/-- The critical half-density Gaussian--Hermite prime atoms are absolutely summable for every
positive heat time. -/
theorem summable_xiGaussianCenteredPrimeAtom
    {t : ℝ} (ht : 0 < t) (k : ℕ) :
    Summable (xiGaussianCenteredPrimeAtom t k) := by
  have hmajor := summable_integral_norm_xiGaussianBottomPrimeAtomIntegrand
    (t := t) (c := (1 : ℝ)) (by norm_num) k
  refine Summable.of_norm_bounded hmajor fun n => ?_
  rw [← integral_xiGaussianBottomPrimeAtom_eq_centered
    ht (by norm_num : (0 : ℝ) ≤ 1) k n]
  exact norm_integral_le_integral_norm _

/-- **Exact full Gaussian prime edge.**  The literal Euler-line von-Mangoldt integral equals the
absolutely convergent depth-free half-density Fourier series. -/
theorem integral_xiGaussianBottomPrimeIntegrand_eq_tsum_centered
    {t c : ℝ} (ht : 0 < t) (hhalf : 1 / 2 < c) (k : ℕ) :
    (∫ x : ℝ, xiGaussianBottomPrimeIntegrand t k c x) =
      ∑' n : ℕ, xiGaussianCenteredPrimeAtom t k n := by
  let F : ℕ → ℝ → ℂ := fun n x => xiGaussianBottomPrimeAtomIntegrand t k c n x
  have hc : 0 ≤ c := (lt_trans (by norm_num) hhalf).le
  have hFint : ∀ n, Integrable (F n) := fun n =>
    integrable_xiGaussianBottomPrimeAtomIntegrand ht k n
  have hFsum : Summable (fun n => ∫ x : ℝ, ‖F n x‖) :=
    summable_integral_norm_xiGaussianBottomPrimeAtomIntegrand hhalf k
  have hinterchange := integral_tsum_of_summable_integral_norm hFint hFsum
  rw [show (fun x : ℝ => ∑' n, F n x) =
      xiGaussianBottomPrimeIntegrand t k c by
    funext x
    have hsum : LSeriesSummable
        (fun n => (ArithmeticFunction.vonMangoldt n : ℂ))
          (xiMassBottomEulerPoint c x) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by
        simp [xiMassBottomEulerPoint]
        linarith)
    dsimp only [F, xiGaussianBottomPrimeAtomIntegrand,
      xiGaussianBottomPrimeIntegrand]
    rw [LSeries, ← tsum_mul_left]] at hinterchange
  rw [show (fun n : ℕ => ∫ x : ℝ, F n x) =
      xiGaussianCenteredPrimeAtom t k by
    funext n
    exact integral_xiGaussianBottomPrimeAtom_eq_centered ht hc k n] at hinterchange
  exact hinterchange.symm

end

end RHTower
