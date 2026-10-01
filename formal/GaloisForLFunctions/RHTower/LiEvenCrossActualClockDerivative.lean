import GaloisForLFunctions.RHTower.LiEvenCrossActualClockDampedResolvent
import GaloisForLFunctions.RHTower.LiClockPairedEtaPositiveCompletion
import GaloisForLFunctions.RHTower.LiClockPairedEtaFirstPrefixGammaBounds
import GaloisForLFunctions.RHTower.XiOrderFourteenCornerSourceExclusion
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.SmoothSeries

open Complex Set MeasureTheory Filter
open scoped BigOperators Topology
namespace RHTower
noncomputable section

private def clockFrequency (q : XiZeroCopy) : ℂ := (xiSpectralPoint q)⁻¹

private theorem clockFrequency_mass_summable :
    Summable (fun q : XiZeroCopy => ‖clockFrequency q‖^2) := by
  simpa [clockFrequency, xiZeroCopyReciprocalSquare, norm_pow] using summable_xiShiftAbsoluteMass 0

private theorem clockFrequency_norm_le_one (q : XiZeroCopy) : ‖clockFrequency q‖ ≤ 1 := by
  have h := norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty q
  have he : ‖xiZeroCopyReciprocalSquare q‖ = ‖clockFrequency q‖^2 := by
    simp [clockFrequency, xiZeroCopyReciprocalSquare, norm_pow]
  rw [he] at h
  nlinarith [norm_nonneg (clockFrequency q)]

private theorem clock_norm_cos (z : ℂ) : ‖Complex.cos z‖ ≤ Real.exp |z.im| := by
  rw [Complex.cos, norm_div, norm_ofNat]
  have h₁ : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (by simpa using neg_le_abs z.im)
  have h₂ : ‖Complex.exp (-z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (by simpa using le_abs_self z.im)
  have := norm_add_le (Complex.exp (z * I)) (Complex.exp (-z * I))
  linarith

private theorem clock_norm_sin (z : ℂ) : ‖Complex.sin z‖ ≤ Real.exp |z.im| := by
  rw [Complex.sin, norm_div, norm_mul, norm_ofNat, Complex.norm_I, mul_one]
  have h₁ : ‖Complex.exp (-z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (by simpa using le_abs_self z.im)
  have h₂ : ‖Complex.exp (z * I)‖ ≤ Real.exp |z.im| := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (by simpa using neg_le_abs z.im)
  have := norm_sub_le (Complex.exp (-z * I)) (Complex.exp (z * I))
  linarith

private theorem clock_norm_sin_linear (z : ℂ) :
    ‖Complex.sin z‖ ≤ ‖z‖ * Real.exp ‖z‖ := by
  have hd (x : ℝ) : HasDerivAt (fun x : ℝ => Complex.sin ((x:ℂ)*z))
      (Complex.cos ((x:ℂ)*z)*z) x := by
    convert! (Complex.hasDerivAt_sin ((x:ℂ)*z)).comp x
      ((Complex.ofRealCLM.hasDerivAt (x:=x)).mul_const z) using 1; simp
  have h := norm_image_sub_le_of_norm_deriv_le_segment'
    (a:=0) (b:=1) (C:=‖z‖*Real.exp ‖z‖)
    (fun x _ => (hd x).hasDerivWithinAt) (by
      intro x hx
      rw [norm_mul]
      have hi : |((x:ℂ)*z).im| ≤ ‖z‖ := by
        simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
          zero_mul, add_zero, abs_mul, abs_of_nonneg hx.1]
        calc
          x * |z.im| ≤ x * ‖z‖ := mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm z) hx.1
          _ ≤ ‖z‖ := by nlinarith [hx.2.le, norm_nonneg z]
      exact (mul_le_mul_of_nonneg_right ((clock_norm_cos _).trans (Real.exp_le_exp.mpr hi))
        (norm_nonneg z)).trans_eq (by ring))
    1 ⟨by norm_num,le_rfl⟩
  simpa using h

private def clockComplexResponse (z : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, clockFrequency q * Complex.sin (z*clockFrequency q)

private theorem clockComplexResponse_majorant {R : ℝ} (hR : 0 ≤ R)
    (q : XiZeroCopy) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖clockFrequency q * Complex.sin (z*clockFrequency q)‖ ≤
      ‖clockFrequency q‖^2 * R * Real.exp R := by
  rw [norm_mul]
  have hn : ‖z*clockFrequency q‖ ≤ R := by
    rw [norm_mul]
    calc
      ‖z‖*‖clockFrequency q‖ ≤ R*‖clockFrequency q‖ := by gcongr
      _ ≤ R := by nlinarith [clockFrequency_norm_le_one q, norm_nonneg (clockFrequency q)]
  calc
    ‖clockFrequency q‖*‖Complex.sin (z*clockFrequency q)‖ ≤
        ‖clockFrequency q‖*(‖z*clockFrequency q‖*Real.exp ‖z*clockFrequency q‖) := by
      gcongr; exact clock_norm_sin_linear _
    _ ≤ ‖clockFrequency q‖*(R*‖clockFrequency q‖*Real.exp R) := by
      rw [norm_mul]
      gcongr
      simpa [norm_mul] using hn
    _ = _ := by ring

private theorem clockComplexResponse_differentiable : Differentiable ℂ clockComplexResponse := by
  intro z
  let R := ‖z‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hu := (clockFrequency_mass_summable.mul_right R).mul_right (Real.exp R)
  have hf (q : XiZeroCopy) : DifferentiableOn ℂ
      (fun u : ℂ => clockFrequency q*Complex.sin (u*clockFrequency q)) (Metric.ball 0 R) := by
    intro u _
    exact (((Complex.hasDerivAt_sin (u*clockFrequency q)).comp u
      ((hasDerivAt_id u).mul_const _)).const_mul (clockFrequency q)).differentiableAt.differentiableWithinAt
  have hb (q : XiZeroCopy) (u : ℂ) (hu : u∈Metric.ball 0 R) :=
    clockComplexResponse_majorant hR q ((by simpa using hu : ‖u‖< R).le)
  exact (Complex.differentiableOn_tsum_of_summable_norm hu hf Metric.isOpen_ball hb).differentiableAt
    (Metric.isOpen_ball.mem_nhds (by simp [R]))

private theorem clockComplexResponse_hasDerivAt (z : ℂ) :
    HasDerivAt clockComplexResponse (∑'q : XiZeroCopy,
      clockFrequency q^2*Complex.cos (z*clockFrequency q)) z := by
  let R := ‖z‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hu := (clockFrequency_mass_summable.mul_right R).mul_right (Real.exp R)
  have hd (q : XiZeroCopy) (u : ℂ) : HasDerivAt
      (fun u : ℂ => clockFrequency q*Complex.sin (u*clockFrequency q))
      (clockFrequency q^2*Complex.cos (u*clockFrequency q)) u := by
    convert! ((Complex.hasDerivAt_sin (u*clockFrequency q)).comp u
      ((hasDerivAt_id u).mul_const _)).const_mul (clockFrequency q) using 1; ring
  have hs := Complex.hasSum_deriv_of_summable_norm (U:=Metric.ball (0:ℂ) R) hu
    (fun q u _ => (hd q u).differentiableAt.differentiableWithinAt)
    Metric.isOpen_ball
    (fun q u hu => clockComplexResponse_majorant hR q ((by simpa using hu : ‖u‖< R).le))
    (z:=z) (by simp [R])
  simp_rw [(hd _ _).deriv] at hs
  rw [hs.tsum_eq]
  exact (clockComplexResponse_differentiable z).hasDerivAt

private theorem clockWeighted_sum_hasDerivAt {f f' : XiZeroCopy → ℂ → ℂ}
    {u : XiZeroCopy → ℝ} (hu : Summable u)
    (hd : ∀ q z, HasDerivAt (f q) (f' q z) z)
    (hb : ∀ R : ℝ, 0 ≤ R → ∀ q z, ‖z‖ ≤ R → ‖f q z‖ ≤ u q*Real.exp R)
    (z : ℂ) : HasDerivAt (fun z => ∑'q, f q z) (∑'q, f' q z) z := by
  let R := ‖z‖+1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hsum := hu.mul_right (Real.exp R)
  have hbound q y (hy : y∈Metric.ball (0:ℂ) R) := hb R hR q y ((by simpa using hy : ‖y‖< R).le)
  have hdiff : DifferentiableOn ℂ (fun z => ∑'q, f q z) (Metric.ball 0 R) :=
    Complex.differentiableOn_tsum_of_summable_norm hsum
      (fun q y _ => (hd q y).differentiableAt.differentiableWithinAt)
      Metric.isOpen_ball hbound
  have hs := Complex.hasSum_deriv_of_summable_norm (U:=Metric.ball (0:ℂ) R) hsum
    (fun q y _ => (hd q y).differentiableAt.differentiableWithinAt)
    Metric.isOpen_ball hbound (z:=z) (by simp [R])
  simp_rw [(hd _ _).deriv] at hs
  rw [hs.tsum_eq]
  exact (hdiff.differentiableAt (Metric.isOpen_ball.mem_nhds (by simp [R]))).hasDerivAt

private theorem clockWeighted_sin_hasDerivAt {c : XiZeroCopy → ℂ}
    (hc : Summable (fun q => ‖c q‖)) (z : ℂ) :
    HasDerivAt (fun z : ℂ => ∑'q, c q*Complex.sin (z*clockFrequency q))
      (∑'q, c q*clockFrequency q*Complex.cos (z*clockFrequency q)) z := by
  refine clockWeighted_sum_hasDerivAt
    (f:=fun q z => c q*Complex.sin (z*clockFrequency q))
    (f':=fun q z => c q*clockFrequency q*Complex.cos (z*clockFrequency q)) hc ?_ ?_ z
  · intro q y
    convert! ((Complex.hasDerivAt_sin (y*clockFrequency q)).comp y
      ((hasDerivAt_id y).mul_const _)).const_mul (c q) using 1; ring
  · intro R hR q y hy
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (clock_norm_sin _).trans
    apply Real.exp_le_exp.mpr
    calc
      |(y*clockFrequency q).im| ≤ ‖y*clockFrequency q‖ := Complex.abs_im_le_norm _
      _ ≤ R := by rw [norm_mul]; nlinarith [clockFrequency_norm_le_one q, norm_nonneg y, norm_nonneg (clockFrequency q)]

private theorem clockWeighted_cos_hasDerivAt {c : XiZeroCopy → ℂ}
    (hc : Summable (fun q => ‖c q‖)) (z : ℂ) :
    HasDerivAt (fun z : ℂ => ∑'q, c q*Complex.cos (z*clockFrequency q))
      (∑'q, -(c q*clockFrequency q)*Complex.sin (z*clockFrequency q)) z := by
  refine clockWeighted_sum_hasDerivAt
    (f:=fun q z => c q*Complex.cos (z*clockFrequency q))
    (f':=fun q z => -(c q*clockFrequency q)*Complex.sin (z*clockFrequency q)) hc ?_ ?_ z
  · intro q y
    convert! ((Complex.hasDerivAt_cos (y*clockFrequency q)).comp y
      ((hasDerivAt_id y).mul_const _)).const_mul (c q) using 1; ring
  · intro R hR q y hy
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply (clock_norm_cos _).trans
    apply Real.exp_le_exp.mpr
    calc
      |(y*clockFrequency q).im| ≤ ‖y*clockFrequency q‖ := Complex.abs_im_le_norm _
      _ ≤ R := by rw [norm_mul]; nlinarith [clockFrequency_norm_le_one q, norm_nonneg y, norm_nonneg (clockFrequency q)]

private theorem clockFrequency_power_norm_summable (n : ℕ) :
    Summable (fun q => ‖clockFrequency q^(n+2)‖) := by
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _) _ clockFrequency_mass_summable
  intro q
  rw [norm_pow, pow_add]
  have hn := pow_le_one₀ (norm_nonneg (clockFrequency q)) (clockFrequency_norm_le_one q) (n:=n)
  nlinarith [sq_nonneg ‖clockFrequency q‖]

private theorem clockComplexResponse_ofReal (t : ℝ) :
    clockComplexResponse (t:ℂ) = (liEvenCrossActualClockResponse t:ℂ) := by
  simpa [clockComplexResponse, clockFrequency, liEvenCrossActualClockSineAtom] using
    (liEvenCrossActualClockResponse_ofReal_eq_tsum_sine t).symm

/-- The actual full-copy response is smooth at every real clock. -/
theorem contDiff_liEvenCrossActualClockResponse :
    ContDiff ℝ (⊤ : ℕ∞) liEvenCrossActualClockResponse := by
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => (clockComplexResponse (x:ℂ)).re) :=
    clockComplexResponse_differentiable.contDiff.real_of_complex
  convert h using 1
  ext t
  rw [clockComplexResponse_ofReal]
  rfl

/-- The literal first derivative of the actual response. -/
def liEvenCrossActualClockDerivative (t : ℝ) : ℝ := deriv liEvenCrossActualClockResponse t

private theorem clockResponse_hasDerivAt_cos (t : ℝ) : HasDerivAt liEvenCrossActualClockResponse
    (∑'q : XiZeroCopy, clockFrequency q^2*Complex.cos ((t:ℂ)*clockFrequency q)).re t := by
  convert (clockComplexResponse_hasDerivAt (t:ℂ)).real_of_complex using 1
  ext u
  rw [clockComplexResponse_ofReal]
  rfl

/-- Complete-copy differentiation identifies the literal derivative. -/
theorem liEvenCrossActualClockDerivative_eq_tsum_cos (t : ℝ) :
    liEvenCrossActualClockDerivative t =
      (∑'q : XiZeroCopy, (xiSpectralPoint q)⁻¹^2*
        Complex.cos ((t:ℂ)*(xiSpectralPoint q)⁻¹)).re :=
  (clockResponse_hasDerivAt_cos t).deriv

/-- The actual response differentiates to its literal first derivative. -/
theorem hasDerivAt_liEvenCrossActualClockResponse (t : ℝ) :
    HasDerivAt liEvenCrossActualClockResponse (liEvenCrossActualClockDerivative t) t := by
  rw [liEvenCrossActualClockDerivative_eq_tsum_cos]
  exact clockResponse_hasDerivAt_cos t

private theorem clockDerivative_hasDerivAt (t : ℝ) :
    HasDerivAt liEvenCrossActualClockDerivative
      (-(∑'q, clockFrequency q^3*Complex.sin ((t:ℂ)*clockFrequency q)).re) t := by
  have h := (clockWeighted_cos_hasDerivAt (c:=fun q => clockFrequency q^2)
    (by simpa using clockFrequency_power_norm_summable 0) (t:ℂ)).real_of_complex
  have he : (fun x : ℝ => (∑'q, clockFrequency q^2*Complex.cos ((x:ℂ)*clockFrequency q)).re) =
      liEvenCrossActualClockDerivative := by
    ext x; exact (liEvenCrossActualClockDerivative_eq_tsum_cos x).symm
  rw [he] at h
  convert h using 1
  rw [← Complex.neg_re, ← tsum_neg]
  congr 2
  ext q
  ring

private theorem clockDerivative_zero :
    liEvenCrossActualClockDerivative 0 = normalizedPrimeArchMoment 0 := by
  have h := tsum_xiZeroCopyReciprocalSquare_pow 0
  rw [← ofReal_normalizedPrimeArchMoment_eq_xiCentralReciprocalMoment] at h
  have hr := congrArg Complex.re h
  rw [liEvenCrossActualClockDerivative_eq_tsum_cos]
  simpa [xiZeroCopyReciprocalSquare] using hr

/-- The second derivative retains every reciprocal-frequency sine atom. -/
theorem iteratedDeriv_two_liEvenCrossActualClockResponse (t : ℝ) :
    iteratedDeriv 2 liEvenCrossActualClockResponse t =
      -(∑'q : XiZeroCopy, (xiSpectralPoint q)⁻¹^3*
        Complex.sin ((t:ℂ)*(xiSpectralPoint q)⁻¹)).re := by
  rw [show (2:ℕ)=1+1 by rfl, iteratedDeriv_succ, iteratedDeriv_one]
  exact (clockDerivative_hasDerivAt t).deriv

private theorem clockSecond_hasDerivAt (t : ℝ) :
    HasDerivAt (iteratedDeriv 2 liEvenCrossActualClockResponse)
      (-(∑'q, clockFrequency q^4*Complex.cos ((t:ℂ)*clockFrequency q)).re) t := by
  have h := ((clockWeighted_sin_hasDerivAt (c:=fun q => clockFrequency q^3)
    (by simpa using clockFrequency_power_norm_summable 1) (t:ℂ)).real_of_complex).neg
  have he : (fun x : ℝ => -(∑'q, clockFrequency q^3*Complex.sin ((x:ℂ)*clockFrequency q)).re) =
      iteratedDeriv 2 liEvenCrossActualClockResponse := by
    ext x; exact (iteratedDeriv_two_liEvenCrossActualClockResponse x).symm
  change HasDerivAt (fun x : ℝ => -(∑'q, clockFrequency q^3*Complex.sin ((x:ℂ)*clockFrequency q)).re)
      (-(∑'q, clockFrequency q^3*clockFrequency q*Complex.cos ((t:ℂ)*clockFrequency q)).re) t at h
  rw [he] at h
  convert h using 1
  congr 2

/-- The third derivative is the complete reciprocal fourth-power cosine trace. -/
theorem iteratedDeriv_three_liEvenCrossActualClockResponse (t : ℝ) :
    iteratedDeriv 3 liEvenCrossActualClockResponse t =
      -(∑'q : XiZeroCopy, (xiSpectralPoint q)⁻¹^4*
        Complex.cos ((t:ℂ)*(xiSpectralPoint q)⁻¹)).re := by
  rw [show (3:ℕ)=2+1 by rfl, iteratedDeriv_succ]
  exact (clockSecond_hasDerivAt t).deriv

/-- The massive rate selected by the literal completion and actual zeroth moment. -/
def liEvenCrossActualClockGreenRate : ℝ :=
  Real.sqrt ((liClockPairedEtaCompletionMoment 0).re-normalizedPrimeArchMoment 0)

/-- The third-minus-first derivative of the literal response. -/
def liEvenCrossActualClockGreenForcing (t : ℝ) : ℝ :=
  iteratedDeriv 3 liEvenCrossActualClockResponse t -
    liEvenCrossActualClockGreenRate^2*liEvenCrossActualClockDerivative t

/-- Every copy whose frequency equals either sign of a fixed frequency contributes. -/
def liEvenCrossActualClockResonantMass (q0 : XiZeroCopy) : ℝ := by
  classical
  exact ∑'q : XiZeroCopy, if (xiSpectralPoint q)⁻¹=(xiSpectralPoint q0)⁻¹ ∨
    (xiSpectralPoint q)⁻¹= -(xiSpectralPoint q0)⁻¹ then ‖(xiSpectralPoint q)⁻¹‖^2 else 0

/-- The complete summable absolute mass of the massive cosine source. -/
def liEvenCrossActualClockGreenAbsoluteMass : ℝ :=
  ∑'q : XiZeroCopy, ‖(xiSpectralPoint q)⁻¹‖^2*
    (‖(xiSpectralPoint q)⁻¹‖^2+liEvenCrossActualClockGreenRate^2)

/-- Literal source estimates place the massive rate strictly between one quarter and two thirds. -/
theorem liEvenCrossActualClockGreenRate_bounds :
    liEvenCrossActualClockGreenRate^2 =
        (liClockPairedEtaCompletionMoment 0).re-normalizedPrimeArchMoment 0 ∧
      1/4< liEvenCrossActualClockGreenRate ∧ liEvenCrossActualClockGreenRate<2/3 := by
  have hc := liClockPairedEtaCompletionMoment_re_ge_margin 0
  have hm := normalizedPrimeArchMoment_zero_lt_twentyNine_over_sixHundredTwentyFive
  have hm0 := normalizedPrimeArchMoment_zero_pos
  have hg := liClockPairedEtaFirstPrefixGammaSquareMass_lt_nine_div_twenty_five
  have hd := liClockPairedEtaDyadicMoment_norm_le 0
  have he : (∑'n : ℕ, liClockPairedEtaGammaReciprocal n^2) =
      liClockPairedEtaFirstPrefixGammaSquareMass := by
    unfold liClockPairedEtaFirstPrefixGammaSquareMass liClockPairedEtaGammaReciprocal
    simp_rw [inv_pow, one_div]
  have hupper : (liClockPairedEtaCompletionMoment 0).re < 651/1600 := by
    simp only [liClockPairedEtaCompletionMoment, Nat.mul_zero, zero_add,
      Complex.add_re, Complex.ofReal_re, he]
    have hr := Complex.re_le_norm (∑'k : ℤ, liClockPairedEtaDyadicReciprocal k^2)
    norm_num at hd
    linarith
  have hpos : 0 < (liClockPairedEtaCompletionMoment 0).re-normalizedPrimeArchMoment 0 := by
    norm_num at hc
    linarith
  have hs : liEvenCrossActualClockGreenRate^2 =
      (liClockPairedEtaCompletionMoment 0).re-normalizedPrimeArchMoment 0 :=
    Real.sq_sqrt hpos.le
  have hn : 0 ≤ liEvenCrossActualClockGreenRate := Real.sqrt_nonneg _
  refine ⟨hs, ?_, ?_⟩
  · norm_num at hc
    nlinarith
  · nlinarith

private theorem clockFrequency_power_trace_summable (n : ℕ) (t : ℝ) :
    Summable (fun q : XiZeroCopy => clockFrequency q^(n+2)*Complex.cos ((t:ℂ)*clockFrequency q)) := by
  apply Summable.of_norm
  have hm := (clockFrequency_power_norm_summable n).mul_right (Real.exp (|t|/300))
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _) _ hm
  intro q
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (clock_norm_cos _).trans
  apply Real.exp_le_exp.mpr
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul]
  have h := (abs_im_inv_xiSpectralPoint_lt_one_div_threeHundred q).le
  dsimp [clockFrequency]
  nlinarith [abs_nonneg t]

private theorem clockGreen_mass_summable : Summable (fun q : XiZeroCopy =>
    ‖clockFrequency q‖^2*(‖clockFrequency q‖^2+liEvenCrossActualClockGreenRate^2)) := by
  have hm := clockFrequency_mass_summable.mul_right (1+liEvenCrossActualClockGreenRate^2)
  apply Summable.of_nonneg_of_le (fun q => by positivity) _ hm
  intro q
  have hw := clockFrequency_norm_le_one q
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  nlinarith [norm_nonneg (clockFrequency q)]

private theorem clockGreen_coefficient_norm_summable : Summable (fun q : XiZeroCopy =>
    ‖clockFrequency q^2*(clockFrequency q^2+(liEvenCrossActualClockGreenRate^2:ℝ))‖) := by
  apply Summable.of_nonneg_of_le (fun q => norm_nonneg _) _ clockGreen_mass_summable
  intro q
  rw [norm_mul, norm_pow]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc
    ‖clockFrequency q^2+(liEvenCrossActualClockGreenRate^2:ℝ)‖ ≤
        ‖clockFrequency q^2‖+‖((liEvenCrossActualClockGreenRate^2:ℝ):ℂ)‖ := norm_add_le _ _
    _ = _ := by simp [norm_pow, Complex.norm_real, Real.norm_eq_abs]

/-- The massive derivative retains the complete literal cosine source. -/
theorem liEvenCrossActualClockGreenForcing_eq_tsum_cos (t : ℝ) :
    liEvenCrossActualClockGreenForcing t =
      -(∑'q : XiZeroCopy, (xiSpectralPoint q)⁻¹^2*
        ((xiSpectralPoint q)⁻¹^2+(liEvenCrossActualClockGreenRate^2:ℝ))*
        Complex.cos ((t:ℂ)*(xiSpectralPoint q)⁻¹)).re := by
  have h2 := clockFrequency_power_trace_summable 0 t
  have h4 := clockFrequency_power_trace_summable 2 t
  unfold liEvenCrossActualClockGreenForcing
  rw [iteratedDeriv_three_liEvenCrossActualClockResponse, liEvenCrossActualClockDerivative_eq_tsum_cos]
  change -(∑'q, clockFrequency q^4*Complex.cos ((t:ℂ)*clockFrequency q)).re -
      liEvenCrossActualClockGreenRate^2*(∑'q, clockFrequency q^2*Complex.cos ((t:ℂ)*clockFrequency q)).re = _
  have ht : (∑'q, clockFrequency q^2*(clockFrequency q^2+(liEvenCrossActualClockGreenRate^2:ℝ))*
      Complex.cos ((t:ℂ)*clockFrequency q)) =
      (∑'q, clockFrequency q^4*Complex.cos ((t:ℂ)*clockFrequency q)) +
        (liEvenCrossActualClockGreenRate^2:ℝ)*(∑'q, clockFrequency q^2*Complex.cos ((t:ℂ)*clockFrequency q)) := by
    rw [← tsum_mul_left, ← h4.tsum_add (h2.mul_left ((liEvenCrossActualClockGreenRate^2:ℝ):ℂ))]
    apply tsum_congr
    intro q
    ring
  change _ = -(∑'q, clockFrequency q^2*(clockFrequency q^2+(liEvenCrossActualClockGreenRate^2:ℝ))*
    Complex.cos ((t:ℂ)*clockFrequency q)).re
  rw [ht]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- The literal derivative is even. -/
theorem liEvenCrossActualClockDerivative_even (t : ℝ) :
    liEvenCrossActualClockDerivative (-t) = liEvenCrossActualClockDerivative t := by
  simp only [liEvenCrossActualClockDerivative_eq_tsum_cos, Complex.ofReal_neg, neg_mul, Complex.cos_neg]

/-- The literal massive forcing is even. -/
theorem liEvenCrossActualClockGreenForcing_even (t : ℝ) :
    liEvenCrossActualClockGreenForcing (-t) = liEvenCrossActualClockGreenForcing t := by
  simp only [liEvenCrossActualClockGreenForcing_eq_tsum_cos, Complex.ofReal_neg, neg_mul, Complex.cos_neg]

/-- Smoothness gives continuity of the literal derivative. -/
theorem continuous_liEvenCrossActualClockDerivative : Continuous liEvenCrossActualClockDerivative := by
  exact continuous_iff_continuousAt.mpr (fun t => (clockDerivative_hasDerivAt t).continuousAt)

/-- Smoothness gives continuity of the literal massive forcing. -/
theorem continuous_liEvenCrossActualClockGreenForcing : Continuous liEvenCrossActualClockGreenForcing := by
  have ht : Continuous (iteratedDeriv 3 liEvenCrossActualClockResponse) :=
    contDiff_liEvenCrossActualClockResponse.continuous_iteratedDeriv 3 (by exact WithTop.coe_le_coe.mpr (show (3:ℕ∞) ≤ ⊤ from le_top))
  exact ht.sub (continuous_const.mul continuous_liEvenCrossActualClockDerivative)

private theorem clockFrequency_mass_eq : (∑'q : XiZeroCopy, ‖clockFrequency q‖^2) =
    xiShiftAbsoluteMass 0 := by
  simp [xiShiftAbsoluteMass, xiZeroCopyReciprocalSquare, clockFrequency, norm_pow]

private theorem clockTrace_norm_bound {c : XiZeroCopy → ℂ} {m : XiZeroCopy → ℝ}
    (hm : Summable m) (hm0 : ∀ q, 0≤ m q) (hc : ∀ q, ‖c q‖≤ m q)
    {γ : ℝ} (_hγ : 0≤γ) (hw : ∀ q, |(clockFrequency q).im|≤γ)
    (t : ℝ) (isSin : Bool) :
    |(∑'q, c q*(if isSin then Complex.sin ((t:ℂ)*clockFrequency q)
      else Complex.cos ((t:ℂ)*clockFrequency q))).re| ≤ (∑'q, m q)*Real.exp (γ*|t|) := by
  have hb (q : XiZeroCopy) :
      ‖c q*(if isSin then Complex.sin ((t:ℂ)*clockFrequency q)
        else Complex.cos ((t:ℂ)*clockFrequency q))‖ ≤ m q*Real.exp (γ*|t|) := by
    rw [norm_mul]
    apply mul_le_mul (hc q)
    · apply (show ‖(if isSin then Complex.sin ((t:ℂ)*clockFrequency q)
        else Complex.cos ((t:ℂ)*clockFrequency q))‖ ≤
        Real.exp |((t:ℂ)*clockFrequency q).im| from by
          cases isSin <;> simp only [Bool.false_eq_true, if_false, if_true]
          · exact clock_norm_cos _
          · exact clock_norm_sin _).trans
      apply Real.exp_le_exp.mpr
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero, abs_mul]
      nlinarith [hw q, abs_nonneg t]
    · exact norm_nonneg _
    · exact hm0 q
  have hs := Summable.of_nonneg_of_le (fun q => norm_nonneg _) hb
    (hm.mul_right (Real.exp (γ*|t|)))
  calc
    _ ≤ ‖∑'q, c q*(if isSin then Complex.sin ((t:ℂ)*clockFrequency q)
      else Complex.cos ((t:ℂ)*clockFrequency q))‖ := Complex.abs_re_le_norm _
    _ ≤ ∑'q, ‖c q*(if isSin then Complex.sin ((t:ℂ)*clockFrequency q)
      else Complex.cos ((t:ℂ)*clockFrequency q))‖ := norm_tsum_le_tsum_norm hs
    _ ≤ ∑'q, m q*Real.exp (γ*|t|) := hs.tsum_le_tsum hb (hm.mul_right _)
    _ = _ := tsum_mul_right

/-- Every real clock has the complete squared-mass exponential derivative envelope. -/
theorem abs_liEvenCrossActualClockDerivative_le (t : ℝ) :
    |liEvenCrossActualClockDerivative t| ≤ xiShiftAbsoluteMass 0*Real.exp (|t|/300) := by
  have h := clockTrace_norm_bound clockFrequency_mass_summable (fun q => sq_nonneg _)
    (c:=fun q => clockFrequency q^2) (fun q => by rw [norm_pow])
    (γ:=1/300) (by norm_num)
    (fun q => (abs_im_inv_xiSpectralPoint_lt_one_div_threeHundred q).le) t false
  rw [clockFrequency_mass_eq] at h
  simpa [liEvenCrossActualClockDerivative_eq_tsum_cos,
    clockFrequency, mul_comm, div_eq_mul_inv] using h

private theorem clockSecond_bound (t : ℝ) :
    |iteratedDeriv 2 liEvenCrossActualClockResponse t| ≤
      xiShiftAbsoluteMass 0*Real.exp (|t|/300) := by
  have h := clockTrace_norm_bound clockFrequency_mass_summable (fun q => sq_nonneg _)
    (c:=fun q => clockFrequency q^3) (fun q => by
      rw [norm_pow, show (3:ℕ)=2+1 by rfl, pow_add, pow_one]
      exact mul_le_of_le_one_right (sq_nonneg _) (clockFrequency_norm_le_one q))
    (γ:=1/300) (by norm_num)
    (fun q => (abs_im_inv_xiSpectralPoint_lt_one_div_threeHundred q).le) t true
  rw [clockFrequency_mass_eq] at h
  simpa [iteratedDeriv_two_liEvenCrossActualClockResponse,
    clockFrequency, mul_comm, div_eq_mul_inv] using h

/-- The massive source has a complete-copy exponential envelope. -/
theorem abs_liEvenCrossActualClockGreenForcing_le (t : ℝ) :
    |liEvenCrossActualClockGreenForcing t| ≤
      liEvenCrossActualClockGreenAbsoluteMass*Real.exp (|t|/300) := by
  have hc (q : XiZeroCopy) :
      ‖clockFrequency q^2*(clockFrequency q^2+((liEvenCrossActualClockGreenRate^2:ℝ):ℂ))‖ ≤
        ‖clockFrequency q‖^2*(‖clockFrequency q‖^2+liEvenCrossActualClockGreenRate^2) := by
    rw [norm_mul, norm_pow]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact (norm_add_le _ _).trans_eq (by simp [norm_pow, Complex.norm_real,
      Real.norm_eq_abs])
  have h := clockTrace_norm_bound clockGreen_mass_summable (fun q => by positivity)
    hc (γ:=1/300) (by norm_num)
    (fun q => (abs_im_inv_xiSpectralPoint_lt_one_div_threeHundred q).le) t false
  simpa [liEvenCrossActualClockGreenAbsoluteMass, liEvenCrossActualClockGreenForcing_eq_tsum_cos,
    clockFrequency, mul_comm, div_eq_mul_inv] using h

/-- The complete resonance mask has positive mass bounded by the complete source mass. -/
theorem liEvenCrossActualClockResonantMass_bounds (q0 : XiZeroCopy) :
    0< liEvenCrossActualClockResonantMass q0 ∧
      liEvenCrossActualClockResonantMass q0≤ xiShiftAbsoluteMass 0 := by
  classical
  let m (q : XiZeroCopy) := if clockFrequency q=clockFrequency q0 ∨
    clockFrequency q= -clockFrequency q0 then ‖clockFrequency q‖^2 else 0
  have hm0 (q : XiZeroCopy) : 0≤ m q := by dsimp [m]; split_ifs <;> positivity
  have hle (q : XiZeroCopy) : m q ≤ ‖clockFrequency q‖^2 := by
    dsimp [m]
    split_ifs
    · exact le_rfl
    · exact sq_nonneg _
  have hm := Summable.of_nonneg_of_le hm0 hle clockFrequency_mass_summable
  change 0<∑'q,m q ∧ (∑'q,m q)≤ xiShiftAbsoluteMass 0
  refine ⟨hm.tsum_pos hm0 q0 ?_, ?_⟩
  · dsimp only [m]
    rw [if_pos (Or.inl rfl)]
    apply pow_pos
    rw [norm_pos_iff]
    exact inv_ne_zero (xiSpectralPoint_ne_zero q0)
  · exact (hm.tsum_le_tsum hle clockFrequency_mass_summable).trans_eq clockFrequency_mass_eq

/-- The complete massive weight is positive and has the literal radius envelope. -/
theorem liEvenCrossActualClockGreenAbsoluteMass_bounds :
    0< liEvenCrossActualClockGreenAbsoluteMass ∧
      liEvenCrossActualClockGreenAbsoluteMass≤ xiShiftAbsoluteMass 0*
        (liEvenCrossActualClockGreenRate^2+1/150) := by
  let q0 : XiZeroCopy := Classical.choice nonempty_xiZeroCopy
  have hpos (q : XiZeroCopy) : 0<‖clockFrequency q‖ := by
    rw [norm_pos_iff]
    exact inv_ne_zero (xiSpectralPoint_ne_zero q)
  change 0<∑'q, ‖clockFrequency q‖^2*(‖clockFrequency q‖^2+liEvenCrossActualClockGreenRate^2) ∧ _
  refine ⟨clockGreen_mass_summable.tsum_pos (fun q => by positivity) q0 ?_, ?_⟩
  · exact mul_pos (pow_pos (hpos q0) 2) (add_pos_of_pos_of_nonneg (pow_pos (hpos q0) 2) (sq_nonneg _))
  have hb (q : XiZeroCopy) : ‖clockFrequency q‖^2*(‖clockFrequency q‖^2+liEvenCrossActualClockGreenRate^2) ≤
      ‖clockFrequency q‖^2*(liEvenCrossActualClockGreenRate^2+1/150) := by
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have h := (norm_xiZeroCopyReciprocalSquare_lt_one_div_oneHundredFifty q).le
    simpa [xiZeroCopyReciprocalSquare, clockFrequency, norm_pow, add_comm] using
      add_le_add_right h (liEvenCrossActualClockGreenRate^2)
  calc
    _ ≤ ∑'q, ‖clockFrequency q‖^2*(liEvenCrossActualClockGreenRate^2+1/150) :=
      clockGreen_mass_summable.tsum_le_tsum hb (clockFrequency_mass_summable.mul_right _)
    _ = _ := by rw [tsum_mul_right, clockFrequency_mass_eq]

private theorem clockFrequency_real_of_rh (hRH : RiemannHypothesis) (q : XiZeroCopy) :
    (clockFrequency q).im=0 := by
  obtain ⟨r,hr⟩ := xiSpectralPoint_real_of_rh hRH q
  simp [clockFrequency, hr, ← Complex.ofReal_inv]

/-- Under RH the literal derivative is uniformly bounded by its complete mass. -/
theorem abs_liEvenCrossActualClockDerivative_le_of_rh (hRH : RiemannHypothesis) (t : ℝ) :
    |liEvenCrossActualClockDerivative t|≤ xiShiftAbsoluteMass 0 := by
  have h := clockTrace_norm_bound clockFrequency_mass_summable (fun q => sq_nonneg _)
    (c:=fun q => clockFrequency q^2) (fun q => by rw [norm_pow])
    (γ:=0) le_rfl (fun q => by simp [clockFrequency_real_of_rh hRH q]) t false
  rw [clockFrequency_mass_eq] at h
  simpa [liEvenCrossActualClockDerivative_eq_tsum_cos, clockFrequency] using h

/-- Under RH the massive forcing is uniformly bounded by its complete massive mass. -/
theorem abs_liEvenCrossActualClockGreenForcing_le_of_rh (hRH : RiemannHypothesis) (t : ℝ) :
    |liEvenCrossActualClockGreenForcing t|≤ liEvenCrossActualClockGreenAbsoluteMass := by
  have hc (q : XiZeroCopy) :
      ‖clockFrequency q^2*(clockFrequency q^2+((liEvenCrossActualClockGreenRate^2:ℝ):ℂ))‖ ≤
        ‖clockFrequency q‖^2*(‖clockFrequency q‖^2+liEvenCrossActualClockGreenRate^2) := by
    rw [norm_mul, norm_pow]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    exact (norm_add_le _ _).trans_eq (by simp [norm_pow, Complex.norm_real,
      Real.norm_eq_abs])
  have h := clockTrace_norm_bound clockGreen_mass_summable (fun q => by positivity)
    hc (γ:=0) le_rfl (fun q => by simp [clockFrequency_real_of_rh hRH q]) t false
  simpa [liEvenCrossActualClockGreenAbsoluteMass, liEvenCrossActualClockGreenForcing_eq_tsum_cos,
    clockFrequency] using h

private theorem clock_exp_abs_integrable {k : ℝ} (hk : 0< k) :
    Integrable (fun s : ℝ => Real.exp (-k*|s|)) := by
  have hl : IntegrableOn (fun s : ℝ => Real.exp (-k*|s|)) (Iic 0) := by
    apply (integrableOn_exp_mul_Iic hk 0).congr_fun _ measurableSet_Iic
    intro s hs
    simp only [mem_Iic] at hs
    simp only [abs_of_nonpos hs]
    congr 1
    ring_nf
  have hr : IntegrableOn (fun s : ℝ => Real.exp (-k*|s|)) (Ioi 0) := by
    apply (integrableOn_exp_mul_Ioi (a:=-k) (by linarith) 0).congr_fun _ measurableSet_Ioi
    intro s hs
    simp only [mem_Ioi] at hs
    simp only [abs_of_pos hs]
  simpa only [Iic_union_Ioi, integrableOn_univ] using hl.union hr

private theorem clock_green_integrable {G : ℝ→ℝ} (hG : Continuous G)
    {A γ ω : ℝ} (hA : 0≤ A) (hγ : 0≤γ) (hγω : γ<ω)
    (hbound : ∀ s, |G s|≤ A*Real.exp (γ*|s|)) (t : ℝ) :
    Integrable (fun s : ℝ => Real.exp (-ω*|t-s|)*G s) := by
  have hm := (clock_exp_abs_integrable (sub_pos.mpr hγω)).const_mul (A*Real.exp (ω*|t|))
  apply hm.mono' ((Real.continuous_exp.comp
    (continuous_const.mul ((continuous_const.sub continuous_id).abs))).mul hG).aestronglyMeasurable
  apply ae_of_all
  intro s
  change |Real.exp (-ω*|t-s|)*G s| ≤ _
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-ω*|t-s|)*|G s| ≤ Real.exp (-ω*|t-s|)*(A*Real.exp (γ*|s|)) := by gcongr; exact hbound s
    _ = A*Real.exp (-ω*|t-s|+γ*|s|) := by rw [mul_left_comm, ← Real.exp_add]
    _ ≤ A*Real.exp (ω*|t|-(ω-γ)*|s|) := by
      gcongr
      have hab : |s|≤|t-s|+|t| := by
        calc |s| = |t-(t-s)| := by congr 1; ring_nf
             _ ≤ |t|+|t-s| := by simpa only [sub_zero, zero_sub, abs_neg] using abs_sub_le t 0 (t-s)
             _ = _ := by ring_nf
      have hω : 0≤ω := by linarith
      nlinarith
    _ = A*Real.exp (ω*|t|)*Real.exp (-(ω-γ)*|s|) := by rw [show ω*|t|-(ω-γ)*|s| = ω*|t| + (-(ω-γ)*|s|) by ring_nf, Real.exp_add]; ring_nf

private theorem clock_green_identity {h h' h'' G : ℝ→ℝ}
    (hd : ∀ s, HasDerivAt h (h' s) s) (hd' : ∀ s, HasDerivAt h' (h'' s) s)
    (hG : Continuous G) {A γ ω : ℝ} (_hA : 0≤ A) (hγ : 0≤γ) (hγω : γ<ω)
    (he : ∀ s, G s=h'' s-ω^2*h s)
    (hb : ∀ s, |h s|≤ A*Real.exp (γ*|s|))
    (hb' : ∀ s, |h' s|≤ A*Real.exp (γ*|s|))
    {M : ℝ} (hM : 0≤ M) (hGM : ∀ s, |G s|≤ M*Real.exp (γ*|s|)) (t : ℝ) :
    h t = -(1/(2*ω))*(∫ s : ℝ, Real.exp (-ω*|t-s|)*G s) := by
  have hω : 0<ω := lt_of_le_of_lt hγ hγω
  have hK := clock_green_integrable hG hM hγ hγω hGM t
  have hleft (s : ℝ) : HasDerivAt (fun s => Real.exp (ω*s)*(h' s-ω*h s))
      (Real.exp (ω*s)*G s) s := by
    convert! (((hasDerivAt_id s).const_mul ω).exp).mul
      ((hd' s).sub ((hd s).const_mul ω)) using 1
    simp only [Pi.sub_apply, id_eq]
    rw [he]
    ring_nf
  have hright (s : ℝ) : HasDerivAt (fun s => Real.exp (-ω*s)*(h' s+ω*h s))
      (Real.exp (-ω*s)*G s) s := by
    convert! (((hasDerivAt_id s).const_mul (-ω)).exp).mul
      ((hd' s).add ((hd s).const_mul ω)) using 1
    simp only [Pi.add_apply, id_eq]
    rw [he]
    ring_nf
  have hLi : IntegrableOn (fun s => Real.exp (ω*s)*G s) (Iic t) := by
    have hi : IntegrableOn (fun s => Real.exp (ω*t)*(Real.exp (-ω*|t-s|)*G s)) (Iic t) :=
      hK.integrableOn.const_mul (Real.exp (ω*t))
    apply hi.congr_fun _ measurableSet_Iic
    intro s hs
    simp only [mem_Iic] at hs
    dsimp only
    rw [abs_of_nonneg (sub_nonneg.mpr hs), ← mul_assoc, ← Real.exp_add]
    congr 2
    ring_nf
  have hRi : IntegrableOn (fun s => Real.exp (-ω*s)*G s) (Ioi t) := by
    have hi : IntegrableOn (fun s => Real.exp (-ω*t)*(Real.exp (-ω*|t-s|)*G s)) (Ioi t) :=
      hK.integrableOn.const_mul (Real.exp (-ω*t))
    apply hi.congr_fun _ measurableSet_Ioi
    intro s hs
    simp only [mem_Ioi] at hs
    dsimp only
    rw [abs_of_neg (sub_neg.mpr hs), ← mul_assoc, ← Real.exp_add]
    congr 2
    ring_nf
  have ht : Tendsto (fun s : ℝ => A*(1+ω)*Real.exp (-(ω-γ)*s)) atTop (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atTop_of_neg (by linarith : -(ω-γ)<0))).const_mul (A*(1+ω))
  have hbot : Tendsto (fun s : ℝ => A*(1+ω)*Real.exp ((ω-γ)*s)) atBot (𝓝 0) := by
    simpa using (Real.tendsto_exp_atBot.comp
      (tendsto_id.const_mul_atBot (by linarith : 0<ω-γ))).const_mul (A*(1+ω))
  have hLT : Tendsto (fun s => Real.exp (ω*s)*(h' s-ω*h s)) atBot (𝓝 0) := by
    apply squeeze_zero_norm' _ hbot
    filter_upwards [eventually_le_atBot (0:ℝ)] with s hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (ω*s)*(|h' s|+ω*|h s|) := by
        gcongr
        calc |h' s-ω*h s| ≤ |h' s|+|ω*h s| := by simpa using abs_sub_le (h' s) 0 (ω*h s)
             _ = _ := by rw [abs_mul, abs_of_pos hω]
      _ ≤ Real.exp (ω*s)*(A*Real.exp (γ*|s|)+ω*(A*Real.exp (γ*|s|))) := by gcongr; exact hb' s; exact hb s
      _ = A*(1+ω)*(Real.exp (ω*s)*Real.exp (γ*|s|)) := by ring_nf
      _ = A*(1+ω)*Real.exp (ω*s+γ*|s|) := by rw [Real.exp_add]
      _ = _ := by congr 2; rw [abs_of_nonpos hs]; ring_nf
  have hRT : Tendsto (fun s => Real.exp (-ω*s)*(h' s+ω*h s)) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ ht
    filter_upwards [eventually_ge_atTop (0:ℝ)] with s hs
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-ω*s)*(|h' s|+ω*|h s|) := by
        gcongr
        calc |h' s+ω*h s| ≤ |h' s|+|ω*h s| := abs_add_le _ _
             _ = _ := by rw [abs_mul, abs_of_pos hω]
      _ ≤ Real.exp (-ω*s)*(A*Real.exp (γ*|s|)+ω*(A*Real.exp (γ*|s|))) := by gcongr; exact hb' s; exact hb s
      _ = A*(1+ω)*(Real.exp (-ω*s)*Real.exp (γ*|s|)) := by ring_nf
      _ = A*(1+ω)*Real.exp (-ω*s+γ*|s|) := by rw [Real.exp_add]
      _ = _ := by congr 2; rw [abs_of_nonneg hs]; ring_nf
  have hLF := integral_Iic_of_hasDerivAt_of_tendsto' (fun s _ => hleft s) hLi hLT
  have hRF := integral_Ioi_of_hasDerivAt_of_tendsto' (fun s _ => hright s) hRi hRT
  have hLK : (∫s in Iic t, Real.exp (-ω*|t-s|)*G s) = h' t-ω*h t := by
    calc
      _ = Real.exp (-ω*t)*(∫s in Iic t, Real.exp (ω*s)*G s) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Iic
        intro s hs
        simp only [mem_Iic] at hs
        dsimp only
        rw [abs_of_nonneg (sub_nonneg.mpr hs), ← mul_assoc, ← Real.exp_add]
        congr 1; ring_nf
      _ = _ := by rw [hLF, sub_zero, ← mul_assoc, ← Real.exp_add]; simp
  have hRK : (∫s in Ioi t, Real.exp (-ω*|t-s|)*G s) = -(h' t+ω*h t) := by
    calc
      _ = Real.exp (ω*t)*(∫s in Ioi t, Real.exp (-ω*s)*G s) := by
        rw [← integral_const_mul]
        apply setIntegral_congr_fun measurableSet_Ioi
        intro s hs
        simp only [mem_Ioi] at hs
        dsimp only
        rw [abs_of_neg (sub_neg.mpr hs), ← mul_assoc, ← Real.exp_add]
        congr 1; ring_nf
      _ = _ := by rw [hRF, zero_sub, mul_neg, ← mul_assoc, ← Real.exp_add]; simp
  have hwhole := integral_add_compl (s:=Iic t) measurableSet_Iic hK
  rw [compl_Iic, hLK, hRK] at hwhole
  rw [← hwhole]
  field_simp [hω.ne']
  ring_nf
private theorem clock_h_deriv (t : ℝ) : HasDerivAt liEvenCrossActualClockDerivative
    (iteratedDeriv 2 liEvenCrossActualClockResponse t) t := by
  rw [iteratedDeriv_two_liEvenCrossActualClockResponse]
  exact clockDerivative_hasDerivAt t

private theorem clock_hprime_deriv (t : ℝ) :
    HasDerivAt (iteratedDeriv 2 liEvenCrossActualClockResponse)
      (iteratedDeriv 3 liEvenCrossActualClockResponse t) t := by
  rw [iteratedDeriv_three_liEvenCrossActualClockResponse]
  exact clockSecond_hasDerivAt t

/-- The literal massive Green integral is absolutely integrable at every real clock. -/
theorem integrable_liEvenCrossActualClockGreenKernel (t : ℝ) :
    Integrable (fun s : ℝ => Real.exp (-liEvenCrossActualClockGreenRate*|t-s|)*
      liEvenCrossActualClockGreenForcing s) := by
  apply clock_green_integrable continuous_liEvenCrossActualClockGreenForcing
    liEvenCrossActualClockGreenAbsoluteMass_bounds.1.le (γ:=1/300) (by norm_num)
    (by linarith [liEvenCrossActualClockGreenRate_bounds.2.1])
    (fun s => by simpa [div_eq_mul_inv, mul_comm] using abs_liEvenCrossActualClockGreenForcing_le s) t

/-- Source growth selects the exact all-real massive Green inverse of the literal derivative. -/
theorem liEvenCrossActualClockDerivative_eq_greenIntegral (t : ℝ) :
    liEvenCrossActualClockDerivative t = -(1/(2*liEvenCrossActualClockGreenRate))*
      (∫s : ℝ, Real.exp (-liEvenCrossActualClockGreenRate*|t-s|)*
        liEvenCrossActualClockGreenForcing s) := by
  exact clock_green_identity clock_h_deriv clock_hprime_deriv
    continuous_liEvenCrossActualClockGreenForcing (xiShiftAbsoluteMass_nonneg 0)
    (γ:=1/300) (by norm_num) (by linarith [liEvenCrossActualClockGreenRate_bounds.2.1])
    (fun s => rfl)
    (fun s => by simpa [div_eq_mul_inv, mul_comm] using abs_liEvenCrossActualClockDerivative_le s)
    (fun s => by simpa [div_eq_mul_inv, mul_comm] using clockSecond_bound s)
    liEvenCrossActualClockGreenAbsoluteMass_bounds.1.le
    (fun s => by simpa [div_eq_mul_inv, mul_comm] using abs_liEvenCrossActualClockGreenForcing_le s) t

end
end RHTower
