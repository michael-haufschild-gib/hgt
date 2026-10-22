import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCompletedDensityReflection
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFiniteShellSeamCancellation
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGaussianHankelRH
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberTranslation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodRayBoundaryResidue

open Complex Real MeasureTheory Set Filter Topology Polynomial
open scoped BigOperators

namespace RHTower

noncomputable section

/-- A positive half-line shell transform of the completed theta-cusp source. -/
def thetaCuspShellHalfLineTransform
    (P : ℝ → ℂ) (n : ℕ) : ℂ :=
  ∫ x : ℝ in Ioi 0, (thetaCuspSourceTerm x n : ℂ) * P x

@[simp] theorem thetaCuspShellHalfLineTransform_zero
    (P : ℝ → ℂ) :
    thetaCuspShellHalfLineTransform P 0 = 0 := by
  simp [thetaCuspShellHalfLineTransform, thetaCuspSourceTerm, thetaCuspSeed]

/-- Absolute shell reassembly on the positive half-line.  Positivity of every source shell makes
the interchange valid for any continuous phase whose product with the completed source is
integrable. -/
theorem hasSum_thetaCuspShellHalfLineTransform
    (P : ℝ → ℂ) (hP : Continuous P)
    (hfull : IntegrableOn
      (fun x : ℝ => (thetaCuspFullSource x : ℂ) * P x) (Ioi 0)) :
    HasSum (thetaCuspShellHalfLineTransform P)
      (∫ x : ℝ in Ioi 0, (thetaCuspFullSource x : ℂ) * P x) := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let F : ℕ → ℝ → ℂ := fun n x =>
    (thetaCuspSourceTerm x n : ℂ) * P x
  have hFmeas : ∀ n, AEStronglyMeasurable (F n) mu := by
    intro n
    exact ((by
      dsimp [F]
      unfold thetaCuspSourceTerm thetaCuspSeed
      fun_prop : Continuous (F n))).aestronglyMeasurable
  have hBoundSummable : ∀ᵐ x ∂mu, Summable (fun n => ‖F n x‖) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    let A : ℕ → ℝ := fun n => thetaCuspSourceTerm x n
    have hA0 (n : ℕ) : 0 ≤ A n :=
      thetaCuspSourceTerm_nonneg_of_pos hx n
    have hAsum : Summable A := summable_thetaCuspSourceTerm x
    have hFnorm (n : ℕ) : ‖F n x‖ = A n * ‖P x‖ := by
      dsimp [F, A]
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (hA0 n)]
    exact (hAsum.mul_right ‖P x‖).congr (fun n => (hFnorm n).symm)
  have hNormEq : ∀ᵐ x ∂mu,
      (∑' n, ‖F n x‖) =
        ‖(thetaCuspFullSource x : ℂ) * P x‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    let A : ℕ → ℝ := fun n => thetaCuspSourceTerm x n
    have hA0 (n : ℕ) : 0 ≤ A n :=
      thetaCuspSourceTerm_nonneg_of_pos hx n
    have hAsum : Summable A := summable_thetaCuspSourceTerm x
    have hFnorm (n : ℕ) : ‖F n x‖ = A n * ‖P x‖ := by
      dsimp [F, A]
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg (hA0 n)]
    have hfull0 : 0 ≤ thetaCuspFullSource x :=
      (thetaCuspFullSource_pos_of_pos hx).le
    calc
      (∑' n, ‖F n x‖) = ∑' n, A n * ‖P x‖ := tsum_congr hFnorm
      _ = (∑' n, A n) * ‖P x‖ := hAsum.tsum_mul_right _
      _ = thetaCuspFullSource x * ‖P x‖ := by rfl
      _ = ‖(thetaCuspFullSource x : ℂ) * P x‖ := by
        rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hfull0]
  have hBoundIntegrable :
      Integrable (fun x => ∑' n, ‖F n x‖) mu := by
    have hfull' : Integrable
        (fun x : ℝ => (thetaCuspFullSource x : ℂ) * P x) mu := hfull
    exact hfull'.norm.congr (hNormEq.mono fun _ hx => hx.symm)
  have hLim : ∀ᵐ x ∂mu,
      HasSum (fun n => F n x)
        ((thetaCuspFullSource x : ℂ) * P x) := by
    filter_upwards with x
    have hAsum : Summable (fun n => thetaCuspSourceTerm x n) :=
      summable_thetaCuspSourceTerm x
    have hAsumC : Summable (fun n => (thetaCuspSourceTerm x n : ℂ)) :=
      (Complex.ofRealCLM : ℝ →L[ℝ] ℂ).summable hAsum
    have h := hAsumC.hasSum.mul_right (P x)
    have hval : ((thetaCuspFullSource x : ℝ) : ℂ) * P x =
        (∑' n, (thetaCuspSourceTerm x n : ℂ)) * P x := by
      unfold thetaCuspFullSource
      push_cast
      rfl
    rw [hval]
    exact h
  have h := hasSum_integral_of_dominated_convergence
    (fun n x => ‖F n x‖) hFmeas
    (fun n => Filter.Eventually.of_forall fun x => le_rfl)
    hBoundSummable hBoundIntegrable hLim
  have h2 : HasSum (fun n => ∫ x, F n x ∂mu)
      (∫ x, (thetaCuspFullSource x : ℂ) * P x ∂mu) := h
  have h3 : HasSum
      (fun n => ∫ x : ℝ in Ioi 0, (thetaCuspSourceTerm x n : ℂ) * P x)
      (∫ x : ℝ in Ioi 0, (thetaCuspFullSource x : ℂ) * P x) := h2
  exact h3

def thetaCuspShellEvenPhaseValue (z : ℂ) (n : ℕ) : ℂ :=
  thetaCuspShellHalfLineTransform
    (thetaCuspTailSecondDensityEvenPhase z) n

theorem hasSum_thetaCuspShellEvenPhaseValue
    {z : ℂ} (hz : |z.im| < 1) :
    HasSum (thetaCuspShellEvenPhaseValue z) (XiC z) := by
  rw [← integral_fullSource_mul_evenPhase_eq_XiC hz]
  exact hasSum_thetaCuspShellHalfLineTransform _
    (by
      unfold thetaCuspTailSecondDensityEvenPhase spectralTranslationPhase
      fun_prop)
    (by
      have hFL := integrable_thetaCuspFourierLaplaceIntegrand hz
      have hplus : IntegrableOn (thetaCuspFourierLaplaceIntegrand z) (Ioi 0) :=
        hFL.integrableOn
      have hminus : IntegrableOn
          (fun x : ℝ => thetaCuspFourierLaplaceIntegrand z (-x)) (Ioi 0) :=
        hFL.comp_neg.integrableOn
      apply (hplus.add hminus).congr_fun
        (fun x hx => ?_) measurableSet_Ioi
      unfold thetaCuspFourierLaplaceIntegrand
        thetaCuspTailSecondDensityEvenPhase spectralTranslationPhase
      simp only [Pi.add_apply]
      rw [thetaCuspFullSource_neg]
      push_cast
      ring_nf)

theorem XiC_eq_tsum_thetaCuspShellEvenPhaseValue
    {z : ℂ} (hz : |z.im| < 1) :
    XiC z = ∑' n : ℕ, thetaCuspShellEvenPhaseValue z n :=
  (hasSum_thetaCuspShellEvenPhaseValue hz).tsum_eq.symm

/-- Spectral, rather than source-variable, derivative of the positive-half-line even phase. -/
def thetaCuspTailSecondDensityEvenPhaseSpectralDerivative
    (z : ℂ) (x : ℝ) : ℂ :=
  (x : ℂ) * I *
    (spectralTranslationPhase x z - spectralTranslationPhase x (-z))

theorem continuous_thetaCuspTailSecondDensityEvenPhaseSpectralDerivative
    (z : ℂ) :
    Continuous (thetaCuspTailSecondDensityEvenPhaseSpectralDerivative z) := by
  unfold thetaCuspTailSecondDensityEvenPhaseSpectralDerivative
    spectralTranslationPhase
  fun_prop

/-- The completed-source first spectral jet reflected to the positive half-line. -/
theorem deriv_XiC_eq_integral_fullSource_mul_evenPhaseSpectralDerivative
    {z : ℂ} (hz : |z.im| < 1) :
    deriv XiC z =
      ∫ x : ℝ in Ioi 0,
        (thetaCuspFullSource x : ℂ) *
          thetaCuspTailSecondDensityEvenPhaseSpectralDerivative z x := by
  have hInt : Integrable (thetaCuspFourierLaplaceDerivativeIntegrand z) := by
    exact (integrable_thetaCuspFourierLaplaceJetIntegrand 1 hz).congr
      (Filter.Eventually.of_forall fun x =>
        thetaCuspFourierLaplaceJetIntegrand_one z x)
  have hJet := iteratedDeriv_XiC_eq_integral_thetaCuspFourierLaplaceJet
    1 (abs_lt.mp hz)
  rw [iteratedDeriv_one] at hJet
  simp only [thetaCuspFourierLaplaceJetIntegrand_one] at hJet
  rw [hJet, integral_eq_integral_Ioi_add_reflect hInt]
  apply integral_congr_ae
  filter_upwards with x
  unfold thetaCuspFourierLaplaceDerivativeIntegrand
    thetaCuspFourierLaplaceIntegrand
    thetaCuspTailSecondDensityEvenPhaseSpectralDerivative
    spectralTranslationPhase
  rw [thetaCuspFullSource_neg]
  push_cast
  ring_nf

def thetaCuspShellEvenPhaseSpectralDerivativeValue
    (z : ℂ) (n : ℕ) : ℂ :=
  thetaCuspShellHalfLineTransform
    (thetaCuspTailSecondDensityEvenPhaseSpectralDerivative z) n

theorem hasSum_thetaCuspShellEvenPhaseSpectralDerivativeValue
    {z : ℂ} (hz : |z.im| < 1) :
    HasSum (thetaCuspShellEvenPhaseSpectralDerivativeValue z)
      (deriv XiC z) := by
  rw [deriv_XiC_eq_integral_fullSource_mul_evenPhaseSpectralDerivative hz]
  exact hasSum_thetaCuspShellHalfLineTransform _
    (continuous_thetaCuspTailSecondDensityEvenPhaseSpectralDerivative z)
    (by
      have hInt : Integrable
          (thetaCuspFourierLaplaceDerivativeIntegrand z) := by
        exact (integrable_thetaCuspFourierLaplaceJetIntegrand 1 hz).congr
          (Filter.Eventually.of_forall fun x =>
            thetaCuspFourierLaplaceJetIntegrand_one z x)
      have hplus :
          IntegrableOn (thetaCuspFourierLaplaceDerivativeIntegrand z) (Ioi 0) :=
        hInt.integrableOn
      have hminus : IntegrableOn
          (fun x : ℝ => thetaCuspFourierLaplaceDerivativeIntegrand z (-x))
            (Ioi 0) :=
        hInt.comp_neg.integrableOn
      apply (hplus.add hminus).congr_fun
        (fun x hx => ?_) measurableSet_Ioi
      unfold thetaCuspFourierLaplaceDerivativeIntegrand
        thetaCuspFourierLaplaceIntegrand
        thetaCuspTailSecondDensityEvenPhaseSpectralDerivative
        spectralTranslationPhase
      simp only [Pi.add_apply]
      rw [thetaCuspFullSource_neg]
      push_cast
      ring_nf)

theorem deriv_XiC_eq_tsum_thetaCuspShellEvenPhaseSpectralDerivativeValue
    {z : ℂ} (hz : |z.im| < 1) :
    deriv XiC z =
      ∑' n : ℕ, thetaCuspShellEvenPhaseSpectralDerivativeValue z n :=
  (hasSum_thetaCuspShellEvenPhaseSpectralDerivativeValue hz).tsum_eq.symm

/-- Ordered shell-pair contribution to the horizontal completed-Xi orientation current. -/
def thetaCuspShellPairHedenmalmCurrent
    (z : ℂ) (q : ℕ × ℕ) : ℝ :=
  2 * (thetaCuspShellEvenPhaseSpectralDerivativeValue z q.1 *
    (starRingEnd ℂ) (thetaCuspShellEvenPhaseValue z q.2)).im

theorem summable_thetaCuspShellPairHedenmalmCurrent
    {z : ℂ} (hz : |z.im| < 1) :
    Summable (thetaCuspShellPairHedenmalmCurrent z) := by
  have hV : Summable (thetaCuspShellEvenPhaseValue z) :=
    (hasSum_thetaCuspShellEvenPhaseValue hz).summable
  have hD : Summable
      (thetaCuspShellEvenPhaseSpectralDerivativeValue z) :=
    (hasSum_thetaCuspShellEvenPhaseSpectralDerivativeValue hz).summable
  have hCV : Summable (fun n =>
      (starRingEnd ℂ) (thetaCuspShellEvenPhaseValue z n)) := by
    exact (Complex.conjCLE.summable).mpr hV
  have hmajor : Summable (fun q : ℕ × ℕ =>
      2 * ‖thetaCuspShellEvenPhaseSpectralDerivativeValue z q.1 *
        (starRingEnd ℂ) (thetaCuspShellEvenPhaseValue z q.2)‖) :=
    (hD.norm.mul_norm hCV.norm).mul_left 2
  apply Summable.of_norm_bounded hmajor
  intro q
  rw [thetaCuspShellPairHedenmalmCurrent, Real.norm_eq_abs,
    abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_left
    (Complex.abs_im_le_norm _) (by norm_num)

/-- Removing the zero row and column from an absolutely summable pair packet does not change its
sum when both coordinate axes vanish. -/
theorem tsum_pair_eq_tsum_succ_pair_of_axes_zero
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℕ × ℕ → E) (hF : Summable F)
    (hleft : ∀ n, F (0, n) = 0)
    (hright : ∀ n, F (n, 0) = 0) :
    (∑' q : ℕ × ℕ, F q) =
      ∑' q : ℕ × ℕ, F (q.1 + 1, q.2 + 1) := by
  have tsum_succ_of_zero (f : ℕ → E) (hf : Summable f) (hf0 : f 0 = 0) :
      (∑' n, f n) = ∑' n, f (n + 1) := by
    simpa only [Finset.sum_range_one, hf0, zero_add] using
      (hf.sum_add_tsum_nat_add 1).symm
  let S : ℕ × ℕ → ℕ × ℕ := fun q => (q.1, q.2 + 1)
  have hSinj : Function.Injective S := by
    rintro ⟨q₁, q₂⟩ ⟨r₁, r₂⟩ h
    simp only [S, Prod.mk.injEq] at h ⊢
    omega
  have hS : Summable (F ∘ S) := hF.comp_injective hSinj
  let T : ℕ × ℕ → ℕ × ℕ := fun q => (q.1 + 1, q.2 + 1)
  have hTinj : Function.Injective T := by
    rintro ⟨q₁, q₂⟩ ⟨r₁, r₂⟩ h
    simp only [T, Prod.mk.injEq] at h ⊢
    omega
  have hT : Summable (F ∘ T) := hF.comp_injective hTinj
  calc
    (∑' q : ℕ × ℕ, F q) =
        ∑' n : ℕ, ∑' m : ℕ, F (n, m) := hF.tsum_prod
    _ = ∑' n : ℕ, ∑' m : ℕ, F (n, m + 1) := by
      apply tsum_congr
      intro n
      exact tsum_succ_of_zero (fun m => F (n, m))
        (hF.prod_factor n) (hright n)
    _ = ∑' n : ℕ, ∑' m : ℕ, F (n + 1, m + 1) := by
      apply tsum_succ_of_zero
        (fun n => ∑' m : ℕ, F (n, m + 1))
      · simpa only [Function.comp_apply, S] using hS.prod
      · simp only [hleft, tsum_zero]
    _ = ∑' q : ℕ × ℕ, F (q.1 + 1, q.2 + 1) := by
      symm
      simpa only [Function.comp_apply, T] using hT.tsum_prod

/-- Exact absolutely convergent double-shell expansion of the horizontal completed-Xi current. -/
theorem xiCHorizontalCurrent_eq_tsum_thetaCuspShellPairHedenmalmCurrent
    {z : ℂ} (hz : |z.im| < 1) :
    2 * (((starRingEnd ℂ) (XiC z)) * (-I * deriv XiC z)).re =
      ∑' q : ℕ × ℕ, thetaCuspShellPairHedenmalmCurrent z q := by
  let V : ℕ → ℂ := thetaCuspShellEvenPhaseValue z
  let D : ℕ → ℂ := thetaCuspShellEvenPhaseSpectralDerivativeValue z
  have hV : Summable V :=
    (hasSum_thetaCuspShellEvenPhaseValue hz).summable
  have hD : Summable D :=
    (hasSum_thetaCuspShellEvenPhaseSpectralDerivativeValue hz).summable
  let CV : ℕ → ℂ := fun n => (starRingEnd ℂ) (V n)
  have hCV : Summable CV := by
    exact (Complex.conjCLE.summable).mpr hV
  have hpair : Summable (fun q : ℕ × ℕ => D q.1 * CV q.2) :=
    summable_mul_of_summable_norm hD.norm hCV.norm
  have hVsum : (∑' n, V n) = XiC z :=
    (hasSum_thetaCuspShellEvenPhaseValue hz).tsum_eq
  have hDsum : (∑' n, D n) = deriv XiC z :=
    (hasSum_thetaCuspShellEvenPhaseSpectralDerivativeValue hz).tsum_eq
  have hCVsum : (∑' n, CV n) = (starRingEnd ℂ) (XiC z) := by
    change (∑' n, Complex.conjCLE (V n)) = Complex.conjCLE (XiC z)
    rw [← hVsum, ← Complex.conjCLE.map_tsum]
  calc
    2 * (((starRingEnd ℂ) (XiC z)) * (-I * deriv XiC z)).re =
        2 * (deriv XiC z * (starRingEnd ℂ) (XiC z)).im := by
          simp only [mul_re, mul_im, conj_re, conj_im, neg_re, neg_im,
            I_re, I_im]
          ring
    _ = 2 * (((∑' n, D n) * (∑' n, CV n)).im) := by
      rw [hDsum, hCVsum]
    _ = 2 * (∑' q : ℕ × ℕ, D q.1 * CV q.2).im := by
      rw [tsum_mul_tsum_of_summable_norm hD.norm hCV.norm]
    _ = ∑' q : ℕ × ℕ,
        2 * (D q.1 * CV q.2).im := by
      rw [Complex.im_tsum hpair, tsum_mul_left]
    _ = ∑' q : ℕ × ℕ,
        thetaCuspShellPairHedenmalmCurrent z q := by
      apply tsum_congr
      intro q
      rfl

/-- The actual Hedenmalm Fourier current is the shell-pair current at `z = b - ia`. -/
theorem thetaCuspCenterMixedFourierCurrent_eq_tsum_shellPair
    {a : ℝ} (ha : |a| < 1) (b : ℝ) :
    thetaCuspCenterMixedFourierCurrent a ha b =
      ∑' q : ℕ × ℕ,
        thetaCuspShellPairHedenmalmCurrent
          ((b : ℂ) - (a : ℂ) * I) q := by
  have hz : |(((b : ℂ) - (a : ℂ) * I).im)| < 1 := by
    simpa only [sub_im, ofReal_im, mul_im, I_re, I_im, ofReal_re,
      zero_mul, mul_one, zero_sub, add_zero, abs_neg] using ha
  rw [thetaCuspCenterMixedFourierCurrent,
    fourier_thetaCuspHorizontalAutocorrelationTangent_scaled_eq_kreinForm ha b]
  simp only [ofReal_re]
  rw [thetaXiHankelOrbit_kreinForm_eq,
    thetaXiHankelOrbitValuePlus, thetaXiHankelOrbitTangentPlus]
  exact xiCHorizontalCurrent_eq_tsum_thetaCuspShellPairHedenmalmCurrent hz

/-- Positive-index source-shell pair, using zero-based coordinates for arithmetic fibres. -/
def thetaCuspPositiveShellPairHedenmalmCurrent
    (z : ℂ) (q : ℕ × ℕ) : ℝ :=
  thetaCuspShellPairHedenmalmCurrent z (q.1 + 1, q.2 + 1)

/-- Actual completed-source current on one fixed positive product fibre. -/
def thetaCuspSourceProductFiberHedenmalmCurrent
    (k : ℕ) (z : ℂ) : ℝ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    thetaCuspPositiveShellPairHedenmalmCurrent z q

/-- Endpoint slope of one completed-source shell. -/
def thetaCuspShellSeamSlope (n : ℕ) : ℝ :=
  iteratedDeriv 1 (fun x : ℝ => thetaCuspSourceTerm x n) 0

@[simp] theorem thetaCuspShellSeamSlope_zero :
    thetaCuspShellSeamSlope 0 = 0 := by
  rw [thetaCuspShellSeamSlope,
    iteratedDeriv_one_thetaCuspSourceTerm_zero_eq_slope]
  simp [thetaCuspSourceTerm, thetaCuspSeed]

theorem thetaCuspShellSeamSlope_one_pos :
    0 < thetaCuspShellSeamSlope 1 := by
  rw [thetaCuspShellSeamSlope,
    iteratedDeriv_one_thetaCuspSourceTerm_zero_eq_slope]
  have hslope :
      thetaCuspAtomBoundaryLogSlope 1 =
        thetaCuspFirstAtomBoundaryLogSlope := by
    simp [thetaCuspAtomBoundaryLogSlope, thetaCuspFirstAtomBoundaryLogSlope]
  rw [hslope]
  exact mul_pos thetaCuspFirstAtomBoundaryLogSlope_pos
    thetaCuspSourceTerm_one_zero_pos

theorem thetaCuspShellSeamSlope_neg
    {n : ℕ} (hn : 2 ≤ n) :
    thetaCuspShellSeamSlope n < 0 :=
  iteratedDeriv_one_thetaCuspSourceTerm_zero_neg hn

theorem summable_thetaCuspShellSeamSlope :
    Summable thetaCuspShellSeamSlope :=
  summable_iteratedDeriv_thetaCuspSourceTerm 1 0

theorem tsum_thetaCuspShellSeamSlope_eq_zero :
    (∑' n : ℕ, thetaCuspShellSeamSlope n) = 0 :=
  tsum_iteratedDeriv_one_thetaCuspSourceTerm_zero_eq_zero

/-- The `(2r+1)`st endpoint jet of one completed-source shell. -/
def thetaCuspShellOddSeamJet (r n : ℕ) : ℝ :=
  iteratedDeriv (2 * r + 1) (fun x : ℝ => thetaCuspSourceTerm x n) 0

theorem summable_thetaCuspShellOddSeamJet (r : ℕ) :
    Summable (thetaCuspShellOddSeamJet r) :=
  summable_iteratedDeriv_thetaCuspSourceTerm (2 * r + 1) 0

/-- Modular reflection cancels every odd endpoint jet across the complete shell family. -/
theorem tsum_thetaCuspShellOddSeamJet_eq_zero (r : ℕ) :
    (∑' n : ℕ, thetaCuspShellOddSeamJet r n) = 0 := by
  change thetaCuspFullDerivative (2 * r + 1) 0 = 0
  rw [← congrFun (iteratedDeriv_thetaCuspFullSource (2 * r + 1)) 0]
  exact iteratedDeriv_thetaCuspFullSource_zero_of_odd
    (odd_two_mul_add_one r)

/-- Fixed-product convolution coefficient for two arbitrary odd shell jets. -/
def thetaCuspSourceProductFiberOddJetCoefficient
    (r s k : ℕ) : ℝ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    thetaCuspShellOddSeamJet r (q.1 + 1) *
      thetaCuspShellOddSeamJet s (q.2 + 1)

/-- **All-order cofinal seam cancellation.**  Every bi-odd endpoint-jet convolution cancels only
after summing the complete infinite arithmetic-fibre family. -/
theorem tsum_thetaCuspSourceProductFiberOddJetCoefficient_eq_zero
    (r s : ℕ) :
    (∑' k : ℕ,
      thetaCuspSourceProductFiberOddJetCoefficient r s k) = 0 := by
  let u : ℕ → ℝ := fun n => thetaCuspShellOddSeamJet r (n + 1)
  let v : ℕ → ℝ := fun n => thetaCuspShellOddSeamJet s (n + 1)
  have hu : Summable u := by
    exact (summable_nat_add_iff 1).mpr
      (summable_thetaCuspShellOddSeamJet r)
  have hv : Summable v := by
    exact (summable_nat_add_iff 1).mpr
      (summable_thetaCuspShellOddSeamJet s)
  have hu0 : thetaCuspShellOddSeamJet r 0 = 0 := by
    simp [thetaCuspShellOddSeamJet, thetaCuspSourceTerm, thetaCuspSeed]
  have hv0 : thetaCuspShellOddSeamJet s 0 = 0 := by
    simp [thetaCuspShellOddSeamJet, thetaCuspSourceTerm, thetaCuspSeed]
  have husum : (∑' n : ℕ, u n) = 0 := by
    have hsplit :=
      (summable_thetaCuspShellOddSeamJet r).sum_add_tsum_nat_add 1
    rw [tsum_thetaCuspShellOddSeamJet_eq_zero r] at hsplit
    simpa only [Finset.sum_range_one, hu0, zero_add, u] using hsplit
  have hvsum : (∑' n : ℕ, v n) = 0 := by
    have hsplit :=
      (summable_thetaCuspShellOddSeamJet s).sum_add_tsum_nat_add 1
    rw [tsum_thetaCuspShellOddSeamJet_eq_zero s] at hsplit
    simpa only [Finset.sum_range_one, hv0, zero_add, v] using hsplit
  have hpair : Summable (fun q : ℕ × ℕ => u q.1 * v q.2) :=
    summable_mul_of_summable_norm hu.norm hv.norm
  rw [show thetaCuspSourceProductFiberOddJetCoefficient r s =
      fun k => ∑ q ∈ thetaPositiveFactorPairs k, u q.1 * v q.2 by
    funext k
    rfl]
  rw [← tsum_eq_tsum_thetaPositiveFactorPairs _ hpair]
  rw [← tsum_mul_tsum_of_summable_norm hu.norm hv.norm, husum, hvsum]
  ring

/-- Dirichlet-convolution seam coefficient carried by one positive product fibre. -/
def thetaCuspSourceProductFiberSeamCoefficient (k : ℕ) : ℝ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    thetaCuspShellSeamSlope (q.1 + 1) *
      thetaCuspShellSeamSlope (q.2 + 1)

/-- Ground fibre has the wrong high-frequency orientation coefficient. -/
theorem thetaCuspSourceProductFiberSeamCoefficient_one_pos :
    0 < thetaCuspSourceProductFiberSeamCoefficient 1 := by
  have hf : thetaPositiveFactorPairs 1 = {(0, 0)} := by
    ext q
    rcases q with ⟨m, n⟩
    simp [thetaPositiveFactorPairs]
  have h :
      thetaCuspSourceProductFiberSeamCoefficient 1 =
        thetaCuspShellSeamSlope 1 ^ (2 : ℕ) := by
    rw [thetaCuspSourceProductFiberSeamCoefficient, hf]
    simp [pow_two]
  rw [h]
  positivity [thetaCuspShellSeamSlope_one_pos]

/-- Every prime fibre has the opposite leading orientation from the ground fibre. -/
theorem thetaCuspSourceProductFiberSeamCoefficient_prime_neg
    {p : ℕ} (hp : p.Prime) :
    thetaCuspSourceProductFiberSeamCoefficient p < 0 := by
  unfold thetaCuspSourceProductFiberSeamCoefficient
  apply Finset.sum_neg
  · intro q hq
    rcases thetaFactorPair_indices_of_prime hp hq with h | h
    · rw [h.1, h.2]
      exact mul_neg_of_pos_of_neg thetaCuspShellSeamSlope_one_pos
        (thetaCuspShellSeamSlope_neg hp.two_le)
    · rw [h.1, h.2]
      exact mul_neg_of_neg_of_pos
        (thetaCuspShellSeamSlope_neg hp.two_le)
        thetaCuspShellSeamSlope_one_pos
  · refine ⟨(0, p - 1), ?_⟩
    have hp0 : 0 < p := hp.pos
    have hp1 : 1 ≤ p := hp.one_le
    simp [thetaPositiveFactorPairs, hp0, hp1,
      Nat.sub_lt hp0 (by norm_num : 0 < 1)]

/-- The full arithmetic seam spectrum cancels exactly.  Fixed fibres retain nonzero algebraic
endpoint currents, while their cofinal sum has zero leading coefficient. -/
theorem tsum_thetaCuspSourceProductFiberSeamCoefficient_eq_zero :
    (∑' k : ℕ, thetaCuspSourceProductFiberSeamCoefficient k) = 0 := by
  let d : ℕ → ℝ := fun n => thetaCuspShellSeamSlope (n + 1)
  have hd : Summable d := by
    exact (summable_nat_add_iff 1).mpr summable_thetaCuspShellSeamSlope
  have hdsum : (∑' n : ℕ, d n) = 0 := by
    have hsplit :=
      summable_thetaCuspShellSeamSlope.sum_add_tsum_nat_add 1
    rw [tsum_thetaCuspShellSeamSlope_eq_zero] at hsplit
    simpa only [Finset.sum_range_one, thetaCuspShellSeamSlope_zero,
      zero_add, d] using hsplit
  have hpair : Summable (fun q : ℕ × ℕ => d q.1 * d q.2) :=
    summable_mul_of_summable_norm hd.norm hd.norm
  rw [show thetaCuspSourceProductFiberSeamCoefficient =
      fun k => ∑ q ∈ thetaPositiveFactorPairs k, d q.1 * d q.2 by
    funext k
    rfl]
  rw [← tsum_eq_tsum_thetaPositiveFactorPairs _ hpair]
  rw [← tsum_mul_tsum_of_summable_norm hd.norm hd.norm, hdsum]
  ring

theorem summable_thetaCuspPositiveShellPairHedenmalmCurrent
    {z : ℂ} (hz : |z.im| < 1) :
    Summable (thetaCuspPositiveShellPairHedenmalmCurrent z) := by
  let T : ℕ × ℕ → ℕ × ℕ := fun q => (q.1 + 1, q.2 + 1)
  have hTinj : Function.Injective T := by
    rintro ⟨q₁, q₂⟩ ⟨r₁, r₂⟩ h
    simp only [T, Prod.mk.injEq] at h ⊢
    omega
  exact (summable_thetaCuspShellPairHedenmalmCurrent hz).comp_injective hTinj

/-- **Actual-source arithmetic-fibre bridge.**  The Hedenmalm Fourier current, not the auxiliary
`4T''` density current, is the absolutely convergent sum of its completed-source product fibres. -/
theorem thetaCuspCenterMixedFourierCurrent_eq_tsum_sourceProductFiber
    {a : ℝ} (ha : |a| < 1) (b : ℝ) :
    thetaCuspCenterMixedFourierCurrent a ha b =
      ∑' k : ℕ,
        thetaCuspSourceProductFiberHedenmalmCurrent k
          ((b : ℂ) - (a : ℂ) * I) := by
  let z : ℂ := (b : ℂ) - (a : ℂ) * I
  have hz : |z.im| < 1 := by
    dsimp [z]
    simpa only [sub_im, ofReal_im, mul_im, I_re, I_im, ofReal_re,
      zero_mul, mul_one, zero_sub, add_zero, abs_neg] using ha
  let F : ℕ × ℕ → ℝ := thetaCuspShellPairHedenmalmCurrent z
  have hF : Summable F := summable_thetaCuspShellPairHedenmalmCurrent hz
  have hleft (n : ℕ) : F (0, n) = 0 := by
    simp [F, thetaCuspShellPairHedenmalmCurrent,
      thetaCuspShellEvenPhaseSpectralDerivativeValue]
  have hright (n : ℕ) : F (n, 0) = 0 := by
    simp [F, thetaCuspShellPairHedenmalmCurrent,
      thetaCuspShellEvenPhaseValue]
  rw [thetaCuspCenterMixedFourierCurrent_eq_tsum_shellPair ha b]
  change (∑' q : ℕ × ℕ, F q) = _
  rw [tsum_pair_eq_tsum_succ_pair_of_axes_zero F hF hleft hright]
  change (∑' q : ℕ × ℕ,
      thetaCuspPositiveShellPairHedenmalmCurrent z q) = _
  rw [tsum_eq_tsum_thetaPositiveFactorPairs _
    (summable_thetaCuspPositiveShellPairHedenmalmCurrent hz)]
  rfl

end

end RHTower
