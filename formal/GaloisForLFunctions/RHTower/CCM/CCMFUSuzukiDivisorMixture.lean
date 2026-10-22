import GaloisForLFunctions.RHTower.CCM.CCMFUSuzukiPositiveMixture
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewCesaroLandauRecurrence

open Complex MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- One literal divisor mode under CCM-FU's moving marked rectangular reporter. -/
def ccmFUXiScrewDivisorTermMixture (b H : ℝ) (q : XiZeroCopy) : ℂ :=
  (∫ t in b..H,
    (ccmThirdGradeCesaroRectangularMixDensity H t : ℂ) * xiScrewDivisorTerm t q) +
    (32 / H ^ (4 : ℕ) : ℝ) * xiScrewDivisorTerm H q

/-- The same moving marked reporter applied before summing divisor modes. -/
def ccmFUXiScrewDivisorMixture (b H : ℝ) : ℂ :=
  (∫ t in b..H,
    (ccmThirdGradeCesaroRectangularMixDensity H t : ℂ) * xiScrewDivisor t) +
    (32 / H ^ (4 : ℕ) : ℝ) * xiScrewDivisor H

private theorem continuous_xiScrewDivisorTerm (q : XiZeroCopy) :
    Continuous (fun t : ℝ => xiScrewDivisorTerm t q) := by
  unfold xiScrewDivisorTerm
  fun_prop

private theorem rectangular_density_continuousOn
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ContinuousOn (ccmThirdGradeCesaroRectangularMixDensity H) (Icc b H) := by
  have hH : 0 < H := hb.trans_le hbH
  intro t ht
  have ht0 : t ≠ 0 := (hb.trans_le ht.1).ne'
  unfold ccmThirdGradeCesaroRectangularMixDensity
  exact ((continuousAt_const.mul (continuousAt_const.sub continuousAt_id)).div
    (continuousAt_const.mul (continuousAt_id.pow 5))
    (mul_ne_zero hH.ne' (pow_ne_zero 5 ht0))).continuousWithinAt

private theorem rectangular_density_mul_term_integrableOn
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) (q : XiZeroCopy) :
    IntegrableOn (fun t : ℝ =>
      (ccmThirdGradeCesaroRectangularMixDensity H t : ℂ) * xiScrewDivisorTerm t q)
      (Ioc b H) := by
  have hρ := rectangular_density_continuousOn hb hbH
  have hρC : ContinuousOn (fun t : ℝ =>
      (ccmThirdGradeCesaroRectangularMixDensity H t : ℂ)) (Icc b H) :=
    Complex.continuous_ofReal.comp_continuousOn hρ
  exact (hρC.mul (continuous_xiScrewDivisorTerm q).continuousOn).integrableOn_Icc.mono_set
    Ioc_subset_Icc_self

private theorem summable_integral_norm_rectangular_density_mul_term
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    Summable (fun q : XiZeroCopy => ∫ t in Ioc b H,
      ‖(ccmThirdGradeCesaroRectangularMixDensity H t : ℂ) * xiScrewDivisorTerm t q‖) := by
  have hH : 0 < H := hb.trans_le hbH
  let mass : ℝ := ∫ t in Ioc b H, ccmThirdGradeCesaroRectangularMixDensity H t
  have hρ := rectangular_density_continuousOn hb hbH
  have hsum0 := xiSpectralPoint_inv_sq_summable.mul_left
    (mass * (Real.exp (H / 2) + 1))
  have hsum : Summable (fun q : XiZeroCopy =>
      mass * ((Real.exp (H / 2) + 1) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)))) :=
    by simpa only [mul_assoc] using hsum0
  refine Summable.of_nonneg_of_le (fun q => integral_nonneg fun _ => norm_nonneg _) (fun q => ?_)
    hsum
  have hweight : IntegrableOn (fun t : ℝ =>
      ccmThirdGradeCesaroRectangularMixDensity H t *
        ((Real.exp (H / 2) + 1) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)))) (Ioc b H) :=
    (hρ.mul continuousOn_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  calc
    (∫ t in Ioc b H,
        ‖(ccmThirdGradeCesaroRectangularMixDensity H t : ℂ) * xiScrewDivisorTerm t q‖) ≤
        ∫ t in Ioc b H, ccmThirdGradeCesaroRectangularMixDensity H t *
          ((Real.exp (H / 2) + 1) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) := by
      refine setIntegral_mono_on
        (rectangular_density_mul_term_integrableOn hb hbH q).norm hweight measurableSet_Ioc ?_
      intro t ht
      have ht0 : 0 ≤ t := le_of_lt (lt_of_lt_of_le hb ht.1.le)
      have htH : t ≤ H := ht.2
      have hρ0 : 0 ≤ ccmThirdGradeCesaroRectangularMixDensity H t :=
        ccmThirdGradeCesaroRectangularMixDensity_nonneg hH (lt_of_lt_of_le hb ht.1.le) htH
      rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
      refine mul_le_mul_of_nonneg_left ?_ hρ0
      calc
        ‖xiScrewDivisorTerm t q‖ ≤
            (Real.exp (|t| / 2) + 1) / ‖xiSpectralPoint q‖ ^ (2 : ℕ) :=
          norm_xiScrewDivisorTerm_le t q
        _ ≤ (Real.exp (H / 2) + 1) / ‖xiSpectralPoint q‖ ^ (2 : ℕ) := by
          gcongr
          rw [abs_of_nonneg ht0]
          linarith
        _ = (Real.exp (H / 2) + 1) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring
    _ = mass * ((Real.exp (H / 2) + 1) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) := by
      dsimp only [mass]
      rw [integral_mul_const]

theorem ccmFUXiScrewDivisorMixture_eq_tsum_termMixture
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    ccmFUXiScrewDivisorMixture b H =
      ∑' q : XiZeroCopy, ccmFUXiScrewDivisorTermMixture b H q := by
  have hterm := rectangular_density_mul_term_integrableOn hb hbH
  have hnorm := summable_integral_norm_rectangular_density_mul_term hb hbH
  have hswap := MeasureTheory.integral_tsum_of_summable_integral_norm hterm hnorm
  unfold ccmFUXiScrewDivisorMixture ccmFUXiScrewDivisorTermMixture xiScrewDivisor
  rw [intervalIntegral.integral_of_le hbH]
  have hpoint : ∀ t : ℝ,
      (ccmThirdGradeCesaroRectangularMixDensity H t : ℂ) *
          (∑' q : XiZeroCopy, xiScrewDivisorTerm t q) =
        ∑' q : XiZeroCopy,
          (ccmThirdGradeCesaroRectangularMixDensity H t : ℂ) * xiScrewDivisorTerm t q := by
    intro t
    exact (tsum_mul_left).symm
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), ← hswap, ← tsum_mul_left]
  let F : XiZeroCopy → ℂ := fun q =>
    ∫ t in Ioc b H,
      (ccmThirdGradeCesaroRectangularMixDensity H t : ℂ) * xiScrewDivisorTerm t q
  let G : XiZeroCopy → ℂ := fun q =>
    ((32 / H ^ (4 : ℕ) : ℝ) : ℂ) * xiScrewDivisorTerm H q
  have hF : Summable F := by
    dsimp only [F]
    apply Summable.of_norm_bounded hnorm
    intro q
    exact norm_integral_le_integral_norm _
  have hG : Summable G := by
    simpa only [G] using (xiScrewDivisorTerm_summable H).mul_left ((32 / H ^ (4 : ℕ) : ℝ) : ℂ)
  let K : XiZeroCopy → ℂ := fun q =>
    (∫ t in b..H,
      (ccmThirdGradeCesaroRectangularMixDensity H t : ℂ) * xiScrewDivisorTerm t q) + G q
  change (∑' q : XiZeroCopy, F q) + ∑' q : XiZeroCopy, G q =
    ∑' q : XiZeroCopy, K q
  calc
    (∑' q : XiZeroCopy, F q) + ∑' q : XiZeroCopy, G q =
      ∑' q : XiZeroCopy, (F q + G q) :=
      (hF.tsum_add hG).symm
    _ = ∑' q : XiZeroCopy, K q := by
      apply tsum_congr
      intro q
      dsimp only [F, K]
      rw [intervalIntegral.integral_of_le hbH]

/-- The literal real CCM-FU source readout is the full complex divisor readout before
any estimate. The equality preserves every signed divisor contribution and the moving endpoint. -/
theorem ofReal_ccmFUCentralXiScrewPositiveMixture_eq_divisorMixture
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    (ccmFUCentralXiScrewPositiveMixture b H : ℂ) = ccmFUXiScrewDivisorMixture b H := by
  have hρ := rectangular_density_continuousOn hb hbH
  have hρψ : IntervalIntegrable
      (fun t : ℝ => ccmThirdGradeCesaroRectangularMixDensity H t * suzukiPsi t)
      volume b H := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hbH]
    exact hρ.mul continuous_suzukiPsi.continuousOn
  have hbulk :
      ((∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * suzukiPsi t : ℝ) : ℂ) =
        ∫ t in b..H,
          (ccmThirdGradeCesaroRectangularMixDensity H t : ℂ) * xiScrewDivisor t := by
    calc
      ((∫ t in b..H, ccmThirdGradeCesaroRectangularMixDensity H t * suzukiPsi t : ℝ) : ℂ) =
          ∫ t in b..H,
            (Complex.ofRealCLM)
              (ccmThirdGradeCesaroRectangularMixDensity H t * suzukiPsi t) := by
            exact (Complex.ofRealCLM.intervalIntegral_comp_comm hρψ).symm
      _ = ∫ t in b..H,
          (ccmThirdGradeCesaroRectangularMixDensity H t : ℂ) * xiScrewDivisor t := by
        apply intervalIntegral.integral_congr
        intro t _
        change (↑(ccmThirdGradeCesaroRectangularMixDensity H t * suzukiPsi t) : ℂ) = _
        rw [Complex.ofReal_mul, ofReal_suzukiPsi_eq_xiScrewDivisor_all]
  have hend :
      (((32 / H ^ (4 : ℕ)) * suzukiPsi H : ℝ) : ℂ) =
        ((32 / H ^ (4 : ℕ) : ℝ) : ℂ) * xiScrewDivisor H := by
    rw [Complex.ofReal_mul, ofReal_suzukiPsi_eq_xiScrewDivisor_all]
  unfold ccmFUCentralXiScrewPositiveMixture ccmFUXiScrewDivisorMixture
  rw [Complex.ofReal_add, hbulk, hend]

/-- Literal CCM-FU in divisor coordinates. No sign, truncation, or mode is discarded. -/
theorem ofReal_ccmFUCentralXiScrewPositiveMixture_eq_tsum_termMixture
    {b H : ℝ} (hb : 0 < b) (hbH : b ≤ H) :
    (ccmFUCentralXiScrewPositiveMixture b H : ℂ) =
      ∑' q : XiZeroCopy, ccmFUXiScrewDivisorTermMixture b H q := by
  rw [ofReal_ccmFUCentralXiScrewPositiveMixture_eq_divisorMixture hb hbH,
    ccmFUXiScrewDivisorMixture_eq_tsum_termMixture hb hbH]

end GaloisForLFunctions.RHTower
