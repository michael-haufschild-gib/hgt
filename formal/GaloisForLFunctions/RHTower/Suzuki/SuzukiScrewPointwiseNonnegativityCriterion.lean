import GaloisForLFunctions.RHTower.CCM.CCMFirstClockLandauHalving
import GaloisForLFunctions.RHTower.CCM.CCMFirstClockTailLowerBoundCompleteness
import GaloisForLFunctions.RHTower.CCM.CCMFirstClockAsymptoticBohrLaw
import GaloisForLFunctions.RHTower.Suzuki.SuzukiScrewFourierTransform

/-!
# Suzuki's pointwise nonnegativity criterion

This module formalizes the non-strict equivalence in Theorem 1.7 of Suzuki,
*Aspects of the screw function corresponding to the Riemann zeta-function*
(arXiv:2206.03682).

The hard direction is Widder--Landau propagation.  For the literal displayed function `Psi`,
pointwise nonnegativity turns each exponentially damped profile into a positive measure.  A
normally convergent rational continuation of its exact Xi-zero Laplace transform is holomorphic
on every half-radius disk centered on the positive real axis.  Taylor--Tonelli transfer therefore
halves the abscissa of convergence repeatedly, giving every positive exponential moment.  The
complete Xi pole theorem then forces RH.
-/

open Complex MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Suzuki's pointwise nonnegativity condition on the source half-line. -/
def SuzukiPsiPointwiseNonnegative : Prop :=
  ∀ t : ℝ, 0 ≤ t → 0 ≤ suzukiPsi t

/-- One rational Laplace atom of the complete multiplicity-exact Suzuki zero series. -/
def suzukiPsiLaplaceAtom (s z : ℂ) : ℂ :=
  1 / (s * (s ^ 2 + z ^ 2))

/-- Normally convergent rational continuation of Suzuki's one-sided Laplace transform. -/
def suzukiPsiLaplaceContinuation (s : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, suzukiPsiLaplaceAtom s (xiSpectralPoint q)

/-- The literal source Laplace transform. -/
def suzukiPsiLaplace (s : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0,
    Complex.exp (-s * (t : ℂ)) * (suzukiPsi t : ℂ)

private theorem suzukiPsiLaplaceAtom_eq_factored
    {s z : ℂ} (hs : s ≠ 0) (hz : z ≠ 0)
    (hminus : s - I * z ≠ 0) (hplus : s + I * z ≠ 0) :
    suzukiPsiLaplaceAtom s z =
      (1 / s - s / (s ^ 2 + z ^ 2)) / z ^ 2 := by
  have hquad : s ^ 2 + z ^ 2 ≠ 0 := by
    rw [show s ^ 2 + z ^ 2 = (s - I * z) * (s + I * z) by
      rw [mul_add, sub_mul]
      ring_nf
      rw [I_sq]
      ring]
    exact mul_ne_zero hminus hplus
  unfold suzukiPsiLaplaceAtom
  field_simp
  ring

private theorem norm_inv_sub_le_twenty_div_suzuki
    {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : s ∈ Metric.ball (r : ℂ) (r / 2))
    (q : XiZeroCopy) :
    ‖1 / (s - I * xiSpectralPoint q)‖ ≤ 20 / r := by
  have hcone := closedBall_real_axis_subset_ccmFirstClockLaplaceCone hr
    (Metric.ball_subset_closedBall hs)
  have hsep := ccmFirstClockLaplaceCone_norm_sub hcone.1 hcone.2 q
    (u := 1) (by norm_num)
  simp only [Complex.ofReal_one, mul_one] at hsep
  have hdenpos : 0 < ‖s - I * xiSpectralPoint q‖ := by
    exact (div_pos hcone.1 (by norm_num : (0 : ℝ) < 10)).trans_le hsep
  have hre := re_lower_of_mem_firstClock_ball hr hs
  rw [norm_div, norm_one]
  apply (div_le_div_iff₀ hdenpos hr).2
  nlinarith

private theorem norm_inv_add_le_twenty_div_suzuki
    {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : s ∈ Metric.ball (r : ℂ) (r / 2))
    (q : XiZeroCopy) :
    ‖1 / (s + I * xiSpectralPoint q)‖ ≤ 20 / r := by
  have hcone := closedBall_real_axis_subset_ccmFirstClockLaplaceCone hr
    (Metric.ball_subset_closedBall hs)
  have hsep := ccmFirstClockLaplaceCone_norm_add hcone.1 hcone.2 q
    (u := 1) (by norm_num)
  simp only [Complex.ofReal_one, mul_one] at hsep
  have hdenpos : 0 < ‖s + I * xiSpectralPoint q‖ := by
    exact (div_pos hcone.1 (by norm_num : (0 : ℝ) < 10)).trans_le hsep
  have hre := re_lower_of_mem_firstClock_ball hr hs
  rw [norm_div, norm_one]
  apply (div_le_div_iff₀ hdenpos hr).2
  nlinarith

private theorem norm_s_le_three_halves_mul
    {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : s ∈ Metric.ball (r : ℂ) (r / 2)) :
    ‖s‖ ≤ 3 * r / 2 := by
  have hdist : ‖s - (r : ℂ)‖ < r / 2 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hs
  calc
    ‖s‖ = ‖(s - (r : ℂ)) + (r : ℂ)‖ := by ring_nf
    _ ≤ ‖s - (r : ℂ)‖ + ‖(r : ℂ)‖ := norm_add_le _ _
    _ ≤ 3 * r / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      linarith

private theorem norm_inv_s_le_two_div
    {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : s ∈ Metric.ball (r : ℂ) (r / 2)) :
    ‖1 / s‖ ≤ 2 / r := by
  have hre := re_lower_of_mem_firstClock_ball hr hs
  have hnorm : s.re ≤ ‖s‖ :=
    (le_abs_self s.re).trans (Complex.abs_re_le_norm s)
  have hspos : 0 < ‖s‖ := (lt_trans (by positivity : 0 < r / 2) hre).trans_le hnorm
  rw [norm_div, norm_one]
  apply (div_le_div_iff₀ hspos hr).2
  nlinarith

/-- Uniform reciprocal-square majorant for the Suzuki rational atoms on a positive-axis disk. -/
theorem norm_suzukiPsiLaplaceAtom_le_ball
    {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : s ∈ Metric.ball (r : ℂ) (r / 2))
    (q : XiZeroCopy) :
    ‖suzukiPsiLaplaceAtom s (xiSpectralPoint q)‖ ≤
      (602 / r) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  let z : ℂ := xiSpectralPoint q
  have hcone := closedBall_real_axis_subset_ccmFirstClockLaplaceCone hr
    (Metric.ball_subset_closedBall hs)
  have hs0 : s ≠ 0 := by
    intro hzero
    rw [hzero, zero_re] at hcone
    linarith
  have hz0 : z ≠ 0 := xiSpectralPoint_ne_zero q
  have hminus : s - I * z ≠ 0 := by
    simpa [z] using ccmFirstClockLaplaceCone_sub_ne_zero hcone.1 hcone.2 q
      (u := 1) (by norm_num)
  have hplus : s + I * z ≠ 0 := by
    simpa [z] using ccmFirstClockLaplaceCone_add_ne_zero hcone.1 hcone.2 q
      (u := 1) (by norm_num)
  have hfactor : s ^ 2 + z ^ 2 = (s - I * z) * (s + I * z) := by
    rw [mul_add, sub_mul]
    ring_nf
    rw [I_sq]
    ring
  have hfrac : s / (s ^ 2 + z ^ 2) =
      s * (1 / (s - I * z)) * (1 / (s + I * z)) := by
    rw [hfactor]
    field_simp [hminus, hplus]
  have hinvMinus := norm_inv_sub_le_twenty_div_suzuki hr hs q
  have hinvPlus := norm_inv_add_le_twenty_div_suzuki hr hs q
  have hsUpper := norm_s_le_three_halves_mul hr hs
  have hsecond : ‖s / (s ^ 2 + z ^ 2)‖ ≤ 600 / r := by
    rw [hfrac, norm_mul, norm_mul]
    calc
      ‖s‖ * ‖1 / (s - I * z)‖ * ‖1 / (s + I * z)‖ ≤
          (3 * r / 2) * (20 / r) * (20 / r) := by gcongr
      _ = 600 / r := by field_simp; ring
  have hfirst := norm_inv_s_le_two_div hr hs
  rw [suzukiPsiLaplaceAtom_eq_factored hs0 hz0 hminus hplus,
    norm_div, norm_pow]
  calc
    ‖1 / s - s / (s ^ 2 + z ^ 2)‖ / ‖z‖ ^ 2 ≤
        (602 / r) / ‖z‖ ^ 2 := by
      gcongr
      calc
        ‖1 / s - s / (s ^ 2 + z ^ 2)‖ ≤
            ‖1 / s‖ + ‖s / (s ^ 2 + z ^ 2)‖ := norm_sub_le _ _
        _ ≤ 2 / r + 600 / r := add_le_add hfirst hsecond
        _ = 602 / r := by ring
    _ = (602 / r) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
      dsimp only [z]
      ring

theorem differentiableOn_suzukiPsiLaplaceAtom_ball
    {r : ℝ} (hr : 0 < r) (q : XiZeroCopy) :
    DifferentiableOn ℂ
      (fun s => suzukiPsiLaplaceAtom s (xiSpectralPoint q))
      (Metric.ball (r : ℂ) (r / 2)) := by
  intro s hs
  have hcone := closedBall_real_axis_subset_ccmFirstClockLaplaceCone hr
    (Metric.ball_subset_closedBall hs)
  have hs0 : s ≠ 0 := by
    intro hzero
    rw [hzero, zero_re] at hcone
    linarith
  have hminus := ccmFirstClockLaplaceCone_sub_ne_zero hcone.1 hcone.2 q
    (u := 1) (by norm_num)
  have hplus := ccmFirstClockLaplaceCone_add_ne_zero hcone.1 hcone.2 q
    (u := 1) (by norm_num)
  simp only [Complex.ofReal_one, mul_one] at hminus hplus
  have hquad : s ^ 2 + xiSpectralPoint q ^ 2 ≠ 0 := by
    rw [show s ^ 2 + xiSpectralPoint q ^ 2 =
        (s - I * xiSpectralPoint q) * (s + I * xiSpectralPoint q) by
      rw [mul_add, sub_mul]
      ring_nf
      rw [I_sq]
      ring]
    exact mul_ne_zero hminus hplus
  change DifferentiableWithinAt ℂ
    (fun w : ℂ => 1 / (w * (w ^ 2 + xiSpectralPoint q ^ 2)))
    (Metric.ball (r : ℂ) (r / 2)) s
  apply DifferentiableAt.differentiableWithinAt
  exact (differentiableAt_const (c := (1 : ℂ))).div
    (by fun_prop) (mul_ne_zero hs0 hquad)

/-- The complete Suzuki rational continuation is holomorphic on every half-radius disk centered
on the positive Laplace axis. -/
theorem differentiableOn_suzukiPsiLaplaceContinuation_ball
    {r : ℝ} (hr : 0 < r) :
    DifferentiableOn ℂ suzukiPsiLaplaceContinuation
      (Metric.ball (r : ℂ) (r / 2)) := by
  unfold suzukiPsiLaplaceContinuation
  apply Complex.differentiableOn_tsum_of_summable_norm
    (u := fun q : XiZeroCopy =>
      (602 / r) * (1 / ‖xiSpectralPoint q‖ ^ 2))
  · exact xiSpectralPoint_inv_sq_summable.mul_left (602 / r)
  · exact differentiableOn_suzukiPsiLaplaceAtom_ball hr
  · exact Metric.isOpen_ball
  · intro q s hs
    exact norm_suzukiPsiLaplaceAtom_le_ball hr hs q

/-- On Suzuki's unconditional half-plane, the literal source Laplace transform is its rational
Xi-zero continuation. -/
theorem suzukiPsiLaplace_eq_continuation
    {s : ℂ} (hs : 1 / 2 < s.re) :
    suzukiPsiLaplace s = suzukiPsiLaplaceContinuation s := by
  calc
    suzukiPsiLaplace s =
        ∫ t : ℝ in Ioi 0,
          Complex.exp (-s * (t : ℂ)) * xiScrewDivisor t := by
      unfold suzukiPsiLaplace
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      rw [ofReal_suzukiPsi_eq_xiScrewDivisor ht.le]
    _ = I / s ^ 2 * logDeriv XiC (I * s) :=
      integral_exp_mul_xiScrewDivisor_eq_logDeriv_XiC hs
    _ = suzukiPsiLaplaceContinuation s := by
      rw [← tsum_screwLaplace_eq_logDeriv_XiC hs]
      rfl

/-- Real positive density obtained by centering Suzuki's exact screw at Laplace abscissa `r`. -/
def suzukiPsiLandauDensity (r t : ℝ) : ℝ :=
  Real.exp (-r * t) * (xiScrewDivisor t).re

theorem measurable_suzukiPsiLandauDensity (r : ℝ) :
    Measurable (suzukiPsiLandauDensity r) := by
  unfold suzukiPsiLandauDensity
  exact (by fun_prop : Measurable (fun t : ℝ => Real.exp (-r * t))).mul
    measurable_xiScrewDivisor.re

theorem suzukiPsiLandauDensity_nonneg_ae
    (hsource : SuzukiPsiPointwiseNonnegative) (r : ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ suzukiPsiLandauDensity r t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  unfold suzukiPsiLandauDensity
  apply mul_nonneg (Real.exp_pos _).le
  rw [← suzukiPsi_eq_xiScrewDivisor_re ht.le]
  exact hsource t ht.le

/-- Unconditional initial integrability, obtained directly from the complete divisor bound. -/
theorem integrableOn_suzukiPsiLandauDensity
    {r : ℝ} (hr : 1 / 2 < r) :
    IntegrableOn (suzukiPsiLandauDensity r) (Ioi 0) := by
  let M : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2
  let g : ℝ → ℝ := fun t =>
    (Real.exp ((-r + 1 / 2) * t) + Real.exp (-r * t)) * M
  have hdecay1 : -r + 1 / 2 < 0 := by linarith
  have hdecay2 : -r < 0 := by linarith
  have hg : IntegrableOn g (Ioi 0) :=
    ((integrableOn_exp_mul_Ioi hdecay1 0).add
      (integrableOn_exp_mul_Ioi hdecay2 0)).mul_const M
  apply Integrable.mono' hg
    (measurable_suzukiPsiLandauDensity r).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := ht.le
  have hM : 0 ≤ M := by
    dsimp only [M]
    exact tsum_nonneg fun _ => by positivity
  unfold suzukiPsiLandauDensity
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-r * t) * |(xiScrewDivisor t).re| ≤
        Real.exp (-r * t) * ‖xiScrewDivisor t‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (Real.exp_pos _).le
    _ ≤ Real.exp (-r * t) *
        ((Real.exp (|t| / 2) + 1) * M) :=
      mul_le_mul_of_nonneg_left (norm_xiScrewDivisor_le t) (Real.exp_pos _).le
    _ = g t := by
      rw [abs_of_nonneg ht0]
      dsimp only [g, M]
      rw [show (-r + 1 / 2) * t = -r * t + t / 2 by ring,
        Real.exp_add]
      ring

/-- Positive measure used in Suzuki's Widder--Landau argument. -/
def suzukiPsiLandauMeasure (r : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun t => ENNReal.ofReal (suzukiPsiLandauDensity r t))

/-- Exponential integrability of Suzuki's positive carrier above an abscissa. -/
def SuzukiPsiMomentsAbove (b : ℝ) : Prop :=
  ∀ r : ℝ, b < r → IntegrableOn (suzukiPsiLandauDensity r) (Ioi 0)

theorem suzukiPsiMomentsAbove_one_half : SuzukiPsiMomentsAbove (1 / 2) := by
  intro r hr
  exact integrableOn_suzukiPsiLandauDensity hr

private theorem integrable_exp_mul_id_suzukiMeasure_of_momentsAbove
    (hsource : SuzukiPsiPointwiseNonnegative)
    {b r rho : ℝ} (hMom : SuzukiPsiMomentsAbove b)
    (hr : b < r - rho) :
    Integrable (fun t : ℝ => Real.exp (rho * id t))
      (suzukiPsiLandauMeasure r) := by
  have hdens := hMom (r - rho) hr
  have hmeas : AEMeasurable
      (fun t => ENNReal.ofReal (suzukiPsiLandauDensity r t))
      (volume.restrict (Ioi 0)) :=
    (measurable_suzukiPsiLandauDensity r).ennreal_ofReal.aemeasurable.restrict
  have hnonneg := suzukiPsiLandauDensity_nonneg_ae hsource r
  rw [suzukiPsiLandauMeasure,
    integrable_withDensity_iff_integrable_smul₀' hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply hdens.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with t ht hden
  rw [ENNReal.toReal_ofReal hden]
  simp only [id_eq, smul_eq_mul]
  unfold suzukiPsiLandauDensity
  rw [show -(r - rho) * t = -r * t + rho * t by ring, Real.exp_add]
  ring

private theorem zero_mem_interior_integrableExpSet_suzukiMeasure
    (hsource : SuzukiPsiPointwiseNonnegative)
    {b r : ℝ} (hMom : SuzukiPsiMomentsAbove b) (hr : b < r) :
    0 ∈ interior (integrableExpSet id (suzukiPsiLandauMeasure r)) := by
  let delta : ℝ := (r - b) / 2
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset
    (Ioo_mem_nhds (a := -delta) (b := delta) (by linarith) (by linarith)) ?_
  intro rho hrho
  exact integrable_exp_mul_id_suzukiMeasure_of_momentsAbove hsource hMom (by
    dsimp only [delta] at hrho
    linarith [hrho.2])

theorem complexMGF_id_suzukiPsiLandauMeasure_eq_laplace
    (hsource : SuzukiPsiPointwiseNonnegative) (r : ℝ) (z : ℂ) :
    complexMGF id (suzukiPsiLandauMeasure r) z =
      suzukiPsiLaplace ((r : ℂ) - z) := by
  have hmeas : AEMeasurable
      (fun t => ENNReal.ofReal (suzukiPsiLandauDensity r t))
      (volume.restrict (Ioi 0)) :=
    (measurable_suzukiPsiLandauDensity r).ennreal_ofReal.aemeasurable.restrict
  have hnonneg := suzukiPsiLandauDensity_nonneg_ae hsource r
  rw [complexMGF, suzukiPsiLandauMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold suzukiPsiLaplace
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with t ht hden
  rw [ENNReal.toReal_ofReal hden, Complex.real_smul]
  simp only [id_eq]
  unfold suzukiPsiLandauDensity
  rw [← suzukiPsi_eq_xiScrewDivisor_re ht.le]
  push_cast
  rw [show
      Complex.exp (-(r : ℂ) * (t : ℂ)) * (suzukiPsi t : ℂ) *
          Complex.exp (z * (t : ℂ)) =
        (Complex.exp (-(r : ℂ) * (t : ℂ)) *
          Complex.exp (z * (t : ℂ))) * (suzukiPsi t : ℂ) by ring]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem analyticOnNhd_suzukiPsiLaplace_of_momentsAbove
    (hsource : SuzukiPsiPointwiseNonnegative)
    {b : ℝ} (hMom : SuzukiPsiMomentsAbove b) :
    AnalyticOnNhd ℂ suzukiPsiLaplace {s : ℂ | b < s.re} := by
  intro s hs
  let r : ℝ := s.re
  let z : ℂ := (r : ℂ) - s
  have hzero := zero_mem_interior_integrableExpSet_suzukiMeasure
    hsource hMom (show b < r from hs)
  have hzre : z.re = 0 := by dsimp only [z, r]; simp
  have hmgf : AnalyticAt ℂ
      (complexMGF id (suzukiPsiLandauMeasure r)) z :=
    analyticAt_complexMGF (by simpa only [hzre] using hzero)
  have hmgf' : AnalyticAt ℂ
      (complexMGF id (suzukiPsiLandauMeasure r)) ((r : ℂ) - s) := by
    simpa only [z] using hmgf
  have haffine : AnalyticAt ℂ (fun w : ℂ => (r : ℂ) - w) s := by fun_prop
  have hcomp := hmgf'.comp haffine
  have heq : (fun w : ℂ =>
      complexMGF id (suzukiPsiLandauMeasure r) ((r : ℂ) - w)) =
      suzukiPsiLaplace := by
    funext w
    exact complexMGF_id_suzukiPsiLandauMeasure_eq_laplace
      hsource r ((r : ℂ) - w) |>.trans (by congr 1; ring)
  rw [← heq]
  exact hcomp

theorem analyticOnNhd_suzukiPsiLaplaceContinuation_strip
    {b : ℝ} (hb : 0 < b) :
    AnalyticOnNhd ℂ suzukiPsiLaplaceContinuation
      (ccmFirstClockLandauStrip b) := by
  intro s hs
  have hsre : 0 < s.re := hb.trans hs.1
  have hsball : s ∈ Metric.ball (s.re : ℂ) (s.re / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : s - (s.re : ℂ) = (s.im : ℂ) * I := by
      apply Complex.ext <;> simp [mul_re, mul_im]
    rw [heq, norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one]
    exact lt_trans hs.2 (by nlinarith [hs.1, hb])
  exact (differentiableOn_suzukiPsiLaplaceContinuation_ball hsre).analyticAt
    (Metric.isOpen_ball.mem_nhds hsball)

theorem suzukiPsiLaplace_eq_continuation_of_momentsAbove
    (hsource : SuzukiPsiPointwiseNonnegative)
    {b : ℝ} (hb : 0 < b) (hbHalf : b ≤ 1 / 2)
    (hMom : SuzukiPsiMomentsAbove b) :
    Set.EqOn suzukiPsiLaplace suzukiPsiLaplaceContinuation
      (ccmFirstClockLandauStrip b) := by
  have hleft := analyticOnNhd_suzukiPsiLaplace_of_momentsAbove hsource hMom
  have hleftStrip : AnalyticOnNhd ℂ suzukiPsiLaplace
      (ccmFirstClockLandauStrip b) := fun s hs => hleft s hs.1
  have hright := analyticOnNhd_suzukiPsiLaplaceContinuation_strip hb
  have hone : (1 : ℂ) ∈ ccmFirstClockLandauStrip b := by
    constructor
    · change b < 1
      linarith
    · simp
      positivity
  have hevent : suzukiPsiLaplace =ᶠ[𝓝 (1 : ℂ)]
      suzukiPsiLaplaceContinuation := by
    have hopen : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hopen] with s hs
    exact suzukiPsiLaplace_eq_continuation hs
  exact hleftStrip.eqOn_of_preconnected_of_eventuallyEq hright
    isPreconnected_ccmFirstClockLandauStrip hone hevent

/-- Translation of Suzuki's rational continuation to a Landau MGF center. -/
def suzukiPsiLandauContinuation (r : ℝ) (z : ℂ) : ℂ :=
  suzukiPsiLaplaceContinuation ((r : ℂ) - z)

theorem differentiableOn_suzukiPsiLandauContinuation_closedBall
    {r : ℝ} (hr : 0 < r) {R : NNReal} (hR : (R : ℝ) < r / 2) :
    DifferentiableOn ℂ (suzukiPsiLandauContinuation r)
      (Metric.closedBall 0 (R : ℝ)) := by
  intro z hz
  have hzNorm : ‖z‖ ≤ (R : ℝ) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hsball : (r : ℂ) - z ∈ Metric.ball (r : ℂ) (r / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : (r : ℂ) - z - (r : ℂ) = -z := by ring
    rw [heq, norm_neg]
    exact lt_of_le_of_lt hzNorm hR
  have hbase := (differentiableOn_suzukiPsiLaplaceContinuation_ball hr
    ((r : ℂ) - z) hsball).differentiableAt
      (Metric.isOpen_ball.mem_nhds hsball)
  have haffine : DifferentiableAt ℂ (fun w : ℂ => (r : ℂ) - w) z := by fun_prop
  exact (hbase.comp z haffine).differentiableWithinAt

private theorem suzukiLandauContinuation_eventuallyEq_complexMGF
    (hsource : SuzukiPsiPointwiseNonnegative)
    {b : ℝ} (hb : 0 < b) (hbHalf : b ≤ 1 / 2)
    (hMom : SuzukiPsiMomentsAbove b) {r : ℝ} (hr : b < r) :
    suzukiPsiLandauContinuation r =ᶠ[𝓝 0]
      complexMGF id (suzukiPsiLandauMeasure r) := by
  have heq := suzukiPsiLaplace_eq_continuation_of_momentsAbove
    hsource hb hbHalf hMom
  have hopen : {z : ℂ | z.re < r - b ∧ |z.im| < b / 4} ∈ 𝓝 (0 : ℂ) := by
    have hOpen : IsOpen {z : ℂ | z.re < r - b ∧ |z.im| < b / 4} :=
      (isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt Complex.continuous_im.abs continuous_const)
    exact hOpen.mem_nhds (by
      constructor
      · simpa using sub_pos.mpr hr
      · simpa using div_pos hb (by norm_num : (0 : ℝ) < 4))
  filter_upwards [hopen] with z hz
  have hsStrip : (r : ℂ) - z ∈ ccmFirstClockLandauStrip b := by
    constructor
    · simp only [sub_re, ofReal_re]
      linarith [hz.1]
    · simp only [sub_im, ofReal_im, zero_sub, abs_neg]
      exact hz.2
  calc
    suzukiPsiLandauContinuation r z =
        suzukiPsiLaplaceContinuation ((r : ℂ) - z) := rfl
    _ = suzukiPsiLaplace ((r : ℂ) - z) := (heq hsStrip).symm
    _ = complexMGF id (suzukiPsiLandauMeasure r) z :=
      (complexMGF_id_suzukiPsiLandauMeasure_eq_laplace hsource r z).symm

private theorem suzuki_landau_integrable_transfer
    (hsource : SuzukiPsiPointwiseNonnegative)
    {b : ℝ} (hb : 0 < b) (hbHalf : b ≤ 1 / 2)
    (hMom : SuzukiPsiMomentsAbove b)
    {r : ℝ} (hr : b < r) {R : NNReal} (hR : (R : ℝ) < r / 2)
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrhoR : rho < (R : ℝ)) :
    Integrable (fun t : ℝ => Real.exp (rho * id t))
      (suzukiPsiLandauMeasure r) := by
  exact landau_complexMGF_integrable_transfer
    (by
      have hmeas : AEMeasurable
          (fun t => ENNReal.ofReal (suzukiPsiLandauDensity r t))
          (volume.restrict (Ioi 0)) :=
        (measurable_suzukiPsiLandauDensity r).ennreal_ofReal.aemeasurable.restrict
      rw [suzukiPsiLandauMeasure, ae_withDensity_iff' hmeas]
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro _hdens
      exact ht.le)
    (zero_mem_interior_integrableExpSet_suzukiMeasure hsource hMom hr)
    (differentiableOn_suzukiPsiLandauContinuation_closedBall (hb.trans hr) hR)
    (suzukiLandauContinuation_eventuallyEq_complexMGF
      hsource hb hbHalf hMom hr)
    hrho0 hrhoR

private theorem integrableOn_suzukiDensity_sub_of_transfer
    (hsource : SuzukiPsiPointwiseNonnegative)
    {r rho : ℝ}
    (htransfer : Integrable (fun t : ℝ => Real.exp (rho * id t))
      (suzukiPsiLandauMeasure r)) :
    IntegrableOn (suzukiPsiLandauDensity (r - rho)) (Ioi 0) := by
  have hmeas : AEMeasurable
      (fun t => ENNReal.ofReal (suzukiPsiLandauDensity r t))
      (volume.restrict (Ioi 0)) :=
    (measurable_suzukiPsiLandauDensity r).ennreal_ofReal.aemeasurable.restrict
  have hnonneg := suzukiPsiLandauDensity_nonneg_ae hsource r
  rw [suzukiPsiLandauMeasure,
    integrable_withDensity_iff_integrable_smul₀' hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at htransfer
  apply htransfer.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with t ht hden
  rw [ENNReal.toReal_ofReal hden]
  simp only [id_eq, smul_eq_mul]
  unfold suzukiPsiLandauDensity
  rw [show -(r - rho) * t = -r * t + rho * t by ring, Real.exp_add]
  ring

/-- One Widder--Landau halving step for Suzuki's literal nonnegative function. -/
theorem suzukiPsiMomentsAbove_half
    (hsource : SuzukiPsiPointwiseNonnegative)
    {b : ℝ} (hb : 0 < b) (hbHalf : b ≤ 1 / 2)
    (hMom : SuzukiPsiMomentsAbove b) :
    SuzukiPsiMomentsAbove (b / 2) := by
  intro a ha
  let r : ℝ := a + b / 2
  let rho : ℝ := b / 2
  let Rreal : ℝ := (rho + r / 2) / 2
  have hr : b < r := by dsimp only [r]; linarith
  have hrho0 : 0 ≤ rho := by dsimp only [rho]; linarith
  have hR0 : 0 ≤ Rreal := by
    dsimp only [Rreal, rho, r]
    linarith [hb, ha]
  let R : NNReal := ⟨Rreal, hR0⟩
  have hrhoR : rho < (R : ℝ) := by
    change rho < Rreal
    dsimp only [Rreal, rho, r]
    linarith
  have hRhalf : (R : ℝ) < r / 2 := by
    change Rreal < r / 2
    have hrhoHalf : rho < r / 2 := by
      dsimp only [rho, r]
      linarith [ha]
    dsimp only [Rreal]
    linarith
  have htransfer := suzuki_landau_integrable_transfer
    hsource hb hbHalf hMom hr hRhalf hrho0 hrhoR
  have hsub := integrableOn_suzukiDensity_sub_of_transfer hsource htransfer
  have hra : r - rho = a := by dsimp only [r, rho]; ring
  simpa only [hra] using hsub

theorem suzukiPsiMomentsAbove_dyadic
    (hsource : SuzukiPsiPointwiseNonnegative) :
    ∀ n : ℕ, SuzukiPsiMomentsAbove (ccmFirstClockDyadicThreshold n) := by
  intro n
  induction n with
  | zero =>
      simpa [ccmFirstClockDyadicThreshold] using suzukiPsiMomentsAbove_one_half
  | succ n ih =>
      rw [ccmFirstClockDyadicThreshold_succ]
      exact suzukiPsiMomentsAbove_half hsource
        (ccmFirstClockDyadicThreshold_pos n)
        (ccmFirstClockDyadicThreshold_le_one_half n) ih

/-- Suzuki's nonnegative carrier has every positive Laplace moment. -/
theorem suzukiPsiMomentsAbove_zero
    (hsource : SuzukiPsiPointwiseNonnegative) :
    SuzukiPsiMomentsAbove 0 := by
  intro a ha
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < a :=
    exists_pow_lt_of_lt_one ha (by norm_num)
  have hthreshold : ccmFirstClockDyadicThreshold n < a := by
    unfold ccmFirstClockDyadicThreshold
    rw [pow_succ]
    have hpowpos : 0 < (1 / 2 : ℝ) ^ n := by positivity
    nlinarith
  exact suzukiPsiMomentsAbove_dyadic hsource n a hthreshold

theorem ccmXiScrewAllExponentialMoments_of_suzukiPsi_nonnegative
    (hsource : SuzukiPsiPointwiseNonnegative) :
    CCMXiScrewAllExponentialMoments := by
  intro a ha
  have hreal := suzukiPsiMomentsAbove_zero hsource a ha
  have hcast : IntegrableOn (fun t : ℝ =>
      (suzukiPsiLandauDensity a t : ℂ)) (Ioi 0) := hreal.ofReal
  apply hcast.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  unfold suzukiPsiLandauDensity
  rw [← suzukiPsi_eq_xiScrewDivisor_re ht.le,
    ← ofReal_suzukiPsi_eq_xiScrewDivisor ht.le]
  rw [show -(a : ℂ) * (t : ℂ) = ((-a * t : ℝ) : ℂ) by push_cast; ring]
  simp

/-- Pointwise nonnegativity of Suzuki's literal `Psi` forces RH. -/
theorem riemannHypothesis_of_suzukiPsiPointwiseNonnegative
    (hsource : SuzukiPsiPointwiseNonnegative) :
    RiemannHypothesis :=
  riemannHypothesis_of_ccmXiScrew_all_exponential_moments
    (ccmXiScrewAllExponentialMoments_of_suzukiPsi_nonnegative hsource)

/-- RH makes every term of Suzuki's exact real zero series nonnegative. -/
theorem suzukiPsiPointwiseNonnegative_of_riemannHypothesis
    (hRH : RiemannHypothesis) : SuzukiPsiPointwiseNonnegative := by
  intro t ht
  rw [suzukiPsi_eq_xiScrewDivisor_re ht,
    xiScrewDivisor_re_eq_xiCriticalScrewSeries_of_rh hRH]
  exact screwSeries_nonneg xiCriticalScrewWeight_nonneg t

/-- **Suzuki 2022, Theorem 1.7 (non-strict equivalence).**  RH is equivalent to pointwise
nonnegativity of the paper's displayed function `Psi` on its source half-line. -/
theorem riemannHypothesis_iff_suzukiPsiPointwiseNonnegative :
    RiemannHypothesis ↔ SuzukiPsiPointwiseNonnegative :=
  ⟨suzukiPsiPointwiseNonnegative_of_riemannHypothesis,
    riemannHypothesis_of_suzukiPsiPointwiseNonnegative⟩

end

end RHTower
