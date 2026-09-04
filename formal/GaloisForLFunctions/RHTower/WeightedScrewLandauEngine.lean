import GaloisForLFunctions.RHTower.SuzukiWeightedScrewTwoBumpLimit
import GaloisForLFunctions.RHTower.SuzukiScrewPointwiseNonnegativityCriterion
import GaloisForLFunctions.RHTower.LandauIntegralTransfer

/-!
# The weighted Widder–Landau engine

Suzuki's pointwise criterion module turns nonnegativity of the screw function `Ψ` into all positive
exponential moments of the Xi screw divisor, through Widder–Landau halving of the abscissa of
convergence.  This module repeats the argument for a **weighted** screw divisor
`Φ_W(t) = Σ'_q W_q (1 − cos(γ_q t))/γ_q²` with bounded weights `W`, assuming only that `Φ_W` is
real-valued and nonnegative on the source half-line.  The rational continuation is the weighted
atom series `Σ'_q W_q /(s (s² + γ_q²))`; nothing about the logarithmic derivative of `Xi` is used.

Main results: `weightedScrewMomentsAbove_zero` (all positive exponential moments),
`analyticOnNhd_weightedScrewLaplace_rightHalf` (the Laplace transform is analytic on `Re s > 0`), and
`weightedScrewLaplace_eq_continuation` (Laplace transform = weighted atom series on `Re s > 1/2`).
-/

open Complex MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

variable (W : XiZeroCopy → ℂ)

/-! ## Measurability and growth -/

theorem measurable_weightedXiScrewDivisor : Measurable (weightedXiScrewDivisor W) := by
  unfold weightedXiScrewDivisor
  exact Measurable.tsum fun q => by
    unfold xiScrewDivisorTerm
    fun_prop

/-- The inverse-square mass of the Xi divisor. -/
def xiInvSqMass : ℝ := ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2

theorem xiInvSqMass_nonneg : 0 ≤ xiInvSqMass :=
  tsum_nonneg fun _ => by positivity

theorem norm_weightedXiScrewDivisor_le {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C) (t : ℝ) :
    ‖weightedXiScrewDivisor W t‖ ≤ C * (Real.exp (|t| / 2) + 1) * xiInvSqMass := by
  unfold weightedXiScrewDivisor xiInvSqMass
  have hsum := summable_weighted_xiScrewDivisorTerm hW t
  calc ‖∑' q : XiZeroCopy, W q * xiScrewDivisorTerm t q‖
      ≤ ∑' q : XiZeroCopy, ‖W q * xiScrewDivisorTerm t q‖ := norm_tsum_le_tsum_norm hsum.norm
    _ ≤ ∑' q : XiZeroCopy, C * (Real.exp (|t| / 2) + 1) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        refine hsum.norm.tsum_le_tsum (fun q => ?_) (xiSpectralPoint_inv_sq_summable.mul_left _)
        rw [norm_mul]
        calc ‖W q‖ * ‖xiScrewDivisorTerm t q‖
            ≤ C * ((Real.exp (|t| / 2) + 1) / ‖xiSpectralPoint q‖ ^ 2) :=
              mul_le_mul (hW q) (norm_xiScrewDivisorTerm_le t q) (norm_nonneg _) hC
          _ = C * (Real.exp (|t| / 2) + 1) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring
    _ = C * (Real.exp (|t| / 2) + 1) * ∑' q : XiZeroCopy, 1 / ‖xiSpectralPoint q‖ ^ 2 := by
        rw [tsum_mul_left]

/-! ## The Landau density and measure -/

/-- `e^{−rt} · Re Φ_W(t)`. -/
def weightedScrewLandauDensity (r t : ℝ) : ℝ :=
  Real.exp (-r * t) * (weightedXiScrewDivisor W t).re

theorem measurable_weightedScrewLandauDensity (r : ℝ) : Measurable (weightedScrewLandauDensity W r) := by
  unfold weightedScrewLandauDensity
  exact (by fun_prop : Measurable (fun t : ℝ => Real.exp (-r * t))).mul
    (measurable_weightedXiScrewDivisor W).re

theorem weightedScrewLandauDensity_nonneg_ae
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ (weightedXiScrewDivisor W t).re) (r : ℝ) :
    ∀ᵐ t ∂volume.restrict (Ioi 0), 0 ≤ weightedScrewLandauDensity W r t := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact mul_nonneg (Real.exp_pos _).le (hpos t ht.le)

theorem integrableOn_weightedScrewLandauDensity {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    {r : ℝ} (hr : 1 / 2 < r) :
    IntegrableOn (weightedScrewLandauDensity W r) (Ioi 0) := by
  let M : ℝ := C * xiInvSqMass
  let g : ℝ → ℝ := fun t =>
    (Real.exp ((-r + 1 / 2) * t) + Real.exp (-r * t)) * M
  have hdecay1 : -r + 1 / 2 < 0 := by linarith
  have hdecay2 : -r < 0 := by linarith
  have hg : IntegrableOn g (Ioi 0) :=
    ((integrableOn_exp_mul_Ioi hdecay1 0).add
      (integrableOn_exp_mul_Ioi hdecay2 0)).mul_const M
  apply Integrable.mono' hg
    (measurable_weightedScrewLandauDensity W r).aestronglyMeasurable.restrict
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := ht.le
  unfold weightedScrewLandauDensity
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp (-r * t) * |(weightedXiScrewDivisor W t).re| ≤
        Real.exp (-r * t) * ‖weightedXiScrewDivisor W t‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (Real.exp_pos _).le
    _ ≤ Real.exp (-r * t) * (C * (Real.exp (|t| / 2) + 1) * xiInvSqMass) :=
      mul_le_mul_of_nonneg_left (norm_weightedXiScrewDivisor_le W hC hW t) (Real.exp_pos _).le
    _ = g t := by
      rw [abs_of_nonneg ht0]
      dsimp only [g, M]
      rw [show (-r + 1 / 2) * t = -r * t + t / 2 by ring, Real.exp_add]
      ring

/-- The positive Landau measure. -/
def weightedScrewLandauMeasure (r : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi 0)).withDensity
    (fun t => ENNReal.ofReal (weightedScrewLandauDensity W r t))

/-- Exponential integrability above an abscissa. -/
def WeightedScrewMomentsAbove (b : ℝ) : Prop :=
  ∀ r : ℝ, b < r → IntegrableOn (weightedScrewLandauDensity W r) (Ioi 0)

theorem weightedScrewMomentsAbove_one_half {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C) :
    WeightedScrewMomentsAbove W (1 / 2) := by
  intro r hr
  exact integrableOn_weightedScrewLandauDensity W hC hW hr

theorem integrable_exp_mul_id_weightedScrewMeasure_of_momentsAbove
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ (weightedXiScrewDivisor W t).re)
    {b r rho : ℝ} (hMom : WeightedScrewMomentsAbove W b) (hr : b < r - rho) :
    Integrable (fun t : ℝ => Real.exp (rho * id t)) (weightedScrewLandauMeasure W r) := by
  have hdens := hMom (r - rho) hr
  have hmeas : AEMeasurable
      (fun t => ENNReal.ofReal (weightedScrewLandauDensity W r t))
      (volume.restrict (Ioi 0)) :=
    (measurable_weightedScrewLandauDensity W r).ennreal_ofReal.aemeasurable.restrict
  have hnonneg := weightedScrewLandauDensity_nonneg_ae W hpos r
  rw [weightedScrewLandauMeasure,
    integrable_withDensity_iff_integrable_smul₀' hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply hdens.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with t ht hden
  rw [ENNReal.toReal_ofReal hden]
  simp only [id_eq, smul_eq_mul]
  unfold weightedScrewLandauDensity
  rw [show -(r - rho) * t = -r * t + rho * t by ring, Real.exp_add]
  ring

theorem zero_mem_interior_integrableExpSet_weightedScrewMeasure
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ (weightedXiScrewDivisor W t).re)
    {b r : ℝ} (hMom : WeightedScrewMomentsAbove W b) (hr : b < r) :
    0 ∈ interior (integrableExpSet id (weightedScrewLandauMeasure W r)) := by
  let delta : ℝ := (r - b) / 2
  have hdelta : 0 < delta := by dsimp only [delta]; linarith
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset
    (Ioo_mem_nhds (a := -delta) (b := delta) (by linarith) (by linarith)) ?_
  intro rho hrho
  exact integrable_exp_mul_id_weightedScrewMeasure_of_momentsAbove W hpos hMom (by
    dsimp only [delta] at hrho
    linarith [hrho.2])

/-! ## The Laplace transform and its rational continuation -/

/-- `∫₀^∞ e^{−st} Φ_W(t) dt`. -/
def weightedScrewLaplace (s : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 0, Complex.exp (-s * (t : ℂ)) * weightedXiScrewDivisor W t

/-- The weighted atom series `Σ'_q W_q / (s (s² + γ_q²))`. -/
def weightedScrewLaplaceContinuation (s : ℂ) : ℂ :=
  ∑' q : XiZeroCopy, W q * suzukiPsiLaplaceAtom s (xiSpectralPoint q)

theorem complexMGF_id_weightedScrewLandauMeasure_eq_laplace
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) (r : ℝ) (z : ℂ) :
    complexMGF id (weightedScrewLandauMeasure W r) z = weightedScrewLaplace W ((r : ℂ) - z) := by
  have hmeas : AEMeasurable
      (fun t => ENNReal.ofReal (weightedScrewLandauDensity W r t))
      (volume.restrict (Ioi 0)) :=
    (measurable_weightedScrewLandauDensity W r).ennreal_ofReal.aemeasurable.restrict
  have hnonneg := weightedScrewLandauDensity_nonneg_ae W hpos r
  rw [complexMGF, weightedScrewLandauMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold weightedScrewLaplace
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with t _ hden
  rw [ENNReal.toReal_ofReal hden, Complex.real_smul]
  simp only [id_eq]
  unfold weightedScrewLandauDensity
  have hcast : ((weightedXiScrewDivisor W t).re : ℂ) = weightedXiScrewDivisor W t := by
    apply Complex.ext
    · simp
    · simp [hreal t]
  push_cast
  rw [hcast]
  rw [show Complex.exp (-(r : ℂ) * (t : ℂ)) * weightedXiScrewDivisor W t *
      Complex.exp (z * (t : ℂ)) =
      (Complex.exp (-(r : ℂ) * (t : ℂ)) * Complex.exp (z * (t : ℂ))) *
        weightedXiScrewDivisor W t by ring]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem analyticOnNhd_weightedScrewLaplace_of_momentsAbove
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0)
    {b : ℝ} (hMom : WeightedScrewMomentsAbove W b) :
    AnalyticOnNhd ℂ (weightedScrewLaplace W) {s : ℂ | b < s.re} := by
  intro s hs
  let r : ℝ := s.re
  let z : ℂ := (r : ℂ) - s
  have hzero := zero_mem_interior_integrableExpSet_weightedScrewMeasure W hpos hMom
    (show b < r from hs)
  have hzre : z.re = 0 := by dsimp only [z, r]; simp
  have hmgf : AnalyticAt ℂ (complexMGF id (weightedScrewLandauMeasure W r)) z :=
    analyticAt_complexMGF (by simpa only [hzre] using hzero)
  have hmgf' : AnalyticAt ℂ (complexMGF id (weightedScrewLandauMeasure W r)) ((r : ℂ) - s) := by
    simpa only [z] using hmgf
  have haffine : AnalyticAt ℂ (fun w : ℂ => (r : ℂ) - w) s := by fun_prop
  have hcomp := hmgf'.comp haffine
  have heq : (fun w : ℂ => complexMGF id (weightedScrewLandauMeasure W r) ((r : ℂ) - w)) =
      weightedScrewLaplace W := by
    funext w
    exact complexMGF_id_weightedScrewLandauMeasure_eq_laplace W hpos hreal r ((r : ℂ) - w) |>.trans
      (by congr 1; ring)
  rw [← heq]
  exact hcomp

theorem norm_weighted_atom_le_ball {C : ℝ} (hW : ∀ q, ‖W q‖ ≤ C) {r : ℝ} (hr : 0 < r) {s : ℂ}
    (hs : s ∈ Metric.ball (r : ℂ) (r / 2)) (q : XiZeroCopy) :
    ‖W q * suzukiPsiLaplaceAtom s (xiSpectralPoint q)‖ ≤
      C * (602 / r) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
  rw [norm_mul]
  have hC : 0 ≤ C := (norm_nonneg _).trans (hW q)
  calc ‖W q‖ * ‖suzukiPsiLaplaceAtom s (xiSpectralPoint q)‖
      ≤ C * ((602 / r) * (1 / ‖xiSpectralPoint q‖ ^ 2)) :=
        mul_le_mul (hW q) (norm_suzukiPsiLaplaceAtom_le_ball hr hs q) (norm_nonneg _) hC
    _ = C * (602 / r) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by ring

theorem differentiableOn_weightedScrewLaplaceContinuation_ball {C : ℝ} (hW : ∀ q, ‖W q‖ ≤ C)
    {r : ℝ} (hr : 0 < r) :
    DifferentiableOn ℂ (weightedScrewLaplaceContinuation W) (Metric.ball (r : ℂ) (r / 2)) := by
  unfold weightedScrewLaplaceContinuation
  apply Complex.differentiableOn_tsum_of_summable_norm
    (u := fun q : XiZeroCopy => C * (602 / r) * (1 / ‖xiSpectralPoint q‖ ^ 2))
  · exact xiSpectralPoint_inv_sq_summable.mul_left _
  · intro q
    exact (differentiableOn_suzukiPsiLaplaceAtom_ball hr q).const_mul _
  · exact Metric.isOpen_ball
  · intro q s hs
    exact norm_weighted_atom_le_ball W hW hr hs q

/-- **Termwise Laplace transform** on the absolute-convergence half-plane. -/
theorem weightedScrewLaplace_eq_continuation {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C) {s : ℂ}
    (hsHalf : 1 / 2 < s.re) :
    weightedScrewLaplace W s = weightedScrewLaplaceContinuation W s := by
  let F : XiZeroCopy → ℝ → ℂ := fun q L =>
    Complex.exp (-s * (L : ℂ)) * (W q * ccmFirstClockScrewKernel L (xiSpectralPoint q))
  let g : ℝ → ℝ := fun L =>
    Real.exp ((-s.re + 1 / 2) * L) + Real.exp ((-s.re) * L)
  have hdecay1 : -s.re + 1 / 2 < 0 := by linarith
  have hdecay2 : -s.re < 0 := by linarith
  have hgint : IntegrableOn g (Ioi 0) :=
    (integrableOn_exp_mul_Ioi hdecay1 0).add (integrableOn_exp_mul_Ioi hdecay2 0)
  have hzstrip : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| < 1 / 2 := fun q => by
    rw [abs_lt]
    constructor <;> linarith [xiSpectralPoint_im_mem_openHalf q]
  have hFint : ∀ q : XiZeroCopy, IntegrableOn (F q) (Ioi 0) := by
    intro q
    have h : IntegrableOn (fun L : ℝ =>
        W q * (Complex.exp (-s * (L : ℂ)) * ccmFirstClockScrewKernel L (xiSpectralPoint q)))
        (Ioi 0) :=
      (integrableOn_exp_mul_ccmFirstClockScrewKernel
        (xiSpectralPoint_ne_zero q) (hzstrip q) hsHalf).const_mul (W q)
    refine h.congr_fun (fun L _ => ?_) measurableSet_Ioi
    dsimp only [F]
    ring
  have hpointBound (q : XiZeroCopy) (L : ℝ) (hL : L ∈ Ioi (0 : ℝ)) :
      ‖F q L‖ ≤ (C * g L) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
    have hLpos : 0 < L := hL
    have hterm := norm_xiScrewDivisorTerm_le L q
    rw [abs_of_pos hLpos] at hterm
    dsimp only [F]
    rw [← xiScrewDivisorTerm_eq_ccmFirstClockScrewKernel, norm_mul, norm_mul, Complex.norm_exp]
    have hexpRe : (-s * (L : ℂ)).re = -s.re * L := by simp [mul_re]
    rw [hexpRe]
    calc
      Real.exp (-s.re * L) * (‖W q‖ * ‖xiScrewDivisorTerm L q‖) ≤
          Real.exp (-s.re * L) * (C * ((Real.exp (L / 2) + 1) / ‖xiSpectralPoint q‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul (hW q) hterm (norm_nonneg _) hC) (Real.exp_pos _).le
      _ = (C * g L) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        dsimp only [g]
        rw [show (-s.re + 1 / 2) * L = -s.re * L + L / 2 by ring, Real.exp_add]
        ring
  have hnormSummable : Summable (fun q : XiZeroCopy => ∫ L : ℝ in Ioi 0, ‖F q L‖) := by
    apply Summable.of_nonneg_of_le
      (fun q => integral_nonneg fun _ => norm_nonneg _)
      (fun q => ?_)
      (xiSpectralPoint_inv_sq_summable.mul_left (∫ L : ℝ in Ioi 0, C * g L))
    have hmajorInt : IntegrableOn
        (fun L : ℝ => (C * g L) * (1 / ‖xiSpectralPoint q‖ ^ 2)) (Ioi 0) :=
      (hgint.const_mul C).mul_const _
    calc
      (∫ L : ℝ in Ioi 0, ‖F q L‖) ≤
          ∫ L : ℝ in Ioi 0, (C * g L) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        apply integral_mono_ae (hFint q).norm hmajorInt
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
        exact hpointBound q L hL
      _ = (∫ L : ℝ in Ioi 0, C * g L) * (1 / ‖xiSpectralPoint q‖ ^ 2) := by
        rw [integral_mul_const]
  have hswap : (∫ L : ℝ in Ioi 0, ∑' q : XiZeroCopy, F q L) =
      ∑' q : XiZeroCopy, ∫ L : ℝ in Ioi 0, F q L :=
    (MeasureTheory.integral_tsum_of_summable_integral_norm hFint hnormSummable).symm
  have hpoint (L : ℝ) : (∑' q : XiZeroCopy, F q L) =
      Complex.exp (-s * (L : ℂ)) * weightedXiScrewDivisor W L := by
    rw [weightedXiScrewDivisor, ← tsum_mul_left]
    apply tsum_congr
    intro q
    dsimp only [F]
    rw [xiScrewDivisorTerm_eq_ccmFirstClockScrewKernel]
  calc
    weightedScrewLaplace W s = ∫ L : ℝ in Ioi 0, ∑' q : XiZeroCopy, F q L := by
      unfold weightedScrewLaplace
      apply integral_congr_ae
      filter_upwards with L
      exact (hpoint L).symm
    _ = ∑' q : XiZeroCopy, ∫ L : ℝ in Ioi 0, F q L := hswap
    _ = weightedScrewLaplaceContinuation W s := by
      unfold weightedScrewLaplaceContinuation
      apply tsum_congr
      intro q
      have h1 : (fun L : ℝ => F q L) = fun L : ℝ =>
          W q * (Complex.exp (-s * (L : ℂ)) * ccmFirstClockScrewKernel L (xiSpectralPoint q)) := by
        funext L
        dsimp only [F]
        ring
      rw [h1, integral_const_mul, integral_exp_mul_ccmFirstClockScrewKernel
        (xiSpectralPoint_ne_zero q) (hzstrip q) hsHalf]
      rfl

theorem analyticOnNhd_weightedScrewLaplaceContinuation_strip {C : ℝ} (hW : ∀ q, ‖W q‖ ≤ C)
    {b : ℝ} (hb : 0 < b) :
    AnalyticOnNhd ℂ (weightedScrewLaplaceContinuation W) (ccmFirstClockLandauStrip b) := by
  intro s hs
  have hsre : 0 < s.re := hb.trans hs.1
  have hsball : s ∈ Metric.ball (s.re : ℂ) (s.re / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : s - (s.re : ℂ) = (s.im : ℂ) * I := by
      apply Complex.ext <;> simp [mul_re, mul_im]
    rw [heq, norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one]
    exact lt_trans hs.2 (by nlinarith [hs.1, hb])
  exact (differentiableOn_weightedScrewLaplaceContinuation_ball W hW hsre).analyticAt
    (Metric.isOpen_ball.mem_nhds hsball)

theorem weightedScrewLaplace_eq_continuation_of_momentsAbove {C : ℝ} (hC : 0 ≤ C)
    (hW : ∀ q, ‖W q‖ ≤ C)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0)
    {b : ℝ} (hb : 0 < b) (hbHalf : b ≤ 1 / 2) (hMom : WeightedScrewMomentsAbove W b) :
    Set.EqOn (weightedScrewLaplace W) (weightedScrewLaplaceContinuation W) (ccmFirstClockLandauStrip b) := by
  have hleft := analyticOnNhd_weightedScrewLaplace_of_momentsAbove W hpos hreal hMom
  have hleftStrip : AnalyticOnNhd ℂ (weightedScrewLaplace W) (ccmFirstClockLandauStrip b) :=
    fun s hs => hleft s hs.1
  have hright := analyticOnNhd_weightedScrewLaplaceContinuation_strip W hW hb
  have hone : (1 : ℂ) ∈ ccmFirstClockLandauStrip b := by
    constructor
    · change b < 1
      linarith
    · simp
      positivity
  have hevent : weightedScrewLaplace W =ᶠ[𝓝 (1 : ℂ)] weightedScrewLaplaceContinuation W := by
    have hopen : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hopen] with s hs
    exact weightedScrewLaplace_eq_continuation W hC hW hs
  exact hleftStrip.eqOn_of_preconnected_of_eventuallyEq hright
    isPreconnected_ccmFirstClockLandauStrip hone hevent

/-- Translation of the weighted continuation to a Landau MGF center. -/
def weightedScrewLandauContinuation (r : ℝ) (z : ℂ) : ℂ :=
  weightedScrewLaplaceContinuation W ((r : ℂ) - z)

theorem differentiableOn_weightedScrewLandauContinuation_closedBall {C : ℝ} (hW : ∀ q, ‖W q‖ ≤ C)
    {r : ℝ} (hr : 0 < r) {R : NNReal} (hR : (R : ℝ) < r / 2) :
    DifferentiableOn ℂ (weightedScrewLandauContinuation W r) (Metric.closedBall 0 (R : ℝ)) := by
  intro z hz
  have hzNorm : ‖z‖ ≤ (R : ℝ) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  have hsball : (r : ℂ) - z ∈ Metric.ball (r : ℂ) (r / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : (r : ℂ) - z - (r : ℂ) = -z := by ring
    rw [heq, norm_neg]
    exact lt_of_le_of_lt hzNorm hR
  have hbase := (differentiableOn_weightedScrewLaplaceContinuation_ball W hW hr
    ((r : ℂ) - z) hsball).differentiableAt (Metric.isOpen_ball.mem_nhds hsball)
  have haffine : DifferentiableAt ℂ (fun w : ℂ => (r : ℂ) - w) z := by fun_prop
  exact (hbase.comp z haffine).differentiableWithinAt

theorem weightedScrewLandauContinuation_eventuallyEq_complexMGF {C : ℝ} (hC : 0 ≤ C)
    (hW : ∀ q, ‖W q‖ ≤ C)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0)
    {b : ℝ} (hb : 0 < b) (hbHalf : b ≤ 1 / 2) (hMom : WeightedScrewMomentsAbove W b)
    {r : ℝ} (hr : b < r) :
    weightedScrewLandauContinuation W r =ᶠ[𝓝 0] complexMGF id (weightedScrewLandauMeasure W r) := by
  have heq := weightedScrewLaplace_eq_continuation_of_momentsAbove W hC hW hpos hreal hb hbHalf hMom
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
    weightedScrewLandauContinuation W r z = weightedScrewLaplaceContinuation W ((r : ℂ) - z) := rfl
    _ = weightedScrewLaplace W ((r : ℂ) - z) := (heq hsStrip).symm
    _ = complexMGF id (weightedScrewLandauMeasure W r) z :=
      (complexMGF_id_weightedScrewLandauMeasure_eq_laplace W hpos hreal r z).symm

theorem weighted_landau_integrable_transfer {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0)
    {b : ℝ} (hb : 0 < b) (hbHalf : b ≤ 1 / 2) (hMom : WeightedScrewMomentsAbove W b)
    {r : ℝ} (hr : b < r) {R : NNReal} (hR : (R : ℝ) < r / 2)
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrhoR : rho < (R : ℝ)) :
    Integrable (fun t : ℝ => Real.exp (rho * id t)) (weightedScrewLandauMeasure W r) := by
  exact landau_complexMGF_integrable_transfer
    (by
      have hmeas : AEMeasurable
          (fun t => ENNReal.ofReal (weightedScrewLandauDensity W r t))
          (volume.restrict (Ioi 0)) :=
        (measurable_weightedScrewLandauDensity W r).ennreal_ofReal.aemeasurable.restrict
      rw [weightedScrewLandauMeasure, ae_withDensity_iff' hmeas]
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      intro _hdens
      exact ht.le)
    (zero_mem_interior_integrableExpSet_weightedScrewMeasure W hpos hMom hr)
    (differentiableOn_weightedScrewLandauContinuation_closedBall W hW (hb.trans hr) hR)
    (weightedScrewLandauContinuation_eventuallyEq_complexMGF W hC hW hpos hreal hb hbHalf hMom hr)
    hrho0 hrhoR

theorem integrableOn_weightedScrewDensity_sub_of_transfer
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ (weightedXiScrewDivisor W t).re)
    {r rho : ℝ}
    (htransfer : Integrable (fun t : ℝ => Real.exp (rho * id t)) (weightedScrewLandauMeasure W r)) :
    IntegrableOn (weightedScrewLandauDensity W (r - rho)) (Ioi 0) := by
  have hmeas : AEMeasurable
      (fun t => ENNReal.ofReal (weightedScrewLandauDensity W r t))
      (volume.restrict (Ioi 0)) :=
    (measurable_weightedScrewLandauDensity W r).ennreal_ofReal.aemeasurable.restrict
  have hnonneg := weightedScrewLandauDensity_nonneg_ae W hpos r
  rw [weightedScrewLandauMeasure,
    integrable_withDensity_iff_integrable_smul₀' hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at htransfer
  apply htransfer.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with t ht hden
  rw [ENNReal.toReal_ofReal hden]
  simp only [id_eq, smul_eq_mul]
  unfold weightedScrewLandauDensity
  rw [show -(r - rho) * t = -r * t + rho * t by ring, Real.exp_add]
  ring

/-- One Widder–Landau halving step. -/
theorem weightedScrewMomentsAbove_half {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0)
    {b : ℝ} (hb : 0 < b) (hbHalf : b ≤ 1 / 2) (hMom : WeightedScrewMomentsAbove W b) :
    WeightedScrewMomentsAbove W (b / 2) := by
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
  have htransfer := weighted_landau_integrable_transfer W hC hW hpos hreal hb hbHalf hMom hr hRhalf
    hrho0 hrhoR
  have hsub := integrableOn_weightedScrewDensity_sub_of_transfer W hpos htransfer
  have hra : r - rho = a := by dsimp only [r, rho]; ring
  simpa only [hra] using hsub

theorem weightedScrewMomentsAbove_dyadic {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) :
    ∀ n : ℕ, WeightedScrewMomentsAbove W (ccmFirstClockDyadicThreshold n) := by
  intro n
  induction n with
  | zero =>
      simpa [ccmFirstClockDyadicThreshold] using weightedScrewMomentsAbove_one_half W hC hW
  | succ n ih =>
      have hb : 0 < ccmFirstClockDyadicThreshold n := ccmFirstClockDyadicThreshold_pos n
      have hbHalf : ccmFirstClockDyadicThreshold n ≤ 1 / 2 := by
        unfold ccmFirstClockDyadicThreshold
        calc (1 / 2 : ℝ) ^ (n + 1) ≤ (1 / 2) ^ 1 :=
              pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          _ = 1 / 2 := by norm_num
      have hhalf := weightedScrewMomentsAbove_half W hC hW hpos hreal hb hbHalf ih
      have heq : ccmFirstClockDyadicThreshold (n + 1) = ccmFirstClockDyadicThreshold n / 2 := by
        unfold ccmFirstClockDyadicThreshold
        rw [pow_succ]
        ring
      rw [heq]
      exact hhalf

/-- **All positive exponential moments.** -/
theorem weightedScrewMomentsAbove_zero {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) :
    WeightedScrewMomentsAbove W 0 := by
  intro a ha
  obtain ⟨n, hn⟩ : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < a :=
    exists_pow_lt_of_lt_one ha (by norm_num)
  have hthreshold : ccmFirstClockDyadicThreshold n < a := by
    unfold ccmFirstClockDyadicThreshold
    rw [pow_succ]
    have hpowpos : 0 < (1 / 2 : ℝ) ^ n := by positivity
    nlinarith
  exact weightedScrewMomentsAbove_dyadic W hC hW hpos hreal n a hthreshold

/-- **The weighted Laplace transform is analytic on the open right half-plane.** -/
theorem analyticOnNhd_weightedScrewLaplace_rightHalf {C : ℝ} (hC : 0 ≤ C) (hW : ∀ q, ‖W q‖ ≤ C)
    (hpos : ∀ t : ℝ, 0 ≤ t → 0 ≤ (weightedXiScrewDivisor W t).re)
    (hreal : ∀ t : ℝ, (weightedXiScrewDivisor W t).im = 0) :
    AnalyticOnNhd ℂ (weightedScrewLaplace W) {s : ℂ | 0 < s.re} :=
  analyticOnNhd_weightedScrewLaplace_of_momentsAbove W hpos hreal
    (weightedScrewMomentsAbove_zero W hC hW hpos hreal)

end

end RHTower
