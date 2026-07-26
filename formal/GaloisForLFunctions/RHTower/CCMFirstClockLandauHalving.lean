import GaloisForLFunctions.RHTower.CCMFirstClockLandauDescent

open Complex MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

/-- Ordinary Laplace transform of the physical first-clock tail. -/
def ccmFirstClockTailLaplace (s : ℂ) : ℂ :=
  ∫ L : ℝ in Ioi (Real.pi / 2),
    Complex.exp (-s * (L : ℂ)) *
      ccmFirstClockXiRationalDivisor L

/-- Exponential integrability of the positive CCM tail above an abscissa. -/
def CCMFirstClockTailMomentsAbove (b : ℝ) : Prop :=
  ∀ a : ℝ, b < a →
    IntegrableOn (ccmFirstClockLandauDensity a) (Ioi (Real.pi / 2))

theorem ccmFirstClockTailMomentsAbove_one_half :
    CCMFirstClockTailMomentsAbove (1 / 2) := by
  intro a ha
  exact integrableOn_ccmFirstClockLandauDensity ha

private theorem integrable_exp_mul_id_landauMeasure_of_momentsAbove
    (hsource : CCMFirstClockPublishedSourceNonnegative)
    {b r t : ℝ} (hMom : CCMFirstClockTailMomentsAbove b)
    (hrt : b < r - t) :
    Integrable (fun L : ℝ => Real.exp (t * id L))
      (ccmFirstClockLandauMeasure r) := by
  have hdens := hMom (r - t) hrt
  have hmeas : AEMeasurable
      (fun L => ENNReal.ofReal (ccmFirstClockLandauDensity r L))
      (volume.restrict (Ioi (Real.pi / 2))) :=
    (measurable_ccmFirstClockLandauDensity r).ennreal_ofReal
      |>.aemeasurable.restrict
  have hnonneg :=
    ccmFirstClockLandauDensity_nonneg_ae hsource r
  rw [ccmFirstClockLandauMeasure,
    integrable_withDensity_iff_integrable_smul₀' hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply hdens.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with L hL hden
  rw [ENNReal.toReal_ofReal hden]
  simp only [id_eq, smul_eq_mul]
  unfold ccmFirstClockLandauDensity
  rw [show -(r - t) * L = -r * L + t * L by ring, Real.exp_add]
  ring

private theorem zero_mem_interior_integrableExpSet_of_momentsAbove
    (hsource : CCMFirstClockPublishedSourceNonnegative)
    {b r : ℝ} (hMom : CCMFirstClockTailMomentsAbove b)
    (hr : b < r) :
    0 ∈ interior (integrableExpSet id (ccmFirstClockLandauMeasure r)) := by
  let δ : ℝ := (r - b) / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset
    (Ioo_mem_nhds (a := -δ) (b := δ) (by linarith) (by linarith)) ?_
  intro t ht
  exact integrable_exp_mul_id_landauMeasure_of_momentsAbove
    hsource hMom (by
      dsimp only [δ] at ht
      linarith [ht.2])

/-- Centered positive-tail MGF equals the ordinary tail Laplace transform wherever either is
used; equality is algebraic after the with-density change of measure. -/
theorem complexMGF_id_ccmFirstClockLandauMeasure_eq_tailLaplace
    (hsource : CCMFirstClockPublishedSourceNonnegative)
    (r : ℝ) (z : ℂ) :
    complexMGF id (ccmFirstClockLandauMeasure r) z =
      ccmFirstClockTailLaplace ((r : ℂ) - z) := by
  have hmeas : AEMeasurable
      (fun L => ENNReal.ofReal (ccmFirstClockLandauDensity r L))
      (volume.restrict (Ioi (Real.pi / 2))) :=
    (measurable_ccmFirstClockLandauDensity r).ennreal_ofReal
      |>.aemeasurable.restrict
  have hnonneg :=
    ccmFirstClockLandauDensity_nonneg_ae hsource r
  rw [complexMGF, ccmFirstClockLandauMeasure,
    integral_withDensity_eq_integral_toReal_smul₀ hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  unfold ccmFirstClockTailLaplace
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with L hL hden
  rw [ENNReal.toReal_ofReal hden, Complex.real_smul]
  push_cast
  simp only [id_eq, Complex.ofReal_re]
  have hQim := ccmFirstClockXiRationalDivisor_im_eq_zero L
  have hQcast :
      ccmFirstClockXiRationalDivisor L =
        ((ccmFirstClockXiRationalDivisor L).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa [hQim]
  rw [hQcast]
  unfold ccmFirstClockLandauDensity
  push_cast
  rw [show
      Complex.exp (-(r : ℂ) * (L : ℂ)) *
          ((ccmFirstClockXiRationalDivisor L).re : ℂ) *
          Complex.exp (z * (L : ℂ)) =
        (Complex.exp (-(r : ℂ) * (L : ℂ)) *
          Complex.exp (z * (L : ℂ))) *
          ((ccmFirstClockXiRationalDivisor L).re : ℂ) by ring]
  rw [← Complex.exp_add]
  congr 1
  ring

theorem analyticOnNhd_ccmFirstClockTailLaplace_of_momentsAbove
    (hsource : CCMFirstClockPublishedSourceNonnegative)
    {b : ℝ} (hMom : CCMFirstClockTailMomentsAbove b) :
    AnalyticOnNhd ℂ ccmFirstClockTailLaplace {s : ℂ | b < s.re} := by
  intro s hs
  let r : ℝ := s.re
  let z : ℂ := (r : ℂ) - s
  have hr : b < r := hs
  have hzero :=
    zero_mem_interior_integrableExpSet_of_momentsAbove hsource hMom hr
  have hzre : z.re = 0 := by
    dsimp only [z, r]
    simp
  have hmgf : AnalyticAt ℂ
      (complexMGF id (ccmFirstClockLandauMeasure r)) z :=
    analyticAt_complexMGF (by simpa only [hzre] using hzero)
  have hmgf' : AnalyticAt ℂ
      (complexMGF id (ccmFirstClockLandauMeasure r)) ((r : ℂ) - s) := by
    simpa only [z] using hmgf
  have haffine : AnalyticAt ℂ (fun w : ℂ => (r : ℂ) - w) s := by
    fun_prop
  have hcomp := hmgf'.comp haffine
  have heq : (fun w : ℂ =>
      complexMGF id (ccmFirstClockLandauMeasure r) ((r : ℂ) - w)) =
      ccmFirstClockTailLaplace := by
    funext w
    exact complexMGF_id_ccmFirstClockLandauMeasure_eq_tailLaplace
      hsource r ((r : ℂ) - w) |>.trans (by
        congr 1
        ring)
  rw [← heq]
  simpa only [Function.comp_apply] using hcomp

/-- Narrow convex strip on which the normally convergent continuation is locally represented
by its half-radius positive-axis disks. -/
def ccmFirstClockLandauStrip (b : ℝ) : Set ℂ :=
  {s : ℂ | b < s.re ∧ |s.im| < b / 4}

theorem isPreconnected_ccmFirstClockLandauStrip
    {b : ℝ} :
    IsPreconnected (ccmFirstClockLandauStrip b) := by
  have hconv : Convex ℝ (ccmFirstClockLandauStrip b) := by
    rw [ccmFirstClockLandauStrip]
    have hre := convex_halfSpace_re_gt b
    have himUp := convex_halfSpace_im_lt (b / 4)
    have himDown := convex_halfSpace_im_gt (-(b / 4))
    rw [show {s : ℂ | b < s.re ∧ |s.im| < b / 4} =
        {s : ℂ | b < s.re} ∩
          ({s : ℂ | -(b / 4) < s.im} ∩ {s : ℂ | s.im < b / 4}) by
      ext s
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, abs_lt]
      ]
    exact hre.inter (himDown.inter himUp)
  exact hconv.isPreconnected

theorem analyticOnNhd_ccmFirstClockTailContinuation_strip
    {b : ℝ} (hb : 0 < b) :
    AnalyticOnNhd ℂ ccmFirstClockTailContinuation
      (ccmFirstClockLandauStrip b) := by
  intro s hs
  have hsre : 0 < s.re := hb.trans hs.1
  have hsball : s ∈ Metric.ball (s.re : ℂ) (s.re / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]
    have heq : s - (s.re : ℂ) = (s.im : ℂ) * I := by
      apply Complex.ext <;> simp [mul_re, mul_im]
    rw [heq, norm_mul, norm_real, Real.norm_eq_abs, norm_I, mul_one]
    exact lt_trans hs.2 (by nlinarith [hs.1, hb])
  have htailOn : DifferentiableOn ℂ ccmFirstClockTailContinuation
      (Metric.ball (s.re : ℂ) (s.re / 2)) := by
    exact (differentiableOn_ccmFirstClockLaplaceContinuation_ball hsre).sub
      differentiable_ccmFirstClockHeadLaplace.differentiableOn
  exact htailOn.analyticAt (Metric.isOpen_ball.mem_nhds hsball)

theorem ccmFirstClockTailLaplace_eq_continuation_of_momentsAbove
    (hsource : CCMFirstClockPublishedSourceNonnegative)
    {b : ℝ} (hb : 0 < b) (hbHalf : b ≤ 1 / 2)
    (hMom : CCMFirstClockTailMomentsAbove b) :
    Set.EqOn ccmFirstClockTailLaplace ccmFirstClockTailContinuation
      (ccmFirstClockLandauStrip b) := by
  have hleft :=
    analyticOnNhd_ccmFirstClockTailLaplace_of_momentsAbove hsource hMom
  have hleftStrip : AnalyticOnNhd ℂ ccmFirstClockTailLaplace
      (ccmFirstClockLandauStrip b) := by
    intro s hs
    exact hleft s hs.1
  have hright :=
    analyticOnNhd_ccmFirstClockTailContinuation_strip hb
  have hone : (1 : ℂ) ∈ ccmFirstClockLandauStrip b := by
    constructor
    · change b < 1
      linarith [hbHalf]
    · simp
      positivity
  have hevent :
      ccmFirstClockTailLaplace =ᶠ[𝓝 (1 : ℂ)]
        ccmFirstClockTailContinuation := by
    have hopen : {s : ℂ | 1 / 2 < s.re} ∈ 𝓝 (1 : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hopen] with s hs
    exact integral_tail_exp_mul_ccmFirstClockXiRationalDivisor_eq_continuation hs
  exact hleftStrip.eqOn_of_preconnected_of_eventuallyEq hright
    isPreconnected_ccmFirstClockLandauStrip hone hevent

private theorem landauContinuation_eventuallyEq_complexMGF_of_momentsAbove
    (hsource : CCMFirstClockPublishedSourceNonnegative)
    {b : ℝ} (hb : 0 < b) (hbHalf : b ≤ 1 / 2)
    (hMom : CCMFirstClockTailMomentsAbove b)
    {r : ℝ} (hr : b < r) :
    ccmFirstClockLandauContinuation r =ᶠ[𝓝 0]
      complexMGF id (ccmFirstClockLandauMeasure r) := by
  have heq :=
    ccmFirstClockTailLaplace_eq_continuation_of_momentsAbove
      hsource hb hbHalf hMom
  have hopen :
      {z : ℂ | z.re < r - b ∧ |z.im| < b / 4} ∈ 𝓝 (0 : ℂ) := by
    have hOpenSet : IsOpen {z : ℂ | z.re < r - b ∧ |z.im| < b / 4} := by
      exact (isOpen_lt Complex.continuous_re continuous_const).inter
        (isOpen_lt (Complex.continuous_im.abs) continuous_const)
    exact hOpenSet.mem_nhds (by
      constructor
      · simpa using sub_pos.mpr hr
      · simpa only [Complex.zero_im, abs_zero] using
          (div_pos hb (by norm_num : (0 : ℝ) < 4)))
  filter_upwards [hopen] with z hz
  have hsStrip : (r : ℂ) - z ∈ ccmFirstClockLandauStrip b := by
    constructor
    · simp only [sub_re, ofReal_re]
      linarith [hz.1]
    · simp only [sub_im, ofReal_im, zero_sub, abs_neg]
      exact hz.2
  calc
    ccmFirstClockLandauContinuation r z =
        ccmFirstClockTailContinuation ((r : ℂ) - z) := rfl
    _ = ccmFirstClockTailLaplace ((r : ℂ) - z) :=
      (heq hsStrip).symm
    _ = complexMGF id (ccmFirstClockLandauMeasure r) z :=
      (complexMGF_id_ccmFirstClockLandauMeasure_eq_tailLaplace
        hsource r z).symm

private theorem landau_integrable_transfer_of_momentsAbove
    (hsource : CCMFirstClockPublishedSourceNonnegative)
    {b : ℝ} (hb : 0 < b) (hbHalf : b ≤ 1 / 2)
    (hMom : CCMFirstClockTailMomentsAbove b)
    {r : ℝ} (hr : b < r) {R : NNReal}
    (hR : (R : ℝ) < r / 2)
    {rho : ℝ} (hrho0 : 0 ≤ rho) (hrhoR : rho < (R : ℝ)) :
    Integrable (fun L : ℝ => Real.exp (rho * id L))
      (ccmFirstClockLandauMeasure r) := by
  exact landau_complexMGF_integrable_transfer
    (by
      have hmeas : AEMeasurable
          (fun L => ENNReal.ofReal (ccmFirstClockLandauDensity r L))
          (volume.restrict (Ioi (Real.pi / 2))) :=
        (measurable_ccmFirstClockLandauDensity r).ennreal_ofReal
          |>.aemeasurable.restrict
      rw [ccmFirstClockLandauMeasure, ae_withDensity_iff' hmeas]
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
      intro hdens
      exact le_trans (by positivity : 0 ≤ Real.pi / 2) hL.le)
    (zero_mem_interior_integrableExpSet_of_momentsAbove hsource hMom hr)
    (differentiableOn_ccmFirstClockLandauContinuation_closedBall
      (hb.trans hr) hR)
    (landauContinuation_eventuallyEq_complexMGF_of_momentsAbove
      hsource hb hbHalf hMom hr)
    hrho0 hrhoR

/-- **Universal CCM Landau halving law.**  If the positive first-clock tail has all
Laplace moments above `b`, normal continuation and the identity theorem force all moments
above `b/2`. -/
theorem ccmFirstClockTailMomentsAbove_half
    (hsource : CCMFirstClockPublishedSourceNonnegative)
    {b : ℝ} (hb : 0 < b) (hbHalf : b ≤ 1 / 2)
    (hMom : CCMFirstClockTailMomentsAbove b) :
    CCMFirstClockTailMomentsAbove (b / 2) := by
  intro a ha
  let r : ℝ := a + b / 2
  let rho : ℝ := b / 2
  let Rreal : ℝ := (rho + r / 2) / 2
  have hr : b < r := by
    dsimp only [r]
    linarith
  have hrpos : 0 < r := (hb.trans hr)
  have hrho0 : 0 ≤ rho := by
    dsimp only [rho]
    linarith
  have hR0 : 0 ≤ Rreal := by
    dsimp only [Rreal]
    positivity
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
  have htransfer :=
    landau_integrable_transfer_of_momentsAbove
      hsource hb hbHalf hMom hr hRhalf hrho0 hrhoR
  have hsub :=
    integrableOn_ccmFirstClockLandauDensity_sub_of_transfer hsource htransfer
  have hra : r - rho = a := by
    dsimp only [r, rho]
    ring
  simpa only [hra] using hsub

end

end RHTower
