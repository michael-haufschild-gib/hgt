import GaloisForLFunctions.RHTower.CCMFirstClockLandauCarrier

open Complex MeasureTheory Set Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

theorem integrable_exp_mul_id_ccmFirstClockLandauMeasure
    (hsource : CCMFirstClockPublishedSourceNonnegative)
    {r t : ℝ} (hrt : 1 / 2 < r - t) :
    Integrable (fun L : ℝ => Real.exp (t * id L))
      (ccmFirstClockLandauMeasure r) := by
  have hdens :
      IntegrableOn (ccmFirstClockLandauDensity (r - t))
        (Ioi (Real.pi / 2)) :=
    integrableOn_ccmFirstClockLandauDensity hrt
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

theorem zero_mem_interior_integrableExpSet_id_ccmFirstClockLandauMeasure
    (hsource : CCMFirstClockPublishedSourceNonnegative)
    {r : ℝ} (hr : 1 / 2 < r) :
    0 ∈ interior
      (integrableExpSet id (ccmFirstClockLandauMeasure r)) := by
  let δ : ℝ := (r - 1 / 2) / 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  rw [mem_interior_iff_mem_nhds]
  refine mem_of_superset
    (Ioo_mem_nhds (a := -δ) (b := δ) (by linarith) (by linarith)) ?_
  intro t ht
  exact integrable_exp_mul_id_ccmFirstClockLandauMeasure hsource
    (by
      dsimp only [δ] at ht
      linarith [ht.2])

/-- Translation of the tail continuation to the MGF origin. -/
def ccmFirstClockLandauContinuation (r : ℝ) (z : ℂ) : ℂ :=
  ccmFirstClockTailContinuation ((r : ℂ) - z)

theorem differentiableOn_ccmFirstClockLandauContinuation_closedBall
    {r : ℝ} (hr : 0 < r) {R : NNReal}
    (hR : (R : ℝ) < r / 2) :
    DifferentiableOn ℂ (ccmFirstClockLandauContinuation r)
      (Metric.closedBall 0 (R : ℝ)) := by
  intro z hz
  have hzNorm : ‖z‖ ≤ (R : ℝ) := by
    simpa [Metric.mem_closedBall, dist_zero_right] using hz
  let s : ℂ := (r : ℂ) - z
  have hsball : s ∈ Metric.ball (r : ℂ) (r / 2) := by
    rw [Metric.mem_ball, dist_eq_norm]
    dsimp only [s]
    have heq : (r : ℂ) - z - (r : ℂ) = -z := by ring
    rw [heq, norm_neg]
    exact lt_of_le_of_lt hzNorm hR
  have hopen : IsOpen (Metric.ball (r : ℂ) (r / 2)) :=
    Metric.isOpen_ball
  have hfullAt : DifferentiableAt ℂ
      ccmFirstClockLaplaceContinuation s :=
    (differentiableOn_ccmFirstClockLaplaceContinuation_ball hr s hsball)
      |>.differentiableAt (hopen.mem_nhds hsball)
  have hheadAt : DifferentiableAt ℂ ccmFirstClockHeadLaplace s :=
    differentiable_ccmFirstClockHeadLaplace s
  have htailAt : DifferentiableAt ℂ ccmFirstClockTailContinuation s := by
    exact hfullAt.sub hheadAt
  have haffine : DifferentiableAt ℂ (fun w : ℂ => (r : ℂ) - w) z := by
    fun_prop
  exact (htailAt.comp z haffine).differentiableWithinAt

theorem ccmFirstClockLandauContinuation_eventuallyEq_complexMGF
    (hsource : CCMFirstClockPublishedSourceNonnegative)
    {r : ℝ} (hr : 1 / 2 < r) :
    ccmFirstClockLandauContinuation r =ᶠ[𝓝 0]
      complexMGF id (ccmFirstClockLandauMeasure r) := by
  have hopen : {z : ℂ | z.re < r - 1 / 2} ∈ 𝓝 (0 : ℂ) := by
    exact (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by
      simpa using sub_pos.mpr hr)
  filter_upwards [hopen] with z hz
  exact (complexMGF_id_ccmFirstClockLandauMeasure_eq_tailContinuation
    hsource hr (by linarith)).symm

/-- One exact Landau descent step from an unconditional center `r>1/2`. -/
theorem ccmFirstClockLandau_integrable_transfer
    (hsource : CCMFirstClockPublishedSourceNonnegative)
    {r : ℝ} (hr : 1 / 2 < r) {R : NNReal}
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
    (zero_mem_interior_integrableExpSet_id_ccmFirstClockLandauMeasure
      hsource hr)
    (differentiableOn_ccmFirstClockLandauContinuation_closedBall
      (lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr) hR)
    (ccmFirstClockLandauContinuation_eventuallyEq_complexMGF hsource hr)
    hrho0 hrhoR

private theorem integrableOn_ccmFirstClockLandauDensity_sub_of_transfer
    (hsource : CCMFirstClockPublishedSourceNonnegative)
    {r rho : ℝ}
    (htransfer : Integrable (fun L : ℝ => Real.exp (rho * id L))
      (ccmFirstClockLandauMeasure r)) :
    IntegrableOn (ccmFirstClockLandauDensity (r - rho))
      (Ioi (Real.pi / 2)) := by
  have hmeas : AEMeasurable
      (fun L => ENNReal.ofReal (ccmFirstClockLandauDensity r L))
      (volume.restrict (Ioi (Real.pi / 2))) :=
    (measurable_ccmFirstClockLandauDensity r).ennreal_ofReal
      |>.aemeasurable.restrict
  have hnonneg :=
    ccmFirstClockLandauDensity_nonneg_ae hsource r
  rw [ccmFirstClockLandauMeasure,
    integrable_withDensity_iff_integrable_smul₀' hmeas
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)] at htransfer
  apply htransfer.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi, hnonneg] with L hL hden
  rw [ENNReal.toReal_ofReal hden]
  simp only [id_eq, smul_eq_mul]
  unfold ccmFirstClockLandauDensity
  rw [show -(r - rho) * L = -r * L + rho * L by ring,
    Real.exp_add]
  ring

/-- **First strict Landau descent.**  Published first-clock nonnegativity pushes ordinary
Laplace integrability from the unconditional line `1/2` down to every line strictly above
`1/4`.  No zero-free estimate or finite divisor truncation is used. -/
theorem integrableOn_ccmFirstClockLandauDensity_of_one_fourth_lt
    (hsource : CCMFirstClockPublishedSourceNonnegative)
    {a : ℝ} (ha : 1 / 4 < a) :
    IntegrableOn (ccmFirstClockLandauDensity a)
      (Ioi (Real.pi / 2)) := by
  by_cases haHalf : 1 / 2 < a
  · exact integrableOn_ccmFirstClockLandauDensity haHalf
  · let r : ℝ := a + 1 / 4
    let rho : ℝ := 1 / 4
    let Rreal : ℝ := (rho + r / 2) / 2
    have hr : 1 / 2 < r := by
      dsimp only [r]
      linarith
    have hrpos : 0 < r :=
      lt_trans (by norm_num : (0 : ℝ) < 1 / 2) hr
    have hrho0 : 0 ≤ rho := by dsimp only [rho]; norm_num
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
      dsimp only [Rreal]
      linarith
    have htransfer :=
      ccmFirstClockLandau_integrable_transfer hsource hr hRhalf
        hrho0 hrhoR
    have hsub :=
      integrableOn_ccmFirstClockLandauDensity_sub_of_transfer
        hsource htransfer
    have hra : r - rho = a := by
      dsimp only [r, rho]
      ring
    simpa only [hra] using hsub

end

end RHTower
