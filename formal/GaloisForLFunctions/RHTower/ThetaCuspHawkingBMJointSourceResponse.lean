import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceFieldDifferential

/-! Admission and actual joint operator response for the complete original-wave cusp residual. -/
open MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMJointSource
open D4BMModularCore D4BMGlobalAngularResponse D4BMJointWave
noncomputable section

/-- Original retained scalar source minus the actual differentiated explicit field. -/
def originalWaveResidual (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (p : ℝ × UpperHalfPlane) : ℂ :=
  originalForcing (physicalRate q branch) w a T (fullSquarePotential q (coordinates p.2))
      (fullGradientEnergy q (coordinates p.2)/2) p.1-
    fieldWave w (explicitField q branch w a T) p.1 (coordinates p.2)

/-- The admitted function is exactly the residual of the original differential equation. -/
theorem originalWaveResidual_eq (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) (t : ℝ) (ht : t < 0) (z : UpperHalfPlane) :
    originalWaveResidual q branch w a T (t,z) = cuspResidualForcing q branch w a T (t,z) := by
  unfold originalWaveResidual
  rw [explicitField_wave q branch w a T hw t ht (coordinates z) z.im_pos,
    originalForcing_explicitResidual q branch w a T hw t ht z]
  ring

/-- The actual L² forcing vector agrees almost everywhere with the full original-wave residual. -/
theorem cuspResidualVector_actual_ae (q : XiZeroCopy) (branch : Bool) (w a T : ℂ)
    (hw : PrincipalChamber q w) :
    cuspResidualVector q branch w a T hw =ᵐ[radialMeasure.prod D4BMModularCore.measure]
      originalWaveResidual q branch w a T := by
  have ht : ∀ᵐ p : ℝ × UpperHalfPlane ∂radialMeasure.prod D4BMModularCore.measure, p.1 < 0 := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_lt measurable_fst measurable_const)).mpr
    filter_upwards [ae_restrict_mem measurableSet_Iio] with t ht
    exact Filter.Eventually.of_forall (fun _ => ht)
  filter_upwards [cuspResidualVector_ae q branch w a T hw,ht] with p hp hpt
  rw [hp,originalWaveResidual_eq q branch w a T hw p.1 hpt p.2]

/-- Complete original-source admission and joint operator response on a whole nonempty frequency
half-plane. No source integrability, angular diagonalization, or response premise is supplied. -/
theorem originalSource_response (q : XiZeroCopy) (branch : Bool) (a T : ℂ) :
    ∃ c : ℝ, ∀ w : ℂ, c < w.re → ∃ (F : SpatialSpace) (u : jointDomain),
      F =ᵐ[radialMeasure.prod D4BMModularCore.measure] originalWaveResidual q branch w a T ∧
      JointWaveSolution w F u ∧
      (∃ hmem : jointEmbedding u ∈ jointEnergyOperator.domain,
        jointEnergyOperator ⟨jointEmbedding u,hmem⟩+(w^(2 : ℕ)-1) • jointEmbedding u = F) ∧
      ‖jointEmbedding u‖ ≤ ‖F‖/(w.re*‖w‖) := by
  refine ⟨principalThreshold q,fun w hw => ?_⟩
  have hch := principalChamber_of_threshold q w hw
  exact ⟨cuspResidualVector q branch w a T hch,cuspResidualResponse q branch w a T hch,
    cuspResidualVector_actual_ae q branch w a T hch,cuspResidualResponse_spec q branch w a T hch,
    cuspResidualResponse_operator q branch w a T hch,cuspResidualResponse_bound q branch w a T hch⟩

end
end RHTower.D4BMJointSource
