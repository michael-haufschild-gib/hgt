import GaloisForLFunctions.RHTower.SelbergMaassCurrentDensityMeasure

/-!
# Exact source carriers and separate modular current measures

The current and residual are exactly the restrictions of the original curvature
measure to the complement of the common-zero set and to the common-zero set.
Original trace invariance makes that separator invariant. Pushforward commutes
with restriction, so full-curvature invariance transports both source measures
separately, retaining every measurable seam contribution. No quotient current
period, nodal area bound, or spectral quarter comparison is assumed.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups CompactlySupported
namespace GaloisForLFunctions.RHTower.SelbergMaassCurrentCarrier
open SelbergMaassCongruenceTrace SelbergMaassCurvatureMeasure SelbergMaassCurrentMeasures
  SelbergMaassResidualSupport SelbergMaassCurrentDensityMeasure SelbergMaassCurvatureTransport
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The literal common-zero set of the original finite congruence source. -/
def sourceNodes : Set ℍ := {z | density N f z = 0}

/-- Original source continuity makes the nodal separator measurable. -/
theorem sourceNodes_measurable : MeasurableSet (sourceNodes N f) :=
  (isClosed_eq (density_continuous N f) continuous_const).measurableSet

/-- The original nodal set is invariant under every integral modular action. -/
theorem sourceNodes_preimage (A : SL2Z) :
    (fun z : ℍ => A • z) ⁻¹' sourceNodes N f = sourceNodes N f := by
  ext z
  simp only [sourceNodes, mem_preimage, mem_setOf_eq, density_invariant]

/-- The residual is exactly the original curvature measure restricted to its original nodal set. -/
theorem curvature_restrict_nodes :
    (curvatureMeasure N f).restrict (sourceNodes N f) = residualMeasure N f := by
  have hr := Measure.restrict_add_restrict_compl (μ := residualMeasure N f) (sourceNodes_measurable N f)
  have hz : (residualMeasure N f).restrict (sourceNodes N f)ᶜ = 0 :=
    Measure.restrict_eq_zero.mpr (residualMeasure_compl_node_zero N f)
  rw [hz, add_zero] at hr
  have hc0 : (currentMeasure N f).restrict (sourceNodes N f) = 0 :=
    Measure.restrict_eq_zero.mpr (currentMeasure_node_zero N f)
  rw [curvatureMeasure_eq_add, Measure.restrict_add, hc0, zero_add]
  exact hr

/-- The current is exactly the original curvature measure restricted away from common zeros. -/
theorem curvature_restrict_compl_nodes :
    (curvatureMeasure N f).restrict (sourceNodes N f)ᶜ = currentMeasure N f := by
  have hc := Measure.restrict_add_restrict_compl (μ := currentMeasure N f) (sourceNodes_measurable N f)
  have hz : (currentMeasure N f).restrict (sourceNodes N f) = 0 :=
    Measure.restrict_eq_zero.mpr (currentMeasure_node_zero N f)
  rw [hz, zero_add] at hc
  have hr0 : (residualMeasure N f).restrict (sourceNodes N f)ᶜ = 0 :=
    Measure.restrict_eq_zero.mpr (residualMeasure_compl_node_zero N f)
  rw [curvatureMeasure_eq_add, Measure.restrict_add, hr0, add_zero]
  exact hc

/-- Modular invariance of the current measure follows from its actual invariant source carrier. -/
theorem currentMeasure_map (A : SL2Z) :
    Measure.map (fun z : ℍ => A • z) (currentMeasure N f) = currentMeasure N f := by
  have hm : Measurable (fun z : ℍ => A • z) :=
    (Homeomorph.smul (A : GL (Fin 2) ℝ)).continuous.measurable
  have h := Measure.restrict_map (μ := curvatureMeasure N f) hm (sourceNodes_measurable N f).compl
  rw [curvatureMeasure_map, preimage_compl, sourceNodes_preimage,
    curvature_restrict_compl_nodes] at h
  exact h.symm

/-- Modular invariance of the residual retains its full original nodal charge. -/
theorem residualMeasure_map (A : SL2Z) :
    Measure.map (fun z : ℍ => A • z) (residualMeasure N f) = residualMeasure N f := by
  have hm : Measurable (fun z : ℍ => A • z) :=
    (Homeomorph.smul (A : GL (Fin 2) ℝ)).continuous.measurable
  have h := Measure.restrict_map (μ := curvatureMeasure N f) hm (sourceNodes_measurable N f)
  rw [curvatureMeasure_map, sourceNodes_preimage, curvature_restrict_nodes] at h
  exact h.symm

/-- Every measurable modular preimage preserves actual current mass. -/
theorem currentMeasure_preimage (A : SL2Z) {s : Set ℍ} (hs : MeasurableSet s) :
    currentMeasure N f ((fun z : ℍ => A • z) ⁻¹' s) = currentMeasure N f s := by
  have hm : Measurable (fun z : ℍ => A • z) :=
    (Homeomorph.smul (A : GL (Fin 2) ℝ)).continuous.measurable
  have h := congrArg (fun μ : Measure ℍ => μ s) (currentMeasure_map N f A)
  rw [Measure.map_apply hm hs] at h
  exact h

/-- Every measurable modular preimage preserves actual residual mass, including seams. -/
theorem residualMeasure_preimage (A : SL2Z) {s : Set ℍ} (hs : MeasurableSet s) :
    residualMeasure N f ((fun z : ℍ => A • z) ⁻¹' s) = residualMeasure N f s := by
  have hm : Measurable (fun z : ℍ => A • z) :=
    (Homeomorph.smul (A : GL (Fin 2) ℝ)).continuous.measurable
  have h := congrArg (fun μ : Measure ℍ => μ s) (residualMeasure_map N f A)
  rw [Measure.map_apply hm hs] at h
  exact h

/-- Actual current integrals admit modular change of variables. -/
theorem integral_current_modular (A : SL2Z) (F : ℍ → ℝ) :
    (∫ z, F (A • z) ∂currentMeasure N f) = ∫ z, F z ∂currentMeasure N f := by
  let e : ℍ ≃ₜ ℍ := Homeomorph.smul (A : GL (Fin 2) ℝ)
  have h := e.measurableEmbedding.integral_map (μ := currentMeasure N f) F
  change (∫ z, F z ∂Measure.map (fun w : ℍ => A • w) (currentMeasure N f)) = _ at h
  rw [currentMeasure_map] at h
  exact h.symm

/-- Actual residual integrals admit modular change of variables with all nodal contributions retained. -/
theorem integral_residual_modular (A : SL2Z) (F : ℍ → ℝ) :
    (∫ z, F (A • z) ∂residualMeasure N f) = ∫ z, F z ∂residualMeasure N f := by
  let e : ℍ ≃ₜ ℍ := Homeomorph.smul (A : GL (Fin 2) ℝ)
  have h := e.measurableEmbedding.integral_map (μ := residualMeasure N f) F
  change (∫ z, F z ∂Measure.map (fun w : ℍ => A • w) (residualMeasure N f)) = _ at h
  rw [residualMeasure_map] at h
  exact h.symm

end
end GaloisForLFunctions.RHTower.SelbergMaassCurrentCarrier
