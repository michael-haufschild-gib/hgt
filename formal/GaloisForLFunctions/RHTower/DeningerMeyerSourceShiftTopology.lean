import GaloisForLFunctions.RHTower.DeningerMeyerCyclicBoundary

/-!
# Strict division on the full strong source

Every shifted source generator is injective and maps onto exactly one closed
Mellin hyperplane. Frechet open mapping makes its inverse continuous. In
particular, it sends closed source subspaces to closed source subspaces.
-/

open Complex Filter Set Topology TopologicalSpace Uniformity

namespace RHTower
noncomputable section
open scoped DeningerMeyerNaturalTopology

def deningerMeyerStrongLogShift (rho : ℂ) : Module.End ℂ DeningerMeyerStrongLogTarget :=
  deningerMeyerStrongLogGenerator - rho • LinearMap.id

theorem deningerMeyerStrongLogShift_mellin (rho : ℂ)
    (g : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerMeyerStrongLogShift rho g) s =
      (s - rho) * deningerMeyerStrongLogMellin g s := by
  change deningerMeyerStrongLogMellinLM s (deningerMeyerStrongLogGenerator g - rho • g) = _
  rw [map_sub, map_smul]
  change deningerMeyerStrongLogMellin (deningerMeyerStrongLogGenerator g) s -
    rho * deningerMeyerStrongLogMellin g s = _
  rw [deningerMeyerStrongLogGenerator_mellin]
  ring

theorem deningerMeyerStrongLogShift_continuous (rho : ℂ) :
    Continuous (deningerMeyerStrongLogShift rho) :=
  deningerMeyerStrongLogGenerator_continuous.sub (continuous_id.const_smul rho)

theorem deningerMeyerStrongLogShift_injective (rho : ℂ) :
    Function.Injective (deningerMeyerStrongLogShift rho) := by
  intro g h he
  apply deningerMeyerStrongLogMellin_injective
  apply Continuous.ext_on (dense_compl_singleton rho)
    (differentiable_deningerMeyerStrongLogMellin g.property).continuous
    (differentiable_deningerMeyerStrongLogMellin h.property).continuous
  intro s hs
  have hm := congrArg (fun v : DeningerMeyerStrongLogTarget => deningerMeyerStrongLogMellin v s) he
  rw [deningerMeyerStrongLogShift_mellin, deningerMeyerStrongLogShift_mellin] at hm
  exact mul_left_cancel₀ (sub_ne_zero.mpr hs) hm

theorem deningerMeyerStrongLogShift_range (rho : ℂ) :
    LinearMap.range (deningerMeyerStrongLogShift rho) =
      LinearMap.ker (deningerMeyerStrongLogMellinLM rho) := by
  ext g
  constructor
  · rintro ⟨h, rfl⟩
    change deningerMeyerStrongLogMellin (deningerMeyerStrongLogShift rho h) rho = 0
    rw [deningerMeyerStrongLogShift_mellin, sub_self, zero_mul]
  · intro hg
    refine ⟨deningerMeyerCausalDivide g rho hg, ?_⟩
    change deningerMeyerStrongLogGenerator _ - rho • _ = g
    rw [deningerMeyerStrongLogGenerator_causalDivide]
    module

theorem deningerMeyerStrongLogShift_range_isClosed (rho : ℂ) :
    IsClosed (LinearMap.range (deningerMeyerStrongLogShift rho) : Set DeningerMeyerStrongLogTarget) := by
  rw [deningerMeyerStrongLogShift_range]
  have he : deningerMeyerStrongLogMellinLM rho = deningerMeyerStrongLogMellinJetLM 0 rho := rfl
  rw [he]
  exact isClosed_eq (deningerMeyerStrongLogMellinJetLM_continuous 0 rho) continuous_const

/-- The exact source inverse, with the inherited range topology. -/
def deningerMeyerStrongLogShiftRangeEquiv (rho : ℂ) :
    DeningerMeyerStrongLogTarget ≃L[ℂ] LinearMap.range (deningerMeyerStrongLogShift rho) := by
  letI : UniformSpace DeningerMeyerStrongLogTarget :=
    DeningerMeyerNaturalTopology.strongLogUniformSpace
  haveI : (𝓤 DeningerMeyerStrongLogTarget).IsCountablyGenerated := by
    rw [uniformity_eq_comap_nhds_zero]
    infer_instance
  haveI : IsCompletelyPseudoMetrizableSpace DeningerMeyerStrongLogTarget := by
    infer_instance
  let e : DeningerMeyerStrongLogTarget ≃ₗ[ℂ]
      LinearMap.range (deningerMeyerStrongLogShift rho) :=
    LinearEquiv.ofInjective _ (deningerMeyerStrongLogShift_injective rho)
  have hc : Continuous e := (deningerMeyerStrongLogShift_continuous rho).subtype_mk _
  haveI : IsUniformAddGroup (LinearMap.range (deningerMeyerStrongLogShift rho)) :=
    inferInstanceAs (IsUniformAddGroup
      (LinearMap.range (deningerMeyerStrongLogShift rho)).toAddSubgroup)
  haveI : IsCompletelyPseudoMetrizableSpace
      (LinearMap.range (deningerMeyerStrongLogShift rho)) :=
    (deningerMeyerStrongLogShift_range_isClosed rho).isCompletelyPseudoMetrizableSpace
  have hci : Continuous e.symm :=
    GaloisForLFunctions.continuous_symm_of_continuous
      (𝕜 := ℂ) (E := DeningerMeyerStrongLogTarget)
      (F := LinearMap.range (deningerMeyerStrongLogShift rho)) e hc
  exact { toLinearEquiv := e, continuous_toFun := hc, continuous_invFun := hci }

theorem deningerMeyerStrongLogShift_isClosedMap (rho : ℂ) :
    IsClosedMap (deningerMeyerStrongLogShift rho) :=
  (deningerMeyerStrongLogShift_range_isClosed rho).isClosedMap_subtype_val.comp
    (deningerMeyerStrongLogShiftRangeEquiv rho).toHomeomorph.isClosedMap

end
end RHTower
