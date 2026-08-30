import GaloisForLFunctions.HTGeometry.HalfPlaneHardyModelSpace
import GaloisForLFunctions.HTGeometry.HardyDiskModelDimension

open Complex
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

local instance halfPlaneFiniteBlaschkeModelLocalInst1 : CompleteSpace UpperHardyL2 :=
  RHTower.isClosed_hardyL2.completeSpace_coe

/-- One divisor point in the open upper half-plane. -/
abbrev UpperHalfPlanePoint := {w : ℂ // 0 < w.im}

/-- Hardy multiplication by a finite ordered upper-half-plane Blaschke divisor. -/
def upperHardyFiniteInner : List UpperHalfPlanePoint → UpperHardyL2 →L[ℂ] UpperHardyL2
  | [] => ContinuousLinearMap.id ℂ UpperHardyL2
  | w :: ws => (upperHardyInnerBlaschke w.1 w.2).comp (upperHardyFiniteInner ws)

@[simp] theorem upperHardyFiniteInner_nil :
    upperHardyFiniteInner [] = ContinuousLinearMap.id ℂ UpperHardyL2 := rfl

@[simp] theorem upperHardyFiniteInner_cons
    (w : UpperHalfPlanePoint) (ws : List UpperHalfPlanePoint) :
    upperHardyFiniteInner (w :: ws) =
      (upperHardyInnerBlaschke w.1 w.2).comp (upperHardyFiniteInner ws) := rfl

theorem norm_upperHardyFiniteInner
    (ws : List UpperHalfPlanePoint) (f : UpperHardyL2) :
    ‖upperHardyFiniteInner ws f‖ = ‖f‖ := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
      rw [upperHardyFiniteInner_cons, ContinuousLinearMap.comp_apply,
        norm_upperHardyInnerBlaschke, ih]

private theorem range_upperHardyFiniteInner_cons
    (w : UpperHalfPlanePoint) (ws : List UpperHalfPlanePoint) :
    LinearMap.range (upperHardyFiniteInner (w :: ws) :
      UpperHardyL2 →ₗ[ℂ] UpperHardyL2) =
      (LinearMap.range (upperHardyFiniteInner ws :
        UpperHardyL2 →ₗ[ℂ] UpperHardyL2)).map
        (upperHardyInnerBlaschke w.1 w.2 :
          UpperHardyL2 →ₗ[ℂ] UpperHardyL2) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨upperHardyFiniteInner ws x, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩

/-- Finite half-plane Blaschke divisors have model dimension equal to list length,
including repeated points. -/
theorem finiteDimensional_and_finrank_orthogonal_range_upperHardyFiniteInner
    (ws : List UpperHalfPlanePoint) :
    FiniteDimensional ℂ ((LinearMap.range (upperHardyFiniteInner ws :
      UpperHardyL2 →ₗ[ℂ] UpperHardyL2))ᗮ : Submodule ℂ UpperHardyL2) ∧
    Module.finrank ℂ ((LinearMap.range (upperHardyFiniteInner ws :
      UpperHardyL2 →ₗ[ℂ] UpperHardyL2))ᗮ : Submodule ℂ UpperHardyL2) = ws.length := by
  induction ws with
  | nil =>
      have hrange : LinearMap.range (upperHardyFiniteInner [] :
          UpperHardyL2 →ₗ[ℂ] UpperHardyL2) = ⊤ := by
        ext f
        simp [upperHardyFiniteInner]
      have horth : ((⊤ : Submodule ℂ UpperHardyL2)ᗮ :
          Submodule ℂ UpperHardyL2) = ⊥ := by
        apply le_antisymm
        · intro f hf
          have hself : inner ℂ (f : UpperHardyL2) f = 0 := hf f (by simp)
          have hf0 : (f : UpperHardyL2) = 0 := inner_self_eq_zero.mp hself
          simpa using hf0
        · exact bot_le
      rw [hrange, horth, List.length_nil]
      exact ⟨inferInstance, finrank_bot ℂ UpperHardyL2⟩
  | cons w ws ih =>
      have hfinOne : FiniteDimensional ℂ
          ((LinearMap.range (upperHardyInnerBlaschke w.1 w.2 :
            UpperHardyL2 →ₗ[ℂ] UpperHardyL2))ᗮ : Submodule ℂ UpperHardyL2) := by
        rw [range_upperHardyInnerBlaschke_eq_orthogonal_span]
        letI : FiniteDimensional ℂ (ℂ ∙ lowerCauchyFeatureAt w.1 w.2) :=
          FiniteDimensional.span_singleton ℂ _
        letI : CompleteSpace (ℂ ∙ lowerCauchyFeatureAt w.1 w.2) :=
          FiniteDimensional.complete ℂ _
        letI : (ℂ ∙ lowerCauchyFeatureAt w.1 w.2).HasOrthogonalProjection :=
          Submodule.HasOrthogonalProjection.ofCompleteSpace _
        rw [Submodule.orthogonal_orthogonal]
        exact inferInstance
      letI : FiniteDimensional ℂ
          ((LinearMap.range (upperHardyInnerBlaschke w.1 w.2 :
            UpperHardyL2 →ₗ[ℂ] UpperHardyL2))ᗮ : Submodule ℂ UpperHardyL2) := hfinOne
      letI : FiniteDimensional ℂ
          ((LinearMap.range (upperHardyFiniteInner ws :
            UpperHardyL2 →ₗ[ℂ] UpperHardyL2))ᗮ : Submodule ℂ UpperHardyL2) := ih.1
      have hsplit := finrank_orthogonal_map_add
        (T := upperHardyInnerBlaschke w.1 w.2)
        (norm_upperHardyInnerBlaschke w.1 w.2)
        (LinearMap.range (upperHardyFiniteInner ws :
          UpperHardyL2 →ₗ[ℂ] UpperHardyL2))
      rw [← range_upperHardyFiniteInner_cons w ws,
        finrank_orthogonal_range_upperHardyInnerBlaschke w.1 w.2,
        ih.2] at hsplit
      refine ⟨hsplit.1, ?_⟩
      simpa [Nat.add_comm] using hsplit.2

theorem finrank_orthogonal_range_upperHardyFiniteInner
    (ws : List UpperHalfPlanePoint) :
    Module.finrank ℂ ((LinearMap.range (upperHardyFiniteInner ws :
      UpperHardyL2 →ₗ[ℂ] UpperHardyL2))ᗮ : Submodule ℂ UpperHardyL2) = ws.length :=
  (finiteDimensional_and_finrank_orthogonal_range_upperHardyFiniteInner ws).2

end GaloisForLFunctions.HTGeometry
