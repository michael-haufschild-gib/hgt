import GaloisForLFunctions.RHTower.Deninger.DeningerCohomologyBasis
import GaloisForLFunctions.RHTower.Deninger.DeningerTransitionWedge

/-!
# The transition maps on the cohomology of the stages

Pulling back along a transition map is linear, preserves closed holomorphic forms and exact forms, so
it induces a linear map of the cohomology modules of the stages.  On constant forms it is composition
with the linear map of the exponent matrix, so under the comparison of the cohomology with the
constant alternating forms the induced map is the `k`-th exterior power of the exponent matrix.

* `deningerCohomologyMap` : the map induced on cohomology by a transition.
* `deningerCohomologyMap_constantClass` : the comparison of `(5)` is natural in the lattice.
-/

set_option maxSynthPendingDepth 3

namespace RHTower

open Complex

section PullbackLinear

variable {r s n : ℕ}

/-- **Pulling back stage forms is linear.** -/
noncomputable def deningerStagePullbackₗ (φ : (Fin s → ℂ) → (Fin r → ℂ)) :
    DeningerStageForm r n →ₗ[ℂ] DeningerStageForm s n where
  toFun ω := deningerStagePullback φ ω
  map_add' ω₁ ω₂ := by
    funext z
    ext v
    rfl
  map_smul' c ω := by
    funext z
    ext v
    rfl

theorem deningerStagePullbackₗ_apply (φ : (Fin s → ℂ) → (Fin r → ℂ))
    (ω : DeningerStageForm r n) (z : Fin s → ℂ) :
    deningerStagePullbackₗ φ ω z = deningerStagePullback φ ω z := rfl

/-- **The pullback of a closed holomorphic form along a transition is closed holomorphic.** -/
theorem deningerPullback_mem_closedForms (m : Fin r → Fin s → ℤ) {ω : DeningerStageForm r n}
    (hω : ω ∈ deningerClosedForms r n) :
    deningerStagePullbackₗ (deningerMonomialMap m) ω ∈ deningerClosedForms s n := by
  refine ⟨deningerMonomialPullback_holomorphic m hω.1, fun z hz => ?_⟩
  show extDeriv (deningerStagePullback (deningerMonomialMap m) ω) z = 0
  rw [deningerMonomialPullback_extDeriv m hω.1 hz]
  show (extDeriv ω (deningerMonomialMap m z)).compContinuousLinearMap
    (fderiv ℂ (deningerMonomialMap m) z) = 0
  rw [hω.2 _ (deningerMonomialMap_mapsTo m hz)]
  ext v
  rfl

/-- The pullback of closed holomorphic forms, as a map of the modules of closed forms. -/
noncomputable def deningerClosedPullback (m : Fin r → Fin s → ℤ) (n : ℕ) :
    (deningerClosedForms r n) →ₗ[ℂ] (deningerClosedForms s n) :=
  (deningerStagePullbackₗ (deningerMonomialMap m)).restrict
    fun _ hω => deningerPullback_mem_closedForms m hω

theorem deningerClosedPullback_coe (m : Fin r → Fin s → ℤ) (n : ℕ)
    (ω : deningerClosedForms r n) :
    (deningerClosedPullback m n ω : DeningerStageForm s n) =
      deningerStagePullback (deningerMonomialMap m) (ω : DeningerStageForm r n) := rfl

/-- **The pullback of an exact form along a transition is exact.** -/
theorem deningerClosedPullback_exact (m : Fin r → Fin s → ℤ) (n : ℕ)
    {ω : deningerClosedForms r (n + 1)} (hω : ω ∈ deningerExactForms r n) :
    deningerClosedPullback m (n + 1) ω ∈ deningerExactForms s n := by
  obtain ⟨θ, hθ, hθeq⟩ := hω
  refine ⟨deningerStagePullback (deningerMonomialMap m) θ,
    deningerMonomialPullback_holomorphic m hθ, fun z hz => ?_⟩
  rw [deningerClosedPullback_coe]
  rw [deningerMonomialPullback_extDeriv m hθ hz]
  show ((ω : DeningerStageForm r (n + 1)) (deningerMonomialMap m z)).compContinuousLinearMap
      (fderiv ℂ (deningerMonomialMap m) z) =
    (extDeriv θ (deningerMonomialMap m z)).compContinuousLinearMap
      (fderiv ℂ (deningerMonomialMap m) z)
  rw [hθeq _ (deningerMonomialMap_mapsTo m hz)]

/-- **The map induced on the cohomology of the stages by a transition map.** -/
noncomputable def deningerCohomologyMap (m : Fin r → Fin s → ℤ) (n : ℕ) :
    deningerCohomology r n →ₗ[ℂ] deningerCohomology s n :=
  Submodule.mapQ _ _ (deningerClosedPullback m (n + 1))
    fun _ hω => deningerClosedPullback_exact m n hω

theorem deningerCohomologyMap_mk (m : Fin r → Fin s → ℤ) (n : ℕ)
    (ω : deningerClosedForms r (n + 1)) :
    deningerCohomologyMap m n (Submodule.Quotient.mk ω) =
      Submodule.Quotient.mk (deningerClosedPullback m (n + 1) ω) :=
  rfl

end PullbackLinear

end RHTower

namespace RHTower

open Complex

section Naturality

variable {r s n : ℕ}

/-- **The pullback of a constant stage form along a transition is the constant stage form of the
composition with the exponent matrix.** -/
theorem deningerMonomialPullback_constantStageForm (m : Fin r → Fin s → ℤ)
    (α : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ) {z : Fin s → ℂ} (hz : z ∈ deningerStageTorus s) :
    deningerStagePullback (deningerMonomialMap m) (deningerConstantStageForm α) z =
      deningerConstantStageForm
        (α.compContinuousLinearMap (deningerMatrixCLM m)) z := by
  refine deningerExpPullback_injective (fun w => ?_) hz
  rw [show deningerPullbackForm (deningerExpMap s)
      (deningerConstantStageForm (α.compContinuousLinearMap (deningerMatrixCLM m))) w =
      α.compContinuousLinearMap (deningerMatrixCLM m) from
    deningerConstantStageForm_pullback _ w]
  show ((deningerConstantStageForm α
      (deningerMonomialMap m (deningerExpMap s w))).compContinuousLinearMap
      (fderiv ℂ (deningerMonomialMap m) (deningerExpMap s w))).compContinuousLinearMap
      (fderiv ℂ (deningerExpMap s) w) =
    α.compContinuousLinearMap (deningerMatrixCLM m)
  rw [(deningerExpMap_hasFDerivAt w).fderiv, deningerCompCLM_compCLM,
    deningerMonomialDeriv_comp_expDeriv m w, ← deningerExpMap_matrixCLM m w,
    ← deningerCompCLM_compCLM]
  have hconst : ContinuousAlternatingMap.compContinuousLinearMap
      (deningerConstantStageForm α (deningerExpMap r (deningerMatrixCLM m w)))
      (deningerExpDeriv (deningerMatrixCLM m w)) = α := by
    have h := deningerConstantStageForm_pullback α (deningerMatrixCLM m w)
    rw [deningerExpPullbackForm, deningerPullbackForm,
      (deningerExpMap_hasFDerivAt (deningerMatrixCLM m w)).fderiv] at h
    exact h
  rw [hconst]

/-- **The comparison of the cohomology with the constant alternating forms is natural in the
lattice**: the map induced by a transition is composition with the linear map of its exponent
matrix, that is, the `k`-th exterior power of the transition. -/
theorem deningerCohomologyMap_constantClass (m : Fin r → Fin s → ℤ) (n : ℕ)
    (α : (Fin r → ℂ) [⋀^Fin (n + 1)]→L[ℂ] ℂ) :
    deningerCohomologyMap m n (deningerConstantClass r n α) =
      deningerConstantClass s n (α.compContinuousLinearMap (deningerMatrixCLM m)) := by
  have hstep : deningerCohomologyMap m n (deningerConstantClass r n α) =
      Submodule.Quotient.mk (deningerClosedPullback m (n + 1)
        ⟨deningerConstantStageForm α, deningerConstantStageForm_mem α⟩) := rfl
  have hstep' : deningerConstantClass s n (α.compContinuousLinearMap (deningerMatrixCLM m)) =
      Submodule.Quotient.mk ⟨deningerConstantStageForm
        (α.compContinuousLinearMap (deningerMatrixCLM m)),
        deningerConstantStageForm_mem _⟩ := rfl
  rw [hstep, hstep']
  refine (Submodule.Quotient.eq _).2 ?_
  refine ⟨0, fun z _ => analyticAt_const, fun z hz => ?_⟩
  show (deningerClosedPullback m (n + 1)
      ⟨deningerConstantStageForm α, deningerConstantStageForm_mem α⟩ :
        DeningerStageForm s (n + 1)) z -
      deningerConstantStageForm (α.compContinuousLinearMap (deningerMatrixCLM m)) z =
    extDeriv (0 : DeningerStageForm s n) z
  rw [deningerClosedPullback_coe, deningerMonomialPullback_constantStageForm m α hz, sub_self]
  exact (deningerExtDeriv_const (0 : (Fin s → ℂ) [⋀^Fin n]→L[ℂ] ℂ) z).symm

end Naturality

end RHTower
