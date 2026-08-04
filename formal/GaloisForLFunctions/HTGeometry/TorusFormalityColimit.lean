import GaloisForLFunctions.HTGeometry.TorusPullbackDGA
import GaloisForLFunctions.HTGeometry.CDGAColimitQuasiIso
import GaloisForLFunctions.HTGeometry.TorusCohomologyColimit

/-!
# Formality of a tower of tori

A directed system of tori gives a directed system of de Rham algebras, with pullback as the
transition morphisms, and a directed system of exterior algebras of the duals of the covering
spaces, with the exterior powers of the transposes.  The comparison of one with the other is a
quasi-isomorphism at every stage and commutes with the transitions, so the induced morphism of the
colimit algebras is a quasi-isomorphism.

* `exteriorPullbackHom` : the transition morphism of the exterior algebras.
* `torusFormalityColimit_isQuasiIso` : the comparison of the colimits is a quasi-isomorphism.
-/

set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

namespace GaloisForLFunctions.HTGeometry

open exteriorPower Module

section ExteriorTransition

variable {𝕜 : Type u} [RCLike 𝕜] {r s : ℕ}

/-- **Pullback of the exterior algebra of the dual**, as a morphism of algebras with zero
differential. -/
noncomputable def exteriorPullbackHom (𝕜 : Type u) [RCLike 𝕜]
    (T : (Fin r → 𝕜) →L[𝕜] (Fin s → 𝕜)) :
    CDGAHom (exteriorCDGA 𝕜 s) (exteriorCDGA 𝕜 r) where
  toFun n y := exteriorPower.map n ((T : (Fin r → 𝕜) →ₗ[𝕜] (Fin s → 𝕜)).dualMap) y
  map_add n y z := map_add _ y z
  map_smul n c y := map_smul _ c y
  map_mul h y z := exteriorMulOf_map h _ y z
  map_d n y := by
    show exteriorPower.map (n + 1) _ 0 = 0
    exact map_zero _

end ExteriorTransition

section System

variable {𝕜 : Type u} [RCLike 𝕜] {p : 𝕜} {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  [DecidableEq ι] (S : TorusCoverSystem 𝕜 p ι)

/-- The transition morphisms of the de Rham algebras of a directed system of tori. -/
noncomputable def torusSystemHom (i j : ι) (h : i ≤ j) :
    CDGAHom (torusDeRhamCDGA p (S.dim i)) (torusDeRhamCDGA p (S.dim j)) :=
  torusPullbackHom p (S.map i j h) (S.map_lattice i j h)

/-- The transition morphisms of the exterior algebras of a directed system of tori. -/
noncomputable def exteriorSystemHom (i j : ι) (h : i ≤ j) :
    CDGAHom (exteriorCDGA 𝕜 (S.dim i)) (exteriorCDGA 𝕜 (S.dim j)) :=
  exteriorPullbackHom 𝕜 (S.map i j h)

omit [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι] in
theorem torusSystemHom_toFun (i j : ι) (h : i ≤ j) (n : ℕ)
    (x : smoothPeriodicForms p (S.dim i) n) :
    (((torusSystemHom S i j h).toFun n x : smoothPeriodicForms p (S.dim j) n) :
        PeriodicFormSpace 𝕜 (S.dim j) n) =
      linearPullback (S.map i j h) (x : PeriodicFormSpace 𝕜 (S.dim i) n) := rfl

omit [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι] in
theorem exteriorSystemHom_toFun (i j : ι) (h : i ≤ j) (n : ℕ)
    (y : ⋀[𝕜]^n (Module.Dual 𝕜 (Fin (S.dim i) → 𝕜))) :
    (exteriorSystemHom S i j h).toFun n y =
      exteriorPower.map n
        ((S.map i j h : (Fin (S.dim j) → 𝕜) →ₗ[𝕜] (Fin (S.dim i) → 𝕜)).dualMap) y := rfl

omit [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι] in
theorem torusSystem_directed : CDGADirectedSystem (fun i => torusDeRhamCDGA p (S.dim i))
    (torusSystemHom S) where
  map_self i h n x := by
    refine Subtype.ext ?_
    rw [torusSystemHom_toFun, S.map_self i h, linearPullback_id]
  map_map i j k hij hjk n x := by
    refine Subtype.ext ?_
    rw [torusSystemHom_toFun, torusSystemHom_toFun, torusSystemHom_toFun,
      ← linearPullback_comp, S.map_trans i j k hij hjk]

omit [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι] in
theorem exteriorSystem_directed : CDGADirectedSystem (fun i => exteriorCDGA 𝕜 (S.dim i))
    (exteriorSystemHom S) where
  map_self i h n y := by
    rw [exteriorSystemHom_toFun, S.map_self i h, ContinuousLinearMap.coe_id,
      LinearMap.dualMap_id, exteriorPower.map_id]
    rfl
  map_map i j k hij hjk n y := by
    rw [exteriorSystemHom_toFun, exteriorSystemHom_toFun, exteriorSystemHom_toFun,
      ← S.map_trans i j k hij hjk, ContinuousLinearMap.coe_comp,
      LinearMap.dualMap_comp_dualMap, exteriorPower.map_comp]
    rfl

end System

section Formality

variable {𝕜 : Type u} [RCLike 𝕜] {p : 𝕜} {ι : Type v} [Preorder ι] [IsDirectedOrder ι] [Nonempty ι]
  [DecidableEq ι] (S : TorusCoverSystem 𝕜 p ι)
  [∀ n : ℕ, DirectedSystem (fun i => smoothPeriodicForms p (S.dim i) n)
    fun i j h => degTransition (torusSystemHom S) n i j h]
  [∀ n : ℕ, DirectedSystem (fun i => ⋀[𝕜]^n (Module.Dual 𝕜 (Fin (S.dim i) → 𝕜)))
    fun i j h => degTransition (exteriorSystemHom S) n i j h]

omit [IsDirectedOrder ι] [Nonempty ι] [DecidableEq ι]
  [∀ n : ℕ, DirectedSystem (fun i => smoothPeriodicForms p (S.dim i) n)
    fun i j h => degTransition (torusSystemHom S) n i j h]
  [∀ n : ℕ, DirectedSystem (fun i => ⋀[𝕜]^n (Module.Dual 𝕜 (Fin (S.dim i) → 𝕜)))
    fun i j h => degTransition (exteriorSystemHom S) n i j h] in
/-- The comparison at each stage is compatible with the transition morphisms. -/
theorem torusFormality_compat (i j : ι) (hij : i ≤ j) (n : ℕ)
    (y : ⋀[𝕜]^n (Module.Dual 𝕜 (Fin (S.dim i) → 𝕜))) :
    (torusFormalityHom p (S.dim j)).toFun n ((exteriorSystemHom S i j hij).toFun n y) =
      (torusSystemHom S i j hij).toFun n ((torusFormalityHom p (S.dim i)).toFun n y) := by
  refine Subtype.ext ?_
  rw [exteriorSystemHom_toFun, torusSystemHom_toFun]
  funext w
  show constantFormOfExterior 𝕜 (S.dim j) n
      (exteriorPower.map n
        ((S.map i j hij : (Fin (S.dim j) → 𝕜) →ₗ[𝕜] (Fin (S.dim i) → 𝕜)).dualMap) y) =
    (constantFormOfExterior 𝕜 (S.dim i) n y).compContinuousLinearMap (S.map i j hij)
  rw [constantFormOfExterior_map_dualMap]

/-- **The comparison of the colimits is a quasi-isomorphism**: the formality statement for a
directed system of tori, as a single morphism of commutative differential graded algebras. -/
theorem torusFormalityColimit_isQuasiIso (hp : p ≠ 0) :
    (colimHom (exteriorSystemHom S) (torusSystemHom S)
      (fun i => torusFormalityHom p (S.dim i)) (torusFormality_compat S)).IsQuasiIso :=
  colimHom_isQuasiIso (exteriorSystemHom S) (torusSystemHom S)
    (fun i => torusFormalityHom p (S.dim i)) (torusFormality_compat S)
    (fun i => torusFormality_isQuasiIso hp (S.dim i))

end Formality

end GaloisForLFunctions.HTGeometry
