import GaloisForLFunctions.HTGeometry.TorusDeRhamCDGA
import GaloisForLFunctions.HTGeometry.PeriodicPullback

/-!
# Pullback is a morphism of de Rham algebras

Pullback of forms along a linear map of covering spaces carrying the period lattice into the period
lattice preserves smoothness, the wedge product and the exterior derivative, so it is a morphism of
the de Rham algebras of the two tori.  Multiplicativity comes from the exterior power of a linear
map being multiplicative.

* `wedgeForm_compContinuousLinearMap` : the wedge product is natural under pullback.
* `torusPullbackHom` : pullback as a morphism of commutative differential graded algebras.
-/

set_option maxSynthPendingDepth 3

namespace GaloisForLFunctions.HTGeometry

open exteriorPower Module
open scoped ContDiff

section Naturality

variable {𝕜 : Type u} [RCLike 𝕜] {r s a b n : ℕ}

/-- **The wedge product of alternating forms is natural under composition with a linear map.** -/
theorem wedgeForm_compContinuousLinearMap (h : a + b = n)
    (T : (Fin r → 𝕜) →L[𝕜] (Fin s → 𝕜)) (α : (Fin s → 𝕜) [⋀^Fin a]→L[𝕜] 𝕜)
    (β : (Fin s → 𝕜) [⋀^Fin b]→L[𝕜] 𝕜) :
    (wedgeForm h α β).compContinuousLinearMap T =
      wedgeForm h (α.compContinuousLinearMap T) (β.compContinuousLinearMap T) := by
  obtain ⟨u, rfl⟩ : ∃ u, constantFormOfExterior 𝕜 s a u = α :=
    ⟨_, (constantFormOfExterior 𝕜 s a).apply_symm_apply α⟩
  obtain ⟨v, rfl⟩ : ∃ v, constantFormOfExterior 𝕜 s b v = β :=
    ⟨_, (constantFormOfExterior 𝕜 s b).apply_symm_apply β⟩
  rw [wedgeForm_constantFormOfExterior, ← constantFormOfExterior_map_dualMap,
    ← constantFormOfExterior_map_dualMap, ← constantFormOfExterior_map_dualMap,
    wedgeForm_constantFormOfExterior, exteriorMulOf_map]

/-- The pullback of a smooth form is smooth. -/
theorem linearPullback_contDiff (T : (Fin r → 𝕜) →L[𝕜] (Fin s → 𝕜))
    {g : PeriodicFormSpace 𝕜 s n} (hg : ContDiff 𝕜 ∞ g) :
    ContDiff 𝕜 ∞ (linearPullback T g) := by
  have h : ContDiff 𝕜 ∞
      ((ContinuousAlternatingMap.compContinuousLinearMapCLM (F := 𝕜) T) ∘ g ∘
        (T : (Fin r → 𝕜) → (Fin s → 𝕜))) :=
    (ContinuousAlternatingMap.compContinuousLinearMapCLM (F := 𝕜) T).contDiff.comp
      (hg.comp T.contDiff)
  exact h

/-- The pullback of a smooth periodic form is a smooth periodic form. -/
theorem linearPullback_mem_smoothPeriodicForms {p : 𝕜}
    (T : (Fin r → 𝕜) →L[𝕜] (Fin s → 𝕜))
    (hT : ∀ l : Fin r, T (p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) ∈ periodLattice p s)
    {g : PeriodicFormSpace 𝕜 s n} (hg : g ∈ smoothPeriodicForms p s n) :
    linearPullback T g ∈ smoothPeriodicForms p r n :=
  ⟨linearPullback_contDiff T hg.1, linearPullback_periodic T hT hg.2⟩

end Naturality

section PullbackHom

variable {𝕜 : Type u} [RCLike 𝕜] {r s : ℕ}

/-- **Pullback along a map of lattices, as a morphism of the de Rham algebras of the tori.** -/
noncomputable def torusPullbackHom (p : 𝕜) (T : (Fin r → 𝕜) →L[𝕜] (Fin s → 𝕜))
    (hT : ∀ l : Fin r, T (p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) ∈ periodLattice p s) :
    CDGAHom (torusDeRhamCDGA p s) (torusDeRhamCDGA p r) where
  toFun n u := ⟨linearPullback T (u : PeriodicFormSpace 𝕜 s n),
    linearPullback_mem_smoothPeriodicForms T hT u.2⟩
  map_add n u v := Subtype.ext (linearPullback_add T _ _)
  map_smul n c u := Subtype.ext (linearPullback_smul T c _)
  map_mul h u v := by
    refine Subtype.ext ?_
    funext w
    exact wedgeForm_compContinuousLinearMap h T _ _
  map_d n u := by
    refine Subtype.ext ?_
    funext w
    show linearPullback T (extDeriv (u : PeriodicFormSpace 𝕜 s n)) w =
      extDeriv (linearPullback T (u : PeriodicFormSpace 𝕜 s n)) w
    exact (linearPullback_extDeriv T (u.2.1.differentiable (by simp)) w).symm

end PullbackHom

end GaloisForLFunctions.HTGeometry
