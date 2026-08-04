import GaloisForLFunctions.HTGeometry.PeriodicPullback
import GaloisForLFunctions.HTGeometry.ExteriorFormPairing

/-!
# The cohomology of the torus is the exterior power of the dual of its covering space

Evaluation at the identity identifies the translation-invariant forms on the torus with the exterior
power of the dual of the covering space: a product of linear forms goes to the determinant form of
their values.  Composing with the comparison of the cohomology with the invariant forms gives a
canonical isomorphism between the exterior power of the dual and the cohomology, which is natural in
the covering space: pullback along a map of lattices corresponds to the exterior power of the
transpose.

* `constantFormOfExterior` : the invariant form of an element of the exterior power of the dual.
* `periodicCohomologyDualEquiv` : the cohomology of the torus is that exterior power.
* `periodicCohomologyDualEquiv_naturality` : the identification is natural in the covering space.
-/

set_option maxSynthPendingDepth 3

namespace GaloisForLFunctions.HTGeometry

open exteriorPower Module

section InvariantForms

variable {𝕜 : Type*} [RCLike 𝕜] {r n : ℕ}

/-- **The invariant form defined by an element of the exterior power of the dual** of the covering
space. -/
noncomputable def constantFormOfExterior (𝕜 : Type*) [RCLike 𝕜] (r n : ℕ) :
    ⋀[𝕜]^n (Module.Dual 𝕜 (Fin r → 𝕜)) ≃ₗ[𝕜] ((Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) :=
  (formOfExteriorEquiv n (Pi.basisFun 𝕜 (Fin r))).trans
    (continuousAlternatingEquiv 𝕜 r (Fin n) 𝕜)

/-- **On a product of linear forms the invariant form is the determinant form.** -/
theorem constantFormOfExterior_ιMulti (φ : Fin n → Module.Dual 𝕜 (Fin r → 𝕜))
    (v : Fin n → (Fin r → 𝕜)) :
    constantFormOfExterior 𝕜 r n (exteriorPower.ιMulti 𝕜 n φ) v =
      Matrix.det (Matrix.of fun i j => φ j (v i)) := by
  show alternatingMapToContinuous
    (formOfExterior 𝕜 (Fin r → 𝕜) n (exteriorPower.ιMulti 𝕜 n φ)) v = _
  rw [alternatingMapToContinuous_apply, formOfExterior_ιMulti]

/-- The invariant form of a transported element is the pullback of the invariant form. -/
theorem constantFormOfExterior_map_dualMap {s : ℕ} (T : (Fin r → 𝕜) →L[𝕜] (Fin s → 𝕜))
    (x : ⋀[𝕜]^n (Module.Dual 𝕜 (Fin s → 𝕜))) :
    constantFormOfExterior 𝕜 r n (exteriorPower.map n ((T : (Fin r → 𝕜) →ₗ[𝕜] _).dualMap) x) =
      (constantFormOfExterior 𝕜 s n x).compContinuousLinearMap T := by
  ext v
  show formOfExterior 𝕜 (Fin r → 𝕜) n
      (exteriorPower.map n ((T : (Fin r → 𝕜) →ₗ[𝕜] _).dualMap) x) v =
    formOfExterior 𝕜 (Fin s → 𝕜) n x fun i => T (v i)
  rw [formOfExterior_map_dualMap]
  rfl

end InvariantForms

section CohomologyComparison

variable {𝕜 : Type*} [RCLike 𝕜] {r s n : ℕ}

/-- **The cohomology of the torus in degree `n + 1` is the `(n+1)`-st exterior power of the dual of
its covering space.** -/
noncomputable def periodicCohomologyDualEquiv {p : 𝕜} (hp : p ≠ 0) (r n : ℕ) :
    ⋀[𝕜]^(n + 1) (Module.Dual 𝕜 (Fin r → 𝕜)) ≃ₗ[𝕜] periodicCohomology p r n :=
  (constantFormOfExterior 𝕜 r (n + 1)).trans (periodicCohomologyEquiv hp r n)

/-- The class attached to an element of the exterior power is the class of its invariant form. -/
theorem periodicCohomologyDualEquiv_apply {p : 𝕜} (hp : p ≠ 0) (r n : ℕ)
    (x : ⋀[𝕜]^(n + 1) (Module.Dual 𝕜 (Fin r → 𝕜))) :
    periodicCohomologyDualEquiv hp r n x =
      constantClass p r n (constantFormOfExterior 𝕜 r (n + 1) x) := rfl

/-- **The comparison of the cohomology of the torus with the exterior power of the dual is natural**
in the covering space: pullback along a map of lattices corresponds to the exterior power of the
transpose. -/
theorem periodicCohomologyDualEquiv_naturality {p : 𝕜} (hp : p ≠ 0)
    (T : (Fin r → 𝕜) →L[𝕜] (Fin s → 𝕜))
    (hT : ∀ l : Fin r, T (p • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) ∈ periodLattice p s) (n : ℕ)
    (x : ⋀[𝕜]^(n + 1) (Module.Dual 𝕜 (Fin s → 𝕜))) :
    periodicCohomologyMap p T hT n (periodicCohomologyDualEquiv hp s n x) =
      periodicCohomologyDualEquiv hp r n
        (exteriorPower.map (n + 1) ((T : (Fin r → 𝕜) →ₗ[𝕜] _).dualMap) x) := by
  rw [periodicCohomologyDualEquiv_apply, periodicCohomologyDualEquiv_apply,
    periodicCohomologyMap_constantClass, constantFormOfExterior_map_dualMap]

end CohomologyComparison

end GaloisForLFunctions.HTGeometry
