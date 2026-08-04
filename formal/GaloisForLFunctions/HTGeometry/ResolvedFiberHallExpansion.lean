import GaloisForLFunctions.HilbertMetric.SymmetricFockShadow

/-!
# Resolved-fibre Hall expansion

An injective family of coordinate resolvers cannot shrink any subspace when
its resolved outputs admit one injective assembly.  This isolates the exact
linear-algebra mechanism behind the two-replica mismatch proof: common-kernel
faithfulness is checked before the edge fibres are assembled, and independent
edge-defect sectors make that assembly faithful.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Resolved fibres whose assembled output is faithful cannot shrink any
subspace.  The assembly hypothesis packages independence of the output
fibres, while injectivity of the stacked resolver packages the common-kernel
condition. -/
theorem resolvedFiberAssembly_subspace_finrank
    {𝕜 X Z Y J : Type*}
    [DivisionRing 𝕜]
    [AddCommGroup X] [Module 𝕜 X]
    [AddCommGroup Z] [Module 𝕜 Z]
    [AddCommGroup Y] [Module 𝕜 Y]
    [Fintype J]
    [FiniteDimensional 𝕜 X] [FiniteDimensional 𝕜 Y]
    (P : J → X →ₗ[𝕜] Z)
    (E : J → Z →ₗ[𝕜] Y)
    (assemble : (J → Z) →ₗ[𝕜] Y)
    (hresolve : ∀ z, assemble z = ∑ j, E j (z j))
    (hP : Function.Injective (LinearMap.pi P))
    (hassemble : Function.Injective assemble)
    (U : Submodule 𝕜 X) (V : Submodule 𝕜 Y)
    (hUV : ∀ j x, x ∈ U → E j (P j x) ∈ V) :
    Module.finrank 𝕜 U ≤ Module.finrank 𝕜 V := by
  let raw : X →ₗ[𝕜] Y := assemble.comp (LinearMap.pi P)
  have hraw_mem : ∀ x : U, raw x ∈ V := by
    intro x
    dsimp [raw]
    rw [hresolve]
    exact Submodule.sum_mem V fun j _ => by
      simpa using hUV j x.1 x.2
  let F : U →ₗ[𝕜] V :=
    ((raw.domRestrict U).codRestrict V fun x => hraw_mem x)
  have hF : Function.Injective F := by
    intro x y hxy
    apply Subtype.ext
    apply hP
    apply hassemble
    exact congrArg Subtype.val hxy
  exact F.finrank_le_finrank_of_injective hF

end

end GaloisForLFunctions.HTGeometry
