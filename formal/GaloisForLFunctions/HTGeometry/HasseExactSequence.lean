import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Algebra.Exact.Basic

/-!
# Generic Hasse quotient interface

An exact local--global sequence with surjective obstruction map canonically identifies local data
modulo globally induced data with the obstruction target.  Additive and linear versions also expose
the local congruence criterion and representative existence with uniqueness modulo the global
range.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exactness plus right-surjectivity identifies local data modulo globally induced data with the
obstruction target. -/
noncomputable def addHasseQuotientEquiv
    {G L O : Type*} [AddCommGroup G] [AddCommGroup L] [AddCommGroup O]
    (global : G →+ L) (obstruction : L →+ O)
    (hexact : Function.Exact global obstruction)
    (hsurj : Function.Surjective obstruction) :
    (L ⧸ global.range) ≃+ O :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (AddMonoidHom.exact_iff.mp hexact).symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective obstruction hsurj)

@[simp] theorem addHasseQuotientEquiv_mk
    {G L O : Type*} [AddCommGroup G] [AddCommGroup L] [AddCommGroup O]
    (global : G →+ L) (obstruction : L →+ O)
    (hexact : Function.Exact global obstruction)
    (hsurj : Function.Surjective obstruction) (x : L) :
    addHasseQuotientEquiv global obstruction hexact hsurj
        (QuotientAddGroup.mk x) = obstruction x := by
  simp only [addHasseQuotientEquiv, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk]
  rfl

/-- Two local data differ by globally induced data exactly when their obstruction values agree. -/
theorem addHasse_congr_iff
    {G L O : Type*} [AddCommGroup G] [AddCommGroup L] [AddCommGroup O]
    (global : G →+ L) (obstruction : L →+ O)
    (hexact : Function.Exact global obstruction) (x y : L) :
    x - y ∈ global.range ↔ obstruction x = obstruction y := by
  rw [← AddMonoidHom.exact_iff.mp hexact]
  change obstruction (x - y) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- Every obstruction value has a local representative, unique modulo globally induced data. -/
theorem addHasse_exists_unique_mod_global
    {G L O : Type*} [AddCommGroup G] [AddCommGroup L] [AddCommGroup O]
    (global : G →+ L) (obstruction : L →+ O)
    (hexact : Function.Exact global obstruction)
    (hsurj : Function.Surjective obstruction) (o : O) :
    ∃ x : L, obstruction x = o ∧
      ∀ y : L, obstruction y = o ↔ y - x ∈ global.range := by
  obtain ⟨x, hx⟩ := hsurj o
  refine ⟨x, hx, fun y => ?_⟩
  simpa only [hx] using (addHasse_congr_iff global obstruction hexact y x).symm

/-- Linear exactness plus right-surjectivity identifies local data modulo globally induced data
with the obstruction target. -/
noncomputable def linearHasseQuotientEquiv
    {𝕜 G L O : Type*} [Field 𝕜]
    [AddCommGroup G] [Module 𝕜 G]
    [AddCommGroup L] [Module 𝕜 L]
    [AddCommGroup O] [Module 𝕜 O]
    (global : G →ₗ[𝕜] L) (obstruction : L →ₗ[𝕜] O)
    (hexact : Function.Exact global obstruction)
    (hsurj : Function.Surjective obstruction) :
    (L ⧸ LinearMap.range global) ≃ₗ[𝕜] O :=
  (Submodule.quotEquivOfEq _ _
    (LinearMap.exact_iff.mp hexact).symm).trans
      (LinearMap.quotKerEquivOfSurjective obstruction hsurj)

@[simp] theorem linearHasseQuotientEquiv_mk
    {𝕜 G L O : Type*} [Field 𝕜]
    [AddCommGroup G] [Module 𝕜 G]
    [AddCommGroup L] [Module 𝕜 L]
    [AddCommGroup O] [Module 𝕜 O]
    (global : G →ₗ[𝕜] L) (obstruction : L →ₗ[𝕜] O)
    (hexact : Function.Exact global obstruction)
    (hsurj : Function.Surjective obstruction) (x : L) :
    linearHasseQuotientEquiv global obstruction hexact hsurj
        (Submodule.Quotient.mk x) = obstruction x := by
  simp [linearHasseQuotientEquiv]

/-- Linear local data are congruent modulo the global range exactly when their obstruction values
agree. -/
theorem linearHasse_congr_iff
    {𝕜 G L O : Type*} [Field 𝕜]
    [AddCommGroup G] [Module 𝕜 G]
    [AddCommGroup L] [Module 𝕜 L]
    [AddCommGroup O] [Module 𝕜 O]
    (global : G →ₗ[𝕜] L) (obstruction : L →ₗ[𝕜] O)
    (hexact : Function.Exact global obstruction) (x y : L) :
    x - y ∈ LinearMap.range global ↔ obstruction x = obstruction y := by
  rw [← LinearMap.exact_iff.mp hexact]
  change obstruction (x - y) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- Every linear obstruction value has a local representative, unique modulo the global range. -/
theorem linearHasse_exists_unique_mod_global
    {𝕜 G L O : Type*} [Field 𝕜]
    [AddCommGroup G] [Module 𝕜 G]
    [AddCommGroup L] [Module 𝕜 L]
    [AddCommGroup O] [Module 𝕜 O]
    (global : G →ₗ[𝕜] L) (obstruction : L →ₗ[𝕜] O)
    (hexact : Function.Exact global obstruction)
    (hsurj : Function.Surjective obstruction) (o : O) :
    ∃ x : L, obstruction x = o ∧
      ∀ y : L, obstruction y = o ↔ y - x ∈ LinearMap.range global := by
  obtain ⟨x, hx⟩ := hsurj o
  refine ⟨x, hx, fun y => ?_⟩
  simpa only [hx] using (linearHasse_congr_iff global obstruction hexact y x).symm

end

end GaloisForLFunctions.HTGeometry
