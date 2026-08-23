import GaloisForLFunctions.HTGeometry.ShilovBoundaryMigrationDefect

/-!
# Shilov boundary Hasse obstruction quotient

The derived boundary sequence identifies compatible stagewise boundary classes modulo coherent
global boundary classes with the first derived inverse limit.  This is the quotient form of the
Shilov local-global obstruction law: local data modulo global image equals `lim¹`.
-/

namespace GaloisForLFunctions.HTGeometry.BoundaryMigration

universe u v

noncomputable section

variable {𝕜 : Type u} [Field 𝕜]
variable (A : ℕ → Type v)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module 𝕜 (A n)]

/-- Compatible local boundary classes modulo coherent global classes are exactly the derived
`lim¹` obstruction. -/
noncomputable def localBoundaryObstructionQuotientEquiv
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n)
    (hsurj : ∀ n, Function.Surjective (bond n)) :
    (CompatibleClassSpace A bond J ⧸
      LinearMap.range (localBoundaryComparison A bond J)) ≃ₗ[𝕜]
        DerivedLimitOne (fun n => J n) (restrictedBond A bond J hstable) :=
  (Submodule.quotEquivOfEq _ _
    (LinearMap.exact_iff.mp
      (localBoundaryDerivedSequence_exact A bond J hstable)).symm).trans
    (LinearMap.quotKerEquivOfSurjective
      (boundaryConnectingMap A bond J hstable)
      (boundaryConnectingMap_surjective A bond J hstable hsurj))

/-- The obstruction quotient equivalence is induced by the boundary connecting map. -/
@[simp] theorem localBoundaryObstructionQuotientEquiv_mk
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n)
    (hsurj : ∀ n, Function.Surjective (bond n))
    (c : CompatibleClassSpace A bond J) :
    localBoundaryObstructionQuotientEquiv A bond J hstable hsurj
        (Submodule.Quotient.mk c) =
      boundaryConnectingMap A bond J hstable c := by
  simp [localBoundaryObstructionQuotientEquiv]

end


end GaloisForLFunctions.HTGeometry.BoundaryMigration
