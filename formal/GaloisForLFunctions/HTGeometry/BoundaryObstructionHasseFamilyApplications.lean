import GaloisForLFunctions.HTGeometry.HasseFamily
import GaloisForLFunctions.HTGeometry.ShilovBoundaryHasseQuotient
import GaloisForLFunctions.HTGeometry.ShilovMigrationHasse

/-!
# Boundary-obstruction Hasse-family applications

Inverse-system local--global principles: compatible boundary data modulo coherent global data are
detected by `lim¹`, while relational migration data modulo global comparison are detected by first
migration cohomology.
-/

namespace GaloisForLFunctions.HTGeometry.BoundaryMigration

universe u v

noncomputable section

variable {𝕜 : Type u} [Field 𝕜]
variable (A : ℕ → Type v)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module 𝕜 (A n)]

/-- The derived-limit obstruction is a complete coordinate for compatible local boundary classes
modulo coherent global classes. -/
noncomputable def localBoundaryObstructionHasseFamily
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hstable : ∀ n (x : A (n + 1)), x ∈ J (n + 1) → bond n x ∈ J n)
    (hsurj : ∀ n, Function.Surjective (bond n)) :=
  HasseFamily.ofEquivSingle
    (localBoundaryObstructionQuotientEquiv A bond J hstable hsurj).toEquiv

/-- First migration cohomology is a complete coordinate for relational local classes modulo the
coherent boundary comparison. -/
noncomputable def localMigrationObstructionHasseFamily
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hsurj : ∀ n, Function.Surjective (bond n)) :=
  HasseFamily.ofEquivSingle
    (localMigrationHasseQuotientEquiv A bond J hsurj).toEquiv

end
end GaloisForLFunctions.HTGeometry.BoundaryMigration
