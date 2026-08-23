import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.HTGeometry.ShilovEnvelopeCorrelationLaw

/-!
# Hasse classification for Shilov boundary migration

For a tower with surjective bonding maps, relational local classes modulo coherent boundary
classes are exactly the degree-one migration obstruction.  The same exactness detects congruence
without a surjectivity condition.
-/

namespace GaloisForLFunctions.HTGeometry
namespace BoundaryMigration

universe u v

variable {𝕜 : Type u} [Field 𝕜]
variable (A : ℕ → Type v)
variable [∀ n, AddCommGroup (A n)] [∀ n, Module 𝕜 (A n)]

noncomputable section

/-- Relational local classes modulo coherent boundary classes classify the migration
obstruction. -/
noncomputable def localMigrationHasseQuotientEquiv
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hsurj : ∀ n, Function.Surjective (bond n)) :
    (RelationalClassSpace A bond J ⧸
      LinearMap.range (localMigrationComparison A bond J)) ≃ₗ[𝕜]
        MigrationCohomologyOne A bond J :=
  linearHasseQuotientEquiv
    (localMigrationComparison A bond J) (migrationConnectingMap A bond J)
    (localMigrationSequence_exact A bond J)
    (migrationConnectingMap_surjective A bond J hsurj)

@[simp] theorem localMigrationHasseQuotientEquiv_mk
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hsurj : ∀ n, Function.Surjective (bond n))
    (x : RelationalClassSpace A bond J) :
    localMigrationHasseQuotientEquiv A bond J hsurj (Submodule.Quotient.mk x) =
      migrationConnectingMap A bond J x := by
  simp [localMigrationHasseQuotientEquiv]

/-- Local relational classes are congruent modulo coherent boundary classes exactly when their
migration obstruction agrees. -/
theorem localMigration_congr_hasse_iff
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (x y : RelationalClassSpace A bond J) :
    x - y ∈ LinearMap.range (localMigrationComparison A bond J) ↔
      migrationConnectingMap A bond J x = migrationConnectingMap A bond J y :=
  linearHasse_congr_iff
    (localMigrationComparison A bond J) (migrationConnectingMap A bond J)
    (localMigrationSequence_exact A bond J) x y

/-- Every migration obstruction has a relational representative, unique modulo coherent boundary
classes. -/
theorem localMigration_exists_unique_mod_boundary
    (bond : ∀ n, A (n + 1) →ₗ[𝕜] A n)
    (J : ∀ n, Submodule 𝕜 (A n))
    (hsurj : ∀ n, Function.Surjective (bond n))
    (o : MigrationCohomologyOne A bond J) :
    ∃ x : RelationalClassSpace A bond J,
      migrationConnectingMap A bond J x = o ∧
      ∀ y : RelationalClassSpace A bond J,
        migrationConnectingMap A bond J y = o ↔
          y - x ∈ LinearMap.range (localMigrationComparison A bond J) :=
  linearHasse_exists_unique_mod_global
    (localMigrationComparison A bond J) (migrationConnectingMap A bond J)
    (localMigrationSequence_exact A bond J)
    (migrationConnectingMap_surjective A bond J hsurj) o

end
end BoundaryMigration
end GaloisForLFunctions.HTGeometry
