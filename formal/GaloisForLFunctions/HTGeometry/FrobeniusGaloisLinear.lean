import GaloisForLFunctions.HTGeometry.FrobeniusGaloisObservation
import GaloisForLFunctions.HTGeometry.SourceFaceObservationExcess
import GaloisForLFunctions.HTGeometry.UnseparatedCofiberTower

/-!
# Frobenius ambiguity of linear observations and quotients

The fixed-point consequences of arXiv:2609.09529, Proposition 3.13,
identify possible zero states with existing invisible-gauge submodules.
They also turn source-face and Hausdorff-separation criteria into exact
statements about all properties, without assuming injectivity or closed range.
-/
namespace GaloisForLFunctions.HTGeometry
open FrobeniusGalois

section Linear
variable {𝕜 M N : Type*} [Ring 𝕜] [AddCommGroup M] [Module 𝕜 M]
  [AddCommGroup N] [Module 𝕜 N]

/-- The possible zero state is exactly the invisible linear gauge. -/
theorem linearObservation_upper_zero (f : M →ₗ[𝕜] N) :
    upper f {0} = (LinearMap.ker f : Set M) := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    have hy' : y = 0 := hy
    rw [hy', map_zero] at he
    exact he.symm
  · intro hx
    exact ⟨0, rfl, (map_zero f).trans hx.symm⟩

/-- Every property is exact precisely when the linear kernel vanishes. -/
theorem linearObservation_all_exact_iff (f : M →ₗ[𝕜] N) :
    (∀ S : Set M, lower f S = upper f S) ↔ LinearMap.ker f = ⊥ := by
  rw [all_properties_exact_iff, LinearMap.ker_eq_bot]

/-- The invisible gauge itself is certain and possible at exactly the same states. -/
theorem linearObservation_kernel_fixed (f : M →ₗ[𝕜] N) :
    lower f (LinearMap.ker f : Set M) = (LinearMap.ker f : Set M) ∧
      upper f (LinearMap.ker f : Set M) = (LinearMap.ker f : Set M) := by
  rw [← linearObservation_upper_zero f, lower_upper, upper_idempotent]
  exact ⟨rfl, rfl⟩

/-- Quotienting the entire inverse image of the discarded target layer removes all ambiguity. -/
theorem maximalSourceFace_all_exact (f : M →ₗ[𝕜] N) (Q : Submodule 𝕜 N) :
    ∀ S : Set (M ⧸ Q.comap f),
      lower (sourceFaceQuotientObservation f (Q.comap f) Q le_rfl) S =
        upper (sourceFaceQuotientObservation f (Q.comap f) Q le_rfl) S := by
  apply (all_properties_exact_iff _).mpr
  exact (sourceFaceQuotientObservation_injective_iff f (Q.comap f) Q le_rfl).mpr le_rfl

variable {ι : Type*} {Nᵢ : ι → Type*}
variable [∀ i, AddCommGroup (Nᵢ i)] [∀ i, Module 𝕜 (Nᵢ i)]

/-- Possible zero observations are exactly the existing common invisible gauge. -/
theorem sourceFixedJoint_upper_zero (K : Submodule 𝕜 M) (R : ∀ i, M →ₗ[𝕜] Nᵢ i) :
    upper (sourceFixedJointObservation K R) {0} =
      ((sourceFixedJointInvisibleGauge K R).comap K.subtype : Set K) := by
  rw [linearObservation_upper_zero, ker_sourceFixedJointObservation]

/-- The common-kernel reconstruction law is universal exactness of properties. -/
theorem sourceFixedJoint_all_exact_iff (K : Submodule 𝕜 M) (R : ∀ i, M →ₗ[𝕜] Nᵢ i) :
    (∀ S : Set K, lower (sourceFixedJointObservation K R) S =
      upper (sourceFixedJointObservation K R) S) ↔
      sourceFixedJointInvisibleGauge K R = ⊥ := by
  rw [all_properties_exact_iff, sourceFixedJointObservation_injective_iff]
end Linear

section Topological
variable {𝕜 E F ι : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
  [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Hausdorff separation regards exactly the closure-born null classes as possibly zero. -/
theorem cofiberSeparation_upper_zero (T : E →ₗ[𝕜] F) :
    upper (unseparatedCofiberToSeparated T) {0} =
      (unseparatedCofiberNullPart T : Set (unseparatedCofiber T)) := by
  rw [linearObservation_upper_zero, ker_unseparatedCofiberToSeparated]

/-- Every algebraic-cokernel property survives Hausdorff separation exactly when range is closed. -/
theorem cofiberSeparation_all_exact_iff (T : E →ₗ[𝕜] F) :
    (∀ S : Set (unseparatedCofiber T),
      lower (unseparatedCofiberToSeparated T) S =
        upper (unseparatedCofiberToSeparated T) S) ↔
      IsClosed (LinearMap.range T : Set F) := by
  rw [linearObservation_all_exact_iff, ker_unseparatedCofiberToSeparated,
    unseparatedCofiberNullPart_eq_bot_iff_isClosed]

/-- The possible zero states of an algebraic quotient tower form its raw intersection. -/
theorem quotientTower_upper_zero (R : ι → Submodule 𝕜 F) :
    upper (quotientTowerObservation R) {0} = ((⨅ i, R i) : Set F) := by
  rw [linearObservation_upper_zero, ker_quotientTowerObservation]
  ext x
  simp

/-- Algebraic tower completeness is exactness of every property. -/
theorem quotientTower_all_exact_iff (R : ι → Submodule 𝕜 F) :
    (∀ S : Set F, lower (quotientTowerObservation R) S =
      upper (quotientTowerObservation R) S) ↔ (⨅ i, R i) = ⊥ := by
  rw [linearObservation_all_exact_iff, ker_quotientTowerObservation]

/-- Separated towers have the intersection of closed layers as their possible zero states. -/
theorem separatedQuotientTower_upper_zero (R : ι → Submodule 𝕜 F) :
    upper (separatedQuotientTowerObservation R) {0} =
      ((⨅ i, (R i).topologicalClosure) : Set F) := by
  rw [linearObservation_upper_zero, ker_separatedQuotientTowerObservation]
  ext x
  simp

/-- Closing every layer preserves all properties exactly when their closed intersection vanishes. -/
theorem separatedQuotientTower_all_exact_iff (R : ι → Submodule 𝕜 F) :
    (∀ S : Set F, lower (separatedQuotientTowerObservation R) S =
      upper (separatedQuotientTowerObservation R) S) ↔
      (⨅ i, (R i).topologicalClosure) = ⊥ := by
  rw [linearObservation_all_exact_iff, ker_separatedQuotientTowerObservation]
end Topological

end GaloisForLFunctions.HTGeometry
