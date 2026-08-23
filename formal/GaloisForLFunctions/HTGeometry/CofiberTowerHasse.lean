import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.HTGeometry.UnseparatedCofiberTower

/-!
# Hasse quotients for cofiber separation and quotient towers

Hausdorff separation and nested quotient transitions are surjective obstruction maps with known
kernels.  Their quotient classifications distinguish closure-born algebraic ghosts from visible
classes and identify the exact layer discarded at each stage of a quotient tower.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w

variable {𝕜 : Type u} {E : Type v} {F : Type w}
variable [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- Inclusion of the closure-born null part followed by Hausdorff separation is exact. -/
theorem unseparatedCofiberHasse_functionExact (T : E →ₗ[𝕜] F) :
    Function.Exact (unseparatedCofiberNullPart T).subtype
      (unseparatedCofiberToSeparated T) := by
  rw [LinearMap.exact_iff, ker_unseparatedCofiberToSeparated,
    Submodule.range_subtype]

/-- Algebraic cofiber classes modulo closure-born ghosts are exactly separated cofiber classes. -/
noncomputable def unseparatedCofiberHasseQuotientEquiv (T : E →ₗ[𝕜] F) :
    (unseparatedCofiber T ⧸ unseparatedCofiberNullPart T) ≃ₗ[𝕜]
      separatedCofiber T :=
  (Submodule.quotEquivOfEq _ _
    (unseparatedCofiberNullPart T).range_subtype.symm).trans
    (linearHasseQuotientEquiv (unseparatedCofiberNullPart T).subtype
      (unseparatedCofiberToSeparated T) (unseparatedCofiberHasse_functionExact T)
      (unseparatedCofiberToSeparated_surjective T))

/-- Hausdorff separation induces the cofiber Hasse equivalence. -/
@[simp] theorem unseparatedCofiberHasseQuotientEquiv_mk
    (T : E →ₗ[𝕜] F) (x : unseparatedCofiber T) :
    unseparatedCofiberHasseQuotientEquiv T (Submodule.Quotient.mk x) =
      unseparatedCofiberToSeparated T x := by
  simp [unseparatedCofiberHasseQuotientEquiv]

/-- Two algebraic cofiber classes have the same separated image exactly when their difference is a
closure-born ghost. -/
theorem unseparatedCofiber_congr_hasse_iff
    (T : E →ₗ[𝕜] F) (x y : unseparatedCofiber T) :
    x - y ∈ unseparatedCofiberNullPart T ↔
      unseparatedCofiberToSeparated T x = unseparatedCofiberToSeparated T y := by
  rw [← (unseparatedCofiberNullPart T).range_subtype]
  exact
    linearHasse_congr_iff (unseparatedCofiberNullPart T).subtype
      (unseparatedCofiberToSeparated T) (unseparatedCofiberHasse_functionExact T) x y

/-- Every separated class has an algebraic representative, unique modulo closure-born ghosts. -/
theorem unseparatedCofiber_exists_unique_mod_nullPart
    (T : E →ₗ[𝕜] F) (z : separatedCofiber T) :
    ∃ x : unseparatedCofiber T, unseparatedCofiberToSeparated T x = z ∧
      ∀ y, unseparatedCofiberToSeparated T y = z ↔
        y - x ∈ unseparatedCofiberNullPart T := by
  rw [← (unseparatedCofiberNullPart T).range_subtype]
  exact
    linearHasse_exists_unique_mod_global (unseparatedCofiberNullPart T).subtype
      (unseparatedCofiberToSeparated T) (unseparatedCofiberHasse_functionExact T)
      (unseparatedCofiberToSeparated_surjective T) z

/-- A quotient-tower layer included in the finer quotient. -/
def quotientTowerLayerInclusion (P Q : Submodule 𝕜 F) : Q →ₗ[𝕜] (F ⧸ P) :=
  P.mkQ.comp Q.subtype

/-- The range of the layer inclusion is the image of the larger discarded submodule. -/
theorem range_quotientTowerLayerInclusion (P Q : Submodule 𝕜 F) :
    LinearMap.range (quotientTowerLayerInclusion P Q) = Q.map P.mkQ := by
  rw [quotientTowerLayerInclusion, LinearMap.range_comp, Submodule.range_subtype]

/-- The added layer is exactly the kernel of the transition to the coarser quotient. -/
theorem quotientTowerHasse_functionExact
    (P Q : Submodule 𝕜 F) (hPQ : P ≤ Q) :
    Function.Exact (quotientTowerLayerInclusion P Q)
      (quotientTowerTransition P Q hPQ) := by
  rw [LinearMap.exact_iff, ker_quotientTowerTransition,
    range_quotientTowerLayerInclusion]

/-- Quotienting a finer stage by the newly discarded layer gives the coarser stage. -/
noncomputable def quotientTowerHasseQuotientEquiv
    (P Q : Submodule 𝕜 F) (hPQ : P ≤ Q) :
    ((F ⧸ P) ⧸ Q.map P.mkQ) ≃ₗ[𝕜] (F ⧸ Q) :=
  (Submodule.quotEquivOfEq _ _
    (range_quotientTowerLayerInclusion P Q).symm).trans
    (linearHasseQuotientEquiv (quotientTowerLayerInclusion P Q)
      (quotientTowerTransition P Q hPQ) (quotientTowerHasse_functionExact P Q hPQ)
      (quotientTowerTransition_surjective P Q hPQ))

/-- Quotient-tower transition induces the layer Hasse equivalence. -/
@[simp] theorem quotientTowerHasseQuotientEquiv_mk
    (P Q : Submodule 𝕜 F) (hPQ : P ≤ Q) (x : F ⧸ P) :
    quotientTowerHasseQuotientEquiv P Q hPQ (Submodule.Quotient.mk x) =
      quotientTowerTransition P Q hPQ x := by
  simp [quotientTowerHasseQuotientEquiv]

/-- Two finer-stage classes have the same coarser image exactly when their difference comes from
the newly discarded layer. -/
theorem quotientTower_congr_hasse_iff
    (P Q : Submodule 𝕜 F) (hPQ : P ≤ Q) (x y : F ⧸ P) :
    x - y ∈ Q.map P.mkQ ↔
      quotientTowerTransition P Q hPQ x = quotientTowerTransition P Q hPQ y := by
  rw [← range_quotientTowerLayerInclusion P Q]
  exact
    linearHasse_congr_iff (quotientTowerLayerInclusion P Q)
      (quotientTowerTransition P Q hPQ) (quotientTowerHasse_functionExact P Q hPQ) x y

/-- Every coarser-stage class has a finer representative, unique modulo the discarded layer. -/
theorem quotientTower_exists_unique_mod_layer
    (P Q : Submodule 𝕜 F) (hPQ : P ≤ Q) (z : F ⧸ Q) :
    ∃ x : F ⧸ P, quotientTowerTransition P Q hPQ x = z ∧
      ∀ y, quotientTowerTransition P Q hPQ y = z ↔ y - x ∈ Q.map P.mkQ := by
  rw [← range_quotientTowerLayerInclusion P Q]
  exact
    linearHasse_exists_unique_mod_global (quotientTowerLayerInclusion P Q)
      (quotientTowerTransition P Q hPQ) (quotientTowerHasse_functionExact P Q hPQ)
      (quotientTowerTransition_surjective P Q hPQ) z

end

end GaloisForLFunctions.HTGeometry
