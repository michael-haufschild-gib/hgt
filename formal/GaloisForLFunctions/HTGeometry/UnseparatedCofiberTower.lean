import Mathlib.Analysis.Normed.Group.Quotient
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Unseparated cofibers and quotient towers

For a linear source map `T : E → F`, the algebraic cokernel `F / range T` remembers two
different obstructions.  The classes coming from `closure (range T) / range T` are invisible
after Hausdorff separation; the quotient `F / closure (range T)` is the separated remainder.
This module makes that distinction exact without assuming that the source range is closed.

For a tower of discarded layers it also identifies every transition kernel and both common
kernels: the algebraic tower reconstructs modulo `⋂ i, R i`, whereas the separated tower
reconstructs only modulo `⋂ i, closure (R i)`.  These statements are the typed common calculus
needed to compare dense factorial reporters, nonclosed multiple-Gamma filtrations, and closed
compact-operator quotients without identifying their genuinely different source classes.

All statements are unconditional elementary functional analysis.  No completeness assumption
is required: the distinction is already present for seminormed source and receiver spaces.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u v w x

variable {𝕜 : Type u} {E : Type v} {F : Type w}
variable [NontriviallyNormedField 𝕜]
variable [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable [SeminormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- The algebraic, generally non-Hausdorff, cokernel of a source map. -/
abbrev unseparatedCofiber (T : E →ₗ[𝕜] F) := F ⧸ LinearMap.range T

/-- The Hausdorff-separated cokernel obtained by closing the source range. -/
abbrev separatedCofiber (T : E →ₗ[𝕜] F) :=
  F ⧸ (LinearMap.range T).topologicalClosure

/-- The part of the algebraic cokernel killed by Hausdorff separation.  It is canonically
`closure (range T) / range T`, represented inside `F / range T`. -/
def unseparatedCofiberNullPart (T : E →ₗ[𝕜] F) :
    Submodule 𝕜 (unseparatedCofiber T) :=
  (LinearMap.range T).topologicalClosure.map (LinearMap.range T).mkQ

/-- The canonical Hausdorff-separation map on a source cokernel. -/
def unseparatedCofiberToSeparated (T : E →ₗ[𝕜] F) :
    unseparatedCofiber T →ₗ[𝕜] separatedCofiber T :=
  Submodule.factor (LinearMap.range T).le_topologicalClosure

@[simp]
theorem unseparatedCofiberToSeparated_mkQ (T : E →ₗ[𝕜] F) (y : F) :
    unseparatedCofiberToSeparated T ((LinearMap.range T).mkQ y) =
      (LinearMap.range T).topologicalClosure.mkQ y :=
  rfl

/-- **Unseparated cofiber exactness.**  The kernel of Hausdorff separation is precisely the
closure-born null part. -/
theorem ker_unseparatedCofiberToSeparated (T : E →ₗ[𝕜] F) :
    LinearMap.ker (unseparatedCofiberToSeparated T) =
      unseparatedCofiberNullPart T := by
  simpa only [unseparatedCofiberToSeparated, unseparatedCofiberNullPart] using!
    Submodule.ker_mapQ (LinearMap.range T)
      (LinearMap.range T).topologicalClosure LinearMap.id
      (by simpa using (LinearMap.range T).le_topologicalClosure)

/-- Hausdorff separation loses only the null part: every separated class has an algebraic
representative. -/
theorem unseparatedCofiberToSeparated_surjective (T : E →ₗ[𝕜] F) :
    Function.Surjective (unseparatedCofiberToSeparated T) := by
  exact Submodule.factor_surjective (LinearMap.range T).le_topologicalClosure

/-- There is no closure-born null defect exactly when the source range is closed. -/
theorem unseparatedCofiberNullPart_eq_bot_iff_isClosed (T : E →ₗ[𝕜] F) :
    unseparatedCofiberNullPart T = ⊥ ↔
      IsClosed (LinearMap.range T : Set F) := by
  constructor
  · intro hnull
    have hle : (LinearMap.range T).topologicalClosure ≤ LinearMap.range T := by
      intro y hy
      have hmap :
          (LinearMap.range T).mkQ y ∈ unseparatedCofiberNullPart T := by
        exact ⟨y, hy, rfl⟩
      rw [hnull] at hmap
      exact (Submodule.Quotient.mk_eq_zero (LinearMap.range T)).mp hmap
    have heq :
        (LinearMap.range T).topologicalClosure = LinearMap.range T :=
      le_antisymm hle (LinearMap.range T).le_topologicalClosure
    rw [← heq]
    exact Submodule.isClosed_topologicalClosure _
  · intro hclosed
    rw [unseparatedCofiberNullPart,
      hclosed.submodule_topologicalClosure_eq]
    exact Submodule.mkQ_map_self _

/-- The closure-born null part fills the whole algebraic cokernel exactly when the source range
is dense.  This is the pure-null phase once the algebraic cokernel itself is nonzero. -/
theorem unseparatedCofiberNullPart_eq_top_iff_dense (T : E →ₗ[𝕜] F) :
    unseparatedCofiberNullPart T = ⊤ ↔
      (LinearMap.range T).topologicalClosure = ⊤ := by
  constructor
  · intro hnull
    apply top_unique
    intro y _
    have hclass :
        (LinearMap.range T).mkQ y ∈ unseparatedCofiberNullPart T := by
      rw [hnull]
      trivial
    obtain ⟨z, hz, hzy⟩ := hclass
    have hdiffQ : (LinearMap.range T).mkQ (y - z) = 0 := by
      rw [map_sub, ← hzy]
      simp
    have hdiff : y - z ∈ LinearMap.range T :=
      (Submodule.Quotient.mk_eq_zero (LinearMap.range T)).mp hdiffQ
    have hdiffClosure :
        y - z ∈ (LinearMap.range T).topologicalClosure :=
      (LinearMap.range T).le_topologicalClosure hdiff
    convert (LinearMap.range T).topologicalClosure.add_mem hz hdiffClosure using 1
    abel
  · intro hclosure
    rw [unseparatedCofiberNullPart, hclosure, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (Submodule.mkQ_surjective _)

/-- The separated remainder is nontrivial exactly when the closed source range is proper. -/
theorem separatedCofiber_nontrivial_iff (T : E →ₗ[𝕜] F) :
    Nontrivial (separatedCofiber T) ↔
      (LinearMap.range T).topologicalClosure ≠ ⊤ :=
  Submodule.Quotient.nontrivial_iff

/-! ## Cofinal quotient towers -/

variable {ι : Type x}

/-- The transition from a finer quotient `F / P` to a coarser quotient `F / Q`. -/
def quotientTowerTransition (P Q : Submodule 𝕜 F) (hPQ : P ≤ Q) :
    (F ⧸ P) →ₗ[𝕜] (F ⧸ Q) :=
  Submodule.factor hPQ

@[simp]
theorem quotientTowerTransition_mkQ
    (P Q : Submodule 𝕜 F) (hPQ : P ≤ Q) (y : F) :
    quotientTowerTransition P Q hPQ (P.mkQ y) = Q.mkQ y :=
  rfl

/-- **Transition-layer law.**  The kernel added between two quotient levels is exactly `Q/P`,
represented as the image of `Q` in `F/P`. -/
theorem ker_quotientTowerTransition
    (P Q : Submodule 𝕜 F) (hPQ : P ≤ Q) :
    LinearMap.ker (quotientTowerTransition P Q hPQ) = Q.map P.mkQ := by
  simpa [quotientTowerTransition] using
    Submodule.ker_mapQ P Q LinearMap.id (by simpa using hPQ)

/-- Every quotient-tower transition is algebraically surjective. -/
theorem quotientTowerTransition_surjective
    (P Q : Submodule 𝕜 F) (hPQ : P ≤ Q) :
    Function.Surjective (quotientTowerTransition P Q hPQ) := by
  exact Submodule.factor_surjective hPQ

/-- Simultaneous observation in every algebraic quotient of a tower. -/
def quotientTowerObservation (R : ι → Submodule 𝕜 F) :
    F →ₗ[𝕜] (∀ i, F ⧸ R i) where
  toFun y i := (R i).mkQ y
  map_add' y z := by
    funext i
    exact map_add (R i).mkQ y z
  map_smul' c y := by
    funext i
    exact map_smul (R i).mkQ c y

@[simp]
theorem quotientTowerObservation_apply
    (R : ι → Submodule 𝕜 F) (y : F) (i : ι) :
    quotientTowerObservation R y i = (R i).mkQ y :=
  rfl

/-- **Algebraic tower reconstruction.**  A vector is invisible at every quotient level exactly
when it lies in the raw intersection of all discarded layers. -/
theorem ker_quotientTowerObservation (R : ι → Submodule 𝕜 F) :
    LinearMap.ker (quotientTowerObservation R) = ⨅ i, R i := by
  ext y
  change quotientTowerObservation R y = 0 ↔ y ∈ ⨅ i, R i
  constructor
  · intro hy
    apply (Submodule.mem_iInf R).mpr
    intro i
    apply (Submodule.Quotient.mk_eq_zero (R i)).mp
    exact congrFun hy i
  · intro hy
    funext i
    exact (Submodule.Quotient.mk_eq_zero (R i)).mpr
      ((Submodule.mem_iInf R).mp hy i)

/-- Simultaneous observation after Hausdorff-separating every quotient level. -/
def separatedQuotientTowerObservation (R : ι → Submodule 𝕜 F) :
    F →ₗ[𝕜] (∀ i, F ⧸ (R i).topologicalClosure) :=
  quotientTowerObservation (fun i ↦ (R i).topologicalClosure)

@[simp]
theorem separatedQuotientTowerObservation_apply
    (R : ι → Submodule 𝕜 F) (y : F) (i : ι) :
    separatedQuotientTowerObservation R y i =
      (R i).topologicalClosure.mkQ y :=
  rfl

/-- **Separated tower reconstruction.**  Levelwise Hausdorff separation reconstructs only modulo
the intersection of the closed layers.  The possible gap from the raw intersection is therefore
explicit and cannot be erased by an untyped inverse-limit slogan. -/
theorem ker_separatedQuotientTowerObservation (R : ι → Submodule 𝕜 F) :
    LinearMap.ker (separatedQuotientTowerObservation R) =
      ⨅ i, (R i).topologicalClosure := by
  exact ker_quotientTowerObservation (fun i ↦ (R i).topologicalClosure)

end

end GaloisForLFunctions.HTGeometry
