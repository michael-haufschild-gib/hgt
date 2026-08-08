import GaloisForLFunctions.HTGeometry.ReplicaProjectionIncidenceLaw
import Mathlib.Data.Sym.Card

/-!
# Symmetric replica rank law

Pure `r`-fold replicas occupy the symmetric, rather than full, tensor power.
This module realizes that statement in finite Hilbert coordinates without any
genericity, independence, nonzero-target, or distinct-label assumption.

Every ordered tensor coordinate factors through its unordered multiset.  The
resulting stars-and-bars factorization gives the exact universal cap

`dim span {v_c ^ tensor r} <= choose (d + r - 1) r`

whenever all occupied one-copy vectors lie in a subspace of dimension `d`.
The proof transports through an arbitrary subspace basis, so the bound depends
on occupied one-copy dimension rather than ambient Hilbert dimension.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Unordered multi-index of an ordered replica coordinate. -/
def symTupleIndex {α : Type*} [Fintype α]
    (r : ℕ) (x : Fin r → α) : Sym α r :=
  Sym.ofVector ⟨List.ofFn x, List.length_ofFn⟩

/-- Pull a coefficient function on unordered multi-indices back to ordered
tensor coordinates. -/
def symmetricTuplePullback {α : Type*} [Fintype α]
    (r : ℕ) :
    EuclideanSpace ℂ (Sym α r) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin r → α) where
  toFun g := WithLp.toLp 2 fun x => g (symTupleIndex r x)
  map_add' _ _ := by ext; rfl
  map_smul' _ _ := by ext; rfl

/-- Unordered monomial coefficient associated with one vector. -/
def symmetricPureCoefficient {α : Type*} [Fintype α]
    (r : ℕ) (v : α → ℂ) : EuclideanSpace ℂ (Sym α r) :=
  WithLp.toLp 2 fun s => (s.toMultiset.map v).prod

/-- Exact factorization of every pure tensor through its unordered
multi-index coefficients. -/
theorem symmetricTuplePullback_pure {α : Type*} [Fintype α]
    (r : ℕ) (v : α → ℂ) :
    symmetricTuplePullback r (symmetricPureCoefficient r v) =
      finitePureTensorPowerEuclidean r v := by
  ext x
  simp [symmetricTuplePullback, symmetricPureCoefficient, symTupleIndex,
    Sym.ofVector, finitePureTensorPowerEuclidean, finitePureTensorPower,
    List.prod_ofFn]

/-- Every occupied replica span is contained in the image of the unordered
coordinate pullback. -/
theorem replicaTargetSpan_le_range_symmetricTuplePullback
    {C α : Type*} [Fintype α] (r : ℕ) (target : C → α → ℂ) :
    replicaTargetSpan r target ≤ LinearMap.range (symmetricTuplePullback r) := by
  rw [replicaTargetSpan]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨c, rfl⟩
  exact ⟨symmetricPureCoefficient r (target c),
    symmetricTuplePullback_pure r (target c)⟩

/-- Ambient symmetric-power cap.  Duplicate and zero targets are harmless
because only the actual occupied span appears. -/
theorem finrank_replicaTargetSpan_le_sym_choose
    {C α : Type*} [Fintype α] (r : ℕ) (target : C → α → ℂ) :
    Module.finrank ℂ (replicaTargetSpan r target) ≤
      (Fintype.card α + r - 1).choose r := by
  classical
  calc
    Module.finrank ℂ (replicaTargetSpan r target) ≤
        Module.finrank ℂ (LinearMap.range (symmetricTuplePullback r)) :=
      Submodule.finrank_mono
        (replicaTargetSpan_le_range_symmetricTuplePullback r target)
    _ ≤ Module.finrank ℂ (EuclideanSpace ℂ (Sym α r)) :=
      LinearMap.finrank_range_le (symmetricTuplePullback r)
    _ = Fintype.card (Sym α r) := finrank_euclideanSpace
    _ = (Fintype.card α + r - 1).choose r := Sym.card_sym_eq_choose r

/-- Tensor product of a finite family of rectangular matrices. -/
def finiteTensorRectangularMatrix
    {R D E : Type*} [Fintype R] [Fintype D] [Fintype E]
    (M : R → Matrix E D ℂ) : Matrix (R → E) (R → D) ℂ :=
  fun x y => ∏ i, M i (x i) (y i)

/-- Tensor lift of a linear map between two possibly different finite
Euclidean spaces. -/
noncomputable def finiteTensorEuclideanMapBetween
    {β α : Type*} [Fintype β] [DecidableEq β]
    [Fintype α] [DecidableEq α] (r : ℕ)
    (A : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ α) :
    EuclideanSpace ℂ (Fin r → β) →ₗ[ℂ]
      EuclideanSpace ℂ (Fin r → α) := by
  classical
  let bβ := (EuclideanSpace.basisFun β ℂ).toBasis
  let bα := (EuclideanSpace.basisFun α ℂ).toBasis
  let brβ := (EuclideanSpace.basisFun (Fin r → β) ℂ).toBasis
  let brα := (EuclideanSpace.basisFun (Fin r → α) ℂ).toBasis
  exact Matrix.toLin brβ brα
    (finiteTensorRectangularMatrix fun _ : Fin r =>
      LinearMap.toMatrix bβ bα A)

/-- Rectangular tensor lifting is functorial on pure tensor powers. -/
theorem finiteTensorEuclideanMapBetween_pureTensor
    {β α : Type*} [Fintype β] [DecidableEq β]
    [Fintype α] [DecidableEq α] (r : ℕ)
    (A : EuclideanSpace ℂ β →ₗ[ℂ] EuclideanSpace ℂ α)
    (v : β → ℂ) :
    finiteTensorEuclideanMapBetween r A
        (finitePureTensorPowerEuclidean r v) =
      finitePureTensorPowerEuclidean r
        (fun x => A (WithLp.toLp 2 v) x) := by
  classical
  let bβ := (EuclideanSpace.basisFun β ℂ).toBasis
  let bα := (EuclideanSpace.basisFun α ℂ).toBasis
  let brβ := (EuclideanSpace.basisFun (Fin r → β) ℂ).toBasis
  let brα := (EuclideanSpace.basisFun (Fin r → α) ℂ).toBasis
  apply brα.repr.injective
  ext x
  rw [show finiteTensorEuclideanMapBetween r A =
      Matrix.toLin brβ brα
        (finiteTensorRectangularMatrix fun _ : Fin r =>
          LinearMap.toMatrix bβ bα A) by rfl]
  rw [Matrix.repr_toLin]
  simp only [brβ, brα]
  let M := LinearMap.toMatrix bβ bα A
  change (∑ y : Fin r → β,
      (∏ i, M (x i) (y i)) * ∏ i, v (y i)) =
    ∏ i, A (WithLp.toLp 2 v) (x i)
  simp_rw [← Finset.prod_mul_distrib]
  have hfactor := sum_pi_prod_complex
    (fun i (y : β) => M (x i) y * v y)
  rw [hfactor]
  apply Finset.prod_congr rfl
  intro i hi
  dsimp only [M]
  have hmul := LinearMap.toMatrix_mulVec_repr bβ bα A
    (WithLp.toLp 2 v)
  have hi' := congrFun hmul (x i)
  simpa [bβ, bα, Matrix.mulVec, dotProduct,
    EuclideanSpace.basisFun_repr] using hi'

/-- Coordinate synthesis from an arbitrary finite-dimensional occupied
one-copy subspace into the ambient Hilbert space. -/
noncomputable def subspaceCoordinateSynthesis
    {α : Type*} [Fintype α]
    (V : Submodule ℂ (EuclideanSpace ℂ α)) :
    EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) →ₗ[ℂ]
      EuclideanSpace ℂ α :=
  V.subtype.comp <|
    (Module.finBasis ℂ V).equivFun.symm.toLinearMap.comp <|
      (WithLp.linearEquiv 2 ℂ
        (Fin (Module.finrank ℂ V) → ℂ)).toLinearMap

/-- Coordinates of an ambient vector known to lie in the occupied subspace. -/
noncomputable def subspaceCoordinates
    {α : Type*} [Fintype α]
    (V : Submodule ℂ (EuclideanSpace ℂ α))
    (v : EuclideanSpace ℂ α) (hv : v ∈ V) :
    Fin (Module.finrank ℂ V) → ℂ :=
  (Module.finBasis ℂ V).equivFun ⟨v, hv⟩

/-- Coordinate synthesis exactly recovers the original occupied vector. -/
theorem subspaceCoordinateSynthesis_coordinates
    {α : Type*} [Fintype α]
    (V : Submodule ℂ (EuclideanSpace ℂ α))
    (v : EuclideanSpace ℂ α) (hv : v ∈ V) :
    subspaceCoordinateSynthesis V
        (WithLp.toLp 2 (subspaceCoordinates V v hv)) = v := by
  simp [subspaceCoordinateSynthesis, subspaceCoordinates]

/-- **Exact occupied-subspace symmetric replica rank law.**  If every target
lies in a one-copy subspace `V`, its complete replica span has dimension at
most `choose (dim V + r - 1) r`.  No enumeration factor appears. -/
theorem finrank_replicaTargetSpan_le_subspace_sym_choose
    {C α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (target : C → α → ℂ)
    (V : Submodule ℂ (EuclideanSpace ℂ α))
    (hV : ∀ c, WithLp.toLp 2 (target c) ∈ V) :
    Module.finrank ℂ (replicaTargetSpan r target) ≤
      (Module.finrank ℂ V + r - 1).choose r := by
  classical
  let d := Module.finrank ℂ V
  let A := subspaceCoordinateSynthesis V
  let L := (finiteTensorEuclideanMapBetween r A).comp
    (symmetricTuplePullback (α := Fin d) r)
  have hspan : replicaTargetSpan r target ≤ LinearMap.range L := by
    rw [replicaTargetSpan]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨c, rfl⟩
    let vc : Fin d → ℂ := subspaceCoordinates V
      (WithLp.toLp 2 (target c)) (hV c)
    refine ⟨symmetricPureCoefficient r vc, ?_⟩
    change finiteTensorEuclideanMapBetween r A
        (symmetricTuplePullback r (symmetricPureCoefficient r vc)) = _
    rw [symmetricTuplePullback_pure,
      finiteTensorEuclideanMapBetween_pureTensor]
    congr 2
    funext x
    change subspaceCoordinateSynthesis V (WithLp.toLp 2 vc) x = target c x
    have hs := subspaceCoordinateSynthesis_coordinates V
      (WithLp.toLp 2 (target c)) (hV c)
    exact congrArg (fun z : EuclideanSpace ℂ α => z x) hs
  calc
    Module.finrank ℂ (replicaTargetSpan r target) ≤
        Module.finrank ℂ (LinearMap.range L) :=
      Submodule.finrank_mono hspan
    _ ≤ Module.finrank ℂ (EuclideanSpace ℂ (Sym (Fin d) r)) :=
      LinearMap.finrank_range_le L
    _ = Fintype.card (Sym (Fin d) r) := finrank_euclideanSpace
    _ = (d + r - 1).choose r := by
      simpa using (Sym.card_sym_eq_choose (α := Fin d) r)
    _ = (Module.finrank ℂ V + r - 1).choose r := rfl

/-- Orthogonally projected occupied targets obey the symmetric-power cap of
the projection carrier itself. -/
theorem finrank_projectedReplicaTargetSpan_le_sym_choose
    {C α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (V : Submodule ℂ (EuclideanSpace ℂ α))
    (target : C → α → ℂ) :
    Module.finrank ℂ (replicaTargetSpan r (projectedReplicaTarget V target)) ≤
      (Module.finrank ℂ V + r - 1).choose r := by
  apply finrank_replicaTargetSpan_le_subspace_sym_choose r
    (projectedReplicaTarget V target) V
  intro c
  have hcoord :
      WithLp.toLp 2 (projectedReplicaTarget V target c) =
        V.starProjection (WithLp.toLp 2 (target c)) := by
    ext x
    rfl
  rw [hcoord]
  exact V.starProjection_apply_mem (WithLp.toLp 2 (target c))

/-- **Two simultaneous occupied-image caps.**  Projection of the complete
replica image cannot increase its original rank, and its rank is also bounded
by the exact symmetric-power dimension of the one-copy carrier. -/
theorem finrank_projectedReplicaTargetSpan_le_min
    {C α : Type*} [Fintype α] [DecidableEq α]
    (r : ℕ) (V : Submodule ℂ (EuclideanSpace ℂ α))
    (target : C → α → ℂ) :
    Module.finrank ℂ (replicaTargetSpan r (projectedReplicaTarget V target)) ≤
      min (Module.finrank ℂ (replicaTargetSpan r target))
        ((Module.finrank ℂ V + r - 1).choose r) := by
  exact le_min
    (finrank_projectedReplicaTargetSpan_le r V.starProjection.toLinearMap target)
    (finrank_projectedReplicaTargetSpan_le_sym_choose r V target)

end

end GaloisForLFunctions.HTGeometry
