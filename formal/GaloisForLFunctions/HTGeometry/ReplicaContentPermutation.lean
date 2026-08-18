import GaloisForLFunctions.HTGeometry.SymmetricReplicaProjector

/-!
# Content classes are permutation orbits, and the symmetric projector is central

Two ordered replica coordinates carry the same content exactly when each letter occupies the same
number of slots in both, and that is exactly when one is a slot permutation of the other: matching
the fibres letter by letter and gluing the resulting bijections produces the permutation.

A function of the ordered coordinate that depends only on the content is a symmetric vector.  Every
replica power of a one-copy matrix preserves the symmetric vectors, because reindexing both the
summation coordinate and the product over slots by the same permutation returns the original sum.
Applying that to a matrix and to its adjoint makes the symmetric projector commute with every
replica power.
-/

open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

noncomputable section

section Content

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem count_symTupleIndex (r : ℕ) (x : Fin r → α) (a : α) :
    Multiset.count a ((symTupleIndex r x : Sym α r) : Multiset α)
      = Fintype.card {i : Fin r // x i = a} := by
  classical
  have hval : ((symTupleIndex r x : Sym α r) : Multiset α)
      = Multiset.map x (Finset.univ : Finset (Fin r)).val := by
    rw [Fin.univ_val_map]
    rfl
  rw [hval, Multiset.count_map, Fintype.card_subtype]
  simp only [Finset.card, Finset.filter_val]
  congr 1
  exact Multiset.filter_congr fun i _ => by simp [eq_comm]

theorem symTupleIndex_eq_iff_card (r : ℕ) (x y : Fin r → α) :
    symTupleIndex r x = symTupleIndex r y ↔
      ∀ a : α, Fintype.card {i : Fin r // x i = a} = Fintype.card {i : Fin r // y i = a} := by
  constructor
  · intro h a
    rw [← count_symTupleIndex r x a, ← count_symTupleIndex r y a, h]
  · intro h
    refine Sym.coe_injective (Multiset.ext.mpr fun a => ?_)
    rw [count_symTupleIndex r x a, count_symTupleIndex r y a, h a]

/-- **Content classes are permutation orbits.**  Equal contents produce a slot permutation. -/
theorem exists_perm_of_symTupleIndex_eq (r : ℕ) {x y : Fin r → α}
    (h : symTupleIndex r x = symTupleIndex r y) :
    ∃ sigma : Equiv.Perm (Fin r), y = x ∘ sigma := by
  classical
  have hcard := (symTupleIndex_eq_iff_card r x y).mp h
  have hfib : ∀ a : α, {i : Fin r // y i = a} ≃ {i : Fin r // x i = a} := fun a =>
    Fintype.equivOfCardEq (hcard a).symm
  refine ⟨(Equiv.sigmaFiberEquiv y).symm.trans
    ((Equiv.sigmaCongrRight hfib).trans (Equiv.sigmaFiberEquiv x)), ?_⟩
  funext i
  have hstep : x (((Equiv.sigmaFiberEquiv y).symm.trans
      ((Equiv.sigmaCongrRight hfib).trans (Equiv.sigmaFiberEquiv x))) i) = y i := by
    simp only [Equiv.trans_apply, Equiv.sigmaFiberEquiv, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
      Equiv.sigmaCongrRight_apply]
    exact (hfib (y i) ⟨i, rfl⟩).2
  exact hstep.symm

theorem symTupleIndex_comp_perm (r : ℕ) (x : Fin r → α) (sigma : Equiv.Perm (Fin r)) :
    symTupleIndex r (x ∘ sigma) = symTupleIndex r x := by
  refine Sym.coe_injective ?_
  show ((List.ofFn (x ∘ sigma) : List α) : Multiset α) = ((List.ofFn x : List α) : Multiset α)
  exact Multiset.coe_eq_coe.mpr (Equiv.Perm.ofFn_comp_perm sigma x)

end Content

section Symmetric

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A vector on ordered replica coordinates that depends only on the content. -/
def IsClassConstant (r : ℕ) (v : (Fin r → α) → ℂ) : Prop :=
  ∀ x y : Fin r → α, symTupleIndex r x = symTupleIndex r y → v x = v y

theorem isClassConstant_pure (r : ℕ) (psi : α → ℂ) :
    IsClassConstant r (finitePureTensorPower r psi) :=
  fun _ _ h => finitePureTensorPower_congr r psi h

theorem isClassConstant_symReplicaProjection_col (r : ℕ) (y : Fin r → α) :
    IsClassConstant r fun z => symReplicaProjection (α := α) r z y := by
  intro z z' h
  show symReplicaProjection (α := α) r z y = symReplicaProjection (α := α) r z' y
  rw [symReplicaProjection_apply, symReplicaProjection_apply, h, symClass_eq_of_index_eq r h]

theorem symReplicaProjection_mulVec_of_classConstant (r : ℕ) {v : (Fin r → α) → ℂ}
    (hv : IsClassConstant r v) :
    (symReplicaProjection (α := α) r).mulVec v = v := by
  funext x
  rw [Matrix.mulVec, dotProduct]
  have hterm : ∀ z : Fin r → α,
      symReplicaProjection (α := α) r x z * v z =
        if symTupleIndex r z = symTupleIndex r x then
          (((symClass r x).card : ℂ))⁻¹ * v x else 0 := by
    intro z
    rw [symReplicaProjection_apply]
    by_cases hz : symTupleIndex r z = symTupleIndex r x
    · rw [if_pos hz.symm, if_pos hz, hv z x hz]
    · rw [if_neg fun hh => hz hh.symm, if_neg hz, zero_mul]
  rw [Finset.sum_congr rfl fun z _ => hterm z, ← Finset.sum_filter]
  show (∑ _z ∈ symClass r x, (((symClass r x).card : ℂ))⁻¹ * v x) = _
  rw [Finset.sum_const, nsmul_eq_mul, ← mul_assoc, mul_inv_cancel₀ (symClass_card_ne_zero r x),
    one_mul]

/-- **Replica powers preserve the symmetric vectors.** -/
theorem isClassConstant_mulVec_replicaTensorPower (r : ℕ) (A : Matrix α α ℂ)
    {v : (Fin r → α) → ℂ} (hv : IsClassConstant r v) :
    IsClassConstant r ((replicaTensorPowerMatrix r A).mulVec v) := by
  intro x x' h
  obtain ⟨sigma, hsig⟩ := exists_perm_of_symTupleIndex_eq r h
  let e : (Fin r → α) ≃ (Fin r → α) :=
    { toFun := fun f => f ∘ sigma
      invFun := fun f => f ∘ sigma.symm
      left_inv := fun f => by funext i; simp
      right_inv := fun f => by funext i; simp }
  have he : ∀ f : Fin r → α, e f = f ∘ sigma := fun _ => rfl
  rw [Matrix.mulVec, Matrix.mulVec, dotProduct, dotProduct,
    ← Equiv.sum_comp e (fun y => replicaTensorPowerMatrix r A x' y * v y)]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [he y]
  have hvy : v (y ∘ sigma) = v y := hv _ _ (symTupleIndex_comp_perm r y sigma)
  rw [hvy]
  congr 1
  show (∏ i, A (x i) (y i)) = ∏ i, A (x' i) ((y ∘ sigma) i)
  rw [hsig]
  exact (Fintype.prod_equiv sigma (fun i => A (x (sigma i)) (y (sigma i)))
    (fun i => A (x i) (y i)) fun _ => rfl).symm

/-- **The symmetric projector is central for replica powers.** -/
theorem symReplicaProjection_commute (r : ℕ) (A : Matrix α α ℂ) :
    symReplicaProjection (α := α) r * replicaTensorPowerMatrix r A
      = replicaTensorPowerMatrix r A * symReplicaProjection (α := α) r := by
  have hstep : ∀ B : Matrix α α ℂ,
      replicaTensorPowerMatrix r B * symReplicaProjection (α := α) r
        = symReplicaProjection (α := α) r *
            (replicaTensorPowerMatrix r B * symReplicaProjection (α := α) r) := by
    intro B
    funext x y
    have hcol : IsClassConstant r
        ((replicaTensorPowerMatrix r B).mulVec
          fun z => symReplicaProjection (α := α) r z y) :=
      isClassConstant_mulVec_replicaTensorPower r B
        (isClassConstant_symReplicaProjection_col r y)
    have hfix := symReplicaProjection_mulVec_of_classConstant r hcol
    exact (congrFun hfix x).symm
  have h1 := hstep A
  have h2 := hstep Aᴴ
  have h3 : symReplicaProjection (α := α) r * replicaTensorPowerMatrix r A
      = (symReplicaProjection (α := α) r * replicaTensorPowerMatrix r A) *
          symReplicaProjection (α := α) r := by
    have h := congrArg Matrix.conjTranspose h2
    simpa [Matrix.conjTranspose_mul, replicaTensorPowerMatrix_conjTranspose,
      symReplicaProjection_conjTranspose, Matrix.mul_assoc] using h
  calc symReplicaProjection (α := α) r * replicaTensorPowerMatrix r A
      = (symReplicaProjection (α := α) r * replicaTensorPowerMatrix r A) *
          symReplicaProjection (α := α) r := h3
    _ = symReplicaProjection (α := α) r *
          (replicaTensorPowerMatrix r A * symReplicaProjection (α := α) r) := by
        rw [Matrix.mul_assoc]
    _ = replicaTensorPowerMatrix r A * symReplicaProjection (α := α) r := h1.symm

end Symmetric

end

end GaloisForLFunctions.HTGeometry
