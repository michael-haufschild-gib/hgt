import GaloisForLFunctions.HTGeometry.CompletedPseudoDiffOpLatticeBasis
import GaloisForLFunctions.HTGeometry.DifferentialVariationalProjectiveBuildingCarrier

/-!
# Linear frames of completed pseudodifferential lattices

Every full finitely generated lattice over the completed valuation ring has an integral basis of
the ambient rank.  Reindexing that basis by the ambient coordinates gives a completed-skew linear
frame whose image of the standard integral lattice is exactly the given lattice.

This is the vertex-transitivity input for arbitrary-lattice Cartan reduction.  It uses the actual
completed skew field and its actual valuation lattices.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]

/-- The image of the standard integral lattice under a completed-skew basis frame is the integral
span of that basis. -/
theorem map_standardCompletedPseudoDiffOpLattice_eq_span_basis
    (b : Module.Basis ι (CompletedPseudoDiffOp K)
      (ι → CompletedPseudoDiffOp K))
    (hspan : Submodule.span (CompletedPseudoDiffOpInteger (K := K))
      (Set.range b) = L) :
    (mapCompletedPseudoDiffOpLatticeLinear b.equivFun.symm
      (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι))).carrier = L := by
  classical
  ext y
  rw [mem_mapCompletedPseudoDiffOpLatticeLinear_iff]
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [← hspan]
    rw [← b.sum_repr (b.equivFun.symm x)]
    apply Submodule.sum_mem
    intro i _
    have hxi : x i ∈ CompletedPseudoDiffOpInteger (K := K) :=
      (mem_standardCompletedPseudoDiffOpLattice_iff x).1 hx i
    have hrepr : b.repr (b.equivFun.symm x) i = x i := by
      have h := b.equivFun.apply_symm_apply x
      exact congrFun h i
    let c : CompletedPseudoDiffOpInteger (K := K) := ⟨x i, hxi⟩
    have hb : b i ∈ Submodule.span (CompletedPseudoDiffOpInteger (K := K))
        (Set.range b) := Submodule.subset_span ⟨i, rfl⟩
    have hc := Submodule.smul_mem
      (Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range b)) c hb
    change (c : CompletedPseudoDiffOp K) • b i ∈
      Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range b) at hc
    convert hc using 1
    rw [hrepr]
  · intro hy
    let x : ι → CompletedPseudoDiffOp K := b.repr y
    have hxint : ∀ i, x i ∈ CompletedPseudoDiffOpInteger (K := K) := by
      rw [← hspan] at hy
      exact Submodule.span_induction
        (p := fun z _ => ∀ i, b.repr z i ∈ CompletedPseudoDiffOpInteger (K := K))
        (fun z hz i => by
          obtain ⟨j, rfl⟩ := hz
          by_cases hji : j = i
          · subst i
            simp
          · simp [hji])
        (by simp)
        (fun z w _ _ hz hw i => by
          have heq : b.repr (z + w) i = b.repr z i + b.repr w i :=
            congrArg (fun f => f i) (b.repr.map_add z w)
          rw [heq]
          exact add_mem (hz i) (hw i))
        (fun c z _ hz i => by
          have heq : b.repr (c • z) i =
              (c : CompletedPseudoDiffOp K) * b.repr z i := by
            change b.repr ((c : CompletedPseudoDiffOp K) • z) i = _
            exact congrArg (fun f => f i)
              (b.repr.map_smul (c : CompletedPseudoDiffOp K) z)
          rw [heq]
          exact mul_mem c.property (hz i))
        hy
    refine ⟨x, (mem_standardCompletedPseudoDiffOpLattice_iff x).2 hxint, ?_⟩
    exact b.equivFun.symm_apply_apply y

/-- Every completed pseudodifferential lattice has a completed-skew basis indexed by the ambient
coordinates whose integral span is exactly its carrier. -/
theorem exists_completedPseudoDiffOpLattice_integral_basis
    (L : CompletedPseudoDiffOpLattice K ι) :
    ∃ b : Module.Basis ι (CompletedPseudoDiffOp K) (ι → CompletedPseudoDiffOp K),
      Submodule.span (CompletedPseudoDiffOpInteger (K := K)) (Set.range b) = L.carrier := by
  classical
  obtain ⟨v, -, hspan, hindepD, hspanD⟩ :=
    exists_completedPseudoDiffOpLattice_full_rank_basis L
  let bFin : Module.Basis (Fin (Fintype.card ι)) (CompletedPseudoDiffOp K)
      (ι → CompletedPseudoDiffOp K) := Module.Basis.mk hindepD (le_of_eq hspanD.symm)
  let b : Module.Basis ι (CompletedPseudoDiffOp K) (ι → CompletedPseudoDiffOp K) :=
    bFin.reindex (Fintype.equivFin ι).symm
  have hbapply : ∀ i, b i = v (Fintype.equivFin ι i) := by
    intro i
    simp [b, bFin, Module.Basis.reindex_apply, Module.Basis.mk_apply]
  have hrange : Set.range b = Set.range v := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fintype.equivFin ι i, (hbapply i).symm⟩
    · rintro ⟨j, rfl⟩
      refine ⟨(Fintype.equivFin ι).symm j, ?_⟩
      rw [hbapply]
      simp
  refine ⟨b, ?_⟩
  rw [hrange]
  exact hspan

/-- Every completed pseudodifferential valuation lattice is a completed-skew linear image of the
standard lattice. -/
theorem exists_completedPseudoDiffOp_linearEquiv_map_standard
    (L : CompletedPseudoDiffOpLattice K ι) :
    ∃ e : (ι → CompletedPseudoDiffOp K) ≃ₗ[CompletedPseudoDiffOp K]
        (ι → CompletedPseudoDiffOp K),
      mapCompletedPseudoDiffOpLatticeLinear e
        (standardCompletedPseudoDiffOpLattice (K := K) (ι := ι)) = L := by
  classical
  obtain ⟨v, hindep, hspan, hindepD, hspanD⟩ :=
    exists_completedPseudoDiffOpLattice_full_rank_basis L
  let bFin : Module.Basis (Fin (Fintype.card ι)) (CompletedPseudoDiffOp K)
      (ι → CompletedPseudoDiffOp K) := Module.Basis.mk hindepD (le_of_eq hspanD.symm)
  let b : Module.Basis ι (CompletedPseudoDiffOp K) (ι → CompletedPseudoDiffOp K) :=
    bFin.reindex (Fintype.equivFin ι).symm
  have hbapply : ∀ i, b i = v (Fintype.equivFin ι i) := by
    intro i
    simp [b, bFin, Module.Basis.reindex_apply, Module.Basis.mk_apply]
  have hrange : Set.range b = Set.range v := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨Fintype.equivFin ι i, (hbapply i).symm⟩
    · rintro ⟨j, rfl⟩
      refine ⟨(Fintype.equivFin ι).symm j, ?_⟩
      rw [hbapply]
      simp
  have hspanb : Submodule.span (CompletedPseudoDiffOpInteger (K := K))
      (Set.range b) = L.carrier := by
    rw [hrange]
    exact hspan
  refine ⟨b.equivFun.symm, ?_⟩
  apply CompletedPseudoDiffOpLattice.ext
  exact map_standardCompletedPseudoDiffOpLattice_eq_span_basis b hspanb

end

end DiffOp

end GaloisForLFunctions.HTGeometry
