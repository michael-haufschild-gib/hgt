import GaloisForLFunctions.HTGeometry.CDGAFreeCover

/-!
# Every differential graded module is covered by a semi-free one

Attaching, at stage `k`, the free cell on the cocycles of degree `k` with the trivial twist produces
a tower of free cells whose colimit maps onto the cocycles of every degree.  So every differential
graded module receives a comparison from a semi-free module which is surjective on cocycles, hence
on cohomology.

* `HTGeometry.coverTower` : the tower of free cells on the cocycles.
* `HTGeometry.coverColimMap` : the comparison from its colimit.
-/

universe w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type w} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  (P : CDGAModuleStructure A M)

/-- The base of the covering tower: the free cell on the cocycles of degree zero. -/
noncomputable def coverBase : CDGAModuleStructure A (FreeCellCarrier (R := R) X
    (cocycleCellCoeff P 0) 0) :=
  freeCellModule A (cocycleCellCoeff P 0) 0

/-- The cells of the covering tower: the free cell on the cocycles of each positive degree. -/
noncomputable def coverCell (i : ℕ) : CDGAModuleStructure A (FreeCellCarrier (R := R) X
    (cocycleCellCoeff P (i + 1)) (i + 1)) :=
  freeCellModule A (cocycleCellCoeff P (i + 1)) (i + 1)

/-- The cells are attached trivially: the tower is a direct sum. -/
noncomputable def coverTwist (i : ℕ)
    (S : CDGAModuleStructure A (towerCarrier (FreeCellCarrier (R := R) X (cocycleCellCoeff P 0) 0)
      (fun i => FreeCellCarrier (R := R) X (cocycleCellCoeff P (i + 1)) (i + 1)) i)) :
    CDGATwist S (coverCell P i) :=
  CDGATwist.zero S (coverCell P i)

/-- **The covering tower of free cells.** -/
noncomputable def coverTower : ∀ i,
    CDGAModuleStructure A (towerCarrier (FreeCellCarrier (R := R) X (cocycleCellCoeff P 0) 0)
      (fun i => FreeCellCarrier (R := R) X (cocycleCellCoeff P (i + 1)) (i + 1)) i) :=
  towerMod (coverBase P) (coverCell P) (coverTwist P)

/-- The comparison from each stage of the covering tower. -/
noncomputable def coverMap : ∀ i, CDGAModuleHom (coverTower P i) P
  | 0 => cocycleCover P 0
  | (i + 1) =>
      twistedExtend (coverMap i)
        (CDGATwistedLift.ofHom (coverMap i) (cocycleCover P (i + 1)))

theorem coverMap_step (i : ℕ) :
    (coverMap P (i + 1)).comp (towerStep (coverBase P) (coverCell P) (coverTwist P) i)
      = coverMap P i :=
  twistedExtend_comp_inl _ _

/-- The comparisons are compatible with the transitions of the tower. -/
theorem coverMap_trans {i j : ℕ} (hij : i ≤ j) (n : ℕ)
    (m : towerCarrier (FreeCellCarrier (R := R) X (cocycleCellCoeff P 0) 0)
      (fun i => FreeCellCarrier (R := R) X (cocycleCellCoeff P (i + 1)) (i + 1)) i n) :
    (coverMap P j).toFun n
        ((towerTrans (coverBase P) (coverCell P) (coverTwist P) i hij).toFun n m)
      = (coverMap P i).toFun n m := by
  induction j, hij using Nat.le_induction with
  | base => rw [towerTrans_self]; rfl
  | succ j hij ih =>
      rw [towerTrans_succ (coverBase P) (coverCell P) (coverTwist P) hij]
      show (coverMap P (j + 1)).toFun n
          ((towerStep (coverBase P) (coverCell P) (coverTwist P) j).toFun n
            ((towerTrans (coverBase P) (coverCell P) (coverTwist P) i hij).toFun n m))
        = (coverMap P i).toFun n m
      rw [show (coverMap P (j + 1)).toFun n
          ((towerStep (coverBase P) (coverCell P) (coverTwist P) j).toFun n
            ((towerTrans (coverBase P) (coverCell P) (coverTwist P) i hij).toFun n m))
        = (coverMap P j).toFun n
          ((towerTrans (coverBase P) (coverCell P) (coverTwist P) i hij).toFun n m) from
        congrFun (congrArg (fun H : CDGAModuleHom (coverTower P j) P => H.toFun n)
          (coverMap_step P j)) _]
      exact ih

/-- **The comparison from the colimit of the covering tower.** -/
noncomputable def coverColimMap :
    CDGAModuleHom (towerColim (coverBase P) (coverCell P) (coverTwist P)) P :=
  colimModuleLift (fun i _ h => towerTrans (coverBase P) (coverCell P) (coverTwist P) i h) P
    (coverMap P) (fun _ _ hij n m => coverMap_trans P hij n m)

section Generators

variable (u : CDGAUnit A)

/-- The generator of the covering tower attached to a cocycle: it lives in the stage whose cell has
that degree. -/
noncomputable def coverGen : ∀ (k : ℕ), P.cocycles k →
    towerCarrier (FreeCellCarrier (R := R) X (cocycleCellCoeff P 0) 0)
      (fun i => FreeCellCarrier (R := R) X (cocycleCellCoeff P (i + 1)) (i + 1)) k k
  | 0, z => freeCellGen (R := R) (X := X) u 0 (Finsupp.single z 1)
  | (i + 1), z => (0, freeCellGen (R := R) (X := X) u (i + 1) (Finsupp.single z 1))

theorem coverGen_mem_cocycles (k : ℕ) (z : P.cocycles k) :
    coverGen P u k z ∈ (coverTower P k).cocycles k := by
  cases k with
  | zero => exact freeCellGen_mem_cocycles u 0 (Finsupp.single z 1)
  | succ i =>
      refine Prod.ext ?_ (freeCellGen_mem_cocycles u (i + 1) (Finsupp.single z 1))
      show (coverTower P i).d (i + 1) 0
          + (coverTwist P i (coverTower P i)).τ (i + 1)
            (freeCellGen (R := R) (X := X) u (i + 1) (Finsupp.single z 1)) = 0
      rw [show (coverTwist P i (coverTower P i)).τ (i + 1)
          (freeCellGen (R := R) (X := X) u (i + 1) (Finsupp.single z 1)) = 0 from rfl,
        show (coverTower P i).d (i + 1) 0 = 0 from ((coverTower P i).dₗ (i + 1)).map_zero,
        add_zero]

variable (hP : CDGAModuleUnital u P)

include hP

theorem coverMap_coverGen (k : ℕ) (z : P.cocycles k) :
    (coverMap P k).toFun k (coverGen P u k z) = (z : M k) := by
  cases k with
  | zero => exact cocycleCover_gen P 0 u hP z
  | succ i =>
      show (coverMap P i).toFun (i + 1) 0
          + (cocycleCover P (i + 1)).toFun (i + 1)
            (freeCellGen (R := R) (X := X) u (i + 1) (Finsupp.single z 1)) = (z : M (i + 1))
      rw [show (coverMap P i).toFun (i + 1) 0 = 0 from ((coverMap P i).mapₗ (i + 1)).map_zero,
        zero_add]
      exact cocycleCover_gen P (i + 1) u hP z

/-- **The comparison from the covering tower hits every cocycle.**  Consequently it is surjective on
cohomology and on the cocycles of degree zero. -/
theorem coverColimMap_surjective_on_cocycles (k : ℕ) (z : P.cocycles k) :
    ∃ y ∈ (towerColim (coverBase P) (coverCell P) (coverTwist P)).cocycles k,
      (coverColimMap P).toFun k y = (z : M k) := by
  refine ⟨(colimModuleOf (fun i _ h =>
    towerTrans (coverBase P) (coverCell P) (coverTwist P) i h) k).toFun k
      (coverGen P u k z), ?_, ?_⟩
  · exact (colimModuleOf (fun i _ h =>
      towerTrans (coverBase P) (coverCell P) (coverTwist P) i h) k).map_mem_cocycles
      (coverGen_mem_cocycles P u k z)
  · rw [coverColimMap, colimModuleLift_colimOf]
    exact coverMap_coverGen P u hP k z

/-- **The comparison is surjective on the cocycles of degree zero.** -/
theorem coverColimMap_cocyclesMap_zero_surjective :
    Function.Surjective ((coverColimMap P).cocyclesMap 0) := by
  intro z
  obtain ⟨y, hy, hyz⟩ := coverColimMap_surjective_on_cocycles P u hP 0 z
  exact ⟨⟨y, hy⟩, Subtype.ext hyz⟩

/-- **The comparison is surjective on cohomology.** -/
theorem coverColimMap_cohomologyMap_surjective (n : ℕ) :
    Function.Surjective ((coverColimMap P).cohomologyMap n) := by
  intro c
  refine Quotient.inductionOn' c fun z => ?_
  obtain ⟨y, hy, hyz⟩ := coverColimMap_surjective_on_cocycles P u hP (n + 1) z
  exact ⟨Submodule.Quotient.mk ⟨y, hy⟩, congrArg Submodule.Quotient.mk (Subtype.ext hyz)⟩

end Generators

end GaloisForLFunctions.HTGeometry
