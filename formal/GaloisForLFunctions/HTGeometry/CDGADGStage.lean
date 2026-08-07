import GaloisForLFunctions.HTGeometry.CDGAFreeCellLift
import GaloisForLFunctions.HTGeometry.CDGAModuleColimitQuasiIso
import GaloisForLFunctions.HTGeometry.CDGAUnitalCells
import Mathlib.Data.Nat.Pairing

/-!
# Stages of a relative cell construction

The cell attached at a stage of a resolution is free on data read off *that stage*, so the family of
cells cannot be fixed before the recursion starts.  A stage therefore has to carry its own carrier,
its own instances, its structure and its comparison to the target, so that all four are produced by
one recursion.

* `HTGeometry.DGStage` : a stage.
* `HTGeometry.killStep` : attach the cell which kills, in one degree, every class the comparison
  sends to a coboundary.
* `HTGeometry.killSeq` : the resulting sequence of stages.
-/

universe w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type w} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]

/-- A filtered colimit of unital modules is unital. -/
theorem colimModule_unital {u : CDGAUnit A} {ι : Type} [Preorder ι] [IsDirectedOrder ι]
    [Nonempty ι] [DecidableEq ι] {N : ι → ℕ → Type w} [∀ i n, AddCommGroup (N i n)]
    [∀ i n, Module R (N i n)] {Q : ∀ i, CDGAModuleStructure A (N i)}
    (ψ : ∀ i j, i ≤ j → CDGAModuleHom (Q i) (Q j))
    [∀ n : ℕ, DirectedSystem (fun i => N i n) fun i j h => moduleDegTransition ψ n i j h]
    (hQ : ∀ i, CDGAModuleUnital u (Q i)) : CDGAModuleUnital u (colimModule ψ) := by
  refine ⟨fun b z => ?_⟩
  obtain ⟨i, m, rfl⟩ := colimModuleOf_exists ψ b z
  show colimModuleAct ψ (Nat.zero_add b) u.one ((colimModuleOf ψ i).toFun b m) = _
  rw [colimModuleAct_colimOf, (hQ i).act_one b m]

/-- **A stage of a relative cell construction**: a differential graded module together with a
comparison to the target, carrying its own instances so that a recursion may produce it. -/
structure DGStage (A : CDGAStructure R X) (P : CDGAModuleStructure A M) where
  /-- The underlying graded family. -/
  carrier : ℕ → Type w
  /-- Its additive structure. -/
  group : ∀ n, AddCommGroup (carrier n)
  /-- Its module structure. -/
  smul : ∀ n, Module R (carrier n)
  /-- The differential graded module structure. -/
  str : letI := group; letI := smul; CDGAModuleStructure A carrier
  /-- The comparison to the target. -/
  cmp : letI := group; letI := smul; CDGAModuleHom str P

attribute [instance] DGStage.group DGStage.smul

variable (P : CDGAModuleStructure A M)

/-- The classes a stage must kill in a degree: a cocycle whose image is a coboundary, together with
a primitive for that coboundary. -/
def killIndex (s : DGStage A P) (k : ℕ) : Type w :=
  { p : (s.str.cocycles (k + 1)) × M k //
      s.cmp.toFun (k + 1) (p.1 : s.carrier (k + 1)) = P.d k p.2 }

/-- The generators of the cell attached at a stage: the cocycles of the target in that degree,
which make the comparison surjective, together with the classes the comparison kills, which make it
injective. -/
def cellIndex (s : DGStage A P) (k : ℕ) : Type w := (P.cocycles k) ⊕ killIndex P s k

/-- The coefficients of the cell attached at a stage. -/
abbrev cellCoeff (s : DGStage A P) (k : ℕ) : Type w := cellIndex P s k →₀ R

/-- The attaching cocycles of the cell, valued in the cocycles of the stage. -/
noncomputable def cellWLift (s : DGStage A P) (k : ℕ) :
    cellCoeff P s k →ₗ[R] s.str.cocycles (k + 1) :=
  Finsupp.linearCombination R (Sum.elim (fun _ : P.cocycles k => 0)
    (fun p : killIndex P s k => p.1.1))

/-- The attaching cocycles of the cell. -/
noncomputable def cellW (s : DGStage A P) (k : ℕ) :
    cellCoeff P s k →ₗ[R] s.carrier (k + 1) :=
  (s.str.cocycles (k + 1)).subtype.comp (cellWLift P s k)

theorem cellW_cocycle (s : DGStage A P) (k : ℕ) (v : cellCoeff P s k) :
    s.str.d (k + 1) (cellW P s k v) = 0 :=
  (cellWLift P s k v).2

/-- The values of the comparison on the generators: a cocycle of the target for the covering
generators, a chosen primitive for the killing ones. -/
noncomputable def cellG (s : DGStage A P) (k : ℕ) : cellCoeff P s k →ₗ[R] M k :=
  Finsupp.linearCombination R (Sum.elim (fun z : P.cocycles k => (z : M k))
    (fun p : killIndex P s k => p.1.2))

@[simp] theorem cellW_single_inl (s : DGStage A P) (k : ℕ) (z : P.cocycles k) (r : R) :
    cellW P s k (Finsupp.single (Sum.inl z) r) = 0 := by
  show ((Finsupp.linearCombination R (Sum.elim (fun _ : P.cocycles k => 0)
    (fun p : killIndex P s k => p.1.1)) (Finsupp.single (Sum.inl z) r) :
      s.str.cocycles (k + 1)) : s.carrier (k + 1)) = 0
  rw [Finsupp.linearCombination_single]
  show ((r • (0 : s.str.cocycles (k + 1)) : s.str.cocycles (k + 1)) : s.carrier (k + 1)) = 0
  rw [smul_zero]
  rfl


@[simp] theorem cellW_single_inr (s : DGStage A P) (k : ℕ) (p : killIndex P s k) :
    cellW P s k (Finsupp.single (Sum.inr p) 1) = (p.1.1 : s.carrier (k + 1)) := by
  show ((Finsupp.linearCombination R (Sum.elim (fun _ : P.cocycles k => 0)
    (fun q : killIndex P s k => q.1.1)) (Finsupp.single (Sum.inr p) 1) :
      s.str.cocycles (k + 1)) : s.carrier (k + 1)) = _
  rw [Finsupp.linearCombination_single, one_smul]
  rfl

@[simp] theorem cellG_single_inl (s : DGStage A P) (k : ℕ) (z : P.cocycles k) :
    cellG P s k (Finsupp.single (Sum.inl z) 1) = (z : M k) := by
  show (Finsupp.linearCombination R (Sum.elim (fun z : P.cocycles k => (z : M k))
    (fun p : killIndex P s k => p.1.2))) (Finsupp.single (Sum.inl z) 1) = _
  rw [Finsupp.linearCombination_single, one_smul]
  rfl

theorem cellG_primitive (s : DGStage A P) (k : ℕ) (v : cellCoeff P s k) :
    P.d k (cellG P s k v) = s.cmp.toFun (k + 1) (cellW P s k v) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero =>
      rw [map_zero, map_zero, show P.d k (0 : M k) = 0 from (P.dₗ k).map_zero,
        show s.cmp.toFun (k + 1) (0 : s.carrier (k + 1)) = 0 from
          (s.cmp.mapₗ (k + 1)).map_zero]
  | add v v' hv hv' =>
      rw [map_add, map_add, P.d_add, hv, hv', s.cmp.map_add]
  | single q r =>
      cases q with
      | inl z =>
          rw [show cellG P s k (Finsupp.single (Sum.inl z) r) = r • (z : M k) from by
              show (Finsupp.linearCombination R (Sum.elim (fun z : P.cocycles k => (z : M k))
                (fun p : killIndex P s k => p.1.2))) (Finsupp.single (Sum.inl z) r) = _
              rw [Finsupp.linearCombination_single]
              rfl,
            show cellW P s k (Finsupp.single (Sum.inl z) r) = 0 from cellW_single_inl P s k z r,
            P.d_smul, show P.d k (z : M k) = 0 from z.2, smul_zero,
            show s.cmp.toFun (k + 1) (0 : s.carrier (k + 1)) = 0 from
              (s.cmp.mapₗ (k + 1)).map_zero]
      | inr p =>
          rw [show cellG P s k (Finsupp.single (Sum.inr p) r) = r • p.1.2 from by
              show (Finsupp.linearCombination R (Sum.elim (fun z : P.cocycles k => (z : M k))
                (fun q : killIndex P s k => q.1.2))) (Finsupp.single (Sum.inr p) r) = _
              rw [Finsupp.linearCombination_single]
              rfl,
            show cellW P s k (Finsupp.single (Sum.inr p) r)
                = r • (p.1.1 : s.carrier (k + 1)) from by
              show ((Finsupp.linearCombination R (Sum.elim (fun _ : P.cocycles k => 0)
                (fun q : killIndex P s k => q.1.1)) (Finsupp.single (Sum.inr p) r) :
                  s.str.cocycles (k + 1)) : s.carrier (k + 1)) = _
              rw [Finsupp.linearCombination_single]
              rfl,
            P.d_smul, s.cmp.map_smul, p.2]

/-- **Attaching the cell which kills, in one degree, every class the comparison sends to a
coboundary.** -/
noncomputable def killStep (k : ℕ) (s : DGStage A P) : DGStage A P where
  carrier n := s.carrier n × FreeCellCarrier (R := R) X (cellCoeff P s k) k n
  group _ := inferInstance
  smul _ := inferInstance
  str := CDGAModuleStructure.twisted s.str (freeCellModule A (cellCoeff P s k) k)
    (freeCellTwist s.str k (cellW P s k) (cellW_cocycle P s k))
  cmp := freeCellAttachExtend s.str P s.cmp k (cellW P s k) (cellW_cocycle P s k)
    (cellG P s k) (cellG_primitive P s k)

/-- The inclusion of a stage into the next. -/
noncomputable def killStepHom (k : ℕ) (s : DGStage A P) :
    CDGAModuleHom s.str (killStep P k s).str :=
  twistedInl s.str (freeCellModule A (cellCoeff P s k) k)
    (freeCellTwist s.str k (cellW P s k) (cellW_cocycle P s k))

theorem killStep_cmp (k : ℕ) (s : DGStage A P) :
    (killStep P k s).cmp.comp (killStepHom P k s) = s.cmp :=
  twistedExtend_comp_inl _ _

/-- **The sequence of stages**: at stage `j` the cell of degree `(Nat.unpair j).2` is attached, so
every degree is revisited infinitely often. -/
noncomputable def killSeq (s₀ : DGStage A P) : ℕ → DGStage A P
  | 0 => s₀
  | (j + 1) => killStep P (Nat.unpair j).2 (killSeq s₀ j)

@[simp] theorem killSeq_zero (s₀ : DGStage A P) : killSeq P s₀ 0 = s₀ := rfl

@[simp] theorem killSeq_succ (s₀ : DGStage A P) (j : ℕ) :
    killSeq P s₀ (j + 1) = killStep P (Nat.unpair j).2 (killSeq P s₀ j) := rfl

/-- The transitions of the sequence of stages. -/
noncomputable def killTrans (s₀ : DGStage A P) (i : ℕ) : ∀ {j : ℕ}, i ≤ j →
    CDGAModuleHom (killSeq P s₀ i).str (killSeq P s₀ j).str :=
  Nat.leRec (motive := fun j _ =>
      CDGAModuleHom (killSeq P s₀ i).str (killSeq P s₀ j).str)
    (CDGAModuleHom.id _)
    (fun {j} _ ih => (killStepHom P (Nat.unpair j).2 (killSeq P s₀ j)).comp ih)

@[simp] theorem killTrans_self (s₀ : DGStage A P) (i : ℕ) (h : i ≤ i) :
    killTrans P s₀ i h = CDGAModuleHom.id _ :=
  Nat.leRec_self _ _

theorem killTrans_succ (s₀ : DGStage A P) {i j : ℕ} (h1 : i ≤ j) {h2 : i ≤ j + 1} :
    killTrans P s₀ i h2
      = (killStepHom P (Nat.unpair j).2 (killSeq P s₀ j)).comp (killTrans P s₀ i h1) :=
  Nat.leRec_succ _ _ h1

theorem killTrans_trans (s₀ : DGStage A P) {i j : ℕ} (hij : i ≤ j) {k : ℕ} (hjk : j ≤ k)
    (n : ℕ) (m : (killSeq P s₀ i).carrier n) :
    (killTrans P s₀ j hjk).toFun n ((killTrans P s₀ i hij).toFun n m)
      = (killTrans P s₀ i (hij.trans hjk)).toFun n m := by
  induction k, hjk using Nat.le_induction with
  | base => rw [killTrans_self]; rfl
  | succ k hjk ih =>
      rw [killTrans_succ P s₀ hjk, killTrans_succ P s₀ (hij.trans hjk)]
      exact congrArg ((killStepHom P (Nat.unpair k).2 (killSeq P s₀ k)).toFun n) ih

/-- **The sequence of stages is a directed system.** -/
theorem killDirectedSystem (s₀ : DGStage A P) :
    CDGAModuleDirectedSystem (fun i => (killSeq P s₀ i).str)
      (fun i _ h => killTrans P s₀ i h) where
  map_self i h n m := by rw [killTrans_self]; rfl
  map_map i j k hij hjk n m := killTrans_trans P s₀ hij hjk n m

instance killDegDirectedSystem (s₀ : DGStage A P) (n : ℕ) :
    DirectedSystem (fun i => (killSeq P s₀ i).carrier n)
      fun i j h => moduleDegTransition (fun i _ h => killTrans P s₀ i h) n i j h :=
  moduleDirectedSystem_deg _ (killDirectedSystem P s₀) n

/-- **The colimit of the sequence of stages.** -/
noncomputable def killColim (s₀ : DGStage A P) :
    CDGAModuleStructure A (colimModuleDeg (fun i _ h => killTrans P s₀ i h)) :=
  colimModule (fun i _ h => killTrans P s₀ i h)

/-- The comparisons of the stages are compatible with the transitions. -/
theorem killSeq_cmp_trans (s₀ : DGStage A P) {i j : ℕ} (hij : i ≤ j) (n : ℕ)
    (m : (killSeq P s₀ i).carrier n) :
    (killSeq P s₀ j).cmp.toFun n ((killTrans P s₀ i hij).toFun n m)
      = (killSeq P s₀ i).cmp.toFun n m := by
  induction j, hij using Nat.le_induction with
  | base => rw [killTrans_self]; rfl
  | succ j hij ih =>
      rw [killTrans_succ P s₀ hij]
      show (killSeq P s₀ (j + 1)).cmp.toFun n
          ((killStepHom P (Nat.unpair j).2 (killSeq P s₀ j)).toFun n
            ((killTrans P s₀ i hij).toFun n m))
        = (killSeq P s₀ i).cmp.toFun n m
      rw [show (killSeq P s₀ (j + 1)).cmp.toFun n
          ((killStepHom P (Nat.unpair j).2 (killSeq P s₀ j)).toFun n
            ((killTrans P s₀ i hij).toFun n m))
        = (killSeq P s₀ j).cmp.toFun n ((killTrans P s₀ i hij).toFun n m) from
        congrFun (congrArg (fun H : CDGAModuleHom (killSeq P s₀ j).str P => H.toFun n)
          (killStep_cmp P (Nat.unpair j).2 (killSeq P s₀ j))) _]
      exact ih

/-- **The comparison from the colimit of the sequence of stages.** -/
noncomputable def killColimMap (s₀ : DGStage A P) :
    CDGAModuleHom (killColim P s₀) P :=
  colimModuleLift (fun i _ h => killTrans P s₀ i h) P (fun i => (killSeq P s₀ i).cmp)
    (fun _ _ hij n m => killSeq_cmp_trans P s₀ hij n m)

section Killing

variable {u : CDGAUnit A}

/-- The twist takes the prescribed value on a generator of a unital module. -/
theorem freeCellTwist_gen {L : ℕ → Type w} [∀ n, AddCommGroup (L n)] [∀ n, Module R (L n)]
    {V : Type w} [AddCommGroup V] [Module R V] (S : CDGAModuleStructure A L)
    (hS : CDGAModuleUnital u S) (k : ℕ) (w : V →ₗ[R] L (k + 1))
    (hw : ∀ v, S.d (k + 1) (w v) = 0) (v : V) :
    (freeCellTwist S k w hw).τ k (freeCellGen (R := R) (X := X) u k v) = w v := by
  show freeCellTwistₗ S k w k (freeCellGen (R := R) (X := X) u k v) = w v
  rw [freeCellTwistₗ_apply S k w (Nat.zero_add k), freeCellGen_apply, TensorProduct.lift.tmul,
    freeCellBil_apply, pow_zero, one_smul]
  exact hS.act_one (k + 1) (w v)

/-- Each stage is unital if the base is. -/
theorem killSeq_unital (s₀ : DGStage A P) (hs₀ : CDGAModuleUnital u s₀.str) :
    ∀ j, CDGAModuleUnital u (killSeq P s₀ j).str
  | 0 => hs₀
  | (j + 1) =>
      twisted_unital _ (killSeq_unital s₀ hs₀ j)
        (freeCell_unital u (cellCoeff P (killSeq P s₀ j) (Nat.unpair j).2) (Nat.unpair j).2)

/-- **The attached cell kills the class it was attached to.** -/
theorem killSeq_kills (s₀ : DGStage A P) (hs₀ : CDGAModuleUnital u s₀.str) (j n : ℕ)
    (hj : (Nat.unpair j).2 = n) (p : killIndex P (killSeq P s₀ j) n) :
    ∃ y : (killSeq P s₀ (j + 1)).carrier n, (killSeq P s₀ (j + 1)).str.d n y
      = (killTrans P s₀ j (Nat.le_succ j)).toFun (n + 1) (p.1.1 : (killSeq P s₀ j).carrier (n + 1))
      := by
  subst hj
  refine ⟨(0, freeCellGen (R := R) (X := X) u (Nat.unpair j).2 (Finsupp.single (Sum.inr p) 1)), ?_⟩
  have hstep : (killTrans P s₀ j (Nat.le_succ j)).toFun ((Nat.unpair j).2 + 1)
      (p.1.1 : (killSeq P s₀ j).carrier ((Nat.unpair j).2 + 1))
    = (killStepHom P (Nat.unpair j).2 (killSeq P s₀ j)).toFun ((Nat.unpair j).2 + 1)
      (p.1.1 : (killSeq P s₀ j).carrier ((Nat.unpair j).2 + 1)) := by
    rw [killTrans_succ P s₀ (le_refl j), killTrans_self]
    rfl
  rw [hstep]
  refine Prod.ext ?_ ?_
  · show (killSeq P s₀ j).str.d (Nat.unpair j).2 0
        + (freeCellTwist (killSeq P s₀ j).str (Nat.unpair j).2
            (cellW P (killSeq P s₀ j) (Nat.unpair j).2)
            (cellW_cocycle P (killSeq P s₀ j) (Nat.unpair j).2)).τ (Nat.unpair j).2
          (freeCellGen (R := R) (X := X) u (Nat.unpair j).2 (Finsupp.single (Sum.inr p) 1))
      = (p.1.1 : (killSeq P s₀ j).carrier ((Nat.unpair j).2 + 1))
    rw [show (killSeq P s₀ j).str.d (Nat.unpair j).2
        (0 : (killSeq P s₀ j).carrier (Nat.unpair j).2) = 0 from
        ((killSeq P s₀ j).str.dₗ (Nat.unpair j).2).map_zero, zero_add,
      freeCellTwist_gen (killSeq P s₀ j).str (killSeq_unital P s₀ hs₀ j) (Nat.unpair j).2
        (cellW P (killSeq P s₀ j) (Nat.unpair j).2)
        (cellW_cocycle P (killSeq P s₀ j) (Nat.unpair j).2) (Finsupp.single (Sum.inr p) 1),
      cellW_single_inr]
  · exact freeCellGen_mem_cocycles u (Nat.unpair j).2 (Finsupp.single (Sum.inr p) 1)

/-- **The attached cell covers every cocycle of the target in its degree.** -/
theorem killSeq_covers (s₀ : DGStage A P) (hs₀ : CDGAModuleUnital u s₀.str)
    (hP : CDGAModuleUnital u P) (j n : ℕ)
    (hj : (Nat.unpair j).2 = n) (z : P.cocycles n) :
    ∃ y : (killSeq P s₀ (j + 1)).carrier n,
      (killSeq P s₀ (j + 1)).str.d n y = 0 ∧
        (killSeq P s₀ (j + 1)).cmp.toFun n y = (z : M n) := by
  subst hj
  refine ⟨(0, freeCellGen (R := R) (X := X) u (Nat.unpair j).2
    (Finsupp.single (Sum.inl z) 1)), ?_, ?_⟩
  · refine Prod.ext ?_ ?_
    · show (killSeq P s₀ j).str.d (Nat.unpair j).2 0
          + (freeCellTwist (killSeq P s₀ j).str (Nat.unpair j).2
              (cellW P (killSeq P s₀ j) (Nat.unpair j).2)
              (cellW_cocycle P (killSeq P s₀ j) (Nat.unpair j).2)).τ (Nat.unpair j).2
            (freeCellGen (R := R) (X := X) u (Nat.unpair j).2
              (Finsupp.single (Sum.inl z) 1)) = 0
      rw [show (killSeq P s₀ j).str.d (Nat.unpair j).2
          (0 : (killSeq P s₀ j).carrier (Nat.unpair j).2) = 0 from
          ((killSeq P s₀ j).str.dₗ (Nat.unpair j).2).map_zero, zero_add,
        freeCellTwist_gen (killSeq P s₀ j).str (killSeq_unital P s₀ hs₀ j) (Nat.unpair j).2
          (cellW P (killSeq P s₀ j) (Nat.unpair j).2)
          (cellW_cocycle P (killSeq P s₀ j) (Nat.unpair j).2)
          (Finsupp.single (Sum.inl z) 1),
        cellW_single_inl]
    · exact freeCellGen_mem_cocycles u (Nat.unpair j).2 (Finsupp.single (Sum.inl z) 1)
  · show (killSeq P s₀ j).cmp.toFun (Nat.unpair j).2 0
        + freeCellExtendₗ P (Nat.unpair j).2 (cellG P (killSeq P s₀ j) (Nat.unpair j).2)
          (Nat.unpair j).2 (freeCellGen (R := R) (X := X) u (Nat.unpair j).2
            (Finsupp.single (Sum.inl z) 1)) = (z : M (Nat.unpair j).2)
    rw [show (killSeq P s₀ j).cmp.toFun (Nat.unpair j).2
        (0 : (killSeq P s₀ j).carrier (Nat.unpair j).2) = 0 from
        ((killSeq P s₀ j).cmp.mapₗ (Nat.unpair j).2).map_zero, zero_add,
      freeCellExtendₗ_gen u (Nat.unpair j).2 P hP
        (cellG P (killSeq P s₀ j) (Nat.unpair j).2) (Finsupp.single (Sum.inl z) 1),
      cellG_single_inl]

/-- The colimit of the sequence of stages is unital. -/
theorem killColim_unital (s₀ : DGStage A P) (hs₀ : CDGAModuleUnital u s₀.str) :
    CDGAModuleUnital u (killColim P s₀) :=
  colimModule_unital (fun i _ h => killTrans P s₀ i h) (killSeq_unital P s₀ hs₀)

/-- **The comparison from the colimit hits every cocycle of the target.** -/
theorem killColimMap_surjective_on_cocycles (s₀ : DGStage A P)
    (hs₀ : CDGAModuleUnital u s₀.str) (hP : CDGAModuleUnital u P) (n : ℕ) (z : P.cocycles n) :
    ∃ ξ ∈ (killColim P s₀).cocycles n, (killColimMap P s₀).toFun n ξ = (z : M n) := by
  obtain ⟨y, hyd, hyz⟩ := killSeq_covers P s₀ hs₀ hP (Nat.pair 0 n) n (by rw [Nat.unpair_pair]) z
  refine ⟨(colimModuleOf (fun i _ h => killTrans P s₀ i h) (Nat.pair 0 n + 1)).toFun n y, ?_, ?_⟩
  · exact (colimModuleOf (fun i _ h => killTrans P s₀ i h)
      (Nat.pair 0 n + 1)).map_mem_cocycles hyd
  · rw [killColimMap, colimModuleLift_colimOf]
    exact hyz

/-- **The comparison from the colimit is injective on cohomology.**  A class killed in the target is
visible at some stage; the cell attached at the next revisit of its degree makes it a coboundary. -/
theorem killColimMap_cohomologyMap_injective (s₀ : DGStage A P)
    (hs₀ : CDGAModuleUnital u s₀.str) (n : ℕ) :
    Function.Injective ((killColimMap P s₀).cohomologyMap n) := by
  refine (injective_iff_map_eq_zero _).2 fun cl hcl => ?_
  refine Quotient.inductionOn' cl ?_ hcl
  intro ξ hξ
  obtain ⟨v, hv⟩ : ∃ v : M n, (killColimMap P s₀).toFun (n + 1)
      (ξ : colimModuleDeg (fun i _ h => killTrans P s₀ i h) (n + 1)) = P.d n v :=
    (Submodule.Quotient.mk_eq_zero _).1 hξ
  obtain ⟨j₀, c, hcd, hcξ⟩ := moduleCocycle_at_stage (fun i _ h => killTrans P s₀ i h) (n + 1)
    (ξ : colimModuleDeg (fun i _ h => killTrans P s₀ i h) (n + 1)) ξ.2
  have hj₀j : j₀ ≤ Nat.pair j₀ n := Nat.left_le_pair j₀ n
  have hjn : (Nat.unpair (Nat.pair j₀ n)).2 = n := by rw [Nat.unpair_pair]
  have hc'd : (killSeq P s₀ (Nat.pair j₀ n)).str.d (n + 1)
      ((killTrans P s₀ j₀ hj₀j).toFun (n + 1) c) = 0 := by
    rw [← (killTrans P s₀ j₀ hj₀j).map_d (n + 1) c, hcd]
    exact ((killTrans P s₀ j₀ hj₀j).mapₗ (n + 2)).map_zero
  have hcmp : (killSeq P s₀ (Nat.pair j₀ n)).cmp.toFun (n + 1)
      ((killTrans P s₀ j₀ hj₀j).toFun (n + 1) c) = P.d n v := by
    rw [killSeq_cmp_trans P s₀ hj₀j (n + 1) c, ← hv, ← hcξ]
    exact (colimModuleLift_colimOf (fun i _ h => killTrans P s₀ i h) P
      (fun i => (killSeq P s₀ i).cmp)
      (fun _ _ hij m₀ m => killSeq_cmp_trans P s₀ hij m₀ m) (n + 1) j₀ c).symm
  obtain ⟨y, hy⟩ := killSeq_kills P s₀ hs₀ (Nat.pair j₀ n) n hjn
    ⟨(⟨(killTrans P s₀ j₀ hj₀j).toFun (n + 1) c, hc'd⟩, v), hcmp⟩
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  refine ⟨(colimModuleOf (fun i _ h => killTrans P s₀ i h) (Nat.pair j₀ n + 1)).toFun n y, ?_⟩
  show (ξ : colimModuleDeg (fun i _ h => killTrans P s₀ i h) (n + 1))
    = (colimModule (fun i _ h => killTrans P s₀ i h)).d n
      ((colimModuleOf (fun i _ h => killTrans P s₀ i h) (Nat.pair j₀ n + 1)).toFun n y)
  rw [← (colimModuleOf (fun i _ h => killTrans P s₀ i h) (Nat.pair j₀ n + 1)).map_d n y, hy,
    colimModuleOf_trans (fun i _ h => killTrans P s₀ i h) (Nat.le_succ (Nat.pair j₀ n)) (n + 1),
    colimModuleOf_trans (fun i _ h => killTrans P s₀ i h) hj₀j (n + 1) c]
  exact hcξ.symm

/-- **A semi-free resolution.**  The colimit of the sequence of stages is built from the base by
attaching free cells, and the comparison to the target is a quasi-isomorphism: surjective because
every cocycle of the target is covered, injective because every class it kills is killed by a cell.
-/
theorem killColimMap_isQuasiIso (s₀ : DGStage A P) (hs₀ : CDGAModuleUnital u s₀.str)
    (hP : CDGAModuleUnital u P) : (killColimMap P s₀).IsQuasiIso := by
  intro n
  refine ⟨killColimMap_cohomologyMap_injective P s₀ hs₀ n, ?_⟩
  intro cl
  refine Quotient.inductionOn' cl fun z => ?_
  obtain ⟨ξ, hξ, hξz⟩ := killColimMap_surjective_on_cocycles P s₀ hs₀ hP (n + 1)
    ⟨(z : M (n + 1)), z.2⟩
  exact ⟨Submodule.Quotient.mk ⟨ξ, hξ⟩, congrArg Submodule.Quotient.mk (Subtype.ext hξz)⟩

/-- **The comparison is surjective on the cocycles of degree zero.** -/
theorem killColimMap_cocyclesMap_zero_surjective (s₀ : DGStage A P)
    (hs₀ : CDGAModuleUnital u s₀.str) (hP : CDGAModuleUnital u P) :
    Function.Surjective ((killColimMap P s₀).cocyclesMap 0) := by
  intro z
  obtain ⟨ξ, hξ, hξz⟩ := killColimMap_surjective_on_cocycles P s₀ hs₀ hP 0 z
  exact ⟨⟨ξ, hξ⟩, Subtype.ext hξz⟩

end Killing

end GaloisForLFunctions.HTGeometry
