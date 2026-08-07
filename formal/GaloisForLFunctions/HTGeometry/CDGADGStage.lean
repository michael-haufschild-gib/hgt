import GaloisForLFunctions.HTGeometry.CDGAFreeCellLift
import GaloisForLFunctions.HTGeometry.CDGAModuleColimitQuasiIso

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

/-- The coefficients of the cell attached at a stage. -/
abbrev killCoeff (s : DGStage A P) (k : ℕ) : Type w := killIndex P s k →₀ R

/-- The attaching cocycles of the cell. -/
noncomputable def killW (s : DGStage A P) (k : ℕ) :
    killCoeff P s k →ₗ[R] s.carrier (k + 1) :=
  (s.str.cocycles (k + 1)).subtype.comp
    (Finsupp.linearCombination R fun p : killIndex P s k => p.1.1)

theorem killW_cocycle (s : DGStage A P) (k : ℕ) (v : killCoeff P s k) :
    s.str.d (k + 1) (killW P s k v) = 0 :=
  ((Finsupp.linearCombination R fun p : killIndex P s k => p.1.1) v).2

/-- The chosen primitives for the images of the attaching cocycles. -/
noncomputable def killG (s : DGStage A P) (k : ℕ) : killCoeff P s k →ₗ[R] M k :=
  Finsupp.linearCombination R fun p : killIndex P s k => p.1.2

theorem killG_primitive (s : DGStage A P) (k : ℕ) (v : killCoeff P s k) :
    P.d k (killG P s k v) = s.cmp.toFun (k + 1) (killW P s k v) := by
  classical
  induction v using Finsupp.induction_linear with
  | zero =>
      rw [map_zero, map_zero, show P.d k (0 : M k) = 0 from (P.dₗ k).map_zero,
        show s.cmp.toFun (k + 1) (0 : s.carrier (k + 1)) = 0 from
          (s.cmp.mapₗ (k + 1)).map_zero]
  | add v v' hv hv' =>
      rw [map_add, map_add, P.d_add, hv, hv', s.cmp.map_add]
  | single p r =>
      rw [killG, Finsupp.linearCombination_single, killW]
      show P.d k (r • p.1.2) = s.cmp.toFun (k + 1)
        ((Finsupp.linearCombination R fun q : killIndex P s k => q.1.1)
          (Finsupp.single p r) : s.carrier (k + 1))
      rw [Finsupp.linearCombination_single]
      show P.d k (r • p.1.2) = s.cmp.toFun (k + 1) (r • (p.1.1 : s.carrier (k + 1)))
      rw [P.d_smul, s.cmp.map_smul, p.2]

/-- **Attaching the cell which kills, in one degree, every class the comparison sends to a
coboundary.** -/
noncomputable def killStep (k : ℕ) (s : DGStage A P) : DGStage A P where
  carrier n := s.carrier n × FreeCellCarrier (R := R) X (killCoeff P s k) k n
  group n := inferInstance
  smul n := inferInstance
  str := CDGAModuleStructure.twisted s.str (freeCellModule A (killCoeff P s k) k)
    (freeCellTwist s.str k (killW P s k) (killW_cocycle P s k))
  cmp := freeCellAttachExtend s.str P s.cmp k (killW P s k) (killW_cocycle P s k)
    (killG P s k) (killG_primitive P s k)

/-- The inclusion of a stage into the next. -/
noncomputable def killStepHom (k : ℕ) (s : DGStage A P) :
    CDGAModuleHom s.str (killStep P k s).str :=
  twistedInl s.str (freeCellModule A (killCoeff P s k) k)
    (freeCellTwist s.str k (killW P s k) (killW_cocycle P s k))

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

end GaloisForLFunctions.HTGeometry
