import GaloisForLFunctions.HTGeometry.CDGACellTower
import GaloisForLFunctions.HTGeometry.CDGAModuleColimitQuasiIso

/-!
# The colimit of a tower of cell attachments

A tower of cell attachments is a sequential directed system: the base of a twisted extension
includes into it by padding with zero, and the transition from a stage to a later one is the
composite of those inclusions.  The colimit of the system is the differential graded module the
tower converges to, and a comparison which is a full quasi-isomorphism at every stage induces one
on the colimits.

* `HTGeometry.twistedInl` : the inclusion of the base into a twisted extension.
* `HTGeometry.towerTrans` : the transition maps of the tower.
* `HTGeometry.towerDirectedSystem` : they form a directed system.
* `HTGeometry.towerColim` : the colimit of the tower.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

section Inclusion

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {N : ℕ → Type w} [∀ n, AddCommGroup (N n)] [∀ n, Module R (N n)]

/-- **The inclusion of the base into a twisted extension**: pad with zero.  The twist contributes
nothing on a zero cell component, so the inclusion commutes with the deformed differential. -/
def twistedInl (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N) (t : CDGATwist P Q) :
    CDGAModuleHom P (CDGAModuleStructure.twisted P Q t) where
  toFun _ m := (m, 0)
  map_add _ _ _ := Prod.ext rfl (add_zero (0 : N _)).symm
  map_smul _ c _ := Prod.ext rfl (smul_zero c).symm
  map_act h x _ := Prod.ext rfl ((Q.actₗ h x).map_zero).symm
  map_d n m := by
    refine Prod.ext ?_ ((Q.dₗ n).map_zero).symm
    show P.d n m = P.d n m + t.τ n 0
    rw [CDGAModuleStructure.CDGATwist.τ_zero, add_zero]

@[simp] theorem twistedInl_toFun (P : CDGAModuleStructure A M) (Q : CDGAModuleStructure A N)
    (t : CDGATwist P Q) (n : ℕ) (m : M n) : (twistedInl P Q t).toFun n m = (m, 0) := rfl

end Inclusion

section Tower

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {C : ℕ → ℕ → Type w} [∀ i n, AddCommGroup (C i n)] [∀ i n, Module R (C i n)]
  (P₀ : CDGAModuleStructure A M) (cellMod : ∀ i, CDGAModuleStructure A (C i))
  (τ : ∀ (i : ℕ) (P : CDGAModuleStructure A (towerCarrier M C i)), CDGATwist P (cellMod i))

/-- The inclusion of one stage of a tower into the next. -/
def towerStep (i : ℕ) :
    CDGAModuleHom (towerMod P₀ cellMod τ i) (towerMod P₀ cellMod τ (i + 1)) :=
  twistedInl (towerMod P₀ cellMod τ i) (cellMod i) (τ i (towerMod P₀ cellMod τ i))

/-- **The transition maps of a tower**: the composite of the inclusions from one stage to a later
one. -/
def towerTrans (i : ℕ) : ∀ {j : ℕ}, i ≤ j →
    CDGAModuleHom (towerMod P₀ cellMod τ i) (towerMod P₀ cellMod τ j) :=
  Nat.leRec (motive := fun j _ =>
      CDGAModuleHom (towerMod P₀ cellMod τ i) (towerMod P₀ cellMod τ j))
    (CDGAModuleHom.id _)
    (fun {k} _ ih => (towerStep P₀ cellMod τ k).comp ih)

@[simp] theorem towerTrans_self (i : ℕ) (h : i ≤ i) :
    towerTrans P₀ cellMod τ i h = CDGAModuleHom.id _ :=
  Nat.leRec_self _ _

theorem towerTrans_succ {i k : ℕ} (h1 : i ≤ k) {h2 : i ≤ k + 1} :
    towerTrans P₀ cellMod τ i h2
      = (towerStep P₀ cellMod τ k).comp (towerTrans P₀ cellMod τ i h1) :=
  Nat.leRec_succ _ _ h1

/-- The transitions of a tower compose. -/
theorem towerTrans_trans {i j : ℕ} (hij : i ≤ j) {k : ℕ} (hjk : j ≤ k) (n : ℕ)
    (m : towerCarrier M C i n) :
    (towerTrans P₀ cellMod τ j hjk).toFun n ((towerTrans P₀ cellMod τ i hij).toFun n m)
      = (towerTrans P₀ cellMod τ i (hij.trans hjk)).toFun n m := by
  induction k, hjk using Nat.le_induction with
  | base => rw [towerTrans_self]; rfl
  | succ k hjk ih =>
      rw [towerTrans_succ P₀ cellMod τ hjk, towerTrans_succ P₀ cellMod τ (hij.trans hjk)]
      exact congrArg ((towerStep P₀ cellMod τ k).toFun n) ih

/-- **A tower is a directed system.** -/
theorem towerDirectedSystem :
    CDGAModuleDirectedSystem (towerMod P₀ cellMod τ) (fun i _ h => towerTrans P₀ cellMod τ i h) where
  map_self i h n m := by rw [towerTrans_self]; rfl
  map_map i j k hij hjk n m := towerTrans_trans P₀ cellMod τ hij hjk n m

instance towerDegDirectedSystem (n : ℕ) :
    DirectedSystem (fun i => towerCarrier M C i n)
      fun i j h => moduleDegTransition (fun i _ h => towerTrans P₀ cellMod τ i h) n i j h :=
  moduleDirectedSystem_deg _ (towerDirectedSystem P₀ cellMod τ) n

/-- **The colimit of a tower of cell attachments.** -/
noncomputable def towerColim : CDGAModuleStructure A
    (colimModuleDeg (fun i _ h => towerTrans P₀ cellMod τ i h)) :=
  colimModule (fun i _ h => towerTrans P₀ cellMod τ i h)

end Tower

section Comparison

variable {R : Type u} [CommRing R] {X : ℕ → Type w} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}
  {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]
  {C : ℕ → ℕ → Type w} [∀ i n, AddCommGroup (C i n)] [∀ i n, Module R (C i n)]
  {C' : ℕ → ℕ → Type w} [∀ i n, AddCommGroup (C' i n)] [∀ i n, Module R (C' i n)]
  (P₀ : CDGAModuleStructure A M) (cellMod : ∀ i, CDGAModuleStructure A (C i))
  (τ : ∀ (i : ℕ) (P : CDGAModuleStructure A (towerCarrier M C i)), CDGATwist P (cellMod i))
  (P₀' : CDGAModuleStructure A M') (cellMod' : ∀ i, CDGAModuleStructure A (C' i))
  (τ' : ∀ (i : ℕ) (P : CDGAModuleStructure A (towerCarrier M' C' i)), CDGATwist P (cellMod' i))
  (Ψ : ∀ i, CDGAModuleHom (towerMod P₀ cellMod τ i) (towerMod P₀' cellMod' τ' i))
  (hΨ : ∀ (i j : ℕ) (hij : i ≤ j) (n : ℕ) (m : towerCarrier M C i n),
    (Ψ j).toFun n ((towerTrans P₀ cellMod τ i hij).toFun n m)
      = (towerTrans P₀' cellMod' τ' i hij).toFun n ((Ψ i).toFun n m))

include hΨ

/-- **A stagewise full quasi-isomorphism of towers induces one on the colimits.** -/
theorem towerColimHom_isQuasiIsoFull (hqi : ∀ i, (Ψ i).IsQuasiIsoFull) :
    (colimModuleHom (fun i _ h => towerTrans P₀ cellMod τ i h)
      (fun i _ h => towerTrans P₀' cellMod' τ' i h) Ψ hΨ).IsQuasiIsoFull :=
  colimModuleHom_isQuasiIsoFull _ _ Ψ hΨ hqi

end Comparison

end GaloisForLFunctions.HTGeometry
