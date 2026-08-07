import GaloisForLFunctions.HTGeometry.CDGAModule

/-!
# Towers of cell attachments

A relative cell construction attaches one cell after another, so its stages have different carriers:
the `i+1`-st is the `i`-th together with the `i`-th cell.  That is a recursion on the degree index
producing *types*, and the additive and module structures have to be produced by the same recursion.

The twisting cochain of a stage refers to the structure built at the previous stage, so the data of
a tower is a family of twists depending on the structure the recursion has reached — which is what
`towerMod` takes.  Each stage is then, by definition, the cell attachment of the previous one, so
`CDGAModuleHom.IsQuasiIso.twistedMap` applies at every step.

* `HTGeometry.towerCarrier` : the carriers of the stages.
* `HTGeometry.towerMod` : the differential graded module at each stage.
* `HTGeometry.towerMod_succ` : each stage is the cell attachment of the previous one.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

variable {R : Type u} [CommRing R] {X : ℕ → Type v} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X}

/-- The carriers of a tower of cell attachments: the `i+1`-st stage is the `i`-th together with the
`i`-th cell. -/
def towerCarrier (M : ℕ → Type w) (C : ℕ → ℕ → Type w) : ℕ → ℕ → Type w
  | 0 => M
  | (i + 1) => fun n => towerCarrier M C i n × C i n

instance towerAddCommGroup (M : ℕ → Type w) (C : ℕ → ℕ → Type w)
    [∀ n, AddCommGroup (M n)] [∀ i n, AddCommGroup (C i n)] :
    ∀ (i n : ℕ), AddCommGroup (towerCarrier M C i n)
  | 0, n => inferInstanceAs (AddCommGroup (M n))
  | (i + 1), n =>
      letI := towerAddCommGroup M C i n
      inferInstanceAs (AddCommGroup (towerCarrier M C i n × C i n))

instance towerModuleInst (M : ℕ → Type w) (C : ℕ → ℕ → Type w)
    [∀ n, AddCommGroup (M n)] [∀ i n, AddCommGroup (C i n)]
    [∀ n, Module R (M n)] [∀ i n, Module R (C i n)] :
    ∀ (i n : ℕ), Module R (towerCarrier M C i n)
  | 0, n => inferInstanceAs (Module R (M n))
  | (i + 1), n =>
      letI : Module R (towerCarrier M C i n) := towerModuleInst M C i n
      inferInstanceAs (Module R (towerCarrier M C i n × C i n))

variable {M : ℕ → Type w} [∀ n, AddCommGroup (M n)] [∀ n, Module R (M n)]
  {C : ℕ → ℕ → Type w} [∀ i n, AddCommGroup (C i n)] [∀ i n, Module R (C i n)]

/-- **The differential graded module at each stage of a tower of cell attachments.**  The twist of a
stage is allowed to refer to the structure the recursion has reached, which is what makes the tower
expressible. -/
def towerMod (P₀ : CDGAModuleStructure A M) (cellMod : ∀ i, CDGAModuleStructure A (C i))
    (τ : ∀ (i : ℕ) (P : CDGAModuleStructure A (towerCarrier M C i)), CDGATwist P (cellMod i)) :
    ∀ i, CDGAModuleStructure A (towerCarrier M C i)
  | 0 => P₀
  | (i + 1) =>
      CDGAModuleStructure.twisted (towerMod P₀ cellMod τ i) (cellMod i)
        (τ i (towerMod P₀ cellMod τ i))

@[simp] theorem towerMod_zero (P₀ : CDGAModuleStructure A M)
    (cellMod : ∀ i, CDGAModuleStructure A (C i))
    (τ : ∀ (i : ℕ) (P : CDGAModuleStructure A (towerCarrier M C i)), CDGATwist P (cellMod i)) :
    towerMod P₀ cellMod τ 0 = P₀ := rfl

/-- **Each stage of a tower is the cell attachment of the previous one**, so the invariance theorem
for a single cell applies at every step. -/
@[simp] theorem towerMod_succ (P₀ : CDGAModuleStructure A M)
    (cellMod : ∀ i, CDGAModuleStructure A (C i))
    (τ : ∀ (i : ℕ) (P : CDGAModuleStructure A (towerCarrier M C i)), CDGATwist P (cellMod i))
    (i : ℕ) :
    towerMod P₀ cellMod τ (i + 1)
      = CDGAModuleStructure.twisted (towerMod P₀ cellMod τ i) (cellMod i)
          (τ i (towerMod P₀ cellMod τ i)) := rfl

section Comparison

variable {M' : ℕ → Type w} [∀ n, AddCommGroup (M' n)] [∀ n, Module R (M' n)]

/-- **A quasi-isomorphism propagates up a tower of cell attachments.**  Given two towers on the same
cells, a family of comparison maps which starts at a quasi-isomorphism, intertwines the twists at
every stage, and is the cell-attachment of its predecessor at every stage, every member of the
family is a quasi-isomorphism.

Supplying the comparison maps as data is what makes the statement non-circular: the compatibility of
a stage refers to the map at that stage, so it cannot be part of a recursion that is producing those
maps. -/
theorem tower_isQuasiIso {P₀ : CDGAModuleStructure A M} {P₀' : CDGAModuleStructure A M'}
    {cellMod : ∀ i, CDGAModuleStructure A (C i)}
    {τ : ∀ (i : ℕ) (P : CDGAModuleStructure A (towerCarrier M C i)), CDGATwist P (cellMod i)}
    {τ' : ∀ (i : ℕ) (P : CDGAModuleStructure A (towerCarrier M' C i)), CDGATwist P (cellMod i)}
    (ψ : ∀ i, CDGAModuleHom (towerMod P₀ cellMod τ i) (towerMod P₀' cellMod τ' i))
    (hcompat : ∀ (i : ℕ) (n : ℕ) (c : C i n),
      (ψ i).toFun (n + 1) ((τ i (towerMod P₀ cellMod τ i)).τ n c)
        = (τ' i (towerMod P₀' cellMod τ' i)).τ n c)
    (hstep : ∀ i, ψ (i + 1) = CDGAModuleHom.twistedMap (τ i (towerMod P₀ cellMod τ i))
      (τ' i (towerMod P₀' cellMod τ' i)) (ψ i) (hcompat i))
    (h₀ : (ψ 0).IsQuasiIso) : ∀ i, (ψ i).IsQuasiIso := by
  intro i
  induction i with
  | zero => exact h₀
  | succ j ih =>
      rw [hstep j]
      exact CDGAModuleHom.IsQuasiIso.twistedMap (hcompat j) ih

end Comparison

end GaloisForLFunctions.HTGeometry
