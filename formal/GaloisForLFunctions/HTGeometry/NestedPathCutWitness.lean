import GaloisForLFunctions.HTGeometry.CircuitTreeCutCertificate
import GaloisForLFunctions.HTGeometry.PathGraphTree

/-!
# Cut witnesses for the nested inverse-power qubit path
-/

open scoped BigOperators Matrix Matrix.Norms.L2Operator
open Matrix

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-- Lexicographic physical order `(j,false),(j,true)` of the nested qubit path. -/
def pairQubitPathEquiv (L : ℕ) : PairQubit L ≃ Fin (L * 2) :=
  ((Equiv.refl (Fin L)).prodCongr finTwoEquiv.symm).trans finProdFinEquiv

def nestedQubitPathGraph (L : ℕ) : SimpleGraph (PairQubit L) :=
  (SimpleGraph.pathGraph (L * 2)).comap (pairQubitPathEquiv L)

noncomputable instance nestedQubitPathGraph_decidableAdj (L : ℕ) :
    DecidableRel (nestedQubitPathGraph L).Adj := Classical.decRel _

theorem nestedQubitPathGraph_isTree {L : ℕ} (hL : 0 < L) :
    (nestedQubitPathGraph L).IsTree := by
  have hsize : L * 2 = (L * 2 - 1) + 1 := by omega
  have hpath : (SimpleGraph.pathGraph (L * 2)).IsTree := by
    rw [hsize]
    exact SimpleGraph.pathGraph_isTree _
  exact (SimpleGraph.Iso.comap (pairQubitPathEquiv L)
    (SimpleGraph.pathGraph (L * 2))).isTree_iff.mpr hpath

@[simp] theorem pairQubitPathEquiv_false {L : ℕ} (j : Fin L) :
    (pairQubitPathEquiv L (j, false)).val = 2 * j.val := by
  simp [pairQubitPathEquiv, finProdFinEquiv, finTwoEquiv]

@[simp] theorem pairQubitPathEquiv_true {L : ℕ} (j : Fin L) :
    (pairQubitPathEquiv L (j, true)).val = 2 * j.val + 1 := by
  simp [pairQubitPathEquiv, finProdFinEquiv, finTwoEquiv]
  omega

theorem nestedQubitPathGraph_adj_pair {L : ℕ} (j : Fin L) :
    (nestedQubitPathGraph L).Adj (j, false) (j, true) := by
  rw [nestedQubitPathGraph, SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj]
  left
  simp

theorem nestedQubitPathGraph_adj_bridge {L : ℕ} (j : Fin (L - 1)) :
    (nestedQubitPathGraph L).Adj
      (nestedBridgeLeft j, true) (nestedBridgeRight j, false) := by
  rw [nestedQubitPathGraph, SimpleGraph.comap_adj, SimpleGraph.pathGraph_adj]
  left
  simp [nestedBridgeLeft, nestedBridgeRight]
  omega

/-- Flip the Boolean coordinate when the prescribed sign is negative. -/
def orientedBit (σ a : Bool) : Bool := if σ then a else !a

/-- Four configurations obtained by independently toggling the two sides of a cut. -/
def cutFourConfig {Q : Type*} [DecidableEq Q]
    (A : Finset Q) (σ : Q → Bool) (a b : Bool) : Config Q :=
  fun q => orientedBit (σ q) (if q ∈ A then a else b)

theorem cutFourConfig_on_eq {Q : Type*} [Fintype Q] [DecidableEq Q]
    (A : Finset Q) (σ : Q → Bool) (a b b' : Bool) :
    (splitConfig A (cutFourConfig A σ a b)).1 =
      (splitConfig A (cutFourConfig A σ a b')).1 := by
  funext q
  simp [cutFourConfig, q.property]

theorem cutFourConfig_off_eq {Q : Type*} [Fintype Q] [DecidableEq Q]
    (A : Finset Q) (σ : Q → Bool) (a a' b : Bool) :
    (splitConfig A (cutFourConfig A σ a b)).2 =
      (splitConfig A (cutFourConfig A σ a' b)).2 := by
  funext q
  simp [cutFourConfig, q.property]

theorem SeparatesAcross.fourPoint_diagonal_cut
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {A : Finset Q} {σ : Q → Bool}
    {W : Matrix (Config Q) (Config Q) ℂ}
    (hW : SeparatesAcross A W) :
    W (cutFourConfig A σ false false) (cutFourConfig A σ false false) *
        W (cutFourConfig A σ true true) (cutFourConfig A σ true true) =
      W (cutFourConfig A σ false true) (cutFourConfig A σ false true) *
        W (cutFourConfig A σ true false) (cutFourConfig A σ true false) := by
  rcases hW with ⟨WA, WB, hW⟩
  rw [hW, hW, hW, hW]
  rw [cutFourConfig_on_eq A σ false false true,
    cutFourConfig_on_eq A σ true true false,
    cutFourConfig_off_eq A σ false true false,
    cutFourConfig_off_eq A σ false true true]
  ring

/-- The sign choice that reverses only the first matching bond. -/
def nestedPhaseSign {L : ℕ} (q : PairQubit L) : Bool :=
  if q.1.val = 0 ∧ q.2 = false then false else true

@[simp] theorem nestedPhaseSign_first_false {L : ℕ} (hL : 0 < L) :
    nestedPhaseSign (⟨0, hL⟩, false) = false := by simp [nestedPhaseSign]

@[simp] theorem nestedPhaseSign_first_true {L : ℕ} (hL : 0 < L) :
    nestedPhaseSign (⟨0, hL⟩, true) = true := by simp [nestedPhaseSign]

theorem nestedPhaseSign_pair_eq {L : ℕ} (j : Fin L) (hj : 0 < j.val) :
    nestedPhaseSign (j, false) = nestedPhaseSign (j, true) := by
  simp [nestedPhaseSign, hj.ne']

theorem nestedPhaseSign_bridge_eq {L : ℕ} (j : Fin (L - 1)) :
    nestedPhaseSign (nestedBridgeLeft j, true) =
      nestedPhaseSign (nestedBridgeRight j, false) := by
  simp [nestedPhaseSign, nestedBridgeLeft, nestedBridgeRight]

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
