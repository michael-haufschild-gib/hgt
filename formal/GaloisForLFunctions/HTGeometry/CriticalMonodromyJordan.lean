import GaloisForLFunctions.HTGeometry.PureFibreCardinality
import GaloisForLFunctions.HTGeometry.CoatomFixedField
import Mathlib.GroupTheory.GroupAction.Jordan

/-!
# Full symmetric monodromy from primitivity and one transposition

A primitive group of permutations of the critical fibre that contains a single transposition is the
whole symmetric group.  That is Jordan's theorem, and it is the group-theoretic content of "the
critical horizon has full symmetric monodromy": the geometric inputs are the primitivity of the
monodromy action and the fact that a meridian around the generic point of the ramification divisor
acts as one transposition, not as a product of several.

The consequence used downstream is that a point stabiliser is then maximal, which is what makes the
critical extension field-primitive.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv

instance decidableEq_criticalHorizonOccupationStates (m n : ℕ) :
    DecidableEq (criticalHorizonOccupationStates m n) := by
  unfold criticalHorizonOccupationStates
  infer_instance

/-- **Jordan's criterion on the critical fibre.**  A primitive group of permutations of the
occupation states containing a transposition is the full symmetric group. -/
theorem monodromy_eq_top_of_isPreprimitive_of_isSwap {m n : ℕ}
    (G : Subgroup (Equiv.Perm (criticalHorizonOccupationStates m n)))
    (hG : MulAction.IsPreprimitive G (criticalHorizonOccupationStates m n))
    (g : Equiv.Perm (criticalHorizonOccupationStates m n)) (hswap : g.IsSwap) (hg : g ∈ G) :
    G = ⊤ :=
  Equiv.Perm.subgroup_eq_top_of_isPreprimitive_of_isSwap_mem hG g hswap hg

/-- **And then every point stabiliser is maximal.**  This is the input that makes a critical
extension field-primitive: its Galois group is the full symmetric group on the fibre, and the
extension is the fixed field of a point stabiliser. -/
theorem isCoatom_stabilizer_of_full_monodromy {m n : ℕ}
    [Nontrivial (criticalHorizonOccupationStates m n)]
    (a : criticalHorizonOccupationStates m n) :
    IsCoatom (MulAction.stabilizer (Equiv.Perm (criticalHorizonOccupationStates m n)) a) :=
  isCoatom_stabilizer_perm a

/-- **Full symmetric monodromy, numerically.**  A primitive group of permutations of the occupation
states containing a transposition has order the factorial of the critical binomial multiplicity. -/
theorem card_monodromy_of_isPreprimitive_of_isSwap {m n : ℕ}
    (G : Subgroup (Equiv.Perm (criticalHorizonOccupationStates m n)))
    (hG : MulAction.IsPreprimitive G (criticalHorizonOccupationStates m n))
    (g : Equiv.Perm (criticalHorizonOccupationStates m n)) (hswap : g.IsSwap) (hg : g ∈ G) :
    Nat.card G = ((m + n).choose m).factorial := by
  classical
  rw [monodromy_eq_top_of_isPreprimitive_of_isSwap G hG g hswap hg]
  rw [Nat.card_congr (Subgroup.topEquiv (G := Equiv.Perm
    (criticalHorizonOccupationStates m n))).toEquiv, Nat.card_perm, Nat.card_eq_fintype_card,
    card_criticalHorizonOccupationStates, criticalHorizonMultiplicity]

end GaloisForLFunctions.HTGeometry
