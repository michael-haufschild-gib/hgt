import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.LogicalCorrespondenceX
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.LogicalCorrespondenceZ
import GaloisForLFunctions.QECLean.Stabilizer.Codes.Toric.StabilizerCode

/-!
# Toric lattice-gauge loop applications

Concrete `2 × 2` torus realization of Wilson order loops and dual 't Hooft disorder loops.  The
matching pairs anticommute, independent pairs commute, and both operators represent nontrivial
logical/homology classes.  Generic chain statements below give the lattice gauge dictionary:
Gauss-law closure is cyclehood, while products of local plaquettes/stars are boundaries.
-/

noncomputable section

namespace Quantum.StabilizerGroup.ToricCodeN.LoopGaugeApplications

open Quantum
open StabilizerGroup

private instance : Fact (2 ≤ 2) := ⟨by omega⟩
private instance : Fact (0 < 2) := ⟨by omega⟩

/-- Nondegenerate toric lattice sizes, with the size side condition internalized as data. -/
abbrev ToricGaugeSize := {L : ℕ // 2 ≤ L}

/-- Wilson order loop at any nondegenerate toric lattice size. -/
noncomputable def toricWilsonLoopAt (L : ToricGaugeSize) (i : Fin 2) :
    NQubitPauliGroupElement (numQubits L.1) := by
  letI : Fact (2 ≤ L.1) := ⟨L.2⟩
  exact (toricStabilizerCode L.1).logicalZ i

/-- Dual 't Hooft disorder loop at any nondegenerate toric lattice size. -/
noncomputable def toricTHooftLoopAt (L : ToricGaugeSize) (i : Fin 2) :
    NQubitPauliGroupElement (numQubits L.1) := by
  letI : Fact (2 ≤ L.1) := ⟨L.2⟩
  exact (toricStabilizerCode L.1).logicalX i

/-- Size-uniform Wilson--'t Hooft intersection algebra, without an external size premise. -/
theorem toric_wilson_tHooft_anticommute_at
    (L : ToricGaugeSize) (i : Fin 2) :
    NQubitPauliGroupElement.Anticommute
      (toricTHooftLoopAt L i) (toricWilsonLoopAt L i) := by
  letI : Fact (2 ≤ L.1) := ⟨L.2⟩
  simpa [toricTHooftLoopAt, toricWilsonLoopAt,
    StabilizerCode.logicalX, StabilizerCode.logicalZ] using
    ((toricStabilizerCode L.1).logicalOps i).anticommute

/-- Wilson order loop on either of the two fundamental torus cycles. -/
noncomputable def toricWilsonLoop (i : Fin 2) :
    NQubitPauliGroupElement (numQubits 2) :=
  (toricStabilizerCode 2).logicalZ i

/-- Dual 't Hooft disorder loop on either fundamental torus cycle. -/
noncomputable def toricTHooftLoop (i : Fin 2) :
    NQubitPauliGroupElement (numQubits 2) :=
  (toricStabilizerCode 2).logicalX i

/-- Wilson--'t Hooft algebra: matching primal and dual loops anticommute. -/
theorem toric_wilson_tHooft_anticommute (i : Fin 2) :
    NQubitPauliGroupElement.Anticommute
      (toricTHooftLoop i) (toricWilsonLoop i) := by
  exact ((toricStabilizerCode 2).logicalOps i).anticommute

/-- Primal lattice Bianchi identity: boundary of every plaquette 2-chain has no endpoint. -/
theorem toric_plaquette_bianchi (f : Quantum.Stabilizer.Lattice.C2 2) :
    Quantum.Stabilizer.Lattice.toricBoundary1 (L := 2)
      (Quantum.Stabilizer.Lattice.toricBoundary2 (L := 2) f) = 0 :=
  Quantum.Stabilizer.Lattice.toricBoundary_comp_zero_apply (L := 2) f

/-- Dual lattice Bianchi identity: every dual boundary is a dual cycle. -/
theorem toric_dual_plaquette_bianchi :
    Quantum.Stabilizer.Lattice.toricDualBoundaries (L := 2) ≤
      Quantum.Stabilizer.Lattice.toricDualCycles (L := 2) :=
  Quantum.Stabilizer.Lattice.toricDualBoundaries_le_toricDualCycles 2

/-- Each 't Hooft loop survives quotienting by local stabilizer gauge transformations. -/
theorem toric_tHooftLoop_nontrivial (i : Fin 2) :
    IsNontrivialLogicalOperator
      (toricTHooftLoop i) (toricStabilizerCode 2).toStabilizerGroup := by
  exact (toricStabilizerCode 2).logicalX_nontrivial i

/-- Each Wilson loop survives quotienting by local stabilizer gauge transformations. -/
theorem toric_wilsonLoop_nontrivial (i : Fin 2) :
    IsNontrivialLogicalOperator
      (toricWilsonLoop i) (toricStabilizerCode 2).toStabilizerGroup := by
  exact (toricStabilizerCode 2).logicalZ_nontrivial i

/-- The two independent torus directions have zero mutual intersection pairing. -/
theorem toric_cross_loop_pairs_commute :
    toricTHooftLoop 0 * toricTHooftLoop 1 =
        toricTHooftLoop 1 * toricTHooftLoop 0 ∧
      toricTHooftLoop 0 * toricWilsonLoop 1 =
        toricWilsonLoop 1 * toricTHooftLoop 0 ∧
      toricWilsonLoop 0 * toricTHooftLoop 1 =
        toricTHooftLoop 1 * toricWilsonLoop 0 ∧
      toricWilsonLoop 0 * toricWilsonLoop 1 =
        toricWilsonLoop 1 * toricWilsonLoop 0 := by
  exact (toricStabilizerCode 2).logical_commute_cross 0 1 (by decide)

open Stabilizer.Lattice

/-- Primal lattice-gauge dictionary at the smallest nondegenerate torus. -/
theorem toric_primal_loop_dictionary (c : C1 2) :
    (xCommutesWithZChecks 2 c ↔ c ∈ toricCycles (L := 2)) ∧
      (xIsPlaquetteProduct 2 c ↔ c ∈ toricBoundaries (L := 2)) ∧
      (IsNontrivialLogicalOperator
          (toricXOperatorOfChain 2 c) (stabilizerGroup 2) ↔
        c ∈ toricCycles (L := 2) ∧ c ∉ toricBoundaries (L := 2)) := by
  exact ⟨xCommutesWithZChecks_iff_mem_toricCycles 2 c,
    xIsPlaquetteProduct_iff_mem_toricBoundaries 2 c,
    xNontrivialLogical_iff_cycle_not_boundary 2 c⟩

/-- Dual lattice-gauge dictionary at the smallest nondegenerate torus. -/
theorem toric_dual_loop_dictionary (c : C1 2) :
    (zCommutesWithXChecks 2 c ↔ c ∈ toricDualCycles (L := 2)) ∧
      (zIsStarProduct 2 c ↔ c ∈ toricDualBoundaries (L := 2)) ∧
      (IsNontrivialLogicalOperator
          (toricZOperatorOfChain 2 c) (stabilizerGroup 2) ↔
        c ∈ toricDualCycles (L := 2) ∧ c ∉ toricDualBoundaries (L := 2)) := by
  exact ⟨zCommutesWithXChecks_iff_mem_toricDualCycles 2 c,
    zIsStarProduct_iff_mem_toricDualBoundaries 2 c,
    zNontrivialLogical_iff_dualCycle_not_dualBoundary 2 c⟩

end Quantum.StabilizerGroup.ToricCodeN.LoopGaugeApplications
