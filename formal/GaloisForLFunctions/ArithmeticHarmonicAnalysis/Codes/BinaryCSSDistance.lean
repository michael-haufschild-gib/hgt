import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.BinaryAffineDualDistance
import GaloisForLFunctions.QECLean.Stabilizer.Framework.Homological.Distance

/-!
# Exact Pauli distance of the affine binary CSS family

For binary cubes of dimension at least four, the least weight of a
nontrivial logical Pauli operator is exactly four. Coordinate moments
give the lower bound; the indicator of a coordinate plane gives an
actual logical operator attaining it.

The symmetric check construction identifies the dual cycle and boundary
spaces with their original counterparts, so the same support bound
controls both Pauli components. Logical nontriviality excludes phase-only
stabilizer cosets.
-/

noncomputable section
open scoped Classical
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
open Quantum.Stabilizer.Homological
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Chain weight and Hamming weight count the same nonzero coordinates. -/
theorem homological_chainWeight_eq_weight (X : HomologicalCode) (c : X.C1 → ZMod 2) :
    X.chainWeight c = weight c := by
  unfold HomologicalCode.chainWeight HomologicalCode.chainSupport weight
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter]

/-- The transpose boundary is precisely the original syndrome map. -/
theorem selfOrthogonalHomologicalCode_dualBoundary
    (C : Submodule (ZMod 2) (ι → ZMod 2)) (hC : SelfOrthogonal (RingHom.id _) C) :
    (selfOrthogonalHomologicalCode C hC).dualBoundary = binaryCheckSyndrome C := by
  ext c j
  rfl

/-- The two cycle spaces coincide for the symmetric CSS construction. -/
theorem selfOrthogonalHomologicalCode_dualCycles
    (C : Submodule (ZMod 2) (ι → ZMod 2)) (hC : SelfOrthogonal (RingHom.id _) C) :
    (selfOrthogonalHomologicalCode C hC).dualCycles =
      (selfOrthogonalHomologicalCode C hC).cycles := by
  change LinearMap.ker (selfOrthogonalHomologicalCode C hC).dualBoundary =
    LinearMap.ker (binaryCheckSyndrome C)
  exact congrArg LinearMap.ker (selfOrthogonalHomologicalCode_dualBoundary C hC)

/-- The two boundary spaces coincide for the symmetric CSS construction. -/
theorem selfOrthogonalHomologicalCode_dualBoundaries
    (C : Submodule (ZMod 2) (ι → ZMod 2)) (hC : SelfOrthogonal (RingHom.id _) C) :
    (selfOrthogonalHomologicalCode C hC).dualBoundaries =
      (selfOrthogonalHomologicalCode C hC).boundaries := by
  change LinearMap.range (selfOrthogonalHomologicalCode C hC).cutMap =
    LinearMap.range (binaryCheckEmbedding C)
  exact congrArg LinearMap.range (selfOrthogonalHomologicalCode_cutMap C hC)

/-- A non-boundary cycle supplies an actual logical Pauli operator of the same weight. -/
theorem homological_exists_logical_weight (X : HomologicalCode) (w : ℕ)
    (h : ∃ c : X.C1 → ZMod 2, c ∈ X.cycles ∧ c ∉ X.boundaries ∧ weight c = w) :
    ∃ g : Quantum.NQubitPauliGroupElement X.numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g X.homologicalStabilizerGroup ∧
        Quantum.NQubitPauliGroupElement.weight g = w := by
  obtain ⟨c, hc, hb, hw⟩ := h
  refine ⟨X.chainXOperator c,
    (HomologicalCode.chainXOperator_isNontrivialLogical_iff (X := X) c).mpr ⟨hc, hb⟩, ?_⟩
  exact (HomologicalCode.weight_chainXOperator (X := X) c).trans
    ((homological_chainWeight_eq_weight X c).trans hw)

/-- A support bound on cycles modulo checks controls both Pauli components. -/
theorem selfOrthogonalHomologicalCode_logical_weight_ge
    (C : Submodule (ZMod 2) (ι → ZMod 2)) (hC : SelfOrthogonal (RingHom.id _) C)
    (w : ℕ)
    (h : ∀ c ∈ (selfOrthogonalHomologicalCode C hC).cycles,
      c ∉ (selfOrthogonalHomologicalCode C hC).boundaries → w ≤ weight c)
    (g : Quantum.NQubitPauliGroupElement (selfOrthogonalHomologicalCode C hC).numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g
      (selfOrthogonalHomologicalCode C hC).homologicalStabilizerGroup) :
    w ≤ Quantum.NQubitPauliGroupElement.weight g := by
  apply HomologicalCode.chainWeight_lower_bound_transfers
    (selfOrthogonalHomologicalCode C hC) w ?_ ?_ g hg
  · intro c hc hb
    rw [homological_chainWeight_eq_weight]
    exact h c hc hb
  · intro c hc hb
    rw [selfOrthogonalHomologicalCode_dualCycles] at hc
    rw [selfOrthogonalHomologicalCode_dualBoundaries] at hb
    rw [homological_chainWeight_eq_weight]
    exact h c hc hb

/-- Every nontrivial logical Pauli operator has weight at least four. -/
theorem binaryAffineCSSStabilizerGroup_weight_ge_four (n : ℕ)
    (g : Quantum.NQubitPauliGroupElement (binaryAffineHomologicalCode n).numQubits)
    (hg : Quantum.StabilizerGroup.IsNontrivialLogicalOperator g (binaryAffineCSSStabilizerGroup n)) :
    4 ≤ Quantum.NQubitPauliGroupElement.weight g := by
  exact selfOrthogonalHomologicalCode_logical_weight_ge (binaryCubeAffineCode n)
    (binaryCubeAffineCode_selfOrthogonal n) 4
    (binaryAffineHomologicalCode_nonboundary_weight_ge_four n) g hg

/-- A coordinate plane gives an actual nontrivial logical Pauli operator of weight four. -/
theorem binaryAffineCSSStabilizerGroup_exists_weight_four (n : ℕ) :
    ∃ g : Quantum.NQubitPauliGroupElement (binaryAffineHomologicalCode (n + 1)).numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g (binaryAffineCSSStabilizerGroup (n + 1)) ∧
      Quantum.NQubitPauliGroupElement.weight g = 4 := by
  exact homological_exists_logical_weight (binaryAffineHomologicalCode (n + 1)) 4
    (binaryAffineHomologicalCode_exists_weight_four n)

/-- Exact distance four for every affine-cube CSS stabilizer group in dimension at least four. -/
theorem binaryAffineCSSStabilizerGroup_distance_four (n : ℕ) :
    (∀ g : Quantum.NQubitPauliGroupElement (binaryAffineHomologicalCode (n + 1)).numQubits,
      Quantum.StabilizerGroup.IsNontrivialLogicalOperator g (binaryAffineCSSStabilizerGroup (n + 1)) →
        4 ≤ Quantum.NQubitPauliGroupElement.weight g) ∧
      ∃ g : Quantum.NQubitPauliGroupElement (binaryAffineHomologicalCode (n + 1)).numQubits,
        Quantum.StabilizerGroup.IsNontrivialLogicalOperator g (binaryAffineCSSStabilizerGroup (n + 1)) ∧
        Quantum.NQubitPauliGroupElement.weight g = 4 :=
  ⟨binaryAffineCSSStabilizerGroup_weight_ge_four (n + 1),
    binaryAffineCSSStabilizerGroup_exists_weight_four n⟩

#print axioms binaryAffineCSSStabilizerGroup_distance_four
#print axioms selfOrthogonalHomologicalCode_dualBoundary
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
