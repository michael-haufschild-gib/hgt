import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.SchurClosedCodes
import GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes.FiberCSSDistance

/-!
# The distance boundary for binary coordinate algebras

A self-orthogonal algebra of binary coordinate functions is a partition
code with even block sizes. If every block has size two, its symmetric
CSS complex has zero first homology. Otherwise two coordinates in a
larger block support a nontrivial logical operator, and exact Pauli
distance is two.

This classification identifies the obstruction to obtaining distance
at least three from unital codes closed under coordinatewise products.
The block decomposition also gives the minimal logical witnesses.
-/

noncomputable section
open scoped BigOperators Classical
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
open Quantum.Stabilizer.Homological
variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-- Every self-orthogonal binary coordinate algebra has zero first homology or exact distance two. -/
theorem binaryCoordinateAlgebra_homology_zero_or_distance_two
    (A : Subalgebra (ZMod 2) (ι → ZMod 2))
    (hA : SelfOrthogonal (RingHom.id _) A.toSubmodule) :
    let X := selfOrthogonalHomologicalCode A.toSubmodule hA
    Module.finrank (ZMod 2) X.H1 = 0 ∨
      ((∀ g : Quantum.NQubitPauliGroupElement X.numQubits,
        Quantum.StabilizerGroup.IsNontrivialLogicalOperator g X.homologicalStabilizerGroup →
          2 ≤ Quantum.NQubitPauliGroupElement.weight g) ∧
      ∃ g : Quantum.NQubitPauliGroupElement X.numQubits,
        Quantum.StabilizerGroup.IsNontrivialLogicalOperator g X.homologicalStabilizerGroup ∧
          Quantum.NQubitPauliGroupElement.weight g = 2) := by
  letI : Fintype (Quotient (coordinateSetoid A)) := Fintype.ofFinite _
  have heven := (coordinateSubalgebra_selfOrthogonal_iff A 2 (RingHom.id _)).mp hA
  by_cases hbig : ∃ b, 2 < Nat.card {i // coordinateProjection A i = b}
  · right
    obtain ⟨b, hb⟩ := hbig
    have hcode := subalgebra_eq_coordinateFiberCode A
    constructor
    · exact unitalBinaryHomologicalCode_logical_weight_ge_two _ hA A.one_mem
    · apply homological_exists_logical_weight
      obtain ⟨c, hc, hnot, hw⟩ :=
        fiberCode_exists_weight_two_nonboundary (coordinateProjection A) b hb
      refine ⟨c, ?_, ?_, hw⟩
      · apply (binaryCheckSyndrome_eq_zero_iff A.toSubmodule c).mpr
        intro d hd
        exact hc d (hcode ▸ hd)
      · intro hmem
        change c ∈ LinearMap.range (binaryCheckEmbedding A.toSubmodule) at hmem
        rw [binaryCheckEmbedding_range] at hmem
        exact hnot (hcode ▸ hmem)
  · left
    have htwo (b : Quotient (coordinateSetoid A)) :
        Nat.card {i // coordinateProjection A i = b} = 2 := by
      have hle : Nat.card {i // coordinateProjection A i = b} ≤ 2 :=
        Nat.le_of_not_gt (fun h => hbig ⟨b, h⟩)
      obtain ⟨i, hi⟩ := coordinateProjection_surjective A b
      letI : Nonempty {i // coordinateProjection A i = b} := ⟨⟨i, hi⟩⟩
      have hpos : 0 < Nat.card {i // coordinateProjection A i = b} := Nat.card_pos
      obtain ⟨k, hk⟩ := heven b
      omega
    have hcard : Fintype.card ι = 2 * Nat.card (Quotient (coordinateSetoid A)) := by
      have h := Finset.card_eq_sum_card_fiberwise (f := coordinateProjection A)
        (s := Finset.univ) (t := Finset.univ) (fun _ _ => Finset.mem_univ _)
      have hs : (∑ b : Quotient (coordinateSetoid A),
          Nat.card {i // coordinateProjection A i = b}) =
          2 * Nat.card (Quotient (coordinateSetoid A)) := by
        calc
          _ = ∑ _b : Quotient (coordinateSetoid A), (2 : ℕ) :=
            Finset.sum_congr rfl (fun b _ => htwo b)
          _ = _ := by simp [Nat.card_eq_fintype_card, Nat.mul_comm]
      rw [← hs]
      simpa only [Finset.card_univ, Nat.card_eq_fintype_card, Fintype.card_subtype] using h
    rw [selfOrthogonalHomologicalCode_finrank_H1]
    change Fintype.card ι - 2 * Module.finrank (ZMod 2) A = 0
    rw [coordinateSubalgebra_finrank, hcard, Nat.sub_self]

#print axioms binaryCoordinateAlgebra_homology_zero_or_distance_two
end GaloisForLFunctions.ArithmeticHarmonicAnalysis.Codes
