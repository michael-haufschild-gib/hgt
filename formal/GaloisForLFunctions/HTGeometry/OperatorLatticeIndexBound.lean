import GaloisForLFunctions.HTGeometry.DifferentialOperatorSubmoduleSplitting
import GaloisForLFunctions.HTGeometry.DifferentialOperatorTorsionDimension

/-!
# A quantitative bound for the index of a lattice pair

Combining the generator count for submodules of a free module with the quantitative torsion bound
gives an explicit estimate: if a lattice is supported on `t` coordinates and every element of it is
carried into a sublattice by a nonzero operator of order at most `D`, then the index of the pair is
at most `t.card * D`.

This is the crude majorization underlying the extremality of coordinate cuts.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K] {ι : Type*} [DecidableEq ι]

/-- **Index bound for a lattice pair.** -/
theorem finrank_quotient_le_card_mul (t : Finset ι) {L N : Submodule (DiffOp K) (ι → DiffOp K)}
    (hN : N ≤ coordSupport t) (D : ℕ)
    (htors : ∀ y ∈ N, ∃ b : DiffOp K, b ≠ 0 ∧ degree b ≤ D ∧ b • y ∈ L) :
    Module.finrank K ((N.restrictScalars K).map (L.restrictScalars K).mkQ) ≤ t.card * D := by
  classical
  obtain ⟨s, hcard, hspan⟩ := exists_generators_card_le t N hN
  have hsub : ∀ y ∈ s, y ∈ N := by
    intro y hy
    rw [← hspan]
    exact Submodule.subset_span (Finset.mem_coe.mpr hy)
  have hex : ∀ y : ι → DiffOp K,
      ∃ b : DiffOp K, y ∈ N → (b ≠ 0 ∧ degree b ≤ D ∧ b • y ∈ L) := by
    intro y
    by_cases hy : y ∈ N
    · obtain ⟨b, hb0, hbd, hbL⟩ := htors y hy
      exact ⟨b, fun _ => ⟨hb0, hbd, hbL⟩⟩
    · exact ⟨1, fun h => absurd h hy⟩
  choose b hb using hex
  have hb0 : ∀ y ∈ s, b y ≠ 0 := fun y hy => (hb y (hsub y hy)).1
  have hbL : ∀ y ∈ s, b y • y ∈ L := fun y hy => (hb y (hsub y hy)).2.2
  have hbound := finrank_map_mkQ_le_sum_degree L s b hb0 hbL
  rw [hspan] at hbound
  refine le_trans hbound ?_
  have hsum : ∑ y ∈ s, degree (b y) ≤ ∑ _y ∈ s, D :=
    Finset.sum_le_sum fun y hy => (hb y (hsub y hy)).2.1
  have hconst : ∑ _y ∈ s, D = s.card * D := by
    rw [Finset.sum_const, smul_eq_mul]
  have hmul : s.card * D ≤ t.card * D := Nat.mul_le_mul_right D hcard
  omega

end

end DiffOp

end GaloisForLFunctions.HTGeometry
