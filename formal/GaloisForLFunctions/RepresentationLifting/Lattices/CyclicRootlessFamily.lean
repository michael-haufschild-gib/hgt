import GaloisForLFunctions.RepresentationLifting.Lattices.CyclicMovingGram
import GaloisForLFunctions.RepresentationLifting.Lattices.CyclicSmallMinima

/-!
# An explicit family of even rootless lattices

For the cyclic group of order `n + 4`, the restricted difference image is an
even positive definite lattice of rank `n + 3`, discriminant `(n + 4)^3`, and
minimum squared norm four. The two smaller nontrivial cyclic groups have
minimum squared norms eight and six.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting

/-- The minimum squared norm for a nontrivial finite cyclic group. -/
def cyclicMinimumEnergy (G : Type) [Fintype G] : ℤ :=
  if Fintype.card G = 2 then 8 else if Fintype.card G = 3 then 6 else 4

/-- The exact minimum of every nontrivial cyclic difference lattice, including orders two and three. -/
theorem cyclicDifference_minimum (G : Type) [CommGroup G] [Fintype G]
    [IsCyclic G] [Nontrivial G] :
    (∀ v : CyclicDifferenceLattice G, v ≠ 0 → cyclicMinimumEnergy G ≤ cyclicMovingEnergy G v) ∧
    (∃ v : CyclicDifferenceLattice G, cyclicMovingEnergy G v = cyclicMinimumEnergy G) := by
  by_cases h2 : Fintype.card G = 2
  · simp only [cyclicMinimumEnergy, if_pos h2]
    exact ⟨cyclicDifference_energy_ge_eight G h2, cyclicDifference_energy_eight_exists G h2⟩
  by_cases h3 : Fintype.card G = 3
  · simp only [cyclicMinimumEnergy, if_neg h2, if_pos h3]
    exact ⟨cyclicDifference_energy_ge_six G h3, cyclicDifference_energy_six_exists G h3⟩
  · have hn : 4 ≤ Fintype.card G := by
      have hpos : 1 < Fintype.card G := Fintype.one_lt_card
      omega
    simp only [cyclicMinimumEnergy, if_neg h2, if_neg h3]
    exact ⟨cyclicDifference_energy_ge_four G, cyclicDifference_energy_four_exists G hn⟩

/-- Cyclic groups of every order at least four. -/
abbrev CyclicPackingGroup (n : ℕ) := Multiplicative (ZMod (n + 4))
/-- The rootless cyclic difference lattice at order `n + 4`. -/
abbrev CyclicPackingLattice (n : ℕ) := CyclicDifferenceLattice (CyclicPackingGroup n)

theorem cyclicPackingGroup_card (n : ℕ) : Fintype.card (CyclicPackingGroup n) = n + 4 := by
  classical
  simp [CyclicPackingGroup]

/-- The Gram matrix of the explicit difference basis. -/
def cyclicPackingGram (n : ℕ) :
    Matrix (CyclicMovingIndex (CyclicPackingGroup n)) (CyclicMovingIndex (CyclicPackingGroup n)) ℤ := by
  classical
  exact (cyclicDifferenceForm (CyclicPackingGroup n)).toMatrix (cyclicDifferenceBasis (CyclicPackingGroup n))

/-- The lattice has rank one less than the cyclic group order. -/
theorem cyclicPacking_rank (n : ℕ) : Module.finrank ℤ (CyclicPackingLattice n) = n + 3 := by
  classical
  have h : Module.finrank ℤ (CyclicPackingLattice n) + 1 = n + 4 := by
    simpa only [cyclicPackingGroup_card] using cyclicDifference_rank (CyclicPackingGroup n)
  omega

/-- The discriminant is the cube of the cyclic group order. -/
theorem cyclicPacking_discriminant (n : ℕ) : (cyclicPackingGram n).det = (n + 4 : ℤ)^3 := by
  classical
  rw [cyclicPackingGram, cyclicDifferenceGram_det, cyclicPackingGroup_card]
  norm_cast

/-- Every vector in the constructed lattice has even squared norm. -/
theorem cyclicPacking_even (n : ℕ) (v : CyclicPackingLattice n) :
    Even (cyclicDifferenceForm (CyclicPackingGroup n) v v) :=
  cyclicDifferenceForm_even _ v

/-- The integral pairing is symmetric. -/
theorem cyclicPacking_symmetric (n : ℕ) (v w : CyclicPackingLattice n) :
    cyclicDifferenceForm (CyclicPackingGroup n) v w =
      cyclicDifferenceForm (CyclicPackingGroup n) w v := by
  change HTGeometry.IntegralZeroSum.pairing
      (cyclicMovingProfile (CyclicPackingGroup n) v) (cyclicMovingProfile (CyclicPackingGroup n) w) =
    HTGeometry.IntegralZeroSum.pairing
      (cyclicMovingProfile (CyclicPackingGroup n) w) (cyclicMovingProfile (CyclicPackingGroup n) v)
  exact HTGeometry.IntegralZeroSum.pairing_comm _ _

/-- The minimum squared norm is exactly four in every rank at least three. -/
theorem cyclicPacking_minimum_four (n : ℕ) :
    (∀ v : CyclicPackingLattice n, v ≠ 0 →
      4 ≤ cyclicDifferenceForm (CyclicPackingGroup n) v v) ∧
    (∃ v : CyclicPackingLattice n, cyclicDifferenceForm (CyclicPackingGroup n) v v = 4) := by
  classical
  constructor
  · intro v hv
    rw [cyclicDifferenceForm_diag]
    exact cyclicDifference_energy_ge_four _ v hv
  · obtain ⟨v, hv⟩ := cyclicDifference_energy_four_exists (CyclicPackingGroup n)
      (by rw [cyclicPackingGroup_card]; omega)
    exact ⟨v, (cyclicDifferenceForm_diag _ v).trans hv⟩

/-- The cyclic group of order two yields minimum squared norm eight. -/
theorem cyclicOrderTwo_minimum_eight :
    (∀ v : CyclicDifferenceLattice (Multiplicative (ZMod 2)), v ≠ 0 →
      8 ≤ cyclicMovingEnergy (Multiplicative (ZMod 2)) v) ∧
    (∃ v : CyclicDifferenceLattice (Multiplicative (ZMod 2)), cyclicMovingEnergy (Multiplicative (ZMod 2)) v = 8) := by
  classical
  have hc : Fintype.card (Multiplicative (ZMod 2)) = 2 := by simp
  exact ⟨cyclicDifference_energy_ge_eight (Multiplicative (ZMod 2)) hc, cyclicDifference_energy_eight_exists (Multiplicative (ZMod 2)) hc⟩

/-- The cyclic group of order three yields minimum squared norm six. -/
theorem cyclicOrderThree_minimum_six :
    (∀ v : CyclicDifferenceLattice (Multiplicative (ZMod 3)), v ≠ 0 →
      6 ≤ cyclicMovingEnergy (Multiplicative (ZMod 3)) v) ∧
    (∃ v : CyclicDifferenceLattice (Multiplicative (ZMod 3)), cyclicMovingEnergy (Multiplicative (ZMod 3)) v = 6) := by
  classical
  have hc : Fintype.card (Multiplicative (ZMod 3)) = 3 := by simp
  exact ⟨cyclicDifference_energy_ge_six (Multiplicative (ZMod 3)) hc, cyclicDifference_energy_six_exists (Multiplicative (ZMod 3)) hc⟩

#print axioms cyclicDifference_minimum
#print axioms cyclicPacking_rank
#print axioms cyclicPacking_discriminant
#print axioms cyclicPacking_even
#print axioms cyclicPacking_minimum_four
#print axioms cyclicOrderTwo_minimum_eight
#print axioms cyclicOrderThree_minimum_six
end GaloisForLFunctions.RepresentationLifting
