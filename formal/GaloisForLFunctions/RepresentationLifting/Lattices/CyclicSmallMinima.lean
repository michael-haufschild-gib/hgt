import GaloisForLFunctions.RepresentationLifting.Lattices.CyclicDifferenceEnergy
import GaloisForLFunctions.HTGeometry.Lattices.SmallZeroSumEnergy

/-!
# The two small cyclic difference minima

The cyclic difference lattice has minimum squared norm eight at group order
two and six at group order three. The lower bounds follow from integral
zero-sum energy exclusions; differences of adjacent roots attain them.
Together with the four-coordinate witness, this determines the minimum for
every nontrivial finite cyclic group.
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry.IntegralZeroSum
variable (G : Type) [CommGroup G] [Fintype G] [IsCyclic G]

/-- At group order three, every nonzero cyclic difference has squared norm at least six. -/
theorem cyclicDifference_energy_ge_six (hn : Fintype.card G = 3)
    (v : CyclicDifferenceLattice G) (hv : v ≠ 0) : 6 ≤ cyclicMovingEnergy G v := by
  have h4 := cyclicDifference_energy_ge_four G v hv
  have hne : cyclicMovingEnergy G v ≠ 4 :=
    energy_ne_four_of_card_le_three (cyclicMovingProfile_sum G v) hn.le
  obtain ⟨k, hk⟩ := cyclicMovingEnergy_even G v
  omega

/-- At group order two, every nonzero cyclic difference has squared norm at least eight. -/
theorem cyclicDifference_energy_ge_eight (hn : Fintype.card G = 2)
    (v : CyclicDifferenceLattice G) (hv : v ≠ 0) : 8 ≤ cyclicMovingEnergy G v := by
  have h4 := cyclicDifference_energy_ge_four G v hv
  have hne4 : cyclicMovingEnergy G v ≠ 4 :=
    energy_ne_four_of_card_le_three (cyclicMovingProfile_sum G v) (by omega)
  have hne6 : cyclicMovingEnergy G v ≠ 6 :=
    energy_ne_six_of_card_two (cyclicMovingProfile_sum G v) hn
  obtain ⟨k, hk⟩ := cyclicMovingEnergy_even G v
  omega

/-- At group order two, a difference of an adjacent root has squared norm eight. -/
theorem cyclicDifference_energy_eight_exists (hn : Fintype.card G = 2) :
    ∃ v : CyclicDifferenceLattice G, cyclicMovingEnergy G v = 8 := by
  classical
  let σ := cyclicRegularGenerator G
  have hord : orderOf σ = 2 := (cyclicRegularGenerator_order G).trans hn
  have hs : σ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    omega
  have hsq : σ * σ = 1 := by
    rw [← pow_two, ← hord]
    exact pow_orderOf_eq_one σ
  refine ⟨⟨cyclicMovingDelta G (cyclicRootVector G 1 σ), ⟨_, rfl⟩⟩, ?_⟩
  change energy (cyclicMovingProfile G (cyclicMovingDelta G (cyclicRootVector G 1 σ))) = 8
  rw [cyclicMovingDelta_root, map_sub, cyclicMovingProfile_root, cyclicMovingProfile_root]
  change energy (root (σ * 1) (σ * σ) - root 1 σ) = 8
  rw [mul_one, hsq, energy_sub, energy_root, energy_root,
    if_neg hs, if_neg (Ne.symm hs), pairing_root_left]
  simp [root, hs, Ne.symm hs]

/-- At group order three, a difference of an adjacent root has squared norm six. -/
theorem cyclicDifference_energy_six_exists (hn : Fintype.card G = 3) :
    ∃ v : CyclicDifferenceLattice G, cyclicMovingEnergy G v = 6 := by
  classical
  let σ := cyclicRegularGenerator G
  have hne (a b : ℕ) (ha : a < 3) (hb : b < 3) (hab : a ≠ b) : σ ^ a ≠ σ ^ b := by
    intro h
    apply hab
    exact pow_injOn_Iio_orderOf
      (by change a < orderOf σ; rw [cyclicRegularGenerator_order, hn]; exact ha)
      (by change b < orderOf σ; rw [cyclicRegularGenerator_order, hn]; exact hb) h
  have h01 := hne 0 1 (by omega) (by omega) (by omega)
  have h02 := hne 0 2 (by omega) (by omega) (by omega)
  have h12 := hne 1 2 (by omega) (by omega) (by omega)
  simp only [pow_zero, pow_one] at h01 h02 h12
  refine ⟨⟨cyclicMovingDelta G (cyclicRootVector G 1 σ), ⟨_, rfl⟩⟩, ?_⟩
  change energy (cyclicMovingProfile G (cyclicMovingDelta G (cyclicRootVector G 1 σ))) = 6
  rw [cyclicMovingDelta_root, map_sub, cyclicMovingProfile_root, cyclicMovingProfile_root]
  change energy (root (σ * 1) (σ * σ) - root 1 σ) = 6
  rw [mul_one, ← pow_two, energy_sub, energy_root, energy_root,
    if_neg h12, if_neg h01, pairing_root_left]
  simp [root, h02, Ne.symm h01, Ne.symm h12]

#print axioms cyclicDifference_energy_ge_eight
#print axioms cyclicDifference_energy_ge_six
#print axioms cyclicDifference_energy_eight_exists
#print axioms cyclicDifference_energy_six_exists
end GaloisForLFunctions.RepresentationLifting
