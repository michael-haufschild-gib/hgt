import GaloisForLFunctions.RepresentationLifting.Lattices.AbelianAugmentationLattice

/-!
# Sharp minimum for finite abelian augmentation squares

A rectangle with labels `1, a, b, a*b` has zero augmentation and first
moment. Choosing `b` outside `1, a, a⁻¹` makes its four coordinates distinct,
so its squared norm is four. Such a choice exists whenever the group has at
least four elements. Combined with root exclusion, this gives the exact minimum.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry.IntegralZeroSum
variable (G : Type) [CommGroup G] [Fintype G]

/-- The alternating group rectangle has zero coefficient sum and first moment. -/
def abelianRectangle (a b : G) : AbelianAugmentationLattice G :=
  ⟨cyclicRootVector G 1 a - cyclicRootVector G b (a * b), by
    change cyclicMovingFirstMoment G (_ - _) = 0
    rw [map_sub, cyclicMovingFirstMoment_root, cyclicMovingFirstMoment_root]
    change (0 - Additive.ofMul a) -
      (Additive.ofMul b - (Additive.ofMul a + Additive.ofMul b)) = 0
    abel⟩

theorem abelianRectangle_energy_four (a b : G) (ha : a ≠ 1) (hb : b ≠ 1)
    (hab : a ≠ b) (hinv : b ≠ a⁻¹) :
    cyclicMovingEnergy G (abelianRectangle G a b) = 4 := by
  classical
  have hprod : a * b ≠ 1 := by
    intro h
    apply hinv
    calc
      b = a⁻¹ * (a * b) := by simp
      _ = a⁻¹ := by rw [h, mul_one]
  have haprod : a ≠ a * b := by simpa using hb
  have hbprod : b ≠ a * b := by simpa using ha
  change energy (cyclicMovingProfile G
    (cyclicRootVector G 1 a - cyclicRootVector G b (a * b))) = 4
  rw [map_sub, cyclicMovingProfile_root, cyclicMovingProfile_root, energy_sub,
    energy_root, energy_root, if_neg ha.symm, if_neg hbprod, pairing_root_left]
  simp [root, hb, hprod, hab, haprod, eq_comm]

theorem abelianAugmentation_energy_four_exists (hn : 4 ≤ Fintype.card G) :
    ∃ v : AbelianAugmentationLattice G, cyclicMovingEnergy G v = 4 := by
  classical
  haveI : Nontrivial G := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨a, ha⟩ := exists_ne (1 : G)
  have hcard : ({1, a, a⁻¹} : Finset G).card < (Finset.univ : Finset G).card := by
    have hle : ({1, a, a⁻¹} : Finset G).card ≤ 3 :=
      (Finset.card_insert_le _ _).trans (by
        have h := Finset.card_insert_le a ({a⁻¹} : Finset G)
        simpa using Nat.add_le_add_right h 1)
    rw [Finset.card_univ]
    omega
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hb
  exact ⟨abelianRectangle G a b,
    abelianRectangle_energy_four G a b ha hb.1 (Ne.symm hb.2.1) hb.2.2⟩

#print axioms abelianAugmentation_energy_four_exists
end GaloisForLFunctions.RepresentationLifting
