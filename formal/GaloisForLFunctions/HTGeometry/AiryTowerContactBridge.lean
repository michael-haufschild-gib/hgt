import GaloisForLFunctions.HTGeometry.AiryTowerSeparatedCore
import GaloisForLFunctions.HTGeometry.StokesDecoratedCore

/-!
# Contact-coordinate bridges for Airy towers

The signed loop formula becomes complementary contact after division by squared ramification.  On
the leading-separated locus, the edge formula becomes reciprocal-min contact.  These identities
connect the arithmetic Airy modules to the universal decorated-core contact coordinate.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

/-- Complementary diagonal contact of a characteristic. -/
def Characteristic.complementaryContact {R beta : ℕ} (c : Characteristic R beta) : ℚ :=
  (c.weightedIrregularity : ℚ) / (R : ℚ) ^ 2

/-- Exact loop/contact identity. -/
theorem Characteristic.complementaryContact_eq_loop {R beta : ℕ}
    (c : Characteristic R beta) :
    c.complementaryContact =
      1 + (((c.diagonalLoop - 1 : ℤ) : ℚ) / (R : ℚ) ^ 2) := by
  have hR : (R : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.zero_lt_one.trans c.ramification_gt_one))
  simp only [Characteristic.complementaryContact, Characteristic.diagonalLoop]
  push_cast
  field_simp
  ring

/-- Zero loop is exactly the critical contact value `1-r⁻²`. -/
theorem Characteristic.complementaryContact_eq_critical_of_loop_zero {R beta : ℕ}
    (c : Characteristic R beta) (hloop : c.diagonalLoop = 0) :
    c.complementaryContact = 1 - 1 / (R : ℚ) ^ 2 := by
  rw [c.complementaryContact_eq_loop, hloop]
  norm_num
  ring

/-- Every Airy tower has critical complementary contact. -/
theorem Characteristic.complementaryContact_eq_critical_of_isAiryTower {R beta : ℕ}
    (c : Characteristic R beta) (hairy : c.IsAiryTower) :
    c.complementaryContact = 1 - 1 / (R : ℚ) ^ 2 := by
  apply c.complementaryContact_eq_critical_of_loop_zero
  exact (c.diagonalLoop_eq_zero_iff_isAiryTower).2 hairy

/-- Complementary contact of a leading-separated pair. -/
def separatedPairContact {R S : ℕ} (x : AiryHead R) (y : AiryHead S) : ℚ :=
  1 + (separatedEdge x y : ℚ) / ((R : ℚ) * (S : ℚ))

/-- Leading-separated contact is the reciprocal of the smaller first factor. -/
theorem separatedPairContact_eq_reciprocalMin {R S : ℕ} (x : AiryHead R) (y : AiryHead S) :
    separatedPairContact x y = 1 + separatedRescaledWeight x.firstFactor y.firstFactor := by
  have hxFactor : 0 < x.firstFactor := lt_of_lt_of_le Nat.zero_lt_two x.factor_ge_two
  have hyFactor : 0 < y.firstFactor := lt_of_lt_of_le Nat.zero_lt_two y.factor_ge_two
  have hRnat : 0 < R := by
    rw [x.ramification_eq]
    exact Nat.mul_pos hxFactor x.next_pos
  have hSnat : 0 < S := by
    rw [y.ramification_eq]
    exact Nat.mul_pos hyFactor y.next_pos
  have hR : 0 < (R : ℚ) := by
    exact_mod_cast hRnat
  have hS : 0 < (S : ℚ) := by
    exact_mod_cast hSnat
  have hxFactorQ : (x.firstFactor : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hxFactor)
  have hyFactorQ : (y.firstFactor : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hyFactor)
  have hxRamification : (R : ℚ) = x.firstFactor * x.nextRamification := by
    exact_mod_cast x.ramification_eq
  have hyRamification : (S : ℚ) = y.firstFactor * y.nextRamification := by
    exact_mod_cast y.ramification_eq
  rcases le_total x.firstFactor y.firstFactor with hxy | hyx
  · rw [separatedPairContact, separatedRescaledWeight, min_eq_left hxy,
      separatedEdge_eq_right_mul_next_of_le x y hxy]
    push_cast
    field_simp [ne_of_gt hR, ne_of_gt hS, hxFactorQ]
    nlinarith [hxRamification]
  · rw [separatedPairContact, separatedRescaledWeight, min_eq_right hyx,
      separatedEdge_eq_left_mul_next_of_le x y hyx]
    push_cast
    field_simp [ne_of_gt hR, ne_of_gt hS, hyFactorQ]
    nlinarith [hyRamification]

end IrregularStokes
end GaloisForLFunctions
