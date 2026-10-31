import GaloisForLFunctions.HTGeometry.RationalDenominatorLadder

/-!
# Orders of rational classes modulo additive subgroups

The cyclic order of a rational class records the first subgroup return. If the
subgroup contains one, this order is positive and divides the reduced denominator.
-/

noncomputable section
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- The additive order of a rational number modulo an additive subgroup. -/
def rationalSubgroupOrder (H : AddSubgroup ℚ) (q : ℚ) : ℕ :=
  addOrderOf ((QuotientAddGroup.mk' H) q)

/-- Natural multiples return to the subgroup exactly at multiples of the quotient order. -/
theorem rationalSubgroupOrder_dvd_iff (H : AddSubgroup ℚ) (q : ℚ) (n : ℕ) :
    rationalSubgroupOrder H q ∣ n ↔ (n : ℚ) * q ∈ H := by
  rw [rationalSubgroupOrder, addOrderOf_dvd_iff_nsmul_eq_zero, ← map_nsmul]
  change (QuotientAddGroup.mk (n • q) : ℚ ⧸ H) = 0 ↔ (n : ℚ) * q ∈ H
  rw [QuotientAddGroup.eq_zero_iff]
  simp only [nsmul_eq_mul]

/-- The quotient order itself gives a subgroup return. -/
theorem rationalSubgroupOrder_mul_mem (H : AddSubgroup ℚ) (q : ℚ) :
    (rationalSubgroupOrder H q : ℚ) * q ∈ H :=
  (rationalSubgroupOrder_dvd_iff H q _).mp (dvd_refl _)

/-- Containing one makes every rational quotient class torsion with denominator period. -/
theorem rationalSubgroupOrder_dvd_den (H : AddSubgroup ℚ) (h1 : (1 : ℚ) ∈ H) (q : ℚ) :
    rationalSubgroupOrder H q ∣ q.den := by
  apply (rationalSubgroupOrder_dvd_iff H q q.den).mpr
  rw [Rat.den_mul_eq_num]
  simpa only [zsmul_eq_mul, mul_one] using H.zsmul_mem h1 q.num

/-- The cyclic quotient order is positive when the subgroup contains the integers. -/
theorem rationalSubgroupOrder_pos (H : AddSubgroup ℚ) (h1 : (1 : ℚ) ∈ H) (q : ℚ) :
    0 < rationalSubgroupOrder H q := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hd := rationalSubgroupOrder_dvd_den H h1 q
  rw [hzero, zero_dvd_iff] at hd
  exact q.den_nz hd

/-- No positive multiple smaller than the quotient order returns to the subgroup. -/
theorem nat_mul_not_mem_below_subgroupOrder (H : AddSubgroup ℚ) (q : ℚ)
    {j : ℕ} (hj : 0 < j) (hjd : j < rationalSubgroupOrder H q) : (j : ℚ) * q ∉ H := by
  intro hmem
  have hd := (rationalSubgroupOrder_dvd_iff H q j).mpr hmem
  exact (not_le_of_gt hjd) (Nat.le_of_dvd hj hd)

/-- Distinct positions before the first return represent different subgroup cosets. -/
theorem nat_difference_not_mem_below_subgroupOrder (H : AddSubgroup ℚ) (q : ℚ)
    {i j : ℕ} (hi : i < rationalSubgroupOrder H q) (hj : j < rationalSubgroupOrder H q)
    (hij : i ≠ j) : ((j : ℚ) - (i : ℚ)) * q ∉ H := by
  by_cases hlt : i < j
  · rw [show (j : ℚ) - (i : ℚ) = ((j - i : ℕ) : ℚ) from (Nat.cast_sub hlt.le).symm]
    exact nat_mul_not_mem_below_subgroupOrder H q (by omega) (by omega)
  · have hgt : j < i := by omega
    intro hmem
    have hreverse := H.neg_mem hmem
    rw [show -(((j : ℚ) - (i : ℚ)) * q) = ((i : ℚ) - (j : ℚ)) * q by ring,
      show (i : ℚ) - (j : ℚ) = ((i - j : ℕ) : ℚ) from (Nat.cast_sub hgt.le).symm] at hreverse
    exact nat_mul_not_mem_below_subgroupOrder H q (by omega) (by omega) hreverse

#print axioms rationalSubgroupOrder_dvd_den
#print axioms rationalSubgroupOrder_pos
#print axioms nat_difference_not_mem_below_subgroupOrder
end GaloisForLFunctions.BiarithmeticGeometry
