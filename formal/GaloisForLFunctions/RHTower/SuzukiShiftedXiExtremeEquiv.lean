import GaloisForLFunctions.RHTower.SuzukiShiftedXiExtremeSplit

open Complex Set

namespace RHTower

noncomputable section

/-- Multiplicity copies strictly beyond the reflected left shifted line. -/
abbrev XiShiftLeftZeroCopy (omega : ℝ) :=
  {q : XiZeroCopy // (I * xiSpectralPoint q).re < -omega}

/-- Functional-equation reflection matches right and left shifted tails copy for copy. -/
def xiShiftRightLeftReflectEquiv (omega : ℝ) :
    XiShiftRightZeroCopy omega ≃ XiShiftLeftZeroCopy omega :=
  Equiv.subtypeEquiv xiZeroCopyReflectEquiv (fun q => by
    rw [xiSpectralPoint_reflect]
    have h : (I * -xiSpectralPoint q).re =
        -(I * xiSpectralPoint q).re := by
      norm_num [mul_re]
    rw [h]
    constructor <;> intro hq <;> linarith)

/-- At nonnegative width, the two-tailed divisor is two copies of its right tail. -/
def xiShiftExtremeSumEquiv (omega : ℝ) (homega : 0 ≤ omega) :
    XiShiftExtremeZeroCopy omega ≃
      XiShiftRightZeroCopy omega ⊕ XiShiftRightZeroCopy omega := by
  let extreme : Set XiZeroCopy :=
    {q | omega < |(I * xiSpectralPoint q).re|}
  let right : Set XiZeroCopy :=
    {q | omega < (I * xiSpectralPoint q).re}
  let left : Set XiZeroCopy :=
    {q | (I * xiSpectralPoint q).re < -omega}
  have hpartition : extreme = right ∪ left := by
    ext q
    simp only [extreme, right, left, Set.mem_setOf_eq, Set.mem_union]
    let t : ℝ := (I * xiSpectralPoint q).re
    change omega < |t| ↔ omega < t ∨ t < -omega
    constructor
    · intro h
      by_cases ht : 0 ≤ t
      · exact Or.inl (by simpa only [abs_of_nonneg ht] using h)
      · right
        rw [abs_of_neg (lt_of_not_ge ht)] at h
        linarith
    · rintro (h | h)
      · have ht : 0 < t := lt_of_le_of_lt homega h
        simpa only [abs_of_pos ht] using h
      · have ht : t < 0 := lt_of_lt_of_le h (neg_nonpos.mpr homega)
        rw [abs_of_neg ht]
        linarith
  have hdisjoint : Disjoint right left := by
    apply Set.disjoint_left.mpr
    intro q hright hleft
    change omega < (I * xiSpectralPoint q).re at hright
    change (I * xiSpectralPoint q).re < -omega at hleft
    linarith
  let eUnion : (right ∪ left : Set XiZeroCopy) ≃
      (right : Set XiZeroCopy) ⊕ (left : Set XiZeroCopy) :=
    Equiv.Set.union hdisjoint
  let eTails : (right : Set XiZeroCopy) ⊕ (left : Set XiZeroCopy) ≃
      XiShiftRightZeroCopy omega ⊕ XiShiftRightZeroCopy omega :=
    Equiv.sumCongr (Equiv.refl _) (xiShiftRightLeftReflectEquiv omega).symm
  exact (Equiv.setCongr hpartition).trans (eUnion.trans eTails)

/-- Finiteness of the selected right divisor makes the full two-tailed divisor finite. -/
@[reducible] noncomputable def xiShiftExtremeFintype (omega : ℝ) (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] :
    Fintype (XiShiftExtremeZeroCopy omega) :=
  Fintype.ofEquiv
    (XiShiftRightZeroCopy omega ⊕ XiShiftRightZeroCopy omega)
    (xiShiftExtremeSumEquiv omega homega).symm

theorem card_xiShiftExtremeZeroCopy (omega : ℝ) (homega : 0 ≤ omega)
    [Fintype (XiShiftRightZeroCopy omega)] :
    @Fintype.card (XiShiftExtremeZeroCopy omega)
        (xiShiftExtremeFintype omega homega) =
      2 * Fintype.card (XiShiftRightZeroCopy omega) := by
  letI : Fintype (XiShiftExtremeZeroCopy omega) :=
    xiShiftExtremeFintype omega homega
  rw [Fintype.card_congr (xiShiftExtremeSumEquiv omega homega)]
  simp
  omega

end

end RHTower
