import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureSevenTenthsCanonicalPacket
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmPrimeGammaExteriorReflectionProjector
import GaloisForLFunctions.HTGeometry.RoundingVarianceFloor

/-!
# Exact canonical HCF shallow/deep census

This module turns the seven-tenths packets into an exact positive-height Xi census.  Critical-line
reflection pairs the left and right off-line support masses without losing analytic multiplicity;
the strict-right mass then splits at `Re rho = 7/10` into the shallow five-center packet and the
Route-T deep packet.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Positive-height Xi supports on the critical line. -/
def criticalFeatureCanonicalCriticalLineSupportPacket (n : ℕ) :
    Finset XiDivisorSupport :=
  (xiSupportsPos (n : ℝ)).filter fun rho => (rho : ℂ).re = 1 / 2

/-- Positive-height Xi supports strictly right of the critical line. -/
def criticalFeatureCanonicalRightSupportPacket (n : ℕ) :
    Finset XiDivisorSupport :=
  (xiSupportsPos (n : ℝ)).filter fun rho => 1 / 2 < (rho : ℂ).re

/-- Positive-height Xi supports strictly left of the critical line. -/
def criticalFeatureCanonicalLeftSupportPacket (n : ℕ) :
    Finset XiDivisorSupport :=
  (xiSupportsPos (n : ℝ)).filter fun rho => (rho : ℂ).re < 1 / 2

/-- Actual positive-height critical-line multiplicity, in the canonical scalar field. -/
def criticalFeatureCanonicalCriticalLineCount (n : ℕ) : ℝ :=
  ∑ rho ∈ criticalFeatureCanonicalCriticalLineSupportPacket n,
    (xiSupportMultiplicity rho : ℝ)

theorem mem_criticalFeatureCanonicalRightSupportPacket
    {n : ℕ} {rho : XiDivisorSupport} :
    rho ∈ criticalFeatureCanonicalRightSupportPacket n ↔
      rho ∈ xiSupportsPos (n : ℝ) ∧ 1 / 2 < (rho : ℂ).re := by
  simp [criticalFeatureCanonicalRightSupportPacket]

theorem mem_criticalFeatureCanonicalLeftSupportPacket
    {n : ℕ} {rho : XiDivisorSupport} :
    rho ∈ criticalFeatureCanonicalLeftSupportPacket n ↔
      rho ∈ xiSupportsPos (n : ℝ) ∧ (rho : ℂ).re < 1 / 2 := by
  simp [criticalFeatureCanonicalLeftSupportPacket]

/-- The strict-right support packet is exactly shallow union deep. -/
theorem criticalFeatureCanonicalRightSupportPacket_eq_shallow_union_deep (n : ℕ) :
    criticalFeatureCanonicalRightSupportPacket n =
      criticalFeatureCanonicalShallowRightSupportPacket n ∪
        criticalFeatureCanonicalDeepRightSupportPacket n := by
  classical
  ext rho
  simp only [criticalFeatureCanonicalRightSupportPacket,
    criticalFeatureCanonicalShallowRightSupportPacket,
    criticalFeatureCanonicalDeepRightSupportPacket, Finset.mem_union, Finset.mem_filter]
  constructor
  · rintro ⟨hrho, hright⟩
    by_cases hshallow : (rho : ℂ).re < 7 / 10
    · exact Or.inl ⟨hrho, hright, hshallow⟩
    · exact Or.inr ⟨hrho, le_of_not_gt hshallow⟩
  · rintro (⟨hrho, hright, _⟩ | ⟨hrho, hdeep⟩)
    · exact ⟨hrho, hright⟩
    · exact ⟨hrho, by linarith [hdeep]⟩

theorem disjoint_criticalFeatureCanonicalShallowRightSupportPacket_deep (n : ℕ) :
    Disjoint (criticalFeatureCanonicalShallowRightSupportPacket n)
      (criticalFeatureCanonicalDeepRightSupportPacket n) := by
  classical
  rw [Finset.disjoint_left]
  intro rho hshallow hdeep
  rw [criticalFeatureCanonicalShallowRightSupportPacket, Finset.mem_filter] at hshallow
  rw [criticalFeatureCanonicalDeepRightSupportPacket, Finset.mem_filter] at hdeep
  linarith [hshallow.2.2, hdeep.2]

private theorem criticalFeatureCanonicalLeftSupportMass_eq_right (n : ℕ) :
    (∑ rho ∈ criticalFeatureCanonicalLeftSupportPacket n,
        (xiSupportMultiplicity rho : ℝ)) =
      ∑ rho ∈ criticalFeatureCanonicalRightSupportPacket n,
        (xiSupportMultiplicity rho : ℝ) := by
  classical
  refine Finset.sum_nbij'
    (i := fun rho : XiDivisorSupport => xiZeroLineConjEquiv rho)
    (j := fun rho : XiDivisorSupport => xiZeroLineConjEquiv rho) ?_ ?_ ?_ ?_ ?_
  · intro rho hrho
    rw [mem_criticalFeatureCanonicalLeftSupportPacket] at hrho
    rw [mem_criticalFeatureCanonicalRightSupportPacket]
    have hre : ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ).re =
        1 - (rho : ℂ).re := by
      rw [xiZeroLineConjEquiv_apply]
      simp
    have him : ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ).im =
        (rho : ℂ).im := by
      rw [xiZeroLineConjEquiv_apply]
      simp
    refine ⟨?_, by rw [hre]; linarith [hrho.2]⟩
    rw [mem_xiSupportsPos] at hrho ⊢
    simpa [him] using hrho.1
  · intro rho hrho
    rw [mem_criticalFeatureCanonicalRightSupportPacket] at hrho
    rw [mem_criticalFeatureCanonicalLeftSupportPacket]
    have hre : ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ).re =
        1 - (rho : ℂ).re := by
      rw [xiZeroLineConjEquiv_apply]
      simp
    have him : ((xiZeroLineConjEquiv rho : XiDivisorSupport) : ℂ).im =
        (rho : ℂ).im := by
      rw [xiZeroLineConjEquiv_apply]
      simp
    refine ⟨?_, by rw [hre]; linarith [hrho.2]⟩
    rw [mem_xiSupportsPos] at hrho ⊢
    simpa [him] using hrho.1
  · intro rho _
    exact xiZeroLineConjEquiv_involutive rho
  · intro rho _
    exact xiZeroLineConjEquiv_involutive rho
  · intro rho _
    rw [xiSupportMultiplicity_lineConj_projector]

private theorem criticalFeatureCanonicalSupportMass_split (n : ℕ) :
    (∑ rho ∈ xiSupportsPos (n : ℝ), (xiSupportMultiplicity rho : ℝ)) =
      criticalFeatureCanonicalCriticalLineCount n +
        2 * (∑ rho ∈ criticalFeatureCanonicalRightSupportPacket n,
          (xiSupportMultiplicity rho : ℝ)) := by
  classical
  let P : Finset XiDivisorSupport := xiSupportsPos (n : ℝ)
  let C : Finset XiDivisorSupport :=
    P.filter fun rho => (rho : ℂ).re = 1 / 2
  let O : Finset XiDivisorSupport :=
    P.filter fun rho => ¬ (rho : ℂ).re = 1 / 2
  let R : Finset XiDivisorSupport :=
    P.filter fun rho => 1 / 2 < (rho : ℂ).re
  let L : Finset XiDivisorSupport :=
    P.filter fun rho => (rho : ℂ).re < 1 / 2
  have hO : O = R ∪ L := by
    ext rho
    simp only [O, R, L, Finset.mem_union, Finset.mem_filter]
    constructor
    · rintro ⟨hrho, hne⟩
      rcases lt_or_gt_of_ne hne with hleft | hright
      · exact Or.inr ⟨hrho, hleft⟩
      · exact Or.inl ⟨hrho, hright⟩
    · rintro (⟨hrho, hright⟩ | ⟨hrho, hleft⟩)
      · exact ⟨hrho, ne_of_gt hright⟩
      · exact ⟨hrho, ne_of_lt hleft⟩
  have hRL : Disjoint R L := by
    rw [Finset.disjoint_left]
    intro rho hrhoR hrhoL
    simp only [R, Finset.mem_filter] at hrhoR
    simp only [L, Finset.mem_filter] at hrhoL
    linarith [hrhoR.2, hrhoL.2]
  have hline := Finset.sum_filter_add_sum_filter_not P
    (fun rho : XiDivisorSupport => (rho : ℂ).re = 1 / 2)
    (fun rho : XiDivisorSupport => (xiSupportMultiplicity rho : ℝ))
  have hline' :
      (∑ rho ∈ C, (xiSupportMultiplicity rho : ℝ)) +
          ∑ rho ∈ O, (xiSupportMultiplicity rho : ℝ) =
        ∑ rho ∈ P, (xiSupportMultiplicity rho : ℝ) := by
    simpa only [C, O] using hline
  have hLR := criticalFeatureCanonicalLeftSupportMass_eq_right n
  have hLR' :
      (∑ rho ∈ L, (xiSupportMultiplicity rho : ℝ)) =
        ∑ rho ∈ R, (xiSupportMultiplicity rho : ℝ) := by
    simpa only [L, R, P, criticalFeatureCanonicalLeftSupportPacket,
      criticalFeatureCanonicalRightSupportPacket] using hLR
  change (∑ rho ∈ P, (xiSupportMultiplicity rho : ℝ)) =
    (∑ rho ∈ C, (xiSupportMultiplicity rho : ℝ)) +
      2 * (∑ rho ∈ R, (xiSupportMultiplicity rho : ℝ))
  rw [← hline', hO, Finset.sum_union hRL, hLR']
  ring

private theorem criticalFeatureCanonicalRightSupportMass_eq_shallow_add_deep (n : ℕ) :
    (∑ rho ∈ criticalFeatureCanonicalRightSupportPacket n,
        (xiSupportMultiplicity rho : ℝ)) =
      ((criticalFeatureCanonicalShallowRightCopyPacket n).card : ℝ) +
        ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) := by
  classical
  have hshallow :
      ((criticalFeatureCanonicalShallowRightCopyPacket n).card : ℝ) =
        ∑ rho ∈ criticalFeatureCanonicalShallowRightSupportPacket n,
          (xiSupportMultiplicity rho : ℝ) := by
    rw [criticalFeatureCanonicalShallowRightCopyPacket,
      card_biUnion_xiZeroCopyFiber]
    norm_cast
  have hdeep :
      ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) =
        ∑ rho ∈ criticalFeatureCanonicalDeepRightSupportPacket n,
          (xiSupportMultiplicity rho : ℝ) := by
    rw [criticalFeatureCanonicalDeepRightCopyPacket,
      card_biUnion_xiZeroCopyFiber]
    norm_cast
  rw [criticalFeatureCanonicalRightSupportPacket_eq_shallow_union_deep,
    Finset.sum_union
      (disjoint_criticalFeatureCanonicalShallowRightSupportPacket_deep n),
    ← hshallow, ← hdeep]

/-- Exact multiplicity census consumed by the shallow/deep 75% receiver. -/
theorem criticalFeatureCanonicalZeroCount_eq_criticalLine_add_two_mul_shallow_deep
    (n : ℕ) :
    criticalFeatureCanonicalZeroCount n =
      criticalFeatureCanonicalCriticalLineCount n +
        2 * (((criticalFeatureCanonicalShallowRightCopyPacket n).card : ℝ) +
          ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ)) := by
  have hN : criticalFeatureCanonicalZeroCount n =
      ∑ rho ∈ xiSupportsPos (n : ℝ), (xiSupportMultiplicity rho : ℝ) := by
    rw [criticalFeatureCanonicalZeroCount,
      xiZeroCount_eq_pos_sum (by positivity : (0 : ℝ) ≤ n)]
    push_cast
    rfl
  rw [hN, criticalFeatureCanonicalSupportMass_split,
    criticalFeatureCanonicalRightSupportMass_eq_shallow_add_deep]

/-- Canonical lattice widened by one radius so every height in `[-n,n]` retains its nearest
integer and the two neighbouring centers on each side. -/
def criticalFeatureCanonicalFiveCenterLatticeWindow (n : ℕ) : Finset ℤ :=
  criticalFeatureCanonicalLatticeWindow (n + 1)

/-- Every canonical shallow copy has all five required centers in the widened lattice. -/
theorem criticalFeatureCanonicalShallowRightCopyPacket_fiveCenters
    {n : ℕ} {q : XiZeroCopy}
    (hq : q ∈ criticalFeatureCanonicalShallowRightCopyPacket n) :
    round (xiSpectralPoint q).re - 2 ∈
        criticalFeatureCanonicalFiveCenterLatticeWindow n ∧
      round (xiSpectralPoint q).re - 1 ∈
        criticalFeatureCanonicalFiveCenterLatticeWindow n ∧
      round (xiSpectralPoint q).re ∈
        criticalFeatureCanonicalFiveCenterLatticeWindow n ∧
      round (xiSpectralPoint q).re + 1 ∈
        criticalFeatureCanonicalFiveCenterLatticeWindow n ∧
      round (xiSpectralPoint q).re + 2 ∈
        criticalFeatureCanonicalFiveCenterLatticeWindow n := by
  have hdata := mem_criticalFeatureCanonicalShallowRightCopyPacket.mp hq
  have hx : |(xiSpectralPoint q).re| ≤ (n : ℝ) := by
    simpa [xiSpectralPoint] using hdata.1
  have herr := HTGeometry.abs_sub_round_le_half (xiSpectralPoint q).re
  rw [abs_le] at hx herr
  have hupperReal : ((round (xiSpectralPoint q).re : ℤ) : ℝ) < n + 1 := by
    linarith [hx.2, herr.1]
  have hlowerReal : -(n : ℝ) - 1 < ((round (xiSpectralPoint q).re : ℤ) : ℝ) := by
    linarith [hx.1, herr.2]
  have hupperInt : round (xiSpectralPoint q).re < (n : ℤ) + 1 := by
    exact_mod_cast hupperReal
  have hlowerInt : -(n : ℤ) - 1 < round (xiSpectralPoint q).re := by
    exact_mod_cast hlowerReal
  have hroundUpper : round (xiSpectralPoint q).re ≤ (n : ℤ) := by omega
  have hroundLower : -(n : ℤ) ≤ round (xiSpectralPoint q).re := by omega
  simp only [criticalFeatureCanonicalFiveCenterLatticeWindow,
    criticalFeatureCanonicalLatticeWindow, Finset.mem_Icc]
  omega

/-- Pointwise canonical 75% receiver.  All divisor bookkeeping, shallow-sector geometry, and
five-center coverage are discharged; only the displayed source budget remains. -/
theorem three_quarters_line_of_canonicalSevenTenthsFiveCenterBudget
    (n : ℕ)
    (hbudget :
      (1 / criticalFeatureShallowReflectedFiveCenterCharge) *
          criticalFeaturePrimeGammaOffLineLatticeBudget
            (criticalFeatureCanonicalFiveCenterLatticeWindow n) +
        ((criticalFeatureCanonicalDeepRightCopyPacket n).card : ℝ) ≤
          criticalFeatureCanonicalZeroCount n / 8) :
    3 * criticalFeatureCanonicalZeroCount n / 4 ≤
      criticalFeatureCanonicalCriticalLineCount n := by
  apply three_quarters_line_of_shallowReflectedFiveCenterCharge_and_deepCount
    (criticalFeatureCanonicalFiveCenterLatticeWindow n)
    (criticalFeatureCanonicalShallowRightCopyPacket n)
    (by
      rw [criticalFeatureCanonicalZeroCount]
      exact_mod_cast xiZeroCount_nonneg (n : ℝ))
  · intro q hq
    exact criticalFeatureCanonicalShallowRightCopyPacket_transverse_pos hq
  · intro q hq
    exact criticalFeatureCanonicalShallowRightCopyPacket_im_le_oneFifth hq
  · intro q hq
    exact criticalFeatureCanonicalShallowRightCopyPacket_fiveCenters hq
  · exact criticalFeatureCanonicalZeroCount_eq_criticalLine_add_two_mul_shallow_deep n
  · exact hbudget

end

end RHTower
