import GaloisForLFunctions.ArithmeticIndexDescent.ThePolePaymentRetainsTheUnusedWidthReserve
import GaloisForLFunctions.ArithmeticIndexDescent.TheSourceKernelEnergyBoundsTheSchurCost

/-!
# The original full section width still leaves a strict source reserve

The allowed width is bounded by the small arithmetic spacing ratio itself.
Keeping that bound inside the exponential pole factor costs strictly less than
the previously rounded one-eighth reserve. A positive uniform reserve therefore
remains on the original full-width spaces, without shrinking their supports.
It also reduces the exact source cost of finite and completed projections.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

private theorem sectionRatio_lt_one : fullSectionRatio < 1 := by
  linarith only [fullSectionRatio_le_half_spacing, spacingRatio_lt_half]

/-- A uniform pole charge retaining the actual maximum allowed width. -/
def fullWidthPoleCost : ℝ := fullSectionRatio * (Real.exp fullSectionRatio + 1)

/-- Reserve remaining after that sharper full-width pole payment. -/
def fullWidthSectionReserve : ℝ := 1 / 8 - fullWidthPoleCost

theorem fullWidthPoleCost_lt_eighth : fullWidthPoleCost < 1 / 8 := by
  have he : Real.exp fullSectionRatio + 1 < Real.exp 1 + 1 := by
    linarith only [Real.exp_lt_exp.mpr sectionRatio_lt_one]
  calc
    fullWidthPoleCost < fullSectionRatio * (Real.exp 1 + 1) :=
      mul_lt_mul_of_pos_left he fullSectionRatio_pos
    _ ≤ (1 / (8 * (Real.exp 1 + 1))) * (Real.exp 1 + 1) :=
      mul_le_mul_of_nonneg_right fullSectionRatio_le_pole (by positivity)
    _ = 1 / 8 := by field_simp

theorem fullWidthSectionReserve_pos : 0 < fullWidthSectionReserve :=
  sub_pos.mpr fullWidthPoleCost_lt_eighth

/-- Every originally allowed cell width satisfies the sharper uniform pole budget. -/
theorem sectionPoleCost_le_fullWidthPoleCost {N : ℕ} (hN : 1 ≤ N)
    {w : ℝ} (hw0 : 0 < w) (hw : w ≤ fullSectionRatio * atomSpacing N) :
    sectionPoleCost N w ≤ fullWidthPoleCost := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hwN : w * N ≤ fullSectionRatio := by
    have h := hw.trans (mul_le_mul_of_nonneg_left (atomSpacing_le_inv hN)
      fullSectionRatio_pos.le)
    rw [show fullSectionRatio * (1 / (N : ℝ)) = fullSectionRatio / N by ring,
      le_div_iff₀ hN0] at h
    exact h
  have hwr : w ≤ fullSectionRatio := by
    have hww : w ≤ w * N := by nlinarith only [hw0, hN1]
    exact hww.trans hwN
  exact mul_le_mul hwN (add_le_add (Real.exp_le_exp.mpr hwr) (le_refl (1 : ℝ)))
    (by positivity) fullSectionRatio_pos.le

/-- A strictly positive weighted reserve survives on the whole original section space. -/
theorem weilPair_arithmeticSection_ge_fullWidth_reserve
    {G : ℕ → ℝ → ℝ} {N : ℕ} {w : ℝ}
    (hg : ∀ n, ContDiff ℝ 2 (G n)) (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0)
    (hN : 1 ≤ N) (hw0 : 0 < w) (hw : w ≤ fullSectionRatio * atomSpacing N) :
    (∫ u, arithmeticSection N G u ^ 2) + fullWidthSectionReserve * sectionReserve N G ≤
      weilPair (arithmeticSection N G) (arithmeticSection N G) := by
  have hW := weilPair_arithmeticSection_ge_unused_reserve hg hs hN hw0 hw
  have hcost := mul_le_mul_of_nonneg_right (sectionPoleCost_le_fullWidthPoleCost hN hw0 hw)
    (sectionReserve_nonneg N G)
  change (∫ u, arithmeticSection N G u ^ 2) +
    (1 / 8 - fullWidthPoleCost) * sectionReserve N G ≤ _
  linarith only [hW, hcost]

/-- Full-width arithmetic sections have a uniform mass floor strictly larger than one. -/
theorem realWeilForm_ge_fullWidth_mass {N : ℕ} (hN : 1 ≤ N)
    {w : ℝ} (hw0 : 0 < w) (hw : w ≤ fullSectionRatio * atomSpacing N)
    (p : arithmeticSectionTests N w) :
    (1 + fullWidthSectionReserve) * sectionMass p.1.1 ≤ realWeilForm p.1 p.1 := by
  obtain ⟨G, hg, hs, he⟩ := p.2
  have hwsep : w < atomSpacing N := by
    have h := hw.trans_lt (mul_lt_mul_of_pos_right sectionRatio_lt_one (atomSpacing_pos hN))
    simpa only [one_mul] using h
  have hmass := integral_arithmeticSection_sq (fun n => (hg n).continuous)
    (fun n => profile_hasCompactSupport (hs n)) hs hwsep
  have hreserve : (∫ u, arithmeticSection N G u ^ 2) ≤ sectionReserve N G := by
    rw [hmass]
    apply Finset.sum_le_sum
    intro n _
    simpa only [one_mul] using mul_le_mul_of_nonneg_right
      (sectionReserveWeight_ge_one N n) (sectionMass_nonneg (G n))
  have hW := weilPair_arithmeticSection_ge_fullWidth_reserve hg hs hN hw0 hw
  have hgain := mul_le_mul_of_nonneg_left hreserve fullWidthSectionReserve_pos.le
  change (1 + fullWidthSectionReserve) * (∫ u, p.1.1 u ^ 2) ≤ weilPair p.1.1 p.1.1
  rw [he]
  linarith only [hW, hgain]

/-- The full-width reserve improves the exact-union source cost without changing the old space. -/
theorem arithmeticSectionProjection_energy_le_fullWidth_sourceCost
    {ι : Type*} [Fintype ι] {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
    (hw : w ≤ fullSectionRatio * atomSpacing N)
    (f : ι → arithmeticSectionTests N w) (g : realTests) :
    realWeilForm (arithmeticSectionProjection hN hw0 hw f g)
      (arithmeticSectionProjection hN hw0 hw f g) ≤
      sourceKernelEnergy (arithmeticSectionSupport N w) g / (1 + fullWidthSectionReserve) := by
  let p := arithmeticSectionProjection hN hw0 hw f g
  let A := 1 + fullWidthSectionReserve
  let D := sourceKernelEnergy (arithmeticSectionSupport N w) g
  have hA : 0 < A := add_pos zero_lt_one fullWidthSectionReserve_pos
  have hD : 0 ≤ D := sourceKernelEnergy_nonneg _ g
  have hp : p ∈ arithmeticSectionTests N w := arithmeticSectionProjection_mem hN hw0 hw f g
  have hfloor := realWeilForm_ge_fullWidth_mass hN hw0 hw ⟨p, hp⟩
  have hE : 0 ≤ realWeilForm p p := arithmeticSectionProjection_energy_nonneg hN hw0 hw f g
  have hpair : realWeilForm p g = realWeilForm p p := by
    obtain ⟨c, hc⟩ := (arithmeticSectionProjection_spec hN hw0 hw f g).1
    have horth := arithmeticSectionProjection_orthogonal hN hw0 hw f c g
    rw [← hc, map_sub] at horth
    exact sub_eq_zero.mp horth
  have hcs := realWeilForm_sq_le_mass_mul_sourceKernelEnergy
    (isCompact_arithmeticSectionSupport N w) p g
    (fun _ hu => arithmeticSectionTest_eq_zero_off_support ⟨p, hp⟩ hu)
  rw [hpair] at hcs
  change realWeilForm p p ^ 2 ≤ sectionMass p.1 * D at hcs
  change A * sectionMass p.1 ≤ realWeilForm p p at hfloor
  have hcsA := mul_le_mul_of_nonneg_left hcs hA.le
  rw [← mul_assoc] at hcsA
  have hbudget := hcsA.trans (mul_le_mul_of_nonneg_right hfloor hD)
  change realWeilForm p p ≤ D / A
  by_cases hz : realWeilForm p p = 0
  · rw [hz]
    exact div_nonneg hD hA.le
  · have hpos := lt_of_le_of_ne hE (Ne.symm hz)
    apply (le_div_iff₀ hA).mpr
    by_contra hbad
    have hprod := mul_pos (sub_pos.mpr (lt_of_not_ge hbad)) hpos
    nlinarith only [hbudget, hprod]

/-- The strict full-width payment survives completion of all independent old profiles. -/
theorem sectionCompletionEnergy_le_fullWidth_sourceCost
    {N : ℕ} (hN : 1 ≤ N) {w : ℝ} (hw0 : 0 < w)
    (hw : w ≤ fullSectionRatio * atomSpacing N) (g : realTests) :
    sectionCompletionEnergy hN hw0 hw g ≤
      sourceKernelEnergy (arithmeticSectionSupport N w) g / (1 + fullWidthSectionReserve) := by
  apply ciSup_le
  intro S
  exact arithmeticSectionProjection_energy_le_fullWidth_sourceCost hN hw0 hw (fun p : S => p.1) g

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.fullWidthSectionReserve_pos
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.weilPair_arithmeticSection_ge_fullWidth_reserve
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.realWeilForm_ge_fullWidth_mass
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.sectionCompletionEnergy_le_fullWidth_sourceCost
