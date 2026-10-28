import GaloisForLFunctions.ArithmeticIndexDescent.ThePolePaymentRetainsTheUnusedWidthReserve
import GaloisForLFunctions.ArithmeticIndexDescent.TheSourceKernelEnergyBoundsTheSchurCost

/-!
# Unused arithmetic reserve reduces the exact source cost

At a smaller width, the complete Weil form controls a weighted sum of the
independent profile masses. Applying the combined source kernel on each actual
cell and retaining these weights divides that cell's dual cost by its reserve.
The estimate controls every finite arithmetic projection and its completion.
-/

open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

/-- The full square-mass coefficient left on a cell at width fraction `a`. -/
def sectionDualWeight (N n : ℕ) (a : ℝ) : ℝ :=
  1 + ((1 - a) / 8) * sectionReserveWeight N n

theorem sectionDualWeight_ge_one (N n : ℕ) {a : ℝ} (ha : a ≤ 1) :
    1 ≤ sectionDualWeight N n a := by
  have h := mul_nonneg (div_nonneg (sub_nonneg.mpr ha) (by norm_num : (0 : ℝ) ≤ 8))
    (sectionReserveWeight_pos N n).le
  exact le_add_of_nonneg_right h

theorem sectionDualWeight_pos (N n : ℕ) {a : ℝ} (ha : a ≤ 1) :
    0 < sectionDualWeight N n a := zero_lt_one.trans_le (sectionDualWeight_ge_one N n ha)

/-- The combined source kernel is divided by the reserve on each literal cell. -/
def weightedSectionKernelEnergy (N : ℕ) (w a : ℝ) (g : realTests) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N,
    sourceKernelEnergy (Set.Icc (Real.log n) (Real.log n + w)) g / sectionDualWeight N n a

theorem weightedSectionKernelEnergy_nonneg (N : ℕ) (w : ℝ) {a : ℝ}
    (ha : a ≤ 1) (g : realTests) : 0 ≤ weightedSectionKernelEnergy N w a g :=
  Finset.sum_nonneg fun n _ => div_nonneg (sourceKernelEnergy_nonneg _ g)
    (sectionDualWeight_pos N n ha).le

/-- Below the arithmetic spacing, exact cell energies add without counting a point twice. -/
theorem sourceKernelEnergy_arithmeticSectionSupport_eq_sum {N : ℕ} {w : ℝ}
    (hw : w < atomSpacing N) (g : realTests) :
    sourceKernelEnergy (arithmeticSectionSupport N w) g =
      ∑ n ∈ Finset.Icc 1 N,
        sourceKernelEnergy (Set.Icc (Real.log n) (Real.log n + w)) g := by
  have hd : Set.Pairwise (↑(Finset.Icc 1 N))
      (fun i j : ℕ => Disjoint (Set.Icc (Real.log i) (Real.log i + w))
        (Set.Icc (Real.log j) (Real.log j + w))) := by
    intro i hi j hj hij
    have hi' := Finset.mem_Icc.mp hi
    have hj' := Finset.mem_Icc.mp hj
    apply Set.disjoint_left.mpr
    intro u hui huj
    have hgap := atomSpacing_le_abs_log_sub_of_min hi'.1 hj'.1
      ((min_le_left i j).trans hi'.2) hij
    have hb : |Real.log i - Real.log j| ≤ w := abs_le.mpr
      ⟨by linarith only [hui.1, hui.2, huj.1, huj.2],
       by linarith only [hui.1, hui.2, huj.1, huj.2]⟩
    exact (not_le_of_gt hw) (hgap.trans hb)
  exact integral_biUnion_finset (Finset.Icc 1 N)
    (fun _ _ => measurableSet_Icc) hd (fun _ _ => integrableOn_sourceKernel_sq isCompact_Icc g)

/-- Retaining reserve never increases the previous exact-union source cost. -/
theorem weightedSectionKernelEnergy_le_sourceKernelEnergy {N : ℕ} {w a : ℝ}
    (hw : w < atomSpacing N) (ha : a ≤ 1) (g : realTests) :
    weightedSectionKernelEnergy N w a g ≤ sourceKernelEnergy (arithmeticSectionSupport N w) g := by
  rw [sourceKernelEnergy_arithmeticSectionSupport_eq_sum hw]
  apply Finset.sum_le_sum
  intro n _
  apply (div_le_iff₀ (sectionDualWeight_pos N n ha)).mpr
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (sectionDualWeight_ge_one N n ha) (sourceKernelEnergy_nonneg _ g)

/-- At full width, the weighted source cost returns exactly to the unweighted one. -/
theorem weightedSectionKernelEnergy_one {N : ℕ} {w : ℝ}
    (hw : w < atomSpacing N) (g : realTests) :
    weightedSectionKernelEnergy N w 1 g = sourceKernelEnergy (arithmeticSectionSupport N w) g := by
  rw [sourceKernelEnergy_arithmeticSectionSupport_eq_sum hw]
  simp only [weightedSectionKernelEnergy, sectionDualWeight, sub_self, zero_div,
    zero_mul, add_zero, div_one]

private theorem realWeilForm_young_sourceKernel {s : Set ℝ} (hs : IsCompact s)
    (p g : realTests) (hp : ∀ u, u ∉ s → p.1 u = 0) {A : ℝ} (hA : 0 < A) :
    2 * realWeilForm p g ≤ A * (∫ u, p.1 u ^ 2) + sourceKernelEnergy s g / A := by
  have hcs := realWeilForm_sq_le_mass_mul_sourceKernelEnergy hs p g hp
  have he : (A * (∫ u, p.1 u ^ 2)) * (sourceKernelEnergy s g / A) =
      (∫ u, p.1 u ^ 2) * sourceKernelEnergy s g := by field_simp
  apply two_mul_le_add_of_sq_le_mul
    (mul_nonneg hA.le (integral_nonneg fun _ => sq_nonneg _))
    (div_nonneg (sourceKernelEnergy_nonneg s g) hA.le)
  rwa [he]

private theorem section_weighted_floor {G : ℕ → ℝ → ℝ} {N : ℕ} {w a : ℝ}
    (hg : ∀ n, ContDiff ℝ 2 (G n)) (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0)
    (hN : 1 ≤ N) (hw0 : 0 < w) (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hw : w ≤ (a * fullSectionRatio) * atomSpacing N) :
    (∑ n ∈ Finset.Icc 1 N, sectionDualWeight N n a * sectionMass (G n)) ≤
      weilPair (arithmeticSection N G) (arithmeticSection N G) := by
  have haF : a * fullSectionRatio ≤ fullSectionRatio := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right ha1 fullSectionRatio_pos.le
  have hwfull := hw.trans (mul_le_mul_of_nonneg_right haF (atomSpacing_pos hN).le)
  have hwhalf := hwfull.trans (mul_le_mul_of_nonneg_right
    fullSectionRatio_le_half_spacing (atomSpacing_pos hN).le)
  have hwsep : w < atomSpacing N := by
    nlinarith only [hwhalf, spacingRatio_lt_half, atomSpacing_pos hN]
  have hf := weilPair_arithmeticSection_ge_width_reserve hg hs hN hw0 ha0 ha1 hw
  rw [integral_arithmeticSection_sq (fun n => (hg n).continuous)
    (fun n => profile_hasCompactSupport (hs n)) hs hwsep] at hf
  have he : (∑ n ∈ Finset.Icc 1 N, sectionDualWeight N n a * sectionMass (G n)) =
      (∑ n ∈ Finset.Icc 1 N, sectionMass (G n)) + ((1 - a) / 8) * sectionReserve N G := by
    simp only [sectionDualWeight, sectionReserve, add_mul, one_mul, mul_assoc,
      Finset.sum_add_distrib, Finset.mul_sum]
  rwa [he]

private theorem section_mixed_young {N : ℕ} {w a : ℝ} (ha : a ≤ 1)
    (p : arithmeticSectionTests N w) (g : realTests)
    {G : ℕ → ℝ → ℝ} (hg : ∀ n, ContDiff ℝ 2 (G n))
    (hs : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0)
    (he : p.1.1 = arithmeticSection N G) :
    2 * realWeilForm p.1 g ≤
      (∑ n ∈ Finset.Icc 1 N, sectionDualWeight N n a * sectionMass (G n)) +
        weightedSectionKernelEnergy N w a g := by
  let f : ℕ → realTests := fun n =>
    ⟨fun u => G n (u - Real.log n),
      (hg n).comp (contDiff_id.sub contDiff_const),
      (profile_hasCompactSupport (hs n)).comp_homeomorph (Homeomorph.subRight (Real.log n))⟩
  have hsum : p.1 = ∑ n ∈ Finset.Icc 1 N, f n := by
    apply Subtype.ext
    funext u
    rw [he]
    simp only [Submodule.coe_sum, Finset.sum_apply, f, arithmeticSection]
  have hlocal : ∀ n : ℕ, 2 * realWeilForm (f n) g ≤
      sectionDualWeight N n a * sectionMass (G n) +
        sourceKernelEnergy (Set.Icc (Real.log n) (Real.log n + w)) g /
          sectionDualWeight N n a := by
    intro n
    have hs' : ∀ u, u ∉ Set.Icc (Real.log n) (Real.log n + w) → (f n).1 u = 0 := by
      intro u hu
      apply hs n
      intro hm
      exact hu ⟨by linarith only [hm.1], by linarith only [hm.2]⟩
    have h := realWeilForm_young_sourceKernel isCompact_Icc (f n) g hs'
      (sectionDualWeight_pos N n ha)
    have hm : (∫ u, (f n).1 u ^ 2) = sectionMass (G n) :=
      integral_sub_right_eq_self (fun u => G n u ^ 2) (Real.log n)
    rwa [hm] at h
  rw [hsum]
  simp only [map_sum, LinearMap.sum_apply, Finset.mul_sum]
  change (∑ n ∈ Finset.Icc 1 N, 2 * realWeilForm (f n) g) ≤ _
  simpa only [Finset.sum_add_distrib, weightedSectionKernelEnergy] using
    Finset.sum_le_sum (fun n (_hn : n ∈ Finset.Icc 1 N) => hlocal n)

/-- The actual unused reserve reduces every finite projection's source cost. -/
theorem arithmeticSectionProjection_energy_le_weightedKernelEnergy
    {ι : Type*} [Fintype ι] {N : ℕ} (hN : 1 ≤ N) {w a : ℝ} (hw0 : 0 < w)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hw : w ≤ (a * fullSectionRatio) * atomSpacing N)
    (f : ι → arithmeticSectionTests N w) (g : realTests) :
    ∀ hfull : w ≤ fullSectionRatio * atomSpacing N,
      realWeilForm (arithmeticSectionProjection hN hw0 hfull f g)
        (arithmeticSectionProjection hN hw0 hfull f g) ≤ weightedSectionKernelEnergy N w a g := by
  intro hfull
  let p := arithmeticSectionProjection hN hw0 hfull f g
  have hp : p ∈ arithmeticSectionTests N w := arithmeticSectionProjection_mem hN hw0 hfull f g
  obtain ⟨G, hg, hs, he⟩ := hp
  have hfloor := section_weighted_floor hg hs hN hw0 ha0 ha1 hw
  have hy := section_mixed_young ha1 ⟨p, ⟨G, hg, hs, he⟩⟩ g hg hs he
  have hpair : realWeilForm p g = realWeilForm p p := by
    obtain ⟨c, hc⟩ := (arithmeticSectionProjection_spec hN hw0 hfull f g).1
    have horth := arithmeticSectionProjection_orthogonal hN hw0 hfull f c g
    rw [← hc, map_sub] at horth
    exact sub_eq_zero.mp horth
  have heW : weilPair (arithmeticSection N G) (arithmeticSection N G) = realWeilForm p p := by
    change _ = weilPair p.1 p.1
    rw [he]
  rw [heW] at hfloor
  change 2 * realWeilForm p g ≤ _ at hy
  rw [hpair] at hy
  change realWeilForm p p ≤ _
  linarith only [hy, hfloor]

/-- The weighted exact-cell source cost survives completion of all old profiles. -/
theorem sectionCompletionEnergy_le_weightedKernelEnergy
    {N : ℕ} (hN : 1 ≤ N) {w a : ℝ} (hw0 : 0 < w)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hw : w ≤ (a * fullSectionRatio) * atomSpacing N)
    (g : realTests) (hfull : w ≤ fullSectionRatio * atomSpacing N) :
    sectionCompletionEnergy hN hw0 hfull g ≤ weightedSectionKernelEnergy N w a g := by
  apply ciSup_le
  intro S
  exact arithmeticSectionProjection_energy_le_weightedKernelEnergy hN hw0 ha0 ha1 hw
    (fun p : S => p.1) g hfull

/-- The completed signed residual retains the improved arithmetic dual reserve. -/
theorem completedSectionResidualForm_ge_weightedKernelEnergy
    {N : ℕ} (hN : 1 ≤ N) {w a : ℝ} (hw0 : 0 < w)
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hw : w ≤ (a * fullSectionRatio) * atomSpacing N)
    (g : realTests) (hfull : w ≤ fullSectionRatio * atomSpacing N) :
    realWeilForm g g - weightedSectionKernelEnergy N w a g ≤
      completedSectionResidualForm hN hw0 hfull g g := by
  change realWeilForm g g - _ ≤ realWeilForm g g - sectionCompletionPair hN hw0 hfull g g
  rw [sectionCompletionPair_self]
  exact sub_le_sub_left
    (sectionCompletionEnergy_le_weightedKernelEnergy hN hw0 ha0 ha1 hw g hfull) _

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.arithmeticSectionProjection_energy_le_weightedKernelEnergy
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.sectionCompletionEnergy_le_weightedKernelEnergy
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.completedSectionResidualForm_ge_weightedKernelEnergy
