import GaloisForLFunctions.ArithmeticIndexDescent.TheFullWidthStillRetainsArithmeticReserve

/-!
# Moving arithmetic bands decouple from fixed tests

Translate the arithmetic band `N/2 ≤ n ≤ N` by `-log N`. Its cells remain in
one fixed window, while the retained source reserve gives a mass floor growing
like `log N`. The exact combined source kernel then bounds its mixed pairing
with any fixed test. The energy unit balls become uniformly invisible to every
fixed probe, even though the number of permitted cells grows.
-/

noncomputable section

open Filter MeasureTheory Set RHTower
open scoped Topology

namespace GaloisForLFunctions.ArithmeticIndexDescent

open ArithmeticCastelnuovoSeveri ArithmeticElectrostatics SpacingScaleHarmonicAnalysis

/-- The actual section translated into a fixed multiplicative band window. -/
def movingArithmeticBandTest (N : ℕ) (G : ℕ → ℝ → ℝ) {w : ℝ}
    (hg : ∀ n, ContDiff ℝ 2 (G n)) (hs : ∀ n u, u ∉ Icc 0 w → G n u = 0) :
    realTests :=
  ⟨scaleShift (-Real.log N) (arithmeticSection N G),
    scaleShift_mem _ ⟨contDiff_arithmeticSection hg N, hasCompactSupport_arithmeticSection hs N⟩⟩

/-- The weighted reserve available throughout the upper half of an arithmetic block. -/
def movingBandFloor (N : ℕ) : ℝ :=
  1 + fullWidthSectionReserve * (1 + (1 + Real.log N) / 2)

theorem movingBandFloor_pos (N : ℕ) : 0 < movingBandFloor N := by
  have hlog := Real.log_natCast_nonneg N
  have hρ := fullWidthSectionReserve_pos
  unfold movingBandFloor
  positivity

private theorem fullWidth_lt_one_and_spacing {N : ℕ} (hN : 1 ≤ N)
    {w : ℝ} (hw : w ≤ fullSectionRatio * atomSpacing N) :
    w < 1 ∧ w < atomSpacing N := by
  have hr : fullSectionRatio < 1 := by
    linarith only [fullSectionRatio_le_half_spacing, spacingRatio_lt_half]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hwdiv : w ≤ fullSectionRatio / N := by
    have h := hw.trans (mul_le_mul_of_nonneg_left (atomSpacing_le_inv hN)
      fullSectionRatio_pos.le)
    simpa only [div_eq_mul_inv, one_mul] using h
  have hwN := (le_div_iff₀ hN0).mp hwdiv
  refine ⟨?_, ?_⟩
  · nlinarith only [hwN, hN1, hr]
  · exact hw.trans_lt (by simpa only [one_mul] using
      mul_lt_mul_of_pos_right hr (atomSpacing_pos hN))

/-- The logarithmic reserve is a growing source floor on the entire independent-profile band. -/
theorem movingArithmeticBand_mass_floor {N : ℕ} (hN : 1 ≤ N) {w : ℝ}
    (hw0 : 0 < w) (hw : w ≤ fullSectionRatio * atomSpacing N)
    (G : ℕ → ℝ → ℝ) (hg : ∀ n, ContDiff ℝ 2 (G n))
    (hs : ∀ n u, u ∉ Icc 0 w → G n u = 0)
    (hband : ∀ n : ℕ, (n : ℝ) < (N : ℝ) / 2 → G n = 0) :
    movingBandFloor N * sectionMass (movingArithmeticBandTest N G hg hs).1 ≤
      realWeilForm (movingArithmeticBandTest N G hg hs) (movingArithmeticBandTest N G hg hs) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog := Real.log_natCast_nonneg N
  have hmass := integral_arithmeticSection_sq (fun n => (hg n).continuous)
    (fun n => profile_hasCompactSupport (hs n)) hs
    (fullWidth_lt_one_and_spacing hN hw).2
  have hreserve : (1 + (1 + Real.log N) / 2) * sectionMass (arithmeticSection N G) ≤
      sectionReserve N G := by
    change (1 + (1 + Real.log N) / 2) * (∫ u, arithmeticSection N G u ^ 2) ≤ _
    rw [hmass, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    by_cases hn : (n : ℝ) < (N : ℝ) / 2
    · simp only [hband n hn, sectionMass, Pi.zero_apply, zero_pow (by decide : 2 ≠ 0),
        integral_zero, mul_zero, le_refl]
    · have hratio : (1 / 2 : ℝ) ≤ (n : ℝ) / N :=
        (le_div_iff₀ hN0).mpr (by linarith only [le_of_not_gt hn])
      have hprod := mul_le_mul_of_nonneg_right hratio
        (show 0 ≤ 1 + Real.log N by linarith only [hlog])
      apply mul_le_mul_of_nonneg_right ?_ (sectionMass_nonneg (G n))
      unfold sectionReserveWeight
      linarith only [hprod]
  have hW := weilPair_arithmeticSection_ge_fullWidth_reserve hg hs hN hw0 hw
  have hgain := mul_le_mul_of_nonneg_left hreserve fullWidthSectionReserve_pos.le
  have hm : sectionMass (scaleShift (-Real.log N) (arithmeticSection N G)) =
      sectionMass (arithmeticSection N G) :=
    integral_sub_right_eq_self (fun u => arithmeticSection N G u ^ 2) (-Real.log N)
  change movingBandFloor N * sectionMass (scaleShift (-Real.log N) (arithmeticSection N G)) ≤
    weilPair (scaleShift (-Real.log N) (arithmeticSection N G))
      (scaleShift (-Real.log N) (arithmeticSection N G))
  rw [hm, weilPair_scaleShift_same]
  change (1 + fullWidthSectionReserve * (1 + (1 + Real.log N) / 2)) *
    (∫ u, arithmeticSection N G u ^ 2) ≤ _
  change fullWidthSectionReserve * ((1 + (1 + Real.log N) / 2) *
    (∫ u, arithmeticSection N G u ^ 2)) ≤ fullWidthSectionReserve * sectionReserve N G at hgain
  nlinarith only [hW, hgain]

/-- Recentring the upper arithmetic band keeps its full support in one fixed compact window. -/
theorem movingArithmeticBand_eq_zero_off_window {N : ℕ} (hN : 1 ≤ N) {w : ℝ}
    (hw : w ≤ fullSectionRatio * atomSpacing N)
    (G : ℕ → ℝ → ℝ) (hg : ∀ n, ContDiff ℝ 2 (G n))
    (hs : ∀ n u, u ∉ Icc 0 w → G n u = 0)
    (hband : ∀ n : ℕ, (n : ℝ) < (N : ℝ) / 2 → G n = 0)
    (u : ℝ) (hu : u ∉ Icc (-Real.log 2) 1) :
    (movingArithmeticBandTest N G hg hs).1 u = 0 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw1 := (fullWidth_lt_one_and_spacing hN hw).1
  change (∑ n ∈ Finset.Icc 1 N, G n (u - (-Real.log N) - Real.log n)) = 0
  apply Finset.sum_eq_zero
  intro n hn
  by_cases hlow : (n : ℝ) < (N : ℝ) / 2
  · rw [hband n hlow]
    rfl
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hloghi : Real.log n ≤ Real.log N :=
    Real.log_le_log hn0 (by exact_mod_cast (Finset.mem_Icc.mp hn).2)
  have hloglo := Real.log_le_log hN0
    (show (N : ℝ) ≤ 2 * (n : ℝ) by linarith only [le_of_not_gt hlow])
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hn0.ne'] at hloglo
  apply hs n
  intro hm
  apply hu
  exact ⟨by linarith only [hm.1, hloglo], by linarith only [hm.2, hloghi, hw1]⟩

/-- The whole arithmetic source, squared only after its terms combine, pays the band coupling. -/
theorem movingArithmeticBand_source_coupling {N : ℕ} (hN : 1 ≤ N) {w : ℝ}
    (hw0 : 0 < w) (hw : w ≤ fullSectionRatio * atomSpacing N)
    (G : ℕ → ℝ → ℝ) (hg : ∀ n, ContDiff ℝ 2 (G n))
    (hs : ∀ n u, u ∉ Icc 0 w → G n u = 0)
    (hband : ∀ n : ℕ, (n : ℝ) < (N : ℝ) / 2 → G n = 0) (g : realTests) :
    movingBandFloor N * realWeilForm (movingArithmeticBandTest N G hg hs) g ^ 2 ≤
      sourceKernelEnergy (Icc (-Real.log 2) 1) g *
        realWeilForm (movingArithmeticBandTest N G hg hs) (movingArithmeticBandTest N G hg hs) := by
  let p := movingArithmeticBandTest N G hg hs
  let D := sourceKernelEnergy (Icc (-Real.log 2) 1) g
  have hcs := realWeilForm_sq_le_mass_mul_sourceKernelEnergy isCompact_Icc p g
    (movingArithmeticBand_eq_zero_off_window hN hw G hg hs hband)
  have hfloor := movingArithmeticBand_mass_floor hN hw0 hw G hg hs hband
  have hbudget := mul_le_mul_of_nonneg_left hcs (movingBandFloor_pos N).le
  have hpaid := mul_le_mul_of_nonneg_right hfloor
    (sourceKernelEnergy_nonneg (Icc (-Real.log 2) 1) g)
  change movingBandFloor N * realWeilForm p g ^ 2 ≤ D * realWeilForm p p
  change movingBandFloor N * realWeilForm p g ^ 2 ≤
    movingBandFloor N * (sectionMass p.1 * D) at hbudget
  change (movingBandFloor N * sectionMass p.1) * D ≤ realWeilForm p p * D at hpaid
  nlinarith only [hbudget, hpaid]

theorem movingBandFloor_tendsto_atTop : Tendsto movingBandFloor atTop atTop := by
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  apply tendsto_atTop.mpr
  intro b
  have hρ := fullWidthSectionReserve_pos
  filter_upwards [hlog.eventually (eventually_ge_atTop (2 * b / fullWidthSectionReserve))]
    with N hN
  have hmul := mul_le_mul_of_nonneg_left hN hρ.le
  have heq : fullWidthSectionReserve * (2 * b / fullWidthSectionReserve) = 2 * b := by
    field_simp
  rw [heq] at hmul
  unfold movingBandFloor
  nlinarith only [hmul, hρ]

/-- Energy-normalized upper-band sections decouple uniformly from every fixed compact probe. -/
theorem movingArithmeticBand_unit_energy_pairing_tendsto_zero (g : realTests)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ w : ℝ, 0 < w →
      w ≤ fullSectionRatio * atomSpacing N →
      ∀ G : ℕ → ℝ → ℝ, ∀ hg : ∀ n, ContDiff ℝ 2 (G n),
      ∀ hs : ∀ n u, u ∉ Icc 0 w → G n u = 0,
      (∀ n : ℕ, (n : ℝ) < (N : ℝ) / 2 → G n = 0) →
      realWeilForm (movingArithmeticBandTest N G hg hs) (movingArithmeticBandTest N G hg hs) ≤ 1 →
      |realWeilForm (movingArithmeticBandTest N G hg hs) g| < ε := by
  let D := sourceKernelEnergy (Icc (-Real.log 2) 1) g
  have hD : 0 ≤ D := sourceKernelEnergy_nonneg _ g
  filter_upwards [eventually_ge_atTop (1 : ℕ),
    movingBandFloor_tendsto_atTop.eventually (eventually_gt_atTop (D / ε ^ 2))]
    with N hN hhigh
  intro w hw0 hw G hg hs hband hunit
  let p := movingArithmeticBandTest N G hg hs
  have hbudget := movingArithmeticBand_source_coupling hN hw0 hw G hg hs hband g
  have hfinal : movingBandFloor N * realWeilForm p g ^ 2 ≤ D :=
    hbudget.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hunit hD)
  have hstrict : D < movingBandFloor N * ε ^ 2 :=
    (div_lt_iff₀ (sq_pos_of_pos hε)).mp hhigh
  by_contra hbad
  have hsq : ε ^ 2 ≤ realWeilForm p g ^ 2 := by
    simpa only [sq_abs] using
      (sq_le_sq₀ hε.le (abs_nonneg (realWeilForm p g))).mpr (le_of_not_gt hbad)
  have hmul := mul_le_mul_of_nonneg_left hsq (movingBandFloor_pos N).le
  linarith only [hfinal, hstrict, hmul]

end GaloisForLFunctions.ArithmeticIndexDescent

#print axioms GaloisForLFunctions.ArithmeticIndexDescent.movingArithmeticBand_mass_floor
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.movingArithmeticBand_source_coupling
#print axioms GaloisForLFunctions.ArithmeticIndexDescent.movingArithmeticBand_unit_energy_pairing_tendsto_zero
