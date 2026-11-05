import GaloisForLFunctions.ArithmeticIncidencePositivity.AWeilFloorSurvivesAnotherDilation
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalThresholdOfAWindow

/-!
# Positive critical pencils beyond the enlarged base window

A second dilation of the actual one-prime Weil form yields a positive window
strictly beyond `2 * enlargedWeilFloorAperture`. Its critical threshold is infinite,
so every positive critical ratio has a positive pencil and each nonzero horizon
test is eventually positive along its critical curve.
-/

noncomputable section

open MeasureTheory Set Filter Topology Zeta23 Matrix
open scoped ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open ArithmeticIncidencePositivity ArithmeticCriticalityTheory ArithmeticCastelnuovoSeveri
  CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis WindowTowerOfSpecZ
  HTGeometry
  _root_.RHTower _root_.RHTower.WeilMarkovPole

/-- Centering transports the second enlarged floor to every shorter half-window. -/
theorem weilQuad_ge_of_le_two_mul_successorWeilFloorAperture {A : ℝ}
    (hA : A ≤ 2 * successorWeilFloorAperture) {H : ℝ → ℝ} (hH : IsWindowTest A H) :
    (1 / 20000 : ℝ) * ∫ u, H u ^ 2 ≤ weilQuad H := by
  set f : ℝ → ℝ := fun u => H (u - A / 2)
  have hfd : ContDiff ℝ 2 f := hH.contDiff.comp (contDiff_id.sub contDiff_const)
  have hfc : HasCompactSupport f :=
    HasCompactSupport.intro (isCompact_Icc (a := -(A / 2)) (b := A / 2)) fun u hu =>
      hH.vanish (u - A / 2) fun hm => hu ⟨by linarith only [hm.1], by linarith only [hm.2]⟩
  have hfs : ∀ u, successorWeilFloorAperture < |u| → f u = 0 := fun u hu => by
    refine hH.vanish (u - A / 2) fun hm => ?_
    rcases lt_abs.mp hu with hpos | hneg
    · linarith only [hm.2, hA, hpos]
    · linarith only [hm.1, hA, hneg]
  have hfloor := fullZeroForm_ge_of_support_le_successorWeilFloorAperture hfd hfc hfs
  have hpair : weilPair f f = fullZeroForm f :=
    LatticeSectionTheory.WindowJumpCounts.weilPair_eq_fullZeroForm ⟨hfd, hfc⟩
  have hquad : weilPair f f = weilQuad H := weilQuad_comp_sub H (A / 2)
  have hmass : (∫ u, f u ^ 2) = ∫ u, H u ^ 2 :=
    integral_sub_right_eq_self (μ := volume) (fun u => H u ^ 2) (A / 2)
  linarith only [hfloor, hpair, hquad, hmass]

/-- Every window through the second enlargement has infinite critical threshold. -/
theorem windowThreshold_eq_top_of_le_successor {A : ℝ}
    (hA : A ≤ 2 * successorWeilFloorAperture) : windowThreshold A = ⊤ := by
  refine windowThreshold_eq_top_iff.mpr fun H hH => ?_
  have hfloor := weilQuad_ge_of_le_two_mul_successorWeilFloorAperture hA hH
  have hmass : 0 ≤ ∫ u, H u ^ 2 := integral_nonneg fun u => sq_nonneg _
  linarith only [hfloor, hmass]

/-- On the larger window the critical pencil is positive at every positive ratio. -/
theorem windowPencil_pos_of_le_successor {A R : ℝ}
    (hA : A ≤ 2 * successorWeilFloorAperture) (hR : 0 < R)
    {H : ℝ → ℝ} (hH : IsWindowTest A H) (hne : H ≠ 0) :
    0 < windowPencil R H := by
  apply pencil_pos_of_lt_windowThreshold hR _ hH hne
  rw [windowThreshold_eq_top_of_le_successor hA]
  exact EReal.coe_lt_top _

/-- The critical-curve limit gives eventual positivity for every nonzero horizon test. -/
theorem eventually_pos_of_le_successor {A R : ℝ} (hA0 : 0 ≤ A)
    (hA : A ≤ 2 * successorWeilFloorAperture) (hR : 0 < R)
    {h : ℝ → ℝ} (hh : ContDiff ℝ 2 h)
    (hsupp : ∀ y, y ∉ Icc (-A) 0 → h y = 0) (hne : halfWeight h ≠ 0)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∀ᶠ N : ℕ in atTop, 0 < (c N)⁻¹ * (weilQuad (ArithmeticElectrostatics.atomicTest N
        (horizonWeights h N) (atomDilate tiltedUnitSpline (c N / N))) /
          ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) := by
  apply eventually_pos_of_lt_windowThreshold hA0 hR _ hh hsupp hne hc1 hcrit
  rw [windowThreshold_eq_top_of_le_successor hA]
  exact EReal.coe_lt_top _

/-- Real and imaginary synthesis transfer the larger-window sign to every finite Gram matrix. -/
theorem hermQuad_weilWindowGram_nonneg_of_le_successor {ι : Type*} [Fintype ι]
    {A : ℝ} (hA : A ≤ 2 * successorWeilFloorAperture) (φ : ℝ → ℝ)
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Icc (-A) 0 → h i y = 0) (x : ι → ℂ) :
    0 ≤ hermQuad (weilWindowGram φ h) x := by
  have hH : ∀ i, ContDiff ℝ 2 (halfWeight (h i)) := fun i => contDiff_halfWeight (hh i)
  have hHc : ∀ i, HasCompactSupport (halfWeight (h i)) := fun i =>
    hasCompactSupport_halfWeight (hasCompactSupport_of_window (hsupp i))
  have hHv : ∀ i y, y ∉ Icc (-A) 0 → halfWeight (h i) y = 0 := fun i =>
    halfWeight_eq_zero_of_window (hsupp i)
  have hpos := windowThreshold_eq_top_iff.mp (windowThreshold_eq_top_of_le_successor hA)
  have hQ : ∀ y : ι → ℝ, 0 ≤ weilQuad (fun u => ∑ i, y i * halfWeight (h i) u) := fun y =>
    hpos _ ⟨ContDiff.sum fun i _ => contDiff_const.mul (hH i), fun u hu => by
      simp only [hHv _ u hu, mul_zero, Finset.sum_const_zero]⟩
  have hreal : ∀ i j, ((weilGram (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      fun i => cx (halfWeight (h i))) i j).im = 0 := by
    intro i j
    simp only [weilGram]
    rw [EffectiveArithmeticHodgeTheory.weilPair_real_eq (hH i) (hHc i) (hH j) (hHc j),
      Complex.ofReal_im]
  unfold weilWindowGram
  rw [HTGeometry.hermQuad_smul, hermQuad_eq_re_add_im hreal,
    hermQuad_weilGram_ofReal hH hHv (fun i => (x i).re),
    hermQuad_weilGram_ofReal hH hHv (fun i => (x i).im)]
  have hκ : 0 ≤ (∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 :=
    div_nonneg (sq_nonneg _) (integral_nonneg fun u => sq_nonneg _)
  exact mul_nonneg hκ (add_nonneg (hQ _) (hQ _))

/-- The whole finite-dimensional critical pencil is positive at every ratio. -/
theorem pencilGram_pos_of_le_successor {ι : Type*} [Fintype ι]
    {A : ℝ} (hA : A ≤ 2 * successorWeilFloorAperture) (φ : ℝ → ℝ)
    {β J R : ℝ} (hβJ : 0 < β * J) (hR : 0 < R)
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Icc (-A) 0 → h i y = 0) (hlin : LinearIndependent ℝ h)
    (x : ι → ℂ) (hx : x ≠ 0) :
    0 < hermQuad (pencilGram φ β J R h) x := by
  rw [pencilGram_eq hh hsupp, HTGeometry.hermQuad_add, HTGeometry.hermQuad_smul]
  have hW := hermQuad_weilWindowGram_nonneg_of_le_successor hA φ hh hsupp x
  have hB : 0 < hermQuad (aliasGram β h) x := by
    have h1 := (Matrix.posDef_iff_dotProduct_mulVec.mp (aliasGram_posDef β hh hsupp hlin)).2 hx
    simpa only [hermQuad, show (0 : ℂ).re = 0 from rfl] using (Complex.lt_def.mp h1).1
  exact add_pos_of_nonneg_of_pos hW (mul_pos (div_pos hβJ hR) hB)

/-- Each fixed independent window family inherits positivity along every positive critical ratio. -/
theorem successor_windows_inherit_exact {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : ℝ} (hA0 : 0 ≤ A) (hA : A ≤ 2 * successorWeilFloorAperture)
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Icc (-A) 0 → h i y = 0) (hlin : LinearIndependent ℝ h)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ι → ℂ, x ≠ 0 →
      0 < hermQuad (horizonGram tiltedUnitSpline h (c N) N) x := by
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hβJ : 0 < 7 * tiltedJordanOne := mul_pos (by norm_num) tiltedJordanOne_pos
  have hpos := pencilGram_pos_of_le_successor hA tiltedUnitSpline hβJ hR hh hsupp hlin
  have hcrit' : Tendsto (fun N : ℕ => c N ^ ((7 : ℝ) + 1) / Real.log N) atTop (𝓝 R) := by
    simpa only [show (7 : ℝ) + 1 = (8 : ℕ) by norm_num, Real.rpow_natCast] using hcrit
  have hherm := pencilGram_isHermitian contDiff_tiltedUnitSpline tiltedUnitSpline_support
    integral_tiltedUnitSpline_sq_pos (p := 8) (by norm_num) hC tiltedUnitSpline_decay
    (β := 7) (by norm_num) tendsto_rpow_seven_mul_completedShellEnergy_tilted
    hh hA0 hsupp hc1 hR hcrit'
  have hlim := tendsto_horizonGram contDiff_tiltedUnitSpline tiltedUnitSpline_support
    integral_tiltedUnitSpline_sq_pos (p := 8) (by norm_num) hC tiltedUnitSpline_decay
    (β := 7) (by norm_num) tendsto_rpow_seven_mul_completedShellEnergy_tilted
    hh hA0 hsupp hc1 hR hcrit'
  have hev := eventually_hermQuad_pos_of_tendsto hherm hpos hlim
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1 x hx
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc1 N)
  have hw : 0 < c N / N := div_pos hc0 hN0
  have hscale : 0 < (c N)⁻¹ / ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2 := by
    rw [integral_atomDilate_sq tiltedUnitSpline hw]
    exact div_pos (inv_pos.mpr hc0) (mul_pos hw integral_tiltedUnitSpline_sq_pos)
  have hp := hN x hx
  rw [HTGeometry.hermQuad_smul] at hp
  exact pos_of_mul_pos_right hp hscale.le

/-- There is an explicit larger window with infinite threshold and positive pencils at all ratios. -/
theorem exists_larger_window_with_all_critical_pencils_positive :
    ∃ A : ℝ, 2 * enlargedWeilFloorAperture < A ∧ A < 1 ∧
      windowThreshold A = ⊤ ∧
      ∀ R : ℝ, 0 < R → ∀ H : ℝ → ℝ, IsWindowTest A H → H ≠ 0 →
        0 < windowPencil R H := by
  refine ⟨2 * successorWeilFloorAperture, ?_, ?_,
    windowThreshold_eq_top_of_le_successor le_rfl, ?_⟩
  · linarith only [successorWeilFloorAperture_bounds.1]
  · linarith only [successorWeilFloorAperture_bounds.2]
  · exact fun _ hR _ hH hne => windowPencil_pos_of_le_successor le_rfl hR hH hne

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.exists_larger_window_with_all_critical_pencils_positive
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.eventually_pos_of_le_successor
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.pencilGram_pos_of_le_successor
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.successor_windows_inherit_exact
