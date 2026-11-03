import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.OneCriticalMultiplePaysEveryWindow
import GaloisForLFunctions.WindowTowerOfSpecZ.TheAliasingNormRetainsTheJointPole

/-!
# Joint pole payment extends the critical ratio

The correlated pole floor gives a strictly larger aperture-independent
interval of critical ratios than the separate-moment floor. Every finite
independent window family inherits strict positivity throughout its open
interval. The finite-horizon threshold may depend on the chosen family.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Matrix
open scoped ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri HTGeometry
  RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  WindowTowerOfSpecZ

variable {φ : ℝ → ℝ} {A : ℝ} {ι : Type*} [Fintype ι]

local notation "Λw" => (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))

/-- The correlated pole floor polarizes over every finite complex family. -/
theorem hermQuad_weilWindowGram_ge_jointAliasGram {β : ℝ} (hβ : 0 < β)
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (x : ι → ℂ) :
    -((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) * jointExponentialWeilFloor (β + 1) *
        hermQuad (aliasGram β h) x ≤ hermQuad (weilWindowGram φ h) x := by
  have hH : ∀ i, ContDiff ℝ 2 (halfWeight (h i)) := fun i => contDiff_halfWeight (hh i)
  have hHc : ∀ i, HasCompactSupport (halfWeight (h i)) := fun i =>
    hasCompactSupport_halfWeight (hasCompactSupport_of_window (hsupp i))
  have hHv : ∀ i y, y ∉ Set.Icc (-A) 0 → halfWeight (h i) y = 0 := fun i =>
    halfWeight_eq_zero_of_window (hsupp i)
  have htest : ∀ y : ι → ℝ, CohomologyOfWindowsOfSpecZ.IsWindowTest A
      (fun u => ∑ i, y i * halfWeight (h i) u) := fun y =>
    ⟨ContDiff.sum fun i _ => contDiff_const.mul (hH i), fun u hu => by simp [hHv _ u hu]⟩
  have hfloor := fun y : ι → ℝ => weilQuad_ge_neg_jointExponentialMass (htest y)
    (by linarith only [hβ] : 1 < β + 1)
  have hreal : ∀ i j, ((weilGram Λw fun i => cx (halfWeight (h i))) i j).im = 0 := by
    intro i j
    simp only [weilGram]
    rw [EffectiveArithmeticHodgeTheory.weilPair_real_eq (hH i) (hHc i) (hH j) (hHc j),
      Complex.ofReal_im]
  have hq := hermQuad_weightGram_eq (A := A) (w := fun y => Real.exp (-((β + 1) * y)))
    (by fun_prop) (H := fun i => halfWeight (h i)) (fun i => (hH i).continuous) hHv x
  have hsplit : hermQuad (aliasGram β h) x =
      exponentialMass (β + 1) (fun u => ∑ i, (x i).re * halfWeight (h i) u) +
      exponentialMass (β + 1) (fun u => ∑ i, (x i).im * halfWeight (h i) u) := by
    unfold aliasGram
    rw [hq]
    simp_rw [congrFun (integral_normSq_eq_re_add_im (H := fun i => halfWeight (h i)) x), mul_add]
    exact integral_add (integrable_exponentialMass (htest _) (β + 1))
      (integrable_exponentialMass (htest _) (β + 1))
  rw [hsplit]
  unfold weilWindowGram
  rw [HTGeometry.hermQuad_smul, hermQuad_eq_re_add_im hreal,
    hermQuad_weilGram_ofReal hH hHv (fun i => (x i).re),
    hermQuad_weilGram_ofReal hH hHv (fun i => (x i).im)]
  have hκ : 0 ≤ (∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 :=
    div_nonneg (sq_nonneg _) (integral_nonneg fun u => sq_nonneg (φ u))
  have h₁ := mul_le_mul_of_nonneg_left (hfloor fun i => (x i).re) hκ
  have h₂ := mul_le_mul_of_nonneg_left (hfloor fun i => (x i).im) hκ
  linarith only [h₁, h₂]

/-- The improved floor pays the whole pencil below its explicit threshold. -/
theorem pencilGram_posDef_below_jointPoleMultiple {β J R : ℝ} (hβ : 0 < β)
    (hR : 0 < R)
    (hsmall : (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * jointExponentialWeilFloor (β + 1) * R < β * J)
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (hlin : LinearIndependent ℝ h) :
    ∀ x : ι → ℂ, x ≠ 0 → 0 < hermQuad (pencilGram φ β J R h) x := by
  intro x hx
  rw [pencilGram_eq hh hsupp, HTGeometry.hermQuad_add, HTGeometry.hermQuad_smul]
  have hW := hermQuad_weilWindowGram_ge_jointAliasGram (φ := φ) hβ hh hsupp x
  have hB : 0 < hermQuad (aliasGram β h) x := by
    have h₁ := (Matrix.posDef_iff_dotProduct_mulVec.mp (aliasGram_posDef β hh hsupp hlin)).2 hx
    simpa only [hermQuad] using (Complex.lt_def.mp h₁).1
  have hgap : (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * jointExponentialWeilFloor (β + 1) <
      β * J / R := (lt_div_iff₀ hR).mpr hsmall
  have hpos := mul_pos (sub_pos.mpr hgap) hB
  nlinarith only [hW, hpos]

/-- The natural critical-ratio threshold from separate pole moments. -/
def separatePoleCriticalRatio : ℝ :=
  7 * tiltedJordanOne / ((∫ u, tiltedUnitSpline u) ^ 2 /
    (∫ u, tiltedUnitSpline u ^ 2) * exponentialWeilFloor 8)

/-- The larger critical-ratio threshold from the joint pole. -/
def jointPoleCriticalRatio : ℝ :=
  7 * tiltedJordanOne / ((∫ u, tiltedUnitSpline u) ^ 2 /
    (∫ u, tiltedUnitSpline u ^ 2) * jointExponentialWeilFloor 8)

private theorem tilted_mass_ratio_pos :
    0 < (∫ u, tiltedUnitSpline u) ^ 2 / ∫ u, tiltedUnitSpline u ^ 2 :=
  div_pos (sq_pos_of_ne_zero integral_tiltedUnitSpline_ne_zero) integral_tiltedUnitSpline_sq_pos

theorem separatePoleCriticalRatio_pos : 0 < separatePoleCriticalRatio :=
  div_pos (mul_pos (by norm_num) tiltedJordanOne_pos)
    (mul_pos tilted_mass_ratio_pos (exponentialWeilFloor_pos (by norm_num)))

theorem jointPoleCriticalRatio_pos : 0 < jointPoleCriticalRatio :=
  div_pos (mul_pos (by norm_num) tiltedJordanOne_pos)
    (mul_pos tilted_mass_ratio_pos (jointExponentialWeilFloor_pos (by norm_num)))

/-- Keeping the joint pole strictly enlarges the natural certified ratio interval. -/
theorem separatePoleCriticalRatio_lt_joint : separatePoleCriticalRatio < jointPoleCriticalRatio := by
  have hκ := tilted_mass_ratio_pos
  have hC := jointExponentialWeilFloor_pos (p := 8) (by norm_num)
  have hD := exponentialWeilFloor_pos (p := 8) (by norm_num)
  have hlt := jointExponentialWeilFloor_lt (p := 8) (by norm_num)
  unfold separatePoleCriticalRatio jointPoleCriticalRatio
  rw [div_lt_div_iff₀ (mul_pos hκ hD) (mul_pos hκ hC)]
  exact mul_lt_mul_of_pos_left (mul_lt_mul_of_pos_left hlt hκ)
    (mul_pos (by norm_num) tiltedJordanOne_pos)

/-- The improved scalar pencil has an explicit margin, also at its closed endpoint. -/
theorem tilted_secondOrderLimit_ge_jointPole_margin {h : ℝ → ℝ}
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) (R : ℝ) :
    (7 * tiltedJordanOne / R - (∫ u, tiltedUnitSpline u) ^ 2 /
        (∫ u, tiltedUnitSpline u ^ 2) * jointExponentialWeilFloor 8) *
        exponentialMass 8 (halfWeight h) ≤ secondOrderLimit tiltedUnitSpline 7 tiltedJordanOne R h := by
  have htest : CohomologyOfWindowsOfSpecZ.IsWindowTest A (halfWeight h) :=
    ⟨contDiff_halfWeight hh, halfWeight_eq_zero_of_window hsupp⟩
  have hf := mul_le_mul_of_nonneg_left
    (weilQuad_ge_neg_jointExponentialMass htest (p := 8) (by norm_num)) tilted_mass_ratio_pos.le
  dsimp only [secondOrderLimit, exponentialMass]
  norm_num only [show (7 : ℝ) + 1 = 8 by norm_num]
  dsimp only [exponentialMass] at hf
  linarith only [hf]

/-- Compensated nonnegativity holds on every aperture through the improved endpoint. -/
theorem tilted_secondOrderLimit_nonneg_below_jointPoleCriticalRatio {R : ℝ} (hR : 0 < R)
    (hRmax : R ≤ jointPoleCriticalRatio) {h : ℝ → ℝ}
    (hh : ContDiff ℝ 2 h) (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    0 ≤ secondOrderLimit tiltedUnitSpline 7 tiltedJordanOne R h := by
  have hden := mul_pos tilted_mass_ratio_pos
    (jointExponentialWeilFloor_pos (p := 8) (by norm_num))
  have hsmall := (le_div_iff₀ hden).mp hRmax
  have hgap : 0 ≤ 7 * tiltedJordanOne / R - (∫ u, tiltedUnitSpline u) ^ 2 /
      (∫ u, tiltedUnitSpline u ^ 2) * jointExponentialWeilFloor 8 := by
    apply sub_nonneg.mpr
    apply (le_div_iff₀ hR).mpr
    simpa only [mul_comm R] using hsmall
  exact (mul_nonneg hgap (exponentialMass_nonneg 8 (halfWeight h))).trans
    (tilted_secondOrderLimit_ge_jointPole_margin hh hsupp R)

/-- At every ratio below the improved threshold, every independent window pencil is strict. -/
theorem tilted_pencilGram_posDef_below_jointPoleCriticalRatio {R : ℝ} (hR : 0 < R)
    (hRmax : R < jointPoleCriticalRatio) {h : ι → ℝ → ℝ}
    (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (hlin : LinearIndependent ℝ h) :
    ∀ x : ι → ℂ, x ≠ 0 → 0 < hermQuad (pencilGram tiltedUnitSpline 7 tiltedJordanOne R h) x := by
  have hsmall := (lt_div_iff₀ (mul_pos tilted_mass_ratio_pos
    (jointExponentialWeilFloor_pos (p := 8) (by norm_num)))).mp hRmax
  apply pencilGram_posDef_below_jointPoleMultiple (by norm_num) hR _ hh hsupp hlin
  simpa only [show (7 : ℝ) + 1 = 8 by norm_num, mul_comm R] using hsmall

/-- Every fixed family inherits the larger interval along any critical schedule. -/
theorem tilted_horizonGram_posDef_below_jointPoleCriticalRatio [DecidableEq ι]
    {R : ℝ} (hR : 0 < R) (hRmax : R < jointPoleCriticalRatio)
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i)) (hA : 0 ≤ A)
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (hlin : LinearIndependent ℝ h)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R)) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ι → ℂ, x ≠ 0 →
      0 < hermQuad (horizonGram tiltedUnitSpline h (c N) N) x := by
  have hpos := tilted_pencilGram_posDef_below_jointPoleCriticalRatio hR hRmax hh hsupp hlin
  have hcrit' : Tendsto (fun N : ℕ => c N ^ ((7 : ℝ) + 1) / Real.log N)
      atTop (𝓝 R) := by
    simpa only [show (7 : ℝ) + 1 = (8 : ℕ) by norm_num, Real.rpow_natCast] using hcrit
  have hdecay : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hlim := tendsto_horizonGram contDiff_tiltedUnitSpline tiltedUnitSpline_support
    integral_tiltedUnitSpline_sq_pos (p := 8) (by norm_num) hdecay tiltedUnitSpline_decay
    (β := 7) (by norm_num) tendsto_rpow_seven_mul_completedShellEnergy_tilted
    hh hA hsupp hc1 hR hcrit'
  have hHerm := pencilGram_isHermitian contDiff_tiltedUnitSpline tiltedUnitSpline_support
    integral_tiltedUnitSpline_sq_pos (p := 8) (by norm_num) hdecay tiltedUnitSpline_decay
    (β := 7) (by norm_num) tendsto_rpow_seven_mul_completedShellEnergy_tilted
    hh hA hsupp hc1 hR hcrit'
  have hev := eventually_hermQuad_pos_of_tendsto hHerm hpos hlim
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1 x hx
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc1 N)
  have hw : 0 < c N / N := div_pos hc0 hN0
  have hs : 0 < (c N)⁻¹ / ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2 := by
    rw [integral_atomDilate_sq tiltedUnitSpline hw]
    exact div_pos (inv_pos.mpr hc0) (mul_pos hw integral_tiltedUnitSpline_sq_pos)
  have h := hN x hx
  rw [HTGeometry.hermQuad_smul] at h
  exact pos_of_mul_pos_right h hs.le

/-- An explicit ratio beyond the old floor works simultaneously for all window pencils. -/
theorem exists_larger_critical_ratio_for_all_window_pencils :
    ∃ R : ℝ, separatePoleCriticalRatio < R ∧ R < jointPoleCriticalRatio ∧
      ∀ (A : ℝ) (n : ℕ) (h : Fin n → ℝ → ℝ),
        (∀ i, ContDiff ℝ 2 (h i)) → (∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) →
        LinearIndependent ℝ h → ∀ x : Fin n → ℂ, x ≠ 0 →
          0 < hermQuad (pencilGram tiltedUnitSpline 7 tiltedJordanOne R h) x := by
  refine ⟨(separatePoleCriticalRatio + jointPoleCriticalRatio) / 2, ?_, ?_, ?_⟩
  · linarith only [separatePoleCriticalRatio_lt_joint]
  · linarith only [separatePoleCriticalRatio_lt_joint]
  · intro A n h hh hsupp hlin
    exact tilted_pencilGram_posDef_below_jointPoleCriticalRatio
      (by linarith only [separatePoleCriticalRatio_pos, jointPoleCriticalRatio_pos])
      (by linarith only [separatePoleCriticalRatio_lt_joint]) hh hsupp hlin

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.separatePoleCriticalRatio_lt_joint
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tilted_secondOrderLimit_nonneg_below_jointPoleCriticalRatio
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.exists_larger_critical_ratio_for_all_window_pencils
#print axioms GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.tilted_horizonGram_posDef_below_jointPoleCriticalRatio
