import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCountPaysTheSecondOrderBelowAUniformMultiple
import GaloisForLFunctions.WindowTowerOfSpecZ.TheAliasingWeightPaysEveryWindow

/-!
# One critical multiple pays every window

The aliasing form retains its full exponential weight. Its weighted Weil
floor is independent of aperture, so a single positive range of critical
multiples works on every window and every independent finite family.
The convergence to the pencil is still asserted separately for each family.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Matrix
open scoped ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri HTGeometry
  RenormalizedArithmeticPotentialTheory.CompletedShell WindowTowerOfSpecZ

variable {φ : ℝ → ℝ} {A : ℝ} {ι : Type*} [Fintype ι]

local notation "Λw" => (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ))

/-- The complete Weil Gram matrix is bounded below by a fixed multiple of
the aliasing Gram matrix, independently of the aperture. -/
theorem hermQuad_weilWindowGram_ge_aliasGram {β : ℝ} (hβ : 0 < β)
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (x : ι → ℂ) :
    -((∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2)) * exponentialWeilFloor (β + 1) *
        hermQuad (aliasGram β h) x ≤ hermQuad (weilWindowGram φ h) x := by
  have hH : ∀ i, ContDiff ℝ 2 (halfWeight (h i)) := fun i => contDiff_halfWeight (hh i)
  have hHc : ∀ i, HasCompactSupport (halfWeight (h i)) := fun i =>
    hasCompactSupport_halfWeight (hasCompactSupport_of_window (hsupp i))
  have hHv : ∀ i y, y ∉ Set.Icc (-A) 0 → halfWeight (h i) y = 0 := fun i =>
    halfWeight_eq_zero_of_window (hsupp i)
  have htest : ∀ y : ι → ℝ, CohomologyOfWindowsOfSpecZ.IsWindowTest A
      (fun u => ∑ i, y i * halfWeight (h i) u) := fun y =>
    ⟨ContDiff.sum fun i _ => contDiff_const.mul (hH i), fun u hu => by simp [hHv _ u hu]⟩
  have hfloor := fun y : ι → ℝ => weilQuad_ge_neg_exponentialMass (htest y)
    (by linarith : 1 < β + 1)
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
  have hκ : 0 ≤ (∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 := by
    have : (0 : ℝ) ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg (φ u)
    positivity
  have h1 := mul_le_mul_of_nonneg_left (hfloor fun i => (x i).re) hκ
  have h2 := mul_le_mul_of_nonneg_left (hfloor fun i => (x i).im) hκ
  linarith only [h1, h2]

/-- A positive range of critical multiples independent of both aperture
and the chosen independent family. -/
theorem pencilGram_posDef_below_apertureIndependentMultiple {β J K : ℝ} (hβ : 0 < β)
    (hK : 0 < K)
    (hsmall : (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * exponentialWeilFloor (β + 1) * K < β * J)
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i))
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (hlin : LinearIndependent ℝ h) :
    ∀ x : ι → ℂ, x ≠ 0 → 0 < hermQuad (pencilGram φ β J K h) x := by
  intro x hx
  rw [pencilGram_eq hh hsupp, HTGeometry.hermQuad_add, HTGeometry.hermQuad_smul]
  have hW := hermQuad_weilWindowGram_ge_aliasGram (φ := φ) hβ hh hsupp x
  have hB : 0 < hermQuad (aliasGram β h) x := by
    have h1 := (Matrix.posDef_iff_dotProduct_mulVec.mp (aliasGram_posDef β hh hsupp hlin)).2 hx
    simpa [hermQuad] using (Complex.lt_def.mp h1).1
  have hgap : (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * exponentialWeilFloor (β + 1) < β * J / K := by
    rwa [lt_div_iff₀ hK]
  have hpos := mul_pos (sub_pos.mpr hgap) hB
  nlinarith only [hW, hpos]

/-- The same explicit critical multiple works for every window length
and every finite number of independent tests. -/
theorem exists_positive_multiple_for_all_windows (φ : ℝ → ℝ) {β J : ℝ}
    (hβ : 0 < β) (hJ : 0 < J) :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ K : ℝ, 0 < K → K ≤ K₀ → ∀ A : ℝ, ∀ n : ℕ,
      ∀ h : Fin n → ℝ → ℝ, (∀ i, ContDiff ℝ 2 (h i)) →
      (∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) → LinearIndependent ℝ h →
      ∀ x : Fin n → ℂ, x ≠ 0 → 0 < hermQuad (pencilGram φ β J K h) x := by
  set C := (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * exponentialWeilFloor (β + 1)
  have hκ : 0 ≤ (∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2 := by
    have : (0 : ℝ) ≤ ∫ u, φ u ^ 2 := integral_nonneg fun u => sq_nonneg (φ u)
    positivity
  have hC : 0 ≤ C := mul_nonneg hκ (exponentialWeilFloor_pos (by linarith)).le
  have hden : 0 < 2 * (C + 1) := by positivity
  refine ⟨β * J / (2 * (C + 1)), div_pos (mul_pos hβ hJ) hden, ?_⟩
  intro K hK hKle A n h hh hsupp hlin
  apply pencilGram_posDef_below_apertureIndependentMultiple hβ hK _ hh hsupp hlin
  change C * K < β * J
  have hbound : K * (2 * (C + 1)) ≤ β * J := (le_div_iff₀ hden).mp hKle
  nlinarith only [hbound, mul_nonneg hC hK.le, hK]

/-- The tilted spline has a single positive interval of critical multiples
on all windows, with no unproved spectral or arithmetic input. -/
theorem tilted_exists_positive_multiple_for_all_windows :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ K : ℝ, 0 < K → K ≤ K₀ → ∀ A : ℝ, ∀ n : ℕ,
      ∀ h : Fin n → ℝ → ℝ, (∀ i, ContDiff ℝ 2 (h i)) →
      (∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) → LinearIndependent ℝ h →
      ∀ x : Fin n → ℂ, x ≠ 0 → 0 < hermQuad (pencilGram tiltedUnitSpline 7 tiltedJordanOne K h) x :=
  exists_positive_multiple_for_all_windows tiltedUnitSpline (by norm_num) tiltedJordanOne_pos

/-- Along the critical curve, the fixed multiple gives eventual positivity
for each independent window family, at every aperture. -/
theorem below_apertureIndependentMultiple_inherit [DecidableEq ι] (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ2 : 0 < ∫ u, φ u ^ 2) {Cφ p : ℝ} (hp : 4 < p)
    (hCφ : 0 ≤ Cφ) (hdecay : ∀ u : ℝ, ‖paperFT (cx φ) u‖ ^ 2 ≤ Cφ * (1 + |u|) ^ (-p))
    {β J : ℝ} (hβ : 0 < β)
    (hbulk : Tendsto (fun s => s ^ β * completedShellEnergy φ s) atTop (𝓝 J))
    {h : ι → ℝ → ℝ} (hh : ∀ i, ContDiff ℝ 2 (h i)) (hA : 0 < A)
    (hsupp : ∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) (hlin : LinearIndependent ℝ h)
    {c : ℕ → ℝ} (hc1 : ∀ N, 1 ≤ c N) {K : ℝ} (hK : 0 < K)
    (hsmall : (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) * exponentialWeilFloor (β + 1) * K < β * J)
    (hcrit : Tendsto (fun N : ℕ => c N ^ (β + 1) / Real.log N) atTop (𝓝 K)) :
    ∀ᶠ N : ℕ in atTop, ∀ x : ι → ℂ, x ≠ 0 → 0 < hermQuad (horizonGram φ h (c N) N) x := by
  have hpos := pencilGram_posDef_below_apertureIndependentMultiple (φ := φ) hβ hK hsmall hh hsupp hlin
  have hev := eventually_hermQuad_pos_of_tendsto
    (pencilGram_isHermitian hφ hφsupp hφ2 hp hCφ hdecay hβ.le hbulk hh hA.le hsupp hc1 hK hcrit) hpos
    (tendsto_horizonGram hφ hφsupp hφ2 hp hCφ hdecay hβ.le hbulk hh hA.le hsupp hc1 hK hcrit)
  filter_upwards [hev, eventually_ge_atTop 1] with N hN hN1 x hx
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hw : 0 < c N / N := div_pos (by linarith [hc1 N]) hN0
  have hs : 0 < (c N)⁻¹ / ∫ u, atomDilate φ (c N / N) u ^ 2 := by
    rw [integral_atomDilate_sq φ hw]
    have : 0 < c N := by linarith [hc1 N]
    positivity
  have h := hN x hx
  rw [HTGeometry.hermQuad_smul] at h
  exact pos_of_mul_pos_right h hs.le

/-- For the tilted spline, one positive range of critical multiples gives
eventual positivity on every fixed finite window family. The starting index
may depend on the window and its family. -/
theorem tilted_exists_positive_multiple_inheriting_all_windows :
    ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ K : ℝ, 0 < K → K ≤ K₀ → ∀ A : ℝ, 0 < A → ∀ n : ℕ,
      ∀ h : Fin n → ℝ → ℝ, (∀ i, ContDiff ℝ 2 (h i)) →
      (∀ i y, y ∉ Set.Icc (-A) 0 → h i y = 0) → LinearIndependent ℝ h →
      ∀ c : ℕ → ℝ, (∀ N, 1 ≤ c N) →
      Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 K) →
      ∀ᶠ N : ℕ in atTop, ∀ x : Fin n → ℂ, x ≠ 0 →
        0 < hermQuad (horizonGram tiltedUnitSpline h (c N) N) x := by
  set C := (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
    exponentialWeilFloor 8
  have hC : 0 ≤ C := by
    have hM := integral_tiltedUnitSpline_sq_pos
    have hfloor := exponentialWeilFloor_pos (p := 8) (by norm_num)
    exact mul_nonneg (div_nonneg (sq_nonneg _) hM.le) hfloor.le
  have hden : 0 < 2 * (C + 1) := by positivity
  refine ⟨7 * tiltedJordanOne / (2 * (C + 1)),
    div_pos (mul_pos (by norm_num) tiltedJordanOne_pos) hden, ?_⟩
  intro K hK hKle A hA n h hh hsupp hlin c hc1 hcrit
  have hsmall : C * K < 7 * tiltedJordanOne := by
    have hbound := (le_div_iff₀ hden).mp hKle
    nlinarith only [hbound, mul_nonneg hC hK.le, hK]
  have hcrit' : Tendsto (fun N : ℕ => c N ^ ((7 : ℝ) + 1) / Real.log N)
      atTop (𝓝 K) := by
    simpa only [show (7 : ℝ) + 1 = (8 : ℕ) by norm_num, Real.rpow_natCast] using hcrit
  have hdecay : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  exact below_apertureIndependentMultiple_inherit contDiff_tiltedUnitSpline
    tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos (p := 8) (by norm_num)
    hdecay tiltedUnitSpline_decay (β := 7) (by norm_num)
    tendsto_rpow_seven_mul_completedShellEnergy_tilted hh hA hsupp hlin hc1 hK
    (by simpa only [show (7 : ℝ) + 1 = 8 by norm_num] using hsmall) hcrit'

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
