import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CriticalMultipleCompleteWeilPositivity
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonCriterion
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.OneCriticalMultiplePaysEveryWindow

/-!
# Complete-Weil positivity at a fixed critical multiple and its window corollaries

This file resolves the fixed-critical-multiple question for the complete Weil family of
`tiltedUnitSpline` together with its implications for growing-conductor uniformity, horizon Gram
matrices, the weighted window sign, the window index, and mixed untwisted/Ramanujan-twisted
window families:

* **Exact critical-multiple positive definiteness**
  (`exists_completeWeilMatrix_tiltedUnitSpline_eventually_posDef_at_critical_multiple`):
  there exists `K₁ > 0` (`2 K₁ ≤ 1`) such that eventually in `N`,
  `completeWeilMatrix tiltedUnitSpline (2 * K₁ * (log N)^{1/8}) N` (and the shifted matrix
  `spectralFloorWeilMatrix (2 * K₁ * (log N)^{1/8}) N`) is positive definite on the whole space
  `EuclideanSpace ℝ (PrimeHorizonIndex N)`.
* **Universal horizon-Gram nonnegativity and zero negative index**
  (`exists_universal_horizonGram_nonneg_and_zero_negIndex_at_critical_multiple`):
  at a single eventual threshold in `N` independent of window length, dimension, and test family,
  `0 ≤ hermQuad (horizonGram tiltedUnitSpline h c N) x` and
  `hermNegIndex (horizonGram tiltedUnitSpline h c N) = 0` hold across
  `1 ≤ c ≤ 2 K₁ (log N)^{1/8}` for every finite family `h : Fin n → ℝ → ℝ`.
* **Weighted window sign and vanishing window index on windows of every length**
  (`exists_secondOrderLimit_nonneg_and_pencilGram_zero_negIndex_from_completeWeil`):
  passing complete-Weil critical-multiple positivity along the canonical critical curve
  `c_N = max 1 ((M log N)^{1/8})` (`c_N^8 / log N → M`) via
  `horizon_layer_criticalCurve_of_regularBulk` and `eventually_hermNegIndex_pencilGram_le` yields
  `0 ≤ secondOrderLimit tiltedUnitSpline 7 tiltedJordanOne M h` and
  `hermNegIndex (pencilGram tiltedUnitSpline 7 tiltedJordanOne M hfam) = 0` for every
  `0 < M ≤ (2 K₁)^8`, every window length `A ≥ 0`, and every `C²` window profile/family supported
  in `[-A, 0]`, without any linear-independence hypothesis.
* **Joint critical-multiple synthesis**
  (`exists_joint_critical_multiple_completeWeil_and_all_window_corollaries`):
  one fixed `K₀ > 0` (`2 K₀ ≤ 1`) simultaneously gives whole-space positive definiteness of
  `spectralFloorWeilMatrix` and `completeWeilMatrix tiltedUnitSpline`, the uniform `(log N)^{-7/8}`
  growing-conductor floor on `(conductorSubspace 1 N)ᗮ`, the weighted window sign on windows of
  every length, strict positive definiteness of `pencilGram` on linearly independent window
  families of every length, and eventual strict positivity of `mixedGram` on mixed untwisted and
  Ramanujan-twisted window families along every critical curve `c_N^8 / log N → M`
  (`0 < M ≤ (2 K₀)^8`).
-/

set_option autoImplicit false
noncomputable section

open Finset Filter Topology MeasureTheory Zeta23 Matrix
open scoped ComplexConjugate ComplexOrder RealInnerProductSpace

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri HTGeometry
  BezoutValuationIncidence RenormalizedArithmeticPotentialTheory CompletedArithmeticForms
  RenormalizedArithmeticPotentialTheory.CompletedShell WindowTowerOfSpecZ
  CriticalArithmeticCorrelationTheory

/-! ### 1. Exact critical-multiple positive definiteness on the whole space -/

/-- **Positive definiteness of `completeWeilMatrix` at one fixed critical multiple.**
There exists `K₁ > 0` (`2 K₁ ≤ 1`) such that eventually in `N`, both
`spectralFloorWeilMatrix (2 * K₁ * (log N)^{1/8}) N` and
`completeWeilMatrix tiltedUnitSpline (2 * K₁ * (log N)^{1/8}) N` are positive definite on the
entire prime-horizon space `EuclideanSpace ℝ (PrimeHorizonIndex N)`. -/
theorem exists_completeWeilMatrix_tiltedUnitSpline_eventually_posDef_at_critical_multiple :
    ∃ K₁ : ℝ, 0 < K₁ ∧ 2 * K₁ ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop,
        (spectralFloorWeilMatrix (2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ)) N).PosDef ∧
        (completeWeilMatrix tiltedUnitSpline
          (2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ)) N).PosDef := by
  obtain ⟨K₁_s, hKs_pos, h2Ks, hs_ev⟩ :=
    exists_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_at_critical_multiple
  obtain ⟨K₁_w, hKw_pos, h2Kw, hw_ev⟩ :=
    exists_tiltedUnitSpline_completeWeilMatrix_posDef_at_critical_multiple
  set K₁ := min K₁_s K₁_w
  have hK₁_pos : 0 < K₁ := lt_min hKs_pos hKw_pos
  have h2K₁ : 2 * K₁ ≤ 1 := by linarith [min_le_left K₁_s K₁_w]
  refine ⟨K₁, hK₁_pos, h2K₁, ?_⟩
  have hL8_lim : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (1 / 8 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards [hs_ev, hw_ev, hL8_lim.eventually_ge_atTop (1 / (2 * K₁))] with N hs hw hL8
  have hc1 : 1 ≤ 2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ) := by
    have hm := (div_le_iff₀ (by positivity : 0 < 2 * K₁)).mp hL8
    linarith only [hm]
  have hL8_nn : 0 ≤ Real.log (N : ℝ) ^ (1 / 8 : ℝ) :=
    le_trans (by positivity) hL8
  have hcs : 2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ) ≤
      2 * K₁_s * Real.log (N : ℝ) ^ (1 / 8 : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith [min_le_left K₁_s K₁_w]) hL8_nn
  have hcw : 2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ) ≤
      2 * K₁_w * Real.log (N : ℝ) ^ (1 / 8 : ℝ) :=
    mul_le_mul_of_nonneg_right (by linarith [min_le_right K₁_s K₁_w]) hL8_nn
  exact ⟨hs _ hc1 hcs, hw _ hc1 hcw⟩

/-! ### 2. Quadratic-form decomposition and universal nonnegativity of `horizonGram` -/

/-- Linear combinations of `horizonTest` match the `horizonTest` of the linear combination. -/
theorem horizonTest_linearCombination {ι : Type*} [Fintype ι]
    (φ : ℝ → ℝ) (h : ι → ℝ → ℝ) (y : ι → ℝ) (c : ℝ) (N : ℕ) :
    (fun u => ∑ i, y i * horizonTest φ (h i) c N u) =
      horizonTest φ (fun v => ∑ i, y i * h i v) c N := by
  funext u
  simp only [horizonTest, atomicTest, horizonWeights, sum_div, sum_mul, Finset.mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun n _ => sum_congr rfl fun i _ => by ring

private lemma weilFullFunctional_cx_eq_weilQuad {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    (RHTower.weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (cx F) (cx F))).re = weilQuad F := by
  rw [LogCells.weilQuad_eq_zetaW hF hFc]
  have hcF : ContDiff ℝ 2 (fun u => (F u : ℂ)) := cx_contDiff hF
  have hcFc : HasCompactSupport (fun u => (F u : ℂ)) := cx_hasCompactSupport hFc
  exact congrArg Complex.re (RHTower.zeta_W_eq_weilFullFunctional hcF hcFc).symm

/-- On real coefficient vectors, `hermQuad (horizonGram φ h c N)` equals `weilQuad` of the
combined horizon test. -/
theorem hermQuad_horizonGram_ofReal {ι : Type*} [Fintype ι] {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (h : ι → ℝ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (y : ι → ℝ) :
    hermQuad (horizonGram φ h c N) (fun i => (y i : ℂ)) =
      weilQuad (horizonTest φ (fun v => ∑ i, y i * h i v) c N) := by
  have hf : ∀ i, ContDiff ℝ 2 (cx (horizonTest φ (h i) c N)) :=
    fun i => cx_contDiff (contDiff_horizonTest hφ (h i) c N)
  have hfc : ∀ i, HasCompactSupport (cx (horizonTest φ (h i) c N)) :=
    fun i => cx_hasCompactSupport (hasCompactSupport_horizonTest hφsupp (h i) hc hN)
  unfold horizonGram
  rw [hermQuad_weilGram _ _ hf hfc]
  have hlin := horizonTest_linearCombination φ h y c N
  have hS : (∑ i, conj ((y i : ℂ)) • cx (horizonTest φ (h i) c N)) =
      cx (horizonTest φ (fun v => ∑ i, y i * h i v) c N) := by
    funext u
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Complex.conj_ofReal, cx, ← hlin,
      Complex.ofReal_sum, Complex.ofReal_mul]
  rw [hS]
  exact weilFullFunctional_cx_eq_weilQuad (contDiff_horizonTest hφ _ c N)
    (hasCompactSupport_horizonTest hφsupp _ hc hN)

/-- On complex coefficient vectors, `hermQuad (horizonGram φ h c N) x` splits into `weilQuad` on
the real and imaginary linear combinations of `h`. -/
theorem hermQuad_horizonGram_eq_re_add_im {ι : Type*} [Fintype ι] {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (h : ι → ℝ → ℝ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) (x : ι → ℂ) :
    hermQuad (horizonGram φ h c N) x =
      weilQuad (horizonTest φ (fun v => ∑ i, (x i).re * h i v) c N) +
        weilQuad (horizonTest φ (fun v => ∑ i, (x i).im * h i v) c N) := by
  have hreal : ∀ i j, (horizonGram φ h c N i j).im = 0 := fun i j => by
    rw [horizonGram_apply hφ hφsupp h hc hN i j, Complex.ofReal_im]
  rw [hermQuad_eq_re_add_im hreal x,
    hermQuad_horizonGram_ofReal hφ hφsupp h hc hN (fun i => (x i).re),
    hermQuad_horizonGram_ofReal hφ hφsupp h hc hN (fun i => (x i).im)]

/-- A matrix whose Hermitian quadratic form is everywhere nonnegative has zero negative index. -/
theorem hermNegIndex_eq_zero_of_hermQuad_nonneg {ι : Type*} [Fintype ι] {G : Matrix ι ι ℂ}
    (hnn : ∀ x : ι → ℂ, 0 ≤ hermQuad G x) :
    hermNegIndex G = 0 := by
  obtain ⟨W, hWr, hW⟩ := exists_isPosDefOn_finrank_eq_posIndex (-G)
  have hbot : W = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Submodule.mem_bot]
    by_contra hx0
    have h1 := hW x hx hx0
    have h2 := hnn x
    rw [hermQuad_neg] at h1
    linarith only [h1, h2]
  unfold hermNegIndex
  rw [← hWr, hbot, finrank_bot]

/-- **Universal nonnegativity and zero negative index of `horizonGram` at a fixed critical
multiple.** There exists `K₁ > 0` (`2 K₁ ≤ 1`) and a single eventual threshold in `N` — uniform
across all overlap ratios `1 ≤ c ≤ 2 K₁ (log N)^{1/8}`, all dimensions `n : ℕ`, and all profile
families `h : Fin n → ℝ → ℝ` — such that `0 ≤ hermQuad (horizonGram tiltedUnitSpline h c N) x`
for every `x : Fin n → ℂ` and `hermNegIndex (horizonGram tiltedUnitSpline h c N) = 0`. -/
theorem exists_universal_horizonGram_nonneg_and_zero_negIndex_at_critical_multiple :
    ∃ K₁ : ℝ, 0 < K₁ ∧ 2 * K₁ ≤ 1 ∧
      ∀ᶠ N : ℕ in atTop,
        ∀ c : ℝ, 1 ≤ c → c ≤ 2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ) →
          ∀ (n : ℕ) (h : Fin n → ℝ → ℝ),
            (∀ x : Fin n → ℂ, 0 ≤ hermQuad (horizonGram tiltedUnitSpline h c N) x) ∧
            hermNegIndex (horizonGram tiltedUnitSpline h c N) = 0 := by
  obtain ⟨K₁, hK₁_pos, h2K₁, hw_ev⟩ :=
    exists_tiltedUnitSpline_weilQuad_nonneg_at_critical_multiple
  refine ⟨K₁, hK₁_pos, h2K₁, ?_⟩
  filter_upwards [hw_ev, eventually_ge_atTop 1] with N hw hN1 c hc1 hcup n h
  have hc0 : 0 < c := zero_lt_one.trans_le hc1
  have hnn : ∀ x : Fin n → ℂ, 0 ≤ hermQuad (horizonGram tiltedUnitSpline h c N) x := fun x => by
    rw [hermQuad_horizonGram_eq_re_add_im contDiff_tiltedUnitSpline tiltedUnitSpline_support
      h hc0 hN1 x]
    exact add_nonneg (hw c hc1 hcup _) (hw c hc1 hcup _)
  exact ⟨hnn, hermNegIndex_eq_zero_of_hermQuad_nonneg hnn⟩

/-! ### 3. The canonical critical curve and deduction of the weighted window sign and window index -/

/-- Canonical critical schedule `c_N = max 1 ((M log N)^{1/8})` realizing `c_N^8 / log N → M`. -/
def canonicalCriticalCurve (M : ℝ) (N : ℕ) : ℝ :=
  max 1 ((M * Real.log (N : ℝ)) ^ (1 / 8 : ℝ))

theorem one_le_canonicalCriticalCurve (M : ℝ) (N : ℕ) :
    1 ≤ canonicalCriticalCurve M N :=
  le_max_left 1 _

theorem eventually_canonicalCriticalCurve_le_and_eq {K₁ M : ℝ}
    (hK₁ : 0 < K₁) (hM : 0 < M) (hM_le : M ≤ (2 * K₁) ^ 8) :
    ∀ᶠ N : ℕ in atTop,
      canonicalCriticalCurve M N ≤ 2 * K₁ * Real.log (N : ℝ) ^ (1 / 8 : ℝ) ∧
      canonicalCriticalCurve M N ^ 8 / Real.log (N : ℝ) = M := by
  have hL_lim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hL_lim.eventually_ge_atTop (max 1 (1 / M))] with N hLN
  have hL1 : 1 ≤ Real.log (N : ℝ) := (le_max_left _ _).trans hLN
  have hL0 : 0 < Real.log (N : ℝ) := zero_lt_one.trans_le hL1
  have h1M : 1 / M ≤ Real.log (N : ℝ) := (le_max_right _ _).trans hLN
  have hML1 : 1 ≤ M * Real.log (N : ℝ) := by
    have hm := (div_le_iff₀ hM).mp h1M
    linarith only [hm]
  have hML_pos : 0 < M * Real.log (N : ℝ) := zero_lt_one.trans_le hML1
  have hmax_eq : canonicalCriticalCurve M N = (M * Real.log (N : ℝ)) ^ (1 / 8 : ℝ) :=
    max_eq_right (Real.one_le_rpow hML1 (by norm_num))
  have hM_rpow : M ^ (1 / 8 : ℝ) ≤ 2 * K₁ := by
    calc
      M ^ (1 / 8 : ℝ) ≤ ((2 * K₁) ^ 8) ^ (1 / 8 : ℝ) :=
        Real.rpow_le_rpow hM.le hM_le (by norm_num)
      _ = 2 * K₁ := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        norm_num [Real.rpow_one]
  refine ⟨?_, ?_⟩
  · rw [hmax_eq, Real.mul_rpow hM.le hL0.le]
    exact mul_le_mul_of_nonneg_right hM_rpow (by positivity)
  · rw [hmax_eq]
    have hp8 : ((M * Real.log (N : ℝ)) ^ (1 / 8 : ℝ)) ^ 8 = M * Real.log (N : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hML_pos.le]
      norm_num [Real.rpow_one]
    rw [hp8, mul_div_cancel_right₀ M hL0.ne']

theorem tendsto_canonicalCriticalCurve_pow_eight {M : ℝ} (hM : 0 < M) :
    Tendsto (fun N : ℕ => canonicalCriticalCurve M N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 M) := by
  have hK : 0 < M ^ (1 / 8 : ℝ) / 2 := by positivity
  have hM_eq : M ≤ (2 * (M ^ (1 / 8 : ℝ) / 2)) ^ 8 := by
    have he : 2 * (M ^ (1 / 8 : ℝ) / 2) = M ^ (1 / 8 : ℝ) := by ring
    rw [he, ← Real.rpow_natCast, ← Real.rpow_mul hM.le]
    norm_num [Real.rpow_one]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_canonicalCriticalCurve_le_and_eq hK hM hM_eq] with N hN
  exact hN.2.symm

/-- **Weighted window sign and zero window index on windows of every length, deduced directly from
complete-Weil critical-multiple positivity.**
There exists `K₁ > 0` (`2 K₁ ≤ 1`) such that for every critical multiple `0 < M ≤ (2 K₁)^8` and
every window length `A ≥ 0`:
1. Every `C²` window profile `h` supported in `[-A, 0]` satisfies
   `0 ≤ secondOrderLimit tiltedUnitSpline 7 tiltedJordanOne M h`, i.e.
   `0 ≤ ((∫ tiltedUnitSpline)^2 / ∫ tiltedUnitSpline^2) * weilQuad (halfWeight h) + (7 * tiltedJordanOne / M) * ∫ y, exp (-8 * y) * halfWeight h y ^ 2`.
2. Every finite `C²` window family `hfam : ι → ℝ → ℝ` supported in `[-A, 0]` (without any linear
   independence assumption) has `hermNegIndex (pencilGram tiltedUnitSpline 7 tiltedJordanOne M hfam) = 0`. -/
theorem exists_secondOrderLimit_nonneg_and_pencilGram_zero_negIndex_from_completeWeil :
    ∃ K₁ : ℝ, 0 < K₁ ∧ 2 * K₁ ≤ 1 ∧
      ∀ M : ℝ, 0 < M → M ≤ (2 * K₁) ^ 8 →
        ∀ A : ℝ, 0 ≤ A →
          (∀ h : ℝ → ℝ, ContDiff ℝ 2 h → (∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) →
            0 ≤ secondOrderLimit tiltedUnitSpline 7 tiltedJordanOne M h) ∧
          (∀ (n : ℕ) (hfam : Fin n → ℝ → ℝ), (∀ i, ContDiff ℝ 2 (hfam i)) →
            (∀ i y, y ∉ Set.Icc (-A) 0 → hfam i y = 0) →
            hermNegIndex (pencilGram tiltedUnitSpline 7 tiltedJordanOne M hfam) = 0) := by
  obtain ⟨K₁, hK₁_pos, h2K₁, hw_ev⟩ :=
    exists_tiltedUnitSpline_weilQuad_nonneg_at_critical_multiple
  refine ⟨K₁, hK₁_pos, h2K₁, ?_⟩
  intro M hM hM_le A hA
  have hc1 : ∀ N : ℕ, 1 ≤ canonicalCriticalCurve M N := one_le_canonicalCriticalCurve M
  have hcrit8 : Tendsto (fun N : ℕ => canonicalCriticalCurve M N ^ 8 / Real.log (N : ℝ))
      atTop (𝓝 M) := tendsto_canonicalCriticalCurve_pow_eight hM
  have hcrit : Tendsto (fun N : ℕ => canonicalCriticalCurve M N ^ ((7 : ℝ) + 1) / Real.log (N : ℝ))
      atTop (𝓝 M) := by
    refine hcrit8.congr fun N => ?_
    rw [show (7 : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hev_c := eventually_canonicalCriticalCurve_le_and_eq hK₁_pos hM hM_le
  refine ⟨?_, ?_⟩
  · intro h hh hsupp
    have hlim := horizon_layer_criticalCurve_of_regularBulk contDiff_tiltedUnitSpline
      tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos (p := 8) (by norm_num) hC
      tiltedUnitSpline_decay (β := 7) (by norm_num)
      tendsto_rpow_seven_mul_completedShellEnergy_tilted hh hA hsupp hc1 hM hcrit
    refine ge_of_tendsto hlim ?_
    filter_upwards [hw_ev, hev_c, eventually_ge_atTop 1] with N hw hc_le hN1
    have hc0 : 0 < canonicalCriticalCurve M N := zero_lt_one.trans_le (hc1 N)
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
    have hw_div : 0 < canonicalCriticalCurve M N / N := div_pos hc0 hN0
    have hden : 0 < ∫ u, atomDilate tiltedUnitSpline (canonicalCriticalCurve M N / N) u ^ 2 := by
      rw [integral_atomDilate_sq _ hw_div]
      exact mul_pos hw_div integral_tiltedUnitSpline_sq_pos
    have hq : 0 ≤ weilQuad (horizonTest tiltedUnitSpline h (canonicalCriticalCurve M N) N) :=
      hw _ (hc1 N) hc_le.1 (horizonWeights h N)
    exact mul_nonneg (inv_nonneg.mpr hc0.le) (div_nonneg hq hden.le)
  · intro n hfam hh hsupp
    have hlsc := eventually_hermNegIndex_pencilGram_le contDiff_tiltedUnitSpline
      tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos (p := 8) (by norm_num) hC
      tiltedUnitSpline_decay (β := 7) (by norm_num)
      tendsto_rpow_seven_mul_completedShellEnergy_tilted hh hA hsupp hc1 hM hcrit
    have hev0 : ∀ᶠ N : ℕ in atTop,
        hermNegIndex (pencilGram tiltedUnitSpline 7 tiltedJordanOne M hfam) ≤ 0 := by
      filter_upwards [hlsc, hw_ev, hev_c, eventually_ge_atTop 1] with N hle hw hc_le hN1
      have hc0 : 0 < canonicalCriticalCurve M N := zero_lt_one.trans_le (hc1 N)
      have hnn : ∀ x : Fin n → ℂ,
          0 ≤ hermQuad (horizonGram tiltedUnitSpline hfam (canonicalCriticalCurve M N) N) x :=
        fun x => by
          rw [hermQuad_horizonGram_eq_re_add_im contDiff_tiltedUnitSpline
            tiltedUnitSpline_support hfam hc0 hN1 x]
          exact add_nonneg (hw _ (hc1 N) hc_le.1 _) (hw _ (hc1 N) hc_le.1 _)
      rwa [hermNegIndex_eq_zero_of_hermQuad_nonneg hnn] at hle
    obtain ⟨_, h0⟩ := hev0.exists
    exact Nat.eq_zero_of_le_zero h0

/-! ### 4. Joint fixed-critical-multiple synthesis across all space and all windows -/

/-- **Joint resolution at a single fixed critical multiple `K₀ > 0`.**
There exists `K₀ > 0` (`2 K₀ ≤ 1`) simultaneously establishing:
1. Eventual positive definiteness of `spectralFloorWeilMatrix c N` and
   `completeWeilMatrix tiltedUnitSpline c N` uniformly across `1 ≤ c ≤ 2 K₀ (log N)^{1/8}` (and in
   particular at `c = 2 K₀ (log N)^{1/8}`), together with the uniform `(log N)^{-7/8}` spectral
   floor on the growing-conductor hyperplane `(conductorSubspace 1 N)ᗮ`.
2. For every critical multiple `0 < M ≤ (2 K₀)^8` and every window length `A ≥ 0`, nonnegativity of
   `secondOrderLimit tiltedUnitSpline 7 tiltedJordanOne M h` on every `C²` window profile `h`
   supported in `[-A, 0]`, and strict positive definiteness of
   `pencilGram tiltedUnitSpline 7 tiltedJordanOne M hfam` on every linearly independent `C²`
   window family `hfam : Fin n → ℝ → ℝ` supported in `[-A, 0]`.
3. Eventual strict positivity of `mixedGram tiltedUnitSpline hfam gfam (ramComb S a) (c N) N` on
   any mixed family of linearly independent untwisted and Ramanujan-twisted `C²` windows of any
   length `A ≥ 0` along every schedule `c N ≥ 1` with `c N ^ 8 / log N → M` (`0 < M ≤ (2 K₀)^8`). -/
theorem exists_joint_critical_multiple_completeWeil_and_all_window_corollaries :
    ∃ K₀ : ℝ, 0 < K₀ ∧ 2 * K₀ ≤ 1 ∧
      (∀ᶠ N : ℕ in atTop,
        (spectralFloorWeilMatrix (2 * K₀ * Real.log (N : ℝ) ^ (1 / 8 : ℝ)) N).PosDef ∧
        (completeWeilMatrix tiltedUnitSpline
          (2 * K₀ * Real.log (N : ℝ) ^ (1 / 8 : ℝ)) N).PosDef) ∧
      (∀ᶠ N : ℕ in atTop,
        ∀ c : ℝ, 1 ≤ c → c ≤ 2 * K₀ * Real.log (N : ℝ) ^ (1 / 8 : ℝ) →
          (spectralFloorWeilMatrix c N).PosDef ∧
          (completeWeilMatrix tiltedUnitSpline c N).PosDef ∧
          ∀ {z : EuclideanSpace ℝ (PrimeHorizonIndex N)}, z ∈ (conductorSubspace 1 N)ᗮ →
            (tiltedSplineSpectralFloorConstant /
                (2 * (2 * K₀) ^ 7 * Real.log (N : ℝ) ^ (7 / 8 : ℝ))) * ‖z‖ ^ 2 ≤
              completeWeilEnergy tiltedUnitSpline c N z) ∧
      (∀ M : ℝ, 0 < M → M ≤ (2 * K₀) ^ 8 →
        ∀ A : ℝ, 0 ≤ A →
          (∀ h : ℝ → ℝ, ContDiff ℝ 2 h → (∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) →
            0 ≤ secondOrderLimit tiltedUnitSpline 7 tiltedJordanOne M h) ∧
          (∀ (n : ℕ) (hfam : Fin n → ℝ → ℝ), (∀ i, ContDiff ℝ 2 (hfam i)) →
            (∀ i y, y ∉ Set.Icc (-A) 0 → hfam i y = 0) → LinearIndependent ℝ hfam →
            ∀ x : Fin n → ℂ, x ≠ 0 →
              0 < hermQuad (pencilGram tiltedUnitSpline 7 tiltedJordanOne M hfam) x) ∧
          (∀ (n m : ℕ) (hfam : Fin n → ℝ → ℝ) (gfam : Fin m → ℝ → ℝ),
            (∀ i, ContDiff ℝ 2 (hfam i)) → (∀ j, ContDiff ℝ 2 (gfam j)) →
            (∀ i y, y ∉ Set.Icc (-A) 0 → hfam i y = 0) →
            (∀ j y, y ∉ Set.Icc (-A) 0 → gfam j y = 0) →
            LinearIndependent ℝ hfam → LinearIndependent ℝ gfam →
            ∀ (S : Finset ℕ), (∀ q ∈ S, 1 < q) →
            ∀ (a : ℕ → ℝ), (∃ q ∈ S, a q ≠ 0) →
            ∀ (c : ℕ → ℝ), (∀ N, 1 ≤ c N) →
            Tendsto (fun N : ℕ => c N ^ 8 / Real.log (N : ℝ)) atTop (𝓝 M) →
            ∀ᶠ N : ℕ in atTop, ∀ x : Fin n ⊕ Fin m → ℂ, x ≠ 0 →
              0 < hermQuad (mixedGram tiltedUnitSpline hfam gfam (ramComb S a) (c N) N) x)) := by
  obtain ⟨K₁_s, hKs_pos, h2Ks, hs_ev⟩ :=
    exists_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_at_critical_multiple
  obtain ⟨K₁_w, hKw_pos, _, hw_ev⟩ :=
    exists_tiltedUnitSpline_completeWeilMatrix_posDef_at_critical_multiple
  obtain ⟨K₁_fl, hKfl_pos, _, hfl_ev⟩ :=
    exists_tiltedUnitSpline_completeWeilEnergy_ge_spectral_floor_at_critical_multiple
  obtain ⟨K₁_sol, hKsol_pos, _, hsol⟩ :=
    exists_secondOrderLimit_nonneg_and_pencilGram_zero_negIndex_from_completeWeil
  set C_win := (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
    exponentialWeilFloor 8
  have hC_win_nn : 0 ≤ C_win :=
    mul_nonneg (div_nonneg (sq_nonneg _) integral_tiltedUnitSpline_sq_pos.le)
      (exponentialWeilFloor_pos (p := 8) (by norm_num)).le
  set M_win := 7 * tiltedJordanOne / (2 * (C_win + 1))
  have hM_win_pos : 0 < M_win :=
    div_pos (mul_pos (by norm_num) tiltedJordanOne_pos) (by positivity)
  set K_win := M_win ^ (1 / 8 : ℝ) / 2
  have hK_win_pos : 0 < K_win := by positivity
  set K₀ := min (min (min K₁_s K₁_w) (min K₁_fl K₁_sol)) K_win
  have hK₀_pos : 0 < K₀ :=
    lt_min (lt_min (lt_min hKs_pos hKw_pos) (lt_min hKfl_pos hKsol_pos)) hK_win_pos
  have hK₀_s : K₀ ≤ K₁_s :=
    ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_left _ _)
  have hK₀_w : K₀ ≤ K₁_w :=
    ((min_le_left _ _).trans (min_le_left _ _)).trans (min_le_right _ _)
  have hK₀_fl : K₀ ≤ K₁_fl :=
    ((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_left _ _)
  have hK₀_sol : K₀ ≤ K₁_sol :=
    ((min_le_left _ _).trans (min_le_right _ _)).trans (min_le_right _ _)
  have hK₀_win : K₀ ≤ K_win := min_le_right _ _
  have h2K₀ : 2 * K₀ ≤ 1 := by linarith only [hK₀_s, h2Ks]
  have hL8_lim : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (1 / 8 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 8)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  refine ⟨K₀, hK₀_pos, h2K₀, ?_, ?_, ?_⟩
  · filter_upwards [hs_ev, hw_ev, hL8_lim.eventually_ge_atTop (1 / (2 * K₀))] with N hs hw hL8
    have hc1 : 1 ≤ 2 * K₀ * Real.log (N : ℝ) ^ (1 / 8 : ℝ) := by
      have hm := (div_le_iff₀ (by positivity : 0 < 2 * K₀)).mp hL8
      linarith only [hm]
    have hL8_nn : 0 ≤ Real.log (N : ℝ) ^ (1 / 8 : ℝ) := le_trans (by positivity) hL8
    exact ⟨hs _ hc1 (mul_le_mul_of_nonneg_right (by linarith only [hK₀_s]) hL8_nn),
      hw _ hc1 (mul_le_mul_of_nonneg_right (by linarith only [hK₀_w]) hL8_nn)⟩
  · filter_upwards [hs_ev, hw_ev, hfl_ev, eventually_ge_atTop 3] with N hs hw hfl hN3
      c hc1 hcup
    have hc0 : 0 < c := zero_lt_one.trans_le hc1
    have hN3R : (3 : ℝ) ≤ N := by exact_mod_cast hN3
    have hL_pos : 0 < Real.log (N : ℝ) := Real.log_pos (by linarith only [hN3R])
    have hL8_nn : 0 ≤ Real.log (N : ℝ) ^ (1 / 8 : ℝ) := Real.rpow_nonneg hL_pos.le _
    refine ⟨hs c hc1 (hcup.trans (mul_le_mul_of_nonneg_right (by linarith only [hK₀_s]) hL8_nn)),
      hw c hc1 (hcup.trans (mul_le_mul_of_nonneg_right (by linarith only [hK₀_w]) hL8_nn)),
      fun {z} _hz => ?_⟩
    have hc7_le : c ^ 7 ≤ (2 * K₀) ^ 7 * Real.log (N : ℝ) ^ (7 / 8 : ℝ) := by
      calc
        c ^ 7 ≤ (2 * K₀ * Real.log (N : ℝ) ^ (1 / 8 : ℝ)) ^ 7 := pow_le_pow_left₀ hc0.le hcup 7
        _ = (2 * K₀) ^ 7 * (Real.log (N : ℝ) ^ (1 / 8 : ℝ)) ^ 7 := mul_pow _ _ 7
        _ = (2 * K₀) ^ 7 * Real.log (N : ℝ) ^ (7 / 8 : ℝ) := by
          rw [← Real.rpow_natCast (Real.log (N : ℝ) ^ (1 / 8 : ℝ)) 7, ← Real.rpow_mul hL_pos.le]
          norm_num
    have hdiv_le : tiltedSplineSpectralFloorConstant /
        (2 * (2 * K₀) ^ 7 * Real.log (N : ℝ) ^ (7 / 8 : ℝ)) ≤
        tiltedSplineSpectralFloorConstant / (2 * c ^ 7) := by
      refine div_le_div_of_nonneg_left tiltedSplineSpectralFloorConstant_pos.le (by positivity) ?_
      linarith only [hc7_le,
        (by ring : 2 * ((2 * K₀) ^ 7 * Real.log (N : ℝ) ^ (7 / 8 : ℝ)) =
          2 * (2 * K₀) ^ 7 * Real.log (N : ℝ) ^ (7 / 8 : ℝ))]
    have hf := hfl c hc1
      (hcup.trans (mul_le_mul_of_nonneg_right (by linarith only [hK₀_fl]) hL8_nn)) z
    exact (mul_le_mul_of_nonneg_right hdiv_le (sq_nonneg ‖z‖)).trans hf
  · intro M hM hM_le A hA
    have hM_sol : M ≤ (2 * K₁_sol) ^ 8 :=
      hM_le.trans (pow_le_pow_left₀ (by positivity) (by linarith only [hK₀_sol]) 8)
    have hM_win_le : M ≤ M_win := by
      have h1 : (2 * K₀) ^ 8 ≤ (2 * K_win) ^ 8 :=
        pow_le_pow_left₀ (by positivity) (by linarith only [hK₀_win]) 8
      have h2 : (2 * K_win) ^ 8 = M_win := by
        have he : 2 * K_win = M_win ^ (1 / 8 : ℝ) := by dsimp [K_win]; ring
        rw [he, ← Real.rpow_natCast, ← Real.rpow_mul hM_win_pos.le]
        norm_num [Real.rpow_one]
      exact hM_le.trans (h1.trans_eq h2)
    have hsmall : (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
        exponentialWeilFloor ((7 : ℝ) + 1) * M < 7 * tiltedJordanOne := by
      have h8 : ((7 : ℝ) + 1) = 8 := by norm_num
      rw [h8]
      change C_win * M < 7 * tiltedJordanOne
      have hden : 0 < 2 * (C_win + 1) := by positivity
      have hbound : M * (2 * (C_win + 1)) ≤ 7 * tiltedJordanOne :=
        (le_div_iff₀ hden).mp hM_win_le
      nlinarith only [hbound, mul_nonneg hC_win_nn hM.le, hM]
    have hPpos_all : ∀ (n : ℕ) (hfam : Fin n → ℝ → ℝ), (∀ i, ContDiff ℝ 2 (hfam i)) →
        (∀ i y, y ∉ Set.Icc (-A) 0 → hfam i y = 0) → LinearIndependent ℝ hfam →
        ∀ x : Fin n → ℂ, x ≠ 0 →
          0 < hermQuad (pencilGram tiltedUnitSpline 7 tiltedJordanOne M hfam) x :=
      fun _ hfam hh hsupp hlin =>
        pencilGram_posDef_below_apertureIndependentMultiple (φ := tiltedUnitSpline)
          (β := 7) (by norm_num) hM hsmall hh hsupp hlin
    refine ⟨(hsol M hM hM_sol A hA).1, hPpos_all, ?_⟩
    intro n m hfam gfam hh hg hsupp hgsupp hlinh hling S hS a ha c hc1 hcrit8
    have hcrit : Tendsto (fun N : ℕ => c N ^ ((7 : ℝ) + 1) / Real.log (N : ℝ)) atTop (𝓝 M) := by
      refine hcrit8.congr fun N => ?_
      rw [show (7 : ℝ) + 1 = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hsum : 0 < ∑ q ∈ S,
        a q ^ 2 * ArithmeticDegenerationTheory.jordanTotient ((7 : ℝ) + 1) q := by
      obtain ⟨q₀, hq₀, haq₀⟩ := ha
      rw [show ((7 : ℝ) + 1) = 8 by norm_num]
      have hnn : ∀ q ∈ S, 0 ≤ a q ^ 2 * ArithmeticDegenerationTheory.jordanTotient 8 q :=
        fun q hq => mul_nonneg (sq_nonneg _)
          (ArithmeticDegenerationTheory.jordanTotient_eight_pos (by linarith [hS q hq])).le
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum hnn hq₀)
      exact mul_pos (by positivity)
        (ArithmeticDegenerationTheory.jordanTotient_eight_pos (by linarith [hS q₀ hq₀]))
    have hC_dec : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
    exact mixed_inherit_of_pencil_pos contDiff_tiltedUnitSpline tiltedUnitSpline_support
      integral_tiltedUnitSpline_sq_pos (q := 8) (by norm_num) hC_dec tiltedUnitSpline_decay
      (β := 7) (by norm_num) tendsto_rpow_seven_mul_completedShellEnergy_tilted
      hh hg hA hsupp hgsupp hling hc1 hM hcrit hS a
      (by have := tiltedJordanOne_pos; positivity)
      (hPpos_all n hfam hh hsupp hlinh)

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
