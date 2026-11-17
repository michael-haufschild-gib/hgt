import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroSideIsNormalisedAtTheLeftEnd
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheZeroValuesOfTheStateAreANegativeVectorOfTheZeroPairing
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheExplicitFormulaHoldsAtTheStateAgainstSmoothTests
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateChangesSignOnEveryRay
import GaloisForLFunctions.ArchimedeanTateDomination.FirstFoldStageDomination
import GaloisForLFunctions.RHTower.WeilMarkovOddSectorTrivialZeroSquares

/-!
# The collar weak equation is soft beyond `(★)`

On the collar `(-log 2, 0)` of the negative half-line, Weil's bare form is coercive on smooth tests
and no forward prime translate enters `primeMixedForm F G`: only backward prime translates
`F(u - log n)` (`n ≥ 2`), supported in `(-∞, -log 2)`, survive. Question E-Q4 asks whether
restricting the confined weak equation to tests supported in `(-log 2, 0)` constrains the values
`L F(z)` at the left zeros beyond the left-normalised Cauchy system `(★)`.

The answer is **no**: the collar is completely soft beyond `(★)`.

* **Collar prime & zero coordinates** (`primeMixedForm_openCollar`,
  `bareMixedEnergy_openCollar`, `criticalState_tendsto_openCollar_zeroPairing`,
  `criticalState_hasSum_openCollar_zeroPairing`). For any half-line profile `F` and any profile `G`
  vanishing outside `(-log 2, 0)`, all forward prime translates vanish and `bareMixedEnergy F G`
  is Gamma plus pole minus the backward prime sum `∑_n (Λ(n)/√n) ∫ F(t) G(t + log n) dt`, equal at
  the critical state to the zero series `∑_z L F(z) L G(-z)` and to `-a(W₀) ∫ F G e^{-8u}`.
* **Smooth-test explicit formula on the whole energy domain** (`hasSum_bareMixedEnergy_of_domain`).
  For **every** profile `F ∈ H` (without assuming the state equation) and every smooth compactly
  supported `G` on `u < 0`, `∑_z L F(z) L G(-z) = bareMixedEnergy F G`.
* **Complete subsumption by `(★)`** (`SatisfiesNormalisedStar`,
  `mixedEnergy_eq_zero_of_normalisedStar`, `openCollar_weakEquation_of_normalisedStar`,
  `normalisedStar_and_openCollarWeak_iff_normalisedStar`). Every profile `F ∈ H` satisfying
  left-normalised `(★)` at ratio `R` automatically satisfies `criticalHalfLineMixedEnergy R F G = 0`
  against all smooth compactly supported half-line tests `G`, and a fortiori on the collar
  `(-log 2, 0)`, as well as the Gaussian-summed zero-pairing law against the entire domain `H`.
  Hence the collar imposes zero additional constraints on `(L F(z_q))_q` beyond `(★)`.
* **Coercivity consequences** (`bareMixedEnergy_collarWindow_ge`,
  `norm_sq_openCollar_zeroPairing_le_of_normalisedStar`, `collar_difference_eq_zero_of_weak`,
  `criticalState_deepTail_sq_pos`). Collar positivity yields the explicit Cauchy–Schwarz bound
  `‖∑_z L F(z) L G(-z)‖² ≤ 2048000 a(R)² W₈(F| collar) B(G, G)` (already satisfied under `(★)`),
  uniqueness of `C²` collar extensions from a fixed tail on `(-∞, -log 2]`, and positive deep-tail
  mass `∫_{u < -A} F² > 0` for every `A ≥ 0`.
-/

noncomputable section
open MeasureTheory Set Filter Zeta23 Complex Metric Topology
open scoped ComplexConjugate ContDiff

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory CohomologyOfWindowsOfSpecZ SpacingScaleHarmonicAnalysis
  ArithmeticIncidencePositivity HTGeometry _root_.RHTower

/-! ### 1. Smooth collar tests and backward prime coordinates on `(-log 2, 0)` -/

/-- A real `C^∞` compactly supported test supported inside the open collar `(-log 2, 0)`. -/
def IsSmoothCollarTest (G : ℝ → ℝ) : Prop :=
  ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧ (∀ u, 0 ≤ u → G u = 0) ∧
    (∀ u, u ≤ -Real.log 2 → G u = 0)

theorem IsSmoothCollarTest.energyDomain {G : ℝ → ℝ} (hG : IsSmoothCollarTest G) :
    CriticalHalfLineEnergyDomain G :=
  criticalHalfLineEnergyDomain_of_compact_negative
    (hG.1.of_le (WithTop.coe_le_coe.mpr le_top)) hG.2.1 hG.2.2.1

theorem IsSmoothCollarTest.isWindowTest_log_two {G : ℝ → ℝ} (hG : IsSmoothCollarTest G) :
    IsWindowTest (Real.log 2) G := by
  refine ⟨hG.1.of_le (WithTop.coe_le_coe.mpr le_top), fun u hu => ?_⟩
  by_cases h0 : 0 ≤ u
  · exact hG.2.2.1 u h0
  · refine hG.2.2.2 u ?_
    by_contra hlt
    exact hu ⟨(not_le.mp hlt).le, (not_le.mp h0).le⟩

private theorem vonMangoldtAtom_zero_of_lt_two {n : ℕ} (hn : n < 2) : vonMangoldtAtom n = 0 := by
  unfold vonMangoldtAtom
  rw [if_neg (by omega)]

/-- On the full open collar `(-log 2, 0)`, every forward prime translate against a half-line
profile vanishes, leaving only the backward prime translate `∫ F(t) G(t + log n) dt`. -/
theorem primePairTerm_openCollar_left {F G : ℝ → ℝ} (hF : ∀ u, 0 ≤ u → F u = 0)
    (hG : ∀ u, u ≤ -Real.log 2 → G u = 0) (n : ℕ) :
    primePairTerm F G n = vonMangoldtAtom n * ∫ t, F t * G (t + Real.log n) := by
  unfold primePairTerm
  rcases lt_or_ge n 2 with hn | hn
  · rw [vonMangoldtAtom_zero_of_lt_two hn, zero_mul, zero_mul]
  · have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have h0 : (fun t => F t * G (t - Real.log n)) = fun _ => 0 := by
      funext t
      rcases le_or_gt 0 t with ht | ht
      · rw [hF t ht, zero_mul]
      · rw [hG (t - Real.log n) (by linarith), mul_zero]
    rw [h0, integral_zero, zero_add]

/-- The transposed prime term on `(-log 2, 0)` equals the same backward prime translate. -/
theorem primePairTerm_openCollar_right {F G : ℝ → ℝ} (hF : ∀ u, 0 ≤ u → F u = 0)
    (hG : ∀ u, u ≤ -Real.log 2 → G u = 0) (n : ℕ) :
    primePairTerm G F n = vonMangoldtAtom n * ∫ t, F t * G (t + Real.log n) := by
  unfold primePairTerm
  rcases lt_or_ge n 2 with hn | hn
  · rw [vonMangoldtAtom_zero_of_lt_two hn, zero_mul, zero_mul]
  · have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
    have h0 : (fun t => G t * F (t + Real.log n)) = fun _ => 0 := by
      funext t
      rcases le_or_gt t (-Real.log 2) with ht | ht
      · rw [hG t ht, zero_mul]
      · rw [hF (t + Real.log n) (by linarith), mul_zero]
    have hs : (∫ t, G t * F (t - Real.log n)) = ∫ t, F t * G (t + Real.log n) := by
      have h := integral_add_right_eq_self (μ := volume)
        (fun t => G t * F (t - Real.log n)) (Real.log n)
      simp only [add_sub_cancel_right] at h
      rw [← h]
      exact integral_congr_ae (Eventually.of_forall fun t => mul_comm _ _)
    rw [h0, integral_zero, add_zero, hs]

/-- **Prime coordinates on the collar.** Against any profile `G` vanishing on `(-∞, -log 2]`,
`primeMixedForm` contains only backward prime translates of `F`. -/
theorem primeMixedForm_openCollar {F G : ℝ → ℝ} (hF : ∀ u, 0 ≤ u → F u = 0)
    (hG : ∀ u, u ≤ -Real.log 2 → G u = 0) :
    primeMixedForm F G = ∑' n : ℕ, vonMangoldtAtom n * ∫ t, F t * G (t + Real.log n) ∧
      primeMixedForm G F = ∑' n : ℕ, vonMangoldtAtom n * ∫ t, F t * G (t + Real.log n) := by
  unfold primeMixedForm
  exact ⟨tsum_congr (primePairTerm_openCollar_left hF hG),
    tsum_congr (primePairTerm_openCollar_right hF hG)⟩

/-- Two profiles both supported in `(-log 2, 0)` have zero mutual prime correlation. -/
theorem primeMixedForm_both_openCollar_eq_zero {F G : ℝ → ℝ}
    (hF0 : ∀ u, 0 ≤ u → F u = 0) (hFc : ∀ u, u ≤ -Real.log 2 → F u = 0)
    (hG0 : ∀ u, 0 ≤ u → G u = 0) (hGc : ∀ u, u ≤ -Real.log 2 → G u = 0) :
    primeMixedForm F G = 0 := by
  rw [(primeMixedForm_openCollar hF0 hGc).1]
  have hterm : (fun n : ℕ => vonMangoldtAtom n * ∫ t, F t * G (t + Real.log n)) = fun _ => 0 := by
    funext n
    rcases lt_or_ge n 2 with hn | hn
    · rw [vonMangoldtAtom_zero_of_lt_two hn, zero_mul]
    · have hlog : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
      have h0 : (fun t => F t * G (t + Real.log n)) = fun _ => 0 := by
        funext t
        rcases le_or_gt t (-Real.log 2) with ht | ht
        · rw [hFc t ht, zero_mul]
        · rw [hG0 (t + Real.log n) (by linarith), mul_zero]
      rw [h0, integral_zero, mul_zero]
  rw [hterm, tsum_zero]

/-- **Bare Weil form in collar prime coordinates.** For `F` on `(-∞, 0)` and `G` vanishing on
`(-∞, -log 2]`, `bareMixedEnergy F G` is Gamma minus backward prime translates plus the pole part. -/
theorem bareMixedEnergy_openCollar {F G : ℝ → ℝ} (hF : ∀ u, 0 ≤ u → F u = 0)
    (hG : ∀ u, u ≤ -Real.log 2 → G u = 0) :
    bareMixedEnergy F G =
      gammaMixedForm F G - (∑' n : ℕ, vonMangoldtAtom n * ∫ t, F t * G (t + Real.log n)) +
        (2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G) := by
  obtain ⟨h1, h2⟩ := primeMixedForm_openCollar hF hG
  unfold bareMixedEnergy
  rw [h1, h2]
  ring

/-- **First lemma of E-Q4 (Gaussian-summed collar explicit formula at the state).** For the
critical state `F` and every energy-domain collar profile `G` (`G = 0` on `(-∞, -log 2]`), the
Gaussian-summed zero pairing tends to the backward-prime collar form and to `-a(W₀) W₈(F, G)`. -/
theorem criticalState_tendsto_openCollar_zeroPairing {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ}
    (hG : CriticalHalfLineEnergyDomain G) (hGc : ∀ u, u ≤ -Real.log 2 → G u = 0) :
    Tendsto (fun ε : ℝ => ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero q ^ 2))
      (𝓝[>] 0)
      (𝓝 (((gammaMixedForm F G - (∑' n : ℕ, vonMangoldtAtom n * ∫ t, F t * G (t + Real.log n)) +
        (2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G) : ℝ) : ℂ))) ∧
      bareMixedEnergy F G = -(criticalAliasCoefficient W₀ *
        ∫ u in Ioo (-Real.log 2) 0, F u * G u * Real.exp (-(8 * u))) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have htend := criticalState_tendsto_zeroPairing hW hthreshold hF hG
  rw [bareMixedEnergy_openCollar hd.support hGc] at htend
  refine ⟨htend, ?_⟩
  have hw := criticalHalfLineMixedEnergy_groundState_eq_zero hW hthreshold hF hG
  rw [criticalHalfLineMixedEnergy_eq_bare_add] at hw
  have hI : (∫ u in Iio (0 : ℝ), F u * G u * Real.exp (-(8 * u))) =
      ∫ u in Ioo (-Real.log 2) 0, F u * G u * Real.exp (-(8 * u)) := by
    rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioo]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ Ioo (-Real.log 2) 0
    · rw [indicator_of_mem hu, indicator_of_mem (Set.mem_Iio.mpr hu.2)]
    · rw [indicator_of_notMem hu]
      by_cases h0 : u < 0
      · have hle : u ≤ -Real.log 2 := not_lt.mp fun hgt => hu ⟨hgt, h0⟩
        rw [indicator_of_mem (Set.mem_Iio.mpr h0), hGc u hle, mul_zero, zero_mul]
      · rw [indicator_of_notMem (show u ∉ Iio (0 : ℝ) from h0)]
  rw [hI] at hw
  linarith

/-- **Unregularized collar explicit formula at the state.** Against any `G ∈ C_c^∞((-log 2, 0))`,
the zero series `∑_z L F(z) L G(-z)` converges directly to the backward-prime collar form and to
`-a(W₀) ∫_{-log 2}^0 F(u) G(u) e^{-8u} du`. -/
theorem criticalState_hasSum_openCollar_zeroPairing {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {G : ℝ → ℝ}
    (hG : IsSmoothCollarTest G) :
    HasSum (fun q : XiZeroCopy =>
        negativeHalfLineLaplace (cx F) (centredZero q) *
          negativeHalfLineLaplace (cx G) (-centredZero q))
      (((gammaMixedForm F G - (∑' n : ℕ, vonMangoldtAtom n * ∫ t, F t * G (t + Real.log n)) +
        (2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G) : ℝ) : ℂ)) := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have h := criticalState_hasSum_bareMixedEnergy hW hthreshold hF hG.1 hG.2.1 hG.2.2.1
  rwa [bareMixedEnergy_openCollar hd.support hG.2.2.2] at h

/-! ### 2. Unconditional smooth-test explicit formula on the entire energy domain `H` -/

/-- Along `Re p = 5`, `∫ ψ̂(5 + it)/(5 + it + c) dt = 2π ∫_{u < 0} ψ(u) e^{c u} du` whenever
`c.re > -5`. -/
private theorem integral_laplaceTest_div_five {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) {c : ℂ} (hc : -5 < c.re) :
    ∫ t : ℝ, laplaceTest ψ (5 + t * I) * (1 / ((5 : ℂ) + t * I + c)) =
      2 * Real.pi * ∫ u : ℝ, ψ u * ((probe 0 u : ℂ) * Complex.exp (c * u)) := by
  have hφm : AEStronglyMeasurable (fun u : ℝ => (probe 0 u : ℂ) * Complex.exp (c * u)) volume :=
    ((Complex.measurable_ofReal.comp (measurable_probe 0)).mul
      (by fun_prop : Continuous fun u : ℝ => Complex.exp (c * u)).measurable).aestronglyMeasurable
  have hφi : Integrable (fun u : ℝ => Real.exp (5 * u) *
      ‖(probe 0 u : ℂ) * Complex.exp (c * u)‖) volume := by
    refine (integrable_probe (p := 5 + c.re) (by linarith)).congr (Eventually.of_forall fun u => ?_)
    dsimp only
    rcases lt_or_ge u 0 with hu | hu
    · rw [probe_of_neg hu, probe_of_neg hu, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        zero_mul, Real.exp_zero, abs_one, one_mul, norm_cexp_mul_ofReal, ← Real.exp_add]
      congr 1; ring
    · rw [probe_of_nonneg hu, probe_of_nonneg hu, Complex.ofReal_zero, zero_mul, norm_zero, mul_zero]
  have h := integral_laplaceTest_mul_laplace hψ hs 5 hφm hφi
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  have h5 : (((5 : ℝ) : ℂ) + (t : ℂ) * I) = (5 : ℂ) + t * I := by norm_num
  rw [h5]
  congr 1
  have hre : 0 < 0 + (((5 : ℂ) + t * I) + c).re := by simp; linarith
  have hp := integral_probe_mul_cexp (p := 0) (w := ((5 : ℂ) + t * I) + c) hre
  rw [Complex.ofReal_zero, zero_add] at hp
  rw [← hp]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  dsimp only
  rw [add_mul, Complex.exp_add]
  ring

/-- The pole term integrated against `laplaceTest (cx G)` on `Re p = 5` is integrable and yields
`2π` times the real pole pairing of `F` and `G`. -/
private theorem integral_laplaceTest_polePart_five (F : ℝ → ℝ) {G : ℝ → ℝ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (hG0 : ∀ u, 0 ≤ u → G u = 0) :
    (Integrable fun t : ℝ => laplaceTest (cx G) (5 + t * I) *
        ((coshHalfMoment F : ℂ) * (1 / ((5 : ℂ) + t * I + 1 / 2) + 1 / ((5 : ℂ) + t * I - 1 / 2)) -
          (sinhHalfMoment F : ℂ) * (1 / ((5 : ℂ) + t * I + 1 / 2) - 1 / ((5 : ℂ) + t * I - 1 / 2)))) ∧
      (∫ t : ℝ, laplaceTest (cx G) (5 + t * I) *
        ((coshHalfMoment F : ℂ) * (1 / ((5 : ℂ) + t * I + 1 / 2) + 1 / ((5 : ℂ) + t * I - 1 / 2)) -
          (sinhHalfMoment F : ℂ) * (1 / ((5 : ℂ) + t * I + 1 / 2) - 1 / ((5 : ℂ) + t * I - 1 / 2)))) =
      2 * Real.pi *
        ((2 * coshHalfMoment F * coshHalfMoment G - 2 * sinhHalfMoment F * sinhHalfMoment G : ℝ) : ℂ) := by
  have hψ : ContDiff ℝ ∞ (cx G) := Complex.ofRealCLM.contDiff.comp hG
  have hs : HasCompactSupport (cx G) := hc.comp_left Complex.ofReal_zero
  obtain ⟨D, hD0, hD⟩ := exists_laplaceTest_decay hψ hs 5 5
  have hint_c : ∀ c : ℂ, -5 < c.re →
      Integrable fun t : ℝ => laplaceTest (cx G) (5 + t * I) * (1 / ((5 : ℂ) + t * I + c)) := by
    intro c hcre
    have hmaj : Integrable fun t : ℝ => D / (5 + c.re) * (1 + t ^ 2)⁻¹ :=
      integrable_inv_one_add_sq.const_mul _
    refine hmaj.mono' ?_ (Eventually.of_forall fun t => ?_)
    · refine (((differentiable_laplaceTest hψ.continuous hs).continuous.comp
        (by fun_prop : Continuous fun t : ℝ => (5 : ℂ) + t * I)).mul
        (continuous_const.div (by fun_prop) fun t h0 => ?_)).aestronglyMeasurable
      have := congrArg Complex.re h0; simp at this; linarith
    · have hden : 5 + c.re ≤ ‖(5 : ℂ) + t * I + c‖ := by
        have h1 := Complex.abs_re_le_norm ((5 : ℂ) + t * I + c)
        have hre : ((5 : ℂ) + t * I + c).re = 5 + c.re := by simp
        rw [hre, abs_of_pos (by linarith)] at h1; exact h1
      have hH : ‖laplaceTest (cx G) (5 + t * I)‖ ≤ D * (1 + t ^ 2)⁻¹ := by
        have h5 := hD 5 t le_rfl le_rfl
        norm_num at h5
        refine h5.trans ?_
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left
          (inv_anti₀ (by positivity) (by nlinarith [sq_nonneg t])) hD0
      rw [norm_mul, norm_div, norm_one, one_div]
      calc ‖laplaceTest (cx G) (5 + t * I)‖ * ‖(5 : ℂ) + t * I + c‖⁻¹
          ≤ (D * (1 + t ^ 2)⁻¹) * (5 + c.re)⁻¹ :=
            mul_le_mul hH (inv_anti₀ (by linarith) hden) (inv_nonneg.mpr (norm_nonneg _)) (by positivity)
        _ = D / (5 + c.re) * (1 + t ^ 2)⁻¹ := by ring
  have i_pos := hint_c (1 / 2) (by norm_num)
  have i_neg := hint_c (-(1 / 2)) (by norm_num)
  have v_pos := integral_laplaceTest_div_five hψ hs (c := 1 / 2) (by norm_num)
  have v_neg := integral_laplaceTest_div_five hψ hs (c := -(1 / 2)) (by norm_num)
  have hlin : (fun t : ℝ => laplaceTest (cx G) (5 + t * I) *
      ((coshHalfMoment F : ℂ) * (1 / ((5 : ℂ) + t * I + 1 / 2) + 1 / ((5 : ℂ) + t * I - 1 / 2)) -
        (sinhHalfMoment F : ℂ) * (1 / ((5 : ℂ) + t * I + 1 / 2) - 1 / ((5 : ℂ) + t * I - 1 / 2)))) =
      fun t : ℝ => ((coshHalfMoment F - sinhHalfMoment F : ℝ) : ℂ) *
        (laplaceTest (cx G) (5 + t * I) * (1 / ((5 : ℂ) + t * I + 1 / 2))) +
        ((coshHalfMoment F + sinhHalfMoment F : ℝ) : ℂ) *
        (laplaceTest (cx G) (5 + t * I) * (1 / ((5 : ℂ) + t * I + -(1 / 2)))) := by
    funext t; rw [sub_eq_add_neg ((5 : ℂ) + t * I) (1 / 2)]; push_cast; ring
  refine ⟨by rw [hlin]; exact (i_pos.const_mul _).add (i_neg.const_mul _), ?_⟩
  rw [hlin, integral_add (i_pos.const_mul _) (i_neg.const_mul _),
    integral_const_mul, integral_const_mul, v_pos, v_neg]
  have hexp_eval : ∀ a : ℝ,
      (∫ u : ℝ, cx G u * ((probe 0 u : ℂ) * Complex.exp ((a : ℂ) * u))) =
        ((∫ u : ℝ, G u * Real.exp (a * u) : ℝ) : ℂ) := by
    intro a
    rw [← integral_complex_ofReal]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rcases lt_or_ge u 0 with hu | hu
    · rw [probe_of_neg hu, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul,
        show (a : ℂ) * u = ((a * u : ℝ) : ℂ) by push_cast; ring,
        ← Complex.ofReal_exp, Complex.ofReal_mul]
      rfl
    · simp [cx, hG0 u hu]
  have e_pos : (∫ u : ℝ, cx G u * ((probe 0 u : ℂ) * Complex.exp ((1 / 2 : ℂ) * u))) =
      ((∫ u : ℝ, G u * Real.exp (1 / 2 * u) : ℝ) : ℂ) := by
    simpa using hexp_eval (1 / 2)
  have e_neg : (∫ u : ℝ, cx G u * ((probe 0 u : ℂ) * Complex.exp ((-(1 / 2) : ℂ) * u))) =
      ((∫ u : ℝ, G u * Real.exp (-(1 / 2) * u) : ℝ) : ℂ) := by
    simpa using hexp_eval (-(1 / 2))
  rw [e_pos, e_neg]
  have hGi1 : Integrable fun u : ℝ => G u * Real.exp (1 / 2 * u) :=
    (hG.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hc.mul_right : HasCompactSupport (G * fun u => Real.exp (1 / 2 * u)))
  have hGi2 : Integrable fun u : ℝ => G u * Real.exp (-(1 / 2) * u) :=
    (hG.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport
      (hc.mul_right : HasCompactSupport (G * fun u => Real.exp (-(1 / 2) * u)))
  have hcosh : coshHalfMoment G =
      ((∫ u : ℝ, G u * Real.exp (1 / 2 * u)) + ∫ u : ℝ, G u * Real.exp (-(1 / 2) * u)) / 2 := by
    unfold coshHalfMoment
    rw [← integral_add hGi1 hGi2, ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [Real.cosh_eq]; ring_nf
  have hsinh : sinhHalfMoment G =
      ((∫ u : ℝ, G u * Real.exp (1 / 2 * u)) - ∫ u : ℝ, G u * Real.exp (-(1 / 2) * u)) / 2 := by
    unfold sinhHalfMoment
    rw [← integral_sub hGi1 hGi2, ← integral_div]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    dsimp only
    rw [Real.sinh_eq]; ring_nf
  rw [hcosh, hsinh]
  push_cast
  ring

/-- The Gamma term integrated against `laplaceTest (cx G)` on `Re p = 5` is integrable and yields
`2π` times `gammaMixedForm F G`. -/
private theorem integral_laplaceTest_stateGamma_five {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) (hG0 : ∀ u, 0 ≤ u → G u = 0) :
    (Integrable fun t : ℝ => laplaceTest (cx G) (5 + t * I) * stateGamma F (5 + t * I)) ∧
      (∫ t : ℝ, laplaceTest (cx G) (5 + t * I) * stateGamma F (5 + t * I)) =
        2 * Real.pi * ((gammaMixedForm F G : ℝ) : ℂ) := by
  have hψ : ContDiff ℝ ∞ (cx G) := Complex.ofRealCLM.contDiff.comp hG
  have hs : HasCompactSupport (cx G) := hc.comp_left Complex.ofReal_zero
  obtain ⟨D, hD0, hD⟩ := exists_laplaceTest_decay hψ hs 5 5
  have hA_int : Integrable fun r : ℝ => |EF.gammaBracket r| * ‖paperFT (cx F) r‖ ^ 2 :=
    hF.gamma.norm.congr (Eventually.of_forall fun r => by
      simp only [norm_mul, norm_pow, Real.norm_eq_abs, abs_norm]; ring)
  have hB_int : Integrable fun r : ℝ => |EF.gammaBracket r| * (1 + r ^ 2)⁻¹ := by
    have i1 := integrable_inv_one_add_sq.const_mul |EvenSector.gammaLogConst|
    have i2 := HTGeometry.integrable_log_mul_inv_sq_add_sq (a := 1) one_pos
    refine (i1.add i2).mono'
      ((Continuous.mul (continuous_abs.comp WeilHerglotz.continuous_gammaBracket)
        (Continuous.inv₀ (f := fun r : ℝ => 1 + r ^ 2) (by fun_prop)
          fun r => show (1 : ℝ) + r ^ 2 ≠ 0 by positivity)).aestronglyMeasurable)
      (Eventually.of_forall fun r => ?_)
    have hg := EvenSector.abs_gammaBracket_le_log r
    have hl : 0 ≤ Real.log (2 + |r|) := Real.log_nonneg (by linarith [abs_nonneg r])
    have hi : 0 < (1 + r ^ 2)⁻¹ := by positivity
    rw [Real.norm_of_nonneg (by positivity), one_pow]
    simp only [Pi.add_apply]
    nlinarith [le_abs_self EvenSector.gammaLogConst]
  set rMaj : ℝ → ℝ := fun r =>
    |EF.gammaBracket r| * ((‖paperFT (cx F) r‖ ^ 2 + (1 + r ^ 2)⁻¹) / 2)
  have hrMaj : Integrable rMaj :=
    ((hA_int.add hB_int).div_const 2).congr (Eventually.of_forall fun r => by
      simp only [rMaj, Pi.add_apply]; ring)
  set K : ℝ → ℝ → ℂ := fun t r =>
    laplaceTest (cx G) (5 + t * I) *
      ((paperFT (cx F) r / ((5 : ℂ) + t * I - I * r) +
        conj (paperFT (cx F) r) / ((5 : ℂ) + t * I + I * r)) / 2 * (EF.gammaBracket r : ℂ))
  have hK_prod : Integrable (Function.uncurry K) ((volume : Measure ℝ).prod volume) := by
    have htMaj : Integrable fun t : ℝ => Real.sqrt 2 * D * (1 + t ^ 2)⁻¹ :=
      integrable_inv_one_add_sq.const_mul _
    refine (htMaj.mul_prod hrMaj).mono' ?_ (Eventually.of_forall fun z => ?_)
    · have hcL : Continuous fun z : ℝ × ℝ => laplaceTest (cx G) (5 + z.1 * I) :=
        (differentiable_laplaceTest hψ.continuous hs).continuous.comp (by fun_prop)
      have hcF : Continuous fun z : ℝ × ℝ => paperFT (cx F) z.2 :=
        (continuous_paperFT_cx hF.integrable).comp continuous_snd
      have hc1 : Continuous fun z : ℝ × ℝ => paperFT (cx F) z.2 / ((5 : ℂ) + z.1 * I - I * z.2) :=
        hcF.div (by fun_prop) fun z h0 => by
          have := congrArg Complex.re h0; simp at this
      have hc2 : Continuous fun z : ℝ × ℝ =>
          conj (paperFT (cx F) z.2) / ((5 : ℂ) + z.1 * I + I * z.2) :=
        (Complex.continuous_conj.comp hcF).div (by fun_prop) fun z h0 => by
          have := congrArg Complex.re h0; simp at this
      have hcG : Continuous fun z : ℝ × ℝ => (EF.gammaBracket z.2 : ℂ) :=
        Complex.continuous_ofReal.comp (WeilHerglotz.continuous_gammaBracket.comp continuous_snd)
      exact (hcL.mul (((hc1.add hc2).div_const 2).mul hcG)).aestronglyMeasurable
    · dsimp only [Function.uncurry, K, rMaj]
      have hHt : ‖laplaceTest (cx G) (5 + z.1 * I)‖ ≤ D / (1 + z.1 ^ 2) ^ 2 := by
        simpa using hD 5 z.1 le_rfl le_rfl
      have hden_bound : ∀ s : ℝ, s = -1 ∨ s = 1 →
          1 / ((1 + z.1 ^ 2) ^ 2 * ‖(5 : ℂ) + z.1 * I + (s : ℂ) * I * z.2‖) ≤
            Real.sqrt 2 * (1 + z.1 ^ 2)⁻¹ * (Real.sqrt (1 + z.2 ^ 2))⁻¹ := by
        intro s hs
        have hnsq : 25 + (z.1 + s * z.2) ^ 2 =
            ‖(5 : ℂ) + z.1 * I + (s : ℂ) * I * z.2‖ ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp; ring
        have hs2 : s ^ 2 = 1 := by rcases hs with rfl | rfl <;> norm_num
        have hquad : 1 + z.2 ^ 2 ≤ 2 * (1 + z.1 ^ 2) * (25 + (z.1 + s * z.2) ^ 2) := by
          nlinarith [sq_nonneg (2 * z.1 + s * z.2), sq_nonneg z.1,
            sq_nonneg (z.1 * (z.1 + s * z.2)), hs2]
        have hsqrt_le : Real.sqrt (1 + z.2 ^ 2) ≤
            Real.sqrt 2 * (1 + z.1 ^ 2) * ‖(5 : ℂ) + z.1 * I + (s : ℂ) * I * z.2‖ := by
          have h1 := Real.sqrt_le_sqrt hquad
          rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity), hnsq,
            Real.sqrt_sq (norm_nonneg _)] at h1
          have ht_le : Real.sqrt (1 + z.1 ^ 2) ≤ 1 + z.1 ^ 2 := by
            have hq : 1 + z.1 ^ 2 ≤ (1 + z.1 ^ 2) ^ 2 := by nlinarith [sq_nonneg z.1]
            simpa [Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 1 + z.1 ^ 2)] using Real.sqrt_le_sqrt hq
          calc Real.sqrt (1 + z.2 ^ 2)
              ≤ Real.sqrt 2 * Real.sqrt (1 + z.1 ^ 2) *
                  ‖(5 : ℂ) + z.1 * I + (s : ℂ) * I * z.2‖ := by
                    simpa [mul_assoc] using h1
            _ ≤ Real.sqrt 2 * (1 + z.1 ^ 2) * ‖(5 : ℂ) + z.1 * I + (s : ℂ) * I * z.2‖ :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left ht_le (Real.sqrt_nonneg 2)) (norm_nonneg _)
        have hpos_n : 0 < ‖(5 : ℂ) + z.1 * I + (s : ℂ) * I * z.2‖ := by
          have hre : 5 ≤ ‖(5 : ℂ) + z.1 * I + (s : ℂ) * I * z.2‖ := by
            have h1 := Complex.abs_re_le_norm ((5 : ℂ) + z.1 * I + (s : ℂ) * I * z.2)
            have hr : ((5 : ℂ) + z.1 * I + (s : ℂ) * I * z.2).re = 5 := by simp
            rw [hr, abs_of_pos (by norm_num)] at h1; exact h1
          linarith
        have hpos_r : 0 < Real.sqrt (1 + z.2 ^ 2) := Real.sqrt_pos.mpr (by positivity)
        have hpos_t : 0 < 1 + z.1 ^ 2 := by positivity
        have hinv : ((1 + z.1 ^ 2) * ‖(5 : ℂ) + z.1 * I + (s : ℂ) * I * z.2‖)⁻¹ ≤
            Real.sqrt 2 * (Real.sqrt (1 + z.2 ^ 2))⁻¹ := by
          rw [← div_eq_mul_inv, inv_le_iff_one_le_mul₀ (mul_pos hpos_t hpos_n),
            div_mul_eq_mul_div, le_div_iff₀ hpos_r]
          linarith
        have hsplit_inv : 1 / ((1 + z.1 ^ 2) ^ 2 * ‖(5 : ℂ) + z.1 * I + (s : ℂ) * I * z.2‖) =
            (1 + z.1 ^ 2)⁻¹ *
              ((1 + z.1 ^ 2) * ‖(5 : ℂ) + z.1 * I + (s : ℂ) * I * z.2‖)⁻¹ := by
          field_simp
        rw [hsplit_inv]
        calc (1 + z.1 ^ 2)⁻¹ * ((1 + z.1 ^ 2) * ‖(5 : ℂ) + z.1 * I + (s : ℂ) * I * z.2‖)⁻¹
            ≤ (1 + z.1 ^ 2)⁻¹ * (Real.sqrt 2 * (Real.sqrt (1 + z.2 ^ 2))⁻¹) :=
                mul_le_mul_of_nonneg_left hinv (by positivity)
          _ = Real.sqrt 2 * (1 + z.1 ^ 2)⁻¹ * (Real.sqrt (1 + z.2 ^ 2))⁻¹ := by ring
      have ham : ‖paperFT (cx F) z.2‖ * (Real.sqrt (1 + z.2 ^ 2))⁻¹ ≤
          (‖paperFT (cx F) z.2‖ ^ 2 + (1 + z.2 ^ 2)⁻¹) / 2 := by
        have hsq : ((Real.sqrt (1 + z.2 ^ 2))⁻¹) ^ 2 = (1 + z.2 ^ 2)⁻¹ := by
          rw [inv_pow, Real.sq_sqrt (by positivity)]
        nlinarith [sq_nonneg (‖paperFT (cx F) z.2‖ - (Real.sqrt (1 + z.2 ^ 2))⁻¹), hsq]
      have b_minus := hden_bound (-1) (Or.inl rfl)
      have b_plus := hden_bound 1 (Or.inr rfl)
      have e_minus : (5 : ℂ) + z.1 * I + ((-1 : ℝ) : ℂ) * I * z.2 =
          (5 : ℂ) + z.1 * I - I * z.2 := by push_cast; ring
      have e_plus : (5 : ℂ) + z.1 * I + ((1 : ℝ) : ℂ) * I * z.2 =
          (5 : ℂ) + z.1 * I + I * z.2 := by push_cast; ring
      rw [e_minus] at b_minus
      rw [e_plus] at b_plus
      rw [norm_mul, norm_mul, norm_div, Complex.norm_two, Complex.norm_real, Real.norm_eq_abs]
      have htri := (norm_add_le (paperFT (cx F) z.2 / ((5 : ℂ) + z.1 * I - I * z.2))
        (conj (paperFT (cx F) z.2) / ((5 : ℂ) + z.1 * I + I * z.2))).trans_eq (by
          rw [norm_div, norm_div, Complex.norm_conj])
      have hterm1 : D / (1 + z.1 ^ 2) ^ 2 *
          (‖paperFT (cx F) z.2‖ / ‖(5 : ℂ) + z.1 * I - I * z.2‖) ≤
          Real.sqrt 2 * D * (1 + z.1 ^ 2)⁻¹ *
            ((‖paperFT (cx F) z.2‖ ^ 2 + (1 + z.2 ^ 2)⁻¹) / 2) := by
        have hdiv1 : D / (1 + z.1 ^ 2) ^ 2 *
            (‖paperFT (cx F) z.2‖ / ‖(5 : ℂ) + z.1 * I - I * z.2‖) =
            D * ‖paperFT (cx F) z.2‖ *
              (1 / ((1 + z.1 ^ 2) ^ 2 * ‖(5 : ℂ) + z.1 * I - I * z.2‖)) := by
          rw [div_mul_div_comm, mul_one_div, div_eq_mul_one_div]
        calc D / (1 + z.1 ^ 2) ^ 2 * (‖paperFT (cx F) z.2‖ / ‖(5 : ℂ) + z.1 * I - I * z.2‖)
            = D * ‖paperFT (cx F) z.2‖ *
                (1 / ((1 + z.1 ^ 2) ^ 2 * ‖(5 : ℂ) + z.1 * I - I * z.2‖)) := hdiv1
          _ ≤ D * ‖paperFT (cx F) z.2‖ *
                (Real.sqrt 2 * (1 + z.1 ^ 2)⁻¹ * (Real.sqrt (1 + z.2 ^ 2))⁻¹) :=
                mul_le_mul_of_nonneg_left b_minus (mul_nonneg hD0 (norm_nonneg _))
          _ = Real.sqrt 2 * D * (1 + z.1 ^ 2)⁻¹ *
                (‖paperFT (cx F) z.2‖ * (Real.sqrt (1 + z.2 ^ 2))⁻¹) := by ring
          _ ≤ Real.sqrt 2 * D * (1 + z.1 ^ 2)⁻¹ *
                ((‖paperFT (cx F) z.2‖ ^ 2 + (1 + z.2 ^ 2)⁻¹) / 2) :=
                mul_le_mul_of_nonneg_left ham (by positivity)
      have hterm2 : D / (1 + z.1 ^ 2) ^ 2 *
          (‖paperFT (cx F) z.2‖ / ‖(5 : ℂ) + z.1 * I + I * z.2‖) ≤
          Real.sqrt 2 * D * (1 + z.1 ^ 2)⁻¹ *
            ((‖paperFT (cx F) z.2‖ ^ 2 + (1 + z.2 ^ 2)⁻¹) / 2) := by
        have hdiv2 : D / (1 + z.1 ^ 2) ^ 2 *
            (‖paperFT (cx F) z.2‖ / ‖(5 : ℂ) + z.1 * I + I * z.2‖) =
            D * ‖paperFT (cx F) z.2‖ *
              (1 / ((1 + z.1 ^ 2) ^ 2 * ‖(5 : ℂ) + z.1 * I + I * z.2‖)) := by
          rw [div_mul_div_comm, mul_one_div, div_eq_mul_one_div]
        calc D / (1 + z.1 ^ 2) ^ 2 * (‖paperFT (cx F) z.2‖ / ‖(5 : ℂ) + z.1 * I + I * z.2‖)
            = D * ‖paperFT (cx F) z.2‖ *
                (1 / ((1 + z.1 ^ 2) ^ 2 * ‖(5 : ℂ) + z.1 * I + I * z.2‖)) := hdiv2
          _ ≤ D * ‖paperFT (cx F) z.2‖ *
                (Real.sqrt 2 * (1 + z.1 ^ 2)⁻¹ * (Real.sqrt (1 + z.2 ^ 2))⁻¹) :=
                mul_le_mul_of_nonneg_left b_plus (mul_nonneg hD0 (norm_nonneg _))
          _ = Real.sqrt 2 * D * (1 + z.1 ^ 2)⁻¹ *
                (‖paperFT (cx F) z.2‖ * (Real.sqrt (1 + z.2 ^ 2))⁻¹) := by ring
          _ ≤ Real.sqrt 2 * D * (1 + z.1 ^ 2)⁻¹ *
                ((‖paperFT (cx F) z.2‖ ^ 2 + (1 + z.2 ^ 2)⁻¹) / 2) :=
                mul_le_mul_of_nonneg_left ham (by positivity)
      have hprod1 : ‖laplaceTest (cx G) (5 + z.1 * I)‖ *
          (‖paperFT (cx F) z.2 / ((5 : ℂ) + z.1 * I - I * z.2) +
            conj (paperFT (cx F) z.2) / ((5 : ℂ) + z.1 * I + I * z.2)‖ / 2) ≤
          Real.sqrt 2 * D * (1 + z.1 ^ 2)⁻¹ *
            ((‖paperFT (cx F) z.2‖ ^ 2 + (1 + z.2 ^ 2)⁻¹) / 2) := by
        set N_pair : ℝ := ‖paperFT (cx F) z.2 / ((5 : ℂ) + z.1 * I - I * z.2) +
          conj (paperFT (cx F) z.2) / ((5 : ℂ) + z.1 * I + I * z.2)‖
        have hN_nn : 0 ≤ N_pair / 2 := div_nonneg (norm_nonneg _) (by norm_num)
        have hstep1 : ‖laplaceTest (cx G) (5 + z.1 * I)‖ * (N_pair / 2) ≤
            D / (1 + z.1 ^ 2) ^ 2 * (N_pair / 2) :=
          mul_le_mul_of_nonneg_right hHt hN_nn
        have hstep2 := mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right htri (by norm_num : (0 : ℝ) ≤ 2))
          (show 0 ≤ D / (1 + z.1 ^ 2) ^ 2 by positivity)
        linarith
      calc ‖laplaceTest (cx G) (5 + z.1 * I)‖ *
            (‖paperFT (cx F) z.2 / ((5 : ℂ) + z.1 * I - I * z.2) +
              conj (paperFT (cx F) z.2) / ((5 : ℂ) + z.1 * I + I * z.2)‖ / 2 *
              |EF.gammaBracket z.2|)
          = (‖laplaceTest (cx G) (5 + z.1 * I)‖ *
              (‖paperFT (cx F) z.2 / ((5 : ℂ) + z.1 * I - I * z.2) +
                conj (paperFT (cx F) z.2) / ((5 : ℂ) + z.1 * I + I * z.2)‖ / 2)) *
              |EF.gammaBracket z.2| := by ring
        _ ≤ (Real.sqrt 2 * D * (1 + z.1 ^ 2)⁻¹ *
              ((‖paperFT (cx F) z.2‖ ^ 2 + (1 + z.2 ^ 2)⁻¹) / 2)) *
              |EF.gammaBracket z.2| :=
            mul_le_mul_of_nonneg_right hprod1 (abs_nonneg _)
        _ = Real.sqrt 2 * D * (1 + z.1 ^ 2)⁻¹ *
              (|EF.gammaBracket z.2| * ((‖paperFT (cx F) z.2‖ ^ 2 + (1 + z.2 ^ 2)⁻¹) / 2)) := by
            ring
  have hstep_fn : (fun t : ℝ => laplaceTest (cx G) (5 + t * I) * stateGamma F (5 + t * I)) =
      fun t : ℝ => (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, K t r := by
    funext t
    unfold stateGamma
    rw [← mul_left_comm, ← integral_const_mul]
  refine ⟨?_, ?_⟩
  · rw [hstep_fn]
    exact hK_prod.integral_prod_left.const_mul _
  · rw [hstep_fn, integral_const_mul, integral_integral_swap hK_prod]
    have hr_eval : ∀ r : ℝ, (∫ t : ℝ, K t r) =
        2 * Real.pi * ((gammaFourierPair F G r * EF.gammaBracket r : ℝ) : ℂ) := by
      intro r
      have iminus := integral_laplaceTest_div_five hψ hs (c := -(I * r)) (by simp)
      have iplus := integral_laplaceTest_div_five hψ hs (c := I * r) (by simp)
      have hint_m : Integrable fun t : ℝ =>
          laplaceTest (cx G) (5 + t * I) * (1 / ((5 : ℂ) + t * I + -(I * r))) := by
        have hmaj : Integrable fun t : ℝ => D * (1 + t ^ 2)⁻¹ :=
          integrable_inv_one_add_sq.const_mul _
        refine hmaj.mono' ?_ (Eventually.of_forall fun t => ?_)
        · refine (((differentiable_laplaceTest hψ.continuous hs).continuous.comp
            (by fun_prop : Continuous fun t : ℝ => (5 : ℂ) + t * I)).mul
            (continuous_const.div (by fun_prop) fun t h0 => ?_)).aestronglyMeasurable
          have := congrArg Complex.re h0; simp at this
        · have hden : (1 : ℝ) ≤ ‖(5 : ℂ) + t * I + -(I * r)‖ := by
            have h1 := Complex.abs_re_le_norm ((5 : ℂ) + t * I + -(I * r))
            have hr : ((5 : ℂ) + t * I + -(I * r)).re = 5 := by simp
            rw [hr, abs_of_pos (by norm_num)] at h1; linarith
          have hHt : ‖laplaceTest (cx G) (5 + t * I)‖ ≤ D * (1 + t ^ 2)⁻¹ := by
            have h5 := hD 5 t le_rfl le_rfl
            norm_num at h5
            refine h5.trans ?_
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left
              (inv_anti₀ (by positivity) (by nlinarith [sq_nonneg t])) hD0
          rw [norm_mul, norm_div, norm_one, mul_one_div]
          calc ‖laplaceTest (cx G) (5 + t * I)‖ / ‖(5 : ℂ) + t * I + -(I * r)‖
              ≤ ‖laplaceTest (cx G) (5 + t * I)‖ / 1 :=
                div_le_div_of_nonneg_left (norm_nonneg _) zero_lt_one hden
            _ ≤ D * (1 + t ^ 2)⁻¹ := by simpa using hHt
      have hint_p : Integrable fun t : ℝ =>
          laplaceTest (cx G) (5 + t * I) * (1 / ((5 : ℂ) + t * I + I * r)) := by
        have hmaj : Integrable fun t : ℝ => D * (1 + t ^ 2)⁻¹ :=
          integrable_inv_one_add_sq.const_mul _
        refine hmaj.mono' ?_ (Eventually.of_forall fun t => ?_)
        · refine (((differentiable_laplaceTest hψ.continuous hs).continuous.comp
            (by fun_prop : Continuous fun t : ℝ => (5 : ℂ) + t * I)).mul
            (continuous_const.div (by fun_prop) fun t h0 => ?_)).aestronglyMeasurable
          have := congrArg Complex.re h0; simp at this
        · have hden : (1 : ℝ) ≤ ‖(5 : ℂ) + t * I + I * r‖ := by
            have h1 := Complex.abs_re_le_norm ((5 : ℂ) + t * I + I * r)
            have hr : ((5 : ℂ) + t * I + I * r).re = 5 := by simp
            rw [hr, abs_of_pos (by norm_num)] at h1; linarith
          have hHt : ‖laplaceTest (cx G) (5 + t * I)‖ ≤ D * (1 + t ^ 2)⁻¹ := by
            have h5 := hD 5 t le_rfl le_rfl
            norm_num at h5
            refine h5.trans ?_
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left
              (inv_anti₀ (by positivity) (by nlinarith [sq_nonneg t])) hD0
          rw [norm_mul, norm_div, norm_one, mul_one_div]
          calc ‖laplaceTest (cx G) (5 + t * I)‖ / ‖(5 : ℂ) + t * I + I * r‖
              ≤ ‖laplaceTest (cx G) (5 + t * I)‖ / 1 :=
                div_le_div_of_nonneg_left (norm_nonneg _) zero_lt_one hden
            _ ≤ D * (1 + t ^ 2)⁻¹ := by simpa using hHt
      have hK_eq : (fun t : ℝ => K t r) = fun t : ℝ =>
          (paperFT (cx F) r * (EF.gammaBracket r : ℂ) / 2) *
            (laplaceTest (cx G) (5 + t * I) * (1 / ((5 : ℂ) + t * I + -(I * r)))) +
          (conj (paperFT (cx F) r) * (EF.gammaBracket r : ℂ) / 2) *
            (laplaceTest (cx G) (5 + t * I) * (1 / ((5 : ℂ) + t * I + I * r))) := by
        funext t; dsimp only [K]; rw [sub_eq_add_neg]; ring
      rw [hK_eq, integral_add (hint_m.const_mul _) (hint_p.const_mul _),
        integral_const_mul, integral_const_mul, iminus, iplus]
      have hp_pos : (∫ u : ℝ, cx G u * ((probe 0 u : ℂ) * Complex.exp (I * (r : ℂ) * u))) =
          paperFT (cx G) r := by
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        dsimp only
        rcases lt_or_ge u 0 with hu | hu
        · rw [probe_of_neg hu, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul]
        · simp [cx, hG0 u hu]
      have hp_neg : (∫ u : ℝ, cx G u * ((probe 0 u : ℂ) * Complex.exp (-(I * (r : ℂ)) * u))) =
          conj (paperFT (cx G) r) := by
        have hconj : conj (paperFT (cx G) r) =
            ∫ u : ℝ, conj (cx G u * Complex.exp (I * (r : ℂ) * u)) :=
          (integral_conj (f := fun u : ℝ => cx G u * Complex.exp (I * (r : ℂ) * u))).symm
        rw [hconj]
        refine integral_congr_ae (Eventually.of_forall fun u => ?_)
        dsimp only
        rcases lt_or_ge u 0 with hu | hu
        · rw [probe_of_neg hu, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul, map_mul,
            ← Complex.exp_conj]
          simp [cx, Complex.conj_ofReal]
        · simp [cx, hG0 u hu]
      rw [hp_neg, hp_pos]
      unfold gammaFourierPair
      have hre_pair : (paperFT (cx F) r * conj (paperFT (cx G) r) +
          conj (paperFT (cx F) r) * paperFT (cx G) r) / 2 =
          (((paperFT (cx F) r).re * (paperFT (cx G) r).re +
            (paperFT (cx F) r).im * (paperFT (cx G) r).im : ℝ) : ℂ) := by
        apply Complex.ext
        · simp
        · simp; ring
      calc (paperFT (cx F) r * (EF.gammaBracket r : ℂ) / 2) * (2 * ↑Real.pi * conj (paperFT (cx G) r)) +
            (conj (paperFT (cx F) r) * (EF.gammaBracket r : ℂ) / 2) * (2 * ↑Real.pi * paperFT (cx G) r)
          = 2 * ↑Real.pi * (((paperFT (cx F) r * conj (paperFT (cx G) r) +
              conj (paperFT (cx F) r) * paperFT (cx G) r) / 2) * (EF.gammaBracket r : ℂ)) := by ring
        _ = 2 * ↑Real.pi *
              ((((paperFT (cx F) r).re * (paperFT (cx G) r).re +
                (paperFT (cx F) r).im * (paperFT (cx G) r).im) * EF.gammaBracket r : ℝ) : ℂ) := by
              rw [hre_pair, Complex.ofReal_mul]
    simp_rw [hr_eval]
    rw [integral_const_mul, integral_complex_ofReal]
    unfold gammaMixedForm
    have h2pi : (2 * Real.pi : ℂ) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    push_cast
    field_simp

/-- The forward prime series integrated against `laplaceTest (cx G)` on `Re p = 5` is integrable
and yields `-2π ∑_n (Λ(n)/√n) ∫ F(t) G(t - log n) dt`. -/
private theorem integral_laplaceTest_forwardPrime_five {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) (_hG0 : ∀ u, 0 ≤ u → G u = 0) :
    (Integrable fun t : ℝ => laplaceTest (cx G) (5 + t * I) *
        (negativeHalfLineLaplace (cx F) (5 + t * I) *
          (deriv riemannZeta (1 / 2 + ((5 : ℂ) + t * I)) /
            riemannZeta (1 / 2 + ((5 : ℂ) + t * I))))) ∧
      (∫ t : ℝ, laplaceTest (cx G) (5 + t * I) *
        (negativeHalfLineLaplace (cx F) (5 + t * I) *
          (deriv riemannZeta (1 / 2 + ((5 : ℂ) + t * I)) /
            riemannZeta (1 / 2 + ((5 : ℂ) + t * I))))) =
      -(2 * Real.pi * ((∑' n : ℕ, vonMangoldtAtom n * ∫ u, F u * G (u - Real.log n) : ℝ) : ℂ)) := by
  have hψ : ContDiff ℝ ∞ (cx G) := Complex.ofRealCLM.contDiff.comp hG
  have hs : HasCompactSupport (cx G) := hc.comp_left Complex.ofReal_zero
  obtain ⟨D, hD0, hD⟩ := exists_laplaceTest_decay hψ hs 5 5
  have hL_zeta : ∀ t : ℝ, deriv riemannZeta (1 / 2 + ((5 : ℂ) + t * I)) /
      riemannZeta (1 / 2 + ((5 : ℂ) + t * I)) =
      -∑' n : ℕ, (vonMangoldtAtom n : ℂ) *
        Complex.exp (-(((5 : ℂ) + t * I) * Real.log n)) := by
    intro t
    have hre : 1 < (1 / 2 + ((5 : ℂ) + t * I)).re := by simp; norm_num
    have hL := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hre
    have hdiv : deriv riemannZeta (1 / 2 + ((5 : ℂ) + t * I)) /
        riemannZeta (1 / 2 + ((5 : ℂ) + t * I)) =
        -LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 / 2 + ((5 : ℂ) + t * I)) := by
      rw [hL, neg_div, neg_neg]
    rw [hdiv, neg_inj]
    unfold LSeries LSeries.term
    refine tsum_congr fun n => ?_
    by_cases hn : n = 0
    · subst hn; simp [vonMangoldtAtom]
    · rw [if_neg hn]
      have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      by_cases hn2 : 2 ≤ n
      · unfold vonMangoldtAtom
        rw [if_pos hn2, Complex.cpow_def_of_ne_zero (Nat.cast_ne_zero.mpr hn),
          ← Complex.natCast_log, Real.sqrt_eq_rpow,
          Real.rpow_def_of_pos hn_pos, Complex.ofReal_div, Complex.ofReal_exp,
          div_mul_eq_mul_div,
          div_eq_div_iff (Complex.exp_ne_zero _) (Complex.exp_ne_zero _),
          mul_assoc, ← Complex.exp_add]
        dsimp only
        congr 2
        push_cast; ring
      · have hn1 : n = 1 := by omega
        subst hn1
        simp [vonMangoldtAtom]
  have hF_norm : ∀ t : ℝ, ‖negativeHalfLineLaplace (cx F) (5 + t * I)‖ ≤ ∫ u, |F u| := by
    intro t
    refine (norm_integral_le_integral_norm _).trans
      (integral_mono_of_nonneg (Eventually.of_forall fun _ => norm_nonneg _) hF.integrable.abs
        (Eventually.of_forall fun u => ?_))
    dsimp only
    rcases lt_or_ge u 0 with hu | hu
    · rw [norm_mul, norm_cexp_mul_ofReal, show ((5 : ℂ) + t * I).re = 5 by simp]
      have he : Real.exp (5 * u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
      have hn : ‖cx F u‖ = |F u| := by simp [cx]
      rw [hn]; nlinarith [abs_nonneg (F u)]
    · simp [cx, hF.support u hu]
  set fn : ℕ → ℝ → ℂ := fun n t =>
    laplaceTest (cx G) (5 + t * I) *
      (negativeHalfLineLaplace (cx F) (5 + t * I) *
        ((vonMangoldtAtom n : ℂ) * Complex.exp (-(((5 : ℂ) + t * I) * Real.log n))))
  have hexp_norm : ∀ (n : ℕ) (t : ℝ),
      ‖Complex.exp (-(((5 : ℂ) + t * I) * Real.log n))‖ = Real.exp (-(5 * Real.log n)) := by
    intro n t
    rw [Complex.norm_exp]
    congr 1
    simp only [Complex.neg_re, Complex.mul_re, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
    norm_num
  have hfn_int : ∀ n : ℕ, Integrable (fn n) := by
    intro n
    have hmaj : Integrable fun t : ℝ =>
        (D * (∫ u, |F u|) * (vonMangoldtAtom n * Real.exp (-(5 * Real.log n)))) *
          (1 + t ^ 2)⁻¹ :=
      integrable_inv_one_add_sq.const_mul _
    refine hmaj.mono' ?_ (Eventually.of_forall fun t => ?_)
    · have hLap : DifferentiableOn ℂ (negativeHalfLineLaplace (cx F)) {p : ℂ | -(8 / 2) < p.re} :=
        differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential
      have hcL : Continuous fun t : ℝ => negativeHalfLineLaplace (cx F) (5 + t * I) :=
        (hLap.continuousOn.comp_continuous (by fun_prop) fun t => by simp; norm_num)
      exact (((differentiable_laplaceTest hψ.continuous hs).continuous.comp (by fun_prop)).mul
        (hcL.mul (continuous_const.mul (by fun_prop)))).aestronglyMeasurable
    · dsimp only [fn]
      have hatom : 0 ≤ vonMangoldtAtom n := by
        unfold vonMangoldtAtom; split_ifs
        · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
        · exact le_rfl
      have hHt : ‖laplaceTest (cx G) (5 + t * I)‖ ≤ D * (1 + t ^ 2)⁻¹ := by
        have h5 := hD 5 t le_rfl le_rfl
        norm_num at h5
        refine h5.trans ?_
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left
          (inv_anti₀ (by positivity) (by nlinarith [sq_nonneg t])) hD0
      rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hatom, hexp_norm n t]
      calc ‖laplaceTest (cx G) (5 + t * I)‖ *
            (‖negativeHalfLineLaplace (cx F) (5 + t * I)‖ *
              (vonMangoldtAtom n * Real.exp (-(5 * Real.log n))))
          ≤ (D * (1 + t ^ 2)⁻¹) *
              ((∫ u, |F u|) * (vonMangoldtAtom n * Real.exp (-(5 * Real.log n)))) :=
            mul_le_mul hHt (mul_le_mul_of_nonneg_right (hF_norm t) (by positivity))
              (by positivity) (by positivity)
        _ = (D * (∫ u, |F u|) * (vonMangoldtAtom n * Real.exp (-(5 * Real.log n)))) *
              (1 + t ^ 2)⁻¹ := by ring
  have hfn_sum : Summable fun n : ℕ => ∫ t : ℝ, ‖fn n t‖ := by
    have hbase : Summable fun n : ℕ =>
        (D * (∫ u, |F u|) * ∫ t : ℝ, (1 + t ^ 2)⁻¹) *
          (vonMangoldtAtom n * Real.exp (-(5 * Real.log n))) := by
      refine ((summable_vonMangoldt_div_rpow (σ := 1 / 2 + 5) (by norm_num)).congr fun n => ?_).mul_left _
      rw [← vonMangoldtAtom_mul_exp_eq]
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_) hbase
    have hatom : 0 ≤ vonMangoldtAtom n := by
      unfold vonMangoldtAtom; split_ifs
      · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
      · exact le_rfl
    calc (∫ t : ℝ, ‖fn n t‖)
        ≤ ∫ t : ℝ, (D * (∫ u, |F u|) * (vonMangoldtAtom n * Real.exp (-(5 * Real.log n)))) *
            (1 + t ^ 2)⁻¹ := by
          refine integral_mono (hfn_int n).norm (integrable_inv_one_add_sq.const_mul _) fun t => ?_
          dsimp only [fn]
          have hHt : ‖laplaceTest (cx G) (5 + t * I)‖ ≤ D * (1 + t ^ 2)⁻¹ := by
            have h5 := hD 5 t le_rfl le_rfl
            norm_num at h5
            refine h5.trans ?_
            rw [div_eq_mul_inv]
            exact mul_le_mul_of_nonneg_left
              (inv_anti₀ (by positivity) (by nlinarith [sq_nonneg t])) hD0
          rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hatom, hexp_norm n t]
          calc ‖laplaceTest (cx G) (5 + t * I)‖ *
                (‖negativeHalfLineLaplace (cx F) (5 + t * I)‖ *
                  (vonMangoldtAtom n * Real.exp (-(5 * Real.log n))))
              ≤ (D * (1 + t ^ 2)⁻¹) *
                  ((∫ u, |F u|) * (vonMangoldtAtom n * Real.exp (-(5 * Real.log n)))) :=
                mul_le_mul hHt (mul_le_mul_of_nonneg_right (hF_norm t) (by positivity))
                  (by positivity) (by positivity)
            _ = (D * (∫ u, |F u|) * (vonMangoldtAtom n * Real.exp (-(5 * Real.log n)))) *
                  (1 + t ^ 2)⁻¹ := by ring
      _ = (D * (∫ u, |F u|) * ∫ t : ℝ, (1 + t ^ 2)⁻¹) *
            (vonMangoldtAtom n * Real.exp (-(5 * Real.log n))) := by
          rw [integral_const_mul]; ring
  have hswap := (hasSum_integral_of_summable_integral_norm hfn_int hfn_sum).tsum_eq
  have hfn_eval : ∀ n : ℕ, (∫ t : ℝ, fn n t) =
      2 * Real.pi * ((vonMangoldtAtom n * ∫ u, F u * G (u - Real.log n) : ℝ) : ℂ) := by
    intro n
    set φn : ℝ → ℂ := fun v => cx F (v + Real.log n)
    have hφm : AEStronglyMeasurable φn volume :=
      (Complex.measurable_ofReal.comp (hF.meas.comp (measurable_id.add_const _))).aestronglyMeasurable
    have hφi : Integrable (fun v : ℝ => Real.exp (5 * v) * ‖φn v‖) volume := by
      have hshift : Integrable (fun u : ℝ => Real.exp (5 * (u - Real.log n)) * ‖cx F u‖) volume := by
        refine (hF.integrable.abs.const_mul (Real.exp (-(5 * Real.log n)))).mono'
          (((by fun_prop : Measurable fun u : ℝ => Real.exp (5 * (u - Real.log n)))).mul
            (Complex.measurable_ofReal.comp hF.meas).norm).aestronglyMeasurable
          (Eventually.of_forall fun u => ?_)
        rw [Real.norm_of_nonneg (by positivity)]
        rcases lt_or_ge u 0 with hu | hu
        · rw [show 5 * (u - Real.log n) = 5 * u + -(5 * Real.log n) by ring, Real.exp_add]
          have he : Real.exp (5 * u) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
          have hn : ‖cx F u‖ = |F u| := by simp [cx]
          rw [hn]
          calc Real.exp (5 * u) * Real.exp (-(5 * Real.log n)) * |F u|
              ≤ 1 * Real.exp (-(5 * Real.log n)) * |F u| :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right he (Real.exp_pos _).le) (abs_nonneg _)
            _ = Real.exp (-(5 * Real.log n)) * |F u| := by ring
        · simp [cx, hF.support u hu]
      simpa [φn, add_sub_cancel_right] using hshift.comp_add_right (Real.log n)
    have hlap_n : ∀ t : ℝ, negativeHalfLineLaplace (cx F) (5 + t * I) *
        Complex.exp (-(((5 : ℂ) + t * I) * Real.log n)) =
        ∫ v : ℝ, Complex.exp (((5 : ℂ) + t * I) * v) * φn v := by
      intro t
      unfold negativeHalfLineLaplace
      rw [← integral_mul_const, ← integral_add_right_eq_self
        (fun u : ℝ => Complex.exp (((5 : ℂ) + t * I) * u) * cx F u *
          Complex.exp (-(((5 : ℂ) + t * I) * Real.log n))) (Real.log n)]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      dsimp only [φn]
      have hexp : ((5 : ℂ) + t * I) * ↑(v + Real.log n) + -(((5 : ℂ) + t * I) * Real.log n) =
          ((5 : ℂ) + t * I) * v := by push_cast; ring
      calc Complex.exp (((5 : ℂ) + t * I) * ↑(v + Real.log n)) * cx F (v + Real.log n) *
            Complex.exp (-(((5 : ℂ) + t * I) * Real.log n))
          = (Complex.exp (((5 : ℂ) + t * I) * ↑(v + Real.log n)) *
              Complex.exp (-(((5 : ℂ) + t * I) * Real.log n))) * cx F (v + Real.log n) := by ring
        _ = Complex.exp (((5 : ℂ) + t * I) * v) * cx F (v + Real.log n) := by
            rw [← Complex.exp_add, hexp]
    have hfn_eq : fn n = fun t : ℝ => (vonMangoldtAtom n : ℂ) *
        (laplaceTest (cx G) (((5 : ℝ) : ℂ) + t * I) *
          ∫ v : ℝ, Complex.exp ((((5 : ℝ) : ℂ) + t * I) * v) * φn v) := by
      funext t; dsimp only [fn]
      have h5 : (((5 : ℝ) : ℂ) + t * I) = (5 : ℂ) + t * I := by norm_num
      rw [h5, ← mul_assoc (vonMangoldtAtom n : ℂ), mul_left_comm (negativeHalfLineLaplace _ _), hlap_n t]
      ring
    rw [hfn_eq, integral_const_mul, integral_laplaceTest_mul_laplace hψ hs 5 hφm hφi]
    have htrans : (∫ v : ℝ, cx G v * φn v) = ((∫ u : ℝ, F u * G (u - Real.log n) : ℝ) : ℂ) := by
      rw [← integral_add_right_eq_self (fun u : ℝ => F u * G (u - Real.log n)) (Real.log n),
        ← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      dsimp only [φn]
      simp [cx, add_sub_cancel_right, mul_comm]
    rw [htrans]
    push_cast; ring
  have hlhs : (fun t : ℝ => laplaceTest (cx G) (5 + t * I) *
      (negativeHalfLineLaplace (cx F) (5 + t * I) *
        (deriv riemannZeta (1 / 2 + ((5 : ℂ) + t * I)) /
          riemannZeta (1 / 2 + ((5 : ℂ) + t * I))))) =
      fun t : ℝ => -(∑' n : ℕ, fn n t) := by
    funext t
    rw [hL_zeta t, mul_neg, mul_neg, neg_inj, ← tsum_mul_left, ← tsum_mul_left]
  refine ⟨?_, ?_⟩
  · have hsum_atom : Summable fun n : ℕ => vonMangoldtAtom n * Real.exp (-(5 * Real.log n)) := by
      refine (summable_vonMangoldt_div_rpow (σ := 1 / 2 + 5) (by norm_num)).congr fun n => ?_
      rw [← vonMangoldtAtom_mul_exp_eq]
    set S₅ : ℝ := ∑' n : ℕ, vonMangoldtAtom n * Real.exp (-(5 * Real.log n))
    refine (integrable_inv_one_add_sq.const_mul (D * (∫ u, |F u|) * S₅)).mono' ?_
      (Eventually.of_forall fun t => ?_)
    · have hLap : DifferentiableOn ℂ (negativeHalfLineLaplace (cx F)) {p : ℂ | -(8 / 2) < p.re} :=
        differentiableOn_laplace_of_sq hF.meas hF.support hF.exponential
      have hcL : Continuous fun t : ℝ => negativeHalfLineLaplace (cx F) (5 + t * I) :=
        hLap.continuousOn.comp_continuous (by fun_prop) fun t => by simp; norm_num
      have hcZ : Continuous fun t : ℝ =>
          deriv riemannZeta (1 / 2 + ((5 : ℂ) + t * I)) /
            riemannZeta (1 / 2 + ((5 : ℂ) + t * I)) := by
        refine continuous_iff_continuousAt.mpr fun t => ?_
        have h1 : (1 : ℂ) / 2 + ((5 : ℂ) + t * I) ≠ 1 := by
          intro h; have := congrArg Complex.re h; simp at this; norm_num at this
        have hζ : riemannZeta (1 / 2 + ((5 : ℂ) + t * I)) ≠ 0 :=
          riemannZeta_ne_zero_of_one_le_re (by simp; norm_num)
        have hdZ : DifferentiableAt ℂ
            (fun p : ℂ => deriv riemannZeta (1 / 2 + p) / riemannZeta (1 / 2 + p))
            ((5 : ℂ) + t * I) :=
          (differentiableAt_deriv_zeta_shift h1).div (differentiableAt_zeta_shift h1) hζ
        exact ContinuousAt.comp (g := fun p : ℂ => deriv riemannZeta (1 / 2 + p) / riemannZeta (1 / 2 + p))
          (f := fun t : ℝ => (5 : ℂ) + t * I) hdZ.continuousAt
          (by fun_prop : Continuous fun t : ℝ => (5 : ℂ) + t * I).continuousAt
      exact (((differentiable_laplaceTest hψ.continuous hs).continuous.comp (by fun_prop)).mul
        (hcL.mul hcZ)).aestronglyMeasurable
    · rw [congrFun hlhs t, norm_neg]
      have hHt : ‖laplaceTest (cx G) (5 + t * I)‖ ≤ D * (1 + t ^ 2)⁻¹ := by
        have h5 := hD 5 t le_rfl le_rfl
        norm_num at h5
        refine h5.trans ?_
        rw [div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_left
          (inv_anti₀ (by positivity) (by nlinarith [sq_nonneg t])) hD0
      have hfn_t : Summable fun n : ℕ => ‖fn n t‖ := by
        refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
          (hsum_atom.mul_left (D * (1 + t ^ 2)⁻¹ * ∫ u, |F u|))
        dsimp only [fn]
        have hatom : 0 ≤ vonMangoldtAtom n := by
          unfold vonMangoldtAtom; split_ifs
          · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
          · exact le_rfl
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hatom, hexp_norm n t]
        calc ‖laplaceTest (cx G) (5 + t * I)‖ *
              (‖negativeHalfLineLaplace (cx F) (5 + t * I)‖ *
                (vonMangoldtAtom n * Real.exp (-(5 * Real.log n))))
            ≤ (D * (1 + t ^ 2)⁻¹) *
                ((∫ u, |F u|) * (vonMangoldtAtom n * Real.exp (-(5 * Real.log n)))) :=
              mul_le_mul hHt (mul_le_mul_of_nonneg_right (hF_norm t) (by positivity))
                (by positivity) (by positivity)
          _ = D * (1 + t ^ 2)⁻¹ * (∫ u, |F u|) *
                (vonMangoldtAtom n * Real.exp (-(5 * Real.log n))) := by ring
      calc ‖∑' n : ℕ, fn n t‖
          ≤ ∑' n : ℕ, ‖fn n t‖ := norm_tsum_le_tsum_norm hfn_t
        _ ≤ ∑' n : ℕ, (D * (1 + t ^ 2)⁻¹ * ∫ u, |F u|) *
              (vonMangoldtAtom n * Real.exp (-(5 * Real.log n))) := by
            refine hfn_t.tsum_le_tsum (fun n => ?_) (hsum_atom.mul_left _)
            dsimp only [fn]
            have hatom : 0 ≤ vonMangoldtAtom n := by
              unfold vonMangoldtAtom; split_ifs
              · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
              · exact le_rfl
            rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hatom, hexp_norm n t]
            calc ‖laplaceTest (cx G) (5 + t * I)‖ *
                  (‖negativeHalfLineLaplace (cx F) (5 + t * I)‖ *
                    (vonMangoldtAtom n * Real.exp (-(5 * Real.log n))))
                ≤ (D * (1 + t ^ 2)⁻¹) *
                    ((∫ u, |F u|) * (vonMangoldtAtom n * Real.exp (-(5 * Real.log n)))) :=
                  mul_le_mul hHt (mul_le_mul_of_nonneg_right (hF_norm t) (by positivity))
                    (by positivity) (by positivity)
              _ = (D * (1 + t ^ 2)⁻¹ * ∫ u, |F u|) *
                    (vonMangoldtAtom n * Real.exp (-(5 * Real.log n))) := by ring
        _ = (D * (∫ u, |F u|) * S₅) * (1 + t ^ 2)⁻¹ := by
            rw [tsum_mul_left]; dsimp [S₅]; ring
  · rw [hlhs, integral_neg, ← hswap]
    simp_rw [hfn_eval]
    rw [tsum_mul_left, Complex.ofReal_tsum]

/-- The backward prime tail `stateTail F (5 + it)` integrated against `laplaceTest (cx G)` is
integrable and yields `2π ∑_n (Λ(n)/√n) ∫ F(t) G(t + log n) dt`. -/
private theorem integral_laplaceTest_stateTail_five {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hc : HasCompactSupport G) (hG0 : ∀ u, 0 ≤ u → G u = 0) :
    (Integrable fun t : ℝ => laplaceTest (cx G) (5 + t * I) * stateTail F (5 + t * I)) ∧
      (∫ t : ℝ, laplaceTest (cx G) (5 + t * I) * stateTail F (5 + t * I)) =
        2 * Real.pi * ((∑' n : ℕ, vonMangoldtAtom n * ∫ u, F u * G (u + Real.log n) : ℝ) : ℂ) := by
  have hψ : ContDiff ℝ ∞ (cx G) := Complex.ofRealCLM.contDiff.comp hG
  have hs : HasCompactSupport (cx G) := hc.comp_left Complex.ofReal_zero
  obtain ⟨D, hD0, hD⟩ := exists_laplaceTest_decay hψ hs 5 5
  set gn : ℕ → ℝ → ℂ := fun n t =>
    laplaceTest (cx G) (5 + t * I) *
      ((vonMangoldtAtom n : ℂ) * (Complex.exp (((5 : ℂ) + t * I) * Real.log n) *
        ∫ u in Iio (-Real.log n), (F u : ℂ) * Complex.exp (((5 : ℂ) + t * I) * u)))
  set M₈ : ℝ := ((∫ u, F u ^ 2 * Real.exp (-(8 * u))) + 1 / 8) / 2
  have hM₈ : 0 ≤ M₈ := by
    dsimp only [M₈]
    have h0 : 0 ≤ ∫ u, F u ^ 2 * Real.exp (-(8 * u)) :=
      integral_nonneg fun _ => mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
    linarith
  have hgn_bound : ∀ n : ℕ, ∀ t : ℝ,
      ‖gn n t‖ ≤ (D * M₈ * (vonMangoldtAtom n * Real.exp (-(4 * Real.log n)))) * (1 + t ^ 2)⁻¹ := by
    intro n t
    dsimp only [gn]
    have hHt : ‖laplaceTest (cx G) (5 + t * I)‖ ≤ D * (1 + t ^ 2)⁻¹ := by
      refine (hD 5 t le_rfl le_rfl).trans ?_
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left
        (inv_anti₀ (by positivity) (by nlinarith [sq_nonneg t])) hD0
    have htail := norm_stateTail_term_le hF (p := (5 : ℂ) + t * I) (by simp) n
    rw [norm_mul]
    calc ‖laplaceTest (cx G) (5 + t * I)‖ *
          ‖(vonMangoldtAtom n : ℂ) * (Complex.exp (((5 : ℂ) + t * I) * Real.log n) *
            ∫ u in Iio (-Real.log n), (F u : ℂ) * Complex.exp (((5 : ℂ) + t * I) * u))‖
        ≤ (D * (1 + t ^ 2)⁻¹) * (vonMangoldtAtom n * (Real.exp (-(4 * Real.log n)) * M₈)) :=
          mul_le_mul hHt htail (norm_nonneg _) (by positivity)
      _ = (D * M₈ * (vonMangoldtAtom n * Real.exp (-(4 * Real.log n)))) * (1 + t ^ 2)⁻¹ := by ring
  have hgn_int : ∀ n : ℕ, Integrable (gn n) := by
    intro n
    refine (integrable_inv_one_add_sq.const_mul _).mono' ?_ (Eventually.of_forall (hgn_bound n))
    have hcT : DifferentiableOn ℂ
        (fun p : ℂ => (vonMangoldtAtom n : ℂ) * (Complex.exp (p * Real.log n) *
          ∫ u in Iio (-Real.log n), (F u : ℂ) * Complex.exp (p * u))) {p : ℂ | 0 < p.re} := by
      refine DifferentiableOn.const_mul (DifferentiableOn.mul
        (by fun_prop : Differentiable ℂ fun p : ℂ => Complex.exp (p * Real.log n)).differentiableOn ?_) _
      refine differentiableOn_integral_of_locally_bounded (ν := volume.restrict (Iio (-Real.log n)))
        (F := fun (u : ℝ) (p : ℂ) => (F u : ℂ) * Complex.exp (p * u))
        (isOpen_lt continuous_const Complex.continuous_re)
        (fun u => (by fun_prop : Differentiable ℂ fun p : ℂ => (F u : ℂ) * Complex.exp (p * u)).differentiableOn)
        (fun p _ => ((Complex.measurable_ofReal.comp hF.meas).mul
          (by fun_prop : Continuous fun u : ℝ => Complex.exp (p * u)).measurable).aestronglyMeasurable) ?_
      intro z₀ hz₀
      have hz₀' : 0 < z₀.re := hz₀
      refine ⟨z₀.re / 2, by linarith, fun z hz => ?_, fun u => |F u|,
        hF.integrable.abs.integrableOn, fun u z hz => ?_⟩
      · rw [mem_closedBall, dist_eq_norm] at hz
        have := (abs_le.mp ((Complex.abs_re_le_norm (z - z₀)).trans hz)).1
        show 0 < z.re; simp at this; linarith
      · rw [mem_closedBall, dist_eq_norm] at hz
        have hre := (abs_le.mp ((Complex.abs_re_le_norm (z - z₀)).trans hz)).1
        simp only [Complex.sub_re] at hre
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, norm_cexp_mul_ofReal]
        rcases lt_or_ge u 0 with hu | hu
        · have he : Real.exp (z.re * u) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
          nlinarith [abs_nonneg (F u)]
        · simp [hF.support u hu]
    exact (((differentiable_laplaceTest hψ.continuous hs).continuous.comp (by fun_prop)).mul
      (hcT.continuousOn.comp_continuous (by fun_prop) fun t => by simp)).aestronglyMeasurable
  have hsum4 : Summable fun n : ℕ => vonMangoldtAtom n * Real.exp (-(4 * Real.log n)) := by
    refine (summable_vonMangoldt_div_rpow (σ := 1 / 2 + 4) (by norm_num)).congr fun n => ?_
    rw [← vonMangoldtAtom_mul_exp_eq]
  have hgn_sum : Summable fun n : ℕ => ∫ t : ℝ, ‖gn n t‖ := by
    have hbase : Summable fun n : ℕ =>
        (D * M₈ * ∫ t : ℝ, (1 + t ^ 2)⁻¹) *
          (vonMangoldtAtom n * Real.exp (-(4 * Real.log n))) := hsum4.mul_left _
    refine Summable.of_nonneg_of_le (fun n => integral_nonneg fun _ => norm_nonneg _) (fun n => ?_) hbase
    calc (∫ t : ℝ, ‖gn n t‖)
        ≤ ∫ t : ℝ, (D * M₈ * (vonMangoldtAtom n * Real.exp (-(4 * Real.log n)))) * (1 + t ^ 2)⁻¹ :=
          integral_mono (hgn_int n).norm (integrable_inv_one_add_sq.const_mul _) (hgn_bound n)
      _ = (D * M₈ * ∫ t : ℝ, (1 + t ^ 2)⁻¹) *
            (vonMangoldtAtom n * Real.exp (-(4 * Real.log n))) := by
          rw [integral_const_mul]; ring
  have hswap := (hasSum_integral_of_summable_integral_norm hgn_int hgn_sum).tsum_eq
  have hgn_eval : ∀ n : ℕ, (∫ t : ℝ, gn n t) =
      2 * Real.pi * ((vonMangoldtAtom n * ∫ u, F u * G (u + Real.log n) : ℝ) : ℂ) := by
    intro n
    set ψn : ℝ → ℂ := (Iio (0 : ℝ)).indicator (fun v => cx F (v - Real.log n))
    have hψm : AEStronglyMeasurable ψn volume :=
      ((Complex.measurable_ofReal.comp
        (hF.meas.comp (measurable_id.sub_const _))).indicator measurableSet_Iio).aestronglyMeasurable
    have hψi : Integrable (fun v : ℝ => Real.exp (5 * v) * ‖ψn v‖) volume := by
      have hdom : Integrable (fun v : ℝ => |F (v - Real.log n)|) volume :=
        hF.integrable.abs.comp_sub_right (Real.log n)
      refine hdom.mono'
        (((by fun_prop : Measurable fun v : ℝ => Real.exp (5 * v))).mul
          ((Complex.measurable_ofReal.comp (hF.meas.comp (measurable_id.sub_const _))).indicator
            measurableSet_Iio).norm).aestronglyMeasurable
        (Eventually.of_forall fun v => ?_)
      dsimp only [ψn]
      rw [Real.norm_of_nonneg (by positivity)]
      by_cases hv : v ∈ Iio (0 : ℝ)
      · rw [indicator_of_mem hv]
        have he : Real.exp (5 * v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hv.out])
        have hn : ‖cx F (v - Real.log n)‖ = |F (v - Real.log n)| := by simp [cx]
        rw [hn]; nlinarith [abs_nonneg (F (v - Real.log n))]
      · rw [indicator_of_notMem hv, norm_zero, mul_zero]; exact abs_nonneg _
    have hlap_n : ∀ t : ℝ, Complex.exp (((5 : ℂ) + t * I) * Real.log n) *
        (∫ u in Iio (-Real.log n), (F u : ℂ) * Complex.exp (((5 : ℂ) + t * I) * u)) =
        ∫ v : ℝ, Complex.exp (((5 : ℂ) + t * I) * v) * ψn v := by
      intro t
      rw [← integral_const_mul, ← integral_indicator measurableSet_Iio,
        ← integral_sub_right_eq_self (fun u : ℝ =>
          (Iio (-Real.log n)).indicator
            (fun w => Complex.exp (((5 : ℂ) + t * I) * Real.log n) *
              ((F w : ℂ) * Complex.exp (((5 : ℂ) + t * I) * w))) u) (Real.log n)]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      dsimp only [ψn]
      by_cases hv : v < 0
      · have hu : v - Real.log n ∈ Iio (-Real.log n) := by simp; linarith
        rw [indicator_of_mem (Set.mem_Iio.mpr hv), indicator_of_mem hu]
        have hexp : ((5 : ℂ) + t * I) * Real.log n + ((5 : ℂ) + t * I) * ↑(v - Real.log n) =
            ((5 : ℂ) + t * I) * v := by push_cast; ring
        calc Complex.exp (((5 : ℂ) + t * I) * Real.log n) *
              ((F (v - Real.log n) : ℂ) * Complex.exp (((5 : ℂ) + t * I) * ↑(v - Real.log n)))
            = (Complex.exp (((5 : ℂ) + t * I) * Real.log n) *
                Complex.exp (((5 : ℂ) + t * I) * ↑(v - Real.log n))) * cx F (v - Real.log n) := by
              simp [cx]; ring
          _ = Complex.exp (((5 : ℂ) + t * I) * v) * cx F (v - Real.log n) := by
              rw [← Complex.exp_add, hexp]
      · have hu : v - Real.log n ∉ Iio (-Real.log n) := by simp; linarith [not_lt.mp hv]
        rw [indicator_of_notMem (show v ∉ Iio (0 : ℝ) from hv), indicator_of_notMem hu, mul_zero]
    have hgn_eq : gn n = fun t : ℝ => (vonMangoldtAtom n : ℂ) *
        (laplaceTest (cx G) (((5 : ℝ) : ℂ) + t * I) *
          ∫ v : ℝ, Complex.exp ((((5 : ℝ) : ℂ) + t * I) * v) * ψn v) := by
      funext t; dsimp only [gn]
      have h5 : (((5 : ℝ) : ℂ) + t * I) = (5 : ℂ) + t * I := by norm_num
      rw [h5, hlap_n t]; ring
    rw [hgn_eq, integral_const_mul, integral_laplaceTest_mul_laplace hψ hs 5 hψm hψi]
    have htrans : (∫ v : ℝ, cx G v * ψn v) = ((∫ u : ℝ, F u * G (u + Real.log n) : ℝ) : ℂ) := by
      rw [← integral_sub_right_eq_self (fun u : ℝ => F u * G (u + Real.log n)) (Real.log n)]
      simp only [sub_add_cancel]
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun v => ?_)
      dsimp only [ψn]
      rcases lt_or_ge v 0 with hv | hv
      · rw [indicator_of_mem (Set.mem_Iio.mpr hv)]; simp [cx, mul_comm]
      · rw [indicator_of_notMem (show v ∉ Iio (0 : ℝ) from not_lt.mpr hv), hG0 v hv]; simp [cx]
    rw [htrans]
    push_cast; ring
  have hlhs : (fun t : ℝ => laplaceTest (cx G) (5 + t * I) * stateTail F (5 + t * I)) =
      fun t : ℝ => ∑' n : ℕ, gn n t := by
    funext t; unfold stateTail; rw [← tsum_mul_left]
  refine ⟨?_, ?_⟩
  · set S₄ : ℝ := ∑' n : ℕ, vonMangoldtAtom n * Real.exp (-(4 * Real.log n))
    refine (integrable_inv_one_add_sq.const_mul (D * M₈ * S₄)).mono' ?_
      (Eventually.of_forall fun t => ?_)
    · have hTailD := differentiableOn_stateTail hF
      exact (((differentiable_laplaceTest hψ.continuous hs).continuous.comp (by fun_prop)).mul
        (hTailD.continuousOn.comp_continuous (by fun_prop) fun t => by simp)).aestronglyMeasurable
    · rw [congrFun hlhs t]
      have hgn_t : Summable fun n : ℕ => ‖gn n t‖ :=
        Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
          (fun n => (hgn_bound n t).trans_eq (by ring))
          (hsum4.mul_left (D * M₈ * (1 + t ^ 2)⁻¹))
      calc ‖∑' n : ℕ, gn n t‖
          ≤ ∑' n : ℕ, ‖gn n t‖ := norm_tsum_le_tsum_norm hgn_t
        _ ≤ ∑' n : ℕ, (D * M₈ * (1 + t ^ 2)⁻¹) *
              (vonMangoldtAtom n * Real.exp (-(4 * Real.log n))) :=
            hgn_t.tsum_le_tsum (fun n => (hgn_bound n t).trans_eq (by ring)) (hsum4.mul_left _)
        _ = (D * M₈ * S₄) * (1 + t ^ 2)⁻¹ := by
            rw [tsum_mul_left]; dsimp [S₄]; ring
  · rw [hlhs, ← hswap]
    simp_rw [hgn_eval]
    rw [tsum_mul_left, Complex.ofReal_tsum]

/-- **Unconditional smooth-test explicit formula on the energy domain.** For **every** profile
`F ∈ CriticalHalfLineEnergyDomain` (with no state-equation assumption) and **every** real smooth
compactly supported test `G` on `u < 0`, the zero series `∑_z L F(z) L G(-z)` converges to
`bareMixedEnergy F G`. -/
theorem hasSum_bareMixedEnergy_of_domain {F : ℝ → ℝ} (hF : CriticalHalfLineEnergyDomain F)
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) (hG0 : ∀ u, 0 ≤ u → G u = 0) :
    HasSum (fun q : XiZeroCopy =>
        negativeHalfLineLaplace (cx F) (centredZero q) *
          negativeHalfLineLaplace (cx G) (-centredZero q))
      ((bareMixedEnergy F G : ℝ) : ℂ) := by
  have hψ : ContDiff ℝ ∞ (cx G) := Complex.ofRealCLM.contDiff.comp hG
  have hs : HasCompactSupport (cx G) := hc.comp_left Complex.ofReal_zero
  have hGd : CriticalHalfLineEnergyDomain G :=
    criticalHalfLineEnergyDomain_of_compact_negative
      (hG.of_le (WithTop.coe_le_coe.mpr le_top)) hc hG0
  obtain ⟨D, -, hD⟩ := exists_laplaceTest_decay hψ hs (-2) 5
  have htwo := hasSum_zeroValues_two_lines hF (differentiable_laplaceTest hψ.continuous hs)
    (a := -2) (b := 5) (by norm_num) (by norm_num) (fun σ t h1 h2 => hD σ t h1 h2)
  have ha1 : (criticalAliasCoefficient 1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (criticalAliasCoefficient_positive one_pos).ne'
  have hleft_pt : ∀ t : ℝ, globalRemainder F (-2 + t * I) =
      -(criticalAliasCoefficient 1 : ℂ) * stateMeromorphic 1 F (-2 + t * I - 8) := by
    intro t
    unfold stateMeromorphic
    have hp : (-2 : ℂ) + t * I - 8 + 8 = -2 + t * I := by ring
    rw [hp]
    field_simp
  have hleft : (∫ t : ℝ, laplaceTest (cx G) (((-2 : ℝ) : ℂ) + t * I) *
      globalRemainder F (((-2 : ℝ) : ℂ) + t * I)) = 0 := by
    have heq : (fun t : ℝ => laplaceTest (cx G) (((-2 : ℝ) : ℂ) + t * I) *
        globalRemainder F (((-2 : ℝ) : ℂ) + t * I)) =
        fun t : ℝ => -(criticalAliasCoefficient 1 : ℂ) *
          (laplaceTest (cx G) (((-2 : ℝ) : ℂ) + t * I) *
            stateMeromorphic 1 F (((-2 : ℝ) : ℂ) + t * I - 8)) := by
      funext t
      have hm2 : (((-2 : ℝ) : ℂ) + t * I) = -2 + t * I := by norm_num
      rw [hm2, hleft_pt t]; ring
    rw [heq, integral_const_mul,
      integral_laplaceTest_mul_stateMeromorphic_left (W₀ := 1) hF hψ hs (a := -2) (by norm_num)]
    have hbw : beyondWallPairing 1 hF (cx G) = 0 := by
      unfold beyondWallPairing
      have hz : (∫ x : ℝ in Ioi (0 : ℝ), cx G x * beyondWallProfile 1 hF x) =
          ∫ x : ℝ in Ioi (0 : ℝ), (0 : ℂ) :=
        setIntegral_congr_fun measurableSet_Ioi fun x hx => by
          simp [cx, hG0 x hx.le]
      rw [hz, integral_zero]
    rw [hbw, mul_zero, mul_zero]
  have hright_pt : ∀ t : ℝ, globalRemainder F (5 + t * I) =
      stateGamma F (5 + t * I) +
        negativeHalfLineLaplace (cx F) (5 + t * I) *
          (deriv riemannZeta (1 / 2 + ((5 : ℂ) + t * I)) /
            riemannZeta (1 / 2 + ((5 : ℂ) + t * I))) -
        stateTail F (5 + t * I) +
        ((coshHalfMoment F : ℂ) * (1 / ((5 : ℂ) + t * I + 1 / 2) + 1 / ((5 : ℂ) + t * I - 1 / 2)) -
          (sinhHalfMoment F : ℂ) * (1 / ((5 : ℂ) + t * I + 1 / 2) - 1 / ((5 : ℂ) + t * I - 1 / 2))) := by
    intro t
    have hp_re : -(1 / 2) < ((5 : ℂ) + t * I).re := by simp; norm_num
    have hp0 : 0 < ((5 : ℂ) + t * I).re := by simp
    have hp_ne : (5 : ℂ) + t * I ≠ 1 / 2 := by
      intro h; have := congrArg Complex.re h; simp at this; norm_num at this
    have hζ : riemannZeta (1 / 2 + ((5 : ℂ) + t * I)) ≠ 0 :=
      riemannZeta_ne_zero_of_one_le_re (by simp; norm_num)
    rw [globalRemainder, if_pos hp_re, levyRemainder_eq hF hp0]
    have hseq := stateEquation_eq_remainder (W₀ := 1) hF hp_ne hζ
    unfold stateEquation at hseq
    linear_combination -hseq
  obtain ⟨i_gam, v_gam⟩ := integral_laplaceTest_stateGamma_five hF hG hc hG0
  obtain ⟨i_fwd, v_fwd⟩ := integral_laplaceTest_forwardPrime_five hF hG hc hG0
  obtain ⟨i_tail, v_tail⟩ := integral_laplaceTest_stateTail_five hF hG hc hG0
  obtain ⟨i_pole, v_pole⟩ := integral_laplaceTest_polePart_five F hG hc hG0
  set f1 : ℝ → ℂ := fun t => laplaceTest (cx G) (5 + t * I) * stateGamma F (5 + t * I)
  set f2 : ℝ → ℂ := fun t => laplaceTest (cx G) (5 + t * I) *
    (negativeHalfLineLaplace (cx F) (5 + t * I) *
      (deriv riemannZeta (1 / 2 + ((5 : ℂ) + t * I)) / riemannZeta (1 / 2 + ((5 : ℂ) + t * I))))
  set f3 : ℝ → ℂ := fun t => laplaceTest (cx G) (5 + t * I) * stateTail F (5 + t * I)
  set f4 : ℝ → ℂ := fun t => laplaceTest (cx G) (5 + t * I) *
    ((coshHalfMoment F : ℂ) * (1 / ((5 : ℂ) + t * I + 1 / 2) + 1 / ((5 : ℂ) + t * I - 1 / 2)) -
      (sinhHalfMoment F : ℂ) * (1 / ((5 : ℂ) + t * I + 1 / 2) - 1 / ((5 : ℂ) + t * I - 1 / 2)))
  have hright : (∫ t : ℝ, laplaceTest (cx G) (((5 : ℝ) : ℂ) + t * I) *
      globalRemainder F (((5 : ℝ) : ℂ) + t * I)) =
      2 * Real.pi * ((bareMixedEnergy F G : ℝ) : ℂ) := by
    have hright_eq : (fun t : ℝ => laplaceTest (cx G) (((5 : ℝ) : ℂ) + t * I) *
        globalRemainder F (((5 : ℝ) : ℂ) + t * I)) = fun t => ((f1 t + f2 t) - f3 t) + f4 t := by
      funext t
      have h5 : (((5 : ℝ) : ℂ) + t * I) = (5 : ℂ) + t * I := by norm_num
      rw [h5, hright_pt t]; dsimp only [f1, f2, f3, f4]; ring
    rw [hright_eq,
      integral_add (f := fun t => (f1 t + f2 t) - f3 t) (g := f4) ((i_gam.add i_fwd).sub i_tail) i_pole,
      integral_sub (f := fun t => f1 t + f2 t) (g := f3) (i_gam.add i_fwd) i_tail,
      integral_add (f := f1) (g := f2) i_gam i_fwd,
      v_gam, v_fwd, v_tail, v_pole]
    have hp_sum : primeMixedForm F G =
        (∑' n : ℕ, vonMangoldtAtom n * ∫ u, F u * G (u - Real.log n)) +
          ∑' n : ℕ, vonMangoldtAtom n * ∫ u, F u * G (u + Real.log n) := by
      obtain ⟨bG, hbG⟩ := hc.isCompact.bddBelow
      set RG : ℝ := -bG
      set N₀ : ℕ := Nat.floor (Real.exp (max RG 0)) + 2
      have hs1 : Summable fun n : ℕ => vonMangoldtAtom n * ∫ u, F u * G (u - Real.log n) := by
        refine summable_of_ne_finset_zero (s := Finset.range N₀) fun n hn => ?_
        have hn_ge : N₀ ≤ n := not_lt.mp (by simpa [Finset.mem_range] using hn)
        have hexp_lt : Real.exp (max RG 0) < (n : ℝ) := by
          have hfl : Real.exp (max RG 0) < (Nat.floor (Real.exp (max RG 0)) : ℝ) + 1 :=
            Nat.lt_floor_add_one _
          have hcast : (Nat.floor (Real.exp (max RG 0)) : ℝ) + 2 ≤ (n : ℝ) := by exact_mod_cast hn_ge
          linarith
        have hlog_gt : max RG 0 < Real.log n :=
          (Real.exp_lt_exp.mp (by rwa [Real.exp_log (lt_trans (Real.exp_pos _) hexp_lt)]))
        have hzero : (fun u : ℝ => F u * G (u - Real.log n)) = fun _ => 0 := by
          funext u
          rcases le_or_gt 0 u with hu | hu
          · rw [hF.support u hu, zero_mul]
          · have hout : u - Real.log n ∉ tsupport G := fun hm => by
              have hlow : bG ≤ u - Real.log n := hbG hm
              have hRG : -bG < Real.log n := lt_of_le_of_lt (le_max_left RG 0) hlog_gt
              linarith
            rw [image_eq_zero_of_notMem_tsupport hout, mul_zero]
        rw [hzero, integral_zero, mul_zero]
      have htot := summable_primePairTerm hF.weighted hGd.weighted
      have hs2 : Summable fun n : ℕ => vonMangoldtAtom n * ∫ u, F u * G (u + Real.log n) := by
        refine (htot.sub hs1).congr fun n => ?_
        unfold primePairTerm; ring
      unfold primeMixedForm
      rw [← hs1.tsum_add hs2]
      refine tsum_congr fun n => ?_
      unfold primePairTerm; ring
    have hp_symm : (primeMixedForm F G + primeMixedForm G F) / 2 = primeMixedForm F G := by
      rw [primeMixedForm_symm G F]; ring
    unfold bareMixedEnergy
    rw [hp_symm, hp_sum]
    push_cast
    ring
  rw [hleft, sub_zero, hright] at htwo
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hval : (1 / (2 * ↑Real.pi) : ℂ) * (2 * ↑Real.pi * ↑(bareMixedEnergy F G)) =
      ((bareMixedEnergy F G : ℝ) : ℂ) := by
    field_simp
  rw [hval] at htwo
  have hfun : (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q)) =
      fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
        laplaceTest (cx G) (centredZero q) :=
    funext fun q => by rw [laplaceTest_eq_laplace_neg]
  rwa [hfun]

/-! ### 3. Complete subsumption of the collar weak equation by `(★)` (Main answer to E-Q4) -/

/-- A profile `F` satisfies the left-normalised Cauchy system `(★)` at ratio `R` if on `Re w > -4`,
the left-regularised Cauchy sum of its zero values equals `-a(R) L F(w)`. -/
def SatisfiesNormalisedStar (R : ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ w : ℂ, -4 < w.re →
    Tendsto (fun b : ℂ => ∑' c : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero c) *
        ((w + 8 - centredZero c)⁻¹ - (b - centredZero c)⁻¹))
      (comap Complex.re atBot)
      (𝓝 (-((criticalAliasCoefficient R : ℂ) * negativeHalfLineLaplace (cx F) w)))

/-- The smooth collar weak equation at ratio `R`: `criticalHalfLineMixedEnergy R F G = 0` for
every `G ∈ C_c^∞((-log 2, 0))`. -/
def SmoothCollarWeakEquation (R : ℝ) (F : ℝ → ℝ) : Prop :=
  ∀ G : ℝ → ℝ, IsSmoothCollarTest G → criticalHalfLineMixedEnergy R F G = 0

/-- The critical state satisfies `SatisfiesNormalisedStar W₀ F`. -/
theorem criticalState_satisfiesNormalisedStar {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    SatisfiesNormalisedStar W₀ F :=
  fun _ hw => criticalState_starEquation_normalised hW hthreshold hF hw

private theorem neBot_comap_re_atBot : (comap Complex.re atBot).NeBot := by
  have ht : Tendsto (fun x : ℝ => (x : ℂ)) atBot (comap Complex.re atBot) := by
    rw [tendsto_comap_iff]
    exact tendsto_id
  exact ht.neBot

/-- Normalised `(★)` identifies `globalRemainder F (w + 8)` with `-a(R) L F(w)` on `Re w > -4`. -/
theorem globalRemainder_eq_of_normalisedStar {R : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hstar : SatisfiesNormalisedStar R F) {w : ℂ}
    (hw : -4 < w.re) :
    globalRemainder F (w + 8) =
      -((criticalAliasCoefficient R : ℂ) * negativeHalfLineLaplace (cx F) w) := by
  haveI : (comap Complex.re atBot).NeBot := neBot_comap_re_atBot
  have hxi : xi (1 / 2 + (w + 8)) ≠ 0 := xi_ne_zero_of_half_le_abs_re (by
    have h8 : (w + 8).re = w.re + 8 := by simp
    rw [h8]
    have := le_abs_self (w.re + 8)
    linarith)
  exact tendsto_nhds_unique (tendsto_tsum_sub_left hF hxi) (hstar w hw)

/-- Under normalised `(★)`, for every smooth compactly supported test `ψ` vanishing on `(0, ∞)`,
`∑_z L F(z) ψ̂(z) = -a(R) ∫ ψ(u) e^{-8u} F(u) du`. -/
theorem hasSum_zeroSeries_test_left_of_normalisedStar {R : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hstar : SatisfiesNormalisedStar R F)
    {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ) (hs : HasCompactSupport ψ)
    (hψ0 : ∀ x, 0 < x → ψ x = 0) :
    HasSum (fun q : XiZeroCopy =>
        negativeHalfLineLaplace (cx F) (centredZero q) * laplaceTest ψ (centredZero q))
      (-((criticalAliasCoefficient R : ℂ) * statePairing F ψ)) := by
  obtain ⟨D, -, hD⟩ := exists_laplaceTest_decay hψ hs (-2) 5
  have htwo := hasSum_zeroValues_two_lines hF (differentiable_laplaceTest hψ.continuous hs)
    (a := -2) (b := 5) (by norm_num) (by norm_num) (fun σ t h1 h2 => hD σ t h1 h2)
  have ha1 : (criticalAliasCoefficient 1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (criticalAliasCoefficient_positive one_pos).ne'
  have hleft : (∫ t : ℝ, laplaceTest ψ (((-2 : ℝ) : ℂ) + t * I) *
      globalRemainder F (((-2 : ℝ) : ℂ) + t * I)) = 0 := by
    have heq : (fun t : ℝ => laplaceTest ψ (((-2 : ℝ) : ℂ) + t * I) *
        globalRemainder F (((-2 : ℝ) : ℂ) + t * I)) =
        fun t : ℝ => -(criticalAliasCoefficient 1 : ℂ) *
          (laplaceTest ψ (((-2 : ℝ) : ℂ) + t * I) *
            stateMeromorphic 1 F (((-2 : ℝ) : ℂ) + t * I - 8)) := by
      funext t
      unfold stateMeromorphic
      have hp : (((-2 : ℝ) : ℂ) + t * I - 8 + 8) = ((-2 : ℝ) : ℂ) + t * I := by ring
      rw [hp]; field_simp
    rw [heq, integral_const_mul,
      integral_laplaceTest_mul_stateMeromorphic_left (W₀ := 1) hF hψ hs (a := -2) (by norm_num)]
    have hbw : beyondWallPairing 1 hF ψ = 0 := by
      unfold beyondWallPairing
      have hz : (∫ x : ℝ in Ioi (0 : ℝ), ψ x * beyondWallProfile 1 hF x) =
          ∫ x : ℝ in Ioi (0 : ℝ), (0 : ℂ) :=
        setIntegral_congr_fun measurableSet_Ioi fun x hx => by rw [hψ0 x hx, zero_mul]
      rw [hz, integral_zero]
    rw [hbw, mul_zero, mul_zero]
  have hright : (∫ t : ℝ, laplaceTest ψ (((5 : ℝ) : ℂ) + t * I) *
      globalRemainder F (((5 : ℝ) : ℂ) + t * I)) =
      -(criticalAliasCoefficient R : ℂ) * (2 * Real.pi * statePairing F ψ) := by
    have heq : (fun t : ℝ => laplaceTest ψ (((5 : ℝ) : ℂ) + t * I) *
        globalRemainder F (((5 : ℝ) : ℂ) + t * I)) =
        fun t : ℝ => -(criticalAliasCoefficient R : ℂ) *
          (laplaceTest ψ (((5 : ℝ) : ℂ) + t * I) *
            negativeHalfLineLaplace (cx F) (((5 : ℝ) : ℂ) + t * I - 8)) := by
      funext t
      have hw : -4 < ((((5 : ℝ) : ℂ) + t * I - 8)).re := by simp; norm_num
      have he := globalRemainder_eq_of_normalisedStar hF hstar hw
      have hp : (((5 : ℝ) : ℂ) + t * I - 8 + 8) = ((5 : ℝ) : ℂ) + t * I := by ring
      rw [hp] at he
      rw [he]; ring
    rw [heq, integral_const_mul,
      integral_laplaceTest_mul_laplace_right hF hψ hs (b := 5) (by norm_num)]
  rw [hleft, sub_zero, hright] at htwo
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  convert htwo using 1
  field_simp

/-- Under normalised `(★)` at `R`, the heated zero series satisfies the exact two-sided heat
identity for every `ε > 0` and `T ∈ ℝ`. -/
theorem hasSum_heated_zeroSeries_of_normalisedStar {R : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hstar : SatisfiesNormalisedStar R F)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    HasSum (fun q : XiZeroCopy =>
        negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε T (centredZero q))
      ((criticalAliasCoefficient 1 : ℂ) * heatedBeyondWall ε 1 hF T -
        (criticalAliasCoefficient R : ℂ) * ((heatedState ε F T : ℝ) : ℂ)) := by
  have htwo := hasSum_zeroValues_two_lines hF (differentiable_stateHeatSymbol ε T)
    (a := -2) (b := 5) (by norm_num) (by norm_num)
    (fun σ t h1 h2 => norm_stateHeatSymbol_strip_le hε T h1 h2 t)
  have ha1 : (criticalAliasCoefficient 1 : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (criticalAliasCoefficient_positive one_pos).ne'
  have hleft : (∫ t : ℝ, stateHeatSymbol ε T (((-2 : ℝ) : ℂ) + t * I) *
      globalRemainder F (((-2 : ℝ) : ℂ) + t * I)) =
      -(criticalAliasCoefficient 1 : ℂ) * (2 * Real.pi * heatedBeyondWall ε 1 hF T) := by
    have heq : (fun t : ℝ => stateHeatSymbol ε T (((-2 : ℝ) : ℂ) + t * I) *
        globalRemainder F (((-2 : ℝ) : ℂ) + t * I)) =
        fun t : ℝ => -(criticalAliasCoefficient 1 : ℂ) *
          (stateHeatSymbol ε T (((-2 : ℝ) : ℂ) + t * I) *
            stateMeromorphic 1 F (((-2 : ℝ) : ℂ) + t * I - 8)) := by
      funext t
      unfold stateMeromorphic
      have hp : (((-2 : ℝ) : ℂ) + t * I - 8 + 8) = ((-2 : ℝ) : ℂ) + t * I := by ring
      rw [hp]; field_simp
    rw [heq, integral_const_mul,
      integral_stateHeatSymbol_mul_stateMeromorphic_left (W₀ := 1) hF hε T (a := -2) (by norm_num)]
  have hright : (∫ t : ℝ, stateHeatSymbol ε T (((5 : ℝ) : ℂ) + t * I) *
      globalRemainder F (((5 : ℝ) : ℂ) + t * I)) =
      -(criticalAliasCoefficient R : ℂ) * (2 * Real.pi * ((heatedState ε F T : ℝ) : ℂ)) := by
    have heq : (fun t : ℝ => stateHeatSymbol ε T (((5 : ℝ) : ℂ) + t * I) *
        globalRemainder F (((5 : ℝ) : ℂ) + t * I)) =
        fun t : ℝ => -(criticalAliasCoefficient R : ℂ) *
          (stateHeatSymbol ε T (((5 : ℝ) : ℂ) + t * I) *
            negativeHalfLineLaplace (cx F) (((5 : ℝ) : ℂ) + t * I - 8)) := by
      funext t
      have hw : -4 < ((((5 : ℝ) : ℂ) + t * I - 8)).re := by simp; norm_num
      have he := globalRemainder_eq_of_normalisedStar hF hstar hw
      have hp : (((5 : ℝ) : ℂ) + t * I - 8 + 8) = ((5 : ℝ) : ℂ) + t * I := by ring
      rw [hp] at he
      rw [he]; ring
    rw [heq, integral_const_mul,
      integral_stateHeatSymbol_mul_laplace_right hF hε T (b := 5) (by norm_num)]
  rw [hleft, hright] at htwo
  have h2pi : (2 * Real.pi : ℂ) ≠ 0 :=
    mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  convert htwo using 1
  field_simp
  ring

/-- Under normalised `(★)` at `R`, the Gaussian-summed zero pairing against **every** domain
profile `G ∈ H` converges to `-a(R) ∫_{u < 0} F(u) G(u) e^{-8u} du`. -/
theorem tendsto_zeroPairing_of_normalisedStar {R : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hstar : SatisfiesNormalisedStar R F)
    {G : ℝ → ℝ} (hG : CriticalHalfLineEnergyDomain G) :
    Tendsto (fun ε : ℝ => ∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero q ^ 2))
      (𝓝[>] 0)
      (𝓝 (((-(criticalAliasCoefficient R *
        ∫ u in Iio (0 : ℝ), F u * G u * Real.exp (-(8 * u))) : ℝ) : ℂ))) := by
  have hheated : ∀ {ε : ℝ}, 0 < ε →
      HasSum (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
          negativeHalfLineLaplace (cx G) (-centredZero q) *
            Complex.exp ((ε : ℂ) * centredZero q ^ 2))
        ((criticalAliasCoefficient 1 : ℂ) * (∫ T : ℝ, cx G T * heatedBeyondWall ε 1 hF T) -
          (criticalAliasCoefficient R : ℂ) *
            ∫ T : ℝ, cx G T * ((heatedState ε F T : ℝ) : ℂ)) := by
    intro ε hε
    have hsplit : ∀ (T : ℝ) (z : ℂ), stateHeatSymbol ε T z =
        Complex.exp ((ε : ℂ) * z ^ 2) * Complex.exp (-z * (T : ℂ)) := by
      intro T z; unfold stateHeatSymbol; rw [sub_eq_add_neg, Complex.exp_add, neg_mul]
    have hzre : ∀ q : XiZeroCopy, (centredZero q).re < 1 / 2 := fun q =>
      (abs_lt.mp (abs_re_centredZero_lt q)).2
    have hterm : ∀ q : XiZeroCopy,
        (∫ T : ℝ, cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
          stateHeatSymbol ε T (centredZero q))) =
        negativeHalfLineLaplace (cx F) (centredZero q) *
          negativeHalfLineLaplace (cx G) (-centredZero q) *
            Complex.exp ((ε : ℂ) * centredZero q ^ 2) := by
      intro q
      have e : (fun T : ℝ => cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
            stateHeatSymbol ε T (centredZero q))) = fun T : ℝ =>
          (negativeHalfLineLaplace (cx F) (centredZero q) *
            Complex.exp ((ε : ℂ) * centredZero q ^ 2)) *
            (Complex.exp (-centredZero q * (T : ℂ)) * cx G T) := by
        funext T; rw [hsplit]; ring
      have hL : negativeHalfLineLaplace (cx G) (-centredZero q) =
          ∫ T : ℝ, Complex.exp (-centredZero q * (T : ℂ)) * cx G T := rfl
      rw [e, integral_const_mul, hL]; ring
    have hint : ∀ q : XiZeroCopy, Integrable fun T : ℝ => cx G T *
        (negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε T (centredZero q)) := by
      intro q
      refine ((integrable_cexp_neg_mul_cx hG (z := centredZero q) (by linarith [hzre q])).const_mul
        (negativeHalfLineLaplace (cx F) (centredZero q) *
          Complex.exp ((ε : ℂ) * centredZero q ^ 2))).congr (Eventually.of_forall fun T => ?_)
      dsimp only
      rw [hsplit]; ring
    have hGm := integrable_abs_mul_exp_of_domain hG (c := -(1 / 2)) (by norm_num)
    have hsum0 := (hasSum_heated_zeroSeries_of_normalisedStar hF hstar hε 0).summable.norm
    have hbound : ∀ q : XiZeroCopy,
        (∫ T : ℝ, ‖cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
          stateHeatSymbol ε T (centredZero q))‖) ≤
        ‖negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε 0 (centredZero q)‖ *
          ∫ u : ℝ, |G u| * Real.exp (-(1 / 2) * u) := by
      intro q
      rw [← integral_const_mul]
      refine integral_mono (hint q).norm (hGm.const_mul _) fun T => ?_
      have h0 : stateHeatSymbol ε 0 (centredZero q) =
          Complex.exp ((ε : ℂ) * centredZero q ^ 2) := by
        unfold stateHeatSymbol; rw [Complex.ofReal_zero, mul_zero, sub_zero]
      have hre : (-centredZero q * (T : ℂ)).re = -(centredZero q).re * T := by simp
      have hgx : |G T| * Real.exp (-(centredZero q).re * T) ≤
          |G T| * Real.exp (-(1 / 2) * T) := by
        rcases le_or_gt 0 T with hT | hT
        · rw [hG.support T hT, abs_zero, zero_mul, zero_mul]
        · refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
          nlinarith [mul_pos (sub_pos.mpr (hzre q)) (neg_pos.mpr hT)]
      show ‖((G T : ℝ) : ℂ) * (negativeHalfLineLaplace (cx F) (centredZero q) *
          stateHeatSymbol ε T (centredZero q))‖ ≤
        ‖negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε 0 (centredZero q)‖ *
          (|G T| * Real.exp (-(1 / 2) * T))
      rw [hsplit, h0, norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        Complex.norm_exp (-centredZero q * (T : ℂ)), hre]
      calc |G T| * (‖negativeHalfLineLaplace (cx F) (centredZero q)‖ *
              (‖Complex.exp ((ε : ℂ) * centredZero q ^ 2)‖ * Real.exp (-(centredZero q).re * T)))
          = (‖negativeHalfLineLaplace (cx F) (centredZero q)‖ *
              ‖Complex.exp ((ε : ℂ) * centredZero q ^ 2)‖) *
              (|G T| * Real.exp (-(centredZero q).re * T)) := by ring
        _ ≤ (‖negativeHalfLineLaplace (cx F) (centredZero q)‖ *
              ‖Complex.exp ((ε : ℂ) * centredZero q ^ 2)‖) *
              (|G T| * Real.exp (-(1 / 2) * T)) :=
            mul_le_mul_of_nonneg_left hgx (by positivity)
    have hsum : Summable fun q : XiZeroCopy =>
        ∫ T : ℝ, ‖cx G T * (negativeHalfLineLaplace (cx F) (centredZero q) *
          stateHeatSymbol ε T (centredZero q))‖ :=
      Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _) hbound
        (hsum0.mul_right _)
    have h := hasSum_integral_of_summable_integral_norm hint hsum
    have htsum : ∀ T : ℝ, (∑' q : XiZeroCopy, cx G T *
        (negativeHalfLineLaplace (cx F) (centredZero q) * stateHeatSymbol ε T (centredZero q))) =
        (criticalAliasCoefficient 1 : ℂ) * (cx G T * heatedBeyondWall ε 1 hF T) -
          (criticalAliasCoefficient R : ℂ) * (cx G T * ((heatedState ε F T : ℝ) : ℂ)) := by
      intro T
      rw [tsum_mul_left, (hasSum_heated_zeroSeries_of_normalisedStar hF hstar hε T).tsum_eq]
      ring
    simp only [hterm, htsum] at h
    have hrhs : (∫ a : ℝ, (criticalAliasCoefficient 1 : ℂ) * (cx G a * heatedBeyondWall ε 1 hF a) -
        (criticalAliasCoefficient R : ℂ) * (cx G a * ((heatedState ε F a : ℝ) : ℂ))) =
        (criticalAliasCoefficient 1 : ℂ) * (∫ T : ℝ, cx G T * heatedBeyondWall ε 1 hF T) -
          (criticalAliasCoefficient R : ℂ) * ∫ T : ℝ, cx G T * ((heatedState ε F T : ℝ) : ℂ) := by
      rw [integral_sub ((integrable_cx_mul_heatedBeyondWall 1 hF hG hε).const_mul _)
        ((integrable_cx_mul_heatedState hF hG hε).const_mul _),
        integral_const_mul, integral_const_mul]
    rwa [hrhs] at h
  have h1 := (tendsto_integral_cx_mul_heatedBeyondWall 1 hF hG).const_mul
    (criticalAliasCoefficient 1 : ℂ)
  have h2 := (tendsto_integral_cx_mul_heatedState hF hG).const_mul
    (criticalAliasCoefficient R : ℂ)
  have h3 := h1.sub h2
  have hv : (criticalAliasCoefficient 1 : ℂ) * 0 -
      (criticalAliasCoefficient R : ℂ) * statePairing F (cx G) =
      ((-(criticalAliasCoefficient R *
        ∫ u in Iio (0 : ℝ), F u * G u * Real.exp (-(8 * u))) : ℝ) : ℂ) := by
    rw [statePairing_cx hF.support G]
    push_cast; ring
  rw [hv] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hheated hε).tsum_eq.symm

/-- **Subsumption of the smooth half-line weak equation by `(★)`.** Every profile `F ∈ H`
satisfying normalised `(★)` at ratio `R` automatically satisfies
`criticalHalfLineMixedEnergy R F G = 0` against every real smooth compactly supported test `G` on
`u < 0`. -/
theorem mixedEnergy_eq_zero_of_normalisedStar {R : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hstar : SatisfiesNormalisedStar R F)
    {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G)
    (hG0 : ∀ u, 0 ≤ u → G u = 0) :
    criticalHalfLineMixedEnergy R F G = 0 := by
  have hψ : ContDiff ℝ ∞ (cx G) := Complex.ofRealCLM.contDiff.comp hG
  have hs : HasCompactSupport (cx G) := hc.comp_left Complex.ofReal_zero
  have hs_bare := hasSum_bareMixedEnergy_of_domain hF hG hc hG0
  have hs_star := hasSum_zeroSeries_test_left_of_normalisedStar hF hstar hψ hs fun x hx => by
    simp [cx, hG0 x hx.le]
  have hfun : (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
        laplaceTest (cx G) (centredZero q)) =
      fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) :=
    funext fun q => by rw [laplaceTest_eq_laplace_neg]
  rw [hfun, statePairing_cx hF.support G] at hs_star
  have heq_c : ((bareMixedEnergy F G : ℝ) : ℂ) =
      -((criticalAliasCoefficient R : ℂ) *
        ((∫ u in Iio (0 : ℝ), F u * G u * Real.exp (-(8 * u)) : ℝ) : ℂ)) :=
    hs_bare.unique hs_star
  have heq_r : bareMixedEnergy F G = -(criticalAliasCoefficient R *
      ∫ u in Iio (0 : ℝ), F u * G u * Real.exp (-(8 * u))) := by
    exact_mod_cast heq_c
  rw [criticalHalfLineMixedEnergy_eq_bare_add, heq_r]
  ring

/-- **Answer to E-Q4 (Collar Softness Theorem).** Every profile `F ∈ H` satisfying left-normalised
`(★)` at ratio `R` automatically satisfies the collar weak equation on `(-log 2, 0)`. -/
theorem openCollar_weakEquation_of_normalisedStar {R : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hstar : SatisfiesNormalisedStar R F) :
    SmoothCollarWeakEquation R F :=
  fun _ hG => mixedEnergy_eq_zero_of_normalisedStar hF hstar hG.1 hG.2.1 hG.2.2.1

/-- **Exact equivalence:** Adjoining the collar weak equation on `(-log 2, 0)` to normalised `(★)`
adds zero constraints on `F` or its zero values `(L F(z_q))_q`. -/
theorem normalisedStar_and_openCollarWeak_iff_normalisedStar {R : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) :
    (SatisfiesNormalisedStar R F ∧ SmoothCollarWeakEquation R F) ↔ SatisfiesNormalisedStar R F :=
  ⟨And.left, fun h => ⟨h, openCollar_weakEquation_of_normalisedStar hF h⟩⟩

/-! ### 4. Collar coercivity, quantitative zero-pairing bound, uniqueness, and deep-tail mass -/

/-- On any `C²` compactly supported profile, `bareMixedEnergy G G = weilQuad G`. -/
theorem bareMixedEnergy_self_eq_weilQuad {G : ℝ → ℝ} (hG : ContDiff ℝ 2 G)
    (hGc : HasCompactSupport G) :
    bareMixedEnergy G G = weilQuad G := by
  have hM := markovEnergy_ofReal_eq_archForm_sub_primeSum hG hGc
  have hP := re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hG.continuous hGc
  have hW : weilQuad G = markovEnergy (fun u => (G u : ℂ)) +
      (weilPoleTerm (EF.weilTest (fun u => (G u : ℂ)) (fun u => (G u : ℂ)))).re := by
    unfold weilQuad markovEnergy
    rw [Complex.sub_re]
    ring
  have harch : gammaMixedForm G G = archForm G := by
    unfold gammaMixedForm archForm gammaFourierPair
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    dsimp only
    rw [show (fun u : ℝ => (G u : ℂ)) = cx G from rfl, Complex.sq_norm, Complex.normSq_apply]
  have hprime : primeMixedForm G G = primeSum G := rfl
  rw [hW, hM, hP]
  unfold bareMixedEnergy
  rw [harch, hprime]
  ring

/-- **Collar bare-form coercivity.** On any `C²` test `G` supported in `[-A, 0]` with
`A ≤ 2 · enlargedWeilFloorAperture` (in particular `A = log 2`),
`bareMixedEnergy G G ≥ (1/8000) ∫ G² ≥ 0`. -/
theorem bareMixedEnergy_collarWindow_ge {A : ℝ} (hA : A ≤ 2 * enlargedWeilFloorAperture)
    {G : ℝ → ℝ} (hG : IsWindowTest A G) :
    (1 / 8000 : ℝ) * (∫ u, G u ^ 2) ≤ bareMixedEnergy G G := by
  rw [bareMixedEnergy_self_eq_weilQuad hG.contDiff hG.hasCompactSupport]
  exact ArchimedeanTateDomination.weilQuad_ge_one_div_eightThousand_of_le_two_mul_enlargedAperture
    hA hG

/-- **Quantitative collar Cauchy–Schwarz bound on the zero values.** Under normalised `(★)` at
ratio `R` (in particular for the critical state at `R = W₀`), every smooth collar test
`G ∈ C_c^∞((-log 2, 0))` satisfies
`‖∑_z L F(z) L G(-z)‖² ≤ 2048000 · a(R)² · (∫_{-log 2}^0 F² e^{-8u}) · bareMixedEnergy G G`.
Thus even the sharpest quantitative inequality induced by collar positivity holds automatically
under `(★)`. -/
theorem norm_sq_openCollar_zeroPairing_le_of_normalisedStar {R : ℝ} {F : ℝ → ℝ}
    (hF : CriticalHalfLineEnergyDomain F) (hstar : SatisfiesNormalisedStar R F)
    {G : ℝ → ℝ} (hG : IsSmoothCollarTest G) :
    ‖∑' q : XiZeroCopy, negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q)‖ ^ 2 ≤
      2048000 * criticalAliasCoefficient R ^ 2 *
        (∫ u in Ioo (-Real.log 2) 0, F u ^ 2 * Real.exp (-(8 * u))) *
          bareMixedEnergy G G := by
  have hψ : ContDiff ℝ ∞ (cx G) := Complex.ofRealCLM.contDiff.comp hG.1
  have hs : HasCompactSupport (cx G) := hG.2.1.comp_left Complex.ofReal_zero
  have hsum := hasSum_zeroSeries_test_left_of_normalisedStar hF hstar hψ hs fun x hx => by
    simp [cx, hG.2.2.1 x hx.le]
  have hfun : (fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
        laplaceTest (cx G) (centredZero q)) =
      fun q : XiZeroCopy => negativeHalfLineLaplace (cx F) (centredZero q) *
        negativeHalfLineLaplace (cx G) (-centredZero q) :=
    funext fun q => by rw [laplaceTest_eq_laplace_neg]
  rw [hfun, statePairing_cx hF.support G] at hsum
  rw [hsum.tsum_eq, norm_neg, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, sq_abs, sq_abs]
  set S : Set ℝ := Ioo (-Real.log 2) 0
  have hI_eq : (∫ u in Iio (0 : ℝ), F u * G u * Real.exp (-(8 * u))) =
      ∫ u in S, F u * G u * Real.exp (-(8 * u)) := by
    rw [← integral_indicator measurableSet_Iio, ← integral_indicator measurableSet_Ioo]
    refine integral_congr_ae (Eventually.of_forall fun u => ?_)
    by_cases hu : u ∈ S
    · rw [indicator_of_mem hu, indicator_of_mem (Set.mem_Iio.mpr hu.2)]
    · rw [indicator_of_notMem hu]
      by_cases h0 : u < 0
      · have hle : u ≤ -Real.log 2 := not_lt.mp fun hgt => hu ⟨hgt, h0⟩
        rw [indicator_of_mem (Set.mem_Iio.mpr h0), hG.2.2.2 u hle, mul_zero, zero_mul]
      · rw [indicator_of_notMem (show u ∉ Iio (0 : ℝ) from h0)]
  rw [hI_eq]
  set A_F : ℝ := ∫ u in S, F u ^ 2 * Real.exp (-(8 * u))
  set A_G : ℝ := ∫ u in S, G u ^ 2 * Real.exp (-(8 * u))
  set I_FG : ℝ := ∫ u in S, F u * G u * Real.exp (-(8 * u))
  have hGd := hG.energyDomain
  have hiF : IntegrableOn (fun u => F u ^ 2 * Real.exp (-(8 * u))) S := hF.exponential.integrableOn
  have hiG : IntegrableOn (fun u => G u ^ 2 * Real.exp (-(8 * u))) S := hGd.exponential.integrableOn
  have hiFG : IntegrableOn (fun u => F u * G u * Real.exp (-(8 * u))) S := by
    refine ((hiF.add hiG).div_const 2).mono'
      (((hF.meas.mul hGd.meas).mul (by fun_prop)).aestronglyMeasurable)
      (Eventually.of_forall fun u => ?_)
    dsimp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_le]
    have he0 : 0 ≤ Real.exp (-(8 * u)) := (Real.exp_pos _).le
    constructor <;> nlinarith [sq_nonneg (F u + G u), sq_nonneg (F u - G u), he0]
  have hA_F0 : 0 ≤ A_F := setIntegral_nonneg measurableSet_Ioo fun _ _ => by positivity
  have hA_G0 : 0 ≤ A_G := setIntegral_nonneg measurableSet_Ioo fun _ _ => by positivity
  have hcs : I_FG ^ 2 ≤ A_F * A_G := by
    have hquad : ∀ t : ℝ, 0 ≤ A_F + 2 * t * I_FG + t ^ 2 * A_G := by
      intro t
      have hnn : 0 ≤ ∫ u in S, (F u + t * G u) ^ 2 * Real.exp (-(8 * u)) :=
        setIntegral_nonneg measurableSet_Ioo fun _ _ => by positivity
      have hexp : (fun u : ℝ => (F u + t * G u) ^ 2 * Real.exp (-(8 * u))) =
          fun u : ℝ => (F u ^ 2 * Real.exp (-(8 * u)) +
            2 * t * (F u * G u * Real.exp (-(8 * u)))) +
            t ^ 2 * (G u ^ 2 * Real.exp (-(8 * u))) := by
        funext u; ring
      rw [hexp,
        integral_add (f := fun u => F u ^ 2 * Real.exp (-(8 * u)) +
          2 * t * (F u * G u * Real.exp (-(8 * u))))
          (g := fun u => t ^ 2 * (G u ^ 2 * Real.exp (-(8 * u))))
          (Integrable.add hiF (hiFG.const_mul (2 * t))) (hiG.const_mul (t ^ 2)),
        integral_add (f := fun u => F u ^ 2 * Real.exp (-(8 * u)))
          (g := fun u => 2 * t * (F u * G u * Real.exp (-(8 * u)))) hiF (hiFG.const_mul (2 * t)),
        integral_const_mul, integral_const_mul] at hnn
      exact hnn
    by_cases hG0_case : A_G = 0
    · rw [hG0_case, mul_zero]
      by_contra hpos
      have hne : I_FG ≠ 0 := fun hz => hpos (by rw [hz]; norm_num)
      have hbad := hquad (-(A_F + 1) / I_FG)
      rw [hG0_case, mul_zero, add_zero, show 2 * (-(A_F + 1) / I_FG) * I_FG =
        -2 * (A_F + 1) by field_simp] at hbad
      linarith
    · have hGpos : 0 < A_G := lt_of_le_of_ne hA_G0 (Ne.symm hG0_case)
      have hq := mul_nonneg (hquad (-I_FG / A_G)) hGpos.le
      have hid : (A_F + 2 * (-I_FG / A_G) * I_FG + (-I_FG / A_G) ^ 2 * A_G) * A_G =
          A_F * A_G - I_FG ^ 2 := by field_simp; ring
      linarith
  have h256 : A_G ≤ 256 * ∫ u, G u ^ 2 := by
    have h1 : A_G ≤ ∫ u in S, 256 * G u ^ 2 := by
      refine setIntegral_mono_on hiG (hGd.sq.const_mul 256).integrableOn measurableSet_Ioo
        fun u hu => ?_
      have hexp : Real.exp (-(8 * u)) ≤ 256 := by
        have h2 : (256 : ℝ) = Real.exp (8 * Real.log 2) := by
          rw [show (8 : ℝ) * Real.log 2 = (8 : ℕ) * Real.log 2 by norm_num, Real.exp_nat_mul,
            Real.exp_log (by norm_num)]
          norm_num
        rw [h2]
        exact Real.exp_le_exp.mpr (by linarith [hu.1])
      nlinarith [sq_nonneg (G u)]
    have h2 : (∫ u in S, 256 * G u ^ 2) ≤ ∫ u, 256 * G u ^ 2 :=
      setIntegral_le_integral (hGd.sq.const_mul 256) (Eventually.of_forall fun _ => by positivity)
    have h3 : (∫ u, 256 * G u ^ 2) = 256 * ∫ u, G u ^ 2 := integral_const_mul 256 _
    linarith
  have hfloor : (1 / 8000 : ℝ) * (∫ u, G u ^ 2) ≤ bareMixedEnergy G G := by
    have haper : Real.log 2 ≤ 2 * enlargedWeilFloorAperture := by
      linarith [enlargedWeilFloorAperture_bounds.1, Real.log_two_lt_d9]
    exact bareMixedEnergy_collarWindow_ge haper hG.isWindowTest_log_two
  have hAG_bare : A_G ≤ 2048000 * bareMixedEnergy G G := by linarith
  calc criticalAliasCoefficient R ^ 2 * I_FG ^ 2
      ≤ criticalAliasCoefficient R ^ 2 * (A_F * A_G) :=
        mul_le_mul_of_nonneg_left hcs (sq_nonneg _)
    _ ≤ criticalAliasCoefficient R ^ 2 * (A_F * (2048000 * bareMixedEnergy G G)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAG_bare hA_F0) (sq_nonneg _)
    _ = 2048000 * criticalAliasCoefficient R ^ 2 * A_F * bareMixedEnergy G G := by ring

/-- **Collar uniqueness from the tail.** If two profiles `F₁, F₂ ∈ H` satisfy the collar weak
equation at ratio `R > 0` against `IsWindowTest (Real.log 2)` and their difference `F₁ - F₂` is a
`C²` collar test on `[-log 2, 0]`, then `F₁ = F₂` everywhere. -/
theorem collar_difference_eq_zero_of_weak {R : ℝ} (hR : 0 < R) {F₁ F₂ : ℝ → ℝ}
    (hF₁ : CriticalHalfLineEnergyDomain F₁) (hF₂ : CriticalHalfLineEnergyDomain F₂)
    (hdiff : IsWindowTest (Real.log 2) (fun u => F₁ u - F₂ u))
    (hw₁ : ∀ G, IsWindowTest (Real.log 2) G → criticalHalfLineMixedEnergy R F₁ G = 0)
    (hw₂ : ∀ G, IsWindowTest (Real.log 2) G → criticalHalfLineMixedEnergy R F₂ G = 0) :
    F₁ = F₂ := by
  set D : ℝ → ℝ := fun u => F₁ u - F₂ u
  have hDd : CriticalHalfLineEnergyDomain D := by
    simpa only [D, neg_one_mul, ← sub_eq_add_neg] using hF₁.add_const_mul hF₂ (-1)
  have hpol1 := criticalHalfLineFullEnergy_add_const_mul R hF₁ hDd (-1)
  have heqF₂ : (fun u => F₁ u + (-1) * D u) = F₂ := by funext u; dsimp [D]; ring
  rw [heqF₂, hw₁ D hdiff] at hpol1
  have hpol2 := criticalHalfLineFullEnergy_add_const_mul R hF₂ hDd 1
  have heqF₁ : (fun u => F₂ u + 1 * D u) = F₁ := by funext u; dsimp [D]; ring
  rw [heqF₁, hw₂ D hdiff] at hpol2
  have hQD0 : criticalHalfLineFullEnergy R D = 0 := by linarith
  have haper : Real.log 2 ≤ 2 * enlargedWeilFloorAperture := by
    linarith [enlargedWeilFloorAperture_bounds.1, Real.log_two_lt_d9]
  have hbare := bareMixedEnergy_collarWindow_ge haper hdiff
  have hfull : criticalHalfLineFullEnergy R D =
      bareMixedEnergy D D + criticalAliasCoefficient R * ∫ u in Iio 0, D u ^ 2 * Real.exp (-(8 * u)) := by
    have harch : gammaMixedForm D D = archForm D := by
      unfold gammaMixedForm archForm gammaFourierPair
      congr 1
      refine integral_congr_ae (Eventually.of_forall fun r => ?_)
      dsimp only
      rw [show (fun u : ℝ => (D u : ℂ)) = cx D from rfl, Complex.sq_norm, Complex.normSq_apply]
    have hprime : primeMixedForm D D = primeSum D := rfl
    unfold criticalHalfLineFullEnergy bareMixedEnergy
    rw [harch, hprime]; ring
  have hconf_nn : 0 ≤ criticalAliasCoefficient R * ∫ u in Iio 0, D u ^ 2 * Real.exp (-(8 * u)) :=
    mul_nonneg (criticalAliasCoefficient_positive hR).le
      (setIntegral_nonneg measurableSet_Iio fun _ _ => by positivity)
  have hsq_nn : 0 ≤ ∫ u, D u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hsq0 : (∫ u, D u ^ 2) = 0 := by linarith
  funext x
  by_contra hne
  have hDx : D x ≠ 0 := sub_ne_zero.mpr hne
  have hcs_sq : HasCompactSupport fun u => D u ^ 2 :=
    HasCompactSupport.comp_left (g := fun y : ℝ => y ^ 2) hdiff.hasCompactSupport (by norm_num)
  have hpos : 0 < ∫ u, D u ^ 2 :=
    (hdiff.continuous.pow 2).integral_pos_of_hasCompactSupport_nonneg_nonzero
      (x := x) hcs_sq (fun u => sq_nonneg (D u)) (pow_ne_zero 2 hDx)
  linarith

/-- **Nonvanishing deep tail of the critical state.** For every `T : ℝ` (in particular
`T = log 2`), the critical state carries strictly positive `L²` mass on `(-∞, -T)`:
`0 < ∫_{u < -T} F(u)² du`. In particular, no critical state is supported in the collar. -/
theorem criticalState_deepTail_sq_pos {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) (T : ℝ) :
    0 < ∫ u in Iio (-T), F u ^ 2 := by
  have hd := criticalHalfLineEnergyDomain_of_groundState hF
  have hnn : 0 ≤ ∫ u in Iio (-T), F u ^ 2 :=
    setIntegral_nonneg measurableSet_Iio fun _ _ => sq_nonneg _
  refine lt_of_le_of_ne hnn fun h0 => ?_
  have hae0 : ∀ᵐ u ∂(volume.restrict (Iio (-T))), F u ^ 2 = 0 :=
    (integral_eq_zero_iff_of_nonneg_ae (Eventually.of_forall fun u => sq_nonneg (F u))
      hd.sq.integrableOn).mp h0.symm
  refine (criticalState_changes_sign_on_every_ray hW hthreshold hF T).1 ?_
  filter_upwards [hae0] with u hu
  have hFu : F u = 0 := sq_eq_zero_iff.mp hu
  linarith

#print axioms primeMixedForm_openCollar
#print axioms hasSum_bareMixedEnergy_of_domain
#print axioms mixedEnergy_eq_zero_of_normalisedStar
#print axioms openCollar_weakEquation_of_normalisedStar
#print axioms normalisedStar_and_openCollarWeak_iff_normalisedStar
#print axioms norm_sq_openCollar_zeroPairing_le_of_normalisedStar
#print axioms collar_difference_eq_zero_of_weak
#print axioms criticalState_deepTail_sq_pos

end GaloisForLFunctions.ExclusionOfTheCriticalState


