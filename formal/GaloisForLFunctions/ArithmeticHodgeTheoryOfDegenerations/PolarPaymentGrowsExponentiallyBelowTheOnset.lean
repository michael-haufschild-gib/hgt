import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePoleCrossPairingIsCompressedBelowTheOnset
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePrimeErrorHasRateSevenEighthsBelowTheOnset
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheContinuumWindowThresholdGrowsExponentially
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheLowPacketPaymentAtEveryRatioIsTheRiemannHypothesis

/-!
# Polar payment grows exponentially below the onset

At critical overlap ratios `c⁸ = R log N`, the low-packet Schur payment on `[−A, 0]` (`PolarPaymentAt R A`)
demands `generalTerminalPolarSource A h ^ 2 / criticalPoleWindowCost R ≤ windowPencil R (halfWeight h)`
uniformly in `A ≥ 0`. Below the onset aperture `a*(ζ)`:

1. **Logarithmic-scale polar kernel** (`generalTerminalPolarSource_eq_integral_terminalPolarKernel`):
   substituting `x = e^y` on `[−A, 0]` expresses `generalTerminalPolarSource A g` as
   `splineAtom * ∫ g(y) (1 − ½ e^y log(1 − e^{2y}) − log(2π) e^y − e^y ψ(e^{−y})) dy`, independent of `A`.
2. **Deep-tail localization** (`sq_generalTerminalPolarSource_deep_le`): cutting `h` smoothly at
   `−s/2` via `windowLeftCutoff (s / 2)` (`s ≥ 6`) leaves a deep remainder supported in
   `(−∞, −(s/2 − 1)]` whose polar source is `O(e^{−7s/4}) √(M₈(H))`.
3. **Top-collar pole-cross compression** (`sq_poleCross_windowTest_le`,
   `abs_top_polarSource_sub_poleCross_le`): on `[−s/2, 0]`, shifting into `(−s, s)` and mollifying
   transfers `exists_sq_integral_poleCrossProfile_le_sharp` to `C²` window tests, while
   `exists_abs_reciprocalMangoldtError_add_euler_le_of_zetaWindowPositive` bounds the
   reciprocal-Mangoldt and Gamma-tail discrepancy by `O(e^{−3s/16}) √(M₈(H))`.
4. **Exponential polar-payment band** (`exists_polarPaymentAt_exp_of_le_onsetAperture`):
   for `R ≤ c₁ e^{c₂ a}` (`0 ≤ a ≤ a*(ζ)`), the Jordan pole reserve `jordanCoefficient 1 / R` inside
   `criticalPoleWindowCost R` absorbs the `O(e^{−s/8})` finite-aperture excess over
   `poleSharpConstant`, proving `PolarPaymentAt R A` uniformly for all `A ≥ 0` with zero log loss.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped CompactlySupported

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open _root_.Zeta23 _root_.RHTower _root_.RHTower.CHMDDoobGraph
  GaloisForLFunctions.SquareRootThreshold
  GaloisForLFunctions.WindowVisibilityLaw
  GaloisForLFunctions.ArithmeticCriticalityTheory
  GaloisForLFunctions.ArithmeticPositivityTheory
  GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
  GaloisForLFunctions.WindowTowerOfSpecZ
  GaloisForLFunctions.SpacingScaleHarmonicAnalysis
  GaloisForLFunctions.CriticalArithmeticCorrelationTheory
  GaloisForLFunctions.ArithmeticDegenerationTheory
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.BiScaleUncertainty

/-! ### 1. Exact logarithmic-variable kernel of `generalTerminalPolarSource` -/

/-- Logarithmic-variable kernel of the complete polar source on `(−∞, 0]`. -/
def terminalPolarKernel (y : ℝ) : ℝ :=
  1 - Real.exp y * Real.log (1 - Real.exp (2 * y)) / 2 -
    Real.log (2 * Real.pi) * Real.exp y - Real.exp y * Chebyshev.psi (Real.exp (-y))

private lemma vanish_zero_of_window_support {g : ℝ → ℝ} {A : ℝ} (hg : Continuous g)
    (hsupp : ∀ y, y ∉ Icc (-A) 0 → g y = 0) : g 0 = 0 := by
  have ht : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h0 : Tendsto (fun n : ℕ => g ((1 : ℝ) / ((n : ℝ) + 1))) atTop (𝓝 0) :=
    tendsto_const_nhds.congr fun n =>
      (hsupp _ fun hm => by
        have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith [hm.2]).symm
  exact tendsto_nhds_unique ((hg.tendsto 0).comp ht) h0

private lemma exists_bound_and_lipschitz_of_window_support {g : ℝ → ℝ} {A : ℝ}
    (hg : ContDiff ℝ 2 g) (hsupp : ∀ y, y ∉ Icc (-A) 0 → g y = 0) :
    ∃ (Bg : ℝ) (Lg : NNReal), 0 ≤ Bg ∧ (∀ x, |g x| ≤ Bg) ∧ LipschitzWith Lg g := by
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hsupp
  obtain ⟨Bg, hBg⟩ := hg.continuous.bounded_above_of_compact_support hgc
  have hgd : Continuous (deriv g) := hg.continuous_deriv (by norm_num)
  obtain ⟨L, hL⟩ := hgd.bounded_above_of_compact_support hgc.deriv
  set Lg : NNReal := Real.toNNReal (max L 0)
  have hlip : LipschitzWith Lg g :=
    lipschitzWith_of_nnnorm_deriv_le (hg.differentiable (by norm_num)) fun x => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs,
        Real.coe_toNNReal _ (le_max_right L 0)]
      exact (Real.norm_eq_abs _ ▸ hL x).trans (le_max_left L 0)
  exact ⟨max Bg 0, Lg, le_max_right Bg 0,
    fun x => (Real.norm_eq_abs _ ▸ hBg x).trans (le_max_left Bg 0), hlip⟩

private lemma integral_polarCenterProfile_logProfile {g : ℝ → ℝ} {A : ℝ}
    (hg : ContDiff ℝ 2 g) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Icc (-A) 0 → g y = 0) :
    (∫ x in (0 : ℝ)..1, polarCenterProfile (logProfile g) x =
        ∫ y, (g y - Real.exp y * g y * Real.log (1 - Real.exp (2 * y)) / 2)) ∧
      Integrable (fun y => g y - Real.exp y * g y * Real.log (1 - Real.exp (2 * y)) / 2) := by
  have hg0 : g 0 = 0 := vanish_zero_of_window_support hg.continuous hsupp
  obtain ⟨Bg, Lg, _, hBg, hLg⟩ := exists_bound_and_lipschitz_of_window_support hg hsupp
  have hLP_lip : ∀ u ∈ Icc (0 : ℝ) 1, ∀ v ∈ Icc (0 : ℝ) 1,
      |logProfile g u - logProfile g v| ≤ ((Lg : ℝ) * Real.exp (2 * A)) * |u - v| :=
    fun u _ v _ => abs_logProfile_sub_le hg hsupp hA hBg hLg u v
  have hLP1 : logProfile g 1 = 0 := logProfile_eq_zero_of_one_le hsupp hg0 le_rfl
  have hLP_zero : ∀ x, 0 ≤ x → x ≤ Real.exp (-A - 1) → logProfile g x = 0 :=
    fun x _ hx => logProfile_eq_zero_of_lt hsupp (hx.trans_lt (Real.exp_lt_exp.mpr (by linarith)))
  have hcontP : ContinuousOn (polarCenterProfile (logProfile g)) (Icc 0 1) :=
    continuousOn_polarCenterProfile (by positivity) hLP_lip hLP1 (Real.exp_pos _) hLP_zero
  set φ : ℝ → ℝ := fun y => g y - Real.exp y * g y * Real.log (1 - Real.exp (2 * y)) / 2
  have heA0 : 0 ≤ Real.exp (-A) := (Real.exp_pos _).le
  have heA1 : Real.exp (-A) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hpt : ∀ y ∈ Icc (-A) 0,
      Real.exp y * polarCenterProfile (logProfile g) (Real.exp y) = φ y := by
    intro y hy
    by_cases hy0 : y = 0
    · subst hy0
      simp only [φ, Real.exp_zero, hLP1, polarCenterProfile, hg0, zero_div, zero_mul, mul_zero,
        sub_zero]
    · have hylt : y < 0 := lt_of_le_of_ne hy.2 hy0
      have hexp : 0 < Real.exp y := Real.exp_pos y
      have hlp : logProfile g (Real.exp y) = g y := by
        rw [logProfile, if_pos hexp, Real.log_exp]
      have hsq : Real.exp y ^ 2 = Real.exp (2 * y) := by
        rw [sq, ← Real.exp_add]; congr 1; ring
      dsimp only [polarCenterProfile, φ]
      rw [hlp, hsq]
      field_simp [hexp.ne']
  have hcontφ : ContinuousOn φ (Icc (-A) 0) := by
    refine (ContinuousOn.mul Real.continuous_exp.continuousOn
      (hcontP.comp Real.continuous_exp.continuousOn fun y hy =>
        ⟨(Real.exp_pos y).le, Real.exp_le_one_iff.mpr hy.2⟩)).congr ?_
    intro y hy
    exact (hpt y hy).symm
  have hsuppφ : Function.support φ ⊆ Icc (-A) 0 := by
    intro y hy
    by_contra hny
    apply hy
    dsimp only [φ]
    rw [hsupp y hny]
    ring
  have hintφ : Integrable φ :=
    (integrableOn_iff_integrable_of_support_subset hsuppφ).mp hcontφ.integrableOn_Icc
  refine ⟨?_, hintφ⟩
  have hI1 : IntervalIntegrable (polarCenterProfile (logProfile g)) volume 0 (Real.exp (-A)) :=
    (hcontP.mono fun x hx => by
      rw [uIcc_of_le heA0] at hx; exact ⟨hx.1, hx.2.trans heA1⟩).intervalIntegrable
  have hI2 : IntervalIntegrable (polarCenterProfile (logProfile g)) volume (Real.exp (-A)) 1 :=
    (hcontP.mono fun x hx => by
      rw [uIcc_of_le heA1] at hx; exact ⟨heA0.trans hx.1, hx.2⟩).intervalIntegrable
  rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
  have hzero1 : ∫ x in (0 : ℝ)..Real.exp (-A), polarCenterProfile (logProfile g) x = 0 := by
    rw [intervalIntegral.integral_of_le heA0, integral_Ioc_eq_integral_Ioo,
      ← integral_indicator measurableSet_Ioo]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Ioo 0 (Real.exp (-A))
    · rw [indicator_of_mem hx]
      have hlp0 : logProfile g x = 0 := logProfile_eq_zero_of_lt hsupp hx.2
      simp only [polarCenterProfile, hlp0, zero_div, zero_mul, sub_zero, Pi.zero_apply]
    · simp only [indicator_of_notMem hx, Pi.zero_apply]
  rw [hzero1, zero_add]
  let P_ext : ℝ → ℝ := fun x => polarCenterProfile (logProfile g) (max 0 (min x 1))
  have hcont_ext : Continuous P_ext := by
    rw [← continuousOn_univ]
    exact hcontP.comp (continuous_const.max (continuous_id.min continuous_const)).continuousOn
      fun x _ => ⟨le_max_left _ _, max_le zero_le_one (min_le_right _ _)⟩
  have hP_eq_I2 : ∫ x in Real.exp (-A)..1, polarCenterProfile (logProfile g) x =
      ∫ x in Real.exp (-A)..Real.exp 0, P_ext x := by
    rw [Real.exp_zero]
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [uIcc_of_le heA1] at hx
    dsimp only [P_ext]
    rw [min_eq_left hx.2, max_eq_right (heA0.trans hx.1)]
  rw [hP_eq_I2]
  have hsub := intervalIntegral.integral_deriv_smul_comp (a := -A) (b := 0) (f := Real.exp)
    (f' := Real.exp) (g := P_ext) (fun y _ => Real.hasDerivAt_exp y)
    Real.continuous_exp.continuousOn hcont_ext
  rw [← hsub]
  have hcongr : ∫ y in (-A)..0, Real.exp y • (P_ext ∘ Real.exp) y =
      ∫ y in (-A)..0, φ y := by
    refine intervalIntegral.integral_congr fun y hy => ?_
    rw [uIcc_of_le (by linarith)] at hy
    simp only [Function.comp_apply, smul_eq_mul, P_ext]
    rw [min_eq_left (Real.exp_le_one_iff.mpr hy.2), max_eq_right (Real.exp_pos y).le]
    exact hpt y hy
  rw [hcongr, intervalIntegral.integral_of_le (by linarith), ← integral_Icc_eq_integral_Ioc,
    setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => by
      dsimp only [φ]; rw [hsupp y hy]; ring]

private lemma finitePrimeTerminalMean_logProfile_eq {g : ℝ → ℝ} {A : ℝ}
    (hg : ContDiff ℝ 2 g) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Icc (-A) 0 → g y = 0) :
    (finitePrimeTerminalMean (logProfile g) ⌈1 / Real.exp (-A - 1)⌉₊ =
        ∫ y, Real.exp y * g y * Chebyshev.psi (Real.exp (-y))) ∧
      Integrable (fun y => Real.exp y * g y * Chebyshev.psi (Real.exp (-y))) := by
  have hg0 : g 0 = 0 := vanish_zero_of_window_support hg.continuous hsupp
  have hcontLP : Continuous (logProfile g) := by
    have h := Complex.continuous_re.comp (continuous_horizonProfile hg.continuous hsupp 1)
    refine h.congr fun x => ?_
    simp only [Function.comp_apply, ← logProfile_eq_horizonProfile, Complex.ofReal_re]
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hsupp
  have hint_eg : Integrable (fun y => Real.exp y * g y) :=
    (Real.continuous_exp.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left
  have hk_eq : ∀ k : ℕ, 1 ≤ k →
      ∫ x in (0 : ℝ)..(1 / (k : ℝ)), logProfile g x =
        ∫ y, (Iic (-Real.log (k : ℝ))).indicator (fun y => Real.exp y * g y) y := by
    intro k hk
    have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
    have h1k_pos : 0 < 1 / (k : ℝ) := by positivity
    have hexp_log : Real.exp (-Real.log (k : ℝ)) = 1 / (k : ℝ) := by
      rw [Real.exp_neg, Real.exp_log hk0, one_div]
    rcases lt_or_ge (-Real.log (k : ℝ)) (-A) with hlt | hge
    · have h1k_lt : 1 / (k : ℝ) < Real.exp (-A) := by
        rw [← hexp_log]; exact Real.exp_lt_exp.mpr hlt
      have hL : ∫ x in (0 : ℝ)..(1 / (k : ℝ)), logProfile g x = 0 := by
        rw [intervalIntegral.integral_of_le h1k_pos.le, ← integral_indicator measurableSet_Ioc]
        refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ Ioc 0 (1 / (k : ℝ))
        · simp only [indicator_of_mem hx, logProfile_eq_zero_of_lt hsupp (hx.2.trans_lt h1k_lt),
            Pi.zero_apply]
        · simp only [indicator_of_notMem hx, Pi.zero_apply]
      have hR : ∫ y, (Iic (-Real.log (k : ℝ))).indicator (fun y => Real.exp y * g y) y = 0 := by
        refine integral_eq_zero_of_ae (Eventually.of_forall fun y => ?_)
        by_cases hy : y ∈ Iic (-Real.log (k : ℝ))
        · simp only [indicator_of_mem hy, hsupp y fun hm => by linarith [mem_Iic.mp hy, hm.1],
            mul_zero, Pi.zero_apply]
        · simp only [indicator_of_notMem hy, Pi.zero_apply]
      rw [hL, hR]
    · have heA_le : Real.exp (-A) ≤ 1 / (k : ℝ) := by
        rw [← hexp_log]; exact Real.exp_le_exp.mpr hge
      have hI1 : IntervalIntegrable (logProfile g) volume 0 (Real.exp (-A)) :=
        hcontLP.intervalIntegrable _ _
      have hI2 : IntervalIntegrable (logProfile g) volume (Real.exp (-A)) (1 / (k : ℝ)) :=
        hcontLP.intervalIntegrable _ _
      rw [← intervalIntegral.integral_add_adjacent_intervals hI1 hI2]
      have hzero1 : ∫ x in (0 : ℝ)..Real.exp (-A), logProfile g x = 0 := by
        rw [intervalIntegral.integral_of_le (Real.exp_pos _).le, integral_Ioc_eq_integral_Ioo,
          ← integral_indicator measurableSet_Ioo]
        refine integral_eq_zero_of_ae (Eventually.of_forall fun x => ?_)
        by_cases hx : x ∈ Ioo 0 (Real.exp (-A))
        · simp only [indicator_of_mem hx, logProfile_eq_zero_of_lt hsupp hx.2, Pi.zero_apply]
        · simp only [indicator_of_notMem hx, Pi.zero_apply]
      rw [hzero1, zero_add, ← hexp_log]
      have hsub := intervalIntegral.integral_deriv_smul_comp (a := -A) (b := -Real.log (k : ℝ))
        (f := Real.exp) (f' := Real.exp) (g := logProfile g) (fun y _ => Real.hasDerivAt_exp y)
        Real.continuous_exp.continuousOn hcontLP
      rw [← hsub]
      have hcongr : ∫ y in (-A)..(-Real.log (k : ℝ)), Real.exp y • (logProfile g ∘ Real.exp) y =
          ∫ y in (-A)..(-Real.log (k : ℝ)), Real.exp y * g y := by
        refine intervalIntegral.integral_congr fun y _ => ?_
        simp only [Function.comp_apply, smul_eq_mul, logProfile, if_pos (Real.exp_pos y),
          Real.log_exp]
      rw [hcongr, intervalIntegral.integral_of_le hge, ← integral_Icc_eq_integral_Ioc,
        ← integral_indicator measurableSet_Icc]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      by_cases hy : y ∈ Iic (-Real.log (k : ℝ))
      · by_cases hyA : -A ≤ y
        · rw [indicator_of_mem (mem_Icc.mpr ⟨hyA, mem_Iic.mp hy⟩), indicator_of_mem hy]
        · rw [indicator_of_notMem fun hm => hyA hm.1, indicator_of_mem hy,
            hsupp y fun hm => hyA hm.1, mul_zero]
      · rw [indicator_of_notMem fun hm => hy (mem_Iic.mpr hm.2), indicator_of_notMem hy]
  set K : ℕ := ⌈1 / Real.exp (-A - 1)⌉₊
  have hterm_int : ∀ k ∈ Finset.Icc 1 K, Integrable fun y =>
      (ArithmeticFunction.vonMangoldt k : ℝ) *
        (Iic (-Real.log (k : ℝ))).indicator (fun y => Real.exp y * g y) y :=
    fun k _ => (hint_eg.indicator measurableSet_Iic).const_mul _
  have hpt_sum : ∀ y : ℝ,
      (∑ k ∈ Finset.Icc 1 K, (ArithmeticFunction.vonMangoldt k : ℝ) *
          (Iic (-Real.log (k : ℝ))).indicator (fun y => Real.exp y * g y) y) =
        Real.exp y * g y * Chebyshev.psi (Real.exp (-y)) := by
    intro y
    by_cases hy : y ∈ Icc (-A) 0
    · by_cases hy0 : y = 0
      · subst hy0
        have hzero_ind : ∀ k ∈ Finset.Icc 1 K,
            (Iic (-Real.log (k : ℝ))).indicator (fun y => Real.exp y * g y) 0 = 0 := by
          intro k _
          by_cases hk0 : 0 ∈ Iic (-Real.log (k : ℝ))
          · rw [indicator_of_mem hk0, hg0, mul_zero]
          · exact indicator_of_notMem hk0 _
        rw [hg0, mul_zero, zero_mul]
        exact Finset.sum_eq_zero fun k hk => by rw [hzero_ind k hk, mul_zero]
      · have hylt : y < 0 := lt_of_le_of_ne hy.2 hy0
        have hsum_ind : (∑ k ∈ Finset.Icc 1 K, (ArithmeticFunction.vonMangoldt k : ℝ) *
              (Iic (-Real.log (k : ℝ))).indicator (fun y => Real.exp y * g y) y) =
            Real.exp y * g y * ∑ k ∈ (Finset.Icc 1 K).filter (fun k : ℕ => y ≤ -Real.log (k : ℝ)),
              (ArithmeticFunction.vonMangoldt k : ℝ) := by
          rw [Finset.mul_sum, Finset.sum_filter]
          refine Finset.sum_congr rfl fun k _ => ?_
          by_cases hky : y ≤ -Real.log (k : ℝ)
          · rw [indicator_of_mem (mem_Iic.mpr hky), if_pos hky]; ring
          · rw [indicator_of_notMem (fun hm => hky (mem_Iic.mp hm)), if_neg hky, mul_zero]
        rw [hsum_ind]
        congr 1
        unfold Chebyshev.psi
        congr 1
        ext k
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
        constructor
        · rintro ⟨⟨hk1, _⟩, hky⟩
          have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
          have hlog : Real.log (k : ℝ) ≤ -y := by linarith
          have hke : (k : ℝ) ≤ Real.exp (-y) := (Real.log_le_iff_le_exp hk0).mp hlog
          exact ⟨hk1, (Nat.le_floor_iff (Real.exp_pos (-y)).le).mpr hke⟩
        · rintro ⟨hk0, hkf⟩
          have hk1 : 1 ≤ k := hk0
          have hkpos : (0 : ℝ) < k := by exact_mod_cast hk1
          have hke : (k : ℝ) ≤ Real.exp (-y) := (Nat.le_floor_iff (Real.exp_pos (-y)).le).mp hkf
          have hlog : Real.log (k : ℝ) ≤ -y := (Real.log_le_iff_le_exp hkpos).mpr hke
          have heA1 : Real.exp (-y) ≤ 1 / Real.exp (-A - 1) := by
            rw [one_div, ← Real.exp_neg, show -(-A - 1) = A + 1 by ring]
            exact Real.exp_le_exp.mpr (by linarith [hy.1])
          have hkK_real : (k : ℝ) ≤ (K : ℝ) :=
            (hke.trans heA1).trans (Nat.le_ceil _)
          exact ⟨⟨hk1, by exact_mod_cast hkK_real⟩, by linarith⟩
    · simp only [hsupp y hy, mul_zero, zero_mul]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hky : y ∈ Iic (-Real.log (k : ℝ))
      · rw [indicator_of_mem hky, hsupp y hy, mul_zero, mul_zero]
      · rw [indicator_of_notMem hky, mul_zero]
  have hint_psi : Integrable (fun y => Real.exp y * g y * Chebyshev.psi (Real.exp (-y))) :=
    (integrable_finsetSum (Finset.Icc 1 K) hterm_int).congr (Eventually.of_forall hpt_sum)
  refine ⟨?_, hint_psi⟩
  unfold finitePrimeTerminalMean
  have hsum_rw : (∑ k ∈ Finset.Icc 1 K, (ArithmeticFunction.vonMangoldt k : ℝ) *
        ∫ x in (0 : ℝ)..(1 / (k : ℝ)), logProfile g x) =
      ∑ k ∈ Finset.Icc 1 K, ∫ y, (ArithmeticFunction.vonMangoldt k : ℝ) *
        (Iic (-Real.log (k : ℝ))).indicator (fun y => Real.exp y * g y) y := by
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [hk_eq k (Finset.mem_Icc.mp hk).1, integral_const_mul]
  rw [hsum_rw, ← integral_finsetSum (Finset.Icc 1 K) hterm_int]
  exact integral_congr_ae (Eventually.of_forall hpt_sum)

/-- **Exact logarithmic-variable representation of `generalTerminalPolarSource`.**
For every `0 ≤ A` and every `C²` test `g` supported in `[−A, 0]`, `generalTerminalPolarSource A g`
equals `splineAtom * ∫ g(y) terminalPolarKernel(y) dy`, with no dependence on `A`. -/
theorem generalTerminalPolarSource_eq_integral_terminalPolarKernel {g : ℝ → ℝ} {A : ℝ}
    (hg : ContDiff ℝ 2 g) (hA : 0 ≤ A) (hsupp : ∀ y, y ∉ Icc (-A) 0 → g y = 0) :
    generalTerminalPolarSource A g = splineAtom * ∫ y, g y * terminalPolarKernel y ∧
      Integrable (fun y => g y * terminalPolarKernel y) := by
  obtain ⟨hP, hintP⟩ := integral_polarCenterProfile_logProfile hg hA hsupp
  obtain ⟨hF, hintF⟩ := finitePrimeTerminalMean_logProfile_eq hg hA hsupp
  have hL := integral_logProfile hg hsupp hA
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hsupp
  have hintL : Integrable (fun y => Real.log (2 * Real.pi) * (Real.exp y * g y)) :=
    ((Real.continuous_exp.mul hg.continuous).integrable_of_hasCompactSupport hgc.mul_left).const_mul _
  have hker_eq : (fun y => g y * terminalPolarKernel y) = fun y =>
      (g y - Real.exp y * g y * Real.log (1 - Real.exp (2 * y)) / 2) -
        Real.log (2 * Real.pi) * (Real.exp y * g y) -
        Real.exp y * g y * Chebyshev.psi (Real.exp (-y)) := by
    funext y
    unfold terminalPolarKernel
    ring
  have hintK : Integrable (fun y => g y * terminalPolarKernel y) := by
    rw [hker_eq]
    exact (hintP.sub hintL).sub hintF
  refine ⟨?_, hintK⟩
  have h_int_eq : ∫ y, g y * terminalPolarKernel y =
      (∫ y, (g y - Real.exp y * g y * Real.log (1 - Real.exp (2 * y)) / 2)) -
        Real.log (2 * Real.pi) * (∫ y, Real.exp y * g y) -
        ∫ y, Real.exp y * g y * Chebyshev.psi (Real.exp (-y)) := by
    have h1 := integral_sub (hintP.sub hintL) hintF
    have h2 := integral_sub hintP hintL
    have h3 := integral_const_mul (Real.log (2 * Real.pi)) (fun y => Real.exp y * g y)
    dsimp only [Pi.sub_apply] at h1 h2
    rw [hker_eq, h1, h2, h3]
  unfold generalTerminalPolarSource splineAtom
  rw [hP, hL, hF, ← h_int_eq]

/-- Additivity of `generalTerminalPolarSource A` on `C²` tests supported in `[−A, 0]`. -/
theorem generalTerminalPolarSource_add {g₁ g₂ : ℝ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hg₁ : ContDiff ℝ 2 g₁) (hsupp₁ : ∀ y, y ∉ Icc (-A) 0 → g₁ y = 0)
    (hg₂ : ContDiff ℝ 2 g₂) (hsupp₂ : ∀ y, y ∉ Icc (-A) 0 → g₂ y = 0) :
    generalTerminalPolarSource A (fun y => g₁ y + g₂ y) =
      generalTerminalPolarSource A g₁ + generalTerminalPolarSource A g₂ := by
  have hsupp12 : ∀ y, y ∉ Icc (-A) 0 → g₁ y + g₂ y = 0 := fun y hy => by
    rw [hsupp₁ y hy, hsupp₂ y hy, add_zero]
  obtain ⟨he₁, hi₁⟩ := generalTerminalPolarSource_eq_integral_terminalPolarKernel hg₁ hA hsupp₁
  obtain ⟨he₂, hi₂⟩ := generalTerminalPolarSource_eq_integral_terminalPolarKernel hg₂ hA hsupp₂
  obtain ⟨he12, _⟩ :=
    generalTerminalPolarSource_eq_integral_terminalPolarKernel (hg₁.add hg₂) hA hsupp12
  rw [he12, he₁, he₂, ← mul_add, ← integral_add hi₁ hi₂]
  congr 2
  funext y
  ring

/-! ### 2. Deep-tail bound for tests vanishing above `−b` -/

private lemma abs_terminalPolarKernel_le_nine {y : ℝ} (hy : y ≤ -2) :
    |terminalPolarKernel y| ≤ 9 := by
  have he2y_pos : 0 < Real.exp (2 * y) := Real.exp_pos _
  have he2y_le : Real.exp (2 * y) ≤ 1 / 2 := by
    have h4 : (2 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp 4]
    have hle : Real.exp (2 * y) ≤ Real.exp (-4) := Real.exp_le_exp.mpr (by linarith)
    rw [Real.exp_neg, ← one_div] at hle
    exact hle.trans (one_div_le_one_div_of_le (by norm_num) h4)
  have h1sub_pos : 0 < 1 - Real.exp (2 * y) := by linarith
  have hlog_le : |Real.log (1 - Real.exp (2 * y))| ≤ 1 := by
    rw [abs_of_neg (Real.log_neg h1sub_pos (by linarith))]
    have hinv : 1 / (1 - Real.exp (2 * y)) ≤ 2 := by
      rw [div_le_iff₀ h1sub_pos]; linarith
    have hlog2 : Real.log (1 / (1 - Real.exp (2 * y))) ≤ 1 := by
      exact (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
    rwa [one_div, Real.log_inv] at hlog2
  have hey_pos : 0 < Real.exp y := Real.exp_pos y
  have hey_le : Real.exp y ≤ 1 / 2 := by
    have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
    have hle : Real.exp y ≤ Real.exp (-2) := Real.exp_le_exp.mpr hy
    rw [Real.exp_neg, ← one_div] at hle
    exact hle.trans (one_div_le_one_div_of_le (by norm_num) h2)
  have hlog2pi_pos : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hlog2pi_le : Real.log (2 * Real.pi) ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by positivity)]
    have h1 := Real.pi_lt_d2
    have h2 : (7.38 : ℝ) ≤ Real.exp 2 := by
      have := Real.exp_one_gt_d9
      have h3 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith
    linarith
  have hpsi0 := Chebyshev.psi_nonneg (Real.exp (-y))
  have hpsi_le := Chebyshev.psi_le_const_mul_self (Real.exp_pos (-y)).le
  have hlog4 : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have hprod_psi : Real.exp y * Chebyshev.psi (Real.exp (-y)) ≤ 6 := by
    have h1 : Chebyshev.psi (Real.exp (-y)) ≤ 6 * Real.exp (-y) := by
      nlinarith [Real.exp_pos (-y)]
    have h2 := mul_le_mul_of_nonneg_left h1 hey_pos.le
    have hec : Real.exp y * (6 * Real.exp (-y)) = 6 := by
      rw [mul_left_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]
    linarith
  have ht1 : |Real.exp y * Real.log (1 - Real.exp (2 * y)) / 2| ≤ 1 := by
    rw [abs_div, abs_mul, abs_of_pos hey_pos, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    nlinarith
  have ht2 : |Real.log (2 * Real.pi) * Real.exp y| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg hlog2pi_pos, abs_of_pos hey_pos]
    nlinarith
  have ht3 : |Real.exp y * Chebyshev.psi (Real.exp (-y))| ≤ 6 := by
    rw [abs_of_nonneg (mul_nonneg hey_pos.le hpsi0)]
    exact hprod_psi
  unfold terminalPolarKernel
  have htri : |1 - Real.exp y * Real.log (1 - Real.exp (2 * y)) / 2 -
        Real.log (2 * Real.pi) * Real.exp y - Real.exp y * Chebyshev.psi (Real.exp (-y))| ≤
      (1 : ℝ) + |Real.exp y * Real.log (1 - Real.exp (2 * y)) / 2| +
        |Real.log (2 * Real.pi) * Real.exp y| +
        |Real.exp y * Chebyshev.psi (Real.exp (-y))| := by
    have hs1 := abs_sub (1 - Real.exp y * Real.log (1 - Real.exp (2 * y)) / 2 -
      Real.log (2 * Real.pi) * Real.exp y) (Real.exp y * Chebyshev.psi (Real.exp (-y)))
    have hs2 := abs_sub (1 - Real.exp y * Real.log (1 - Real.exp (2 * y)) / 2)
      (Real.log (2 * Real.pi) * Real.exp y)
    have hs3 := abs_sub (1 : ℝ) (Real.exp y * Real.log (1 - Real.exp (2 * y)) / 2)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1)] at hs3
    linarith
  linarith

private lemma abs_halfMoment_sq_le_shifted_exponentialMass {F : ℝ → ℝ} {b : ℝ}
    (hF : Continuous F) (hFc : HasCompactSupport F) (hb : 0 ≤ b)
    (hFs : ∀ y, -b < y → F y = 0) :
    (∫ y, |F y| * Real.exp (-(y / 2))) ^ 2 ≤ Real.exp (-7 * b) * exponentialMass 8 F := by
  let B : ℝ → ℝ := (Iic (-b)).indicator fun y => Real.exp (7 * y)
  have iB : Integrable B :=
    (integrable_indicator_iff measurableSet_Iic).mpr
      (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 7) (-b))
  have hnormB : ∫ y, B y = Real.exp (-7 * b) / 7 := by
    dsimp only [B]
    rw [integral_indicator measurableSet_Iic, integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 7) (-b)]
    congr 1; ring
  have hF2c : HasCompactSupport (fun y => F y ^ 2) := by
    rw [hasCompactSupport_iff_eventuallyEq] at hFc ⊢
    exact hFc.mono fun y hy => by change F y = 0 at hy; change F y ^ 2 = 0; rw [hy]; norm_num
  have iE : Integrable fun y => Real.exp (-(8 * y)) * F y ^ 2 :=
    ((by fun_prop : Continuous fun y => Real.exp (-(8 * y))).mul (hF.pow 2)).integrable_of_hasCompactSupport
      hF2c.mul_left
  have hFabsc : HasCompactSupport (fun y => |F y|) := hFc.comp_left abs_zero
  have igq : Integrable fun y => |F y| * Real.exp (-(y / 2)) :=
    (hF.abs.mul (by fun_prop)).integrable_of_hasCompactSupport hFabsc.mul_right
  set M := exponentialMass 8 F
  have hM0 : 0 ≤ M := exponentialMass_nonneg 8 F
  have hquad : ∀ t : ℝ, 0 ≤ M * (t * t) + (2 * ∫ y, |F y| * Real.exp (-(y / 2))) * t + ∫ y, B y := by
    intro t
    have hpt : ∀ y, 0 ≤ (t * t) * (Real.exp (-(8 * y)) * F y ^ 2) +
        2 * t * (|F y| * Real.exp (-(y / 2))) + B y := by
      intro y
      by_cases hy : y ≤ -b
      · dsimp only [B]
        rw [indicator_of_mem (mem_Iic.mpr hy)]
        have hs := sq_nonneg (t * Real.exp (-4 * y) * |F y| + Real.exp (7 * y / 2))
        have he1 : Real.exp (-4 * y) ^ 2 = Real.exp (-(8 * y)) := by
          rw [sq, ← Real.exp_add]; congr 1; ring
        have he2 : Real.exp (7 * y / 2) ^ 2 = Real.exp (7 * y) := by
          rw [sq, ← Real.exp_add]; congr 1; ring
        have hec : Real.exp (-4 * y) * Real.exp (7 * y / 2) = Real.exp (-(y / 2)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [add_sq, mul_pow, mul_pow, sq_abs, he1, he2] at hs
        have hc : 2 * (t * Real.exp (-4 * y) * |F y|) * Real.exp (7 * y / 2) =
            2 * t * (|F y| * Real.exp (-(y / 2))) := by
          linear_combination (2 * t * |F y|) * hec
        linarith only [hs, hc]
      · push Not at hy
        dsimp only [B]
        rw [indicator_of_notMem (fun hm => not_lt.mpr (mem_Iic.mp hm) hy), hFs y hy, abs_zero]
        norm_num
    have hint := integral_nonneg fun y => hpt y
    rw [integral_add ((iE.const_mul (t * t)).add (igq.const_mul (2 * t))) iB,
      integral_add (iE.const_mul (t * t)) (igq.const_mul (2 * t)),
      integral_const_mul, integral_const_mul] at hint
    change 0 ≤ (t * t) * M + 2 * t * (∫ y, |F y| * Real.exp (-(y / 2))) + ∫ y, B y at hint
    linarith only [hint]
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  rw [hnormB] at hd
  have h1 : (∫ y, |F y| * Real.exp (-(y / 2))) ^ 2 ≤ (Real.exp (-7 * b) / 7) * M := by
    nlinarith only [hd]
  have hdiv : Real.exp (-7 * b) / 7 ≤ Real.exp (-7 * b) :=
    div_le_self (Real.exp_pos _).le (by norm_num)
  exact h1.trans (mul_le_mul_of_nonneg_right hdiv hM0)

/-- **Deep-tail polar source bound.** If `g` is `C²`, supported in `[−A, 0]`, and vanishes above
`−b` (`b ≥ 2`), then `(generalTerminalPolarSource A g / splineAtom)² ≤ 81 e^{−7b} M₈(halfWeight g)`. -/
theorem sq_generalTerminalPolarSource_deep_le {g : ℝ → ℝ} {A b : ℝ} (hA : 0 ≤ A) (hb : 2 ≤ b)
    (hg : ContDiff ℝ 2 g) (hsupp : ∀ y, y ∉ Icc (-A) 0 → g y = 0)
    (hdeep : ∀ y, -b < y → g y = 0) :
    (generalTerminalPolarSource A g / splineAtom) ^ 2 ≤
      81 * Real.exp (-7 * b) * exponentialMass 8 (halfWeight g) := by
  obtain ⟨heq, hintK⟩ := generalTerminalPolarSource_eq_integral_terminalPolarKernel hg hA hsupp
  have hκ : splineAtom ≠ 0 := splineAtom_pos.ne'
  have hdiv : generalTerminalPolarSource A g / splineAtom = ∫ y, g y * terminalPolarKernel y := by
    rw [heq, mul_div_cancel_left₀ _ hκ]
  rw [hdiv]
  set F := halfWeight g
  have hF : Continuous F := Real.continuous_exp.comp (continuous_id.div_const 2) |>.mul hg.continuous
  have hgc : HasCompactSupport g := HasCompactSupport.intro isCompact_Icc hsupp
  have hFc : HasCompactSupport F := hgc.mul_left
  have hFs : ∀ y, -b < y → F y = 0 := fun y hy => by
    simp only [F, halfWeight, hdeep y hy, mul_zero]
  have hFabsc : HasCompactSupport (fun y => |F y|) := hFc.comp_left abs_zero
  have igq : Integrable fun y => |F y| * Real.exp (-(y / 2)) :=
    (hF.abs.mul (by fun_prop)).integrable_of_hasCompactSupport hFabsc.mul_right
  have hpt : ∀ y, ‖g y * terminalPolarKernel y‖ ≤ 9 * (|F y| * Real.exp (-(y / 2))) := by
    intro y
    rw [Real.norm_eq_abs, abs_mul]
    by_cases hy : y ≤ -b
    · have hk9 := abs_terminalPolarKernel_le_nine (hy.trans (by linarith))
      have hgF : |g y| = |F y| * Real.exp (-(y / 2)) := by
        have hid : g y = F y * Real.exp (-(y / 2)) := by
          dsimp only [F, halfWeight]
          rw [mul_right_comm, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
        rw [hid, abs_mul, abs_of_pos (Real.exp_pos _)]
      rw [hgF]
      exact (mul_le_mul_of_nonneg_left hk9
        (mul_nonneg (abs_nonneg (F y)) (Real.exp_pos _).le)).trans_eq (mul_comm _ _)
    · push Not at hy
      rw [hdeep y hy, hFs y hy, abs_zero, zero_mul, zero_mul, mul_zero]
  have habs : |∫ y, g y * terminalPolarKernel y| ≤ 9 * ∫ y, |F y| * Real.exp (-(y / 2)) := by
    have h := norm_integral_le_of_norm_le (igq.const_mul 9) (Eventually.of_forall hpt)
    rw [Real.norm_eq_abs, integral_const_mul] at h
    exact h
  have hsq1 : (∫ y, g y * terminalPolarKernel y) ^ 2 ≤
      81 * (∫ y, |F y| * Real.exp (-(y / 2))) ^ 2 := by
    have hp := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rw [sq_abs] at hp
    linarith [hp]
  exact hsq1.trans (by
    have hm := abs_halfMoment_sq_le_shifted_exponentialMass hF hFc (by linarith) hFs
    nlinarith [hm])

/-! ### 3. Top-collar pole-cross compression and discrepancy bound -/

private lemma measurable_chebyshevPsi : Measurable Chebyshev.psi := by
  have hmono : Monotone Chebyshev.psi := by
    intro x y hxy
    rcases lt_or_ge x 0 with hx | hx
    · have hf0 : ⌊x⌋₊ = 0 := Nat.floor_of_nonpos hx.le
      unfold Chebyshev.psi
      rw [hf0]
      simp only [Finset.Ioc_self, Finset.sum_empty]
      exact Chebyshev.psi_nonneg y
    · unfold Chebyshev.psi
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun n hn => Finset.mem_Ioc.mpr
          ⟨(Finset.mem_Ioc.mp hn).1, (Finset.mem_Ioc.mp hn).2.trans (Nat.floor_mono hxy)⟩)
        fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg
  exact hmono.measurable

private lemma measurable_ccmReciprocalMangoldtError : Measurable ccmReciprocalMangoldtError := by
  have hmono : Monotone ccmReciprocalMangoldtCumulative := by
    intro x y hxy
    rcases lt_or_ge x 0 with hx | hx
    · have hf0 : ⌊x⌋₊ = 0 := Nat.floor_of_nonpos hx.le
      unfold ccmReciprocalMangoldtCumulative
      rw [hf0]
      have hempty : Finset.Icc 2 0 = ∅ := by ext n; simp
      rw [hempty, Finset.sum_empty]
      exact Finset.sum_nonneg fun _ _ =>
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
    · unfold ccmReciprocalMangoldtCumulative
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (fun n hn => Finset.mem_Icc.mpr
          ⟨(Finset.mem_Icc.mp hn).1, (Finset.mem_Icc.mp hn).2.trans (Nat.floor_mono hxy)⟩)
        fun _ _ _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  unfold ccmReciprocalMangoldtError
  exact (hmono.measurable.comp Real.continuous_exp.measurable).sub measurable_id

private lemma measurable_poleCrossProfile (s : ℝ) : Measurable (poleCrossProfile s) := by
  unfold poleCrossProfile ccmGammaPolarBoundary
  have m1 : Measurable fun x : ℝ => Real.exp (x / 2) := (by fun_prop : Continuous _).measurable
  have m2 : Measurable fun x : ℝ => -(1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (s - x)))) -
      Real.log (1 - Real.exp (-(s + x))) +
      (1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (s + x)))) := by
    have c1 : Measurable fun x : ℝ => 1 - Real.exp (-(2 * (s - x))) :=
      (by fun_prop : Continuous _).measurable
    have c2 : Measurable fun x : ℝ => 1 - Real.exp (-(s + x)) :=
      (by fun_prop : Continuous _).measurable
    have c3 : Measurable fun x : ℝ => 1 - Real.exp (-(2 * (s + x))) :=
      (by fun_prop : Continuous _).measurable
    exact ((measurable_const.mul c1.log).sub c2.log).add (measurable_const.mul c3.log)
  have m3 : Measurable fun x : ℝ => Chebyshev.psi (Real.exp (s - x)) - Real.exp (s - x) :=
    (measurable_chebyshevPsi.comp (by fun_prop : Continuous fun x => Real.exp (s - x)).measurable).sub
      (by fun_prop : Continuous _).measurable
  have m4 : Measurable fun x : ℝ => ccmReciprocalMangoldtError (s + x) :=
    measurable_ccmReciprocalMangoldtError.comp (by fun_prop : Continuous _).measurable
  have m5 : Measurable fun x : ℝ =>
      (-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) * Real.exp (x / 2) -
        Real.exp (-s) * Real.exp (-(x / 2)) := (by fun_prop : Continuous _).measurable
  exact (m1.mul ((m2.sub m3).sub m4)).add m5

private lemma fullZeroForm_eq_weilQuad_of_cont {F : ℝ → ℝ} (hF : Continuous F)
    (hFc : HasCompactSupport F) : fullZeroForm F = weilQuad F := by
  have h1 : markovEnergy (fun u => (F u : ℂ)) = weilQuad F -
      (weilPoleTerm (EF.weilTest (fun u => (F u : ℂ)) (fun u => (F u : ℂ)))).re := by
    unfold markovEnergy weilQuad
    rw [Complex.sub_re]
  have h2 := re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq hF hFc
  unfold fullZeroForm
  rw [h1, h2]
  unfold oddPoleMoment evenPoleMoment coshHalfMoment sinhHalfMoment
  ring

private lemma abs_neg_mul_log_one_sub_exp_two_mul_le {s y : ℝ} (hs : 1 ≤ s) (hys : -s ≤ y)
    (hy0 : y < 0) :
    (-y) * |Real.log (1 - Real.exp (2 * y))| ≤ 2 * s ^ 2 + s + 1 := by
  set t : ℝ := -2 * y
  have ht_pos : 0 < t := by dsimp only [t]; linarith
  have ht_le : t ≤ 2 * s := by dsimp only [t]; linarith
  have he2y_eq : Real.exp (2 * y) = Real.exp (-t) := by congr 1; dsimp only [t]; ring
  have h1sub_pos : 0 < 1 - Real.exp (2 * y) := by
    have : Real.exp (2 * y) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    linarith
  have h1sub_lt : 1 - Real.exp (2 * y) < 1 := by linarith [Real.exp_pos (2 * y)]
  have hlower : Real.exp (-t) * t ≤ 1 - Real.exp (2 * y) := by
    have hexp : t ≤ Real.exp t - 1 := by linarith [Real.add_one_le_exp t]
    have hm := mul_le_mul_of_nonneg_left hexp (Real.exp_pos (-t)).le
    have hid : Real.exp (-t) * (Real.exp t - 1) = 1 - Real.exp (2 * y) := by
      rw [mul_sub, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one, he2y_eq]
    linarith
  have hlog_le : |Real.log (1 - Real.exp (2 * y))| ≤ t - Real.log t := by
    rw [abs_of_neg (Real.log_neg h1sub_pos h1sub_lt)]
    have hle := Real.log_le_log (mul_pos (Real.exp_pos (-t)) ht_pos) hlower
    rw [Real.log_mul (Real.exp_pos (-t)).ne' ht_pos.ne', Real.log_exp] at hle
    linarith
  have hsq_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hneg_log : -Real.log t ≤ 2 / Real.sqrt t := by
    have hl_sqrt := Real.log_sqrt ht_pos.le
    have hsub := Real.log_le_sub_one_of_pos (one_div_pos.mpr hsq_pos)
    rw [one_div, Real.log_inv] at hsub
    rw [← one_div] at hsub
    linarith
  have ht_neg_log : t * (-Real.log t) ≤ t + 1 := by
    have hm := mul_le_mul_of_nonneg_left hneg_log ht_pos.le
    have hdiv : t * (2 / Real.sqrt t) = 2 * Real.sqrt t := by
      calc t * (2 / Real.sqrt t) = Real.sqrt t ^ 2 * (2 / Real.sqrt t) := by
            rw [Real.sq_sqrt ht_pos.le]
        _ = 2 * Real.sqrt t := by field_simp [hsq_pos.ne']
    have hamgm : 2 * Real.sqrt t ≤ t + 1 := by
      nlinarith [sq_nonneg (Real.sqrt t - 1), Real.sq_sqrt ht_pos.le]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hlog_le (by linarith : 0 ≤ -y)
  have hrewrite : (-y) * (t - Real.log t) = (-y) * t + (t * (-Real.log t)) / 2 := by
    dsimp only [t]; ring
  rw [hrewrite] at hmul
  have hyt : (-y) * t ≤ 2 * s ^ 2 := by dsimp only [t]; nlinarith [hys, hy0, hs]
  linarith

private lemma abs_log_one_sub_le_two_mul {u : ℝ} (hu0 : 0 < u) (hu : u ≤ 1 / 2) :
    |Real.log (1 - u)| ≤ 2 * u := by
  have h1 : 0 < 1 - u := by linarith
  rw [abs_of_neg (Real.log_neg h1 (by linarith))]
  have hinv : 1 / (1 - u) - 1 ≤ 2 * u := by
    rw [div_sub_one h1.ne', div_le_iff₀ h1]
    nlinarith
  have hlog := Real.log_le_sub_one_of_pos (one_div_pos.mpr h1)
  rw [one_div, Real.log_inv, ← one_div] at hlog
  linarith

/-- **Pole-cross compression on `C²` half-aperture window tests.** Given a sharp bound at aperture
`s ≥ 6` on smooth interior sources, shifting inward and mollifying transfers it to every `C²`
profile `H₁` vanishing outside `[−s/2, 0]`:
`(e^{−s/2} ∫ 1_{[−s,s]}(y+s) P_s(y+s) H₁(y) dy)² ≤ (κ₀ + C e^{−s/2}) Q(H₁)`. -/
theorem sq_poleCross_windowTest_le {s C_pole : ℝ} (hs : 6 ≤ s) (hCp : 0 ≤ C_pole)
    (hsharp : ∀ {F : ℝ → ℝ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F),
      tsupport F ⊆ Ioo (-s) s →
      (∫ x, (centralInterval s).indicator (poleCrossProfile s) x * F x) ^ 2 ≤
        Real.exp s * (poleSharpConstant + C_pole * Real.exp (-(s / 2))) * fullZeroForm F)
    {H₁ : ℝ → ℝ} (hH₁ : ContDiff ℝ 2 H₁) (hsupp₁ : ∀ y, y ∉ Icc (-(s / 2)) 0 → H₁ y = 0) :
    Integrable (fun y => (centralInterval s).indicator (poleCrossProfile s) (y + s) * H₁ y) ∧
      (Real.exp (-(s / 2)) *
          ∫ y, (centralInterval s).indicator (poleCrossProfile s) (y + s) * H₁ y) ^ 2 ≤
        (poleSharpConstant + C_pole * Real.exp (-(s / 2))) * weilQuad H₁ := by
  have hH₁0 : H₁ 0 = 0 := vanish_zero_of_window_support hH₁.continuous hsupp₁
  obtain ⟨B₁, L₁, hB₁0, hB₁, hL₁⟩ := exists_bound_and_lipschitz_of_window_support hH₁ hsupp₁
  have hH₁c : HasCompactSupport H₁ := HasCompactSupport.intro isCompact_Icc hsupp₁
  -- Step 1: fixed inward shift `0 < δ ≤ 1/5`, mollification limit `k → ∞`
  have hshift_bound : ∀ δ : ℝ, 0 < δ → δ ≤ 1 / 5 →
      (∫ y, (centralInterval s).indicator (poleCrossProfile s) (y + s) * H₁ (y + δ)) ^ 2 ≤
        Real.exp s * (poleSharpConstant + C_pole * Real.exp (-(s / 2))) * weilQuad H₁ := by
    intro δ hδ0 hδ5
    set G : ℝ → ℝ := fun x => H₁ (x - s + δ)
    have hG2 : ContDiff ℝ 2 G := hH₁.comp ((contDiff_id.sub contDiff_const).add contDiff_const)
    have hGc : HasCompactSupport G :=
      hH₁c.comp_homeomorph ((Homeomorph.subRight s).trans (Homeomorph.addRight δ))
    have hGv : ∀ x, s - δ < |x| → G x = 0 := by
      intro x hx
      refine hsupp₁ (x - s + δ) fun hm => ?_
      rcases lt_or_ge x 0 with hx0 | hx0
      · rw [abs_of_neg hx0] at hx; linarith [hm.1]
      · rw [abs_of_nonneg hx0] at hx; linarith [hm.2]
    have hGB : ∀ x, |G x| ≤ B₁ := fun x => hB₁ _
    -- fullZeroForm convergence of mollifications
    have hsm : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (smooth G k) := contDiff_top_smooth hG2.continuous hGc
    have hsc : ∀ k, HasCompactSupport (smooth G k) := smooth_compact hGc
    obtain ⟨fc, hfc⟩ : ∃ fc : C_c(ℝ, ℝ), (fc : ℝ → ℝ) = G := ⟨⟨⟨G, hG2.continuous⟩, hGc⟩, rfl⟩
    have hJ : IntegrableOn (fun x =>
        (ArchimedeanAnomaly.autocorr fc 0 - ArchimedeanAnomaly.autocorr fc x) *
          archLevySinhWeight x) (Ioi 0) := by
      rw [hfc]; exact integrableOn_biScaleLevyIntegrand hG2 hGc
    have hlimZ := re_weilFullFunctional_smooth_tendsto fc hJ
    rw [hfc] at hlimZ
    have hZ_tendsto : Tendsto (fun k => fullZeroForm (smooth G k)) atTop (𝓝 (weilQuad H₁)) := by
      have hGW : fullZeroForm G = weilQuad H₁ := by
        rw [fullZeroForm_eq_weilQuad_of_cont hG2.continuous hGc]
        have hGe : G = fun x => H₁ (x - (s - δ)) := by funext x; dsimp only [G]; ring_nf
        rw [hGe, weilQuad_comp_sub]
      rw [← hGW, fullZeroForm_eq_re_weilFullFunctional hG2.continuous hGc]
      exact hlimZ.congr fun k =>
        (fullZeroForm_eq_re_weilFullFunctional (hsm k).continuous (hsc k)).symm
    -- LHS integral convergence on compact interior interval `Icc (-(s - δ/2)) (s - δ/2)`
    set r : ℝ := s - δ / 2
    have hr_pos : 0 < r := by dsimp only [r]; linarith
    have hrs : r < s := by dsimp only [r]; linarith
    have hcont_gam : ContinuousOn (fun x => ccmGammaPolarBoundary (s - x) (s + x)) (Icc (-r) r) := by
      unfold ccmGammaPolarBoundary
      have hpos1 : ∀ x ∈ Icc (-r) r, 1 - Real.exp (-(2 * (s - x))) ≠ 0 := fun x hx =>
        (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by dsimp only [r] at hx; linarith [hx.2]))).ne'
      have hpos2 : ∀ x ∈ Icc (-r) r, 1 - Real.exp (-(s + x)) ≠ 0 := fun x hx =>
        (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by dsimp only [r] at hx; linarith [hx.1]))).ne'
      have hpos3 : ∀ x ∈ Icc (-r) r, 1 - Real.exp (-(2 * (s + x))) ≠ 0 := fun x hx =>
        (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by dsimp only [r] at hx; linarith [hx.1]))).ne'
      exact ((continuousOn_const.mul
        ((by fun_prop : Continuous fun x => 1 - Real.exp (-(2 * (s - x)))).continuousOn.log hpos1)).sub
        ((by fun_prop : Continuous fun x => 1 - Real.exp (-(s + x))).continuousOn.log hpos2)).add
        (continuousOn_const.mul
          ((by fun_prop : Continuous fun x => 1 - Real.exp (-(2 * (s + x)))).continuousOn.log hpos3))
    obtain ⟨Bg, hBg⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_gam
    set BP : ℝ := Real.exp s * (max Bg 0 + ((Real.log 4 + 4) * Real.exp (2 * s) + Real.exp (2 * s)) +
      (Real.log 4 + 5)) + (|Real.eulerMascheroniConstant| + |Real.log (2 * Real.pi)| + 1) * Real.exp s
    have hBP0 : 0 ≤ BP := by
      dsimp only [BP]
      have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
      positivity
    have hP_le : ∀ x ∈ Icc (-r) r, |poleCrossProfile s x| ≤ BP := by
      intro x hx
      have hsx1 : 0 ≤ s + x := by dsimp only [r] at hx; linarith [hx.1]
      have hsx2 : s - x ≤ 2 * s := by dsimp only [r] at hx; linarith [hx.1]
      have hex1 : Real.exp (x / 2) ≤ Real.exp s := Real.exp_le_exp.mpr (by dsimp only [r] at hx; linarith [hx.2])
      have hex2 : Real.exp (-(x / 2)) ≤ Real.exp s := Real.exp_le_exp.mpr (by dsimp only [r] at hx; linarith [hx.1])
      have hex3 : Real.exp (s - x) ≤ Real.exp (2 * s) := Real.exp_le_exp.mpr hsx2
      have hgam : |ccmGammaPolarBoundary (s - x) (s + x)| ≤ max Bg 0 :=
        (Real.norm_eq_abs _ ▸ hBg x hx).trans (le_max_left Bg 0)
      have hpsi : |Chebyshev.psi (Real.exp (s - x)) - Real.exp (s - x)| ≤
          (Real.log 4 + 4) * Real.exp (2 * s) + Real.exp (2 * s) := by
        have hp0 := Chebyshev.psi_nonneg (Real.exp (s - x))
        have hple := Chebyshev.psi_le_const_mul_self (Real.exp_pos (s - x)).le
        have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
        calc |Chebyshev.psi (Real.exp (s - x)) - Real.exp (s - x)|
            ≤ |Chebyshev.psi (Real.exp (s - x))| + |Real.exp (s - x)| := abs_sub _ _
          _ = Chebyshev.psi (Real.exp (s - x)) + Real.exp (s - x) := by
              rw [abs_of_nonneg hp0, abs_of_pos (Real.exp_pos _)]
          _ ≤ (Real.log 4 + 4) * Real.exp (s - x) + Real.exp (s - x) := by linarith
          _ ≤ (Real.log 4 + 4) * Real.exp (2 * s) + Real.exp (2 * s) :=
              add_le_add (mul_le_mul_of_nonneg_left hex3 (by positivity)) hex3
      have hmert := abs_ccmReciprocalMangoldtError_le hsx1
      have htail : |(-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) * Real.exp (x / 2) -
          Real.exp (-s) * Real.exp (-(x / 2))| ≤
          (|Real.eulerMascheroniConstant| + |Real.log (2 * Real.pi)| + 1) * Real.exp s := by
        have he_s : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have ht1 : |(-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) * Real.exp (x / 2)| ≤
            (|Real.eulerMascheroniConstant| + |Real.log (2 * Real.pi)|) * Real.exp s := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          have hc : |-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)| ≤
              |Real.eulerMascheroniConstant| + |Real.log (2 * Real.pi)| := by
            simpa [sub_eq_add_neg] using abs_add_le (-Real.eulerMascheroniConstant) (-Real.log (2 * Real.pi))
          exact mul_le_mul hc hex1 (Real.exp_pos _).le (by positivity)
        have ht2 : |Real.exp (-s) * Real.exp (-(x / 2))| ≤ Real.exp s := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
          nlinarith [Real.exp_pos (-(x / 2))]
        calc _ ≤ |(-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) * Real.exp (x / 2)| +
              |Real.exp (-s) * Real.exp (-(x / 2))| := abs_sub _ _
          _ ≤ _ := by linarith
      unfold poleCrossProfile
      have hmain : |Real.exp (x / 2) * (ccmGammaPolarBoundary (s - x) (s + x) -
            (Chebyshev.psi (Real.exp (s - x)) - Real.exp (s - x)) -
            ccmReciprocalMangoldtError (s + x))| ≤
          Real.exp s * (max Bg 0 + ((Real.log 4 + 4) * Real.exp (2 * s) + Real.exp (2 * s)) +
            (Real.log 4 + 5)) := by
        rw [abs_mul, abs_of_pos (Real.exp_pos _)]
        have hsum : |ccmGammaPolarBoundary (s - x) (s + x) -
              (Chebyshev.psi (Real.exp (s - x)) - Real.exp (s - x)) -
              ccmReciprocalMangoldtError (s + x)| ≤
            max Bg 0 + ((Real.log 4 + 4) * Real.exp (2 * s) + Real.exp (2 * s)) +
              (Real.log 4 + 5) := by
          have hs1 := abs_sub (ccmGammaPolarBoundary (s - x) (s + x) -
            (Chebyshev.psi (Real.exp (s - x)) - Real.exp (s - x)))
            (ccmReciprocalMangoldtError (s + x))
          have hs2 := abs_sub (ccmGammaPolarBoundary (s - x) (s + x))
            (Chebyshev.psi (Real.exp (s - x)) - Real.exp (s - x))
          linarith
        exact mul_le_mul hex1 hsum (abs_nonneg _) (Real.exp_pos s).le
      calc _ ≤ _ + _ := abs_add_le _ _
        _ ≤ BP := by dsimp only [BP]; linarith
    obtain ⟨K₀, hK₀⟩ := exists_nat_one_div_lt (by positivity : 0 < δ / 2)
    have hradK : ∀ k : ℕ, (s - δ) + 1 / (4 * (((k + K₀ : ℕ) : ℝ) + 1)) ≤ r := by
      intro k
      have h1 : 1 / (4 * (((k + K₀ : ℕ) : ℝ) + 1)) ≤ 1 / ((K₀ : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by
          have : (K₀ : ℝ) ≤ (k + K₀ : ℕ) := by exact_mod_cast Nat.le_add_left K₀ k
          linarith)
      dsimp only [r]
      linarith
    have hdom_k : Integrable (fun x => (Icc (-r) r).indicator (fun _ => BP * B₁) x) :=
      (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
    have hmeasP : Measurable ((centralInterval s).indicator (poleCrossProfile s)) :=
      (measurable_poleCrossProfile s).indicator (measurableSet_centralInterval s)
    have hI_tendsto : Tendsto (fun k : ℕ =>
        ∫ x, (centralInterval s).indicator (poleCrossProfile s) x * smooth G (k + K₀) x) atTop
        (𝓝 (∫ x, (centralInterval s).indicator (poleCrossProfile s) x * G x)) := by
      refine tendsto_integral_of_dominated_convergence _ (fun k => ?_) hdom_k (fun k => ?_) ?_
      · exact (hmeasP.mul (hsm (k + K₀)).continuous.measurable).aestronglyMeasurable
      · refine Eventually.of_forall fun x => ?_
        by_cases hxr : x ∈ Icc (-r) r
        · have hxc : x ∈ centralInterval s := ⟨by linarith [hxr.1], by linarith [hxr.2]⟩
          rw [indicator_of_mem hxr, indicator_of_mem hxc, Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hP_le x hxr) (smooth_bound hB₁0 hGB (k + K₀) x)
            (abs_nonneg _) hBP0
        · have hxabs : r < |x| := not_le.mp fun hle => hxr (abs_le.mp hle)
          rw [indicator_of_notMem hxr,
            smooth_eq_zero_of_radius_lt_abs hGv (k + K₀) ((hradK k).trans_lt hxabs),
            mul_zero, norm_zero]
      · refine Eventually.of_forall fun x => ?_
        exact (smooth_tendsto_of_continuous hG2.continuous x).const_mul _
    have hineq_k : ∀ k : ℕ,
        (∫ x, (centralInterval s).indicator (poleCrossProfile s) x * smooth G (k + K₀) x) ^ 2 ≤
          Real.exp s * (poleSharpConstant + C_pole * Real.exp (-(s / 2))) *
            fullZeroForm (smooth G (k + K₀)) := by
      intro k
      refine hsharp (hsm (k + K₀)) (hsc (k + K₀)) ?_
      have hsub : tsupport (smooth G (k + K₀)) ⊆ Icc (-r) r := by
        refine closure_minimal (fun x hx => ?_) isClosed_Icc
        rw [Function.mem_support] at hx
        exact abs_le.mp (not_lt.mp fun hgt =>
          hx (smooth_eq_zero_of_radius_lt_abs hGv (k + K₀) ((hradK k).trans_lt hgt)))
      exact hsub.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have hlim_ineq := le_of_tendsto_of_tendsto
      (hI_tendsto.pow 2)
      ((hZ_tendsto.comp (tendsto_add_atTop_nat K₀)).const_mul _)
      (Eventually.of_forall hineq_k)
    have hshift_eq : (∫ x, (centralInterval s).indicator (poleCrossProfile s) x * G x) =
        ∫ y, (centralInterval s).indicator (poleCrossProfile s) (y + s) * H₁ (y + δ) := by
      rw [← integral_add_right_eq_self
        (fun x => (centralInterval s).indicator (poleCrossProfile s) x * G x) s]
      refine integral_congr_ae (Eventually.of_forall fun y => ?_)
      dsimp only [G]
      ring_nf
    rwa [hshift_eq] at hlim_ineq
  -- Step 2: dominated limit `δ_m = 1/(m + 5) → 0`
  set C_dom : ℝ :=
    Real.exp s * ((L₁ : ℝ) * (2 * s ^ 2 + s + 1) + 4 * B₁ +
      ((Real.log 4 + 5) * Real.exp s + (Real.log 4 + 5)) * B₁) +
      (|Real.eulerMascheroniConstant| + |Real.log (2 * Real.pi)| + 1) * Real.exp s * B₁
  have hCdom0 : 0 ≤ C_dom := by
    dsimp only [C_dom]
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    positivity
  have hpt_dom : ∀ δ : ℝ, 0 ≤ δ → δ ≤ 1 / 5 → ∀ y : ℝ,
      ‖(centralInterval s).indicator (poleCrossProfile s) (y + s) * H₁ (y + δ)‖ ≤
        (Icc (-s) 0).indicator (fun _ => C_dom) y := by
    intro δ hδ0 hδ5 y
    by_cases hyI : y ∈ Ioo (-(s / 2) - 1 / 5) 0
    · have hyIcc : y ∈ Icc (-s) 0 := ⟨by linarith [hyI.1], hyI.2.le⟩
      have hys_mem : y + s ∈ centralInterval s := ⟨by linarith [hyI.1], by linarith [hyI.2]⟩
      rw [indicator_of_mem hyIcc, indicator_of_mem hys_mem, Real.norm_eq_abs]
      by_cases hyδ : 0 ≤ y + δ
      · have hH0_in : H₁ (y + δ) = 0 := by
          rcases eq_or_lt_of_le hyδ with he0 | hgt0
          · rw [← he0, hH₁0]
          · exact hsupp₁ (y + δ) fun hm => by linarith [hm.2]
        rw [hH0_in, mul_zero, abs_zero]
        exact hCdom0
      · push Not at hyδ
        have hH_lip : |H₁ (y + δ)| ≤ (L₁ : ℝ) * (-y) := by
          have hd := hL₁.dist_le_mul (y + δ) 0
          rw [Real.dist_eq, Real.dist_eq, hH₁0, sub_zero, sub_zero, abs_of_neg hyδ] at hd
          exact hd.trans (mul_le_mul_of_nonneg_left (by linarith) (NNReal.coe_nonneg L₁))
        have hH_bd : |H₁ (y + δ)| ≤ B₁ := hB₁ _
        have h2s_ge : 2 ≤ y + 2 * s := by linarith [hyI.1]
        have he_tail1 : Real.exp (-(y + 2 * s)) ≤ 1 / 2 := by
          have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
          have hle : Real.exp (-(y + 2 * s)) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
          rw [Real.exp_neg, ← one_div] at hle
          exact hle.trans (one_div_le_one_div_of_le (by norm_num) h2)
        have he_tail2 : Real.exp (-(2 * (y + 2 * s))) ≤ 1 / 2 := by
          exact (Real.exp_le_exp.mpr (by linarith)).trans he_tail1
        have hlt1 := abs_log_one_sub_le_two_mul (Real.exp_pos _) he_tail1
        have hlt2 := abs_log_one_sub_le_two_mul (Real.exp_pos _) he_tail2
        have hgam_split : ccmGammaPolarBoundary (s - (y + s)) (s + (y + s)) * H₁ (y + δ) =
            -(1 / 2 : ℝ) * Real.log (1 - Real.exp (2 * y)) * H₁ (y + δ) +
              (-Real.log (1 - Real.exp (-(y + 2 * s))) +
                (1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s))))) * H₁ (y + δ) := by
          unfold ccmGammaPolarBoundary
          have h1 : -(2 * (s - (y + s))) = 2 * y := by ring
          have h2 : s + (y + s) = y + 2 * s := by ring
          rw [h1, h2]
          ring
        have hlog_sing : |-(1 / 2 : ℝ) * Real.log (1 - Real.exp (2 * y)) * H₁ (y + δ)| ≤
            (L₁ : ℝ) * (2 * s ^ 2 + s + 1) := by
          rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
          have h1 := mul_le_mul_of_nonneg_left hH_lip
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (abs_nonneg _))
          have h2 := abs_neg_mul_log_one_sub_exp_two_mul_le (by linarith) hyIcc.1 hyI.2
          have h3 := mul_le_mul_of_nonneg_left h2 (NNReal.coe_nonneg L₁)
          nlinarith [NNReal.coe_nonneg L₁, abs_nonneg (Real.log (1 - Real.exp (2 * y)))]
        have hgam_rem : |(-Real.log (1 - Real.exp (-(y + 2 * s))) +
              (1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s))))) * H₁ (y + δ)| ≤
            4 * B₁ := by
          rw [abs_mul]
          have hsum : |-Real.log (1 - Real.exp (-(y + 2 * s))) +
              (1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s))))| ≤ 4 := by
            calc _ ≤ |-Real.log (1 - Real.exp (-(y + 2 * s)))| +
                  |(1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s))))| := abs_add_le _ _
              _ = |Real.log (1 - Real.exp (-(y + 2 * s)))| +
                  (1 / 2 : ℝ) * |Real.log (1 - Real.exp (-(2 * (y + 2 * s))))| := by
                rw [abs_neg, abs_mul, abs_of_pos (by norm_num)]
              _ ≤ 2 * Real.exp (-(y + 2 * s)) + (1 / 2) * (2 * Real.exp (-(2 * (y + 2 * s)))) := by
                linarith
              _ ≤ 4 := by linarith
          exact mul_le_mul hsum hH_bd (abs_nonneg _) (by norm_num)
        have hpsi_bd : |Chebyshev.psi (Real.exp (s - (y + s))) - Real.exp (s - (y + s))| ≤
            (Real.log 4 + 5) * Real.exp s := by
          have hsy : s - (y + s) = -y := by ring
          rw [hsy]
          have hp0 := Chebyshev.psi_nonneg (Real.exp (-y))
          have hple := Chebyshev.psi_le_const_mul_self (Real.exp_pos (-y)).le
          have hey_s : Real.exp (-y) ≤ Real.exp s := Real.exp_le_exp.mpr (by linarith [hyIcc.1])
          have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
          calc |Chebyshev.psi (Real.exp (-y)) - Real.exp (-y)|
              ≤ Chebyshev.psi (Real.exp (-y)) + Real.exp (-y) := by
                refine (abs_sub _ _).trans ?_
                rw [abs_of_nonneg hp0, abs_of_pos (Real.exp_pos _)]
            _ ≤ (Real.log 4 + 5) * Real.exp (-y) := by linarith
            _ ≤ (Real.log 4 + 5) * Real.exp s := mul_le_mul_of_nonneg_left hey_s (by positivity)
        have hmert := abs_ccmReciprocalMangoldtError_le (show 0 ≤ s + (y + s) by linarith)
        have hexp_p : Real.exp ((y + s) / 2) ≤ Real.exp s :=
          Real.exp_le_exp.mpr (by linarith [hyI.2])
        have hexp_m : Real.exp (-((y + s) / 2)) ≤ Real.exp s :=
          Real.exp_le_exp.mpr (by linarith [hyI.1])
        have he_s1 : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
        have hdecomp : poleCrossProfile s (y + s) * H₁ (y + δ) =
            Real.exp ((y + s) / 2) *
              (-(1 / 2 : ℝ) * Real.log (1 - Real.exp (2 * y)) * H₁ (y + δ) +
                (-Real.log (1 - Real.exp (-(y + 2 * s))) +
                  (1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s))))) * H₁ (y + δ) -
                (Chebyshev.psi (Real.exp (s - (y + s))) - Real.exp (s - (y + s))) * H₁ (y + δ) -
                ccmReciprocalMangoldtError (s + (y + s)) * H₁ (y + δ)) +
              ((-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) *
                  Real.exp ((y + s) / 2) * H₁ (y + δ) -
                Real.exp (-s) * Real.exp (-((y + s) / 2)) * H₁ (y + δ)) := by
          unfold poleCrossProfile
          linear_combination Real.exp ((y + s) / 2) * hgam_split
        rw [hdecomp]
        have hp_mul : |(Chebyshev.psi (Real.exp (s - (y + s))) - Real.exp (s - (y + s))) *
              H₁ (y + δ)| ≤ (Real.log 4 + 5) * Real.exp s * B₁ := by
          rw [abs_mul]
          exact mul_le_mul hpsi_bd hH_bd (abs_nonneg _)
            (mul_nonneg (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]) (Real.exp_pos s).le)
        have hm_mul : |ccmReciprocalMangoldtError (s + (y + s)) * H₁ (y + δ)| ≤
            (Real.log 4 + 5) * B₁ := by
          rw [abs_mul]
          exact mul_le_mul hmert hH_bd (abs_nonneg _)
            (by linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)])
        have hfirst : |Real.exp ((y + s) / 2) *
              (-(1 / 2 : ℝ) * Real.log (1 - Real.exp (2 * y)) * H₁ (y + δ) +
                (-Real.log (1 - Real.exp (-(y + 2 * s))) +
                  (1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s))))) * H₁ (y + δ) -
                (Chebyshev.psi (Real.exp (s - (y + s))) - Real.exp (s - (y + s))) * H₁ (y + δ) -
                ccmReciprocalMangoldtError (s + (y + s)) * H₁ (y + δ))| ≤
            Real.exp s * ((L₁ : ℝ) * (2 * s ^ 2 + s + 1) + 4 * B₁ +
              ((Real.log 4 + 5) * Real.exp s + (Real.log 4 + 5)) * B₁) := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _)]
          have hinner : |-(1 / 2 : ℝ) * Real.log (1 - Real.exp (2 * y)) * H₁ (y + δ) +
                (-Real.log (1 - Real.exp (-(y + 2 * s))) +
                  (1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s))))) * H₁ (y + δ) -
                (Chebyshev.psi (Real.exp (s - (y + s))) - Real.exp (s - (y + s))) * H₁ (y + δ) -
                ccmReciprocalMangoldtError (s + (y + s)) * H₁ (y + δ)| ≤
              (L₁ : ℝ) * (2 * s ^ 2 + s + 1) + 4 * B₁ +
                ((Real.log 4 + 5) * Real.exp s + (Real.log 4 + 5)) * B₁ := by
            have hs1 := abs_sub
              (-(1 / 2 : ℝ) * Real.log (1 - Real.exp (2 * y)) * H₁ (y + δ) +
                (-Real.log (1 - Real.exp (-(y + 2 * s))) +
                  (1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s))))) * H₁ (y + δ) -
                (Chebyshev.psi (Real.exp (s - (y + s))) - Real.exp (s - (y + s))) * H₁ (y + δ))
              (ccmReciprocalMangoldtError (s + (y + s)) * H₁ (y + δ))
            have hs2 := abs_sub
              (-(1 / 2 : ℝ) * Real.log (1 - Real.exp (2 * y)) * H₁ (y + δ) +
                (-Real.log (1 - Real.exp (-(y + 2 * s))) +
                  (1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s))))) * H₁ (y + δ))
              ((Chebyshev.psi (Real.exp (s - (y + s))) - Real.exp (s - (y + s))) * H₁ (y + δ))
            have hs3 := abs_add_le
              (-(1 / 2 : ℝ) * Real.log (1 - Real.exp (2 * y)) * H₁ (y + δ))
              ((-Real.log (1 - Real.exp (-(y + 2 * s))) +
                (1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s))))) * H₁ (y + δ))
            linarith
          exact mul_le_mul hexp_p hinner (abs_nonneg _) (Real.exp_pos s).le
        have hsecond : |(-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) *
              Real.exp ((y + s) / 2) * H₁ (y + δ) -
            Real.exp (-s) * Real.exp (-((y + s) / 2)) * H₁ (y + δ)| ≤
            (|Real.eulerMascheroniConstant| + |Real.log (2 * Real.pi)| + 1) * Real.exp s * B₁ := by
          have ht1 : |(-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)) *
              Real.exp ((y + s) / 2) * H₁ (y + δ)| ≤
              (|Real.eulerMascheroniConstant| + |Real.log (2 * Real.pi)|) * Real.exp s * B₁ := by
            rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
            have hc : |-Real.eulerMascheroniConstant - Real.log (2 * Real.pi)| ≤
                |Real.eulerMascheroniConstant| + |Real.log (2 * Real.pi)| := by
              simpa [sub_eq_add_neg] using
                abs_add_le (-Real.eulerMascheroniConstant) (-Real.log (2 * Real.pi))
            exact mul_le_mul (mul_le_mul hc hexp_p (Real.exp_pos _).le (by positivity))
              hH_bd (abs_nonneg _) (by positivity)
          have ht2 : |Real.exp (-s) * Real.exp (-((y + s) / 2)) * H₁ (y + δ)| ≤
              Real.exp s * B₁ := by
            rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
            exact mul_le_mul (by nlinarith [Real.exp_pos (-((y + s) / 2))]) hH_bd
              (abs_nonneg _) (Real.exp_pos s).le
          calc _ ≤ _ + _ := abs_sub _ _
            _ ≤ _ := by linarith
        calc _ ≤ _ + _ := abs_add_le _ _
          _ ≤ C_dom := by dsimp only [C_dom]; linarith
    · have hH0_out : H₁ (y + δ) = 0 := by
        rcases le_or_gt y (-(s / 2) - 1 / 5) with hle | hgt
        · exact hsupp₁ (y + δ) fun hm => by linarith [hm.1]
        · have hy0 : 0 ≤ y := not_lt.mp fun hlt => hyI ⟨hgt, hlt⟩
          rcases eq_or_lt_of_le (add_nonneg hy0 hδ0) with he0 | hgt0
          · rw [← he0, hH₁0]
          · exact hsupp₁ (y + δ) fun hm => by linarith [hm.2]
      rw [hH0_out, mul_zero, norm_zero]
      by_cases hyc : y ∈ Icc (-s) 0
      · rw [indicator_of_mem hyc]; exact hCdom0
      · rw [indicator_of_notMem hyc]
  have hdom_int : Integrable (fun y => (Icc (-s) 0).indicator (fun _ => C_dom) y) :=
    (continuous_const.integrableOn_Icc).integrable_indicator measurableSet_Icc
  have hmeas_shift : Measurable fun y => (centralInterval s).indicator (poleCrossProfile s) (y + s) :=
    ((measurable_poleCrossProfile s).indicator (measurableSet_centralInterval s)).comp
      (by fun_prop : Continuous fun y => y + s).measurable
  have hint0 : Integrable (fun y => (centralInterval s).indicator (poleCrossProfile s) (y + s) * H₁ y) :=
    hdom_int.mono' (hmeas_shift.mul hH₁.continuous.measurable).aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa only [add_zero] using hpt_dom 0 le_rfl (by norm_num) y)
  refine ⟨hint0, ?_⟩
  set δm : ℕ → ℝ := fun m => 1 / ((m : ℝ) + 5)
  have hδm0 : ∀ m, 0 < δm m := fun m => by dsimp only [δm]; positivity
  have hδm5 : ∀ m, δm m ≤ 1 / 5 := fun m =>
    one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) m])
  have hδm_lim : Tendsto δm atTop (𝓝 0) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 4)
    refine h.congr fun m => ?_
    dsimp only [Function.comp_def, δm]
    push_cast
    ring
  have hIm_lim : Tendsto (fun m =>
      ∫ y, (centralInterval s).indicator (poleCrossProfile s) (y + s) * H₁ (y + δm m)) atTop
      (𝓝 (∫ y, (centralInterval s).indicator (poleCrossProfile s) (y + s) * H₁ y)) := by
    refine tendsto_integral_of_dominated_convergence _ (fun m => ?_) hdom_int (fun m => ?_) ?_
    · exact (hmeas_shift.mul
        (hH₁.continuous.comp (continuous_id.add continuous_const)).measurable).aestronglyMeasurable
    · exact Eventually.of_forall fun y => hpt_dom (δm m) (hδm0 m).le (hδm5 m) y
    · refine Eventually.of_forall fun y => ?_
      have hH_cont : Tendsto (fun m => H₁ (y + δm m)) atTop (𝓝 (H₁ y)) := by
        simpa only [add_zero] using (hH₁.continuous.tendsto y).comp (tendsto_const_nhds.add hδm_lim)
      exact hH_cont.const_mul _
  have hlim0 := ge_of_tendsto (hIm_lim.pow 2)
    (Eventually.of_forall fun m => hshift_bound (δm m) (hδm0 m) (hδm5 m))
  have hm := mul_le_mul_of_nonneg_left hlim0 (sq_nonneg (Real.exp (-(s / 2))))
  have hec : Real.exp (-(s / 2)) ^ 2 * Real.exp s = 1 := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    have : -(s / 2) + -(s / 2) + s = 0 := by ring
    rw [this, Real.exp_zero]
  rw [← mul_pow] at hm
  linear_combination (weilQuad H₁ * (poleSharpConstant + C_pole * Real.exp (-(s / 2)))) * hec + hm

/-- **Top-collar discrepancy between `generalTerminalPolarSource` and `poleCrossProfile`.**
On `[−s/2, 0]` (`s ≥ 6`), the difference between `generalTerminalPolarSource A h₁ / splineAtom`
and `e^{−s/2} ∫ 1_{[−s,s]}(y+s) P_s(y+s) H₁(y) dy` is bounded by `(C_pr + 4) e^{−3s/16} √(M₈(H₁))`. -/
theorem sq_top_polarSource_sub_poleCross_le {A s C_pr : ℝ} (hA : 0 ≤ A) (hs : 6 ≤ s)
    (hCpr : 0 ≤ C_pr)
    (hmert : ∀ t : ℝ, 3 * s / 2 ≤ t → t ≤ 2 * s →
      |reciprocalMangoldtError t + Real.eulerMascheroniConstant| ≤ C_pr * Real.exp (-(t / 8)))
    {h₁ : ℝ → ℝ} (hh₁ : ContDiff ℝ 2 h₁)
    (hsuppA : ∀ y, y ∉ Icc (-A) 0 → h₁ y = 0)
    (hsupps : ∀ y, y ∉ Icc (-(s / 2)) 0 → h₁ y = 0)
    (hintP : Integrable (fun y =>
      (centralInterval s).indicator (poleCrossProfile s) (y + s) * halfWeight h₁ y)) :
    (generalTerminalPolarSource A h₁ / splineAtom -
        Real.exp (-(s / 2)) *
          ∫ y, (centralInterval s).indicator (poleCrossProfile s) (y + s) * halfWeight h₁ y) ^ 2 ≤
      (C_pr + 4) ^ 2 * Real.exp (-3 * s / 8) * exponentialMass 8 (halfWeight h₁) := by
  obtain ⟨heq, hintK⟩ := generalTerminalPolarSource_eq_integral_terminalPolarKernel hh₁ hA hsuppA
  have hdiv : generalTerminalPolarSource A h₁ / splineAtom = ∫ y, h₁ y * terminalPolarKernel y := by
    rw [heq, mul_div_cancel_left₀ _ splineAtom_pos.ne']
  rw [hdiv, ← integral_const_mul, ← integral_sub hintK (hintP.const_mul _)]
  set H₁ := halfWeight h₁
  have hh₁0 : h₁ 0 = 0 := vanish_zero_of_window_support hh₁.continuous hsuppA
  have hh₁_left : h₁ (-(s / 2)) = 0 := by
    have h0_seq : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have ht : Tendsto (fun n : ℕ => -(s / 2) - 1 / ((n : ℝ) + 1)) atTop (𝓝 (-(s / 2))) := by
      simpa only [sub_zero] using (tendsto_const_nhds (x := -(s / 2))).sub h0_seq
    have h0 : Tendsto (fun n : ℕ => h₁ (-(s / 2) - 1 / ((n : ℝ) + 1))) atTop (𝓝 0) :=
      tendsto_const_nhds.congr fun n =>
        (hsupps _ fun hm => by
          have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith [hm.1]).symm
    exact tendsto_nhds_unique ((hh₁.continuous.tendsto _).comp ht) h0
  have hH₁ : Continuous H₁ :=
    (Real.continuous_exp.comp (continuous_id.div_const 2)).mul hh₁.continuous
  have hH₁c : HasCompactSupport H₁ := (HasCompactSupport.intro isCompact_Icc hsuppA).mul_left
  have hH₁_absc : HasCompactSupport (fun y => |H₁ y|) := hH₁c.comp_left abs_zero
  have igq : Integrable fun y => |H₁ y| * Real.exp (-(y / 2)) :=
    (hH₁.abs.mul (by fun_prop)).integrable_of_hasCompactSupport hH₁_absc.mul_right
  have hH₁_pos : ∀ y, 0 < y → H₁ y = 0 := fun y hy => by
    simp only [H₁, halfWeight, hsupps y fun hm => by linarith [hm.2], mul_zero]
  have hpt : ∀ y : ℝ,
      ‖h₁ y * terminalPolarKernel y -
          Real.exp (-(s / 2)) *
            ((centralInterval s).indicator (poleCrossProfile s) (y + s) * H₁ y)‖ ≤
        ((C_pr + 4) * Real.exp (-3 * s / 16)) * (|H₁ y| * Real.exp (-(y / 2))) := by
    intro y
    rw [Real.norm_eq_abs]
    by_cases hyI : y ∈ Ioo (-(s / 2)) 0
    · have hys_mem : y + s ∈ centralInterval s := ⟨by linarith [hyI.1], by linarith [hyI.2]⟩
      rw [indicator_of_mem hys_mem]
      have hH_inv : h₁ y = Real.exp (-(y / 2)) * H₁ y := by
        dsimp only [H₁, halfWeight]
        rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
      have hexp1 : Real.exp y * (Real.exp (-(y / 2)) * H₁ y) = Real.exp (y / 2) * H₁ y := by
        rw [← mul_assoc, ← Real.exp_add, show y + -(y / 2) = y / 2 by ring]
      have hexp2 : Real.exp (-(s / 2)) * Real.exp ((y + s) / 2) = Real.exp (y / 2) := by
        rw [← Real.exp_add, show -(s / 2) + (y + s) / 2 = y / 2 by ring]
      have hexp3 : Real.exp (-(s / 2)) * (Real.exp (-s) * Real.exp (-((y + s) / 2))) =
          Real.exp (-2 * s) * Real.exp (-(y / 2)) := by
        rw [← mul_assoc, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1; ring
      have hsy1 : s - (y + s) = -y := by ring
      have hsy2 : s + (y + s) = y + 2 * s := by ring
      have hmert_eq : ccmReciprocalMangoldtError (y + 2 * s) = reciprocalMangoldtError (y + 2 * s) := rfl
      have hid : h₁ y * terminalPolarKernel y -
          Real.exp (-(s / 2)) * (poleCrossProfile s (y + s) * H₁ y) =
          Real.exp (y / 2) * H₁ y *
            (Real.log (1 - Real.exp (-(y + 2 * s))) -
              (1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s)))) +
              (reciprocalMangoldtError (y + 2 * s) + Real.eulerMascheroniConstant)) +
            Real.exp (-2 * s) * Real.exp (-(y / 2)) * H₁ y := by
        unfold terminalPolarKernel poleCrossProfile ccmGammaPolarBoundary
        have hexp0 : Real.exp y * Real.exp (-y) = 1 := by
          rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        rw [hsy1, hsy2, hmert_eq, show -(2 * -y) = 2 * y by ring, hH_inv]
        linear_combination
          -(Real.exp (-(y / 2)) * H₁ y) * hexp0 +
          (-Real.log (1 - Real.exp (2 * y)) / 2 - Real.log (2 * Real.pi) -
              Chebyshev.psi (Real.exp (-y)) + Real.exp (-y)) * hexp1 +
            (-(H₁ y * (-(1 / 2 : ℝ) * Real.log (1 - Real.exp (2 * y)) -
                Real.log (1 - Real.exp (-(y + 2 * s))) +
                (1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s)))) -
                (Chebyshev.psi (Real.exp (-y)) - Real.exp (-y)) -
                reciprocalMangoldtError (y + 2 * s) +
                (-Real.eulerMascheroniConstant - Real.log (2 * Real.pi))))) * hexp2 +
            (H₁ y) * hexp3
      rw [hid]
      have ht_lo : 3 * s / 2 ≤ y + 2 * s := by linarith [hyI.1]
      have ht_hi : y + 2 * s ≤ 2 * s := by linarith [hyI.2]
      have he_t1 : Real.exp (-(y + 2 * s)) ≤ 1 / 2 := by
        have h2 : (2 : ℝ) ≤ Real.exp 2 := by linarith [Real.add_one_le_exp 2]
        have hle : Real.exp (-(y + 2 * s)) ≤ Real.exp (-2) := Real.exp_le_exp.mpr (by linarith)
        rw [Real.exp_neg, ← one_div] at hle
        exact hle.trans (one_div_le_one_div_of_le (by norm_num) h2)
      have he_t2 : Real.exp (-(2 * (y + 2 * s))) ≤ 1 / 2 :=
        (Real.exp_le_exp.mpr (by linarith)).trans he_t1
      have hl1 : |Real.log (1 - Real.exp (-(y + 2 * s)))| ≤ 2 * Real.exp (-3 * s / 16) :=
        (abs_log_one_sub_le_two_mul (Real.exp_pos _) he_t1).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by norm_num))
      have hl2 : |(1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s))))| ≤
          Real.exp (-3 * s / 16) := by
        rw [abs_mul, abs_of_pos (by norm_num)]
        have hb := abs_log_one_sub_le_two_mul (Real.exp_pos _) he_t2
        have hd := Real.exp_le_exp.mpr (show -(2 * (y + 2 * s)) ≤ -3 * s / 16 by linarith)
        linarith
      have hm_bd : |reciprocalMangoldtError (y + 2 * s) + Real.eulerMascheroniConstant| ≤
          C_pr * Real.exp (-3 * s / 16) :=
        (hmert (y + 2 * s) ht_lo ht_hi).trans
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hCpr)
      have he2s : Real.exp (-2 * s) ≤ Real.exp (-3 * s / 16) :=
        Real.exp_le_exp.mpr (by linarith)
      have hey_half : Real.exp (y / 2) ≤ Real.exp (-(y / 2)) :=
        Real.exp_le_exp.mpr (by linarith [hyI.2])
      have hbr : |Real.log (1 - Real.exp (-(y + 2 * s))) -
            (1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s)))) +
            (reciprocalMangoldtError (y + 2 * s) + Real.eulerMascheroniConstant)| ≤
          (C_pr + 3) * Real.exp (-3 * s / 16) := by
        have hs1 := abs_add_le
          (Real.log (1 - Real.exp (-(y + 2 * s))) -
            (1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s)))))
          (reciprocalMangoldtError (y + 2 * s) + Real.eulerMascheroniConstant)
        have hs2 := abs_sub
          (Real.log (1 - Real.exp (-(y + 2 * s))))
          ((1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s)))))
        linarith
      calc _ ≤ |Real.exp (y / 2) * H₁ y *
              (Real.log (1 - Real.exp (-(y + 2 * s))) -
                (1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s)))) +
                (reciprocalMangoldtError (y + 2 * s) + Real.eulerMascheroniConstant))| +
              |Real.exp (-2 * s) * Real.exp (-(y / 2)) * H₁ y| := abs_add_le _ _
        _ = Real.exp (y / 2) * |H₁ y| *
              |Real.log (1 - Real.exp (-(y + 2 * s))) -
                (1 / 2 : ℝ) * Real.log (1 - Real.exp (-(2 * (y + 2 * s)))) +
                (reciprocalMangoldtError (y + 2 * s) + Real.eulerMascheroniConstant)| +
              Real.exp (-2 * s) * Real.exp (-(y / 2)) * |H₁ y| := by
          rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _),
            abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
        _ ≤ Real.exp (-(y / 2)) * |H₁ y| * ((C_pr + 3) * Real.exp (-3 * s / 16)) +
              Real.exp (-3 * s / 16) * Real.exp (-(y / 2)) * |H₁ y| :=
          add_le_add
            (mul_le_mul (mul_le_mul_of_nonneg_right hey_half (abs_nonneg _)) hbr (abs_nonneg _)
              (mul_nonneg (Real.exp_pos _).le (abs_nonneg _)))
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right he2s (Real.exp_pos _).le) (abs_nonneg _))
        _ = ((C_pr + 4) * Real.exp (-3 * s / 16)) * (|H₁ y| * Real.exp (-(y / 2))) := by ring
    · have hh0_out : h₁ y = 0 := by
        by_cases hyc : y ∈ Icc (-(s / 2)) 0
        · rcases eq_or_lt_of_le hyc.1 with he1 | hgt1
          · rw [← he1, hh₁_left]
          · rcases eq_or_lt_of_le hyc.2 with he2 | hlt2
            · rw [he2, hh₁0]
            · exact absurd ⟨hgt1, hlt2⟩ hyI
        · exact hsupps y hyc
      have hH0_out : H₁ y = 0 := by simp only [H₁, halfWeight, hh0_out, mul_zero]
      simp [hh0_out, hH0_out]
  have habs : |∫ y, (h₁ y * terminalPolarKernel y -
        Real.exp (-(s / 2)) *
          ((centralInterval s).indicator (poleCrossProfile s) (y + s) * H₁ y))| ≤
      ((C_pr + 4) * Real.exp (-3 * s / 16)) * ∫ y, |H₁ y| * Real.exp (-(y / 2)) := by
    have h := norm_integral_le_of_norm_le
      (igq.const_mul ((C_pr + 4) * Real.exp (-3 * s / 16))) (Eventually.of_forall hpt)
    rw [Real.norm_eq_abs, integral_const_mul] at h
    exact h
  have hsq1 : (∫ y, (h₁ y * terminalPolarKernel y -
        Real.exp (-(s / 2)) *
          ((centralInterval s).indicator (poleCrossProfile s) (y + s) * H₁ y))) ^ 2 ≤
      (C_pr + 4) ^ 2 * Real.exp (-3 * s / 8) * (∫ y, |H₁ y| * Real.exp (-(y / 2))) ^ 2 := by
    have hp := pow_le_pow_left₀ (abs_nonneg _) habs 2
    rwa [sq_abs, mul_pow, mul_pow, sq (Real.exp _), ← Real.exp_add,
      show -3 * s / 16 + -3 * s / 16 = -3 * s / 8 by ring] at hp
  have hm0 := abs_halfMoment_sq_le_shifted_exponentialMass hH₁ hH₁c le_rfl
    (fun y hy => hH₁_pos y (by linarith))
  rw [mul_zero, Real.exp_zero, one_mul] at hm0
  exact hsq1.trans (mul_le_mul_of_nonneg_left hm0 (by positivity))

/-! ### 4. Exponential growth of `PolarPaymentAt` below the onset aperture -/

private lemma criticalPoleWindowCost_eq_jordan_add_sharp {R : ℝ} (hR : 0 < R) :
    criticalPoleWindowCost R = jordanCoefficient 1 / R + splineAtom * poleSharpConstant := by
  unfold criticalPoleWindowCost criticalGenusCoefficient splineAtom
  field_simp [hR.ne']

/-- **Exponential growth of `PolarPaymentAt` in the onset aperture (zero logarithmic loss).**
There exist explicit universal constants `c₁ > 0` and `c₂ > 0` such that for every `0 ≤ a` with
`(a : EReal) ≤ onsetAperture zetaZeroConfig`, every `0 < R ≤ c₁ * e^{c₂ a}`, and every `A ≥ 0`,
`PolarPaymentAt R A` holds. -/
theorem exists_polarPaymentAt_exp_of_le_onsetAperture :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
      ∀ {a : ℝ}, 0 ≤ a → (a : EReal) ≤ onsetAperture zetaZeroConfig →
        ∀ {R : ℝ}, 0 < R → R ≤ c₁ * Real.exp (c₂ * a) →
          ∀ {A : ℝ}, 0 ≤ A → PolarPaymentAt R A := by
  obtain ⟨R₀, hR₀, hband⟩ := exists_polarPaymentAt_on_every_window
  obtain ⟨K₁, a₁, C_pole, hK₁, hCpole, hsharp_all⟩ := exists_sq_integral_poleCrossProfile_le_sharp
  obtain ⟨K₂, a₂, C_pr, hK₂, hCpr, hmert_all⟩ :=
    exists_abs_reciprocalMangoldtError_add_euler_le_of_zetaWindowPositive
  set Kstar : ℝ := max 1 (max K₁ K₂)
  have hK_pos : 0 < Kstar := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hK1_le : K₁ ≤ Kstar := (le_max_left K₁ K₂).trans (le_max_right 1 _)
  have hK2_le : K₂ ≤ Kstar := (le_max_right K₁ K₂).trans (le_max_right 1 _)
  set a_min : ℝ := max (max 1 (max a₁ a₂)) (14 * Kstar)
  have ha_min_pos : 0 < a_min := lt_of_lt_of_le one_pos ((le_max_left _ _).trans (le_max_left _ _))
  set C_kap : ℝ := poleSharpConstant + 2 * C_pole
  have hCkap_pos : 0 < C_kap := add_pos_of_pos_of_nonneg poleSharpConstant_pos (by positivity)
  set C_rem : ℝ := C_pr + 4 + 9 * Real.exp (7 / 2 : ℝ)
  have hCrem_pos : 0 < C_rem := by positivity
  set C_M : ℝ := splineAtom * windowCutoffLocalizationConstant +
      2 * splineAtom * C_rem ^ 2 / poleSharpConstant
  have hCM_pos : 0 < C_M := by
    have := splineAtom_pos
    have := windowCutoffLocalizationConstant_pos
    have := poleSharpConstant_pos
    positivity
  set c₂ : ℝ := 1 / (16 * Kstar)
  have hc₂ : 0 < c₂ := by dsimp only [c₂]; positivity
  set c_large : ℝ := min
      (jordanCoefficient 1 / (splineAtom * C_kap) * Real.exp (-(1 / 8 : ℝ)))
      (7 * tiltedJordanOne / C_M * Real.exp (-(1 / 8 : ℝ)))
  have hc_large_pos : 0 < c_large := by
    have hJ1 := jordanCoefficient_pos one_pos
    have hJt := tiltedJordanOne_pos
    have hκ := splineAtom_pos
    exact lt_min (by positivity) (by positivity)
  set c₁ : ℝ := min (R₀ * Real.exp (-(c₂ * a_min))) c_large
  have hc₁ : 0 < c₁ := lt_min (by positivity) hc_large_pos
  refine ⟨c₁, c₂, hc₁, hc₂, fun {a} ha0 ha {R} hR hR_le {A} hA => ?_⟩
  rcases lt_or_ge a a_min with hsmall | hbig
  · -- Bounded `a < a_min`: certified band `R₀` covers all `R ≤ c₁ e^{c₂ a}`
    have hRR₀ : R ≤ R₀ := by
      have hc1_le : c₁ ≤ R₀ * Real.exp (-(c₂ * a_min)) := min_le_left _ _
      have hexp_le : Real.exp (c₂ * a) ≤ Real.exp (c₂ * a_min) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsmall.le hc₂.le)
      calc R ≤ c₁ * Real.exp (c₂ * a) := hR_le
        _ ≤ (R₀ * Real.exp (-(c₂ * a_min))) * Real.exp (c₂ * a_min) :=
          mul_le_mul hc1_le hexp_le (Real.exp_pos _).le (by positivity)
        _ = R₀ := by rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    exact hband R hR hRR₀ A hA
  · -- Large `a ≥ a_min`: aperture `s = a/(2 Kstar) - 1 ≥ 6`
    set s : ℝ := a / (2 * Kstar) - 1
    have hs6 : 6 ≤ s := by
      have h14 : 14 * Kstar ≤ a := (le_max_right _ _).trans hbig
      dsimp only [s]
      rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
      linarith
    have hs_pos : 0 < s := by linarith
    have h2s2 : 2 * s + 2 = a / Kstar := by
      dsimp only [s]
      field_simp [hK_pos.ne']
      ring
    have ha1_le : a₁ ≤ a := ((le_max_left a₁ a₂).trans (le_max_right 1 _)).trans
      ((le_max_left _ _).trans hbig)
    have ha2_le : a₂ ≤ a := ((le_max_right a₁ a₂).trans (le_max_right 1 _)).trans
      ((le_max_left _ _).trans hbig)
    have hK1s : K₁ * (2 * s + 2) ≤ a := by
      rw [h2s2]
      calc K₁ * (a / Kstar) ≤ Kstar * (a / Kstar) :=
            mul_le_mul_of_nonneg_right hK1_le (div_nonneg ha0 hK_pos.le)
        _ = a := mul_div_cancel₀ a hK_pos.ne'
    have hmax_pole : ((max a₁ (K₁ * (2 * s + 2)) : ℝ) : EReal) ≤ onsetAperture zetaZeroConfig :=
      (EReal.coe_le_coe_iff.mpr (max_le ha1_le hK1s)).trans ha
    have hWa : ZetaWindowPositive a :=
      (windowPositiveAt_zeta_iff a).mp
        ((windowPositiveAt_iff_le_onsetAperture temperedConfig_zetaZeroConfig ha0).mpr ha)
    have hmert_s : ∀ t : ℝ, 3 * s / 2 ≤ t → t ≤ 2 * s →
        |reciprocalMangoldtError t + Real.eulerMascheroniConstant| ≤ C_pr * Real.exp (-(t / 8)) := by
      intro t ht_lo ht_hi
      have ht_pos : 0 < t := by linarith
      have hK2t : K₂ * (t + 2) ≤ a := by
        have ht2 : t + 2 ≤ 2 * s + 2 := by linarith
        calc K₂ * (t + 2) ≤ Kstar * (2 * s + 2) :=
              mul_le_mul hK2_le ht2 (by linarith) hK_pos.le
          _ = a := by rw [h2s2, mul_div_cancel₀ a hK_pos.ne']
      exact hmert_all a ha2_le hWa t ht_pos hK2t
    have hWs4 : ZetaWindowPositive ((s / 2) / 2) := by
      refine zetaWindowPositive_antitone ?_ hWa
      have h1K : 1 ≤ Kstar := le_max_left 1 _
      have hs_le_a : s / 4 ≤ a := by
        have : s / 4 ≤ Kstar * (2 * s + 2) := by nlinarith
        have : Kstar * (2 * s + 2) = a := by rw [h2s2, mul_div_cancel₀ a hK_pos.ne']
        linarith
      linarith
    have hQ_pos_s2 : ∀ H₁ : ℝ → ℝ, IsWindowTest (s / 2) H₁ → 0 ≤ weilQuad H₁ :=
      (windowForm_nonneg_iff_zetaWindowPositive_half (s / 2)).mpr hWs4
    -- Now prove PolarPaymentAt R A for any test `h` on `[-A, 0]`
    intro h hh hsupp
    set H := halfWeight h
    have hH2 : ContDiff ℝ 2 H :=
      (Real.contDiff_exp.comp (contDiff_id.div_const 2)).mul hh
    have hHc : HasCompactSupport H := (HasCompactSupport.intro isCompact_Icc hsupp).mul_left
    have hH0 : ∀ y, 0 < y → H y = 0 := fun y hy => by
      simp only [H, halfWeight, hsupp y fun hm => by linarith [hm.2], mul_zero]
    set θ := windowLeftCutoff (s / 2)
    set h₁ : ℝ → ℝ := fun y => θ y * h y
    set h₂ : ℝ → ℝ := fun y => (1 - θ y) * h y
    have hh₁ : ContDiff ℝ 2 h₁ := (contDiff_windowLeftCutoff (s / 2)).mul hh
    have hh₂ : ContDiff ℝ 2 h₂ := (contDiff_const.sub (contDiff_windowLeftCutoff (s / 2))).mul hh
    have hsupp₁A : ∀ y, y ∉ Icc (-A) 0 → h₁ y = 0 := fun y hy => by
      simp only [h₁, hsupp y hy, mul_zero]
    have hsupp₂A : ∀ y, y ∉ Icc (-A) 0 → h₂ y = 0 := fun y hy => by
      simp only [h₂, hsupp y hy, mul_zero]
    have hsupp₁s : ∀ y, y ∉ Icc (-(s / 2)) 0 → h₁ y = 0 := by
      intro y hy
      rw [mem_Icc, not_and_or, not_le, not_le] at hy
      rcases hy with hlt | hgt
      · simp only [h₁, θ, windowLeftCutoff_eq_zero_of_le hlt.le, zero_mul]
      · simp only [h₁, hsupp y fun hm => by linarith [hm.2], mul_zero]
    have hdeep₂ : ∀ y, -(s / 2 - 1) < y → h₂ y = 0 := fun y hy => by
      simp only [h₂, θ, windowLeftCutoff_eq_one_of_ge hy.le, sub_self, zero_mul]
    have hh_sum : h = fun y => h₁ y + h₂ y := by funext y; dsimp only [h₁, h₂]; ring
    have hS_split : generalTerminalPolarSource A h / splineAtom =
        generalTerminalPolarSource A h₁ / splineAtom +
          generalTerminalPolarSource A h₂ / splineAtom := by
      rw [hh_sum, generalTerminalPolarSource_add hA hh₁ hsupp₁A hh₂ hsupp₂A, add_div]
    -- Exponential masses of H₁ and H₂ are ≤ M₈(H)
    set M := exponentialMass 8 H
    have hM0 : 0 ≤ M := exponentialMass_nonneg 8 H
    have hH2_int : Integrable fun y => Real.exp (-(8 * y)) * H y ^ 2 := by
      have hF2c : HasCompactSupport (fun y => H y ^ 2) := by
        rw [hasCompactSupport_iff_eventuallyEq] at hHc ⊢
        exact hHc.mono fun y hy => by change H y = 0 at hy; change H y ^ 2 = 0; rw [hy]; norm_num
      exact ((by fun_prop : Continuous fun y => Real.exp (-(8 * y))).mul
        (hH2.continuous.pow 2)).integrable_of_hasCompactSupport hF2c.mul_left
    have hM₁_le : exponentialMass 8 (halfWeight h₁) ≤ M := by
      unfold exponentialMass
      have hint1 : Integrable fun y => Real.exp (-(8 * y)) * halfWeight h₁ y ^ 2 := by
        have hc1 : HasCompactSupport (fun y => halfWeight h₁ y ^ 2) :=
          ((HasCompactSupport.intro isCompact_Icc hsupp₁A).mul_left).comp_left
            (by norm_num : (0 : ℝ) ^ 2 = 0)
        exact ((by fun_prop : Continuous fun y => Real.exp (-(8 * y))).mul
          (((Real.continuous_exp.comp (continuous_id.div_const 2)).mul hh₁.continuous).pow 2)).integrable_of_hasCompactSupport hc1.mul_left
      refine integral_mono hint1 hH2_int fun y => ?_
      have hb := windowLeftCutoff_bounds (s / 2) y
      have heq : halfWeight h₁ y = θ y * H y := by dsimp only [halfWeight, h₁, H]; ring
      rw [heq, mul_pow]
      have hθ2 : θ y ^ 2 ≤ 1 := by nlinarith [hb.1, hb.2]
      exact mul_le_mul_of_nonneg_left
        (by nlinarith [sq_nonneg (H y), hθ2]) (Real.exp_pos _).le
    have hM₂_le : exponentialMass 8 (halfWeight h₂) ≤ M := by
      unfold exponentialMass
      have hint2 : Integrable fun y => Real.exp (-(8 * y)) * halfWeight h₂ y ^ 2 := by
        have hc2 : HasCompactSupport (fun y => halfWeight h₂ y ^ 2) :=
          ((HasCompactSupport.intro isCompact_Icc hsupp₂A).mul_left).comp_left
            (by norm_num : (0 : ℝ) ^ 2 = 0)
        exact ((by fun_prop : Continuous fun y => Real.exp (-(8 * y))).mul
          (((Real.continuous_exp.comp (continuous_id.div_const 2)).mul hh₂.continuous).pow 2)).integrable_of_hasCompactSupport hc2.mul_left
      refine integral_mono hint2 hH2_int fun y => ?_
      have hb := windowLeftCutoff_bounds (s / 2) y
      have heq : halfWeight h₂ y = (1 - θ y) * H y := by dsimp only [halfWeight, h₂, H]; ring
      rw [heq, mul_pow]
      have hθ2 : (1 - θ y) ^ 2 ≤ 1 := by nlinarith [hb.1, hb.2]
      exact mul_le_mul_of_nonneg_left
        (by nlinarith [sq_nonneg (H y), hθ2]) (Real.exp_pos _).le
    -- Apply top compression and discrepancy bounds
    have hH₁_eq : halfWeight h₁ = fun y => θ y * H y := by funext y; dsimp only [halfWeight, h₁, H]; ring
    have hH₁_diff : ContDiff ℝ 2 (halfWeight h₁) := by
      rw [hH₁_eq]; exact (contDiff_windowLeftCutoff (s / 2)).mul hH2
    have hH₁_supps : ∀ y, y ∉ Icc (-(s / 2)) 0 → halfWeight h₁ y = 0 := fun y hy => by
      simp only [halfWeight, hsupp₁s y hy, mul_zero]
    obtain ⟨hintP, hI₁_sq⟩ := sq_poleCross_windowTest_le (s := s) (C_pole := C_pole) hs6 hCpole
      (fun hF hFc hFs => hsharp_all ⟨s, hs_pos⟩ (by linarith) hmax_pole hF hFc hFs)
      hH₁_diff hH₁_supps
    have htop_err := sq_top_polarSource_sub_poleCross_le hA hs6 hCpr hmert_s
      hh₁ hsupp₁A hsupp₁s hintP
    have hdeep_err := sq_generalTerminalPolarSource_deep_le hA (by linarith : 2 ≤ s / 2 - 1)
      hh₂ hsupp₂A hdeep₂
    -- Combine top discrepancy + deep tail into `E^2 ≤ C_rem^2 * e^{-3s/8} * M`
    set I₁ := Real.exp (-(s / 2)) *
      ∫ y, (centralInterval s).indicator (poleCrossProfile s) (y + s) * halfWeight h₁ y
    set E₁ := generalTerminalPolarSource A h₁ / splineAtom - I₁
    set E₂ := generalTerminalPolarSource A h₂ / splineAtom
    have hE₁_abs : |E₁| ≤ (C_pr + 4) * Real.exp (-3 * s / 16) * Real.sqrt M := by
      have h1 : E₁ ^ 2 ≤ ((C_pr + 4) * Real.exp (-3 * s / 16) * Real.sqrt M) ^ 2 := by
        have hm := htop_err.trans (mul_le_mul_of_nonneg_left hM₁_le (by positivity))
        have hsq : ((C_pr + 4) * Real.exp (-3 * s / 16) * Real.sqrt M) ^ 2 =
            (C_pr + 4) ^ 2 * Real.exp (-3 * s / 8) * M := by
          rw [mul_pow, mul_pow, Real.sq_sqrt hM0, sq (Real.exp _), ← Real.exp_add]
          congr 2; ring
        linarith
      exact abs_le_of_sq_le_sq' h1 (by positivity) |>.2
    have hE₂_abs : |E₂| ≤ 9 * Real.exp (7 / 2 : ℝ) * Real.exp (-3 * s / 16) * Real.sqrt M := by
      have h7b : Real.exp (-7 * (s / 2 - 1)) ≤ Real.exp (7 : ℝ) * Real.exp (-3 * s / 8) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      have h1 : E₂ ^ 2 ≤ (9 * Real.exp (7 / 2 : ℝ) * Real.exp (-3 * s / 16) * Real.sqrt M) ^ 2 := by
        have hm := hdeep_err.trans (mul_le_mul_of_nonneg_left hM₂_le (by positivity))
        have hm2 := hm.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h7b (by norm_num : (0 : ℝ) ≤ 81)) hM0)
        have hsq : (9 * Real.exp (7 / 2 : ℝ) * Real.exp (-3 * s / 16) * Real.sqrt M) ^ 2 =
            81 * (Real.exp (7 : ℝ) * Real.exp (-3 * s / 8)) * M := by
          rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hM0, sq (Real.exp (7 / 2 : ℝ)),
            ← Real.exp_add, sq (Real.exp (-3 * s / 16)), ← Real.exp_add]
          norm_num
          ring_nf
        linarith
      exact abs_le_of_sq_le_sq' h1 (by positivity) |>.2
    have hE_sq : (E₁ + E₂) ^ 2 ≤ C_rem ^ 2 * Real.exp (-3 * s / 8) * M := by
      have habs : |E₁ + E₂| ≤ C_rem * Real.exp (-3 * s / 16) * Real.sqrt M := by
        calc |E₁ + E₂| ≤ |E₁| + |E₂| := abs_add_le _ _
          _ ≤ _ := by dsimp only [C_rem]; linarith
      have hp := pow_le_pow_left₀ (abs_nonneg _) habs 2
      rw [sq_abs, mul_pow, mul_pow, Real.sq_sqrt hM0, sq (Real.exp _), ← Real.exp_add,
        show -3 * s / 16 + -3 * s / 16 = -3 * s / 8 by ring] at hp
      exact hp
    -- Young's inequality with `η = e^{-s/8}` on `T(A, h) = I₁ + (E₁ + E₂)`
    set η := Real.exp (-(s / 8))
    have hη_pos : 0 < η := Real.exp_pos _
    have hη_le1 : η ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    have hyoung : (I₁ + (E₁ + E₂)) ^ 2 ≤ (1 + η) * I₁ ^ 2 + (1 + Real.exp (s / 8)) * (E₁ + E₂) ^ 2 := by
      have hs_nn := sq_nonneg (Real.sqrt η * I₁ - Real.sqrt (Real.exp (s / 8)) * (E₁ + E₂))
      have hprod : Real.sqrt η * Real.sqrt (Real.exp (s / 8)) = 1 := by
        rw [← Real.sqrt_mul hη_pos.le, ← Real.exp_add, neg_add_cancel, Real.exp_zero, Real.sqrt_one]
      rw [sub_sq, mul_pow, mul_pow, Real.sq_sqrt hη_pos.le, Real.sq_sqrt (Real.exp_pos _).le] at hs_nn
      have hmid : 2 * (Real.sqrt η * I₁) * (Real.sqrt (Real.exp (s / 8)) * (E₁ + E₂)) =
          2 * I₁ * (E₁ + E₂) := by
        linear_combination (2 * I₁ * (E₁ + E₂)) * hprod
      nlinarith [hs_nn, hmid]
    have hQ₁_nn : 0 ≤ weilQuad (halfWeight h₁) := by
      rw [hH₁_eq]
      exact hQ_pos_s2 _ (isWindowTest_windowLeftCutoff_mul (s / 2) hH2 hH0)
    have hQ₁_loc : weilQuad (halfWeight h₁) ≤
        weilQuad H + windowCutoffLocalizationConstant * Real.exp (-3 * (s / 2)) * M := by
      rw [hH₁_eq]
      linarith [weilQuad_windowLeftCutoff_sub_le (by linarith : 2 < s / 2) hH2 hHc hH0]
    have hkap_prod : (1 + η) * (poleSharpConstant + C_pole * Real.exp (-(s / 2))) ≤
        poleSharpConstant + C_kap * η := by
      have he2 : Real.exp (-(s / 2)) ≤ η := Real.exp_le_exp.mpr (by linarith)
      have he_prod : η * Real.exp (-(s / 2)) ≤ η := mul_le_of_le_one_right hη_pos.le
        (Real.exp_le_one_iff.mpr (by linarith))
      dsimp only [C_kap]
      nlinarith [hCpole, poleSharpConstant_pos]
    have hrem_prod : (1 + Real.exp (s / 8)) * (C_rem ^ 2 * Real.exp (-3 * s / 8) * M) ≤
        2 * C_rem ^ 2 * Real.exp (-(s / 4)) * M := by
      have h1e : 1 + Real.exp (s / 8) ≤ 2 * Real.exp (s / 8) := by
        linarith [Real.one_le_exp (by linarith : 0 ≤ s / 8)]
      have hexp_c : Real.exp (s / 8) * Real.exp (-3 * s / 8) = Real.exp (-(s / 4)) := by
        rw [← Real.exp_add]; congr 1; ring
      calc (1 + Real.exp (s / 8)) * (C_rem ^ 2 * Real.exp (-3 * s / 8) * M)
          ≤ (2 * Real.exp (s / 8)) * (C_rem ^ 2 * Real.exp (-3 * s / 8) * M) :=
            mul_le_mul_of_nonneg_right h1e (by positivity)
        _ = 2 * C_rem ^ 2 * (Real.exp (s / 8) * Real.exp (-3 * s / 8)) * M := by ring
        _ = 2 * C_rem ^ 2 * Real.exp (-(s / 4)) * M := by rw [hexp_c]
    have hT_sq : (generalTerminalPolarSource A h / splineAtom) ^ 2 ≤
        (poleSharpConstant + C_kap * η) * weilQuad (halfWeight h₁) +
          2 * C_rem ^ 2 * Real.exp (-(s / 4)) * M := by
      have hid : generalTerminalPolarSource A h / splineAtom = I₁ + (E₁ + E₂) := by
        rw [hS_split]; dsimp only [E₁, E₂]; ring
      rw [hid]
      have h1 := mul_le_mul_of_nonneg_left hI₁_sq (by positivity : 0 ≤ 1 + η)
      have h2 : (1 + η) * ((poleSharpConstant + C_pole * Real.exp (-(s / 2))) *
          weilQuad (halfWeight h₁)) ≤ (poleSharpConstant + C_kap * η) * weilQuad (halfWeight h₁) := by
        rw [← mul_assoc]
        exact mul_le_mul_of_nonneg_right hkap_prod hQ₁_nn
      have h3 := (mul_le_mul_of_nonneg_left hE_sq (by positivity : 0 ≤ 1 + Real.exp (s / 8))).trans
        hrem_prod
      linarith
    -- Absorb into `criticalPoleWindowCost R` and `windowPencil R H`
    have hc2a : c₂ * a = s / 8 + 1 / 8 := by
      dsimp only [c₂, s]
      field_simp [hK_pos.ne']
      ring
    have hR_exp : R ≤ c_large * Real.exp (s / 8 + 1 / 8) := by
      rw [← hc2a]
      exact hR_le.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) (Real.exp_pos _).le)
    have hR_s8_1 : R ≤ jordanCoefficient 1 / (splineAtom * C_kap) * Real.exp (s / 8) := by
      have hm := min_le_left
        (jordanCoefficient 1 / (splineAtom * C_kap) * Real.exp (-(1 / 8 : ℝ)))
        (7 * tiltedJordanOne / C_M * Real.exp (-(1 / 8 : ℝ)))
      calc R ≤ c_large * Real.exp (s / 8 + 1 / 8) := hR_exp
        _ ≤ (jordanCoefficient 1 / (splineAtom * C_kap) * Real.exp (-(1 / 8 : ℝ))) *
              Real.exp (s / 8 + 1 / 8) := mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
        _ = jordanCoefficient 1 / (splineAtom * C_kap) * Real.exp (s / 8) := by
          rw [mul_assoc, ← Real.exp_add, show -(1 / 8 : ℝ) + (s / 8 + 1 / 8) = s / 8 by ring]
    have hR_s8_2 : R ≤ 7 * tiltedJordanOne / C_M * Real.exp (s / 8) := by
      have hm := min_le_right
        (jordanCoefficient 1 / (splineAtom * C_kap) * Real.exp (-(1 / 8 : ℝ)))
        (7 * tiltedJordanOne / C_M * Real.exp (-(1 / 8 : ℝ)))
      calc R ≤ c_large * Real.exp (s / 8 + 1 / 8) := hR_exp
        _ ≤ (7 * tiltedJordanOne / C_M * Real.exp (-(1 / 8 : ℝ))) *
              Real.exp (s / 8 + 1 / 8) := mul_le_mul_of_nonneg_right hm (Real.exp_pos _).le
        _ = 7 * tiltedJordanOne / C_M * Real.exp (s / 8) := by
          rw [mul_assoc, ← Real.exp_add, show -(1 / 8 : ℝ) + (s / 8 + 1 / 8) = s / 8 by ring]
    have hkap_cost : splineAtom * (poleSharpConstant + C_kap * η) ≤ criticalPoleWindowCost R := by
      rw [criticalPoleWindowCost_eq_jordan_add_sharp hR]
      have h1 : splineAtom * C_kap * η ≤ jordanCoefficient 1 / R := by
        rw [le_div_iff₀ hR]
        have h2 := mul_le_mul_of_nonneg_left hR_s8_1
          (mul_nonneg splineAtom_pos.le hCkap_pos.le)
        have hid : splineAtom * C_kap *
            (jordanCoefficient 1 / (splineAtom * C_kap) * Real.exp (s / 8)) =
            jordanCoefficient 1 * Real.exp (s / 8) := by
          field_simp [splineAtom_pos.ne', hCkap_pos.ne']
        rw [hid] at h2
        have h3 := mul_le_mul_of_nonneg_right h2 hη_pos.le
        have hec : Real.exp (s / 8) * η = 1 := by
          dsimp only [η]; rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
        linear_combination (jordanCoefficient 1) * hec + h3
      linarith
    have hD_pos : 0 < criticalPoleWindowCost R := criticalPoleWindowCost_pos hR
    have hD_ge_sharp : splineAtom * poleSharpConstant ≤ criticalPoleWindowCost R := by
      rw [criticalPoleWindowCost_eq_jordan_add_sharp hR]
      linarith [div_pos (jordanCoefficient_pos one_pos) hR]
    have hκ := splineAtom_pos
    have hS_sq : generalTerminalPolarSource A h ^ 2 =
        splineAtom ^ 2 * (generalTerminalPolarSource A h / splineAtom) ^ 2 := by
      field_simp [hκ.ne']
    rw [hS_sq]
    have hnum_le := mul_le_mul_of_nonneg_left hT_sq (sq_nonneg splineAtom)
    have hdiv1 : splineAtom ^ 2 * ((poleSharpConstant + C_kap * η) * weilQuad (halfWeight h₁)) /
        criticalPoleWindowCost R ≤ splineAtom * weilQuad (halfWeight h₁) := by
      rw [div_le_iff₀ hD_pos]
      have hm := mul_le_mul_of_nonneg_left hkap_cost (mul_nonneg hκ.le hQ₁_nn)
      linarith [show splineAtom * weilQuad (halfWeight h₁) *
          (splineAtom * (poleSharpConstant + C_kap * η)) =
          splineAtom ^ 2 * ((poleSharpConstant + C_kap * η) * weilQuad (halfWeight h₁)) by ring]
    have hdiv2 : splineAtom ^ 2 * (2 * C_rem ^ 2 * Real.exp (-(s / 4)) * M) /
        criticalPoleWindowCost R ≤
        (2 * splineAtom * C_rem ^ 2 / poleSharpConstant) * Real.exp (-(s / 4)) * M := by
      have hden_pos : 0 < splineAtom * poleSharpConstant :=
        mul_pos hκ poleSharpConstant_pos
      calc splineAtom ^ 2 * (2 * C_rem ^ 2 * Real.exp (-(s / 4)) * M) / criticalPoleWindowCost R
          ≤ splineAtom ^ 2 * (2 * C_rem ^ 2 * Real.exp (-(s / 4)) * M) /
              (splineAtom * poleSharpConstant) :=
            div_le_div_of_nonneg_left (by positivity) hden_pos hD_ge_sharp
        _ = (2 * splineAtom * C_rem ^ 2 / poleSharpConstant) * Real.exp (-(s / 4)) * M := by
          field_simp [hκ.ne', poleSharpConstant_pos.ne']
    have hCM_le : C_M * η ≤ 7 * tiltedJordanOne / R := by
      rw [le_div_iff₀ hR]
      have h2 := mul_le_mul_of_nonneg_left hR_s8_2 hCM_pos.le
      have hid : C_M * (7 * tiltedJordanOne / C_M * Real.exp (s / 8)) =
          7 * tiltedJordanOne * Real.exp (s / 8) := by
        field_simp [hCM_pos.ne']
      rw [hid] at h2
      have h3 := mul_le_mul_of_nonneg_right h2 hη_pos.le
      have hec : Real.exp (s / 8) * η = 1 := by
        dsimp only [η]; rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      linear_combination (7 * tiltedJordanOne) * hec + h3
    have hd1 : Real.exp (-3 * (s / 2)) ≤ η := Real.exp_le_exp.mpr (by dsimp only [η]; linarith)
    have hd2 : Real.exp (-(s / 4)) ≤ η := Real.exp_le_exp.mpr (by dsimp only [η]; linarith)
    have hM_term : (splineAtom * windowCutoffLocalizationConstant * Real.exp (-3 * (s / 2)) +
          (2 * splineAtom * C_rem ^ 2 / poleSharpConstant) * Real.exp (-(s / 4))) * M ≤
        7 * tiltedJordanOne / R * M := by
      refine mul_le_mul_of_nonneg_right ?_ hM0
      refine le_trans ?_ hCM_le
      dsimp only [C_M]
      rw [ right_distrib ]
      exact add_le_add
        (mul_le_mul_of_nonneg_left hd1
          (mul_nonneg hκ.le windowCutoffLocalizationConstant_pos.le))
        (mul_le_mul_of_nonneg_left hd2 (by
          have := poleSharpConstant_pos; positivity))
    unfold windowPencil
    calc splineAtom ^ 2 * (generalTerminalPolarSource A h / splineAtom) ^ 2 / criticalPoleWindowCost R
        ≤ (splineAtom ^ 2 * ((poleSharpConstant + C_kap * η) * weilQuad (halfWeight h₁)) +
            splineAtom ^ 2 * (2 * C_rem ^ 2 * Real.exp (-(s / 4)) * M)) /
            criticalPoleWindowCost R := by
          refine div_le_div_of_nonneg_right ?_ hD_pos.le
          linarith [hnum_le]
      _ = splineAtom ^ 2 * ((poleSharpConstant + C_kap * η) * weilQuad (halfWeight h₁)) /
            criticalPoleWindowCost R +
          splineAtom ^ 2 * (2 * C_rem ^ 2 * Real.exp (-(s / 4)) * M) /
            criticalPoleWindowCost R := add_div _ _ _
      _ ≤ splineAtom * weilQuad (halfWeight h₁) +
          (2 * splineAtom * C_rem ^ 2 / poleSharpConstant) * Real.exp (-(s / 4)) * M :=
        add_le_add hdiv1 hdiv2
      _ ≤ splineAtom * (weilQuad H + windowCutoffLocalizationConstant * Real.exp (-3 * (s / 2)) * M) +
          (2 * splineAtom * C_rem ^ 2 / poleSharpConstant) * Real.exp (-(s / 4)) * M :=
        add_le_add_right (mul_le_mul_of_nonneg_left hQ₁_loc hκ.le) _
      _ = splineAtom * weilQuad H +
          (splineAtom * windowCutoffLocalizationConstant * Real.exp (-3 * (s / 2)) +
            (2 * splineAtom * C_rem ^ 2 / poleSharpConstant) * Real.exp (-(s / 4))) * M := by ring
      _ ≤ splineAtom * weilQuad H + 7 * tiltedJordanOne / R * M :=
        add_le_add_left hM_term _

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
