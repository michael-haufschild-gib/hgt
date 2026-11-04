import GaloisForLFunctions.SignedWindowCriticality.BelowLogFour.TwoProfileRefutationBelowLogFour
import GaloisForLFunctions.SignedWindowCriticality.TheParitySectorsAreTheBandAtTheCentre
import GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace.IntrinsicWeilTraceAndWindowCorollaries
import GaloisForLFunctions.SquareRootThreshold.VisibilityTradeoffAndExcludedDepthLaw

/-!
# Retained Pole Variance, the Sharp `log 4` Boundary, and the `{2, 3}` Half-Window Band

Together with `GaugeExtensionInvarianceAndHalfNormDual` and `TwoProfileRefutationBelowLogFour`,
this module completes the unconditional resolution of the window-certificate problem on windows of
length `2c < log 4` (`0 < c < log 2`):

1. **Sharp prime-free half-window boundary at `2c = log 4` (`c = log 2`)**
   (`primeSum_eq_zero_of_halfWindow_le_log_two`, `exists_halfWindow_primeSum_pos_of_log_two_lt`,
   `primeFree_halfWindow_iff_le_log_two`). A continuous half-window test `f` supported in `[−c, 0]`
   has `primeSum f = 0` — making its Weil diagonal `weilQuad f` purely archimedean-polar — for all
   such `f` if and only if `c ≤ log 2` (`2c ≤ log 4`). Beyond `c = log 2` (`2c > log 4`), smooth
   nonnegative half-window tests already carry `primeSum f > 0`.
2. **Exact `{2, 3}` reflection-band and Markov–Hankel equivalence across `(0, log 2)`**
   (`centreCoupling_eq_two_three_of_lt_log_two`, `zetaWindowPositive_iff_even_and_odd_sectors`,
   `zetaWindowPositive_iff_abs_centreCoupling_le`, `zetaWindowPositive_iff_two_three_band`,
   `zetaWindowPositive_iff_two_three_markov_hankel`). Orthogonal parity splitting reduces
   `ZetaWindowPositive c` to simultaneous positivity of the even and odd sectors, which for every
   `0 < c < log 2` (`2c < log 4`) is equivalent to the prime-free half-window `{2, 3}` Hankel band
   `|𝓗₀(f) − w₂(f⋆f)(−log 2) − w₃(f⋆f)(−log 3)| ≤ W(f)` on `[−c, 0]`.
3. **Retained-variance Doob–theta signed certificate equivalence**
   (`even_nonneg_iff_retainedVariance_evenThetaGauge`,
   `odd_nonneg_iff_retainedVariance_shiftedGroundState`,
   `zetaWindowPositive_below_log_four_equivalences`). Retaining the pole-charge variance `2V^S(u)` —
   proved mandatory in Part I (`TwoProfileRefutationBelowLogFour`) — turns every positive even theta
   gauge in the even sector and every shifted ground state `ω_a` (`a > 0`) in the odd sector into an
   exact signed certificate equivalent to `ZetaWindowPositive c`, to `(scalingSubsurface (realTestsAt c)).HodgeIndex`,
   and to Künneth effectivity at aperture `c`.
4. **Convex `{2, 3}` weight geometry, unconditional nonpositive-`w₂` exclusion, and synthesis**
   (`belowLogFourBandWeights`, `convex_belowLogFourBandWeights`,
   `not_mem_belowLogFourBandWeights_of_nonpos`, `question_two_eight_complete_resolution`). For every
   `c ≥ 21/40`, no weight pair `(w₂, w₃)` with `w₂ ≤ 0` (in particular neither the prime-free weight
   `(0, w₃)` nor the Liouville-flipped weight `(−w₂, w₃)`) belongs to `belowLogFourBandWeights c`.
-/

open MeasureTheory Set Filter Topology
open scoped Real BigOperators
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilMarkovPole

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality.BelowLogFour

open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.ArithmeticPositivityTheory
open GaloisForLFunctions.SignedWindowCriticality
open GaloisForLFunctions.CanonicalSystemOfTheWindowTower (leftMoment trivialExponent)
open GaloisForLFunctions.WindowTowerOfSpecZ
open GaloisForLFunctions.CohomologyOfWindowsOfSpecZ
open GaloisForLFunctions.SpacingScaleHarmonicAnalysis
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri
open GaloisForLFunctions.LatticeSectionTheory
open GaloisForLFunctions.ArithmeticEffectivityTheory
open GaloisForLFunctions.SelectivePositivityAndThresholdLaws.SemilocalPrimeTwoTrace
open GaloisForLFunctions.SquareRootThreshold

/-! ### 1. Boundary vanishing, parity orthogonality, and `ZetaWindowPositive` -/

/-- A continuous function supported in `[−c, c]` (`0 ≤ c`) vanishes on `(−c, c)ᶜ`, including at the
endpoints `±c`. -/
theorem vanishesOff_Ioo_iff_supportedIn {c : ℝ} (hc : 0 ≤ c) {u : ℝ → ℝ} (hu : Continuous u) :
    (∀ x, x ∉ Ioo (-c) c → u x = 0) ↔ SupportedIn c u := by
  constructor
  · intro hoff x hx
    refine hoff x fun hmem => ?_
    have habs : |x| < c := abs_lt.mpr hmem
    linarith
  · intro hsupp x hx
    simp only [mem_Ioo, not_and_or, not_lt] at hx
    rcases hx with hle | hge
    · have ht : Tendsto (fun k : ℕ => x - 1 / ((k : ℝ) + 1)) atTop (𝓝 x) := by
        simpa using (tendsto_const_nhds (x := x)).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hz : ∀ k : ℕ, u (x - 1 / ((k : ℝ) + 1)) = 0 := fun k => by
        have hk : 0 < 1 / ((k : ℝ) + 1) := by positivity
        refine hsupp _ ?_
        rw [abs_of_neg (by linarith)]
        linarith
      have hulim := (hu.continuousAt.tendsto).comp ht
      exact tendsto_nhds_unique (hulim.congr hz) tendsto_const_nhds
    · have ht : Tendsto (fun k : ℕ => x + 1 / ((k : ℝ) + 1)) atTop (𝓝 x) := by
        simpa using (tendsto_const_nhds (x := x)).add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hz : ∀ k : ℕ, u (x + 1 / ((k : ℝ) + 1)) = 0 := fun k => by
        have hk : 0 < 1 / ((k : ℝ) + 1) := by positivity
        refine hsupp _ ?_
        rw [abs_of_pos (by linarith)]
        linarith
      have hulim := (hu.continuousAt.tendsto).comp ht
      exact tendsto_nhds_unique (hulim.congr hz) tendsto_const_nhds

theorem hasCompactSupport_of_supportedIn {c : ℝ} {F : ℝ → ℝ} (hFc : SupportedIn c F) :
    HasCompactSupport F :=
  HasCompactSupport.intro (isCompact_Icc (a := -c) (b := c)) fun x hx =>
    hFc x (lt_abs_of_notMem_Icc hx)

theorem supportedIn_evenPartReal {c : ℝ} {F : ℝ → ℝ} (hFc : SupportedIn c F) :
    SupportedIn c (evenPartReal F) := fun u hu => by
  unfold evenPartReal
  rw [hFc u hu, hFc (-u) (by rwa [abs_neg]), add_zero, zero_div]

theorem supportedIn_oddPartReal {c : ℝ} {F : ℝ → ℝ} (hFc : SupportedIn c F) :
    SupportedIn c (oddPartReal F) := fun u hu => by
  unfold oddPartReal
  rw [hFc u hu, hFc (-u) (by rwa [abs_neg]), sub_zero, zero_div]

/-- Orthogonal parity decomposition of `fullZeroForm` on `C²_c(ℝ)`. -/
theorem fullZeroForm_eq_even_add_odd {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    fullZeroForm F = fullZeroForm (evenPartReal F) + fullZeroForm (oddPartReal F) := by
  set Fe := evenPartReal F
  set Fo := oddPartReal F
  have hFed := contDiff_evenPartReal hF
  have hFod := contDiff_oddPartReal hF
  have hFec := hasCompactSupport_evenPartReal hFc
  have hFoc := hasCompactSupport_oddPartReal hFc
  have hM := markovEnergy_ofReal_eq_even_add_odd hF hFc
  have hEo : evenPoleMoment Fo = 0 :=
    evenPoleMoment_eq_zero_of_odd (oddPartReal_neg F)
  have hOe : oddPoleMoment Fe = 0 :=
    integral_eq_zero_of_odd fun x => by
      dsimp only [Fe]
      rw [evenPartReal_neg F x, show -x / 2 = -(x / 2) by ring, Real.sinh_neg]; ring
  have hE : evenPoleMoment F = evenPoleMoment Fe := by
    unfold evenPoleMoment
    have i1 : Integrable fun x => Fe x * Real.cosh (x / 2) :=
      (hFed.continuous.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
        hFec.mul_right
    have i2 : Integrable fun x => Fo x * Real.cosh (x / 2) :=
      (hFod.continuous.mul (Real.continuous_cosh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
        hFoc.mul_right
    have hpt : (fun x => F x * Real.cosh (x / 2)) =
        fun x => Fe x * Real.cosh (x / 2) + Fo x * Real.cosh (x / 2) := by
      funext x; rw [← add_mul, evenPartReal_add_oddPartReal]
    have hz : ∫ x, Fo x * Real.cosh (x / 2) = 0 := hEo
    rw [hpt, integral_add i1 i2, hz, add_zero]
  have hO : oddPoleMoment F = oddPoleMoment Fo := by
    unfold oddPoleMoment
    have i1 : Integrable fun x => Fe x * Real.sinh (x / 2) :=
      (hFed.continuous.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
        hFec.mul_right
    have i2 : Integrable fun x => Fo x * Real.sinh (x / 2) :=
      (hFod.continuous.mul (Real.continuous_sinh.comp (continuous_id.div_const 2))).integrable_of_hasCompactSupport
        hFoc.mul_right
    have hpt : (fun x => F x * Real.sinh (x / 2)) =
        fun x => Fe x * Real.sinh (x / 2) + Fo x * Real.sinh (x / 2) := by
      funext x; rw [← add_mul, evenPartReal_add_oddPartReal]
    have hz : ∫ x, Fe x * Real.sinh (x / 2) = 0 := hOe
    rw [hpt, integral_add i1 i2, hz, zero_add]
  unfold fullZeroForm
  rw [hM, hE, hO, hEo, hOe]
  ring

private lemma fullZeroForm_eq_weilQuad' {F : ℝ → ℝ} (hF : Continuous F) (hFc : HasCompactSupport F) :
    fullZeroForm F = weilQuad F :=
  fullZeroForm_eq_re_weilFullFunctional hF hFc

/-- Orthogonal parity decomposition of `weilQuad` on `C²_c(ℝ)`. -/
theorem weilQuad_eq_even_add_odd {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) :
    weilQuad F = weilQuad (evenPartReal F) + weilQuad (oddPartReal F) := by
  rw [← fullZeroForm_eq_weilQuad' hF.continuous hFc,
    ← fullZeroForm_eq_weilQuad' (contDiff_evenPartReal hF).continuous
      (hasCompactSupport_evenPartReal hFc),
    ← fullZeroForm_eq_weilQuad' (contDiff_oddPartReal hF).continuous
      (hasCompactSupport_oddPartReal hFc)]
  exact fullZeroForm_eq_even_add_odd hF hFc

/-- **`ZetaWindowPositive c` splits into the even and odd parity sectors.** -/
theorem zetaWindowPositive_iff_even_and_odd_sectors (c : ℝ) :
    ZetaWindowPositive c ↔
      (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = F x) → SupportedIn c F → 0 ≤ weilQuad F) ∧
      (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = -F x) → SupportedIn c F → 0 ≤ weilQuad F) := by
  constructor
  · intro hW
    refine ⟨fun F hF _ hFc => ?_, fun F hF _ hFc => ?_⟩
    · have hcs := hasCompactSupport_of_supportedIn hFc
      rw [← fullZeroForm_eq_weilQuad' hF.continuous hcs]
      exact hW F hF hcs hFc
    · have hcs := hasCompactSupport_of_supportedIn hFc
      rw [← fullZeroForm_eq_weilQuad' hF.continuous hcs]
      exact hW F hF hcs hFc
  · rintro ⟨heven, hodd⟩ F hF hFc hsupp
    rw [fullZeroForm_eq_weilQuad' hF.continuous hFc, weilQuad_eq_even_add_odd hF hFc]
    exact add_nonneg
      (heven (evenPartReal F) (contDiff_evenPartReal hF) (evenPartReal_neg F)
        (supportedIn_evenPartReal hsupp))
      (hodd (oddPartReal F) (contDiff_oddPartReal hF) (oddPartReal_neg F)
        (supportedIn_oddPartReal hsupp))

/-! ### 2. Sharp prime-free half-window boundary at `2c = log 4` (`c = log 2`) -/

/-- A continuous half-window function vanishing on `(0, ∞)` and `(−∞, −c)` (`0 ≤ c`) vanishes at
`0` and `−c` as well. -/
lemma halfWindow_eq_zero_of_nonpos_or_le {c : ℝ} (_hc : 0 ≤ c) {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : ∀ u, 0 < u → f u = 0) (hfc : ∀ u, u < -c → f u = 0) :
    (∀ u, 0 ≤ u → f u = 0) ∧ (∀ u, u ≤ -c → f u = 0) := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · rcases lt_or_eq_of_le hu with hpos | rfl
    · exact h0 u hpos
    · have ht : Tendsto (fun k : ℕ => (0 : ℝ) + 1 / ((k : ℝ) + 1)) atTop (𝓝 0) := by
        simpa using (tendsto_const_nhds (x := (0 : ℝ))).add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hz : ∀ k : ℕ, f ((0 : ℝ) + 1 / ((k : ℝ) + 1)) = 0 := fun k =>
        h0 _ (by positivity)
      have hlim := (hf.continuousAt.tendsto).comp ht
      exact tendsto_nhds_unique (hlim.congr hz) tendsto_const_nhds
  · rcases lt_or_eq_of_le hu with hlt | rfl
    · exact hfc u hlt
    · have ht : Tendsto (fun k : ℕ => -c - 1 / ((k : ℝ) + 1)) atTop (𝓝 (-c)) := by
        simpa using (tendsto_const_nhds (x := -c)).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hz : ∀ k : ℕ, f (-c - 1 / ((k : ℝ) + 1)) = 0 := fun k => by
        have hk : 0 < 1 / ((k : ℝ) + 1) := by positivity
        exact hfc _ (by linarith)
      have hlim := (hf.continuousAt.tendsto).comp ht
      exact tendsto_nhds_unique (hlim.congr hz) tendsto_const_nhds

/-- **Prime-free half-window law up to `c = log 2` (`2c ≤ log 4`).** For `0 ≤ c ≤ log 2`, every
continuous function `f` supported in `[−c, 0]` has `primeSum f = 0`. -/
theorem primeSum_eq_zero_of_halfWindow_le_log_two {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ Real.log 2)
    {f : ℝ → ℝ} (hf : Continuous f) (h0 : ∀ u, 0 < u → f u = 0) (hfc : ∀ u, u < -c → f u = 0) :
    primeSum f = 0 := by
  obtain ⟨h0', hfc'⟩ := halfWindow_eq_zero_of_nonpos_or_le hc0 hf h0 hfc
  unfold primeSum
  refine (tsum_congr (g := fun _ => (0 : ℝ)) fun n => ?_).trans tsum_zero
  by_cases hn : 2 ≤ n
  · have hlog : c ≤ Real.log n :=
      hc.trans (Real.log_le_log (by norm_num) (by exact_mod_cast hn))
    have hz1 : ∀ t, f t * f (t - Real.log n) = 0 := fun t => by
      rcases le_or_gt 0 t with ht | ht
      · rw [h0' t ht, zero_mul]
      · rw [hfc' (t - Real.log n) (by linarith), mul_zero]
    have hz2 : ∀ t, f t * f (t + Real.log n) = 0 := fun t => by
      rcases le_or_gt t (-c) with ht | ht
      · rw [hfc' t ht, zero_mul]
      · rw [h0' (t + Real.log n) (by linarith), mul_zero]
    simp only [hz1, hz2, integral_zero, add_zero, mul_zero]
  · simp [vonMangoldtAtom, hn]

/-- **Purely archimedean-polar Weil diagonal on `[−c, 0]` for `0 ≤ c ≤ log 2`.** -/
theorem weilQuad_eq_archPolar_of_halfWindow_le_log_two {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ Real.log 2)
    {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (h0 : ∀ u, 0 < u → f u = 0)
    (hfc : ∀ u, u < -c → f u = 0) :
    weilQuad f = 2 * gammaHardyPhaseRate 0 * (∫ u, f u ^ 2) + levyEnergy f +
      (2 * coshHalfMoment f ^ 2 - 2 * sinhHalfMoment f ^ 2) := by
  rw [weilQuad_eq hf (hasCompactSupport_of_half h0 hfc),
    primeSum_eq_zero_of_halfWindow_le_log_two hc0 hc hf.continuous h0 hfc, sub_zero]

/-- **Sharpness of `c = log 2` (`2c = log 4`).** For every `c > log 2`, there exists a smooth
nonnegative half-window test `f` supported in `[−c, 0]` with `0 < primeSum f`. -/
theorem exists_halfWindow_primeSum_pos_of_log_two_lt {c : ℝ} (hc : Real.log 2 < c) :
    ∃ f : ℝ → ℝ, ContDiff ℝ 2 f ∧ (∀ u, 0 ≤ f u) ∧
      (∀ u, 0 < u → f u = 0) ∧ (∀ u, u < -c → f u = 0) ∧ 0 < primeSum f := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set δ := min ((c - Real.log 2) / 4) (Real.log 2 / 4)
  have hδ : 0 < δ := lt_min (by linarith) (by linarith)
  have hδ1 : δ ≤ (c - Real.log 2) / 4 := min_le_left _ _
  set f : ℝ → ℝ := fun u =>
    centreBump ((u + δ) / δ) + centreBump ((u + Real.log 2 + δ) / δ)
  have hf_diff : ContDiff ℝ 2 f :=
    (contDiff_centreBump.comp ((contDiff_id.add contDiff_const).div_const δ)).add
      (contDiff_centreBump.comp (((contDiff_id.add contDiff_const).add contDiff_const).div_const δ))
  have hf_nn : ∀ u, 0 ≤ f u := fun u => add_nonneg (centreBump_nonneg _) (centreBump_nonneg _)
  have hf0 : ∀ u, 0 < u → f u = 0 := fun u hu => by
    have b1 : centreBump ((u + δ) / δ) = 0 := by
      apply centreBump_eq_zero
      rw [abs_of_pos (div_pos (by linarith) hδ), one_le_div hδ]
      linarith
    have b2 : centreBump ((u + Real.log 2 + δ) / δ) = 0 := by
      apply centreBump_eq_zero
      rw [abs_of_pos (div_pos (by linarith) hδ), one_le_div hδ]
      linarith
    dsimp only [f]; rw [b1, b2, add_zero]
  have hfc : ∀ u, u < -c → f u = 0 := fun u hu => by
    have b1 : centreBump ((u + δ) / δ) = 0 := by
      apply centreBump_eq_zero
      rw [abs_of_neg (div_neg_of_neg_of_pos (by linarith) hδ), ← neg_div, one_le_div hδ]
      linarith
    have b2 : centreBump ((u + Real.log 2 + δ) / δ) = 0 := by
      apply centreBump_eq_zero
      rw [abs_of_neg (div_neg_of_neg_of_pos (by linarith) hδ), ← neg_div, one_le_div hδ]
      linarith
    dsimp only [f]; rw [b1, b2, add_zero]
  have hf_supp : SupportedIn c f := fun u hu => by
    rcases lt_or_ge 0 u with hp | hn
    · exact hf0 u hp
    · rw [abs_of_nonpos hn] at hu
      exact hfc u (by linarith)
  have hf_cs : HasCompactSupport f := hasCompactSupport_of_supportedIn hf_supp
  refine ⟨f, hf_diff, hf_nn, hf0, hfc, ?_⟩
  rw [primeSum_eq_sum_of_supportedIn hf_supp]
  have hmem2 : 2 ∈ Finset.range (lagRange c) := by
    rw [Finset.mem_range]
    unfold lagRange
    have hexp : (2 : ℝ) ≤ Real.exp (2 * c) := by
      have h1 : Real.log 2 < 2 * c := by linarith
      have h2 := Real.exp_lt_exp.mpr h1
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at h2
      exact h2.le
    have hceil_r : ((2 : ℕ) : ℝ) ≤ (⌈Real.exp (2 * c)⌉₊ : ℝ) := by
      norm_num only [Nat.cast_ofNat]
      exact hexp.trans (Nat.le_ceil _)
    have hceil : 2 ≤ ⌈Real.exp (2 * c)⌉₊ := Nat.cast_le.mp hceil_r
    omega
  refine Finset.sum_pos' (fun k _ => ?_) ⟨2, hmem2, ?_⟩
  · exact mul_nonneg (_root_.RHTower.vonMangoldtAtom_nonneg' k)
      (add_nonneg (integral_nonneg fun t => mul_nonneg (hf_nn t) (hf_nn _))
        (integral_nonneg fun t => mul_nonneg (hf_nn t) (hf_nn _)))
  · norm_num only [Nat.cast_ofNat]
    have hw2 : 0 < vonMangoldtAtom 2 := by
      unfold vonMangoldtAtom
      rw [if_pos (by decide), ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
      exact div_pos hlog2 (Real.sqrt_pos.mpr (by norm_num))
    have hint_nn : 0 ≤ ∫ t, f t * f (t - Real.log 2) :=
      integral_nonneg fun t => mul_nonneg (hf_nn t) (hf_nn _)
    have hint_pos : 0 < ∫ t, f t * f (t + Real.log 2) := by
      have hprod_cont : Continuous fun t => f t * f (t + Real.log 2) :=
        hf_diff.continuous.mul (hf_diff.continuous.comp (continuous_add_const _))
      have hi : Integrable fun t => f t * f (t + Real.log 2) :=
        hprod_cont.integrable_of_hasCompactSupport hf_cs.mul_right
      set a := -(Real.log 2 + 3 * δ / 2)
      set b := -(Real.log 2 + δ / 2)
      have hab : a < b := by dsimp only [a, b]; linarith
      have hIcc_pos : 0 < ∫ t in Icc a b, f t * f (t + Real.log 2) := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le]
        refine intervalIntegral.intervalIntegral_pos_of_pos_on (hprod_cont.intervalIntegrable a b)
          (fun t ht => ?_) hab
        have hb_left : centreBump ((t + Real.log 2 + δ) / δ) = 1 := by
          apply centreBump_eq_one
          rw [abs_div, abs_of_pos hδ, div_le_iff₀ hδ]
          exact abs_le.mpr ⟨by dsimp only [a] at ht; linarith [ht.1],
            by dsimp only [b] at ht; linarith [ht.2]⟩
        have hb_right : centreBump (((t + Real.log 2) + δ) / δ) = 1 := by
          simpa only [add_assoc] using hb_left
        have hft : 1 ≤ f t := by
          dsimp only [f]; rw [hb_left]; linarith [centreBump_nonneg ((t + δ) / δ)]
        have hftr : 1 ≤ f (t + Real.log 2) := by
          dsimp only [f]; rw [hb_right]
          linarith [centreBump_nonneg ((t + Real.log 2 + Real.log 2 + δ) / δ)]
        nlinarith
      have hsub : Icc a b ⊆ (univ : Set ℝ) := subset_univ _
      have hmono : (∫ t in Icc a b, f t * f (t + Real.log 2)) ≤
          ∫ t in univ, f t * f (t + Real.log 2) :=
        setIntegral_mono_set hi.integrableOn
          (Eventually.of_forall fun t => mul_nonneg (hf_nn t) (hf_nn _))
          (Eventually.of_forall hsub)
      rw [Measure.restrict_univ] at hmono
      linarith
    exact mul_pos hw2 (by linarith)

/-- **Exact boundary characterization of `2c = log 4` (`c = log 2`).** For `c > 0`, every smooth
half-window test on `[−c, 0]` is prime-free if and only if `c ≤ log 2`. -/
theorem primeFree_halfWindow_iff_le_log_two {c : ℝ} (hc0 : 0 < c) :
    (∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -c → f u = 0) →
      primeSum f = 0) ↔ c ≤ Real.log 2 := by
  constructor
  · intro hall
    by_contra hgt
    push Not at hgt
    obtain ⟨f, hf, _, h0, hfc, hpos⟩ := exists_halfWindow_primeSum_pos_of_log_two_lt hgt
    linarith [hall f hf h0 hfc]
  · exact fun hle f hf h0 hfc =>
      primeSum_eq_zero_of_halfWindow_le_log_two hc0.le hle hf.continuous h0 hfc

/-! ### 3. Exact `{2, 3}` centre-coupling truncation and half-window band below `log 4` -/

/-- For `c < log 2` (`2c < log 4`), only the primes `2` and `3` meet the reflection across `0` for
tests vanishing left of `−c`. -/
theorem centreCoupling_eq_two_three_of_lt_log_two {c : ℝ} (hc : c < Real.log 2)
    {f : ℝ → ℝ} (hfc : ∀ u, u < -c → f u = 0) :
    centreCoupling f =
      collarHankel 0 f - vonMangoldtAtom 2 * selfConv f (-Real.log 2) -
        vonMangoldtAtom 3 * selfConv f (-Real.log 3) := by
  have hsum : (∑' n : ℕ, vonMangoldtAtom n * selfConv f (2 * 0 - Real.log n)) =
      vonMangoldtAtom 2 * selfConv f (-Real.log 2) +
        vonMangoldtAtom 3 * selfConv f (-Real.log 3) := by
    rw [tsum_eq_sum (s := ({2, 3} : Finset ℕ)) fun n hn => ?_,
      Finset.sum_pair (by decide : (2 : ℕ) ≠ 3)]
    · simp
    · simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
      rcases lt_or_ge n 2 with hlt | hge
      · simp [vonMangoldtAtom, not_le.mpr hlt]
      · have h4 : 4 ≤ n := by omega
        have hlog4 : 2 * Real.log 2 ≤ Real.log n := by
          have heq : 2 * Real.log 2 = Real.log 4 := by
            rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
            norm_num
          rw [heq]
          exact Real.log_le_log (by norm_num) (by exact_mod_cast h4)
        have hz : selfConv f (2 * 0 - Real.log n) = 0 := by
          unfold selfConv
          refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
          dsimp only [Pi.zero_apply]
          rcases lt_or_ge u (-c) with hu | hu
          · rw [hfc u hu, zero_mul]
          · rw [hfc (2 * 0 - Real.log n - u) (by linarith), mul_zero]
        rw [hz, mul_zero]
  unfold centreCoupling
  rw [hsum]
  ring

/-- For every `c > 0`, `ZetaWindowPositive c` is equivalent to the symmetric half-window centre band
`|𝒞₀(f)| ≤ W(f)` on `[−c, 0]`. -/
theorem zetaWindowPositive_iff_abs_centreCoupling_le {c : ℝ} (hc : 0 < c) :
    ZetaWindowPositive c ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -c → f u = 0) →
        |centreCoupling f| ≤ weilQuad f := by
  rw [zetaWindowPositive_iff_even_and_odd_sectors,
    even_nonneg_iff_neg_centreCoupling_le hc, odd_nonneg_iff_centreCoupling_le hc]
  constructor
  · rintro ⟨he, ho⟩ f hf h0 hfc
    exact abs_le.mpr ⟨by linarith [he f hf h0 hfc], ho f hf h0 hfc⟩
  · intro hall
    refine ⟨fun f hf h0 hfc => ?_, fun f hf h0 hfc => (abs_le.mp (hall f hf h0 hfc)).2⟩
    have h := (abs_le.mp (hall f hf h0 hfc)).1
    linarith

/-- **Exact `{2, 3}` half-window band characterization below `log 4`.** For `0 < c < log 2`
(`0 < 2c < log 4`), `ZetaWindowPositive c` holds if and only if
`|𝓗₀(f) − w₂(f⋆f)(−log 2) − w₃(f⋆f)(−log 3)| ≤ W(f)` for every `C²` test `f` on `[−c, 0]`, where
`W(f)` is purely archimedean-polar (`primeSum f = 0`). -/
theorem zetaWindowPositive_iff_two_three_band {c : ℝ} (hc0 : 0 < c) (hc : c < Real.log 2) :
    ZetaWindowPositive c ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -c → f u = 0) →
        |collarHankel 0 f - vonMangoldtAtom 2 * selfConv f (-Real.log 2) -
            vonMangoldtAtom 3 * selfConv f (-Real.log 3)| ≤ weilQuad f := by
  rw [zetaWindowPositive_iff_abs_centreCoupling_le hc0]
  refine forall_congr' fun f => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun hfc => ?_
  rw [centreCoupling_eq_two_three_of_lt_log_two hc hfc]

/-- **Exact `{2, 3}` Markov–Hankel sector pair below `log 4`.** -/
theorem zetaWindowPositive_iff_two_three_markov_hankel {c : ℝ} (hc0 : 0 < c)
    (hc : c < Real.log 2) :
    ZetaWindowPositive c ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -c → f u = 0) →
        4 * sinhHalfMoment f ^ 2 ≤
            (weilQuad f - 2 * coshHalfMoment f ^ 2 + 2 * sinhHalfMoment f ^ 2) +
              leftMoment f (-(1 / 2)) ^ 2 + (∑' k : ℕ, leftMoment f (trivialExponent k) ^ 2) +
              vonMangoldtAtom 2 * selfConv f (-Real.log 2) +
              vonMangoldtAtom 3 * selfConv f (-Real.log 3) ∧
          leftMoment f (-(1 / 2)) ^ 2 + (∑' k : ℕ, leftMoment f (trivialExponent k) ^ 2) +
              vonMangoldtAtom 2 * selfConv f (-Real.log 2) +
              vonMangoldtAtom 3 * selfConv f (-Real.log 3) ≤
            (weilQuad f - 2 * coshHalfMoment f ^ 2 + 2 * sinhHalfMoment f ^ 2) +
              4 * coshHalfMoment f ^ 2 := by
  rw [zetaWindowPositive_iff_two_three_band hc0 hc]
  refine forall_congr' fun f => imp_congr_right fun hf => imp_congr_right fun h0 =>
    imp_congr_right fun hfc => ?_
  have hfcs := hasCompactSupport_of_half h0 hfc
  have hH : collarHankel 0 f =
      leftMoment f (1 / 2) ^ 2 - ∑' k : ℕ, leftMoment f (trivialExponent k) ^ 2 := by
    simp [collarHankel]
  rw [hH, leftMoment_half_eq hf.continuous hfcs, leftMoment_neg_half_eq hf.continuous hfcs, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

/-! ### 4. Retained-variance Doob–theta signed certificates in both parity sectors -/

/-- **Even-sector retained-variance signed certificate in any positive even theta gauge.** For every
even theta gauge `ω = translateSpan s α b` whose coordinate `M = Φω` is everywhere positive on `ℝ`
(in particular `ω = 1` with `M = Φ`, and every nonzero nonnegative symmetric combination of
translates of `Φ`), nonnegativity of the even sector on `[−c, c]` (`c ≥ 0`) is equivalent to the
retained-variance inequality `2V_c^S(u) + 2τ_c^S ∫ u² M cosh(x/2) ≤ J_M(u)` on even `u ∈ C²_c`
supported in `[−c, c]`. -/
theorem even_nonneg_iff_retainedVariance_evenThetaGauge {c : ℝ} (hc : 0 ≤ c)
    {ι : Type*} (s : Finset ι) (α b : ι → ℝ)
    (hMeven : ∀ x, riemannKernelReal (-x) * translateSpan s α b (-x) =
      riemannKernelReal x * translateSpan s α b x)
    (hB : translateSinhCoefficient s α b = 0)
    (hMpos : ∀ x, 0 < riemannKernelReal x * translateSpan s α b x) :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = F x) → SupportedIn c F → 0 ≤ weilQuad F) ↔
      ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
        2 * chargeVariance
            (fun x => riemannKernelReal x * translateSpan s α b x * Real.cosh (x / 2))
            (Ioo (-c) c) u +
          2 * (translateCoshCoefficient s α b / 2 - coshCharge (translateSpan s α b) (Ioo (-c) c)) *
            (∫ x, u x ^ 2 * (riemannKernelReal x * translateSpan s α b x * Real.cosh (x / 2))) ≤
          signedJumpEnergy (fun y => riemannKernelReal y * translateSpan s α b y) u := by
  set ω := translateSpan s α b
  set M : ℝ → ℝ := fun x => riemannKernelReal x * ω x
  have hM_diff : ContDiff ℝ 2 M := contDiff_riemannKernelReal.mul (contDiff_translateSpan s α b)
  constructor
  · intro heven u hu hue huc
    have hucs := hasCompactSupport_of_supportedIn huc
    set F := phiDoobTest fun y => ω y * u y
    have hF_eq : ∀ x, F x = M x * u x := fun x => by simp only [F, M, phiDoobTest, ← mul_assoc]
    have hF_diff : ContDiff ℝ 2 F := by
      rw [show F = fun x => M x * u x from funext hF_eq]
      exact hM_diff.mul hu
    have hF_even : ∀ x, F (-x) = F x := fun x => by
      rw [hF_eq, hF_eq]; dsimp only [M]; rw [hMeven x, hue x]
    have hF_supp : SupportedIn c F := fun x hx => by
      rw [hF_eq, huc x hx, mul_zero]
    have hF_cs := hasCompactSupport_of_supportedIn hF_supp
    have hnn := heven F hF_diff hF_even hF_supp
    rw [← fullZeroForm_eq_weilQuad' hF_diff.continuous hF_cs,
      fullZeroForm_evenThetaGauge_window s α b hc hMeven hB hu hucs hue] at hnn
    linarith
  · intro hcert F hF hFe hFc
    set u : ℝ → ℝ := fun x => F x / M x
    have hu_diff : ContDiff ℝ 2 u := hF.div hM_diff fun x => (hMpos x).ne'
    have hu_even : ∀ x, u (-x) = u x := fun x => by
      dsimp only [u, M]; rw [hFe x, hMeven x]
    have hu_supp : SupportedIn c u := fun x hx => by
      dsimp only [u]; rw [hFc x hx, zero_div]
    have hu_cs := hasCompactSupport_of_supportedIn hu_supp
    have hF_cs := hasCompactSupport_of_supportedIn hFc
    have hphi : (phiDoobTest fun y => ω y * u y) = F := funext fun x => by
      simp only [phiDoobTest, u, M, ← mul_assoc]
      exact mul_div_cancel₀ (F x) (hMpos x).ne'
    have hineq := hcert u hu_diff hu_even hu_supp
    have hid := fullZeroForm_evenThetaGauge_window s α b hc hMeven hB hu_diff hu_cs hu_even
    rw [hphi, fullZeroForm_eq_weilQuad' hF.continuous hF_cs] at hid
    linarith

/-- **Odd-sector retained-variance signed certificate in any shifted ground state `ω_a` (`a > 0`).**
On every symmetric window `[−c, c]` (`c > 0`) and for every shift `a > 0`, nonnegativity of the odd
sector is equivalent to nonnegativity of the retained-variance Doob–theta functional of `ω_a` across
all even `u ∈ C²_c` supported in `[−c, c]`. -/
theorem odd_nonneg_iff_retainedVariance_shiftedGroundState {a c : ℝ} (ha : 0 < a) (_hc : 0 < c) :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = -F x) → SupportedIn c F → 0 ≤ weilQuad F) ↔
      ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
        0 ≤ 2 * sameSideEnergy (shiftedGroundState a) u -
            reflectedDifferenceEnergy (shiftedGroundState a) u +
          8 * ((∫ x in Ioo (0 : ℝ) c, shiftDifference a x * Real.sinh (x / 2)) *
              (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) -
            (∫ x in Ioi (0 : ℝ), u x * shiftDifference a x * Real.sinh (x / 2)) ^ 2) +
          8 * outsideCharge a c *
            ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
  have hM_diff : ContDiff ℝ 2 (shiftDifference a) := by
    rw [show shiftDifference a = fun x => riemannKernelReal x * shiftedGroundState a x from
      funext fun x => (riemannKernelReal_mul_shiftedGroundState a x).symm]
    exact contDiff_riemannKernelReal.mul (contDiff_shiftedGroundState a)
  have hMnz : ∀ x ∈ Ioo (-(c + 1)) (c + 1), x ≠ 0 → shiftDifference a x ≠ 0 := fun x _ hx0 => by
    rcases lt_trichotomy x 0 with hlt | rfl | hgt
    · have hp := shiftDifference_pos ha (neg_pos.mpr hlt)
      rw [shiftDifference_neg] at hp
      linarith
    · exact absurd rfl hx0
    · exact (shiftDifference_pos ha hgt).ne'
  constructor
  · intro hodd u hu hue huc
    have hucs := hasCompactSupport_of_supportedIn huc
    set F := phiDoobTest fun y => shiftedGroundState a y * u y
    have hF_eq : ∀ x, F x = shiftDifference a x * u x := fun x => by
      simp only [F, phiDoobTest, ← mul_assoc, riemannKernelReal_mul_shiftedGroundState]
    have hF_diff : ContDiff ℝ 2 F := by
      rw [show F = fun x => shiftDifference a x * u x from funext hF_eq]
      exact hM_diff.mul hu
    have hF_odd : ∀ x, F (-x) = -F x := fun x => by
      rw [hF_eq, hF_eq, shiftDifference_neg, hue x]; ring
    have hF_supp : SupportedIn c F := fun x hx => by
      rw [hF_eq, huc x hx, mul_zero]
    have hF_cs := hasCompactSupport_of_supportedIn hF_supp
    have hnn := hodd F hF_diff hF_odd hF_supp
    rw [← fullZeroForm_eq_weilQuad' hF_diff.continuous hF_cs,
      fullZeroForm_shiftedGroundState_window ha c hu hucs hue] at hnn
    exact hnn
  · intro hcert F hF hFo hFc
    refine le_weilQuad_of_centreCutoff hF hFc fun n => ?_
    set ε := 1 / (2 * ((n : ℝ) + 1))
    have hε : 0 < ε := by positivity
    have hc1 : c < c + 1 := by linarith
    set Fn := cutAtCentre F n
    have hFn_diff : ContDiff ℝ 2 Fn := hF.add (hF.mul (contDiff_centreCutoff n)).neg
    have hFn_odd : ∀ x, Fn (-x) = -Fn x := cutAtCentre_neg_of_odd hFo n
    have hFn_zero : ∀ x, |x| ≤ ε → Fn x = 0 := fun x hx => cutAtCentre_eq_zero hx
    have hFn_supp : SupportedIn c Fn := fun x hx => by simp [Fn, cutAtCentre, hFc x hx]
    have hFn_cs := hasCompactSupport_of_supportedIn hFn_supp
    set u := windowGaugeQuotient ε c (c + 1) (shiftDifference a) Fn
    have hu_diff : ContDiff ℝ 2 u :=
      contDiff_windowGaugeQuotient hε hc1 hM_diff hMnz hFn_diff hFn_zero hFn_supp
    have hu_even : ∀ x, u (-x) = u x :=
      windowGaugeQuotient_even hc1 (fun x _ => shiftDifference_neg a x) hFn_odd
    have hu_supp : SupportedIn c u := fun x hx => by
      unfold u windowGaugeQuotient
      split_ifs
      · rfl
      · rw [hFn_supp x hx, zero_div]
    have hu_cs := hasCompactSupport_of_supportedIn hu_supp
    have hphi : (phiDoobTest fun y => shiftedGroundState a y * u y) = Fn := funext fun x => by
      simp only [phiDoobTest, ← mul_assoc, riemannKernelReal_mul_shiftedGroundState]
      exact windowGaugeQuotient_mul hε hc1 hMnz hFn_zero hFn_supp x
    have hineq := hcert u hu_diff hu_even hu_supp
    have hid := fullZeroForm_shiftedGroundState_window ha c hu_diff hu_cs hu_even
    rw [hphi, fullZeroForm_eq_weilQuad' hFn_diff.continuous hFn_cs] at hid
    linarith

/-- Ground-state (`ω = 1`, `M = Φ`) specialization of the even-sector retained-variance certificate. -/
theorem even_nonneg_iff_retainedVariance_groundState {c : ℝ} (hc : 0 ≤ c) :
    (∀ F : ℝ → ℝ, ContDiff ℝ 2 F → (∀ x, F (-x) = F x) → SupportedIn c F → 0 ≤ weilQuad F) ↔
      ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
        2 * chargeVariance (fun x => riemannKernelReal x * Real.cosh (x / 2)) (Ioo (-c) c) u +
          2 * (1 / 2 - ∫ x in Ioo (-c) c, riemannKernelReal x * Real.cosh (x / 2)) *
            (∫ x, u x ^ 2 * (riemannKernelReal x * Real.cosh (x / 2))) ≤
          signedJumpEnergy riemannKernelReal u := by
  set s0 : Finset Unit := {()}
  set α0 : Unit → ℝ := fun _ => 1
  set b0 : Unit → ℝ := fun _ => 0
  have hcoord : ∀ x, riemannKernelReal x * translateSpan s0 α0 b0 x = riemannKernelReal x :=
    fun x => by rw [thetaGauge_coordinate]; simp [s0, α0, b0]
  have hA : translateCoshCoefficient s0 α0 b0 = 1 := by
    unfold translateCoshCoefficient; simp [s0, α0, b0]
  have hB : translateSinhCoefficient s0 α0 b0 = 0 := by
    unfold translateSinhCoefficient; simp [s0, α0, b0]
  have hMeven : ∀ x, riemannKernelReal (-x) * translateSpan s0 α0 b0 (-x) =
      riemannKernelReal x * translateSpan s0 α0 b0 x := fun x => by
    rw [hcoord, hcoord, riemannKernelReal_neg']
  have hMpos : ∀ x, 0 < riemannKernelReal x * translateSpan s0 α0 b0 x := fun x => by
    rw [hcoord]; exact riemannKernelReal_pos x
  have hcc : coshCharge (translateSpan s0 α0 b0) (Ioo (-c) c) =
      ∫ x in Ioo (-c) c, riemannKernelReal x * Real.cosh (x / 2) := by
    unfold coshCharge
    exact setIntegral_congr_fun measurableSet_Ioo fun x _ => by rw [hcoord]
  rw [even_nonneg_iff_retainedVariance_evenThetaGauge hc s0 α0 b0 hMeven hB hMpos]
  refine forall_congr' fun u => imp_congr_right fun _ => imp_congr_right fun _ =>
    imp_congr_right fun _ => ?_
  have hfn1 : (fun y => riemannKernelReal y * translateSpan s0 α0 b0 y) = riemannKernelReal :=
    funext hcoord
  have hfn2 : (fun x => riemannKernelReal x * translateSpan s0 α0 b0 x * Real.cosh (x / 2)) =
      fun x => riemannKernelReal x * Real.cosh (x / 2) :=
    funext fun x => by rw [hcoord]
  rw [hfn1, hfn2, hA, hcc]
  simp only [hcoord]

/-- **Multi-way structural equivalence on every window of length `2c < log 4` (`0 < c < log 2`).**
Equates `ZetaWindowPositive c`, the prime-free half-window `{2, 3}` Hankel band, the `{2, 3}`
Markov–Hankel sector pair, the scaling-subsurface Castelnuovo–Severi Hodge index, Künneth
effectivity at aperture `c`, and the retained-variance Doob–theta signed certificate in `(Φ, ω_a)`. -/
theorem zetaWindowPositive_below_log_four_equivalences {a c : ℝ} (ha : 0 < a)
    (hc0 : 0 < c) (hc : c < Real.log 2) :
    (ZetaWindowPositive c ↔
      ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -c → f u = 0) →
        |collarHankel 0 f - vonMangoldtAtom 2 * selfConv f (-Real.log 2) -
            vonMangoldtAtom 3 * selfConv f (-Real.log 3)| ≤ weilQuad f) ∧
    (ZetaWindowPositive c ↔ (scalingSubsurface (realTestsAt c)).HodgeIndex) ∧
    (ZetaWindowPositive c ↔
      (RiemannInequality (scalingSubsurface (realTestsAt c)) 0 0
          (kunnethH0 (scalingSubsurface (realTestsAt c))) ∧
        DegreeBounded (scalingSubsurface (realTestsAt c))
          (kunnethH0 (scalingSubsurface (realTestsAt c))))) ∧
    (ZetaWindowPositive c ↔
      (∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
        2 * chargeVariance (fun x => riemannKernelReal x * Real.cosh (x / 2)) (Ioo (-c) c) u +
          2 * (1 / 2 - ∫ x in Ioo (-c) c, riemannKernelReal x * Real.cosh (x / 2)) *
            (∫ x, u x ^ 2 * (riemannKernelReal x * Real.cosh (x / 2))) ≤
          signedJumpEnergy riemannKernelReal u) ∧
      (∀ u : ℝ → ℝ, ContDiff ℝ 2 u → (∀ x, u (-x) = u x) → SupportedIn c u →
        0 ≤ 2 * sameSideEnergy (shiftedGroundState a) u -
            reflectedDifferenceEnergy (shiftedGroundState a) u +
          8 * ((∫ x in Ioo (0 : ℝ) c, shiftDifference a x * Real.sinh (x / 2)) *
              (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) -
            (∫ x in Ioi (0 : ℝ), u x * shiftDifference a x * Real.sinh (x / 2)) ^ 2) +
          8 * outsideCharge a c *
            ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2))) :=
  ⟨zetaWindowPositive_iff_two_three_band hc0 hc,
    zetaWindowPositive_iff_scalingSubsurface_hodgeIndex c,
    zetaWindowPositive_iff_kunneth_effectivity c,
    (zetaWindowPositive_iff_even_and_odd_sectors c).trans
      (and_congr (even_nonneg_iff_retainedVariance_groundState hc0.le)
        (odd_nonneg_iff_retainedVariance_shiftedGroundState ha hc0))⟩

/-! ### 5. Convexity and unconditional nonpositive-`w₂` exclusion in `belowLogFourBandWeights` -/

/-- The set of weight pairs `(w₂, w₃) ∈ ℝ × ℝ` satisfying the two-sided half-window `{2, 3}`
reflection band on `[−c, 0]`. -/
def belowLogFourBandWeights (c : ℝ) : Set (ℝ × ℝ) :=
  {w | ∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -c → f u = 0) →
    |collarHankel 0 f - w.1 * selfConv f (-Real.log 2) - w.2 * selfConv f (-Real.log 3)| ≤
      weilQuad f}

/-- For `0 < c < log 2`, `ZetaWindowPositive c` holds iff `(w₂, w₃)` lies in
`belowLogFourBandWeights c`. -/
theorem zetaWindowPositive_iff_mem_belowLogFourBandWeights {c : ℝ} (hc0 : 0 < c)
    (hc : c < Real.log 2) :
    ZetaWindowPositive c ↔ (vonMangoldtAtom 2, vonMangoldtAtom 3) ∈ belowLogFourBandWeights c :=
  zetaWindowPositive_iff_two_three_band hc0 hc

/-- Monotonicity of `belowLogFourBandWeights` as the half-aperture shrinks. -/
theorem belowLogFourBandWeights_anti {c₁ c₂ : ℝ} (h : c₁ ≤ c₂) :
    belowLogFourBandWeights c₂ ⊆ belowLogFourBandWeights c₁ :=
  fun _ hw f hf h0 hfc₁ => hw f hf h0 fun u hu => hfc₁ u (by linarith)

/-- **`belowLogFourBandWeights c` is a convex subset of `ℝ × ℝ`.** -/
theorem convex_belowLogFourBandWeights (c : ℝ) : Convex ℝ (belowLogFourBandWeights c) := by
  intro w₁ hw₁ w₂ hw₂ s t hs ht hst f hf h0 hfc
  have e₁ := hw₁ f hf h0 hfc
  have e₂ := hw₂ f hf h0 hfc
  have hlin : collarHankel 0 f - (s • w₁ + t • w₂).1 * selfConv f (-Real.log 2) -
        (s • w₁ + t • w₂).2 * selfConv f (-Real.log 3) =
      s * (collarHankel 0 f - w₁.1 * selfConv f (-Real.log 2) - w₁.2 * selfConv f (-Real.log 3)) +
        t * (collarHankel 0 f - w₂.1 * selfConv f (-Real.log 2) - w₂.2 * selfConv f (-Real.log 3)) := by
    simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add, smul_eq_mul]
    have h1 : collarHankel 0 f = (s + t) * collarHankel 0 f := by rw [hst, one_mul]
    linear_combination h1
  rw [hlin]
  calc |s * (collarHankel 0 f - w₁.1 * selfConv f (-Real.log 2) - w₁.2 * selfConv f (-Real.log 3)) +
          t * (collarHankel 0 f - w₂.1 * selfConv f (-Real.log 2) - w₂.2 * selfConv f (-Real.log 3))|
      ≤ |s * (collarHankel 0 f - w₁.1 * selfConv f (-Real.log 2) - w₁.2 * selfConv f (-Real.log 3))| +
          |t * (collarHankel 0 f - w₂.1 * selfConv f (-Real.log 2) - w₂.2 * selfConv f (-Real.log 3))| :=
        abs_add_le _ _
    _ = s * |collarHankel 0 f - w₁.1 * selfConv f (-Real.log 2) - w₁.2 * selfConv f (-Real.log 3)| +
          t * |collarHankel 0 f - w₂.1 * selfConv f (-Real.log 2) - w₂.2 * selfConv f (-Real.log 3)| := by
        rw [abs_mul, abs_mul, abs_of_nonneg hs, abs_of_nonneg ht]
    _ ≤ s * weilQuad f + t * weilQuad f :=
        add_le_add (mul_le_mul_of_nonneg_left e₁ hs) (mul_le_mul_of_nonneg_left e₂ ht)
    _ = weilQuad f := by rw [← add_mul, hst, one_mul]

/-- Orthogonal parity splitting of `primeSum` on compactly supported continuous functions. -/
private lemma primeSum_eq_even_add_odd {R : ℝ} {F : ℝ → ℝ} (hF : Continuous F)
    (hFR : SupportedIn R F) :
    primeSum F = primeSum (evenPartReal F) + primeSum (oddPartReal F) := by
  set Fe := evenPartReal F
  set Fo := oddPartReal F
  have hFc := hasCompactSupport_of_supportedIn hFR
  have hFeR := supportedIn_evenPartReal hFR
  have hFoR := supportedIn_oddPartReal hFR
  have hFe_cont : Continuous Fe := (hF.add (hF.comp continuous_neg)).div_const 2
  have hFo_cont : Continuous Fo := (hF.sub (hF.comp continuous_neg)).div_const 2
  have hFec := hasCompactSupport_evenPartReal hFc
  have hFoc := hasCompactSupport_oddPartReal hFc
  rw [primeSum_eq_sum_of_supportedIn hFR, primeSum_eq_sum_of_supportedIn hFeR,
    primeSum_eq_sum_of_supportedIn hFoR, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsumF : (fun x => Fe x + Fo x) = F := funext (evenPartReal_add_oddPartReal F)
  have hc_pos := crossCorr_add_add hFe_cont hFec hFo_cont hFoc (Real.log k)
  have hc_neg := crossCorr_add_add hFe_cont hFec hFo_cont hFoc (-Real.log k)
  rw [hsumF] at hc_pos hc_neg
  have hcross : crossCorr Fe Fo (Real.log k) + crossCorr Fo Fe (Real.log k) +
      (crossCorr Fe Fo (-Real.log k) + crossCorr Fo Fe (-Real.log k)) = 0 := by
    rw [crossCorr_even_odd_neg (evenPartReal_neg F) (oddPartReal_neg F),
      crossCorr_odd_even_neg (evenPartReal_neg F) (oddPartReal_neg F)]
    ring
  have hconv : ∀ (g : ℝ → ℝ),
      (∫ t, g t * g (t - Real.log k)) + (∫ t, g t * g (t + Real.log k)) =
        crossCorr g g (Real.log k) + crossCorr g g (-Real.log k) := fun g => by
    unfold crossCorr
    simp only [sub_neg_eq_add]
  rw [hconv F, hconv Fe, hconv Fo, hc_pos, hc_neg]
  linear_combination vonMangoldtAtom k * hcross

/-- On `[−21/40, 21/40]` (`21/20 < log 3`), only `k = 2` contributes to `primeSum`. -/
private lemma primeSum_eq_two_of_supportedIn_21_40 {G : ℝ → ℝ} (_hG : Continuous G)
    (hGR : SupportedIn (21 / 40) G) :
    primeSum G = 2 * vonMangoldtAtom 2 * ∫ t, G t * G (t + Real.log 2) := by
  have hlog3 : (21 / 20 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
  unfold primeSum
  rw [tsum_eq_single 2 fun n hn => ?_]
  · norm_num only [Nat.cast_ofNat]
    have hshift : (∫ t, G t * G (t - Real.log 2)) = ∫ t, G t * G (t + Real.log 2) := by
      have h : (∫ t, G (t + Real.log 2) * G (t + Real.log 2 - Real.log 2)) =
          ∫ t, G t * G (t - Real.log 2) :=
        integral_add_right_eq_self (fun t => G t * G (t - Real.log 2)) (Real.log 2)
      rw [← h]
      exact integral_congr_ae (Eventually.of_forall fun t => by
        dsimp only
        rw [show t + Real.log 2 - Real.log 2 = t by ring, mul_comm])
    rw [hshift]
    ring
  · rcases lt_or_ge n 2 with hlt | hge
    · simp [vonMangoldtAtom, not_le.mpr hlt]
    · have h3 : 3 ≤ n := by omega
      have hln : 2 * (21 / 40 : ℝ) < |Real.log n| := by
        have hle : Real.log 3 ≤ Real.log n := Real.log_le_log (by norm_num) (by exact_mod_cast h3)
        rw [abs_of_pos (by linarith)]
        linarith
      have hz1 : ∀ t, G t * G (t - Real.log n) = 0 := fun t => by
        rw [sub_eq_add_neg]
        exact mul_shift_eq_zero_of_supportedIn hGR hGR (by rwa [abs_neg]) t
      have hz2 : ∀ t, G t * G (t + Real.log n) = 0 :=
        mul_shift_eq_zero_of_supportedIn hGR hGR hln
      simp only [hz1, hz2, integral_zero, add_zero, mul_zero]

/-- On `[−21/40, 0]`, `primeSum (f + ε · collarReflect 0 f) = 2 ε w₂ (f⋆f)(−log 2)` for `ε = ±1`. -/
private lemma primeSum_reflect_pair_21_40 {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : ∀ u, 0 < u → f u = 0) (hfc : ∀ u, u < -(21 / 40) → f u = 0)
    {ε : ℝ} (hε : ε = 1 ∨ ε = -1) :
    primeSum (fun u => f u + ε * collarReflect 0 f u) =
      2 * ε * vonMangoldtAtom 2 * selfConv f (-Real.log 2) := by
  obtain ⟨h0', hfc'⟩ := halfWindow_eq_zero_of_nonpos_or_le (by norm_num) hf h0 hfc
  have hsupp : SupportedIn (21 / 40) (fun u => f u + ε * collarReflect 0 f u) :=
    supportedIn_reflect_pair (by norm_num) h0 hfc ε
  have hcont : Continuous fun u => f u + ε * collarReflect 0 f u :=
    hf.add (continuous_const.mul (hf.comp (continuous_const.sub continuous_id)))
  rw [primeSum_eq_two_of_supportedIn_21_40 hcont hsupp]
  have hl2 : (21 / 40 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hint : (∫ t, (f t + ε * collarReflect 0 f t) *
        (f (t + Real.log 2) + ε * collarReflect 0 f (t + Real.log 2))) =
      ε * selfConv f (-Real.log 2) := by
    unfold selfConv
    rw [← MeasureTheory.integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    dsimp only
    simp only [collarReflect, mul_zero, zero_sub]
    have z1 : f t * f (t + Real.log 2) = 0 := by
      rcases le_or_gt t (-(21 / 40)) with ht | ht
      · rw [hfc' t ht, zero_mul]
      · rw [h0' (t + Real.log 2) (by linarith), mul_zero]
    have z2 : f (-t) * f (t + Real.log 2) = 0 := by
      rcases le_or_gt 0 t with ht | ht
      · rw [h0' (t + Real.log 2) (by linarith), mul_zero]
      · rw [h0' (-t) (by linarith), zero_mul]
    have z3 : f (-t) * f (-(t + Real.log 2)) = 0 := by
      rcases le_or_gt 0 (-t) with ht | ht
      · rw [h0' (-t) ht, zero_mul]
      · rw [hfc' (-(t + Real.log 2)) (by linarith), mul_zero]
    have harg : -(t + Real.log 2) = -Real.log 2 - t := by ring
    rcases hε with rfl | rfl
    · calc (f t + 1 * f (-t)) * (f (t + Real.log 2) + 1 * f (-(t + Real.log 2)))
          = f t * f (t + Real.log 2) + f (-t) * f (t + Real.log 2) +
              f (-t) * f (-(t + Real.log 2)) + 1 * (f t * f (-(t + Real.log 2))) := by ring
        _ = 1 * (f t * f (-Real.log 2 - t)) := by rw [z1, z2, z3, harg]; ring
    · calc (f t + (-1) * f (-t)) * (f (t + Real.log 2) + (-1) * f (-(t + Real.log 2)))
          = f t * f (t + Real.log 2) - f (-t) * f (t + Real.log 2) +
              f (-t) * f (-(t + Real.log 2)) + (-1) * (f t * f (-(t + Real.log 2))) := by ring
        _ = (-1) * (f t * f (-Real.log 2 - t)) := by rw [z1, z2, z3, harg]; ring
  rw [hint]
  ring

/-- For `G` supported in `[−21/40, 21/40]` and `n ≥ 6` (`1/(n+1) ≤ 1/7 < log 2 − 21/40`), the
centre cutoff does not touch the prime-`2` lag: `primeSum (cutAtCentre G n) = primeSum G`. -/
private lemma primeSum_cutAtCentre_eq_of_ge_six {G : ℝ → ℝ} (hG : Continuous G)
    (hGR : SupportedIn (21 / 40) G) {n : ℕ} (hn : 6 ≤ n) :
    primeSum (cutAtCentre G n) = primeSum G := by
  have hGn_cont : Continuous (cutAtCentre G n) :=
    hG.add (hG.mul (contDiff_centreCutoff n).continuous).neg
  have hGnR : SupportedIn (21 / 40) (cutAtCentre G n) := fun u hu => by
    simp [cutAtCentre, hGR u hu]
  rw [primeSum_eq_two_of_supportedIn_21_40 hGn_cont hGnR,
    primeSum_eq_two_of_supportedIn_21_40 hG hGR]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun t => ?_)
  dsimp only
  have hnr : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hrad : 1 / ((n : ℝ) + 1) ≤ 1 / 7 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith)
  have hl2 : (693 / 1000 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  by_cases ht1 : |t| < 1 / 7
  · have hfar : (21 / 40 : ℝ) < |t + Real.log 2| := by
      have h := (abs_lt.mp ht1).1
      rw [abs_of_pos (by linarith)]
      linarith
    rw [hGnR _ hfar, hGR _ hfar, mul_zero, mul_zero]
  · by_cases ht2 : |t + Real.log 2| < 1 / 7
    · have hfar : (21 / 40 : ℝ) < |t| := by
        have h := (abs_lt.mp ht2).2
        rw [abs_of_neg (by linarith)]
        linarith
      rw [hGnR _ hfar, hGR _ hfar, zero_mul, zero_mul]
    · push Not at ht1 ht2
      rw [cutAtCentre, centreCutoff_eq_zero (hrad.trans ht1), mul_zero, neg_zero, add_zero,
        cutAtCentre, centreCutoff_eq_zero (hrad.trans ht2), mul_zero, neg_zero, add_zero]

/-- Upper semicontinuity of `weilQuad (cutAtCentre G n)` as `n → ∞` (zero `H^{1/2}` capacity of a
point in dimension `1`). -/
private lemma exists_tendsto_zero_weilQuad_cutAtCentre_le {a : ℝ} {G : ℝ → ℝ}
    (hG : ContDiff ℝ 2 G) (hGa : SupportedIn a G) :
    ∃ E : ℕ → ℝ, Tendsto E atTop (𝓝 0) ∧ ∀ n : ℕ, weilQuad (cutAtCentre G n) ≤ weilQuad G + E n := by
  have hGc := hasCompactSupport_of_supportedIn hGa
  obtain ⟨M, hM⟩ := hGc.exists_bound_of_continuous hG.continuous
  obtain ⟨KG, hKG⟩ := hG.lipschitzWith_of_hasCompactSupport hGc (by norm_num)
  obtain ⟨Lb, hLb⟩ := contDiff_centreBump.lipschitzWith_of_hasCompactSupport
    hasCompactSupport_centreBump (by norm_num)
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hGb : ∀ u, |G u| ≤ M := fun u => by simpa [Real.norm_eq_abs] using hM u
  have hGL : ∀ u v, |G u - G v| ≤ KG * |u - v| := fun u v => by
    simpa [Real.dist_eq] using hKG.dist_le_mul u v
  have hbL : ∀ x y, |centreBump x - centreBump y| ≤ Lb * |x - y| := fun x y => by
    simpa [Real.dist_eq] using hLb.dist_le_mul x y
  refine ⟨cutErr (2 * |gammaHardyPhaseRate 0|) (Real.sqrt (∫ u, G u ^ 2))
      (Real.sqrt (levyEnergy G)) (2 * primeMass a)
      (4 * Real.cosh (a / 2) * (|coshHalfMoment G| + |sinhHalfMoment G|))
      (4 * Real.cosh (a / 2) ^ 2) M KG Lb,
    tendsto_cutErr _ _ _ _ _ _ _ _ _, fun n => ?_⟩
  have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  set D : ℝ → ℝ := fun u => -(G u * centreCutoff n u)
  have hDc : ContDiff ℝ 2 D := (hG.mul (contDiff_centreCutoff n)).neg
  have hDcs : HasCompactSupport D := (hGc.mul_right).neg
  have hDa : SupportedIn a D := fun u hu => by simp [D, hGa u hu]
  have hDz : ∀ u, u ∉ Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1)) → D u = 0 :=
    fun u hu => by simp [D, centreCutoff_eq_zero (lt_abs_of_notMem_Icc hu).le]
  have hDb : ∀ u, |D u| ≤ M := fun u => by
    simp only [D, abs_neg, abs_mul]
    exact (mul_le_mul (hGb u) (abs_centreCutoff_le n u) (abs_nonneg _) hM0).trans (by linarith)
  have hx0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  have hvol : volume.real (Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))) =
      2 * (1 / ((n : ℝ) + 1)) := by
    rw [Real.volume_real_Icc_of_le (by linarith)]; ring
  have hA : (∫ u, D u ^ 2) ≤ cutA M n := by
    have e : (∫ u, D u ^ 2) = ∫ u in Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1)), D u ^ 2 :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by simp [hDz u hu]).symm
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))) (f := fun u => D u ^ 2)
      measure_Icc_lt_top (C := M ^ 2) fun u _ => by
        rw [Real.norm_eq_abs, abs_pow]
        exact pow_le_pow_left₀ (abs_nonneg _) (hDb u) 2
    rw [hvol, Real.norm_eq_abs] at h
    have h2 := le_abs_self (∫ u in Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1)), D u ^ 2)
    rw [e]; unfold cutA; linarith
  have hB : (∫ u, |D u|) ≤ cutB M n := by
    have e : (∫ u, |D u|) = ∫ u in Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1)), |D u| :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero fun u hu => by simp [hDz u hu]).symm
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume)
      (s := Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1))) (f := fun u => |D u|)
      measure_Icc_lt_top (C := M) fun u _ => by
        rw [Real.norm_eq_abs, abs_abs]; exact hDb u
    rw [hvol, Real.norm_eq_abs] at h
    have h2 := le_abs_self (∫ u in Icc (-(1 / ((n : ℝ) + 1))) (1 / ((n : ℝ) + 1)), |D u|)
    rw [e]; unfold cutB; linarith
  have hKD : 0 ≤ (KG : ℝ) + M * Lb * ((n : ℝ) + 1) :=
    add_nonneg KG.coe_nonneg (mul_nonneg (mul_nonneg hM0 Lb.coe_nonneg) hn.le)
  have hDL : ∀ u v, |D u - D v| ≤ ((KG : ℝ) + M * Lb * ((n : ℝ) + 1)) * |u - v| := fun u v => by
    have hcL : |centreCutoff n u - centreCutoff n v| ≤ Lb * ((n : ℝ) + 1) * |u - v| := by
      have h := hbL (((n : ℝ) + 1) * u) (((n : ℝ) + 1) * v)
      rw [show ((n : ℝ) + 1) * u - ((n : ℝ) + 1) * v = ((n : ℝ) + 1) * (u - v) by ring,
        abs_mul, abs_of_pos hn] at h
      simp only [centreCutoff]; linarith
    have e : D u - D v = -((G u - G v) * centreCutoff n u + G v *
        (centreCutoff n u - centreCutoff n v)) := by simp only [D]; ring
    rw [e, abs_neg]
    calc |(G u - G v) * centreCutoff n u + G v * (centreCutoff n u - centreCutoff n v)|
        ≤ |G u - G v| * |centreCutoff n u| +
            |G v| * |centreCutoff n u - centreCutoff n v| := by
          rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
      _ ≤ KG * |u - v| * 1 + M * (Lb * ((n : ℝ) + 1) * |u - v|) :=
          add_le_add (mul_le_mul (hGL u v) (abs_centreCutoff_le n u) (abs_nonneg _)
            (mul_nonneg KG.coe_nonneg (abs_nonneg _)))
            (mul_le_mul (hGb v) hcL (abs_nonneg _) hM0)
      _ = ((KG : ℝ) + M * Lb * ((n : ℝ) + 1)) * |u - v| := by ring
  have hx2 : 0 < (1 / ((n : ℝ) + 1)) ^ 2 := by positivity
  have hx21 : (1 / ((n : ℝ) + 1)) ^ 2 ≤ 1 := by
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hn]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact (pow_le_pow_left₀ (by positivity) h1 2).trans (by norm_num)
  have hlev := levyEnergy_le_lipschitz hDc hDcs hDL hx2 hx21
  have hlog : Real.log (1 / (1 / ((n : ℝ) + 1)) ^ 2) = 2 * Real.log ((n : ℝ) + 1) := by
    rw [div_pow, one_pow, one_div_one_div, Real.log_pow]; push_cast; ring
  rw [hlog] at hlev
  have hI0 : 0 ≤ ∫ u, |D u| := integral_nonneg fun u => abs_nonneg _
  have hC0 : 0 ≤ 2 * (2 * Real.log ((n : ℝ) + 1)) + levyLipConstant := by
    have hlog0 : 0 ≤ Real.log ((n : ℝ) + 1) :=
      Real.log_nonneg (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
    linarith [levyLipConstant_nonneg]
  have hV : levyEnergy D ≤ cutV M KG Lb n := by
    have hcoef : 0 ≤ Real.exp (1 / 2) * ((KG : ℝ) + M * Lb * ((n : ℝ) + 1)) *
        (1 / ((n : ℝ) + 1)) ^ 2 := mul_nonneg (mul_nonneg (Real.exp_pos _).le hKD) hx2.le
    have := add_le_add (mul_le_mul_of_nonneg_left hB hcoef) (mul_le_mul_of_nonneg_left hA hC0)
    unfold cutV; linarith
  have hpert := weilQuad_add_le hG hGc hDc hDcs hGa hDa
  have hcut : (fun u => G u + D u) = cutAtCentre G n := funext fun u => rfl
  rw [hcut] at hpert
  have hP0 : 0 ≤ 2 * primeMass a := mul_nonneg (by norm_num) (primeMass_nonneg a)
  have hθ0 : 0 ≤ 2 * |gammaHardyPhaseRate 0| := by positivity
  have hnG : 0 ≤ Real.sqrt (∫ u, G u ^ 2) := Real.sqrt_nonneg _
  have hlG : 0 ≤ Real.sqrt (levyEnergy G) := Real.sqrt_nonneg _
  have hm₀ : 0 ≤ 4 * Real.cosh (a / 2) * (|coshHalfMoment G| + |sinhHalfMoment G|) := by positivity
  have hm₁ : 0 ≤ 4 * Real.cosh (a / 2) ^ 2 := by positivity
  have s1 := Real.sqrt_le_sqrt hA
  have s2 := Real.sqrt_le_sqrt hV
  have s3 := pow_le_pow_left₀ hI0 hB 2
  have c1 := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left s1 hnG)
      (by norm_num : (0 : ℝ) ≤ 2)) hA) hθ0
  have c2 := add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left s2 hlG)
    (by norm_num : (0 : ℝ) ≤ 2)) hV
  have c3 := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left s1 hnG)
      (by norm_num : (0 : ℝ) ≤ 2)) hA) hP0
  have c4 := mul_le_mul_of_nonneg_left hB hm₀
  have c5 := mul_le_mul_of_nonneg_left s3 hm₁
  unfold cutErr
  linarith

/-- **Unconditional exclusion of the nonpositive-`w₂` half-plane from `belowLogFourBandWeights c`.**
For every half-aperture `c ≥ 21/40` (`2c ≥ 21/20 = 1.05`, in particular every `c ∈ [21/40, log 2)`),
every `w₂ ≤ 0`, and every `w₃ : ℝ`, `(w₂, w₃) ∉ belowLogFourBandWeights c`. In particular both the
prime-free weight `(0, w₃)` and the Liouville-flipped weight `(−w₂, w₃)` are excluded unconditionally
for every `w₃ : ℝ`. -/
theorem not_mem_belowLogFourBandWeights_of_nonpos {c w₂ w₃ : ℝ} (hc : 21 / 40 ≤ c)
    (hw₂ : w₂ ≤ 0) (hmem : (w₂, w₃) ∈ belowLogFourBandWeights c) : False := by
  have hw_base : (w₂, w₃) ∈ belowLogFourBandWeights (21 / 40) :=
    belowLogFourBandWeights_anti hc hmem
  obtain ⟨H, hH, hstage, hQpos⟩ := exists_first_stage_negative_frozen_positive_complete
  set F : ℝ → ℝ := fun x => H (x - 21 / 40)
  have hF_diff : ContDiff ℝ 2 F := hH.contDiff.comp (contDiff_id.sub contDiff_const)
  have hF_supp : SupportedIn (21 / 40) F := fun x hx =>
    hH.vanish (x - 21 / 40) fun hm => by
      have habs : |x| ≤ 21 / 40 := abs_le.mpr ⟨by linarith [hm.1], by linarith [hm.2]⟩
      linarith
  have hQF : weilQuad F = weilQuad H := weilQuad_comp_sub H (21 / 40)
  -- Identify `stageForm 1 H` with `weilQuad F + primeSum F`
  have hw2_eq : vonMangoldtAtom 2 = primeJumpWeight 2 := by
    unfold vonMangoldtAtom primeJumpWeight
    rw [if_pos (by decide)]
  have hw2_pos : 0 < vonMangoldtAtom 2 := by
    unfold vonMangoldtAtom
    rw [if_pos (by decide), ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    exact div_pos (Real.log_pos (by norm_num)) (Real.sqrt_pos.mpr (by norm_num))
  have hlevel : windowLevel (21 / 20) = 2 := by
    unfold windowLevel
    apply (Nat.floor_eq_iff (Real.exp_pos (21 / 20 : ℝ)).le).mpr
    exact ⟨by simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2), Nat.cast_ofNat] using
        Real.exp_le_exp.mpr (by linarith [Real.log_two_lt_d9] : Real.log 2 ≤ 21 / 20),
      by simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 3), Nat.cast_ofNat,
        show (2 : ℝ) + 1 = 3 by norm_num] using
        Real.exp_lt_exp.mpr (by linarith [Real.log_three_gt_d9] : (21 / 20 : ℝ) < Real.log 3)⟩
  have hlocal := weilQuad_eq_markovForm_windowLevel hH
  rw [hlevel] at hlocal
  have hstep := markovForm_succ hH.continuous hH.hasCompactSupport (N := 1) (by norm_num)
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hstep
  have hstage_eq : stageForm 1 H =
      weilQuad H + 2 * vonMangoldtAtom 2 * ∫ u, H u * H (u + Real.log 2) := by
    unfold stageForm
    rw [hw2_eq]
    linarith [hlocal, hstep]
  have hPF : primeSum F = 2 * vonMangoldtAtom 2 * ∫ u, H u * H (u + Real.log 2) := by
    rw [primeSum_eq_two_of_supportedIn_21_40 hF_diff.continuous hF_supp]
    congr 1
    calc (∫ t, H (t - 21 / 40) * H (t + Real.log 2 - 21 / 40))
        = ∫ t, H (t - 21 / 40) * H ((t - 21 / 40) + Real.log 2) :=
          integral_congr_ae (Eventually.of_forall fun t => by
            dsimp only
            rw [show t + Real.log 2 - 21 / 40 = (t - 21 / 40) + Real.log 2 by ring])
      _ = ∫ u, H u * H (u + Real.log 2) :=
          integral_sub_right_eq_self (fun u => H u * H (u + Real.log 2)) (21 / 40)
  set α := 1 - w₂ / vonMangoldtAtom 2
  have hα1 : 1 ≤ α := by
    have hnp : w₂ / vonMangoldtAtom 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg hw₂ hw2_pos.le
    dsimp only [α]; linarith
  have hPF_neg : primeSum F < 0 := by linarith [hstage, hstage_eq, hQpos]
  have htot_neg : weilQuad F + α * primeSum F < 0 := by
    have hle : (α - 1) * primeSum F ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by linarith) hPF_neg.le
    linarith [hstage, hstage_eq, hQF, hPF]
  -- Split `F = Fe + Fo` and cut both at the centre at a single `n ≥ 6`
  set Fe := evenPartReal F
  set Fo := oddPartReal F
  have hFe_diff := contDiff_evenPartReal hF_diff
  have hFo_diff := contDiff_oddPartReal hF_diff
  have hFe_supp := supportedIn_evenPartReal hF_supp
  have hFo_supp := supportedIn_oddPartReal hF_supp
  obtain ⟨Ee, hEe0, hEe⟩ := exists_tendsto_zero_weilQuad_cutAtCentre_le hFe_diff hFe_supp
  obtain ⟨Eo, hEo0, hEo⟩ := exists_tendsto_zero_weilQuad_cutAtCentre_le hFo_diff hFo_supp
  have hEsum : Tendsto (fun n => Ee n + Eo n) atTop (𝓝 0) := by simpa using hEe0.add hEo0
  have hev := hEsum.eventually (Iio_mem_nhds (neg_pos.mpr htot_neg))
  obtain ⟨n, hn6, hn_lt⟩ := ((eventually_ge_atTop 6).and hev).exists
  -- Evaluate `(w₂, w₃) ∈ belowLogFourBandWeights (21/40)` on the left halves of `cutAtCentre Fe n`
  -- and `cutAtCentre Fo n`
  have hsec_nonneg : ∀ (G : ℝ → ℝ) (ε : ℝ), ContDiff ℝ 2 G → SupportedIn (21 / 40) G →
      (ε = 1 ∨ ε = -1) → (∀ x, G (-x) = ε * G x) →
      0 ≤ weilQuad (cutAtCentre G n) + α * primeSum G := by
    intro G ε hG hGs hε hGp
    obtain ⟨hl, hl0, hla⟩ := leftHalf_cut_props hG hGs n
    set f := leftHalf n (cutAtCentre G n)
    have hlog3 : (21 / 20 : ℝ) < Real.log 3 := by linarith [Real.log_three_gt_d9]
    have hsc3 : selfConv f (-Real.log 3) = 0 := by
      unfold selfConv
      refine integral_eq_zero_of_ae (Eventually.of_forall fun u => ?_)
      dsimp only [Pi.zero_apply]
      rcases lt_or_ge u (-(21 / 40)) with hu | hu
      · rw [hla u hu, zero_mul]
      · rw [hla (-Real.log 3 - u) (by linarith), mul_zero]
    have hband := hw_base f hl hl0 hla
    dsimp only at hband
    rw [hsc3, mul_zero, sub_zero] at hband
    have hfcs := hasCompactSupport_of_half hl0 hla
    have hPcut : primeSum (cutAtCentre G n) = primeSum G :=
      primeSum_cutAtCentre_eq_of_ge_six hG.continuous hGs hn6
    rcases hε with rfl | rfl
    · have hevG : ∀ x, G (-x) = G x := fun x => by simpa using hGp x
      have hcut_eq := cutAtCentre_eq_add_reflect hevG n
      have hQ := weilQuad_add_collarReflect hl hfcs hl0
      have hP := primeSum_reflect_pair_21_40 hl.continuous hl0 hla (Or.inl rfl)
      simp only [one_mul] at hP
      rw [← cutAtCentre_eq_add_reflect hevG n] at hQ hP
      have hc0 := centreCoupling_eq_two_three_of_lt_log_two
        (c := 21 / 40) (by linarith [Real.log_two_gt_d9]) hla
      rw [hsc3, mul_zero, sub_zero] at hc0
      unfold centreCoupling at hc0
      rw [hc0] at hQ
      have hband_lo := (abs_le.mp hband).1
      have hid : weilQuad (cutAtCentre G n) + α * primeSum (cutAtCentre G n) =
          2 * weilQuad f + 2 * (collarHankel 0 f - w₂ * selfConv f (-Real.log 2)) := by
        rw [hQ, hP]; dsimp only [α]; field_simp [hw2_pos.ne']; ring
      rw [← hPcut, hid]
      linarith
    · have hodG : ∀ x, G (-x) = -G x := fun x => by simpa using hGp x
      have hQ := weilQuad_sub_collarReflect hl hfcs hl0
      have hP := primeSum_reflect_pair_21_40 hl.continuous hl0 hla (Or.inr rfl)
      simp only [neg_one_mul] at hP
      rw [← cutAtCentre_eq_sub_reflect hodG n] at hQ hP
      have hc0 := centreCoupling_eq_two_three_of_lt_log_two
        (c := 21 / 40) (by linarith [Real.log_two_gt_d9]) hla
      rw [hsc3, mul_zero, sub_zero] at hc0
      unfold centreCoupling at hc0
      rw [hc0] at hQ
      have hband_hi := (abs_le.mp hband).2
      have hid : weilQuad (cutAtCentre G n) + α * primeSum (cutAtCentre G n) =
          2 * weilQuad f - 2 * (collarHankel 0 f - w₂ * selfConv f (-Real.log 2)) := by
        rw [hQ, hP]; dsimp only [α]; field_simp [hw2_pos.ne']; ring
      rw [← hPcut, hid]
      linarith
  have hge_e := hsec_nonneg Fe 1 hFe_diff hFe_supp (Or.inl rfl)
    fun x => by dsimp only [Fe]; rw [evenPartReal_neg, one_mul]
  have hge_o := hsec_nonneg Fo (-1) hFo_diff hFo_supp (Or.inr rfl)
    fun x => by dsimp only [Fo]; rw [oddPartReal_neg, neg_one_mul]
  dsimp only [Fe, Fo] at hge_e hge_o
  have hF_cs := hasCompactSupport_of_supportedIn hF_supp
  have hQsplit := weilQuad_eq_even_add_odd hF_diff hF_cs
  have hPsplit := primeSum_eq_even_add_odd hF_diff.continuous hF_supp
  have hαP : α * primeSum F = α * primeSum (evenPartReal F) + α * primeSum (oddPartReal F) := by
    rw [hPsplit, mul_add]
  have h1 := hEe n
  have h2 := hEo n
  change Ee n + Eo n < -(weilQuad F + α * primeSum F) at hn_lt
  linarith

/-- Prime-free (`w₂ = 0`) and Liouville-flipped (`w₂ = −Λ(2)/√2`) weights are excluded across the
entire vertical lines `{0} × ℝ` and `{−w₂} × ℝ` for every `c ≥ 21/40`. -/
theorem zero_and_flipped_not_mem_belowLogFourBandWeights {c : ℝ} (hc : 21 / 40 ≤ c) (w₃ : ℝ) :
    (0, w₃) ∉ belowLogFourBandWeights c ∧
      (-vonMangoldtAtom 2, w₃) ∉ belowLogFourBandWeights c := by
  refine ⟨fun h => not_mem_belowLogFourBandWeights_of_nonpos hc le_rfl h,
    fun h => not_mem_belowLogFourBandWeights_of_nonpos hc ?_ h⟩
  linarith [_root_.RHTower.vonMangoldtAtom_nonneg' 2]

/-- Every admissible `{2, 3}` weight pair at `c ≥ 21/40` has strictly positive prime-`2` weight
`0 < w₂`. -/
theorem fst_pos_of_mem_belowLogFourBandWeights {c : ℝ} (hc : 21 / 40 ≤ c) {w : ℝ × ℝ}
    (hw : w ∈ belowLogFourBandWeights c) : 0 < w.1 := by
  by_contra hle
  exact not_mem_belowLogFourBandWeights_of_nonpos hc (not_lt.mp hle) hw

/-- Certifying `(w₂, w₃) ∈ belowLogFourBandWeights c` (`0 < c < log 2`) immediately yields the
level-`c` Hodge index `HodgeIndexAtLevel zetaZeroConfig c`. -/
theorem hodgeIndexAtLevel_of_mem_belowLogFourBandWeights {c : ℝ} (hc0 : 0 < c)
    (hc : c < Real.log 2)
    (hw : (vonMangoldtAtom 2, vonMangoldtAtom 3) ∈ belowLogFourBandWeights c) :
    HodgeIndexAtLevel zetaZeroConfig c :=
  hodgeIndexAtLevel_of_zetaWindowPositive
    ((zetaWindowPositive_iff_mem_belowLogFourBandWeights hc0 hc).mpr hw)

/-! ### 6. Master synthesis: complete resolution below `log 4` -/

/-- **Complete unconditional resolution of the signed window-certificate question below `log 4`:**
1. **(Odd-sector variance-dropped refutation below `log 4`):** For every `c > 273/400` (`2c > 273/200 < log 4`,
   so in particular every `c ∈ (273/400, log 2)`), no compact `C²` odd pole-charged supersolution, no
   odd non-compact theta-gauge outside-charge certificate, and no shifted ground state `ω_a` (`a > 0`)
   variance-dropped lower bound holds on `(−c, c)`.
2. **(Even-sector outside-cosh deficit on every bounded window):** For every `c ≥ 0` and every
   nonzero nonnegative theta gauge, the outside cosh charge is strictly positive, making the
   cosh-charged subsolution defect strictly negative wherever the gauge is positive.
3. **(Sharp prime-free half-window boundary at `2c = log 4`):** For `c > 0`, `primeSum f = 0` holds
   for all `C²` half-window tests on `[−c, 0]` if and only if `c ≤ log 2` (`2c ≤ log 4`).
4. **(Retained-variance & `{2, 3}` band equivalence across `(0, log 2)`):** For every `0 < c < log 2`
   (`2c < log 4`) and `a > 0`, `ZetaWindowPositive c` is equivalent to the prime-free half-window
   `{2, 3}` Hankel band `(w₂, w₃) ∈ belowLogFourBandWeights c`, to `(scalingSubsurface (realTestsAt c)).HodgeIndex`,
   to Künneth effectivity at `c`, and to the retained-variance Doob–theta signed certificate in
   `(Φ, ω_a)`, while `belowLogFourBandWeights c` is convex and excludes every `(w₂', w₃')` with
   `w₂' ≤ 0` once `c ≥ 21/40`. -/
theorem question_two_eight_complete_resolution :
    (∀ c : ℝ, 273 / 400 < c →
      (¬ ∃ ω : ℝ → ℝ, ContDiff ℝ 2 ω ∧ HasCompactSupport ω ∧
        (∀ x ∈ Ioo (-c) c, ω (-x) = -ω x) ∧
        (∀ x ∈ Ioo (0 : ℝ) c, 0 < ω x) ∧
        (∀ x ∈ Ioo (-c) c, 0 ≤ ω x * (markovDefect ω x -
          2 * sinhCharge ω (Ioo (-c) c) * (riemannKernelReal x * Real.sinh (x / 2)))) ∧
        (∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u → (∀ x, u (-x) = u x) →
          (∀ x, x ∉ Ioo (-c) c → u x = 0) →
          0 ≤ signedJumpEnergy (fun y => riemannKernelReal y * ω y) u)) ∧
      (∀ a : ℝ, 0 < a → ∃ u : ℝ → ℝ, ContDiff ℝ 2 u ∧ HasCompactSupport u ∧
        (∀ x, u (-x) = u x) ∧ (∀ x, x ∉ Ioo (-c) c → u x = 0) ∧
        2 * sameSideEnergy (shiftedGroundState a) u -
          reflectedDifferenceEnergy (shiftedGroundState a) u +
          8 * outsideCharge a c *
            (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) < 0)) ∧
    (∀ (c : ℝ), 0 ≤ c → ∀ (s : Finset ℕ) (α b : ℕ → ℝ),
      (∀ j ∈ s, 0 ≤ α j) → (∃ j ∈ s, 0 < α j) →
      0 < translateCoshCoefficient s α b / 2 - coshCharge (translateSpan s α b) (Ioo (-c) c)) ∧
    (∀ c : ℝ, 0 < c →
      ((∀ f : ℝ → ℝ, ContDiff ℝ 2 f → (∀ u, 0 < u → f u = 0) → (∀ u, u < -c → f u = 0) →
        primeSum f = 0) ↔ c ≤ Real.log 2)) ∧
    (∀ c : ℝ, 0 < c → c < Real.log 2 →
      Convex ℝ (belowLogFourBandWeights c) ∧
      (ZetaWindowPositive c ↔ (vonMangoldtAtom 2, vonMangoldtAtom 3) ∈ belowLogFourBandWeights c) ∧
      (ZetaWindowPositive c ↔ (scalingSubsurface (realTestsAt c)).HodgeIndex) ∧
      (21 / 40 ≤ c → ∀ w₂ w₃ : ℝ, w₂ ≤ 0 → (w₂, w₃) ∉ belowLogFourBandWeights c)) :=
  ⟨fun _ hc => ⟨not_exists_odd_sinhCharged_gauge_below_log_four hc,
      fun _ ha => exists_shiftedGroundState_windowLower_neg_below_log_four ha hc⟩,
    fun _ hc s α b hα0 hαpos => outsideCosh_pos_of_nonneg_weights s α b hc hα0 hαpos,
    fun _ hc0 => primeFree_halfWindow_iff_le_log_two hc0,
    fun c hc0 hc => ⟨convex_belowLogFourBandWeights c,
      zetaWindowPositive_iff_mem_belowLogFourBandWeights hc0 hc,
      zetaWindowPositive_iff_scalingSubsurface_hodgeIndex c,
      fun hc21 _ _ hw₂ hmem => not_mem_belowLogFourBandWeights_of_nonpos hc21 hw₂ hmem⟩⟩

end GaloisForLFunctions.SignedWindowCriticality.BelowLogFour

end
