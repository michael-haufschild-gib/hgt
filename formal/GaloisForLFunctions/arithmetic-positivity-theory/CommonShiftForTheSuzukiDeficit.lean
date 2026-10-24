import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalFamilyContraction
import GaloisForLFunctions.«arithmetic-positivity-theory».SourceSelectionInTheFullWeilCone

/-!
# A Common Shift for the Suzuki Deficit: Universal First-Variation Envelopes, Block-Uniform Contraction, and Receiver Transfer

`SuzukiCriticalFamilyContraction.lean` proves that for each high dyadic critical source `g_b` and
each sufficiently fine smoothing index `k`, there exists a positive shift neighbourhood
`ω ∈ (0, ω₀)` on which the literal Suzuki pairing has a strict first-order deficit
`suzukiCriticalSourcePairing (smoothCompactSource g_b k) ω < autocorr (smoothCompactSource g_b k) 0`,
with `ω₀` chosen source by source and smoothing index by smoothing index.

This module resolves all three questions of §7.10:

1. **Universal First-Variation Error Envelope (`suzukiUniversalPrimaryRemainder`,
   `suzukiFirstVariationEnvelope`, `abs_suzukiCriticalSourcePairing_firstVariation_sub_le`,
   `exists_common_suzuki_shift_of_bounded_envelope_family`)**:
   Establishes an explicit source-independent error envelope `suzukiFirstVariationEnvelope A E₀ B ω`
   that tends to `0` as `ω → 0⁺`, scales homogeneously of degree `1` in `(E₀, B)`, and bounds
   `|(autocorr f 0 - suzukiCriticalSourcePairing f ω) / ω - Re W_Λ(f ⋆ f̃)|` for every compact
   `C²` real test `f` with correlation cutoff `A > 0`, energy `autocorr f 0 ≤ E₀`, and correlation
   increment slope `autocorr f 0 - autocorr f t ≤ B * t` (`t > 0`).

2. **Common Smoothing and Shift Thresholds Uniform in the Pattern `b`, Smoothing Index `k`, and
   Scale Block (`exists_common_suzuki_shift_dyadic_blocks`,
   `exists_common_suzuki_shift_bounded_block_horizon`,
   `exists_common_suzuki_shift_lacunary_windows`)**:
   Decomposing `criticalTruncatedSource V S b` into single-scale basis modes shows that its
   amplitude and Lipschitz constants scale as `O(√(∑_{n ∈ S} b_n²))` with coefficients monotone in
   `S`. Because mollification contracts translation increments (`autocorr_smooth_sub_le`), all
   smoothed sources `smoothCompactSource (criticalTruncatedTest hV S b) k` (`k ∈ ℕ`) share a single
   `k`-independent envelope `(A_V, E₀(V, S) E_b, B₀(V, S) E_b)`. Consequently, at every dyadic
   block scale `M ≥ M₀` (and over every bounded horizon `M₀ ≤ M ≤ M_max`, as well as on lacunary
   polynomial-width multi-windows), there exist a **common smoothing threshold `k₀`** and a
   **common shift threshold `ω₀ > 0`** — independent of the pattern `b`, the block `S ⊆ [M, 2M]`,
   and `k ≥ k₀` — on which the strict first-order Suzuki deficit holds simultaneously.

3. **Truncation Dependence (`V → ∞`), Untruncated `O(r^{-3/2})` Correlation Decay, and Receiver
   Transfer Without Archimedean Subsidy (`abs_criticalFactorialSource_correlation_le_rpow`,
   `exists_common_suzuki_shift_small_aperture_receiver`,
   `exists_common_suzuki_shift_odd_receiver_past_two`,
   `suzuki_small_shift_deficit_iff_receiver_weil_ge`,
   `zetaZeroWidth_le_of_graded_odd_suzuki_deficit`,
   `riemannHypothesis_iff_suzuki_small_shift_non_overshoot`)**:
   Separates the `V`-dependence of the literal unsubtracted growing polar window `A_V asymp 2 log V`
   from the `V`-independent complete Weil energy margin and the untruncated `O(r^{-3/2})`
   correlation decay of `criticalFactorialSource`, proves unconditional common-shift Suzuki deficits
   directly on small-aperture receiver tests (`[-3/10, 3/10]` and odd tests on `[-181/500, 181/500]`
   past `(log 2)/2`) with no scale parameter `M → ∞`, and proves that small-shift Suzuki deficit
   floors on odd receiver tests transfer directly to `zetaZeroWidth ≤ σ` and `RiemannHypothesis`
   without any archimedean subsidy.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real BigOperators CompactlySupported
open _root_.Zeta23 _root_.RHTower _root_.RHTower.WeilSpectral
open _root_.RHTower.ArchimedeanAnomaly _root_.RHTower.ArchimedeanExactForm
open _root_.RHTower.CHMDDoobGraph _root_.RHTower.WeilMarkovPole
open GaloisForLFunctions.BiScaleUncertainty
open GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.SquareRootThreshold

noncomputable section
namespace GaloisForLFunctions.ArithmeticPositivityTheory
set_option autoImplicit false

/-! ## Section 1: Universal First-Variation Error Envelope for the Literal Suzuki Pairing -/

/-- Source-independent first-moment remainder of the compensated primary Suzuki Beta density
against its critical tangent `2 e^{-5t/2} / (1 - e^{-2t})`. -/
def suzukiUniversalPrimaryRemainder (omega : ℝ) : ℝ :=
  ∫ t in Ioi 0, t * |suzukiCriticalPrimaryDensity omega t / omega -
    2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))|

theorem suzukiUniversalPrimaryRemainder_nonneg (omega : ℝ) :
    0 ≤ suzukiUniversalPrimaryRemainder omega :=
  setIntegral_nonneg measurableSet_Ioi fun _ ht => mul_nonneg (le_of_lt ht) (abs_nonneg _)

private theorem archLevySinhWeight_eq_div {t : ℝ} (ht : 0 < t) :
    archLevySinhWeight t = 2 * Real.exp (-t / 2) / (1 - Real.exp (-2 * t)) := by
  rw [archLevySinhWeight, exp_half_div_sinh_eq ht, archLevyDensity]
  ring

private theorem primary_tangent_nonneg_and_le_levy {t : ℝ} (ht : 0 < t) :
    0 ≤ 2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)) ∧
    2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)) ≤ archLevySinhWeight t := by
  have hb : 0 < 1 - Real.exp (-2 * t) :=
    sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))
  have he : Real.exp (-(5 / 2 : ℝ) * t) ≤ Real.exp (-t / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  refine ⟨by positivity, ?_⟩
  rw [archLevySinhWeight_eq_div ht]
  exact div_le_div_of_nonneg_right (by linarith) hb.le

private theorem abs_primary_density_sub_tangent_le {omega t : ℝ}
    (homega : 0 < omega) (homega2 : omega ≤ 2) (ht : 0 < t) :
    |suzukiCriticalPrimaryDensity omega t / omega -
      2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))| ≤
      (suzukiCriticalPrimaryScale omega + 1) * archLevySinhWeight t := by
  have h1_pos : 0 ≤ suzukiCriticalPrimaryDensity omega t / omega :=
    div_nonneg (suzukiCriticalPrimaryDensity_pos homega ht).le homega.le
  have h1_le : suzukiCriticalPrimaryDensity omega t / omega ≤
      suzukiCriticalPrimaryScale omega * archLevySinhWeight t := by
    rw [archLevySinhWeight_eq_div ht]
    exact suzukiCriticalPrimaryDensity_div_le homega homega2 ht
  obtain ⟨h2_pos, h2_le⟩ := primary_tangent_nonneg_and_le_levy ht
  calc |suzukiCriticalPrimaryDensity omega t / omega -
        2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))|
      ≤ |suzukiCriticalPrimaryDensity omega t / omega| +
          |2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))| := abs_sub _ _
    _ = suzukiCriticalPrimaryDensity omega t / omega +
          2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)) := by
          rw [abs_of_nonneg h1_pos, abs_of_nonneg h2_pos]
    _ ≤ suzukiCriticalPrimaryScale omega * archLevySinhWeight t + archLevySinhWeight t :=
          add_le_add h1_le h2_le
    _ = (suzukiCriticalPrimaryScale omega + 1) * archLevySinhWeight t := by ring

theorem integrableOn_suzukiUniversalPrimaryRemainder {omega : ℝ}
    (homega : 0 < omega) (homega2 : omega ≤ 2) :
    IntegrableOn (fun t => t * |suzukiCriticalPrimaryDensity omega t / omega -
      2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))|) (Ioi 0) := by
  have hm : Measurable (fun t : ℝ => t * |suzukiCriticalPrimaryDensity omega t / omega -
      2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))|) :=
    measurable_id.mul (((measurable_suzukiCriticalPrimaryDensity omega).div measurable_const).sub
      (by fun_prop)).abs
  refine (integrableOn_mul_archLevySinhWeight.const_mul
    (suzukiCriticalPrimaryScale omega + 1)).mono' hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  change 0 < t at ht
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht.le (abs_nonneg _))]
  calc t * |suzukiCriticalPrimaryDensity omega t / omega -
        2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))|
      ≤ t * ((suzukiCriticalPrimaryScale omega + 1) * archLevySinhWeight t) :=
        mul_le_mul_of_nonneg_left (abs_primary_density_sub_tangent_le homega homega2 ht) ht.le
    _ = (suzukiCriticalPrimaryScale omega + 1) * (t * archLevySinhWeight t) := by ring

/-- The universal primary remainder vanishes as `ω → 0⁺`, independently of any test source. -/
theorem tendsto_suzukiUniversalPrimaryRemainder :
    Tendsto suzukiUniversalPrimaryRemainder (𝓝[>] 0) (𝓝 0) := by
  have ha : ∀ᶠ omega in 𝓝[>] (0 : ℝ), suzukiCriticalPrimaryScale omega < 2 :=
    (tendsto_suzukiCriticalPrimaryScale.mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds (by norm_num : (1 : ℝ) < 2))
  have ho : ∀ᶠ omega in 𝓝[>] (0 : ℝ), omega < 2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 2))
  have hlim : Tendsto suzukiUniversalPrimaryRemainder (𝓝[>] 0)
      (𝓝 (∫ _t in Ioi (0 : ℝ), (0 : ℝ))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun t => 3 * (t * archLevySinhWeight t)) ?_ ?_
      (integrableOn_mul_archLevySinhWeight.const_mul 3) ?_
    · exact Eventually.of_forall fun omega =>
        (measurable_id.mul (((measurable_suzukiCriticalPrimaryDensity omega).div
          measurable_const).sub (by fun_prop)).abs).aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin, ho, ha] with omega homega ho ha
      change 0 < omega at homega
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      change 0 < t at ht
      have hw := (archLevySinhWeight_pos ht).le
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht.le (abs_nonneg _))]
      calc t * |suzukiCriticalPrimaryDensity omega t / omega -
            2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))|
          ≤ t * ((suzukiCriticalPrimaryScale omega + 1) * archLevySinhWeight t) :=
            mul_le_mul_of_nonneg_left (abs_primary_density_sub_tangent_le homega ho.le ht) ht.le
        _ ≤ t * (3 * archLevySinhWeight t) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hw) ht.le
        _ = 3 * (t * archLevySinhWeight t) := by ring
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hsub := ((tendsto_suzukiCriticalPrimaryDensity_div ht).sub_const
        (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))).abs.const_mul t
      simpa only [sub_self, abs_zero, mul_zero] using hsub
  simpa only [integral_zero] using hlim

/-- Any linear bound `autocorr f 0 - autocorr f t ≤ B * t` on positive correlation increments
controls `biScaleLevyEnergy f` by `B * archWeightFirstMoment`. -/
theorem biScaleLevyEnergy_le_of_increment_slope {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) {B : ℝ}
    (hB : ∀ t : ℝ, 0 < t → autocorr f 0 - autocorr f t ≤ B * t) :
    biScaleLevyEnergy f ≤ B * archWeightFirstMoment := by
  unfold biScaleLevyEnergy archWeightFirstMoment
  rw [← integral_const_mul]
  refine setIntegral_mono_on (integrableOn_biScaleLevyIntegrand hf hfc)
    (integrableOn_mul_archLevySinhWeight.const_mul B) measurableSet_Ioi fun t ht => ?_
  calc (autocorr f 0 - autocorr f t) * archLevySinhWeight t
      ≤ (B * t) * archLevySinhWeight t :=
        mul_le_mul_of_nonneg_right (hB t ht) (archLevySinhWeight_pos ht).le
    _ = B * (t * archLevySinhWeight t) := by ring

/-- Universal source-independent error envelope for the positive-shift Suzuki first variation on
any compact `C²` source with correlation cutoff `A`, zero-lag energy bound `E₀`, and correlation
increment slope `B`. -/
def suzukiFirstVariationEnvelope (A E₀ B omega : ℝ) : ℝ :=
  let Mω := suzukiCriticalPrimaryMass omega
  let Sω := suzukiCriticalPrimaryScale omega
  let Kω := Real.sqrt (max (E₀ * B) 0) *
    Real.sqrt (max (2 * Mω * Sω * omega * archWeightFirstMoment) 0)
  let primErr := Kω + |Mω - 1| * E₀
  let cuspRad := Kω + 2 * omega * Mω * E₀ * A * Real.exp (A / 2)
  (|(Mω - 1) / omega - (Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re)| * E₀ +
      B * suzukiUniversalPrimaryRemainder omega) +
    2 * A * Real.exp (A / 2) * (primErr + omega * A * E₀) +
    ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
      Real.exp (-Real.log n / 2) *
        (|suzukiShiftedCoefficient omega n / omega| * cuspRad +
          |suzukiShiftedCoefficient omega n / omega * Mω -
            2 * ArithmeticFunction.vonMangoldt n| * E₀)

theorem suzukiFirstVariationEnvelope_nonneg {A E₀ B : ℝ} (hA : 0 ≤ A) (hE₀ : 0 ≤ E₀)
    (hB : 0 ≤ B) {omega : ℝ} (homega : 0 < omega) (homega2 : omega ≤ 2) :
    0 ≤ suzukiFirstVariationEnvelope A E₀ B omega := by
  have hMω : 0 ≤ suzukiCriticalPrimaryMass omega := by
    rw [← integral_suzukiCriticalPrimaryDensity homega (by linarith)]
    exact setIntegral_nonneg measurableSet_Ioi fun _ ht =>
      (suzukiCriticalPrimaryDensity_pos homega ht).le
  have hR := suzukiUniversalPrimaryRemainder_nonneg omega
  unfold suzukiFirstVariationEnvelope
  dsimp only
  refine add_nonneg (add_nonneg ?_ ?_) ?_
  · positivity
  · positivity
  · refine Finset.sum_nonneg fun n _ => mul_nonneg (Real.exp_pos _).le ?_
    positivity

/-- Exact degree-`1` homogeneity of `suzukiFirstVariationEnvelope` in `(E₀, B)`. -/
theorem suzukiFirstVariationEnvelope_mul (A E₀ B : ℝ) {c : ℝ} (hc : 0 ≤ c) (omega : ℝ) :
    suzukiFirstVariationEnvelope A (c * E₀) (c * B) omega =
      c * suzukiFirstVariationEnvelope A E₀ B omega := by
  have hmax : max ((c * E₀) * (c * B)) 0 = c ^ 2 * max (E₀ * B) 0 := by
    rw [show (c * E₀) * (c * B) = c ^ 2 * (E₀ * B) by ring,
      ← mul_max_of_nonneg _ _ (sq_nonneg c), mul_zero]
  have hsqrt : Real.sqrt (max ((c * E₀) * (c * B)) 0) = c * Real.sqrt (max (E₀ * B) 0) := by
    rw [hmax, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]
  unfold suzukiFirstVariationEnvelope
  dsimp only
  rw [hsqrt, Finset.mul_sum]
  ring_nf
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- Monotonicity of `suzukiFirstVariationEnvelope` in the energy and increment bounds `(E₀, B)`. -/
theorem suzukiFirstVariationEnvelope_mono {A E₀ E₀' B B' omega : ℝ}
    (hA : 0 ≤ A) (hE₀ : 0 ≤ E₀) (hEE : E₀ ≤ E₀') (hB : 0 ≤ B) (hBB : B ≤ B')
    (homega : 0 < omega) (homega2 : omega ≤ 2) :
    suzukiFirstVariationEnvelope A E₀ B omega ≤
      suzukiFirstVariationEnvelope A E₀' B' omega := by
  have hMω : 0 ≤ suzukiCriticalPrimaryMass omega := by
    rw [← integral_suzukiCriticalPrimaryDensity homega (by linarith)]
    exact setIntegral_nonneg measurableSet_Ioi fun _ ht =>
      (suzukiCriticalPrimaryDensity_pos homega ht).le
  have hR := suzukiUniversalPrimaryRemainder_nonneg omega
  have hK : Real.sqrt (max (E₀ * B) 0) ≤ Real.sqrt (max (E₀' * B') 0) :=
    Real.sqrt_le_sqrt (max_le_max (mul_le_mul hEE hBB hB (hE₀.trans hEE)) le_rfl)
  unfold suzukiFirstVariationEnvelope
  dsimp only
  gcongr

private theorem suzukiShiftedCoefficient_zero_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    suzukiShiftedCoefficient 0 n = 0 := by
  obtain ⟨p, hp⟩ := Nat.nonempty_primeFactors.mpr hn
  rw [suzukiShiftedCoefficient,
    Finset.prod_eq_zero hp (by simp : 1 - (p : ℝ) ^ (-2 * (0 : ℝ)) = 0)]
  simp

private theorem tendsto_suzukiShiftedCoefficient_div {n : ℕ} (hn : 2 ≤ n) :
    Tendsto (fun omega : ℝ => suzukiShiftedCoefficient omega n / omega) (𝓝[>] 0)
      (𝓝 (2 * ArithmeticFunction.vonMangoldt n)) := by
  simpa only [zero_add, suzukiShiftedCoefficient_zero_of_two_le hn, sub_zero, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using
    (hasDerivAt_suzukiShiftedCoefficient (by omega : 1 ≤ n)).tendsto_slope_zero_right

/-- The universal first-variation envelope tends to `0` as `ω → 0⁺` for every `(A, E₀, B)`. -/
theorem tendsto_suzukiFirstVariationEnvelope (A E₀ B : ℝ) :
    Tendsto (suzukiFirstVariationEnvelope A E₀ B) (𝓝[>] 0) (𝓝 0) := by
  have hm := tendsto_suzukiCriticalPrimaryMass.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have hs := tendsto_suzukiCriticalPrimaryScale.mono_left (nhdsWithin_le_nhds (s := Ioi 0))
  have hi : Tendsto (fun omega : ℝ => omega) (𝓝[>] 0) (𝓝 0) := continuousWithinAt_id
  have hK : Tendsto (fun omega : ℝ =>
      Real.sqrt (max (E₀ * B) 0) *
        Real.sqrt (max (2 * suzukiCriticalPrimaryMass omega *
          suzukiCriticalPrimaryScale omega * omega * archWeightFirstMoment) 0))
      (𝓝[>] 0) (𝓝 0) := by
    have hin := (((hm.const_mul 2).mul hs).mul hi).mul_const archWeightFirstMoment
    have hmax := hin.max tendsto_const_nhds
    have hrt := (Real.continuous_sqrt.continuousAt.tendsto.comp hmax).const_mul
      (Real.sqrt (max (E₀ * B) 0))
    simpa only [Function.comp_apply, mul_zero, zero_mul, max_self, Real.sqrt_zero] using hrt
  have hprimErr : Tendsto (fun omega : ℝ =>
      Real.sqrt (max (E₀ * B) 0) *
        Real.sqrt (max (2 * suzukiCriticalPrimaryMass omega *
          suzukiCriticalPrimaryScale omega * omega * archWeightFirstMoment) 0) +
        |suzukiCriticalPrimaryMass omega - 1| * E₀) (𝓝[>] 0) (𝓝 0) := by
    simpa only [sub_self, abs_zero, zero_mul, add_zero] using
      hK.add (((hm.sub_const 1).abs).mul_const E₀)
  have hcuspRad : Tendsto (fun omega : ℝ =>
      Real.sqrt (max (E₀ * B) 0) *
        Real.sqrt (max (2 * suzukiCriticalPrimaryMass omega *
          suzukiCriticalPrimaryScale omega * omega * archWeightFirstMoment) 0) +
        2 * omega * suzukiCriticalPrimaryMass omega * E₀ * A * Real.exp (A / 2))
      (𝓝[>] 0) (𝓝 0) := by
    have hpole := (((((hi.const_mul 2).mul hm).mul_const E₀).mul_const A).mul_const (Real.exp (A / 2)))
    simpa only [mul_zero, zero_mul, add_zero] using hK.add hpole
  have h1 : Tendsto (fun omega : ℝ =>
      |(suzukiCriticalPrimaryMass omega - 1) / omega -
        (Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re)| * E₀ +
      B * suzukiUniversalPrimaryRemainder omega) (𝓝[>] 0) (𝓝 0) := by
    have hsec := ((tendsto_suzukiCriticalPrimaryMass_secant.sub_const _).abs).mul_const E₀
    have hrem := tendsto_suzukiUniversalPrimaryRemainder.const_mul B
    simpa only [sub_self, abs_zero, zero_mul, mul_zero, add_zero] using hsec.add hrem
  have h2 : Tendsto (fun omega : ℝ =>
      2 * A * Real.exp (A / 2) *
        ((Real.sqrt (max (E₀ * B) 0) *
            Real.sqrt (max (2 * suzukiCriticalPrimaryMass omega *
              suzukiCriticalPrimaryScale omega * omega * archWeightFirstMoment) 0) +
            |suzukiCriticalPrimaryMass omega - 1| * E₀) +
          omega * A * E₀)) (𝓝[>] 0) (𝓝 0) := by
    have hlin := (hi.mul_const A).mul_const E₀
    simpa only [zero_mul, mul_zero, add_zero] using
      (hprimErr.add hlin).const_mul (2 * A * Real.exp (A / 2))
  have h3 : Tendsto (fun omega : ℝ =>
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
        Real.exp (-Real.log n / 2) *
          (|suzukiShiftedCoefficient omega n / omega| *
            (Real.sqrt (max (E₀ * B) 0) *
              Real.sqrt (max (2 * suzukiCriticalPrimaryMass omega *
                suzukiCriticalPrimaryScale omega * omega * archWeightFirstMoment) 0) +
              2 * omega * suzukiCriticalPrimaryMass omega * E₀ * A * Real.exp (A / 2)) +
            |suzukiShiftedCoefficient omega n / omega * suzukiCriticalPrimaryMass omega -
              2 * ArithmeticFunction.vonMangoldt n| * E₀)) (𝓝[>] 0) (𝓝 0) := by
    have hsum := tendsto_finsetSum (Finset.Icc 2 ⌊Real.exp A⌋₊) fun n hn => by
      have hn2 : 2 ≤ n := (Finset.mem_Icc.mp hn).1
      have hc := tendsto_suzukiShiftedCoefficient_div hn2
      have ha1 := hc.abs.mul hcuspRad
      have ha2 := (((hc.mul hm).sub_const (2 * ArithmeticFunction.vonMangoldt n)).abs).mul_const E₀
      exact (ha1.add ha2).const_mul (Real.exp (-Real.log n / 2))
    simpa only [mul_one, sub_self, abs_zero, zero_mul, mul_zero, add_zero,
      Finset.sum_const_zero] using hsum
  unfold suzukiFirstVariationEnvelope
  dsimp only
  simpa only [add_zero] using (h1.add h2).add h3

private theorem abs_primaryCusp_secant_sub_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {E₀ B omega : ℝ} (hE₀ : autocorr f 0 ≤ E₀) (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 < t → autocorr f 0 - autocorr f t ≤ B * t)
    (homega : 0 < omega) (homega2 : omega ≤ 2) :
    |(suzukiCriticalPrimaryCusp f omega 0 - autocorr f 0) / omega -
      ((Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re) * autocorr f 0 -
        ∫ t in Ioi 0, (autocorr f 0 - autocorr f t) *
          (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))))| ≤
      |(suzukiCriticalPrimaryMass omega - 1) / omega -
        (Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re)| * E₀ +
      B * suzukiUniversalPrimaryRemainder omega := by
  have homega5 : omega < 5 / 2 := by linarith
  have hR0 : 0 ≤ autocorr f 0 := GaloisForLFunctions.BiScaleUncertainty.autocorr_zero_nonneg f
  have hi := integrableOn_suzukiCriticalPrimaryDensity homega homega5
  have hp0 : IntegrableOn (fun t => autocorr f t * suzukiCriticalPrimaryDensity omega t) (Ioi 0) := by
    simpa only [zero_add] using integrableOn_suzukiCriticalPrimaryCusp_integrand hf hfc homega homega5 0
  have hcomp_int : IntegrableOn (fun t => (autocorr f 0 - autocorr f t) *
      (suzukiCriticalPrimaryDensity omega t / omega)) (Ioi 0) := by
    refine ((hi.const_mul (autocorr f 0)).sub hp0).div_const omega |>.congr_fun ?_ measurableSet_Ioi
    intro t _
    dsimp only [Pi.sub_apply]
    ring
  have htan_int : IntegrableOn (fun t => (autocorr f 0 - autocorr f t) *
      (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))) (Ioi 0) := by
    have hcm : ContinuousOn (fun t => (autocorr f 0 - autocorr f t) *
        (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))) (Ioi 0) :=
      (continuousOn_const.sub (continuous_autocorr hf hfc).continuousOn).mul
        ((by fun_prop : Continuous fun t : ℝ => 2 * Real.exp (-(5 / 2 : ℝ) * t)).continuousOn.div
          (by fun_prop : Continuous fun t : ℝ => 1 - Real.exp (-2 * t)).continuousOn
          fun t ht => (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith [show 0 < t from ht]))).ne')
    refine (integrableOn_biScaleLevyIntegrand hf hfc).mono'
      (hcm.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hDt := autocorr_sub_nonneg hfc hf.continuous t
    obtain ⟨h1, h2⟩ := primary_tangent_nonneg_and_le_levy ht
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hDt h1)]
    exact mul_le_mul_of_nonneg_left h2 hDt
  have hsec_eq : (suzukiCriticalPrimaryCusp f omega 0 - autocorr f 0) / omega =
      (suzukiCriticalPrimaryMass omega - 1) / omega * autocorr f 0 -
        ∫ t in Ioi 0, (autocorr f 0 - autocorr f t) *
          (suzukiCriticalPrimaryDensity omega t / omega) := by
    have he : (∫ t in Ioi 0, (autocorr f 0 - autocorr f t) *
        (suzukiCriticalPrimaryDensity omega t / omega)) =
        (autocorr f 0 * suzukiCriticalPrimaryMass omega -
          suzukiCriticalPrimaryCusp f omega 0) / omega := by
      calc _ = (∫ t in Ioi 0, autocorr f 0 * suzukiCriticalPrimaryDensity omega t -
            autocorr f t * suzukiCriticalPrimaryDensity omega t) / omega := by
            rw [← integral_div]
            exact congrArg (· / omega) (setIntegral_congr_fun measurableSet_Ioi fun _ _ => by ring)
        _ = _ := by
            rw [integral_sub (hi.const_mul _) hp0, integral_const_mul,
              integral_suzukiCriticalPrimaryDensity homega homega5]
            unfold suzukiCriticalPrimaryCusp
            simp only [zero_add]
    rw [he]
    ring
  rw [hsec_eq]
  have hsplit : ((suzukiCriticalPrimaryMass omega - 1) / omega * autocorr f 0 -
        ∫ t in Ioi 0, (autocorr f 0 - autocorr f t) *
          (suzukiCriticalPrimaryDensity omega t / omega)) -
      ((Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re) * autocorr f 0 -
        ∫ t in Ioi 0, (autocorr f 0 - autocorr f t) *
          (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))) =
      ((suzukiCriticalPrimaryMass omega - 1) / omega -
        (Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re)) * autocorr f 0 -
      ((∫ t in Ioi 0, (autocorr f 0 - autocorr f t) *
          (suzukiCriticalPrimaryDensity omega t / omega)) -
        ∫ t in Ioi 0, (autocorr f 0 - autocorr f t) *
          (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))) := by ring
  rw [hsplit, ← integral_sub hcomp_int htan_int]
  refine (abs_sub _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_nonneg hR0]
    exact mul_le_mul_of_nonneg_left hE₀ (abs_nonneg _)
  · have hint_le := norm_integral_le_of_norm_le
      ((integrableOn_suzukiUniversalPrimaryRemainder homega homega2).const_mul B)
      (f := fun t => (autocorr f 0 - autocorr f t) *
        (suzukiCriticalPrimaryDensity omega t / omega) -
        (autocorr f 0 - autocorr f t) *
          (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))) ?_
    · simpa only [Real.norm_eq_abs, integral_const_mul, suzukiUniversalPrimaryRemainder] using hint_le
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have hDt := autocorr_sub_nonneg hfc hf.continuous t
      rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg hDt]
      calc (autocorr f 0 - autocorr f t) *
            |suzukiCriticalPrimaryDensity omega t / omega -
              2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))|
          ≤ (B * t) * |suzukiCriticalPrimaryDensity omega t / omega -
              2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))| :=
            mul_le_mul_of_nonneg_right (hB t ht) (abs_nonneg _)
        _ = B * (t * |suzukiCriticalPrimaryDensity omega t / omega -
              2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t))|) := by ring

private theorem primaryCuspError_and_cuspRadius_le_envelope {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {A E₀ B omega : ℝ} (hA : 0 ≤ A) (hE₀ : autocorr f 0 ≤ E₀) (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 < t → autocorr f 0 - autocorr f t ≤ B * t)
    (homega : 0 < omega) (homega2 : omega ≤ 2) :
    let Mω := suzukiCriticalPrimaryMass omega
    let Sω := suzukiCriticalPrimaryScale omega
    let Kω := Real.sqrt (max (E₀ * B) 0) *
      Real.sqrt (max (2 * Mω * Sω * omega * archWeightFirstMoment) 0)
    suzukiCriticalPrimaryCuspError f omega ≤ Kω + |Mω - 1| * E₀ ∧
    suzukiCriticalCuspRadius f omega A ≤ Kω + 2 * omega * Mω * E₀ * A * Real.exp (A / 2) := by
  dsimp only
  have hR0 : 0 ≤ autocorr f 0 := GaloisForLFunctions.BiScaleUncertainty.autocorr_zero_nonneg f
  have hE₀_nn : 0 ≤ E₀ := hR0.trans hE₀
  have hMω : 0 ≤ suzukiCriticalPrimaryMass omega := by
    rw [← integral_suzukiCriticalPrimaryDensity homega (by linarith)]
    exact setIntegral_nonneg measurableSet_Ioi fun _ ht =>
      (suzukiCriticalPrimaryDensity_pos homega ht).le
  have hSω : 0 ≤ suzukiCriticalPrimaryScale omega := by
    unfold suzukiCriticalPrimaryScale
    exact div_nonneg (Real.rpow_nonneg Real.pi_pos.le _)
      (Real.Gamma_pos_of_pos (by linarith)).le
  have hJ0 : 0 ≤ biScaleLevyEnergy f :=
    setIntegral_nonneg measurableSet_Ioi fun t ht =>
      mul_nonneg (autocorr_sub_nonneg hfc hf.continuous t) (archLevySinhWeight_pos ht).le
  have hJle : biScaleLevyEnergy f ≤ B * archWeightFirstMoment :=
    biScaleLevyEnergy_le_of_increment_slope hf hfc hB
  have hA1 : 0 ≤ archWeightFirstMoment := archWeightFirstMoment_nonneg
  have hprod : 2 * autocorr f 0 * suzukiCriticalPrimaryMass omega *
      suzukiCriticalPrimaryScale omega * omega * biScaleLevyEnergy f ≤
      (E₀ * B) * (2 * suzukiCriticalPrimaryMass omega *
        suzukiCriticalPrimaryScale omega * omega * archWeightFirstMoment) := by
    have h1 : autocorr f 0 * biScaleLevyEnergy f ≤ E₀ * (B * archWeightFirstMoment) :=
      mul_le_mul hE₀ hJle hJ0 hE₀_nn
    have h2 : 0 ≤ 2 * suzukiCriticalPrimaryMass omega * suzukiCriticalPrimaryScale omega * omega := by
      positivity
    calc 2 * autocorr f 0 * suzukiCriticalPrimaryMass omega *
          suzukiCriticalPrimaryScale omega * omega * biScaleLevyEnergy f
        = (2 * suzukiCriticalPrimaryMass omega * suzukiCriticalPrimaryScale omega * omega) *
            (autocorr f 0 * biScaleLevyEnergy f) := by ring
      _ ≤ (2 * suzukiCriticalPrimaryMass omega * suzukiCriticalPrimaryScale omega * omega) *
            (E₀ * (B * archWeightFirstMoment)) := mul_le_mul_of_nonneg_left h1 h2
      _ = (E₀ * B) * (2 * suzukiCriticalPrimaryMass omega *
            suzukiCriticalPrimaryScale omega * omega * archWeightFirstMoment) := by ring
  have hrt : Real.sqrt (2 * autocorr f 0 * suzukiCriticalPrimaryMass omega *
      suzukiCriticalPrimaryScale omega * omega * biScaleLevyEnergy f) ≤
      Real.sqrt (max (E₀ * B) 0) *
        Real.sqrt (max (2 * suzukiCriticalPrimaryMass omega *
          suzukiCriticalPrimaryScale omega * omega * archWeightFirstMoment) 0) := by
    rw [← Real.sqrt_mul (le_max_right _ _)]
    refine Real.sqrt_le_sqrt (hprod.trans ?_)
    exact mul_le_mul (le_max_left _ _) (le_max_left _ _) (by positivity) (le_max_right _ _)
  refine ⟨?_, ?_⟩
  · unfold suzukiCriticalPrimaryCuspError
    exact add_le_add hrt (mul_le_mul_of_nonneg_left hE₀ (abs_nonneg _))
  · unfold suzukiCriticalCuspRadius
    refine add_le_add hrt ?_
    have h3 : 0 ≤ 2 * omega * suzukiCriticalPrimaryMass omega := by positivity
    have h4 : 0 ≤ A * Real.exp (A / 2) := by positivity
    calc 2 * omega * suzukiCriticalPrimaryMass omega * autocorr f 0 * A * Real.exp (A / 2)
        = (2 * omega * suzukiCriticalPrimaryMass omega) * autocorr f 0 * (A * Real.exp (A / 2)) := by ring
      _ ≤ (2 * omega * suzukiCriticalPrimaryMass omega) * E₀ * (A * Real.exp (A / 2)) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE₀ h3) h4
      _ = 2 * omega * suzukiCriticalPrimaryMass omega * E₀ * A * Real.exp (A / 2) := by ring

private theorem abs_poleCusp_zero_sub_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {A E₀ B omega : ℝ} (hA : 0 < A) (hcut : ∀ t : ℝ, A ≤ t → autocorr f t = 0)
    (hE₀ : autocorr f 0 ≤ E₀) (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 < t → autocorr f 0 - autocorr f t ≤ B * t)
    (homega : 0 < omega) (homega2 : omega ≤ 2) :
    |suzukiCriticalPoleCusp f omega 0 - ∫ s in Ioi 0, Real.exp (s / 2) * autocorr f s| ≤
      A * Real.exp (A / 2) *
        ((Real.sqrt (max (E₀ * B) 0) *
            Real.sqrt (max (2 * suzukiCriticalPrimaryMass omega *
              suzukiCriticalPrimaryScale omega * omega * archWeightFirstMoment) 0) +
            |suzukiCriticalPrimaryMass omega - 1| * E₀) +
          omega * A * E₀) := by
  have homega5 : omega < 5 / 2 := by linarith
  have hR0 : 0 ≤ autocorr f 0 := GaloisForLFunctions.BiScaleUncertainty.autocorr_zero_nonneg f
  have hcutint : (∫ s in Ioi 0, Real.exp (s / 2) * autocorr f s) =
      ∫ s in Ioo 0 A, Real.exp (s / 2) * autocorr f s := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi (fun _ hs => hs.1)
    intro s hs
    have hsA : A ≤ s := le_of_not_gt fun h => hs.2 ⟨hs.1, h⟩
    rw [hcut s hsA, mul_zero]
  rw [suzukiCriticalPoleCusp_eq_integral_primaryCusp hf hfc hA le_rfl hcut homega homega5, hcutint]
  have hmeas_Ioo : volume (Ioo (0 : ℝ) A) < ⊤ :=
    lt_of_le_of_lt (measure_mono Ioo_subset_Icc_self) isCompact_Icc.measure_lt_top
  have hi1 : IntegrableOn (fun s => Real.exp ((1 / 2 - omega) * s) *
      suzukiCriticalPrimaryCusp f omega (0 + s)) (Ioo 0 A) := by
    have hm : Measurable (fun s : ℝ => Real.exp ((1 / 2 - omega) * s) *
        suzukiCriticalPrimaryCusp f omega (0 + s)) :=
      (by fun_prop : Measurable fun s : ℝ => Real.exp ((1 / 2 - omega) * s)).mul
        ((measurable_suzukiCriticalPrimaryCusp hf hfc omega).comp (measurable_const.add measurable_id))
    refine (integrableOn_const hmeas_Ioo.ne).mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have he : Real.exp ((1 / 2 - omega) * s) ≤ Real.exp (A / 2) := by
      apply Real.exp_le_exp.mpr
      have hws := mul_nonneg homega.le hs.1.le
      nlinarith only [hs.2, hws]
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul he (abs_suzukiCriticalPrimaryCusp_le hf hfc homega homega5 _)
      (abs_nonneg _) (Real.exp_pos _).le
  have hi2 : IntegrableOn (fun s => Real.exp (s / 2) * autocorr f s) (Ioo 0 A) :=
    (((by fun_prop : Continuous fun s : ℝ => Real.exp (s / 2)).mul
      (continuous_autocorr hf hfc)).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  rw [← integral_sub hi1 hi2]
  obtain ⟨hperr, -⟩ := primaryCuspError_and_cuspRadius_le_envelope hf hfc hA.le hE₀ hB0 hB homega homega2
  set P_env := Real.sqrt (max (E₀ * B) 0) *
      Real.sqrt (max (2 * suzukiCriticalPrimaryMass omega *
        suzukiCriticalPrimaryScale omega * omega * archWeightFirstMoment) 0) +
      |suzukiCriticalPrimaryMass omega - 1| * E₀
  have hb : ∀ s ∈ Ioo (0 : ℝ) A,
      ‖Real.exp ((1 / 2 - omega) * s) * suzukiCriticalPrimaryCusp f omega (0 + s) -
        Real.exp (s / 2) * autocorr f s‖ ≤
        Real.exp (A / 2) * (P_env + omega * A * E₀) := by
    intro s hs
    simp only [zero_add]
    have hsplit : Real.exp ((1 / 2 - omega) * s) * suzukiCriticalPrimaryCusp f omega s -
        Real.exp (s / 2) * autocorr f s =
        Real.exp ((1 / 2 - omega) * s) * (suzukiCriticalPrimaryCusp f omega s - autocorr f s) +
        (Real.exp ((1 / 2 - omega) * s) - Real.exp (s / 2)) * autocorr f s := by ring
    rw [Real.norm_eq_abs, hsplit]
    have he1 : Real.exp ((1 / 2 - omega) * s) ≤ Real.exp (A / 2) := by
      apply Real.exp_le_exp.mpr
      have hws := mul_nonneg homega.le hs.1.le
      nlinarith only [hs.2, hws]
    have ht1 : |Real.exp ((1 / 2 - omega) * s) * (suzukiCriticalPrimaryCusp f omega s - autocorr f s)| ≤
        Real.exp (A / 2) * P_env := by
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul he1 ((abs_suzukiCriticalPrimaryCusp_sub_le hf hfc homega homega2 s).trans hperr)
        (abs_nonneg _) (Real.exp_pos _).le
    have hexp_diff : |Real.exp ((1 / 2 - omega) * s) - Real.exp (s / 2)| ≤
        Real.exp (A / 2) * (omega * A) := by
      have hfac : Real.exp ((1 / 2 - omega) * s) - Real.exp (s / 2) =
          -(Real.exp (s / 2) * (1 - Real.exp (-(omega * s)))) := by
        rw [mul_sub, mul_one, ← Real.exp_add]
        congr 1
        ring_nf
      have hws0 : 0 ≤ omega * s := mul_nonneg homega.le hs.1.le
      have h1_nn : 0 ≤ 1 - Real.exp (-(omega * s)) :=
        sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
      have h1_le : 1 - Real.exp (-(omega * s)) ≤ omega * A := by
        have := Real.add_one_le_exp (-(omega * s))
        have hwsA : omega * s ≤ omega * A := mul_le_mul_of_nonneg_left hs.2.le homega.le
        linarith
      have hes : Real.exp (s / 2) ≤ Real.exp (A / 2) := Real.exp_le_exp.mpr (by linarith [hs.2])
      rw [hfac, abs_neg, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_nonneg h1_nn]
      exact mul_le_mul hes h1_le h1_nn (Real.exp_pos _).le
    have ht2 : |(Real.exp ((1 / 2 - omega) * s) - Real.exp (s / 2)) * autocorr f s| ≤
        Real.exp (A / 2) * (omega * A * E₀) := by
      rw [abs_mul]
      calc |Real.exp ((1 / 2 - omega) * s) - Real.exp (s / 2)| * |autocorr f s|
          ≤ (Real.exp (A / 2) * (omega * A)) * E₀ :=
            mul_le_mul hexp_diff ((abs_autocorr_le_zero hfc hf.continuous s).trans hE₀)
              (abs_nonneg _) (by positivity)
        _ = Real.exp (A / 2) * (omega * A * E₀) := by ring
    exact (abs_add_le _ _).trans ((add_le_add ht1 ht2).trans_eq (by ring))
  have hi := norm_setIntegral_le_of_norm_le_const (μ := volume) hmeas_Ioo hb
  rw [Real.norm_eq_abs, Real.volume_real_Ioo_of_le hA.le, sub_zero] at hi
  exact hi.trans_eq (by ring)

/-- **Universal First-Variation Error Envelope Theorem.**
For every compact `C²` real source `f` with correlation cutoff `A > 0`, zero-lag energy
`autocorr f 0 ≤ E₀`, and correlation increment slope `autocorr f 0 - autocorr f t ≤ B * t`
(`t > 0`), and for every shift `0 < ω ≤ 2`, the secant quotient of the literal Suzuki pairing is
within `suzukiFirstVariationEnvelope A E₀ B ω` of the complete Weil quadratic form. -/
theorem abs_suzukiCriticalSourcePairing_firstVariation_sub_le {f : ℝ → ℝ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    {A E₀ B omega : ℝ} (hA : 0 < A) (hcut : ∀ t : ℝ, A ≤ t → autocorr f t = 0)
    (hE₀ : autocorr f 0 ≤ E₀) (hB0 : 0 ≤ B)
    (hB : ∀ t : ℝ, 0 < t → autocorr f 0 - autocorr f t ≤ B * t)
    (homega : 0 < omega) (homega2 : omega ≤ 2) :
    |(autocorr f 0 - suzukiCriticalSourcePairing f omega) / omega -
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re| ≤
      suzukiFirstVariationEnvelope A E₀ B omega := by
  haveI : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
  have hweil_eq : (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
      (EF.weilTest (fun u => (f u : ℂ)) (fun u => (f u : ℂ)))).re =
      -(((Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re) * autocorr f 0 -
        ∫ t in Ioi 0, (autocorr f 0 - autocorr f t) *
          (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))) -
        2 * ∫ t in Ioi 0, Real.exp (t / 2) * autocorr f t) -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
          (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
            autocorr f (Real.log n) :=
    tendsto_nhds_unique (tendsto_suzukiCriticalSourcePairing_firstVariation_of_contDiff hf hfc)
      (tendsto_suzukiCriticalSourcePairing_firstVariation_finite hf hfc hA hcut)
  have hsec_eq : (autocorr f 0 - suzukiCriticalSourcePairing f omega) / omega =
      -(((suzukiCriticalPrimaryCusp f omega 0 - autocorr f 0) / omega) -
        2 * suzukiCriticalPoleCusp f omega 0) -
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
          (suzukiShiftedCoefficient omega n / omega * Real.exp (-Real.log n / 2)) *
            suzukiCriticalSourceCusp f omega (Real.log n) := by
    have hsplit : (∑ n ∈ Finset.Icc 1 ⌊Real.exp A⌋₊,
        (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
          suzukiCriticalSourceCusp f omega (Real.log n)) =
        (suzukiShiftedCoefficient omega 1 * Real.exp (-Real.log 1 / 2)) *
          suzukiCriticalSourceCusp f omega (Real.log 1) +
        ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
          (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
            suzukiCriticalSourceCusp f omega (Real.log n) := by
      have hN : 1 ≤ ⌊Real.exp A⌋₊ := by
        simpa using Nat.floor_mono (Real.one_le_exp_iff.mpr hA.le)
      have hset : Finset.Icc 1 ⌊Real.exp A⌋₊ = insert 1 (Finset.Icc 2 ⌊Real.exp A⌋₊) := by
        ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
      rw [hset, Finset.sum_insert (by simp)]
      simp only [Nat.cast_one]
    have hunit : (suzukiShiftedCoefficient omega 1 * Real.exp (-Real.log 1 / 2)) *
        suzukiCriticalSourceCusp f omega (Real.log 1) = suzukiCriticalSourceCusp f omega 0 := by
      simp [suzukiShiftedCoefficient]
    have hdiv : (∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
        (suzukiShiftedCoefficient omega n / omega * Real.exp (-Real.log n / 2)) *
          suzukiCriticalSourceCusp f omega (Real.log n)) =
        (∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
          (suzukiShiftedCoefficient omega n * Real.exp (-Real.log n / 2)) *
            suzukiCriticalSourceCusp f omega (Real.log n)) / omega := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [suzukiCriticalSourcePairing_eq_finite hf hfc hA hcut homega (by linarith),
      hsplit, hunit, suzukiCriticalSourceCusp_eq hf hfc hA le_rfl hcut homega (by linarith), hdiv]
    field_simp [homega.ne']
    ring
  rw [hsec_eq, hweil_eq]
  set P_sec := (suzukiCriticalPrimaryCusp f omega 0 - autocorr f 0) / omega
  set P_lim := (Real.log Real.pi - (Complex.digamma ((5 / 4 : ℝ) : ℂ)).re) * autocorr f 0 -
    ∫ t in Ioi 0, (autocorr f 0 - autocorr f t) *
      (2 * Real.exp (-(5 / 2 : ℝ) * t) / (1 - Real.exp (-2 * t)))
  set Q_sec := suzukiCriticalPoleCusp f omega 0
  set Q_lim := ∫ t in Ioi 0, Real.exp (t / 2) * autocorr f t
  set S_sec := ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
    (suzukiShiftedCoefficient omega n / omega * Real.exp (-Real.log n / 2)) *
      suzukiCriticalSourceCusp f omega (Real.log n)
  set S_lim := ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
    (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
      autocorr f (Real.log n)
  have halg : (-(P_sec - 2 * Q_sec) - S_sec) - (-(P_lim - 2 * Q_lim) - S_lim) =
      -(P_sec - P_lim) + 2 * (Q_sec - Q_lim) - (S_sec - S_lim) := by ring
  rw [halg]
  have hp_bound := abs_primaryCusp_secant_sub_le hf hfc hE₀ hB0 hB homega homega2
  have hq_bound := abs_poleCusp_zero_sub_le hf hfc hA hcut hE₀ hB0 hB homega homega2
  obtain ⟨-, hrad_le⟩ := primaryCuspError_and_cuspRadius_le_envelope hf hfc hA.le hE₀ hB0 hB
    homega homega2
  have hs_bound : |S_sec - S_lim| ≤
      ∑ n ∈ Finset.Icc 2 ⌊Real.exp A⌋₊,
        Real.exp (-Real.log n / 2) *
          (|suzukiShiftedCoefficient omega n / omega| *
            (Real.sqrt (max (E₀ * B) 0) *
              Real.sqrt (max (2 * suzukiCriticalPrimaryMass omega *
                suzukiCriticalPrimaryScale omega * omega * archWeightFirstMoment) 0) +
              2 * omega * suzukiCriticalPrimaryMass omega * E₀ * A * Real.exp (A / 2)) +
            |suzukiShiftedCoefficient omega n / omega * suzukiCriticalPrimaryMass omega -
              2 * ArithmeticFunction.vonMangoldt n| * E₀) := by
    dsimp only [S_sec, S_lim]
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n hn => ?_)
    have hn1 : 1 ≤ n := by have := (Finset.mem_Icc.mp hn).1; omega
    have hu : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
    have hcusp := (abs_suzukiCriticalSourceCusp_sub_mass_le hf hfc hA hu hcut homega homega2).trans
      hrad_le
    have hsplit_n : (suzukiShiftedCoefficient omega n / omega * Real.exp (-Real.log n / 2)) *
          suzukiCriticalSourceCusp f omega (Real.log n) -
        (2 * ArithmeticFunction.vonMangoldt n * Real.exp (-Real.log n / 2)) *
          autocorr f (Real.log n) =
        Real.exp (-Real.log n / 2) *
          ((suzukiShiftedCoefficient omega n / omega) *
            (suzukiCriticalSourceCusp f omega (Real.log n) -
              suzukiCriticalPrimaryMass omega * autocorr f (Real.log n)) +
            (suzukiShiftedCoefficient omega n / omega * suzukiCriticalPrimaryMass omega -
              2 * ArithmeticFunction.vonMangoldt n) * autocorr f (Real.log n)) := by ring
    rw [hsplit_n, abs_mul, abs_of_pos (Real.exp_pos _)]
    refine mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add ?_ ?_)) (Real.exp_pos _).le
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hcusp (abs_nonneg _)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left
        ((abs_autocorr_le_zero hfc hf.continuous (Real.log n)).trans hE₀) (abs_nonneg _)
  calc |-(P_sec - P_lim) + 2 * (Q_sec - Q_lim) - (S_sec - S_lim)|
      ≤ |-(P_sec - P_lim) + 2 * (Q_sec - Q_lim)| + |S_sec - S_lim| := abs_sub _ _
    _ ≤ |P_sec - P_lim| + 2 * |Q_sec - Q_lim| + |S_sec - S_lim| := by
        refine add_le_add ?_ le_rfl
        refine (abs_add_le _ _).trans ?_
        rw [abs_neg, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ _ := by
        unfold suzukiFirstVariationEnvelope
        dsimp only
        linarith only [hp_bound, hq_bound, hs_bound]

/-- **General Common-Shift Contraction Theorem for Bounded-Envelope Families.**
Let `{f_i}_{i ∈ ι}` be any family of compact `C²` real sources indexed by `ι` with nonnegative
scale weights `w : ι → ℝ`, sharing a common correlation cutoff `A > 0`, unit-normalized energy
bound `E₀`, unit-normalized correlation increment slope `B ≥ 0`, and strictly positive Weil margin
`γ * w i ≤ Re W_Λ(f_i ⋆ f̃_i)` (`γ > 0`). Then there exists a **single shift threshold `ω₀ > 0`
independent of `i`** such that for all `ω ∈ (0, ω₀)` and every `i` with `w i > 0`,
`ω * (γ / 2 * w i) < autocorr (f_i) 0 - suzukiCriticalSourcePairing (f_i) ω`. -/
theorem exists_common_suzuki_shift_of_bounded_envelope_family {ι : Type*}
    (f : ι → ℝ → ℝ) (w : ι → ℝ) {A E₀ B γ : ℝ}
    (hA : 0 < A) (hB0 : 0 ≤ B) (hγ : 0 < γ)
    (hf : ∀ i, ContDiff ℝ 2 (f i))
    (hfc : ∀ i, HasCompactSupport (f i))
    (hcut : ∀ i t, A ≤ t → autocorr (f i) t = 0)
    (hE : ∀ i, autocorr (f i) 0 ≤ w i * E₀)
    (hinc : ∀ i t, 0 < t → autocorr (f i) 0 - autocorr (f i) t ≤ (w i * B) * t)
    (hweil : ∀ i, γ * w i ≤
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun u => (f i u : ℂ)) (fun u => (f i u : ℂ)))).re) :
    ∃ omega₀ : ℝ, 0 < omega₀ ∧ ∀ omega : ℝ, 0 < omega → omega < omega₀ →
      ∀ i : ι, 0 < w i →
        omega * (γ / 2 * w i) < autocorr (f i) 0 - suzukiCriticalSourcePairing (f i) omega ∧
        suzukiCriticalSourcePairing (f i) omega < autocorr (f i) 0 := by
  have hev : ∀ᶠ omega in 𝓝[>] (0 : ℝ), suzukiFirstVariationEnvelope A E₀ B omega < γ / 2 :=
    (tendsto_suzukiFirstVariationEnvelope A E₀ B).eventually (Iio_mem_nhds (by positivity))
  have ho2 : ∀ᶠ omega in 𝓝[>] (0 : ℝ), omega ≤ 2 :=
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by norm_num : (0 : ℝ) < 2))
  obtain ⟨s, hs_nhds, hs_sub⟩ := eventually_nhdsWithin_iff.mp (hev.and ho2)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs_nhds
  refine ⟨δ, hδ, fun omega homega homega_lt i hwi => ?_⟩
  have hmem : omega ∈ s := hball (by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos homega]
    exact homega_lt)
  obtain ⟨henv, homega2⟩ := hs_sub hmem homega
  have herr := abs_suzukiCriticalSourcePairing_firstVariation_sub_le (hf i) (hfc i) hA
    (hcut i) (hE i) (mul_nonneg hwi.le hB0) (hinc i) homega homega2
  rw [suzukiFirstVariationEnvelope_mul A E₀ B hwi.le omega] at herr
  have hlow := (abs_le.mp herr).1
  have hmul_lt : w i * suzukiFirstVariationEnvelope A E₀ B omega < w i * (γ / 2) :=
    mul_lt_mul_of_pos_left henv hwi
  have hw := hweil i
  have hquot : γ / 2 * w i <
      (autocorr (f i) 0 - suzukiCriticalSourcePairing (f i) omega) / omega := by
    linarith
  have hdef : omega * (γ / 2 * w i) <
      autocorr (f i) 0 - suzukiCriticalSourcePairing (f i) omega := by
    simpa only [mul_comm] using (lt_div_iff₀ homega).mp hquot
  exact ⟨hdef, by
    have hpos : 0 < omega * (γ / 2 * w i) := by positivity
    linarith only [hdef, hpos]⟩

/-! ## Section 2: Pattern-, Smoothing-, and Block-Uniform Common Shifts on Critical Sources -/

/-- Decomposition of `criticalTruncatedSource V S b` into single-scale basis modes `{n}`. -/
theorem criticalTruncatedSource_eq_sum_singletons (V : ℝ) (S : Finset ℕ) (b : ℕ → ℝ) (x : ℝ) :
    criticalTruncatedSource V S b x =
      ∑ n ∈ S, b n * criticalTruncatedSource V {n} (fun _ => 1) x := by
  simp_rw [criticalTruncatedSource_eq, realPhaseCombination]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [Finset.sum_singleton, one_mul]
  ring

/-- Nonnegative Lipschitz constant of the single-scale basis mode
`criticalTruncatedSource V {n} (fun _ => 1)`. -/
def criticalSingleModeLipschitz {V : ℝ} (hV : 0 < V) (n : ℕ) : ℝ :=
  max (Classical.choose (exists_lipschitz_criticalTruncatedSource hV {n} (fun _ => 1))) 0

theorem criticalSingleModeLipschitz_nonneg {V : ℝ} (hV : 0 < V) (n : ℕ) :
    0 ≤ criticalSingleModeLipschitz hV n :=
  le_max_right _ _

theorem abs_criticalSingleMode_sub_le {V : ℝ} (hV : 0 < V) (n : ℕ) (x y : ℝ) :
    |criticalTruncatedSource V {n} (fun _ => 1) x -
      criticalTruncatedSource V {n} (fun _ => 1) y| ≤
      criticalSingleModeLipschitz hV n * |x - y| := by
  have h := Classical.choose_spec (exists_lipschitz_criticalTruncatedSource hV {n} (fun _ => 1)) x y
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))

theorem abs_criticalSingleMode_le_two (V : ℝ) (n : ℕ) (x : ℝ) :
    |criticalTruncatedSource V {n} (fun _ => 1) x| ≤ 2 := by
  by_cases hx : x ≤ 0
  · rw [criticalTruncatedSource_eq, abs_mul, abs_mul, abs_mul]
    have h1 : |criticalUpperCutoff (Real.exp (-x) / V)| ≤ 1 := by
      rw [abs_of_nonneg (criticalUpperCutoff_nonneg _)]; exact criticalUpperCutoff_le_one _
    have h2 : |Real.smoothTransition (Real.exp (-x) - 1)| ≤ 1 := by
      rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]; exact Real.smoothTransition.le_one _
    have h3 : |Real.exp (x / 2)| ≤ 1 := by
      rw [abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by linarith)
    have h4 : |realPhaseCombination {n} (fun _ => 1) (Real.exp (-x))| ≤ 2 := by
      simpa using abs_realPhaseCombination_le_two_mul {n} (fun _ => 1) (Real.exp (-x))
    calc |criticalUpperCutoff (Real.exp (-x) / V)| *
          (|Real.smoothTransition (Real.exp (-x) - 1)| *
            (|Real.exp (x / 2)| * |realPhaseCombination {n} (fun _ => 1) (Real.exp (-x))|))
        ≤ 1 * (1 * (1 * 2)) :=
          mul_le_mul h1 (mul_le_mul h2 (mul_le_mul h3 h4 (abs_nonneg _) zero_le_one)
            (abs_nonneg _) zero_le_one) (abs_nonneg _) zero_le_one
      _ = 2 := by ring
  · rw [criticalTruncatedSource_eq, Real.smoothTransition.zero_of_nonpos (by
      have := Real.exp_le_exp.mpr (show -x ≤ 0 by linarith)
      rw [Real.exp_zero] at this; linarith)]
    simp

/-- Pattern-independent amplitude constant `2 |S|` for `criticalTruncatedSource V S b` per unit
`ℓ²` norm on `S`. -/
def criticalScaleAmplitudeConstant (S : Finset ℕ) : ℝ :=
  2 * (S.card : ℝ)

/-- Pattern-independent Lipschitz constant for `criticalTruncatedSource V S b` per unit `ℓ²` norm
on `S`. -/
def criticalScaleLipschitzConstant {V : ℝ} (hV : 0 < V) (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, criticalSingleModeLipschitz hV n

theorem criticalScaleAmplitudeConstant_nonneg (S : Finset ℕ) :
    0 ≤ criticalScaleAmplitudeConstant S := by
  unfold criticalScaleAmplitudeConstant; positivity

theorem criticalScaleLipschitzConstant_nonneg {V : ℝ} (hV : 0 < V) (S : Finset ℕ) :
    0 ≤ criticalScaleLipschitzConstant hV S :=
  Finset.sum_nonneg fun n _ => criticalSingleModeLipschitz_nonneg hV n

theorem criticalScaleAmplitudeConstant_mono {S T : Finset ℕ} (hST : S ⊆ T) :
    criticalScaleAmplitudeConstant S ≤ criticalScaleAmplitudeConstant T := by
  unfold criticalScaleAmplitudeConstant
  have hcard : (S.card : ℝ) ≤ (T.card : ℝ) := by exact_mod_cast Finset.card_le_card hST
  linarith

theorem criticalScaleLipschitzConstant_mono {V : ℝ} (hV : 0 < V) {S T : Finset ℕ} (hST : S ⊆ T) :
    criticalScaleLipschitzConstant hV S ≤ criticalScaleLipschitzConstant hV T :=
  Finset.sum_le_sum_of_subset_of_nonneg hST fun n _ _ => criticalSingleModeLipschitz_nonneg hV n

private theorem abs_coeff_le_sqrt_sum_sq {S : Finset ℕ} (b : ℕ → ℝ) {n : ℕ} (hn : n ∈ S) :
    |b n| ≤ Real.sqrt (∑ m ∈ S, b m ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (fun m _ => sq_nonneg (b m)) hn)

/-- Uniform amplitude bound for `criticalTruncatedTest hV S b` normalized by `√(∑_{n ∈ S} b_n²)`. -/
theorem abs_criticalTruncatedTest_le_norm {V : ℝ} (hV : 0 < V) (S : Finset ℕ) (b : ℕ → ℝ)
    (x : ℝ) :
    |criticalTruncatedTest hV S b x| ≤
      criticalScaleAmplitudeConstant S * Real.sqrt (∑ n ∈ S, b n ^ 2) := by
  rw [criticalTruncatedTest_apply, criticalTruncatedSource_eq_sum_singletons]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ n ∈ S, |b n * criticalTruncatedSource V {n} (fun _ => 1) x|
      ≤ ∑ _n ∈ S, Real.sqrt (∑ m ∈ S, b m ^ 2) * 2 := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [abs_mul]
        exact mul_le_mul (abs_coeff_le_sqrt_sum_sq b hn) (abs_criticalSingleMode_le_two V n x)
          (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = criticalScaleAmplitudeConstant S * Real.sqrt (∑ n ∈ S, b n ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
        unfold criticalScaleAmplitudeConstant
        ring

/-- Uniform Lipschitz bound for `criticalTruncatedTest hV S b` normalized by `√(∑_{n ∈ S} b_n²)`. -/
theorem abs_criticalTruncatedTest_sub_le_norm {V : ℝ} (hV : 0 < V) (S : Finset ℕ) (b : ℕ → ℝ)
    (x y : ℝ) :
    |criticalTruncatedTest hV S b x - criticalTruncatedTest hV S b y| ≤
      criticalScaleLipschitzConstant hV S * Real.sqrt (∑ n ∈ S, b n ^ 2) * |x - y| := by
  rw [criticalTruncatedTest_apply, criticalTruncatedTest_apply,
    criticalTruncatedSource_eq_sum_singletons, criticalTruncatedSource_eq_sum_singletons,
    ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ n ∈ S, |b n * criticalTruncatedSource V {n} (fun _ => 1) x -
        b n * criticalTruncatedSource V {n} (fun _ => 1) y|
      ≤ ∑ n ∈ S, Real.sqrt (∑ m ∈ S, b m ^ 2) * (criticalSingleModeLipschitz hV n * |x - y|) := by
        refine Finset.sum_le_sum fun n hn => ?_
        rw [← mul_sub, abs_mul]
        exact mul_le_mul (abs_coeff_le_sqrt_sum_sq b hn) (abs_criticalSingleMode_sub_le hV n x y)
          (abs_nonneg _) (Real.sqrt_nonneg _)
    _ = criticalScaleLipschitzConstant hV S * Real.sqrt (∑ n ∈ S, b n ^ 2) * |x - y| := by
        unfold criticalScaleLipschitzConstant
        rw [Finset.sum_mul, Finset.sum_mul]
        exact Finset.sum_congr rfl fun _ _ => by ring

/-- Centered support radius `max(log(2V), 0)` of `criticalTruncatedTest hV S b`. -/
def criticalSupportRadius (V : ℝ) : ℝ :=
  max (Real.log (2 * V)) 0

/-- Common correlation cutoff `2(max(log(2V), 0) + 1) + 1` shared by `criticalTruncatedTest hV S b`
and all of its mollifications `smoothCompactSource (criticalTruncatedTest hV S b) k` (`k ∈ ℕ`). -/
def criticalSuzukiAperture (V : ℝ) : ℝ :=
  2 * (criticalSupportRadius V + 1) + 1

/-- Unit-normalized zero-lag autocorrelation bound for all mollifications of
`criticalTruncatedTest hV S b`. -/
def criticalSuzukiEnergyEnvelope (V : ℝ) (S : Finset ℕ) : ℝ :=
  2 * (criticalSupportRadius V + 1) * criticalScaleAmplitudeConstant S ^ 2

/-- Unit-normalized correlation increment slope bound for all mollifications of
`criticalTruncatedTest hV S b`. -/
def criticalSuzukiIncrementEnvelope {V : ℝ} (hV : 0 < V) (S : Finset ℕ) : ℝ :=
  criticalScaleLipschitzConstant hV S *
    (2 * criticalSupportRadius V * criticalScaleAmplitudeConstant S)

/-- Unit-normalized complete Weil smoothing cost for `criticalTruncatedTest hV S b`. -/
def criticalSuzukiSmoothingCost {V : ℝ} (hV : 0 < V) (S : Finset ℕ) : ℝ :=
  compactFullWeilApproximationCost (criticalSupportRadius V)
    (criticalScaleAmplitudeConstant S) (criticalScaleLipschitzConstant hV S)

theorem criticalSupportRadius_nonneg (V : ℝ) : 0 ≤ criticalSupportRadius V :=
  le_max_right _ _

theorem criticalSuzukiAperture_pos (V : ℝ) : 0 < criticalSuzukiAperture V := by
  have := criticalSupportRadius_nonneg V
  unfold criticalSuzukiAperture
  linarith

theorem criticalTruncatedTest_eq_zero_of_radius {V : ℝ} (hV : 0 < V) (S : Finset ℕ) (b : ℕ → ℝ)
    {x : ℝ} (hx : criticalSupportRadius V < |x|) :
    criticalTruncatedTest hV S b x = 0 := by
  rw [criticalTruncatedTest_apply]
  refine criticalTruncatedSource_eq_zero hV S b fun hmem => ?_
  have h1 : |x| ≤ criticalSupportRadius V := by
    rw [abs_le]
    exact ⟨by linarith [le_max_left (Real.log (2 * V)) 0, hmem.1],
      hmem.2.trans (le_max_right _ _)⟩
  linarith

/-- **Uniform Smoothing Rate Normalized by `∑_{n ∈ S} b_n²`.** -/
theorem compactFullWeilEnergy_smoothing_error_criticalTruncatedTest {V : ℝ} (hV : 0 < V)
    (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) :
    |compactFullWeilEnergy (smoothCompactSource (criticalTruncatedTest hV S b) k) -
      compactFullWeilEnergy (criticalTruncatedTest hV S b)| ≤
      criticalSuzukiSmoothingCost hV S / ((k : ℝ) + 1) * ∑ n ∈ S, b n ^ 2 := by
  set E := ∑ n ∈ S, b n ^ 2
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE
  have herr := compactFullWeilEnergy_smoothing_error (criticalTruncatedTest hV S b)
    (abs_criticalTruncatedTest_le_norm hV S b)
    (abs_criticalTruncatedTest_sub_le_norm hV S b)
    (criticalSupportRadius_nonneg V)
    (criticalTruncatedTest_eq_zero_of_radius hV S b) k
  refine herr.trans (le_of_eq ?_)
  unfold criticalSuzukiSmoothingCost compactFullWeilApproximationCost
  have hk_pos : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  field_simp [hk_pos.ne']
  linear_combination (criticalSupportRadius V + 1) * criticalScaleLipschitzConstant hV S *
    (criticalScaleAmplitudeConstant S *
      (|EF.gammaBracket 0| + 2 * mass (compactFullWeilPrimeCutoff (criticalSupportRadius V))) +
      criticalScaleLipschitzConstant hV S * archWeightFirstMoment) * hsq

/-- **Uniform `k`- and `b`-Normalized Envelope Bounds for All Mollifications of
`criticalTruncatedTest hV S b`.**
Every mollified source `smoothCompactSource (criticalTruncatedTest hV S b) k` (`k ∈ ℕ`) is smooth,
has correlation cutoff `criticalSuzukiAperture V`, zero-lag autocorrelation bounded by
`criticalSuzukiEnergyEnvelope V S * ∑_{n ∈ S} b_n²`, and correlation increment slope bounded by
`criticalSuzukiIncrementEnvelope hV S * (∑_{n ∈ S} b_n²) * t` — all with constants independent of
both `b` and `k`. -/
theorem smoothCompactSource_criticalTruncatedTest_envelope {V : ℝ} (hV : 0 < V)
    (S : Finset ℕ) (b : ℕ → ℝ) (k : ℕ) :
    let g := criticalTruncatedTest hV S b
    let fk := smoothCompactSource g k
    let E := ∑ n ∈ S, b n ^ 2
    ContDiff ℝ 2 (fk : ℝ → ℝ) ∧
    (∀ t : ℝ, criticalSuzukiAperture V ≤ t → autocorr fk t = 0) ∧
    autocorr fk 0 ≤ E * criticalSuzukiEnergyEnvelope V S ∧
    (∀ t : ℝ, 0 < t → autocorr fk 0 - autocorr fk t ≤ (E * criticalSuzukiIncrementEnvelope hV S) * t) := by
  dsimp only
  set g := criticalTruncatedTest hV S b
  set fk := smoothCompactSource g k
  set E := ∑ n ∈ S, b n ^ 2
  set R := criticalSupportRadius V
  have hE : 0 ≤ E := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hsq : Real.sqrt E ^ 2 = E := Real.sq_sqrt hE
  have hR0 : 0 ≤ R := criticalSupportRadius_nonneg V
  have hgR : ∀ x, R < |x| → g x = 0 := criticalTruncatedTest_eq_zero_of_radius hV S b
  have hgM : ∀ x, |g x| ≤ criticalScaleAmplitudeConstant S * Real.sqrt E :=
    abs_criticalTruncatedTest_le_norm hV S b
  have hgK : ∀ x y, |g x - g y| ≤ criticalScaleLipschitzConstant hV S * Real.sqrt E * |x - y| :=
    abs_criticalTruncatedTest_sub_le_norm hV S b
  have hsm : ContDiff ℝ 2 (fk : ℝ → ℝ) :=
    smooth_contDiff (g.continuous.memLp_of_hasCompactSupport g.hasCompactSupport) k
  have hcut : ∀ t : ℝ, criticalSuzukiAperture V ≤ t → autocorr fk t = 0 := by
    intro t ht
    refine autocorr_eq_zero_of_far (fun x hx => smooth_eq_zero_of_far hgR k hx) ?_
    have : 2 * (R + 1) < t := by unfold criticalSuzukiAperture at ht; linarith
    exact this.trans_le (le_abs_self t)
  have hE_bound : autocorr fk 0 ≤ E * criticalSuzukiEnergyEnvelope V S := by
    have hM0 : 0 ≤ criticalScaleAmplitudeConstant S * Real.sqrt E :=
      mul_nonneg (criticalScaleAmplitudeConstant_nonneg S) (Real.sqrt_nonneg E)
    have hfkM : ∀ x, |fk x| ≤ criticalScaleAmplitudeConstant S * Real.sqrt E :=
      smooth_bound hM0 hgM k
    have hfkR : ∀ x, R + 1 < |x| → fk x = 0 := fun x hx => smooth_eq_zero_of_far hgR k hx
    have habs := (le_abs_self _).trans (abs_autocorr_le_of_bound hfkM hfkR 0)
    have hint : (∫ u, (Icc (-(R + 1)) (R + 1)).indicator
        (fun _ => (criticalScaleAmplitudeConstant S * Real.sqrt E) ^ 2) u) =
        2 * (R + 1) * (criticalScaleAmplitudeConstant S * Real.sqrt E) ^ 2 := by
      rw [integral_indicator measurableSet_Icc, setIntegral_const,
        Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
      ring
    rw [hint] at habs
    refine habs.trans (le_of_eq ?_)
    unfold criticalSuzukiEnergyEnvelope
    linear_combination 2 * (R + 1) * criticalScaleAmplitudeConstant S ^ 2 * hsq
  have hinc_bound : ∀ t : ℝ, 0 < t →
      autocorr fk 0 - autocorr fk t ≤ (E * criticalSuzukiIncrementEnvelope hV S) * t := by
    intro t ht
    have hsub := (autocorr_smooth_sub_le g.continuous hgM hgR k t).2
    have hlip := autocorr_increment_le_lipschitz g hgK t
    have hL1 : (∫ u, |g u|) ≤ 2 * R * (criticalScaleAmplitudeConstant S * Real.sqrt E) := by
      have hset : (∫ u, |g u|) = ∫ u in Icc (-R) R, |g u| := by
        symm
        refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
        have hxa : R < |x| := not_le.mp fun h => hx (abs_le.mp h)
        rw [hgR x hxa, abs_zero]
      rw [hset]
      have hgi : IntegrableOn (fun u => |g u|) (Icc (-R) R) :=
        g.continuous.abs.integrableOn_Icc
      calc (∫ u in Icc (-R) R, |g u|)
          ≤ ∫ _u in Icc (-R) R, criticalScaleAmplitudeConstant S * Real.sqrt E :=
            setIntegral_mono_on hgi (integrableOn_const (by simp)) measurableSet_Icc fun x _ => hgM x
        _ = 2 * R * (criticalScaleAmplitudeConstant S * Real.sqrt E) := by
            rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
            ring
    have hKL := mul_le_mul_of_nonneg_left hL1
      (mul_nonneg (criticalScaleLipschitzConstant_nonneg hV S) (Real.sqrt_nonneg E))
    have hKt := mul_le_mul_of_nonneg_right hKL (abs_nonneg t)
    calc autocorr fk 0 - autocorr fk t
        ≤ autocorr g 0 - autocorr g t := hsub
      _ ≤ (criticalScaleLipschitzConstant hV S * Real.sqrt E) * (∫ u, |g u|) * |t| := hlip
      _ ≤ (criticalScaleLipschitzConstant hV S * Real.sqrt E) *
            (2 * R * (criticalScaleAmplitudeConstant S * Real.sqrt E)) * |t| := hKt
      _ = (E * criticalSuzukiIncrementEnvelope hV S) * t := by
          rw [abs_of_pos ht]
          unfold criticalSuzukiIncrementEnvelope
          linear_combination 2 * R * criticalScaleLipschitzConstant hV S *
            criticalScaleAmplitudeConstant S * t * hsq
  exact ⟨hsm, hcut, hE_bound, hinc_bound⟩

private theorem subset_Icc_of_dyadicScaleBlock {S : Finset ℕ} {M : ℕ} (hS : DyadicScaleBlock S M) :
    S ⊆ Finset.Icc 0 (2 * M) := by
  intro n hn
  rw [Finset.mem_Icc]
  have := (hS n hn).2
  omega

/-- **Block-, Pattern-, and Smoothing-Uniform Common Shift on Dyadic Critical Sources.**
There exists `M₀ : ℕ` such that for every scale `M ≥ M₀` and every truncation
`V ≥ criticalTruncationThreshold` (`hV : 0 < V`), there exist a **common smoothing threshold `k₀`**
and a **common shift threshold `ω₀ > 0`** — independent of the dyadic block `S` at scale `M`,
independent of the nonzero pattern `b`, and (for `ω₀`) independent of the smoothing index `k ≥ k₀`
— such that for all `S` with `DyadicScaleBlock S M`, all nonzero patterns `b` on `S`, all `k ≥ k₀`,
and all `ω ∈ (0, ω₀)`,
`ω * (compactFullWeilEnergy (criticalTruncatedTest hV S b) / 4) < autocorr f_{b,k} 0 - suzukiCriticalSourcePairing f_{b,k} ω`. -/
theorem exists_common_suzuki_shift_dyadic_blocks :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, ∀ V : ℝ, ∀ hV : 0 < V, criticalTruncationThreshold ≤ V →
      ∃ (k₀ : ℕ) (omega₀ : ℝ), 0 < omega₀ ∧
        ∀ S : Finset ℕ, DyadicScaleBlock S M →
        ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
          0 < compactFullWeilEnergy (criticalTruncatedTest hV S b) ∧
          ∀ k ≥ k₀, ∀ omega : ℝ, 0 < omega → omega < omega₀ →
            omega * (compactFullWeilEnergy (criticalTruncatedTest hV S b) / 4) <
              autocorr (smoothCompactSource (criticalTruncatedTest hV S b) k) 0 -
                suzukiCriticalSourcePairing
                  (smoothCompactSource (criticalTruncatedTest hV S b) k) omega ∧
            suzukiCriticalSourcePairing
              (smoothCompactSource (criticalTruncatedTest hV S b) k) omega <
              autocorr (smoothCompactSource (criticalTruncatedTest hV S b) k) 0 := by
  have hs := criticalTruncatedArchLogSlope_pos
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((hlog.eventually_gt_atTop
    (criticalTruncatedArchLogOffset +
      criticalTruncatedChannelConstant / criticalTruncatedArchLogSlope)).and
      (eventually_ge_atTop 2))
  refine ⟨M₀, fun M hM V hV hVt => ?_⟩
  obtain ⟨hlogM, hM2⟩ := hM₀ M hM
  set γ := criticalTruncatedArchLogSlope * (Real.log M - criticalTruncatedArchLogOffset) -
    criticalTruncatedChannelConstant
  have hγ : 0 < γ := by
    have h1 : criticalTruncatedChannelConstant / criticalTruncatedArchLogSlope <
        Real.log M - criticalTruncatedArchLogOffset := by linarith
    have h2 := (div_lt_iff₀ hs).mp h1
    unfold γ; linarith
  set T_amb : Finset ℕ := Finset.Icc 0 (2 * M)
  set C_sm := criticalSuzukiSmoothingCost hV T_amb
  set E₀_amb := criticalSuzukiEnergyEnvelope V T_amb
  set B₀_amb := criticalSuzukiIncrementEnvelope hV T_amb
  set A_V := criticalSuzukiAperture V
  have hA_V : 0 < A_V := criticalSuzukiAperture_pos V
  have hE₀_nn : 0 ≤ E₀_amb := by
    unfold E₀_amb criticalSuzukiEnergyEnvelope
    have := criticalSupportRadius_nonneg V
    positivity
  have hB₀_nn : 0 ≤ B₀_amb := by
    unfold B₀_amb criticalSuzukiIncrementEnvelope
    exact mul_nonneg (criticalScaleLipschitzConstant_nonneg hV T_amb)
      (mul_nonneg (mul_nonneg (by norm_num) (criticalSupportRadius_nonneg V))
        (criticalScaleAmplitudeConstant_nonneg T_amb))
  obtain ⟨k₀, hk₀_gt⟩ := exists_nat_gt (2 * max C_sm 0 / γ)
  have hev : ∀ᶠ omega in 𝓝[>] (0 : ℝ),
      suzukiFirstVariationEnvelope A_V E₀_amb B₀_amb omega < γ / 4 :=
    (tendsto_suzukiFirstVariationEnvelope A_V E₀_amb B₀_amb).eventually
      (Iio_mem_nhds (by positivity))
  have ho2 : ∀ᶠ omega in 𝓝[>] (0 : ℝ), omega ≤ 2 :=
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by norm_num : (0 : ℝ) < 2))
  obtain ⟨s, hs_nhds, hs_sub⟩ := eventually_nhdsWithin_iff.mp (hev.and ho2)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs_nhds
  refine ⟨k₀, δ, hδ, fun S hS b hb => ?_⟩
  set g := criticalTruncatedTest hV S b
  set E := ∑ n ∈ S, b n ^ 2
  obtain ⟨j₀, hj₀, hbj₀⟩ := hb
  have hE_pos : 0 < E :=
    lt_of_lt_of_le (sq_pos_of_ne_zero hbj₀) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj₀)
  have hsub : S ⊆ T_amb := subset_Icc_of_dyadicScaleBlock hS
  have hM_mono : criticalScaleAmplitudeConstant S ≤ criticalScaleAmplitudeConstant T_amb :=
    criticalScaleAmplitudeConstant_mono hsub
  have hK_mono : criticalScaleLipschitzConstant hV S ≤ criticalScaleLipschitzConstant hV T_amb :=
    criticalScaleLipschitzConstant_mono hV hsub
  have hweil_ge : γ * E ≤ compactFullWeilEnergy g := by
    have hcomp := criticalTruncatedCompleteEnergy_ge S b hM2 hS hVt
    rw [← compactFullWeilEnergy_criticalTruncatedTest hV] at hcomp
    exact EReal.coe_le_coe_iff.mp hcomp
  have hg_pos : 0 < compactFullWeilEnergy g := lt_of_lt_of_le (mul_pos hγ hE_pos) hweil_ge
  refine ⟨hg_pos, fun k hk omega homega homega_lt => ?_⟩
  set fk := smoothCompactSource g k
  -- 1. Uniform smoothing margin `compactFullWeilEnergy g / 2 ≤ compactFullWeilEnergy fk`:
  have hC_mono : criticalSuzukiSmoothingCost hV S ≤ C_sm := by
    unfold criticalSuzukiSmoothingCost C_sm compactFullWeilApproximationCost
    have hR0 := criticalSupportRadius_nonneg V
    have hM0 := criticalScaleAmplitudeConstant_nonneg S
    have hK0 := criticalScaleLipschitzConstant_nonneg hV S
    have hmass0 := mass_nonneg (compactFullWeilPrimeCutoff (criticalSupportRadius V))
    have harch0 := archWeightFirstMoment_nonneg
    gcongr
  have hsm_err := (compactFullWeilEnergy_smoothing_error_criticalTruncatedTest hV S b k).trans
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (hC_mono.trans (le_max_left C_sm 0)) (by positivity)) hE_pos.le)
  have hk_bound : max C_sm 0 / ((k : ℝ) + 1) ≤ γ / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hk_cast : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
    have h1 : 2 * max C_sm 0 < (k₀ : ℝ) * γ := (div_lt_iff₀ hγ).mp hk₀_gt
    nlinarith
  have hfk_weil : compactFullWeilEnergy g / 2 ≤ compactFullWeilEnergy fk := by
    have hsm_low := (abs_le.mp hsm_err).1
    have h1 : max C_sm 0 / ((k : ℝ) + 1) * E ≤ (γ / 2) * E :=
      mul_le_mul_of_nonneg_right hk_bound hE_pos.le
    linarith
  -- 2. Uniform first-variation error `< compactFullWeilEnergy g / 4`:
  have hmem : omega ∈ s := hball (by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos homega]
    exact homega_lt)
  obtain ⟨henv_lt, homega2⟩ := hs_sub hmem homega
  obtain ⟨hfk_diff, hfk_cut, hfk_E, hfk_inc⟩ :=
    smoothCompactSource_criticalTruncatedTest_envelope hV S b k
  have hE_mono : criticalSuzukiEnergyEnvelope V S ≤ E₀_amb := by
    unfold criticalSuzukiEnergyEnvelope E₀_amb
    have hR0 := criticalSupportRadius_nonneg V
    have hM0 := criticalScaleAmplitudeConstant_nonneg S
    gcongr
  have hB_mono : criticalSuzukiIncrementEnvelope hV S ≤ B₀_amb := by
    unfold criticalSuzukiIncrementEnvelope B₀_amb
    have hR0 := criticalSupportRadius_nonneg V
    have hM0 := criticalScaleAmplitudeConstant_nonneg S
    have hK0 := criticalScaleLipschitzConstant_nonneg hV S
    gcongr
  have hfk_E' : autocorr fk 0 ≤ E * E₀_amb :=
    hfk_E.trans (mul_le_mul_of_nonneg_left hE_mono hE_pos.le)
  have hfk_inc' : ∀ t : ℝ, 0 < t → autocorr fk 0 - autocorr fk t ≤ (E * B₀_amb) * t := fun t ht =>
    (hfk_inc t ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hB_mono hE_pos.le) ht.le)
  have herr := abs_suzukiCriticalSourcePairing_firstVariation_sub_le hfk_diff fk.hasCompactSupport
    hA_V hfk_cut hfk_E' (mul_nonneg hE_pos.le hB₀_nn) hfk_inc' homega homega2
  rw [suzukiFirstVariationEnvelope_mul A_V E₀_amb B₀_amb hE_pos.le omega] at herr
  have hlow := (abs_le.mp herr).1
  have hmul_lt : E * suzukiFirstVariationEnvelope A_V E₀_amb B₀_amb omega < E * (γ / 4) :=
    mul_lt_mul_of_pos_left henv_lt hE_pos
  have hquot : compactFullWeilEnergy g / 4 <
      (autocorr fk 0 - suzukiCriticalSourcePairing fk omega) / omega := by
    change |(autocorr fk 0 - suzukiCriticalSourcePairing fk omega) / omega -
      compactFullWeilEnergy fk| ≤ _ at herr
    have hlow' : -(E * suzukiFirstVariationEnvelope A_V E₀_amb B₀_amb omega) ≤
        (autocorr fk 0 - suzukiCriticalSourcePairing fk omega) / omega -
          compactFullWeilEnergy fk := (abs_le.mp herr).1
    linarith
  have hdef : omega * (compactFullWeilEnergy g / 4) <
      autocorr fk 0 - suzukiCriticalSourcePairing fk omega := by
    simpa only [mul_comm] using (lt_div_iff₀ homega).mp hquot
  exact ⟨hdef, by
    have hpos : 0 < omega * (compactFullWeilEnergy g / 4) := by positivity
    linarith only [hdef, hpos]⟩

/-- **Common Shift Across Any Bounded Horizon of Dyadic Scale Blocks.**
For every upper scale `M_max ≥ M₀` and every `V ≥ criticalTruncationThreshold`, a single pair
`(k₀, ω₀)` works simultaneously across **all** scales `M ∈ [M₀, M_max]`, **all** dyadic blocks `S`
at scale `M`, **all** nonzero patterns `b` on `S`, and **all** `k ≥ k₀`. -/
theorem exists_common_suzuki_shift_bounded_block_horizon :
    ∃ M₀ : ℕ, ∀ M_max ≥ M₀, ∀ V : ℝ, ∀ hV : 0 < V, criticalTruncationThreshold ≤ V →
      ∃ (k₀ : ℕ) (omega₀ : ℝ), 0 < omega₀ ∧
        ∀ M : ℕ, M₀ ≤ M → M ≤ M_max →
        ∀ S : Finset ℕ, DyadicScaleBlock S M →
        ∀ b : ℕ → ℝ, (∃ n ∈ S, b n ≠ 0) →
          ∀ k ≥ k₀, ∀ omega : ℝ, 0 < omega → omega < omega₀ →
            omega * (compactFullWeilEnergy (criticalTruncatedTest hV S b) / 4) <
              autocorr (smoothCompactSource (criticalTruncatedTest hV S b) k) 0 -
                suzukiCriticalSourcePairing
                  (smoothCompactSource (criticalTruncatedTest hV S b) k) omega ∧
            suzukiCriticalSourcePairing
              (smoothCompactSource (criticalTruncatedTest hV S b) k) omega <
              autocorr (smoothCompactSource (criticalTruncatedTest hV S b) k) 0 := by
  have hs := criticalTruncatedArchLogSlope_pos
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((hlog.eventually_gt_atTop
    (criticalTruncatedArchLogOffset +
      criticalTruncatedChannelConstant / criticalTruncatedArchLogSlope)).and
      (eventually_ge_atTop 2))
  refine ⟨M₀, fun M_max hMmax V hV hVt => ?_⟩
  obtain ⟨hlogM₀, hM₀2⟩ := hM₀ M₀ le_rfl
  set γ₀ := criticalTruncatedArchLogSlope * (Real.log M₀ - criticalTruncatedArchLogOffset) -
    criticalTruncatedChannelConstant
  have hγ₀ : 0 < γ₀ := by
    have h1 : criticalTruncatedChannelConstant / criticalTruncatedArchLogSlope <
        Real.log M₀ - criticalTruncatedArchLogOffset := by linarith
    have h2 := (div_lt_iff₀ hs).mp h1
    unfold γ₀; linarith
  set T_amb : Finset ℕ := Finset.Icc 0 (2 * M_max)
  set C_sm := criticalSuzukiSmoothingCost hV T_amb
  set E₀_amb := criticalSuzukiEnergyEnvelope V T_amb
  set B₀_amb := criticalSuzukiIncrementEnvelope hV T_amb
  set A_V := criticalSuzukiAperture V
  have hA_V : 0 < A_V := criticalSuzukiAperture_pos V
  have hB₀_nn : 0 ≤ B₀_amb := by
    unfold B₀_amb criticalSuzukiIncrementEnvelope
    exact mul_nonneg (criticalScaleLipschitzConstant_nonneg hV T_amb)
      (mul_nonneg (mul_nonneg (by norm_num) (criticalSupportRadius_nonneg V))
        (criticalScaleAmplitudeConstant_nonneg T_amb))
  obtain ⟨k₀, hk₀_gt⟩ := exists_nat_gt (2 * max C_sm 0 / γ₀)
  have hev : ∀ᶠ omega in 𝓝[>] (0 : ℝ),
      suzukiFirstVariationEnvelope A_V E₀_amb B₀_amb omega < γ₀ / 4 :=
    (tendsto_suzukiFirstVariationEnvelope A_V E₀_amb B₀_amb).eventually
      (Iio_mem_nhds (by positivity))
  have ho2 : ∀ᶠ omega in 𝓝[>] (0 : ℝ), omega ≤ 2 :=
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by norm_num : (0 : ℝ) < 2))
  obtain ⟨s, hs_nhds, hs_sub⟩ := eventually_nhdsWithin_iff.mp (hev.and ho2)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hs_nhds
  refine ⟨k₀, δ, hδ, fun M hM_lo hM_hi S hS b hb k hk omega homega homega_lt => ?_⟩
  set g := criticalTruncatedTest hV S b
  set fk := smoothCompactSource g k
  set E := ∑ n ∈ S, b n ^ 2
  obtain ⟨j₀, hj₀, hbj₀⟩ := hb
  have hE_pos : 0 < E :=
    lt_of_lt_of_le (sq_pos_of_ne_zero hbj₀) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj₀)
  have hsub : S ⊆ T_amb := (subset_Icc_of_dyadicScaleBlock hS).trans
    (Finset.Icc_subset_Icc_right (by omega))
  have hM_mono : criticalScaleAmplitudeConstant S ≤ criticalScaleAmplitudeConstant T_amb :=
    criticalScaleAmplitudeConstant_mono hsub
  have hK_mono : criticalScaleLipschitzConstant hV S ≤ criticalScaleLipschitzConstant hV T_amb :=
    criticalScaleLipschitzConstant_mono hV hsub
  have hlog_mono : Real.log M₀ ≤ Real.log M :=
    Real.log_le_log (by exact_mod_cast (show 0 < M₀ by omega)) (by exact_mod_cast hM_lo)
  have hweil_ge : γ₀ * E ≤ compactFullWeilEnergy g := by
    have hcomp := criticalTruncatedCompleteEnergy_ge S b (hM₀2.trans hM_lo) hS hVt
    rw [← compactFullWeilEnergy_criticalTruncatedTest hV] at hcomp
    have hcomp' := EReal.coe_le_coe_iff.mp hcomp
    have hγ_le : γ₀ ≤ criticalTruncatedArchLogSlope *
        (Real.log M - criticalTruncatedArchLogOffset) - criticalTruncatedChannelConstant := by
      unfold γ₀; nlinarith
    exact (mul_le_mul_of_nonneg_right hγ_le hE_pos.le).trans hcomp'
  have hC_mono : criticalSuzukiSmoothingCost hV S ≤ C_sm := by
    unfold criticalSuzukiSmoothingCost C_sm compactFullWeilApproximationCost
    have hR0 := criticalSupportRadius_nonneg V
    have hM0 := criticalScaleAmplitudeConstant_nonneg S
    have hK0 := criticalScaleLipschitzConstant_nonneg hV S
    have hmass0 := mass_nonneg (compactFullWeilPrimeCutoff (criticalSupportRadius V))
    have harch0 := archWeightFirstMoment_nonneg
    gcongr
  have hsm_err := (compactFullWeilEnergy_smoothing_error_criticalTruncatedTest hV S b k).trans
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (hC_mono.trans (le_max_left C_sm 0)) (by positivity)) hE_pos.le)
  have hk_bound : max C_sm 0 / ((k : ℝ) + 1) ≤ γ₀ / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hk_cast : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
    have h1 : 2 * max C_sm 0 < (k₀ : ℝ) * γ₀ := (div_lt_iff₀ hγ₀).mp hk₀_gt
    nlinarith
  have hfk_weil : compactFullWeilEnergy g / 2 ≤ compactFullWeilEnergy fk := by
    have hsm_low := (abs_le.mp hsm_err).1
    have h1 : max C_sm 0 / ((k : ℝ) + 1) * E ≤ (γ₀ / 2) * E :=
      mul_le_mul_of_nonneg_right hk_bound hE_pos.le
    linarith
  have hmem : omega ∈ s := hball (by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos homega]
    exact homega_lt)
  obtain ⟨henv_lt, homega2⟩ := hs_sub hmem homega
  obtain ⟨hfk_diff, hfk_cut, hfk_E, hfk_inc⟩ :=
    smoothCompactSource_criticalTruncatedTest_envelope hV S b k
  have hE_mono : criticalSuzukiEnergyEnvelope V S ≤ E₀_amb := by
    unfold criticalSuzukiEnergyEnvelope E₀_amb
    have hR0 := criticalSupportRadius_nonneg V
    have hM0 := criticalScaleAmplitudeConstant_nonneg S
    gcongr
  have hB_mono : criticalSuzukiIncrementEnvelope hV S ≤ B₀_amb := by
    unfold criticalSuzukiIncrementEnvelope B₀_amb
    have hR0 := criticalSupportRadius_nonneg V
    have hM0 := criticalScaleAmplitudeConstant_nonneg S
    have hK0 := criticalScaleLipschitzConstant_nonneg hV S
    gcongr
  have hfk_E' : autocorr fk 0 ≤ E * E₀_amb :=
    hfk_E.trans (mul_le_mul_of_nonneg_left hE_mono hE_pos.le)
  have hfk_inc' : ∀ t : ℝ, 0 < t → autocorr fk 0 - autocorr fk t ≤ (E * B₀_amb) * t := fun t ht =>
    (hfk_inc t ht).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hB_mono hE_pos.le) ht.le)
  have herr := abs_suzukiCriticalSourcePairing_firstVariation_sub_le hfk_diff fk.hasCompactSupport
    hA_V hfk_cut hfk_E' (mul_nonneg hE_pos.le hB₀_nn) hfk_inc' homega homega2
  rw [suzukiFirstVariationEnvelope_mul A_V E₀_amb B₀_amb hE_pos.le omega] at herr
  have hlow' : -(E * suzukiFirstVariationEnvelope A_V E₀_amb B₀_amb omega) ≤
      (autocorr fk 0 - suzukiCriticalSourcePairing fk omega) / omega -
        compactFullWeilEnergy fk := (abs_le.mp herr).1
  have hmul_lt : E * suzukiFirstVariationEnvelope A_V E₀_amb B₀_amb omega < E * (γ₀ / 4) :=
    mul_lt_mul_of_pos_left henv_lt hE_pos
  have hquot : compactFullWeilEnergy g / 4 <
      (autocorr fk 0 - suzukiCriticalSourcePairing fk omega) / omega := by linarith
  have hdef : omega * (compactFullWeilEnergy g / 4) <
      autocorr fk 0 - suzukiCriticalSourcePairing fk omega := by
    simpa only [mul_comm] using (lt_div_iff₀ homega).mp hquot
  have hg_pos : 0 < compactFullWeilEnergy g := lt_of_lt_of_le (mul_pos hγ₀ hE_pos) hweil_ge
  exact ⟨hdef, by
    have hpos : 0 < omega * (compactFullWeilEnergy g / 4) := by positivity
    linarith only [hdef, hpos]⟩

/-- **Pattern- and Smoothing-Uniform Common Shift on Lacunary Multi-Windows with Polynomial Widths.**
There exist `δ > 0` and `M₀ : ℕ` such that for any lacunary multi-window family `(J, M, L, W)` with
`M 0 ≥ M₀` and `L i ≤ (M 0 : ℝ) ^ δ` (`i < J`), and any truncation `V ≥ criticalTruncationThreshold`
(`hV : 0 < V`), there exist a **common smoothing threshold `k₀`** and a **common shift threshold
`ω₀ > 0`** — independent of the pattern `b` on `T = ⋃_{i < J} W i` and (for `ω₀`) independent of
`k ≥ k₀` — on which the strict first-order Suzuki deficit holds across all nonzero patterns `b`. -/
theorem exists_common_suzuki_shift_lacunary_windows :
    ∃ δ : ℝ, 0 < δ ∧ ∃ M₀ : ℕ, ∀ (J : ℕ) (M L : ℕ → ℕ) (W : ℕ → Finset ℕ),
      LacunaryScaleWindows J M L W → M₀ ≤ M 0 →
      (∀ i < J, (L i : ℝ) ≤ (M 0 : ℝ) ^ δ) →
      ∀ {V : ℝ} (hV : 0 < V), criticalTruncationThreshold ≤ V →
        let T : Finset ℕ := (Finset.range J).biUnion W
        ∃ (k₀ : ℕ) (omega₀ : ℝ), 0 < omega₀ ∧
          ∀ b : ℕ → ℝ, (∃ n ∈ T, b n ≠ 0) →
            ∀ k ≥ k₀, ∀ omega : ℝ, 0 < omega → omega < omega₀ →
              omega * (compactFullWeilEnergy (criticalTruncatedTest hV T b) / 4) <
                autocorr (smoothCompactSource (criticalTruncatedTest hV T b) k) 0 -
                  suzukiCriticalSourcePairing
                    (smoothCompactSource (criticalTruncatedTest hV T b) k) omega ∧
              suzukiCriticalSourcePairing
                (smoothCompactSource (criticalTruncatedTest hV T b) k) omega <
                autocorr (smoothCompactSource (criticalTruncatedTest hV T b) k) 0 := by
  set s_arch := criticalTruncatedArchLogSlope
  have hs : 0 < s_arch := criticalTruncatedArchLogSlope_pos
  set Wp := directTruncatedWindowPrimeSlope
  have hWp : 0 ≤ Wp := directTruncatedWindowPrimeSlope_nonneg
  set δ := s_arch / (4 * (Wp + 1))
  have hδ : 0 < δ := by positivity
  set K_const := s_arch * criticalTruncatedArchLogOffset + criticalTruncatedWindowBaseConstant +
    1300 * truncatedCrossBlockConstant + 2 * Wp * windowRingMajorantUpperOffset
  have hlog : Tendsto (fun M : ℕ => Real.log M) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.mp ((hlog.eventually_gt_atTop (4 * K_const / s_arch)).and
    (eventually_ge_atTop 3))
  refine ⟨δ, hδ, M₀, fun J M L W h hM hL_pow {V} hV hVt => ?_⟩
  dsimp only
  obtain ⟨hlogM, _⟩ := hM₀ (M 0) hM
  set T : Finset ℕ := (Finset.range J).biUnion W
  have hM3 : 3 ≤ M 0 := h.1
  have hMpos : (0 : ℝ) < M 0 := by exact_mod_cast (show 0 < M 0 by omega)
  have hlogM_pos : 0 < Real.log (M 0) := Real.log_pos (by exact_mod_cast (show 1 < M 0 by omega))
  set γ := s_arch / 4 * Real.log (M 0)
  have hγ : 0 < γ := by unfold γ; positivity
  set C_sm := criticalSuzukiSmoothingCost hV T
  set E₀_T := criticalSuzukiEnergyEnvelope V T
  set B₀_T := criticalSuzukiIncrementEnvelope hV T
  set A_V := criticalSuzukiAperture V
  have hA_V : 0 < A_V := criticalSuzukiAperture_pos V
  have hB₀_nn : 0 ≤ B₀_T := by
    unfold B₀_T criticalSuzukiIncrementEnvelope
    exact mul_nonneg (criticalScaleLipschitzConstant_nonneg hV T)
      (mul_nonneg (mul_nonneg (by norm_num) (criticalSupportRadius_nonneg V))
        (criticalScaleAmplitudeConstant_nonneg T))
  obtain ⟨k₀, hk₀_gt⟩ := exists_nat_gt (2 * max C_sm 0 / γ)
  have hev : ∀ᶠ omega in 𝓝[>] (0 : ℝ),
      suzukiFirstVariationEnvelope A_V E₀_T B₀_T omega < γ / 4 :=
    (tendsto_suzukiFirstVariationEnvelope A_V E₀_T B₀_T).eventually
      (Iio_mem_nhds (by positivity))
  have ho2 : ∀ᶠ omega in 𝓝[>] (0 : ℝ), omega ≤ 2 :=
    mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds (by norm_num : (0 : ℝ) < 2))
  obtain ⟨s, hs_nhds, hs_sub⟩ := eventually_nhdsWithin_iff.mp (hev.and ho2)
  obtain ⟨ω₀, hω₀, hball⟩ := Metric.mem_nhds_iff.mp hs_nhds
  refine ⟨k₀, ω₀, hω₀, fun b hb k hk omega homega homega_lt => ?_⟩
  set g := criticalTruncatedTest hV T b
  set fk := smoothCompactSource g k
  set E := ∑ n ∈ T, b n ^ 2
  obtain ⟨j₀, hj₀, hbj₀⟩ := hb
  have hE_pos : 0 < E :=
    lt_of_lt_of_le (sq_pos_of_ne_zero hbj₀) (Finset.single_le_sum (fun i _ => sq_nonneg (b i)) hj₀)
  have hgap_i : ∀ i ∈ Finset.range J,
      γ ≤ s_arch * (Real.log (M 0) - criticalTruncatedArchLogOffset) -
        criticalTruncatedWindowBaseConstant - 1300 * truncatedCrossBlockConstant -
        2 * Wp * (Real.log (L i) + windowRingMajorantUpperOffset) := by
    intro i hi
    have hi_lt := Finset.mem_range.mp hi
    have hLi0 : (0 : ℝ) < L i := by exact_mod_cast h.2.1 i hi_lt
    have hlogLi : Real.log (L i) ≤ δ * Real.log (M 0) := by
      have := Real.log_le_log hLi0 (hL_pow i hi_lt)
      rwa [Real.log_rpow hMpos] at this
    have h1 : 2 * Wp * Real.log (L i) ≤ s_arch / 2 * Real.log (M 0) := by
      calc 2 * Wp * Real.log (L i) ≤ 2 * Wp * (δ * Real.log (M 0)) := by gcongr
        _ = s_arch / 2 * Real.log (M 0) * (Wp / (Wp + 1)) := by unfold δ; field_simp; ring
        _ ≤ s_arch / 2 * Real.log (M 0) * 1 := by
            gcongr; rw [div_le_one (by linarith)]; linarith
        _ = s_arch / 2 * Real.log (M 0) := by ring
    have h2 : K_const < s_arch / 4 * Real.log (M 0) := by
      have := (div_lt_iff₀ hs).mp hlogM; linarith
    unfold K_const at h2; unfold γ; linarith
  have hweil_ge : γ * E ≤ compactFullWeilEnergy g := by
    have hcomp := criticalTruncatedCompleteEnergy_ge_of_lacunaryWindows h b hVt
    rw [← compactFullWeilEnergy_criticalTruncatedTest hV] at hcomp
    have hsum_ge : γ * E ≤
        ∑ i ∈ Finset.range J,
          (s_arch * (Real.log (M 0) - criticalTruncatedArchLogOffset) -
            criticalTruncatedWindowBaseConstant - 1300 * truncatedCrossBlockConstant -
            2 * Wp * (Real.log (L i) + windowRingMajorantUpperOffset)) * ∑ n ∈ W i, b n ^ 2 := by
      dsimp only [E, T]
      rw [Finset.sum_biUnion h.pairwiseDisjoint, Finset.mul_sum]
      exact Finset.sum_le_sum fun i hi =>
        mul_le_mul_of_nonneg_right (hgap_i i hi) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
    exact hsum_ge.trans (EReal.coe_le_coe_iff.mp hcomp)
  have hsm_err := (compactFullWeilEnergy_smoothing_error_criticalTruncatedTest hV T b k).trans
    (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (le_max_left C_sm 0) (by positivity)) hE_pos.le)
  have hk_bound : max C_sm 0 / ((k : ℝ) + 1) ≤ γ / 2 := by
    rw [div_le_iff₀ (by positivity)]
    have hk_cast : (k₀ : ℝ) ≤ k := by exact_mod_cast hk
    have h1 : 2 * max C_sm 0 < (k₀ : ℝ) * γ := (div_lt_iff₀ hγ).mp hk₀_gt
    nlinarith
  have hfk_weil : compactFullWeilEnergy g / 2 ≤ compactFullWeilEnergy fk := by
    have hsm_low := (abs_le.mp hsm_err).1
    have h1 : max C_sm 0 / ((k : ℝ) + 1) * E ≤ (γ / 2) * E :=
      mul_le_mul_of_nonneg_right hk_bound hE_pos.le
    linarith
  have hmem : omega ∈ s := hball (by
    rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos homega]
    exact homega_lt)
  obtain ⟨henv_lt, homega2⟩ := hs_sub hmem homega
  obtain ⟨hfk_diff, hfk_cut, hfk_E, hfk_inc⟩ :=
    smoothCompactSource_criticalTruncatedTest_envelope hV T b k
  have herr := abs_suzukiCriticalSourcePairing_firstVariation_sub_le hfk_diff fk.hasCompactSupport
    hA_V hfk_cut hfk_E (mul_nonneg hE_pos.le hB₀_nn) hfk_inc homega homega2
  rw [suzukiFirstVariationEnvelope_mul A_V E₀_T B₀_T hE_pos.le omega] at herr
  have hlow' : -(E * suzukiFirstVariationEnvelope A_V E₀_T B₀_T omega) ≤
      (autocorr fk 0 - suzukiCriticalSourcePairing fk omega) / omega -
        compactFullWeilEnergy fk := (abs_le.mp herr).1
  have hmul_lt : E * suzukiFirstVariationEnvelope A_V E₀_T B₀_T omega < E * (γ / 4) :=
    mul_lt_mul_of_pos_left henv_lt hE_pos
  have hquot : compactFullWeilEnergy g / 4 <
      (autocorr fk 0 - suzukiCriticalSourcePairing fk omega) / omega := by linarith
  have hdef : omega * (compactFullWeilEnergy g / 4) <
      autocorr fk 0 - suzukiCriticalSourcePairing fk omega := by
    simpa only [mul_comm] using (lt_div_iff₀ homega).mp hquot
  have hg_pos : 0 < compactFullWeilEnergy g := lt_of_lt_of_le (mul_pos hγ hE_pos) hweil_ge
  exact ⟨hdef, by
    have hpos : 0 < omega * (compactFullWeilEnergy g / 4) := by positivity
    linarith only [hdef, hpos]⟩

/-! ## Section 3: Truncation Dependence (`V → ∞`), Untruncated `O(r^{-3/2})` Correlation Decay, and Receiver Transfer Without Archimedean Subsidy -/

/-- **Untruncated `O(r^{-3/2})` Logarithmic Correlation Decay of Critical Arithmetic Sources.**
Without any upper compact truncation `V`, the bounded phase primitive gains one full dilation
power on `(1, ∞)` beyond the `r^{-1/2}` critical envelope, so the logarithmic autocorrelation of
`criticalFactorialSource S b` at `log r` (`r ≥ 1`) decays as `O(r^{-3/2})`. Contrast this with the
literal unsubtracted Suzuki pairing `suzukiCriticalSourcePairing`, whose growing polar branch
`e^{(1/2 - ω) s}` requires a finite correlation cutoff `A_V = 2(max(log(2V), 0) + 1) + 1`. -/
theorem abs_criticalFactorialSource_correlation_le_rpow (S : Finset ℕ) (b : ℕ → ℝ)
    {r : ℕ} (hr : 1 ≤ r) :
    |∫ x : ℝ, criticalFactorialSource S b x *
      criticalFactorialSource S b (x - Real.log (r : ℝ))| ≤
      criticalFactorialPrimeConstant S b / (r : ℝ) ^ (3 / 2 : ℝ) := by
  have hr_pos : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hrs : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hr_pos
  have hcorr := critical_factorial_physical_correlation_bound S b (r - 1)
  rw [Nat.sub_add_cancel hr] at hcorr
  rw [criticalFactorialSource_correlation_eq S b hr1, abs_mul, abs_of_pos (inv_pos.mpr hrs)]
  have hrpow : Real.sqrt (r : ℝ) * (r : ℝ) = (r : ℝ) ^ (3 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add_one hr_pos.ne']
    norm_num
  calc (Real.sqrt (r : ℝ))⁻¹ *
        |∫ v in Ioi (1 : ℝ), v ^ (-2 : ℝ) *
          (factorialPhaseCombination S (fun n => (b n : ℂ)) v).re *
          (factorialPhaseCombination S (fun n => (b n : ℂ)) ((r : ℝ) * v)).re|
      ≤ (Real.sqrt (r : ℝ))⁻¹ * (criticalFactorialPrimeConstant S b / (r : ℝ)) :=
        mul_le_mul_of_nonneg_left hcorr (inv_pos.mpr hrs).le
    _ = criticalFactorialPrimeConstant S b / (Real.sqrt (r : ℝ) * (r : ℝ)) := by field_simp
    _ = criticalFactorialPrimeConstant S b / (r : ℝ) ^ (3 / 2 : ℝ) := by rw [hrpow]

/-- **Unconditional Common-Shift Suzuki Deficit on Small-Aperture Receiver Tests (`[-3/10, 3/10]`)
Without Any Archimedean Scale Subsidy.**
For every normalized increment-slope bound `B₀ ≥ 0`, there exists a common shift threshold
`ω₀ > 0` such that every nonzero `F ∈ C_c²([-3/10, 3/10], ℝ)` satisfying
`autocorr F 0 - autocorr F t ≤ B₀ * autocorr F 0 * t` (`t > 0`) has a strict first-order Suzuki
deficit on `(0, ω₀)` with margin `(1 / 10000) * autocorr F 0` — with no scale parameter `M → ∞`. -/
theorem exists_common_suzuki_shift_small_aperture_receiver {B₀ : ℝ} (hB₀ : 0 ≤ B₀) :
    ∃ omega₀ : ℝ, 0 < omega₀ ∧ ∀ omega : ℝ, 0 < omega → omega < omega₀ →
      ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x : ℝ, 3 / 10 < |x| → F x = 0) →
        (∀ t : ℝ, 0 < t → autocorr F 0 - autocorr F t ≤ (autocorr F 0 * B₀) * t) →
        0 < autocorr F 0 →
          omega * ((1 / 10000) * autocorr F 0) <
            autocorr F 0 - suzukiCriticalSourcePairing F omega ∧
          suzukiCriticalSourcePairing F omega < autocorr F 0 := by
  let Sub := {F : ℝ → ℝ // ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
    (∀ x : ℝ, 3 / 10 < |x| → F x = 0) ∧
    (∀ t : ℝ, 0 < t → autocorr F 0 - autocorr F t ≤ (autocorr F 0 * B₀) * t)}
  obtain ⟨omega₀, homega₀, hcommon⟩ :=
    exists_common_suzuki_shift_of_bounded_envelope_family
      (ι := Sub) (f := Subtype.val) (w := fun F => autocorr F.1 0)
      (A := 1) (E₀ := 1) (B := B₀) (γ := 1 / 5000)
      zero_lt_one hB₀ (by norm_num)
      (fun F => F.2.1) (fun F => F.2.2.1)
      (fun F t ht => autocorr_eq_zero_of_far F.2.2.2.1 (by linarith [le_abs_self t]))
      (fun F => by rw [mul_one])
      (fun F => F.2.2.2.2)
      (fun F => by
        set Fc : C_c(ℝ, ℝ) := ⟨⟨F.1, F.2.1.continuous⟩, F.2.2.1⟩
        have h1 := (compactFullWeilEnergy_and_gridTent_ge_of_support_le_threeTenths
          F.2.1 F.2.2.1 F.2.2.2.1).1
        have hsq : autocorr F.1 0 = ∫ x, F.1 x ^ 2 := by
          unfold autocorr; simp only [add_zero, sq]
        change 1 / 5000 * autocorr F.1 0 ≤ compactFullWeilEnergy Fc
        rw [hsq]
        linarith)
  refine ⟨omega₀, homega₀, fun omega homega homega_lt F hF hFc hsupp hinc hpos => ?_⟩
  simpa only [show (1 / 5000 : ℝ) / 2 = 1 / 10000 by norm_num] using
    hcommon omega homega homega_lt ⟨F, hF, hFc, hsupp, hinc⟩ hpos

/-- **Unconditional Common-Shift Suzuki Deficit on Odd Receiver Tests Past the First Prime
(`[-181/500, 181/500]`, `(log 2)/2 < 181/500`) Without Any Archimedean Scale Subsidy.** -/
theorem exists_common_suzuki_shift_odd_receiver_past_two {B₀ : ℝ} (hB₀ : 0 ≤ B₀) :
    Real.log 2 / 2 < 181 / 500 ∧
    ∃ omega₀ : ℝ, 0 < omega₀ ∧ ∀ omega : ℝ, 0 < omega → omega < omega₀ →
      ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x : ℝ, F (-x) = -F x) →
        (∀ x : ℝ, 181 / 500 < |x| → F x = 0) →
        (∀ t : ℝ, 0 < t → autocorr F 0 - autocorr F t ≤ (autocorr F 0 * B₀) * t) →
        0 < autocorr F 0 →
          omega * ((1 / 2000) * autocorr F 0) <
            autocorr F 0 - suzukiCriticalSourcePairing F omega ∧
          suzukiCriticalSourcePairing F omega < autocorr F 0 := by
  refine ⟨half_log_two_lt_threeHundredSixtyTwoThousandths, ?_⟩
  let Sub := {F : ℝ → ℝ // ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
    (∀ x : ℝ, F (-x) = -F x) ∧ (∀ x : ℝ, 181 / 500 < |x| → F x = 0) ∧
    (∀ t : ℝ, 0 < t → autocorr F 0 - autocorr F t ≤ (autocorr F 0 * B₀) * t)}
  obtain ⟨omega₀, homega₀, hcommon⟩ :=
    exists_common_suzuki_shift_of_bounded_envelope_family
      (ι := Sub) (f := Subtype.val) (w := fun F => autocorr F.1 0)
      (A := 1) (E₀ := 1) (B := B₀) (γ := 1 / 1000)
      zero_lt_one hB₀ (by norm_num)
      (fun F => F.2.1) (fun F => F.2.2.1)
      (fun F t ht => autocorr_eq_zero_of_far F.2.2.2.2.1 (by linarith [le_abs_self t]))
      (fun F => by rw [mul_one])
      (fun F => F.2.2.2.2.2)
      (fun F => by
        set Fc : C_c(ℝ, ℝ) := ⟨⟨F.1, F.2.1.continuous⟩, F.2.2.1⟩
        have h1 := (compactFullWeilEnergy_and_gridTent_ge_of_odd_support_le_threeHundredSixtyTwoThousandths
          F.2.1 F.2.2.1 F.2.2.2.1 F.2.2.2.2.1).2.1
        have hsq : autocorr F.1 0 = ∫ x, F.1 x ^ 2 := by
          unfold autocorr; simp only [add_zero, sq]
        change 1 / 1000 * autocorr F.1 0 ≤ compactFullWeilEnergy Fc
        rw [hsq]
        linarith)
  refine ⟨omega₀, homega₀, fun omega homega homega_lt F hF hFc hodd hsupp hinc hpos => ?_⟩
  simpa only [show (1 / 1000 : ℝ) / 2 = 1 / 2000 by norm_num] using
    hcommon omega homega homega_lt ⟨F, hF, hFc, hodd, hsupp, hinc⟩ hpos

/-- **Individual Suzuki-to-Receiver Transfer Equivalence (No Archimedean Subsidy Needed).**
For any compact `C²` real test `F` and any real margin `μ`, a small-shift Suzuki deficit of slope
at least `μ - δ` (`∀ δ > 0`) is unconditionally equivalent to `μ ≤ (zetaZeroConfig.W F F).re`
(and hence implies `configurationReflectionDefect zetaZeroConfig F + μ ≤ configurationSquareMass zetaZeroConfig F`). -/
theorem suzuki_small_shift_deficit_iff_receiver_weil_ge {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hFc : HasCompactSupport F) (μ : ℝ) :
    ((∀ δ : ℝ, 0 < δ → ∀ᶠ omega : ℝ in 𝓝[>] 0,
        omega * (μ - δ) ≤ autocorr F 0 - suzukiCriticalSourcePairing F omega) ↔
      μ ≤ (zetaZeroConfig.W (fun x => (F x : ℂ)) (fun x => (F x : ℂ))).re) ∧
    (μ ≤ (zetaZeroConfig.W (fun x => (F x : ℂ)) (fun x => (F x : ℂ))).re →
      configurationReflectionDefect zetaZeroConfig (fun x => (F x : ℂ)) + μ ≤
        configurationSquareMass zetaZeroConfig (fun x => (F x : ℂ))) := by
  have hF_c : ContDiff ℝ 2 (fun x => (F x : ℂ)) := Complex.ofRealCLM.contDiff.comp hF
  have hFc_c : HasCompactSupport (fun x => (F x : ℂ)) := hFc.comp_left Complex.ofReal_zero
  have hW_eq : (zetaZeroConfig.W (fun x => (F x : ℂ)) (fun x => (F x : ℂ))).re =
      (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
        (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re :=
    congrArg Complex.re (zeta_W_eq_weilFullFunctional hF_c hFc_c)
  have hlim := tendsto_suzukiCriticalSourcePairing_firstVariation_of_contDiff hF hFc
  refine ⟨?_, fun hge => ?_⟩
  · rw [hW_eq]
    constructor
    · intro hdef
      haveI : (𝓝[>] (0 : ℝ)).NeBot := nhdsWithin_Ioi_neBot le_rfl
      refine le_of_forall_pos_le_add fun δ hδ => ?_
      have hev : ∀ᶠ omega : ℝ in 𝓝[>] 0,
          μ - δ ≤ (autocorr F 0 - suzukiCriticalSourcePairing F omega) / omega := by
        filter_upwards [self_mem_nhdsWithin, hdef δ hδ] with omega homega hle
        change 0 < omega at homega
        exact (le_div_iff₀ homega).mpr (by linarith)
      have hge := ge_of_tendsto hlim hev
      linarith
    · intro hge δ hδ
      have hlt : μ - δ < (weilFullFunctional (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
          (EF.weilTest (fun x => (F x : ℂ)) (fun x => (F x : ℂ)))).re := by linarith
      filter_upwards [self_mem_nhdsWithin, hlim.eventually (Ioi_mem_nhds hlt)] with omega homega hq
      change 0 < omega at homega
      change μ - δ < (autocorr F 0 - suzukiCriticalSourcePairing F omega) / omega at hq
      have := (lt_div_iff₀ homega).mp hq
      linarith
  · have hrefl := zetaZeroConfig.W_re_eq_squareMass_sub_reflectionDefect (fun x => (F x : ℂ))
    linarith

/-- **Graded Zero-Width Receiver Law From Small-Shift Suzuki Deficits Without Archimedean Subsidy.**
If for some `σ ≥ 0` and `C : ℝ`, every odd receiver test `F ∈ C_c²([-r, r], ℝ)` (`r > 0`) satisfies
the small-shift Suzuki deficit floor
`-(C * e^{2σ r} * autocorr F 0 + δ) * ω ≤ autocorr F 0 - suzukiCriticalSourcePairing F ω`
eventually as `ω → 0⁺` for every `δ > 0`, then `zetaZeroWidth ≤ σ` unconditionally. -/
theorem zetaZeroWidth_le_of_graded_odd_suzuki_deficit {σ C : ℝ} (hσ : 0 ≤ σ)
    (hsuz : ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
      (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
      ∀ δ : ℝ, 0 < δ → ∀ᶠ omega : ℝ in 𝓝[>] 0,
        omega * (-(C * Real.exp (2 * σ * r) * autocorr F 0) - δ) ≤
          autocorr F 0 - suzukiCriticalSourcePairing F omega) :
    zetaZeroWidth ≤ σ := by
  refine zetaZeroWidth_le_of_graded_odd_fullZeroForm_floor (C := C) hσ ?_
  intro r hr F hF hFc hodd hsupp
  have hiff := (suzuki_small_shift_deficit_iff_receiver_weil_ge hF hFc
    (-(C * Real.exp (2 * σ * r) * autocorr F 0))).1
  have hge := hiff.mp (hsuz r hr F hF hFc hodd hsupp)
  rw [← fullZeroForm_eq_zeta_W_re hF hFc] at hge
  have hsq : autocorr F 0 = ∫ x, F x ^ 2 := by
    unfold autocorr; simp only [add_zero, sq]
  rwa [hsq] at hge

/-- **Unconditional `RiemannHypothesis` Equivalence With Small-Shift Suzuki Non-Overshoot.**
`RiemannHypothesis` holds if and only if:
1. For every compact `C²` real test `F` and every `δ > 0`, the literal Suzuki pairing has no
   small-shift linear overshoot above `autocorr F 0`:
   `∀ᶠ ω in 𝓝[>] 0, -δ * ω ≤ autocorr F 0 - suzukiCriticalSourcePairing F ω`;
2. Equivalently, on the odd receiver sector alone with a subexponential rate floor: for every
   `σ > 0` there exists `C : ℝ` such that for every `r > 0`, every odd `F ∈ C_c²([-r, r], ℝ)`, and
   every `δ > 0`,
   `∀ᶠ ω in 𝓝[>] 0, ω * (-(C * e^{2σ r} * autocorr F 0) - δ) ≤ autocorr F 0 - suzukiCriticalSourcePairing F ω`. -/
theorem riemannHypothesis_iff_suzuki_small_shift_non_overshoot :
    (RiemannHypothesis ↔
      ∀ F : ℝ → ℝ, ContDiff ℝ 2 F → HasCompactSupport F →
        ∀ δ : ℝ, 0 < δ → ∀ᶠ omega : ℝ in 𝓝[>] 0,
          -δ * omega ≤ autocorr F 0 - suzukiCriticalSourcePairing F omega) ∧
    (RiemannHypothesis ↔
      ∀ σ : ℝ, 0 < σ → ∃ C : ℝ, ∀ r : ℝ, 0 < r → ∀ F : ℝ → ℝ,
        ContDiff ℝ 2 F → HasCompactSupport F →
        (∀ x, F (-x) = -F x) → (∀ x, r < |x| → F x = 0) →
        ∀ δ : ℝ, 0 < δ → ∀ᶠ omega : ℝ in 𝓝[>] 0,
          omega * (-(C * Real.exp (2 * σ * r) * autocorr F 0) - δ) ≤
            autocorr F 0 - suzukiCriticalSourcePairing F omega) := by
  refine ⟨?_, ?_⟩
  · constructor
    · intro hRH F hF hFc δ hδ
      have hF_c : ContDiff ℝ 2 (fun x => (F x : ℂ)) := Complex.ofRealCLM.contDiff.comp hF
      have hFc_c : HasCompactSupport (fun x => (F x : ℂ)) := hFc.comp_left Complex.ofReal_zero
      have h0 : 0 ≤ (zetaZeroConfig.W (fun x => (F x : ℂ)) (fun x => (F x : ℂ))).re := by
        rw [zeta_W_eq_weilFullFunctional hF_c hFc_c]
        exact (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) _ hF_c hFc_c
      have hev := (suzuki_small_shift_deficit_iff_receiver_weil_ge hF hFc 0).1.mpr h0 δ hδ
      filter_upwards [hev] with omega hle
      linarith
    · intro hsuz
      rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero]
      refine le_antisymm ?_ zetaZeroWidth_nonneg
      refine zetaZeroWidth_le_of_graded_odd_suzuki_deficit (C := 0) le_rfl ?_
      intro r _ F hF hFc _ _ δ hδ
      filter_upwards [hsuz F hF hFc δ hδ] with omega hle
      simp only [zero_mul, neg_zero, zero_sub]
      linarith
  · constructor
    · intro hRH σ _
      refine ⟨0, fun r _ F hF hFc _ _ δ hδ => ?_⟩
      have hF_c : ContDiff ℝ 2 (fun x => (F x : ℂ)) := Complex.ofRealCLM.contDiff.comp hF
      have hFc_c : HasCompactSupport (fun x => (F x : ℂ)) := hFc.comp_left Complex.ofReal_zero
      have h0 : 0 ≤ (zetaZeroConfig.W (fun x => (F x : ℂ)) (fun x => (F x : ℂ))).re := by
        rw [zeta_W_eq_weilFullFunctional hF_c hFc_c]
        exact (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) _ hF_c hFc_c
      have hev := (suzuki_small_shift_deficit_iff_receiver_weil_ge hF hFc 0).1.mpr h0 δ hδ
      filter_upwards [hev] with omega hle
      simp only [zero_mul, neg_zero, zero_sub]
      linarith
    · intro hsub
      rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero]
      refine le_antisymm ?_ zetaZeroWidth_nonneg
      refine le_of_forall_pos_le_add fun σ hσ => ?_
      rw [zero_add]
      obtain ⟨C, hC⟩ := hsub σ hσ
      exact zetaZeroWidth_le_of_graded_odd_suzuki_deficit hσ.le hC

end GaloisForLFunctions.ArithmeticPositivityTheory
end
