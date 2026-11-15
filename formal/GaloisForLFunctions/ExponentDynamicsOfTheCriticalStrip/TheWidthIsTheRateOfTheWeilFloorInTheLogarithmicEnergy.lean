import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TransformsSampledOnLogarithmicallyDensePoints
import GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.EveryRulerCarriesTheSeedAndEveryLever
import GaloisForLFunctions.SquareRootThreshold.TheWidthIsTheGroundEnergyRateWhenOffLineZerosDoNotCluster
import GaloisForLFunctions.SquareRootThreshold.GroundEnergyAbscissaAndLagGridAttainmentBridge
import GaloisForLFunctions.RHTower.XiEndpointSchwarzPairHeightGap

/-!
# The zero width is the rate of the Weil floor in the logarithmic energy

The margin of the Weil form is a half ruler in the mass normalisation: a floor
`W(f, f) ≥ −C e^{2βa} ∫|f|²` on sources of aperture `a` gives `zetaZeroWidth ≤ β`, and the converse
needs the off-line zeros not to cluster, since a unit window at height `T` may carry `C log T` of
them. Normalising by the logarithmic energy `E(f) = ∫₀¹ ‖f(· + t) − f‖² dt/t` makes the ruler exact.

* **The floor** (`sourceQuadratic_ge_neg_logEnergy`, `abs_sourceQuadratic_le_logEnergy`): for
  every smooth source `u` of aperture `a`,
  `|W(u, u)| ≤ 160 · 4 (2a + 2 + 2π) e^{2π} e^{σ(2a+3)} (E(u) + ∫|u|²)` with `σ = zetaZeroWidth`.
  No hypothesis on the zeros and no loss in the exponent. On the zero side the on-line copies
  contribute `|Φ(γ)|² ≥ 0` and every copy between `∓(|Φ(z)|² + |Φ(z̄)|²)/2`; the weights
  `1/log(|Im ρ| + 5)` are bounded by `160` on unit windows (local zero count; no zero below height
  `13/2`), and the sampling inequality with the logarithmic weight pays for the logarithm with
  `E(u)`.
* **The ruler** (`isRuler_logEnergyFloor`): for `β ≥ 0`, `zetaZeroWidth ≤ β` iff
  `W(u, u) ≥ −C (1 + a) e^{2βa} (E(u) + ∫|u|²)` for all smooth sources. The receiver is the lag family
  `κ(· + v/2) − κ(· − v/2)` of one bump: its mass is constant and its logarithmic energy grows
  linearly in `v`, so the floor gives `W ≥ −C' e^{(β+ε)v}` along the family, and the lag family
  measures the abscissa.
* **Readings**: the floor at the width itself (`logEnergyFloor_zetaZeroWidth`), at the seed `3/8`
  (`logEnergyFloor_three_eighths`), and at `0` exactly under the Riemann hypothesis
  (`riemannHypothesis_iff_logEnergyFloor_zero`): a floor polynomial in the aperture is the line.
* **Bounded oscillation** (`sourceQuadratic_ge_neg_mass_of_logEnergy_le`): on sources with
  `E(u) ≤ κ ∫|u|²` the floor holds in the mass normalisation at the exact rate.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real
open GaloisForLFunctions.HTGeometry _root_.Zeta23 _root_.RHTower _root_.RHTower.CCMParityQuartet
open GaloisForLFunctions.SquareRootThreshold

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

noncomputable section

/-! ### 1. The logarithmic weights of the zero copies on unit windows -/

/-- No zero copy has height below `13/2`. -/
theorem thirteen_halves_lt_abs_re_xiSpectralPoint (q : XiZeroCopy) :
    13 / 2 < |(xiSpectralPoint q).re| := by
  have hre : (xiSpectralPoint q).re = (q.1 : ℂ).im := by simp [xiSpectralPoint]
  rw [hre]
  exact not_le.mp fun h =>
    xi_ne_zero_of_abs_im_le_thirteen_halves h (xi_eq_zero_of_mem_divisor_support q.1)

/-- **The weights `1/log(|Im ρ| + 5)` sum to at most `160` on every unit window**: a window at
height `|T| ≥ 4` carries at most `40 log(180|T|) ≤ 160 log(|T| + 4)` copies, and a lower window
none. -/
theorem sum_inv_log_height_window_le (T : ℝ) (t : Finset XiZeroCopy)
    (ht : ∀ q ∈ t, |-(xiSpectralPoint q).re - T| ≤ 1) :
    ∑ q ∈ t, (Real.log (|-(xiSpectralPoint q).re| + 5))⁻¹ ≤ 160 := by
  have hre : ∀ q : XiZeroCopy, (xiSpectralPoint q).re = (q.1 : ℂ).im := fun q => by
    simp [xiSpectralPoint]
  by_cases hT : 4 ≤ |T|
  · have hcard := card_le_of_ordinates_in_window (t := -T) (by rwa [abs_neg]) t fun q hq => by
      have h := ht q hq
      rw [hre q] at h
      rwa [show (q.1 : ℂ).im - -T = -(-(q.1 : ℂ).im - T) by ring, abs_neg]
    rw [abs_neg] at hcard
    have hL : 0 < Real.log (|T| + 4) := Real.log_pos (by linarith)
    have h512 : (512 : ℝ) ≤ (|T| + 4) ^ 3 := by
      have h8 : (8 : ℝ) ^ 3 ≤ (|T| + 4) ^ 3 := pow_le_pow_left₀ (by norm_num) (by linarith) 3
      norm_num at h8
      exact h8
    have hpow : 180 * |T| ≤ (|T| + 4) ^ 4 := by
      have h4 : (|T| + 4) ^ 4 = (|T| + 4) * (|T| + 4) ^ 3 := by ring
      rw [h4]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ |T| + 4) (sub_nonneg.mpr h512)]
    have hlog : Real.log (180 * |T|) ≤ 4 * Real.log (|T| + 4) := by
      have h := Real.log_le_log (by linarith : (0 : ℝ) < 180 * |T|) hpow
      rw [Real.log_pow] at h
      push_cast at h
      exact h
    have hterm : ∀ q ∈ t,
        (Real.log (|-(xiSpectralPoint q).re| + 5))⁻¹ ≤ (Real.log (|T| + 4))⁻¹ := by
      intro q hq
      have h1 := ht q hq
      have h2 := abs_sub (-(xiSpectralPoint q).re) (-(xiSpectralPoint q).re - T)
      rw [show -(xiSpectralPoint q).re - (-(xiSpectralPoint q).re - T) = T by ring] at h2
      exact inv_anti₀ hL (Real.log_le_log (by linarith) (by linarith))
    calc ∑ q ∈ t, (Real.log (|-(xiSpectralPoint q).re| + 5))⁻¹
        ≤ ∑ _q ∈ t, (Real.log (|T| + 4))⁻¹ := Finset.sum_le_sum hterm
      _ = (t.card : ℝ) * (Real.log (|T| + 4))⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 40 * (4 * Real.log (|T| + 4)) * (Real.log (|T| + 4))⁻¹ :=
          mul_le_mul_of_nonneg_right (hcard.trans (by linarith)) (inv_nonneg.mpr hL.le)
      _ = 160 := by
          rw [show (40 : ℝ) * (4 * Real.log (|T| + 4)) * (Real.log (|T| + 4))⁻¹ =
            160 * (Real.log (|T| + 4) * (Real.log (|T| + 4))⁻¹) by ring,
            mul_inv_cancel₀ hL.ne', mul_one]
  · have hempty : t = ∅ := by
      by_contra hne
      obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have h1 := ht q hq
      have h2 := thirteen_halves_lt_abs_re_xiSpectralPoint q
      have h3 := abs_sub (-(xiSpectralPoint q).re - T) (-T)
      rw [show -(xiSpectralPoint q).re - T - -T = -(xiSpectralPoint q).re by ring, abs_neg,
        abs_neg] at h3
      linarith [not_le.mp hT]
    rw [hempty]
    simp

/-! ### 2. The floor -/

/-- The sample of a function at a zero copy: `(|Φ(−z)|² + |Φ(−z̄)|²)/2` for its transform `Φ`. -/
def zeroSample (f : ℝ → ℂ) (q : XiZeroCopy) : ℝ :=
  (‖testTransform f (-xiSpectralPoint q)‖ ^ 2 +
    ‖testTransform f (-(starRingEnd ℂ) (xiSpectralPoint q))‖ ^ 2) / 2

theorem zeroSample_nonneg (f : ℝ → ℂ) (q : XiZeroCopy) : 0 ≤ zeroSample f q := by
  unfold zeroSample
  positivity

/-- **The samples at the zero copies are bounded by the logarithmic energy**: for a continuous
`f` supported in `[−a, a]`,
`Σ_q (|Φ(−z_q)|² + |Φ(−z̄_q)|²)/2 ≤ 160 · L(a, σ) (E(f) + ∫|f|²)` with `σ` the zero width. The
weights `1/log(|Im ρ| + 5)` are bounded by `160` on unit windows, and the sampling inequality
with the logarithmic weight pays for the logarithm with `E(f)`. -/
theorem sum_zeroSample_le {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ} (hf : IntervalSource a f)
    (hG : IntervalIntegrable (fun t => (∫ u, ‖f (u + t) - f u‖ ^ 2) / t) volume 0 1)
    (s : Finset XiZeroCopy) :
    ∑ q ∈ s, zeroSample f q ≤
      160 * (logSamplingConst a zetaZeroWidth * (logEnergy f + ∫ x, ‖f x‖ ^ 2)) := by
  set B := 160 * (logSamplingConst a zetaZeroWidth * (logEnergy f + ∫ x, ‖f x‖ ^ 2)) with hB
  have hℓ0 : ∀ q : XiZeroCopy, 0 < Real.log (|-(xiSpectralPoint q).re| + 5) := fun q =>
    Real.log_pos (by linarith [abs_nonneg (-(xiSpectralPoint q).re)])
  -- the sampled sum over the copies, at any depths within the width
  have hkey : ∀ y : XiZeroCopy → ℝ, (∀ q, |y q| ≤ zetaZeroWidth) → ∀ s : Finset XiZeroCopy,
      ∑ q ∈ s, ‖testTransform f (((-(xiSpectralPoint q).re : ℝ) : ℂ) + (y q : ℂ) * I)‖ ^ 2 ≤
        B := by
    intro y hy s
    have h := sum_weight_mul_log_mul_norm_sq_testTransform_le ha hf
      (fun q : XiZeroCopy => -(xiSpectralPoint q).re) y
      (fun q : XiZeroCopy => (Real.log (|-(xiSpectralPoint q).re| + 5))⁻¹)
      zetaZeroWidth_nonneg hy (fun q => (inv_pos.mpr (hℓ0 q)).le) s
      (fun T t _ ht => sum_inv_log_height_window_le T t ht) hG
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun q _ => ?_)) h
    exact (inv_mul_cancel_left₀ (hℓ0 q).ne' _).symm
  have hdepth : ∀ q : XiZeroCopy, |-(xiSpectralPoint q).im| ≤ zetaZeroWidth := fun q => by
    rw [abs_neg]
    exact _root_.RHTower.abs_im_xiSpectralPoint_le_zetaZeroWidth q
  have hA : ∑ q ∈ s, ‖testTransform f (-xiSpectralPoint q)‖ ^ 2 ≤ B := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun q _ => ?_))
      (hkey (fun q => -(xiSpectralPoint q).im) hdepth s)
    congr 3
    apply Complex.ext <;> simp
  have hA' : ∑ q ∈ s, ‖testTransform f (-(starRingEnd ℂ) (xiSpectralPoint q))‖ ^ 2 ≤ B := by
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun q _ => ?_))
      (hkey (fun q => (xiSpectralPoint q).im) _root_.RHTower.abs_im_xiSpectralPoint_le_zetaZeroWidth s)
    congr 3
    apply Complex.ext <;> simp
  unfold zeroSample
  rw [← Finset.sum_div, Finset.sum_add_distrib]
  linarith

theorem summable_zeroSample {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ} (hf : IntervalSource a f)
    (hG : IntervalIntegrable (fun t => (∫ u, ‖f (u + t) - f u‖ ^ 2) / t) volume 0 1) :
    Summable (zeroSample f) :=
  summable_of_sum_le (zeroSample_nonneg f) (sum_zeroSample_le ha hf hG)

theorem tsum_zeroSample_le {a : ℝ} (ha : 0 < a) {f : ℝ → ℂ} (hf : IntervalSource a f)
    (hG : IntervalIntegrable (fun t => (∫ u, ‖f (u + t) - f u‖ ^ 2) / t) volume 0 1) :
    ∑' q, zeroSample f q ≤
      160 * (logSamplingConst a zetaZeroWidth * (logEnergy f + ∫ x, ‖f x‖ ^ 2)) :=
  (summable_zeroSample ha hf hG).tsum_le_of_sum_le (sum_zeroSample_le ha hf hG)

/-- A zero term lies between `∓` the sample. -/
theorem abs_re_zeroSumTerm_le (f : ℝ → ℂ) (q : XiZeroCopy) :
    |(zeroSumTerm f (xiSpectralPoint q)).re| ≤ zeroSample f q := by
  have h1 := Complex.abs_re_le_norm (zeroSumTerm f (xiSpectralPoint q))
  have h2 : ‖zeroSumTerm f (xiSpectralPoint q)‖ = ‖testTransform f (-xiSpectralPoint q)‖ *
      ‖testTransform f (-(starRingEnd ℂ) (xiSpectralPoint q))‖ := by
    simp only [CCMParityQuartet.zeroSumTerm, norm_mul, Complex.norm_conj]
  unfold zeroSample
  nlinarith [sq_nonneg (‖testTransform f (-xiSpectralPoint q)‖ -
    ‖testTransform f (-(starRingEnd ℂ) (xiSpectralPoint q))‖)]

/-- The logarithmic energy density of a smooth source is integrable. -/
theorem intervalIntegrable_logEnergy_source {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    IntervalIntegrable (fun t => (∫ x, ‖u (x + t) - u x‖ ^ 2) / t) volume 0 1 := by
  have hu2 : ContDiff ℝ 2 (u : ℝ → ℂ) := u.smooth.of_le (WithTop.coe_le_coe.mpr le_top)
  obtain ⟨K, hK⟩ := hu2.lipschitzWith_of_hasCompactSupport u.hasCompactSupport (by norm_num)
  exact intervalIntegrable_logEnergy_of_lipschitz a.2.le (smoothSource_intervalSource u) hK

/-- **The Weil form is bounded by the logarithmic energy.** For a smooth source `u` of aperture
`a`, `|W(u, u)| ≤ 160 · 4 (2a + 2 + 2π) e^{2π} e^{σ(2a+3)} (E(u) + ∫|u|²)` with `σ` the zero
width: each zero term lies between `∓(|Φ(z)|² + |Φ(z̄)|²)/2`. -/
theorem abs_sourceQuadratic_le_logEnergy {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    |ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector| ≤
      160 * (logSamplingConst a.1 zetaZeroWidth * (logEnergy u + ∫ x, ‖u x‖ ^ 2)) := by
  have hI := smoothSource_intervalSource u
  have hG := intervalIntegrable_logEnergy_source u
  have hS := summable_zeroSample a.2 hI hG
  have hle := tsum_zeroSample_le a.2 hI hG
  have hsumm : Summable fun q : XiZeroCopy => zeroSumTerm u (xiSpectralPoint q) :=
    summable_zeroSumTerm u
  have hsumm_re : Summable fun q : XiZeroCopy => (zeroSumTerm u (xiSpectralPoint q)).re :=
    Complex.reCLM.summable hsumm
  rw [sourceQuadratic_eq_re_tsum, Complex.re_tsum hsumm, abs_le]
  constructor
  · calc -(160 * (logSamplingConst a.1 zetaZeroWidth * (logEnergy u + ∫ x, ‖u x‖ ^ 2)))
        ≤ -∑' q, zeroSample u q := neg_le_neg hle
      _ = ∑' q, -zeroSample u q := by rw [tsum_neg]
      _ ≤ ∑' q, (zeroSumTerm u (xiSpectralPoint q)).re :=
          hS.neg.tsum_le_tsum (fun q => (abs_le.mp (abs_re_zeroSumTerm_le u q)).1) hsumm_re
  · exact (hsumm_re.tsum_le_tsum (fun q => (abs_le.mp (abs_re_zeroSumTerm_le u q)).2) hS).trans
      hle

/-- **The Weil floor in the logarithmic energy.** For a smooth source `u` of aperture `a`,
`W(u, u) ≥ −160 · 4 (2a + 2 + 2π) e^{2π} e^{σ(2a+3)} (E(u) + ∫|u|²)` with `σ` the zero width. -/
theorem sourceQuadratic_ge_neg_logEnergy {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    -(160 * (logSamplingConst a.1 zetaZeroWidth * (logEnergy u + ∫ x, ‖u x‖ ^ 2))) ≤
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector :=
  (abs_le.mp (abs_sourceQuadratic_le_logEnergy u)).1

/-- The bound for the Weil form of the zeros of `ζ`. -/
theorem abs_zetaZeroConfig_re_W_le_logEnergy {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    |(zetaZeroConfig.W u u).re| ≤
      160 * (logSamplingConst a.1 zetaZeroWidth * (logEnergy u + ∫ x, ‖u x‖ ^ 2)) := by
  rw [← ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil]
  exact abs_sourceQuadratic_le_logEnergy u

/-- The floor for the Weil form of the zeros of `ζ`. -/
theorem zetaZeroConfig_re_W_ge_neg_logEnergy {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    -(160 * (logSamplingConst a.1 zetaZeroWidth * (logEnergy u + ∫ x, ‖u x‖ ^ 2))) ≤
      (zetaZeroConfig.W u u).re := by
  rw [← ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil]
  exact sourceQuadratic_ge_neg_logEnergy u

/-- **Bounded oscillation.** On sources with `E(u) ≤ κ ∫|u|²` the floor holds in the mass
normalisation, at the exact rate and with no hypothesis on the zeros. -/
theorem sourceQuadratic_ge_neg_mass_of_logEnergy_le {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) {κ : ℝ} (hκ : logEnergy u ≤ κ * ∫ x, ‖u x‖ ^ 2) :
    -(160 * (logSamplingConst a.1 zetaZeroWidth * ((1 + κ) * ∫ x, ‖u x‖ ^ 2))) ≤
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector := by
  refine le_trans (neg_le_neg ?_) (sourceQuadratic_ge_neg_logEnergy u)
  have hL := logSamplingConst_nonneg (σ := zetaZeroWidth) a.2.le
  have h1 : logEnergy u + ∫ x, ‖u x‖ ^ 2 ≤ (1 + κ) * ∫ x, ‖u x‖ ^ 2 := by linarith
  have h2 := mul_le_mul_of_nonneg_left h1 hL
  linarith

/-! ### 3. The ruler -/

/-- **The floor of the Weil form in the logarithmic energy at rate `β`**: one constant `C` with
`W(u, u) ≥ −C (1 + a) e^{2βa} (E(u) + ∫|u|²)` for every smooth source of every aperture `a`. -/
def LogEnergyFloor (β : ℝ) : Prop :=
  ∃ C : ℝ, ∀ (a : SuzukiPositiveAperture) (u : CCMComplexSmoothInteriorSource a),
    -(C * ((1 + a.1) * Real.exp (2 * β * a.1) * (logEnergy u + ∫ x, ‖u x‖ ^ 2))) ≤
      ccmRestrictedWeilSourceQuadratic a u.toCCMFormVector

/-- **Transmitter.** A bound on the width is a floor at that rate. -/
theorem logEnergyFloor_of_zetaZeroWidth_le {β : ℝ} (h : zetaZeroWidth ≤ β) : LogEnergyFloor β := by
  refine ⟨160 * (4 * (2 + 2 * π) * Real.exp (2 * π) * Real.exp (3 * β)), fun a u => ?_⟩
  have ha : 0 < a.1 := a.2
  have hπ := Real.pi_pos
  refine le_trans (neg_le_neg ?_) (sourceQuadratic_ge_neg_logEnergy u)
  have hEN : 0 ≤ logEnergy u + ∫ x, ‖u x‖ ^ 2 :=
    add_nonneg (logEnergy_nonneg _) (integral_nonneg fun _ => sq_nonneg _)
  have hconst : logSamplingConst a.1 zetaZeroWidth ≤
      4 * (2 + 2 * π) * Real.exp (2 * π) * Real.exp (3 * β) *
        ((1 + a.1) * Real.exp (2 * β * a.1)) := by
    unfold logSamplingConst
    have h1 : Real.exp (zetaZeroWidth * (2 * a.1 + 3)) ≤
        Real.exp (3 * β) * Real.exp (2 * β * a.1) := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_right h (by linarith : (0 : ℝ) ≤ 2 * a.1 + 3)])
    have h2 : 2 * a.1 + 2 + 2 * π ≤ (2 + 2 * π) * (1 + a.1) := by nlinarith [mul_pos hπ ha]
    calc 4 * (2 * a.1 + 2 + 2 * π) * Real.exp (2 * π) * Real.exp (zetaZeroWidth * (2 * a.1 + 3))
        ≤ 4 * ((2 + 2 * π) * (1 + a.1)) * Real.exp (2 * π) *
            (Real.exp (3 * β) * Real.exp (2 * β * a.1)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 (by norm_num))
            (Real.exp_pos _).le) h1 (Real.exp_pos _).le (by positivity)
      _ = _ := by ring
  have h3 := mul_le_mul_of_nonneg_right hconst hEN
  linarith

/-- **Receiver.** A floor at rate `β` along the lag family of one bump bounds the width: the
family has constant mass and logarithmic energy linear in the lag. -/
theorem zetaZeroWidth_le_of_logEnergyFloor {β : ℝ} (hβ : 0 ≤ β) (h : LogEnergyFloor β) :
    zetaZeroWidth ≤ β := by
  obtain ⟨C, hC⟩ := h
  obtain ⟨w, hw, -, hgood⟩ := exists_good_width zetaZeroConfig
  obtain ⟨K, hK⟩ := (contDiff_modScaledBump_two w 0).lipschitzWith_of_hasCompactSupport
    (hasCompactSupport_modScaledBump hw 0) (by norm_num)
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = ∫ t, ‖modScaledBump w 0 t‖ ^ 2 := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := by rw [hM]; exact integral_nonneg fun _ => sq_nonneg _
  have hlt : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re < 1 := fun ρ hρ => hρ.2.2
  refine (zetaZeroWidth_le_iff_re_le hβ).mpr fun ρ hρ => le_of_forall_pos_le_add fun ε hε => ?_
  have hσ : 0 ≤ β + ε := by linarith
  suffices hlag : ∃ C' V : ℝ, ∀ v : ℝ, V ≤ v → -(C' * Real.exp ((β + ε) * v)) ≤
      (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
        (twoBump (modScaledBump w 0) v (-1))).re by
    have := (re_le_iff_lag_twoBump_ge_neg_exp zetaZeroConfig temperedConfig_zetaZeroConfig hlt hw
      hgood hσ).mpr hlag ρ hρ
    linarith
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = min (ε / 2) 1 := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδ]; exact lt_min (by linarith) one_pos
  have hδ1 : δ ≤ 1 := by rw [hδ]; exact min_le_right _ _
  have hδε : 2 * δ ≤ ε := by
    have := min_le_left (ε / 2) 1
    rw [← hδ] at this
    linarith
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = (w + 2) * (4 * (K : ℝ) ^ 2 * (2 * w + 4) + 2 * M) *
      Real.exp (β * (2 * w + 2)) := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; positivity
  refine ⟨|C| * (c₀ / δ ^ 2), 2 * w + 1, fun v hv => ?_⟩
  have hv0 : 0 ≤ v := by linarith
  have hv2 : 2 * w < v := by linarith
  -- the difference test as an interior source of aperture `v/2 + w + 1`
  obtain ⟨A, hA1⟩ : ∃ A : SuzukiPositiveAperture, A.1 = v / 2 + w + 1 :=
    ⟨⟨v / 2 + w + 1, by positivity⟩, rfl⟩
  have hts := tsupport_twoBump_modScaledBump_subset hw hv0
  have hsub : tsupport (twoBump (modScaledBump w 0) v (-1)) ⊆ Ioo (-A.1) A.1 := by
    rw [hA1]
    exact hts.trans fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  obtain ⟨u, hu⟩ : ∃ u : CCMComplexSmoothInteriorSource A,
      (u : ℝ → ℂ) = twoBump (modScaledBump w 0) v (-1) :=
    ⟨⟨twoBump (modScaledBump w 0) v (-1),
      contDiff_top_bumpTest (contDiff_top_modScaledBump w 0) v ![1, -1],
      IsCompact.of_isClosed_subset isCompact_Icc (isClosed_tsupport _) hts, hsub⟩, rfl⟩
  have hfloor := hC A u
  rw [ccmRestrictedWeilSource_complexSmooth_eq_zetaWeil u] at hfloor
  have hI : IntervalSource A.1 (u : ℝ → ℂ) := smoothSource_intervalSource u
  rw [hu] at hfloor hI
  -- the family is `2K`-Lipschitz, of mass `2M`
  have hLip : LipschitzWith (2 * K) (twoBump (modScaledBump w 0) v (-1)) := by
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    have h1 := hK.dist_le_mul (s + v / 2) (t + v / 2)
    have h2 := hK.dist_le_mul (s - v / 2) (t - v / 2)
    rw [dist_eq_norm, Real.dist_eq] at h1 h2
    rw [show s + v / 2 - (t + v / 2) = s - t by ring] at h1
    rw [show s - v / 2 - (t - v / 2) = s - t by ring] at h2
    rw [dist_eq_norm, twoBump_apply, twoBump_apply, Real.dist_eq,
      show modScaledBump w 0 (s + v / 2) + -1 * modScaledBump w 0 (s - v / 2) -
        (modScaledBump w 0 (t + v / 2) + -1 * modScaledBump w 0 (t - v / 2)) =
        (modScaledBump w 0 (s + v / 2) - modScaledBump w 0 (t + v / 2)) -
          (modScaledBump w 0 (s - v / 2) - modScaledBump w 0 (t - v / 2)) by ring]
    calc ‖(modScaledBump w 0 (s + v / 2) - modScaledBump w 0 (t + v / 2)) -
          (modScaledBump w 0 (s - v / 2) - modScaledBump w 0 (t - v / 2))‖
        ≤ ‖modScaledBump w 0 (s + v / 2) - modScaledBump w 0 (t + v / 2)‖ +
          ‖modScaledBump w 0 (s - v / 2) - modScaledBump w 0 (t - v / 2)‖ := norm_sub_le _ _
      _ ≤ (K : ℝ) * |s - t| + (K : ℝ) * |s - t| := add_le_add h1 h2
      _ = ((2 * K : NNReal) : ℝ) * |s - t| := by push_cast; ring
  have hE := logEnergy_le_of_lipschitz A.2.le hI hLip
  push_cast at hE
  rw [hA1] at hE
  have hmass := integral_norm_sq_twoBump_modScaledBump_eq hw hv2
  rw [← hM] at hmass
  have hE0 := logEnergy_nonneg (twoBump (modScaledBump w 0) v (-1))
  -- the three factors of the floor
  have hP1 : 1 + A.1 ≤ (w + 2) * (1 + v) := by
    rw [hA1]
    nlinarith [mul_nonneg hw.le hv0]
  have hP2 : Real.exp (2 * β * A.1) = Real.exp (β * (2 * w + 2)) * Real.exp (β * v) := by
    rw [← Real.exp_add, hA1]
    congr 1
    ring
  have hP3 : logEnergy (twoBump (modScaledBump w 0) v (-1)) +
      ∫ x, ‖twoBump (modScaledBump w 0) v (-1) x‖ ^ 2 ≤
      (4 * (K : ℝ) ^ 2 * (2 * w + 4) + 2 * M) * (1 + v) := by
    rw [hmass]
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg (K : ℝ)) hv0) (by linarith : (0 : ℝ) ≤ 2 * w + 3),
      mul_nonneg hM0 hv0]
  have hP30 : 0 ≤ logEnergy (twoBump (modScaledBump w 0) v (-1)) +
      ∫ x, ‖twoBump (modScaledBump w 0) v (-1) x‖ ^ 2 :=
    add_nonneg hE0 (integral_nonneg fun _ => sq_nonneg _)
  -- a square of the lag is paid by `e^{εv}`
  have h1v : 1 + v ≤ Real.exp (δ * v) / δ := by
    rw [le_div_iff₀ hδ0]
    nlinarith [Real.add_one_le_exp (δ * v), mul_nonneg hδ0.le hv0]
  have hexp2 : Real.exp (δ * v) ^ 2 = Real.exp (2 * δ * v) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsq : (1 + v) ^ 2 ≤ Real.exp (ε * v) / δ ^ 2 := by
    have h2 : (1 + v) ^ 2 ≤ (Real.exp (δ * v) / δ) ^ 2 := pow_le_pow_left₀ (by linarith) h1v 2
    rw [div_pow, hexp2] at h2
    exact h2.trans (div_le_div_of_nonneg_right
      (Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hδε hv0])) (by positivity))
  have hX : (1 + A.1) * Real.exp (2 * β * A.1) *
      (logEnergy (twoBump (modScaledBump w 0) v (-1)) +
        ∫ x, ‖twoBump (modScaledBump w 0) v (-1) x‖ ^ 2) ≤
      c₀ / δ ^ 2 * Real.exp ((β + ε) * v) := by
    calc (1 + A.1) * Real.exp (2 * β * A.1) *
          (logEnergy (twoBump (modScaledBump w 0) v (-1)) +
            ∫ x, ‖twoBump (modScaledBump w 0) v (-1) x‖ ^ 2)
        ≤ (w + 2) * (1 + v) * (Real.exp (β * (2 * w + 2)) * Real.exp (β * v)) *
            ((4 * (K : ℝ) ^ 2 * (2 * w + 4) + 2 * M) * (1 + v)) := by
          rw [hP2]
          exact mul_le_mul (mul_le_mul_of_nonneg_right hP1 (by positivity)) hP3 hP30
            (by positivity)
      _ = c₀ * ((1 + v) ^ 2 * Real.exp (β * v)) := by rw [hc₀]; ring
      _ ≤ c₀ * (Real.exp (ε * v) / δ ^ 2 * Real.exp (β * v)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsq (Real.exp_pos _).le) hc₀0
      _ = c₀ / δ ^ 2 * Real.exp ((β + ε) * v) := by
          rw [show (β + ε) * v = ε * v + β * v by ring, Real.exp_add]
          ring
  obtain ⟨X, hXdef⟩ : ∃ X : ℝ, X = (1 + A.1) * Real.exp (2 * β * A.1) *
      (logEnergy (twoBump (modScaledBump w 0) v (-1)) +
        ∫ x, ‖twoBump (modScaledBump w 0) v (-1) x‖ ^ 2) := ⟨_, rfl⟩
  rw [← hXdef] at hfloor hX
  have hX0 : 0 ≤ X := by
    rw [hXdef]
    exact mul_nonneg (mul_nonneg (by linarith [A.2]) (Real.exp_pos _).le) hP30
  have hCX : C * X ≤ |C| * (c₀ / δ ^ 2) * Real.exp ((β + ε) * v) := by
    calc C * X ≤ |C| * X := mul_le_mul_of_nonneg_right (le_abs_self C) hX0
      _ ≤ |C| * (c₀ / δ ^ 2 * Real.exp ((β + ε) * v)) :=
          mul_le_mul_of_nonneg_left hX (abs_nonneg C)
      _ = _ := by ring
  linarith

/-- **The Weil floor in the logarithmic energy is a ruler of the zero width.** For `β ≥ 0`:
`zetaZeroWidth ≤ β` iff `W(u, u) ≥ −C (1 + a) e^{2βa} (E(u) + ∫|u|²)` on all smooth sources. -/
theorem isRuler_logEnergyFloor : IsRuler zetaZeroWidth (Ici 0) LogEnergyFloor :=
  fun _ hβ => ⟨logEnergyFloor_of_zetaZeroWidth_le, zetaZeroWidth_le_of_logEnergyFloor hβ⟩

/-- The reading at the width itself: the rate is attained, with no loss in the exponent. -/
theorem logEnergyFloor_zetaZeroWidth : LogEnergyFloor zetaZeroWidth :=
  logEnergyFloor_of_zetaZeroWidth_le le_rfl

/-- The seed on this ruler: the floor at rate `3/8`, with no hypothesis. -/
theorem logEnergyFloor_three_eighths : LogEnergyFloor (3 / 8) :=
  logEnergyFloor_of_zetaZeroWidth_le zetaZeroWidth_le_three_eighths

/-- **A floor polynomial in the aperture is the critical line.** The Riemann hypothesis holds iff
`W(u, u) ≥ −C (1 + a) (E(u) + ∫|u|²)` for all smooth sources of all apertures. -/
theorem riemannHypothesis_iff_logEnergyFloor_zero : RiemannHypothesis ↔ LogEnergyFloor 0 := by
  rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  exact ⟨fun h => logEnergyFloor_of_zetaZeroWidth_le h.le,
    fun h => le_antisymm (zetaZeroWidth_le_of_logEnergyFloor le_rfl h) zetaZeroWidth_nonneg⟩

#print axioms isRuler_logEnergyFloor
#print axioms sourceQuadratic_ge_neg_logEnergy
#print axioms riemannHypothesis_iff_logEnergyFloor_zero

end

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
