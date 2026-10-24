import GaloisForLFunctions.BiScaleUncertainty.WeilLagAndDeficitEnergyZeroWidthLaw
import GaloisForLFunctions.BiScaleUncertainty.CramerLimitLaw
import GaloisForLFunctions.SquareRootThreshold.AmplificationMultipliesTheZeroWidthExponent
import GaloisForLFunctions.RHTower.WeilLagFunctionGrowthLower
import GaloisForLFunctions.RHTower.WeilLagFunctionSingleBase
import Mathlib.Analysis.Calculus.SmoothSeries

/-!
# Exact endpoint attainment and fourth-power zero-energy limit law for the critical prime deficit

In `WeilLagAndDeficitEnergyZeroWidthLaw` and `TheZeroWidthIsALandauExponent`, the zero width
`zetaZeroWidth` was characterized asymptotically as the infimum of admissible exponential rates
`β > zetaZeroWidth` via Cramér's mean-square band and generalized von Koch, which lose a polynomial
factor `(1 + T)` at the critical abscissa itself.

This module eliminates the endpoint loss and establishes the exact spectral representation,
endpoint attainment, two-prime rational lag characterization, and asymptotic limit law of the
critical prime-deficit system:

1. **Unconditional spectral deficit representation**
   (`spectralFluxState`, `spectralDeficitSum`, `hasDerivAt_spectralFluxState`,
   `spectralDeficitWeight_eq_inv_sq`, `exists_abs_ccmPrimeDeficitIncoming_sub_spectralDeficitSum_le`):
   Weighting the Weil-lag coefficients `lagWeight q = 1 / (ρ_q (1 − ρ_q))` by `1 / ρ_q` defines the
   unconditional state `spectralFluxState t = Σ_q (lagWeight q / ρ_q) e^{t(ρ_q − 1/2)}`, which
   satisfies `(d/dt) spectralFluxState t = weilLagFunction t − spectralFluxState t / 2` everywhere
   on `ℝ` without any hypothesis on the zeros. Comparing this ODE against
   `hasDerivAt_ccmPrimeDeficitFluxState` and using the algebraic cancellation
   `lagWeight q / ρ_q − lagWeight q = 1 / ρ_q²` yields an unconditional explicit formula for the
   incoming prime deficit:
   `|ccmPrimeDeficitIncoming T − Re (Σ_q e^{T(ρ_q − 1/2)} / ρ_q²)| ≤ C₀ (1 + T) e^{−T/2}`
   for all `T ≥ 0`, with an absolutely convergent reciprocal-square zero series.

2. **Slack-free endpoint attainment and two-prime rational lag width laws**
   (`exists_univ_abs_ccmPrimeDeficitIncoming_le_of_zetaZeroWidth_le`,
   `zetaZeroWidth_le_iff_endpoint_equivalences`, `zetaZeroWidth_le_iff_two_primes_exp`,
   `deficitAbsRates_eq_Ici`, `pureDeficitRates_eq_Ici`, `deficitPowerRates_eq_Ici`,
   `criticalDeficitPointwiseRates_eq_Ici`, `coprimeCrossWorkLowerRates_eq_Ici`,
   `riemannHypothesis_iff_bddAbove_ccmPrimeDeficitCriticalEnergy`,
   `riemannHypothesis_iff_bddBelow_ccmPrimeDeficitCoprimeCrossWork`):
   Because `Σ_q 1 / ‖ρ_q‖² < ∞` unconditionally, there exists a single universal constant
   `B_univ > 0` independent of `σ` such that whenever `zetaZeroWidth ≤ σ` (`σ ≥ 0`),
   `|ccmPrimeDeficitIncoming T| ≤ B_univ e^{σ T}`,
   `|ccmLogChebyshevDeficitPrimitive T| ≤ B_univ e^{(1/2 + σ) T}`,
   `ccmPrimeDeficitCriticalEnergy T ≤ B_univ² e^{2σ T}`, and
   `−ccmPrimeDeficitCoprimeCrossWork T ≤ (B_univ² + 49/4) e^{2σ T}` for all `T ≥ 0` with no
   `(1 + T)` factor and no `β > σ` slack. Consequently `deficitAbsRates`, `pureDeficitRates`,
   `criticalDeficitPointwiseRates`, and `coprimeCrossWorkLowerRates` all equal the closed ray
   `Ici zetaZeroWidth` (attaining `zetaZeroWidth` as their minimum), `deficitPowerRates k` equals
   `Ici (k * zetaZeroWidth)`, `RiemannHypothesis` is unconditionally equivalent to boundedness above
   of `ccmPrimeDeficitCriticalEnergy` on `[0, ∞)` and to boundedness below of
   `ccmPrimeDeficitCoprimeCrossWork` on `ℝ`, and for any two distinct primes `p ≠ q` and
   `0 ≤ σ < 1/2`, `zetaZeroWidth ≤ σ` is characterized by one-sided `O(e^{σ L})` growth of
   `weilLagFunctionReal` on `{k log p + l log q ≥ 0 : k, l ∈ ℤ}`.

3. **Exact fourth-power zero-energy limit law under `RiemannHypothesis`**
   (`totalFourthPowerZeroEnergy`, `summable_zetaFourthPowerZeroEnergy`,
   `totalFourthPowerZeroEnergy_pos`, `tendsto_mean_ccmPrimeDeficitCriticalEnergy`,
   `tendsto_mean_ccmPrimeDeficitSignedWorkDensity`,
   `isGLB_asymptoticCriticalEnergySlope_fourthPowerZeroEnergy`):
   The fourth-power zero energy `totalFourthPowerZeroEnergy = Σ_ρ m_ρ² / ‖ρ‖⁴` converges and is
   strictly positive unconditionally (`≤ (2/41) totalZeroEnergy` under RH). Under `RiemannHypothesis`,
   theODE `J'(t) = −J(t)/2` and boundedness on `ℝ` force `spectralDeficitSum t` to be purely real,
   and Parseval's theorem on the distinct critical ordinates yields the exact asymptotic laws
   `(1 / T) ∫_0^T ccmPrimeDeficitCriticalEnergy t dt → Σ_ρ m_ρ² / ‖ρ‖⁴` and
   `(1 / T) ∫_0^T ccmPrimeDeficitSignedWorkDensity t dt → (1 / 2) Σ_ρ m_ρ² / ‖ρ‖⁴` as `T → ∞`.
-/

open MeasureTheory Set Filter Topology Complex
open scoped BigOperators

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open _root_.RHTower GaloisForLFunctions.SquareRootThreshold

noncomputable section
set_option autoImplicit false

local notation "𝒵" => Zeta23.zetaZeroConfig.carrier

/-! ## §1. Unconditional spectral flux state and reciprocal-square deficit series -/

/-- Every copy in `XiZeroCopy` has norm strictly greater than `4`, since `(Im ρ)² > 41 / 2 > 16`. -/
theorem four_lt_norm_xiZeroCopy (q : XiZeroCopy) : 4 < ‖(q.1 : ℂ)‖ := by
  have h1 := xiZeroCopy_fortyOne_div_two_lt_im_sq q
  have h2 : |(q.1 : ℂ).im| ≤ ‖(q.1 : ℂ)‖ := Complex.abs_im_le_norm (q.1 : ℂ)
  have h3 : (q.1 : ℂ).im ^ 2 ≤ ‖(q.1 : ℂ)‖ ^ 2 := by
    rw [← sq_abs ((q.1 : ℂ).im)]
    exact pow_le_pow_left₀ (abs_nonneg _) h2 2
  nlinarith [norm_nonneg (q.1 : ℂ)]

/-- Every reflected copy `1 − ρ` in `XiZeroCopy` has norm strictly greater than `4`. -/
theorem four_lt_norm_one_sub_xiZeroCopy (q : XiZeroCopy) : 4 < ‖1 - (q.1 : ℂ)‖ := by
  simpa only [xiZeroCopy_reflect_val] using four_lt_norm_xiZeroCopy (xiZeroCopyReflectEquiv q)

/-- For every `q : XiZeroCopy`, `1 / ‖q.1‖² ≤ 2 ‖lagWeight q‖`, because `‖1 − ρ‖ ≤ 1 + ‖ρ‖ ≤ 2 ‖ρ‖`. -/
theorem one_div_norm_sq_le_two_mul_norm_lagWeight (q : XiZeroCopy) :
    1 / ‖(q.1 : ℂ)‖ ^ 2 ≤ 2 * ‖lagWeight q‖ := by
  have h4 := four_lt_norm_xiZeroCopy q
  have h4' := four_lt_norm_one_sub_xiZeroCopy q
  have hpos : 0 < ‖(q.1 : ℂ)‖ := by linarith
  have hpos' : 0 < ‖1 - (q.1 : ℂ)‖ := by linarith
  have h1sub : ‖1 - (q.1 : ℂ)‖ ≤ 2 * ‖(q.1 : ℂ)‖ := by
    calc ‖1 - (q.1 : ℂ)‖ ≤ ‖(1 : ℂ)‖ + ‖(q.1 : ℂ)‖ := norm_sub_le _ _
      _ = 1 + ‖(q.1 : ℂ)‖ := by rw [norm_one]
      _ ≤ 2 * ‖(q.1 : ℂ)‖ := by linarith
  rw [lagWeight, norm_div, norm_one, norm_mul]
  rw [div_le_iff₀ (sq_pos_of_pos hpos), show 2 * (1 / (‖(q.1 : ℂ)‖ * ‖1 - (q.1 : ℂ)‖)) *
      ‖(q.1 : ℂ)‖ ^ 2 = (2 * ‖(q.1 : ℂ)‖) / ‖1 - (q.1 : ℂ)‖ * ‖(q.1 : ℂ)‖ / ‖(q.1 : ℂ)‖ by ring]
  rw [mul_div_cancel_right₀ _ hpos.ne', one_le_div hpos']
  exact h1sub

/-- Unconditional summability of `1 / ‖q.1‖²` over `XiZeroCopy`. -/
theorem summable_inv_norm_sq_xiZeroCopy : Summable fun q : XiZeroCopy => 1 / ‖(q.1 : ℂ)‖ ^ 2 :=
  Summable.of_nonneg_of_le (fun _ => by positivity)
    one_div_norm_sq_le_two_mul_norm_lagWeight (summable_norm_lagWeight.mul_left 2)

/-- Unconditional spectral flux weight `lagWeight q / ρ_q = 1 / (ρ_q² (1 − ρ_q))`. -/
def spectralFluxWeight (q : XiZeroCopy) : ℂ := lagWeight q / (q.1 : ℂ)

/-- Unconditional spectral deficit weight `spectralFluxWeight q − lagWeight q`. -/
def spectralDeficitWeight (q : XiZeroCopy) : ℂ := spectralFluxWeight q - lagWeight q

/-- Algebraic cancellation of the `1 − ρ_q` factor:
`spectralDeficitWeight q = lagWeight q / ρ_q − lagWeight q = 1 / ρ_q²`. -/
theorem spectralDeficitWeight_eq_inv_sq (q : XiZeroCopy) :
    spectralDeficitWeight q = 1 / (q.1 : ℂ) ^ 2 := by
  unfold spectralDeficitWeight spectralFluxWeight lagWeight
  have h0 : (q.1 : ℂ) ≠ 0 := xiZeroCopy_ne_zero q
  have h1 : 1 - (q.1 : ℂ) ≠ 0 := sub_ne_zero.mpr (Ne.symm (xiZeroCopy_ne_one q))
  field_simp

theorem norm_spectralFluxWeight_le (q : XiZeroCopy) :
    ‖spectralFluxWeight q‖ ≤ ‖lagWeight q‖ / 4 := by
  unfold spectralFluxWeight
  rw [norm_div]
  have h4 := four_lt_norm_xiZeroCopy q
  exact div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num) h4.le

theorem summable_norm_spectralFluxWeight : Summable fun q : XiZeroCopy => ‖spectralFluxWeight q‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun q => (norm_spectralFluxWeight_le q).trans (by linarith [norm_nonneg (lagWeight q)]))
    summable_norm_lagWeight

theorem summable_norm_spectralDeficitWeight :
    Summable fun q : XiZeroCopy => ‖spectralDeficitWeight q‖ := by
  refine Summable.congr summable_inv_norm_sq_xiZeroCopy fun q => ?_
  rw [spectralDeficitWeight_eq_inv_sq, norm_div, norm_one, norm_pow]

/-- The unconditional spectral flux state `Σ_q (lagWeight q / ρ_q) e^{t(ρ_q − 1/2)}`. -/
def spectralFluxState (t : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, spectralFluxWeight q * Complex.exp ((t : ℂ) * ((q.1 : ℂ) - 1 / 2))

/-- The unconditional reciprocal-square zero series `Σ_q e^{t(ρ_q − 1/2)} / ρ_q²`. -/
def spectralDeficitSum (t : ℝ) : ℂ :=
  ∑' q : XiZeroCopy, (1 / (q.1 : ℂ) ^ 2) * Complex.exp ((t : ℂ) * ((q.1 : ℂ) - 1 / 2))

/-- Total unconditional `ℓ¹` weight `Σ_q 1 / ‖q.1‖²` of the reciprocal-square zero series. -/
def reciprocalSquareWeightTotal : ℝ := ∑' q : XiZeroCopy, 1 / ‖(q.1 : ℂ)‖ ^ 2

theorem reciprocalSquareWeightTotal_nonneg : 0 ≤ reciprocalSquareWeightTotal :=
  tsum_nonneg fun _ => by positivity

private theorem norm_exp_strip_le (t : ℝ) (q : XiZeroCopy) :
    ‖Complex.exp ((t : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ ≤ Real.exp (|t| / 2) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  have hre : ((t : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = t * ((q.1 : ℂ).re - 1 / 2) := by
    simp [Complex.mul_re]
  rw [hre]
  have hb : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := abs_le.mpr ⟨by linarith, by linarith⟩
  calc t * ((q.1 : ℂ).re - 1 / 2) ≤ |t * ((q.1 : ℂ).re - 1 / 2)| := le_abs_self _
    _ = |t| * |(q.1 : ℂ).re - 1 / 2| := abs_mul _ _
    _ ≤ |t| * (1 / 2) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
    _ = |t| / 2 := by ring

theorem summable_spectralFluxState_term (t : ℝ) :
    Summable fun q : XiZeroCopy =>
      spectralFluxWeight q * Complex.exp ((t : ℂ) * ((q.1 : ℂ) - 1 / 2)) :=
  Summable.of_norm_bounded
    (g := fun q => ‖spectralFluxWeight q‖ * Real.exp (|t| / 2))
    (summable_norm_spectralFluxWeight.mul_right _)
    fun q => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_exp_strip_le t q) (norm_nonneg _)

theorem summable_spectralDeficitSum_term (t : ℝ) :
    Summable fun q : XiZeroCopy =>
      (1 / (q.1 : ℂ) ^ 2) * Complex.exp ((t : ℂ) * ((q.1 : ℂ) - 1 / 2)) :=
  Summable.of_norm_bounded
    (g := fun q => (1 / ‖(q.1 : ℂ)‖ ^ 2) * Real.exp (|t| / 2))
    (summable_inv_norm_sq_xiZeroCopy.mul_right _)
    fun q => by
      rw [norm_mul, norm_div, norm_one, norm_pow]
      exact mul_le_mul_of_nonneg_left (norm_exp_strip_le t q) (by positivity)

/-- `spectralDeficitSum t = spectralFluxState t − weilLagFunction t` for all `t ∈ ℝ`. -/
theorem spectralDeficitSum_eq_sub (t : ℝ) :
    spectralDeficitSum t = spectralFluxState t - weilLagFunction t := by
  rw [spectralFluxState, weilLagFunction_eq_tsum_lagWeight,
    ← (summable_spectralFluxState_term t).tsum_sub (summable_lagWeight_mul_exp t),
    spectralDeficitSum]
  refine tsum_congr fun q => ?_
  rw [← sub_mul, ← spectralDeficitWeight, spectralDeficitWeight_eq_inv_sq]

/-- Real-part identity `(spectralDeficitSum t).re = (spectralFluxState t).re − weilLagFunctionReal t`. -/
theorem spectralDeficitSum_re_eq (t : ℝ) :
    (spectralDeficitSum t).re = (spectralFluxState t).re - weilLagFunctionReal t := by
  rw [spectralDeficitSum_eq_sub, Complex.sub_re, weilLagFunctionReal]

private theorem spectralFluxWeight_mul_pole (q : XiZeroCopy) :
    spectralFluxWeight q * ((q.1 : ℂ) - 1 / 2) = lagWeight q - spectralFluxWeight q / 2 := by
  have h : spectralFluxWeight q * (q.1 : ℂ) = lagWeight q :=
    div_mul_cancel₀ _ (xiZeroCopy_ne_zero q)
  linear_combination h

private theorem hasDerivAt_spectralFluxTerm (q : XiZeroCopy) (y : ℝ) :
    HasDerivAt (fun z : ℝ => spectralFluxWeight q * Complex.exp ((z : ℂ) * ((q.1 : ℂ) - 1 / 2)))
      ((lagWeight q - spectralFluxWeight q / 2) *
        Complex.exp ((y : ℂ) * ((q.1 : ℂ) - 1 / 2))) y := by
  have h1 : HasDerivAt (fun z : ℝ => (z : ℂ) * ((q.1 : ℂ) - 1 / 2))
      ((q.1 : ℂ) - 1 / 2) y := by
    simpa only [one_mul] using (Complex.hasDerivAt_ofReal y).mul_const ((q.1 : ℂ) - 1 / 2)
  have h2 := (h1.cexp).const_mul (spectralFluxWeight q)
  refine h2.congr_deriv ?_
  linear_combination (spectralFluxWeight_mul_pole q) *
    Complex.exp ((y : ℂ) * ((q.1 : ℂ) - 1 / 2))

/-- **Unconditional differential equation for `spectralFluxState`.** Without any hypothesis on the
zeros of `ζ`, `(d/dt) spectralFluxState t = weilLagFunction t − spectralFluxState t / 2` for every
`t ∈ ℝ`. -/
theorem hasDerivAt_spectralFluxState (t : ℝ) :
    HasDerivAt spectralFluxState (weilLagFunction t - spectralFluxState t / 2) t := by
  set U : Set ℝ := Ioo (t - 1) (t + 1)
  have htU : t ∈ U := ⟨by linarith, by linarith⟩
  have hu : Summable fun q : XiZeroCopy =>
      2 * Real.exp ((|t| + 1) / 2) * ‖lagWeight q‖ :=
    summable_norm_lagWeight.mul_left _
  have hd := hasDerivAt_tsum_of_isPreconnected hu isOpen_Ioo isPreconnected_Ioo
    (fun q y _ => hasDerivAt_spectralFluxTerm q y)
    (fun q y hy => by
      rw [norm_mul]
      have hy_abs : |y| ≤ |t| + 1 := by
        rw [abs_le]
        have ht_abs := le_abs_self t
        have hnt_abs := neg_le_abs t
        exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
      have hexp : ‖Complex.exp ((y : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ ≤
          Real.exp ((|t| + 1) / 2) :=
        (norm_exp_strip_le y q).trans (Real.exp_le_exp.mpr (by linarith))
      have hcoeff : ‖lagWeight q - spectralFluxWeight q / 2‖ ≤ 2 * ‖lagWeight q‖ := by
        have hfw := norm_spectralFluxWeight_le q
        calc ‖lagWeight q - spectralFluxWeight q / 2‖
            ≤ ‖lagWeight q‖ + ‖spectralFluxWeight q / 2‖ := norm_sub_le _ _
          _ = ‖lagWeight q‖ + ‖spectralFluxWeight q‖ / 2 := by
              rw [norm_div, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
          _ ≤ 2 * ‖lagWeight q‖ := by linarith [norm_nonneg (lagWeight q)]
      calc ‖lagWeight q - spectralFluxWeight q / 2‖ *
            ‖Complex.exp ((y : ℂ) * ((q.1 : ℂ) - 1 / 2))‖
          ≤ (2 * ‖lagWeight q‖) * Real.exp ((|t| + 1) / 2) :=
            mul_le_mul hcoeff hexp (norm_nonneg _) (by positivity)
        _ = 2 * Real.exp ((|t| + 1) / 2) * ‖lagWeight q‖ := by ring)
    htU (summable_spectralFluxState_term t) htU
  refine hd.congr_deriv ?_
  rw [weilLagFunction_eq_tsum_lagWeight, spectralFluxState, ← tsum_div_const,
    ← (summable_lagWeight_mul_exp t).tsum_sub
      ((summable_spectralFluxState_term t).div_const 2)]
  refine tsum_congr fun q => ?_
  ring

/-- Real-part ODE: `(d/dt) (spectralFluxState t).re = weilLagFunctionReal t − (spectralFluxState t).re / 2`. -/
theorem hasDerivAt_spectralFluxState_re (t : ℝ) :
    HasDerivAt (fun x => (spectralFluxState x).re)
      (weilLagFunctionReal t - (spectralFluxState t).re / 2) t := by
  simpa only [Complex.reCLM_apply, Function.comp_def, Complex.sub_re,
    Complex.div_ofNat_re, weilLagFunctionReal] using
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_spectralFluxState t)

/-- Continuity of `spectralFluxState` on `ℝ`. -/
theorem continuous_spectralFluxState : Continuous spectralFluxState :=
  Differentiable.continuous fun t => (hasDerivAt_spectralFluxState t).differentiableAt

/-- Continuity of `spectralDeficitSum` on `ℝ`. -/
theorem continuous_spectralDeficitSum : Continuous spectralDeficitSum := by
  rw [funext spectralDeficitSum_eq_sub]
  exact continuous_spectralFluxState.sub continuous_weilLagFunction_unconditional

/-- **Unconditional explicit formula for `ccmPrimeDeficitIncoming`.** There exists an explicit
universal constant `C₀ > 0` such that for all `T ≥ 0`,
`|ccmPrimeDeficitIncoming T − (spectralDeficitSum T).re| ≤ C₀ * (1 + T) * Real.exp (-T / 2)`. -/
theorem exists_abs_ccmPrimeDeficitIncoming_sub_spectralDeficitSum_le :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ T : ℝ, 0 ≤ T →
      |ccmPrimeDeficitIncoming T - (spectralDeficitSum T).re| ≤
        C₀ * (1 + T) * Real.exp (-T / 2) := by
  let R : ℝ → ℝ := fun t => Real.exp (t / 2) *
    (ccmPrimeDeficitFluxState t - (spectralFluxState t).re)
  let C_arch : ℝ := |Real.log (2 * Real.pi)| + 1
  have hC_arch : 0 < C_arch := by dsimp [C_arch]; positivity
  have hd (t : ℝ) : HasDerivAt R
      (Real.exp (t / 2) * (ccmPrimeDeficitOutgoing t - weilLagFunctionReal t)) t := by
    convert! (((hasDerivAt_id t).div_const 2).exp).mul
      ((hasDerivAt_ccmPrimeDeficitFluxState t).sub (hasDerivAt_spectralFluxState_re t)) using 1
    dsimp only [ccmPrimeDeficitOutgoing, id_eq, Pi.sub_apply]
    ring
  have hbd (t : ℝ) (ht : 1 ≤ t) :
      ‖Real.exp (t / 2) * (ccmPrimeDeficitOutgoing t - weilLagFunctionReal t)‖ ≤ C_arch := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    have h := mul_le_mul_of_nonneg_left
      (abs_ccmPrimeDeficitOutgoing_sub_weilLag (by linarith : 0 < t))
      (Real.exp_pos (t / 2)).le
    have he : Real.exp (t / 2) * Real.exp (-t / 2) = 1 := by
      rw [← Real.exp_add, show t / 2 + -t / 2 = 0 by ring, Real.exp_zero]
    simpa only [← mul_assoc, he, one_mul] using h
  have hR (T : ℝ) (hT : 1 ≤ T) : |R T| ≤ |R 1| + C_arch * T := by
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t (_ht : t ∈ Icc (1 : ℝ) T) => (hd t).hasDerivWithinAt)
      (fun t ht => hbd t ht.1) (convex_Icc 1 T)
      (show (1 : ℝ) ∈ Icc 1 T from ⟨le_rfl, hT⟩)
      (show T ∈ Icc 1 T from ⟨hT, le_rfl⟩)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith : 0 ≤ T - 1)] at h
    have ha := abs_add_le (R T - R 1) (R 1)
    rw [sub_add_cancel] at ha
    nlinarith
  have hcont_err : Continuous fun t : ℝ =>
      |ccmPrimeDeficitIncoming t - (spectralDeficitSum t).re| :=
    (continuous_ccmPrimeDeficitIncoming.sub
      (Complex.continuous_re.comp continuous_spectralDeficitSum)).abs
  obtain ⟨t_max, -, ht_max⟩ := isCompact_Icc.exists_isMaxOn
    (nonempty_Icc.mpr (zero_le_one' ℝ)) hcont_err.continuousOn
  set M₀ := |ccmPrimeDeficitIncoming t_max - (spectralDeficitSum t_max).re| * Real.exp (1 / 2)
  have hM₀ : 0 ≤ M₀ := by positivity
  refine ⟨M₀ + |R 1| + C_arch + 1, by positivity, fun T hT => ?_⟩
  rcases le_or_gt T 1 with hT1 | hT1
  · have hle : |ccmPrimeDeficitIncoming T - (spectralDeficitSum T).re| ≤
        |ccmPrimeDeficitIncoming t_max - (spectralDeficitSum t_max).re| :=
      ht_max ⟨hT, hT1⟩
    have hexp : 1 ≤ Real.exp (1 / 2) * Real.exp (-T / 2) := by
      rw [← Real.exp_add]
      exact Real.one_le_exp (by linarith)
    have h1 : |ccmPrimeDeficitIncoming T - (spectralDeficitSum T).re| ≤
        M₀ * Real.exp (-T / 2) := by
      calc |ccmPrimeDeficitIncoming T - (spectralDeficitSum T).re|
          ≤ |ccmPrimeDeficitIncoming t_max - (spectralDeficitSum t_max).re| * 1 := by
            rw [mul_one]; exact hle
        _ ≤ |ccmPrimeDeficitIncoming t_max - (spectralDeficitSum t_max).re| *
              (Real.exp (1 / 2) * Real.exp (-T / 2)) :=
            mul_le_mul_of_nonneg_left hexp (abs_nonneg _)
        _ = M₀ * Real.exp (-T / 2) := by simp only [M₀]; ring
    calc |ccmPrimeDeficitIncoming T - (spectralDeficitSum T).re|
        ≤ M₀ * Real.exp (-T / 2) := h1
      _ ≤ (M₀ + |R 1| + C_arch + 1) * (1 + T) * Real.exp (-T / 2) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos (-T / 2)).le
          nlinarith [abs_nonneg (R 1)]
  · have hdiff : ccmPrimeDeficitIncoming T - (spectralDeficitSum T).re =
        (ccmPrimeDeficitFluxState T - (spectralFluxState T).re) -
          (ccmPrimeDeficitOutgoing T - weilLagFunctionReal T) := by
      rw [spectralDeficitSum_re_eq]
      dsimp only [ccmPrimeDeficitOutgoing]
      ring
    have hstate : |ccmPrimeDeficitFluxState T - (spectralFluxState T).re| ≤
        (|R 1| + C_arch * T) * Real.exp (-T / 2) := by
      have he : ccmPrimeDeficitFluxState T - (spectralFluxState T).re =
          R T * Real.exp (-T / 2) := by
        dsimp [R]
        rw [mul_right_comm, ← Real.exp_add, show T / 2 + -T / 2 = 0 by ring,
          Real.exp_zero, one_mul]
      rw [he, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (hR T hT1.le) (Real.exp_pos _).le
    have hout : |ccmPrimeDeficitOutgoing T - weilLagFunctionReal T| ≤
        C_arch * Real.exp (-T / 2) := by
      rw [mul_comm]
      exact abs_ccmPrimeDeficitOutgoing_sub_weilLag (by linarith)
    rw [hdiff]
    calc |(ccmPrimeDeficitFluxState T - (spectralFluxState T).re) -
            (ccmPrimeDeficitOutgoing T - weilLagFunctionReal T)|
        ≤ |ccmPrimeDeficitFluxState T - (spectralFluxState T).re| +
            |ccmPrimeDeficitOutgoing T - weilLagFunctionReal T| := abs_sub _ _
      _ ≤ (|R 1| + C_arch * T) * Real.exp (-T / 2) + C_arch * Real.exp (-T / 2) :=
          add_le_add hstate hout
      _ ≤ (M₀ + |R 1| + C_arch + 1) * (1 + T) * Real.exp (-T / 2) := by
          rw [← add_mul]
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos (-T / 2)).le
          nlinarith [hM₀, abs_nonneg (R 1)]

/-! ## §2. Universal endpoint bounds, closed-ray rate sets, and two-prime rational lags -/

/-- `zetaZeroWidth ≤ σ` (`σ ≥ 0`) iff every copy in `XiZeroCopy` satisfies `|(q.1 : ℂ).re − 1/2| ≤ σ`. -/
theorem zetaZeroWidth_le_iff_xiZeroCopy_abs_re_sub_half_le {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ σ := by
  rw [zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ]
  constructor
  · intro h q
    have h1 : (q.1 : ℂ).re ≤ 1 / 2 + σ := h (q.1 : ℂ) (xi_xiZeroCopy_eq_zero q)
    have h2 : ((xiZeroCopyReflectEquiv q).1 : ℂ).re ≤ 1 / 2 + σ :=
      h _ (xi_xiZeroCopy_eq_zero (xiZeroCopyReflectEquiv q))
    rw [xiZeroCopy_reflect_val, Complex.sub_re, Complex.one_re] at h2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro h ρ hρ
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
    linarith [(abs_le.mp (h q)).2]

/-- **Universal endpoint bound on `spectralDeficitSum`.** Whenever `zetaZeroWidth ≤ σ` (`σ ≥ 0`),
`‖spectralDeficitSum t‖ ≤ reciprocalSquareWeightTotal * e^{σ |t|}` for all `t ∈ ℝ`. -/
theorem norm_spectralDeficitSum_le_of_zetaZeroWidth_le {σ : ℝ} (hσ : 0 ≤ σ)
    (hw : zetaZeroWidth ≤ σ) (t : ℝ) :
    ‖spectralDeficitSum t‖ ≤ reciprocalSquareWeightTotal * Real.exp (σ * |t|) := by
  have hstrip := (zetaZeroWidth_le_iff_xiZeroCopy_abs_re_sub_half_le hσ).mp hw
  have hterm : ∀ q : XiZeroCopy,
      ‖(1 / (q.1 : ℂ) ^ 2) * Complex.exp ((t : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ ≤
        (1 / ‖(q.1 : ℂ)‖ ^ 2) * Real.exp (σ * |t|) := fun q => by
    rw [norm_mul, norm_div, norm_one, norm_pow, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have hre : ((t : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = t * ((q.1 : ℂ).re - 1 / 2) := by
      simp [Complex.mul_re]
    rw [hre]
    calc t * ((q.1 : ℂ).re - 1 / 2) ≤ |t * ((q.1 : ℂ).re - 1 / 2)| := le_abs_self _
      _ = |t| * |(q.1 : ℂ).re - 1 / 2| := abs_mul _ _
      _ ≤ |t| * σ := mul_le_mul_of_nonneg_left (hstrip q) (abs_nonneg _)
      _ = σ * |t| := mul_comm _ _
  have hs : Summable fun q : XiZeroCopy =>
      ‖(1 / (q.1 : ℂ) ^ 2) * Complex.exp ((t : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ :=
    (summable_spectralDeficitSum_term t).norm
  calc ‖spectralDeficitSum t‖
      ≤ ∑' q : XiZeroCopy,
          ‖(1 / (q.1 : ℂ) ^ 2) * Complex.exp ((t : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' q : XiZeroCopy, (1 / ‖(q.1 : ℂ)‖ ^ 2) * Real.exp (σ * |t|) :=
        hs.tsum_le_tsum hterm (summable_inv_norm_sq_xiZeroCopy.mul_right _)
    _ = reciprocalSquareWeightTotal * Real.exp (σ * |t|) := by
        rw [tsum_mul_right]; rfl

/-- **Universal endpoint bound on `weilLagFunctionReal`.** Whenever `zetaZeroWidth ≤ σ` (`σ ≥ 0`),
`|weilLagFunctionReal L| ≤ lagWeightTotal * e^{σ |L|}` for all `L ∈ ℝ`, with constant
`lagWeightTotal` independent of `σ`. -/
theorem abs_weilLagFunctionReal_le_of_zetaZeroWidth_le {σ : ℝ} (hσ : 0 ≤ σ)
    (hw : zetaZeroWidth ≤ σ) (L : ℝ) :
    |weilLagFunctionReal L| ≤ lagWeightTotal * Real.exp (σ * |L|) := by
  have hstrip := (zetaZeroWidth_le_iff_xiZeroCopy_abs_re_sub_half_le hσ).mp hw
  have h1 : |weilLagFunctionReal L| = ‖weilLagFunction L‖ := by
    rw [weilLagFunction_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
  rw [h1, weilLagFunction_eq_tsum_lagWeight]
  have hs : Summable fun q : XiZeroCopy =>
      ‖lagWeight q * Complex.exp ((L : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ :=
    (summable_lagWeight_mul_exp L).norm
  have hterm : ∀ q : XiZeroCopy,
      ‖lagWeight q * Complex.exp ((L : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ ≤
        ‖lagWeight q‖ * Real.exp (σ * |L|) := fun q => by
    rw [norm_mul, Complex.norm_exp]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
    have hre : ((L : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = L * ((q.1 : ℂ).re - 1 / 2) := by
      simp [Complex.mul_re]
    rw [hre]
    calc L * ((q.1 : ℂ).re - 1 / 2) ≤ |L * ((q.1 : ℂ).re - 1 / 2)| := le_abs_self _
      _ = |L| * |(q.1 : ℂ).re - 1 / 2| := abs_mul _ _
      _ ≤ |L| * σ := mul_le_mul_of_nonneg_left (hstrip q) (abs_nonneg _)
      _ = σ * |L| := mul_comm _ _
  calc ‖∑' q : XiZeroCopy, lagWeight q * Complex.exp ((L : ℂ) * ((q.1 : ℂ) - 1 / 2))‖
      ≤ ∑' q : XiZeroCopy, ‖lagWeight q * Complex.exp ((L : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ :=
        norm_tsum_le_tsum_norm hs
    _ ≤ ∑' q : XiZeroCopy, ‖lagWeight q‖ * Real.exp (σ * |L|) :=
        hs.tsum_le_tsum hterm (summable_norm_lagWeight.mul_right _)
    _ = lagWeightTotal * Real.exp (σ * |L|) := by
        rw [tsum_mul_right]; rfl

private theorem one_add_mul_exp_neg_half_le (T : ℝ) :
    (1 + T) * Real.exp (-T / 2) ≤ 2 := by
  have h1 : 1 + T / 2 ≤ Real.exp (T / 2) := by linarith [Real.add_one_le_exp (T / 2)]
  have h2 : 1 + T ≤ 2 * Real.exp (T / 2) := by linarith
  have h3 := mul_le_mul_of_nonneg_right h2 (Real.exp_pos (-T / 2)).le
  rwa [mul_assoc, ← Real.exp_add, show T / 2 + -T / 2 = 0 by ring, Real.exp_zero, mul_one] at h3

/-- **Universal `σ`-independent endpoint bound for `ccmPrimeDeficitIncoming`.** There exists a
single unconditional constant `B > 0`, independent of `σ`, such that whenever `zetaZeroWidth ≤ σ`
(`σ ≥ 0`), `|ccmPrimeDeficitIncoming T| ≤ B * e^{σ T}` for all `T ≥ 0`. -/
theorem exists_univ_abs_ccmPrimeDeficitIncoming_le_of_zetaZeroWidth_le :
    ∃ B : ℝ, 0 < B ∧ ∀ {σ : ℝ}, 0 ≤ σ → zetaZeroWidth ≤ σ →
      ∀ T : ℝ, 0 ≤ T → |ccmPrimeDeficitIncoming T| ≤ B * Real.exp (σ * T) := by
  obtain ⟨C₀, hC₀, herr⟩ := exists_abs_ccmPrimeDeficitIncoming_sub_spectralDeficitSum_le
  refine ⟨reciprocalSquareWeightTotal + 2 * C₀ + 1,
    by linarith [reciprocalSquareWeightTotal_nonneg, hC₀], fun {σ} hσ hw T hT => ?_⟩
  have hsum : |(spectralDeficitSum T).re| ≤ reciprocalSquareWeightTotal * Real.exp (σ * T) := by
    calc |(spectralDeficitSum T).re| ≤ ‖spectralDeficitSum T‖ := Complex.abs_re_le_norm _
      _ ≤ reciprocalSquareWeightTotal * Real.exp (σ * |T|) :=
          norm_spectralDeficitSum_le_of_zetaZeroWidth_le hσ hw T
      _ = reciprocalSquareWeightTotal * Real.exp (σ * T) := by rw [abs_of_nonneg hT]
  have he : |ccmPrimeDeficitIncoming T - (spectralDeficitSum T).re| ≤ 2 * C₀ := by
    calc |ccmPrimeDeficitIncoming T - (spectralDeficitSum T).re|
        ≤ C₀ * ((1 + T) * Real.exp (-T / 2)) := by
          simpa only [mul_assoc] using herr T hT
      _ ≤ C₀ * 2 := mul_le_mul_of_nonneg_left (one_add_mul_exp_neg_half_le T) hC₀.le
      _ = 2 * C₀ := by ring
  have hexp1 : 1 ≤ Real.exp (σ * T) := Real.one_le_exp (mul_nonneg hσ hT)
  have htri : |ccmPrimeDeficitIncoming T| ≤
      |ccmPrimeDeficitIncoming T - (spectralDeficitSum T).re| + |(spectralDeficitSum T).re| := by
    simpa only [sub_add_cancel] using
      abs_add_le (ccmPrimeDeficitIncoming T - (spectralDeficitSum T).re) (spectralDeficitSum T).re
  nlinarith

/-- **Unconditional exact-width bound for `ccmPrimeDeficitIncoming`, `ccmLogChebyshevDeficitPrimitive`,
and `ccmPrimeDeficitCriticalEnergy` at `zetaZeroWidth` itself.** Without any `β > zetaZeroWidth`
slack and without any `(1 + T)` factor, there exists `B > 0` such that for all `T ≥ 0`:
* `|ccmPrimeDeficitIncoming T| ≤ B * e^{zetaZeroWidth * T}`,
* `|ccmLogChebyshevDeficitPrimitive T| ≤ B * e^{(1/2 + zetaZeroWidth) * T}`,
* `ccmPrimeDeficitCriticalEnergy T ≤ B ^ 2 * e^{2 * zetaZeroWidth * T}`. -/
theorem exists_endpoint_bounds_at_zetaZeroWidth :
    ∃ B : ℝ, 0 < B ∧ ∀ T : ℝ, 0 ≤ T →
      |ccmPrimeDeficitIncoming T| ≤ B * Real.exp (zetaZeroWidth * T) ∧
      |ccmLogChebyshevDeficitPrimitive T| ≤ B * Real.exp ((1 / 2 + zetaZeroWidth) * T) ∧
      ccmPrimeDeficitCriticalEnergy T ≤ B ^ 2 * Real.exp (2 * zetaZeroWidth * T) := by
  obtain ⟨B, hB, huniv⟩ := exists_univ_abs_ccmPrimeDeficitIncoming_le_of_zetaZeroWidth_le
  refine ⟨B, hB, fun T hT => ?_⟩
  have hin := huniv zetaZeroWidth_nonneg le_rfl T hT
  have hprim : |ccmLogChebyshevDeficitPrimitive T| ≤
      B * Real.exp ((1 / 2 + zetaZeroWidth) * T) := by
    have hid : ccmLogChebyshevDeficitPrimitive T =
        Real.exp (T / 2) * ccmPrimeDeficitIncoming T := by
      unfold ccmPrimeDeficitIncoming
      rw [← mul_assoc, ← Real.exp_add, show T / 2 + -T / 2 = 0 by ring, Real.exp_zero, one_mul]
    rw [hid, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (T / 2) * |ccmPrimeDeficitIncoming T|
        ≤ Real.exp (T / 2) * (B * Real.exp (zetaZeroWidth * T)) :=
          mul_le_mul_of_nonneg_left hin (Real.exp_pos _).le
      _ = B * (Real.exp (T / 2) * Real.exp (zetaZeroWidth * T)) := by ring
      _ = B * Real.exp ((1 / 2 + zetaZeroWidth) * T) := by
          rw [← Real.exp_add]; congr 2; ring
  have hcrit : ccmPrimeDeficitCriticalEnergy T ≤
      B ^ 2 * Real.exp (2 * zetaZeroWidth * T) := by
    rw [← ccmPrimeDeficitIncoming_sq, ← sq_abs]
    calc |ccmPrimeDeficitIncoming T| ^ 2
        ≤ (B * Real.exp (zetaZeroWidth * T)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) hin 2
      _ = B ^ 2 * (Real.exp (zetaZeroWidth * T) * Real.exp (zetaZeroWidth * T)) := by ring
      _ = B ^ 2 * Real.exp (2 * zetaZeroWidth * T) := by
          rw [← Real.exp_add]; congr 2; ring
  exact ⟨hin, hprim, hcrit⟩

/-- Pointwise rate `CriticalDeficitPointwiseRate σ` holds at every `σ ≥ zetaZeroWidth`. -/
theorem criticalDeficitPointwiseRate_of_zetaZeroWidth_le {σ : ℝ} (hw : zetaZeroWidth ≤ σ) :
    CriticalDeficitPointwiseRate σ := by
  have hσ : 0 ≤ σ := zetaZeroWidth_nonneg.trans hw
  obtain ⟨B, hB, huniv⟩ := exists_univ_abs_ccmPrimeDeficitIncoming_le_of_zetaZeroWidth_le
  refine ⟨B ^ 2, by positivity, fun T hT => ?_⟩
  have hin := huniv hσ hw T hT
  rw [← ccmPrimeDeficitIncoming_sq, ← sq_abs]
  calc |ccmPrimeDeficitIncoming T| ^ 2
      ≤ (B * Real.exp (σ * T)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hin 2
    _ = B ^ 2 * (Real.exp (σ * T) * Real.exp (σ * T)) := by ring
    _ = B ^ 2 * Real.exp (2 * σ * T) := by rw [← Real.exp_add]; congr 2; ring

/-- Coprime cross-work rate `CoprimeCrossWorkLowerRate σ` holds at every `σ ≥ zetaZeroWidth`. -/
theorem coprimeCrossWorkLowerRate_of_zetaZeroWidth_le {σ : ℝ} (hw : zetaZeroWidth ≤ σ) :
    CoprimeCrossWorkLowerRate σ :=
  (criticalDeficitPointwiseRate_iff_coprimeCrossWorkLowerRate
    (zetaZeroWidth_nonneg.trans hw)).mp (criticalDeficitPointwiseRate_of_zetaZeroWidth_le hw)

/-- **Slack-free zero-width equivalence for `CriticalDeficitPointwiseRate` (all `σ ≥ 0`).** -/
theorem zetaZeroWidth_le_iff_criticalDeficitPointwiseRate {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ CriticalDeficitPointwiseRate σ := by
  constructor
  · exact criticalDeficitPointwiseRate_of_zetaZeroWidth_le
  · intro h
    rcases lt_or_ge σ (1 / 2) with hσ' | hσ'
    · exact (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).mpr
        (xiZeroHalfPlaneBound_of_criticalDeficitPointwiseRate hσ h)
    · exact zetaZeroWidth_le_half.trans hσ'

/-- **Slack-free zero-width equivalence for `CoprimeCrossWorkLowerRate` (all `σ ≥ 0`).** -/
theorem zetaZeroWidth_le_iff_coprimeCrossWorkLowerRate {σ : ℝ} (hσ : 0 ≤ σ) :
    zetaZeroWidth ≤ σ ↔ CoprimeCrossWorkLowerRate σ :=
  (zetaZeroWidth_le_iff_criticalDeficitPointwiseRate hσ).trans
    (criticalDeficitPointwiseRate_iff_coprimeCrossWorkLowerRate hσ)

/-- **Slack-free cumulative energy equivalence for `zetaZeroWidth ≤ σ` (`σ > 0`).** For every
strictly positive `σ > 0`, `zetaZeroWidth ≤ σ` iff `CriticalDeficitEnergyRate σ` holds at `σ`
itself. -/
theorem zetaZeroWidth_le_iff_criticalDeficitEnergyRate_of_pos {σ : ℝ} (hσ : 0 < σ) :
    zetaZeroWidth ≤ σ ↔ CriticalDeficitEnergyRate σ := by
  constructor
  · intro hw
    obtain ⟨C, hC0, hC⟩ := criticalDeficitPointwiseRate_of_zetaZeroWidth_le hw
    refine ⟨C / (2 * σ), by positivity, fun T hT => ?_⟩
    have hle : (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) ≤
        ∫ t in Icc 0 T, C * Real.exp (2 * σ * t) :=
      setIntegral_mono_on continuous_ccmPrimeDeficitCriticalEnergy.integrableOn_Icc
        ((continuous_const.mul (Real.continuous_exp.comp
          (continuous_const.mul continuous_id))).integrableOn_Icc)
        measurableSet_Icc fun t ht => hC t ht.1
    have hprim : ∀ t : ℝ, HasDerivAt (fun s => C / (2 * σ) * Real.exp (2 * σ * s))
        (C * Real.exp (2 * σ * t)) t := fun t => by
      have h1 : HasDerivAt (fun s : ℝ => 2 * σ * s) (2 * σ) t := by
        simpa only [mul_one] using (hasDerivAt_id' t).const_mul (2 * σ)
      refine (h1.exp.const_mul (C / (2 * σ))).congr_deriv ?_
      field_simp
    have hint : (∫ t in Icc 0 T, C * Real.exp (2 * σ * t)) =
        C / (2 * σ) * (Real.exp (2 * σ * T) - 1) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hT,
        intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hprim t)
          ((continuous_const.mul (Real.continuous_exp.comp
            (continuous_const.mul continuous_id))).intervalIntegrable 0 T)]
      simp only [mul_zero, Real.exp_zero]
      ring
    rw [hint] at hle
    exact hle.trans (by nlinarith [div_nonneg hC0 (by positivity : (0 : ℝ) ≤ 2 * σ)])
  · intro h
    rcases lt_or_ge σ (1 / 2) with hσ' | hσ'
    · exact (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ.le).mpr
        (xiZeroHalfPlaneBound_of_criticalDeficitEnergyRate hσ.le h)
    · exact zetaZeroWidth_le_half.trans hσ'

/-- Admissible `(1 + T)`-free rates of the integrated Chebyshev deficit:
`|ccmLogChebyshevDeficitPrimitive T| ≤ B e^{(1/2 + β) T}` for all `T ≥ 0`. -/
def pureDeficitRates : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ ∃ B : ℝ, ∀ T : ℝ, 0 ≤ T →
    |ccmLogChebyshevDeficitPrimitive T| ≤ B * Real.exp ((1 / 2 + β) * T)}

/-- Set of admissible pointwise critical-energy rates `β ≥ 0`. -/
def criticalDeficitPointwiseRates : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ CriticalDeficitPointwiseRate β}

/-- Set of admissible coprime cross-work lower-bound rates `β ≥ 0`. -/
def coprimeCrossWorkLowerRates : Set ℝ :=
  {β : ℝ | 0 ≤ β ∧ CoprimeCrossWorkLowerRate β}

/-- **Exact closed-ray theorem for `pureDeficitRates`:** `pureDeficitRates = Ici zetaZeroWidth`. -/
theorem pureDeficitRates_eq_Ici : pureDeficitRates = Ici zetaZeroWidth := by
  ext β
  rw [mem_Ici]
  constructor
  · rintro ⟨hβ, B, hB⟩
    have hB0 : 0 ≤ B := by
      have h0 := hB 0 le_rfl
      simp only [mul_zero, Real.exp_zero, mul_one] at h0
      exact (abs_nonneg _).trans h0
    refine zetaZeroWidth_le_of_mem_deficitAbsRates ⟨hβ, B, fun T hT => ?_⟩
    calc |ccmLogChebyshevDeficitPrimitive T|
        ≤ B * Real.exp ((1 / 2 + β) * T) := hB T hT
      _ ≤ B * (1 + T) * Real.exp ((1 / 2 + β) * T) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos ((1 / 2 + β) * T)).le
          nlinarith
  · intro hw
    have hβ : 0 ≤ β := zetaZeroWidth_nonneg.trans hw
    obtain ⟨B, _, huniv⟩ := exists_univ_abs_ccmPrimeDeficitIncoming_le_of_zetaZeroWidth_le
    refine ⟨hβ, B, fun T hT => ?_⟩
    have hin := huniv hβ hw T hT
    have hid : ccmLogChebyshevDeficitPrimitive T =
        Real.exp (T / 2) * ccmPrimeDeficitIncoming T := by
      unfold ccmPrimeDeficitIncoming
      rw [← mul_assoc, ← Real.exp_add, show T / 2 + -T / 2 = 0 by ring, Real.exp_zero, one_mul]
    rw [hid, abs_mul, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (T / 2) * |ccmPrimeDeficitIncoming T|
        ≤ Real.exp (T / 2) * (B * Real.exp (β * T)) :=
          mul_le_mul_of_nonneg_left hin (Real.exp_pos _).le
      _ = B * (Real.exp (T / 2) * Real.exp (β * T)) := by ring
      _ = B * Real.exp ((1 / 2 + β) * T) := by rw [← Real.exp_add]; congr 2; ring

/-- **Exact closed-ray theorem for `deficitAbsRates`:** `deficitAbsRates = Ici zetaZeroWidth`,
upgrading `zetaZeroWidth_eq_sInf_deficitAbsRates` to exact minimum attainment (`IsLeast`). -/
theorem deficitAbsRates_eq_Ici : deficitAbsRates = Ici zetaZeroWidth := by
  ext β
  rw [mem_Ici]
  constructor
  · exact zetaZeroWidth_le_of_mem_deficitAbsRates
  · intro hw
    obtain ⟨hβ, B, hB⟩ := pureDeficitRates_eq_Ici.symm.subset hw
    have hB0 : 0 ≤ B := by
      have h0 := hB 0 le_rfl
      simp only [mul_zero, Real.exp_zero, mul_one] at h0
      exact (abs_nonneg _).trans h0
    refine ⟨hβ, B, fun T hT => (hB T hT).trans ?_⟩
    refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos ((1 / 2 + β) * T)).le
    nlinarith

theorem isLeast_pureDeficitRates : IsLeast pureDeficitRates zetaZeroWidth := by
  rw [pureDeficitRates_eq_Ici]; exact isLeast_Ici

theorem isLeast_deficitAbsRates : IsLeast deficitAbsRates zetaZeroWidth := by
  rw [deficitAbsRates_eq_Ici]; exact isLeast_Ici

/-- **Exact closed-ray theorem for `deficitPowerRates k` (`k > 0`):**
`deficitPowerRates k = Ici (k * zetaZeroWidth)`, attaining `k * zetaZeroWidth` as its minimum. -/
theorem deficitPowerRates_eq_Ici {k : ℕ} (hk : 0 < k) :
    deficitPowerRates k = Ici ((k : ℝ) * zetaZeroWidth) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  ext γ
  rw [mem_deficitPowerRates_iff hk, deficitAbsRates_eq_Ici, mem_Ici, mem_Ici,
    le_div_iff₀ hkpos, mul_comm]

theorem isLeast_deficitPowerRates {k : ℕ} (hk : 0 < k) :
    IsLeast (deficitPowerRates k) ((k : ℝ) * zetaZeroWidth) := by
  rw [deficitPowerRates_eq_Ici hk]; exact isLeast_Ici

/-- **Exact closed-ray theorem for `criticalDeficitPointwiseRates`:**
`criticalDeficitPointwiseRates = Ici zetaZeroWidth`. -/
theorem criticalDeficitPointwiseRates_eq_Ici :
    criticalDeficitPointwiseRates = Ici zetaZeroWidth := by
  ext β
  rw [criticalDeficitPointwiseRates, mem_setOf_eq, mem_Ici]
  exact ⟨fun ⟨hβ, h⟩ => (zetaZeroWidth_le_iff_criticalDeficitPointwiseRate hβ).mpr h,
    fun hw => ⟨zetaZeroWidth_nonneg.trans hw, criticalDeficitPointwiseRate_of_zetaZeroWidth_le hw⟩⟩

theorem isLeast_criticalDeficitPointwiseRates :
    IsLeast criticalDeficitPointwiseRates zetaZeroWidth := by
  rw [criticalDeficitPointwiseRates_eq_Ici]; exact isLeast_Ici

/-- **Exact closed-ray theorem for `coprimeCrossWorkLowerRates`:**
`coprimeCrossWorkLowerRates = Ici zetaZeroWidth`. -/
theorem coprimeCrossWorkLowerRates_eq_Ici :
    coprimeCrossWorkLowerRates = Ici zetaZeroWidth := by
  ext β
  rw [coprimeCrossWorkLowerRates, mem_setOf_eq, mem_Ici]
  exact ⟨fun ⟨hβ, h⟩ => (zetaZeroWidth_le_iff_coprimeCrossWorkLowerRate hβ).mpr h,
    fun hw => ⟨zetaZeroWidth_nonneg.trans hw, coprimeCrossWorkLowerRate_of_zetaZeroWidth_le hw⟩⟩

theorem isLeast_coprimeCrossWorkLowerRates :
    IsLeast coprimeCrossWorkLowerRates zetaZeroWidth := by
  rw [coprimeCrossWorkLowerRates_eq_Ici]; exact isLeast_Ici

/-- For `T < 0`, `⌊e^T⌋₊ = 0`, so `ccmPrimeDeficitCoprimeCrossWork T = 0`. -/
theorem ccmPrimeDeficitCoprimeCrossWork_eq_zero_of_neg {T : ℝ} (hT : T < 0) :
    ccmPrimeDeficitCoprimeCrossWork T = 0 := by
  have hfl : ⌊Real.exp T⌋₊ = 0 := Nat.floor_eq_zero.mpr (Real.exp_lt_one_iff.mpr hT)
  have hempty : Finset.Icc 1 ⌊Real.exp T⌋₊ = ∅ := by rw [hfl]; simp
  have hexp : ccmPrimeDeficitMobiusExplicitWork T = 0 := by
    unfold ccmPrimeDeficitMobiusExplicitWork; rw [hempty]; simp
  have hcent : ccmPrimeDeficitMobiusCenteredWork T = 0 := by
    unfold ccmPrimeDeficitMobiusCenteredWork; rw [hempty]; simp
  have hcross : logarithmicCoprimeCross ccmPrimeDeficitMobiusCenteredWork T = 0 := by
    unfold logarithmicCoprimeCross; rw [hempty]; simp
  unfold ccmPrimeDeficitCoprimeCrossWork
  rw [hexp, hcent, hcross]
  ring

/-- Global unconditional upper bound `ccmPrimeDeficitCoprimeCrossWork T ≤ 49 / 4` on all of `ℝ`. -/
theorem ccmPrimeDeficitCoprimeCrossWork_le_forty_nine_fourths_all (T : ℝ) :
    ccmPrimeDeficitCoprimeCrossWork T ≤ 49 / 4 := by
  rcases lt_or_ge T 0 with hT | hT
  · rw [ccmPrimeDeficitCoprimeCrossWork_eq_zero_of_neg hT]; norm_num
  · exact ccmPrimeDeficitCoprimeCrossWork_le_forty_nine_fourths hT

/-- **Endpoint `σ = 0` boundedness characterization of `RiemannHypothesis` via
`ccmPrimeDeficitCriticalEnergy` on `[0, ∞)`.** -/
theorem riemannHypothesis_iff_bddAbove_ccmPrimeDeficitCriticalEnergy :
    RiemannHypothesis ↔ BddAbove (ccmPrimeDeficitCriticalEnergy '' Ici 0) := by
  rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  have hw0 : zetaZeroWidth = 0 ↔ zetaZeroWidth ≤ 0 :=
    ⟨fun h => h.le, fun h => le_antisymm h zetaZeroWidth_nonneg⟩
  rw [hw0, zetaZeroWidth_le_iff_criticalDeficitPointwiseRate le_rfl]
  constructor
  · rintro ⟨C, _, hC⟩
    refine ⟨C, ?_⟩
    rintro _ ⟨T, hT, rfl⟩
    simpa using hC T hT
  · rintro ⟨M, hM⟩
    refine ⟨max M 0, le_max_right M 0, fun T hT => ?_⟩
    simp only [mul_zero, zero_mul, Real.exp_zero, mul_one]
    exact (hM ⟨T, hT, rfl⟩).trans (le_max_left M 0)

/-- **Endpoint `σ = 0` boundedness characterization of `RiemannHypothesis` via
`ccmPrimeDeficitCoprimeCrossWork` on all of `ℝ`.** `RiemannHypothesis` holds if and only if
`ccmPrimeDeficitCoprimeCrossWork` is bounded below on `ℝ`. -/
theorem riemannHypothesis_iff_bddBelow_ccmPrimeDeficitCoprimeCrossWork :
    RiemannHypothesis ↔ BddBelow (Set.range ccmPrimeDeficitCoprimeCrossWork) := by
  rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero]
  have hw0 : zetaZeroWidth = 0 ↔ zetaZeroWidth ≤ 0 :=
    ⟨fun h => h.le, fun h => le_antisymm h zetaZeroWidth_nonneg⟩
  rw [hw0, zetaZeroWidth_le_iff_coprimeCrossWorkLowerRate le_rfl]
  constructor
  · rintro ⟨C, hC0, hC⟩
    refine ⟨-C, ?_⟩
    rintro _ ⟨T, rfl⟩
    rcases lt_or_ge T 0 with hT | hT
    · rw [ccmPrimeDeficitCoprimeCrossWork_eq_zero_of_neg hT]
      linarith
    · have h := hC T hT
      simp only [mul_zero, zero_mul, Real.exp_zero, mul_one] at h
      linarith
  · rintro ⟨M, hM⟩
    refine ⟨max (-M) 0, le_max_right (-M) 0, fun T _hT => ?_⟩
    simp only [mul_zero, zero_mul, Real.exp_zero, mul_one]
    have h : M ≤ ccmPrimeDeficitCoprimeCrossWork T := hM ⟨T, rfl⟩
    have h' : -ccmPrimeDeficitCoprimeCrossWork T ≤ -M := neg_le.mp (by linarith)
    exact h'.trans (le_max_left (-M) 0)

/-- **Two-prime rational lag characterization of `zetaZeroWidth ≤ σ` (`0 ≤ σ < 1/2`), upper and
lower one-sided forms.** For any two distinct primes `p ≠ q` and any `0 ≤ σ < 1/2`, the following
are unconditionally equivalent:
1. `zetaZeroWidth ≤ σ`;
2. `weilLagFunctionReal (k log p + l log q) ≤ M e^{σ (k log p + l log q)}` for all `k, l ∈ ℤ` with
   `0 ≤ k log p + l log q`;
3. `−M e^{σ (k log p + l log q)} ≤ weilLagFunctionReal (k log p + l log q)` for all `k, l ∈ ℤ` with
   `0 ≤ k log p + l log q`. -/
theorem zetaZeroWidth_le_iff_two_primes_exp {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {σ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ < 1 / 2) :
    (zetaZeroWidth ≤ σ ↔
      ∃ M : ℝ, ∀ k l : ℤ, 0 ≤ (k : ℝ) * Real.log p + (l : ℝ) * Real.log q →
        weilLagFunctionReal ((k : ℝ) * Real.log p + (l : ℝ) * Real.log q) ≤
          M * Real.exp (σ * ((k : ℝ) * Real.log p + (l : ℝ) * Real.log q))) ∧
    (zetaZeroWidth ≤ σ ↔
      ∃ M : ℝ, ∀ k l : ℤ, 0 ≤ (k : ℝ) * Real.log p + (l : ℝ) * Real.log q →
        -(M * Real.exp (σ * ((k : ℝ) * Real.log p + (l : ℝ) * Real.log q))) ≤
          weilLagFunctionReal ((k : ℝ) * Real.log p + (l : ℝ) * Real.log q)) := by
  set G : Set ℝ := ((AddSubgroup.closure {Real.log p, Real.log q} : AddSubgroup ℝ) : Set ℝ)
  have hdG : Dense G := dense_addSubgroup_log_primes hp hq hpq
  have hcl : Ici (0 : ℝ) ⊆ closure (G ∩ Ici 0) := by
    intro L hL
    rw [Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨x, hxIoo, hxG⟩ := hdG.inter_open_nonempty (Ioo L (L + ε)) isOpen_Ioo
      ⟨L + ε / 2, by linarith, by linarith⟩
    have hx0 : 0 ≤ x := by linarith [mem_Ici.mp hL, hxIoo.1]
    refine ⟨x, ⟨hxG, hx0⟩, ?_⟩
    rw [Real.dist_eq, abs_of_neg (by linarith [hxIoo.1])]
    linarith [hxIoo.2]
  constructor
  · constructor
    · intro hw
      refine ⟨lagWeightTotal, fun k l hnn => ?_⟩
      have h := (abs_le.mp (abs_weilLagFunctionReal_le_of_zetaZeroWidth_le hσ hw
        ((k : ℝ) * Real.log p + (l : ℝ) * Real.log q))).2
      rwa [abs_of_nonneg hnn] at h
    · rintro ⟨M, hM⟩
      have hclosed : IsClosed {L : ℝ | weilLagFunctionReal L ≤ M * Real.exp (σ * L)} :=
        isClosed_le continuous_weilLagFunctionReal
          (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id)))
      have honG : G ∩ Ici 0 ⊆ {L : ℝ | weilLagFunctionReal L ≤ M * Real.exp (σ * L)} := by
        rintro L ⟨hLG, hL0⟩
        obtain ⟨k, l, hkl⟩ := AddSubgroup.mem_closure_pair.mp hLG
        rw [← hkl, zsmul_eq_mul, zsmul_eq_mul] at hL0 ⊢
        exact hM k l hL0
      have hall : ∀ L : ℝ, 0 ≤ L → weilLagFunctionReal L ≤ M * Real.exp (σ * L) := fun L hL =>
        (closure_minimal honG hclosed) (hcl hL)
      rw [zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ]
      intro ρ hρ
      obtain ⟨q₀, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
      exact re_le_half_add_of_weilLagFunctionReal_le_exp hσ hσ' hall q₀
  · constructor
    · intro hw
      refine ⟨lagWeightTotal, fun k l hnn => ?_⟩
      have h := (abs_le.mp (abs_weilLagFunctionReal_le_of_zetaZeroWidth_le hσ hw
        ((k : ℝ) * Real.log p + (l : ℝ) * Real.log q))).1
      rwa [abs_of_nonneg hnn] at h
    · rintro ⟨M, hM⟩
      have hclosed : IsClosed {L : ℝ | -(M * Real.exp (σ * L)) ≤ weilLagFunctionReal L} :=
        isClosed_le ((continuous_const.mul
          (Real.continuous_exp.comp (continuous_const.mul continuous_id))).neg)
          continuous_weilLagFunctionReal
      have honG : G ∩ Ici 0 ⊆ {L : ℝ | -(M * Real.exp (σ * L)) ≤ weilLagFunctionReal L} := by
        rintro L ⟨hLG, hL0⟩
        obtain ⟨k, l, hkl⟩ := AddSubgroup.mem_closure_pair.mp hLG
        rw [← hkl, zsmul_eq_mul, zsmul_eq_mul] at hL0 ⊢
        exact hM k l hL0
      have hall : ∀ L : ℝ, 0 ≤ L → -(M * Real.exp (σ * L)) ≤ weilLagFunctionReal L :=
        fun L hL => (closure_minimal honG hclosed) (hcl hL)
      rw [zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ]
      intro ρ hρ
      obtain ⟨q₀, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
      exact re_le_half_add_of_neg_exp_le_weilLagFunctionReal hσ hσ' hall q₀

/-- **Slack-free endpoint equivalence dictionary for `zetaZeroWidth ≤ σ` (`0 ≤ σ < 1/2`).**
Without any `β > σ` slack or `(1 + T)` factor, `zetaZeroWidth ≤ σ` is simultaneously equivalent to:
1. `∃ B ≥ 0, ∀ T ≥ 0, |ccmPrimeDeficitIncoming T| ≤ B e^{σ T}`;
2. `∃ B ≥ 0, ∀ T ≥ 0, ccmLogChebyshevDeficitPrimitive T ≤ B e^{(1/2 + σ) T}` (one-sided upper);
3. `CriticalDeficitPointwiseRate σ` (`ccmPrimeDeficitCriticalEnergy T ≤ C e^{2σ T}`);
4. `CoprimeCrossWorkLowerRate σ` (`−ccmPrimeDeficitCoprimeCrossWork T ≤ C e^{2σ T}`);
5. `∃ M ≥ 0, ∀ L ≥ 0, weilLagFunctionReal L ≤ M e^{σ L}` (one-sided Weil-lag upper bound). -/
theorem zetaZeroWidth_le_iff_endpoint_equivalences {σ : ℝ} (hσ : 0 ≤ σ) (hσ' : σ < 1 / 2) :
    (zetaZeroWidth ≤ σ ↔
      ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 ≤ T →
        |ccmPrimeDeficitIncoming T| ≤ B * Real.exp (σ * T)) ∧
    (zetaZeroWidth ≤ σ ↔
      ∃ B : ℝ, 0 ≤ B ∧ ∀ T : ℝ, 0 ≤ T →
        ccmLogChebyshevDeficitPrimitive T ≤ B * Real.exp ((1 / 2 + σ) * T)) ∧
    (zetaZeroWidth ≤ σ ↔ CriticalDeficitPointwiseRate σ) ∧
    (zetaZeroWidth ≤ σ ↔ CoprimeCrossWorkLowerRate σ) ∧
    (zetaZeroWidth ≤ σ ↔
      ∃ M : ℝ, 0 ≤ M ∧ ∀ L : ℝ, 0 ≤ L →
        weilLagFunctionReal L ≤ M * Real.exp (σ * L)) := by
  refine ⟨?_, ?_, zetaZeroWidth_le_iff_criticalDeficitPointwiseRate hσ,
    zetaZeroWidth_le_iff_coprimeCrossWorkLowerRate hσ, ?_⟩
  · constructor
    · intro hw
      obtain ⟨B, hB, huniv⟩ := exists_univ_abs_ccmPrimeDeficitIncoming_le_of_zetaZeroWidth_le
      exact ⟨B, hB.le, huniv hσ hw⟩
    · rintro ⟨B, hB0, hB⟩
      refine (zetaZeroWidth_le_iff_criticalDeficitPointwiseRate hσ).mpr ⟨B ^ 2, by positivity, ?_⟩
      intro T hT
      rw [← ccmPrimeDeficitIncoming_sq, ← sq_abs]
      calc |ccmPrimeDeficitIncoming T| ^ 2
          ≤ (B * Real.exp (σ * T)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) (hB T hT) 2
        _ = B ^ 2 * (Real.exp (σ * T) * Real.exp (σ * T)) := by ring
        _ = B ^ 2 * Real.exp (2 * σ * T) := by rw [← Real.exp_add]; congr 2; ring
  · constructor
    · intro hw
      obtain ⟨_, B, hB⟩ := pureDeficitRates_eq_Ici.symm.subset hw
      have hB0 : 0 ≤ B := by
        have h0 := hB 0 le_rfl
        simp only [mul_zero, Real.exp_zero, mul_one] at h0
        exact (abs_nonneg _).trans h0
      exact ⟨B, hB0, fun T hT => (le_abs_self _).trans (hB T hT)⟩
    · rintro ⟨B, hB0, hB⟩
      refine (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).mpr
        (xiZeroHalfPlaneBound_of_deficitPrimitive_le (B := B) hσ hσ' fun T hT =>
          (hB T hT).trans ?_)
      refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos ((1 / 2 + σ) * T)).le
      nlinarith
  · constructor
    · intro hw
      refine ⟨lagWeightTotal, tsum_nonneg fun _ => norm_nonneg _, fun L hL => ?_⟩
      have h := (abs_le.mp (abs_weilLagFunctionReal_le_of_zetaZeroWidth_le hσ hw L)).2
      rwa [abs_of_nonneg hL] at h
    · rintro ⟨M, _, hM⟩
      rw [zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ]
      intro ρ hρ
      obtain ⟨q₀, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
      exact re_le_half_add_of_weilLagFunctionReal_le_exp hσ hσ' hM q₀

/-! ## §3. Exact fourth-power zero-energy limit law under `RiemannHypothesis` -/

/-- The fourth-power zero energy `Σ_ρ m_ρ² / ‖ρ‖⁴` over all nontrivial zeros of `ζ`. -/
def totalFourthPowerZeroEnergy : ℝ :=
  ∑' ρ : 𝒵, (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 4

theorem totalFourthPowerZeroEnergy_nonneg : 0 ≤ totalFourthPowerZeroEnergy :=
  tsum_nonneg fun _ => by positivity

/-- Equivalence between `XiZeroCopy` and the sigma-type over `XiDivisorSupport`. -/
private def xiZeroCopySigmaEquiv :
    XiZeroCopy ≃ Σ ρ : XiDivisorSupport, Fin (xiSupportMultiplicity ρ) :=
  Equiv.refl _

/-- Unconditional summability of `(xiSupportMultiplicity ρ : ℝ) / ‖(ρ : ℂ)‖²` on `XiDivisorSupport`. -/
theorem summable_xiDivisorSupport_mult_div_norm_sq :
    Summable fun ρ : XiDivisorSupport => (xiSupportMultiplicity ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2 := by
  have hs := summable_inv_norm_sq_xiZeroCopy
  have hpart := hs.sigma
  refine hpart.congr fun ρ => ?_
  have hfin : (∑' _i : Fin (xiSupportMultiplicity ρ), 1 / ‖(ρ : ℂ)‖ ^ 2) =
      (xiSupportMultiplicity ρ : ℝ) / ‖(ρ : ℂ)‖ ^ 2 := by
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one_div]
  exact hfin

/-- **Unconditional summability of the fourth-power zero energy `Σ_ρ m_ρ² / ‖ρ‖⁴`.** Because
`a_ρ = m_ρ / ‖ρ‖²` is unconditionally in `ℓ¹`, its square `a_ρ² = m_ρ² / ‖ρ‖⁴` is unconditionally
summable without any hypothesis on the zeros of `ζ`. -/
theorem summable_xiDivisorSupport_fourthPowerZeroEnergy :
    Summable fun ρ : XiDivisorSupport =>
      (xiSupportMultiplicity ρ : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 4 := by
  have hs := summable_xiDivisorSupport_mult_div_norm_sq
  have hsq := hs.mul_of_nonneg hs (fun _ => by positivity) (fun _ => by positivity)
  exact Summable.congr hsq fun ρ => by dsimp only [Pi.mul_apply]; ring

theorem summable_zetaFourthPowerZeroEnergy :
    Summable fun ρ : 𝒵 => (Zeta23.zetaZeroConfig.mult (ρ : ℂ) : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 4 := by
  rw [← xiDivisorSupportEquivCarrier.symm.summable_iff]
  refine summable_xiDivisorSupport_fourthPowerZeroEnergy.congr fun ρ => ?_
  simp only [Function.comp_apply, xiDivisorSupportEquivCarrier_symm_coe,
    xiSupportMultiplicity_eq_zetaZeroMult]

theorem tsum_xiDivisorSupport_fourthPowerZeroEnergy_eq :
    (∑' ρ : XiDivisorSupport, (xiSupportMultiplicity ρ : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 4) =
      totalFourthPowerZeroEnergy := by
  rw [totalFourthPowerZeroEnergy, ← xiDivisorSupportEquivCarrier.tsum_eq]
  refine tsum_congr fun ρ => ?_
  rw [xiDivisorSupportEquivCarrier_coe, xiSupportMultiplicity_eq_zetaZeroMult]

/-- `XiZeroCopy` is unconditionally nonempty, because `weilLagFunction 0 = poleSharpConstant > 0`. -/
theorem nonempty_xiZeroCopy_of_weilLag : Nonempty XiZeroCopy := by
  by_contra hemp
  rw [not_nonempty_iff] at hemp
  have hz : weilLagFunction 0 = 0 := by
    unfold weilLagFunction
    exact tsum_empty
  rw [weilLagFunction_zero] at hz
  have h0 : poleSharpConstant = 0 := Complex.ofReal_injective (hz.trans Complex.ofReal_zero.symm)
  exact poleSharpConstant_pos.ne' h0

/-- **Strict unconditional positivity of `totalFourthPowerZeroEnergy`.** -/
theorem totalFourthPowerZeroEnergy_pos : 0 < totalFourthPowerZeroEnergy := by
  rw [← tsum_xiDivisorSupport_fourthPowerZeroEnergy_eq]
  obtain ⟨q₀⟩ := nonempty_xiZeroCopy_of_weilLag
  have hm : 0 < (xiSupportMultiplicity q₀.1 : ℝ) := by
    exact_mod_cast xiSupportMultiplicity_pos q₀.1
  have hn : 0 < ‖(q₀.1 : ℂ)‖ := lt_trans (by norm_num) (four_lt_norm_xiZeroCopy q₀)
  exact lt_of_lt_of_le (by positivity)
    (summable_xiDivisorSupport_fourthPowerZeroEnergy.le_tsum q₀.1 fun _ _ => by positivity)

/-- Under `RiemannHypothesis`, `totalFourthPowerZeroEnergy ≤ (2 / 41) * totalZeroEnergy`. -/
theorem totalFourthPowerZeroEnergy_le_two_div_fortyOne_mul_totalZeroEnergy
    (hRH : RiemannHypothesis) :
    totalFourthPowerZeroEnergy ≤ 2 / 41 * totalZeroEnergy := by
  rw [← tsum_xiDivisorSupport_fourthPowerZeroEnergy_eq, totalZeroEnergy,
    ← tsum_xiDivisorSupport_zeroEnergy_eq,
    ← (summable_xiDivisorSupport_zeroEnergy_of_riemannHypothesis hRH).tsum_mul_left]
  refine summable_xiDivisorSupport_fourthPowerZeroEnergy.tsum_le_tsum (fun ρ => ?_)
    ((summable_xiDivisorSupport_zeroEnergy_of_riemannHypothesis hRH).mul_left (2 / 41))
  have him := xiZeroCopy_fortyOne_div_two_lt_im_sq (firstCopy ρ)
  have hle : ((ρ : ℂ).im) ^ 2 ≤ ‖(ρ : ℂ)‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_im_le_norm _) 2
  have hn2 : (41 / 2 : ℝ) < ‖(ρ : ℂ)‖ ^ 2 := lt_of_lt_of_le him hle
  have hnpos : 0 < ‖(ρ : ℂ)‖ ^ 2 := by linarith
  have hinv : 1 / ‖(ρ : ℂ)‖ ^ 2 ≤ 2 / 41 := by
    rw [div_le_div_iff₀ hnpos (by norm_num)]
    linarith
  calc (xiSupportMultiplicity ρ : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 4
      = (1 / ‖(ρ : ℂ)‖ ^ 2) * ((xiSupportMultiplicity ρ : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2) := by ring
    _ ≤ (2 / 41) * ((xiSupportMultiplicity ρ : ℝ) ^ 2 / ‖(ρ : ℂ)‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hinv (by positivity)

/-- Under `RiemannHypothesis`, `(spectralFluxState t).im = 0` for all `t ∈ ℝ`, because
`J(t) = (spectralFluxState t).im` satisfies `J'(t) = −J(t) / 2` and is bounded on all of `ℝ`. -/
theorem spectralFluxState_im_eq_zero_of_riemannHypothesis (hRH : RiemannHypothesis) (t : ℝ) :
    (spectralFluxState t).im = 0 := by
  let G : ℝ → ℝ := fun x => Real.exp (x / 2) * (spectralFluxState x).im
  have hdJ : ∀ x : ℝ, HasDerivAt (fun y => (spectralFluxState y).im)
      (-(spectralFluxState x).im / 2) x := fun x => by
    have h1 := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_spectralFluxState x)
    refine h1.congr_deriv ?_
    simp only [Complex.imCLM_apply, Complex.sub_im, weilLagFunction_im_eq_zero,
      Complex.div_ofNat_im, zero_sub]
    ring
  have hdG : ∀ x : ℝ, HasDerivAt G 0 x := fun x => by
    have h1 := (((hasDerivAt_id x).div_const 2).exp).mul (hdJ x)
    refine h1.congr_deriv ?_
    simp only [id_eq]
    ring
  have hGconst : ∀ x : ℝ, G x = G 0 := fun x => by
    have hc := is_const_of_deriv_eq_zero (fun y => (hdG y).differentiableAt)
      (fun y => (hdG y).deriv) x 0
    exact hc
  have hbnd : ∀ x : ℝ, |(spectralFluxState x).im| ≤ ∑' q : XiZeroCopy, ‖spectralFluxWeight q‖ := by
    intro x
    have hterm : ∀ q : XiZeroCopy,
        ‖spectralFluxWeight q * Complex.exp ((x : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ =
          ‖spectralFluxWeight q‖ := fun q => by
      rw [norm_mul, Complex.norm_exp]
      have hre : ((x : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = x * ((q.1 : ℂ).re - 1 / 2) := by
        simp [Complex.mul_re]
      rw [hre, xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q, sub_self, mul_zero,
        Real.exp_zero, mul_one]
    have hs : Summable fun q : XiZeroCopy =>
        ‖spectralFluxWeight q * Complex.exp ((x : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ := by
      simp_rw [hterm]; exact summable_norm_spectralFluxWeight
    calc |(spectralFluxState x).im| ≤ ‖spectralFluxState x‖ := Complex.abs_im_le_norm _
      _ ≤ ∑' q : XiZeroCopy,
            ‖spectralFluxWeight q * Complex.exp ((x : ℂ) * ((q.1 : ℂ) - 1 / 2))‖ :=
          norm_tsum_le_tsum_norm hs
      _ = ∑' q : XiZeroCopy, ‖spectralFluxWeight q‖ := by simp_rw [hterm]
  have hG0 : G 0 = 0 := by
    by_contra hne
    set M := ∑' q : XiZeroCopy, ‖spectralFluxWeight q‖
    have hM0 : 0 ≤ M := tsum_nonneg fun _ => norm_nonneg _
    have ha : 0 < |G 0| := abs_pos.mpr hne
    set x₀ : ℝ := -2 * (M / |G 0| + 1)
    have hGx₀ : |G 0| = Real.exp (x₀ / 2) * |(spectralFluxState x₀).im| := by
      have h : G 0 = Real.exp (x₀ / 2) * (spectralFluxState x₀).im := (hGconst x₀).symm
      rw [h, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hexp_gt : M / |G 0| + 1 < Real.exp (-x₀ / 2) := by
      have h1 : -x₀ / 2 = M / |G 0| + 1 := by simp only [x₀]; ring
      rw [h1]
      linarith [Real.add_one_le_exp (M / |G 0| + 1)]
    have hval : |(spectralFluxState x₀).im| = |G 0| * Real.exp (-x₀ / 2) := by
      rw [hGx₀, mul_right_comm, ← Real.exp_add, show x₀ / 2 + -x₀ / 2 = 0 by ring,
        Real.exp_zero, one_mul]
    have hgt : M < |(spectralFluxState x₀).im| := by
      rw [hval]
      have hm := mul_lt_mul_of_pos_left hexp_gt ha
      have hcancel : |G 0| * (M / |G 0| + 1) = M + |G 0| := by field_simp
      linarith
    exact (not_lt_of_ge (hbnd x₀)) hgt
  have hGt := (hGconst t).trans hG0
  exact (mul_eq_zero.mp hGt).resolve_left (Real.exp_pos _).ne'

/-- Under `RiemannHypothesis`, `spectralDeficitSum t` is purely real, so
`((spectralDeficitSum t).re)² = ‖spectralDeficitSum t‖²`. -/
theorem spectralDeficitSum_re_sq_eq_norm_sq_of_riemannHypothesis
    (hRH : RiemannHypothesis) (t : ℝ) :
    (spectralDeficitSum t).re ^ 2 = ‖spectralDeficitSum t‖ ^ 2 := by
  have him : (spectralDeficitSum t).im = 0 := by
    rw [spectralDeficitSum_eq_sub, Complex.sub_im,
      spectralFluxState_im_eq_zero_of_riemannHypothesis hRH t, weilLagFunction_im_eq_zero,
      sub_zero]
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, him]
  ring

/-- Multiplicity-grouped coefficient `(xiSupportMultiplicity ρ : ℂ) / (ρ : ℂ)²` on `XiDivisorSupport`. -/
def spectralDeficitSupportCoeff (ρ : XiDivisorSupport) : ℂ :=
  (xiSupportMultiplicity ρ : ℂ) / (ρ : ℂ) ^ 2

theorem summable_norm_spectralDeficitSupportCoeff :
    Summable fun ρ : XiDivisorSupport => ‖spectralDeficitSupportCoeff ρ‖ := by
  refine summable_xiDivisorSupport_mult_div_norm_sq.congr fun ρ => ?_
  unfold spectralDeficitSupportCoeff
  rw [norm_div, Complex.norm_natCast, norm_pow]

theorem tsum_norm_sq_spectralDeficitSupportCoeff_eq :
    (∑' ρ : XiDivisorSupport, ‖spectralDeficitSupportCoeff ρ‖ ^ 2) =
      totalFourthPowerZeroEnergy := by
  rw [← tsum_xiDivisorSupport_fourthPowerZeroEnergy_eq]
  refine tsum_congr fun ρ => ?_
  unfold spectralDeficitSupportCoeff
  rw [norm_div, Complex.norm_natCast, norm_pow]
  ring

/-- Under `RiemannHypothesis`, `spectralDeficitSum t` equals the distinct-frequency almost-periodic
series `Σ_ρ (m_ρ / ρ²) e^{i (Im ρ) t}` over `XiDivisorSupport`. -/
theorem spectralDeficitSum_eq_tsum_support_of_riemannHypothesis
    (hRH : RiemannHypothesis) (t : ℝ) :
    spectralDeficitSum t =
      ∑' ρ : XiDivisorSupport,
        spectralDeficitSupportCoeff ρ * Complex.exp ((((ρ : ℂ).im * t : ℝ) : ℂ) * I) := by
  unfold spectralDeficitSum
  rw [(summable_spectralDeficitSum_term t).tsum_sigma]
  refine tsum_congr fun ρ => ?_
  have hre : (ρ : ℂ).re = 1 / 2 := xiZeroCopy_re_eq_half_of_riemannHypothesis hRH (firstCopy ρ)
  have hexp : Complex.exp ((t : ℂ) * ((ρ : ℂ) - 1 / 2)) =
      Complex.exp ((((ρ : ℂ).im * t : ℝ) : ℂ) * I) := by
    congr 1
    apply Complex.ext <;> simp [hre, mul_comm]
  have hconst : ∀ _i : Fin (xiSupportMultiplicity ρ),
      (1 / (ρ : ℂ) ^ 2) * Complex.exp ((t : ℂ) * ((ρ : ℂ) - 1 / 2)) =
        (1 / (ρ : ℂ) ^ 2) * Complex.exp ((((ρ : ℂ).im * t : ℝ) : ℂ) * I) :=
    fun _ => by rw [hexp]
  change (∑' i : Fin (xiSupportMultiplicity ρ),
      (1 / (ρ : ℂ) ^ 2) * Complex.exp ((t : ℂ) * ((ρ : ℂ) - 1 / 2))) = _
  rw [tsum_fintype, Finset.sum_congr rfl fun i _ => hconst i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, spectralDeficitSupportCoeff]
  ring

/-- Under `RiemannHypothesis`, `(1 / T) ∫_0^T ((spectralDeficitSum t).re)² dt → totalFourthPowerZeroEnergy`. -/
theorem tendsto_mean_spectralDeficitSum_re_sq (hRH : RiemannHypothesis) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, (spectralDeficitSum t).re ^ 2) / T)
      atTop (𝓝 totalFourthPowerZeroEnergy) := by
  rw [← tsum_norm_sq_spectralDeficitSupportCoeff_eq]
  have hP := tendsto_mean_normSq_tsum summable_norm_spectralDeficitSupportCoeff
    (im_injective_of_riemannHypothesis hRH)
  refine hP.congr fun T => ?_
  congr 1
  refine intervalIntegral.integral_congr fun t _ => ?_
  rw [spectralDeficitSum_re_sq_eq_norm_sq_of_riemannHypothesis hRH t,
    spectralDeficitSum_eq_tsum_support_of_riemannHypothesis hRH t]

/-- Uniform `L²` bound on `ccmPrimeDeficitIncoming t − (spectralDeficitSum t).re` across `[0, ∞)`:
there exists `K_err ≥ 0` such that `∫_0^T (ccmPrimeDeficitIncoming t − (spectralDeficitSum t).re)² dt ≤ K_err`
for all `T ≥ 0` unconditionally. -/
theorem exists_integral_incoming_sub_spectralDeficitSum_sq_le :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 ≤ T →
      (∫ t in (0 : ℝ)..T, (ccmPrimeDeficitIncoming t - (spectralDeficitSum t).re) ^ 2) ≤ K := by
  obtain ⟨C₀, hC₀, herr⟩ := exists_abs_ccmPrimeDeficitIncoming_sub_spectralDeficitSum_le
  refine ⟨5 * C₀ ^ 2, by positivity, fun T hT => ?_⟩
  have hpt : ∀ t : ℝ, 0 ≤ t →
      (ccmPrimeDeficitIncoming t - (spectralDeficitSum t).re) ^ 2 ≤
        C₀ ^ 2 * ((1 + t) ^ 2 * Real.exp (-t)) := fun t ht => by
    rw [← sq_abs]
    calc |ccmPrimeDeficitIncoming t - (spectralDeficitSum t).re| ^ 2
        ≤ (C₀ * (1 + t) * Real.exp (-t / 2)) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (herr t ht) 2
      _ = C₀ ^ 2 * (1 + t) ^ 2 * (Real.exp (-t / 2) * Real.exp (-t / 2)) := by ring
      _ = C₀ ^ 2 * ((1 + t) ^ 2 * Real.exp (-t)) := by
          rw [← Real.exp_add, show -t / 2 + -t / 2 = -t by ring]; ring
  have hprim : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => -(s ^ 2 + 4 * s + 5) * Real.exp (-s))
      ((1 + t) ^ 2 * Real.exp (-t)) t := fun t => by
    have h1 : HasDerivAt (fun s : ℝ => -(s ^ 2 + 4 * s + 5)) (-(2 * t + 4)) t := by
      have hs2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
        simpa using (hasDerivAt_pow 2 t)
      have hs1 : HasDerivAt (fun s : ℝ => 4 * s) 4 t := by
        simpa using (hasDerivAt_id' t).const_mul 4
      have hsum := ((hs2.add hs1).add (hasDerivAt_const t (5 : ℝ))).neg
      exact (hsum.congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun s => by simp)).congr_deriv (by ring)
    have h2 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (-Real.exp (-t)) t := by
      simpa using ((hasDerivAt_id t).neg).exp
    refine (h1.mul h2).congr_deriv ?_
    ring
  have hI_lhs : IntervalIntegrable
      (fun t => (ccmPrimeDeficitIncoming t - (spectralDeficitSum t).re) ^ 2) volume 0 T :=
    ((continuous_ccmPrimeDeficitIncoming.sub
      (Complex.continuous_re.comp continuous_spectralDeficitSum)).pow 2).intervalIntegrable 0 T
  have hI_rhs : IntervalIntegrable
      (fun t => C₀ ^ 2 * ((1 + t) ^ 2 * Real.exp (-t))) volume 0 T := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmono : (∫ t in (0 : ℝ)..T,
      (ccmPrimeDeficitIncoming t - (spectralDeficitSum t).re) ^ 2) ≤
      ∫ t in (0 : ℝ)..T, C₀ ^ 2 * ((1 + t) ^ 2 * Real.exp (-t)) :=
    intervalIntegral.integral_mono_on hT hI_lhs hI_rhs fun t ht => hpt t ht.1
  have heval : (∫ t in (0 : ℝ)..T, (1 + t) ^ 2 * Real.exp (-t)) =
      5 - (T ^ 2 + 4 * T + 5) * Real.exp (-T) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hprim t)
      (by apply Continuous.intervalIntegrable; fun_prop)]
    simp only [neg_zero, Real.exp_zero]
    ring
  rw [intervalIntegral.integral_const_mul, heval] at hmono
  have hnn : 0 ≤ (T ^ 2 + 4 * T + 5) * Real.exp (-T) := by positivity
  nlinarith

/-- **Exact fourth-power zero-energy limit law for `ccmPrimeDeficitCriticalEnergy`.** Under
`RiemannHypothesis`,
`lim_{T → ∞} (1 / T) ∫_0^T ccmPrimeDeficitCriticalEnergy t dt = Σ_ρ m_ρ² / ‖ρ‖⁴`. -/
theorem tendsto_mean_ccmPrimeDeficitCriticalEnergy (hRH : RiemannHypothesis) :
    Tendsto (fun T : ℝ => (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) / T)
      atTop (𝓝 totalFourthPowerZeroEnergy) := by
  obtain ⟨K, hK0, hK⟩ := exists_integral_incoming_sub_spectralDeficitSum_sq_le
  have hspec := tendsto_mean_spectralDeficitSum_re_sq hRH
  rw [Metric.tendsto_nhds]
  intro ε hε
  set η : ℝ := min (1 / 2) (ε / (4 * (totalFourthPowerZeroEnergy + 1)))
  have hη_pos : 0 < η := lt_min (by norm_num)
    (div_pos hε (by linarith [totalFourthPowerZeroEnergy_nonneg]))
  have hη_half : η ≤ 1 / 2 := min_le_left _ _
  have hη_eps : η * (totalFourthPowerZeroEnergy + 1) ≤ ε / 4 := by
    have h := min_le_right (1 / 2) (ε / (4 * (totalFourthPowerZeroEnergy + 1)))
    have hpos : 0 < totalFourthPowerZeroEnergy + 1 :=
      by linarith [totalFourthPowerZeroEnergy_nonneg]
    dsimp only [η]
    exact (le_div_iff₀ hpos).mp (by simpa only [div_div, mul_comm (4 : ℝ)] using h)
  have hδ : 0 < min (ε / 4) 1 := lt_min (by positivity) one_pos
  have hev_spec := (Metric.tendsto_nhds.mp hspec) (min (ε / 4) 1) hδ
  have hev_err : ∀ᶠ T : ℝ in atTop, (1 + 1 / η) * K / T < ε / 4 :=
    (tendsto_const_nhds.div_atTop tendsto_id).eventually (gt_mem_nhds (by positivity))
  filter_upwards [eventually_gt_atTop (0 : ℝ), hev_spec, hev_err] with T hT hT_spec hT_err
  rw [Real.dist_eq] at hT_spec ⊢
  obtain ⟨hspec_lo, hspec_hi⟩ := abs_lt.mp hT_spec
  have hδ1 : min (ε / 4) 1 ≤ 1 := min_le_right _ _
  have hδe : min (ε / 4) 1 ≤ ε / 4 := min_le_left _ _
  set A : ℝ → ℝ := fun t => (spectralDeficitSum t).re
  set B : ℝ → ℝ := fun t => ccmPrimeDeficitIncoming t - (spectralDeficitSum t).re
  have hIA : IntervalIntegrable (fun t => A t ^ 2) volume 0 T :=
    ((Complex.continuous_re.comp continuous_spectralDeficitSum).pow 2).intervalIntegrable 0 T
  have hIB : IntervalIntegrable (fun t => B t ^ 2) volume 0 T :=
    ((continuous_ccmPrimeDeficitIncoming.sub
      (Complex.continuous_re.comp continuous_spectralDeficitSum)).pow 2).intervalIntegrable 0 T
  have hIE : IntervalIntegrable ccmPrimeDeficitCriticalEnergy volume 0 T :=
    continuous_ccmPrimeDeficitCriticalEnergy.intervalIntegrable 0 T
  have hconv : (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) =
      ∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t := by
    rw [intervalIntegral.integral_of_le hT.le, integral_Icc_eq_integral_Ioc]
  rw [hconv]
  have hup_int : (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) ≤
      (1 + η) * (∫ t in (0 : ℝ)..T, A t ^ 2) + (1 + 1 / η) * (∫ t in (0 : ℝ)..T, B t ^ 2) := by
    have hpt : ∀ t : ℝ, ccmPrimeDeficitCriticalEnergy t ≤
        (1 + η) * A t ^ 2 + (1 + 1 / η) * B t ^ 2 := fun t => by
      rw [← ccmPrimeDeficitIncoming_sq]
      have hsum : ccmPrimeDeficitIncoming t = A t + B t := by simp only [A, B]; ring
      rw [hsum]
      have hsq : 0 ≤ η * A t ^ 2 - 2 * A t * B t + (1 / η) * B t ^ 2 := by
        have h1 : 0 ≤ (η * A t - B t) ^ 2 := sq_nonneg _
        have h2 := div_nonneg h1 hη_pos.le
        have h3 : (η * A t - B t) ^ 2 / η =
            η * A t ^ 2 - 2 * A t * B t + (1 / η) * B t ^ 2 := by field_simp; ring
        rwa [h3] at h2
      linarith
    have hm := intervalIntegral.integral_mono hT.le hIE
      ((hIA.const_mul (1 + η)).add (hIB.const_mul (1 + 1 / η))) hpt
    rwa [intervalIntegral.integral_add (hIA.const_mul (1 + η)) (hIB.const_mul (1 + 1 / η)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hm
  have hlo_int : (1 - η) * (∫ t in (0 : ℝ)..T, A t ^ 2) -
        (1 + 1 / η) * (∫ t in (0 : ℝ)..T, B t ^ 2) ≤
      ∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t := by
    have hpt : ∀ t : ℝ, (1 - η) * A t ^ 2 - (1 + 1 / η) * B t ^ 2 ≤
        ccmPrimeDeficitCriticalEnergy t := fun t => by
      rw [← ccmPrimeDeficitIncoming_sq]
      have hsum : ccmPrimeDeficitIncoming t = A t + B t := by simp only [A, B]; ring
      rw [hsum]
      have hsq : 0 ≤ η * A t ^ 2 + 2 * A t * B t + (1 / η) * B t ^ 2 := by
        have h1 : 0 ≤ (η * A t + B t) ^ 2 := sq_nonneg _
        have h2 := div_nonneg h1 hη_pos.le
        have h3 : (η * A t + B t) ^ 2 / η =
            η * A t ^ 2 + 2 * A t * B t + (1 / η) * B t ^ 2 := by field_simp; ring
        rwa [h3] at h2
      nlinarith [sq_nonneg (B t)]
    have hm := intervalIntegral.integral_mono hT.le
      ((hIA.const_mul (1 - η)).sub (hIB.const_mul (1 + 1 / η))) hIE hpt
    rwa [intervalIntegral.integral_sub (hIA.const_mul (1 - η)) (hIB.const_mul (1 + 1 / η)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hm
  set SA := (∫ t in (0 : ℝ)..T, A t ^ 2) / T
  set SB := (∫ t in (0 : ℝ)..T, B t ^ 2) / T
  set SE := (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) / T
  have hSB_le : (1 + 1 / η) * SB < ε / 4 := by
    have h1 : SB ≤ K / T := div_le_div_of_nonneg_right (hK T hT.le) hT.le
    have h2 : (1 + 1 / η) * SB ≤ (1 + 1 / η) * K / T := by
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left h1 (by positivity)
    exact lt_of_le_of_lt h2 hT_err
  have hSA_nn : 0 ≤ SA :=
    div_nonneg (intervalIntegral.integral_nonneg hT.le fun _ _ => sq_nonneg _) hT.le
  have hSA_bound : SA ≤ totalFourthPowerZeroEnergy + 1 := by linarith
  have hSE_up : SE ≤ (1 + η) * SA + (1 + 1 / η) * SB := by
    have h := div_le_div_of_nonneg_right hup_int hT.le
    simpa only [SA, SB, SE, add_div, mul_div_assoc] using h
  have hSE_lo : (1 - η) * SA - (1 + 1 / η) * SB ≤ SE := by
    have h := div_le_div_of_nonneg_right hlo_int hT.le
    simpa only [SA, SB, SE, sub_div, mul_div_assoc] using h
  have hηSA : η * SA ≤ ε / 4 :=
    (mul_le_mul_of_nonneg_left hSA_bound hη_pos.le).trans hη_eps
  rw [abs_lt]
  constructor <;> linarith

/-- **Exact asymptotic limit law for `ccmPrimeDeficitSignedWorkDensity`.** Under
`RiemannHypothesis`, `(1 / T) ∫_0^T ccmPrimeDeficitSignedWorkDensity t dt → totalFourthPowerZeroEnergy / 2`,
because `ccmPrimeDeficitCriticalEnergy T` is bounded on `[0, ∞)` and hence `O(1/T)` after dividing
the exact work balance `E(T) + ∫_0^T E(t) dt = 2 ∫_0^T W(t) dt` by `2 T`. -/
theorem tendsto_mean_ccmPrimeDeficitSignedWorkDensity (hRH : RiemannHypothesis) :
    Tendsto (fun T : ℝ => (∫ t in (0 : ℝ)..T, ccmPrimeDeficitSignedWorkDensity t) / T)
      atTop (𝓝 (totalFourthPowerZeroEnergy / 2)) := by
  obtain ⟨M, hM⟩ := riemannHypothesis_iff_bddAbove_ccmPrimeDeficitCriticalEnergy.mp hRH
  have hterm : Tendsto (fun T : ℝ => ccmPrimeDeficitCriticalEnergy T / (2 * T))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun T => max M 0 / (2 * T)) ?_ ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
      rw [Real.norm_eq_abs, abs_of_nonneg
        (div_nonneg (ccmPrimeDeficitCriticalEnergy_nonneg T) (by positivity))]
      exact div_le_div_of_nonneg_right
        ((hM ⟨T, hT.le, rfl⟩).trans (le_max_left M 0)) (by positivity)
    · exact tendsto_const_nhds.div_atTop (tendsto_id.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
  have hmean := (tendsto_mean_ccmPrimeDeficitCriticalEnergy hRH).div_const 2
  have hsum := hterm.add hmean
  rw [zero_add] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
  have hbal := ccmPrimeDeficitCriticalEnergy_balance 0 T
  rw [ccmPrimeDeficitCriticalEnergy_zero, sub_zero, intervalIntegral.integral_of_le hT.le,
    ← integral_Icc_eq_integral_Ioc] at hbal
  have hT0 : T ≠ 0 := hT.ne'
  field_simp
  linarith

/-- Physical-coordinate limit law: under `RiemannHypothesis`,
`(1 / log X) ∫_1^X ccmLogChebyshevDeficitPrimitive(log x)² / x² dx → totalFourthPowerZeroEnergy`
as `X → ∞`. -/
theorem tendsto_mean_deficitPrimitive_sq_div_log (hRH : RiemannHypothesis) :
    Tendsto (fun X : ℝ =>
        (∫ x in Icc 1 X, ccmLogChebyshevDeficitPrimitive (Real.log x) ^ 2 / x ^ 2) / Real.log X)
      atTop (𝓝 totalFourthPowerZeroEnergy) := by
  have h := (tendsto_mean_ccmPrimeDeficitCriticalEnergy hRH).comp Real.tendsto_log_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
  dsimp only [Function.comp_def]
  congr 1
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
  have himg : Icc 1 X = Real.exp '' Icc 0 (Real.log X) := by
    rw [Real.image_exp_Icc, Real.exp_zero, Real.exp_log (lt_of_lt_of_le zero_lt_one hX)]
  rw [himg, integral_image_eq_integral_abs_deriv_smul measurableSet_Icc
    (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt) Real.exp_injective.injOn]
  refine setIntegral_congr_fun measurableSet_Icc fun t _ => ?_
  rw [abs_of_pos (Real.exp_pos t), smul_eq_mul, Real.log_exp, ccmPrimeDeficitCriticalEnergy,
    Real.exp_neg]
  have he := (Real.exp_pos t).ne'
  field_simp

/-- A slope `C` is an asymptotic linear critical-energy slope if
`∫_0^T ccmPrimeDeficitCriticalEnergy t dt ≤ C * T + K` for all `T ≥ 0` and some `K ≥ 0`. -/
def IsAsymptoticCriticalEnergySlope (C : ℝ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 ≤ T →
    (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) ≤ C * T + K

/-- Existence of any asymptotic linear critical-energy slope is unconditionally equivalent to
`RiemannHypothesis`. -/
theorem exists_asymptoticCriticalEnergySlope_iff_riemannHypothesis :
    (∃ C : ℝ, IsAsymptoticCriticalEnergySlope C) ↔ RiemannHypothesis := by
  rw [riemannHypothesis_iff_linear_criticalDeficitEnergy]
  constructor
  · rintro ⟨C, K, hK0, hCK⟩
    have hC0 : 0 ≤ max C 0 := le_max_right C 0
    refine ⟨max C 0 + K, by positivity, fun T hT => ?_⟩
    have h1 := hCK T hT
    have h2 : C * T ≤ max C 0 * T := mul_le_mul_of_nonneg_right (le_max_left C 0) hT
    nlinarith
  · rintro ⟨C, hC0, hC⟩
    exact ⟨C, C, hC0, fun T hT => by linarith [hC T hT]⟩

/-- **Sharp greatest-lower-bound characterization of asymptotic critical-energy slopes.** Under
`RiemannHypothesis`, every `C > totalFourthPowerZeroEnergy` is a valid linear critical-energy slope,
and `totalFourthPowerZeroEnergy` is the greatest lower bound of all valid linear critical-energy
slopes. -/
theorem isGLB_asymptoticCriticalEnergySlope_fourthPowerZeroEnergy (hRH : RiemannHypothesis) :
    (∀ C : ℝ, totalFourthPowerZeroEnergy < C → IsAsymptoticCriticalEnergySlope C) ∧
    IsGLB {C : ℝ | IsAsymptoticCriticalEnergySlope C} totalFourthPowerZeroEnergy := by
  have hlim := tendsto_mean_ccmPrimeDeficitCriticalEnergy hRH
  have hgt : ∀ C : ℝ, totalFourthPowerZeroEnergy < C → IsAsymptoticCriticalEnergySlope C := by
    intro C hC
    have hε : 0 < C - totalFourthPowerZeroEnergy := sub_pos.mpr hC
    have hev := (Metric.tendsto_nhds.mp hlim) (C - totalFourthPowerZeroEnergy) hε
    obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hev
    set M₀ := max T₀ 1
    have hM₀ : 0 ≤ M₀ := by positivity
    refine ⟨∫ t in Icc 0 M₀, ccmPrimeDeficitCriticalEnergy t,
      setIntegral_nonneg measurableSet_Icc fun _ _ => ccmPrimeDeficitCriticalEnergy_nonneg _,
      fun T hT => ?_⟩
    rcases le_or_gt T M₀ with hle | hgt'
    · have hmono : (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) ≤
          ∫ t in Icc 0 M₀, ccmPrimeDeficitCriticalEnergy t :=
        setIntegral_mono_set continuous_ccmPrimeDeficitCriticalEnergy.integrableOn_Icc
          (Eventually.of_forall ccmPrimeDeficitCriticalEnergy_nonneg)
          (Icc_subset_Icc le_rfl hle).eventuallyLE
      have hCT : 0 ≤ C * T :=
        mul_nonneg (totalFourthPowerZeroEnergy_nonneg.trans hC.le) hT
      linarith
    · have hT_ge : T₀ ≤ T := (le_max_left T₀ 1).trans hgt'.le
      have hT_pos : 0 < T := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ M₀) hgt'
      have hd := hT₀ T hT_ge
      rw [Real.dist_eq] at hd
      have hdiv : (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) / T < C := by
        linarith [(abs_lt.mp hd).2]
      have hmul := (div_lt_iff₀ hT_pos).mp hdiv
      have hK0 : 0 ≤ ∫ t in Icc 0 M₀, ccmPrimeDeficitCriticalEnergy t :=
        setIntegral_nonneg measurableSet_Icc fun _ _ => ccmPrimeDeficitCriticalEnergy_nonneg _
      linarith
  refine ⟨hgt, ⟨fun C ⟨K, _, hCK⟩ => ?_, fun b hb => ?_⟩⟩
  · by_contra hlt
    rw [not_le] at hlt
    set ε := (totalFourthPowerZeroEnergy - C) / 2
    have hε : 0 < ε := by simp only [ε]; linarith
    have hev1 := (Metric.tendsto_nhds.mp hlim) ε hε
    have hev2 : ∀ᶠ T : ℝ in atTop, K / T < ε :=
      (tendsto_const_nhds.div_atTop tendsto_id).eventually (gt_mem_nhds hε)
    obtain ⟨T, hT0, hd, hKT⟩ := ((eventually_gt_atTop (0 : ℝ)).and (hev1.and hev2)).exists
    rw [Real.dist_eq] at hd
    have hlo : totalFourthPowerZeroEnergy - ε <
        (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) / T := by
      linarith [(abs_lt.mp hd).1]
    have hup : (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) / T ≤ C + K / T := by
      have h := div_le_div_of_nonneg_right (hCK T hT0.le) hT0.le
      rwa [add_div, mul_div_cancel_right₀ C hT0.ne'] at h
    simp only [ε] at hlo hKT
    linarith
  · by_contra hlt
    rw [not_le] at hlt
    have hmid : totalFourthPowerZeroEnergy < (totalFourthPowerZeroEnergy + b) / 2 := by linarith
    have hle := hb (hgt _ hmid)
    linarith

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
