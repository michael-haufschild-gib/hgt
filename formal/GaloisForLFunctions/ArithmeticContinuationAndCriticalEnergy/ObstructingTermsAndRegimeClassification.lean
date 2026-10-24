import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheCoreDebtIsThePrimeHarmonicSeries
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheQuadraticTermIsTheResidualEnergy
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheDilationDirichletFormOfTheWork
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.TheTangentFactorsThroughTheMoebiusDilation
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.ReadingsOfTheSignCriterion
import GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy.SignedAveragedContinuationAndTheZeroWidthBand
import GaloisForLFunctions.ArithmeticCompensationTheory.TheCoreDebtOnAPositiveIntervalIsAZetaLogRatio

/-!
# Which Terms Obstruct: Exact Faces of the Signed Work and Regime Classification

This module resolves Open Problem 5 of the Arithmetic Continuation and Critical Energy programme by
expressing the negative signed damping work `−2 W_T(ε)` through all owned divisor, dilation,
Markov, window-mean, and Möbius-factored identities, classifying the terms whose negative part is
not controlled uniformly in the horizon, and proving the sharp parameter-regime dichotomy between
the zero anchor `(0, ε]` and compact positive intervals `[a, c]` (`0 < a ≤ c`).

1. **Five Exact Faces of the Obstructing Work (`§1`)**:
   - *Core + deviation accounting*:
     `−2 W_T(ε) = −2 workDeviation ε T − 2 workCore ε T`, where `workCore ε T ≥ 0` helps backward
     continuation, `workQuadratic ε T` is bounded in magnitude by `Θ_ε(T) · 3(1 + E_T(ε))`, and
     `workDeviation = workLinearWindow + workLinearPrefix + workQuadratic + polarDilationCorrection`
     carries the signed oscillation (`neg_two_mul_signedDampingWork_eq_deviation_sub_core`).
   - *Dilation Dirichlet form*:
     `−2 W_T(ε) = dilationJumpEnergy ε T A_ε − dilationEdgeMass ε T A_ε − 2 polarDilationCorrection ε T`,
     identifying the nonnegative dilation jump energy `J_ε(A_ε)` as the obstructing term and the
     edge mass `M_ε(A_ε) = dilationCreationPotential + dilationFibrePotential` as the restoring term
     (`neg_two_mul_signedDampingWork_eq_dilationJump_sub_edgeMass`).
   - *Arithmetic Markov generator*:
     `−2 W_T(ε) = arithmeticDampingTotalJumpEnergy (arithmeticDampingCenteredMean ε) T + 2 dampedReadout ε Σ_n (n/(n+1)) arithmeticDampingCenteredMean ε n − arithmeticDampingBoundaryFlux (arithmeticDampingCenteredMean ε) T`,
     identifying the nonnegative Markov jump energy plus density forcing minus boundary flux as the
     obstructing combination (`neg_two_mul_signedDampingWork_eq_markov`).
   - *Window-mean smoothing*:
     `−2 W_T(ε) = −2 (Σ_{j≤T} Λ(j) j^{−ε} ⟪F_j A_ε, A_ε⟫_T + polarDilationCorrection ε T)`,
     identifying the negative prime-weighted correlation of the source with its own fibre window
     means (`neg_two_mul_signedDampingWork_eq_windowMean`).
   - *Möbius-factored tangent*:
     `W_T(ε) = ⟪A_ε, D^{μ_ε}(moebiusFreeTangentCore ε)⟫_T + ⟪A_ε, tangentPolarShift ε⟫_T`, isolating
     all Möbius signs of the tangent inside a single Möbius dilation acting on an explicit
     Möbius-free row (`signedDampingWork_eq_moebiusDilation_pairing`).

2. **The Sharp Parameter-Regime Dichotomy (`§2`)**:
   - *Zero anchor `(0, ε]`*: The integrated core grows on the prime-harmonic scale (`Σ_{p≤T/2} 1/p`),
     so under admission at `ε` the integrated deviation `∫_η^ε 2 workDeviation x T dx` cannot be
     bounded below uniformly in `(η, T)`: for every `M : ℝ` there exist `T ≥ 2` and `η ∈ (0, ε]`
     with `∫_η^ε 2 workDeviation x T dx ≤ −M` (`exists_horizon_damping_integral_workDeviation_le`).
   - *Positive interval `[a, c]` (`0 < a ≤ c`)*: The integrated core satisfies
     `0 ≤ ∫_a^c workCore x T dx ≤ log ζ(1+a) − log ζ(1+c)` for every horizon `T` and converges to
     `log ζ(1+a) − log ζ(1+c)` as `T → ∞` (`integral_workCore_bounds_on_positive_interval`). Hence
     the core is horizon-uniformly paid, and when both endpoints are admitted the integrated
     deviation `|∫_a^c 2 workDeviation x T dx|` is bounded uniformly in `T`
     (`exists_abs_integral_workDeviation_le_of_admits`).

3. **Five-Way Equivalence of Obstructing-Term Control on `[a, c]` (`§3`)**:
   On any compact positive interval `[a, c]` (`0 < a ≤ c`) with `c` admitted, admission at `a` is
   five-way equivalent (`obstructingTerms_positive_interval_tfae`) to a horizon-uniform upper bound
   on the integral over `[a, c]` of:
   - the negative deviation `−2 workDeviation x T`;
   - the dilation jump energy minus edge mass and polar correction;
   - the Markov jump energy plus density forcing minus boundary flux;
   - the negative prime-weighted window-mean correlation.

4. **Unconditional Control Above `Θ − ½` and on the Vinogradov–Korobov Band (`§4`)**:
   All four integrated obstructing combinations are unconditionally bounded uniformly in `T` on
   every compact `[a, c] ⊂ (Θ − ½, ∞)` (`exists_obstructing_integrals_le_of_zetaZeroAbscissa_sub_half_lt`)
   and uniformly in `(T, a, c)` along the Vinogradov–Korobov band
   `a ≥ ½ − κ σ(T)/(480 log T)` (`exists_obstructing_integrals_le_on_vinogradovKorobovBand`).
-/

open Set Filter Finset MeasureTheory Topology
open RHTower RHTower.Sieve
open GaloisForLFunctions.BezoutValuationIncidence
open GaloisForLFunctions.ArithmeticCompensationTheory

namespace GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy

noncomputable section
set_option autoImplicit false

/-! ## §1. Five Exact Faces of the Obstructing Signed Work `-2 W_T(ε)` -/

/-- **Face 1 (Core + deviation accounting).**
Twice the negative signed work splits into the negative deviation minus twice the nonnegative core:
`-(2 * signedDampingWork ε T) = -(2 * workDeviation ε T) - 2 * workCore ε T`. -/
theorem neg_two_mul_signedDampingWork_eq_deviation_sub_core (ε : ℝ) (T : ℕ) :
    -(2 * signedDampingWork ε T) = -(2 * workDeviation ε T) - 2 * workCore ε T := by
  rw [signedDampingWork_eq_core_add_deviation]
  ring

/-- **Face 2 (Dilation Dirichlet form: jump energy minus edge mass).**
Twice the negative signed work is the nonnegative dilation jump energy minus the dilation edge mass
and twice the polar correction. -/
theorem neg_two_mul_signedDampingWork_eq_dilationJump_sub_edgeMass (ε : ℝ) (T : ℕ) :
    -(2 * signedDampingWork ε T) =
      dilationJumpEnergy ε T (pmPowerDampedCenteredDivisorPrefix ε) -
        dilationEdgeMass ε T (pmPowerDampedCenteredDivisorPrefix ε) -
        2 * polarDilationCorrection ε T := by
  have h1 := signedDampingWork_eq_dilationForm_add_correction ε T
  have h2 := two_mul_rowDilationForm_eq ε T (pmPowerDampedCenteredDivisorPrefix ε)
  rw [← dilationForm_eq_rowDilationForm] at h2
  linarith

/-- **Face 2b (Dilation jump energy minus creation and fibre potentials).** -/
theorem neg_two_mul_signedDampingWork_eq_dilationJump_sub_potentials (ε : ℝ) (T : ℕ) :
    -(2 * signedDampingWork ε T) =
      dilationJumpEnergy ε T (pmPowerDampedCenteredDivisorPrefix ε) -
        dilationCreationPotential ε T (pmPowerDampedCenteredDivisorPrefix ε) -
        dilationFibrePotential ε T (pmPowerDampedCenteredDivisorPrefix ε) -
        2 * polarDilationCorrection ε T := by
  rw [neg_two_mul_signedDampingWork_eq_dilationJump_sub_edgeMass, dilationEdgeMass_eq]
  ring

/-- **Face 3 (Arithmetic Markov generator: jump energy + density forcing minus boundary flux).** -/
theorem neg_two_mul_signedDampingWork_eq_markov {ε : ℝ} (hε : 0 < ε) (T : ℕ) :
    -(2 * signedDampingWork ε T) =
      arithmeticDampingTotalJumpEnergy (arithmeticDampingCenteredMean ε) T +
        2 * dampedReadout ε *
          (∑ n ∈ Finset.Icc 1 T, ((n : ℝ) / (n + 1)) * arithmeticDampingCenteredMean ε n) -
        arithmeticDampingBoundaryFlux (arithmeticDampingCenteredMean ε) T := by
  have h := two_mul_signedDampingWork_eq_markov hε T
  linarith

/-- **Face 4 (Window-mean correlation).**
Twice the negative signed work is `-2` times the prime-weighted correlation of the centred source
with its own fibre window means plus the polar dilation correction. -/
theorem neg_two_mul_signedDampingWork_eq_windowMean (ε : ℝ) (T : ℕ) :
    -(2 * signedDampingWork ε T) =
      -2 * ((∑ j ∈ Finset.Icc 1 T, dampedPrimeWeight ε j *
          pronicPairing T (rowFibreAverage j T (pmPowerDampedCenteredDivisorPrefix ε))
            (pmPowerDampedCenteredDivisorPrefix ε)) +
        polarDilationCorrection ε T) := by
  rw [signedDampingWork_eq_dilationForm_add_correction, dilationForm_eq_rowDilationForm,
    rowDilationForm_eq_fibreAverage_pairing ε T (pmPowerDampedCenteredDivisorPrefix ε)
      (pmPowerDampedCenteredDivisorPrefix_zero ε)]
  ring

/-- The explicit Möbius-free row `Ψ_ε(m) − m₀(ε) Σ_{j ≤ m} Λ(j) j^{−ε} Φ_ε(⌊m/j⌋)` on which the
damped Möbius dilation acts to produce the damping tangent. -/
def moebiusFreeTangentCore (ε : ℝ) (m : ℕ) : ℝ :=
  dampedPrimeFloorSum ε m -
    (pmPowerDampedDivisorDensity ε).re *
      ∑ j ∈ Finset.Icc 1 m, dampedPrimeWeight ε j * dampedUnitFloorSum ε (m / j)

/-- The explicit polar shift `m₀(ε) Ψ_ε(n) − n m(ε)` of the damping tangent. -/
def tangentPolarShift (ε : ℝ) (n : ℕ) : ℝ :=
  (pmPowerDampedDivisorDensity ε).re * dampedPrimeFloorSum ε n - dampedReadout ε * n

/-- **Face 5 (Möbius-factored tangent pairing).**
The signed damping work pairs the centred source against the single Möbius dilation of the explicit
Möbius-free row `moebiusFreeTangentCore ε`, plus the explicit polar shift `tangentPolarShift ε`. -/
theorem signedDampingWork_eq_moebiusDilation_pairing (ε : ℝ) (T : ℕ) :
    signedDampingWork ε T =
      pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε)
        (prefixDilation (dampedMoebiusWeight ε) (moebiusFreeTangentCore ε)) +
      pronicPairing T (pmPowerDampedCenteredDivisorPrefix ε) (tangentPolarShift ε) := by
  unfold signedDampingWork pronicPairing
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [dampedChebyshevError_eq_moebiusDilation ε n]
  unfold moebiusFreeTangentCore tangentPolarShift
  ring

/-! ## §2. The Sharp Parameter-Regime Dichotomy: Zero Anchor vs. Positive Interval -/

/-- The explicit core `workCore ε T` is nonnegative at every damping and every horizon. -/
theorem workCore_nonneg (ε : ℝ) (T : ℕ) : 0 ≤ workCore ε T := by
  unfold workCore
  refine Finset.sum_nonneg fun n hn => ?_
  have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  exact div_nonneg (dampedPrimePrefix_nonneg ε n) (by positivity)

/-- `workCore · T` is interval-integrable on every compact damping interval. -/
theorem intervalIntegrable_workCore (η ε : ℝ) (T : ℕ) :
    IntervalIntegrable (fun x => workCore x T) volume η ε := by
  refine ContinuousOn.intervalIntegrable ?_
  rw [show (fun x : ℝ => workCore x T) =
      (fun x : ℝ => ∑ n ∈ Finset.Icc 1 T, dampedPrimePrefix x n /
        ((n : ℝ) * ((n : ℝ) + 1))) from rfl]
  refine continuousOn_finsetSum _ fun n _ => ContinuousOn.div_const ?_ _
  rw [show (fun x : ℝ => dampedPrimePrefix x n) =
      (fun x : ℝ => ∑ j ∈ Finset.Icc 1 n, dampedPrimeWeight x j) from rfl]
  exact continuousOn_finsetSum _ fun j hj =>
    continuousOn_const.mul (continuousOn_rpow_neg_natCast (Finset.mem_Icc.mp hj).1 _)

/-- `2 * workDeviation · T` is interval-integrable on every positive interval `[a, c]`. -/
theorem intervalIntegrable_two_mul_workDeviation {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) (T : ℕ) :
    IntervalIntegrable (fun x => 2 * workDeviation x T) volume a c := by
  have hW := intervalIntegrable_signedDampingWork ha hac T
  have hC := (intervalIntegrable_workCore a c T).const_mul 2
  have hfun : (fun x => 2 * workDeviation x T) =
      (fun x => 2 * signedDampingWork x T - 2 * workCore x T) :=
    funext fun x => by rw [signedDampingWork_eq_core_add_deviation]; ring
  rw [hfun]
  exact hW.sub hC

/-- **Positive-interval core bounds.**
On any compact positive interval `[a, c]` (`0 < a ≤ c`), the integrated core is nonnegative, bounded
uniformly in `T` by `log ζ(1+a) − log ζ(1+c)`, and converges to `log ζ(1+a) − log ζ(1+c)` as
`T → ∞`. -/
theorem integral_workCore_bounds_on_positive_interval {a c : ℝ} (ha : 0 < a) (hac : a ≤ c) :
    (∀ T : ℕ, 0 ≤ ∫ x in a..c, workCore x T) ∧
    (∀ T : ℕ, (∫ x in a..c, workCore x T) ≤
      Real.log (riemannZeta ((1 + a : ℝ) : ℂ)).re -
        Real.log (riemannZeta ((1 + c : ℝ) : ℂ)).re) ∧
    Tendsto (fun T : ℕ => ∫ x in a..c, workCore x T) atTop
      (𝓝 (Real.log (riemannZeta ((1 + a : ℝ) : ℂ)).re -
        Real.log (riemannZeta ((1 + c : ℝ) : ℂ)).re)) :=
  ⟨fun T => intervalIntegral.integral_nonneg hac (fun x _ => workCore_nonneg x T),
   fun T => integral_workCore_le_logZeta ha hac T,
   tendsto_integral_workCore_logZeta ha (ha.trans_le hac)⟩

/-- **At the zero anchor, admission forces the integrated deviation to diverge to `−∞`.**
If `ε > 0` is admitted (`∀ T, E_T(ε) ≤ B`), then for every `M : ℝ` there exist a horizon `T ≥ 2` and
a left endpoint `η ∈ (0, ε]` such that `∫_η^ε 2 * workDeviation x T dx ≤ −M`. -/
theorem exists_horizon_damping_integral_workDeviation_le {ε B : ℝ} (hε : 0 < ε)
    (hB : ∀ T : ℕ, dampedMobiusEnergy ε T ≤ B) (M : ℝ) :
    ∃ (T : ℕ) (η : ℝ), 2 ≤ T ∧ 0 < η ∧ η ≤ ε ∧
      (∫ x in η..ε, 2 * workDeviation x T) ≤ -M := by
  have h2 : (2 : ℝ) ^ (-(ε / 2)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hconst : 0 < (1 - (2 : ℝ) ^ (-(ε / 2))) / 2 := by linarith
  obtain ⟨N, hN⟩ := ((Filter.tendsto_atTop.mp tendsto_primeHarmonic_atTop)
    ((B + M) / ((1 - (2 : ℝ) ^ (-(ε / 2))) / 2))).exists
  set T : ℕ := 2 * N + 2
  have hT2 : 2 ≤ T := by omega
  have hT1 : (1 : ℝ) < (T : ℝ) := by exact_mod_cast (show 1 < T by omega)
  have hT0 : (0 : ℝ) < (T : ℝ) := by linarith
  have hlogT : 0 < Real.log T := Real.log_pos hT1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set η : ℝ := min (ε / 2) (Real.log 2 / Real.log T)
  have hη0 : 0 < η := lt_min (by linarith) (div_pos hlog2 hlogT)
  have hη_half : η ≤ ε / 2 := min_le_left _ _
  have hηε : η ≤ ε := by linarith
  have hη_log : η ≤ Real.log 2 / Real.log T := min_le_right _ _
  have hTη : (1 : ℝ) / 2 ≤ (T : ℝ) ^ (-η) := by
    have hmul : Real.log T * η ≤ Real.log 2 := by
      calc Real.log T * η ≤ Real.log T * (Real.log 2 / Real.log T) :=
            mul_le_mul_of_nonneg_left hη_log hlogT.le
        _ = Real.log 2 := mul_div_cancel₀ _ hlogT.ne'
    have hexp : Real.log (1 / 2 : ℝ) ≤ Real.log T * (-η) := by
      rw [Real.log_div (by norm_num) (by norm_num), Real.log_one]
      linarith
    calc (1 : ℝ) / 2 = Real.exp (Real.log (1 / 2 : ℝ)) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log T * (-η)) := Real.exp_le_exp.mpr hexp
      _ = (T : ℝ) ^ (-η) := (Real.rpow_def_of_pos hT0 (-η)).symm
  have h2gap : 1 - (2 : ℝ) ^ (-(ε / 2)) ≤ 1 - (2 : ℝ) ^ (-(ε - η)) := by
    have hpow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by linarith : -(ε - η) ≤ -(ε / 2))
    linarith
  have hmono : primeHarmonic N ≤ primeHarmonic (T / 2 + 1) :=
    primeHarmonic_mono (by omega)
  have hPH_nonneg : 0 ≤ primeHarmonic (T / 2 + 1) := by
    unfold primeHarmonic
    exact Finset.sum_nonneg fun p _ => by positivity
  have hprod : (1 - (2 : ℝ) ^ (-(ε / 2))) / 2 * primeHarmonic (T / 2 + 1) ≤
      2 * (((T : ℝ) ^ (-η) * (1 - (2 : ℝ) ^ (-(ε - η))) / 2) * primeHarmonic (T / 2 + 1)) := by
    have hfac : (1 - (2 : ℝ) ^ (-(ε / 2))) / 2 ≤
        (T : ℝ) ^ (-η) * (1 - (2 : ℝ) ^ (-(ε - η))) := by
      nlinarith
    nlinarith
  have hBM : B + M ≤ (1 - (2 : ℝ) ^ (-(ε / 2))) / 2 * primeHarmonic (T / 2 + 1) := by
    have hNle : (B + M) / ((1 - (2 : ℝ) ^ (-(ε / 2))) / 2) ≤ primeHarmonic (T / 2 + 1) :=
      hN.trans hmono
    linarith [(div_le_iff₀ hconst).mp hNle]
  have hmain := integral_workDeviation_le_primeHarmonic hη0 hηε hB hT2
  refine ⟨T, η, hT2, hη0, hηε, ?_⟩
  linarith

/-- Exact split of the energy difference on `[a, c]` into core and deviation integrals. -/
theorem dampedMobiusEnergy_sub_eq_core_add_deviation_integral {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (T : ℕ) :
    dampedMobiusEnergy c T - dampedMobiusEnergy a T =
      2 * (∫ x in a..c, workCore x T) + ∫ x in a..c, 2 * workDeviation x T := by
  have hdrop := (integral_signedDampingWork_eq ha hac T).symm
  have hW := intervalIntegrable_signedDampingWork ha hac T
  have hC := (intervalIntegrable_workCore a c T).const_mul 2
  have hD := intervalIntegrable_two_mul_workDeviation ha hac T
  have hfun : (fun x => 2 * signedDampingWork x T) =
      (fun x => 2 * workCore x T + 2 * workDeviation x T) :=
    funext fun x => by rw [signedDampingWork_eq_core_add_deviation]; ring
  rw [hdrop, hfun, intervalIntegral.integral_add hC hD, intervalIntegral.integral_const_mul]

/-- **On a positive interval `[a, c]` with both endpoints admitted, the integrated deviation is
bounded in absolute value uniformly in `T`.** -/
theorem exists_abs_integral_workDeviation_le_of_admits {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hadm_a : Admits dampedMobiusEnergy a) (hadm_c : Admits dampedMobiusEnergy c) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℕ, |∫ x in a..c, 2 * workDeviation x T| ≤ K := by
  obtain ⟨Ba, hBa⟩ := hadm_a
  obtain ⟨Bc, hBc⟩ := hadm_c
  set L : ℝ := Real.log (riemannZeta ((1 + a : ℝ) : ℂ)).re -
    Real.log (riemannZeta ((1 + c : ℝ) : ℂ)).re
  have hL0 : 0 ≤ L :=
    (intervalIntegral.integral_nonneg hac (fun x _ => workCore_nonneg x 0)).trans
      (integral_workCore_le_logZeta ha hac 0)
  refine ⟨max Ba 0 + max Bc 0 + 2 * L, by positivity, fun T => ?_⟩
  have hsplit := dampedMobiusEnergy_sub_eq_core_add_deviation_integral ha hac T
  have hcore_nn : 0 ≤ ∫ x in a..c, workCore x T :=
    intervalIntegral.integral_nonneg hac (fun x _ => workCore_nonneg x T)
  have hcore_le : (∫ x in a..c, workCore x T) ≤ L := integral_workCore_le_logZeta ha hac T
  have hEa0 := dampedMobiusEnergy_nonneg a T
  have hEc0 := dampedMobiusEnergy_nonneg c T
  have hEa : dampedMobiusEnergy a T ≤ max Ba 0 := (hBa T).trans (le_max_left Ba 0)
  have hEc : dampedMobiusEnergy c T ≤ max Bc 0 := (hBc T).trans (le_max_left Bc 0)
  rw [abs_le]
  constructor <;> linarith

/-! ## §3. Five-Way Equivalence of Obstructing-Term Control on Positive Intervals -/

/-- On `[a, c]`, the integral of `-(2 * signedDampingWork x T)` equals the integral of the
dilation jump energy minus edge mass and polar correction. -/
theorem integral_neg_two_mul_signedDampingWork_eq_dilationJump {a c : ℝ} (T : ℕ) :
    (∫ x in a..c, -(2 * signedDampingWork x T)) =
      ∫ x in a..c,
        (dilationJumpEnergy x T (pmPowerDampedCenteredDivisorPrefix x) -
          dilationEdgeMass x T (pmPowerDampedCenteredDivisorPrefix x) -
          2 * polarDilationCorrection x T) :=
  intervalIntegral.integral_congr fun x _ =>
    neg_two_mul_signedDampingWork_eq_dilationJump_sub_edgeMass x T

/-- On `[a, c]` (`0 < a ≤ c`), the integral of `-(2 * signedDampingWork x T)` equals the integral
of the Markov jump energy plus density forcing minus boundary flux. -/
theorem integral_neg_two_mul_signedDampingWork_eq_markov {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (T : ℕ) :
    (∫ x in a..c, -(2 * signedDampingWork x T)) =
      ∫ x in a..c,
        (arithmeticDampingTotalJumpEnergy (arithmeticDampingCenteredMean x) T +
          2 * dampedReadout x *
            (∑ n ∈ Finset.Icc 1 T, ((n : ℝ) / (n + 1)) * arithmeticDampingCenteredMean x n) -
          arithmeticDampingBoundaryFlux (arithmeticDampingCenteredMean x) T) := by
  refine intervalIntegral.integral_congr fun x hx => ?_
  rw [Set.uIcc_of_le hac] at hx
  exact neg_two_mul_signedDampingWork_eq_markov (lt_of_lt_of_le ha hx.1) T

/-- On `[a, c]`, the integral of `-(2 * signedDampingWork x T)` equals the integral of `-2` times
the prime-weighted window-mean correlation plus polar correction. -/
theorem integral_neg_two_mul_signedDampingWork_eq_windowMean {a c : ℝ} (T : ℕ) :
    (∫ x in a..c, -(2 * signedDampingWork x T)) =
      ∫ x in a..c,
        -2 * ((∑ j ∈ Finset.Icc 1 T, dampedPrimeWeight x j *
            pronicPairing T (rowFibreAverage j T (pmPowerDampedCenteredDivisorPrefix x))
              (pmPowerDampedCenteredDivisorPrefix x)) +
          polarDilationCorrection x T) :=
  intervalIntegral.integral_congr fun x _ =>
    neg_two_mul_signedDampingWork_eq_windowMean x T

/-- **Five-Way Equivalence of Obstructing-Term Control on Positive Intervals.**
For any `0 < a ≤ c` with admitted right endpoint `c`, admission at `a` is equivalent to a
horizon-uniform upper bound on the integral over `[a, c]` of:
1. the negative deviation `-(2 * workDeviation x T)`;
2. the dilation jump energy minus edge mass and polar correction;
3. the Markov jump energy plus density forcing minus boundary flux;
4. the negative prime-weighted window-mean correlation. -/
theorem obstructingTerms_positive_interval_tfae {a c : ℝ} (ha : 0 < a) (hac : a ≤ c)
    (hc : Admits dampedMobiusEnergy c) :
    List.TFAE
      [ Admits dampedMobiusEnergy a,
        ∃ C : ℝ, ∀ T : ℕ, (∫ x in a..c, -(2 * workDeviation x T)) ≤ C,
        ∃ C : ℝ, ∀ T : ℕ,
          (∫ x in a..c,
            (dilationJumpEnergy x T (pmPowerDampedCenteredDivisorPrefix x) -
              dilationEdgeMass x T (pmPowerDampedCenteredDivisorPrefix x) -
              2 * polarDilationCorrection x T)) ≤ C,
        ∃ C : ℝ, ∀ T : ℕ,
          (∫ x in a..c,
            (arithmeticDampingTotalJumpEnergy (arithmeticDampingCenteredMean x) T +
              2 * dampedReadout x *
                (∑ n ∈ Finset.Icc 1 T, ((n : ℝ) / (n + 1)) * arithmeticDampingCenteredMean x n) -
              arithmeticDampingBoundaryFlux (arithmeticDampingCenteredMean x) T)) ≤ C,
        ∃ C : ℝ, ∀ T : ℕ,
          (∫ x in a..c,
            -2 * ((∑ j ∈ Finset.Icc 1 T, dampedPrimeWeight x j *
                pronicPairing T (rowFibreAverage j T (pmPowerDampedCenteredDivisorPrefix x))
                  (pmPowerDampedCenteredDivisorPrefix x)) +
              polarDilationCorrection x T)) ≤ C ] := by
  have h13 : Admits dampedMobiusEnergy a ↔
      ∃ C : ℝ, ∀ T : ℕ, (∫ x in a..c, -(2 * signedDampingWork x T)) ≤ C :=
    (signedAveragedContinuation_tfae ha hac hc).out 0 4
  tfae_have 1 ↔ 3 := by
    rw [h13]
    simp_rw [← integral_neg_two_mul_signedDampingWork_eq_dilationJump]
  tfae_have 1 ↔ 4 := by
    rw [h13]
    simp_rw [← integral_neg_two_mul_signedDampingWork_eq_markov ha hac]
  tfae_have 1 ↔ 5 := by
    rw [h13]
    simp_rw [← integral_neg_two_mul_signedDampingWork_eq_windowMean]
  tfae_have 1 ↔ 2 := by
    rw [h13]
    set L : ℝ := Real.log (riemannZeta ((1 + a : ℝ) : ℂ)).re -
      Real.log (riemannZeta ((1 + c : ℝ) : ℂ)).re
    constructor
    · rintro ⟨C, hC⟩
      refine ⟨C + 2 * L, fun T => ?_⟩
      have hsplit := dampedMobiusEnergy_sub_eq_core_add_deviation_integral ha hac T
      have hdrop := integral_signedDampingWork_eq ha hac T
      have hneg : (∫ x in a..c, -(2 * signedDampingWork x T)) =
          dampedMobiusEnergy a T - dampedMobiusEnergy c T := by
        rw [intervalIntegral.integral_neg, hdrop]; ring
      have hnegD : (∫ x in a..c, -(2 * workDeviation x T)) =
          -(∫ x in a..c, 2 * workDeviation x T) := intervalIntegral.integral_neg
      have hcore_le : (∫ x in a..c, workCore x T) ≤ L := integral_workCore_le_logZeta ha hac T
      linarith [hC T]
    · rintro ⟨C, hC⟩
      refine ⟨C, fun T => ?_⟩
      have hsplit := dampedMobiusEnergy_sub_eq_core_add_deviation_integral ha hac T
      have hdrop := integral_signedDampingWork_eq ha hac T
      have hneg : (∫ x in a..c, -(2 * signedDampingWork x T)) =
          dampedMobiusEnergy a T - dampedMobiusEnergy c T := by
        rw [intervalIntegral.integral_neg, hdrop]; ring
      have hnegD : (∫ x in a..c, -(2 * workDeviation x T)) =
          -(∫ x in a..c, 2 * workDeviation x T) := intervalIntegral.integral_neg
      have hcore_nn : 0 ≤ ∫ x in a..c, workCore x T :=
        intervalIntegral.integral_nonneg hac (fun x _ => workCore_nonneg x T)
      linarith [hC T]
  tfae_finish

/-! ## §4. Unconditional Control Above `Θ − ½` and on the Vinogradov–Korobov Band -/

/-- **Unconditional Control of All Obstructing Integrals Above the Zero Width `Θ − ½`.**
For every compact interval `[a, c]` with `Θ − ½ < a ≤ c`, the integrated negative deviation, the
integrated dilation jump-minus-edge-mass, the integrated Markov jump-plus-forcing-minus-flux, and
the integrated negative window-mean correlation are all unconditionally bounded uniformly in `T`. -/
theorem exists_obstructing_integrals_le_of_zetaZeroAbscissa_sub_half_lt {a c : ℝ}
    (ha : zetaZeroAbscissa - 1 / 2 < a) (hac : a ≤ c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℕ,
      |∫ x in a..c, 2 * workDeviation x T| ≤ C ∧
      (∫ x in a..c,
        (dilationJumpEnergy x T (pmPowerDampedCenteredDivisorPrefix x) -
          dilationEdgeMass x T (pmPowerDampedCenteredDivisorPrefix x) -
          2 * polarDilationCorrection x T)) ≤ C ∧
      (∫ x in a..c,
        (arithmeticDampingTotalJumpEnergy (arithmeticDampingCenteredMean x) T +
          2 * dampedReadout x *
            (∑ n ∈ Finset.Icc 1 T, ((n : ℝ) / (n + 1)) * arithmeticDampingCenteredMean x n) -
          arithmeticDampingBoundaryFlux (arithmeticDampingCenteredMean x) T)) ≤ C ∧
      (∫ x in a..c,
        -2 * ((∑ j ∈ Finset.Icc 1 T, dampedPrimeWeight x j *
            pronicPairing T (rowFibreAverage j T (pmPowerDampedCenteredDivisorPrefix x))
              (pmPowerDampedCenteredDivisorPrefix x)) +
          polarDilationCorrection x T)) ≤ C := by
  have ha0 : 0 < a := by linarith [half_le_zetaZeroAbscissa]
  have hadm_a := admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt ha
  have hadm_c := admits_dampedMobiusEnergy_of_zetaZeroAbscissa_sub_half_lt (ha.trans_le hac)
  obtain ⟨K, hK0, hK⟩ := exists_abs_integral_workDeviation_le_of_admits ha0 hac hadm_a hadm_c
  obtain ⟨W, hW⟩ := exists_neg_signedDampingWork_integral_le_of_zetaZeroAbscissa_sub_half_lt ha hac
  refine ⟨max K (max W 0), by positivity, fun T => ?_⟩
  have hWT : (∫ x in a..c, -(2 * signedDampingWork x T)) ≤ max K (max W 0) :=
    (hW T).trans ((le_max_left W 0).trans (le_max_right K _))
  refine ⟨(hK T).trans (le_max_left K _), ?_, ?_, ?_⟩
  · rw [← integral_neg_two_mul_signedDampingWork_eq_dilationJump]
    exact hWT
  · rw [← integral_neg_two_mul_signedDampingWork_eq_markov ha0 hac]
    exact hWT
  · rw [← integral_neg_two_mul_signedDampingWork_eq_windowMean]
    exact hWT

/-- **Unconditional Control of Obstructing Integrals on the Vinogradov–Korobov Band.**
For every damping floor `ε₀ > 0`, there exists `E ≥ 0` such that for all `T : ℕ` and all intervals
`[a, c]` with `ε₀ ≤ a ≤ c ≤ 1/2` and `a` in the Vinogradov–Korobov band
`a ≥ 1/2 − κ σ(T)/(480 log T)`, the dilation Dirichlet, Markov, and window-mean obstructing
integrals are all bounded by `E`, and the negative deviation integral is bounded by
`E + 2(log ζ(1+a) − log ζ(1+c))`. -/
theorem exists_obstructing_integrals_le_on_vinogradovKorobovBand {ε₀ : ℝ} (hε₀ : 0 < ε₀) :
    ∃ E : ℝ, 0 ≤ E ∧
      ∀ (T : ℕ) (a c : ℝ), ε₀ ≤ a → a ≤ c → c ≤ 1 / 2 →
        1 / 2 - vkKappa * vkScale T / (480 * Real.log T) ≤ a →
          (∫ x in a..c,
            (dilationJumpEnergy x T (pmPowerDampedCenteredDivisorPrefix x) -
              dilationEdgeMass x T (pmPowerDampedCenteredDivisorPrefix x) -
              2 * polarDilationCorrection x T)) ≤ E ∧
          (∫ x in a..c,
            (arithmeticDampingTotalJumpEnergy (arithmeticDampingCenteredMean x) T +
              2 * dampedReadout x *
                (∑ n ∈ Finset.Icc 1 T, ((n : ℝ) / (n + 1)) * arithmeticDampingCenteredMean x n) -
              arithmeticDampingBoundaryFlux (arithmeticDampingCenteredMean x) T)) ≤ E ∧
          (∫ x in a..c,
            -2 * ((∑ j ∈ Finset.Icc 1 T, dampedPrimeWeight x j *
                pronicPairing T (rowFibreAverage j T (pmPowerDampedCenteredDivisorPrefix x))
                  (pmPowerDampedCenteredDivisorPrefix x)) +
              polarDilationCorrection x T)) ≤ E ∧
          (∫ x in a..c, -(2 * workDeviation x T)) ≤
            E + 2 * (Real.log (riemannZeta ((1 + a : ℝ) : ℂ)).re -
              Real.log (riemannZeta ((1 + c : ℝ) : ℂ)).re) := by
  obtain ⟨E, _, hE0, _, hE⟩ := exists_signedWorkIntegral_and_relativeLoss_le_on_vinogradovKorobovBand hε₀
  refine ⟨E, hE0, fun T a c ha_ge hac hc2 hband => ?_⟩
  have ha0 : 0 < a := lt_of_lt_of_le hε₀ ha_ge
  have hwork := (hE T a c ha_ge hac hc2 hband).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← integral_neg_two_mul_signedDampingWork_eq_dilationJump]
    exact hwork
  · rw [← integral_neg_two_mul_signedDampingWork_eq_markov ha0 hac]
    exact hwork
  · rw [← integral_neg_two_mul_signedDampingWork_eq_windowMean]
    exact hwork
  · have hsplit := dampedMobiusEnergy_sub_eq_core_add_deviation_integral ha0 hac T
    have hdrop := integral_signedDampingWork_eq ha0 hac T
    have hneg : (∫ x in a..c, -(2 * signedDampingWork x T)) =
        dampedMobiusEnergy a T - dampedMobiusEnergy c T := by
      rw [intervalIntegral.integral_neg, hdrop]; ring
    have hnegD : (∫ x in a..c, -(2 * workDeviation x T)) =
        -(∫ x in a..c, 2 * workDeviation x T) := intervalIntegral.integral_neg
    have hcore_le := integral_workCore_le_logZeta ha0 hac T
    linarith

end

end GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy
