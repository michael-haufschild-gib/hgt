import GaloisForLFunctions.BiScaleUncertainty.WeilLagPacketCancellationAndPositivity
import GaloisForLFunctions.SquareRootThreshold.TheWallsMeasureOneZeroWidth
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitCoprimeBalance
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitDiagonalControl
import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitChronologicalWork
import GaloisForLFunctions.RHTower.CCM.CCMPrimeEntryEulerEndpointControl
import GaloisForLFunctions.BiScaleUncertainty.PrimeWindowCeilingVinogradovKorobovRemainder

/-!
# The critical prime-deficit energy and Weil-lag flux measure one zero width

This module connects the second-order prime-lag packet identities of
`WeilLagPacketCancellationAndPositivity` with the zero-width dictionary of
`BandSpectrumZeroWidthLaw` and `TheWallsMeasureOneZeroWidth`:

1. **Exact Hardy-type critical energy inequality**
   (`ccmPrimeDeficitSignedWorkDensity_eq`,
   `two_mul_ccmPrimeDeficitSignedWorkDensity_eq`,
   `two_mul_ccmPrimeDeficitCriticalEnergy_add_integral_le_band`,
   `ccmPrimeDeficitCriticalEnergy_le_two_mul_band`,
   `integral_ccmPrimeDeficitCriticalEnergy_le_four_mul_band`):
   Because `ccmPrimeDeficitSignedWorkDensity t = −ccmPrimeDeficitIncoming t * normalizedLogError t`
   and `ccmPrimeDeficitIncoming t ^ 2 = ccmPrimeDeficitCriticalEnergy t`, completing the square in
   the differential energy balance `E'(t) + E(t) = 2 W(t)` gives the pointwise identity
   `2 W(t) = (1/2) E(t) + 2 Ẽ(t)² − (1/2) (ccmPrimeDeficitIncoming t + 2 Ẽ(t))²`,
   and therefore on every interval `[0, T]` (`T ≥ 0`) the exact log-loss-free inequality
   `2 * ccmPrimeDeficitCriticalEnergy T + ∫_0^T ccmPrimeDeficitCriticalEnergy t dt ≤ 4 * ∫_0^T normalizedLogError t ^ 2 dt`.

2. **Windowed AM–GM bridge from local `L²` energy to `stationaryPacket splineProbe`**
   (`integral_abs_Icc_le_of_pos`, `abs_stationaryPacket_splineProbe_le_of_local_sq`,
   `xiZeroHalfPlaneBound_of_local_criticalEnergy_le`,
   `xiZeroHalfPlaneBound_of_local_outgoing_sq_le`,
   `xiZeroHalfPlaneBound_of_local_weilLag_sq_le`):
   Evaluating `2 μ |g(t)| ≤ μ² + g(t)²` at the scale `μ = e^{βτ}` converts any local window `L²`
   bound `∫_{τ−4}^{τ+4} g(t)² dt ≤ C e^{2βτ}` on `ccmPrimeDeficitIncoming`,
   `ccmPrimeDeficitOutgoing`, or `weilLagFunctionReal` directly into an `O(e^{βτ})` bound on
   `stationaryPacket splineProbe τ`, and hence into `XiZeroHalfPlaneBound β`.

3. **Zero-width equivalences and endpoint self-improvement**
   (`CriticalDeficitEnergyRate`, `CriticalDeficitPointwiseRate`,
   `OutgoingDeficitFluxRate`, `WeilLagEnergyRate`,
   `xiZeroHalfPlaneBound_iff_forall_criticalDeficitEnergyRate`,
   `xiZeroHalfPlaneBound_iff_forall_criticalDeficitPointwiseRate`,
   `zetaZeroWidth_le_iff_forall_criticalDeficitEnergyRate`,
   `zetaZeroWidth_le_iff_forall_criticalDeficitPointwiseRate`,
   `riemannHypothesis_iff_linear_criticalDeficitEnergy`,
   `exists_linear_criticalDeficitEnergy_of_forall_criticalDeficitEnergyRate`,
   `riemannHypothesis_of_forall_weilLagEnergyRate`,
   `riemannHypothesis_of_forall_outgoingDeficitFluxRate`):
   For every `0 ≤ σ < 1/2`, `zetaZeroWidth ≤ σ` (and `XiZeroHalfPlaneBound σ`) is unconditionally
   equivalent to `∀ β > σ, CriticalDeficitEnergyRate β` and to
   `∀ β > σ, CriticalDeficitPointwiseRate β`. At `σ = 0`, subexponential growth of
   `∫_0^T ccmPrimeDeficitCriticalEnergy t dt` is equivalent to `RiemannHypothesis` and
   self-improves to linear growth `O(1 + T)`. Moreover, subexponential growth of the cumulative
   Weil-lag energy `∫_0^T (weilLagFunctionReal t)² dt` or outgoing flux energy
   `∫_0^T (ccmPrimeDeficitOutgoing t)² dt` unconditionally implies `RiemannHypothesis` and linear
   critical deficit energy.

4. **Arithmetic reductions and polynomial-to-linear self-improvement**
   (`ccmPrimeDeficitCoprimeCrossWork_le_forty_nine_fourths`,
   `criticalDeficitPointwiseRate_iff_coprimeCrossWorkLowerRate`,
   `riemannHypothesis_iff_forall_coprimeCrossWorkLowerRate`,
   `criticalDeficitEnergyRate_iff_centeredOffDiagonalRate`,
   `riemannHypothesis_iff_quadratic_centeredOffDiagonal`,
   `riemannHypothesis_iff_linear_centeredOffDiagonal`,
   `criticalDeficitEnergyRate_iff_centeredEulerCurvatureRate`,
   `riemannHypothesis_iff_cubic_centeredEulerCurvature`,
   `riemannHypothesis_iff_linear_centeredEulerCurvature`,
   `riemannHypothesis_of_quadratic_chronologicalWork`):
   Because the coprime Möbius square source (`|·| ≤ 49/4`), the prime-entry diagonal
   (`≤ T² + 78 T + 50`), the self-jump budget (`≤ T² + 78 T + 50`), and the Euler-deformation
   endpoint (`≤ (T + 2)(T² / 2 + 30 T + 120)`) are unconditionally controlled, the zero-width
   rate `zetaZeroWidth ≤ σ` and `RiemannHypothesis` reduce to any of the corresponding signed
   arithmetic targets, with quadratic `O(1 + T²)` and cubic `O(1 + T³)` bounds self-improving
   unconditionally to linear `O(1 + T)` bounds.

5. **Unconditional Vinogradov–Korobov frontier bounds**
   (`exists_eventually_ccmPrimeDeficitCriticalEnergy_le_vk`,
   `exists_eventually_abs_ccmPrimeDeficitIncoming_le_vk`,
   `exists_eventually_neg_ccmPrimeDeficitCoprimeCrossWork_le_vk`):
   For every `0 < ex < 3 / 5`, unconditional Vinogradov–Korobov savings yield `C, κ > 0` such that
   `ccmPrimeDeficitCriticalEnergy T ≤ C e^{T − κ T^{ex}}`,
   `|ccmPrimeDeficitIncoming T| ≤ C e^{T/2 − κ T^{ex}}`, and
   `-ccmPrimeDeficitCoprimeCrossWork T ≤ C e^{T − κ T^{ex}}` eventually.
-/

open MeasureTheory Set Filter Topology Complex
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge

open SignedPrimePolar RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open _root_.RHTower GaloisForLFunctions.SquareRootThreshold

noncomputable section
set_option autoImplicit false

/-! ## §1. Exact Hardy-type critical energy inequality -/

/-- Exact factorization of the signed arithmetic work density:
`ccmPrimeDeficitSignedWorkDensity t = −ccmPrimeDeficitIncoming t * normalizedLogError t`. -/
theorem ccmPrimeDeficitSignedWorkDensity_eq (t : ℝ) :
    ccmPrimeDeficitSignedWorkDensity t =
      -ccmPrimeDeficitIncoming t * normalizedLogError t := by
  unfold ccmPrimeDeficitSignedWorkDensity ccmPrimeDeficitIncoming normalizedLogError logError
  have hexp : Real.exp (-t) = Real.exp (-t / 2) * Real.exp (-t / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [hexp]
  ring

/-- Exact completion of the square for the signed work density:
`2 W(t) = (1/2) E(t) + 2 Ẽ(t)² − (1/2) (ccmPrimeDeficitIncoming t + 2 Ẽ(t))²`. -/
theorem two_mul_ccmPrimeDeficitSignedWorkDensity_eq (t : ℝ) :
    2 * ccmPrimeDeficitSignedWorkDensity t =
      1 / 2 * ccmPrimeDeficitCriticalEnergy t + 2 * normalizedLogError t ^ 2 -
        1 / 2 * (ccmPrimeDeficitIncoming t + 2 * normalizedLogError t) ^ 2 := by
  rw [ccmPrimeDeficitSignedWorkDensity_eq, ← ccmPrimeDeficitIncoming_sq]
  ring

/-- Pointwise upper bound on the signed work density:
`2 W(t) ≤ (1/2) E(t) + 2 Ẽ(t)²`. -/
theorem two_mul_ccmPrimeDeficitSignedWorkDensity_le (t : ℝ) :
    2 * ccmPrimeDeficitSignedWorkDensity t ≤
      1 / 2 * ccmPrimeDeficitCriticalEnergy t + 2 * normalizedLogError t ^ 2 := by
  rw [two_mul_ccmPrimeDeficitSignedWorkDensity_eq]
  linarith [sq_nonneg (ccmPrimeDeficitIncoming t + 2 * normalizedLogError t)]

/-- **Exact Hardy-type inequality for the critical prime-deficit energy.** On every interval
`[0, T]` (`T ≥ 0`), twice the terminal critical energy plus the integrated critical energy is
bounded by four times the Chebyshev mean-square band:
`2 * ccmPrimeDeficitCriticalEnergy T + ∫_{0}^T ccmPrimeDeficitCriticalEnergy t dt ≤ 4 * ∫_{0}^T normalizedLogError t ^ 2 dt`. -/
theorem two_mul_ccmPrimeDeficitCriticalEnergy_add_integral_le_band {T : ℝ} (hT : 0 ≤ T) :
    2 * ccmPrimeDeficitCriticalEnergy T +
        (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) ≤
      4 * ∫ t in Icc 0 T, normalizedLogError t ^ 2 := by
  have hbal := ccmPrimeDeficitCriticalEnergy_balance 0 T
  rw [ccmPrimeDeficitCriticalEnergy_zero, sub_zero] at hbal
  have hI_work : IntervalIntegrable (fun t => 2 * ccmPrimeDeficitSignedWorkDensity t) volume 0 T :=
    (intervalIntegrable_ccmPrimeDeficitSignedWorkDensity 0 T).const_mul 2
  have hI_crit : IntervalIntegrable ccmPrimeDeficitCriticalEnergy volume 0 T :=
    continuous_ccmPrimeDeficitCriticalEnergy.intervalIntegrable 0 T
  have hI_err : IntervalIntegrable (fun t => normalizedLogError t ^ 2) volume 0 T := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT]
    exact integrableOn_normalizedLogError_sq T
  have hle : (∫ t in (0 : ℝ)..T, 2 * ccmPrimeDeficitSignedWorkDensity t) ≤
      ∫ t in (0 : ℝ)..T,
        (1 / 2 * ccmPrimeDeficitCriticalEnergy t + 2 * normalizedLogError t ^ 2) :=
    intervalIntegral.integral_mono hT hI_work
      ((hI_crit.const_mul (1 / 2)).add (hI_err.const_mul 2))
      two_mul_ccmPrimeDeficitSignedWorkDensity_le
  rw [intervalIntegral.integral_const_mul] at hle
  rw [intervalIntegral.integral_add (hI_crit.const_mul (1 / 2)) (hI_err.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hle
  have hconv1 : (∫ t in (0 : ℝ)..T, ccmPrimeDeficitCriticalEnergy t) =
      ∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t := by
    rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]
  have hconv2 : (∫ t in (0 : ℝ)..T, normalizedLogError t ^ 2) =
      ∫ t in Icc 0 T, normalizedLogError t ^ 2 := by
    rw [intervalIntegral.integral_of_le hT, integral_Icc_eq_integral_Ioc]
  rw [hconv1] at hbal hle
  rw [hconv2] at hle
  linarith

/-- Pointwise bound on `ccmPrimeDeficitCriticalEnergy T` by twice the mean-square band. -/
theorem ccmPrimeDeficitCriticalEnergy_le_two_mul_band {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitCriticalEnergy T ≤ 2 * ∫ t in Icc 0 T, normalizedLogError t ^ 2 := by
  have h1 := two_mul_ccmPrimeDeficitCriticalEnergy_add_integral_le_band hT
  have h2 : 0 ≤ ∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t :=
    setIntegral_nonneg measurableSet_Icc fun t _ => ccmPrimeDeficitCriticalEnergy_nonneg t
  linarith

/-- Cumulative bound on `∫_0^T ccmPrimeDeficitCriticalEnergy t dt` by four times the mean-square
band. -/
theorem integral_ccmPrimeDeficitCriticalEnergy_le_four_mul_band {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) ≤
      4 * ∫ t in Icc 0 T, normalizedLogError t ^ 2 := by
  have h1 := two_mul_ccmPrimeDeficitCriticalEnergy_add_integral_le_band hT
  have h2 := ccmPrimeDeficitCriticalEnergy_nonneg T
  linarith

/-! ## §2. Windowed AM–GM bridge from local `L²` energy to `stationaryPacket splineProbe` -/

/-- On `[τ − 4, τ + 4]`, for any continuous `g : ℝ → ℝ` and `μ > 0`,
`∫_{τ−4}^{τ+4} |g(t)| dt ≤ 4 μ + (∫_{τ−4}^{τ+4} g(t)² dt) / (2 μ)`. -/
theorem integral_abs_Icc_le_of_pos {g : ℝ → ℝ} (hg : Continuous g) (τ : ℝ) {μ : ℝ} (hμ : 0 < μ) :
    (∫ t in Icc (τ - 4) (τ + 4), |g t|) ≤
      4 * μ + (∫ t in Icc (τ - 4) (τ + 4), g t ^ 2) / (2 * μ) := by
  set s := Icc (τ - 4) (τ + 4)
  have hI1 : IntegrableOn (fun _ : ℝ => μ / 2) s := continuous_const.integrableOn_Icc
  have hI2 : IntegrableOn (fun t : ℝ => g t ^ 2 / (2 * μ)) s :=
    ((hg.pow 2).div_const (2 * μ)).integrableOn_Icc
  have hle : (∫ t in s, |g t|) ≤ ∫ t in s, (μ / 2 + g t ^ 2 / (2 * μ)) := by
    refine setIntegral_mono_on hg.abs.integrableOn_Icc (hI1.add hI2) measurableSet_Icc fun t _ => ?_
    have hdiv : μ / 2 + g t ^ 2 / (2 * μ) = (μ ^ 2 + g t ^ 2) / (2 * μ) := by
      field_simp
    rw [hdiv, le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (μ - |g t|), sq_abs (g t)]
  rw [integral_add hI1 hI2, setIntegral_const, Real.volume_real_Icc_of_le (by linarith),
    smul_eq_mul, integral_div] at hle
  linarith

/-- Specialization of `integral_abs_Icc_le_of_pos` to `μ = e^{βτ}`: a local `L²` bound
`∫_{τ−4}^{τ+4} g(t)² dt ≤ C e^{2βτ}` gives `∫_{τ−4}^{τ+4} |g(t)| dt ≤ (4 + C/2) e^{βτ}`. -/
theorem integral_abs_Icc_le_exp_of_sq_le {g : ℝ → ℝ} (hg : Continuous g) {β C τ : ℝ}
    (hsq : (∫ t in Icc (τ - 4) (τ + 4), g t ^ 2) ≤ C * Real.exp (2 * β * τ)) :
    (∫ t in Icc (τ - 4) (τ + 4), |g t|) ≤ (4 + C / 2) * Real.exp (β * τ) := by
  set μ := Real.exp (β * τ)
  have hμ : 0 < μ := Real.exp_pos _
  have h1 := integral_abs_Icc_le_of_pos hg τ hμ
  have hexp : Real.exp (2 * β * τ) = μ * μ := by
    simp only [μ, ← Real.exp_add]; congr 1; ring
  have hdiv : (∫ t in Icc (τ - 4) (τ + 4), g t ^ 2) / (2 * μ) ≤ C / 2 * μ := by
    rw [div_le_iff₀ (by positivity)]
    rw [hexp] at hsq
    linarith
  linarith

/-- **Local window critical-energy bound implies `XiZeroHalfPlaneBound β`.** If
`∫_{τ−4}^{τ+4} ccmPrimeDeficitCriticalEnergy t dt ≤ C e^{2βτ}` eventually (`β ≥ 0`), then
`XiZeroHalfPlaneBound β` holds. -/
theorem xiZeroHalfPlaneBound_of_local_criticalEnergy_le {β : ℝ} (hβ : 0 ≤ β)
    (hloc : ∃ T C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, T ≤ τ →
      (∫ t in Icc (τ - 4) (τ + 4), ccmPrimeDeficitCriticalEnergy t) ≤
        C * Real.exp (2 * β * τ)) :
    XiZeroHalfPlaneBound β := by
  obtain ⟨T, C, hC0, hC⟩ := hloc
  rw [xiZeroHalfPlaneBound_iff_splineProbe_packet_upper hβ]
  refine ⟨max T 5, 4 * Real.exp 2 + 13 / 8 * Real.exp 4 * (4 + C / 2), fun τ hτ => ?_⟩
  have hτ4 : 4 < τ := by linarith [le_max_right T 5]
  have hτ0 : 0 ≤ τ := by linarith
  have hsq : (∫ t in Icc (τ - 4) (τ + 4), ccmPrimeDeficitIncoming t ^ 2) ≤
      C * Real.exp (2 * β * τ) := by
    simp only [ccmPrimeDeficitIncoming_sq]
    exact hC τ (le_of_max_le_left hτ)
  have hL1 := integral_abs_Icc_le_exp_of_sq_le continuous_ccmPrimeDeficitIncoming hsq
  have hpkt := abs_stationaryPacket_splineProbe_le_local_incoming hτ4
  have hexp1 : Real.exp (2 - τ / 2) ≤ Real.exp 2 * Real.exp (β * τ) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc stationaryPacket splineProbe τ
      ≤ |stationaryPacket splineProbe τ| := le_abs_self _
    _ ≤ 4 * Real.exp (2 - τ / 2) +
          13 / 8 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |ccmPrimeDeficitIncoming t| := hpkt
    _ ≤ 4 * (Real.exp 2 * Real.exp (β * τ)) +
          13 / 8 * Real.exp 4 * ((4 + C / 2) * Real.exp (β * τ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hexp1 (by norm_num))
          (mul_le_mul_of_nonneg_left hL1 (by positivity))
    _ = (4 * Real.exp 2 + 13 / 8 * Real.exp 4 * (4 + C / 2)) * Real.exp (β * τ) := by ring

/-- **Local window outgoing-flux bound implies `XiZeroHalfPlaneBound β`.** If
`∫_{τ−4}^{τ+4} (ccmPrimeDeficitOutgoing t)² dt ≤ C e^{2βτ}` eventually (`β ≥ 0`), then
`XiZeroHalfPlaneBound β` holds. -/
theorem xiZeroHalfPlaneBound_of_local_outgoing_sq_le {β : ℝ} (hβ : 0 ≤ β)
    (hloc : ∃ T C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, T ≤ τ →
      (∫ t in Icc (τ - 4) (τ + 4), ccmPrimeDeficitOutgoing t ^ 2) ≤
        C * Real.exp (2 * β * τ)) :
    XiZeroHalfPlaneBound β := by
  obtain ⟨T, C, hC0, hC⟩ := hloc
  rw [xiZeroHalfPlaneBound_iff_splineProbe_packet_upper hβ]
  refine ⟨max T 5, 4 * Real.exp 2 + 9 / 8 * Real.exp 4 * (4 + C / 2), fun τ hτ => ?_⟩
  have hτ4 : 4 < τ := by linarith [le_max_right T 5]
  have hτ0 : 0 ≤ τ := by linarith
  have hL1 := integral_abs_Icc_le_exp_of_sq_le continuous_ccmPrimeDeficitOutgoing
    (hC τ (le_of_max_le_left hτ))
  have hpkt := abs_stationaryPacket_splineProbe_le_local_outgoing hτ4
  have hexp1 : Real.exp (2 - τ / 2) ≤ Real.exp 2 * Real.exp (β * τ) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc stationaryPacket splineProbe τ
      ≤ |stationaryPacket splineProbe τ| := le_abs_self _
    _ ≤ 4 * Real.exp (2 - τ / 2) +
          9 / 8 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |ccmPrimeDeficitOutgoing t| := hpkt
    _ ≤ 4 * (Real.exp 2 * Real.exp (β * τ)) +
          9 / 8 * Real.exp 4 * ((4 + C / 2) * Real.exp (β * τ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hexp1 (by norm_num))
          (mul_le_mul_of_nonneg_left hL1 (by positivity))
    _ = (4 * Real.exp 2 + 9 / 8 * Real.exp 4 * (4 + C / 2)) * Real.exp (β * τ) := by ring

/-- **Local window Weil-lag energy bound implies `XiZeroHalfPlaneBound β`.** If
`∫_{τ−4}^{τ+4} (weilLagFunctionReal t)² dt ≤ C e^{2βτ}` eventually (`β ≥ 0`), then
`XiZeroHalfPlaneBound β` holds. -/
theorem xiZeroHalfPlaneBound_of_local_weilLag_sq_le {β : ℝ} (hβ : 0 ≤ β)
    (hloc : ∃ T C : ℝ, 0 ≤ C ∧ ∀ τ : ℝ, T ≤ τ →
      (∫ t in Icc (τ - 4) (τ + 4), weilLagFunctionReal t ^ 2) ≤
        C * Real.exp (2 * β * τ)) :
    XiZeroHalfPlaneBound β := by
  obtain ⟨T, C, hC0, hC⟩ := hloc
  rw [xiZeroHalfPlaneBound_iff_splineProbe_packet_upper hβ]
  refine ⟨max T 5, 13 * Real.exp 6 + 9 / 8 * Real.exp 4 * (4 + C / 2), fun τ hτ => ?_⟩
  have hτ4 : 4 < τ := by linarith [le_max_right T 5]
  have hτ0 : 0 ≤ τ := by linarith
  have hL1 := integral_abs_Icc_le_exp_of_sq_le continuous_weilLagFunctionReal
    (hC τ (le_of_max_le_left hτ))
  have hpkt := abs_stationaryPacket_splineProbe_le_local_weilLag hτ4
  have hexp1 : Real.exp (6 - τ / 2) ≤ Real.exp 6 * Real.exp (β * τ) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith)
  calc stationaryPacket splineProbe τ
      ≤ |stationaryPacket splineProbe τ| := le_abs_self _
    _ ≤ 13 * Real.exp (6 - τ / 2) +
          9 / 8 * Real.exp 4 * ∫ t in Icc (τ - 4) (τ + 4), |weilLagFunctionReal t| := hpkt
    _ ≤ 13 * (Real.exp 6 * Real.exp (β * τ)) +
          9 / 8 * Real.exp 4 * ((4 + C / 2) * Real.exp (β * τ)) :=
        add_le_add (mul_le_mul_of_nonneg_left hexp1 (by norm_num))
          (mul_le_mul_of_nonneg_left hL1 (by positivity))
    _ = (13 * Real.exp 6 + 9 / 8 * Real.exp 4 * (4 + C / 2)) * Real.exp (β * τ) := by ring

/-! ## §3. Cumulative and pointwise energy rate equivalences for `zetaZeroWidth` -/

/-- The cumulative critical prime-deficit energy grows at most like `e^{2βT}`. -/
def CriticalDeficitEnergyRate (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
    (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) ≤ C * Real.exp (2 * β * T)

/-- The pointwise critical prime-deficit energy grows at most like `e^{2βT}`. -/
def CriticalDeficitPointwiseRate (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
    ccmPrimeDeficitCriticalEnergy T ≤ C * Real.exp (2 * β * T)

/-- The cumulative outgoing prime-deficit flux energy grows at most like `e^{2βT}`. -/
def OutgoingDeficitFluxRate (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
    (∫ t in Icc 0 T, ccmPrimeDeficitOutgoing t ^ 2) ≤ C * Real.exp (2 * β * T)

/-- The cumulative Weil-lag energy grows at most like `e^{2βT}`. -/
def WeilLagEnergyRate (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
    (∫ t in Icc 0 T, weilLagFunctionReal t ^ 2) ≤ C * Real.exp (2 * β * T)

/-- A mean-square band of rate `β` implies a cumulative critical-deficit energy rate `β` (with
constant `4 C`). -/
theorem criticalDeficitEnergyRate_of_meanSquareBandRate {β : ℝ} (h : MeanSquareBandRate β) :
    CriticalDeficitEnergyRate β := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨4 * C, by positivity, fun T hT => ?_⟩
  calc ∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t
      ≤ 4 * ∫ t in Icc 0 T, normalizedLogError t ^ 2 :=
        integral_ccmPrimeDeficitCriticalEnergy_le_four_mul_band hT
    _ ≤ 4 * (C * Real.exp (2 * β * T)) :=
        mul_le_mul_of_nonneg_left (hC T hT) (by norm_num)
    _ = 4 * C * Real.exp (2 * β * T) := by ring

/-- A mean-square band of rate `β` implies a pointwise critical-deficit energy rate `β` (with
constant `2 C`). -/
theorem criticalDeficitPointwiseRate_of_meanSquareBandRate {β : ℝ} (h : MeanSquareBandRate β) :
    CriticalDeficitPointwiseRate β := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨2 * C, by positivity, fun T hT => ?_⟩
  calc ccmPrimeDeficitCriticalEnergy T
      ≤ 2 * ∫ t in Icc 0 T, normalizedLogError t ^ 2 :=
        ccmPrimeDeficitCriticalEnergy_le_two_mul_band hT
    _ ≤ 2 * (C * Real.exp (2 * β * T)) :=
        mul_le_mul_of_nonneg_left (hC T hT) (by norm_num)
    _ = 2 * C * Real.exp (2 * β * T) := by ring

/-- A cumulative critical-deficit energy rate `β ≥ 0` implies `XiZeroHalfPlaneBound β`. -/
theorem xiZeroHalfPlaneBound_of_criticalDeficitEnergyRate {β : ℝ} (hβ : 0 ≤ β)
    (h : CriticalDeficitEnergyRate β) : XiZeroHalfPlaneBound β := by
  obtain ⟨C, hC0, hC⟩ := h
  refine xiZeroHalfPlaneBound_of_local_criticalEnergy_le hβ
    ⟨4, C * Real.exp (8 * β), by positivity, fun τ hτ => ?_⟩
  have hsub : Icc (τ - 4) (τ + 4) ⊆ Icc 0 (τ + 4) :=
    Icc_subset_Icc (by linarith) le_rfl
  calc ∫ t in Icc (τ - 4) (τ + 4), ccmPrimeDeficitCriticalEnergy t
      ≤ ∫ t in Icc 0 (τ + 4), ccmPrimeDeficitCriticalEnergy t :=
        setIntegral_mono_set
          (continuous_ccmPrimeDeficitCriticalEnergy.integrableOn_Icc)
          (Eventually.of_forall ccmPrimeDeficitCriticalEnergy_nonneg)
          hsub.eventuallyLE
    _ ≤ C * Real.exp (2 * β * (τ + 4)) := hC (τ + 4) (by linarith)
    _ = C * Real.exp (8 * β) * Real.exp (2 * β * τ) := by
        rw [show 2 * β * (τ + 4) = 8 * β + 2 * β * τ by ring, Real.exp_add]
        ring

/-- A pointwise critical-deficit energy rate `β ≥ 0` bounds the local window integral on
`[τ − 4, τ + 4]` by `8 C e^{8β} e^{2βτ}`, hence implies `XiZeroHalfPlaneBound β`. -/
theorem xiZeroHalfPlaneBound_of_criticalDeficitPointwiseRate {β : ℝ} (hβ : 0 ≤ β)
    (h : CriticalDeficitPointwiseRate β) : XiZeroHalfPlaneBound β := by
  obtain ⟨C, hC0, hC⟩ := h
  refine xiZeroHalfPlaneBound_of_local_criticalEnergy_le hβ
    ⟨4, 8 * C * Real.exp (8 * β), by positivity, fun τ hτ => ?_⟩
  have hle : (∫ t in Icc (τ - 4) (τ + 4), ccmPrimeDeficitCriticalEnergy t) ≤
      ∫ _t in Icc (τ - 4) (τ + 4), (C * Real.exp (2 * β * (τ + 4)) : ℝ) := by
    refine setIntegral_mono_on
      continuous_ccmPrimeDeficitCriticalEnergy.integrableOn_Icc
      continuous_const.integrableOn_Icc measurableSet_Icc fun t ht => ?_
    calc ccmPrimeDeficitCriticalEnergy t
        ≤ C * Real.exp (2 * β * t) := hC t (by linarith [ht.1])
      _ ≤ C * Real.exp (2 * β * (τ + 4)) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 (by linarith))) hC0
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at hle
  calc ∫ t in Icc (τ - 4) (τ + 4), ccmPrimeDeficitCriticalEnergy t
      ≤ (τ + 4 - (τ - 4)) * (C * Real.exp (2 * β * (τ + 4))) := hle
    _ = 8 * C * Real.exp (8 * β) * Real.exp (2 * β * τ) := by
        rw [show τ + 4 - (τ - 4) = 8 by ring,
          show 2 * β * (τ + 4) = 8 * β + 2 * β * τ by ring, Real.exp_add]
        ring

/-- An outgoing prime-deficit flux rate `β ≥ 0` implies a cumulative critical-deficit energy rate
`β` (by `ccmPrimeDeficitCriticalEnergy_integral_le_outgoing`), and hence `XiZeroHalfPlaneBound β`. -/
theorem criticalDeficitEnergyRate_of_outgoingDeficitFluxRate {β : ℝ} (hβ : 0 ≤ β)
    (h : OutgoingDeficitFluxRate β) : CriticalDeficitEnergyRate β := by
  obtain ⟨C, hC0, hC⟩ := h
  refine ⟨C + (Real.eulerMascheroniConstant + 1) ^ 2, by positivity, fun T hT => ?_⟩
  have h1 := ccmPrimeDeficitCriticalEnergy_integral_le_outgoing T
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc] at h1
  have hexp : 1 ≤ Real.exp (2 * β * T) := Real.one_le_exp (by positivity)
  have h2 := hC T hT
  nlinarith [sq_nonneg (Real.eulerMascheroniConstant + 1)]

/-- A cumulative Weil-lag energy rate `β ≥ 0` implies a cumulative critical-deficit energy rate `β`
(by `ccmPrimeDeficitCriticalEnergy_integral_le_weilLag_sq`), and hence `XiZeroHalfPlaneBound β`. -/
theorem criticalDeficitEnergyRate_of_weilLagEnergyRate {β : ℝ} (hβ : 0 ≤ β)
    (h : WeilLagEnergyRate β) : CriticalDeficitEnergyRate β := by
  obtain ⟨C, hC0, hC⟩ := h
  set K := 2 * (|Real.log (2 * Real.pi)| + 1) ^ 2 + (Real.eulerMascheroniConstant + 1) ^ 2
  have hK0 : 0 ≤ K := by positivity
  refine ⟨2 * C + K, by positivity, fun T hT => ?_⟩
  have h1 := ccmPrimeDeficitCriticalEnergy_integral_le_weilLag_sq hT
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc] at h1
  have hexp : 1 ≤ Real.exp (2 * β * T) := Real.one_le_exp (by positivity)
  have h2 := hC T hT
  nlinarith

/-- **The cumulative critical-deficit energy spectrum is the zero width.** For `0 ≤ σ < 1/2`,
`XiZeroHalfPlaneBound σ` holds iff `CriticalDeficitEnergyRate β` holds for every `β > σ`. -/
theorem xiZeroHalfPlaneBound_iff_forall_criticalDeficitEnergyRate {σ : ℝ} (hσ : 0 ≤ σ)
    (hσ' : σ < 1 / 2) :
    XiZeroHalfPlaneBound σ ↔ ∀ β : ℝ, σ < β → CriticalDeficitEnergyRate β := by
  constructor
  · intro hXi β hβ
    exact criticalDeficitEnergyRate_of_meanSquareBandRate
      ((xiZeroHalfPlaneBound_iff_meanSquareBandRate hσ hσ').mp hXi β hβ)
  · intro h
    rw [← zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ]
    by_contra hlt
    rw [not_le] at hlt
    set β := (σ + zetaZeroWidth) / 2
    have hβσ : σ < β := by simp only [β]; linarith
    have hβ0 : 0 ≤ β := by linarith
    have hXiβ := xiZeroHalfPlaneBound_of_criticalDeficitEnergyRate hβ0 (h β hβσ)
    have hw := (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hβ0).mpr hXiβ
    simp only [β] at hw
    linarith

/-- **The pointwise critical-deficit energy spectrum is the zero width.** For `0 ≤ σ < 1/2`,
`XiZeroHalfPlaneBound σ` holds iff `CriticalDeficitPointwiseRate β` holds for every `β > σ`. -/
theorem xiZeroHalfPlaneBound_iff_forall_criticalDeficitPointwiseRate {σ : ℝ} (hσ : 0 ≤ σ)
    (hσ' : σ < 1 / 2) :
    XiZeroHalfPlaneBound σ ↔ ∀ β : ℝ, σ < β → CriticalDeficitPointwiseRate β := by
  constructor
  · intro hXi β hβ
    exact criticalDeficitPointwiseRate_of_meanSquareBandRate
      ((xiZeroHalfPlaneBound_iff_meanSquareBandRate hσ hσ').mp hXi β hβ)
  · intro h
    rw [← zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ]
    by_contra hlt
    rw [not_le] at hlt
    set β := (σ + zetaZeroWidth) / 2
    have hβσ : σ < β := by simp only [β]; linarith
    have hβ0 : 0 ≤ β := by linarith
    have hXiβ := xiZeroHalfPlaneBound_of_criticalDeficitPointwiseRate hβ0 (h β hβσ)
    have hw := (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hβ0).mpr hXiβ
    simp only [β] at hw
    linarith

/-- `zetaZeroWidth ≤ σ` iff `CriticalDeficitEnergyRate β` holds for every `β > σ` (`0 ≤ σ < 1/2`). -/
theorem zetaZeroWidth_le_iff_forall_criticalDeficitEnergyRate {σ : ℝ} (hσ : 0 ≤ σ)
    (hσ' : σ < 1 / 2) :
    zetaZeroWidth ≤ σ ↔ ∀ β : ℝ, σ < β → CriticalDeficitEnergyRate β :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (xiZeroHalfPlaneBound_iff_forall_criticalDeficitEnergyRate hσ hσ')

/-- `zetaZeroWidth ≤ σ` iff `CriticalDeficitPointwiseRate β` holds for every `β > σ`
(`0 ≤ σ < 1/2`). -/
theorem zetaZeroWidth_le_iff_forall_criticalDeficitPointwiseRate {σ : ℝ} (hσ : 0 ≤ σ)
    (hσ' : σ < 1 / 2) :
    zetaZeroWidth ≤ σ ↔ ∀ β : ℝ, σ < β → CriticalDeficitPointwiseRate β :=
  (zetaZeroWidth_le_iff_xiZeroHalfPlaneBound hσ).trans
    (xiZeroHalfPlaneBound_iff_forall_criticalDeficitPointwiseRate hσ hσ')

/-- **RH is every subexponential critical-deficit energy rate.** -/
theorem riemannHypothesis_iff_forall_criticalDeficitEnergyRate :
    RiemannHypothesis ↔ ∀ β : ℝ, 0 < β → CriticalDeficitEnergyRate β := by
  rw [_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero]
  exact xiZeroHalfPlaneBound_iff_forall_criticalDeficitEnergyRate le_rfl (by norm_num)

/-- **RH is every subexponential pointwise critical-deficit energy rate.** -/
theorem riemannHypothesis_iff_forall_criticalDeficitPointwiseRate :
    RiemannHypothesis ↔ ∀ β : ℝ, 0 < β → CriticalDeficitPointwiseRate β := by
  rw [_root_.RHTower.riemannHypothesis_iff_xiZeroHalfPlaneBound_zero]
  exact xiZeroHalfPlaneBound_iff_forall_criticalDeficitPointwiseRate le_rfl (by norm_num)

/-- **RH is linear cumulative critical prime-deficit energy.** Under RH, the Hardy-type inequality
and Cramér's linear mean-square band give `∫_0^T ccmPrimeDeficitCriticalEnergy t dt ≤ C (1 + T)`
with no extra logarithmic factors; conversely, linear growth implies every subexponential rate and
hence RH. -/
theorem riemannHypothesis_iff_linear_criticalDeficitEnergy :
    RiemannHypothesis ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
        (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) ≤ C * (1 + T) := by
  constructor
  · intro hRH
    obtain ⟨C, hC0, hC⟩ := exists_meanSquare_band_of_riemannHypothesis hRH
    refine ⟨4 * C, by positivity, fun T hT => ?_⟩
    calc ∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t
        ≤ 4 * ∫ t in Icc 0 T, normalizedLogError t ^ 2 :=
          integral_ccmPrimeDeficitCriticalEnergy_le_four_mul_band hT
      _ ≤ 4 * (C * (1 + T)) := mul_le_mul_of_nonneg_left (hC T hT) (by norm_num)
      _ = 4 * C * (1 + T) := by ring
  · rintro ⟨C, hC0, hlin⟩
    rw [riemannHypothesis_iff_forall_criticalDeficitEnergyRate]
    intro β hβ
    refine ⟨C * (1 + 1 / (2 * β)), by positivity, fun T hT => ?_⟩
    have hT' : T ≤ Real.exp (2 * β * T) / (2 * β) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [Real.add_one_le_exp (2 * β * T)]
    have h1 : 1 ≤ Real.exp (2 * β * T) := Real.one_le_exp (by positivity)
    calc ∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t
        ≤ C * (1 + T) := hlin T hT
      _ ≤ C * (Real.exp (2 * β * T) + Real.exp (2 * β * T) / (2 * β)) :=
          mul_le_mul_of_nonneg_left (add_le_add h1 hT') hC0
      _ = C * (1 + 1 / (2 * β)) * Real.exp (2 * β * T) := by ring

/-- **Self-improvement of the critical prime-deficit energy.** If
`∫_0^T ccmPrimeDeficitCriticalEnergy t dt = O(e^{2βT})` for every `β > 0`, then
`∫_0^T ccmPrimeDeficitCriticalEnergy t dt = O(1 + T)` linearly. -/
theorem exists_linear_criticalDeficitEnergy_of_forall_criticalDeficitEnergyRate
    (h : ∀ β : ℝ, 0 < β → CriticalDeficitEnergyRate β) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) ≤ C * (1 + T) :=
  riemannHypothesis_iff_linear_criticalDeficitEnergy.mp
    (riemannHypothesis_iff_forall_criticalDeficitEnergyRate.mpr h)

/-- **Subexponential cumulative Weil-lag energy implies `RiemannHypothesis`.** If
`∫_0^T (weilLagFunctionReal t)² dt = O(e^{2βT})` for every `β > 0` (in particular if the cumulative
Weil-lag energy grows polynomially or linearly), then `RiemannHypothesis` holds. -/
theorem riemannHypothesis_of_forall_weilLagEnergyRate
    (h : ∀ β : ℝ, 0 < β → WeilLagEnergyRate β) : RiemannHypothesis :=
  riemannHypothesis_iff_forall_criticalDeficitEnergyRate.mpr fun β hβ =>
    criticalDeficitEnergyRate_of_weilLagEnergyRate hβ.le (h β hβ)

/-- **Subexponential cumulative outgoing-flux energy implies `RiemannHypothesis`.** -/
theorem riemannHypothesis_of_forall_outgoingDeficitFluxRate
    (h : ∀ β : ℝ, 0 < β → OutgoingDeficitFluxRate β) : RiemannHypothesis :=
  riemannHypothesis_iff_forall_criticalDeficitEnergyRate.mpr fun β hβ =>
    criticalDeficitEnergyRate_of_outgoingDeficitFluxRate hβ.le (h β hβ)

/-! ## §4. Arithmetic reductions and polynomial-to-linear self-improvement -/

private theorem self_le_exp_two_mul {β T : ℝ} (hβ : 0 < β) :
    T ≤ 1 / (2 * β) * Real.exp (2 * β * T) := by
  rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
  linarith [Real.add_one_le_exp (2 * β * T)]

private theorem sq_le_exp_two_mul {β T : ℝ} (hβ : 0 < β) (hT : 0 ≤ T) :
    T ^ 2 ≤ 1 / β ^ 2 * Real.exp (2 * β * T) := by
  have h1 : β * T ≤ Real.exp (β * T) := by linarith [Real.add_one_le_exp (β * T)]
  have h2 : (β * T) ^ 2 ≤ Real.exp (β * T) ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have hexp : Real.exp (β * T) ^ 2 = Real.exp (2 * β * T) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  rw [hexp, mul_pow] at h2
  rw [one_div_mul_eq_div, le_div_iff₀ (by positivity)]
  linarith

private theorem cube_le_exp_two_mul {β T : ℝ} (hβ : 0 < β) (hT : 0 ≤ T) :
    T ^ 3 ≤ 27 / (8 * β ^ 3) * Real.exp (2 * β * T) := by
  have h1 : 2 / 3 * β * T ≤ Real.exp (2 / 3 * β * T) := by
    linarith [Real.add_one_le_exp (2 / 3 * β * T)]
  have h2 : (2 / 3 * β * T) ^ 3 ≤ Real.exp (2 / 3 * β * T) ^ 3 :=
    pow_le_pow_left₀ (by positivity) h1 3
  have hexp : Real.exp (2 / 3 * β * T) ^ 3 = Real.exp (2 * β * T) := by
    rw [pow_succ, sq, ← Real.exp_add, ← Real.exp_add]; congr 1; ring
  have hpow : (2 / 3 * β * T) ^ 3 = 8 / 27 * β ^ 3 * T ^ 3 := by ring
  rw [hexp, hpow] at h2
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

/-- **Unconditional upper bound on the coprime Möbius cross work.** Because
`ccmPrimeDeficitCriticalEnergy T ≥ 0` and
`|ccmPrimeDeficitCriticalEnergy T + ccmPrimeDeficitCoprimeCrossWork T| ≤ 49 / 4`, the coprime
cross work is uniformly bounded above by `49 / 4` for all `T ≥ 0`. -/
theorem ccmPrimeDeficitCoprimeCrossWork_le_forty_nine_fourths {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitCoprimeCrossWork T ≤ 49 / 4 := by
  have h1 := (abs_le.mp (abs_ccmPrimeDeficitCriticalEnergy_add_coprimeCrossWork_le hT)).2
  have h2 := ccmPrimeDeficitCriticalEnergy_nonneg T
  linarith

/-- **Two-sided sandwich between `ccmPrimeDeficitCriticalEnergy` and `-ccmPrimeDeficitCoprimeCrossWork`.**
For all `T ≥ 0`, `-ccmPrimeDeficitCoprimeCrossWork T` differs from
`ccmPrimeDeficitCriticalEnergy T` by at most `49 / 4`. -/
theorem neg_ccmPrimeDeficitCoprimeCrossWork_bounds {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitCriticalEnergy T - 49 / 4 ≤ -ccmPrimeDeficitCoprimeCrossWork T ∧
      -ccmPrimeDeficitCoprimeCrossWork T ≤ ccmPrimeDeficitCriticalEnergy T + 49 / 4 := by
  obtain ⟨hl, hu⟩ := abs_le.mp (abs_ccmPrimeDeficitCriticalEnergy_add_coprimeCrossWork_le hT)
  exact ⟨by linarith, by linarith⟩

/-- The negative coprime Möbius cross work `-ccmPrimeDeficitCoprimeCrossWork T` grows at most like
`e^{2βT}`. -/
def CoprimeCrossWorkLowerRate (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
    -ccmPrimeDeficitCoprimeCrossWork T ≤ C * Real.exp (2 * β * T)

/-- For `β ≥ 0`, `CriticalDeficitPointwiseRate β` is unconditionally equivalent to
`CoprimeCrossWorkLowerRate β`. -/
theorem criticalDeficitPointwiseRate_iff_coprimeCrossWorkLowerRate {β : ℝ} (hβ : 0 ≤ β) :
    CriticalDeficitPointwiseRate β ↔ CoprimeCrossWorkLowerRate β := by
  constructor
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C + 49 / 4, by positivity, fun T hT => ?_⟩
    have h1 := (neg_ccmPrimeDeficitCoprimeCrossWork_bounds hT).2
    have h2 := hC T hT
    have hexp : 1 ≤ Real.exp (2 * β * T) := Real.one_le_exp (by positivity)
    nlinarith
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C + 49 / 4, by positivity, fun T hT => ?_⟩
    have h1 := (neg_ccmPrimeDeficitCoprimeCrossWork_bounds hT).1
    have h2 := hC T hT
    have hexp : 1 ≤ Real.exp (2 * β * T) := Real.one_le_exp (by positivity)
    nlinarith

/-- `zetaZeroWidth ≤ σ` iff `CoprimeCrossWorkLowerRate β` holds for every `β > σ` (`0 ≤ σ < 1/2`). -/
theorem zetaZeroWidth_le_iff_forall_coprimeCrossWorkLowerRate {σ : ℝ} (hσ : 0 ≤ σ)
    (hσ' : σ < 1 / 2) :
    zetaZeroWidth ≤ σ ↔ ∀ β : ℝ, σ < β → CoprimeCrossWorkLowerRate β := by
  rw [zetaZeroWidth_le_iff_forall_criticalDeficitPointwiseRate hσ hσ']
  exact forall₂_congr fun β hβ =>
    criticalDeficitPointwiseRate_iff_coprimeCrossWorkLowerRate (hσ.trans hβ.le)

/-- **RH is every subexponential lower bound on the coprime Möbius cross work.** -/
theorem riemannHypothesis_iff_forall_coprimeCrossWorkLowerRate :
    RiemannHypothesis ↔ ∀ β : ℝ, 0 < β → CoprimeCrossWorkLowerRate β := by
  rw [riemannHypothesis_iff_forall_criticalDeficitPointwiseRate]
  exact forall₂_congr fun β hβ =>
    criticalDeficitPointwiseRate_iff_coprimeCrossWorkLowerRate hβ.le

/-- **Two-sided quadratic sandwich for the centered off-diagonal prime-entry energy.** For all
`T ≥ 0`,
`ccmPrimeEntryCenteredOffDiagonal T ≤ ∫_0^T ccmPrimeDeficitCriticalEnergy t dt ≤ ccmPrimeEntryCenteredOffDiagonal T + T² + 78 T + 50`. -/
theorem ccmPrimeEntryCenteredOffDiagonal_bounds {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeEntryCenteredOffDiagonal T ≤
        (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) ∧
      (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) ≤
        ccmPrimeEntryCenteredOffDiagonal T + T ^ 2 + 78 * T + 50 := by
  have heq := ccmPrimeDeficitCriticalEnergy_integral_eq_diagonal_add_centered hT
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc] at heq
  have h0 := ccmPrimeEntryDiagonal_nonneg hT
  have hq := ccmPrimeEntryDiagonal_le_quadratic hT
  exact ⟨by linarith, by linarith⟩

/-- The centered off-diagonal prime-entry energy grows at most like `e^{2βT}`. -/
def CenteredOffDiagonalRate (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
    ccmPrimeEntryCenteredOffDiagonal T ≤ C * Real.exp (2 * β * T)

/-- For `β > 0`, `CriticalDeficitEnergyRate β` is unconditionally equivalent to
`CenteredOffDiagonalRate β`. -/
theorem criticalDeficitEnergyRate_iff_centeredOffDiagonalRate {β : ℝ} (hβ : 0 < β) :
    CriticalDeficitEnergyRate β ↔ CenteredOffDiagonalRate β := by
  constructor
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C, hC0, fun T hT => (ccmPrimeEntryCenteredOffDiagonal_bounds hT).1.trans (hC T hT)⟩
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C + 1 / β ^ 2 + 78 * (1 / (2 * β)) + 50, by positivity, fun T hT => ?_⟩
    have h1 := (ccmPrimeEntryCenteredOffDiagonal_bounds hT).2
    have h2 := hC T hT
    have hT2 := sq_le_exp_two_mul hβ hT
    have hT1 := self_le_exp_two_mul hβ (T := T)
    have hT0 : 1 ≤ Real.exp (2 * β * T) := Real.one_le_exp (by positivity)
    linarith

/-- `zetaZeroWidth ≤ σ` iff `CenteredOffDiagonalRate β` holds for every `β > σ` (`0 ≤ σ < 1/2`). -/
theorem zetaZeroWidth_le_iff_forall_centeredOffDiagonalRate {σ : ℝ} (hσ : 0 ≤ σ)
    (hσ' : σ < 1 / 2) :
    zetaZeroWidth ≤ σ ↔ ∀ β : ℝ, σ < β → CenteredOffDiagonalRate β := by
  rw [zetaZeroWidth_le_iff_forall_criticalDeficitEnergyRate hσ hσ']
  exact forall₂_congr fun β hβ =>
    criticalDeficitEnergyRate_iff_centeredOffDiagonalRate (hσ.trans_lt hβ)

/-- **RH is a linear bound on `ccmPrimeEntryCenteredOffDiagonal`.** -/
theorem riemannHypothesis_iff_linear_centeredOffDiagonal :
    RiemannHypothesis ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
        ccmPrimeEntryCenteredOffDiagonal T ≤ C * (1 + T) := by
  rw [riemannHypothesis_iff_linear_criticalDeficitEnergy]
  constructor
  · rintro ⟨C, hC0, hC⟩
    exact ⟨C, hC0, fun T hT => (ccmPrimeEntryCenteredOffDiagonal_bounds hT).1.trans (hC T hT)⟩
  · rintro ⟨C, hC0, hC⟩
    refine riemannHypothesis_iff_linear_criticalDeficitEnergy.mp ?_
    rw [riemannHypothesis_iff_forall_criticalDeficitEnergyRate]
    intro β hβ
    rw [criticalDeficitEnergyRate_iff_centeredOffDiagonalRate hβ]
    refine ⟨C * (1 + 1 / (2 * β)), by positivity, fun T hT => ?_⟩
    have h1 : 1 ≤ Real.exp (2 * β * T) := Real.one_le_exp (by positivity)
    have hT1 := self_le_exp_two_mul hβ (T := T)
    have h2 := hC T hT
    nlinarith

/-- **Quadratic-to-linear self-improvement for `ccmPrimeEntryCenteredOffDiagonal`.** A quadratic
upper bound `ccmPrimeEntryCenteredOffDiagonal T ≤ C (1 + T²)` is unconditionally equivalent to
`RiemannHypothesis` (and hence self-improves to `O(1 + T)`). -/
theorem riemannHypothesis_iff_quadratic_centeredOffDiagonal :
    RiemannHypothesis ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
        ccmPrimeEntryCenteredOffDiagonal T ≤ C * (1 + T ^ 2) := by
  constructor
  · intro hRH
    obtain ⟨C, hC0, hC⟩ := riemannHypothesis_iff_linear_centeredOffDiagonal.mp hRH
    refine ⟨2 * C, by positivity, fun T hT => ?_⟩
    have h1 := hC T hT
    have h2 : 1 + T ≤ 2 * (1 + T ^ 2) := by nlinarith [sq_nonneg (T - 1)]
    nlinarith
  · rintro ⟨C, hC0, hC⟩
    rw [riemannHypothesis_iff_forall_criticalDeficitEnergyRate]
    intro β hβ
    rw [criticalDeficitEnergyRate_iff_centeredOffDiagonalRate hβ]
    refine ⟨C * (1 + 1 / β ^ 2), by positivity, fun T hT => ?_⟩
    have h1 : 1 ≤ Real.exp (2 * β * T) := Real.one_le_exp (by positivity)
    have hT2 := sq_le_exp_two_mul hβ hT
    have h2 := hC T hT
    nlinarith

/-- **Two-sided cubic sandwich for the centered Euler-deformation curvature.** For all `T ≥ 0`,
`ccmPrimeDeficitCenteredEulerCurvature T ≤ ∫_0^T ccmPrimeDeficitCriticalEnergy t dt ≤ ccmPrimeDeficitCenteredEulerCurvature T + (T + 2)(T² / 2 + 30 T + 120)`. -/
theorem ccmPrimeDeficitCenteredEulerCurvature_bounds {T : ℝ} (hT : 0 ≤ T) :
    ccmPrimeDeficitCenteredEulerCurvature T ≤
        (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) ∧
      (∫ t in Icc 0 T, ccmPrimeDeficitCriticalEnergy t) ≤
        ccmPrimeDeficitCenteredEulerCurvature T +
          (T + 2) * (T ^ 2 / 2 + 30 * T + 120) := by
  obtain ⟨hl, hu⟩ := ccmPrimeDeficitCriticalEnergy_integral_sub_centeredEuler_bounds hT
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc] at hl hu
  exact ⟨by linarith, by linarith⟩

/-- The centered Euler-deformation curvature grows at most like `e^{2βT}`. -/
def CenteredEulerCurvatureRate (β : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
    ccmPrimeDeficitCenteredEulerCurvature T ≤ C * Real.exp (2 * β * T)

/-- For `β > 0`, `CriticalDeficitEnergyRate β` is unconditionally equivalent to
`CenteredEulerCurvatureRate β`. -/
theorem criticalDeficitEnergyRate_iff_centeredEulerCurvatureRate {β : ℝ} (hβ : 0 < β) :
    CriticalDeficitEnergyRate β ↔ CenteredEulerCurvatureRate β := by
  constructor
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C, hC0, fun T hT =>
      (ccmPrimeDeficitCenteredEulerCurvature_bounds hT).1.trans (hC T hT)⟩
  · rintro ⟨C, hC0, hC⟩
    refine ⟨C + 1 / 2 * (27 / (8 * β ^ 3)) + 31 * (1 / β ^ 2) + 180 * (1 / (2 * β)) + 240,
      by positivity, fun T hT => ?_⟩
    have h1 := (ccmPrimeDeficitCenteredEulerCurvature_bounds hT).2
    have hpoly : (T + 2) * (T ^ 2 / 2 + 30 * T + 120) =
        1 / 2 * T ^ 3 + 31 * T ^ 2 + 180 * T + 240 := by ring
    rw [hpoly] at h1
    have h2 := hC T hT
    have hT3 := cube_le_exp_two_mul hβ hT
    have hT2 := sq_le_exp_two_mul hβ hT
    have hT1 := self_le_exp_two_mul hβ (T := T)
    have hT0 : 1 ≤ Real.exp (2 * β * T) := Real.one_le_exp (by positivity)
    linarith

/-- `zetaZeroWidth ≤ σ` iff `CenteredEulerCurvatureRate β` holds for every `β > σ`
(`0 ≤ σ < 1/2`). -/
theorem zetaZeroWidth_le_iff_forall_centeredEulerCurvatureRate {σ : ℝ} (hσ : 0 ≤ σ)
    (hσ' : σ < 1 / 2) :
    zetaZeroWidth ≤ σ ↔ ∀ β : ℝ, σ < β → CenteredEulerCurvatureRate β := by
  rw [zetaZeroWidth_le_iff_forall_criticalDeficitEnergyRate hσ hσ']
  exact forall₂_congr fun β hβ =>
    criticalDeficitEnergyRate_iff_centeredEulerCurvatureRate (hσ.trans_lt hβ)

/-- **RH is a linear bound on `ccmPrimeDeficitCenteredEulerCurvature`.** -/
theorem riemannHypothesis_iff_linear_centeredEulerCurvature :
    RiemannHypothesis ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
        ccmPrimeDeficitCenteredEulerCurvature T ≤ C * (1 + T) := by
  constructor
  · intro hRH
    obtain ⟨C, hC0, hC⟩ := riemannHypothesis_iff_linear_criticalDeficitEnergy.mp hRH
    exact ⟨C, hC0, fun T hT =>
      (ccmPrimeDeficitCenteredEulerCurvature_bounds hT).1.trans (hC T hT)⟩
  · rintro ⟨C, hC0, hC⟩
    rw [riemannHypothesis_iff_forall_criticalDeficitEnergyRate]
    intro β hβ
    rw [criticalDeficitEnergyRate_iff_centeredEulerCurvatureRate hβ]
    refine ⟨C * (1 + 1 / (2 * β)), by positivity, fun T hT => ?_⟩
    have h1 : 1 ≤ Real.exp (2 * β * T) := Real.one_le_exp (by positivity)
    have hT1 := self_le_exp_two_mul hβ (T := T)
    have h2 := hC T hT
    nlinarith

/-- **Cubic-to-linear self-improvement for `ccmPrimeDeficitCenteredEulerCurvature`.** A cubic upper
bound `ccmPrimeDeficitCenteredEulerCurvature T ≤ C (1 + T³)` is unconditionally equivalent to
`RiemannHypothesis` (and hence self-improves to `O(1 + T)`). -/
theorem riemannHypothesis_iff_cubic_centeredEulerCurvature :
    RiemannHypothesis ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
        ccmPrimeDeficitCenteredEulerCurvature T ≤ C * (1 + T ^ 3) := by
  constructor
  · intro hRH
    obtain ⟨C, hC0, hC⟩ := riemannHypothesis_iff_linear_centeredEulerCurvature.mp hRH
    refine ⟨2 * C, by positivity, fun T hT => ?_⟩
    have h1 := hC T hT
    have h2 : 1 + T ≤ 2 * (1 + T ^ 3) := by
      by_cases hT1 : T ≤ 1
      · have hT3 : 0 ≤ T ^ 3 := by positivity
        linarith
      · have hT1' : 1 ≤ T := le_of_not_ge hT1
        have hT2 : T ≤ T ^ 2 := by nlinarith
        have hT3 : T ^ 2 ≤ T ^ 3 := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hT1') (sq_nonneg T)]
        linarith
    nlinarith
  · rintro ⟨C, hC0, hC⟩
    rw [riemannHypothesis_iff_forall_criticalDeficitEnergyRate]
    intro β hβ
    rw [criticalDeficitEnergyRate_iff_centeredEulerCurvatureRate hβ]
    refine ⟨C * (1 + 27 / (8 * β ^ 3)), by positivity, fun T hT => ?_⟩
    have h1 : 1 ≤ Real.exp (2 * β * T) := Real.one_le_exp (by positivity)
    have hT3 := cube_le_exp_two_mul hβ hT
    have h2 := hC T hT
    nlinarith

/-- **Quadratic upper bound on chronological prime-entry work implies `RiemannHypothesis`.** -/
theorem riemannHypothesis_of_quadratic_chronologicalWork
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 0 ≤ T →
      ccmPrimeDeficitChronologicalWork T ≤ C * (1 + T ^ 2)) :
    RiemannHypothesis := by
  obtain ⟨C, hC0, hC⟩ := h
  rw [riemannHypothesis_iff_forall_criticalDeficitEnergyRate]
  intro β hβ
  refine ⟨2 * C * (1 + 1 / β ^ 2) + 1 / β ^ 2 + 78 * (1 / (2 * β)) + 52,
    by positivity, fun T hT => ?_⟩
  have h1 := ccmPrimeDeficitCausalStorage_add_energy_le_work hT
  rw [intervalIntegral.integral_of_le hT, ← integral_Icc_eq_integral_Ioc] at h1
  have h2 := ccmPrimeDeficitCausalStorage_nonneg T
  have h3 := hC T hT
  have hT2 := sq_le_exp_two_mul hβ hT
  have hT1 := self_le_exp_two_mul hβ (T := T)
  have hT0 : 1 ≤ Real.exp (2 * β * T) := Real.one_le_exp (by positivity)
  nlinarith

/-! ## §5. Unconditional Vinogradov–Korobov frontier bounds -/

/-- **Unconditional Vinogradov–Korobov bound for the critical prime-deficit energy.** For every
`0 < ex < 3 / 5`, there exist `C ≥ 0` and `κ > 0` such that eventually
`ccmPrimeDeficitCriticalEnergy T ≤ C * Real.exp (T - κ * T ^ ex)`. -/
theorem exists_eventually_ccmPrimeDeficitCriticalEnergy_le_vk
    {ex : ℝ} (h0 : 0 < ex) (h35 : ex < 3 / 5) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧
      ∀ᶠ T in atTop,
        ccmPrimeDeficitCriticalEnergy T ≤ C * Real.exp (T - κ * T ^ ex) := by
  obtain ⟨C, κ, hC, hκ, hvk⟩ := exists_eventually_abs_ccmLogChebyshevDeficitPrimitive_le_vk h0 h35
  refine ⟨C ^ 2, 2 * κ, by positivity, by positivity, ?_⟩
  filter_upwards [hvk] with T hT
  unfold ccmPrimeDeficitCriticalEnergy
  have hsq : ccmLogChebyshevDeficitPrimitive T ^ 2 ≤
      (C * Real.exp (T - κ * T ^ ex)) ^ 2 := by
    rw [← sq_abs (ccmLogChebyshevDeficitPrimitive T)]
    exact pow_le_pow_left₀ (abs_nonneg _) hT 2
  calc Real.exp (-T) * ccmLogChebyshevDeficitPrimitive T ^ 2
      ≤ Real.exp (-T) * (C * Real.exp (T - κ * T ^ ex)) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
    _ = C ^ 2 * (Real.exp (-T) * (Real.exp (T - κ * T ^ ex) * Real.exp (T - κ * T ^ ex))) := by
        ring
    _ = C ^ 2 * Real.exp (T - 2 * κ * T ^ ex) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

/-- **Unconditional Vinogradov–Korobov bound for the incoming prime-deficit amplitude.** For every
`0 < ex < 3 / 5`, there exist `C ≥ 0` and `κ > 0` such that eventually
`|ccmPrimeDeficitIncoming T| ≤ C * Real.exp (T / 2 - κ * T ^ ex)`. -/
theorem exists_eventually_abs_ccmPrimeDeficitIncoming_le_vk
    {ex : ℝ} (h0 : 0 < ex) (h35 : ex < 3 / 5) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧
      ∀ᶠ T in atTop,
        |ccmPrimeDeficitIncoming T| ≤ C * Real.exp (T / 2 - κ * T ^ ex) := by
  obtain ⟨C, κ, hC, hκ, hvk⟩ := exists_eventually_abs_ccmLogChebyshevDeficitPrimitive_le_vk h0 h35
  refine ⟨C, κ, hC, hκ, ?_⟩
  filter_upwards [hvk] with T hT
  unfold ccmPrimeDeficitIncoming
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  calc Real.exp (-T / 2) * |ccmLogChebyshevDeficitPrimitive T|
      ≤ Real.exp (-T / 2) * (C * Real.exp (T - κ * T ^ ex)) :=
        mul_le_mul_of_nonneg_left hT (Real.exp_pos _).le
    _ = C * (Real.exp (-T / 2) * Real.exp (T - κ * T ^ ex)) := by ring
    _ = C * Real.exp (T / 2 - κ * T ^ ex) := by
        rw [← Real.exp_add]
        congr 2
        ring

/-- **Unconditional Vinogradov–Korobov lower bound for the coprime Möbius cross work.** For every
`0 < ex < 3 / 5`, there exist `C ≥ 0` and `κ > 0` such that eventually
`-ccmPrimeDeficitCoprimeCrossWork T ≤ C * Real.exp (T - κ * T ^ ex)`. -/
theorem exists_eventually_neg_ccmPrimeDeficitCoprimeCrossWork_le_vk
    {ex : ℝ} (h0 : 0 < ex) (h35 : ex < 3 / 5) :
    ∃ C κ : ℝ, 0 ≤ C ∧ 0 < κ ∧
      ∀ᶠ T in atTop,
        -ccmPrimeDeficitCoprimeCrossWork T ≤ C * Real.exp (T - κ * T ^ ex) := by
  obtain ⟨C, κ, hC, hκ, hvk⟩ := exists_eventually_ccmPrimeDeficitCriticalEnergy_le_vk h0 h35
  have hsub : Tendsto (fun T : ℝ => T - κ * T ^ ex) atTop atTop := by
    have h1 : Tendsto (fun T : ℝ => T ^ (1 - ex) - κ) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).atTop_add tendsto_const_nhds
    have h2 : Tendsto (fun T : ℝ => T ^ ex * (T ^ (1 - ex) - κ)) atTop atTop :=
      (tendsto_rpow_atTop h0).atTop_mul_atTop₀ h1
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    rw [mul_sub, ← Real.rpow_add hT, add_sub_cancel, Real.rpow_one]
    ring
  refine ⟨C + 49 / 4, κ, by positivity, hκ, ?_⟩
  filter_upwards [hvk, eventually_ge_atTop (0 : ℝ),
    hsub.eventually_ge_atTop (0 : ℝ)] with T hT hT0 hpos
  have hb := (neg_ccmPrimeDeficitCoprimeCrossWork_bounds hT0).2
  have hexp : 1 ≤ Real.exp (T - κ * T ^ ex) := Real.one_le_exp hpos
  nlinarith

end

end GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
