import GaloisForLFunctions.HTGeometry.TwoProjectionHilbertSchmidtEnergy
import GaloisForLFunctions.HTGeometry.RectangularTraceNorm
import GaloisForLFunctions.RHTower.FrankensteinCCMRoutePBaseCubicGreenSourceBridge
import GaloisForLFunctions.RHTower.SourceHorizontalWoldBVCompleteSplitPrimitiveBudgetFirewall
import GaloisForLFunctions.RHTower.VonMangoldtGammaJetBoundaryConvergence
import GaloisForLFunctions.RHTower.SquaredXiChebyshevWindow
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMEisensteinActualFourierCoefficient
import GaloisForLFunctions.RHTower.VonMangoldtLineSeriesSwap
import GaloisForLFunctions.HTGeometry.DaiYoshikawa.SpectralZetaMellinSum
import GaloisForLFunctions.RHTower.ZetaUnitIntervalIntegrals
import GaloisForLFunctions.HTGeometry.NevanlinnaPickGramSplitting
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles
import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolApertureDefectFirstFlux

/-!
# Restricted-unitary cubic relative index

This module starts from the actual critical ideal boundary: a self-adjoint difference of two
orthogonal projections is only assumed Hilbert--Schmidt.  Its cubic power is nevertheless
Schatten one and splits exactly into the two oriented positive projection channels.  The scalar
source side is the literal natural-number von Mangoldt carrier of the Route-P base budget.

No divisor, zero ordinate, RH hypothesis, axiom, or finite computation occurs below.
-/

noncomputable section

namespace RHTower

open ContinuousLinearMap
open MeasureTheory Set
open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Difference of two orthogonal polarizations. -/
def restrictedProjectionDisplacement (R P : H →L[ℂ] H) : H →L[ℂ] H :=
  R - P

/-- First odd nuclear polynomial at the Hilbert--Schmidt boundary. -/
def restrictedProjectionCubicDefect (R P : H →L[ℂ] H) : H →L[ℂ] H :=
  restrictedProjectionDisplacement R P ^ 3

/-- Positive channel in which `R` exits the `P` polarization. -/
def restrictedProjectionPositiveChannel (R P : H →L[ℂ] H) : H →L[ℂ] H :=
  R * (1 - P) * R

/-- A difference of self-adjoint polarizations is self-adjoint. -/
theorem adjoint_restrictedProjectionDisplacement
    (R P : H →L[ℂ] H)
    (hR : ContinuousLinearMap.adjoint R = R)
    (hP : ContinuousLinearMap.adjoint P = P) :
    ContinuousLinearMap.adjoint (restrictedProjectionDisplacement R P) =
      restrictedProjectionDisplacement R P := by
  rw [restrictedProjectionDisplacement, ContinuousLinearMap.adjoint.map_sub, hR, hP]

/-- Two Hilbert--Schmidt factors make the square nuclear; the ideal law then makes the cubic
nuclear without strengthening the displacement to Schatten one. -/
theorem restrictedProjectionCubicDefect_memSchattenClass_one
    (R P : H →L[ℂ] H)
    (hDelta : (restrictedProjectionDisplacement R P).IsHilbertSchmidt) :
    MemSchattenClass 1 (restrictedProjectionCubicDefect R P) := by
  have hsqRect :=
    memRectSchattenClass_one_comp_of_hilbertSchmidt_unrestricted hDelta hDelta
  have hsq : MemSchattenClass 1
      ((restrictedProjectionDisplacement R P) ∘L
        restrictedProjectionDisplacement R P) :=
    (memRectSchattenClass_iff_memSchattenClass
      1 (restrictedProjectionDisplacement R P ∘L
        restrictedProjectionDisplacement R P)).mp hsqRect
  have hcube := memSchattenClass_one_comp_right hsq
    (restrictedProjectionDisplacement R P)
  simpa [restrictedProjectionCubicDefect, pow_succ, ContinuousLinearMap.mul_def] using hcube

/-- Cubing preserves self-adjointness of the projection displacement. -/
theorem adjoint_restrictedProjectionCubicDefect
    (R P : H →L[ℂ] H)
    (hR : ContinuousLinearMap.adjoint R = R)
    (hP : ContinuousLinearMap.adjoint P = P) :
    ContinuousLinearMap.adjoint (restrictedProjectionCubicDefect R P) =
      restrictedProjectionCubicDefect R P := by
  rw [restrictedProjectionCubicDefect, show (restrictedProjectionDisplacement R P) ^ 3 =
      ((restrictedProjectionDisplacement R P) ∘L
          restrictedProjectionDisplacement R P) ∘L
        restrictedProjectionDisplacement R P by
      simp [pow_succ, ContinuousLinearMap.mul_def]]
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    adjoint_restrictedProjectionDisplacement R P hR hP]
  ext x
  rfl

omit [CompleteSpace H] in
/-- Exact positive-channel decomposition `(R-P)^3 = R(1-P)R - P(1-R)P`. -/
theorem restrictedProjectionCubicDefect_eq_channels
    (R P : H →L[ℂ] H)
    (hR : IsIdempotentElem R)
    (hP : IsIdempotentElem P) :
    restrictedProjectionCubicDefect R P =
      restrictedProjectionPositiveChannel R P -
        restrictedProjectionPositiveChannel P R := by
  change (R - P) ^ 3 = R * (1 - P) * R - P * (1 - R) * P
  have hRR : R * R = R := hR
  have hPP : P * P = P := hP
  noncomm_ring [hRR, hPP]

omit [CompleteSpace H] in
/-- Orientation reversal negates the cubic defect exactly. -/
theorem restrictedProjectionCubicDefect_swap
    (R P : H →L[ℂ] H) :
    restrictedProjectionCubicDefect P R = -restrictedProjectionCubicDefect R P := by
  rw [restrictedProjectionCubicDefect, restrictedProjectionCubicDefect,
    restrictedProjectionDisplacement, restrictedProjectionDisplacement]
  noncomm_ring

/-- The natural-number source weight is exactly the unsquared von Mangoldt mass divided by the
cubic logarithmic clock. -/
theorem routePPrimeGammaBaseCubicWeight_eq_vonMangoldt (n : ℕ) :
    routePPrimeGammaBaseCubicWeight n =
      finiteVonMangoldtRealWeight n / (4 * Real.log n ^ 3) := by
  rw [routePPrimeGammaBaseCubicWeight, routePPrimeGammaCubicWeight,
    vonMangoldtInverseLogPowerWeight]
  norm_num
  ring

/-- Exact source identity and strict subunit bound for the complete cubic Route-P budget. -/
theorem restrictedUnitaryCubic_sourceBudget_closed :
    (∑' n : ℕ, routePPrimeGammaBaseCubicWeight n) =
        routePPrimitiveBaseCauchyCubicTraceBudget ∧
      routePPrimitiveBaseCauchyCubicTraceBudget < 1 := by
  exact ⟨tsum_routePPrimeGammaBaseCubicWeight_eq_budget,
    routePPrimitiveBaseCauchyCubicTraceBudget_lt_one⟩

/-! ## Exact safe-Euler Gamma clock -/

/-- Literal safe von-Mangoldt current on the natural-number carrier.  The factor
`finiteVonMangoldtRealWeight n` already contains the required `1 / n`. -/
def restrictedUnitarySafeEulerCurrent (t : ℝ) : ℝ :=
  ∑' n : ℕ, finiteVonMangoldtRealWeight n * Real.exp (-(Real.log n * t))

/-- Single natural-number summand of the cubic safe-Euler clock. -/
def restrictedUnitaryCubicClockTerm (n : ℕ) (t : ℝ) : ℝ :=
  t ^ 2 * (finiteVonMangoldtRealWeight n * Real.exp (-(Real.log n * t)))

/-- Exact one-frequency Gamma-clock integral. -/
theorem integral_restrictedUnitaryCubicClockTerm (n : ℕ) :
    (∫ t : ℝ in Ioi 0, restrictedUnitaryCubicClockTerm n t) =
      2 * vonMangoldtInverseLogPowerWeight 0 n := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n <;>
      simp [restrictedUnitaryCubicClockTerm, vonMangoldtInverseLogPowerWeight,
        finiteVonMangoldtRealWeight]
  · have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
    have hlog : 0 < Real.log n := Real.log_pos hnreal
    change (∫ t : ℝ in Ioi 0, t ^ 2 *
      (finiteVonMangoldtRealWeight n * Real.exp (-(Real.log n * t)))) = _
    rw [vonMangoldtInverseLogPowerWeight]
    rw [show (fun t : ℝ => t ^ 2 *
        (finiteVonMangoldtRealWeight n * Real.exp (-(Real.log n * t)))) =
      fun t : ℝ => finiteVonMangoldtRealWeight n *
        (t ^ 2 * Real.exp (-(Real.log n * t))) by
      funext t
      ring]
    rw [MeasureTheory.integral_const_mul,
      integral_pow_mul_exp_neg_mul_Ioi hlog 2]
    norm_num
    ring

/-- Every one-frequency cubic clock is integrable on the positive ray. -/
theorem integrableOn_restrictedUnitaryCubicClockTerm (n : ℕ) :
    IntegrableOn (restrictedUnitaryCubicClockTerm n) (Ioi 0) := by
  rcases lt_or_ge n 2 with hn | hn
  · have hw : finiteVonMangoldtRealWeight n = 0 := by
      interval_cases n
      · simp [finiteVonMangoldtRealWeight]
      · simp [finiteVonMangoldtRealWeight,
          ArithmeticFunction.vonMangoldt_apply_one]
    change IntegrableOn (fun t : ℝ => t ^ 2 *
      (finiteVonMangoldtRealWeight n * Real.exp (-(Real.log n * t)))) (Ioi 0)
    rw [hw]
    simp
  · have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
    have hlog : 0 < Real.log n := Real.log_pos hnreal
    have h := (integrableOn_pow_mul_exp_neg_mul_Ioi hlog 2).const_mul
      (finiteVonMangoldtRealWeight n)
    refine h.congr (Filter.Eventually.of_forall fun t => ?_)
    simp only [restrictedUnitaryCubicClockTerm]
    ring

/-- Positivity makes the integral of the norm equal to the exact Gamma-clock mass. -/
theorem integral_norm_restrictedUnitaryCubicClockTerm (n : ℕ) :
    (∫ t : ℝ in Ioi 0, ‖restrictedUnitaryCubicClockTerm n t‖) =
      2 * vonMangoldtInverseLogPowerWeight 0 n := by
  rw [show (fun t : ℝ => ‖restrictedUnitaryCubicClockTerm n t‖) =
      restrictedUnitaryCubicClockTerm n by
    funext t
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact mul_nonneg (sq_nonneg t)
      (mul_nonneg (finiteVonMangoldtRealWeight_nonneg n) (Real.exp_pos _).le)]
  exact integral_restrictedUnitaryCubicClockTerm n

/-- Absolute integral masses of the natural-number clock are summable. -/
theorem summable_integral_norm_restrictedUnitaryCubicClockTerm :
    Summable (fun n : ℕ => ∫ t : ℝ in Ioi 0,
      ‖restrictedUnitaryCubicClockTerm n t‖) := by
  apply (summable_vonMangoldtInverseLogPowerWeight 0).mul_left 2 |>.congr
  intro n
  rw [integral_norm_restrictedUnitaryCubicClockTerm]

/-- **Exact Gamma-clock source identity `(RUCRI.8)`.**  The complete Route-P budget is the
positive cubic moment of the literal unsquared von-Mangoldt current.  The proof performs the
actual Tonelli interchange; no finite truncation or numerical evaluation is used. -/
theorem integral_restrictedUnitarySafeEulerCurrent :
    (1 / 8 : ℝ) * (∫ t : ℝ in Ioi 0,
      t ^ 2 * restrictedUnitarySafeEulerCurrent t) =
      routePPrimitiveBaseCauchyCubicTraceBudget := by
  have hswap : (∫ t : ℝ in Ioi 0,
      ∑' n : ℕ, restrictedUnitaryCubicClockTerm n t) =
      ∑' n : ℕ, ∫ t : ℝ in Ioi 0,
        restrictedUnitaryCubicClockTerm n t := by
    exact GaloisForLFunctions.HTGeometry.integral_tsum_eq_tsum_integral_of_summable_integral_norm
      (μ := volume.restrict (Ioi 0))
      (fun n => integrableOn_restrictedUnitaryCubicClockTerm n)
      summable_integral_norm_restrictedUnitaryCubicClockTerm
  rw [show (fun t : ℝ => t ^ 2 * restrictedUnitarySafeEulerCurrent t) =
      fun t : ℝ => ∑' n : ℕ, restrictedUnitaryCubicClockTerm n t by
    funext t
    rw [restrictedUnitarySafeEulerCurrent]
    simp only [restrictedUnitaryCubicClockTerm]
    rw [tsum_mul_left]]
  rw [hswap]
  simp_rw [integral_restrictedUnitaryCubicClockTerm]
  rw [tsum_mul_left]
  rw [show (∑' n : ℕ, vonMangoldtInverseLogPowerWeight 0 n) =
      4 * routePPrimitiveBaseCauchyCubicTraceBudget by
    calc
      (∑' n : ℕ, vonMangoldtInverseLogPowerWeight 0 n) =
          ∑' n : ℕ, 4 * routePPrimeGammaBaseCubicWeight n := by
        apply tsum_congr
        intro n
        rw [routePPrimeGammaBaseCubicWeight_eq_vonMangoldt,
          vonMangoldtInverseLogPowerWeight]
        ring
      _ = 4 * ∑' n : ℕ, routePPrimeGammaBaseCubicWeight n := tsum_mul_left
      _ = 4 * routePPrimitiveBaseCauchyCubicTraceBudget := by
        rw [tsum_routePPrimeGammaBaseCubicWeight_eq_budget]]
  ring

/-! ## Gaussian Mellin subordination -/

def restrictedUnitaryGaussianPrimeCurrent (x : ℝ) : ℝ :=
  ∑' n : ℕ, finiteVonMangoldtRealWeight n *
    Real.exp (-(Real.pi * (n : ℝ) ^ 2 * x))
def restrictedUnitaryGaussianPrimeMellinTerm (t : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  x ^ (t / 2 - 1) *
    (finiteVonMangoldtRealWeight n * Real.exp (-(Real.pi * (n : ℝ) ^ 2 * x)))

theorem integral_restrictedUnitaryGaussianPrimeMellinTerm
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (∫ x : ℝ in Ioi 0, restrictedUnitaryGaussianPrimeMellinTerm t n x) =
      finiteVonMangoldtRealWeight n *
        (Real.Gamma (t / 2) / (Real.pi * (n : ℝ) ^ 2) ^ (t / 2)) := by
  rcases lt_or_ge n 2 with hn | hn
  · have hw : finiteVonMangoldtRealWeight n = 0 := by
      interval_cases n
      · simp [finiteVonMangoldtRealWeight]
      · simp [finiteVonMangoldtRealWeight,
          ArithmeticFunction.vonMangoldt_apply_one]
    simp [restrictedUnitaryGaussianPrimeMellinTerm, hw]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
    have hb : 0 < Real.pi * (n : ℝ) ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hnpos)
    have hs : 0 < t / 2 := by linarith
    rw [show (fun x : ℝ => restrictedUnitaryGaussianPrimeMellinTerm t n x) =
        fun x : ℝ => finiteVonMangoldtRealWeight n *
          (Real.exp (-((Real.pi * (n : ℝ) ^ 2) * x)) * x ^ (t / 2 - 1)) by
      funext x
      rw [restrictedUnitaryGaussianPrimeMellinTerm]
      ring]
    rw [MeasureTheory.integral_const_mul,
      GaloisForLFunctions.HTGeometry.DaiYoshikawa.integral_exp_neg_mul_rpow hb hs]

theorem integral_restrictedUnitaryGaussianPrimeMellinTerm_eq_safe
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (∫ x : ℝ in Ioi 0, restrictedUnitaryGaussianPrimeMellinTerm t n x) =
      (Real.Gamma (t / 2) / Real.pi ^ (t / 2)) *
        (finiteVonMangoldtRealWeight n * Real.exp (-(Real.log n * t))) := by
  rw [integral_restrictedUnitaryGaussianPrimeMellinTerm ht n]
  rcases lt_or_ge n 2 with hn | hn
  · have hw : finiteVonMangoldtRealWeight n = 0 := by
      interval_cases n
      · simp [finiteVonMangoldtRealWeight]
      · simp [finiteVonMangoldtRealWeight,
          ArithmeticFunction.vonMangoldt_apply_one]
    simp [hw]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
    have hpi : 0 < Real.pi ^ (t / 2) := Real.rpow_pos_of_pos Real.pi_pos _
    have hnexp : 0 < Real.exp (Real.log n * t) := Real.exp_pos _
    have hden : (Real.pi * (n : ℝ) ^ 2) ^ (t / 2) =
        Real.pi ^ (t / 2) * Real.exp (Real.log n * t) := by
      rw [Real.mul_rpow Real.pi_pos.le (sq_nonneg _),
        Real.rpow_def_of_pos (sq_pos_of_pos hnpos), Real.log_pow]
      congr 1
      ring
    rw [hden, show Real.exp (-(Real.log n * t)) =
        (Real.exp (Real.log n * t))⁻¹ by rw [Real.exp_neg]]
    field_simp

theorem restrictedUnitarySafeEulerTerm_eq_rpow
    {t : ℝ} (_ht : 0 < t) (n : ℕ) :
    finiteVonMangoldtRealWeight n * Real.exp (-(Real.log n * t)) =
      ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(1 + t)) := by
  rcases lt_or_ge n 2 with hn | hn
  · interval_cases n
    · simp [finiteVonMangoldtRealWeight]
    · simp [finiteVonMangoldtRealWeight,
        ArithmeticFunction.vonMangoldt_apply_one]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
    rw [finiteVonMangoldtRealWeight, Real.rpow_def_of_pos hnpos]
    have hinv : ((n : ℝ))⁻¹ = Real.exp (-Real.log n) := by
      rw [Real.exp_neg, Real.exp_log hnpos]
    rw [div_eq_mul_inv, hinv, mul_assoc, ← Real.exp_add]
    congr 2
    ring

theorem summable_restrictedUnitarySafeEulerTerm {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ =>
      finiteVonMangoldtRealWeight n * Real.exp (-(Real.log n * t))) := by
  exact (summable_vonMangoldt_mul_rpow (σ := 1 + t) (by linarith)).congr
    (fun n => (restrictedUnitarySafeEulerTerm_eq_rpow ht n).symm)

theorem integrableOn_restrictedUnitaryGaussianPrimeMellinTerm
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    IntegrableOn (restrictedUnitaryGaussianPrimeMellinTerm t n) (Ioi 0) := by
  rcases lt_or_ge n 2 with hn | hn
  · have hw : finiteVonMangoldtRealWeight n = 0 := by
      interval_cases n
      · simp [finiteVonMangoldtRealWeight]
      · simp [finiteVonMangoldtRealWeight,
          ArithmeticFunction.vonMangoldt_apply_one]
    rw [show restrictedUnitaryGaussianPrimeMellinTerm t n = 0 by
      funext x
      simp [restrictedUnitaryGaussianPrimeMellinTerm, hw]]
    exact integrableOn_zero
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hn)
    have hb : 0 < Real.pi * (n : ℝ) ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hnpos)
    have hs : 0 < t / 2 := by linarith
    have h :=
      (GaloisForLFunctions.HTGeometry.DaiYoshikawa.integrableOn_exp_neg_mul_rpow hb hs).const_mul
        (finiteVonMangoldtRealWeight n)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    rw [restrictedUnitaryGaussianPrimeMellinTerm]
    ring

theorem integral_norm_restrictedUnitaryGaussianPrimeMellinTerm
    {t : ℝ} (ht : 0 < t) (n : ℕ) :
    (∫ x : ℝ in Ioi 0, ‖restrictedUnitaryGaussianPrimeMellinTerm t n x‖) =
      (Real.Gamma (t / 2) / Real.pi ^ (t / 2)) *
        (finiteVonMangoldtRealWeight n * Real.exp (-(Real.log n * t))) := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact mul_nonneg (Real.rpow_nonneg hx.le _)
      (mul_nonneg (finiteVonMangoldtRealWeight_nonneg n) (Real.exp_pos _).le))]
  exact integral_restrictedUnitaryGaussianPrimeMellinTerm_eq_safe ht n

theorem summable_integral_norm_restrictedUnitaryGaussianPrimeMellinTerm
    {t : ℝ} (ht : 0 < t) :
    Summable (fun n : ℕ => ∫ x : ℝ in Ioi 0,
      ‖restrictedUnitaryGaussianPrimeMellinTerm t n x‖) := by
  apply (summable_restrictedUnitarySafeEulerTerm ht).mul_left
    (Real.Gamma (t / 2) / Real.pi ^ (t / 2)) |>.congr
  intro n
  rw [integral_norm_restrictedUnitaryGaussianPrimeMellinTerm ht n]

theorem integral_restrictedUnitaryGaussianPrimeCurrent
    {t : ℝ} (ht : 0 < t) :
    (∫ x : ℝ in Ioi 0,
      x ^ (t / 2 - 1) * restrictedUnitaryGaussianPrimeCurrent x) =
      (Real.Gamma (t / 2) / Real.pi ^ (t / 2)) *
        restrictedUnitarySafeEulerCurrent t := by
  have hswap :
      (∫ x : ℝ in Ioi 0,
        ∑' n : ℕ, restrictedUnitaryGaussianPrimeMellinTerm t n x) =
        ∑' n : ℕ, ∫ x : ℝ in Ioi 0,
          restrictedUnitaryGaussianPrimeMellinTerm t n x := by
    exact GaloisForLFunctions.HTGeometry.integral_tsum_eq_tsum_integral_of_summable_integral_norm
      (μ := volume.restrict (Ioi 0))
      (fun n => integrableOn_restrictedUnitaryGaussianPrimeMellinTerm ht n)
      (summable_integral_norm_restrictedUnitaryGaussianPrimeMellinTerm ht)
  rw [show (fun x : ℝ => x ^ (t / 2 - 1) * restrictedUnitaryGaussianPrimeCurrent x) =
      fun x : ℝ => ∑' n : ℕ, restrictedUnitaryGaussianPrimeMellinTerm t n x by
    funext x
    rw [restrictedUnitaryGaussianPrimeCurrent]
    simp only [restrictedUnitaryGaussianPrimeMellinTerm]
    rw [tsum_mul_left]]
  rw [hswap]
  simp_rw [integral_restrictedUnitaryGaussianPrimeMellinTerm_eq_safe ht]
  rw [restrictedUnitarySafeEulerCurrent]
  exact tsum_mul_left

theorem restrictedUnitarySafeEulerCurrent_eq_gaussianMellin
    {t : ℝ} (ht : 0 < t) :
    restrictedUnitarySafeEulerCurrent t =
      Real.pi ^ (t / 2) / Real.Gamma (t / 2) *
        (∫ x : ℝ in Ioi 0,
          x ^ (t / 2 - 1) * restrictedUnitaryGaussianPrimeCurrent x) := by
  rw [integral_restrictedUnitaryGaussianPrimeCurrent ht]
  have hpi : Real.pi ^ (t / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
  have hgamma : Real.Gamma (t / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  field_simp

def restrictedUnitaryGaussianContinuumCurrent (x : ℝ) : ℝ :=
  ∫ u : ℝ in Ici 1, Real.exp (-(Real.pi * u ^ 2 * x)) / u

def restrictedUnitaryGaussianContinuumJoint (t : ℝ) (p : ℝ × ℝ) : ℝ :=
  p.1 ^ (t / 2 - 1) * (Real.exp (-(Real.pi * p.2 ^ 2 * p.1)) / p.2)

theorem integral_restrictedUnitaryGaussianContinuumJoint_left
    {t u : ℝ} (ht : 0 < t) (hu : 1 ≤ u) :
    (∫ x : ℝ in Ioi 0, restrictedUnitaryGaussianContinuumJoint t (x, u)) =
      (Real.Gamma (t / 2) / Real.pi ^ (t / 2)) * u ^ (-(1 + t)) := by
  have hupos : 0 < u := zero_lt_one.trans_le hu
  have hb : 0 < Real.pi * u ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hupos)
  have hs : 0 < t / 2 := by linarith
  rw [show (fun x : ℝ => restrictedUnitaryGaussianContinuumJoint t (x, u)) =
      fun x : ℝ => u⁻¹ *
        (Real.exp (-((Real.pi * u ^ 2) * x)) * x ^ (t / 2 - 1)) by
    funext x
    rw [restrictedUnitaryGaussianContinuumJoint, div_eq_mul_inv]
    ring]
  rw [MeasureTheory.integral_const_mul,
    GaloisForLFunctions.HTGeometry.DaiYoshikawa.integral_exp_neg_mul_rpow hb hs]
  have hpi : Real.pi ^ (t / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
  have huexp : Real.exp (Real.log u * t) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hden : (Real.pi * u ^ 2) ^ (t / 2) =
      Real.pi ^ (t / 2) * Real.exp (Real.log u * t) := by
    rw [Real.mul_rpow Real.pi_pos.le (sq_nonneg _),
      Real.rpow_def_of_pos (sq_pos_of_pos hupos), Real.log_pow]
    congr 1
    ring
  have hrpow : u ^ (-(1 + t)) = u⁻¹ * (Real.exp (Real.log u * t))⁻¹ := by
    rw [Real.rpow_def_of_pos hupos]
    have huinv : u⁻¹ = Real.exp (-Real.log u) := by
      rw [Real.exp_neg, Real.exp_log hupos]
    rw [huinv, ← Real.exp_neg]
    rw [← Real.exp_add]
    congr 2
    ring
  rw [hden, hrpow]
  field_simp

theorem integral_norm_restrictedUnitaryGaussianContinuumJoint_left
    {t u : ℝ} (ht : 0 < t) (hu : 1 ≤ u) :
    (∫ x : ℝ in Ioi 0, ‖restrictedUnitaryGaussianContinuumJoint t (x, u)‖) =
      (Real.Gamma (t / 2) / Real.pi ^ (t / 2)) * u ^ (-(1 + t)) := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    exact mul_nonneg (Real.rpow_nonneg hx.le _)
      (div_nonneg (Real.exp_pos _).le (zero_lt_one.trans_le hu).le))]
  exact integral_restrictedUnitaryGaussianContinuumJoint_left ht hu

theorem integrableOn_restrictedUnitaryGaussianContinuumJoint_left
    {t u : ℝ} (ht : 0 < t) (hu : 1 ≤ u) :
    IntegrableOn (fun x : ℝ => restrictedUnitaryGaussianContinuumJoint t (x, u)) (Ioi 0) := by
  have hupos : 0 < u := zero_lt_one.trans_le hu
  have hb : 0 < Real.pi * u ^ 2 := mul_pos Real.pi_pos (sq_pos_of_pos hupos)
  have hs : 0 < t / 2 := by linarith
  have h :=
    (GaloisForLFunctions.HTGeometry.DaiYoshikawa.integrableOn_exp_neg_mul_rpow hb hs).const_mul
      u⁻¹
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  change u⁻¹ * (Real.exp (-(Real.pi * u ^ 2 * x)) * x ^ (t / 2 - 1)) =
    x ^ (t / 2 - 1) * (Real.exp (-(Real.pi * u ^ 2 * x)) / u)
  rw [div_eq_mul_inv]
  ring

theorem integrableOn_restrictedUnitaryContinuumTail
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun u : ℝ => u ^ (-(1 + t))) (Ici 1) := by
  have hcomplex := integrableOn_Ici_ofReal_cpow (c := 1) one_pos
    (r := ((-(1 + t) : ℝ) : ℂ)) (by simp; linarith)
  have hre := hcomplex.re
  refine hre.congr ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ici] with u hu
  exact (congrArg Complex.re
    (Complex.ofReal_cpow (le_trans zero_le_one hu) (-(1 + t)))).symm

theorem integral_restrictedUnitaryContinuumTail
    {t : ℝ} (ht : 0 < t) :
    (∫ u : ℝ in Ici 1, u ^ (-(1 + t))) = 1 / t := by
  have hcomplexInt := integral_Ici_ofReal_cpow (c := 1) one_pos
    (r := ((-(1 + t) : ℝ) : ℂ)) (by simp; linarith)
  have hcomplexIntegrable := integrableOn_Ici_ofReal_cpow (c := 1) one_pos
    (r := ((-(1 + t) : ℝ) : ℂ)) (by simp; linarith)
  calc
    (∫ u : ℝ in Ici 1, u ^ (-(1 + t))) =
        ∫ u : ℝ in Ici 1, ((u : ℂ) ^ ((-(1 + t) : ℝ) : ℂ)).re := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict measurableSet_Ici] with u hu
      have hc := congrArg Complex.re
        (Complex.ofReal_cpow (le_trans zero_le_one hu) (-(1 + t)))
      norm_num at hc
      convert hc using 1 <;> push_cast <;> ring
    _ = (∫ u : ℝ in Ici 1, (u : ℂ) ^ ((-(1 + t) : ℝ) : ℂ)).re := by
      exact (GaloisForLFunctions.HTGeometry.integral_re_eq hcomplexIntegrable).symm
    _ = 1 / t := by
      rw [hcomplexInt]
      push_cast
      simp

theorem integrable_restrictedUnitaryGaussianContinuumJoint
    {t : ℝ} (ht : 0 < t) :
    Integrable (restrictedUnitaryGaussianContinuumJoint t)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ici 1))) := by
  have hmeas : AEStronglyMeasurable (restrictedUnitaryGaussianContinuumJoint t)
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ici 1))) := by
    apply AEMeasurable.aestronglyMeasurable
    unfold restrictedUnitaryGaussianContinuumJoint
    measurability
  refine (integrable_prod_iff' hmeas).2 ⟨?_, ?_⟩
  · filter_upwards [self_mem_ae_restrict measurableSet_Ici] with u hu
    exact integrableOn_restrictedUnitaryGaussianContinuumJoint_left ht hu
  · have htail := (integrableOn_restrictedUnitaryContinuumTail ht).const_mul
      (Real.Gamma (t / 2) / Real.pi ^ (t / 2))
    refine htail.congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with u hu
    exact (integral_norm_restrictedUnitaryGaussianContinuumJoint_left ht hu).symm

theorem integral_restrictedUnitaryGaussianContinuumCurrent
    {t : ℝ} (ht : 0 < t) :
    (∫ x : ℝ in Ioi 0,
      x ^ (t / 2 - 1) * restrictedUnitaryGaussianContinuumCurrent x) =
      (Real.Gamma (t / 2) / Real.pi ^ (t / 2)) * (1 / t) := by
  have hprod := integrable_restrictedUnitaryGaussianContinuumJoint ht
  have hswap := MeasureTheory.integral_integral_swap
    (μ := volume.restrict (Ioi 0)) (ν := volume.restrict (Ici 1))
    (f := fun x u => restrictedUnitaryGaussianContinuumJoint t (x, u)) hprod
  rw [show (fun x : ℝ => x ^ (t / 2 - 1) *
      restrictedUnitaryGaussianContinuumCurrent x) =
      fun x : ℝ => ∫ u : ℝ in Ici 1,
        restrictedUnitaryGaussianContinuumJoint t (x, u) by
    funext x
    rw [restrictedUnitaryGaussianContinuumCurrent,
      ← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    rfl]
  rw [hswap]
  have hinter : ∀ᵐ u : ℝ ∂volume.restrict (Ici 1),
      (∫ x : ℝ in Ioi 0, restrictedUnitaryGaussianContinuumJoint t (x, u)) =
        (Real.Gamma (t / 2) / Real.pi ^ (t / 2)) * u ^ (-(1 + t)) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ici] with u hu
    exact integral_restrictedUnitaryGaussianContinuumJoint_left ht hu
  rw [integral_congr_ae hinter]
  rw [MeasureTheory.integral_const_mul,
    integral_restrictedUnitaryContinuumTail ht]

theorem restrictedUnitaryContinuumPole_eq_gaussianMellin
    {t : ℝ} (ht : 0 < t) :
    1 / t = Real.pi ^ (t / 2) / Real.Gamma (t / 2) *
      (∫ x : ℝ in Ioi 0,
        x ^ (t / 2 - 1) * restrictedUnitaryGaussianContinuumCurrent x) := by
  rw [integral_restrictedUnitaryGaussianContinuumCurrent ht]
  have hpi : Real.pi ^ (t / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
  have hgamma : Real.Gamma (t / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (by linarith))
  field_simp

theorem integrableOn_restrictedUnitaryGaussianPrimeMellinCurrent
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ =>
      x ^ (t / 2 - 1) * restrictedUnitaryGaussianPrimeCurrent x) (Ioi 0) := by
  have hsum :=
    GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
      (μ := volume.restrict (Ioi 0))
      (fun n => integrableOn_restrictedUnitaryGaussianPrimeMellinTerm ht n)
      (summable_integral_norm_restrictedUnitaryGaussianPrimeMellinTerm ht)
  refine hsum.congr (Filter.Eventually.of_forall fun x => ?_)
  change (∑' n : ℕ, x ^ (t / 2 - 1) *
      (finiteVonMangoldtRealWeight n * Real.exp (-(Real.pi * (n : ℝ) ^ 2 * x)))) =
    x ^ (t / 2 - 1) * (∑' n : ℕ, finiteVonMangoldtRealWeight n *
      Real.exp (-(Real.pi * (n : ℝ) ^ 2 * x)))
  rw [tsum_mul_left]

theorem integrableOn_restrictedUnitaryGaussianContinuumMellinCurrent
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ =>
      x ^ (t / 2 - 1) * restrictedUnitaryGaussianContinuumCurrent x) (Ioi 0) := by
  have hprod := integrable_restrictedUnitaryGaussianContinuumJoint ht
  have houter := hprod.integral_prod_left
  refine houter.congr (Filter.Eventually.of_forall fun x => ?_)
  change (∫ u : ℝ in Ici 1, restrictedUnitaryGaussianContinuumJoint t (x, u)) =
    x ^ (t / 2 - 1) *
      (∫ u : ℝ in Ici 1, Real.exp (-(Real.pi * u ^ 2 * x)) / u)
  rw [← MeasureTheory.integral_const_mul]
  apply integral_congr_ae
  filter_upwards with u
  rfl

theorem integralOn_mul_sub_of_integrableOn
    {f g h : ℝ → ℝ}
    (hfg : IntegrableOn (fun x => f x * g x) (Ioi 0))
    (hfh : IntegrableOn (fun x => f x * h x) (Ioi 0)) :
    (∫ x : ℝ in Ioi 0, f x * (g x - h x)) =
      (∫ x : ℝ in Ioi 0, f x * g x) -
        ∫ x : ℝ in Ioi 0, f x * h x := by
  calc
    _ = ∫ x : ℝ in Ioi 0, (f x * g x - f x * h x) := by
      apply integral_congr_ae
      filter_upwards with x
      exact mul_sub _ _ _
    _ = _ := MeasureTheory.integral_sub hfg hfh

theorem restrictedUnitaryGaussianDiscrepancy_eq_mellin
    {t : ℝ} (ht : 0 < t) :
    restrictedUnitarySafeEulerCurrent t - 1 / t =
      Real.pi ^ (t / 2) / Real.Gamma (t / 2) *
        (∫ x : ℝ in Ioi 0, x ^ (t / 2 - 1) *
          (restrictedUnitaryGaussianPrimeCurrent x -
            restrictedUnitaryGaussianContinuumCurrent x)) := by
  have hp := integrableOn_restrictedUnitaryGaussianPrimeMellinCurrent ht
  have hc := integrableOn_restrictedUnitaryGaussianContinuumMellinCurrent ht
  rw [integralOn_mul_sub_of_integrableOn hp hc]
  rw [mul_sub]
  rw [← restrictedUnitarySafeEulerCurrent_eq_gaussianMellin ht,
    ← restrictedUnitaryContinuumPole_eq_gaussianMellin ht]


/-- The complete cubic safe-Euler current is integrable on the positive ray. -/
theorem integrableOn_restrictedUnitaryCubicSafeCurrent :
    IntegrableOn (fun t : ℝ => t ^ 2 * restrictedUnitarySafeEulerCurrent t) (Ioi 0) := by
  have hsum :=
    GaloisForLFunctions.HTGeometry.integrable_tsum_of_summable_integral_norm
      (μ := volume.restrict (Ioi 0))
      integrableOn_restrictedUnitaryCubicClockTerm
      summable_integral_norm_restrictedUnitaryCubicClockTerm
  refine hsum.congr (Filter.Eventually.of_forall fun t => ?_)
  change (∑' n : ℕ, t ^ 2 *
      (finiteVonMangoldtRealWeight n * Real.exp (-(Real.log n * t)))) =
    t ^ 2 * (∑' n : ℕ,
      finiteVonMangoldtRealWeight n * Real.exp (-(Real.log n * t)))
  rw [tsum_mul_left]

/-- Positive cubic Mellin kernel from `(RUCRI.12)`. -/
def restrictedUnitaryCubicGaussianKernel (x : ℝ) : ℝ :=
  (1 / 8 : ℝ) * ∫ t : ℝ in Ioi 0,
    t ^ 2 * (Real.pi ^ (t / 2) / Real.Gamma (t / 2)) * x ^ (t / 2 - 1)

def restrictedUnitaryCubicGaussianJoint (p : ℝ × ℝ) : ℝ :=
  (1 / 8 : ℝ) * p.1 ^ 2 *
    (Real.pi ^ (p.1 / 2) / Real.Gamma (p.1 / 2)) *
    p.2 ^ (p.1 / 2 - 1) * restrictedUnitaryGaussianPrimeCurrent p.2

theorem measurable_restrictedUnitaryGaussianPrimeCurrent :
    Measurable restrictedUnitaryGaussianPrimeCurrent := by
  unfold restrictedUnitaryGaussianPrimeCurrent
  apply Measurable.tsum
  intro n
  measurability

theorem restrictedUnitaryCubicGaussianKernel_nonneg
    {x : ℝ} (hx : 0 < x) :
    0 ≤ restrictedUnitaryCubicGaussianKernel x := by
  rw [restrictedUnitaryCubicGaussianKernel]
  apply mul_nonneg (by norm_num)
  apply integral_nonneg_of_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
  have hgamma : 0 < Real.Gamma (t / 2) :=
    Real.Gamma_pos_of_pos (half_pos ht)
  positivity

theorem integrableOn_restrictedUnitaryCubicGaussianJoint_right
    {t : ℝ} (ht : 0 < t) :
    IntegrableOn (fun x : ℝ => restrictedUnitaryCubicGaussianJoint (t, x)) (Ioi 0) := by
  have hp := integrableOn_restrictedUnitaryGaussianPrimeMellinCurrent ht
  have h := hp.const_mul
    ((1 / 8 : ℝ) * t ^ 2 * (Real.pi ^ (t / 2) / Real.Gamma (t / 2)))
  refine h.congr (Filter.Eventually.of_forall fun x => ?_)
  dsimp only [restrictedUnitaryCubicGaussianJoint]
  ring

theorem integral_norm_restrictedUnitaryCubicGaussianJoint_right
    {t : ℝ} (ht : 0 < t) :
    (∫ x : ℝ in Ioi 0, ‖restrictedUnitaryCubicGaussianJoint (t, x)‖) =
      (1 / 8 : ℝ) * t ^ 2 * restrictedUnitarySafeEulerCurrent t := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun x hx => by
    rw [Real.norm_eq_abs, abs_of_nonneg]
    have hgamma : 0 < Real.Gamma (t / 2) :=
      Real.Gamma_pos_of_pos (half_pos ht)
    change 0 ≤ (1 / 8 : ℝ) * t ^ 2 *
      (Real.pi ^ (t / 2) / Real.Gamma (t / 2)) *
        x ^ (t / 2 - 1) * restrictedUnitaryGaussianPrimeCurrent x
    exact mul_nonneg
      (mul_nonneg
        (mul_nonneg
          (mul_nonneg (by norm_num) (sq_nonneg t))
          (div_nonneg (Real.rpow_nonneg Real.pi_pos.le _) hgamma.le))
        (Real.rpow_nonneg hx.le _))
      (tsum_nonneg fun n => mul_nonneg (finiteVonMangoldtRealWeight_nonneg n)
        (Real.exp_pos _).le))]
  rw [show (fun x : ℝ => restrictedUnitaryCubicGaussianJoint (t, x)) =
      fun x : ℝ => ((1 / 8 : ℝ) * t ^ 2 *
        (Real.pi ^ (t / 2) / Real.Gamma (t / 2))) *
          (x ^ (t / 2 - 1) * restrictedUnitaryGaussianPrimeCurrent x) by
    funext x
    rw [restrictedUnitaryCubicGaussianJoint]
    ring]
  rw [MeasureTheory.integral_const_mul,
    integral_restrictedUnitaryGaussianPrimeCurrent ht]
  have hpi : Real.pi ^ (t / 2) ≠ 0 :=
    ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
  have hgamma : Real.Gamma (t / 2) ≠ 0 :=
    ne_of_gt (Real.Gamma_pos_of_pos (half_pos ht))
  field_simp

theorem integrable_restrictedUnitaryCubicGaussianJoint :
    Integrable restrictedUnitaryCubicGaussianJoint
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
  have hmeas : AEStronglyMeasurable restrictedUnitaryCubicGaussianJoint
      ((volume.restrict (Ioi 0)).prod (volume.restrict (Ioi 0))) := by
    have hGamma : Measurable (fun p : ℝ × ℝ => Real.Gamma (p.1 / 2)) :=
      (HTGeometry.measurable_realGamma).comp (measurable_fst.div_const 2)
    have hcurrent : Measurable
        (fun p : ℝ × ℝ => restrictedUnitaryGaussianPrimeCurrent p.2) :=
      measurable_restrictedUnitaryGaussianPrimeCurrent.comp measurable_snd
    apply AEMeasurable.aestronglyMeasurable
    unfold restrictedUnitaryCubicGaussianJoint
    measurability
  refine (integrable_prod_iff hmeas).2 ⟨?_, ?_⟩
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    exact integrableOn_restrictedUnitaryCubicGaussianJoint_right ht
  · have h := integrableOn_restrictedUnitaryCubicSafeCurrent.const_mul (1 / 8 : ℝ)
    refine h.congr ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    simpa only [mul_assoc] using
      (integral_norm_restrictedUnitaryCubicGaussianJoint_right ht).symm

theorem integral_restrictedUnitaryCubicGaussianKernel :
    (1 / 8 : ℝ) * (∫ t : ℝ in Ioi 0,
      t ^ 2 * restrictedUnitarySafeEulerCurrent t) =
      ∫ x : ℝ in Ioi 0,
        restrictedUnitaryCubicGaussianKernel x *
          restrictedUnitaryGaussianPrimeCurrent x := by
  have hprod := integrable_restrictedUnitaryCubicGaussianJoint
  have hswap := MeasureTheory.integral_integral_swap
    (μ := volume.restrict (Ioi 0)) (ν := volume.restrict (Ioi 0))
    (f := fun t x => restrictedUnitaryCubicGaussianJoint (t, x)) hprod
  have hleft : (∫ t : ℝ in Ioi 0,
      ∫ x : ℝ in Ioi 0, restrictedUnitaryCubicGaussianJoint (t, x)) =
      (1 / 8 : ℝ) * (∫ t : ℝ in Ioi 0,
        t ^ 2 * restrictedUnitarySafeEulerCurrent t) := by
    rw [← MeasureTheory.integral_const_mul]
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with t ht
    rw [show (fun x : ℝ => restrictedUnitaryCubicGaussianJoint (t, x)) =
        fun x : ℝ => ((1 / 8 : ℝ) * t ^ 2 *
          (Real.pi ^ (t / 2) / Real.Gamma (t / 2))) *
            (x ^ (t / 2 - 1) * restrictedUnitaryGaussianPrimeCurrent x) by
      funext x
      rw [restrictedUnitaryCubicGaussianJoint]
      ring]
    rw [MeasureTheory.integral_const_mul,
      integral_restrictedUnitaryGaussianPrimeCurrent ht]
    have hpi : Real.pi ^ (t / 2) ≠ 0 :=
      ne_of_gt (Real.rpow_pos_of_pos Real.pi_pos _)
    have hgamma : Real.Gamma (t / 2) ≠ 0 :=
      ne_of_gt (Real.Gamma_pos_of_pos (half_pos ht))
    field_simp
  have hright : (∫ x : ℝ in Ioi 0,
      ∫ t : ℝ in Ioi 0, restrictedUnitaryCubicGaussianJoint (t, x)) =
      ∫ x : ℝ in Ioi 0,
        restrictedUnitaryCubicGaussianKernel x *
          restrictedUnitaryGaussianPrimeCurrent x := by
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with x hx
    rw [restrictedUnitaryCubicGaussianKernel,
      ← MeasureTheory.integral_const_mul,
      ← MeasureTheory.integral_mul_const]
    apply integral_congr_ae
    filter_upwards with t
    rw [restrictedUnitaryCubicGaussianJoint]
    ring
  rw [← hleft, hswap, hright]

/-- **Positive cubic Gaussian subordination `(RUCRI.12)`.**  The exact Route-P base budget is
the Gaussian-prime current paired with the positive cubic Mellin kernel. -/
theorem routePPrimitiveBaseCauchyCubicTraceBudget_eq_gaussianKernel :
    routePPrimitiveBaseCauchyCubicTraceBudget =
      ∫ x : ℝ in Ioi 0,
        restrictedUnitaryCubicGaussianKernel x *
          restrictedUnitaryGaussianPrimeCurrent x := by
  rw [← integral_restrictedUnitarySafeEulerCurrent,
    integral_restrictedUnitaryCubicGaussianKernel]

/-! ## Total Burnol colligation flux -/

/-- Damped aperture flux of one primitive label. -/
def restrictedUnitaryBurnolApertureFluxTerm
    (c : ℝ) (pe : Nat.Primes × ℕ) : ℝ :=
  Real.exp (-2 * c * xiGammaEulerPrimitiveLogFrequency pe) *
    routePPrimitiveBurnolApertureDefectFlux pe

/-- Complete matrix-label flux at aperture time `c`. -/
def restrictedUnitaryBurnolApertureTotalFlux (c : ℝ) : ℝ :=
  ∑' pe : Nat.Primes × ℕ, restrictedUnitaryBurnolApertureFluxTerm c pe

theorem restrictedUnitaryBurnolApertureFluxTerm_nonneg
    {c : ℝ} (hc : 0 ≤ c) (pe : Nat.Primes × ℕ) :
    0 ≤ restrictedUnitaryBurnolApertureFluxTerm c pe := by
  exact mul_nonneg (Real.exp_pos _).le
    (routePPrimitiveBurnolApertureDefectFlux_pos pe).le

theorem restrictedUnitaryBurnolApertureFluxTerm_le
    {c : ℝ} (hc : 0 ≤ c) (pe : Nat.Primes × ℕ) :
    restrictedUnitaryBurnolApertureFluxTerm c pe ≤
      routePPrimitiveBurnolApertureDefectFlux pe := by
  rw [restrictedUnitaryBurnolApertureFluxTerm]
  have hfrequency := xiGammaEulerPrimitiveLogFrequency_pos pe
  have hexp : Real.exp (-2 * c * xiGammaEulerPrimitiveLogFrequency pe) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    positivity
  exact mul_le_of_le_one_left
    (routePPrimitiveBurnolApertureDefectFlux_pos pe).le
    (Real.exp_pos _).le hexp

theorem summable_restrictedUnitaryBurnolApertureFluxTerm
    {c : ℝ} (hc : 0 ≤ c) :
    Summable (restrictedUnitaryBurnolApertureFluxTerm c) := by
  exact Summable.of_nonneg_of_le
    (restrictedUnitaryBurnolApertureFluxTerm_nonneg hc)
    (restrictedUnitaryBurnolApertureFluxTerm_le hc)
    summable_routePPrimitiveBurnolApertureDefectFlux

/-- Each primitive defect mass has the exact damped first flux at every aperture time. -/
theorem hasDerivAt_routePPrimitiveBurnolApertureDefectMass
    (c : ℝ) (pe : Nat.Primes × ℕ) :
    HasDerivAt (fun y : ℝ => routePPrimitiveBurnolApertureDefectMass y pe)
      (restrictedUnitaryBurnolApertureFluxTerm c pe) c := by
  let lambda := xiGammaEulerPrimitiveLogFrequency pe
  let w := routePPrimitiveBaseCauchyCubicWeight pe
  have hlinear : HasDerivAt (fun y : ℝ => -2 * y * lambda) (-2 * lambda) c := by
    simpa only [id_eq, mul_one] using!
      ((hasDerivAt_id (𝕜 := ℝ) c).const_mul (-2)).mul_const lambda
  have hexp : HasDerivAt (fun y : ℝ => Real.exp (-2 * y * lambda))
      (Real.exp (-2 * c * lambda) * (-2 * lambda)) c := by
    simpa only [Function.comp_apply] using
      (Real.hasDerivAt_exp (-2 * c * lambda)).comp c hlinear
  have hsub : HasDerivAt (fun y : ℝ => 1 - Real.exp (-2 * y * lambda))
      (2 * lambda * Real.exp (-2 * c * lambda)) c := by
    convert (hasDerivAt_const (x := c) (c := (1 : ℝ))).sub hexp using 1 <;> ring
  unfold routePPrimitiveBurnolApertureDefectMass
  change HasDerivAt (fun y : ℝ => (1 - Real.exp (-2 * y * lambda)) * w)
    (restrictedUnitaryBurnolApertureFluxTerm c pe) c
  convert hsub.mul_const w using 1
  rw [restrictedUnitaryBurnolApertureFluxTerm,
    routePPrimitiveBurnolApertureDefectFlux]
  simp only [lambda, w]
  ring

/-- **Interior aperture derivative `(RUCRI.15)`.**  At every positive time, differentiation
commutes with the complete primitive sum. -/
theorem hasDerivAt_routePPrimitiveBurnolApertureTotalDefectMass
    {c : ℝ} (hc : 0 < c) :
    HasDerivAt routePPrimitiveBurnolApertureTotalDefectMass
      (restrictedUnitaryBurnolApertureTotalFlux c) c := by
  have h := hasDerivAt_tsum_of_isPreconnected
    (u := routePPrimitiveBurnolApertureDefectFlux)
    (g := fun pe y => routePPrimitiveBurnolApertureDefectMass y pe)
    (g' := fun pe y => restrictedUnitaryBurnolApertureFluxTerm y pe)
    summable_routePPrimitiveBurnolApertureDefectFlux
    isOpen_Ioi convex_Ioi.isPreconnected
    (fun pe y _hy => hasDerivAt_routePPrimitiveBurnolApertureDefectMass y pe)
    (fun pe y hy => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg (restrictedUnitaryBurnolApertureFluxTerm_nonneg hy.le pe)]
      exact restrictedUnitaryBurnolApertureFluxTerm_le hy.le pe)
    (show (1 : ℝ) ∈ Ioi 0 by norm_num)
    (summable_routePPrimitiveBurnolApertureDefectMass (by norm_num)) hc
  simpa only [routePPrimitiveBurnolApertureTotalDefectMass,
    restrictedUnitaryBurnolApertureTotalFlux] using h

/-- Each positive primitive flux is integrable over the full aperture ray. -/
theorem integrableOn_restrictedUnitaryBurnolApertureFluxTerm
    (pe : Nat.Primes × ℕ) :
    IntegrableOn (fun c : ℝ => restrictedUnitaryBurnolApertureFluxTerm c pe) (Ioi 0) := by
  have hfrequency := xiGammaEulerPrimitiveLogFrequency_pos pe
  have hrate : 0 < 2 * xiGammaEulerPrimitiveLogFrequency pe := by positivity
  have h := (integrableOn_pow_mul_exp_neg_mul_Ioi hrate 0).const_mul
    (routePPrimitiveBurnolApertureDefectFlux pe)
  refine h.congr (Filter.Eventually.of_forall fun c => ?_)
  rw [restrictedUnitaryBurnolApertureFluxTerm]
  simp only [pow_zero, one_mul]
  ring

/-- The integrated norm of one flux channel is exactly its undamped cubic base weight. -/
theorem integral_norm_restrictedUnitaryBurnolApertureFluxTerm
    (pe : Nat.Primes × ℕ) :
    (∫ c : ℝ in Ioi 0, ‖restrictedUnitaryBurnolApertureFluxTerm c pe‖) =
      routePPrimitiveBaseCauchyCubicWeight pe := by
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun c hc => by
    rw [Real.norm_eq_abs,
      abs_of_nonneg (restrictedUnitaryBurnolApertureFluxTerm_nonneg hc.le pe)])]
  rw [show (fun c : ℝ => restrictedUnitaryBurnolApertureFluxTerm c pe) =
      fun c : ℝ => routePPrimitiveBurnolApertureDefectFlux pe *
        (c ^ 0 * Real.exp (-(2 * xiGammaEulerPrimitiveLogFrequency pe * c))) by
    funext c
    rw [restrictedUnitaryBurnolApertureFluxTerm]
    simp only [pow_zero, one_mul]
    ring]
  rw [MeasureTheory.integral_const_mul,
    integral_pow_mul_exp_neg_mul_Ioi
      (by positivity : 0 < 2 * xiGammaEulerPrimitiveLogFrequency pe) 0]
  rw [routePPrimitiveBurnolApertureDefectFlux]
  have hfrequency := (xiGammaEulerPrimitiveLogFrequency_pos pe).ne'
  norm_num
  field_simp

theorem integral_restrictedUnitaryBurnolApertureFluxTerm
    (pe : Nat.Primes × ℕ) :
    (∫ c : ℝ in Ioi 0, restrictedUnitaryBurnolApertureFluxTerm c pe) =
      routePPrimitiveBaseCauchyCubicWeight pe := by
  rw [← integral_norm_restrictedUnitaryBurnolApertureFluxTerm]
  apply integral_congr_ae
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with c hc
  rw [Real.norm_eq_abs,
    abs_of_nonneg (restrictedUnitaryBurnolApertureFluxTerm_nonneg hc.le pe)]

theorem summable_integral_norm_restrictedUnitaryBurnolApertureFluxTerm :
    Summable (fun pe : Nat.Primes × ℕ => ∫ c : ℝ in Ioi 0,
      ‖restrictedUnitaryBurnolApertureFluxTerm c pe‖) := by
  exact summable_routePPrimitiveBaseCauchyCubicWeight.congr
    (fun pe => (integral_norm_restrictedUnitaryBurnolApertureFluxTerm pe).symm)

/-- **Total positive colligation action `(RUCRI.16)`.**  The complete cubic source budget is the
integral of its matrix-label Burnol aperture flux. -/
theorem integral_restrictedUnitaryBurnolApertureTotalFlux :
    (∫ c : ℝ in Ioi 0, restrictedUnitaryBurnolApertureTotalFlux c) =
      routePPrimitiveBaseCauchyCubicTraceBudget := by
  have hswap : (∫ c : ℝ in Ioi 0,
      ∑' pe : Nat.Primes × ℕ, restrictedUnitaryBurnolApertureFluxTerm c pe) =
      ∑' pe : Nat.Primes × ℕ, ∫ c : ℝ in Ioi 0,
        restrictedUnitaryBurnolApertureFluxTerm c pe := by
    exact GaloisForLFunctions.HTGeometry.integral_tsum_eq_tsum_integral_of_summable_integral_norm
      (μ := volume.restrict (Ioi 0))
      integrableOn_restrictedUnitaryBurnolApertureFluxTerm
      summable_integral_norm_restrictedUnitaryBurnolApertureFluxTerm
  rw [restrictedUnitaryBurnolApertureTotalFlux, hswap]
  simp_rw [integral_restrictedUnitaryBurnolApertureFluxTerm]
  rfl


/-- Hypothesis-free certificate for the projection algebra and literal source identities proved
in this module.  Quantification retains the full infinite-dimensional Hilbert-space statement. -/
theorem restrictedUnitaryCubicRelativeIndex_algebra_closed :
    (∀ (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
        (R P : H →L[ℂ] H),
      IsIdempotentElem R → IsIdempotentElem P →
      ContinuousLinearMap.adjoint R = R → ContinuousLinearMap.adjoint P = P →
      (restrictedProjectionDisplacement R P).IsHilbertSchmidt →
      ContinuousLinearMap.adjoint (restrictedProjectionDisplacement R P) =
          restrictedProjectionDisplacement R P ∧
        ContinuousLinearMap.adjoint (restrictedProjectionCubicDefect R P) =
          restrictedProjectionCubicDefect R P ∧
        MemSchattenClass 1 (restrictedProjectionCubicDefect R P) ∧
        restrictedProjectionCubicDefect R P =
          restrictedProjectionPositiveChannel R P -
            restrictedProjectionPositiveChannel P R) ∧
    (∀ n, routePPrimeGammaBaseCubicWeight n =
      finiteVonMangoldtRealWeight n / (4 * Real.log n ^ 3)) ∧
    (∑' n : ℕ, routePPrimeGammaBaseCubicWeight n) =
      routePPrimitiveBaseCauchyCubicTraceBudget ∧
    routePPrimitiveBaseCauchyCubicTraceBudget < 1 := by
  refine ⟨?_, routePPrimeGammaBaseCubicWeight_eq_vonMangoldt, ?_, ?_⟩
  · intro H _ _ _ R P hR hP hRadj hPadj hDelta
    exact ⟨adjoint_restrictedProjectionDisplacement R P hRadj hPadj,
      adjoint_restrictedProjectionCubicDefect R P hRadj hPadj,
      restrictedProjectionCubicDefect_memSchattenClass_one R P hDelta,
      restrictedProjectionCubicDefect_eq_channels R P hR hP⟩
  · exact tsum_routePPrimeGammaBaseCubicWeight_eq_budget
  · exact routePPrimitiveBaseCauchyCubicTraceBudget_lt_one

end RHTower
