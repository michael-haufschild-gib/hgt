import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheActualUpwardSourceIsUniformOnBoundedOverlap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheNearGammaDownwardCancellationIsUniformOnBoundedOverlap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheReplacementErrorsVanishUniformlyOnBoundedOverlap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilFormIsPositiveAtEveryFixedOverlap

/-!
# Completed conductor quasimodes are uniform on bounded overlap

The exact complete-Weil residual retains all eight source terms. Uniform upward shell
realization, full near-Gamma/downward cancellation and replacement estimates make their finite
sum small at one common horizon. Every fixed positive conductor therefore has its actual
completed energy uniformly throughout a bounded overlap interval.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis

private theorem norm_seven_residuals_le {E : Type*} [SeminormedAddCommGroup E]
    (p s c x q y z : E) :
    ‖-p + s + c - x + q + (y + z)‖ ≤ ‖p‖ + ‖s‖ + ‖c‖ + ‖x‖ + ‖q‖ + ‖y‖ + ‖z‖ := by
  have h₁ := norm_add_le (-p) s
  have h₂ := norm_add_le (-p + s) c
  have h₃ := norm_sub_le (-p + s + c) x
  have h₄ := norm_add_le (-p + s + c - x) q
  have h₅ := norm_add_le (-p + s + c - x + q) (y + z)
  have h₆ := norm_add_le y z
  rw [norm_neg] at h₁
  linarith only [h₁, h₂, h₃, h₄, h₅, h₆]

private theorem norm_eight_residuals_le {E : Type*} [SeminormedAddCommGroup E]
    (p s c x q y z u : E) :
    ‖-p + s + c - x + q + (y + z) - u‖ ≤
      ‖p‖ + ‖s‖ + ‖c‖ + ‖x‖ + ‖q‖ + ‖y‖ + ‖z‖ + ‖u‖ := by
  have h₁ := norm_seven_residuals_le p s c x q y z
  have h₂ := norm_sub_le (-p + s + c - x + q + (y + z)) u
  linarith only [h₁, h₂]

/-- All eight literal source residuals vanish at one horizon on every bounded overlap interval. -/
theorem eventually_completeWeil_completedConductor_residual_uniform_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {K : ℝ} (hK : 1 ≤ K) {m : ℕ} (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K →
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖ ≤ ε := by
  let A := |(Real.sqrt (m.totient : ℝ))⁻¹|
  let η := ε / (8 * (A + 1))
  have hA : 0 ≤ A := abs_nonneg _
  have hη : 0 < η := div_pos hε (by positivity)
  have hηeq : η * (8 * (A + 1)) = ε := div_mul_cancel₀ ε (by positivity)
  filter_upwards [(tendsto_normalizedRamanujanHorizonVector_residual_norm hm).eventually (ge_mem_nhds hη),
    eventually_completeWeilSelfError_norm_uniform_overlap hφ hsupp hM (K := K) hm hη,
    eventually_fullWeilCenter_norm_uniform_overlap (φ := φ) (zero_lt_one.trans_le hK) hm hη,
    eventually_separatedCrossError_norm_uniform_overlap hφ hsupp hM (K := K) hm hη,
    eventually_fullWeilPoleError_norm_uniform_overlap hφ hsupp hM (K := K) hm hη,
    eventually_normalizedFullNearGammaDownwardVector_norm_uniform_overlap hφ hsupp hM hK m hη,
    eventually_nearCenterVector_norm_uniform_overlap hM (K := K) hm hη,
    eventually_normalizedUpwardPrimeResidual_norm_uniform_overlap hφ hsupp hM hK hm hη,
    eventually_ge_atTop 1] with N hp hs hcenter hx hq hdown hnear hup hN
  intro c hc1 hcK
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hs' := hs c hc hcK
  have hcenter' := hcenter c hc hcK
  have hx' := hx c hc hcK
  have hq' := hq c hc hcK
  have hnear' := hnear c hc1 hcK
  have hdown' : ‖(Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m‖ ≤ A * η := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hdown c hc1 hcK) hA
  have hup' : ‖upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N‖ ≤ A * η := by
    rw [upwardPrimeVector_ramanujan_residual_eq φ c N hm, norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hup c hc1 hcK) hA
  rw [completeWeilMatrix_ramanujan_residual_eq_at_every_overlap hφ hsupp hM hc hN hm]
  have hsum := norm_eight_residuals_le
    (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N)
    (completeWeilSelfError φ c N • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N)
      (normalizedRamanujanHorizonVector m N) -
      (if m = 1 then completeWeilPoleShift φ c else 0) • normalizedRamanujanHorizonVector m N)
    (Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    (Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) (normalizedRamanujanHorizonVector m N))
    ((Real.sqrt (m.totient : ℝ))⁻¹ • normalizedFullNearGammaDownwardVector φ c N m)
    (nearCenterVector φ c N m)
    (upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N)
  nlinarith only [hsum, hp, hs', hcenter', hx', hq', hdown', hnear', hup', hηeq, hη,
    mul_nonneg hA hη.le]

/-- The explicit tilted spline has uniformly valid completed conductor quasimodes on bounded overlap. -/
theorem eventually_tiltedUnitSpline_completedConductor_residual_uniform_overlap
    {K : ℝ} (hK : 1 ≤ K) {m : ℕ} (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ K →
      ‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ ≤ ε :=
  eventually_completeWeil_completedConductor_residual_uniform_overlap contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hK hm hε

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_completeWeil_completedConductor_residual_uniform_overlap
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_completedConductor_residual_uniform_overlap
