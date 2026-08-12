import GaloisForLFunctions.RHTower.HedenmalmThetaRoutePInformationWoldGaussVirialBridge
import GaloisForLFunctions.RHTower.MobiusLaplaceCriticalDilationNoGo
import GaloisForLFunctions.RHTower.SectorPrimeZeroUniqueness

/-!
# Route P all-prime information virial divergence

The local geometric-KL virial is finite at each prime, but its valuation-one layer already
contains the unstable exponential branch.  At every positive horizontal depth, that layer
eventually dominates Euler's prime harmonic mass.  Consequently both valuation-one information
mass and complete per-prime geometric KL chirality are nonsummable over all primes.

This is the nonlinear information-geometric form of the moving-horizon analytic-doublet
obstruction: KL geometry receives off-wall growth, but cannot itself be Route P's missing finite
global source norm.
-/

open Real Set Filter Topology

namespace RHTower.HedenmalmThetaSource

noncomputable section

/-- Once oriented displacement passes two, holonomy virial contains at least one quarter of its
unstable exponential branch. -/
theorem exp_div_four_le_sourceHorizontalHolonomyVirial
    {u : ℝ} (hu : 2 ≤ u) :
    Real.exp u / 4 ≤ sourceHorizontalHolonomyVirial u := by
  rw [sourceHorizontalHolonomyVirial]
  have hs : Real.exp u / 4 ≤ Real.sinh u :=
    RHTower.sinh_ge_quarter_exp (by linarith)
  have hc : Real.sinh u < Real.cosh u := Real.sinh_lt_cosh u
  have hsp : 0 < Real.sinh u := Real.sinh_pos_iff.mpr (by linarith)
  nlinarith

/-- Exact first-prime-power expression: nonlinear information carrier already contains the
unstable exponential branch at valuation one. -/
theorem sourceHorizontalPrimeGeometricKLScaleTerm_zero_eq
    (p : Nat.Primes) (t : ℝ) :
    sourceHorizontalPrimeGeometricKLScaleTerm p 0 t =
      4 * Real.exp (-Real.log (p : ℝ)) *
        sourceHorizontalHolonomyVirial (2 * Real.log (p : ℝ) * t) := by
  rw [sourceHorizontalPrimeGeometricKLScaleTerm,
    sourceHorizontalPrimePowerHolonomy_scaleVirial]
  norm_num
  ring

/-- At every sufficiently large prime, first nonlinear information layer dominates prime
harmonic mass. -/
theorem eventually_one_div_prime_le_sourceHorizontalPrimeGeometricKLScaleTerm_zero
    {t : ℝ} (ht : 0 < t) :
    ∀ᶠ p : Nat.Primes in cofinite,
      (1 / (p : ℝ) : ℝ) ≤ sourceHorizontalPrimeGeometricKLScaleTerm p 0 t := by
  have hlogtop : Tendsto (fun p : Nat.Primes => Real.log (p : ℝ))
      cofinite atTop := by
    simpa only [Function.comp_def] using!
      Real.tendsto_log_atTop.comp RHTower.tendsto_prime_coe_real_cofinite_atTop
  have hscaled : Tendsto (fun p : Nat.Primes =>
      (2 * t) * Real.log (p : ℝ)) cofinite atTop :=
    hlogtop.const_mul_atTop (by positivity)
  have hlarge := Filter.tendsto_atTop.mp hscaled 2
  filter_upwards [hlarge] with p hpLarge
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.prop.pos
  have hu : 2 ≤ 2 * Real.log (p : ℝ) * t := by
    simpa [mul_assoc, mul_comm, mul_left_comm] using hpLarge
  have hvir := exp_div_four_le_sourceHorizontalHolonomyVirial hu
  have hexpOne : 1 ≤ Real.exp (2 * Real.log (p : ℝ) * t) :=
    Real.one_le_exp (by positivity)
  rw [sourceHorizontalPrimeGeometricKLScaleTerm_zero_eq,
    Real.exp_neg, Real.exp_log hp0]
  have hinv : 0 ≤ ((p : ℝ)⁻¹) := inv_nonneg.mpr hp0.le
  calc
    1 / (p : ℝ) = (p : ℝ)⁻¹ := one_div _
    _ ≤ (p : ℝ)⁻¹ * Real.exp (2 * Real.log (p : ℝ) * t) := by
      simpa using mul_le_mul_of_nonneg_left hexpOne hinv
    _ = 4 * (p : ℝ)⁻¹ * (Real.exp (2 * Real.log (p : ℝ) * t) / 4) := by ring
    _ ≤ 4 * (p : ℝ)⁻¹ * sourceHorizontalHolonomyVirial
          (2 * Real.log (p : ℝ) * t) := by gcongr

/-- **P-G58 nonlinear analytic-doublet obstruction.**  At every positive horizontal depth,
all-prime valuation-one geometric-KL virial is not summable. -/
theorem not_summable_sourceHorizontalPrimeGeometricKLScaleTerm_zero
    {t : ℝ} (ht : 0 < t) :
    ¬ Summable (fun p : Nat.Primes =>
      sourceHorizontalPrimeGeometricKLScaleTerm p 0 t) := by
  intro hsum
  apply Nat.Primes.not_summable_one_div
  apply Summable.of_norm_bounded_eventually hsum
  filter_upwards
    [eventually_one_div_prime_le_sourceHorizontalPrimeGeometricKLScaleTerm_zero ht]
      with p hp
  have hp0 : 0 ≤ (1 / (p : ℝ) : ℝ) := by positivity
  simpa [Real.norm_of_nonneg hp0] using hp

/-- Valuation-one virial is a lower bound for complete per-prime geometric KL chirality
throughout physical strip. -/
theorem sourceHorizontalPrimeGeometricKLScaleTerm_zero_le_chirality
    (p : Nat.Primes) {t : ℝ} (ht : 0 < t) (htHalf : t < 1 / 2) :
    sourceHorizontalPrimeGeometricKLScaleTerm p 0 t ≤
      sourceHorizontalCenteredGeometricKLChirality
        (-Real.log (p : ℝ)) (2 * t * Real.log (p : ℝ)) := by
  have habs : |t| < 1 / 2 := by rw [abs_of_pos ht]; exact htHalf
  have hsum : HasSum (fun n : ℕ =>
      sourceHorizontalPrimeGeometricKLScaleTerm p n t)
      (sourceHorizontalCenteredGeometricKLChirality
        (-Real.log (p : ℝ)) (2 * t * Real.log (p : ℝ))) := by
    simpa only [sourceHorizontalPrimeGeometricKLScaleTerm] using
      hasSum_sourceHorizontalPrimeGeometricKL_scaleVirial p habs
  rw [← hsum.tsum_eq]
  apply hsum.summable.le_tsum 0
  intro n _
  rw [sourceHorizontalPrimeGeometricKLScaleTerm,
    sourceHorizontalPrimePowerHolonomy_scaleVirial]
  have hvir : 0 < sourceHorizontalHolonomyVirial
      (2 * (n + 1) * Real.log (p : ℝ) * t) := by
    apply sourceHorizontalHolonomyVirial_pos
    have hp : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast p.prop.one_lt)
    positivity
  apply mul_nonneg
  · positivity
  · exact mul_nonneg (by norm_num) hvir.le

/-- **Complete all-prime obstruction.**  In right physical strip, actual per-prime geometric KL
chirality fails to be summable.  Nonlinear information geometry therefore cannot be finite global
source norm required by Route P. -/
theorem not_summable_sourceHorizontalPrimeGeometricKLChirality
    {t : ℝ} (ht : 0 < t) (htHalf : t < 1 / 2) :
    ¬ Summable (fun p : Nat.Primes =>
      sourceHorizontalCenteredGeometricKLChirality
        (-Real.log (p : ℝ)) (2 * t * Real.log (p : ℝ))) := by
  intro hsum
  apply not_summable_sourceHorizontalPrimeGeometricKLScaleTerm_zero ht
  exact Summable.of_nonneg_of_le
    (fun p => (sourceHorizontalPrimePowerHolonomy_scaleVirial_pos p 0 ht).le |>
      mul_nonneg (by positivity))
    (fun p => sourceHorizontalPrimeGeometricKLScaleTerm_zero_le_chirality
      p ht htHalf)
    hsum

end

end RHTower.HedenmalmThetaSource
