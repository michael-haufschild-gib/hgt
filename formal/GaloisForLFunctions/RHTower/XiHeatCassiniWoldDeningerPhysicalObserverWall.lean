import GaloisForLFunctions.RHTower.XiHeatCassiniWoldDeningerBoundaryGrade
import GaloisForLFunctions.RHTower.FisherDeconvolvedSameCarrierOrientationLaw
import GaloisForLFunctions.RHTower.EulerActivationSquarefreeProbability
import GaloisForLFunctions.HTGeometry.ZetaVerticalAlmostPeriodic

/-!
# Physical observer wall for the Route-T Deninger boundary grade

The activation-Fisher boundary coefficient is normalized by `sqrt(d_F(p))`, whereas the physical
Wold terminal flux carries the restored half-density `sqrt(p)`.  Their exact ratio is not a
prime-log derivative: it is the multiplicative-height coefficient `p + 1`.

This module constructs the resulting reflection-odd physical observer and proves that it recovers
the actual centered Wold residual terminal flux prime by prime.  It also gives one explicit vector
which belongs to every finite prime-log graph domain but leaves `ell^2` after multiplication by
`p + 1`.  Thus no amount of finite log regularity closes the physical observation step.
-/

open Complex
open Filter Topology

namespace RHTower

noncomputable section

/-- Exact square root of the source-selected activation-Fisher density. -/
theorem sqrt_primeActivationOccupancyFisherDensity_eq
    (p : Nat.Primes) :
    Real.sqrt (primeActivationOccupancyFisherDensity p) =
      Real.sqrt (p : ℝ) / ((p : ℝ) + 1) := by
  rw [primeActivationOccupancyFisherDensity_eq,
    Real.sqrt_div (by positivity), Real.sqrt_sq_eq_abs,
    abs_of_pos (by positivity)]

/-- Fisher normalization is undone by exactly one factor `p + 1`. -/
theorem sqrt_primeActivationOccupancyFisherDensity_mul_succ
    (p : Nat.Primes) :
    Real.sqrt (primeActivationOccupancyFisherDensity p) *
        ((p : ℝ) + 1) =
      Real.sqrt (p : ℝ) := by
  rw [sqrt_primeActivationOccupancyFisherDensity_eq]
  field_simp

/-- The physical-to-Fisher half-density ratio is the exact multiplicative-height step `p + 1`. -/
theorem sqrt_prime_div_sqrt_activationFisher_eq_succ
    (p : Nat.Primes) :
    Real.sqrt (p : ℝ) /
        Real.sqrt (primeActivationOccupancyFisherDensity p) =
      (p : ℝ) + 1 := by
  apply (div_eq_iff (Real.sqrt_pos.2
    (primeActivationOccupancyFisherDensity_pos' p)).ne').2
  rw [mul_comm, sqrt_primeActivationOccupancyFisherDensity_mul_succ]

/-- Exact scalar coefficient required to convert Fisher boundary normalization into physical
half-density normalization. -/
def xiHeatCassiniWoldFisherPhysicalObserverCoefficient
    (p : Nat.Primes) : ℝ :=
  (p : ℝ) + 1

/-- The physical observer is literally normalized Fisher transport in the forbidden reflected
horizontal chamber `t = -1`. -/
theorem xiHeatCassiniWoldFisherPhysicalObserverCoefficient_eq_reflectedComparison
    (p : Nat.Primes) :
    xiHeatCassiniWoldFisherPhysicalObserverCoefficient p =
      fisherDeconvolvedComparisonWeight (-1) p := by
  rw [xiHeatCassiniWoldFisherPhysicalObserverCoefficient,
    fisherDeconvolvedComparisonWeight]
  norm_num
  ring

/-- Source meaning of the physical coefficient: it is the reciprocal probability of the critical
prime-occupancy event. -/
theorem xiHeatCassiniWoldFisherPhysicalObserverCoefficient_eq_inv_occupancy
    (p : Nat.Primes) :
    xiHeatCassiniWoldFisherPhysicalObserverCoefficient p =
      (diagonalActivationOccupancyProbability
        (xiTransversePrimeApertureDiskNode 1 p))⁻¹ := by
  rw [xiHeatCassiniWoldFisherPhysicalObserverCoefficient,
    diagonalActivationOccupancyProbability,
    xiTransversePrimeApertureDiskNode_one_eq_inv]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  field_simp [hp0]

/-- Fisher density times physical deconvolution is the vacancy probability, equivalently minus
the occupied Boolean score. -/
theorem activationFisher_mul_physicalObserverCoefficient_eq_neg_occupiedScore
    (p : Nat.Primes) :
    primeActivationOccupancyFisherDensity p *
        xiHeatCassiniWoldFisherPhysicalObserverCoefficient p =
      -diagonalActivationOccupancyScore
        (xiTransversePrimeApertureDiskNode 1 p) true := by
  simp only [diagonalActivationOccupancyScore]
  rw [primeActivationOccupancyFisherDensity_eq,
    xiHeatCassiniWoldFisherPhysicalObserverCoefficient,
    diagonalActivationOccupancyProbability,
    xiTransversePrimeApertureDiskNode_one_eq_inv]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  field_simp [hp0]
  simp

/-- **Score interpretation of restored half-density.**  The physical factor `sqrt(p)` is exactly
the occupied Boolean score whitened by its source Fisher metric. -/
theorem sqrt_prime_eq_neg_occupiedScore_div_sqrt_activationFisher
    (p : Nat.Primes) :
    Real.sqrt (p : ℝ) =
      -diagonalActivationOccupancyScore
          (xiTransversePrimeApertureDiskNode 1 p) true /
        Real.sqrt (primeActivationOccupancyFisherDensity p) := by
  have hdpos := primeActivationOccupancyFisherDensity_pos' p
  have hwhiten :
      Real.sqrt (primeActivationOccupancyFisherDensity p) *
          xiHeatCassiniWoldFisherPhysicalObserverCoefficient p =
        -diagonalActivationOccupancyScore
            (xiTransversePrimeApertureDiskNode 1 p) true /
          Real.sqrt (primeActivationOccupancyFisherDensity p) := by
    apply (eq_div_iff (Real.sqrt_pos.2 hdpos).ne').2
    calc
      (Real.sqrt (primeActivationOccupancyFisherDensity p) *
            xiHeatCassiniWoldFisherPhysicalObserverCoefficient p) *
          Real.sqrt (primeActivationOccupancyFisherDensity p) =
        Real.sqrt (primeActivationOccupancyFisherDensity p) ^ 2 *
          xiHeatCassiniWoldFisherPhysicalObserverCoefficient p := by ring
      _ = primeActivationOccupancyFisherDensity p *
          xiHeatCassiniWoldFisherPhysicalObserverCoefficient p := by
        rw [Real.sq_sqrt hdpos.le]
      _ = -diagonalActivationOccupancyScore
            (xiTransversePrimeApertureDiskNode 1 p) true :=
        activationFisher_mul_physicalObserverCoefficient_eq_neg_occupiedScore p
  calc
    Real.sqrt (p : ℝ) =
        Real.sqrt (primeActivationOccupancyFisherDensity p) *
          xiHeatCassiniWoldFisherPhysicalObserverCoefficient p := by
      rw [xiHeatCassiniWoldFisherPhysicalObserverCoefficient]
      exact (sqrt_primeActivationOccupancyFisherDensity_mul_succ p).symm
    _ = _ := hwhiten

/-- Physical observation is unbounded on the fixed Fisher carrier. -/
theorem xiHeatCassiniWoldFisherPhysicalObserverCoefficient_not_isBounded :
    ¬ Bornology.IsBounded
      (Set.range (fun p : Nat.Primes =>
        (xiHeatCassiniWoldFisherPhysicalObserverCoefficient p : ℂ))) := by
  simpa only [
    xiHeatCassiniWoldFisherPhysicalObserverCoefficient_eq_reflectedComparison] using
    (fisherDeconvolvedComparisonWeight_not_isBounded_of_neg
      (show (-1 : ℝ) < 0 by norm_num))

/-- **Exact same-carrier obstruction.**  Physical observation does not descend on the fixed
Fisher-deconvolved source ideal because it has horizontal grade `-1`. -/
theorem xiHeatCassiniWoldFisherPhysicalObserverCoefficient_not_preservesFisherWeightedL1 :
    ¬ PrimeDiagonalPreservesFisherWeightedL1
      (fun p : Nat.Primes =>
        (xiHeatCassiniWoldFisherPhysicalObserverCoefficient p : ℂ)) := by
  intro hpreserves
  have hgrade : (0 : ℝ) ≤ -1 :=
    (fisherDeconvolvedComparisonWeight_preserves_iff (-1)).1 (by
      simpa only [
        xiHeatCassiniWoldFisherPhysicalObserverCoefficient_eq_reflectedComparison] using
        hpreserves)
  norm_num at hgrade

/-- Primewise multiplier which restores the physical Xi-mass half-density after Fisher
normalization. -/
def xiHeatCassiniWoldFisherPhysicalObserver
    (a : ℝ) (τ : ℂ) (p : Nat.Primes) : ℂ :=
  (xiHeatCassiniWoldFisherPhysicalObserverCoefficient p : ℂ) *
    xiHeatCassiniPrimeMassFourierProfile a τ p

/-- Prime transport of the centered Wold holonomy residual agrees with its ordered value. -/
theorem xiHeatCassiniPrimeWoldResidualLogDiscrepancy_nthPrime
    (N : ℕ) :
    xiHeatCassiniPrimeWoldResidualLogDiscrepancy (nthPrimeSubtype N) =
      xiHeatCassiniOrderedWoldResidualLogDiscrepancy N := by
  change xiHeatCassiniOrderedWoldResidualLogDiscrepancy
      (nthPrimeEquiv.symm (nthPrimeSubtype N)) =
    xiHeatCassiniOrderedWoldResidualLogDiscrepancy N
  rw [show nthPrimeSubtype N = nthPrimeEquiv N by rfl,
    Equiv.symm_apply_apply]

/-- **Exact physical factorization.**  Fisher boundary amplitude paired with the physical
observer is the actual centered Wold residual terminal flux. -/
theorem xiHeatCassiniWoldActivationFisherAmplitude_mul_physicalObserver
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    (xiHeatCassiniWoldActivationFisherAmplitude
        (true, nthPrimeSubtype N) : ℂ) *
      xiHeatCassiniWoldFisherPhysicalObserver a τ (nthPrimeSubtype N) =
    xiHeatCassiniOrderedWoldResidualTerminalFlux a τ N := by
  rw [xiHeatCassiniWoldActivationFisherAmplitude,
    xiHeatCassiniWoldFisherPhysicalObserver,
    xiHeatCassiniWoldFisherPhysicalObserverCoefficient,
    xiHeatCassiniOrderedWoldResidualTerminalFlux,
    xiHeatCassiniOrderedPrimeHalfDensityProfile,
    xiHeatCassiniPrimeWoldResidualLogDiscrepancy_nthPrime]
  have hroot :
      (Real.sqrt (primeActivationOccupancyFisherDensity (nthPrimeSubtype N)) : ℂ) *
          (((nthPrimeSubtype N : ℝ) + 1 : ℝ) : ℂ) =
        (Real.sqrt (nthPrimeSubtype N : ℝ) : ℂ) := by
    exact_mod_cast
      sqrt_primeActivationOccupancyFisherDensity_mul_succ (nthPrimeSubtype N)
  calc
    ((Real.sqrt (primeActivationOccupancyFisherDensity (nthPrimeSubtype N)) *
          xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℝ) : ℂ) *
        ((((nthPrimeSubtype N : ℝ) + 1 : ℝ) : ℂ) *
          xiHeatCassiniPrimeMassFourierProfile a τ (nthPrimeSubtype N)) =
        ((Real.sqrt (primeActivationOccupancyFisherDensity (nthPrimeSubtype N)) : ℂ) *
          (((nthPrimeSubtype N : ℝ) + 1 : ℝ) : ℂ)) *
          xiHeatCassiniPrimeMassFourierProfile a τ (nthPrimeSubtype N) *
            (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) := by
      push_cast
      ring
    _ = (Real.sqrt (nthPrimeSubtype N : ℝ) : ℂ) *
          xiHeatCassiniPrimeMassFourierProfile a τ (nthPrimeSubtype N) *
            (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N : ℂ) := by rw [hroot]

/-- Reflection-odd physical observation of the Hodge-changed Fisher boundary vector. -/
def xiHeatCassiniWoldActivationFisherOddPhysicalHodgeAtom
    (a : ℝ) (τ : ℂ) (p : Nat.Primes) : ℂ :=
  xiHeatCassiniWoldActivationFisherHodgeL2 (true, p) *
      xiHeatCassiniWoldFisherPhysicalObserver a τ p -
    xiHeatCassiniWoldActivationFisherHodgeL2 (false, p) *
      xiHeatCassiniWoldFisherPhysicalObserver a τ p

/-- **Physical odd-observer landing.**  Sheet contrast followed by exact Fisher deconvolution
recovers twice the physical centered Wold residual terminal flux, rotated by `i`. -/
theorem xiHeatCassiniWoldActivationFisherOddPhysicalHodgeAtom_nthPrime_eq
    (a : ℝ) (τ : ℂ) (N : ℕ) :
    xiHeatCassiniWoldActivationFisherOddPhysicalHodgeAtom
        a τ (nthPrimeSubtype N) =
      2 * Complex.I * xiHeatCassiniOrderedWoldResidualTerminalFlux a τ N := by
  rw [xiHeatCassiniWoldActivationFisherOddPhysicalHodgeAtom,
    xiHeatCassiniWoldActivationFisherHodgeL2_true,
    xiHeatCassiniWoldActivationFisherHodgeL2_false,
    xiHeatCassiniWoldActivationFisherL2_apply,
    xiHeatCassiniWoldActivationFisherL2_apply]
  have hsame :
      xiHeatCassiniWoldActivationFisherAmplitude
          (false, nthPrimeSubtype N) =
        xiHeatCassiniWoldActivationFisherAmplitude
          (true, nthPrimeSubtype N) := rfl
  rw [hsame]
  calc
    Complex.I *
          (xiHeatCassiniWoldActivationFisherAmplitude
            (true, nthPrimeSubtype N) : ℂ) *
          xiHeatCassiniWoldFisherPhysicalObserver a τ (nthPrimeSubtype N) -
        (-Complex.I *
          (xiHeatCassiniWoldActivationFisherAmplitude
            (true, nthPrimeSubtype N) : ℂ)) *
          xiHeatCassiniWoldFisherPhysicalObserver a τ (nthPrimeSubtype N) =
        2 * Complex.I *
          ((xiHeatCassiniWoldActivationFisherAmplitude
              (true, nthPrimeSubtype N) : ℂ) *
            xiHeatCassiniWoldFisherPhysicalObserver a τ (nthPrimeSubtype N)) := by
      ring
    _ = 2 * Complex.I *
          xiHeatCassiniOrderedWoldResidualTerminalFlux a τ N := by
      rw [xiHeatCassiniWoldActivationFisherAmplitude_mul_physicalObserver]

/-! ## Strict separation from every finite prime-log graph domain -/

/-- A concrete prime boundary probe with one multiplicative-height unit of decay. -/
def xiHeatCassiniWoldPhysicalObserverWallProbe (p : Nat.Primes) : ℝ :=
  1 / (p : ℝ)

/-- The same probe belongs to every finite prime-log graph domain. -/
theorem summable_xiHeatCassiniWoldPhysicalObserverWallProbe_logGraph_sq
    (k : ℕ) :
    Summable (fun p : Nat.Primes =>
      (Real.log (p : ℝ) ^ k *
        xiHeatCassiniWoldPhysicalObserverWallProbe p) ^ 2) := by
  have hNat :=
    HTGeometry.summable_log_pow_div_nat_rpow (2 * k)
      (show (1 : ℝ) < 2 by norm_num)
  have hPrime := hNat.subtype Nat.Prime
  refine hPrime.congr fun p => ?_
  change Real.log (p : ℝ) ^ (2 * k) / (p : ℝ) ^ (2 : ℝ) = _
  rw [xiHeatCassiniWoldPhysicalObserverWallProbe, Real.rpow_two]
  rw [show 2 * k = k * 2 by omega, pow_mul]
  field_simp

/-- Multiplication by the exact physical observer coefficient sends the all-log-smooth probe out
of `ell^2`. -/
theorem not_summable_xiHeatCassiniWoldPhysicalObserverWallProbe_physical_sq :
    ¬ Summable (fun p : Nat.Primes =>
      (((p : ℝ) + 1) *
        xiHeatCassiniWoldPhysicalObserverWallProbe p) ^ 2) := by
  intro hsum
  have hsmall : ∀ᶠ p : Nat.Primes in cofinite,
      (((p : ℝ) + 1) *
        xiHeatCassiniWoldPhysicalObserverWallProbe p) ^ 2 < 1 :=
    hsum.tendsto_cofinite_zero.eventually_lt_const zero_lt_one
  obtain ⟨p, hp⟩ := hsmall.exists
  have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hratio :
      ((p : ℝ) + 1) * xiHeatCassiniWoldPhysicalObserverWallProbe p =
        1 + 1 / (p : ℝ) := by
    rw [xiHeatCassiniWoldPhysicalObserverWallProbe]
    field_simp
  have hge :
      1 ≤ (((p : ℝ) + 1) *
        xiHeatCassiniWoldPhysicalObserverWallProbe p) ^ 2 := by
    rw [hratio]
    nlinarith [one_div_pos.mpr hp0]
  exact (not_lt_of_ge hge) hp

/-- **Maximal log-smooth domain is strictly too large for physical observation.** -/
theorem exists_all_logGraph_smooth_not_physicalL2 :
    ∃ x : Nat.Primes → ℝ,
      (∀ k : ℕ, Summable (fun p : Nat.Primes =>
        (Real.log (p : ℝ) ^ k * x p) ^ 2)) ∧
      ¬ Summable (fun p : Nat.Primes => (((p : ℝ) + 1) * x p) ^ 2) := by
  exact ⟨xiHeatCassiniWoldPhysicalObserverWallProbe,
    summable_xiHeatCassiniWoldPhysicalObserverWallProbe_logGraph_sq,
    not_summable_xiHeatCassiniWoldPhysicalObserverWallProbe_physical_sq⟩

end


end RHTower
