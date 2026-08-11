import GaloisForLFunctions.RHTower.XiHeatCassiniWoldHolonomyFisherEnergy
import GaloisForLFunctions.RHTower.PrimeFirstTraceEssentialEdgeReflectedIdealGrade

/-!
# Wold holonomy landing in the activation-Fisher essential-edge domain

The quantitative Route-T Wold residual has finite energy for the logarithmic harmonic prime
measure.  The literal strict-preclosure essential edge and the independently selected Euler
activation Fisher density are both bounded above by `1/p`, hence by a fixed multiple of
`log(p)/p`.  Therefore the same residual lands in both concrete source-selected Hilbert domains.

This is a domain identification, not a grade-flip theorem.  It supplies the non-collapsing common
domain on which a future graph-singular Boolean-grade operator would have to act.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Ordered Wold holonomy residual transported from the prime index to the literal prime. -/
def xiHeatCassiniPrimeWoldResidualLogDiscrepancy (p : Nat.Primes) : ℝ :=
  xiHeatCassiniOrderedWoldResidualLogDiscrepancy (nthPrimeEquiv.symm p)

/-- Prime-index Fisher energy and literal-prime harmonic energy are the same series. -/
theorem summable_xiHeatCassiniPrimeWoldResidual_harmonicEnergy :
    Summable (fun p : Nat.Primes =>
      xiMassPrimeHarmonicRealCoefficient p *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2) := by
  have hNat :=
    summable_xiHeatCassiniOrderedWoldResidual_harmonicEnergy
  apply nthPrimeEquiv.summable_iff.mp
  refine hNat.congr (fun N => ?_)
  change
    xiMassPrimeHarmonicRealCoefficient (nthPrimeSubtype N) *
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy N ^ 2 =
      xiMassPrimeHarmonicRealCoefficient (nthPrimeEquiv N) *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy (nthPrimeEquiv N) ^ 2
  have hsymm : nthPrimeEquiv.symm (nthPrimeSubtype N) = N := by
    change nthPrimeEquiv.symm (nthPrimeEquiv N) = N
    exact Equiv.symm_apply_apply nthPrimeEquiv N
  rw [show nthPrimeEquiv N = nthPrimeSubtype N by rfl,
    xiHeatCassiniPrimeWoldResidualLogDiscrepancy, hsymm]

/-- Harmonic energy controls unweighted prime-harmonic energy by the fixed factor
`1 / log 2`. -/
theorem summable_xiHeatCassiniPrimeWoldResidual_oneDivEnergy :
    Summable (fun p : Nat.Primes =>
      (1 / (p : ℝ)) * xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2) := by
  have hscaled :=
    summable_xiHeatCassiniPrimeWoldResidual_harmonicEnergy.mul_left
      (1 / Real.log 2)
  refine Summable.of_nonneg_of_le (fun p => mul_nonneg (by positivity) (sq_nonneg _))
    (fun p => ?_) hscaled
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.2.pos
  have hlogle : Real.log 2 ≤ Real.log (p : ℝ) :=
    Real.strictMonoOn_log.monotoneOn (by norm_num) hp0
      (by exact_mod_cast p.2.two_le)
  have hfactor : 1 ≤ (1 / Real.log 2) * Real.log (p : ℝ) := by
    have hdiv : 1 ≤ Real.log (p : ℝ) / Real.log 2 :=
      (le_div_iff₀ hlog2).2 (by simpa only [one_mul] using hlogle)
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  calc
    (1 / (p : ℝ)) * xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2 =
        1 * ((1 / (p : ℝ)) *
          xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2) := by ring
    _ ≤ ((1 / Real.log 2) * Real.log (p : ℝ)) *
          ((1 / (p : ℝ)) *
            xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2) :=
      mul_le_mul_of_nonneg_right hfactor
        (mul_nonneg (by positivity) (sq_nonneg _))
    _ = (1 / Real.log 2) *
        (xiMassPrimeHarmonicRealCoefficient p *
          xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2) := by
      rw [xiMassPrimeHarmonicRealCoefficient]
      ring

/-- **Activation-Fisher landing.**  Centered Wold holonomy belongs to the literal diagonal Euler
activation Fisher Hilbert domain. -/
theorem summable_xiHeatCassiniPrimeWoldResidual_activationFisherEnergy :
    Summable (fun p : Nat.Primes =>
      primeActivationOccupancyFisherDensity p *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun p => mul_nonneg (by
      exact (by positivity : 0 ≤ 1 / (4 * (p : ℝ))).trans
        (primeActivationOccupancyFisherDensity_bounds p).1) (sq_nonneg _))
    (fun p => ?_)
    summable_xiHeatCassiniPrimeWoldResidual_oneDivEnergy
  exact mul_le_mul_of_nonneg_right
    (primeActivationOccupancyFisherDensity_bounds p).2 (sq_nonneg _)

/-- **Literal essential-edge landing.**  Same residual belongs to the actual strict-preclosure
essential-edge Hilbert domain. -/
theorem summable_xiHeatCassiniPrimeWoldResidual_actualEssentialEdgeEnergy :
    Summable (fun p : Nat.Primes =>
      primeFirstTraceEssentialHarmonicCoordinate p *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun p => mul_nonneg (primeFirstTraceEssentialHarmonicCoordinate_nonneg p)
      (sq_nonneg _))
    (fun p => ?_)
    summable_xiHeatCassiniPrimeWoldResidual_oneDivEnergy
  exact mul_le_mul_of_nonneg_right
    (primeFirstTraceEssentialHarmonicCoordinate_bounds p).2 (sq_nonneg _)

/-- Residual holonomy lies in the graph domain of the unbounded prime-log half-gradient over the
activation-Fisher Hilbert source. -/
theorem summable_xiHeatCassiniPrimeWoldResidual_activationFisherLogGraphEnergy :
    Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) * primeActivationOccupancyFisherDensity p *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun p => mul_nonneg (mul_nonneg (log_prime_pos p).le (by
      exact (by positivity : 0 ≤ 1 / (4 * (p : ℝ))).trans
        (primeActivationOccupancyFisherDensity_bounds p).1)) (sq_nonneg _))
    (fun p => ?_)
    summable_xiHeatCassiniPrimeWoldResidual_harmonicEnergy
  have hlog0 : 0 ≤ Real.log (p : ℝ) := (log_prime_pos p).le
  calc
    Real.log (p : ℝ) * primeActivationOccupancyFisherDensity p *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2 ≤
      Real.log (p : ℝ) * (1 / (p : ℝ)) *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (primeActivationOccupancyFisherDensity_bounds p).2 hlog0)
        (sq_nonneg _)
    _ = xiMassPrimeHarmonicRealCoefficient p *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2 := by
      rw [xiMassPrimeHarmonicRealCoefficient]
      ring

/-- Same unbounded prime-log graph landing holds for the literal essential edge. -/
theorem summable_xiHeatCassiniPrimeWoldResidual_actualEssentialEdgeLogGraphEnergy :
    Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) * primeFirstTraceEssentialHarmonicCoordinate p *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2) := by
  refine Summable.of_nonneg_of_le
    (fun p => mul_nonneg
      (mul_nonneg (log_prime_pos p).le
        (primeFirstTraceEssentialHarmonicCoordinate_nonneg p)) (sq_nonneg _))
    (fun p => ?_)
    summable_xiHeatCassiniPrimeWoldResidual_harmonicEnergy
  have hlog0 : 0 ≤ Real.log (p : ℝ) := (log_prime_pos p).le
  calc
    Real.log (p : ℝ) * primeFirstTraceEssentialHarmonicCoordinate p *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2 ≤
      Real.log (p : ℝ) * (1 / (p : ℝ)) *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (primeFirstTraceEssentialHarmonicCoordinate_bounds p).2 hlog0)
        (sq_nonneg _)
    _ = xiMassPrimeHarmonicRealCoefficient p *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2 := by
      rw [xiMassPrimeHarmonicRealCoefficient]
      ring

/-- The two source-selected residual energies differ by an absolutely summable sequence. -/
theorem summable_xiHeatCassiniPrimeWoldResidual_actualEdge_sub_activationFisherEnergy :
    Summable (fun p : Nat.Primes =>
      (primeFirstTraceEssentialHarmonicCoordinate p -
          primeActivationOccupancyFisherDensity p) *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ 2) := by
  have hsub :=
    summable_xiHeatCassiniPrimeWoldResidual_actualEssentialEdgeEnergy.sub
      summable_xiHeatCassiniPrimeWoldResidual_activationFisherEnergy
  exact hsub.congr fun p => by ring

end

end RHTower
