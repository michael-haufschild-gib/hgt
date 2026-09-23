import GaloisForLFunctions.RHTower.XiHeatCassiniWoldHolonomyActivationFisherLanding

/-!
# Log-smoothness of the centered Wold holonomy

Exponential square-root-log damping absorbs every polynomial in prime-log height.  Consequently
the centered Route-T Wold holonomy residual lies in every polynomial graph domain of the
unbounded prime-log generator, both for the literal essential-edge measure and for the
source-selected activation-Fisher measure.

This proves arithmetic graph smoothness to all finite orders.  It does not construct the missing
Boolean grade-changing action on the propagated mass profile.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Every even prime-log moment of the ordered residual is summable against `1/p`. -/
theorem summable_xiHeatCassiniOrderedWoldResidual_logPow_oneDivEnergy (k : ℕ) :
    Summable (fun N : ℕ =>
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) /
          (nthPrimeSubtype N : ℝ) *
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy N ^ (2 : ℕ)) := by
  obtain ⟨B, c, hc, hB, hrate⟩ :=
    exists_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_rate
  have hprime := (burnolSummable_poissonWeight_logPow hc k).mul_left (B ^ (2 : ℕ))
  have hmajor : Summable (fun N : ℕ =>
      B ^ (2 : ℕ) *
        (Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) *
          Real.exp (-(2 * c * Real.sqrt
            (Real.log (nthPrimeSubtype N : ℝ)))) /
              (nthPrimeSubtype N : ℝ))) := by
    have h := nthPrimeEquiv.summable_iff.mpr hprime
    exact h.congr fun N => rfl
  let clipped : ℕ → ℝ := fun N =>
    if |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-c * Real.sqrt
          (Real.log (nthPrimeSubtype N : ℝ))) then
      Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) /
          (nthPrimeSubtype N : ℝ) *
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy N ^ (2 : ℕ)
    else 0
  have hclipped : Summable clipped := by
    refine Summable.of_nonneg_of_le (fun N => ?_) (fun N => ?_) hmajor
    · dsimp only [clipped]
      split_ifs
      · exact mul_nonneg (div_nonneg (by positivity) (by positivity)) (sq_nonneg _)
      · exact le_rfl
    · dsimp only [clipped]
      split_ifs with hN
      · let p : Nat.Primes := nthPrimeSubtype N
        let L : ℝ := Real.log (p : ℝ)
        let E : ℝ := Real.exp (-c * Real.sqrt L)
        have hE0 : 0 ≤ E := (Real.exp_pos _).le
        have hBE0 : 0 ≤ B * E := mul_nonneg hB hE0
        have hrateSq :
            xiHeatCassiniOrderedWoldResidualLogDiscrepancy N ^ (2 : ℕ) ≤
              B ^ (2 : ℕ) * Real.exp (-(2 * c * Real.sqrt L)) := by
          have hsquare := pow_le_pow_left₀
            (abs_nonneg (xiHeatCassiniOrderedWoldResidualLogDiscrepancy N))
            (by simpa only [p, L, E] using hN) 2
          calc
            xiHeatCassiniOrderedWoldResidualLogDiscrepancy N ^ (2 : ℕ) =
                |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ^ (2 : ℕ) := by
              rw [sq_abs]
            _ ≤ (B * E) ^ (2 : ℕ) := hsquare
            _ = B ^ (2 : ℕ) * Real.exp (-(2 * c * Real.sqrt L)) := by
              dsimp only [E]
              rw [mul_pow, ← Real.exp_nat_mul]
              congr 2
              ring
        have hweight0 :
            0 ≤ Real.log (p : ℝ) ^ (2 * k) / (p : ℝ) := by
          positivity
        calc
          Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) /
                (nthPrimeSubtype N : ℝ) *
              xiHeatCassiniOrderedWoldResidualLogDiscrepancy N ^ (2 : ℕ) ≤
            (Real.log (p : ℝ) ^ (2 * k) / (p : ℝ)) *
              (B ^ (2 : ℕ) * Real.exp (-(2 * c * Real.sqrt L))) := by
                exact mul_le_mul_of_nonneg_left hrateSq hweight0
          _ = B ^ (2 : ℕ) *
              (Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) *
                Real.exp (-(2 * c * Real.sqrt
                  (Real.log (nthPrimeSubtype N : ℝ)))) /
                    (nthPrimeSubtype N : ℝ)) := by
              dsimp only [p, L]
              ring
      · positivity
  apply hclipped.congr_atTop
  filter_upwards [hrate] with N hN
  simp only [clipped, if_pos hN]

/-- Literal-prime form: the residual is smooth for every power of the prime-log generator over
the harmonic base measure. -/
theorem summable_xiHeatCassiniPrimeWoldResidual_logPow_oneDivEnergy (k : ℕ) :
    Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) ^ (2 * k) / (p : ℝ) *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ (2 : ℕ)) := by
  have hNat :=
    summable_xiHeatCassiniOrderedWoldResidual_logPow_oneDivEnergy k
  apply nthPrimeEquiv.summable_iff.mp
  refine hNat.congr (fun N => ?_)
  change
    Real.log (nthPrimeSubtype N : ℝ) ^ (2 * k) /
          (nthPrimeSubtype N : ℝ) *
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy N ^ (2 : ℕ) =
      Real.log (nthPrimeEquiv N : ℝ) ^ (2 * k) /
          (nthPrimeEquiv N : ℝ) *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy (nthPrimeEquiv N) ^ (2 : ℕ)
  have hsymm : nthPrimeEquiv.symm (nthPrimeSubtype N) = N := by
    change nthPrimeEquiv.symm (nthPrimeEquiv N) = N
    exact Equiv.symm_apply_apply nthPrimeEquiv N
  rw [show nthPrimeEquiv N = nthPrimeSubtype N by rfl,
    xiHeatCassiniPrimeWoldResidualLogDiscrepancy, hsymm]

/-- **Activation-Fisher log-smoothness.**  Residual holonomy belongs to every polynomial graph
domain of the source-selected activation-Fisher prime-log generator. -/
theorem summable_xiHeatCassiniPrimeWoldResidual_activationFisherLogPowEnergy (k : ℕ) :
    Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) ^ (2 * k) * primeActivationOccupancyFisherDensity p *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ (2 : ℕ)) := by
  refine Summable.of_nonneg_of_le
    (fun p => mul_nonneg (mul_nonneg (by positivity) (by
      exact (by positivity : 0 ≤ 1 / (4 * (p : ℝ))).trans
        (primeActivationOccupancyFisherDensity_bounds p).1)) (sq_nonneg _))
    (fun p => ?_)
    (summable_xiHeatCassiniPrimeWoldResidual_logPow_oneDivEnergy k)
  calc
    Real.log (p : ℝ) ^ (2 * k) * primeActivationOccupancyFisherDensity p *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ (2 : ℕ) ≤
      Real.log (p : ℝ) ^ (2 * k) * (1 / (p : ℝ)) *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (primeActivationOccupancyFisherDensity_bounds p).2 (by positivity))
        (sq_nonneg _)
    _ = Real.log (p : ℝ) ^ (2 * k) / (p : ℝ) *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ (2 : ℕ) := by ring

/-- **Essential-edge log-smoothness.**  Same all-orders graph landing holds for the literal
strict-preclosure essential edge. -/
theorem summable_xiHeatCassiniPrimeWoldResidual_actualEssentialEdgeLogPowEnergy (k : ℕ) :
    Summable (fun p : Nat.Primes =>
      Real.log (p : ℝ) ^ (2 * k) *
        primeFirstTraceEssentialHarmonicCoordinate p *
          xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ (2 : ℕ)) := by
  refine Summable.of_nonneg_of_le
    (fun p => mul_nonneg
      (mul_nonneg (by positivity)
        (primeFirstTraceEssentialHarmonicCoordinate_nonneg p)) (sq_nonneg _))
    (fun p => ?_)
    (summable_xiHeatCassiniPrimeWoldResidual_logPow_oneDivEnergy k)
  calc
    Real.log (p : ℝ) ^ (2 * k) *
          primeFirstTraceEssentialHarmonicCoordinate p *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ (2 : ℕ) ≤
      Real.log (p : ℝ) ^ (2 * k) * (1 / (p : ℝ)) *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left
          (primeFirstTraceEssentialHarmonicCoordinate_bounds p).2 (by positivity))
        (sq_nonneg _)
    _ = Real.log (p : ℝ) ^ (2 * k) / (p : ℝ) *
        xiHeatCassiniPrimeWoldResidualLogDiscrepancy p ^ (2 : ℕ) := by ring

end

end RHTower
