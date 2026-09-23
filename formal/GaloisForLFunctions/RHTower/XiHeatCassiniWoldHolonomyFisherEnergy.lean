import GaloisForLFunctions.RHTower.XiHeatCassiniWoldHolonomyExpRate
import GaloisForLFunctions.RHTower.BurnolPoissonSubordinateWall

/-!
# Critical harmonic energy of the centered Route-T Wold holonomy

Pointwise square-root-log damping is too weak to beat the restored half-density envelope.  Its
square is nevertheless integrable against the critical harmonic prime measure `log p / p`.
Thus the centered Wold holonomy is an unconditional finite-energy vector in the exact arithmetic
coframe used by Route T.  This is the strongest normed survivor of the quantitative holonomy rate;
any further closure must pair this energy with phase-sensitive profile transport rather than total
variation.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- Exponential square-root-log damping is summable against a logarithmic harmonic prime weight. -/
theorem summable_log_harmonic_exp_neg_sqrt_prime
    {c : ℝ} (hc : 0 < c) :
    Summable (fun p : Nat.Primes =>
      (1 + Real.log (p : ℝ) ^ (2 : ℕ)) *
        Real.exp (-(2 * c * Real.sqrt (Real.log (p : ℝ)))) / (p : ℝ)) := by
  have hzero := burnolSummable_poissonWeight_logPow hc 0
  have hone := burnolSummable_poissonWeight_logPow hc 1
  have hadd : Summable (fun p : Nat.Primes =>
      Real.log ((p : ℕ) : ℝ) ^ (2 * 0) *
          Real.exp (-(2 * c * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) / ((p : ℕ) : ℝ) +
        Real.log ((p : ℕ) : ℝ) ^ (2 * 1) *
          Real.exp (-(2 * c * Real.sqrt (Real.log ((p : ℕ) : ℝ)))) / ((p : ℕ) : ℝ)) :=
    hzero.add hone
  refine hadd.congr ?_
  intro p
  norm_num
  ring

/-- **Finite critical Fisher energy of the Wold holonomy residual.** -/
theorem summable_xiHeatCassiniOrderedWoldResidual_harmonicEnergy :
    Summable (fun N : ℕ =>
      xiMassPrimeHarmonicRealCoefficient (nthPrimeSubtype N) *
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy N ^ (2 : ℕ)) := by
  obtain ⟨B, c, hc, hB, hrate⟩ :=
    exists_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_rate
  have hprime := (summable_log_harmonic_exp_neg_sqrt_prime hc).mul_left (B ^ (2 : ℕ))
  have hmajor : Summable (fun N : ℕ =>
      B ^ (2 : ℕ) * ((1 + Real.log (nthPrimeSubtype N : ℝ) ^ (2 : ℕ)) *
        Real.exp (-(2 * c * Real.sqrt
          (Real.log (nthPrimeSubtype N : ℝ)))) /
            (nthPrimeSubtype N : ℝ))) := by
    have h := nthPrimeEquiv.summable_iff.mpr hprime
    exact h.congr fun N => rfl
  let clipped : ℕ → ℝ := fun N =>
    if |xiHeatCassiniOrderedWoldResidualLogDiscrepancy N| ≤
        B * Real.exp (-c * Real.sqrt
          (Real.log (nthPrimeSubtype N : ℝ))) then
      xiMassPrimeHarmonicRealCoefficient (nthPrimeSubtype N) *
        xiHeatCassiniOrderedWoldResidualLogDiscrepancy N ^ (2 : ℕ)
    else 0
  have hclipped : Summable clipped := by
    refine Summable.of_nonneg_of_le (fun N => ?_) (fun N => ?_) hmajor
    · dsimp only [clipped]
      split_ifs
      · exact mul_nonneg (by
          rw [xiMassPrimeHarmonicRealCoefficient]
          exact div_nonneg (log_prime_pos _).le (by positivity)) (sq_nonneg _)
      · exact le_rfl
    · dsimp only [clipped]
      split_ifs with hN
      · let p : Nat.Primes := nthPrimeSubtype N
        let L : ℝ := Real.log (p : ℝ)
        let E : ℝ := Real.exp (-c * Real.sqrt L)
        have hL0 : 0 ≤ L := by
          dsimp only [L]
          exact (log_prime_pos p).le
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
        have hLle : L ≤ 1 + L ^ (2 : ℕ) := by
          nlinarith [sq_nonneg (L - 1 / 2)]
        have hp0 : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
        have hharmonic0 :
            0 ≤ xiMassPrimeHarmonicRealCoefficient p := by
          rw [xiMassPrimeHarmonicRealCoefficient]
          exact div_nonneg hL0 hp0.le
        calc
          xiMassPrimeHarmonicRealCoefficient (nthPrimeSubtype N) *
              xiHeatCassiniOrderedWoldResidualLogDiscrepancy N ^ (2 : ℕ) ≤
            xiMassPrimeHarmonicRealCoefficient p *
              (B ^ (2 : ℕ) * Real.exp (-(2 * c * Real.sqrt L))) := by
                exact mul_le_mul_of_nonneg_left hrateSq hharmonic0
          _ = L * (B ^ (2 : ℕ) * Real.exp (-(2 * c * Real.sqrt L)) / (p : ℝ)) := by
                rw [xiMassPrimeHarmonicRealCoefficient]
                ring
          _ ≤ (1 + L ^ (2 : ℕ)) *
              (B ^ (2 : ℕ) * Real.exp (-(2 * c * Real.sqrt L)) / (p : ℝ)) :=
                mul_le_mul_of_nonneg_right hLle (by positivity)
          _ = B ^ (2 : ℕ) * ((1 + Real.log (nthPrimeSubtype N : ℝ) ^ (2 : ℕ)) *
              Real.exp (-(2 * c * Real.sqrt
                (Real.log (nthPrimeSubtype N : ℝ)))) /
                (nthPrimeSubtype N : ℝ)) := by
                  dsimp only [p, L]
                  ring
      · positivity
  apply hclipped.congr_atTop
  filter_upwards [hrate] with N hN
  simp only [clipped, if_pos hN]

end

end RHTower
