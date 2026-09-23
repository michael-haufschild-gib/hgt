import GaloisForLFunctions.RHTower.Sieve.MaynardOrderedPrimeGapOccupancy

/-!
# Small-shell closure for the Route-T prime-gap moment

The fixed-width Route-T packet first applies at relative width `M^(-49/80)`, equivalently
additive gap scale `4 * M^(31/80)` in a physical dyadic block `[M, 2M]`.  Below that boundary no
large-values estimate is needed: the literal gap occupancy is contained in the block, so its
square mass has exponent `1 + 31/80 = 111/80 < 3/2`.

This isolates the only unresolved portion of the critical gap-moment producer: shells at or above
the fixed-width packet threshold.
-/

open Complex MeasureTheory Set
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Every dyadic gap shell has square mass at most its scale times its ambient physical block.
This uses only the disjoint literal occupancy intervals, not prime density. -/
theorem sum_primeGapSquare_le_eight_mul_scale_mul_dyadicBase (k j : ℕ) :
    (∑ n ∈ routeTPrimeGapDyadicBlockShell k j,
        xiHeatCassiniOrderedPrimeGap n ^ 2) ≤
      8 * routeTPrimeGapDyadicScale j * routeTPrimeGapDyadicBase k := by
  have hsubset := routeTPrimeGapDyadicBlockOccupancy_subset_block k j
  have hfinite : volume (Set.Icc (routeTPrimeGapDyadicBase k)
      (2 * routeTPrimeGapDyadicBase k)) ≠ ⊤ := by
    exact ne_of_lt isCompact_Icc.measure_lt_top
  have hvolume : volume.real (routeTPrimeGapDyadicBlockOccupancy k j) ≤
      routeTPrimeGapDyadicBase k := by
    calc
      volume.real (routeTPrimeGapDyadicBlockOccupancy k j) ≤
          volume.real (Set.Icc (routeTPrimeGapDyadicBase k)
            (2 * routeTPrimeGapDyadicBase k)) :=
        measureReal_mono hsubset hfinite
      _ = routeTPrimeGapDyadicBase k := by
        rw [Real.volume_real_Icc, max_eq_left]
        · ring
        · nlinarith [routeTPrimeGapDyadicBase_pos k]
  calc
    (∑ n ∈ routeTPrimeGapDyadicBlockShell k j,
        xiHeatCassiniOrderedPrimeGap n ^ 2) ≤
        8 * routeTPrimeGapDyadicScale j *
          volume.real (routeTPrimeGapDyadicBlockOccupancy k j) :=
      sum_primeGapSquare_le_eight_mul_volume_occupancy k j
    _ ≤ 8 * routeTPrimeGapDyadicScale j * routeTPrimeGapDyadicBase k :=
      mul_le_mul_of_nonneg_left hvolume
        (mul_nonneg (by norm_num) (routeTPrimeGapDyadicScale_pos j).le)

/-- Shells below the fixed-width packet threshold already have a subcritical square-gap exponent.
The threshold `4 * M^(31/80)` is exactly the additive form of the packet's relative width
`M^(-49/80)`. -/
theorem sum_primeGapSquare_le_small_shell_subcritical
    {k j : ℕ}
    (hscale : routeTPrimeGapDyadicScale j ≤
      4 * routeTPrimeGapDyadicBase k ^ (31 / 80 : ℝ)) :
    (∑ n ∈ routeTPrimeGapDyadicBlockShell k j,
        xiHeatCassiniOrderedPrimeGap n ^ 2) ≤
      32 * routeTPrimeGapDyadicBase k ^ (111 / 80 : ℝ) := by
  let M : ℝ := routeTPrimeGapDyadicBase k
  have hM : 0 < M := routeTPrimeGapDyadicBase_pos k
  calc
    (∑ n ∈ routeTPrimeGapDyadicBlockShell k j,
        xiHeatCassiniOrderedPrimeGap n ^ 2) ≤
        8 * routeTPrimeGapDyadicScale j * M := by
      simpa only [M] using sum_primeGapSquare_le_eight_mul_scale_mul_dyadicBase k j
    _ = (8 * M) * routeTPrimeGapDyadicScale j := by ring
    _ ≤ (8 * M) * (4 * M ^ (31 / 80 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left hscale
      positivity
    _ = 32 * M ^ (111 / 80 : ℝ) := by
      rw [show (111 / 80 : ℝ) = 1 + 31 / 80 by norm_num,
        Real.rpow_add hM]
      rw [Real.rpow_one]
      ring

end

end RHTower.Sieve
