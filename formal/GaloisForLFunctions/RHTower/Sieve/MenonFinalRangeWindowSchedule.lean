import GaloisForLFunctions.RHTower.Sieve.MenonFinalRangeWindowPartitionFilter
import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicFinalRangeSchedule

/-!
# The corrected window estimate at Menon's literal `H`-adic schedule

Every structural side condition of
`integral_Icc_normSq_menonFinalRangeShell_le_partition_mass_filter` is discharged at the paper's
own ladder `Q = P(X)`, `η = exp(1/(log X)^(10 : ℕ)) − 1`, `L = ⌈H·log(⌊3X⌋/P(X))⌉`: the range coverage,
both cofactor endpoints, the block top, and the positivity of the base.  What is left is only the
schedule's own choice of thresholds `V j`, base levels `V₀ j` and level counts `J j`, and a level
count always exists.
-/

namespace RHTower.Sieve

open Filter Finset MeasureTheory

noncomputable section

/-- A level count always exists: any positive base level reaches any mass after finitely many
doublings. -/
theorem exists_levelCount (a : ℝ) {v : ℝ} (hv : 0 < v) : ∃ J : ℕ, a ≤ 2 ^ J * v := by
  obtain ⟨J, hJ⟩ := exists_nat_gt (a / v)
  refine ⟨J, ?_⟩
  have h2 : (J : ℝ) ≤ 2 ^ J := by
    have := Nat.lt_two_pow_self (n := J)
    exact_mod_cast this.le
  have hlt : a / v < 2 ^ J := lt_of_lt_of_le hJ h2
  rw [div_lt_iff₀ hv] at hlt
  linarith

/-- **Menon's shell on a frequency window, at the paper's literal ladder.**  No structural side
condition remains: only the schedule's own thresholds. -/
theorem eventually_integral_Icc_normSq_menonFinalRangeShell_le_ladderSchedule
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ᶠ x : ℝ in atTop,
      ∀ (W : ℝ) (V V₀ : ℕ → ℝ) (J : ℕ → ℕ),
        1 ≤ W → W ≤ x →
        (∀ j ∈ Finset.range (menonFinalRangeLadderSteps x), 0 < V j) →
        (∀ j ∈ Finset.range (menonFinalRangeLadderSteps x), 0 < V₀ j) →
        (∀ j ∈ Finset.range (menonFinalRangeLadderSteps x),
          harmonicPrimeMass (geomBlock (menonFinalRangePrimes x)
              (menonFinalRangeLadderBase x)
              (1 + menonFinalRangeLadderEta x) j) ≤ 2 ^ (J j) * V₀ j) →
        (∫ w in Set.Icc (-W) W,
          ‖logPoly harmonicMoebiusC (menonFinalRangeShell x) w‖ ^ (2 : ℕ))
          ≤ 2 * (harmonicPrimeMass (menonFinalRangePrimes x) *
                  ∑ j ∈ menonHarmonicActiveBlocks (menonFinalRangePrimes x)
                      (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x)
                      (menonFinalRangeLadderSteps x),
                  min (menonHarmonicAllSmallBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
                        (menonFinalRangeTopNat x) (menonFinalRangeLadderBase x)
                        (menonFinalRangeLadderEta x) W (V j)
                        (menonHarmonicAllBlocksSmall (menonFinalRangePrimes x)
                          (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x)
                          (menonFinalRangeLadderSteps x) V W) j)
                    (menonHarmonicSwappedBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
                      (menonFinalRangeTopNat x) (menonFinalRangeLadderBase x)
                      (menonFinalRangeLadderEta x) W
                      (menonHarmonicAllBlocksSmall (menonFinalRangePrimes x)
                        (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x)
                        (menonFinalRangeLadderSteps x) V W) j)
                    / harmonicPrimeMass (geomBlock (menonFinalRangePrimes x)
                        (menonFinalRangeLadderBase x)
                        (1 + menonFinalRangeLadderEta x) j)
              + harmonicPrimeMass (menonFinalRangePrimes x) *
                  ∑ j ∈ menonHarmonicActiveBlocks (menonFinalRangePrimes x)
                      (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x)
                      (menonFinalRangeLadderSteps x),
                  menonHarmonicLevelTrivialBlockCost (menonFinalRangePrimes x) ⌈x⌉₊
                      (menonFinalRangeTopNat x) (menonFinalRangeLadderBase x)
                      (menonFinalRangeLadderEta x) W
                      (menonHarmonicSomeLargeMomentBudget k (menonFinalRangeTopNat x)
                        (menonFinalRangeLadderBase x) (menonFinalRangeLadderEta x) W
                        (menonFinalRangeLadderSteps x) V) k j (J j) (V₀ j)
                    / harmonicPrimeMass (geomBlock (menonFinalRangePrimes x)
                        (menonFinalRangeLadderBase x)
                        (1 + menonFinalRangeLadderEta x) j))
            + 2 * menonFinalRangeHarmonicRoughEnergy x := by
  filter_upwards [eventually_menonFinalRangeLadder_basic,
    eventually_menonFinalRangePrimes_ladder_range,
    eventually_menonFinalRangeLadder_cofactor_endpoints] with x hbasic hrange hend
  intro W V V₀ J hW hWx hV hV₀ hJ
  rcases hbasic with ⟨hx1, _hH, hQ1, _htop, heta, hsteps⟩
  have hbase0 : 0 < menonFinalRangeLadderBase x := by linarith
  have hstep1 : (1 : ℝ) ≤ 1 + menonFinalRangeLadderEta x := by linarith
  have hx0 : 0 < x := lt_trans zero_lt_one hx1
  have hceil : 1 ≤ ⌈x⌉₊ := Nat.one_le_ceil_iff.2 hx0
  have htopj : ∀ j ∈ Finset.range (menonFinalRangeLadderSteps x),
      1 ≤ ⌊menonFinalRangeLadderBase x *
        (1 + menonFinalRangeLadderEta x) ^ (j + 1)⌋₊ := by
    intro j _
    refine Nat.le_floor ?_
    have hpow : (1 : ℝ) ≤ (1 + menonFinalRangeLadderEta x) ^ (j + 1) :=
      one_le_pow₀ hstep1
    have := mul_le_mul hQ1.le hpow zero_le_one hbase0.le
    push_cast
    nlinarith
  exact integral_Icc_normSq_menonFinalRangeShell_le_partition_mass_filter
    (x := x) (Q := menonFinalRangeLadderBase x) (eta := menonFinalRangeLadderEta x)
    (W := W) (L := menonFinalRangeLadderSteps x)
    k hk hceil hbase0 heta hW hWx hsteps hrange
    (fun j hj => (hend j hj).1) (fun j hj => (hend j hj).2) htopj
    V hV V₀ hV₀ J hJ

end

end RHTower.Sieve
