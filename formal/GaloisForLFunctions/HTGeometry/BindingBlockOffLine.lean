/-
Which block binds off the critical line, and why the record pair achieves nothing there.

At abscissa `s` the growth exponent is bounded by the worst dyadic block:

    μ(s) ≤ max over `0 ≤ c ≤ 1/2` of  ( E(c) - c·s ) ,

where `E(c)` is the best available exponent for `Σ_(n ∼ t^c) n^(-it)`.  A pair `(κ, λ)` gives
`E(c) ≤ min(c, κ + c(λ - κ))`, the two branches crossing at

    **c₀ = κ / (1 - λ + κ) = κ / (1/2 - d)** ,   `d = λ - κ - 1/2` .

For `s > 1/2` the trivial branch `c(1 - s)` increases and the pair branch has slope
`λ - κ - s = d + 1/2 - s`.  So:

* if `d ≤ s - 1/2` the pair branch decreases and the **crossover block `c₀` binds**, giving
  `μ(s) ≤ c₀(1 - s)`;
* if `d > s - 1/2` the pair branch increases and the **critical block binds**, giving
  `μ(s) ≤ κ + (d + 1/2 - s)/2`.

On the line of symmetry `d = 0`, so the crossover always binds and `c₀ = 2κ`: **every abscissa
`s > 1/2` is decided by the same block length `t^(2κ)`**, whereas at `s = 1/2` the whole range
`[2κ, 1/2]` binds equally.  Moving off the critical line therefore *concentrates* the problem onto a
single scale.

At that scale the record pair is exactly trivial: nontriviality at `c = 13/42` is `29κ + 13λ < 13`,
and Bourgain's pair gives `29·(13/84) + 13·(55/84) = 13` on the nose.  Its `A`-image is strictly
nontrivial there, with saving `169/8148 = 13²/(84·97)` — but its displacement `21/97` exceeds
`s - 1/2 = 1/5` at `s = 7/10` by `8/485`, so the critical block binds for it instead.
-/
import GaloisForLFunctions.HTGeometry.VanishingNeedsCorner

namespace HTGeometry

/-! ### The crossover block -/

/-- The block scale at which the trivial and exponent-pair branches cross. -/
def crossoverScale (κ d : ℚ) : ℚ := κ / (1 / 2 - d)

/-- **On the line of symmetry the crossover is at `2κ`.** -/
@[simp] theorem crossoverScale_on_line (κ : ℚ) : crossoverScale κ 0 = 2 * κ := by
  unfold crossoverScale; norm_num
  ring

/-- For the record pair it is `13/42`. -/
@[simp] theorem crossoverScale_bourgain : crossoverScale bourgainKappa 0 = 13 / 42 := by
  rw [crossoverScale_on_line]; unfold bourgainKappa; norm_num

/-- The slope of the pair branch of `E(c) - c·s`. -/
def pairBranchSlope (d s : ℚ) : ℚ := d + 1 / 2 - s

/-- **The crossover binds exactly when the displacement does not exceed the distance from the
critical line.** -/
theorem crossover_binds_iff (d s : ℚ) : pairBranchSlope d s ≤ 0 ↔ d ≤ s - 1 / 2 := by
  unfold pairBranchSlope
  constructor <;> intro h <;> linarith

/-- **On the line the crossover always binds off the critical line.** -/
theorem line_crossover_binds {s : ℚ} (h : 1 / 2 ≤ s) : pairBranchSlope 0 s ≤ 0 := by
  unfold pairBranchSlope; linarith

/-- **And the resulting profile is the linear one.** -/
theorem line_profile_from_crossover (κ s : ℚ) :
    crossoverScale κ 0 * (1 - s) = linePairProfile κ s := by
  rw [crossoverScale_on_line]
  unfold linePairProfile; ring

/-! ### Concentration off the critical line -/

/-- At the critical line the pair branch of `E(c) - c/2` is constant, equal to `κ`. -/
theorem critical_line_branch_constant (κ c : ℚ) :
    blockPairBound κ c - c * (1 / 2) = κ := by
  unfold blockPairBound; ring

/-- **So at `s = 1/2` every block from the crossover upward binds equally** — the campaign's earlier
observation that each dyadic block contributes the same amount. -/
theorem all_blocks_bind_at_critical (κ c c' : ℚ) :
    blockPairBound κ c - c * (1 / 2) = blockPairBound κ c' - c' * (1 / 2) := by
  rw [critical_line_branch_constant, critical_line_branch_constant]

/-- **Off the critical line the pair branch is strictly decreasing**, so only the crossover binds. -/
theorem off_line_branch_decreasing {s c c' : ℚ} (hs : 1 / 2 < s) (h : c < c') :
    blockPairBound 0 c' - c' * s < blockPairBound 0 c - c * s := by
  unfold blockPairBound; nlinarith

/-! ### Nontriviality at the binding block -/

/-- The nontriviality condition for a pair at the block scale `13/42`. -/
def nontrivialAtThirteenFortyTwo (κ lam : ℚ) : Prop := 29 * κ + 13 * lam < 13

/-- **The record pair is exactly trivial at its own binding block.** -/
theorem record_exactly_trivial_at_binding :
    29 * bourgainKappa + 13 * bourgainLambda = 13 := by
  unfold bourgainKappa bourgainLambda; norm_num

/-- **Its `A`-image is strictly nontrivial there.** -/
theorem procA_bourgain_nontrivial_at_binding :
    nontrivialAtThirteenFortyTwo (procA_fst bourgainKappa)
      (procA_snd bourgainKappa bourgainLambda) := by
  rw [procA_bourgain.1, procA_bourgain.2]
  unfold nontrivialAtThirteenFortyTwo; norm_num

/-- The `A`-image's block exponent at `13/42`. -/
theorem procA_bourgain_block_exponent :
    procA_fst bourgainKappa
        + (13 / 42) * (procA_snd bourgainKappa bourgainLambda - procA_fst bourgainKappa)
      = 2353 / 8148 := by
  rw [procA_bourgain.1, procA_bourgain.2]; norm_num

/-- **The saving over the trivial bound is `169/8148 = 13²/(84·97)`.** -/
theorem procA_bourgain_block_saving :
    (13 : ℚ) / 42 - 2353 / 8148 = 169 / 8148 ∧ (169 : ℚ) = 13 ^ 2 := by
  constructor <;> norm_num

/-! ### But the displacement penalty overrides it at `σ = 7/10` -/

/-- **The `A`-image's displacement exceeds the distance from the critical line at `s = 7/10`.** -/
theorem procA_displacement_exceeds_distance :
    (7 : ℚ) / 10 - 1 / 2 < epDisplacement (procA_fst bourgainKappa)
      (procA_snd bourgainKappa bourgainLambda) := by
  rw [procA_bourgain_displacement]; norm_num

/-- By exactly `8/485`. -/
theorem procA_displacement_excess :
    epDisplacement (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
      - ((7 : ℚ) / 10 - 1 / 2) = 8 / 485 := by
  rw [procA_bourgain_displacement]; norm_num

/-- **Hence for the `A`-image the critical block binds at `σ = 7/10`, not the crossover.** -/
theorem procA_critical_block_binds :
    ¬ (pairBranchSlope (epDisplacement (procA_fst bourgainKappa)
        (procA_snd bourgainKappa bourgainLambda)) (7 / 10) ≤ 0) := by
  rw [crossover_binds_iff]
  have := procA_displacement_exceeds_distance
  linarith

/-- **The trade, exactly.**  The `A`-image buys a saving of `169/8148` at the binding block but pays a
displacement excess of `8/485` at `σ = 7/10`, and the second decides which block binds. -/
theorem binding_block_trade :
    (13 : ℚ) / 42 - 2353 / 8148 = 169 / 8148 ∧
      epDisplacement (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
        - ((7 : ℚ) / 10 - 1 / 2) = 8 / 485 := by
  exact ⟨procA_bourgain_block_saving.1, procA_displacement_excess⟩

/-- **The single-scale conclusion.**  For a pair on the line, every abscissa `s > 1/2` is decided by
the same block `t^(2κ)`, where the pair's bound coincides with the trivial one.  So any nontrivial
cancellation at that one length improves `μ(σ)` for **every** `σ > 1/2` at once. -/
theorem single_scale_conclusion :
    crossoverScale bourgainKappa 0 = 13 / 42 ∧
      blockPairBound bourgainKappa (13 / 42) = 13 / 42 ∧
      29 * bourgainKappa + 13 * bourgainLambda = 13 := by
  refine ⟨crossoverScale_bourgain, ?_, record_exactly_trivial_at_binding⟩
  unfold blockPairBound bourgainKappa; norm_num

end HTGeometry
