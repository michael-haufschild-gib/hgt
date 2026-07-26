/-
Why the vanishing abscissa is stuck at `1`: the obstruction is at the small blocks.

For `μ(s) = 0` the approximate functional equation at abscissa `s` requires every dyadic block to be
bounded: `M^(-s)·|Σ_(n∼M) n^(-it)| ≪ t^ε`, i.e. writing `M = t^c` with `0 < c ≤ 1/2`,

    **required exponent at the block:  c·s** .

An exponent pair on the line of symmetry, `(κ, κ + 1/2)`, gives the block bound `t^(κ + c/2)`.  So it
covers the block exactly when

    κ + c/2 ≤ c·s ,   i.e.   **κ ≤ c·(s - 1/2)** ,   i.e.   **c ≥ κ/(s - 1/2)** .

Two consequences.

* At `s = 17/21` and `κ = 13/84` the threshold is exactly `c = 1/2`: **the record pair covers the
  critical block and nothing below it.**  This is why `17/21` is the abscissa attached to the record.
* Letting `c → 0` forces `κ ≤ 0`.  **No exponent pair with `κ > 0` proves `μ(s) = 0` for any `s`**, and
  the obstruction sits at the *small* blocks — the opposite end from the critical-line obstruction,
  which sits at `c = 1/2`.

The reason is the `t^κ` floor: the pair's bound does not shrink with the block, while the requirement
`c·s` does.  So the vanishing route, like the Farey-numerator target, collapses to the corner `κ = 0`.
-/
import GaloisForLFunctions.HTGeometry.VanishingTransfer

namespace HTGeometry

/-! ### Block requirement and block bound -/

/-- The exponent a block of length `t^c` must achieve for `μ(s) = 0`. -/
def blockRequirement (s c : ℚ) : ℚ := c * s

/-- The exponent a line exponent pair delivers at that block. -/
def blockPairBound (κ c : ℚ) : ℚ := κ + c / 2

/-- **The pair covers the block exactly when `κ ≤ c(s - 1/2)`.** -/
theorem pair_covers_block_iff (κ s c : ℚ) :
    blockPairBound κ c ≤ blockRequirement s c ↔ κ ≤ c * (s - 1 / 2) := by
  unfold blockPairBound blockRequirement
  constructor <;> intro h <;> nlinarith

/-- The smallest block the pair covers. -/
def coverageThreshold (κ s : ℚ) : ℚ := κ / (s - 1 / 2)

/-- **Coverage is exactly the condition `c ≥ κ/(s - 1/2)`.** -/
theorem pair_covers_iff_threshold {κ s c : ℚ} (hs : 1 / 2 < s) :
    blockPairBound κ c ≤ blockRequirement s c ↔ coverageThreshold κ s ≤ c := by
  rw [pair_covers_block_iff]
  unfold coverageThreshold
  rw [div_le_iff₀ (by linarith : (0:ℚ) < s - 1 / 2)]

/-! ### The record's abscissa is the critical-block threshold -/

/-- **At the record pair and `s = 17/21` the coverage threshold is exactly the critical block.** -/
theorem record_threshold_is_critical_block :
    coverageThreshold bourgainKappa (17 / 21) = 1 / 2 := by
  unfold coverageThreshold bourgainKappa; norm_num

/-- **So the record pair covers the critical block at `s = 17/21` with equality.** -/
theorem record_covers_critical_block :
    blockPairBound bourgainKappa (1 / 2) = blockRequirement (17 / 21) (1 / 2) := by
  unfold blockPairBound blockRequirement bourgainKappa; norm_num

/-- **And fails at every smaller block.** -/
theorem record_fails_below_critical {c : ℚ} (h : c < 1 / 2) :
    ¬ (blockPairBound bourgainKappa c ≤ blockRequirement (17 / 21) c) := by
  rw [pair_covers_iff_threshold (by norm_num), record_threshold_is_critical_block]
  linarith

/-- Explicitly at `c = 1/4`: the pair gives `0.2798…` where `0.2024…` is required. -/
theorem record_fails_at_quarter :
    blockRequirement (17 / 21) (1 / 4) < blockPairBound bourgainKappa (1 / 4) := by
  unfold blockRequirement blockPairBound bourgainKappa; norm_num

/-! ### The small blocks force the corner -/

/-- **A positive `κ` leaves a block uncovered.**  Half the coverage threshold is a positive block the
pair misses. -/
theorem positive_kappa_misses_a_block {κ s : ℚ} (hκ : 0 < κ) (hs : 1 / 2 < s) :
    0 < coverageThreshold κ s / 2 ∧
      ¬ (blockPairBound κ (coverageThreshold κ s / 2)
          ≤ blockRequirement s (coverageThreshold κ s / 2)) := by
  have hd : 0 < s - 1 / 2 := by linarith
  have hth : 0 < coverageThreshold κ s := by
    unfold coverageThreshold; exact div_pos hκ hd
  refine ⟨by linarith, ?_⟩
  rw [pair_covers_iff_threshold hs]
  linarith

/-- **Covering every block down to zero forces `κ ≤ 0`.** -/
theorem coverage_of_all_blocks_forces_corner {κ s : ℚ} (hκ : 0 ≤ κ) (hs : 1 / 2 < s)
    (hall : ∀ c : ℚ, 0 < c → c ≤ 1 / 2 → blockPairBound κ c ≤ blockRequirement s c) :
    κ = 0 := by
  by_contra hne
  have hpos : 0 < κ := lt_of_le_of_ne hκ (Ne.symm hne)
  obtain ⟨hcpos, hmiss⟩ := positive_kappa_misses_a_block hpos hs
  have hd : 0 < s - 1 / 2 := by linarith
  have hth : 0 < coverageThreshold κ s := by
    unfold coverageThreshold; exact div_pos hpos hd
  by_cases hsmall : coverageThreshold κ s / 2 ≤ 1 / 2
  · exact hmiss (hall _ hcpos hsmall)
  · have hbig : (1 : ℚ) / 2 < coverageThreshold κ s / 2 := by linarith
    have hquarter := hall (1 / 2) (by norm_num) le_rfl
    rw [pair_covers_iff_threshold hs] at hquarter
    linarith

/-- **Hence the vanishing route collapses to the corner.**  A line exponent pair proves `μ(s) = 0` for
some `s > 1/2` only if `κ = 0`, which with `λ = κ + 1/2` is the exponent-pair conjecture `(0, 1/2)`. -/
theorem vanishing_route_needs_corner {κ s : ℚ} (hκ : 0 ≤ κ) (hs : 1 / 2 < s)
    (hall : ∀ c : ℚ, 0 < c → c ≤ 1 / 2 → blockPairBound κ c ≤ blockRequirement s c) :
    κ = 0 ∧ epMu κ (κ + 1 / 2) = 0 := by
  have hz := coverage_of_all_blocks_forces_corner hκ hs hall
  refine ⟨hz, ?_⟩
  rw [hz]
  unfold epMu; norm_num

/-! ### The two obstructions sit at opposite ends -/

/-- **The critical-line obstruction is at the top block, the vanishing obstruction at the bottom.**
For the record pair at `s = 17/21` the covered set of block scales is exactly `{1/2}`. -/
theorem obstructions_at_opposite_ends {c : ℚ} (h1 : c ≤ 1 / 2) :
    (blockPairBound bourgainKappa c ≤ blockRequirement (17 / 21) c) ↔ c = 1 / 2 := by
  rw [pair_covers_iff_threshold (by norm_num), record_threshold_is_critical_block]
  constructor
  · intro h; linarith
  · intro h; linarith

/-- **The unification.**  Three targets — the subconvexity record, the Farey-numerator square-root
bound, and the vanishing abscissa — all reduce inside the exponent-pair framework to `κ = 0`.  Only
methods that do not factor through an exponent pair can separate them. -/
theorem three_targets_one_corner {κ s : ℚ} (hκ : 0 ≤ κ) (hs : 1 / 2 < s)
    (hall : ∀ c : ℚ, 0 < c → c ≤ 1 / 2 → blockPairBound κ c ≤ blockRequirement s c) :
    epMu κ (κ + 1 / 2) = 0 ∧ epDisplacement κ (κ + 1 / 2) = 0 := by
  refine ⟨(vanishing_route_needs_corner hκ hs hall).2, ?_⟩
  unfold epDisplacement; ring

end HTGeometry
