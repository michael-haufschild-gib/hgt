/-
Duality between the growth exponent off the critical line and the block exponent at a scale.

A contour shift converts a growth bound at abscissa `σ` into a bound for the block
`Σ_(n ∼ T^c) n^(-it)`, of size `T^(c/2) · T^(μ(σ) + c(σ - 1/2))`.  So the **block exponent** that
off-line data at `σ` delivers at scale `T^c` is

    **blockBound(c, σ) = μ(σ) + c·(σ - 1/2)** ,

the affine form `κ + c·d` of an exponent pair with `κ = μ(σ)` and `d = σ - 1/2`.  The block exponent
function is therefore the concave conjugate `inf_σ blockBound(·, σ)` of the growth exponent, and the
exponent-pair region is conjugate to the epigraph of `μ`.

Three exact consequences.

* **The functional equation is the simultaneous reflection.**  `blockBound(c, 1-σ) = blockBound(1-c, σ)`:
  reflecting the abscissa *is* reflecting the scale, by the same involution `x ↦ 1 - x` that the
  van der Corput `B`-process performs on lengths.

* **The critical scale is exactly as hard as the critical line.**  `μ(1/2) ≤ blockBound(1/2, σ)` for
  every `σ`, with equality at `σ = 1/2`, so `μ(1/2) = inf_σ blockBound(1/2, σ)`.  Off-line data can
  never improve the critical scale: conjugation is lossless, and round-tripping gains nothing.

* **Freeing a scale is strictly cheaper than transferring.**  At target `β`, a datum `μ(σ₀) ≤ m₀`
  makes every scale `c ≤ (β - m₀)/(σ₀ - 1/2)` meet the target by itself.  With `σ₀ = 1`, `m₀ = 0` this
  is the trivial threshold `2β`; the datum beats it **iff `m₀ < 2β(1 - σ₀)`**, i.e. iff `(σ₀, m₀)` lies
  strictly below the chord from `(1/2, β)` to `(1, 0)`.  The freed range reaches the critical scale
  `c = 1/2` **iff `m₀ + (σ₀ - 1/2)/2 ≤ β`** — the off-line transfer condition.  Hence the transfer
  theorem is the endpoint of a one-parameter family of scale-freeing statements, every interior member
  of which is strictly weaker, the gap being `(σ₀ - 1/2)(1/2 - 2β)`.

Since `m₀ ≥ 0`, an abscissa `σ₀ > 1/2 + 2β` can never transfer to the critical line at level `β`,
while it still frees scales for every `σ₀ < 1`.  At `β = 13/84` the transfer limit is `σ₀ = 17/21`,
the abscissa at which the record's growth bound vanishes.
-/
import GaloisForLFunctions.HTGeometry.OffLineTransfer
import GaloisForLFunctions.HTGeometry.ArchitectureSensitivity

namespace HTGeometry

namespace GrowthExponent

variable (G : GrowthExponent)

/-! ### The block exponent delivered by off-line data -/

/-- The block exponent at scale `T^c` obtained from the growth bound at abscissa `σ`. -/
def blockBound (c σ : ℚ) : ℚ := G.mu σ + c * (σ - 1 / 2)

/-- **At the critical abscissa the delivered bound is flat in the scale.** -/
@[simp] theorem blockBound_at_half (c : ℚ) : G.blockBound c (1 / 2) = G.mu (1 / 2) := by
  unfold blockBound; ring

/-- **The functional equation reflects abscissa and scale simultaneously.** -/
theorem blockBound_reflect (c σ : ℚ) : G.blockBound c (1 - σ) = G.blockBound (1 - c) σ := by
  unfold blockBound
  have h := G.functionalEquation σ
  have : G.mu (1 - σ) = G.mu σ + σ - 1 / 2 := by linarith
  rw [this]; ring

/-- The reflection is an involution in the scale variable. -/
theorem blockBound_reflect_twice (c σ : ℚ) :
    G.blockBound (1 - (1 - c)) σ = G.blockBound c σ := by
  norm_num

/-- **Above the critical abscissa the delivered bound grows with the scale.** -/
theorem blockBound_mono {σ : ℚ} (hσ : 1 / 2 ≤ σ) {c c' : ℚ} (h : c ≤ c') :
    G.blockBound c σ ≤ G.blockBound c' σ := by
  unfold blockBound
  have : c * (σ - 1 / 2) ≤ c' * (σ - 1 / 2) :=
    mul_le_mul_of_nonneg_right h (by linarith)
  linarith

/-! ### The critical scale is exactly the critical line -/

/-- **No abscissa delivers anything better than `μ(1/2)` at the critical scale.** -/
theorem mu_half_le_blockBound_half (σ : ℚ) : G.mu (1 / 2) ≤ G.blockBound (1 / 2) σ := by
  unfold blockBound
  have h := G.mu_half_le σ
  linarith

/-- **And the critical abscissa attains it.**  So `μ(1/2) = inf_σ blockBound(1/2, σ)`: conjugating the
growth exponent and reading it back at the critical scale is lossless. -/
theorem blockBound_half_isLeast :
    G.blockBound (1 / 2) (1 / 2) = G.mu (1 / 2) ∧
      ∀ σ : ℚ, G.mu (1 / 2) ≤ G.blockBound (1 / 2) σ :=
  ⟨G.blockBound_at_half _, G.mu_half_le_blockBound_half⟩

/-! ### Freeing scales -/

/-- The largest scale exponent that a datum `μ(σ₀) ≤ m₀` frees at target `β`. -/
def freeThreshold (m₀ σ₀ β : ℚ) : ℚ := (β - m₀) / (σ₀ - 1 / 2)

/-- **A scale is freed exactly below the threshold.** -/
theorem free_iff {m₀ σ₀ β c : ℚ} (hσ : 1 / 2 < σ₀) (hm : G.mu σ₀ ≤ m₀) :
    c ≤ freeThreshold m₀ σ₀ β → G.blockBound c σ₀ ≤ β := by
  intro h
  have hpos : (0 : ℚ) < σ₀ - 1 / 2 := by linarith
  rw [freeThreshold, le_div_iff₀ hpos] at h
  unfold blockBound
  linarith

/-- **The trivial threshold.**  The datum `μ(1) = 0` frees every scale below `2β`. -/
theorem freeThreshold_trivial (β : ℚ) : freeThreshold 0 1 β = 2 * β := by
  unfold freeThreshold
  norm_num
  ring

/-- **The chord criterion.**  A datum beats the trivial threshold exactly when it lies strictly below
the chord joining `(1/2, β)` to `(1, 0)`. -/
theorem freeThreshold_beats_trivial {m₀ σ₀ β : ℚ} (hσ : 1 / 2 < σ₀) :
    2 * β < freeThreshold m₀ σ₀ β ↔ m₀ < 2 * β * (1 - σ₀) := by
  have hpos : (0 : ℚ) < σ₀ - 1 / 2 := by linarith
  rw [freeThreshold, lt_div_iff₀ hpos]
  constructor <;> intro h <;> nlinarith

/-- **The transfer condition is the endpoint.**  The freed range reaches the critical scale exactly
when the off-line transfer already proves the target. -/
theorem freeThreshold_reaches_critical {m₀ σ₀ β : ℚ} (hσ : 1 / 2 < σ₀) :
    1 / 2 ≤ freeThreshold m₀ σ₀ β ↔ m₀ + (σ₀ - 1 / 2) / 2 ≤ β := by
  have hpos : (0 : ℚ) < σ₀ - 1 / 2 := by linarith
  rw [freeThreshold, le_div_iff₀ hpos]
  constructor <;> intro h <;> linarith

/-- **Freeing is strictly cheaper than transferring**, by exactly `(σ₀ - 1/2)(1/2 - 2β)`. -/
theorem freeing_cheaper_than_transfer (σ₀ β : ℚ) :
    2 * β * (1 - σ₀) - (β - (σ₀ - 1 / 2) / 2) = (σ₀ - 1 / 2) * (1 / 2 - 2 * β) := by
  ring

/-- **Below the convexity bound the gap is strictly positive off the critical line.** -/
theorem freeing_gap_pos {σ₀ β : ℚ} (hσ : 1 / 2 < σ₀) (hβ : β < 1 / 4) :
    β - (σ₀ - 1 / 2) / 2 < 2 * β * (1 - σ₀) := by
  nlinarith

/-! ### The transfer limit -/

/-- **An abscissa beyond `1/2 + 2β` cannot transfer to the critical line at level `β`.** -/
theorem transfer_limit {m₀ σ₀ β : ℚ} (hm : 0 ≤ m₀) (h : m₀ + (σ₀ - 1 / 2) / 2 ≤ β) :
    σ₀ ≤ 1 / 2 + 2 * β := by
  linarith

/-! ### What a datum below the chord buys -/

/-- A datum at `σ₀ = 3/4` must beat `13/168` to free more than the trivial range, but must beat the
much smaller `5/168` to transfer — a factor `13/5`. -/
theorem chord_versus_transfer_at_three_quarters :
    2 * bourgainTheta * (1 - 3 / 4) = 13 / 168 ∧
      bourgainTheta - (3 / 4 - 1 / 2) / 2 = 5 / 168 ∧
      (13 : ℚ) / 168 = (13 / 5) * (5 / 168) := by
  unfold bourgainTheta
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- A datum `μ(3/4) ≤ 1/24` lies below the chord and frees every scale up to `19/42`, past the
threshold `17/42` at which the final source of the covering architecture becomes available — yet it
falls short of transferring, since `1/24 > 5/168`. -/
theorem free_range_past_decoupling :
    freeThreshold (1 / 24) (3 / 4) bourgainTheta = 19 / 42 ∧
      (17 : ℚ) / 42 < 19 / 42 ∧
      (1 : ℚ) / 24 < 13 / 168 ∧ (5 : ℚ) / 168 < 1 / 24 := by
  unfold freeThreshold bourgainTheta
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Summary.**  The block exponent is the conjugate of the growth exponent; the functional equation
is the simultaneous reflection of abscissa and scale; the critical scale is exactly as hard as the
critical line, so conjugation is lossless; and the off-line transfer condition is precisely the
statement that the freed range of scales reaches the critical scale. -/
theorem scale_abscissa_duality (c σ : ℚ) :
    G.blockBound c (1 - σ) = G.blockBound (1 - c) σ ∧
      G.blockBound c (1 / 2) = G.mu (1 / 2) ∧
      G.mu (1 / 2) ≤ G.blockBound (1 / 2) σ :=
  ⟨G.blockBound_reflect c σ, G.blockBound_at_half c, G.mu_half_le_blockBound_half σ⟩

end GrowthExponent

end HTGeometry
