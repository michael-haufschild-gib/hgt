/-
The coverage geometry of a two-regime spacing endgame.

A spacing endgame for a sixth-power large-value quantity `A = S^(6 : ℕ)` attached to a Dirichlet polynomial
of length `M` at height `T` supplies two source bounds and asks for one target:

    source, upper regime :   A ≤ M^(4 : ℕ) · T^b     for  M ≥ T^m
    source, lower regime :   A ≤ M^(2 : ℕ) · T^c     for  M < T^m
    target               :   A ≤ M^(3 : ℕ) · T^(6θ)      (i.e. `S ≤ M^(1/2) T^θ`)

Everything below is an identity or inequality in the three exponents `(b, c, θ)`; no analytic input
is used.

Write `M = T^x`.  Each bound becomes a line in `x`: the sources are `p x + b` with `p = 4` and
`q x + c` with `q = 2`, the target is `r x + 6θ` with `r = 3`.  Since the upper regime is used
exactly where it is the *weaker* of the two, the bound actually available at `x` is the upper
envelope

    E(x) = max (4x + b, 2x + c),

a convex piecewise-linear function whose corner sits at `m = (c - b)/2`.  A source bound implies the
target at `x` precisely when `E(x) ≤ r x + 6θ`, i.e. when `x` lies in the sublevel set

    { x : E(x) - r x ≤ 6θ } .

Because `q < r < p`, the function `E(x) - r x` is convex with slopes `-1` and `+1`, so it attains its
minimum at the corner and the sublevel set is a **closed interval centred at the corner**:

    [ c - 6θ , 6θ - b ] ,   centre  (c - b)/2 ,   width  12θ - (b + c).

Three consequences, all proved below:

* the endpoints sum to `c - b` **independently of `θ`**, and their midpoint is the regime crossover,
  also independent of `θ`: improving the target contracts the interval symmetrically about a centre
  that cannot move;
* the interval is nonempty exactly when `θ ≥ (b + c)/12`, so `(b + c)/12` is the exponent below which
  **the two spacing estimates cover no length `M` whatsoever** and the entire endgame would have to
  be carried by the direct estimate alone;
* the amount by which the sources beat the target at the corner is exactly `6(θ - (b+c)/12)` — the
  whole surplus the spacing estimates have to spend, and exactly half the coverage width.

For Bourgain's exponents `b = 1/2`, `c = 4/3` this gives corner `5/12`, threshold `11/72`, and at the
record `θ = 13/84` a coverage interval `[17/42, 3/7]` of width `1/42` bought by a corner surplus of
`1/84`.  The record therefore sits `1/504` above the exponent at which its own spacing estimates stop
contributing.
-/
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace HTGeometry

/-! ### The three lines -/

/-- Exponent of the target `M^(3 : ℕ) T^(6θ)` at `M = T^x`. -/
def sixthTargetExponent (θ x : ℚ) : ℚ := 3 * x + 6 * θ

/-- Exponent of the upper-regime source `M^(4 : ℕ) T^b` at `M = T^x`. -/
def sourceExponentMid (b x : ℚ) : ℚ := 4 * x + b

/-- Exponent of the lower-regime source `M^(2 : ℕ) T^c` at `M = T^x`. -/
def sourceExponentLow (c x : ℚ) : ℚ := 2 * x + c

/-- The crossover between the two source regimes: the corner of their upper envelope. -/
def spacingCrossover (b c : ℚ) : ℚ := (c - b) / 2

/-- At the crossover the two source exponents agree. -/
theorem spacing_crossover_balances (b c : ℚ) :
    sourceExponentMid b (spacingCrossover b c) = sourceExponentLow c (spacingCrossover b c) := by
  unfold sourceExponentMid sourceExponentLow spacingCrossover; ring

/-- Above the crossover the upper-regime line is the larger of the two, so it is the envelope. -/
theorem mid_is_envelope_above {b c x : ℚ} (hx : spacingCrossover b c ≤ x) :
    sourceExponentLow c x ≤ sourceExponentMid b x := by
  unfold sourceExponentLow sourceExponentMid spacingCrossover at *; linarith

/-- Below the crossover the lower-regime line is the larger of the two. -/
theorem low_is_envelope_below {b c x : ℚ} (hx : x ≤ spacingCrossover b c) :
    sourceExponentMid b x ≤ sourceExponentLow c x := by
  unfold sourceExponentLow sourceExponentMid spacingCrossover at *; linarith

/-! ### The coverage interval -/

/-- Left endpoint of the set of lengths on which a source bound implies the target. -/
def spacingLowerEndpoint (c θ : ℚ) : ℚ := c - 6 * θ

/-- Right endpoint of the set of lengths on which a source bound implies the target. -/
def spacingUpperEndpoint (b θ : ℚ) : ℚ := 6 * θ - b

/-- Length of the interval of lengths covered by the two spacing estimates. -/
def spacingCoverageWidth (b c θ : ℚ) : ℚ :=
  spacingUpperEndpoint b θ - spacingLowerEndpoint c θ

/-- The exponent below which the spacing estimates cover no length at all. -/
def spacingCoverageFloor (b c : ℚ) : ℚ := (b + c) / 12

/-- **Left of the left endpoint the lower regime is strictly weaker than the target.** -/
theorem low_regime_fails_below {c θ x : ℚ} (hx : x ≤ spacingLowerEndpoint c θ) :
    sixthTargetExponent θ x ≤ sourceExponentLow c x := by
  unfold sixthTargetExponent sourceExponentLow spacingLowerEndpoint at *; linarith

/-- **On the left half of the coverage interval the lower regime implies the target.** -/
theorem low_regime_implies_target {c θ x : ℚ} (hx : spacingLowerEndpoint c θ ≤ x) :
    sourceExponentLow c x ≤ sixthTargetExponent θ x := by
  unfold sixthTargetExponent sourceExponentLow spacingLowerEndpoint at *; linarith

/-- **Right of the right endpoint the upper regime is strictly weaker than the target.** -/
theorem mid_regime_fails_above {b θ x : ℚ} (hx : spacingUpperEndpoint b θ ≤ x) :
    sixthTargetExponent θ x ≤ sourceExponentMid b x := by
  unfold sixthTargetExponent sourceExponentMid spacingUpperEndpoint at *; linarith

/-- **On the right half of the coverage interval the upper regime implies the target.** -/
theorem mid_regime_implies_target {b θ x : ℚ} (hx : x ≤ spacingUpperEndpoint b θ) :
    sourceExponentMid b x ≤ sixthTargetExponent θ x := by
  unfold sixthTargetExponent sourceExponentMid spacingUpperEndpoint at *; linarith

/-- At the left endpoint the lower regime meets the target **exactly**. -/
theorem spacing_tight_at_lower (c θ : ℚ) :
    sourceExponentLow c (spacingLowerEndpoint c θ)
      = sixthTargetExponent θ (spacingLowerEndpoint c θ) := by
  unfold sourceExponentLow sixthTargetExponent spacingLowerEndpoint; ring

/-- At the right endpoint the upper regime meets the target **exactly**. -/
theorem spacing_tight_at_upper (b θ : ℚ) :
    sourceExponentMid b (spacingUpperEndpoint b θ)
      = sixthTargetExponent θ (spacingUpperEndpoint b θ) := by
  unfold sourceExponentMid sixthTargetExponent spacingUpperEndpoint; ring

/-! ### The centre cannot move -/

/-- **The endpoints sum to `c - b`, with no dependence on `θ`.**  Improving the target contracts the
coverage interval; it cannot translate it. -/
theorem spacing_endpoints_sum (b c θ : ℚ) :
    spacingLowerEndpoint c θ + spacingUpperEndpoint b θ = c - b := by
  unfold spacingLowerEndpoint spacingUpperEndpoint; ring

/-- **The crossover is exactly the midpoint of the coverage interval**, for every target. -/
theorem spacing_crossover_is_midpoint (b c θ : ℚ) :
    (spacingLowerEndpoint c θ + spacingUpperEndpoint b θ) / 2 = spacingCrossover b c := by
  rw [spacing_endpoints_sum]; unfold spacingCrossover; ring

/-! ### The floor -/

/-- The coverage width is `12θ - (b + c)`. -/
theorem spacing_coverage_width_eq (b c θ : ℚ) :
    spacingCoverageWidth b c θ = 12 * θ - (b + c) := by
  unfold spacingCoverageWidth spacingUpperEndpoint spacingLowerEndpoint; ring

/-- The width is twelve times the distance to the floor. -/
theorem spacing_coverage_width_eq_floor_gap (b c θ : ℚ) :
    spacingCoverageWidth b c θ = 12 * (θ - spacingCoverageFloor b c) := by
  rw [spacing_coverage_width_eq]; unfold spacingCoverageFloor; ring

/-- **The coverage interval degenerates to a point exactly at the floor.** -/
theorem spacing_coverage_closes_iff (b c θ : ℚ) :
    spacingCoverageWidth b c θ = 0 ↔ θ = spacingCoverageFloor b c := by
  rw [spacing_coverage_width_eq_floor_gap]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h' | h'
    · norm_num at h'
    · linarith
  · intro h; rw [h]; ring

/-- **The spacing estimates cover a nonempty range of lengths only above the floor.**  If the target
exponent drops below `(b+c)/12`, the interval on which either source implies the target is empty:
every length would have to be handled by the direct estimate alone. -/
theorem spacing_coverage_nonempty_iff (b c θ : ℚ) :
    spacingLowerEndpoint c θ ≤ spacingUpperEndpoint b θ ↔ spacingCoverageFloor b c ≤ θ := by
  constructor
  · intro h
    have hw : 0 ≤ spacingCoverageWidth b c θ := by
      unfold spacingCoverageWidth; linarith
    rw [spacing_coverage_width_eq_floor_gap] at hw
    nlinarith
  · intro h
    have hw : (0 : ℚ) ≤ 12 * (θ - spacingCoverageFloor b c) := by nlinarith
    rw [← spacing_coverage_width_eq_floor_gap] at hw
    unfold spacingCoverageWidth at hw; linarith

/-- **The surplus at the crossover is six times the distance to the floor.**  This is the entire
resource the two spacing estimates have: the amount by which they beat the target at the centre of
their range. -/
theorem spacing_crossover_surplus (b c θ : ℚ) :
    sixthTargetExponent θ (spacingCrossover b c) - sourceExponentLow c (spacingCrossover b c)
      = 6 * (θ - spacingCoverageFloor b c) := by
  unfold sixthTargetExponent sourceExponentLow spacingCrossover spacingCoverageFloor; ring

/-- The corner surplus is exactly half the coverage width: the sources spend their surplus at unit
rate on each side of the crossover. -/
theorem spacing_surplus_eq_half_width (b c θ : ℚ) :
    2 * (sixthTargetExponent θ (spacingCrossover b c)
          - sourceExponentLow c (spacingCrossover b c))
      = spacingCoverageWidth b c θ := by
  rw [spacing_crossover_surplus, spacing_coverage_width_eq_floor_gap]; ring

/-! ### The general envelope statement

For source slopes `p > q`, target slope `r` with `q < r < p`, and intercepts `b` (upper) and `c`
(lower), the same argument gives the corner and the floor.  The floor is the value at the corner of
the source envelope measured against the target's slope — a Legendre-type quantity.
-/

/-- Corner of the envelope of two source lines of slopes `p > q` and intercepts `b`, `c`. -/
def envelopeCorner (p q b c : ℚ) : ℚ := (c - b) / (p - q)

/-- The two source lines agree at the corner. -/
theorem envelope_corner_balances {p q b c : ℚ} (h : p ≠ q) :
    p * envelopeCorner p q b c + b = q * envelopeCorner p q b c + c := by
  have hpq : p - q ≠ 0 := sub_ne_zero.mpr h
  unfold envelopeCorner
  field_simp
  ring

/-- The intercept the target must carry in order to reach the corner of the source envelope. -/
def envelopeFloor (p q r b c : ℚ) : ℚ :=
  (p * envelopeCorner p q b c + b) - r * envelopeCorner p q b c

/-- **Bourgain's slopes specialise the general floor to `(b+c)/2`,** whose sixth part is the coverage
floor `(b+c)/12` in the target exponent `θ`. -/
theorem envelopeFloor_bourgain_slopes (b c : ℚ) :
    envelopeFloor 4 2 3 b c = (b + c) / 2 := by
  unfold envelopeFloor envelopeCorner
  norm_num
  ring

/-- The general floor divided by the moment order recovers the coverage floor. -/
theorem envelopeFloor_div_six (b c : ℚ) :
    envelopeFloor 4 2 3 b c / 6 = spacingCoverageFloor b c := by
  rw [envelopeFloor_bourgain_slopes]; unfold spacingCoverageFloor; ring

/-- **The floor is a convex combination of the two source intercepts**, with weights given by where
the target slope sits between the source slopes. -/
theorem envelopeFloor_is_convex_combination {p q r b c : ℚ} (h : p ≠ q) :
    envelopeFloor p q r b c
      = ((r - q) / (p - q)) * b + ((p - r) / (p - q)) * c := by
  have hpq : p - q ≠ 0 := sub_ne_zero.mpr h
  unfold envelopeFloor envelopeCorner
  field_simp
  ring

/-! ### Bourgain's exponents -/

/-- Bourgain's upper-regime spacing exponent. -/
def bourgainB : ℚ := 1 / 2

/-- Bourgain's lower-regime spacing exponent. -/
def bourgainC : ℚ := 4 / 3

/-- Bourgain's subconvexity exponent. -/
def bourgainTheta : ℚ := 13 / 84

@[simp] theorem bourgain_lower_endpoint :
    spacingLowerEndpoint bourgainC bourgainTheta = 17 / 42 := by
  unfold spacingLowerEndpoint bourgainC bourgainTheta; norm_num

@[simp] theorem bourgain_upper_endpoint :
    spacingUpperEndpoint bourgainB bourgainTheta = 3 / 7 := by
  unfold spacingUpperEndpoint bourgainB bourgainTheta; norm_num

@[simp] theorem bourgain_crossover_eq :
    spacingCrossover bourgainB bourgainC = 5 / 12 := by
  unfold spacingCrossover bourgainB bourgainC; norm_num

/-- **The two endpoints of Bourgain's covered range sum to `5/6`** — the classical incoherent block
exponent — and this sum does not depend on the target. -/
theorem bourgain_endpoints_sum :
    spacingLowerEndpoint bourgainC bourgainTheta + spacingUpperEndpoint bourgainB bourgainTheta
      = 5 / 6 := by
  rw [spacing_endpoints_sum]; unfold bourgainB bourgainC; norm_num

/-- **Bourgain's spacing estimates cover an interval of lengths of width `1/42`.** -/
@[simp] theorem bourgain_coverage_width :
    spacingCoverageWidth bourgainB bourgainC bourgainTheta = 1 / 42 := by
  rw [spacing_coverage_width_eq]; unfold bourgainB bourgainC bourgainTheta; norm_num

/-- **The floor of Bourgain's spacing endgame is `11/72`.** -/
@[simp] theorem bourgain_coverage_floor : spacingCoverageFloor bourgainB bourgainC = 11 / 72 := by
  unfold spacingCoverageFloor bourgainB bourgainC; norm_num

/-- **The record sits exactly `1/504` above the exponent at which its own spacing estimates stop
covering any length.** -/
theorem bourgain_room_above_floor :
    bourgainTheta - spacingCoverageFloor bourgainB bourgainC = 1 / 504 := by
  rw [bourgain_coverage_floor]; unfold bourgainTheta; norm_num

/-- **The surplus at the crossover is `1/84`.** -/
theorem bourgain_crossover_surplus_eq :
    sixthTargetExponent bourgainTheta (spacingCrossover bourgainB bourgainC)
      - sourceExponentLow bourgainC (spacingCrossover bourgainB bourgainC) = 1 / 84 := by
  rw [spacing_crossover_surplus, bourgain_coverage_floor]; unfold bourgainTheta; norm_num

/-- The floor is strictly below the record: the spacing estimates are not yet exhausted. -/
theorem bourgain_floor_lt_record : spacingCoverageFloor bourgainB bourgainC < bourgainTheta := by
  rw [bourgain_coverage_floor]; unfold bourgainTheta; norm_num

/-- But it is far above the Lindelöf target. -/
theorem bourgain_floor_pos : 0 < spacingCoverageFloor bourgainB bourgainC := by
  rw [bourgain_coverage_floor]; norm_num

/-! ### What the Lindelöf target demands of the spacing exponents -/

/-- **The floor vanishes exactly when the two spacing exponents are negatives of each other.**  So a
two-regime spacing endgame can still cover a length at `θ = 0` only with `b = -c`: the upper regime
must *save* a power of `T` over the trivial fourth-power count by exactly the amount the lower regime
loses. -/
theorem lindelof_forces_opposite_exponents (b c : ℚ) :
    spacingCoverageFloor b c = 0 ↔ b = -c := by
  unfold spacingCoverageFloor
  constructor
  · intro h
    have hbc : b + c = 0 := by
      rcases div_eq_zero_iff.mp h with h' | h'
      · exact h'
      · norm_num at h'
    linarith
  · intro h; rw [h]; ring

/-- The Lindelöf-limiting upper-regime exponent at the invariant crossover. -/
def lindelofB : ℚ := -5 / 12

/-- The lower-regime partner of `lindelofB`. -/
def lindelofC : ℚ := 5 / 12

/-- **At the Lindelöf limit the floor is zero.** -/
@[simp] theorem lindelof_coverage_floor : spacingCoverageFloor lindelofB lindelofC = 0 := by
  unfold spacingCoverageFloor lindelofB lindelofC; norm_num

/-- **The crossover is invariant**: Bourgain's spacing exponents and the Lindelöf-limiting ones place
the corner at the same Dirichlet-polynomial length `M = T^(5/12)`. -/
theorem crossover_invariant :
    spacingCrossover bourgainB bourgainC = spacingCrossover lindelofB lindelofC := by
  unfold spacingCrossover bourgainB bourgainC lindelofB lindelofC; norm_num

/-- At the Lindelöf limit the covered set is the single length `T^(5/12)`. -/
theorem lindelof_coverage_is_a_point :
    spacingCoverageWidth lindelofB lindelofC 0 = 0 ∧
      spacingLowerEndpoint lindelofC 0 = spacingCrossover lindelofB lindelofC := by
  constructor
  · rw [spacing_coverage_width_eq]; unfold lindelofB lindelofC; norm_num
  · unfold spacingLowerEndpoint spacingCrossover lindelofB lindelofC; norm_num

/-- The invariant crossover is `5/6` of the critical length `T^(1/2)` supplied by the approximate
functional equation. -/
theorem crossover_share_of_critical_length :
    spacingCrossover bourgainB bourgainC / (1 / 2) = 5 / 6 := by
  rw [bourgain_crossover_eq]; norm_num

/-- **The single statement the architecture reduces to at its Lindelöf limit**: at the invariant
crossover the target and the degenerate source coincide, so the method collapses to square-root
cancellation, `S^(6 : ℕ) ≤ M^(3 : ℕ)`, for a Dirichlet polynomial of length `T^(5/12)`. -/
theorem lindelof_collapses_to_crossover :
    sixthTargetExponent 0 (spacingCrossover lindelofB lindelofC)
      = sourceExponentLow lindelofC (spacingCrossover lindelofB lindelofC) := by
  have h := spacing_crossover_surplus lindelofB lindelofC 0
  rw [lindelof_coverage_floor] at h
  linarith

end HTGeometry
