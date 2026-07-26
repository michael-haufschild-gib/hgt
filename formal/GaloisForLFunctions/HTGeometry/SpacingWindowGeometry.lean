/-
The window geometry of a two-regime spacing endgame.

A spacing endgame for a sixth-power large-value quantity `A = S^6` of a Dirichlet polynomial of
length `M` at height `T` consists of two source bounds and one target:

    source, upper regime :   A ≤ M^4 · T^b     for  M ≥ T^m
    source, lower regime :   A ≤ M^2 · T^c     for  M < T^m
    target               :   A ≤ M^3 · T^(6θ)

with the target read off as `S ≤ M^(1/2) T^θ`.  Everything below is an identity in the three
exponents `(b, c, θ)`; no analytic input is used.

Writing exponents of `M` as powers of `T` (`M = T^x`), the source bounds hold as *exponent*
inequalities `4x + b ≤ 3x + 6θ` and `2x + c ≤ 3x + 6θ`, i.e.

    upper regime succeeds  ⟺  x ≤ 6θ - b ,
    lower regime succeeds  ⟺  x ≥ c - 6θ .

So the two regimes cover the whole line exactly when `c - 6θ ≤ 6θ - b`, and the interval they fail
to cover — the *window* on which a separate direct estimate is required — is

    [ c - 6θ , 6θ - b ] ,   of width  12θ - (b + c) .

Three consequences, all proved below:

* the endpoints sum to `c - b` **independently of `θ`**, and their midpoint is the regime crossover
  `m = (c - b)/2`, also independent of `θ`;
* the window is nonempty exactly when `θ ≥ (b + c)/12`, so `(b + c)/12` is an **architectural floor**:
  no choice of the direct estimate can push the method below it while `b` and `c` are fixed;
* the slack of the target over the sources at the crossover is exactly `6(θ - (b+c)/12)`, i.e. six
  times the distance to the floor, and exactly half the window width.

For Bourgain's exponents `b = 1/2`, `c = 4/3` this gives crossover `5/12`, floor `11/72`, and at the
record `θ = 13/84` a window `[17/42, 3/7]` of width `1/42` and a crossover slack of `1/84`.  The
record therefore sits `1/504` above the floor of its own architecture.
-/
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

namespace HTGeometry

/-! ### The three exponents and the derived geometry -/

/-- Lower endpoint of the window: below it the `M^2 T^c` regime already implies the target. -/
def spacingLowerEndpoint (c θ : ℚ) : ℚ := c - 6 * θ

/-- Upper endpoint of the window: above it the `M^4 T^b` regime already implies the target. -/
def spacingUpperEndpoint (b θ : ℚ) : ℚ := 6 * θ - b

/-- The crossover between the two source regimes, where `M^4 T^b = M^2 T^c`. -/
def spacingCrossover (b c : ℚ) : ℚ := (c - b) / 2

/-- Width of the window on which neither source regime suffices. -/
def spacingWindowWidth (b c θ : ℚ) : ℚ :=
  spacingUpperEndpoint b θ - spacingLowerEndpoint c θ

/-- The architectural floor of the two-regime endgame. -/
def spacingArchFloor (b c : ℚ) : ℚ := (b + c) / 12

/-- Exponent of the target `M^3 T^(6θ)` at `M = T^x`. -/
def sixthTargetExponent (θ x : ℚ) : ℚ := 3 * x + 6 * θ

/-- Exponent of the upper-regime source `M^4 T^b` at `M = T^x`. -/
def sourceExponentMid (b x : ℚ) : ℚ := 4 * x + b

/-- Exponent of the lower-regime source `M^2 T^c` at `M = T^x`. -/
def sourceExponentLow (c x : ℚ) : ℚ := 2 * x + c

/-! ### The endpoints are forced, and their sum is free of the target -/

/-- **The window's endpoints sum to `c - b`, with no dependence on `θ`.**  Improving the target
slides the window symmetrically; it cannot move its centre. -/
theorem spacing_endpoints_sum (b c θ : ℚ) :
    spacingLowerEndpoint c θ + spacingUpperEndpoint b θ = c - b := by
  unfold spacingLowerEndpoint spacingUpperEndpoint; ring

/-- **The crossover is exactly the midpoint of the window**, for every target. -/
theorem spacing_crossover_is_midpoint (b c θ : ℚ) :
    (spacingLowerEndpoint c θ + spacingUpperEndpoint b θ) / 2 = spacingCrossover b c := by
  rw [spacing_endpoints_sum]; unfold spacingCrossover; ring

/-- The crossover is where the two source exponents agree. -/
theorem spacing_crossover_balances (b c : ℚ) :
    sourceExponentMid b (spacingCrossover b c) = sourceExponentLow c (spacingCrossover b c) := by
  unfold sourceExponentMid sourceExponentLow spacingCrossover; ring

/-- At the lower endpoint the lower-regime source meets the target **exactly**. -/
theorem spacing_tight_at_lower (c θ : ℚ) :
    sourceExponentLow c (spacingLowerEndpoint c θ)
      = sixthTargetExponent θ (spacingLowerEndpoint c θ) := by
  unfold sourceExponentLow sixthTargetExponent spacingLowerEndpoint; ring

/-- At the upper endpoint the upper-regime source meets the target **exactly**. -/
theorem spacing_tight_at_upper (b θ : ℚ) :
    sourceExponentMid b (spacingUpperEndpoint b θ)
      = sixthTargetExponent θ (spacingUpperEndpoint b θ) := by
  unfold sourceExponentMid sixthTargetExponent spacingUpperEndpoint; ring

/-- Outside the window on the low side, the lower regime beats the target. -/
theorem spacing_low_regime_suffices {c θ x : ℚ} (hx : x ≤ spacingLowerEndpoint c θ) :
    sixthTargetExponent θ x ≤ sourceExponentLow c x := by
  unfold sixthTargetExponent sourceExponentLow spacingLowerEndpoint at *; linarith

/-- Outside the window on the high side, the upper regime beats the target. -/
theorem spacing_mid_regime_suffices {b θ x : ℚ} (hx : spacingUpperEndpoint b θ ≤ x) :
    sixthTargetExponent θ x ≤ sourceExponentMid b x := by
  unfold sixthTargetExponent sourceExponentMid spacingUpperEndpoint at *; linarith

/-! ### The floor -/

/-- The window width is `12θ - (b + c)`. -/
theorem spacing_window_width_eq (b c θ : ℚ) :
    spacingWindowWidth b c θ = 12 * θ - (b + c) := by
  unfold spacingWindowWidth spacingUpperEndpoint spacingLowerEndpoint; ring

/-- The width is exactly twelve times the distance to the floor. -/
theorem spacing_window_width_eq_floor_gap (b c θ : ℚ) :
    spacingWindowWidth b c θ = 12 * (θ - spacingArchFloor b c) := by
  rw [spacing_window_width_eq]; unfold spacingArchFloor; ring

/-- **The window degenerates to a point exactly at the floor.** -/
theorem spacing_window_closes_iff (b c θ : ℚ) :
    spacingWindowWidth b c θ = 0 ↔ θ = spacingArchFloor b c := by
  rw [spacing_window_width_eq_floor_gap]
  constructor
  · intro h; have := mul_eq_zero.mp h; rcases this with h' | h'
    · norm_num at h'
    · linarith
  · intro h; rw [h]; ring

/-- **The two-regime architecture is consistent only above its floor.**  If the target exponent is
below `(b+c)/12` the two source regimes overlap in the wrong direction: the window has negative
width, so no direct estimate on a genuine range of `M` can be posed. -/
theorem spacing_architecture_needs_floor (b c θ : ℚ) :
    0 ≤ spacingWindowWidth b c θ ↔ spacingArchFloor b c ≤ θ := by
  rw [spacing_window_width_eq_floor_gap]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- **The crossover slack is six times the distance to the floor** — a direct readout of the room
remaining in the architecture. -/
theorem spacing_crossover_slack (b c θ : ℚ) :
    sixthTargetExponent θ (spacingCrossover b c) - sourceExponentLow c (spacingCrossover b c)
      = 6 * (θ - spacingArchFloor b c) := by
  unfold sixthTargetExponent sourceExponentLow spacingCrossover spacingArchFloor; ring

/-- The crossover slack is half the window width. -/
theorem spacing_slack_eq_half_width (b c θ : ℚ) :
    2 * (sixthTargetExponent θ (spacingCrossover b c)
          - sourceExponentLow c (spacingCrossover b c))
      = spacingWindowWidth b c θ := by
  rw [spacing_crossover_slack, spacing_window_width_eq_floor_gap]; ring

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

/-- **The two endpoints of Bourgain's range sum to `5/6`** — the classical incoherent block
exponent — and this sum is independent of the target. -/
theorem bourgain_endpoints_sum :
    spacingLowerEndpoint bourgainC bourgainTheta + spacingUpperEndpoint bourgainB bourgainTheta
      = 5 / 6 := by
  rw [spacing_endpoints_sum]; unfold bourgainB bourgainC; norm_num

/-- **Bourgain's window is `1/42` wide.** -/
@[simp] theorem bourgain_window_width :
    spacingWindowWidth bourgainB bourgainC bourgainTheta = 1 / 42 := by
  rw [spacing_window_width_eq]; unfold bourgainB bourgainC bourgainTheta; norm_num

/-- **The architectural floor of Bourgain's spacing endgame is `11/72`.** -/
@[simp] theorem bourgain_arch_floor : spacingArchFloor bourgainB bourgainC = 11 / 72 := by
  unfold spacingArchFloor bourgainB bourgainC; norm_num

/-- **The record sits exactly `1/504` above the floor of its own architecture.** -/
theorem bourgain_room_above_floor :
    bourgainTheta - spacingArchFloor bourgainB bourgainC = 1 / 504 := by
  rw [bourgain_arch_floor]; unfold bourgainTheta; norm_num

/-- **The crossover slack at the record is `1/84`.** -/
theorem bourgain_crossover_slack_eq :
    sixthTargetExponent bourgainTheta (spacingCrossover bourgainB bourgainC)
      - sourceExponentLow bourgainC (spacingCrossover bourgainB bourgainC) = 1 / 84 := by
  rw [spacing_crossover_slack, bourgain_arch_floor]; unfold bourgainTheta; norm_num

/-- The floor is strictly below the record: the architecture is not yet exhausted. -/
theorem bourgain_floor_lt_record : spacingArchFloor bourgainB bourgainC < bourgainTheta := by
  rw [bourgain_arch_floor]; unfold bourgainTheta; norm_num

/-- But it is far above the Lindelöf target. -/
theorem bourgain_floor_pos : 0 < spacingArchFloor bourgainB bourgainC := by
  rw [bourgain_arch_floor]; norm_num

/-! ### What the Lindelöf target demands of the spacing exponents -/

/-- **The floor vanishes exactly when the two spacing exponents are negatives of each other.**  So a
two-regime spacing endgame can reach `θ = 0` only with `b = -c`: the upper regime must *save* a power
of `T` over the trivial fourth-power count by exactly the amount the lower regime loses. -/
theorem lindelof_forces_opposite_exponents (b c : ℚ) :
    spacingArchFloor b c = 0 ↔ b = -c := by
  unfold spacingArchFloor
  constructor
  · intro h
    have hbc : b + c = 0 := by
      rcases div_eq_zero_iff.mp h with h' | h'
      · exact h'
      · norm_num at h'
    linarith
  · intro h; rw [h]; ring

/-- The Lindelöf-limiting spacing exponents at the invariant crossover. -/
def lindelofB : ℚ := -5 / 12

/-- The lower-regime partner of `lindelofB`. -/
def lindelofC : ℚ := 5 / 12

/-- **At the Lindelöf limit the floor is zero.** -/
@[simp] theorem lindelof_arch_floor : spacingArchFloor lindelofB lindelofC = 0 := by
  unfold spacingArchFloor lindelofB lindelofC; norm_num

/-- **The crossover is invariant**: Bourgain's spacing exponents and the Lindelöf-limiting ones
place the degenerate point at the same Dirichlet-polynomial length `M = T^(5/12)`. -/
theorem crossover_invariant :
    spacingCrossover bourgainB bourgainC = spacingCrossover lindelofB lindelofC := by
  unfold spacingCrossover bourgainB bourgainC lindelofB lindelofC; norm_num

/-- At the Lindelöf limit the window is a single point, namely the crossover. -/
theorem lindelof_window_is_a_point :
    spacingWindowWidth lindelofB lindelofC 0 = 0 ∧
      spacingLowerEndpoint lindelofC 0 = spacingCrossover lindelofB lindelofC := by
  constructor
  · rw [spacing_window_width_eq]; unfold lindelofB lindelofC; norm_num
  · unfold spacingLowerEndpoint spacingCrossover lindelofB lindelofC; norm_num

/-- The invariant crossover is `5/6` of the critical length `T^(1/2)` supplied by the approximate
functional equation. -/
theorem crossover_share_of_critical_length :
    spacingCrossover bourgainB bourgainC / (1 / 2) = 5 / 6 := by
  rw [bourgain_crossover_eq]; norm_num

/-- **The single statement the architecture reduces to at its Lindelöf limit**: at the invariant
crossover the target and the degenerate source coincide, so the whole method collapses to square-root
cancellation for a Dirichlet polynomial of length `T^(5/12)`. -/
theorem lindelof_collapses_to_crossover :
    sixthTargetExponent 0 (spacingCrossover lindelofB lindelofC)
      = sourceExponentLow lindelofC (spacingCrossover lindelofB lindelofC) := by
  have h := spacing_crossover_slack lindelofB lindelofC 0
  rw [lindelof_arch_floor] at h
  linarith

end HTGeometry
