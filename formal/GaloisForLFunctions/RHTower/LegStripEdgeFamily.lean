/-
# The edge-law family `margin·√d → 2κ√a` and the general local factor `κ(c) = c/π²`

The `c = 2` edge law `(½ − θ_max)√d → 1/π` (`LegStripEdge.edge_margin_const`) is one point of a
two-parameter family. For any marginal carrier the deviation decomposes as `½ − θ_max = κ · m`, where
`κ` is the **local field factor** and `m = min_{x>0}(x/d + a/x)` is the AM–GM balance of the finite-`d`
truncation against the finite-`i` shell correction with coefficient `a`. The `√d`-scaled margin is then
the carrier-independent constant

> `margin·√d → ρ(κ, a) = 2·κ·√a`.

At the physical carrier `κ = 2/π²`, `a = π²/16`, so `ρ = 1/π`.

The **local factor is `κ(c) = c/π²`** at the harmonic carrier `δ_j = c/j`: near the gap the pole
distances are `≈ (c/i)(k+½)`, so `|F'(m)| = ½Σ csch²(dist/2) → (16i²/c²)·Σ_{k≥0}1/(2k+1)²` and
`|F'(m)|·δ_i/i → 2π²/c`, whence `κ(c) = 2/(|F'|δ/i) = c/π²`. It is grounded in odd Basel:
`κ(c) = c/(8·Σ 1/(2k+1)²)` (`localFactor_odd_basel`), so `κ(2) = 2/π²` recovers the physical factor.

This file makes the family a theorem: `edge_margin_const_general` (the exact `√d`-cancellation to
`2κ√a`), `edge_law_reduction_general` (the reduction: the physical decomposition in, the `2κ√a` limit
out), and `edge_law_family` (specialized to `κ = c/π²`), with the harmonic instance `ρ(2) = 1/π`.
-/
import GaloisForLFunctions.RHTower.LegStripEdge
open Real Filter Topology
noncomputable section
namespace RHTower

/-- The edge-law limit constant `ρ(κ, a) = 2κ√a`: the `√d`-scaled margin of a marginal carrier with
local factor `κ` and shell coefficient `a`. -/
def rhoFamily (κ a : ℝ) : ℝ := 2 * κ * Real.sqrt a

/-- **The general edge-law constant identity.** For any local factor `κ` and shell coefficient
`a ≥ 0`, the edge margin `κ·2√(a/d)` scaled by `√d` is the dead constant `2κ√a`: the `√d` cancels
exactly. Generalizes `edge_margin_const` (recovered at `κ = 2/π²`, `a = π²/16`). -/
theorem edge_margin_const_general {κ a d : ℝ} (ha : 0 ≤ a) (hd : 0 < d) :
    Real.sqrt d * (κ * (2 * Real.sqrt (a/d))) = rhoFamily κ a := by
  have hsd : Real.sqrt d > 0 := Real.sqrt_pos.mpr hd
  rw [Real.sqrt_div ha, rhoFamily]
  field_simp

/-- **The edge law as a reduction, in full generality.** Given the physical decomposition
`margin(d) = κ · m(d)` with `m(d)` the least value of the gap margin `x/d + a/x` (`a > 0`), the
`√d`-scaled margin tends to `ρ(κ, a) = 2κ√a`. The AM–GM minimization (`m(d) = 2√(a/d)`, via
`edge_isLeast` uniqueness) and the exact `√d`-cancellation (`edge_margin_const_general`) are discharged
here; the decomposition is the sole input. -/
theorem edge_law_reduction_general {κ a : ℝ} (ha : 0 < a) {mgn m : ℝ → ℝ}
    (hm : ∀ d, 0 < d → IsLeast ((fun x => x/d + a/x) '' Set.Ioi 0) (m d))
    (hθ : ∀ d, 0 < d → mgn d = κ * m d) :
    Tendsto (fun d => mgn d * Real.sqrt d) atTop (𝓝 (rhoFamily κ a)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with d hd
  have hmeq : m d = 2 * Real.sqrt (a/d) := (hm d hd).unique (edge_isLeast ha hd)
  rw [hθ d hd, hmeq, mul_comm]
  exact (edge_margin_const_general ha.le hd).symm

/-- The harmonic instance: `ρ(2/π², π²/16) = 1/π`. The `c = 2` edge law is one point of the family. -/
theorem rhoFamily_harmonic : rhoFamily (2/π^2) (π^2/16) = 1/π := by
  have hpi : 0 < π := Real.pi_pos
  rw [rhoFamily, show (π^2/16 : ℝ) = (π/4)^2 by ring, Real.sqrt_sq (by positivity)]
  field_simp
  ring

/-- **The general local field factor** `κ(c) = c/π²` at the harmonic carrier `δ_j = c/j`. -/
def localFactor (c : ℝ) : ℝ := c / π^2

/-- At the physical carrier the local factor is `κ(2) = 2/π²`. -/
theorem localFactor_two : localFactor 2 = 2/π^2 := by rw [localFactor]

/-- The local factor is grounded in odd Basel: `κ(c) = c/(8·Σ_{k≥0} 1/(2k+1)²)`, since
`Σ 1/(2k+1)² = π²/8` (`hasSum_odd_basel`). The edge constant `ρ` is thus the odd-Basel constant read
through the `√d` boundary layer, for every carrier `c`. -/
theorem localFactor_odd_basel (c : ℝ) :
    localFactor c = c / (8 * ∑' k : ℕ, (1:ℝ)/(2*k+1)^2) := by
  rw [localFactor, hasSum_odd_basel.tsum_eq, show (8:ℝ)*(π^2/8) = π^2 by ring]

/-- **The assembled edge-law family.** At the harmonic carrier `δ_j = c/j` with local factor
`κ = c/π²` and shell coefficient `a > 0`, given the decomposition `margin(d) = κ · m(d)` (with `m` the
least gap margin), the `√d`-scaled margin tends to `ρ(c/π², a) = (2c/π²)√a`. -/
theorem edge_law_family {c a : ℝ} (ha : 0 < a) {mgn m : ℝ → ℝ}
    (hm : ∀ d, 0 < d → IsLeast ((fun x => x/d + a/x) '' Set.Ioi 0) (m d))
    (hθ : ∀ d, 0 < d → mgn d = localFactor c * m d) :
    Tendsto (fun d => mgn d * Real.sqrt d) atTop (𝓝 (rhoFamily (localFactor c) a)) :=
  edge_law_reduction_general ha hm hθ

/-- The harmonic carrier `c = 2` sits at `ρ = 1/π`: `rhoFamily (localFactor 2) (π²/16) = 1/π`. -/
theorem rho_at_two : rhoFamily (localFactor 2) (π^2/16) = 1/π := by
  rw [localFactor_two]; exact rhoFamily_harmonic

/-- **The finite-size-scaling crossover function.** Along the scaling curve `c = 2 − ξ/√d`
(`ξ = (2−c)√d`), the `√d`-scaled margin tends to `G(ξ) = 1/π − ξ/4`: the edge law `G(0) = 1/π` and the
off-marginal linear response `G(ξ) → −ξ/4` (from `Φ'(2) = −π²/8` read through `κ = 2/π²`), joined in a
single **linear** crossover — because the leading imbalance `(π²/8)(c−2)` is `i`-independent, the AM–GM
minimizer is unchanged and the imbalance shifts the margin additively. -/
def crossoverG (ξ : ℝ) : ℝ := 1/π - ξ/4

/-- **The crossover reduction.** Given the near-marginal decomposition
`margin(d) = (2/π²)·((π²/8)·(−ξ/√d) + m(d))` — the local factor `κ = 2/π²` times the off-marginal
imbalance `(π²/8)(c−2) = −(π²/8)ξ/√d` plus the least gap margin `m(d)` (coefficient `a = π²/16`) — the
`√d`-scaled margin tends to `G(ξ) = 1/π − ξ/4`. The imbalance term contributes exactly `−ξ/4` (the `√d`
cancels for every `d`); the gap-margin term contributes `1/π` (the edge law, `edge_law_reduction_general`
via `rhoFamily_harmonic`). This constructs the crossover as a theorem, its two boundary constants unified. -/
theorem crossover_reduction {margin m : ℝ → ℝ} (ξ : ℝ)
    (hm : ∀ d, 0 < d → IsLeast ((fun x => x/d + (π^2/16)/x) '' Set.Ioi 0) (m d))
    (hmargin : ∀ d, 0 < d → margin d = (2/π^2)*((π^2/8)*(-(ξ/Real.sqrt d)) + m d)) :
    Tendsto (fun d => margin d * Real.sqrt d) atTop (𝓝 (crossoverG ξ)) := by
  -- second term: (2/π²)·m(d)·√d → 1/π
  have hsecond : Tendsto (fun d => (2/π^2) * m d * Real.sqrt d) atTop (𝓝 (1/π)) := by
    have := edge_law_reduction_general (κ := 2/π^2) (a := π^2/16)
      (by positivity [Real.pi_pos]) hm (fun d _ => rfl)
    rwa [rhoFamily_harmonic] at this
  -- first term: (2/π²)·(π²/8)·(−ξ/√d)·√d = −ξ/4 for every d>0 (√d cancels)
  have hfirst : Tendsto (fun d => (2/π^2)*((π^2/8)*(-(ξ/Real.sqrt d)))*Real.sqrt d) atTop
      (𝓝 (-ξ/4)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop 0] with d hd
    have hsd : Real.sqrt d ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hd)
    have hpi : (π:ℝ) ≠ 0 := ne_of_gt Real.pi_pos
    field_simp
    ring
  have hsum := hfirst.add hsecond
  have hgoal : Tendsto (fun d => margin d * Real.sqrt d) atTop (𝓝 (-ξ/4 + 1/π)) := by
    refine hsum.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with d hd
    rw [hmargin d hd]
    ring
  have : crossoverG ξ = -ξ/4 + 1/π := by unfold crossoverG; ring
  rwa [this]

/-- The crossover recovers the edge law at the marginal point: `G(0) = 1/π`. -/
theorem crossoverG_zero : crossoverG 0 = 1/π := by unfold crossoverG; ring

/-- The crossover's off-marginal asymptote is the `Φ'(2) = −π²/8` linear response: `G(ξ) + ξ/4 = 1/π`
(exact, since the crossover is linear at leading order). -/
theorem crossoverG_slope (ξ : ℝ) : crossoverG ξ + ξ/4 = 1/π := by unfold crossoverG; ring

/-- **The marginal-carrier family `ρ(c, a)`.** Sectioning the abstract `ρ`-surface `2κ√a` along the
carrier curve `c ↦ (κ(c), a(c))` with local factor `κ(c) = c/π²` gives the one-parameter family
`ρ(c, a) = (2c/π²)·√a`, whose value at the physical marginal carrier `(c, a) = (2, π²/16)` is `1/π`. -/
def rhoOfCarrier (c a : ℝ) : ℝ := rhoFamily (localFactor c) a

/-- The family in closed form: `ρ(c, a) = (2c/π²)·√a`. -/
theorem rhoOfCarrier_eq (c a : ℝ) :
    rhoOfCarrier c a = (2*c/π^2) * Real.sqrt a := by
  unfold rhoOfCarrier rhoFamily localFactor; ring

/-- The physical marginal carrier sits at `ρ(2, π²/16) = 1/π`. -/
theorem rhoOfCarrier_two : rhoOfCarrier 2 (π^2/16) = 1/π := rho_at_two

/-- **The edge law along the carrier curve.** For a carrier with local factor `κ(c) = c/π²` and shell
coefficient `a > 0`, given the decomposition `margin(d) = κ(c)·m(d)` (least gap margin), the `√d`-scaled
margin tends to the family value `ρ(c, a) = (2c/π²)√a`. This realizes `ρ(κ(c), a(c))` as a genuine
one-parameter family, not a single point: `ρ(2, π²/16) = 1/π`, and every `(c, a)` is a marginal-carrier
value the abstract skeleton `2κ√a` sections. -/
theorem edge_law_along_curve {c a : ℝ} (ha : 0 < a) {mgn m : ℝ → ℝ}
    (hm : ∀ d, 0 < d → IsLeast ((fun x => x/d + a/x) '' Set.Ioi 0) (m d))
    (hθ : ∀ d, 0 < d → mgn d = localFactor c * m d) :
    Tendsto (fun d => mgn d * Real.sqrt d) atTop (𝓝 (rhoOfCarrier c a)) :=
  edge_law_reduction_general ha hm hθ

end RHTower
end
