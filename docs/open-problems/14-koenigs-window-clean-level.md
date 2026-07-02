# Open Problem 14: One clean level in a Koenigs window on the real slice

**Field:** complex/real dynamics, one dimension. **This is a FINITE problem**: one
parameter, one scale window, one level with a margin. Certified computer-assisted
proofs (interval arithmetic with explicit constants) are fully acceptable.
**Self-contained:** everything needed is defined below; classical results from the
literature may be used freely with citation.

## Setting

Fix a REAL parameter `c ∈ [−2, 1/4)` with `c ∉ {0, −2}` (so the Julia set is
fractal). A single explicit choice — e.g. `c = −0.5`, `c = −1`, or `c = 0.2` — is a
complete solution. Let `f_c(z) = z² + c`, `K_c` its filled Julia set (compact, full,
connected), `J_c = ∂K_c`, and

- `β = (1 + √(1−4c))/2` — the repelling fixed point on `J_c ∩ ℝ`, multiplier
  `λ = 2β ∈ (1, 4)`;
- `L_c` — the Koenigs linearizer at `β`: the conformal map on a disk
  `B(β, R_c)` with `L_c(β) = 0`, `L_c′(β) = 1`, and `L_c(f_c(z)) = λ·L_c(z)`
  wherever both sides are defined (classical, exists at any repelling fixed point);
  for real `c` it commutes with complex conjugation;
- `γ_c : ℝ/ℤ → J_c` — the landing map: `J_c` is locally connected for every real
  `c ∈ [−2, 1/4]` (Levin–van Strien, *Local connectivity of the Julia set of real
  polynomials*), so the inverse Böttcher coordinate extends continuously to the unit
  circle (Carathéodory); `γ_c(2t) = f_c(γ_c(t))`, and `γ_c(t) = β` iff `t = 0`
  (only the ray of angle `0` lands at `β`; Douady–Hubbard, Milnor);
- pick `t₀ > 0` small enough that `γ_c([−t₀, t₀]) ⊆ B(β, R_c)`, and define the
  **Koenigs profile**

  > `r_c : [−t₀, t₀] → [0, ∞)`, `r_c(t) = |L_c(γ_c(t))|`.

**Its two exact properties** (one-line proofs): `r_c(t) = 0` iff `t = 0`, and
`r_c(−t) = r_c(t)`; and for `|t| ≤ t₀/2`,

> `r_c(2t) = λ · r_c(t)` (exactly),

from `L_c(f_c(z)) = λ L_c(z)` and `γ_c(2t) = f_c(γ_c(t))`.

## The Problem

> **Exhibit a level `σ > 0` and a gap `g > 0`, with a proof, such that**
>
> 1. **(band cleanness)** for every `σ′ ∈ [σ(1−g), σ(1+g)]`, the sublevel set
>    `{ t ∈ [−t₀, t₀] : r_c(t) < σ′ }` is a single interval (containing `0`); and
> 2. **(window edge)** `σ(1+g) < inf { r_c(t) : t₀/2 ≤ |t| ≤ t₀ }`.
>
> Any positive `σ, g` (and any admissible `t₀`) will do; by the symmetry
> `r_c(−t) = r_c(t)` it suffices to verify cleanness on `[0, t₀]`.

### Why this finishes a larger problem (may be assumed as a black box)

The following chain is established. By the exact relation, condition (1)+(2)
propagates: for every `n`, all sublevels at levels `λ^{-n}σ′` are single intervals
(points outside `|t| ≤ t₀ 2^{-n}` are excluded by (2) and the relation; points
outside the window entirely are excluded, at small levels, because
`φ_c(t) = |γ_c(t) − β|` has a positive minimum on `|t| ≥ t₀`). Since
`L_c⁻¹(w) = β + w + O(w²)`, the Euclidean landing-distance `φ_c` differs from `r_c`
by a factor `1 + O(λ^{-n})` at scale `λ^{-n}σ`, which the fixed gap `g` dominates for
large `n`; hence `φ_c` has connected sublevel sets at arbitrarily small levels. By a
further proven reduction this yields arbitrarily small radii `ρ` with
`B(β,ρ) ∖ K_c` connected — and for a pair of real parameters `c₁ < c₂` (both
nonexceptional) this is the last analytic input, at `β₁`, of a proof that the
Böttcher coordinates of `f_{c₁}` and `f_{c₂}` are algebraically independent over
`ℂ(z)`. Solving the Problem for a subrange of `c` closes that theorem for all real
pairs from the subrange.

### Orientation

- **What the claim says geometrically:** side wells of `r_c` (angles `t` far from
  `0` whose rays land close to `β` in the linearizing metric) exist — numerically,
  at `c = −0.9`, they disconnect sublevels on bands of levels recurring once per
  multiplicative period `λ` — but they never fill a whole period: some level band
  stays clean. Rasterized experiments at `c ∈ {0.2, 0.24, −0.5, −1.0}` found clean
  bands at every sampled scale over five periods, so the verification has visible
  margin; the content is to certify one band rigorously.
- **Computability:** `r_c` is accessible to certified numerics: the landing map on
  dyadic angles via inverse iteration (`γ_c(t/2)` = the appropriate square-root
  preimage of `γ_c(t)`), the Koenigs map via its convergent iteration
  `L_c = lim λ^{-n}(f_c^n − β)` with explicit error bounds on a disk where `f_c` is
  expanding, and modulus-of-continuity control of `γ_c` (Hölder for hyperbolic `c`)
  to pass from finitely many sampled angles to all `t` in the window. All constants
  are explicit; the configuration is compact.
- **A soft proof** would need to bound the radial oscillation of one arm of the
  Koenigs image of `J_c` in a single window — the same difficulty as in the
  companion planar problem; any genuinely new mechanism (positive expansion gaps,
  bounded-turning localized to the window, symbolic large-deviation bounds on
  near-misses) is welcome.

## Deliverable

Explicit `c, t₀, σ, g` with a complete rigorous proof (human or
certified-numerical) of (1) and (2); or a proof that for some real fractal `c` NO
such window exists (i.e. every level band of every window is dirty), which would
refute cofinal one-sidedness at `β` there and be equally decisive.
