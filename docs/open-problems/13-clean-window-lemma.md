# Open Problem 13: One clean window on a main-cardioid Julia set

**Field:** complex dynamics / computational plane geometry. **This is a FINITE
problem**: it asks for one explicit point, one explicit scale band, and one
verification in a compact family of configurations. Certified computer-assisted
proofs (interval arithmetic with explicit constants) are fully acceptable.
**Self-contained:** everything needed is defined below; classical results from the
literature may be used freely with citation.

## Setting

Fix `c ≠ 0` in the open main cardioid of the Mandelbrot set (the parameters where
`f_c(z) = z² + c` has an attracting fixed point whose basin contains the critical
point `0`). A single explicit choice of `c` (e.g. `c = 0.2` or `c = −0.5`, or `c = i/4`)
is a complete solution. Then:

- `K_c` = filled Julia set (compact, full, connected), `J_c = ∂K_c` a quasicircle;
- `f_c` is hyperbolic: uniformly expanding on `J_c`;
- `β = (1 + √(1−4c))/2` is the repelling fixed point that is the landing point of the
  external ray of angle `0` (multiplier `2β`, `|2β| > 1`).

**Nearly-round curves.** For a center `x ∈ ℂ`, size `s > 0`, and roundness tolerance
`η > 0`, call a Jordan curve `Γ` an **`(x, s, η)-round curve`** if it is the polar
graph `Γ = { x + R(θ) e^{iθ} : θ ∈ [0, 2π) }` of a Lipschitz function
`R : S¹ → (0, ∞)` with

> `|R(θ) − s| ≤ η s` and `|R′(θ)| ≤ η s` for all `θ`.

(Round circles are the case `R ≡ s`. Images of round circles under univalent maps of
small Koebe distortion are of this form, with `η → 0` as the distortion tends to `1`;
that is the only reason this family appears.)

## The Problem

> **Exhibit `q ∈ J_c`, scales `0 < a < b`, and tolerances `δ > 0`, `η > 0`, with a
> proof that:**
>
> for every `q' ∈ J_c ∩ B(q, δ)`, every `s ∈ [a, b]`, and every `(q', s, η)`-round
> curve `Γ`:
>
> `#( J_c ∩ Γ ) ≤ 3.`

Any positive constants will do — no uniformity in `c` is asked, the band `[a, b]` may
be as thin as desired (it only needs to be nonempty and open), and `δ, η` may be tiny.
The point `q` may be chosen anywhere on `J_c`; the natural candidate is `q = β` (see
below), but that is not required.

### Why this finishes a larger problem (may be assumed)

The following reduction is established and may be used as a black box. For hyperbolic
`f_c`, the Brolin/harmonic measure `μ` is ergodic; a.e. orbit returns infinitely often
to the trace of `B(q, δ)`; inverse branches along returns have Koebe distortion
tending to `1` on small charts, and they transport round circles centered at a typical
point `p` to `(q', s, η)`-round curves with `s ∈ [a, b]`, bijecting the crossing sets.
Hence a positive answer gives: for `μ`-a.e. `p ∈ J_c` there are arbitrarily small
radii `t` with `#(J_c ∩ ∂B(p, t)) ≤ 3` — and (by a further proven lemma) with
`B(p, t) ∖ K_c` connected. Downstream, this closes the last analytic input of an
algebraic-independence theorem for the Böttcher coordinates of pairs of main-cardioid
quadratics.

### Why the candidate `q = β` is promising

In the linearizing coordinate at `β` the two local arms of `J_c` are invariant under
`w ↦ (2β) w`; a curve invariant under multiplication by a complex number of modulus
`> 1` is, in the exact linear model, a logarithmic spiral — along which the modulus is
strictly monotone. So in the linear model each arm crosses every centered circle
exactly once: `N_β(t) = 2` at every scale, and by continuity nearby centers and
nearly-round curves stay at `≤ 3` in suitable bands. The entire content of the
Problem is that the FRACTAL correction to the linear model (the decoration of the
arms, present at all scales) does not add crossings in SOME band. Numerical
raster experiments at real cardioid parameters found clean bands at every sampled
scale over five multiplicative periods; the Problem asks to certify one such band
rigorously.

### Remarks on method

- The configuration space is compact: one scale window, a compact family of
  nearly-round curves, one fixed fractal set. Interval-arithmetic enclosure of `J_c`
  in the window (e.g. via the Böttcher parametrization or via preimage refinement
  with expansion bounds) plus a certified crossing count is a legitimate complete
  proof; explicit distortion constants for the enclosure are part of the deliverable.
- A soft proof at `q = β` may be possible for REAL `c ∈ (−3/4, 0) ∪ (0, 1/4)`, where
  the multiplier is real, the two arms are complex-conjugate, and the ball picture is
  symmetric; any such argument must control the radial oscillation of one arm (the
  arm is a fractal quasi-arc, not a smooth spiral — this is where all previous soft
  attempts stopped, so a proof must genuinely bound the oscillation, e.g. through
  hyperbolic-metric or bounded-turning estimates localized to the window).
- A refutation would show the chosen window is never clean; note that refuting ALL
  windows at ALL points would contradict the numerical evidence, so refutation
  attempts should target the specific formulation (e.g. the polar-graph family being
  too wide) rather than the phenomenon.

## Deliverable

Explicit `c, q, a, b, δ, η` together with a complete rigorous proof (human or
certified-numerical) of the displayed inequality; or a proof that no such window
exists for some main-cardioid `c` (which would refute the a.e. low-crossing statement
it feeds and be equally decisive).
