# Open Problem 15: One clean window on a main-cardioid Julia set (repaired formulation)

**Field:** complex dynamics / computational plane geometry. **This is a FINITE
problem**: one explicit point, one explicit scale band, one verification in a compact
family of configurations. Certified computer-assisted proofs (interval arithmetic
with explicit constants) are fully acceptable. **Self-contained:** everything needed
is defined below; classical results from the literature may be used freely with
citation.

*This restates an earlier formulation whose scale band was not required to probe the
Julia set locally, admitting a vacuous solution (band far outside the set). The
repair is the absolute cap `b ≤ 1/4` in the Problem below; a proof of non-vacuity is
included.*

## Setting

Fix `c ≠ 0` in the open main cardioid of the Mandelbrot set (the parameters where
`f_c(z) = z² + c` has an attracting fixed point whose basin contains the critical
point `0`). A single explicit choice of `c` (e.g. `c = 0.2`, `c = −0.5`, or
`c = i/4`) is a complete solution. Then:

- `K_c` = filled Julia set (compact, full, connected, `K_c ⊆ B̄(0,2)`),
  `J_c = ∂K_c` a quasicircle;
- `f_c` is hyperbolic: uniformly expanding on `J_c`;
- `β = (1 + √(1−4c))/2` (principal root) is the repelling fixed point at which the
  external ray of angle `0` lands; with the cardioid parametrization
  `c = w/2 − w²/4` (`|w| < 1` the multiplier of the attracting fixed point) one has
  `β = 1 − w/2`, hence `|β| > 1/2` and, by the symmetry `K_c = −K_c`,
  `diam(J_c) ≥ 2|β| > 1`.

**Nearly-round curves.** For a center `x ∈ ℂ`, size `s > 0`, and tolerance
`η ∈ (0, 1/10]`, an **`(x, s, η)-round curve`** is a Jordan curve of the form
`Γ = { x + R(θ) e^{iθ} : θ ∈ [0, 2π) }` with `R : S¹ → (0, ∞)` Lipschitz,

> `|R(θ) − s| ≤ η s` and `|R′(θ)| ≤ η s` for all `θ`.

(Round circles are `R ≡ s`; images of round circles under univalent maps of small
Koebe distortion are of this form with `η → 0` as the distortion tends to `1` —
which is the only reason this family appears.)

## The Problem

> **Exhibit `q ∈ J_c`, scales `0 < a < b ≤ 1/4`, and tolerances `δ > 0`,
> `η ∈ (0, 1/10]`, with a proof that:**
>
> for every `q' ∈ J_c ∩ B(q, δ)`, every `s ∈ [a, b]`, and every `(q', s, η)`-round
> curve `Γ`:
>
> `#( J_c ∩ Γ ) ≤ 3.`

The band may be as thin as desired (nonempty and open suffices), `δ` and `η` may be
tiny, and `q` is free; the natural candidate is `q = β` (see below).

**Non-vacuity (proved).** Under the cap `b ≤ 1/4`, every admissible `Γ` satisfies
`#(J_c ∩ Γ) ≥ 2`: the interior of the polar graph contains `B(q', s(1−η))`, which
meets `J_c` in infinitely many points (`q' ∈ J_c` and `J_c` is perfect), while `Γ`
lies within `B̄(q', s(1+η))` of diameter `≤ (1/4)(1+1/10)·2 < 1 < diam(J_c)`, so
`J_c` also has points outside; a connected set meeting both complementary components
of a Jordan curve meets the curve, and a closed curve entering and leaving does so at
least twice. So the Problem genuinely pins the crossing count between `2` and `3` in
one window.

### Why this finishes a larger problem (may be assumed)

The following reduction is established and may be used as a black box. For hyperbolic
`f_c`, the Brolin/harmonic measure `μ` is ergodic; a.e. orbit returns infinitely
often to the trace of `B(q, δ)`; inverse branches along returns have Koebe
distortion tending to `1` on small charts, and they transport round circles centered
at a typical point `p` to `(q', s, η)`-round curves with `s ∈ [a, b]`, bijecting the
crossing sets. Hence a positive answer gives: for `μ`-a.e. `p ∈ J_c` there are
arbitrarily small radii `t` with `#(J_c ∩ ∂B(p,t)) ≤ 3` — and (by a further proven
lemma) with `B(p,t) ∖ K_c` connected. Downstream, this closes the last analytic
input of an algebraic-independence theorem for the Böttcher coordinates of pairs of
main-cardioid quadratics.

### Why the candidate `q = β` is promising

In the linearizing coordinate at `β` the two local arms of `J_c` are invariant under
`w ↦ (2β)w`; in the exact linear model an invariant curve is a logarithmic spiral,
along which the modulus is strictly monotone — each arm crosses every centered
circle exactly once, so the count is `2` at every scale, and by continuity nearby
centers and nearly-round curves stay `≤ 3` in suitable bands. The entire content of
the Problem is that the FRACTAL correction to the linear model (the decoration of
the arms, present at all scales) adds no crossings in SOME band. Numerical raster
experiments at real cardioid parameters found clean bands at every sampled scale
over five multiplicative periods; the Problem asks to certify one band rigorously.

### Remarks on method

- The configuration space is compact: one scale window, a compact family of
  nearly-round curves, one fixed fractal set. Interval-arithmetic enclosure of `J_c`
  in the window (e.g. via preimage refinement with expansion bounds, or via the
  Böttcher parametrization) plus a certified crossing count is a legitimate complete
  proof; explicit constants are part of the deliverable.
- A soft proof at `q = β` may be possible for REAL `c ∈ (−3/4, 0) ∪ (0, 1/4)`, where
  the multiplier is real and the two arms are complex-conjugate; any such argument
  must genuinely bound the radial oscillation of one fractal arm in one window
  (hyperbolic-metric or bounded-turning estimates localized to the window) — this is
  where soft attempts have stopped so far.
- A refutation must show every window at every point is dirty; that would contradict
  the numerical evidence, so refutation attempts should target the formulation (e.g.
  the polar-graph family being too wide) rather than the phenomenon.

## Deliverable

Explicit `c, q, a, b, δ, η` (with `b ≤ 1/4`) together with a complete rigorous proof
(human or certified-numerical) of the displayed inequality; or a proof that for some
main-cardioid `c` no such window exists.
