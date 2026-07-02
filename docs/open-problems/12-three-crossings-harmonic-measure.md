# Open Problem 12: Arbitrarily small radii with at most three circle crossings, almost surely for harmonic measure on a quadratic quasicircle

**Field:** geometric function theory (harmonic measure) / complex dynamics.
**Self-contained:** everything needed is defined below and every nonclassical input is
proved or sketched inline; classical results from the literature may be used freely
with citation. **The request:** prove the Problem (the dynamical subclass suffices),
or refute it.

## Setting

- `J ⊂ ℂ` a **quasicircle**: a Jordan curve with the Ahlfors bounded-turning
  property (`∃C ≥ 1`: for `x, y ∈ J` the smaller subarc between them has diameter
  `≤ C|x − y|`). `K` = its closed Jordan interior (a full compact set), and `μ` =
  harmonic measure of `ℂ̂ ∖ K` at `∞` (= equilibrium measure of `K`), a non-atomic
  probability measure with support `J`.
- For `p ∈ J` and `t > 0` write the **crossing count**
  `N_p(t) = #( J ∩ ∂B(p,t) )`.

**Dynamical subclass (extra structure; solving only this case is a complete
solution):** `K = K_c`, the filled Julia set of `f_c(z) = z² + c` with `c ≠ 0` in the
open main cardioid of the Mandelbrot set. There `J_c` is a quasicircle, `f_c` is
hyperbolic (uniformly expanding on `J_c`), and `μ` is the Brolin measure — the measure
of maximal entropy — invariant, ergodic, a Gibbs measure for the expanding dynamics;
Koebe distortion gives uniformly bounded-distortion inverse branches, so Euclidean
balls at boundary points correspond to bounded-distortion images of a fixed-size
dynamical picture ("cylinder scales").

## The Problem

> **Prove: for `μ`-almost every `p ∈ J`, for every `ε > 0` there exists
> `0 < t < ε` with `N_p(t) ≤ 3`.**
>
> (Full-measure reading if the set is non-measurable: its complement is contained in
> a Borel `μ`-null set. The weaker form "every Borel set of positive `μ`-measure
> contains such a `p`" is equally acceptable.)

## Why `≤ 3` — the proven consequence (may be assumed; proof sketch included)

**Lemma (proved).** For all but at most countably many radii `t` (those where `J`
contains an arc of the circle `∂B(p,t)`): if `N_p(t) ≤ 3` then `B(p,t) ∖ K` is
connected.
*Sketch.* Each connected component of `J ∩ B(p,t)` is an open subarc whose closure
has two endpoint on `∂B(p,t)`, and these endpoints are DISTINCT points of the plane;
two different components cannot share an endpoint (the simple curve would visit a
point twice). So `N_p(t) ≤ 3` leaves room for exactly one interior component — the
one through `p` — plus at most one tangential touch. That component is a single
crosscut of the ball through `p`; it cuts the ball into exactly two Jordan pieces,
each disjoint from `J`, hence one inside `K` and one outside; so `B(p,t) ∖ K` is the
outside piece — connected. ∎

Hence a positive answer gives: `μ`-a.e. `p` admits arbitrarily small radii with
`B(p,t) ∖ K` connected ("cofinally one-sided points" carry full harmonic measure).

## What is already proved, and why it does not settle this

**Rectifiable case — solved.** If `H¹(J) < ∞`, the statement holds. Template: by
F. & M. Riesz, `μ` and arclength are mutually absolutely continuous; if some `p` had
`N_p(t) ≥ 4` for a.e. `t < ε₀`, the Eilenberg coarea inequality for `z ↦ |z − p|` on
the rectifiable set `J` gives `H¹(J ∩ (B(p,r) ∖ B̄(p,r/2))) ≥ ∫_{r/2}^r 4 dt = 2r`,
contradicting Besicovitch density (`= r + o(r)` at `H¹`-a.e. point). So
`H¹`-a.e. — hence `μ`-a.e. — point has cofinally many `t` with `N_p(t) ≤ 3`.

**Why it stops there.** For `c ≠ 0` in the main cardioid, `dim_H(J_c) > 1` (Ruelle's
expansion `1 + |c|²/(4 log 2) + …` near `0`; Zdunik's strict dimension inequality in
general), so `H¹(J_c) = ∞`: not one nontrivial quadratic quasicircle is rectifiable.
Worse, on a purely non-rectifiable curve harmonic measure is SINGULAR with respect to
`H¹` (local F. & M. Riesz / Bishop–Jones theory), so no arclength-based counting can
reach a `μ`-a.e. conclusion. **The crossing count must be estimated against `μ`
itself.** Any valid proof must respect this: at a.e. point of the dynamical subclass,
`J` has infinite length in every ball, so the coarea bound `∫N ≤ H¹` is vacuous —
yet the claim is that crossing counts still drop to `≤ 3` at cofinally many scales.

## Suggested routes (take or ignore freely)

1. **Symbolic bounded-window event (dynamical subclass — most concrete).** By
   bounded distortion, whether `N_p(t) ≤ 3` for some `t` in a fixed multiplicative
   window of cylinder scales at `p` is determined, up to controlled error, by a
   bounded block of the symbolic itinerary of `p` under the expanding dynamics. If
   ONE clean block with positive Gibbs probability exists, ergodicity delivers it
   infinitely often along a.e. itinerary — i.e. cofinally many clean scales `μ`-a.e.
   The work: (a) the distortion dictionary between Euclidean balls and cylinders;
   (b) exhibiting one clean block (e.g. near the β fixed point, where the picture is
   an almost-straight crosscut at appropriate phases).
2. **A `μ`-coarea substitute.** Replace arclength by harmonic measure: bound
   `∫ N_p(t) dσ(t)` for a suitable scale measure `σ` by the `μ`-mass of annuli via
   extremal length / Beurling-type estimates for the family of curves joining the
   crossing points, and contradict persistent `N ≥ 4` with the `μ`-density behavior
   (Makarov: `dim μ = 1`, with iterated-logarithm-controlled fluctuations).
3. **β-numbers.** Persistent `N_p(t) ≥ 4` at ALL scales forces persistent
   non-flatness (`β`-numbers bounded below along all scales at `p`); Jones-type
   square-function / traveling-salesman estimates weighted by harmonic measure
   (Bishop–Jones) may show `μ`-a.e. this fails, i.e. flat-ish scales recur.

## What a solution yields

For two distinct parameters in the open main cardioid, the outer boundary of
`K_{c₁} ∪ K_{c₂}` carries (after a swap) positive `K_{c₁}`-equilibrium measure off
`K_{c₂}` — this is proved. Full `μ`-measure of cofinally one-sided points (which the
Problem gives via the Lemma) then produces by pigeonhole a point of `J_{c₁}`, off
`K_{c₂}`, on that outer boundary, with arbitrarily small balls meeting no bounded
complementary component of the union — the last geometric input in a proof that the
Böttcher coordinates of `f_{c₁}` and `f_{c₂}` are algebraically independent over
`ℂ(z)` for every such pair. Independently of that application, the statement is a
new a.e. boundary-regularity property of non-rectifiable quasicircles, strictly
between accessibility and rectifiability.

## Deliverable

A rigorous, self-contained proof (modulo cited literature) for the dynamical
subclass or for general quasicircles; or a refutation (a quasicircle — ideally a
main-cardioid `K_c` — with a positive-`μ`-measure set of points whose crossing counts
stay `≥ 4` below some scale).
