# Open Problem 10: Cofinally one-sided points of a quasidisk carry full harmonic measure

**Field:** geometric function theory (boundary behavior, harmonic measure) / plane
topology; a dynamical subclass is offered for extra structure.
**Self-contained:** everything needed is defined below and every nonclassical input is
proved inline; classical results from the literature may be used freely with citation.
**The request:** prove the Problem (the subclass form suffices), or refute it.

> **STATUS (2026-07-02): the RECTIFIABLE subcase is PROVEN** (see
> [10-answer.md](10-answer.md), verified): if `H¹(J) < ∞` then `μ(Q(K)) = 1`, via
> F. & M. Riesz + a crossing-count/coarea/density argument. This settles chord-arc
> quasidisks but NOT the dynamical subclass: for `c ≠ 0` in the main cardioid
> `dim_H(J_c) > 1` (Ruelle, Zdunik), so `J_c` is never rectifiable. Moreover the
> counting lemma of that proof is fully general and REDUCES the remaining problem to
> the sharpened form below (A4), while Bishop–Jones singularity (`μ ⊥ H¹` on purely
> non-rectifiable curves) provably blocks any arclength-based transfer — a solution
> must count crossings against `μ` directly.

## Setting

- A **quasicircle** is a Jordan curve `J ⊂ ℂ` with the Ahlfors bounded-turning
  property: there is `C ≥ 1` such that for all `x, y ∈ J`, the smaller-diameter subarc
  of `J` between `x` and `y` has diameter `≤ C·|x − y|`.
- Let `K` be the closed Jordan-interior of `J` (so `K` is a compact, full set with
  `∂K = J` — a **closed quasidisk**), and `Ω = ℂ̂ ∖ K` the exterior domain.
- Let `μ` be the **harmonic measure** of `Ω` evaluated at `∞` — equivalently the
  equilibrium measure of `K`. It is a non-atomic Borel probability measure with
  support `J`.
- `p ∈ J` is **cofinally one-sided** if for every `ε > 0` there is some `0 < ρ < ε`
  such that `B(p,ρ) ∖ K` is connected. Write `Q(K)` for the set of such `p`.

## The Problem

> **Prove: `μ(Q(K)) = 1`** — cofinally one-sided points carry full harmonic measure.
>
> The following weaker form is equally acceptable: every Borel `E ⊆ J` with
> `μ(E) > 0` contains a point of `Q(K)`. (If `Q(K)` is not measurable, read the
> full-measure statement as: `J ∖ Q(K)` is contained in a Borel `μ`-null set.)

### Acceptable subclass (extra structure available)

It suffices to prove the statement for `K = K_c`, the filled Julia set of
`f_c(z) = z² + c` with `c ≠ 0` in the **open main cardioid** of the Mandelbrot set
(the parameters where `f_c` has an attracting fixed point whose basin contains the
critical point). There `J_c` is a quasicircle (classical), `f_c` is hyperbolic
(uniformly expanding on `J_c`), and `μ` coincides with the measure of maximal entropy
(Brolin), invariant and ergodic under `f_c` — so symbolic dynamics, Gibbs/thermodynamic
formalism, and conformal self-similarity of `J_c` may all be used.

## Cautions — known traps around this statement

- **Do not conflate accessibility with ball-connectivity.** Quasidisks are uniform
  domains, hence John domains on both sides, so EVERY boundary point is
  cone-accessible from `Ω`; by McMillan's twist/cone dichotomy, `μ`-a.e. point is
  non-twisting. None of this settles the Problem: a cone access in one direction does
  not by itself forbid complementary pockets in other directions at every scale. In
  particular, the implication "non-twisting ⟹ cofinally one-sided" is NOT a known
  theorem; if your proof uses it, prove it.
- **Do not aim at the strong form.** Whether `B(p,ρ) ∖ K` is connected for ALL small
  `ρ` at a.e. `p` is a different (likely false or much harder) statement; for
  non-Jordan quadratic Julia sets the all-`ρ` form provably fails a.e., and
  numerically it fails at single-access points on log-periodically recurring scale
  bands. Only arbitrarily-small good radii are asked for.

## Structural anchors (proved inline)

**A1 (every complementary piece reaches the rim).** If `V` is a connected component of
`B(p,ρ) ∖ K` whose closure misses `∂B(p,ρ)`, then `∂V ⊆ K`, so `V` is a bounded open
set with boundary inside the full compact `K`, hence `V ⊆ K` — contradiction. So every
component of `B(p,ρ) ∖ K` touches the rim, and disconnection happens exactly when
`K` chords the ball.

**A2 (arc localization by bounded turning).** For `p ∈ J` and
`ρ < diam(J)/(2C)`: every `x ∈ J ∩ B(p,ρ)` has its smaller subarc `J[p,x]` of diameter
`≤ Cρ`; the union of these subarcs over all such `x` is a connected subset of `J`
containing `p`, hence a single subarc `A_ρ ∋ p` with
`J ∩ B(p,ρ) ⊆ A_ρ ⊆ J ∩ B̄(p, Cρ)`.
*Consequence:* all boundary structure of `B(p,ρ) ∖ K` inside the ball is carried by
ONE subarc of `J` through `p`, of diameter `≤ 2Cρ`.

**A3 (two crossings ⟹ connected).** If moreover `J` meets `∂B(p,ρ)` in exactly two
points, then `J ∩ B̄(p,ρ)` is a single crosscut of the ball through `p`, the ball is
cut into exactly two pieces, one in `Ω` and one in `int K`, and `B(p,ρ) ∖ K` is
connected. So the Problem is equivalent to: **for `μ`-a.e. `p`, there are arbitrarily
small scales at which the localized arc through `p` does not double back across the
sphere `∂B(p,ρ)`** (or at which whatever doubling-back occurs does not separate).

**A4 (sharpened residual form — PROVEN sufficient).** Write
`N_p(t) = #(J ∩ ∂B(p,t))`. The verified rectifiable-case proof establishes in full
generality (no rectifiability needed): for all but countably many `t`, `N_p(t) ≤ 3`
implies `B(p,t) ∖ K` connected — distinct interior components of `J ∩ B(p,t)` have
disjoint pairs of rim endpoints (a shared endpoint would make the simple curve visit a
point twice), so `N_p(t) ≤ 3` forces a single crosscut through `p` plus at most a
tangency. Hence it SUFFICES to prove:

> for `μ`-a.e. `p ∈ J` and every `ε > 0` there is `0 < t < ε` with `N_p(t) ≤ 3`.

CAUTION: for non-rectifiable `J` this cannot be reached through arclength — harmonic
measure is singular with respect to `H¹` on purely non-rectifiable curves (local
F. & M. Riesz / Bishop–Jones) — so the crossing count must be estimated against `μ`
itself (on the dynamical subclass: against the Brolin measure, where `N_p(t) ≤ 3` at
cylinder scales is a bounded-window symbolic event under Koebe distortion).

## Suggested routes (take or ignore freely)

1. **Makarov-type boundary theory.** Harmonic measure on a simply connected domain
   lives on sets of dimension 1 with iterated-logarithm-controlled oscillation
   (Makarov). A quantitative "a.e. point has infinitely many nearly-flat scales"
   statement — flat meaning the localized arc `A_ρ` stays in a thin slab, which
   forbids separating doubling-backs — would finish via A3. The i.o. (not a.e.-scale)
   nature of the required flatness is what makes this plausible.
2. **Dynamical route on the subclass.** For `K_c` (main cardioid) the event
   "`J` doubles back at scale `ρ` around `p`" is, by expansion and bounded distortion
   (Koebe), read off from a bounded-length symbolic window of the itinerary of `p`;
   clean windows exist (the numerical picture shows clean scale-bands), so ergodicity
   of `μ` gives positive frequency of clean scales along a.e. orbit, hence infinitely
   many clean radii a.e. The work is the bounded-distortion dictionary between
   Euclidean balls at `p` and dynamical cylinders — this route seems the most likely
   to close completely for the subclass.
3. **Quasiconformal transplantation.** `J` is the image of the round circle under a
   quasiconformal homeomorphism of the plane; on the circle every point is cofinally
   (indeed everywhere) one-sided. The obstruction: QC maps distort round balls into
   quasi-round regions, and connectivity of `D ∖ K` for quasi-round `D` does not pass
   to round sub-balls. Any solution along this route must convert quasi-round clean
   shapes into round clean shapes — e.g. via A2/A3 plus quasisymmetric modulus
   estimates.

## What a solution yields

Beyond intrinsic interest (a new a.e. boundary-regularity statement for quasicircles,
strictly between accessibility and tangential smoothness): for two distinct quadratic
parameters in the open main cardioid, the outer boundary `∂W` of `K_{c₁} ∪ K_{c₂}`
carries positive `K_{c₁}`-equilibrium measure off `K_{c₂}` (after a swap; this is
proved), so full measure of `Q(K_{c₁})` produces by pigeonhole an exposed cofinally
one-sided point — the last geometric input, for this parameter class, in a proof that
the Böttcher coordinates of `f_{c₁}` and `f_{c₂}` are algebraically independent over
`ℂ(z)`.

## Deliverable

A rigorous, self-contained proof (modulo cited literature) for general quasidisks or
for the main-cardioid subclass, written so each step can be checked independently; or
a refutation (a quasidisk with `μ(Q(K)) < 1`, noting whether it can be realized as a
main-cardioid `K_c`).
