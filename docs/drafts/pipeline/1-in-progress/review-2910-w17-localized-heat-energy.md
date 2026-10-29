# Localized heat-zero energy evolution

- **ID:** review-2910-w17-localized-heat-energy
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / integration
- **Source:** W17 of the obstacles summary.
- **Statement:** Combine the actual heat-zero velocity, gap-independent pair flux,
  exterior force and forward simplicity into a collision-compatible local energy estimate.

## Existing ingredients checked

`Heat/LocalizedHeatPairForce` bounds each pair by its negative vertical interaction
plus `2M(y²+y'²)`, where M is the Lipschitz constant of the cutoff derivative.
A nonreal conjugate pair contributes exactly `−4w(x)`.
`Heat/HeatExteriorForce.exists_uniform_riemannHeat_exterior_force` supplies the
actual packet `|Re z−X|≤2`, its degree at most `C log X`, and a real-symmetric
exterior field Q with `|Im Q(z)|≤C log X |Im z|`.
`Heat/HeatLocalizedEnergyEvolution` contains draft proofs of the velocity and local
simple branches, then compact-region forward simplicity after every positive time.
The velocity, branches, compact forward simplicity, and actual finite-branch
energy derivative have now passed a direct Lean audit. The integrated evolution
estimate remains unfinished.
`Heat/HeatZeroSumContinuity` proves collision-continuity of the weighted energy.

## Paper calculation and remaining proof obligations

For `E_X=Σ w(Re z−X)(Im z)²`, simple-zero velocity is
`z'=2Σ_{b≠z}(z−b)⁻¹+2Q(z)`. Pair symmetrization and conjugation give

`E'_X ≤ −2Σ_{Im z≠0}w(Re z−X)
        + C(2M+2V+4W) log X Σ_{|Re z−X|≤2}(Im z)²`,

for a nonnegative cutoff supported in `(-1,1)`, bounded by W, with derivative
bounded by V and Lipschitz constant M. The pair error is
`2M(m−1)Σ y²`; use `m≤C log X`. The exterior contribution is at most
`C(2V+4W) log X Σ y²`. No minimum zero gap appears.

The finite-packet identity, derivative of the actual weighted sum, and passage
through collisions must all be formalized. A finite configuration inequality alone
does not finish this task. For the integrated form, a continuous outer cutoff
majorizes the radius-two squared-height sum. Forward simplicity supplies each
short punctured time interval; continuity handles its initial collision.

The earlier [energy-flux card](wd-heat-localized-energy-flux.md) remains the detailed
source ledger. In particular, forward simplicity does not imply finitely many
collisions; collision passage must use continuity and local one-sided comparison.

## Gates

- [x] Corpus search and source statements read.
- [x] Symmetrized finite-packet inequality with conjugate dissipation; direct final audit pending.
- [x] Actual localized energy derivative on simple intervals.
- [ ] Collision-compatible local/integrated evolution theorem.
- [ ] Direct leaf checks, transitive axiom audit, umbrella wiring.

`Heat/LocalizedHeatPacketFlux.lean` now proves the exact reciprocal-field identity,
the pair dissipation bound, the exterior bound and their sum. Its olean was built
because the evolution file imports it; both terminal axiom audits returned only
`propext`, `Classical.choice`, and `Quot.sound`. The final plain check remains.

The actual finite-branch derivative identification and compact forward simplicity
passed a direct Lean check. Both transitive axiom audits returned only `propext`,
`Classical.choice`, and `Quot.sound`. No integrated evolution theorem has been
marked complete.

## Derivative and collision construction plan

Use the actual radius-two packet S at a simple time. Choose disjoint isolating
balls and the proved actual simple-zero branch for each member. The compact set
`closedBall X 2` minus those open balls has no initial zeros; compact-open heat
continuity excludes future zeros there. Every zero carrying the radius-one weight
lies in this compact ball, so the actual weighted tsum is exactly the finite
branch sum for small nonnegative increments. This identifies its right derivative
without a root-path premise. The radius-two packet may meet the enclosing circle;
only the support of the weight, not all packet members, must lie inside it.

The exterior bound is needed only where w or its derivative is nonzero. Set the
auxiliary exterior field to zero outside the inner window when applying the finite
packet lemma. This avoids requiring the source field estimate on the whole packet.

For collision passage, replace the discontinuous nonreal indicator temporarily
by a continuous function `u(y)` with `0≤u≤1` and `u(0)=0`, for example
`min(1,y²/ε²)`. Its actual weighted zero sum is continuous by the same compact
multiplicity-conservation theorem. Choose a continuous outer cutoff at least one
on the radius-two window. Then the derivative majorant is continuous at collisions.
Apply the simple-time comparison on each short punctured future interval and pass
to its initial endpoint by continuity; local one-sided comparison gives global
finite-time comparison. Finally monotone convergence as ε tends to zero recovers
the integrated weighted nonreal count. Neither finite collision count nor a
uniform simplicity interval is assumed.

For the pointwise upper right-Dini estimate, a stronger shortcut is available:
at each fixed time the local packet is finite, so one truncated indicator already
equals the full nonreal indicator on that packet. The integrated continuous
majorant for this fixed truncation then gives the full count at the initial time
by continuity. This avoids assuming regularity of the discontinuous count while
retaining its entire conjugate dissipation coefficient.

On a whole interval `[a,b]` with `0≤a≤b≤1/8` and `b log X≤1`, no extra
time cutoff is required: the abstract comparison uses regular times `s<b` only.
At each interior time `x>0`, compact forward simplicity on `closedBall X 3`
covers the radius-two packet. The initial endpoint (including zero) is recovered
by continuity. For the integrated full count, the truncated observables are
bounded by `W C log X` throughout `[a,b]`, directly from the actual packet's
multiplicity bound; dominated convergence then removes the truncation.
