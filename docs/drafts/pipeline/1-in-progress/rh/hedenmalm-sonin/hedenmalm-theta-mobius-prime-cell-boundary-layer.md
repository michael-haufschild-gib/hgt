# Hedenmalm--theta Möbius prime-cell boundary-layer conjugacy

- **ID:** P-G47
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) + LEAN FORMALIZATION IN PROGRESS
- **Source:** P-G44--P-G46; Route-P harmonic escape and source-Julia saturation core
- **Statement:** Every interior thermal prime cell is exactly a singular-wall cell under positive semigroup flow `q ↦ q exp(-k)`, where `k=(r-1)log T`; finite boundary transport cannot annihilate a positive cell.

## Goal

Classify nonuniform transition between P-G45 cold vacuum and P-G46 wall freezing.  Decide whether
boundary scaling creates missing Route-P annihilator or only transports existing positive defect.

## Gates

- [x] 0 → 1 in-progress: exact conjugacy, semigroup, source-prime specialization
- [ ] 1 → 2 fully-proven: finalize after Lean source check
- [ ] 2 → 3 formalized: module, umbrella, build, lint, axiom audit green
- [ ] 3 → 4 publication-ready: standalone exposition and external novelty audit

## P-G47 boundary-layer theorem `[PROVED HERE]`

P-G45 gives

\[
 W_{q,r}(T)=\frac{qT^{-r}(T-1)^2}{T(1+qT^{-r})^2}.
\tag{1}
\]

Introduce finite running coordinate

\[
 k=(r-1)\log T,
 \qquad r_k(T)=1+\frac{k}{\log T},
 \qquad \mathcal R_k(q)=qe^{-k}.
\tag{2}
\]

Then exact exponent algebra, not asymptotics, gives

\[
 qT^{-r_k(T)}=\frac{qe^{-k}}{T}
\tag{3}
\]

and hence

\[
 \boxed{W_{q,r_k(T)}(T)=W_{\mathcal R_k(q),1}(T).}
\tag{P-G47}
\]

The transport maps form a positive semigroup:

\[
 \mathcal R_0=\mathrm{id},\qquad
 \mathcal R_{k_1+k_2}=\mathcal R_{k_2}\circ\mathcal R_{k_1},\qquad
 q>0\Longrightarrow\mathcal R_k(q)>0.
\tag{4}
\]

Using P-G46 on the right side of `(P-G47)` yields the complete finite-coordinate limit

\[
 \lim_{T\to\infty}W_{q,1+k/\log T}(T)=qe^{-k}.
\tag{5}
\]

Thus two familiar iterated limits are endpoints of a continuum:

- fixed `r>1`: `k=(r-1)log T→∞`, residue tends to zero (P-G43/P-G45 cold vacuum);
- wall `r=1`: `k=0`, residue is `q` (P-G46 freezing);
- finite `k`: strictly positive interpolating residue `qe^{-k}`.

## Literal source specialization

For prime `p`, slower aperture `x>0`, oriented half-gap `delta>0`, and thermal parameter
`epsilon>0`, set

\[
 q=p^{-1},\quad T=p^{\delta\epsilon},\quad
 k=x\epsilon\log p.
\tag{6}
\]

Then

\[
 1+\frac{k}{\log T}=\frac{x+\delta}{\delta},
 \qquad
 \mathcal R_k(p^{-1})=p^{-(1+x\epsilon)}.
\tag{7}
\]

Therefore every literal interior source cell satisfies

\[
 W_{p^{-1},(x+\delta)/\delta}(p^{\delta\epsilon})
 =W_{p^{-(1+x\epsilon)},1}(p^{\delta\epsilon}).
\tag{8}
\]

P-G44's slower-aperture prime-two valuation and P-G46's wall `1/p` residue are the same running
odds viewed at `k→∞` and `k=0`.  P-G42 hot-edge curvature is initial creation of this same
flow before its ordered prime cascade becomes visible.

## Conjecture loop verdict

### Conjecture P-G47.A

Boundary-layer scaling might supply a new sign-changing or vanishing source current.

**Killed.** `(4)` proves every finite transport preserves positivity and nonvanishing.  It changes
decay exponent but creates no opposite phase.  Boundary-layer renormalization alone cannot force
Julia saturation.

### Positive survivor

Route P's endpoint obstruction is a nonuniform semigroup escape law.  Any successful producer must
intertwine this positive odds semigroup with an independent signed Euler--Gamma/Poisson channel.
Because `k=x epsilon log p`, label dependence is already exact: missing channel must act before
primewise wall evaluation and reverse principal symbol on the same labelled cell.  Scalar
renormalization after `(5)` has no remaining freedom.

## Lean certificate

Module:

```text
formal/GaloisForLFunctions/RHTower/
  HedenmalmThetaMobiusPoleUnitPrimeCellBoundaryLayer.lean
```

Key declarations:

- `thermalBernoulliRunningOdds_add`;
- `thermalBernoulliRunningOdds_pos`;
- `thermalBernoulliBoundaryLayerMass_eq`;
- `thermalBernoulliBoundaryLayerDefectOdds_eq_wall`;
- `tendsto_thermalBernoulliBoundaryLayerDefectOdds_atTop`;
- `thermalBernoulliBoundaryLayerEccentricity_rpow`;
- `prime_boundaryLayer_effectiveOdds`;
- `thermalBernoulliPrimeCell_eq_runningWall`.

## Next hard gate

Find or rule out a source-derived signed intertwiner `D` coupling running Euler odds to the
archimedean/Poisson channel before positive completion.  Required identity must be nonseparable
and coefficient-faithful; a diagonal map of `q e^{-k}` cannot annihilate finite positive `k`.

## Log

- 2026-08-12 — derived exact boundary-layer conjugacy, positive running-odds semigroup, complete
  finite-coordinate limit, and literal slower-aperture prime specialization; Lean module started.
