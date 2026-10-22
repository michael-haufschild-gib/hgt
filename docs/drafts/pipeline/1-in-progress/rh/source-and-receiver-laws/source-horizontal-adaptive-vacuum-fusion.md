# Source-horizontal adaptive vacuum fusion

- **ID:** `source-horizontal-adaptive-vacuum-fusion`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / THEOREM (Lean) / OPEN SOURCE REALIZATION
- **Source:** `rh-current-frontier-map.md`; `rh-frankenstein-source-grade-transition-atlas.md`;
  `HedenmalmGammaSewnSquarefreeParityLocalization.lean`;
  `SourceHorizontalAdaptiveFisherCofinalContiguitySelection.lean`
- **Statement:** Adaptive odds split exactly into centered horizontal odds and prime-vacuum odds;
  equality postselection has uniform admission at least `1/(p+1)`. Route N's critical/twisted
  squarefree parity pair reconstructs both adaptive orientations non-equivariantly as `T` and
  `C^2/T`. A uniformly admitted realization of those events on two fixed convergent abelian class
  laws forces neutral horizontal grade and, for every Xi multiplicity copy, RH.

## Goal

Replace overstrong unconditioned adaptive-observer producer by literal cross-source transition:
centered horizontal orientation, prime-vacuum grade, and a uniformly admitted equality relation.
Close scalar coefficient formula from existing source data and isolate only remaining event-level
source realization.

## Gates

- [x] 0 → 1 in-progress: source-pure factorization, hostile postselection audit, Route-N collision,
  and exact open producer frozen
- [ ] 1 → 2 fully-proven: external novelty audit and independent manuscript audit
- [x] paper proof dependency-closed for algebraic factorization and contiguity receiver
- [x] Lean declarations elaborate directly without `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- [x] targeted module build and axiom audit
- [ ] RH: uniformly admitted abelian event realization remains open

## Heavy conjecture loop

### C14.0 — one geometric parity coordinate

**Conjecture.** Use parity of a geometric occupation coordinate to realize adaptive logistic
marginals directly.

**Failure.** Parity has odds equal to geometric ratio. Existing positive abelian parameters supply
only decaying odds and cannot make one fixed event cross from probability zero to one between two
mutually absolutely continuous convergent class laws. This is already prohibited abstractly by
cofinal contiguity.

**Positive survivor.** Parity is nevertheless exact logistic scalarization: odds `r` give success
probability `r/(1+r)`. The obstruction is not logistic realization but arithmetic baseline and
same-source orientation.

### C14.1 — vacuum fusion

**Conjecture.** Split adaptive natural parameter

```text
(t-1) log p = t log p - log p
```

and multiply centered horizontal odds `p^t` by vacuum odds `p^-1` through equality postselection.

**Verdict: PROVED.** For

```text
E(x,y) = xy / (xy + (1-x)(1-y)),
A(x,y) = xy + (1-x)(1-y),
```

centered occupation `x=p^t/(1+p^t)` and vacuum occupation `y=1/(p+1)` satisfy

```text
E(x,y) = q_p(t),
A(x,y) = (p^t+p)/((p^t+1)(p+1)) >= 1/(p+1).
```

Thus postselection cannot conceal cofinal separation in a vanishing aperture.

### C14.2 — varying-aperture escape

**Conjecture.** Although fixed-source observers are impossible off line, varying admission events
could evade contiguity.

**Failure.** If forward admission remains at least `c>0`, adaptive forward conditional success
tends to one, so unconditional forward success stays bounded away from zero. Reflected conditional
success tends to zero, so reflected unconditional success tends to zero. Absolute continuity then
forces forward success to zero as well, contradiction. Only admission collapse can evade the
selector.

**Positive survivor.** Exact producer needs no unconditioned observer and no KL bound: conditional
mass identities plus one uniform forward admission floor suffice.

### C14.3 — Route-N parity collision

Let

```text
C_p = routeNGammaSewnCriticalSquarefreeParityOdds(p) = p^-1,
T_(p,t) = routeNGammaSewnTwistedSquarefreeParityOdds(t,p) = p^(-1-2|t|).
```

**Conjecture.** Existing Route-N source already contains both adaptive scalar orientations after a
non-equivariant reconstruction.

**Verdict: PROVED.** Define

```text
inward  = T_(p,t),
outward = C_p^2 / T_(p,t).
```

Then

```text
inward  = p^(-2|t|-1),
outward = p^( 2|t|-1),
inward * outward = C_p^2.
```

Their squarefree parity probabilities are exactly `q_p(-2|t|)` and `q_p(2|t|)`. Every
nonnegative adaptive grade `u` is obtained by the Route-N parameter `u/2`. Prime label and both
orientations survive; formula uses only already-source-derived critical and twisted parity odds.

### C14.4 — actual source-law realization

**Open conjecture.** For each Xi multiplicity copy and cofinal grade `u_n=2^n|t_q|`, realize Route
N outward/inward parity probabilities as conditional masses of one event family on two fixed
convergent abelian class laws, with forward admission bounded below uniformly in `n`.

This is strictly narrower than previous exact-observer target. Scalar coefficients, reflection
orientations, vacuum bias, prime label, multiplicity parameter, and aperture lower bound are all
closed. Missing theorem is literal source relation producing reciprocal orientation `C^2/T` on
same admitted carrier. Lean certificate
`SourceHorizontalXiRouteNParityFusionCertificate` names exactly this data and
`riemannHypothesis_of_sourceHorizontalXi_routeNParityFusionCertificates` is its RH endpoint.

## No-go closure

- **Exact killing mechanism:** geometric parity alone cannot realize a cofinally separating same
  event under fixed mutually absolutely continuous class laws; postselection only helps if its
  forward aperture collapses.
- **Strongest positive survivor:** adaptive doublet is already coefficient-exact Route-N parity
  data `T` and `C^2/T`, and equality fusion has noncollapsing arithmetic admission.
- **New insight:** baseline `-log p` is not nuisance normalization. It is prime-vacuum grade. Missing
  Frankenstein transition is reciprocal parity orientation fused with that vacuum through a
  uniformly admitted source relation—the same retained-vacuum issue isolated by first-trace /
  Calderón source-grade atlas.
- **Status:** internal corpus novelty only; no external novelty claim yet. Paper dependencies and
  Lean proofs for stated algebraic/measure theorems are closed. Event realization and RH remain
  open.

## Lean

- `formal/GaloisForLFunctions/RHTower/SourceHorizontalAdaptiveVacuumFusion.lean`
- Direct check: `lake env lean GaloisForLFunctions/RHTower/SourceHorizontalAdaptiveVacuumFusion.lean`
  passes.
- Targeted build only:
  `lake build GaloisForLFunctions.RHTower.SourceHorizontalAdaptiveVacuumFusion` passes at
  `[12666/12666]`; no umbrella build was run.
- `#print axioms` for fusion, admission, Route-N doublet, contiguity, abelian specialization, and
  RH endpoint reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden-token scan and `git diff --check` pass; no Lean process remains.

## Log

- 2026-08-12 — C14.0 failed sharply; C14.1–C14.3 proved; C14.2 upgraded receiver to uniformly
  admitted varying relations; concrete abelian/Xi certificate and RH endpoint formalized.
