# Source-horizontal Gamma-six/theta conditioning Lyapunov law

- **ID:** `source-horizontal-gamma-six-theta-conditioning-lyapunov`
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) / FRANKENSTEIN SEAM / NOT RH
- **Source:** `rh-current-frontier-map.md`;
  `source-horizontal-gamma-six-relative-reflection-framing.md`;
  `source-horizontal-shared-reservoir-polarization.md`;
  `source-horizontal-route-n-projective-cremona-gamma-six-collision.md`
- **Statement:** Gamma-six two-orientation trace amplification, nonunitary Hermitianizing-gauge
  distortion, Route-P/R rapidity, and genuine Hedenmalm theta boundary flux are one exact
  coefficient-faithful Lyapunov exponent.

## Goal

Retain the horizontal datum after trace moments, normalized probability laws, stable index, and
Hermitian similarity erase it. Determine whether expanded corpus supplies an independent source
bound on that surviving datum, and reject combinations which merely restate the same scalar in
another chart.

Formal module:
`formal/GaloisForLFunctions/RHTower/SourceHorizontalGammaSixThetaConditioningLyapunov.lean`.

## Gates

- [x] 0 → 1 in-progress: exact source carriers, hostile alternatives, and coefficient-safe attack
  identified
- [ ] 1 → 2 fully-proven: internal/external novelty audit and manuscript proof review
- [ ] 2 → 3 formalized: direct Lean, exact leaf build, and axiom audit pass; transition waits
  stage-2 novelty/manuscript audit
- [ ] 3 → 4 publication-ready: standalone theorem/no-go manuscript

## Exact theorem

For shell depth `m`, horizontal rate `delta`, and Hermitianizing diagonal gauge

```text
G_(m,delta)=diag(1,(6^-m)^delta),
```

define its logarithmic diagonal condition ratio

```text
L_(m,delta)=|log((6^-m)^delta)|.
```

Lean proves unconditionally

```text
L_(m,delta)=m log(6)|delta|,
L_(m,delta)/(m log 6)=|delta|                  (m>0),
M_two(m,delta)=5 exp(L_(m,delta))              (m>=3).
```

Thus complete-shell trace amplification is exactly exponential nonunitary conditioning. It is not
an independent moment equation. The same number is absolute inverse-Cayley rapidity:

```text
L_(m,delta)=|artanh(tanh(m log(6) delta))|.
```

For an actual multiplicity-labelled Xi copy `q`, put
`delta=primeDepthBVWoldXiCenteredRate(q)`. Existing source law

```text
thetaFlux(q)=-(thetaMass * thetaRootEnergy(q)) delta
```

then gives the new coefficient identity

```text
L_(m,delta)/(m log 6)
  = |thetaFlux(q)|/(thetaMass * thetaRootEnergy(q)).
```

The denominator is strictly positive. Hence positive-shell distortion vanishes iff the genuine
compact theta boundary current vanishes; global vanishing is equivalent to RH. This terminal
equivalence is an audited receiver, not a source proof.

## Heavy conjecture loop

### C0 — source isometry uniformly bounds balancing gauge

**Conjecture.** Source involution is isometric, so the Gamma-six Hermitianizing gauge has uniformly
bounded condition number and `delta=0`.

**Verdict: FAILED.** Source involution gives cross-fibre adjointness and exchanges `delta` with
`-delta`. Existing Wold-stationarity and relative-framing classifications show that same-fibre
isometry is exactly the missing RH-strength condition. Treating the transported metric as fixed
silently assumes the conclusion.

### C1 — shared-reservoir rank--trace amplification avoids index price

**Conjecture.** Couple arbitrarily many labelled prime coefficients to one negative reservoir,
keeping Frobenius cost small while positive index grows.

**Verdict: FAILED AGAINST EXACT SIGN ACCOUNTING.** The cheap orientation amplifies negative index;
reflection makes those directions positive. Simultaneous realization restores linear positive
index, exactly the term priced by the external rank--trace inequality. The already-formalized
shared-reservoir construction is the strongest positive survivor, not a contradiction.

### C2 — condition growth is independent of shell trace growth

**Conjecture.** Nonnormal conditioning may retain information not already present in unnormalized
two-orientation mass.

**Verdict: FALSIFIED SHARPLY.** Lean proves

```text
M_two=5 exp(L).
```

Trace explosion and Hermitianizing condition growth are exactly the same invariant.

### C3 — fixed-frame rapidity and theta boundary flux are independent constraints

**Conjecture.** Relative reflection skew might supply a second equation capable of killing the
Gamma-shell Lyapunov exponent.

**Verdict: FALSIFIED; COEFFICIENT IDENTITY PROVED.** Normalized `L` is `|delta|`; relative
fixed-frame skew is `tanh(rapidity)`; genuine theta flux is the same `delta` times one strictly
positive mass-energy. The displayed coefficient identity proves all three charts carry one scalar.

### C4 — surviving producer

**OPEN.** Prove from literal pre-divisor prime--Gamma/theta arithmetic that actual fixed-frame
transport has zero Lyapunov exponent, or a genuinely stronger theorem implying this without
assuming same-fibre self-adjointness, Wold stationarity, two-orientation subexponential mass, or
theta-flux annihilation. Each of those four statements is now known to be the same terminal
constraint.

## Higher universal principle

Horizontal information is a relative-metric Lyapunov exponent. Stable conjugacy, spectral moments,
normalized probability, signed reflected trace, and transported metrics quotient it out. Keeping
the fixed frame exposes it, but Gamma trace, Route-P/R skew, and theta Green current are coordinate
changes of one exponent. A Frankenstein proof cannot obtain independence by combining them; it
must derive zero relative metric entropy from a pre-divisor arithmetic conservation law.

## No-go closure

- **Exact killing theorem/mechanism:** shared-reservoir reflection restores positive-index price;
  source isometry is cross-fibre only; all surviving quantitative reporters equal one Lyapunov
  exponent.
- **Strongest positive survivor:** exact mass/conditioning/current coefficient identity above.
- **New insight:** missing producer is zero relative metric entropy in one fixed source frame, not
  bounded scalar trace, additional amplification, normalized probability, or another reflection
  reporter.
- **Status:** Lean source elaboration passes; direct one-process `.olean` generation passes; exact
  leaf target build passes with `maxJobs=1` (Lake replayed its stale dependency graph, but no
  umbrella target was requested); axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`; umbrella import wired without umbrella build. Scoped forbidden-token and whitespace
  scans pass. Novelty remains unaudited externally.

## Log

- 2026-08-12 — C0/C1 rejected against existing exact no-gos; C2/C3 coefficient laws proved in
  Lean; C4 isolated as zero relative metric entropy producer.
