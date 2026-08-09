# Mass-shifted three-point orbit polarity no-go

- **ID:** `mass-shifted-three-point-orbit-polarity-no-go`
- **Stage:** 3-formalized
- **Formalized companion:** `./mass-shifted-three-point-orbit-polarity-no-go-formalized.md`
- **Type:** FALSIFIED / THEOREM (paper)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 exact open core
- **Statement:** Every actual squared-Xi conjugate orbit has a strictly positive protected
  three-point matrix, yet every genuinely off-line orbit has strictly negative first confluent
  derivative-Hankel minor; separated-point positivity cannot orient the mass-shifted boundary.
- **Novelty:** `[CORPUS-SYNTHESIS][NOVELTY UNVERIFIED]`

## Goal

Test whether new `SquaredXiThreePointOrbitPositivity` and strengthened source height/strip theorems
can lower §9.3 proof burden by supplying finite positive matrices that survive confluence to the
shifted-Hankel moment tower.

## Gates

- [x] 0 → 1 in-progress: exact actual-Xi chamber specialization and confluent minor fixed
- [x] 1 → 2 fully-proven: actual orbit chamber and polarity split proved on paper
- [x] 2 → 3 formalized: `RHTower/MassShiftedThreePointOrbitPolarity.lean`; axiom audit clean
- [ ] 3 → 4 publication-ready: external novelty audit incomplete

## Conjecture/proof loop

### Conjecture 33 — protected three-point positivity survives to the derivative Hankel face

For an Xi zero copy `q`, write

```text
u = (Re rho - 1/2)^2,
v = (Im rho)^2,
T = v-u,
C = 4uv,
H(y) = (T+y)/((T+y)^2+C).
```

The new corpus theorem proves positive definiteness of

```text
M(H) = [[H(0),H(1),H(4)],
        [H(1),H(0),H(1)],
        [H(4),H(1),H(0)]]
```

when `T>2`, `0≤C≤T+1/4`. Conjecture: this protected positivity supplies, or at least points in the
same sign direction as, the first derivative-Hankel minor of the mass-shifted tower.

**FAIL.** The current source height gap gives `v>41/2`, while the critical strip gives `u<1/4`.
Hence

```text
T = v-u > 2,
C = 4uv ≥ 0,
C < T+1/4.
```

The last inequality factors exactly as

```text
(T+1/4)-C = (1-4u)(v+1/4)/1 > 0.
```

Thus every actual Xi orbit lies in the protected three-point chamber and `M(H)` is positive
definite. But its central derivative moments are

```text
m0 = Re lambda,
m1 = Re lambda^2,
m2 = Re lambda^3,
lambda = 1/(T+i sqrt(C)),
```

and the first Hankel minor is

```text
m0*m2-m1^2 = -Im(lambda)^2 |lambda|^2.                  (1)
```

For an off-critical orbit `Im(lambda)≠0`, so (1) is strictly negative. Therefore the same orbit is
strictly positive in the separated-point matrix and strictly negative in the first confluent
derivative-Hankel detector.

## Strongest positive survivor

The polarity split identifies the missing mechanism at the first nonconstant level. Per-orbit
three-point positivity is self-channel geometry; it cannot pay the negative transverse charge in
(1). In a finite packet the exact existing decomposition is

```text
first Hankel minor
  = cross-orbit response-slope Hilbert dispersion
      - total transverse boundary charge.
```

Only cross-orbit dispersion can cancel an off-line self-charge. This sharpens the §9.3 source
target: useful new positive kernels must couple distinct completed-source orbits and remain
compatible with the adaptive null polynomial. Per-orbit protected matrices, however strong, live
in the wrong polarization.

## No-go closure

- **Exact killing theorem/mechanism:** actual Xi orbit simultaneously has positive separated-point
  matrix and negative confluent first minor when off-line.
- **Strongest positive survivor:** kernel-polarity classification; cross-orbit dispersion is the
  unique positive cancellation channel at first nonconstant order.
- **New insight:** repeated positivity failures are shadows of a polarization mismatch, not weak
  constants. Nonlocal response kernels and local factorial-Hankel derivatives need not share sign.
- **Status:** paper proof dependency-closed; Lean specialization closed in
  `RHTower/MassShiftedThreePointOrbitPolarity.lean` (see the formalized companion).

## Corpus boundary

- `SquaredXiThreePointOrbitPositivity` proves protected abstract orbit positivity; its actual-Xi
  chamber specialization is now `RHTower.xiOrbitMatrix_posDef`.
- `XiSquaredEulerApertureHilbertCorrelation` proves (1) and its strict off-line sign; the
  simultaneous polarity split is now `RHTower.xiOrbit_separated_positive_and_confluent_negative`.
- The simultaneous actual-Xi polarity theorem is new corpus synthesis; no external priority claim
  is made.

## Log

- 2026-08-09 — conjecture 33 killed by exact separated/confluent polarity split; actual-Xi chamber
  proof and cross-orbit survivor completed on paper.
- 2026-08-09 — actual-Xi chamber, reciprocal-square chamber coordinates, exact confluent minor
  identity, and the simultaneous polarity split formalized in
  `RHTower/MassShiftedThreePointOrbitPolarity.lean`; card promoted to Stage 3.
