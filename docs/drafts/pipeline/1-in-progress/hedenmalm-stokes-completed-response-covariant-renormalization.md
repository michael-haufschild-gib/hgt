# Hedenmalm Stokes completed-response covariant renormalization

- **Label:** `P-G141`
- **Route:** Frankenstein (`P` Stokes first trace + theta/Ward + completed response)
- **Parents:** `P-G140`, `HedenmalmThetaMovingHorizonCovariantHardyGreenRegularization`,
  `HedenmalmThetaPhysicalEndpointCompletedResponseWardBridge`
- **Stage:** 1-in-progress
- **Type:** heavy-conjecture loop / coefficient-faithful renormalization
- **Status:** `[PROVED IN LEAN] [POSITIVE SURVIVOR EXTRACTED] [NOT RH]`

## Conjecture A — critical marginal weld

`[PROVED]`

At valuation zero and critical source aperture, P-G140's positive Stokes moment is exactly the
physical endpoint marginal:

```text
firstTraceMoment(1,(p,0)) = log(p)/p.
```

The finite valuation-corrected completed response must therefore have row marginal equal to this
same labelled moment. Its packet-dependent diagonal is the canonical label-faithful counterterm,
not a fitted scalar Gamma subtraction.

## Conjecture B — hostile mass-conservation audit

`[PROVED; PROPOSED COUNTERTERM FALSIFIED]`

Finite row balancing redistributes but does not annihilate first-trace mass. Prove total coupling
mass equals the finite sum of critical positive moments. If true, completed response alone cannot
cross P-G140's all-prime divergence wall; its cofinal diagonal shell must carry the divergence.

## Conjecture C — covariant moment renormalization

`[PROVED]`

The theta moving-horizon connection should provide the missing before-limit operation. For
centered depth `d`, its labelled prime energy is expected to be exactly

```text
8 d^2 firstTraceMoment(1+2d,(p,0)).
```

This preserves every prime label, kills the universal critical carrier, is summable for every
`d>0`, and extends to zero at `d=0`. Prove equality coefficient-by-coefficient, then identify its
all-prime total with the already formal covariant Ward energy.

## Conjecture D — orientation test

`[PROVED SHARP WALL]`

Audit whether covariant renormalization is odd before energy scalarization. If only its square is
source-defined, reflection makes the two orientations equal without forcing either to vanish; that
is a precise remaining producer, not RH.

Lean proves exactly this split: normalized physical source half-density is reflection-odd
labelwise, while covariantly renormalized first-trace energy is reflection-even labelwise.

## Lean outcome

Module:
`formal/GaloisForLFunctions/RHTower/HedenmalmStokesCompletedResponseCovariantRenormalization.lean`.

Closed results:

1. `firstTraceMoment(1,(p,0)) = physicalPrimeEndpointWeight(p) = log(p)/p`.
2. Every finite completed-response row has that exact labelled marginal.
3. Total finite coupling mass equals the sum of those positive moments; completed balancing only
   redistributes critical divergence into packet-dependent diagonals.
4. Adding a prime changes every old diagonal counterterm by exactly the negative new pair response.
5. The moving-horizon covariant term is coefficientwise
   `8 d^2 firstTraceMoment(1+2d,(p,0))`, equivalently `8 d^2` times the prime-square Euler weight.
6. This renormalized family is summable for every `d>0`.
7. Its all-prime total is exactly the existing covariant Ward energy on every Xi multiplicity copy.
8. Global vanishing of these totals is equivalent to RH.
9. Source vector is reflection-odd while renormalized energy is reflection-even.

Direct elaboration and exact leaf build passed. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. Umbrella import is wired; no umbrella build was run.

## Positive survivor

P-G140's required Gamma/polar finite part is not a scalar subtraction and not finite response row
balancing. The corpus-native operation is now exact:

```text
covariant first trace at depth d = 8 d^2 firstTrace(1+2d).
```

It acts before all-prime limit, preserves every prime label, is ordinarily summable, and has the
correct RH radical. Remaining producer is an **oriented linear Ward law** forcing its zero before
energy scalarization. Any theorem stated only after squaring is reflection-even and cannot identify
the two prime-translation responses `p^(-t)` and `p^t`.

## Non-theatre gate

Success requires exact labelwise identities, finite-packet conservation/no-go, and a summable
source-native renormalized moment. Merely renaming existing energy does not count.

## Gates

- [x] 0 → 1: exact cross-corpus conjectures fixed
- [x] 1 → 2: paper proof or sharp falsifier
- [x] 2 → 3: Lean exact-leaf build, axiom audit, umbrella wiring
- [ ] 3 → 4: publication-ready extraction

## Honest boundary

No claim here proves RH. Required endpoint is still an unconditional source law forcing the
renormalized oriented transport, rather than only its even energy, to vanish on every Xi copy.

## Log

- 2026-08-13 — opened after P-G140 ruled out ordinary passive extraction and corpus audit found
  exact physical marginal `log(p)/p` plus moving-horizon covariant desingularization.
- 2026-08-13 — critical marginal, completed-response conservation falsifier, covariant
  renormalization, summability, reflection parity split, and global RH endpoint proved in Lean.
  Exact module build passed (`12810/12810`); standard Lean axioms only.
