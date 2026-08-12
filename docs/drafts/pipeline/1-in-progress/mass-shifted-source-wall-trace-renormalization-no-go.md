# Mass-shifted source-wall trace renormalization no-go

- **ID:** `mass-shifted-source-wall-trace-renormalization-no-go`
- **Stage:** 1-in-progress
- **Type:** NO-GO + POSITIVE SURVIVOR
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` · §9.3 Exact open core
- **Statement:** Raw adaptive Christoffel source walls carry a universal linearly growing
  newborn-edge dimension tax in every infinite positive moment tower, so no finite positive trace
  can aggregate them; subtracting the forced tax leaves every strict-frontier all-contact residue
  unchanged.

## Goal

Hostile-test proposed common finite trace action for exact all-contact walls. Extract strongest
surviving renormalized target if raw trace is impossible.

## Gates

- [x] 0 → 1 in-progress: exact claim, corpus dependencies, falsifier, and positive survivor identified
- [ ] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: exact Lean theorem, targeted build and axiom audit green
- [ ] 3 → 4 publication-ready: independent novelty/priority review

## Conjecture → proof/fail ledger

1. `[FALSIFIED]` Raw walls are diagonals of a finite positive trace-class arithmetic action.
   In every positive moment tower the degree-`n` wall strictly exceeds `(n+1)/16`; its diagonal
   sequence cannot even tend to zero.
2. `[FALSIFIED AS GENERIC CLOSURE]` Summing source-wall residues after degree separation can be
   the missing common budget. The divergence already occurs in fully positive towers and
   therefore cannot distinguish RH from false RH.
3. `[POSITIVE SURVIVOR]` The forced newborn-edge counterterm is `(n+1)/16`. A viable common action
   must be counterterm-renormalized and Xi-specific, with cancellation performed before degree
   reporting.
4. `[PAPER TARGET]` Subtracting this regular counterterm leaves every intrinsic `distance^d`
   strict-frontier residue exactly unchanged, so renormalization does not erase local obstruction.

## Dependency-closed paper proof

Let `s` be a positive moment form, `beta_j` its monic Jacobi edges, and `E_n` the exact adaptive
Jacobi source energy. For `n>0`, corpus completed-square formula is

```text
E_n = sum_{j<n}(alpha_j+alpha_n/2)^2
    + (3n/4+1) alpha_n^2
    + 2 sum_{j<n} beta_j
    + (n+1)(beta_n+beta_(n+1)).
```

Every displayed account is nonnegative, while `beta_n>0`. Therefore

```text
(n+1) beta_(n+1) < E_n.
```

The source-first wall is exactly

```text
W_n = h_n E_n/(16 h_(n+1)) = E_n/(16 beta_(n+1)),
```

and `beta_(n+1)>0`; hence `W_n>(n+1)/16`. Consequently `(W_(n+1))_n` does not tend to zero and is
not summable. This kills every positive finite-trace interpretation of raw degree walls, including
under complete Hankel positivity.

Define `W_n^ren=W_n-(n+1)/16`. At strict frontier `y`, first contact `d>0`, existing exact residue
law gives `u^d W_n(y+u)->R_d>0`. Since `u^d(n+1)/16->0`,

```text
u^d W_n^ren(y+u) -> R_d.
```

Thus counterterm is mandatory for any common finite action but does not remove local source-wall
principal part. QED.

## Significance and exact residual

This rules out raw trace-class aggregation as a possible completion of §9.3 and identifies correct
category of remaining theorem: an Xi-specific, counterterm-renormalized common action formed
before degree separation. No claim is made that counterterm alone makes wall sequence summable.

## Log

- 2026-08-13 — raw common-trace conjecture killed; forced dimension counterterm and residue-stable
  renormalization isolated.
