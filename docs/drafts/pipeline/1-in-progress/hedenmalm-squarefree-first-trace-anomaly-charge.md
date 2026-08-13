# Hedenmalm squarefree first-trace anomaly charge

- **Label:** `P-G138`
- **Route:** P
- **Parents:** `P-G137`, `SquarefreeCarlemanDeterminant`, `SquarefreeCarlemanLogExpansion`
- **Stage:** 1-in-progress
- **Type:** theorem / first-trace anomaly localization / determinant no-go
- **Status:** `[PAPER-PROVED] [LEAN EXACT-LEAF GREEN] [NOT RH]`

## Universal-principle conjecture

Squarefree Euler operator `I+A_s` is uniformly invertible and its second regularized determinant
`D2(s)` is holomorphic and nowhere zero on `Re(s)>1/2`. P-G137 nevertheless finds complete Xi
divisor and conormal charge in squarefree source. Conjecture: all discrete charge is carried by
non-trace-class first-trace anomaly left after dividing squarefree overlap by `D2` transport.

For fixed source chart, define

```text
A(sigma,epsilon,u)
 = B_sq(sigma,epsilon,u)
   / (D2(sigma+u epsilon)/D2(sigma)).
```

## Heavy conjecture loop

### P-G138.A — Carleman determinant carries divisor charge

Test whether Hilbert--Schmidt determinant can supply P-G137 multiplicity.

**Expected falsifier.** `D2` is exponential and nowhere zero, so its local analytic order is zero.

**Result:** falsified. Lean proves both analytic order and logarithmic-derivative residue of the
Carleman transport are zero. No Xi multiplicity can live in this factor.

### P-G138.B — first-trace anomaly carries full charge

On strict-right strip, prove `A` analytic and its analytic order equals squarefree overlap order,
hence complete Xi order. Prove its logarithmic/Fisher residue retains full `2m`, while `D2`
connection has zero residue.

**Result:** proved. The anomaly has the overlap's exact local analytic order; at a strict-right Xi
zero this is full Xi order `m`. Its pointed Fisher quotient has residue `2m`.

### P-G138.C — Euler-chamber identification

For `Re(sigma+u epsilon)>1`, prove

```text
A = exp(P(sigma+u epsilon)-P(sigma)),
```

where `P` is prime zeta. Thus source zero is precisely obstruction to retaining a holomorphic
first-trace logarithm past trace-class wall.

**Result:** proved on the Euler chamber with strict real-part hypothesis.

### P-G138.D — global endpoint

Construct anomaly-defined finite source support/multiplicity charge and prove it equals P-G137
charge and canonical Xi reflection self-intersection charge.

**Result:** proved. The anomaly support and multiplicity recover the strict-right Xi divisor
exactly; the anomaly-defined squared reflection charge equals canonical
`xiReflectionSelfIntersectionCharge` for every cutoff.

## Non-theatre gate

Card succeeds only with exact order/residue localization plus Euler-chamber prime-zeta identity.
Merely citing nonvanishing of `D2`, or renaming squarefree overlap, does not count.

## Gates

- [x] 0 → 1: determinant-versus-first-trace question and exact quotient fixed
- [x] 1 → 2: determinant falsified as carrier; first-trace anomaly proved exact positive survivor
- [x] 2 → 3: Lean module, exact leaf build, forbidden-declaration scan, axiom audit, umbrella wiring
- [ ] 3 → 4: publication-ready extraction

## Lean realization

`HedenmalmSquarefreeFirstTraceAnomalyCharge.lean` proves:

- analytic/nonzero Carleman transport and analytic anomaly quotient;
- exact anomaly order, strict-right Xi order, and Fisher residue `2m`;
- zero Carleman logarithmic residue;
- Euler-chamber identity `A = exp(P(sigma+u epsilon)-P(sigma))`;
- anomaly-defined support, multiplicity, and reflection charge;
- exact equality with `xiReflectionSelfIntersectionCharge`.

Direct `lake env lean` and exact-module `lake build` pass. Headline axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. Module is wired into `RHTower.lean`.

## Honest boundary

Even exact localization does not prove RH. It identifies sole source singularity needing control.
Unconditional RH would require proving anomaly admits a zero-free holomorphic logarithm, or an
equivalent source theorem forcing anomaly charge below first nonzero quantum.

## Log

- 2026-08-13 — opened after P-G137 constructed source-defined charge and hostile audit observed
  Carleman determinant is already nonvanishing throughout relevant half-plane.
- 2026-08-13 — P-G138.A falsified and B--D proved in Lean. All discrete reflection charge is the
  non-trace-class first-trace anomaly; regularized determinant contributes zero order and residue.
