# Hedenmalm theta anomaly--Burnol multiplicative syzygy quotient

## Metadata

- **Label:** `P-G117`
- **Type:** `[THEOREM (LEAN)] [MULTIPLICATIVE SYZYGY] [AFFINE CLASSIFICATION] [NO-GO]`
- **Parents:** `P-G114`, `P-G115`, `P-G116`
- **Status:** theorem proved and formalized; scratch, direct, exact module, axiom, and full umbrella audits passed; repository lint blocked by unrelated pre-existing reachability debt
- **Route:** P (Hedenmalm theta anomaly / completed Burnol co-Poisson cells)

## Frozen conjecture

Arithmetic multiplicativity across overlapping prime frames might impose an additional coherence
law capable of cancelling P-G115's Gaussian horizontal gauge. Test first nontrivial composite cell
`6=2*3` without fitting a coefficient or assuming a zero location.

## Exact source syzygy

Write `A_n(z)` for the completed centered Burnol multiplier. Define entire coefficients

```text
u(z) = scale(6)/scale(2) cos(z log(3)/2),
v(z) = scale(6)/scale(3) cos(z log(2)/2).
```

Lean proves globally, including the removable origin,

```text
A_6(z) = u(z) A_2(z) + v(z) A_3(z).
```

This is the completed co-Poisson image of sine addition for `log 6 = log 2 + log 3`.

## Complete three-cell classification

Every synthesis

```text
b_2 A_2 + b_3 A_3 + b_6 A_6 = 1
```

has unique normal form

```text
(b_2,b_3,b_6)
  = (BurnolAffine(c).1 - u d,
     BurnolAffine(c).2 - v d,
     d),
```

where

- `d=b_6` is the exact multiplicative-syzygy coordinate;
- `c` is P-G114's horizontal determinant-line gauge of the effective pair
  `(b_2+u b_6, b_3+v b_6)`.

Both coordinates are recovered exactly, so this is exhaustive rather than a constructed family.

## Falsification result

For every `c,d,z`, eliminating the six-cell returns `BurnolAffine(c)` and its horizontal gauge is
exactly `c`. Consequently, for P-G115's Gaussian source gauge, existence of any arithmetic
syzygy correction `d` making horizontal gauge zero is equivalent to `Re(rho)=1/2`.

Multiplicative redundancy cannot be used as a cancellation channel. Any proof choosing `d` to
remove the source class would conflate two independent kernel directions.

## Scientific delta

First composite co-Poisson cell exposes a canonical two-stage quotient:

```text
three-cell synthesis torsor
  / exact arithmetic multiplicative syzygies
  = horizontal determinant-line torsor.
```

Route P obstruction survives this quotient faithfully. P-G116's orientation line is not an
artifact of choosing only primes 2 and 3; it remains after adding and exactly eliminating the
first composite source relation.

## Positive survivor

A viable multiplicative producer must contribute a second source equation whose image is nonzero
in the horizontal quotient. Pure sine-addition/composite-cell relations lie entirely in arithmetic
syzygy direction and are exhausted. Next tests should use genuinely nonlocal prime interaction,
completed Gamma/polar relation, or source Ward law before scalar co-Poisson evaluation.

## Theatre audit

- No RH premise, zero-location bound, positivity assumption, or fitted gauge is used.
- Relation is proved at every complex spectral point, including origin.
- Classification covers every three-cell synthesis, not sampled examples.
- Result does not claim RH; it removes one proposed cancellation mechanism and preserves exact
  survivor.

## Formal artifact

`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaAnomalyBurnolMultiplicativeSyzygyQuotient.lean`

Imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Verification log

- 2026-08-13 — Exact source identity and two-gauge classification frozen.
- 2026-08-13 — `/tmp/P117Scratch.lean` passed `lake env lean`.
- 2026-08-13 — Promoted module passed direct `lake env lean` check.
- 2026-08-13 — Exact `lake build GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaAnomalyBurnolMultiplicativeSyzygyQuotient` passed (`12939` jobs).
- 2026-08-13 — Axiom audit reported only `propext`, `Classical.choice`, and `Quot.sound`; full RHTower umbrella build passed (`19790` jobs).
- 2026-08-13 — Repository lint failed on 41 pre-existing unrelated unreachable modules; no P-G115--P-G117 module appeared in failures.
