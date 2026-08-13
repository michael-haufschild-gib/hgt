# Shifted-Xi characteristic-apex contact orientation

- **ID:** `shifted-xi-characteristic-apex-contact-orientation`
- **Stage:** 3-formalized
- **Route:** U
- **Type:** THEOREM
- **Scientific status:** `[PROVED HERE] [CORPUS-NOVEL] [LEAN-PROVED]`
- **External priority:** provisional; this is the source-specific first-order resolution of the
  top-product wall isolated by the radial Christoffel law.
- **Lean status:** complete in
  `RHTower/XiShiftedCanonicalAdmissionCharacteristicApexContactOrientation.lean`, umbrella-wired.
  Direct `lake env lean` passes. Targeted
  `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionCharacteristicApexContactOrientation`
  succeeds and produces an importable `.olean`. Axiom audit of all seven public theorems reports
  only `[propext, Classical.choice, Quot.sound]`. Forbidden-token scan is clean. Repository lint
  reaches the new module; its nonzero exit is caused by unrelated unwired modules, not this file.

## Frozen theorem

Put

```text
A_n(y) = P_n(y,1/y),
N_n(y) = <P_n(y),P_n(y)>_y,
T_n(y) = A_(n+1)(y) A_n(y) / N_n(y),
R_n(y) = A_n(y) / A_(n+1)(y).
```

For `y>0`, `n>0`, and a positive shifted-Xi moment block through size `n+3`, every contact
`A_n(y)=0` satisfies

```text
A_(n+1)(y) != 0,
T_n'(y) = -2n A_(n+1)(y)^2 / N_n(y) < 0,
R_n'(y) = -2n < 0.
```

Lean also proves source-native versions with no positivity premise whenever

```text
routeUParabolicDegreeHorizon * (n+3)^2 <= y.
```

## Proof

The already formalized characteristic transport gives, at `A_n(y)=0`,

```text
A_n'(y) = -2n A_(n+1)(y).
```

Finite positive-block no-common-root proves the degree-`n+1` monic value is nonzero. The `n+3`
block identifies that monic polynomial with the actual degree-`n+1` canonical admission, hence
`A_(n+1)(y) != 0`. Differentiating the exact canonical product gives

```text
T_n' = (A_(n+1)' A_n + A_(n+1) A_n')/N_n
       - A_(n+1) A_n N_n'/N_n^2.
```

Both terms containing `A_n` vanish at contact. Norm positivity and adjacent nonvanishing make the
surviving value strictly negative. In the quotient `R_n`, the same cancellation removes the norm
and adjacent amplitude entirely, leaving the universal slope `-2n`. No computation, numerical
certificate, limit, RH premise, or added axiom is used.

## Conjecture / failure / pivot ledger

1. **First-order radial Christoffel energy orients contact.** `[FAILED]` Its derivative is zero at
   `A_n=0`; stationarity alone has no sign.
2. **Differentiate the isolated normalized top product at contact.** `[PROVED HERE]` The unknown
   degree-`n+1` velocity and norm velocity are multiplied by `A_n` and vanish. The only survivor is
   a strictly negative square.
3. **Amplitude-free contact coordinate exists.** `[PROVED HERE]` The projective ratio
   `A_n/A_(n+1)` has universal slope `-2n`.

## Higher principle

The previous sign ambiguity was an off-contact coordinate ambiguity, not contact ambiguity.
Characteristic transport coorients every positive-degree zero universally after projectivization.
Norm, Jacobi drift, and adjacent amplitude are gauge variables at contact. The true remaining
global obstruction is phase accumulation through the poles `A_(n+1)=0`: local contact orientation
is fixed, but projective cells can reset across adjacent-degree poles.

## Exact remaining obstruction

This theorem is not RH. It closes the local top-product contact wall but does not orient the product
between contacts. Route U now needs a global projective/Pruefer law that controls passage through
the interlacing poles, or an equivalent source-specific cumulative phase/boundary budget on a
cofinal parabolic schedule. Repeating local transversality, generic interlacing, or stationary
Christoffel-energy arguments cannot supply that global phase control.
