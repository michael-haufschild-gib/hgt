# Route P: depletion before inverse incidence no-go (P-G87)

Status: failed route with formally proved positive survivor

## Conjecture

Multiplying P-G85's adjacent local edge Gram by P-G84's positive cofinal residual scalar might
turn the local physical Schur form into P-G78's global weak Gamma kernel.

## Verdict

False.

For prime-index deltas at indices zero and two at one common depth, every adjacent local edge
pairing vanishes. Multiplication by any scalar preserves that zero. P-G86's cumulative primitive
kernel, hence P-G78's weak kernel, equals one on the same pair. P-G84's residual is strictly
positive, so its global reduced weak response equals that positive residual factor and cannot equal
the reduced local edge response.

## Formal obstruction

File:

- `formal/GaloisForLFunctions/RHTower/GammaValuationSchurCofinalReducedWeakKernel.lean`

Headline theorem:

- `gammaSewnCriticalCofinalReducedLocalEdgeKernel_ne_reducedWeakKernel`.

## Positive survivor

Schur depletion and inverse incidence do not commute at operator level. Correct order is:

```text
adjacent physical data -> cumulative inverse incidence -> global Gram -> scalar residual.
```

Applying that order yields P-G88's exact reduced weak kernel. It retains positive same-depth
covariance between every pair of prime axes and has continuous nonnegative quadratic energy.

## No-go closure audit

This route is retired only in its local form. Positive survivor is dependency-closed and formalized
in same Lean module. Re-attempting scalar multiplication of a banded edge Gram cannot recover
nonadjacent covariance.

