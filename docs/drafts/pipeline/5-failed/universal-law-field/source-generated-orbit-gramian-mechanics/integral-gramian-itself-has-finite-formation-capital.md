# Integral Gramian itself has finite formation capital

- **ID:** ULF-SGOGM-FAIL-004
- **Stage:** 5-failed
- **Status:** `[FALSIFIED]`
- **Positive survivor:** ULF-PCOB-001, self-financing square law

## Claim

Because the pre-divisor prime--Hodge Gramian `mathsf T` is positive, nuclear, and has trace one,
its interpretation as a positive defect should have finite formation capital in the source orbit
that generates it.

## Countertheorem

Write the quasiaffine reachability map as

```text
mathcal R=mathsf T^(1/2)V,
mathsf T=mathcal R mathcal R*,
```

where `U` is unitary.  A positive defect with density `mathsf T` has amplitude
`X=mathsf T^(1/2)`.  Any source factorization `X=mathcal R B` forces

```text
B=V*.
```

The carriers are infinite-dimensional, so `V*` is not Hilbert--Schmidt.  Formation capital is
infinite.  Integral trace and finite source work are different invariants.

## Positive survivor

For the squared density `mathsf D=mathsf T^2`, choose amplitude `X=mathsf T`.  Then

```text
X=mathcal R mathcal R*,
B=mathcal R*,
||B||_HS^2=Tr mathsf T=1.
```

Injectivity makes this the unique control.  One additional formation power is exactly what moves
the integral boundary from infinite capital into the finite-capital ideal.  Future arguments must
not assign finite work directly to `mathsf T`; they must use `mathsf T^2` or prove a different
source factorization.
