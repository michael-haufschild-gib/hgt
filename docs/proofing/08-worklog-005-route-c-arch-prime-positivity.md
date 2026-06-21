# C-2026-06-18-005 Proof Attempt: Route-C Archimedean Minus Prime Positivity

Source: `docs/consolidated/08-conjectures-required.md` §4.

Claim status: `[CONJECTURE]`.

## Target Claim

```text
A_arch - sum_{p in S} P_p >= 0 as S -> all primes <=> RH.
```

## Attempt

The only viable route is to identify the limit with the Weil/FE polarization
`Q_W`. If a family of finite-source quadratic forms `Q_S` satisfied

```text
Q_S = A_arch - sum_{p in S} P_p,
Q_S -> Q_W strongly on a common test space,
Q_S >= 0 for all S or eventually in S,
```

then the limit would give `Q_W >= 0`, hence RH by the Weil positivity
criterion.

## Weakened Theorem

If `Q_S` are positive semidefinite forms converging pointwise on a dense domain
to a closable form `Q_W`, then `Q_W` is positive on that domain. Therefore the
Route-C statement would prove RH once the identification `lim_S Q_S = Q_W` and
eventual positivity are proved.

## Obstruction

The corpus warns that prime and archimedean pieces do not split into separately
positive summands. The completed positivity is a polarization fact, not
componentwise positivity. Thus the required monotone/semi-local inequality is
currently unsupported and may be false-shaped.

## Missing

Define `Q_S`, prove convergence to `Q_W`, and prove positivity without using
zero locations.
