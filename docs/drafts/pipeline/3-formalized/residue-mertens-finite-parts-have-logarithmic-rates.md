# Residue Mertens finite parts have logarithmic rates

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** fixed-conductor-packets-remain-positive-at-growing-overlap

## Statement

Fix a positive modulus `q`. Write `A_F(x)=Σ_(n≤x)F(n mod q)Λ(n)`,
`κ_F=ϕ(q)⁻¹Σ_(r unit)F(r)`, and
`E_F(x)=Σ_(n≤x)F(n mod q)Λ(n)/n−κ_F log x−C_F`, with the existing
residue Mertens finite part `C_F`. For every natural `k`, one horizon
works for every signed residue pattern and all `X≥Y` beyond that horizon:

`|E_F(X)| ≤ 2/(log Y)^k · Σ_r |F(r)|`.

## Proof

Put `R_F(t)=A_F(t)−κ_F t` and `L=Σ_r|F(r)|`. The cumulative source
estimate gives `|R_F(t)|≤Lt/(log t)^(k+2)` beyond a horizon independent
of `F`. Abel summation on `[X,Z]` gives the exact identity

`E_F(Z)−E_F(X)=R_F(Z)/Z−R_F(X)/X+∫_X^Z R_F(t)/t² dt`.

The integral has absolute value at most
`L/((k+1)(log X)^(k+1))`, by the reciprocal-log antiderivative.
Let `Z→∞`: both `E_F(Z)` and `R_F(Z)/Z` tend to zero. Hence

`|E_F(X)|≤L/(log X)^(k+2)+L/((k+1)(log X)^(k+1))`.

For `log X≥log Y≥1`, each summand is at most `L/(log Y)^k`.
Every source coefficient and prime power remains in the identity.

## Lean status

`ResidueMertensFinitePartsHaveLogarithmicRates` proves the exact
`residuePrimeRealError_sub_eq` identity and
`eventually_residuePrimeRealError_log_bound`. Final direct Lean check
passed without warnings; both dependency audits contain only standard
logical axioms. CACT umbrella wired. Supporting source transfer; no
separate contribution count.
