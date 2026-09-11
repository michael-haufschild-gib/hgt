# Möbius shifted-moment gap and renewal pairing sign

- **ID:** E-LREA-SIGN-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** source sign theorem; novelty unverified; not an RH proof.
- **Lean:** `GaloisForLFunctions.RHTower.MobiusRenewalEnergySign`
- **Research context:** [literal renewal energy attack](../1-in-progress/route-e-literal-renewal-energy-attack.md).

## Exact theorem

Let

```
F_N(x) = sum_{n=1}^N mu(n) exp(-n*x),
V_N(r) = sum_{n=1}^N mu(n)/n^r,
U_N(r) = sum_{n=1}^N mu(n)/(n+1)^r,
E_N(r) = integral_0^infinity x^(r-1) F_N(x)^2 dx.
```

For all `N>=4` and `r>=1`,
`V_N(r)-U_N(r) >= 4^(-r)-5^(-r)`.
There exists `epsilon>0` such that for every `1<r<1+epsilon`, eventually in `N`,

```
U_N(r) < -1/80,
integral_0^infinity x^(r-1) F_N(x) (exp(-x)-F_N(x)) dx < -Gamma(r)/80.
```

Every displayed finite integral is admitted. The mixed pairing is exactly
`Gamma(r)*U_N(r)-E_N(r)` for every `N` and `r>0`.

## Dependency-closed proof

Set `d_n=n^(-r)-(n+1)^(-r)`. These differences are nonnegative for `r>=1`.
Every `(1+mu(n))*d_n` is nonnegative. The terms at `n=1` and `n=4`
contribute `2*d_1` and `d_4`, since `mu(1)=1` and `mu(4)=0`.
Subtracting the telescoping sum of all `d_n` gives

```
V_N-U_N >= 1-2*2^(-r)+(N+1)^(-r)+d_4 >= d_4.
```

For `r>1`, absolute convergence of the Möbius Dirichlet series gives
`V_N(r) -> invZeta(r)`. Here `invZeta` is the regular reciprocal, continuous
and equal to zero at one; no value of the totalized zeta quotient at its pole
is substituted. Since `d_4(1)=1/20`, continuity and convergence give the
uniform negative margin for `U_N` on a nonempty interval above one.

The Gamma atom integral identifies the complete first-atom pairing with
`Gamma(r)*U_N`. Subtracting the admitted square integral yields the mixed
identity. Finally `E_N>=0` and `Gamma(r)>0` give the negative pairing bound.

## No-go closure

- **Excluded mechanism:** eventual nonnegative pairing of the literal source
  with its complete complement `exp(-x)-F_N` near energy order one.
- **Positive survivor:** explicit finite shifted-moment gap, convergence of
  the original moment to the regular reciprocal, and a signed source moment
  uniformly separated from zero at all sufficiently large cutoffs.
- **New insight:** the wrong sign persists on an open interval and through all
  large integer cutoffs; it is not merely a small-prefix exception.
- **Remaining obstacle:** a cutoff-independent quantitative compensation for
  the negative feedback. None of these results bounds the original energy or
  signed off-diagonal covariance from above. Route E remains open.

## Verified declarations and checks

- `RHTower.MobiusRenewalEnergy.difference_moment_lower`
- `RHTower.MobiusRenewalEnergy.tendsto_originalMoment`
- `RHTower.MobiusRenewalEnergy.eventually_shiftedMoment_negative`
- `RHTower.MobiusRenewalEnergy.moment_integral`
- `RHTower.MobiusRenewalEnergy.renewalPairing_eq`
- `RHTower.MobiusRenewalEnergy.eventually_renewalPairing_negative`

`lake env lean /tmp/route_e_renewal.lean` passed without warnings.
`lake build GaloisForLFunctions.RHTower.MobiusRenewalEnergySign` passed.
Module is wired into `RHTower.lean`; generated indexes refreshed.
`scripts/formal_tools.py lint` passed, with repository file-size warnings.
No numerical experiment, `#print axioms`, umbrella build, or full build was run.
