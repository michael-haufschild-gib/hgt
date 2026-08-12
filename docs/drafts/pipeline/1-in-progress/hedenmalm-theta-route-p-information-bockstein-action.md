# Route-P information--Bockstein action identity

- **ID:** `P-G59`
- **Stage:** `1-in-progress`
- **Type:** exact pre-polar precursor identification / determinant-action no-go
- **Status:** `[PAPER-PROVED] [LEAN DIRECT GREEN] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-all-prime-information-virial-divergence.md`
- **Corpus weld:** `PrimeGammaCofinalBocksteinDeterminantTransgression`

## Conjecture

P-G58 shows complete geometric KL diverges globally off wall.  Search before positive
scalarization for coefficient-faithful signed precursor.  Literal candidate is Route R signed
Gamma-Bockstein determinant transgression

```text
beta_p(t)=F_p(p^(-t)-p^t),
F_p=p/(p+1)^2.
```

Test whether P-G58's valuation-one information virial is independent positive receiver or radial
action of this signed source current.

## Result

Lean proves doubled-grade hyperbolic identity

```text
beta_p(2t)=-2 F_p sinh(2t log p).                         (P-G59a)
```

Define canonical radial determinant-action density

```text
A_p(t)=-8 ((p+1)^2/p^2) (log p)^2 t beta_p(2t).
```

Then coefficient cancellation gives

```text
A_p(t)=16 p^(-1)(log p)^2 t sinh(2t log p),               (P-G59b)
d/dt K_p,1(t)=A_p(t),                                    (P-G59c)
K_p,1(t)=integral_[0,t] A_p(r) dr.                        (P-G59d)
```

For `t>0`, signed precursor satisfies `beta_p(2t)<0`, but canonical action density satisfies
`A_p(t)>0`.  P-G58's divergent information virial is therefore accumulated radial work of literal
Gamma-Bockstein determinant transgression.

## Conjecture loop verdict

### Conjecture P-G59.A

Signed determinant transgression supplies cancellation lost by geometric KL scalarization.

**Killed.** Signed Bockstein exists and is exact precursor, but radial grade factor has opposite
sign.  Their product is strictly positive at every prime and positive grade.  Determinant action
creates P-G58 virial rather than cancels it.

### Higher universal principle

Route P/R positive descendants are not merely parallel presentations.  Source chain is

```text
signed orientation determinant difference beta_p
  -- radial action t d/dt --> positive information work A_p
  -- grade integration --> KL holonomy virial K_p,1.
```

Orientation sign is consumed by radial direction before positive completion.  Any surviving
producer must annihilate Bockstein coefficient itself or couple different prime/height phases
before radial action; determinant/KL integration afterward is too late.

## Lean realization

Module:
`formal/GaloisForLFunctions/RHTower/HedenmalmThetaRoutePInformationBocksteinAction.lean`

Headline declarations:

- `primeGammaCofinalBocksteinCoefficient_two_mul_eq_sinh`;
- `sourceHorizontalPrimeBocksteinActionDensity`;
- `sourceHorizontalPrimeBocksteinActionDensity_eq`;
- `hasDerivAt_sourceHorizontalPrimeGeometricKLScaleTerm_zero_eq_bocksteinAction`;
- `intervalIntegral_sourceHorizontalPrimeBocksteinActionDensity`;
- `sourceHorizontalPrimeBocksteinActionDensity_pos`.

## Honest boundary

P-G59 is not RH.  It identifies exact signed precursor and proves its natural action has wrong
polarity for cancellation.

## Next hard gate

Do not apply radial action primewise.  Test only remaining phase-sensitive precursor: retain actual
height phase `p^(-i gamma)` in cross-prime/non-diagonal source complex and ask whether completed
Euler--Gamma continuation supplies a zero boundary before norm, KL, determinant action, or
reflection folding.  Required theorem must be coefficient-faithful and cannot assume Xi landing
equality.
