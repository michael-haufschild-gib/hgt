# Route-P dyadic information--Möbius rigidity

- **ID:** `P-G56`
- **Stage:** `1-in-progress`
- **Type:** full-tower classification / orientation-reversal no-go
- **Status:** `[PAPER-PROVED] [LEAN DIRECT GREEN] [UMBRELLA-WIRED] [NOT RH]`
- **Parent:** `hedenmalm-theta-route-p-geometric-kl-burnol-holonomy-virial.md`

## Conjecture

P-G53 left open whether Gamma/co-Poisson action on full residual dyadic valuation tower could
create opposite information orientation.  For binary digit `j`, define

```text
chi_j(c,s) = chi_B(2^j c, 2^j s).
```

Conjecture exact finite decomposition

```text
chi_geo(c,s) = sum_(j<N) chi_j(c,s) + chi_geo(2^N c,2^N s),  (P-G56a)
```

and test sign and infinite-depth residual rather than assuming tail harmless.

## Result

Lean proves `(P-G56a)`, residual convergence

```text
chi_geo(2^N c,2^N s) -> 0,                               (P-G56b)
```

and therefore, for `c<0`, `0<s<-c`,

```text
chi_geo(c,s) = sum_(j>=0) chi_j(c,s),
chi_j(c,s)>0 for every j.                                 (P-G56c)
```

No exact or asymptotic opposite orientation exists anywhere in binary valuation fibre.

Coefficientwise reason is sharper.  Write prime-power exponent as `k=2^v m`, `m` odd.  At binary
level `j<=v`, alternating Gamma primitive contributes

```text
(-1)^((2^(v-j))m+1) 2^j.
```

Lean proves contributions are

```text
-1,-2,...,-2^(v-1),+2^v
```

and

```text
sum_(j=0)^v contribution(v,m,j) = 1.                      (P-G56d)
```

Full alternating Fermi/Gamma tower reconstructs one positive Bose coefficient at every exponent.
This is binary Möbius inversion, not orientation cancellation.

## Conjecture loop verdict

### Conjecture P-G56.A

Higher dyadic valuation fibres could reverse P-G53 parity chirality and balance full observer.

**Killed.** Every digit is strictly same-sign and their exact infinite sum is total geometric
chirality.  `(P-G56d)` closes route coefficientwise before summation.

### Higher universal principle

Recurring parity, squarefree Gamma, Burnol dyadic contraction, and Bose information phenomena are
shadows of same binary Möbius law: alternating finite-level signs reconstruct unit coefficient
after causal summation.  Sign read before full coefficient-faithful summation is misleading;
positive metric/information read afterward retains strict horizontal orientation.

This explains why neither parity scalarization nor full dyadic completion is producer.  Potential
opposite sign lives only in pre-completion singular amplitude coordinate, before binary Möbius
resummation and before KL/Hellinger convexification.

## Lean realization

Module:
`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaRoutePDyadicInformationMobiusRigidity.lean`

Headline declarations:

- `sourceHorizontalGeometricKLChirality_finiteDyadic_decomposition`;
- `sourceHorizontalDyadicBitKLChirality_pos`;
- `tendsto_sourceHorizontalGeometricKLChirality_dyadicResidual`;
- `hasSum_sourceHorizontalDyadicBitKLChirality`;
- `sourceHorizontal_dyadicGammaExponentCoefficient_eq_one`.

## Honest boundary

P-G56 is not RH.  It decisively retires dyadic orientation reversal but does not prove required
pre-completion singular source sign.

## Next hard gate

Weld binary Möbius unit `(P-G56d)` to actual Burnol causal contraction
`T₂ f₀=-fract(t)/t`.  Determine whether first-wall singular residue supplies independent boundary
unit before Gamma factor `w-1`; reject any proposed law factoring through completed/KL/Hellinger
quotient, since P-G55--P-G56 prove those quotients preserve strict off-wall orientation.
