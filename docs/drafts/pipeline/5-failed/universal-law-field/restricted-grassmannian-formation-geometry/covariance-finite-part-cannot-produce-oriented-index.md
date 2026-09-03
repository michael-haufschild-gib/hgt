# Covariance finite parts cannot produce an oriented index

- **ID:** ULF-CFPO-001
- **Stage:** 5-failed
- **Type:** unconditional no-go theorem with positive survivor
- **Parents:** `ULF-ZDIA-001`, `ULF-CAGC-001`, `ULF-FACHD-001`
- **Retired claim:** a counterterm-renormalized positive inverse-completion covariance can, by
  itself, have cubic cyclic boundary `mathsf T_D`.

## 1. Big-picture meaning

Completion action and completion charge are different kinds of information.  A Gram/covariance
records how much formation is present; an index records its orientation.  Renormalizing the first
cannot create the second.

This is not a technical gap.  It is an exact parity obstruction.  The universal field must carry
two coupled legs from the start:

```text
metric leg       = singular inverse-completion action,
orientation leg  = source-native reflection-odd current.
```

## 2. Abstract theorem

Let `X` carry an involution `sigma`.  Let

```text
Q : X -> Y,      q : X -> A,
```

where `A` is an abelian group with no nonzero element of order two.  Assume

```text
Q(sigma x)=Q(x),       q(sigma x)=-q(x).              (CFPO.1)
```

**Theorem CFPO-A.** If `q=F o Q` for any map `F:Y->A`, then `q=0`.

**Proof.** For every `x`,

```text
q(x)=F(Q(x))=F(Q(sigma x))=q(sigma x)=-q(x).
```

Thus `2q(x)=0`; the hypothesis on `A` gives `q(x)=0`.  QED.

The conclusion also applies to every limit, finite part, functional calculus, trace, determinant,
or cyclic expression built functorially from `Q`: each still factors through the same even datum.

## 3. Covariance specialization

Let `A_x:E->H` be a source synthesis and let `G>=0` be independent of source orientation.  Then

```text
Q(x)=A_x* G A_x
```

is unchanged by `A_x -> -A_x`.  In particular every regulated inverse-completion action

```text
C_epsilon=A_E*(A_0 A_0*+epsilon I)^(-1)A_E           (CFPO.2)
```

and every coefficient-native counterterm depending only on this covariance is orientation-even.

By contrast, winding is odd:

```text
wind(u^(-1))=-wind(u).                                (CFPO.3)
```

The formation defect satisfies

```text
Tr T(u,v)=wind(u)-wind(v),
Tr T(v,u)=-Tr T(u,v).                                 (CFPO.4)
```

Taking the standard loop `u_n(exp(i theta))=exp(i n theta)` gives nonzero values `n`; hence no
covariance-only natural transformation can recover `(CFPO.4)`.

## 4. Corpus certificate

This parity obstruction already occurs on literal Euler data.

- `centralSoninKoplienkoSecondOrderGram_logCoefficient_neg_invariant` proves that a prime-power
  coefficient and its negative have identical second-order Gram remainder.
- `centralSoninPrimePower_quadraticBlind_linearSemilocalOrientation` proves that the corresponding
  linear semilocal current distinguishes the two orientations.
- `unitary_edge_gram_blind`, `probe_blind_to_winding`, and
  `wilsonPhase_does_not_determine_windingAction` give the same separation in unitary, recurrence,
  and holonomy gauges.
- `thetaQuantileMetricSymplecticCurrent_resolvent_eq_logDeriv` shows the theta resolvent recovers
  divisor orientation only through an antisymmetric metric cross-current, not a quadratic energy.

Therefore the proposed equation

```text
Ch_3(C_rel)=mathsf T_D
```

is false or circular when `C_rel` is constructed from covariance alone.  It can hold only if
`Ch_3` receives an independently derived oriented connection/current.

## 5. Positive survivor

`C_epsilon` remains canonical and useful: it is the prime-mixed nuclear **metric leg**, detects
zero-distance/infinite-action exclusion, and is the only current construction here controlled by
the sub-unit Euler budget.  What survives is a bivariant target

```text
Theta(metric action, oriented source current)=mathsf T_D,             (CFPO.5)
```

where the second input must be fixed before divisor formation, preserve unsquared von Mangoldt
coefficients, reverse under reflection, and satisfy an exact Green/Maurer--Cartan transport law.

The corpus supplies candidates for that second input:
`contract_dirichletMaurerCartanForm_eq_vonMangoldt`, the semilocal linear orientation law, and the
theta metric-symplectic Green current.  It does not yet supply `(CFPO.5)` or its sub-unit bound.

## 6. Status

No-go proof dependency-closed.  Covariance-only transgression retired.  Successor search class is
strictly narrowed to a source-derived bivariant metric--orientation pairing.
