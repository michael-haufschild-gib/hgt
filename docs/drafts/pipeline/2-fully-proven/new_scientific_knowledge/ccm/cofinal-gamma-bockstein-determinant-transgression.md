# Cofinal Gamma Bockstein determinant transgression

- **Stage:** 3-formalized
- **Type:** exact source/physical comparison and corrected-determinant no-go
- **Formal module:** `GaloisForLFunctions/RHTower/PrimeGammaCofinalBocksteinDeterminantTransgression.lean`

## Theorem

For ordinary prime `p`, let `d(p)>0` be the activation-Fisher density and put

```text
b_t(p)=F_(-t)(p)-F_t(p),
det R_t(p)=-p^t,
det tau=-1.
```

Then, for every real `t`,

```text
b_t(p)=d(p)(det R_t(p)-det R_(-t)(p)).           (1)
```

Consequently the following are equivalent:

```text
b_t(p)=0;
det R_t(p)=det R_(-t)(p);
det R_t(p)=det tau=det R_(-t)(p);
t=0.                                             (2)
```

For every common correction factor `c!=0`,

```text
c det R_t(p)=c det R_(-t)(p) <-> t=0.            (3)
```

In particular a common determinant-one `det2`/BV Stokes correction annihilates the determinant
transgression iff the uncorrected Bockstein already vanishes.

## Proof

By definition, `F_t(p)=p^t d(p)`.  Hence

```text
b_t(p)=d(p)(p^(-t)-p^t)
      =d(p)(-p^t-(-p^(-t))),
```

which is (1).  Since `d(p)>0`, vanishing is equality of the two determinants.  The function
`x -> p^x` is strictly increasing because `p>1`, so `p^t=p^(-t)` iff `t=-t`, hence iff `t=0`.
The source determinant comparison follows identically from `p^t=1`.  Finally, nonzero `c`
cancels from both sides of (3).

## Frontier consequence

The explicit cofinal Bockstein is not an auxiliary quotient artifact: it is the abelianized
orientation-determinant defect of the physical paracyclic landing.  A common unimodular Stokes
factor cannot remove it.  Missing Route-R producer must generate an orientation-sensitive source
transgression before divisor specialization, or instead prove a source-derived corona-kernel
admission for the positive scalar excess.

## Lean audit surface

- `primeGammaCofinalBocksteinCoefficient_eq_determinantTransgression`
- `primeGammaPhysicalRotationDeterminant_eq_reflection_iff`
- `primeGammaCofinalBocksteinCoefficient_eq_zero_iff_determinants`
- `primeGammaCommonCorrectedRotationDeterminant_eq_reflection_iff`
- `primeGammaDeterminantOneStokesCorrection_eq_iff_bockstein_eq_zero`
- `primeGammaBothPhysicalDeterminants_eq_source_iff_bockstein_eq_zero`
