# Route R common det2/BV Stokes determinant correction

- **Stage:** 5-failed
- **Disposition:** formally falsified as Bockstein annihilator
- **Positive survivor:** exact determinant transgression of the cofinal Gamma Bockstein

## Proposed mechanism

Use the graded `det2` quadratic cocycle and singular BV first-trace counterterm to construct one
corrected determinant-one Stokes product.  Compare source cyclic rotation with both physical Gamma
orientations and conclude that their difference vanishes.

## Falsification

The signed Bockstein coefficient is exactly

```text
b_t(p)=d(p)(det R_t(p)-det R_(-t)(p)),   d(p)>0.
```

Multiplying both orientations by one common nonzero correction `c` gives

```text
c det R_t(p)=c det R_(-t)(p)
  <-> det R_t(p)=det R_(-t)(p)
  <-> b_t(p)=0
  <-> t=0.
```

Thus determinant-one correction preserves, rather than creates, Bockstein annihilation.  A direct
comparison `det R_t=det tau` is also exactly `t=0`; using it as a Stokes law without an independent
source derivation assumes the desired conclusion.

## Positive survivor

The Bockstein has an exact geometric meaning as Fisher-weighted physical orientation-determinant
transgression.  This identifies what a valid producer must change: it needs orientation-sensitive
source data, or a coefficient-generated Rees/corona realization whose source exactness places the
actual physical conormal in the quotient kernel.  Common unimodular conservation is excluded.

## Formal status

Formalized in
`GaloisForLFunctions/RHTower/PrimeGammaCofinalBocksteinDeterminantTransgression.lean` and wired
through the `GaloisForLFunctions.RHTower` umbrella.
