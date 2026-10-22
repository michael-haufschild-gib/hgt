# Theta compact source-entropy boundary weld

- **Stage:** 3-formalized (certificate: `theta-compact-source-entropy-boundary-weld-formalized.md`)
- **Type:** THEOREM
- **Lean target:** `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaSourceEntropyBoundaryWeld.lean`

## Statement

For every multiplicity-exact Xi zero copy `q`, the signed boundary quadratic form of its genuine
eigenvector of the fixed compact theta source inverse is exactly the prime-two reflected source
entropy times the canonical positive mass-energy weight:

```text
thetaXiRankTwoBoundaryFlux q
  = thetaSource.mass * thetaXiRootEnergy q
      * riemannReflectedSourceEntropy (q.1 : C).
```

Consequently the sign of the operator boundary flux, the sign of the reflected arithmetic source
entropy, and the horizontal side of the Xi divisor are identical.  After canonical normalization,
the squared boundary output is the source-entropy density term copy by copy, so their global sums
agree.

## Proof

The compact boundary theorem gives

```text
F_q = 2 M Im(z_q) E_q.
```

For `z_q = -i (rho_q - 1/2)`, one has `Im(z_q)=1/2-Re(rho_q)`.  The prime-two reflected entropy law
gives

```text
S_q = -sourceCayleyTransverseRate 1 rho_q
    = -2 (Re(rho_q)-1/2)
    = 2 Im(z_q).
```

Thus `F_q=M E_q S_q`.  Substitution into the normalized boundary term and the established
pointwise source-entropy density identity proves equality of the signed-normalized squares.  The
global equality follows by termwise summation.

## Hostile audit

- No RH premise occurs.
- Sign is retained until the final squared density; this is stronger than composing two global
  RH-equivalent energies.
- `XiZeroCopy` retains multiplicity.
- The equality does not assert entropy vanishing.  It identifies the exact source-side signed
  quantity whose independent conservation or neutrality would finish the compact route.

