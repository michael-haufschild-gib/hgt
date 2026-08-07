# Theta compact boundary-flux energy

- **Stage:** 3-formalized (certificate: `theta-compact-boundary-flux-energy-formalized.md`)
- **Type:** THEOREM
- **Lean target:** `formal/GaloisForLFunctions/RHTower/HedenmalmThetaCompactFluxEnergy.lean`

## Statement

For each multiplicity-exact Xi zero copy `q`, let `z = xiSpectralPoint q`, let `v_q` be its
canonical nonzero eigenvector of the fixed compact theta source inverse, and set

```text
F_q = Re <pinnedBoundaryCLM v_q, v_q>,
E_q = thetaRootEnergy z,
M   = thetaSource.mass,
D_q = normSq z.
```

Then

```text
F_q = 2 M Im(z) E_q
```

and the normalized compact-boundary observer satisfies

```text
(Re(z) F_q / (M E_q D_q^2))^2
  = Im((z^-1)^2)^2.
```

Consequently its multiplicity-exact sum is summable and equals
`xiThermalOrientationEnergy`; it vanishes exactly under RH.

## Proof

The quantile unitary representative of `v_q` is almost everywhere
`sqrt(M) * rootG(thetaSource,z)`.  The root has canonical monopole one.  Its centered dipole is
the negative integral of `rootH`.  Substitution in the universal rank-two boundary formula gives
`F_q = M` times the root boundary pairing.  The exact root flux law identifies that pairing with
`2 Im(z) E_q`, proving the first identity.

At a Xi divisor, `z != 0` and `E_q > 0`.  Direct complex inversion gives

```text
Im((z^-1)^2) = -2 Re(z) Im(z) / normSq(z)^2.
```

Substituting the first identity into the normalized observer makes it the negative of this
imaginary part; squaring proves the pointwise identity.  Summability and the global equality then
follow termwise from the already-proved summability of reciprocal-square orientation terms.
The established theorem `xiThermalOrientationEnergy_eq_zero_iff_rh` gives the zero locus.

## Scientific consequence

The low-degree faithful RH energy is not merely a divisor-indexed diagonal surrogate: it is
exactly the squared output energy of the fixed rank-two boundary observer evaluated on genuine
eigenvectors of one source-built compact operator, after canonical positive normalization.
The remaining annihilation problem is therefore an operator boundary-conservation statement.

## Hostile audit

- No RH premise occurs in either pointwise identity or summability proof.
- Denominators are discharged by `thetaSource.mass_pos`, `thetaRootEnergy_pos`, and
  `xiSpectralPoint_ne_zero`.
- Multiplicity is retained through `XiZeroCopy`.
- This theorem does not claim boundary-flux neutrality; it identifies the exact load-bearing
  positive energy which must be annihilated.
