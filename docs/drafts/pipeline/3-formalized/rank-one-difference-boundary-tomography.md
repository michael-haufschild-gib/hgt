# Oriented rank-one boundary currents reconstruct scalar coefficient jets

- **ID:** `rank-one-difference-boundary-tomography`
- **Stage:** 3-formalized
- **Type:** NON-AFFINE RANK-ONE DIFFERENCE SOURCE THEOREM
- **Scientific status:** `[LEAN-FORMALIZED] [SIGNIFICANT POSITIVE THEOREM] [PARENT ALGEBRA; GAUGE QUOTIENT OPEN]`
- **Parent:** `../1-in-progress/rank-one-difference-seam-galois-transgression.md`
- **Statement:** Scalar coefficient prolongations all expose one new boundary output, but the
  orientation of that line reconstructs every positive coefficient derivative visible at the
  clock level.

## Exact theorem

For a coefficient jet `c_r`, define the binomial Leibniz prolongation

```text
(M_c^N u)_j=sum_(k<=j) binom(j,k)c_(j-k)u_k.
```

Lean proves:

```text
p_N M_c^(N+1)=M_c^N p_N,
gamma_N^c(u)|old=0,
gamma_N^c(u)|new=L_N^c(u),
L_N^c(u)=sum_(k=0)^N binom(N+1,k)c_(N+1-k)u_k.
```

Pairing with Taylor curvature gives

```text
(C_N^c u)_i=L_N^c(u)/(N+1-i)!.
```

For every coordinate `k`,

```text
L_N^c(e_k)=binom(N+1,k)c_(N+1-k).
```

The binomial factor is nonzero over `C`. Therefore equality of either `L_N^c` or `C_N^c` for two
coefficient jets forces equality of all positive derivatives `c_1,...,c_(N+1)`.

Passing over every resolution, Lean proves

```text
(forall N, C_N^c=C_N^d)  implies  (forall r>=1, c_r=d_r).
```

Adding equality of the bulk value gives the complete reconstruction theorem

```text
c_0=d_0 and (forall N, C_N^c=C_N^d)  implies  c=d.
```

## No-go and positive residue

The boundary output rank is universally at most one, so rank cannot carry source identity. The
positive invariant before gauge quotient is the oriented covector `L_N^c`; its tower is complete
finite-jet tomography for the positive coefficient germ.

The value `c_0` stays in the bulk symbol, so the complete colligation—not the current alone—recovers
the full coefficient germ. Gauge quotienting this tomography is the next research step.

## Lean declarations

`GaloisForLFunctions.HTGeometry.RankOneDifferenceBoundaryTomography` contains:

- `rankOneCoefficientClockMultiplication`;
- `rankOneCoefficientClockMultiplication_truncate`;
- `rankOneCoefficientIncomingCovector`;
- `rankOneCoefficientIncoming`;
- `rankOneCoefficientIncoming_apply_castSucc`;
- `rankOneCoefficientIncoming_apply_last`;
- `rankOneCoefficientIncomingCovector_single`;
- `rankOneCoefficientJet_eq_of_incomingCovector_eq`;
- `rankOneCoefficientPairedBoundaryCurrent`;
- `rankOneCoefficientPairedBoundaryCurrent_apply`;
- `rankOneCoefficientPairedBoundaryCurrent_eq_outerProduct`;
- `rankOneCoefficientJet_eq_of_pairedBoundaryCurrent_eq`;
- `rankOneCoefficientPositiveJet_eq_of_pairedBoundaryCurrent_tower_eq`;
- `rankOneCoefficient_eq_of_colligationTower_eq`;
- `rankOneGaugeLogCurrent_aut`;
- `rankOneGaugeCoefficient`;
- `rankOneGaugeLogCurrent_div`;
- `rankOneGaugeLogCurrent`.

The last theorem is the exact abstract gauge law

```text
dlog(a sigma(g)/g)=dlog(a)+(sigma-1)dlog(g).
```

It proves that the raw seam is chart-dependent while its logarithmic-current class modulo
difference defects is invariant. Since logarithmic differentiation forgets multiplicative
holonomy, the complete conjectural invariant retains both the multiplicative source class and this
additive transgression.

The module has a cached object, so the new tower theorems were verified by one direct source check
without a build. Their axiom audit uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] general coefficient prolongation formalized
- [x] opposite-variance boundary defect formalized
- [x] exact incoming covector formalized
- [x] exact paired-current outer product formalized
- [x] incoming-covector tomography formalized
- [x] paired-current tomography formalized
- [x] positive coefficient germ reconstructed from the entire current tower
- [x] full coefficient germ reconstructed from bulk-plus-boundary colligation tower
- [x] logarithmic-current gauge transformation law formalized
- [ ] full finite oriented-seam gauge transformation law formalized
- [ ] gauge-invariant seam quotient constructed
