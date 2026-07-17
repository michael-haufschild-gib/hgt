# Finite von Mangoldt--Gamma full-jet orientation

- **ID:** `finite-von-mangoldt-gamma-full-jet-orientation`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), SOURCE-SIDE JET-CONE PRODUCER
- **Scientific status:** `[PROVED] [FORMALIZED] [BRIDGE] [NOT AN RH PROOF]`
- **Parents:**
  `von-mangoldt-gamma-all-depth-oriented-anomaly.md`;
  `finite-von-mangoldt-gamma-aperture-orientation-floor.md`.

## Theorem

Fix a positive Gamma depth `N`.  For one positive real exponential atom of weight `q`, rate
`lambda`, and real base coordinate `x`, every coordinate `i : Fin N` of the finite Gamma-descent
anomaly is

```text
alpha_(N,i)(q,lambda,x)
 =q*(-lambda)^i*exp(-x*lambda)
   *(sum_(h<N-i)(-lambda)^h/h! - exp(-lambda)).          (1)
```

The derivative factor has parity `(-1)^i`.  The omitted exponential tail of depth `N-i` has
parity `(-1)^(N-i+1)`.  Since `i<N`, these multiply to one common orientation:

```text
(-1)^(N+1) Re alpha_(N,i)(q,lambda,x)>0                 (2)
```

for every `i`, whenever `q>0` and `lambda>0`.

For the actual finite von Mangoldt source, the module proves the exact coordinatewise aggregation

```text
finiteVonMangoldtGammaAnomaly(M,x,N,1)(i)
 =sum_(p : Fin M)
    alpha_(N,i)(Lambda(p+2)/(p+2),log(p+2),x).           (3)
```

All summands are nonnegative after multiplication by `(-1)^(N+1)`, and the `p=0` term, coming from
the prime `2`, is strict.  Hence every nonempty aperture satisfies

```text
forall i : Fin N,
  0<(-1)^(N+1)
      *Re(finiteVonMangoldtGammaAnomaly(M,x,N,1)(i)).    (4)
```

Thus the complete finite anomaly jet lies in one open orthant.  Higher derivative coordinates do
not introduce independent sign choices.

## What this closes

The concurrently strengthened singleton module now supplies `(1)--(2)`.  The present module avoids
duplicating that work and formalizes the missing aperture-level statements:

1. coordinatewise decomposition of any finite real source into singleton anomalies;
2. finite von Mangoldt aggregation `(3)`;
3. strict componentwise von Mangoldt orientation `(4)`;
4. a positive first-prime lower floor in every coordinate, uniform over all nonempty apertures.

This discharges the finite jet-cone part of the proposed reduced Gauss--Ward construction.  It is
stronger than entrywise positivity of a target Hankel matrix: the sign is produced before
continuation from the actual von Mangoldt weights and Gamma clock.

## RH boundary

The child theorem
`von-mangoldt-gamma-bivariate-hausdorff-moment.md` now upgrades componentwise jet positivity to a
canonical source-side Hausdorff moment representation and arbitrary mixed bivariate Gram
positivity across Gamma depths.  The unrenormalized unit source is still not the completed cofinal
Euler Hilbert carrier.  Exact analytic value identities already identify the inverse-tilted
prime--Gamma germ with the completed central moment germ.  The next proof-bearing identity must
show that causal/polar completion is a positive compression or Schur complement of this same
moment kernel.

The remaining chain is

```text
full finite source jet in one strict oriented cone
  -> fixed bivariate source moment kernel + all mixed Gram cones
  -> existing inverse-tilted completed source/Xi value comparison
  -> [OPEN] positive causal/polar compression identity
  -> complete prime--Gamma Hankel cone
  -> RH.                                                  (5)
```

Taking an arbitrary Gram of the coordinates would not close `(5)`: the Gram must be the one whose
trace/value relation is the completed source after the boundary subtraction.

## Lean certificate

Module:

- `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaFiniteJetOrientation.lean`

Principal declarations:

- `finiteExponentialGammaAnomaly_real_apply_eq_sum_singleton`
- `finiteVonMangoldtGammaAnomaly_apply_eq_sum_singleton`
- `finiteVonMangoldtGammaAnomaly_apply_oriented_re_pos`
- `firstVonMangoldtGammaAtom_apply_le_finiteAnomaly`
- `finiteVonMangoldtGammaAnomaly_apply_uniform_firstAtom_floor`

## Gates

- [x] exact arbitrary-coordinate formula
- [x] common depth orientation independent of coordinate
- [x] finite von Mangoldt coordinatewise aggregation
- [x] strict positive source jet cone
- [x] direct Lean check
- [x] exact target build and axiom audit (`propext`, `Classical.choice`, `Quot.sound` only)
- [x] no numerical computation
- [x] source-side all-depth bivariate moment Gram
- [x] inverse-tilted completed source/Xi analytic value comparison (existing modules)
- [ ] positive causal/polar compression identity
- [ ] RH
