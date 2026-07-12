# Countable-shift polynomial differential freeness

- **ID:** `countable-shift-polynomial-differential-freeness`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED] [FORMALIZED] [BRIDGE]`
- **Lane:** countable source selection for the facet-sewn HT realization
- **Statement:** For every countable injective complex shift palette, a dense residual set of
  bounded prime-log gauges satisfies coefficient rigidity for every finite translated
  polynomial-coefficient differential pattern simultaneously.

## The theorem

A finite pattern consists of:

```text
m                         number of distinct shifts,
h : Fin m -> Gamma        injective shift packet,
n : Fin m -> N            jet-order bounds,
M_1,...,M_k               distinct monomials in those jets,
q                         polynomial coefficient-degree bound.
```

The complex coefficient vector is not part of the code.  For a pattern, one chooses
`k(q+1)` noncolliding upper evaluation rows and forms the square expanded matrix

```text
A_u(a,(r,d)) = z_a^d M_r((g_u^(j)(z_a+h_i))_(i,j)).         (1)
```

The finite-pattern theorem proves that the rank-defect set `{u:det A_u=0}` is closed and nowhere
dense.  If `Gamma` is countable, the dependent type of all finite patterns above is countable:
finite functions, finite jet rectangles, finite-support exponent vectors, and natural degree
bounds are all countable.  Baire category therefore gives a dense residual set of bounded gauges
for which every matrix (1) is invertible.

For such a gauge, suppose one encoded relation holds throughout the common upper domain:

```text
sum_(r,d) c_(r,d) z^d M_r((g_u^(j)(z+h_i))_(i,j)) = 0.      (2)
```

Evaluating (2) at the rows selected for its pattern gives `A_u c=0`.  Invertibility forces
`c=0`.  Thus every encoded functional relation is the zero relation. `QED`

## Exact facet-sewn palette

For a finite vertex type `V` and real periods `omega_v`, define

```text
Gamma_omega = Q(i) + sum_(v in V) Z omega_v subset C.       (3)
```

The raw representation in (3) need not be unique, so Lean uses the range subtype in `C`.  That
subtype is countable and its inclusion into `C` is injective.  The theorem therefore supplies one
bounded prime-log gauge satisfying (2)-rigidity on every finite packet from the exact shift palette
used by the facet-sewn construction.

## Formal boundary

The normalization theorem is now formalized in `PolynomialPatternRectangularization`: arbitrary
finite `C[z]`-coefficient support is encoded by one pattern, its coefficient vector is faithful,
and its specialized evaluation is reconstructed exactly.  `PolynomialCoefficientDifferentialFreeness`
therefore proves the conventional finite-packet `C[z]`-relation statement.  Canonical rational
coefficient clearing and the corresponding `C(z)` source theorem are formalized separately in
`countable-shift-rational-differential-freeness`.

The remaining interface boundary is representation, not normalization: place the actual prime-log
functions in a differential field of meromorphic functions and identify the cleared functional
predicate with the repository's `DifferentialIndependent (RatFunc C)` definition.

## Lean certificate

`GaloisForLFunctions.HTGeometry.CountableDifferentialPattern` proves:

- countability of `FiniteDifferentialPattern Gamma` for countable `Gamma`;
- `universalPatternFullness_dense_residual`;
- `exists_universalPatternFullRankGauge`;
- `patternRelation_coefficients_eq_zero`;
- `countableShiftPolynomialDifferentialFree_dense_residual`;
- `exists_countableShiftPolynomialDifferentialFree`.

`GaloisForLFunctions.HTGeometry.CountableShiftPalette` proves countability of (3) and the exact
specializations `rationalLatticeShift_polynomialDifferentialFree_dense_residual` and
`exists_rationalLatticeShift_polynomialDifferentialFree`.

The certificate has no `sorry`, `admit`, project axiom, opaque postulate, or unsafe declaration.

## Classification

The countability and Baire assembly are classical.  This is a formal bridge from the
candidate-new finite rank-defect geometry to the facet-sewn source, not independent new scientific
knowledge.

## Gates

- [x] 0 → 1: coefficient-free countable pattern code isolated
- [x] 1 → 2: complete unconditional proof above
- [x] 2 → 3: dependent countability, simultaneous full rank, coefficient rigidity, and exact
  rational-lattice palette specialization formalized in Lean
- [ ] 3 → 4: no standalone publication planned; classified as a bridge
