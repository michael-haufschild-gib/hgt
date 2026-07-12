# Upper-half-plane polynomial relation detector

- **ID:** `upper-half-plane-polynomial-relation-detector`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED] [FORMALIZED] [BRIDGE]`
- **Lane:** nonlinear differential-relation detection; translated finite jets
- **Statement:** Every nonzero multivariate relation with one-variable polynomial coefficients has
  a nonzero specialization at a finite packet of distinct upper-half-plane translated nodes.

## The theorem

Let `Q∈C[z][X_s:s∈S]` be nonzero.  For every real height `H` there is `z_0∈C` with

```text
Im(z_0)>H,
Q(z_0,X)∈C[X_s:s∈S] nonzero.                                (1)
```

If `(h_i)_(i∈I)` is a finite injective complex shift packet, then `z_0` can be chosen so that

```text
z_0+h_i are distinct,
Im(z_0+h_i)>0                                                (2)
```

for every `i`, while the specialization in (1) remains nonzero.

## Proof

Choose one monomial `X^d` whose coefficient `q_d(z)∈C[z]` in `Q` is nonzero.  The roots of `q_d`
form a finite set.  The vertical ray

```text
{iy:y>H}
```

is infinite, so it contains a point `z_0` which is not a root of `q_d`.  The `X^d` coefficient of
`Q(z_0,X)` is then nonzero, proving (1).

For (2), choose `H` above every number `-Im(h_i)`.  Such an `H` exists because the shift packet is
finite.  Then `Im(z_0+h_i)>0`.  Translation by the common `z_0` preserves injectivity, so the nodes
remain distinct. `QED`

## Prime-log consequence

Combined with `positive-prime-log-polynomial-jet-escape`, the detector gives an unconditional
finite-dimensional statement: every nonzero `C[z]`-coefficient relation in finitely many translated
actual differential-jet variables can be broken inside every bounded prime-log gauge ball at one
packet of distinct upper-half-plane nodes.

The rational-coefficient passage is now formalized in
`rational-coefficient-prime-log-differential-relation-escape`: it canonically clears all
denominators, chooses the detector away from their common divisor, and breaks the honest
specialized rational relation on actual derivatives.

The coefficient-uniform route step is now closed.  For each finite expanded-monomial support and
coefficient-degree bound, `CoefficientPatternDeterminant` packages every complex coefficient
vector into one evaluation-matrix rank-defect locus.  `CoefficientUniformJetEscape` and
`BoundedGaugeGenericity` prove that the actual-derivative defect is closed and nowhere dense in the
complete bounded-gauge topology.  `countable_actualCoefficientFullRank_dense_residual` then gives
the countable Baire assembly over combinatorial patterns.  Individual `C(z)`-coefficient relations
remain uncountable, but they are never enumerated: one determinant excludes all coefficient
vectors of its pattern simultaneously.

## Lean certificate

`GaloisForLFunctions.HTGeometry.PolynomialRelationDetector` proves:

- `exists_upper_specializePolynomialCoefficients_ne_zero`;
- `finite_complex_family_has_imaginary_lower_bound`;
- `exists_upper_noncolliding_polynomial_detector`.

`GaloisForLFunctions.HTGeometry.PrimeLogPolynomialJetEscape` proves the combined theorem
`primeDyadic_polynomialCoefficientRelation_has_gaugeBall_escape`.

`GaloisForLFunctions.HTGeometry.RationalCoefficientClearing` strengthens the detector to avoid a
prescribed nonzero polynomial divisor and composes it with actual differential-jet escape for
nonzero `C(X)`-coefficient relations.

The proof contains no `sorry`, `admit`, project axiom, opaque postulate, or unsafe declaration.

## Classification

The proof is finite-root rigidity plus a vertical-ray choice and is therefore classical.  Its role
is to close a precise analytic-algebraic bridge in the HT realization route, not to supply the new
constraint geometry itself.

## Gates

- [x] 0 → 1: exact detector statement isolated
- [x] 1 → 2: complete unconditional paper proof
- [x] 2 → 3: upper specialization, node geometry, and prime-log gauge-ball composition formalized
- [ ] 3 → 4: no standalone publication planned; classified as a bridge
