# Before There Was Time: the holographic determinant horizon

- **ID:** `holographic-determinant-horizon-integrability`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / MATRIX PRINCIPAL SYMBOLS / JOINT HYPERTRANSCENDENCE
- **Scientific status:** `[GENERAL DIFFERENTIAL HORIZON LEAN-FORMALIZED] [CONCRETE REALIZATION OPEN] [NOVELTY UNVERIFIED]`
- **Statement:** A flat finite-rank observable sector has either no hypertranscendental law
  direction or one intrinsic determinantal characteristic hypersurface. The infinite sequence of
  layer horizons cannot vary independently.

## 1. Matrix symbol system

Let `g` be a finite-dimensional law space and let every graded observable layer have rank `r`.
For a law direction `A`, write the principal action between consecutive layers as

```text
S_n(A) : V_n -> V_(n+1),    dim V_n = r.
```

The rank-one theory corresponds to `r=1`. Commutator closure at filtered order one forces the
commuting-square equations

```text
S_(n+1)(A) S_n(B) = S_(n+1)(B) S_n(A)                 (1)
```

for all `n,A,B`. Equation `(1)` is the vanishing of the matrix principal-symbol curvature.

## 2. Exact determinant-horizon theorem `[LEAN SOURCE-CHECKED]`

Let an `r`-component initial observable packet have an algebraically free complete source
filtration, and let one law act triangularly with principal blocks `S_n(A)`. Then

```text
the complete joint law-jet packet is algebraically independent
  iff
det S_n(A) != 0 for every n.                              (2)
```

Thus the differential-algebraic law spectrum is initially the countable union

```text
union_n {A | det S_n(A)=0}.                               (3)
```

## 3. Flat determinant rigidity `[PAPER PROOF COMPLETE]`

Assume `(1)` and suppose there is one direction `A_0` with

```text
det S_n(A_0) != 0 for every n.                            (4)
```

Taking determinants in `(1)` with `B=A_0` gives

```text
det S_(n+1)(A) det S_n(A_0)
  = det S_(n+1)(A_0) det S_n(A).                          (5)
```

Both reference factors in `(5)` are nonzero. Therefore

```text
det S_(n+1)(A)=0 iff det S_n(A)=0.
```

Induction identifies every set in `(3)` with the first determinantal locus

```text
H = {A | det S_0(A)=0}.                                   (6)
```

If no direction satisfies `(4)`, every direction belongs to `(3)`. Consequently `(2)` would give
the exact dichotomy:

```text
joint HT phase is empty,
or
the complete DA spectrum is the single determinantal hypersurface H.
```

For `r=1`, `H` is the hyperplane proved in
`pretemporal-horizon-curvature-rigidity`. For `r>1`, this is the first integrable setting in which
the horizon can be nonlinear.

The complete determinant-rigidity claim is unconditional in
`formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolDeterminantHorizon.lean`:

- `matrixPrincipalSymbol_det_cross` proves `(5)`;
- `matrixPrincipalSymbol_det_succ_eq_zero_iff` proves equality of adjacent singular loci;
- `matrixPrincipalSymbol_det_eq_zero_iff_first` identifies every layer with the first;
- `matrixSymbolCharacteristicSet_eq_firstSingularSet` proves `(6)` for the complete union;
- `matrixSymbolCharacteristicSet_eq_univ_of_no_regularDirection` proves the empty-regular-phase
  branch;
- `matrixPrincipalSymbolFlat_characteristicSet_dichotomy` proves the full matrix-symbol dichotomy.

Direct source checking and the targeted leaf build pass.

The exact joint criterion `(2)` and its combination with determinant rigidity are unconditional in
`formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolHypertranscendenceHorizon.lean`:

- `MatrixPrincipalPacketRealization` specifies the finite block principal-symbol law, including
  equality of every diagonal block with the reindexed matrix symbol rather than determinant data
  alone;
- `algebraicIndependent_matrixLinearForms_blockTriangular_iff` proves the exact finite block
  criterion;
- `matrixPrincipalPacket_algebraicIndependent_iff` proves `(2)` for the complete packet;
- `matrixPacketDependentSet_eq_characteristicSet` identifies `(3)` with the actual complete joint
  algebraic-dependence spectrum;
- `matrixPacketDependentSet_eq_firstSingularSet_of_flat` proves the one-horizon branch;
- `matrixPrincipalPacket_flat_dependenceSpectrum_dichotomy` proves the exact total/one-horizon
  dichotomy.

The finite interface is derived from an explicit strict-lower-layer law in
`formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolLowerLaw.lean`:

- `MatrixPrincipalLowerLaw` says that the same-layer block is exactly the matrix principal symbol,
  every later-layer coefficient vanishes, and the remainder points strictly into the past
  filtration;
- `matrixPrincipalPacketRealization_of_lowerLaw` proves that these local laws generate the packet
  realization;
- `matrixPrincipalLowerLaw_algebraicIndependent_iff` gives the exact complete packet criterion
  directly from that local law.

The actual differential theorem is unconditional in
`formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolDifferentialHorizon.lean`:

- `matrixPrincipalLowerLaw_differentialIndependent_iff` proves that a differentially independent
  source family produces a differentially independent target family exactly when every symbol is
  nonsingular;
- `matrixPrincipalLowerLaw_hypertranscendentalOver_iff` gives the one-element
  hypertranscendence specialization;
- `matrixDifferentialDependentSet_eq_characteristicSet` identifies the determinant union with the
  actual differential-algebraic law spectrum;
- `matrixDifferentialDependentSet_eq_firstSingularSet_of_flat` and
  `matrixPrincipalLowerLaw_flat_differentialSpectrum_dichotomy` prove the exact flat holographic
  horizon theorem.

The remaining realization problem is concrete rather than formal: exhibit a named function or
field-observable family whose full jets satisfy `MatrixPrincipalLowerLaw`. That
application-facing hypothesis cannot be advertised as physics until it is constructed.

## 4. Algebraic object

The flat symbols form a representation of the layered commutative-square quiver: the arrows are
the law directions and `(1)` imposes the square relations. Equivalently, after choosing one
everywhere-invertible direction, the remaining pencils transport coherently between layers. The
determinant horizon is the singular support of this symbol representation.

The conjectural broad theory identifies that quiver support with the ordinary
differential-algebraic spectrum of the observable packet. This is not the ordinary characteristic
variety of a fixed differential operator: the point of the variety is itself the chosen
derivation law.

## 5. Spectral strengthening and parent-theory verdict

Relative to one everywhere-invertible direction, equation `(1)` makes consecutive normalized
symbols conjugate. Hence their complete characteristic polynomials are layer-independent; the
determinant horizon is only the zero-eigenvalue slice of one conserved spectral cover. This is
formalized in
`formal/GaloisForLFunctions/HTGeometry/MatrixPrincipalSymbolSpectralHolography.lean`.

This is a discrete Lax/ispectral transport law and is therefore `[BRIDGE]`, not a novelty claim.
Its role is structural: it identifies the exact parent theory and shows that the potentially new
content must involve the hypertranscendence/dependence spectrum, not isospectrality itself.

## 6. Physical interpretation `[CONJECTURE]`

Before a time direction is chosen, `g` parametrizes candidate consistent laws and the rank `r`
records the number of observable channels crossing each filtration layer. Flatness forbids a new
horizon at every scale: the complete infinite system is encoded on one degree-`r` boundary
hypersurface. Nontrivial horizon topology therefore measures multi-channel observable structure,
while failure of `(1)` is the curvature/anomaly found in the rank-one theorem.

No claim is made that a known QFT, black hole, or cosmology realizes this symbol system. An actual
application must reconstruct `V_n`, `S_n`, and the algebraically free source from its observable
constraints.

## 7. Anti-theatre and novelty gate

Taking determinants of a commuting square is elementary and is not novelty. Block-triangular
algebraic-independence transfer is also standard. Candidate scientific content is the complete
classification `(2)`--`(6)`: the ordinary differential-algebraic direction spectrum of a flat
finite-rank observable sector is either total or one intrinsic determinantal hypersurface.

Parent theories to audit are characteristic and support varieties of filtered modules,
representations of commutative-square/Beilinson quivers, matrix pencils and determinantal
hypersurfaces, Spencer formal integrability, discrete Lax systems, Higgs bundles, and parametrized
differential Galois theory. Current searches found each ingredient separately but no theorem
identifying a law-parameter determinant support with the complete ordinary joint
hypertranscendence spectrum. This is an absence-of-hit verdict, not a priority claim.

## 8. RH impact

The theorem would constrain any multi-component completed-`L`-function law theory: if its
constraint algebra is flat and the source filtration has constant rank `r`, every proposed
critical-law wall must be the same determinantal hypersurface. This does not prove RH, but it rules
out independent scale-by-scale walls and identifies the only possible finite-rank symbol geometry.

## 9. Lean route

- [x] formalize matrix-symbol flatness and determinant cross-ratio identity
- [x] prove the common singular-locus theorem and empty/common-horizon dichotomy
- [x] derive the packet realization from an explicit strict-lower-layer principal law
- [x] prove finite block-triangular algebraic-independence transfer
- [x] prove exact joint hypertranscendence criterion `(2)`
- [x] combine it with determinant rigidity into the complete spectrum theorem
- [x] lift the theorem to genuine differential independence and one-element hypertranscendence
- [x] formalize and classify the discrete-Lax spectral strengthening as bridge material
- [ ] construct a concrete named function/QFT observable realization of the lower law
- [x] targeted leaf build, formal lint, and terminal axiom audit
