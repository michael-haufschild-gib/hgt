# Complex state-space Hankel boundary for nonnormal ringdown

- **ID:** `complex-state-space-hankel-pseudospectral-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean target)
- **Register:** `[BRIDGE] [CORPUS-USEFUL] [NOT A NOVELTY CLAIM]`

## Claim

Let `K` be a field and let

```text
r(n) = output dot (A^n input)
```

be the scalar observation of a `d`-dimensional linear realization over `K`.  Its leading Hankel
block factors as

```text
H_d(r) = Observability_d(A,output) * Controllability_d(A,input).       (1)
```

Consequently

```text
det H_d(r) = det Observability_d * det Controllability_d,             (2)
det H_(d+1)(r) = 0.                                                    (3)
```

If both finite realization matrices are nonsingular, `(2)--(3)` give an exact positive noiseless
state-dimension certificate.  The singularity conclusion survives pointwise limits and arbitrary
finite-coordinate approximation when the state dimension remains uniformly bounded.

The complex specialization covers diagonal quasinormal-mode packets, nondiagonalizable Jordan
responses, and arbitrary nonnormal finite transfer matrices.  It therefore strictly contains the
current complex-modal theorem and strictly extends the current real state-space theorem.

## RHTower consumer

For the completed moving complex prime--Gamma moments, any nonzero determinant in size `d+1`
excludes every uniformly `d`-dimensional complex state-space local approximation at that base
point.  At the functional-equation center, RH supplies this nonvanishing at every size and hence
excludes every fixed complex state dimension.

The formal implication chain is

```text
finite complex modal width d
  -> exact complex state-space dimension d
  -> fixed-dimension complex local closure d
  -> completed moving Hankel determinant H_(d+1) = 0.                  (4)
```

Thus determinant nonvanishing kills all three model classes at once.

## Formal surface

`formal/GaloisForLFunctions/HTGeometry/FiniteFieldStateSpaceHankelRank.lean` exports:

- `algebraicStateSpaceResponse`;
- `AlgebraicStateSpaceDimensionAtMost`;
- `FixedAlgebraicStateSpaceDimensionLocalClosure`;
- `algebraicStateSpaceResponse_diagonal_eq_finiteModalSequence`;
- `algebraicStateSpaceDimensionAtMost_of_finiteModalWidthAtMost`;
- `algebraicStateSpaceControllabilityMatrix`;
- `algebraicStateSpaceObservabilityMatrix`;
- `algebraicHankelMatrix_stateSpaceResponse_eq_observability_mul_controllability`;
- `det_algebraicHankelMatrix_stateSpaceResponse_eq_observability_mul_controllability`;
- `det_algebraicHankelMatrix_stateSpaceResponse_ne_zero_iff`;
- `exists_algebraicStateSpace_controllability_relation`;
- `det_algebraicHankelMatrix_stateSpaceResponse_succ_eq_zero`;
- `algebraicStateSpaceResponse_exact_hankel_stateDimension`;
- `det_algebraicHankelMatrix_succ_eq_zero_of_fixedStateSpaceDimensionLocalClosure`;
- `not_fixedAlgebraicStateSpaceDimensionLocalClosure_of_det_ne_zero`.

`formal/GaloisForLFunctions/RHTower/CompletedPrimeGammaComplexStateSpaceBoundary.lean` exports:

- `CompletedMovingComplexStateSpaceDimensionAtMost`;
- `CompletedMovingComplexFixedStateSpaceDimensionLocalClosure`;
- `completedMovingComplexStateSpaceDimensionAtMost_of_modalWidthAtMost`;
- `completedMovingComplexFixedStateSpaceDimensionLocalClosure_of_dimensionAtMost`;
- `completedMovingComplexHankelDet_eq_zero_of_fixedStateSpaceDimensionLocalClosure`;
- `not_completedMovingComplexFixedStateSpaceDimensionLocalClosure_of_det_ne_zero`;
- `not_completedMovingComplexFixedStateSpaceDimensionLocalClosure_one_half_of_riemannHypothesis`.

## Physics provenance

- J. L. Jaramillo, R. Panosso Macedo, and L. Al Sheikh, *Pseudospectrum and black hole quasi-normal
  mode (in)stability*, arXiv:2004.06434.  The black-hole QNM problem is a spectral problem for a
  non-self-adjoint operator, so nonnormal response cannot be reduced safely to orthogonal modes.
- K. Destounis and F. Duque, *Black-hole spectroscopy: quasinormal modes, ringdown stability and
  the pseudospectrum*, arXiv:2308.16227.  Pseudospectra are used as a nonmodal stability interface
  for black-hole and horizonless-compact-object spectroscopy.
- R. Panosso Macedo, T. Katagiri, K.-i. Kubota, and H. Motohashi, *Exceptional Points and Resonance
  in Black Hole Ringdown*, arXiv:2512.02110.  Near-coalescing eigenvalues and eigenfunctions motivate
  retaining Jordan/nonnormal finite responses rather than assuming a diagonal modal basis.

## RH boundary

This is not an independent source of Hankel nonvanishing and therefore does not prove RH.  Its
value is hypothesis discharge and architecture exclusion: any future determinant producer
automatically rules out the corresponding fixed complex hidden dimension, including nonnormal
and defective realizations rather than only finite QNM sums.

## Gates

- [x] real state-space and complex modal corpus surfaces audited
- [x] nonnormal/Jordan physics class isolated
- [x] field-generic exact factorization and rank boundary proved in Lean
- [x] complex local-closure theorem proved in Lean
- [x] completed-source consumer proved in Lean
- [x] targeted verification and axiom audit

## Verification

- one combined scratch proof passed before source insertion;
- one serialized targeted build of the deepest RHTower module was run because its `.olean` was
  absent; it cached its single new HTGeometry dependency;
- both touched source files pass direct `lake env lean` checks;
- `FiniteStateSpaceHankelRank.lean` also passes directly after its duplicated real limit and
  local-closure proofs were replaced by specialization of the new theorem;
- the five audited capstones use only `propext`, `Classical.choice`, and `Quot.sound`;
- the lint gate reports neither new module as unreachable; the current repo-wide lint remains
  blocked by unrelated modules being added concurrently without umbrella imports;
- no numerical computation, full build, or self-concurrent Lean build was run.
