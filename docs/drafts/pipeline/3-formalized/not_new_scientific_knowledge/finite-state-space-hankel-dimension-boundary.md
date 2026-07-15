# Finite state-space responses force finite Hankel rank

- **ID:** `finite-state-space-hankel-dimension-boundary`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); cross-field realization boundary and RHTower consumer
- **Register:** `[BRIDGE] [CORPUS-STRENGTHENING] [NOT A NOVELTY CLAIM]`
- **Formal files:**
  `formal/GaloisForLFunctions/HTGeometry/FiniteStateSpaceHankelRank.lean` and
  `formal/GaloisForLFunctions/RHTower/PrimeArchFiniteStateDimension.lean`
- **Statement:** Every scalar response `m_n=output dot A^n input` of a real `d`-dimensional linear
  realization has zero leading Hankel determinant in size `d+1`.  The obstruction survives
  pointwise limits and local finite-coordinate approximation at fixed dimension.  Consequently
  every infinite-support moment clock, and under RH the normalized prime--Gamma source, escapes
  every uniformly bounded finite hidden-state dimension.

## Why this strengthens the corpus

`FiniteSpectralHankelRank.lean` treated diagonalizable finite spectral clocks

```text
m_n = sum_i mass_i node_i^n.
```

The new theorem permits an arbitrary matrix `A`:

```text
m_n = output dot A^n input.                            (1)
```

Diagonal `A` recovers the old spectral model exactly, and this inclusion is formalized.  Arbitrary
`A` additionally contains nonnormal and nondiagonalizable/Jordan responses, finite state-space and
linear recurrent models, unary weighted automata, scalar transfer-matrix correlations, and the
finite-dimensional Liouville representation of quantum channels.  No positivity, stochasticity,
self-adjointness, or diagonalizability is assumed.

## Exact factorization

For the Hankel matrix `H_ij=m_(i+j)`, equation `(1)` gives

```text
H_ij = output dot A^i (A^j input).                     (2)
```

The first `d+1` controllability vectors `A^j input` lie in a `d`-dimensional space.  Choose a
nonzero coefficient vector `c` with

```text
sum_(j=0)^d c_j A^j input = 0.                         (3)
```

Equation `(2)` then gives `H c=0` row by row, so

```text
det H_(d+1) = 0.                                       (4)
```

The proof is a static factorization of observed values.  The index `n` need not be interpreted as
physical time.

## Formalized content

### General HTGeometry layer

- `finiteStateSpaceResponse`
- `StateSpaceDimensionAtMost`
- `FixedStateSpaceDimensionLocalClosure`
- `finiteStateSpaceResponse_diagonal_eq_finiteSpectralMoment`
- `fixedStateSpaceDimensionLocalClosure_of_fixedSpectralWidthLocalClosure`
- `finiteStateSpaceResponse_add`
- `exists_finiteStateSpace_controllability_relation`
- `momentHankelMatrix_mulVec_finiteStateSpace_relation_eq_zero`
- `det_momentHankelMatrix_finiteStateSpaceResponse_succ_eq_zero`
- `det_momentHankelMatrix_succ_eq_zero_of_stateSpaceDimensionAtMost`
- `det_momentHankelMatrix_succ_eq_zero_of_fixedStateSpaceDimension_tendsto`
- `det_momentHankelMatrix_succ_eq_zero_of_fixedStateSpaceDimensionLocalClosure`
- `not_fixedStateSpaceDimensionLocalClosure_of_det_ne_zero`
- `not_fixedStateSpaceDimensionLocalClosure_of_infiniteSupport`

### Prime--archimedean RHTower layer

- `PrimeArchFixedStateSpaceDimensionLocalClosure`
- `primeArchFixedStateSpaceDimensionLocalClosure_of_fixedSpectralWidth`
- `det_primeArchSourceMomentHankelMatrix_succ_eq_zero_of_fixedStateSpaceDimensionLocalClosure`
- `not_primeArchFixedStateSpaceDimensionLocalClosure_of_det_ne_zero`
- `not_primeArchFixedStateSpaceDimensionLocalClosure_zero`
- `not_primeArchFixedStateSpaceDimensionLocalClosure_of_riemannHypothesis`

The RHTower theorem strictly widens the previous finite-clock exclusion: one nonzero source Hankel
determinant excludes every real `d`-state linear realization, not only every `d`-line spectral
clock.

## Physics, AI, and genomic transfer

1. **Quantum physics and quantum many-body theory.**  Finite-dimensional channels compose by
   multiplication in Liouville form.  Finite-bond matrix-product-state correlations are scalar
   matrix elements of powers of a transfer matrix.  Both therefore satisfy `(4)` at the relevant
   transfer-space dimension.
2. **Machine learning and AI.**  Linear recurrent networks, learned linear state-space models,
   unary weighted automata, and finite Koopman truncations use `(1)` as their exact scalar response.
   The theorem applies even when the learned transition is nonnormal and cannot be decomposed into
   independent spectral lines.
3. **Genomics/genetics.**  Finite hidden-state or reporter models use a finite transition/transfer
   operator.  Any lag response or one-parameter observation string reduced to `(1)` has bounded
   Hankel rank.  Thus fixed hidden-state dimension can fit finite windows but cannot exactly or
   locally-cofinally realize an infinite-support moment clock.

This theorem does not claim that arbitrary multiletter HMM word probabilities are captured by one
matrix `A`; their generalized word Hankel matrix uses a family of transition matrices.  The result
applies exactly to their unary, fixed-channel, lag-correlation, or transfer-response specialization.

## No-go and significant positive replacement

**No-go.**  Increasing algebraic sophistication inside a fixed finite hidden state does not cross
the boundary.  Nonnormality, Jordan blocks, signed states, negative weights, and changing the
realization separately for each finite observation window still force determinant `(4)` when the
dimension bound is fixed.

**Positive replacement.**  A single positive or merely nonzero Hankel determinant is a certified
lower bound on hidden-state dimension.  A hierarchy of nonzero determinants forces the required
dimension to grow without bound.  This turns every future determinant theorem in the corpus into a
simultaneous exclusion of finite HMM, recurrent, transfer-matrix, and quantum-channel response
models at the corresponding dimension.

## RH impact

The theorem is not a source producer and does not prove RH.  It strengthens an RH consequence and
the corresponding route gate:

```text
RH -> every leading prime--Gamma Hankel determinant is positive
   -> no fixed-dimensional real linear state-space model locally approximates all source blocks.
```

Unconditionally, the positive first source determinant already excludes hidden dimension zero;
any independently obtained nonvanishing determinant of size `d+1` now excludes dimension `d`.

The research implication is precise.  A quantum/AI/genomic realization of the full source must
have unbounded bond, latent, reporter, or Liouville dimension, or must introduce a nonlinear/nonlocal
source constraint that is not a finite linear realization.  Merely replacing a diagonal finite
clock by a coupled finite transfer matrix cannot advance the RH proof search.

## Literature provenance

- B. Balle, P. Panangaden, and D. Precup, *A Canonical Form for Weighted Automata and Applications
  to Approximate Minimization*, arXiv:1501.06841.  Finite weighted automata represent rational
  series and their Hankel matrices control minimal realization dimension.
- Y. Ohta, *On the Realization of Hidden Markov Models and Tensor Decomposition*,
  arXiv:2008.11487.  Effective hidden-state dimension is bounded through the rank of a generalized
  Hankel matrix.
- V. Zauner et al., *Transfer Matrices and Excitations with Matrix Product States*,
  arXiv:1408.5140.  Finite-bond matrix-product states encode static correlations through a finite
  transfer matrix.
- E. Magesan, J. M. Gambetta, and J. Emerson, *Scalable and Robust Randomized Benchmarking of
  Quantum Processes*, and the Liouville-transfer literature use matrix multiplication for finite
  quantum-channel composition.  Only this standard finite transfer representation, not a
  benchmarking claim, is used here.

The rank law is standard realization theory.  The corpus contribution is its exact formal
strengthening from finite spectral lines to arbitrary finite state-space responses and its direct
prime--archimedean determinant consumer.

## Verification

- isolated scratch proof passed before source insertion;
- one targeted cached build was run for each new module because its `.olean` was absent;
- both touched Lean files pass direct `lake env lean` checks;
- capstone axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`;
- formal lint passes;
- no numerical computation and no full or self-concurrent build was run.

## Gates

- [x] 0 -> 1: exact finite-state value form and corpus consumer identified
- [x] 1 -> 2: controllability relation, Hankel kernel, closure stability, and infinite-support
  escape proved
- [x] 2 -> 3: HTGeometry theorem and prime--archimedean/RH dimension-growth consumer formalized
- [ ] 3 -> 4: standard parent theory; no standalone novelty claim
