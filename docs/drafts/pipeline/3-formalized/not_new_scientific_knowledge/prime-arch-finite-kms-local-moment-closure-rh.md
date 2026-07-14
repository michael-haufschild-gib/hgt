# Prime--archimedean finite KMS and positive-atomic local moment-closure law

- **ID:** `prime-arch-finite-kms-local-moment-closure-rh`
- **Stage:** 3-formalized
- **Type:** FORMALIZED REDUCTION (not new scientific knowledge)
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeArchFiniteKMSLocalMomentClosure.lean`

## Main law

Let `m_n` be the normalized prime--Gamma source moment sequence.  The following are equivalent:

1. RH;
2. for every `N` and `ε > 0`, some canonical finite KMS/Wightman moment sequence approximates
   `m_0,...,m_{N-1}` within `ε` coordinatewise;
3. for every `N` and `ε > 0`, there exist finitely many scalar masses and nodes
   `w_i,x_i ≥ 0` such that

   ```text
   |sum_i w_i x_i^n - m_n| < ε       for every n < N.
   ```
4. for every `j`, one finite positive-atomic sequence approximates the first `j+1` source
   coordinates within the single prescribed error `1/(j+1)`.

The approximating systems or scalar atomic measures may be unrelated for different pairs
`(N, ε)`.  No single finite system and no preassembled thermodynamic family is assumed.

For every admissible rectangular prime--polar source, these equivalent conditions are also
equivalent to

```text
abscissaOfAbsConv (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) ≤ 1.
```

## Lean surface

- `FiniteKMSWightmanLocalMomentClosure`
- `FinitePositiveAtomicMomentSequence`
- `FinitePositiveAtomicLocalMomentClosure`
- `FinitePositiveAtomicDiagonalApproximation`
- `exists_finiteKMSWightmanMomentSequence_tendsto_of_localMomentClosure`
- `finiteKMSWightmanLocalMomentClosure_of_tendsto`
- `finitePositiveAtomicMomentSequence_finiteKMSWightman`
- `finitePositiveAtomicMomentSequence_xiThermalTruncation`
- `primeArchFiniteKMSWightmanLocalMomentClosure_iff_riemannHypothesis`
- `primeArchFinitePositiveAtomicLocalMomentClosure_iff_riemannHypothesis`
- `primeArchFinitePositiveAtomicDiagonalApproximation_iff_riemannHypothesis`
- `primeArchFinitePositiveAtomicLocalMomentClosure_iff_finiteKMSLocalMomentClosure`
- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_primeArchFiniteKMSLocalClosure`
- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_primeArchFinitePositiveAtomicLocalClosure`
- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_primeArchFinitePositiveAtomicDiagonalApproximation`

## Proof

Local finite-block KMS approximation is diagonalized: at stage `j`, choose a system approximating
the first `j+1` moments with error `1/(j+1)`.  The resulting systems converge coordinatewise to
the complete source sequence.  Closedness of the trace-Hankel cone transports finite KMS
positivity to the source, and the existing prime--Gamma trace-Hankel consumer yields RH.

Conversely, under RH the explicit multiplicity-exact Xi thermal truncations converge pointwise to
the source moments.  Every truncation is both a canonical finite KMS/Wightman system and a finite
positive atomic Stieltjes moment sequence.  Finite coordinatewise convergence gives each local
block approximation.

Every finite positive atomic moment sequence has a canonical finite KMS realization at thermal
parameter zero, so the scalar atomic condition feeds the KMS condition without additional
physics hypotheses.

The full cutoff--tolerance quantification is equivalent to the canonical diagonal schedule with
block length `j+1` and error `1/(j+1)`.  Diagonal choice again produces the pointwise limit.

## Proof-burden reduction

The remaining physics or analysis obligation can be local and finite-dimensional.  It is enough
to construct, independently for each finite source block and tolerance, nonnegative scalar masses
and nodes satisfying finitely many approximate value relations.  A thermodynamic family,
Hamiltonian flow, common observable, and compatibility between successive cutoffs are unnecessary.
Equivalently, it is enough to supply one such independent finite certificate at each natural-number
level with the prescribed error `1/(j+1)`.

This does not prove RH: an unconditional proof of the local positive-atomic approximation property
is still missing.  Positively stated, completing that finite interpolation property completes the
critical prime--polar abscissa bound and hence RH.

## Verification

- Direct Lean check: passed.
- Narrow Lake build: passed.
- Formal lint with generated indexes: passed.
- Axiom audit of the principal equivalences: only `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, custom `axiom`, `opaque`, or `unsafe` declaration occurs in the module.
