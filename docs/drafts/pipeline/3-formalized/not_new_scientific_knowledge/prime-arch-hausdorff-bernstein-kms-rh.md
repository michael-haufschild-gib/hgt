# Prime--archimedean Hausdorff--Bernstein finite-system law for RH

- **ID:** `prime-arch-hausdorff-bernstein-kms-rh`
- **Stage:** 3-formalized
- **Type:** FORMALIZED REDUCTION (not new scientific knowledge)
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT AN RH PROOF]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/PrimeArchHausdorffBernsteinKMSRH.lean`

## Main law

Let

```text
m_n = normalizedPrimeArchMoment n,
D(k,0) = m_k,
D(k,r+1) = D(k,r) - D(k+1,r).
```

Lean proves the exact equivalence

```text
(forall k r, 0 <= D(k,r)) <-> RiemannHypothesis.
```

For every admissible rectangular prime--polar source, the same condition is equivalent to

```text
abscissaOfAbsConv
  (rectangularPrimePolarSourceTailNegativeDirichletCoefficient L N) <= 1.
```

The condition is entirely linear in the normalized prime--Gamma source values.  Equivalently,

```text
D(k,r) = sum_(j=0)^r (-1)^j binom(r,j) m_(k+j).
```

The recursive definition is the one used by Lean.

## Canonical finite systems

For a real sequence `m`, define the Bernstein value

```text
w_(M,i) = momentFunctional m (bernsteinPolynomial R M i).
```

Complete difference nonnegativity makes all `w_(M,i)` nonnegative.  At approximation level `N`,
put the degree-`N+1` weight `w_(N+1,i)` at the scalar node `i/(N+1)`.  This gives the finite
positive-atomic moment sequence

```text
b_N(n) = sum_(i=0)^(N+1) w_(N+1,i) (i/(N+1))^n.
```

The formal falling-factorial identity is

```text
sum_i (i)_j w_(M,i) = (M)_j m_j.
```

Expanding ordinary powers using Stirling numbers of the second kind gives the exact formula

```text
b_N(n)
  = sum_(j=0)^n S(n,j) ((N+1)_j/(N+1)^n) m_j,
```

and Lean proves `b_N(n) -> m_n` for every fixed `n`.  Hence complete source differences produce
a canonical sequence of finite positive-atomic systems converging pointwise to the source.  The
existing finite-KMS realization and closed trace--Hankel cone then imply RH.

## Reverse direction

Lean also proves the converse.  Every reciprocal-square Xi thermal node lies unconditionally in
`(0,1)`.  The finite Xi truncations therefore satisfy

```text
D_N(k,r)
  = sum_(j<N) lambda_j^(k+1) (1-lambda_j)^r >= 0.
```

Under RH these truncations converge pointwise to the normalized prime--Gamma moment tower.
Complementary differences are continuous under pointwise convergence, so all source differences
are nonnegative.  Thus the criterion loses no information relative to RH.

## Lean surface

- `HausdorffBernsteinNonnegative`
- `hausdorffBernsteinAtomicMoment`
- `hausdorffBernstein_factorialMoment`
- `hausdorffBernsteinAtomicMoment_eq_stirling`
- `tendsto_hausdorffBernsteinAtomicMoment`
- `HausdorffMomentDifferencesNonnegative`
- `finitePositiveAtomicLocalMomentClosure_of_hausdorffMomentDifferencesNonnegative`
- `PrimeArchHausdorffMomentDifferencesNonnegative`
- `riemannHypothesis_of_primeArchHausdorffMomentDifferencesNonnegative`
- `xiThermalNode_lt_one`
- `hausdorffMomentDifference_xiThermalTruncation`
- `primeArchHausdorffMomentDifferencesNonnegative_of_riemannHypothesis`
- `primeArchHausdorffMomentDifferencesNonnegative_iff_riemannHypothesis`
- `rectangularPrimePolarSource_negativeAbscissa_le_one_iff_primeArchHausdorffMomentDifferencesNonnegative`

## Proof-burden reduction

The remaining source obligation is the explicit family

```text
D(k,r) >= 0 for every k,r.
```

No Hamiltonian, observable, representing measure, compatibility between cutoffs, or thermodynamic
model remains to be constructed.  Once the linear inequalities are known, the finite systems and
their limit are canonical formulas in the source values.

This does not prove RH: an unconditional proof of all source finite differences is still missing.
Positively stated, proving this complete monotonicity property completes both RH and the critical
prime--polar negative-abscissa bound.

## Verification

- Direct Lean check: passed without warnings.
- Narrow Lake build: passed.
- Umbrella import: added to `formal/GaloisForLFunctions/RHTower.lean`.
- Axiom audit of the generic closure theorem, RH implication, RH equivalence, and abscissa
  equivalence: only `propext`, `Classical.choice`, and `Quot.sound`.
- The source implication and reverse implication use no `sorry`, `admit`, custom `axiom`, `opaque`,
  or `unsafe` declaration.
