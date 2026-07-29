# Finite reciprocal-square laws have terminating Hankel towers

- **ID:** `reciprocal-square-hankel-termination`
- **Stage:** 3-formalized
- **Type:** THEOREM / boundary certificate
- **Register:** `[BRIDGE] [NOT A NOVELTY CLAIM]`
- **Lean:** `GaloisForLFunctions.HTGeometry.ReciprocalSquareHankelTermination`

## Exact theorem

For a finite \(d\times d\) complex matrix \(A\), define

\[
s_k(A)=\operatorname{tr}(A^{k+1}),\qquad k\geq 0.
\]

The first \(d^2+1\) powers of \(A\) are linearly dependent in the \(d^2\)-dimensional complex
matrix space.  Any nonzero relation

\[
\sum_{j=0}^{d^2}c_jA^j=0
\]

annihilates every row of the shifted trace-power Hankel matrix.  Hence

\[
\det[s_{i+j}(A)]_{0\leq i,j\leq d^2}=0. \tag{1}
\]

The bound \(d^2+1\) is deliberately non-sharp.  Cayley--Hamilton gives a sharper degree-\(d\)
recurrence, but `(1)` certifies the only property needed here—finite termination—without
diagonalization or spectral hypotheses.

For a finite rectangular transfer \(D:\mathbb C^n\to\mathbb C^m\), let

\[
Q=D^\dagger D,\qquad G=DD^\dagger,\qquad
m_k(D)=\operatorname{tr}(Q^{k+1}).
\]

The previously formalized reciprocal moment law gives

\[
m_k(D)=\operatorname{tr}(G^{k+1})
\]

for every \(k\).  The same shared sequence therefore has a singular Hankel block at both finite
matrix-space bounds \(n^2+1\) and \(m^2+1\).

## Formal declarations

- `matrixComplexTracePowerMoment`
- `exists_matrixPower_relation`
- `algebraicHankelMatrix_mulVec_matrixPower_relation_eq_zero`
- `det_algebraicHankelMatrix_matrixComplexTracePowerMoment_eq_zero`
- `reciprocalSquareMoment`
- `reciprocalSquareMoment_eq_codomain`
- `det_algebraicHankelMatrix_reciprocalSquareMoment_domain_eq_zero`
- `det_algebraicHankelMatrix_reciprocalSquareMoment_codomain_eq_zero`

## Positive survivor

This closes the finite-moment gap in the obstruction-law program:

```text
finite transfer
  -> shared reciprocal trace moments
  -> finite linear recurrence
  -> terminating Hankel tower.
```

By contrast, the existing infinite-support moment theorem gives strictly positive determinants at
every finite order and excludes every uniformly bounded finite spectral or state-space
realization.  Thus a non-terminating positive source cannot be one finite reciprocal-square event.
It must live in an unbounded event completion, continuum measure, or genuinely infinite operator
algebra.

This is not yet Hypertranscendence.  Infinite support does not imply differential
transcendence, much less hypertranscendence.  The exact missing bridge is a theorem forcing
differential-algebraic finiteness from finite positive ternary closure, or forcing non-finite
positive ternary closure from the source Hypertranscendence certificate.

## Parent theory

Finite trace-power recurrences are standard linear algebra, realization theory, and moment
theory.  The scientific value is boundary placement: it proves that any finite matrix realization
of the proposed reciprocal law is necessarily a truncation.

## Verification

- [x] direct `lake env lean` check
- [x] targeted final module build (`8490/8490`)
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
