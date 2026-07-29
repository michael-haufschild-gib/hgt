# Reciprocal squares share one nonzero characteristic polynomial

- **ID:** `reciprocal-square-characteristic-polynomial-law`
- **Stage:** 3-formalized
- **Type:** exact spectral bridge
- **Scientific status:** `[LEAN-PROVED] [BRIDGE] [REDISCOVERED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** Sylvester determinant identity / rectangular \(AB\)--\(BA\) spectral equivalence

## Exact theorem

Let \(R\) be a commutative ring with involution and let

\[
D:R^n\longrightarrow R^m
\]

be represented by an \(m\times n\) matrix.  Define the formal reciprocal squares

\[
Q=D^\dagger D\in M_n(R),\qquad G=DD^\dagger\in M_m(R).
\]

If \(m\leq n\), then

\[
\boxed{
\chi_Q(X)=X^{n-m}\chi_G(X).
}
\tag{1}
\]

If \(n\leq m\), then

\[
\boxed{
\chi_G(X)=X^{m-n}\chi_Q(X).
}
\tag{2}
\]

Consequently \(Q\) and \(G\) have exactly the same nonzero characteristic factor, including
algebraic multiplicity.  Their only possible spectral difference is the number of forced zero
modes.

For \(m\leq n\), coefficient extraction gives

\[
[X^{n-m+k}]\chi_Q=[X^k]\chi_G
\tag{3}
\]

for every \(k\), while

\[
[X^k]\chi_Q=0\qquad (k<n-m).
\tag{4}
\]

## Paper proof

For rectangular matrices \(A\in M_{n,m}(R)\), \(B\in M_{m,n}(R)\) with \(m\leq n\), the
rectangular Sylvester characteristic identity is

\[
\chi_{AB}(X)=X^{n-m}\chi_{BA}(X).
\tag{5}
\]

Apply `(5)` with \(A=D^\dagger\) and \(B=D\) to obtain `(1)`.  Apply it with \(A=D\) and
\(B=D^\dagger\) to obtain `(2)`.  Expanding \(X^r p(X)\) shifts every coefficient of \(p\) upward
by \(r\), proving `(3)` and `(4)`.  No diagonalization, positivity, field hypothesis, or analytic
spectral theorem is used.

Every dependency is closed.  The theorem is standard and stronger than trace-moment conservation
as an algebraic finite-spectrum certificate.

## Physical interpretation boundary

For a complex transfer, \(Q\) and \(G\) are positive semidefinite.  The theorem upgrades

```text
equal rank
  -> equal power traces
  -> one complete nonzero characteristic polynomial.
```

If the coefficients vary in a differential field, their differential-algebraic or
Hypertranscendental complexity is literally shared: the two sides do not merely have correlated
spectra; the invariant functions are the same elements after the forced zero shift.

This does not identify either side with physics.  Supersymmetric quantum mechanics, singular-value
theory, and \(AB\)--\(BA\) spectral equivalence are established parents.  Candidate physics still
requires a source theorem identifying \(Q\) with quantum/gauge response and \(G\) with
causal/gravitational response.

## Lean formalization

Module `GaloisForLFunctions.HTGeometry.ReciprocalSquareCharacteristicPolynomial` proves:

- both dimension-ordered characteristic identities over a generic commutative star ring;
- shifted coefficient equality;
- vanishing of forced low coefficients;
- equal-dimension equality;
- complex reciprocal-square specializations.

The pure algebra module imports `Mathlib` directly.  This keeps the standard
\(AB\)--\(BA\) theorem independent of the heavier event/physics import chain.  Its complex
products are definitionally the same \(D^\dagger D\) and \(DD^\dagger\) used by
`SourceOddPositivitySquareLaw`.

Foreground verification:

```text
lake env lean GaloisForLFunctions/HTGeometry/ReciprocalSquareCharacteristicPolynomial.lean
lake build GaloisForLFunctions.HTGeometry.ReciprocalSquareCharacteristicPolynomial
```

The direct check passed and the targeted build completed `8655/8655`.

A separate `/tmp` audit reports exactly
`[propext, Classical.choice, Quot.sound]` for every declaration and no project axiom.
Repository-wide lint currently exits nonzero because another active worktree migration has many
unreachable new modules in both `RHTower` and `HTGeometry`; this module is imported by the
`HTGeometry` umbrella and is not among the reported failures.

## Gate

- [x] exact statement frozen
- [x] hostile verdict: `BRIDGE / REDISCOVERED`
- [x] dependency-closed paper proof
- [x] exact Lean formalization
- [x] axiom audit
- [ ] repository-wide lint audit after concurrent umbrella migration settles
