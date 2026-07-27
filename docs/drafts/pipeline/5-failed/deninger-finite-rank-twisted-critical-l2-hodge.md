# Finite-rank twisted critical \(L^2\) Hodge quotient

- **ID:** `deninger-finite-rank-twisted-critical-l2-hodge`
- **Stage:** 5-failed
- **Type:** FALSIFIED HILBERT-COMPLETION ROUTE
- **Label:** `DAC_FINITE_RANK_TWISTED_CRITICAL_L2_NO_GO`
- **Parent:** `deninger-poisson-hodge-polarization`
- **Claim tested:** retain nonzero reduced Poisson cohomology by
  tensoring the critical radial \(L^2\) complex with a finite-rank
  positive unitary Kummer/orientation coefficient before taking the
  cokernel.

## Abstract multiplier theorem

Let \(K\) be a nonzero finite-dimensional complex Hilbert space and
let
\[
 A:\mathbb R\longrightarrow\operatorname{End}(K)               \tag{1}
\]
be a measurable matrix function such that
\[
 \det A(t)\ne0
\quad\text{for almost every }t.                                \tag{2}
\]
Let \(M_A\) be its maximal multiplication operator on
\(L^2(\mathbb R,K)\).

`[PROVED HERE] [DAC_FINITE_RANK_TWISTED_CRITICAL_L2_NO_GO]`

The range of \(M_A\) is dense.  Hence
\[
 L^2(\mathbb R,K)/
 \overline{\operatorname{ran}M_A}=0.                            \tag{3}
\]

If \(A(s)\) is a holomorphic matrix family on a neighborhood of the
critical line and \(\det A\) is not identically zero, hypothesis
`(2)` is automatic.  Its failures are discrete and therefore have
Lebesgue measure zero.

### Proof

For any densely defined closed operator,
\[
 \overline{\operatorname{ran}M_A}
 =
 (\ker M_A^*)^\perp.                                           \tag{4}
\]
The adjoint is multiplication by \(A(t)^*\).  Under `(2)`,
\(A(t)^*\) is invertible almost everywhere, so
\[
 A(t)^*g(t)=0\text{ a.e.}\quad\Longrightarrow\quad g=0.
\]
Thus \(\ker M_A^*=0\), and `(4)` proves `(3)`.

For a holomorphic finite matrix, either its determinant is
identically zero or its zero set is discrete.  The latter has measure
zero, proving the final assertion.

## Arithmetic specialization

After the critical Mellin transform, a finite-rank twisted Poisson
operator has the form `(1)` whenever the coefficient power maps give
a finite matrix-valued analytic Dirichlet multiplier.  Therefore:

1. if its determinant is not identically zero, reduced critical
   \(L^2\)-cohomology vanishes by `(3)`;
2. if its determinant is identically zero, a kernel channel exists
   on a positive-measure continuum and does not produce the desired
   discrete Meyer spectrum.

This includes the scalar coefficient as rank one and shows that the
finite-rank real orientation-sign or local quaternionic twist cannot
by itself repair
`DAC_CRITICAL_RADIAL_L2_POISSON_QUOTIENT_NO_GO`.

## Strongest positive survivor

The finite-rank twist remains essential for local parity, cup
orientation, and Hodge star.  What fails is the order of operations:
\[
 \boxed{
 \text{nuclear Poisson cohomology first}
 \;\longrightarrow\;
 \text{source Green/Hodge realization afterward}.}             \tag{5}
\]

A successful positive realization must use at least one of:

1. a Hilbert norm constructed on the already-formed nuclear
   cohomology \(M_\zeta\), not the critical \(L^2\) cokernel;
2. a rigged/resonant Hilbert complex with source boundary conditions;
3. genuinely infinite-rank transverse coefficient data whose
   operator-valued multiplier has a nontrivial singular spectral
   sector without continuum cohomology.

The first option is the exact Deninger Green/polarization gate.  Its
flow naturality and faithfulness cannot be inferred from local
finite-rank positivity.

## No-go closure

- **Killing mechanism:** finite-dimensional analytic multipliers are
  invertible almost everywhere unless identically singular.
- **Positive survivor:** finite-rank \(K_{\mathbb R}\) data still
  supplies local odd Hodge parity and orientation, but Hilbert
  completion must follow nuclear cohomology.
- **New invariant:** the relevant distinction is the singular
  spectral multiplicity of the transverse coefficient, not its local
  positive rank.
- **Lean status:** abstract finite-dimensional multiplication
  statement is not on final RH dependency path; no Lean expansion is
  justified before a concrete source Green operator is constructed.

## Hostile audit

- No pointwise value of \(\zeta\) is computed.
- No assumption about RH or zero simplicity is used.
- The theorem is conditional only on the explicit multiplier
  hypotheses `(1)`--`(2)`, and the holomorphic specialization proves
  those hypotheses whenever the determinant is not identically zero.
- It does not exclude infinite-rank singular coefficients or
  post-cohomology Hodge completion.
- No CCM object or numerical computation occurs.

## Log

- 2026-07-27 — Generalized the scalar dense-range obstruction to
  every finite-rank analytic unitary twist and isolated
  post-cohomology Green/Hodge completion as the positive survivor.
