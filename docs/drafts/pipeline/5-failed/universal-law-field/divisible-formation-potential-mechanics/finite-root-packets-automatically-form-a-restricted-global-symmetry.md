# Failed conjecture: finite root packets automatically form a restricted global symmetry

- **Status:** [FAILED] [EXACT COUNTERTHEOREM] [POSITIVE SURVIVOR EXTRACTED]
- **Parent:** ULF-DFPM-4

## Conjecture

Because every depth-
\(n\) Kummer inertia packet is finite-dimensional, unitary, and recurrent, their complete root-depth
tower should automatically define a compact perturbation of the identity.  If true, the divisor
selection theorem would become an RH proof immediately.

## Failure

For integer charge \(q\), the canonical global operator is

\[
 U_q=\bigoplus_{n\ge2}L_{n,q}
\]

on \(\bigoplus_{n\ge2}\ell^2(\mathbb Z/n\mathbb Z)\).  If \(q\ne0\), infinitely many depth blocks
contain a \((-1)\)-eigenvector for \(L_{n,q}\).  These eigenvectors form an orthonormal, hence
weakly-null, sequence on which \(U_q-I\) has norm \(2\).  Every compact correction tends to zero on
that sequence.  Therefore

\[
 \|\pi(U_q)-1\|=2,
\]

and \(U_q-I\) is not compact, not Schatten, and not determinant class.

Finite-dimensional regularity at every stage is therefore compatible with maximal global
noncompactness.  Neither recurrence nor root-stack existence supplies restricted formation.

## Positive survivor

The failure is coefficient-faithful rather than destructive:

\[
 q\longmapsto\pi(U_q)
\]

is an injective group homomorphism into the Calkin unitary group, with pairwise essential distance
\(2\).  Hence the missing RH input is no longer an adjustable weighted bound.  It is the exact
source-admission statement that the literal complete inertia symmetry belongs to the compactly
restricted global formation group.

No Lean was written or built in this research pass.
