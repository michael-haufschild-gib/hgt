# Failed: identifying the arithmetic coefficient with the rational-Witt structure sheaf

- **ID:** `deninger-rational-witt-structure-sheaf-as-coefficient`
- **Stage:** 5-failed
- **Type:** NO-GO WITH POSITIVE SURVIVOR
- **Parent:** `deninger-arithmetic-cohomology-construction`
- **Retired claim:** The missing coefficient \(R\alpha_*\mathscr G\) should have
  \(\pi_0=W_{\mathrm{rat}}\).

## No-go

Deninger's construction uses \(W_{\mathrm{rat}}(\mathcal O_X)\) as the structure sheaf whose
complex-valued points form the rational-Witt approximation.  In the same introduction he
separately states that, if
\[
 \alpha:X_{\mathrm{arith}}\longrightarrow W_{\mathrm{rat}}(X)(\mathbb C)
\]
exists, the missing arithmetic cohomology must be computed on the approximation with a
relevant complex of sheaves \(R\alpha_*\mathscr G\).  He does not identify the degree-zero
coefficient sheaf with \(W_{\mathrm{rat}}\).

The proposed identification has the wrong cohomological output.  For the
Kucharczyk--Scholze character component \(X_F\), the desired corrected space satisfies
\[
 H^i(X_F^M,\mathbb Z)\cong K_i^M(F)_{\mathrm{tf}}.
\]
Consequently
\[
 H^0(X_F^M,\mathbb Z)=\mathbb Z,\qquad
 H^1(X_F^M,\mathbb Z)=F^\times_{\mathrm{tf}},
\]
not \(W_{\mathrm{rat}}(F)\).  Deninger's global connectedness theorem likewise gives
one-dimensional zeroth foliation cohomology.  Thus imposing
\(\pi_0R\alpha_*\mathscr G=W_{\mathrm{rat}}\) confuses coordinate functions on the
approximation with coefficients used to compute its corrected cohomology.

This is decisive: a derived quotient whose main theorem is
\(\pi_0\simeq W_{\mathrm{rat}}\) does not yet address Deninger's cohomological defect, even if
the quotient is algebraically valid.

## Strongest positive survivor

`[POSITIVE SURVIVOR] [DAC_UNIT_AMALGAMATED_MW_COCHAIN_COEFFICIENT]`

Keep \(W_{\mathrm{rat}}\) as geometry and use its finite-correspondence description to
construct Frobenius/Verschiebung and residue functoriality.  Construct the coefficient on the
associated character spaces:

1. \(C_F=C^*(X_F,\mathbb Z)\), the integral \(E_\infty\) cochain algebra of the
   rational-Witt character component;
2. \(P_F=\operatorname{Free}_{E_\infty}^{+}(\Sigma H(F^\times_{\mathrm{tf}}))\), the
   universal degree-one unit algebra;
3. \(\mathcal K_F^M\) and \(\mathcal K_F^{MW}\), the diagonal ordinary and
   Milnor--Witt motivic symbol algebras;
4. derived unit-amalgamations
   \[
     C_F^M=C_F\otimes_{P_F}^{\mathbb L}\mathcal K_F^M,\qquad
     C_F^{MW}=C_F\otimes_{P_F}^{\mathbb L}\mathcal K_F^{MW};
   \]
5. the relative rank-connected quotient of \(C_F^{MW}\to C_F^M\), which removes the
   degree-zero Grothendieck--Witt kernel while retaining positive MW duality data.

This selectively imposes the full Milnor--Witt symbol relations, beginning with Steinberg,
without applying \(\mathbb A^1\)-localization to Deninger's rational-Witt coordinate.
Galois, finite-topology, residue, and power descent then produce the sheaf complex on the
rational-Witt flow space.

## New exact insight

The two roles are:
\[
 \boxed{
 W_{\mathrm{rat}}\ \text{constructs the space and its power maps};
 \qquad
 R\alpha_*\mathscr G\ \text{corrects cohomology on that space}.}
\]
They may interact through finite correspondences and Gysin maps, but their degree-zero
objects must not be identified.

## Status of survivor

Paper construction and falsifiers are recorded on
`deninger-derived-mw-rational-witt-coefficient`.  Generic positive-cell and rank-quotient
algebra remains valid.  Required new source theorem is the low-degree and full Milnor
comparison for the unit-amalgamated cochains, followed by equivariant descent.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*, introduction, pp. 3--4:
  https://arxiv.org/abs/1807.06400
- Robert A. Kucharczyk and Peter Scholze,
  *Topological realisations of absolute Galois groups*, Question 1.10:
  https://people.mpim-bonn.mpg.de/scholze/GaloisTop.pdf

## Log

- 2026-07-26 — retired after separating rational-Witt geometry from the missing derived
  coefficient complex; unit-amalgamated Milnor--Witt cochains extracted as positive survivor.
