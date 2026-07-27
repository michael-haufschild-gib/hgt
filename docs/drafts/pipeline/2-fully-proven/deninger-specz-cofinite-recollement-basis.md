# Spec Z cofinite recollement basis

- **ID:** `deninger-specz-cofinite-recollement-basis`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Label:** `DAC_SPECZ_COFINITE_RECOLLEMENT_BASIS`
- **Parent:** `deninger-arithmetic-projection-leray-rost-schmid-resolution`
- **Statement:** the actual Zariski space of
  \(\operatorname{Spec}\mathbb Z\) is the cofinite generic-prime star,
  and its arithmetic opens form the finite-boundary recollement basis
  needed for Deninger's source localization.

## Theorem

Let
\[
 S=\operatorname{Spec}\mathbb Z,\qquad
 \eta=(0),\qquad
 S^{(1)}=\{(p):p\text{ prime}\}.
\]
Then:

1. As a set,
   \[
   |S|=\{\eta\}\amalg S^{(1)}.                                   \tag{1}
   \]
2. Every nonempty open contains \(\eta\).  Every proper closed subset
   is a finite set of closed prime points.  Hence the nonempty opens
   are exactly
   \[
   \{\eta\}\cup
   \bigl(S^{(1)}\setminus P\bigr),
   \qquad P\subset S^{(1)}\text{ finite}.                         \tag{2}
   \]
3. The principal arithmetic opens
   \[
   U_N=D(N)=\operatorname{Spec}\mathbb Z[1/N],
   \qquad N\ne0,                                                  \tag{3}
   \]
   form a basis, and
   \[
   S\setminus U_N=\{(p):p\mid N\},\qquad
   U_M\cap U_N=U_{\operatorname{lcm}(|M|,|N|)}.                   \tag{4}
   \]
4. For every finite \(P\subset S^{(1)}\), the decomposition
   \[
   i_P:P\hookrightarrow S,\qquad
   j_P:S\setminus P\hookrightarrow S                             \tag{5}
   \]
   is an open--closed recollement, and
   \[
   P=\coprod_{p\in P}\{(p)\}.                                    \tag{6}
   \]
   Thus for any derived sheaf coefficient \(\mathscr F\) on \(S\),
   the standard localization triangle has finite boundary term
   \[
   R\Gamma_P(S,\mathscr F)
   \longrightarrow R\Gamma(S,\mathscr F)
   \longrightarrow R\Gamma(S\setminus P,j_P^*\mathscr F)
   \xrightarrow{+1},                                             \tag{7}
   \]
   with
   \[
   R\Gamma_P(S,\mathscr F)
   \simeq
   \bigoplus_{p\in P}R\Gamma_{\{p\}}(S,\mathscr F).               \tag{8}
   \]

Equations `(2)`--`(8)` are the source-native prime-star organization:
no auxiliary topological space, quotient stack, or finite
constructible stratification is required.

## Proof

Prime ideals of \(\mathbb Z\) are \((0)\) and \((p)\), proving `(1)`.
Every nonempty open of an irreducible scheme contains its generic
point.  A proper closed subset is \(V(I)\) for a nonzero ideal
\(I=(N)\); its points are exactly the finitely many prime ideals
\((p)\) with \(p\mid N\).  Conversely any finite prime set is
\(V(\prod_{p\in P}p)\).  This proves `(2)`--`(4)`.

A finite union of closed points is closed, so `(5)` is the standard
closed/open decomposition.  Distinct prime points are disjoint,
giving `(6)`.  Derived sheaves on any open--closed decomposition have
the localization triangle `(7)`.  Local cohomology with support in a
finite disjoint union is the finite direct sum of the individual
support functors, proving `(8)`.

## Deninger consequence

By `DAC_DENINGER_COFINITE_OPEN_BASE_CHANGE`,
\[
 a^{-1}(S\setminus P)
\]
is the actual Deninger suspension constructed from the arithmetic
open \(S\setminus P\), and the restricted coefficient is the actual
underived invariant coefficient.  Pulling `(5)` back along \(a\)
therefore gives finite recollements of Deninger's source space.

The filtered system over finite \(P\) exhausts every arithmetic
neighborhood of the generic fibre.  To obtain the infinite
generic-to-prime Cousin row, one must still prove that the analytic
localization triangles pass to this filtered system with the required
strict direct-sum topology.  That is
`DAC_COFINITE_PRO_RECOLLEMENT_ANALYTIC_COMPARISON`.

## Hostile audit

- The infinite set of all closed primes is not closed in \(S\); only
  finite \(P\) enters a recollement.
- Finite recollements do not by themselves justify passage to an
  infinite direct sum or completion.
- Exodromy for one finite constructible stratification does not cover
  the filtered infinite-prime system.
- Base topology determines the horizontal prime direction, not the
  internal analytic amplitude of \(\mathscr F\).
- No chartwise cochain object is treated as a sheaf.

## Gates

- [x] 0 → 1 in-progress: exact source topology isolated
- [x] 1 → 2 fully-proven: classification of opens and finite
  recollements complete
- [ ] 2 → 3 formalized: prime-open basis and finite-support
  decomposition remain to be encoded in Lean
- [ ] 3 → 4 publication-ready: integrate with pro-recollement
  analytic comparison

## References

- Stacks Project, spectra of rings and standard opens:
  https://stacks.math.columbia.edu/tag/00DY
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  Lemmas 7.1--7.3:
  https://arxiv.org/abs/1807.06400

## Log

- 2026-07-27 — replaced an auxiliary prime-star analytic-space
  conjecture by the exact cofinite-star topology and finite
  recollements of \(\operatorname{Spec}\mathbb Z\).
