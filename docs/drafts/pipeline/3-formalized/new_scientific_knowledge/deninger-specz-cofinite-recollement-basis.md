# Spec Z cofinite recollement basis

- **ID:** `deninger-specz-cofinite-recollement-basis`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) · LEAN 4 THEOREM
- **Label:** `DAC_SPECZ_COFINITE_RECOLLEMENT_BASIS`
- **Parent:** `deninger-arithmetic-projection-leray-rost-schmid-resolution`
- **Statement:** the actual Zariski space of
  \(\operatorname{Spec}\mathbb Z\) is the cofinite generic-prime star,
  and its arithmetic opens form the finite-boundary recollement basis
  needed for Deninger's source localization.
- **Lean module:**
  `GaloisForLFunctions.RHTower.Deninger.DeningerSpecZCofiniteRecollement`

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

## Formalized statement

All declarations live in the `RHTower` namespace and work with mathlib's
`PrimeSpectrum ℤ`.  `deningerSpecZGeneric` is \(\eta=(0)\) and
`deningerSpecZClosed p hp` is the closed point \((p)\).

`(1)` Points:

- `deningerSpecZ_eq_generic_or_closed` : every point is `deningerSpecZGeneric`
  or `deningerSpecZClosed p hp` for a rational prime `p`;
- `deningerSpecZClosed_ne_generic` : the two families are disjoint.

`(2)` Opens:

- `deningerSpecZGeneric_mem_of_isOpen` : every nonempty open contains \(\eta\);
- `deningerSpecZ_isClosed_singleton` : every non-generic point is closed;
- `deningerSpecZ_finite_mem_asIdeal` : for \(N\ne0\) the primes containing `N`
  form a finite set;
- `deningerSpecZ_isClosed_of_finite` : a finite set of non-generic points is
  closed;
- `deningerSpecZ_isOpen_iff` : `IsOpen U ↔ U = ∅ ∨ (η ∈ U ∧ Uᶜ finite)`;
- `deningerSpecZ_isOpen_iff_star` : a nonempty `U` is open exactly when it is the
  complement of a finite set of closed points, which is `(2)` verbatim.

`(3)`, `(4)` Principal arithmetic opens:

- `deningerSpecZ_isTopologicalBasis` : the `D(N)` form a basis;
- `deningerSpecZ_basicOpen_eq_range_localization` :
  \(D(N)=\operatorname{Spec}\mathbb Z[1/N]\), as the range of the map of spectra
  induced by the localization away from `N`;
- `deningerSpecZ_compl_basicOpen_eq_primes` :
  \(S\setminus D(N)=\{(p):p\mid N\}\) for \(N\ne0\);
- `deningerSpecZ_basicOpen_inter` and `deningerSpecZ_basicOpen_inter_eq_lcm` :
  \(D(M)\cap D(N)=D(MN)=D(\operatorname{lcm}(M,N))\).

`(5)`, `(6)` Finite recollement data:

- `deningerSpecZ_isClosedEmbedding_of_finite` : \(i_P\) is a closed embedding;
- `deningerSpecZ_isOpenEmbedding_compl` : \(j_P\) is an open embedding;
- `deningerSpecZ_range_compl` : their ranges are complementary;
- `deningerSpecZ_discreteTopology`, `deningerSpecZ_isClopen_singleton`,
  `deningerSpecZ_finite_star` : \(P\) is a finite discrete subspace, i.e. it is
  the coproduct of its points, which is `(6)`.

### What is formalized and what is quoted

`(1)`--`(6)` are formalized outright: no hypothesis beyond finiteness of `P`,
`η ∉ P`, and `N ≠ 0` where stated.

`(7)` and `(8)` are not proved here and were not proved on the card either: the
card obtains them by quoting the standard localization triangle for derived
sheaves on an open--closed decomposition, and the standard decomposition of local
cohomology with support in a disjoint union.  What those two quoted facts consume
is exactly the topological input `(5)`--`(6)`, which is now formalized: the
closed/open embedding pair with complementary ranges, and the discreteness of the
finite prime star.

## Verification

- Direct command:
  `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerSpecZCofiniteRecollement.lean`
- Result: passed with no errors and no warnings.
- Scratch `#print axioms` on all 24 declarations: only the Lean/mathlib standard
  `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- Imported by the `GaloisForLFunctions.RHTower` umbrella.

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
- The Lean development is topology and commutative algebra only: it does not
  construct any derived sheaf, and `(7)`--`(8)` remain quoted.

## Gates

- [x] 0 → 1 in-progress: exact source topology isolated
- [x] 1 → 2 fully-proven: classification of opens and finite
  recollements complete
- [x] 2 → 3 formalized: prime-open basis and finite-support
  decomposition encoded in Lean
  (`GaloisForLFunctions.RHTower.Deninger.DeningerSpecZCofiniteRecollement`)
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
- 2026-08-01 — formalized `(1)`--`(6)` unconditionally in Lean 4.
