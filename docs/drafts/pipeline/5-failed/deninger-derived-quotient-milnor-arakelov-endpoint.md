# Derived quotient equals the Milnor--Arakelov endpoint

- **ID:** `deninger-derived-quotient-milnor-arakelov-endpoint`
- **Stage:** 5-failed
- **Type:** RETIRED CONJECTURE / OUT-OF-SCOPE ROUTE
- **Label:** `DAC_DERIVED_QUOTIENT_MILNOR_ARAKELOV_ENDPOINT`
- **Parent:** `deninger-canonical-coarse-derived-middle-fiber`
- **Statement:** the proposed computation of derived quotient descent
  as the algebraic endpoint is not Deninger's source construction and
  is retired from the arithmetic-cohomology dependency graph.

## Retraction

Deninger's Definition 10.1 first forms the degreewise invariant sheaf
\[
 (\pi_*\widetilde{\mathscr A})^{\mathbb Q_{>0}}
\]
on the coarse quotient and only then takes derived global sections.
The quotient-stack object studied below inserts derived
\(\mathbb Q_{>0}\)-invariants, whose higher bar/Koszul directions are
absent from that definition.  Even a successful endpoint computation
would therefore compute an auxiliary object rather than construct
Deninger's arithmetic cohomology.

The finite contraction proposed in A also lacks a source proof that
relative Milnor cells cancel the independent group-cohomology
direction.  The already-proved bar skeleton shows those directions
exist, while the source definition says not to introduce them.
Accordingly this route is retired rather than promoted as the open
core.

**Strongest positive survivor:** the finite residue endpoint page
`DAC_FINITE_PRIME_MILNOR_ENDPOINT_PAGE` remains valid as the target
of arithmetic-curve Rost--Schmid localization.  It now feeds
`DAC_ARITHMETIC_PROJECTION_LERAY_ROST_SCHMID_RESOLUTION`, where primes
are codimension-one residues and not group-cohomology generators.

## Source objects

Let
\[
 G=\mathbb Q_{>0}\cong\bigoplus_p\mathbb Z
\]
act on Deninger's suspension cover \(\widetilde X\), and let
\[
 c:[\widetilde X/G]\longrightarrow X=\widetilde X/G
\]
be the quotient-stack to coarse-quotient map.  On the cover use the
already constructed equivariant Tate--Milnor sheaf
\[
 \widetilde{\mathscr A}^{M}_{\mathrm{geom}}
 =
 \mathscr T_{\widetilde X}
 \mathop{\otimes}^{\mathbb L}_{\mathscr P}
 \underline{\mathcal K}^{M}_{\mathbb R}.                           \tag{1}
\]
Adjoin the generic/finite Rost--Schmid localization map and the single
real signature orientation to obtain
\(\widetilde{\mathscr A}_{\mathrm{arith}}\).

There are two different source complexes:
\[
 C_{\mathrm{coarse}}
 =
 R\Gamma\!\left(
   X,c_*\widetilde{\mathscr A}_{\mathrm{arith}}\right),             \tag{2}
\]
\[
 C_{\mathrm{der}}
 =
 R\Gamma\!\left(
   X,Rc_*\widetilde{\mathscr A}_{\mathrm{arith}}\right)
 \simeq
 R\Gamma\!\left(
   [\widetilde X/G],
   \widetilde{\mathscr A}_{\mathrm{arith}}\right).                 \tag{3}
\]
Equation `(2)` is Deninger's degreewise invariant sheaf followed by
ordinary derived global sections.  Equation `(3)` is derived
transformation-groupoid descent.  They must not be identified.

## Main conjecture

`[CONJECTURE] [DAC_DERIVED_QUOTIENT_MILNOR_ARAKELOV_ENDPOINT]`

There is a flow- and correspondence-equivariant quasi-isomorphism
\[
 C_{\mathrm{der}}
 \simeq
 C_{\mathrm{end}}(\mathbb Q)
 =
 \mathbb R[0]\oplus
 \left[
  (\mathbb Q^\times/\{\pm1\})\otimes\mathbb R
  \xrightarrow{\operatorname{pr}}
  \operatorname{Div}_{\mathrm{Ar}}(\mathbb Q)_{\mathbb R}
 \right]_{[1,2]}.                                                   \tag{4}
\]
Under `(4)`, the canonical map
\[
 C_{\mathrm{coarse}}\longrightarrow C_{\mathrm{der}}               \tag{5}
\]
is the connected-rank map in degree zero and the arithmetic
degree/trace map in degree two.

Consequently
\[
 H^0(C_{\mathrm{der}})=\mathbb R,\qquad
 H^1(C_{\mathrm{der}})=0,\qquad
 H^2(C_{\mathrm{der}})=\mathbb R(-1).                              \tag{6}
\]
If `DAC_ARITHMETIC_ROST_SCHMID_SIGNATURE_RESOLUTION` supplies
amplitude \([0,2]\) for `(2)`, then
`DAC_CANONICAL_COARSE_DERIVED_MIDDLE_FIBER` gives
\[
 \operatorname{Fib}((5))
 \simeq H^1(C_{\mathrm{coarse}})[-1].                              \tag{7}
\]

## Conjecturing decomposition

The main conjecture is intentionally split into three falsifiable
claims.

### A. Finite-power Steinberg--bar contraction

`[CONJECTURE] [DAC_FINITE_POWER_STEINBERG_BAR_CONTRACTION]`

For a finite set of primes \(S\), let
\[
 G_S=\langle p:p\in S\rangle\cong\mathbb Z^S.
\]
On every finite compact-Stein character stage, totalize:

1. the normalized \(G_S\)-bar/Koszul resolution;
2. the finite relative Milnor cell presentation of `(1)`;
3. the residues \(\operatorname{ord}_p\), \(p\in S\).

There is a multiplicative deformation retraction of this totalization
onto
\[
 \mathbb R[0]\oplus
 \left[
   V_S\xrightarrow{(\operatorname{ord}_p)_{p\in S}}
   \mathbb R^S
 \right]_{[1,2]},                                                   \tag{8}
\]
where \(V_S\) is the real span of the \(S\)-units.  The contraction is
natural under adjoining a prime and under Frobenius/Verschiebung.

This is the exact place where the Steinberg relative cells must cancel
the higher exterior/Koszul classes of the free abelian power group.
Deleting those cells leaves cohomology through degree \(|S|\) and
falsifies `(8)`.

### B. Restricted-product continuity

`[CONJECTURE] [DAC_RESTRICTED_PRODUCT_ENDPOINT_CONTINUITY]`

The contractions in `(8)` are strict for the nuclear analytic factor
and the mixed \(L^1/L^2\) Kummer topology.  They pass through the
filtered system of finite prime sets and through the restricted
product completion:
\[
 \varinjlim_S V_S
 \xrightarrow{\sim}
 \bigoplus_p\mathbb R[p].                                         \tag{9}
\]
No \(\varprojlim^1\), nonclosed range, or completed-product class
survives in \(H^1\) of the derived quotient term.

The last sentence is essential.  Algebraic exactness of `(9)` alone
does not imply exactness after topological completion.

### C. Real signature endpoint gluing

`[CONJECTURE] [DAC_REAL_SIGNATURE_ENDPOINT_GLUE]`

The real Betti/Milnor--Witt boundary glues to `(9)` by the product
formula and produces the exact sequence
\[
 0\longrightarrow
 (\mathbb Q^\times/\{\pm1\})\otimes\mathbb R
 \longrightarrow
 \operatorname{Div}_{\mathrm{Ar}}(\mathbb Q)_{\mathbb R}
 \xrightarrow{\deg}
 \mathbb R(-1)
 \longrightarrow0.                                                \tag{10}
\]
All higher real signature weights map to an acyclic summand of the
derived quotient totalization.  Thus exactly one orientation line,
not the full real Milnor--Witt tower, survives.

Claims A--C imply `(4)` by finite-stage descent, filtered passage, and
real gluing.

## Evidence already proved

1. `DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE` constructs `(1)`
   as a genuine equivariant sheaf.
2. `DAC_PRO_STEIN_RELATIVE_CELL_GLOBAL_SECTIONS` proves the
   relative-cell/global-section comparison on finite pro-Stein stages.
3. `DAC_CHARACTER_SHAPE_FORMALITY` identifies raw character cochains
   with the exterior unit algebra.
4. `DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE` proves that real Milnor
   symbols for algebraic extensions of \(\mathbb Q\) have no degrees
   above one.
5. `DAC_REAL_ARAKELOV_DIVISOR_ENDPOINT` proves `(10)`.
6. Clausen--Scholze prove compact-Stein pseudocoherent derived descent
   and flat restriction for compact Stein inclusions.  This supports
   the finite analytic stages, not the nonproper coarse quotient.

## Why a new comparison theorem is necessary

Deninger proves that the relevant rational-power action is not
properly discontinuous.  He also exhibits an irreducible coarse
quotient whose leaf topology is strictly finer.  Therefore ordinary
compact-Stein descent cannot be applied directly to \(X\).

Moreover,
\[
 H^\bullet(G,\mathbb R)
 \cong
 \Lambda^\bullet\operatorname{Hom}(G,\mathbb R)
\]
is unbounded because \(G\) has countably infinite rank.  The endpoint
claim can only follow from a source-defined cancellation between:

- power-group bar directions;
- all Steinberg and higher relative Milnor cells;
- finite residue localization;
- the real signature boundary.

It cannot follow from base dimension one, a Postnikov declaration, or
exact invariants.

## Proof program

1. Write the normalized bar/Koszul complex for every \(G_S\) in the
   condensed nuclear module category.
2. Choose the functorial finite relative Milnor cell filtration already
   used in the pro-Stein comparison.
3. Filter the combined complex by bar degree plus relative-cell degree.
4. Identify the first spectral-sequence page with the exterior unit
   algebra modulo the full Milnor cell differential.
5. Construct a filtration-preserving contraction onto `(8)` and prove
   compatibility when \(S\subset S'\).
6. Add finite residues and prove the residue/power square before
   completion.
7. Prove strictness and closed range in the mixed topology; pass to all
   primes without a derived-limit error.
8. Glue the real signature boundary and prove `(10)` as the only
   surviving endpoint.
9. Identify the induced maps in degrees zero and two with Deninger's
   connected unit and arithmetic trace.

## Hostile audit and falsifiers

- A contraction depending on an ordering of primes must be proved
  independent of that ordering.
- A finite-stage quasi-isomorphism without uniform strictness does not
  imply the completed statement.
- Any surviving \(H^1\) in `(3)` means the canonical fiber captures
  only a kernel, not all of Deninger's \(H^1\).
- Any surviving \(H^q\), \(q>2\), disproves the arithmetic endpoint
  model.
- The stalk Tor class
  \(\Lambda^2V\) is not allowed to be discarded.  It must cancel in
  derived quotient localization; it need not vanish stalkwise.
- Full quotient-stack cohomology with the raw coefficient is
  unbounded.  The theorem concerns the corrected arithmetic
  totalization only.
- Exact coarse/derived comparison would make `(7)` zero and is ruled
  out by the scalar-spectrum no-go.
- No \(\xi\)-zero, CCM model, RH premise, or numerical computation may
  define the contraction or its topology.

## Literature and novelty status

Deninger defines `(2)` for his raw leafwise sheaf, proves the connected
degree-zero result, and explicitly notes nonproperness.  Kucharczyk--
Scholze compute the raw exterior cohomology and expose the Steinberg
defect.  Clausen--Scholze provide the finite compact-Stein descent
technology.  None of these sources proves the combined contraction
A, its strict infinite-prime passage B, or the endpoint comparison
`(4)`.

**Verdict:** `RETIRED FROM SOURCE THEORY; FINITE RESIDUE ENDPOINT
SURVIVES INSIDE THE COARSE-SHEAF LERAY--ROST--SCHMID ROUTE`.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  especially Definition 10.1, Theorem 10.2, Proposition 10.3, and
  §12: https://arxiv.org/abs/1807.06400
- Robert A. Kucharczyk and Peter Scholze,
  *Topological realisations of absolute Galois groups*:
  https://arxiv.org/abs/1609.04717
- Dustin Clausen and Peter Scholze,
  *Condensed Mathematics and Complex Geometry*, Theorems 9.15, 10.1,
  and 10.5: https://arxiv.org/abs/2605.11731
- Jacob Lurie, *Higher Algebra*:
  https://www.math.ias.edu/~lurie/papers/HA.pdf

## Log

- 2026-07-27 — Extracted the canonical endpoint conjecture from the
  coarse-to-derived comparison and split it into finite contraction,
  strict restricted-product passage, and real signature gluing.
- 2026-07-27 — Retired after source audit: derived quotient descent is
  not Deninger's degreewise invariant-sheaf construction.  The finite
  residue endpoint page survives as arithmetic-curve localization.
