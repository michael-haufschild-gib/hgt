# Unit-amalgamated Milnor--Witt coefficient on Deninger's rational-Witt space

- **ID:** `deninger-derived-mw-rational-witt-coefficient`
- **Stage:** 1-in-progress
- **Type:** CONJECTURAL SOURCE CONSTRUCTION
- **Labels:** `DAC_UNIT_AMALGAMATED_MW_COCHAIN_COEFFICIENT`,
  `DAC_DERIVED_MW_RATIONAL_WITT_COEFFICIENT`
- **Parent:** `deninger-rost-schmid-flow-realization`
- **Target:** Deninger's missing derived coefficient complex on the
  rational-Witt approximation; optional geometric realization as
  \(R\alpha_*\mathscr G\)

## Correction of roles

Deninger's rational-Witt sheaf constructs the approximation
\[
 W_{\mathrm{rat}}(X)(\mathbb C).
\]
It is geometry, not the degree-zero arithmetic coefficient.  The missing
\(R\alpha_*\mathscr G\) is a complex of sheaves **on** that space.  On a
Kucharczyk--Scholze character component \(X_F\), the corrected integral cohomology is
required to satisfy
\[
 H^q(X_F^M,\mathbb Z)\cong K_q^M(F)_{\mathrm{tf}},
\]
so in particular \(H^0=\mathbb Z\), not \(W_{\mathrm{rat}}(F)\).  The contrary
identification is retired in
`deninger-rational-witt-structure-sheaf-as-coefficient`.

Rational-Witt finite correspondences remain indispensable: they construct the space,
Frobenius/Verschiebung, finite descent, and prime packets.  They no longer serve as the
claimed \(H^0\) coefficient.

## Arithmetic grading

We write arithmetic degree \(q\) as \(\pi_q=H^q\).  Let
\(\Sigma_{\mathrm{ar}}^q\) denote suspension in this arithmetic grading.  All connectivity,
cell-attachment, and truncation statements below use this convention.

## Primary local coefficient sheaf

Deninger's primary paper gives two routes.  If a true Milnor character
space and a map
\[
 \alpha_F:X_F^M\longrightarrow X_F                                  \tag{0}
\]
exist, then \(R\alpha_{F,*}\mathbb R\) is the desired coefficient.
However, Deninger immediately states that working on the rational-Witt
approximation instead requires finding the relevant **complexes of
sheaves on that approximation**.  Thus `(0)` is a geometric enhancement,
not a prerequisite for defining arithmetic cohomology.

The active primary coefficient consequently starts with Deninger's
equivariant Tate-graded algebra on the suspension cover:
\[
 \widetilde{\mathscr A}^M_{F,\mathrm{geom}}
 =
 \left(
   \Omega^\bullet_{\mathrm{cyl},F}
   \widehat\otimes\bigoplus_{n\ge0}\mathbb R(n)
 \right)
 \mathop{\otimes}^{\mathbb L}_{\mathscr P_F}
 \underline{\mathcal K}^M_{F,\mathbb R}.                             \tag{0a}
\]
Its existence and universal property are paper-proved in
`DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`.  The critical local
Kummer map and its weight-one twist are source-proved in
`DAC_DENINGER_EQUIVARIANT_TATE_REGULATOR_KUMMER`; they are not assumptions.
The chartwise derived-global-section comparison is closed on the
pro-Stein refinement.  The critical global gate is diagonal arithmetic
localization, which combines non-proper suspension descent with prime
residues instead of exactifying invariants.  A later equivariant lift
\[
 R\widetilde\alpha_{F,*}\mathbb R
 \simeq\widetilde{\mathscr A}^M_{F,\mathrm{geom}}                    \tag{0b}
\]
would geometrize the same coefficient but is not needed to proceed.

`DAC_PRO_STEIN_CYLINDER_ANALYTIC_LEAF` constructs the analytic factor in
`(0a)`, and `DAC_PRO_STEIN_RELATIVE_CELL_GLOBAL_SECTIONS` proves the
chartwise relative-cell/global-section comparison on that refinement.
`DAC_PURE_SUSPENSION_SCALAR_SPECTRUM_NO_GO` proves that deleting this
factor and retaining only the pure Milnor symbol algebra cannot produce
the nontrivial zeta spectrum.

`DAC_RELATIVE_SULLIVAN_MILNOR_RESOLUTION` proves the algebraic input.  For
algebraic cyclotomic \(F/\mathbb Q\), with
\[
 V_F=(F^\times/\mu_\infty)\otimes\mathbb R,
\]
there is a relative Sullivan factorization
\[
 \Lambda(V_F)\longrightarrow Q_F\xrightarrow{\sim}\mathbb R\oplus V_F,
\]
whose first degree-one relative generators transgress to degree-two
products and whose later generators kill all resulting syzygies.  Thus a
contravariant realization of \(Q_F\) would have exactly the required real
Milnor cohomology.  Ordinary Sullivan realization is nevertheless
literature-falsified, already at rank two.  The active topological
replacement is `DAC_BAUMSLAG_MILNOR_PRO_REALIZATION`:
`DAC_BAUMSLAG_FREE_RATIONAL_MILNOR_PACKET` supplies each basis-chosen
finite unit packet with square-zero rational cohomology and divisible
fiber, and `DAC_TWO_TERM_CDGA_FORMALITY` compares its isolated cochains to
the Milnor model.  Basis-independent coherence, fiberwise
Eilenberg--Moore comparison, pro-descent, integral refinement, and
arithmetic operations remain the precise realization gates inside
`DAC_RELATIVE_MILNOR_CHARACTER_REALIZATION`.

The topological realization work therefore moves off the critical path.
It remains a meaningful optional strengthening of `(0a)`, and all
Sullivan/finite-cover no-go results remain valid constraints on that
strengthening.

## Algebraic comparison model on a character component

Let \(F\supset\mathbb Q(\mu_\infty)\) be a field occurring on the cyclotomic cover
of Deninger's rational-Witt space.  Put
\[
 V_F:=F^\times/\mu_\infty.
\]
This is the torsion-free degree-one group used by Kucharczyk--Scholze.  Let
\[
 \mathcal C_F:=C^*_{\mathrm{sh}}(X_F,\mathbb Z)
\]
be the integral shape/Čech \(E_\infty\) cochain algebra of their character component, written
in arithmetic grading.  This inverse-limit model is natural for the generally
non-locally-contractible character group.  The universal character gives the Kummer map
\[
 \kappa_F:V_F\longrightarrow \pi_1\mathcal C_F.
\]
Set
\[
 \mathcal P_F
 :=
 \operatorname{Free}_{E_\infty}^{+}
   \bigl(\Sigma_{\mathrm{ar}}^1H V_F\bigr).                             \tag{1}
\]
The Kummer map induces \(\mathcal P_F\to\mathcal C_F\).

Let \(\mathcal K_F^M\) and \(\mathcal K_F^{MW}\) denote the connective diagonal symbol
algebras extracted respectively from ordinary and Milnor--Witt motivic cohomology, with
\[
 \pi_q\mathcal K_F^M=K_q^M(F)_{\mathrm{tf}},\qquad
 \pi_q\mathcal K_F^{MW}=K_q^{MW}(F)_{\mathrm{tf}}                      \tag{2}
\]
in the diagonal range.  Their degree-one symbol maps induce
\[
 \mathcal P_F\longrightarrow\mathcal K_F^M,\qquad
 \mathcal P_F\longrightarrow\mathcal K_F^{MW}.
\]
The forgetful/rank transformation of motivic ring spectra gives
\[
 \mathrm{rk}:\mathcal K_F^{MW}\longrightarrow\mathcal K_F^M.           \tag{3}
\]

Define the two unit-amalgamated cochain algebras
\[
 \mathcal C_F^M
 :=
 \mathcal C_F
 \mathop{\otimes}^{\mathbb L}_{\mathcal P_F}
 \mathcal K_F^M,                                                       \tag{4}
\]
\[
 \mathcal C_F^{MW}
 :=
 \mathcal C_F
 \mathop{\otimes}^{\mathbb L}_{\mathcal P_F}
 \mathcal K_F^{MW}.                                                    \tag{5}
\]
Base change of `(3)` gives
\[
 r_F:\mathcal C_F^{MW}\longrightarrow\mathcal C_F^M.                  \tag{6}
\]

Formulae `(4)`--`(5)` are the concrete meaning of the selective multiplicative
bar--residue envelope.  They modify the products generated by degree-one arithmetic units;
they do not impose \(\mathbb A^1\)-invariance on Deninger's rational-Witt coordinate.
They are chartwise derived-global-section models, not coefficient sheaves or
stalks.  The genuine sheaf construction is
`DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`: it performs the same
pushout inside Tate-graded equivariant commutative algebra objects on
Deninger's suspension cover.  Identifying its derived global sections
with `(4)`--`(5)`
is the separate conjecture
`DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON`.

## Geometric rank collapse and placement of quadratic data

`DAC_GEOMETRIC_MW_RANK_COLLAPSE` proves that for algebraically closed
character fields, the forgetful map
\[
 K_q^{MW}(F)\xrightarrow{\sim}K_q^M(F)\qquad(q\geq0)                   \tag{7}
\]
is already an integral isomorphism.  Hence \(r_F\) is an equivalence there and a
local derived rank quotient would do nothing.

More generally every cyclotomic \(F\) contains \(\sqrt{-1}\), hence is nonreal.  Its Witt
ring is torsion.  The Milnor--Witt fundamental square therefore implies
\[
 K_q^{MW}(F)\otimes\mathbb R
 \xrightarrow{\sim}
 K_q^M(F)\otimes\mathbb R
 \qquad(q\geq0).                                                       \tag{8}
\]
Consequently the chartwise derived-section comparison object is
\[
 \mathcal A_{F,\mathbb R}^{\mathrm{geom}}
 :=
 \mathcal C_F^M\otimes\mathbb R
 \simeq
 \mathcal C_F^{MW}\otimes\mathbb R.                                   \tag{9}
\]
For Deninger's algebraic \(F/\mathbb Q\),
`DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE` further proves
\[
 \pi_q\mathcal A_{F,\mathbb R}^{\mathrm{geom}}=0\qquad(q\geq2).
\]
Thus the chartwise real geometric **derived-section comparison algebra**
has canonical amplitude \([0,1]\).  This says neither that `(0)` has
two-term stalks nor that its global arithmetic descent already has
amplitude \([0,2]\).

The quadratic contribution cannot be stored as an extra nonnegative summand in a
geometric stalk.  It must enter through twisted MW residue/Gysin maps before
realification and through the real-signature term in archimedean descent.  The generic
derived rank-quotient theorem remains valid, but it is no longer an active local gate.

## Why this selectively imposes Steinberg

In \(\mathcal C_F\), Kucharczyk--Scholze prove that the degree-one Kummer classes generate
an exterior cohomology algebra and that
\[
 \kappa_F(a)\smile\kappa_F(1-a)\neq0
\]
in general.  In each motivic symbol algebra,
\[
 [a]\,[1-a]=0.                                                        \tag{10}
\]
The pushouts `(4)`--`(5)` identify Kummer classes with motivic symbols.  Therefore the image
of every class in `(10)` is coherently null in the unit-amalgamated cochains.

Choose a relative cellular \(E_\infty\) presentation of
\(\mathcal P_F\to\mathcal K_F^{MW}\).  Its first relation layer consists of
arithmetic degree-two Steinberg cells; subsequent positive cells encode all relations among
relations and the remaining Milnor--Witt symbol laws.  Thus the earlier one-step
\(S_{\mathrm{St}}\)-attachment is only the degree-two skeleton of `(5)`, not the complete
coefficient.

Since every relation cell is in positive arithmetic degree,
`DAC_POSITIVE_CELL_PI0_INVARIANCE` explains why the Steinberg correction itself preserves
degree zero.  Equations `(7)`--`(9)` show that no further quotient is present on a
geometric real stalk.

## Global descent

Let
\[
 j:X_{\mathrm{cyc}}\longrightarrow W_{\mathrm{rat}}(X)(\mathbb C)_E
\]
be the cyclotomic/Galois character cover implicit in Deninger's construction.
The local equivariant derived coefficient sheaves
\(\widetilde{\mathscr A}^M_{F,\mathrm{geom}}\) from `(0a)` are required to form a
homotopy-coherent Galois diagram.
`DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON` identifies their derived
sections with `(9)`.  `DAC_RELATIVE_MILNOR_CHARACTER_REALIZATION` would
add the optional pushforward interpretation `(0b)`.
Define
\[
 \mathscr A_{\mathrm{cyc},\mathbb R}
 :=
 \operatorname{Desc}^{0}_{G}
 \{\widetilde{\mathscr A}_{F,\mathbb R}^{\mathrm{geom}}\}_F,          \tag{10}
\]
where the right side is compact Galois descent before rational-power
localization.  It is enhanced by:

1. finite-topology descent from Deninger's finite-correspondence presentation;
2. Rost--Schmid MW residue and Gysin maps at arithmetic specializations;
3. coherent Frobenius/Verschiebung maps induced by \(t\mapsto t^n\);
4. the condition \(E\) selecting Deninger's connected subsystem.

Let \(\mathscr A_{\infty,\mathbb R}^{\mathrm{sig}}\) be the real Betti/MW-signature
complex on the real fixed locus, and let
\(\mathscr A_{\mathbb C,\mathbb R}\) be the common complexified comparison object.
Déglise--Feld--Jin's arithmetic computation shows that the full realified MW
signature tower has a real-place survivor in every weight \(q>1\).  It cannot
be inserted untruncated into Deninger's three-degree theory.  The arithmetic
coefficient is therefore the multiplicative arithmetic-curve Postnikov
window of the homotopy pullback
\[
 \mathscr A_{\mathrm{ar},\mathbb R}
 :=
 \tau_{\le2}^{\mathrm{arith}}\!\left(
   \mathscr A_{\mathrm{cyc},\mathbb R}
   \mathop{\times}^{h}_{\mathscr A_{\mathbb C,\mathbb R}}
   \mathscr A_{\infty,\mathbb R}^{\mathrm{sig}}
 \right).                                                             \tag{11}
\]
Here \(\tau_{\le2}^{\mathrm{arith}}\) retains the connected rank unit, the
degree-one character coefficient, and one real orientation
\(i_{\infty,*}\mathbb R(-1)[-2]\), while killing higher signature weights.
It must be constructed as a power-, residue-, and product-compatible
Postnikov quotient; it is not a truncation chosen from the zeta divisor.
Formula `(11)`, rather than a stalkwise rank quotient, is where rank and
signature must be reconciled while retaining \(H^0=\mathbb R\).

After inverting the coherent Frobenius monoid, form Deninger's coefficient
sheaf on the coarse suspension degreewise:
\[
 \mathscr A_{\mathrm{flow}}
 :=
 \left(
   \pi_*\operatorname*{hocolim}_{F_n}
   \widetilde{\mathscr A}_{\mathrm{ar},\mathbb R}
 \right)^{\mathbb Q_{>0}}.                                         \tag{12}
\]
The superscript in `(12)` is taken before derived global sections, exactly
as in Deninger's Definition 10.1.  The separate finite-place
Rost--Schmid resolution and its regulator edge are
`DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`.  Formula `(12)` does
not identify the whole spectral cohomology with invariants of already
computed local Milnor cohomology.
Archimedean gluing is not used to impose Steinberg; it supplies the real-signature boundary
absent from cyclotomic geometric stalks.

## Main conjecture

`[CONJECTURE] [DAC_UNIT_AMALGAMATED_MW_COCHAIN_COEFFICIENT]`

Constructions `(1)`--`(12)` exist functorially and satisfy:

1. **Derived sheaf coefficient.**  The equivariant cover sheaf `(0a)` is functorial under
   restriction, Galois maps, finite correspondences, and powers.  It has
   the chartwise derived-section comparison in clause 2 and the diagonal
   descent/residue enhancement in clauses 3--5.
   Optionally,
   `DAC_RELATIVE_MILNOR_CHARACTER_REALIZATION` supplies `(0)` and `(0b)`;
   no later clause depends on that optional geometrization.

2. **Milnor comparison.**
   \[
   \pi_q\mathcal C_F^M
   \xrightarrow{\sim}
   K_q^M(F)_{\mathrm{tf}}
   \quad(q\geq0).                                                       \tag{13}
   \]
   In degrees \(0,1\), `(13)` is compatible with the known
   Kucharczyk--Scholze isomorphisms.  Equation `(13)` is the spectral
   \(E_\infty\)-algebra form of their Question 1.10.  Its real cyclotomic-character case is
   proved by `DAC_CHARACTER_SHAPE_FORMALITY` and
   `DAC_REAL_FREE_UNIT_EQUIVALENCE`; its two-term amplitude for algebraic
   \(F/\mathbb Q\) is proved by `DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE`.
   Applying these chartwise theorems to the sheaf coefficient requires
   `DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON`; it is not automatic.

3. **MW refinement without wrong geometric stalks.**  The equivalences `(7)`--`(9)`
   hold.  Twisted MW residues and transfers construct the comparison maps entering `(11)`,
   and the arithmetic-curve signature window satisfies
   \[
   H^0(\mathscr A_{\mathrm{ar},\mathbb R})=\mathbb R,                  \tag{14}
   \]
   has \(\mathcal H^2=i_{\infty,*}\mathbb R(-1)\), and has no higher
   signature sheaves.  The retained real signature term supplies determinant
   orientation and pairing data required for Poincaré duality.

4. **Power equivariance.**  Frobenius and Verschiebung preserve the full relative cell
   presentation, not merely the degree-two Steinberg ideal, and descend through `(11)`.
   They satisfy
   \[
   F_mF_n=F_{mn},\qquad V_mV_n=V_{mn}                                  \tag{15}
   \]
   with projection formula and coherent ramified Gysin composition.

5. **Arithmetic descent.**  Derived Galois descent `(10)` and arithmetic pullback `(11)`
   are compatible with finite
   correspondences and Rost--Schmid residues.  It introduces no extra degree-zero
   components and retains the prime packets.

6. **Flow coefficient.**  The chartwise geometric derived-section algebra
   has proved amplitude \([0,1]\).  Its sheafified Kummer pushout is not
   assumed two-term on stalks:
   `DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION` proves a
   \(\Lambda^2V_F\) stalk-Tor class.  Instead,
   `DAC_ARITHMETIC_ROST_SCHMID_SIGNATURE_RESOLUTION` constructs a two-level
   arithmetic localization model whose generic and prime-packet
   derived-section columns have amplitude \([0,1]\), plus one real
   orientation in degree two.  `DAC_TWO_COLUMN_HYPERCOHOMOLOGY_AMPLITUDE`
   then gives global amplitude \([0,2]\), \(H^0=\mathbb R\), and an
   infinite-dimensional reduced \(H^1\).

7. **Multiplicative duality.**  Product, MW residue adjunction, and arithmetic trace descend
   to a degree-two cup pairing whose radical is exactly the boundary subspace.

## Step-by-step proof program

1. Use Deninger's equivariant Tate algebra
   \(\bigoplus_{n\ge0}\mathbb R(n)\) and
   `DAC_DENINGER_EQUIVARIANT_TATE_REGULATOR_KUMMER`; perform the bigraded
   derived \(E_\infty\) pushout of
   `DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`.
2. Construct the diagonal \(E_\infty\) symbol algebras in `(2)` from the
   ordinary and Milnor--Witt motivic ring spectra; prove their sheaf symbol
   maps and the global-section comparison `(4)`--`(6)`.
3. Prove the derived-global-section part of
   `DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON`.  Then use
   `DAC_CHARACTER_SHAPE_FORMALITY` to close `(13)` after realification on every
   cyclotomic character component, and
   `DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE` to reduce it to degrees \(0,1\).
   Compute the integral relative bar spectral sequence of `(4)`,
   first in degrees \(0,1,2\), then inductively through the relative cell filtration.
4. Use `DAC_GEOMETRIC_MW_RANK_COLLAPSE` and the torsion theorem for Witt rings of
   nonreal fields to prove `(7)`--`(9)`; no local rank-quotient bar calculation remains.
5. Prove operation-stability of every relative cell and descend \(F_n,V_n\);
   form Deninger's degreewise invariant coarse sheaf and construct
   `DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`, including its
   regulator edge.
6. Glue generic charts to closed arithmetic points by coherent twisted Rost--Schmid residues and
   finite Gysin maps.
7. Construct the real Betti/MW-signature comparison and prove arithmetic pullback `(11)`.
8. Construct the multiplicative arithmetic-curve Postnikov window in `(11)`;
   verify that it retains exactly the degree-two real orientation and commutes
   with residues and power maps.
9. Prove the two-level arithmetic derived-section localization conjecture
   `DAC_ARITHMETIC_ROST_SCHMID_SIGNATURE_RESOLUTION`.
10. Perform Galois descent, Frobenius localization, and suspension `(12)`;
    compute the three-term global complex.
11. Optional geometric strengthening: construct the coherent Baumslag
    realization and prove `(0b)`.

## Hostile audit and falsifiers

- The Kummer map and its Tate twist are source-proved.  Failure can occur
  in extending its Milnor cells or in diagonal localization descent, not
  in existence of the degree-one input.
- For the optional geometrization, a Sullivan algebra is only a rational algebraic model, and its ordinary
  realization is false here: rank-two free-group \(\mathbb Q\)-completion
  already has unwanted \(H_2\).  The Baumslag replacement avoids that
  obstruction at a basis-chosen finite stage, but without coherent
  assembly, twisted pullback cochains, pro-cover descent, and an
  integral/profinite enhancement it still does not construct `(0)`.
- If derived global sections do not commute with the sheaf-level relative
  cell presentation, the chartwise algebra `(4)` is not the cohomology of the
  proposed coefficient sheaf.
- If chartwise two-term amplitude is used as a stalkwise assertion, the
  construction contradicts `DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION`.
- If `(4)` changes \(\pi_0\) or \(\pi_1\), it fails the already known
  Kucharczyk--Scholze comparison.
- Killing only the visible Steinberg classes is insufficient if higher syzygy cells are
  omitted.  Formula `(5)` uses the full motivic symbol algebra.
- Full \(\mathbb A^1\)-localization of the rational-Witt coordinate is forbidden: target
  scaling contracts that coordinate to the zero section.  Only the relation algebra in
  `(2)` is motivic.
- If the real-signature comparison in `(11)` duplicates the rank constant or loses the
  determinant orientation, `(14)` fails; the comparison morphism, not a geometric stalk,
  must be corrected.
- If `(11)` retains the full real MW signature tower, Déglise--Feld--Jin's
  \(\mathbb Z^r\) survivors in every weight \(q>1\) force nonzero
  cohomology above degree two.
- A determinant-line orientation gives MW Gysin data, not positivity.  Positive Hodge theory
  must come from the archimedean regulator after `(12)`.
- Neither `(13)` nor `(14)` supplies the zeta spectrum, Lefschetz distribution, determinant,
  or RH.  Those remain later source theorems.

**Verdict:** `SURVIVES TENTH CORRECTION`.  Rational-Witt data constructs the
base space.  Deninger's own formulation permits the relevant derived
complex of sheaves on that approximation, so the paper-proved
unit-amalgamated motivic symbol sheaf is the primary coefficient.
The relative Milnor character map \(\alpha_F\) and Baumslag assembly are
retained as an optional geometric realization, not a blocking premise.
Geometric MW coefficients collapse to
ordinary Milnor coefficients in the nonnegative range, while quadratic
information belongs to twisted residue and archimedean signature descent.
Real chartwise ordinary comparison and two-term derived-section amplitude
are proved; stalkwise two-term amplitude is false.  Exact open core starts
with the derived-section, restriction, and operation clauses of
`DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON`, then the coherent
Rost--Schmid/Galois/signature pullback `(11)`, its
multiplicative arithmetic-curve signature window and the two-level derived
localization comparison of
`DAC_ARITHMETIC_ROST_SCHMID_SIGNATURE_RESOLUTION`, and compatibility with
power operations.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*:
  https://arxiv.org/abs/1807.06400
- Robert A. Kucharczyk and Peter Scholze,
  *Topological realisations of absolute Galois groups*, Question 1.10:
  https://people.mpim-bonn.mpg.de/scholze/GaloisTop.pdf
- Frédéric Déglise and Jean Fasel,
  *The Milnor-Witt motivic ring spectrum and its associated theories*:
  https://arxiv.org/abs/1708.06102
- Tom Bachmann, Baptiste Calmès, Frédéric Déglise, Jean Fasel, Paul Arne Østvær,
  *Milnor-Witt motives*:
  https://arxiv.org/abs/2004.06634
- Håkon Kolderup, Oliver Röndigs, Paul Arne Østvær,
  *Hermitian K-theory and Milnor-Witt motivic cohomology over Z*:
  https://arxiv.org/abs/2509.16404
- Frédéric Déglise, Niels Feld, Fangzhou Jin,
  *Homotopy coherent Gysin functoriality*:
  https://arxiv.org/abs/2605.01855
- Frédéric Déglise, Niels Feld, Fangzhou Jin,
  *Homological Milnor-Witt modules and Chow-Witt groups over general bases*,
  Theorem 4.4.20:
  https://arxiv.org/abs/2512.09876
- Jacob Lurie, *Higher Algebra*:
  https://www.math.ias.edu/~lurie/papers/HA.pdf

## Log

- 2026-07-26 — replaced the false identification
  \(\pi_0R\alpha_*\mathscr G=W_{\mathrm{rat}}\) by the unit-amalgamated cochain
  construction `(4)`--`(7)`; initially isolated a local rank-Tor gate, superseded below.
- 2026-07-26 — `DAC_GEOMETRIC_MW_RANK_COLLAPSE` eliminated the local rank quotient:
  algebraically closed stalks have \(K_{\geq0}^{MW}=K_{\geq0}^M\), and cyclotomic stalks
  agree after realification.  Relocated quadratic data to twisted residues and
  archimedean rank/signature pullback `(11)`.
- 2026-07-26 — made
  `DAC_RELATIVE_MILNOR_CHARACTER_REALIZATION` the primary local geometric
  gate.  `DAC_RELATIVE_SULLIVAN_MILNOR_RESOLUTION` supplies its proved
  algebraic model; the leafwise unit-amalgamated sheaf is now explicitly a
  candidate comparison for \(R\alpha_{F,*}\mathbb R\).
- 2026-07-26 — ordinary Sullivan realization was falsified both for the
  infinite unit space and at finite rank two.  Replaced it by
  `DAC_BAUMSLAG_MILNOR_PRO_REALIZATION`.  Its basis-chosen finite packet,
  square-zero rational cohomology, CDGA formality, divisible kernel, and
  stagewise finite-cover invariance are paper-closed.
- 2026-07-26 — primary-source correction: Deninger, introduction
  pp. 4--5, explicitly permits replacing the unknown true space by relevant
  complexes of sheaves on the rational-Witt approximation.  Promoted the
  leafwise unit-amalgamated derived sheaf to primary coefficient; moved
  \(\alpha_F\)/Baumslag realization to optional geometrization.
