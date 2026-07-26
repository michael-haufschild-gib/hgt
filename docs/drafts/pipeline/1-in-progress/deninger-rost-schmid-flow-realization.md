# Deninger Rost--Schmid flow realization

- **ID:** `deninger-rost-schmid-flow-realization`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** `deninger-arithmetic-cohomology-construction`
- **Scope:** direct construction of Deninger's missing arithmetic coefficient complex

## Exact frontier

`[LITERATURE]` Deninger's rational-Witt dynamical system has the prime packets and continuous
flow required by the explicit formula, but he calls it an approximation to the expected
arithmetic space.  If
\[
  \alpha:X_{\mathrm{arith}}\longrightarrow X_W
\]
is the missing comparison, its cohomology would be computed by
\(R\alpha_*\mathscr G\).  He immediately adds that one may instead work
directly on the approximation by constructing the relevant complexes of
sheaves there.  The latter is the active route; \(\alpha\) is optional
geometrization.

`[LITERATURE]` Deninger's 2025 finite-correspondence theorem identifies rational Witt vectors on
normal domains with universally integral finite relative correspondences.  Frobenius and
Verschiebung become pushforward and pullback under power maps.

`[LITERATURE]` Déglise--Feld--Jin construct Rost--Schmid complexes for homological
Milnor--Witt modules over excellent arithmetic bases.  For a regular one-dimensional base their
complex has only generic and closed-point residue degrees, with proper pushforward, lci Gysin
maps, localization, and duality.

`[LITERATURE]` Kolderup--Röndigs--Østvær construct integral Milnor--Witt motivic cohomology over
\(\operatorname{Spec}\mathbb Z\).  Thus the missing object is not Milnor--Witt theory itself; it
is its realization on Deninger's flow space and its archimedean completion.

`[LOCAL-RESEARCH]` The repository has an exact Xi-multiplier cochain complex, determinant,
Lefschetz distribution, divisor Hilbert completion, cup pairing, and source Green transport.
Those results give a faithful target and comparison tests.  They do not construct the missing
coefficient complex: completed Hodge--Frobenius naturality remains equivalent to RH.

## Conjecture

`[CONJECTURE] [DAC_ROST_SCHMID_FLOW_REALIZATION]`

Let
\[
  X_W=\check X_0(\mathbb C)_E\times_{\mathbb Q_{>0}}\mathbb R_{>0}
\]
be Deninger's rational-Witt dynamical approximation for
\(X_0=\operatorname{Spec}\mathbb Z\).  On each cyclotomic character
component of the suspension cover, use the source-defined analytic
Tate-graded coefficient
\[
 \widetilde{\mathscr A}_{F,\mathbb R}^{\mathrm{an}}
 =
 \left(
   \Omega^\bullet_{\mathrm{cyl},F}
   \widehat\otimes\bigoplus_{n\ge0}\mathbb R(n)
 \right)
 \mathop{\otimes}^{\mathbb L}_{\mathscr P_F}
 \underline{\mathcal K}^{M}_{F,\mathbb R}.                          \tag{A0}
\]
`DAC_PRO_STEIN_CYLINDER_ANALYTIC_LEAF` constructs the analytic factor,
`DAC_DENINGER_EQUIVARIANT_TATE_REGULATOR_KUMMER` constructs the
weight-one Kummer map, and the relative motivic cells impose Steinberg
and all higher syzygies.  Rational-Witt data defines the base space and
its power maps.  On
geometric sheaves the nonnegative MW and ordinary channels agree by
`DAC_GEOMETRIC_MW_RANK_COLLAPSE`; retain MW only in twisted residue/Gysin
descent.  Apply compact Galois descent, invert coherent power maps, and
form Deninger's degreewise invariant coefficient sheaf on the coarse
suspension:
\[
 \mathscr A_{\mathrm{flow}}
 :=
 \left(
   \pi_*\operatorname*{hocolim}_{F_n}
   \operatorname{Desc}^{0}_{G}
   \{\widetilde{\mathscr A}_{F,\mathbb R}^{\mathrm{an}}\}_F
 \right)^{\mathbb Q_{>0}}.                                         \tag{A}
\]
Prime packets then enter through the separate Rost--Schmid localization
map of `DAC_COARSE_INVARIANT_SHEAF_ROST_SCHMID_DESCENT`.
Let \(i_\infty:X_\infty\hookrightarrow\overline X_W\) denote the real boundary.  There are
unital real Betti and Deligne coefficient algebras on \(X_\infty\), a common Betti boundary
algebra \(\mathscr B_\infty\), and regulator maps forming the homotopy-pullback gluing
\[
 \mathscr A_{\mathrm{arith}}
 :=
 (\mathscr A_{\mathrm{flow}}\otimes\mathbb R)
 \mathop{\times}^{h}_{i_{\infty,*}\mathscr B_\infty}
 i_{\infty,*}\mathscr D_\infty .                                     \tag{B}
\]
Its reduced regulator fiber agrees with the standard Arakelov-motivic homotopy fiber.  Formula
`(B)`, rather than the nonunital fiber alone, retains the unit and cup product needed by
Deninger's cohomology.  Define
\[
 C^\bullet_{\mathrm{arith}}
 :=R\Gamma(\overline X_W,\mathscr A_{\mathrm{arith}})_{\mathrm{red}}.   \tag{C}
\]
The construction is from rational-Witt correspondences, MW residues, and the real regulator;
it contains no Xi divisor data.  It has the following properties.

1. `DAC_RELATIVE_SULLIVAN_MILNOR_RESOLUTION` gives the algebraic relative
   cells in `(A0)`, while
   `DAC_PRO_STEIN_RELATIVE_CELL_GLOBAL_SECTIONS` proves their chartwise
   analytic global-section comparison.  No character-space realization
   map is required.  `DAC_RELATIVE_MILNOR_CHARACTER_REALIZATION` remains
   an optional theorem identifying `(A0)` with a geometric derived
   pushforward.  No local geometric rank quotient occurs.
   The gluing `(B)` reconciles rank with the real MW-signature boundary and retains the
   Witt duality channel; it is not responsible for imposing the Steinberg relation.
2. The hypercohomology `(C)` has cohomological amplitude \([0,2]\) and admits a closed
   three-term representative
   \[
     L^0\xrightarrow{d^0_F}L^1\xrightarrow{d^1_F}L^2,
     \qquad d^1_Fd^0_F=0.
   \]
   These degrees are the derived sheaf/leafwise degrees of \(\mathscr A_{\mathrm{arith}}\).
   Deninger's current rational-Witt partition is not assumed to be a smooth
   two-dimensional foliation, and transverse flow is not used as a cohomological
   differential.  Concretely,
   `DAC_ARITHMETIC_ROST_SCHMID_SIGNATURE_RESOLUTION` supplies two
   Rost--Schmid derived-section columns of amplitude \([0,1]\) and one real
   orientation in degree \(2\).  No two-term stalkwise amplitude is assumed;
   `DAC_TWO_COLUMN_HYPERCOHOMOLOGY_AMPLITUDE` then proves this bound.
3. The suspension action gives a strongly continuous flow
   \(\phi^t\) on `(C)`.  On its smooth vectors its infinitesimal generator
   \(\Theta=\left.\frac d{dt}\right|_{t=0}\phi^t\) is a closed cochain endomorphism
   \(\Theta^q:L^q\to L^q\) satisfying
   \[
     \Theta^1d^0_F=d^0_F\Theta^0,\qquad
     \Theta^2d^1_F=d^1_F\Theta^1.
   \]
   Thus \(\Theta\) descends to dynamical cohomology.
4. The unit in `(B)` and Deninger's connectedness theorem induce
   \[
     H^0_{\mathrm{arith}}\simeq\mathbb R(0),\qquad \Theta_0=0.
   \]
   Perfect weight-one endpoint duality then forces
   \(H^2_{\mathrm{arith}}\simeq\mathbb R(-1)\) and \(\Theta_2=1\) by
   `DAC_ENDPOINT_PURITY`.  Reduced \(H^1_{\mathrm{arith}}\) is infinite-dimensional.
5. For every integer \(n\), the four-term mapping fiber of
   \(\Theta-n\) on \(L^\bullet\) is canonically quasi-isomorphic to the
   Milnor--Witt-refined Weil--Arakelov complex, compatibly with cup-\(\theta\), products, and
   duality.
6. The \(E_\infty\) product in `(B)`, Rost--Schmid residue adjunction, and the arithmetic trace
   satisfy `DAC_THREE_TERM_CUP_DESCENT`; their exact middle radical is the boundary subspace,
   so they induce perfect weight-one Poincaré duality on cohomology.
7. The real-place boundary supplies a positive odd Hodge operator on reduced \(H^1\), and the
   centered flow is Hodge-natural before comparison with Xi.
8. The flow trace is the full prime-power plus Gamma Lefschetz distribution, and its
   regularized alternating determinant is the completed Riemann zeta function.
9. The resulting comparison to the repository's Xi-multiplier target is defined on source
   correspondences, is dense and cup-isometric, and is proved before evaluating any Xi zero.

Properties 1--5 give the source architecture and the independently known Weil--Arakelov
specializations.  Properties 6--9 make it the arithmetic cohomology requested by
`docs/Deninger program.md`; existing target theorems then derive RH from property 7.

## Why this representation

The arithmetic coefficient system is resolved by Rost--Schmid residues and real-regulator
gluing.  Derived sheaf cohomology supplies the cohomological degrees; Deninger's suspension flow
supplies a commuting endomorphism.  This separates structures that cannot be conflated:

\[
  (\check X_F(\mathbb C),\Omega^\bullet_{\mathrm{cyl},F})
    \longrightarrow
  \text{analytic Tate--Milnor leafwise coefficient}
    \xrightarrow{\text{twisted residues/Gysin}}
  \text{Rost--Schmid descent coefficient}
    \xrightarrow{\text{real/Deligne gluing}}
  \mathscr A_{\mathrm{arith}}
    \xrightarrow{R\Gamma}
  (L^\bullet,\Theta)
    \xrightarrow{\operatorname{Fib}(\Theta-n)}
  \text{Weil--Arakelov specialization}.
\]

## Hostile attack

- Raw Milnor--Witt cohomology of \(\operatorname{Spec}\mathbb Z\) is finitely generated in the
  relevant one-dimensional range.  It cannot itself be the infinite spectral \(H^1\).
  Noncompact leafwise flow completion is essential.
- Raw arithmetic MW degree zero is too large: rank-zero signature classes survive.  They
  are absent on algebraically closed geometric stalks, so a stalkwise rank quotient is
  redundant.  Rank and signature must instead be matched by the archimedean pullback `(B)`;
  its connected unit must be proved to give exactly one copy of \(\mathbb R\).
- Full realified arithmetic MW theory is also too large in positive degree:
  Déglise--Feld--Jin compute a real-place \(\mathbb Z^r\) in every MW weight
  \(q>1\).  The boundary gluing must therefore use the multiplicative
  arithmetic-curve signature window, retaining only the degree-two
  orientation in this cohomology theory.
- Ordinary rational-Witt correspondences retain the Kucharczyk--Scholze Steinberg defect.
  Full \(\mathbb A^1\)-localization is not a repair: scaling contracts the entire reduced
  rational-Witt coordinate.  Derived base change to the full motivic symbol algebra repairs
  Steinberg and its higher syzygies without localizing that coordinate.
- A bare chartwise cochain algebra is not a sheaf.
  `DAC_PRO_STEIN_CYLINDER_ANALYTIC_LEAF` supplies the missing analytic
  pro-sheaf, but comparison with the coarse suspension remains required.
- A relative Sullivan resolution is not a space over \(X_F\), and ordinary
  realization is literature-falsified.  This blocks only optional
  geometrization of `(A0)`, not the direct analytic sheaf construction.
- A pure Milnor symbol coefficient is spectrally insufficient.
  `DAC_PURE_SUSPENSION_SCALAR_SPECTRUM_NO_GO` proves that scalar
  rational-power action extends to a scalar continuous flow.  The
  cylinder-analytic chain factor in `(A0)` is mandatory and must survive
  coarse descent and completion.
- Chartwise amplitude is not stalkwise amplitude.
  `DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION` computes an unavoidable
  \(\Lambda^2V_F\) Tor class in the naïve pushout stalk.  Property 2 must
  therefore come from the arithmetic derived-section localization theorem,
  not a two-term homotopy-sheaf assertion.
- Milnor--Witt transfer forms are indefinite over \(\mathbb R\).  They supply orientation and
  Poincaré duality, not positive Hodge theory.  Positivity must come from the archimedean
  boundary realization.
- A determinant declared equal to \(\widehat\zeta\), or a comparison declared faithful, can
  encode the desired divisor.  Both must be derived from finite correspondences and the
  prime--Gamma trace before divisor evaluation.
- A positive Hodge form on a target indexed by Xi zeros is not source construction.  Flow
  naturality on the source total complex must be proved first.

**Verdict:** `SURVIVES THIRD HOSTILE AUDIT`.  The local analytic
Tate--Milnor sheaf and its pro-Stein global-section comparison are
paper-proved.  Diagonal coarse suspension/prime localization, arithmetic
localization, duality, trace, and positivity remain open.

## First naturality audit

`[LITERATURE] [DAC_RS_FROBENIUS_CHAIN_MAP]` Déglise--Feld--Jin, Proposition 1.4.6(1),
proves for every proper morphism \(f:X\to Y\) that
\[
  d_Y f_*=f_*d_X
\]
on Rost--Schmid cycle complexes.  The power map
\(\pi_n:\mathbb A^1_{\mathbb Z}\to\mathbb A^1_{\mathbb Z}\),
\(x\mapsto x^n\), is finite and therefore proper.  Hence its pushforward \(F_n=\pi_{n*}\)
is a chain map.  Their Proposition 1.4.1(1) gives functoriality, so
\[
  F_mF_n=F_{mn}.
\]
The Frobenius half of residue naturality is therefore established by existing theory.

`[LITERATURE] [DAC_RS_GYSIN_COHERENCE]` Déglise--Feld--Jin's 2026
*Homotopy coherent Gysin functoriality* completes that deferred higher-coherence problem.  For
every weak Borel--Moore theory on smooth \(S\)-schemes it constructs a strict simplicial
contravariant Gysin functor, and its Rost--Schmid corollary applies to MW-homodules over
noetherian excellent bases.  Since \(\mathbb A^1_{\mathbb Z}\) is smooth and every
\(\pi_n:x\mapsto x^n\) is a morphism over \(\mathbb Z\), the maps
\[
  V_n=\pi_n^*
\]
exist in the derived Rost--Schmid theory and satisfy all composition coherences.  Thus the
Verschiebung coherence gap is literature-closed as well.

`[LITERATURE] [DAC_MW_ORDINARY_RANK_BRIDGE]` Kolderup--Röndigs--Østvær define integral
Milnor--Witt motivic cohomology over every scheme essentially smooth over a Dedekind scheme by
the homotopy pullback
\[
  \widetilde{\mathsf M\mathbb Z}
  =
  \mathsf M\mathbb Z
  \mathop{\times}^{h}_{\mathsf M\mathbb Z/2}
  \mathsf W\mathbb Z.
\]
Its first projection is the canonical map from Milnor--Witt motivic cohomology to ordinary
motivic cohomology.  On degree-zero quadratic coefficients this projection is the rank map
\(\mathrm{GW}\to\mathbb Z\), hence
\[
  n_\epsilon=\sum_{j<n}\epsilon^j\longmapsto n.
\]
Thus the finite-place scalar relation is already canonical; it is not supplied by the
archimedean realization.  The unresolved issue is to retain the quadratic/Witt channel needed
for duality while descending the ordinary channel to Deninger's rational-Witt site.

## Open core

`[OPEN CORE]` Construct and compare the remaining arrows in `(A)`--`(C)`:
comparison of the pro-Stein analytic sheaf with Deninger's coarse
suspension as a degreewise invariant sheaf, integral/profinite and
arithmetic-operation enhancement, coarse-sheaf/Rost--Schmid descent,
power-map localization, unital rank/signature
Betti--Deligne boundary gluing, the multiplicative arithmetic-curve signature
window, the two-level derived localization theorem, and the closed real regulator
realization.  Then prove exact cup radicals, Hodge positivity, and the source
Lefschetz/determinant theorem.  The resulting \([0,2]\) bound is already a
formal consequence of `DAC_TWO_COLUMN_HYPERCOHOMOLOGY_AMPLITUDE`.
Frobenius, coherent Verschiebung, \(n_\epsilon\mapsto n\), and abstract
three-term/duality descent are closed inputs, not open constructions.
Coherent Baumslag/Milnor character realization is optional geometrization,
not part of this open core.

The algebraic residue--flow totalization theorem is separated into
`deninger-residue-flow-totalization`; it does not solve this open core.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*:
  https://arxiv.org/abs/1807.06400
- Christopher Deninger, *Rational Witt vectors and associated sheaves*:
  https://arxiv.org/abs/2508.05329
- Frédéric Déglise, Niels Feld, Fangzhou Jin,
  *Homological Milnor-Witt modules and Chow-Witt groups over general bases*:
  https://arxiv.org/abs/2512.09876
- Frédéric Déglise, Niels Feld, Fangzhou Jin,
  *Homotopy coherent Gysin functoriality*:
  https://arxiv.org/abs/2605.01855
- Håkon Kolderup, Oliver Röndigs, Paul Arne Østvær,
  *Hermitian K-theory and Milnor-Witt motivic cohomology over Z*:
  https://arxiv.org/abs/2509.16404
- Andreas Holmström, Jakob Scholbach, *Arakelov motivic cohomology I*:
  https://arxiv.org/abs/1012.2523

## Log

- 2026-07-26 — Created after direct scope correction.  CCM is not a dependency.  Exact active
  object is Deninger's missing derived coefficient complex, represented as a
  Milnor--Witt/Rost--Schmid residue complex totalized with leafwise flow.
- 2026-07-26 — Primary-source audit proved the Frobenius pushforward half of residue
  naturality from proper functoriality of Rost--Schmid complexes.  The literature boundary is
  exact: chain-level smoothable-lci Gysin/Verschiebung coherence is not yet constructed there.
- 2026-07-26 — Updated against Déglise--Feld--Jin 2026: their strict simplicial Gysin functor
  for Rost--Schmid complexes closes the higher-coherent Verschiebung gap.  Open core moves to
  comparison with the rational-Witt correspondence site and archimedean realization.
- 2026-07-26 — Corrected the finite-place bridge using Kolderup--Röndigs--Østvær's integral
  homotopy-pullback definition of \(\widetilde{\mathsf M\mathbb Z}\).  Its canonical ordinary
  projection is rank on quadratic degree, so \(n_\epsilon\mapsto n\) is already algebraic.
  Remaining problem is simultaneous descent of the ordinary channel and preservation of the
  Witt/duality channel, followed by leafwise and archimedean constructions.
- 2026-07-26 — made the relative Milnor character map
  \(\alpha_F:X_F^M\to X_F\) primary.  Its relative Sullivan algebra is
  paper-proved; pro-space realization, finite-cover invariance, integral
  enhancement, and comparison of \(R\alpha_{F,*}\mathbb R\) with the
  unit-amalgamated leafwise sheaf remain exact local gates.
- 2026-07-26 — ordinary Sullivan realization was retired after the
  rank-two free \(\mathbb Q\)-completion \(H_2\) obstruction.  Baumslag
  free-rational packets now give the paper-closed finite topological
  model; basis-independent coherence, twisted Eilenberg--Moore,
  pro-descent, and integral enhancement remain open.
