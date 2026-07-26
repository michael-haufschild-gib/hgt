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
is the missing comparison, he states that the cohomological problem on the approximation is to
construct the relevant derived coefficient complex \(R\alpha_*\mathscr G\).

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
  U:\widetilde{\operatorname{Corr}}_{\mathbb Z}
      \longrightarrow \operatorname{Corr}_{\mathbb Z}
\]
forget the quadratic orientation of a finite Milnor--Witt correspondence.  On the
finite-correspondence site presenting Deninger's rational-Witt object, let
\[
  \mathscr A_{\mathrm{MW}} :=
    R U_*\widetilde{\mathrm M}\mathbb Z_{\mathbb Z}.
\]
There is an archimedean boundary extension
\(\mathscr A_{\mathrm{arith}}\) of \(\mathscr A_{\mathrm{MW}}\), constructed from the real
place and not from the Xi divisor, with the following properties.

1. Its coefficient resolution uses the arithmetic Rost--Schmid complex and its
   Deligne-regulator mapping fiber.  This resolution repairs the Steinberg defect and retains
   the Witt duality channel.
2. Its reduced leafwise complex on Deninger's flow space is genuinely three-term,
   \[
     L^0\xrightarrow{d^0_F}L^1\xrightarrow{d^1_F}L^2,
     \qquad d^1_Fd^0_F=0.
   \]
   The three cohomological degrees come from two-dimensional leafwise cohomology, not by using
   transverse flow as a differential.
3. Framed power correspondences induce a transverse flow generator
   \(\Theta^q:L^q\to L^q\) satisfying
   \[
     \Theta^1d^0_F=d^0_F\Theta^0,\qquad
     \Theta^2d^1_F=d^1_F\Theta^1.
   \]
   Thus \(\Theta\) descends to dynamical cohomology.
4. Compact-support leafwise hypercohomology of \(L^\bullet\) has
   \[
     H^0_{\mathrm{arith}}\simeq\mathbb C,\qquad
     H^2_{\mathrm{arith}}\simeq\mathbb C(-1),
   \]
   and its reduced middle cohomology is infinite-dimensional.
5. For every integer \(n\), the four-term mapping fiber of
   \(\Theta-n\) on \(L^\bullet\) is canonically quasi-isomorphic to the
   Milnor--Witt-refined Weil--Arakelov complex, compatibly with cup-\(\theta\), products, and
   duality.
6. The Milnor--Witt product and arithmetic duality induce cup product and Poincaré duality on
   \(L^\bullet\).
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

The arithmetic coefficient system is resolved by Rost--Schmid residues, while Deninger's
two-dimensional leaves supply the cohomological degrees and his transverse flow supplies a
commuting endomorphism.  This separates three structures that cannot be conflated:

\[
  \text{quadratic finite correspondences}
    \xrightarrow{R U_*}
  \text{Rost--Schmid/Deligne coefficients}
    \xrightarrow{\Omega_F^\bullet}
  (L^\bullet,\Theta)
    \xrightarrow{\operatorname{Fib}(\Theta-n)}
  \text{Weil--Arakelov specialization}.
\]

## Hostile attack

- Raw Milnor--Witt cohomology of \(\operatorname{Spec}\mathbb Z\) is finitely generated in the
  relevant one-dimensional range.  It cannot itself be the infinite spectral \(H^1\).
  Noncompact leafwise flow completion is essential.
- Ordinary rational-Witt correspondences retain the Kucharczyk--Scholze Steinberg defect.
  Forgetting to derive along \(U\) returns the known wrong cohomology.
- Milnor--Witt transfer forms are indefinite over \(\mathbb R\).  They supply orientation and
  Poincaré duality, not positive Hodge theory.  Positivity must come from the archimedean
  boundary realization.
- A determinant declared equal to \(\widehat\zeta\), or a comparison declared faithful, can
  encode the desired divisor.  Both must be derived from finite correspondences and the
  prime--Gamma trace before divisor evaluation.
- A positive Hodge form on a target indexed by Xi zeros is not source construction.  Flow
  naturality on the source total complex must be proved first.

**Verdict:** `SURVIVES PRELIMINARY ATTACK`.  It is compatible with the strongest available
arithmetic correspondence and Milnor--Witt theories, and it targets Deninger's stated
\(R\alpha_*\mathscr G\) gap.  No source realization theorem presently proves properties 1--8.

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

`[OPEN CORE]` Construct a monoidal comparison from the ordinary projection of the
homotopy-coherent Rost--Schmid MW coefficient system to Deninger's
finite-correspondence/rational-Witt site, while retaining its Witt fiber as the duality channel.
Descend the resulting \(\mathbb Q_{>0}\)-localization to the leafwise connection \(\nabla\),
then construct the archimedean extension and its positive Hodge operator.  Frobenius,
coherent Verschiebung, and \(n_\epsilon\mapsto n\) are literature inputs, not open
constructions.

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
