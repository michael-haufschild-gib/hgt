# Deninger cofinite-open base change

- **ID:** `deninger-cofinite-open-base-change`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Label:** `DAC_DENINGER_COFINITE_OPEN_BASE_CHANGE`
- **Parent:** `deninger-arithmetic-projection-leray-rost-schmid-resolution`
- **Statement:** Deninger's character space, Frobenius colimit,
  suspension, and degreewise coarse invariant coefficient restrict
  canonically to every cofinite arithmetic open.
- **Lean modules:**
  `GaloisForLFunctions.RHTower.DeningerArithmeticCofiniteOpenBaseChange`
  (the quotient/saturated-open topology of clause 3),
  `GaloisForLFunctions.RHTower.DeningerInvariantRestriction` (the invariant restriction `(5)`),
  `GaloisForLFunctions.RHTower.DeningerCharacterProjectionOpen` (the projection-level content of
  clauses 1--2),
  `GaloisForLFunctions.RHTower.DeningerSchemeCharacterSpace` (the character space itself, with
  Lemmas 7.1--7.3),
  `GaloisForLFunctions.RHTower.DeningerFrobeniusColimitSpace` (the Frobenius colimit,
  Proposition 7.4, and the colimit-level open embedding of clause 2)

## Goal

Separate a topological and sheaf-theoretic fact from the open analytic
comparison.  This theorem identifies the source object over
\[
 U_N=\operatorname{Spec}\mathbb Z[1/N]
\]
without commuting derived sections with invariants and without
replacing Deninger's coarse quotient by a quotient stack.

## Setup

Put \(S=\operatorname{Spec}\mathbb Z\).  Use the same Frobenius monoid
\(\mathbb N_{>0}\) for \(S\) and every \(U_N\); this is allowed because
Deninger only requires its set of prime generators to contain the
residue characteristics of the arithmetic scheme.

Write
\[
 \dot S(\mathbb C),\qquad
 \check S(\mathbb C)=
 \mathop{\mathrm{colim}}_{\nu\in\mathbb N_{>0},F_\nu}
 \dot S(\mathbb C)
\]
for Deninger's character space and Frobenius colimit.  Let
\[
 Y_S=\check S(\mathbb C)\times\mathbb R_{>0},\qquad
 X_S=Y_S/\mathbb Q_{>0},
\]
where
\[
 q\cdot(P,u)=(F_qP,q^{-1}u).
\]
The arithmetic projection is
\[
 a_S:X_S\longrightarrow S,\qquad [P,u]\longmapsto\operatorname{pr}(P).
                                                               \tag{1}
\]
The same notation with \(U_N\) in place of \(S\) denotes the
construction performed on the arithmetic open.

Let \(\widetilde{\mathscr A}^{\bullet}_S\) be any
\(\mathbb Q_{>0}\)-equivariant cover coefficient on \(Y_S\), and put
\[
 \mathscr E^\bullet_S
 =
 (\pi_{S,*}\widetilde{\mathscr A}^{\bullet}_S)
 ^{\mathbb Q_{>0}}.                                             \tag{2}
\]
For the final comparison one takes the Tate--Milnor coefficient of
`DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`.

## Theorem

`[PROVED HERE] [DAC_DENINGER_COFINITE_OPEN_BASE_CHANGE]`

For every nonzero \(N\):

1. \(\dot U_N(\mathbb C)\) is canonically the open subspace
   \[
   \operatorname{pr}^{-1}(U_N)\subset\dot S(\mathbb C).
                                                               \tag{3}
   \]
2. The induced map
   \[
   \check U_N(\mathbb C)\longrightarrow\check S(\mathbb C)
   \]
   is an open embedding with image
   \(\check{\operatorname{pr}}^{-1}(U_N)\).  Its image is invariant
   under every \(F_q\), under the Galois action before Galois descent,
   and under \(\mathbb Q_{>0}\).
3. The suspension made from \(U_N\) is canonically homeomorphic to
   the saturated open subspace
   \[
   X_{U_N}\ \xrightarrow{\sim}\ a_S^{-1}(U_N)\subset X_S.        \tag{4}
   \]
4. If
   \(Y_{U_N}=\pi_S^{-1}(a_S^{-1}U_N)\), then restriction of `(2)`
   satisfies, degreewise,
   \[
   \left.\mathscr E^\bullet_S\right|_{a_S^{-1}U_N}
   \cong
   \left(
      \pi_{U_N,*}
      \left.\widetilde{\mathscr A}^{\bullet}_S\right|_{Y_{U_N}}
   \right)^{\mathbb Q_{>0}}.                                    \tag{5}
   \]
   The isomorphism is functorial under \(U_M\subseteq U_N\), is
   compatible with the differential and product, and commutes with
   every equivariant source operation.

Equation `(5)` is underived.  Applying ordinary derived global
sections only after `(5)` gives
\[
 R\Gamma\!\left(a_S^{-1}U_N,\mathscr E^\bullet_S\right)
 =
 R\Gamma\!\left(
   X_{U_N},
   \left(
     \pi_{U_N,*}
     \widetilde{\mathscr A}^{\bullet}_S|_{Y_{U_N}}
   \right)^{\mathbb Q_{>0}}
 \right).                                                       \tag{6}
\]
No invariants have been moved through \(R\Gamma\).

## Proof

### Character space

Deninger's Lemma 7.1 identifies the inverse image of an arithmetic
open under the character-space projection.  Lemma 7.2 proves that
for every open immersion \(U\hookrightarrow S\), the induced
\(\dot U(\mathbb C)\hookrightarrow\dot S(\mathbb C)\) is an open
embedding.  These statements give `(3)`.

The Frobenius maps preserve the underlying scheme point:
\[
 F_\nu(x,P^\times)=(x,F_\nu P^\times).                           \tag{7}
\]
Consequently the embeddings in `(3)` commute with the common
Frobenius diagram.  Under the inductive-limit topology,
\(\check U_N(\mathbb C)\) is therefore exactly
\(\check{\operatorname{pr}}^{-1}(U_N)\).  For every Frobenius chart
its intersection is the open subspace `(3)`, so it is open.
Deninger's Proposition 7.4 makes every \(F_q\) a homeomorphism on
the colimit.  Equation `(7)` proves invariance under \(F_q\); the
Galois action also preserves \(x\)'s image in \(S\).  This proves
clause 2.

### Quotient and suspension

We use the following elementary quotient lemma.  If a group \(G\)
acts by homeomorphisms on \(Y\), \(V\subseteq Y\) is open and
\(G\)-invariant, and \(q:Y\to Y/G\) is the quotient map, then
\[
 V/G\longrightarrow q(V)
\]
is a homeomorphism and \(q(V)\) is open.  Indeed,
\[
 q^{-1}q(V)=V,\qquad
 q^{-1}q(O)=\bigcup_{g\in G}gO
                                                               \tag{8}
\]
for \(O\subseteq Y\).  The second set is open whenever \(O\) is
open, so \(q\) is open; applying the quotient criterion to the
restriction proves the homeomorphism.

Apply the lemma first to Galois descent, when present, and then to
the diagonal \(\mathbb Q_{>0}\)-action on
\(\check S(\mathbb C)\times\mathbb R_{>0}\).  The open from clause 2
times \(\mathbb R_{>0}\) is saturated because the rational-power
action preserves the arithmetic projection.  Its quotient is
precisely `(4)`, proving clause 3.

### Invariant coefficient

Let \(W\subseteq a_S^{-1}U_N\) be open.  Direct image and restriction
give the literal equality
\[
 \begin{aligned}
 \left(\pi_{S,*}\widetilde{\mathscr A}^n_S\right)(W)
 &=
 \widetilde{\mathscr A}^n_S(\pi_S^{-1}W)\\
 &=
 \left(\pi_{U_N,*}
   \widetilde{\mathscr A}^n_S|_{Y_{U_N}}\right)(W).              \tag{9}
 \end{aligned}
\]
Both \(\mathbb Q_{>0}\)-actions in `(9)` are restrictions of the same
action.  Taking their equalizers sectionwise gives `(5)`.
Differential, multiplication, restriction in \(N\), and every
commuting operation are unchanged under `(9)`.  This proves clause 4
and `(6)`.

## Exact boundary of the theorem

The theorem proves source localization, not the desired arithmetic
amplitude.  It does **not** prove:

- acyclicity or Steinness of \(a_S^{-1}U_N\);
- a Cartier/Kummer description of any prime packet;
- a two-row model for `(6)`;
- commutation of invariants with cohomology;
- exactness of the Rost--Schmid residue sequence.

Those assertions remain in
`DAC_COFINITE_COARSE_ANALYTIC_DIVISOR_COMPARISON`.

## Hostile audit

- Using a smaller Frobenius monoid for \(U_N\) would make the two
  colimits different diagrams.  The theorem fixes one common monoid.
- Openness before the Frobenius colimit alone is insufficient;
  compatibility `(7)` and the inductive-limit topology are both used.
- A quotient of an arbitrary open need not be its subspace quotient.
  Saturation and the open-quotient lemma are essential.
- Equation `(5)` concerns degreewise fixed sections.  It supplies no
  group-cohomology or homotopy-quotient comparison.
- The proof uses no zeta zero, RH statement, spectral realization, or
  numerical computation.

## Formalized statement

`GaloisForLFunctions/RHTower/DeningerArithmeticCofiniteOpenBaseChange.lean` already encodes the
elementary quotient lemma used for clause 3, in the saturated-open form:

- `DeningerSaturatedOpen q V` : `V` is the full inverse image of its image, i.e. `V` is
  saturated for the quotient map;
- `deningerSaturatedOpen_of_fiberwise` : fibrewise-constant membership implies saturation;
- `deningerSaturatedOpen_image_isOpen` : the image of a saturated open under an open quotient map
  is open — this is "`q(V)` is open";
- `deningerSaturatedOpen_restrict_isOpenQuotientMap` : the base change of an open quotient map to
  that image is again an open quotient map;
- `deningerSaturatedOpenDomainHomeomorph` (with its two `apply` lemmas) : for a saturated open,
  the domain of the restricted quotient map is canonically homeomorphic to `V` — this is
  "`V/G → q(V)` is a homeomorphism".

`GaloisForLFunctions/RHTower/DeningerInvariantRestriction.lean` encodes clause 4, equation
`(5)`.  The reason `(5)` holds, and the reason no invariants are moved past anything, is that an
invariant `π` makes every preimage stable:

- `DeningerInvariantMap G π` : `π (g • y) = π y`;
- `deningerPreimage_smul_mem`, `deningerPreimageSub` : every `π ⁻¹' W` is stable, hence a
  sub-action, so the action restricts to `π ⁻¹' V`;
- `deningerRestrictInvariantMap` : the restricted map is again invariant, which is what makes the
  construction iterate along `U_M ⊆ U_N`;
- `deningerPreimageRestrictEquiv` and `deningerPreimageRestrictEquiv_smul` : for `W ⊆ V` the
  `W`-part of `π ⁻¹' V` is *equivariantly* the same as `π ⁻¹' W`;
- `deningerInvariantSectionsEquiv` : therefore the equivariant sections with values in any
  coefficient `G`-set over the two descriptions are in canonical bijection — this is `(5)`
  degreewise.

### What is formalized and what is not

Formalized: the elementary quotient lemma of clause 3, and the invariant restriction `(5)` of
clause 4.

The `(5)` formalization is at the level of equivariant sections valued in a coefficient `G`-set,
which is the shape the card's degreewise statement takes; it is not phrased through a sheaf-of-
abelian-groups pushforward functor, because the corpus has no equivariant sheaf object to phrase
it against.  The mathematical content — stability of preimages and the equivariant identification
— is the same either way.

Not formalized: clauses 1 and 2.  They rest on Deninger's Lemmas 7.1--7.3 and Proposition 7.4
(the character-space inverse image, the open embedding, and Frobenius acting by homeomorphisms on
the colimit).  Those are quoted geometric input about a space the corpus does not construct, so
they are not formalizable as stated without first building Deninger's character space.  A search
of the formal tree confirms no character-space object exists anywhere in it, so this needs its own
construction card rather than further work here.

## Gates

- [x] 0 → 1 in-progress: precise source-local statement
- [x] 1 → 2 fully-proven: topological and equalizer proof complete
- [x] 2 → 3 formalized, quotient-open part
  (`GaloisForLFunctions.RHTower.DeningerArithmeticCofiniteOpenBaseChange`)
- [x] 2 → 3 formalized, invariant-restriction part `(5)`
  (`GaloisForLFunctions.RHTower.DeningerInvariantRestriction`)
- [x] 2 → 3 formalized, clauses 1--2, projection-level content
  (`GaloisForLFunctions.RHTower.DeningerCharacterProjectionOpen`)
- [x] 2 → 3 formalized, clauses 1--2, the character space itself, constructed with such a
  projection, together with Lemmas 7.1--7.3 for it
  (`GaloisForLFunctions.RHTower.DeningerSchemeCharacterSpace`)
- [x] 2 → 3 formalized, clause 2, the Frobenius colimit and Proposition 7.4
  (`GaloisForLFunctions.RHTower.DeningerFrobeniusColimitSpace`)
- [x] 2 → 3 formalized, clause 2, the colimit-level open embedding `Ǔ_N(ℂ) ↪ Š(ℂ)` with image
  `p̌r⁻¹(U_N)` (`GaloisForLFunctions.RHTower.DeningerFrobeniusColimitSpace`)
- [ ] 3 → 4 publication-ready: integrate with analytic purity proof

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  Lemmas 7.1--7.3 and Proposition 7.4:
  https://arxiv.org/abs/1807.06400
- `DAC_COARSE_INVARIANT_SHEAF_EXISTENCE`
- `DAC_COFINITE_DIVISOR_SPLIT_STRICTNESS`

## Log

- 2026-07-27 — isolated and proved exact compatibility of Deninger's
  source space and underived invariant coefficient with cofinite
  arithmetic opens.

## Log

- 2026-08-01 — Recorded the existing Lean module.  The card previously claimed nothing was
  encoded, but `DeningerArithmeticCofiniteOpenBaseChange.lean` already proves the quotient-open
  and saturated-open homeomorphism lemmas of clause 3.  Split the remaining formalization gate
  into the invariant-restriction identity `(5)`, which is reachable, and clauses 1--2, which are
  blocked on the character space not existing in the corpus.
- 2026-08-01 — Formalized `(5)`: preimages under an invariant map are stable, the restricted map
  is again invariant, and for `W ⊆ V` the `W`-part of `π⁻¹V` is equivariantly `π⁻¹W`, so
  equivariant sections agree.  Axiom audit shows these use only `propext` and `Quot.sound`, no
  choice.

### Clauses 1--2, projection level

`formal/GaloisForLFunctions/RHTower/DeningerCharacterProjectionOpen.lean` (8 declarations; the
set-theoretic ones depend on no axioms at all, the topological ones on `propext` alone) formalizes
everything in clauses 1--2 that does not mention the internal structure of the character space:

- `deningerCharacterOver` — the character space over an arithmetic open, *defined* as the preimage
  under the projection, which is what Deninger's Lemma 7.1 identifies it with;
- `deningerCharacterOver_isOpen`, `deningerCharacterOver_mono` — it is open and grows with the
  open, which is `(3)` and the functoriality in `U_M ⊆ U_N`;
- `deningerCharacterOver_map_mem`, `deningerCharacterOver_image_subset` — **`(7)`**: a map
  preserving the projection, such as every Frobenius, preserves it, since it does not move the
  underlying scheme point;
- `deningerCharacterOver_smul_mem` — the suspension action preserves it too, whenever the action
  preserves the projection; this is why the open of clause 2 times `ℝ_{>0}` is saturated;
- `deningerColimitCharacterOver_isOpen` — **openness in the Frobenius colimit**: if the colimit
  carries the inductive-limit topology and its projection restricts to the chart projections, then
  the character space over an arithmetic open is open in the colimit, because in each chart it is
  the chart-level character space.

What is still quoted from Deninger is only the identification of his `Ṡ(ℂ)` with a space carrying
such a projection — Lemmas 7.1--7.3 and Proposition 7.4 — which needs that space to be constructed
in the corpus first.

### The character space, constructed

The earlier note that "no character-space object exists anywhere in the formal tree, so this needs
its own construction card" is superseded: the space is now built.

`formal/GaloisForLFunctions/RHTower/DeningerSchemeCharacterSpace.lean` (27 declarations, axiom
audit `propext, Classical.choice, Quot.sound` throughout) defines

- `DeningerCharacterSpace X` — a point is a point of the scheme together with a character of the
  multiplicative group of its residue field, `Hom(κ(x)^×, ℂ^×)`;
- `deningerCharacterPr` — the arithmetic projection, forgetting the character;
- `deningerCharacterMap f` — functoriality, pulling a character back along
  `Scheme.Hom.residueFieldMap`.

For an open immersion the residue field map is an isomorphism (mathlib's
`IsIso (f.residueFieldMap x)`), which is what makes the following true:

- `deningerCharacterMap_injective`, `deningerCharacterMap_range` — **Lemma 7.1**: the character
  space of an open subscheme is exactly the part of the character space lying over that open,
  `pr⁻¹(range f)`, phrased against the existing `deningerCharacterOver`;
- `deningerCharacterMap_range_opens` — the same for `U : X.Opens`, giving `(3)` on the nose;
- `deningerCharacterMap_isOpenEmbedding` — **Lemmas 7.2--7.3**: the induced map is an open
  embedding.  The topology used is the arithmetic topology `instTopologicalSpace`, the coarsest
  one for which the projection is continuous; the inducing step is
  `deningerCharacterMap_isInducing`, which is where the open-embedding property of the scheme
  morphism on points enters;
- `deningerCharacterFrobenius n` — the Frobenius maps, raising a character to its `n`-th power.
  `deningerCharacterFrobenius_pr` is **`(7)`**, `_comp` and `_one` are the monoid law of the
  Frobenius diagram, `deningerCharacterMap_frobenius` is the commutation of the open embeddings
  with that diagram, and `deningerCharacterFrobenius_characterOver_mem` is the `F_q`-invariance
  asserted in clause 2.

### The Frobenius colimit, constructed

`formal/GaloisForLFunctions/RHTower/DeningerFrobeniusColimitSpace.lean` (25 declarations, same
axiom audit) builds `Š(ℂ)`:

- `DeningerFrobeniusColimit X` — the quotient of one copy of the character space per Frobenius
  stage, where a point at stage `μ` and one at stage `ν` are identified when a pair of Frobenius
  maps with matching stage cofactors makes them equal.  Transitivity of that relation is the
  filtered-colimit computation `μ(ks) = ρ(lt)`, done in `deningerFrobeniusRel_trans`;
- `deningerColimit_topology` — **the colimit carries the inductive-limit topology of its charts**,
  which is exactly the hypothesis `deningerColimitCharacterOver_isOpen` was stated against.  That
  abstract lemma is now instantiated: `deningerColimitCharacterOver_isOpen'` is the openness of
  the character space over an arithmetic open in the actual colimit;
- `deningerColimitPr` — the arithmetic projection descends, because every Frobenius map fixes the
  underlying scheme point;
- `deningerColimitFrobeniusHomeomorph` — **Proposition 7.4**: every Frobenius map is a
  homeomorphism of the colimit.  On the character space itself `F_q` is not injective, since the
  `q`-th power map of `ℂ^×` is not; on the colimit its inverse is the map that advances the stage
  instead of raising the character to a power, and the two composites are the identity by a
  one-line cofactor computation;
- `deningerColimitFrobenius_pr` and `deningerColimitFrobenius_characterOver_mem` — `(7)` and the
  `F_q`-invariance of the character space over an open, now at colimit level.

### What is still not formalized

Clause 2 asserts that `Ǔ_N(ℂ) → Š(ℂ)` is an *open embedding*.  Its image is computed and shown to
be open, and the chart-level map is an open embedding; the colimit-level inducing and open-map
refinement is not proved.  That is a statement about images of opens under a filtered colimit of
open embeddings and is the one remaining `2 → 3` gate.

Clause 3's quotient lemma and clause 4's invariant restriction `(5)` were already formalized in
`DeningerArithmeticCofiniteOpenBaseChange` and `DeningerInvariantRestriction`, and are unchanged.

### Log

- 2026-08-02 — Constructed the character space of a scheme and its Frobenius colimit, discharging
  the blocker recorded on 2026-08-01.  Lemmas 7.1--7.3 and Proposition 7.4 are now proved for the
  constructed object rather than quoted.

### The colimit-level open embedding

The gate left open above is now closed.  `DeningerFrobeniusColimitSpace.lean` (36 declarations,
axiom audit `propext, Classical.choice, Quot.sound` throughout) adds:

- `deningerColimit_isOpen_iff` — a subset of the colimit is open exactly when its preimage in
  every chart is open, the working form of the inductive-limit topology;
- `deningerColimitMap f` — the map of Frobenius colimits induced by a scheme morphism, well
  defined because the functorial map commutes with the Frobenius maps;
- `deningerColimitPr_map` — naturality of the arithmetic projection;
- `deningerColimitMap_injective` — injectivity, which reduces to injectivity on a chart because
  the Frobenius identification of the source is the restriction of that of the target;
- `deningerColimitMap_range`, `deningerColimitMap_opens_range` — **the image is
  `p̌r⁻¹(U_N)`**, exactly as clause 2 asserts;
- `deningerColimitMap_isOpenMap` — the map is open.  The computation behind it is that a chart
  point `z` at stage `n` lies in the image of an open set `O` exactly when, for some `l`, the
  `l`-th Frobenius power of `z` is the image of a point of `O` sitting at stage `n·l`.  Writing
  the preimage as that union over `l` turns it into a union of sets of the form
  `F_l⁻¹(ι(chart_{n·l}⁻¹(O)))`, each open because `F_l` and the charts are continuous and `ι` is
  an open map on the character space;
- `deningerColimitMap_isOpenEmbedding`, `deningerColimitMap_opens_isOpenEmbedding` — **clause 2**:
  `Ǔ_N(ℂ) → Š(ℂ)` is an open embedding.

The reindexing identity that makes the union work is that a point at stage `μ` equals the `k`-th
Frobenius power of itself at stage `μ·k`; it is the same cofactor computation that makes each
`F_q` invertible on the colimit.

All `2 → 3` gates of this card are now closed.

### Log

- 2026-08-02 — Proved the colimit-level open embedding, closing the last formalization gate.
