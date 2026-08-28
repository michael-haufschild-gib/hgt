# Coefficient-dominated refinement collapse, presentation core, and serial-charge invariance law

- **ID:** ULF-DOFM-2
- **Stage:** 3 -- formalized in Lean 4
- **Type:** THEOREM (paper) / PRESENTATION-INDEPENDENCE LAW
- **Programme:** `../../../1-in-progress/universal-law-field/derived-observer-formation-mechanics/field-programme.md`
- **Parent:** ULF-DOFM-1
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [PRESENTATION INVARIANCE]`
  `[EXPLICIT CHAIN CONTRACTION] [ALL HOMOLOGICAL DEGREES]`
  `[SERIAL ERASURE/RETENTION INVARIANT] [SHARP JOIN-REDUNDANCY COUNTERMODEL]`
  `[CLASSICAL CONTIGUITY MACHINERY] [NOT RH] [LEAN-FORMALIZED] [AXIOM-AUDITED]`
- **Formal status:** formalized unconditionally in
  `GaloisForLFunctions.HTGeometry.CoefficientDominatedRefinementCollapse`. Direct Lean elaboration
  and targeted leaf build pass. Audited capstones depend only on `propext`, `Classical.choice`, and
  `Quot.sound`. The sharp join-redundancy countermodel is instantiated over `ℚ`, making the
  load-bearing non-characteristic-two condition explicit.
- **Statement:** Adding a formation leg contained in an existing leg adds a contractible
  coefficient-incidence sector.  Deleting the dominated leg is a chain-homotopy equivalence for
  every observer-formation complex and for the serial kernel/retention complexes.  Mere redundancy
  at the level of the total join is insufficient and can create new formation homology.

## 1. Setup

Let `k` be a field, let `V` be a `k`-vector space, let `I` be a finite ordered set, and let

\[
 W=(W_i)_{i\in I},\qquad W_i\subseteq V.
 \tag{DRC.1}
\]

Let `L:V->Y` be linear.  Write `F_L(W)` for the augmented observer-formation complex of
ULF-DOFM-1:

\[
 \mathsf F_L(W)_p
 =\bigoplus_{|J|=p+1}L(W_J),
 \qquad
 \mathsf F_L(W)_{-1}=L\left(\sum_iW_i\right),
 \tag{DRC.2}
\]

where `W_J=cap_{j in J}W_j` and the boundary is the alternating sum of inclusions.

Add a new label `star` and a new leg `W_star`.  Assume that for one old label `a in I`,

\[
 \boxed{W_\star\subseteq W_a.}
 \tag{DRC.3}
\]

Call this a **coefficient-dominated refinement**.  The adjective matters: the underlying abstract
simplex on the labels is always contractible; the content is that every coefficient carried by a
simplex containing `star` also legally maps to the coefficient obtained by replacing `star` by
`a`.

Because of `(DRC.3)`,

\[
 W_{J\cup\{a\}}=W_J
 \quad\text{whenever }\star\in J.
 \tag{DRC.4}
\]

The total join is unchanged:

\[
 \sum_{i\in I\cup\{\star\}}W_i=\sum_{i\in I}W_i.
 \tag{DRC.5}
\]

## 2. Order invariance

### Lemma 2.1 -- relabelling is a chain isomorphism

Every permutation of the finite label set induces a chain isomorphism of formation complexes.  On
the summand indexed by `J`, multiply the evident relabelling map by the sign of the induced ordering
of `J`.  The augmentation is unchanged.

### Proof

The sign converts the boundary orientation before relabelling into the boundary orientation after
relabelling.  Intersections and the total join depend only on the underlying subset, not its listed
order.  The inverse permutation supplies the inverse chain map.  QED.

Consequently we may place `a` and `star` adjacent in the order while proving the collapse.

## 3. Dominated-refinement collapse

Let `W^+=W cup {W_star}`.  The old summands define a chain inclusion

\[
 \iota:\mathsf F_L(W)\longrightarrow\mathsf F_L(W^+).
 \tag{DRC.6}
\]

The augmentation component of `iota` is the identity by `(DRC.5)`.

Define a label retraction

\[
 \rho(\star)=a,
 \qquad
 \rho(i)=i\quad(i\in I).
 \tag{DRC.7}
\]

It induces a normalized simplicial chain map

\[
 r:\mathsf F_L(W^+)\longrightarrow\mathsf F_L(W).
 \tag{DRC.8}
\]

On a summand indexed by `J`:

1. if `J` does not contain `star`, `r` is the identity;
2. if `J` contains `star` but not `a`, replace `star` by `a`, use the inclusion
   `L(W_J) subset L(W_{rho J})`, and insert the ordering sign;
3. if `J` contains both `star` and `a`, the normalized image is degenerate and `r` is zero.

At augmentation degree `r` is the identity.

### Lemma 3.1 -- the retraction is a chain map

The map `r` commutes with the alternating boundary and augmentation, and

\[
 r\iota=1_{\mathsf F_L(W)}.
 \tag{DRC.9}
\]

### Proof

The normalized chain map associated with a vertex map commutes with simplicial boundaries: faces
whose images repeat a label vanish, while the remaining faces occur with the induced ordering
sign.  The coefficient map is legal because `W_J subset W_{rho J}`.  In degree zero an element in
`L(W_star)` is included into `L(W_a)` and then into the same augmentation target, so the
augmentation commutes.  Old labels are fixed, proving `(DRC.9)`.  QED.

### Theorem 3.2 -- explicit dominated contraction

The inclusion `iota` and retraction `r` are chain-homotopy inverses.  Hence

\[
 \boxed{
 \mathsf H_p(L;W^+)\simeq\mathsf H_p(L;W)
 \quad\text{for every }p.}
 \tag{DRC.10}
\]

The isomorphism induced by deletion of the dominated leg is canonical; the chosen dominator is
needed only to write a homotopy inverse.

### Proof

We already have `r iota=1`.  Define a degree-`+1` prism operator `h` on a summand indexed by `J`:

\[
 h_J=
 \begin{cases}
  \epsilon_J\,\mathrm{id}_{L(W_J)}:
  L(W_J)\longrightarrow L(W_{J\cup\{a\}}),
   &\star\in J,\ a\notin J,\\
  0,&\text{otherwise},
 \end{cases}
 \tag{DRC.11}
\]

where `epsilon_J` is the orientation sign for inserting `a`.  The displayed identity map is typed
because `(DRC.4)` gives `W_{J cup {a}}=W_J`.  Put `h=0` in augmentation degree.

In the boundary of `J cup {a}`, deleting `a` returns `J`, while deleting `star` returns the
retracted simplex `rho J`.  All other faces occur once in `d h` and once in `h d` with opposite
signs.  If `J` already contains `a`, the normalized retraction is zero and the same face pairing
holds with `h_J=0`.  Thus the direct alternating-boundary calculation gives

\[
 d h+h d=1-\iota r.
 \tag{DRC.12}
\]

Together with `(DRC.9)`, this proves the chain-homotopy equivalence and `(DRC.10)`.  QED.

### Corollary 3.3 -- iterated legal refinements

Any finite sequence of coefficient-dominated insertions or deletions induces a chain-homotopy
equivalence.  The homology isomorphisms induced by the canonical inclusions compose strictly.

### Proof

Compose the chain-homotopy equivalences of Theorem 3.2.  Functoriality of homology makes the
inclusion-induced isomorphisms compose.  QED.

## 4. Coefficient-functor form

The proof did not use any property specific to `A mapsto L(A)` beyond covariant inclusion maps.
Let `Phi` be any coefficient rule on the relevant subspace poset such that

\[
 A\subseteq B\Longrightarrow \Phi(A)\longrightarrow\Phi(B)
 \tag{DRC.13}
\]

functorially.  Replacing every `L(W_J)` by `Phi(W_J)` gives the same contraction.  Therefore
coefficient-dominated refinement invariance holds simultaneously for image, kernel-intersection,
quotient, filtered, and reporter coefficient systems whenever their structure maps respect the
dominating inclusion.

This is the route-independent statement: presentation stability is a law of the formation
mechanism, not a property of one chosen observer.

## 5. Compatibility with serial observer mechanics

Let `V -L-> Y -M-> Z` and `K=ker M`, as in ULF-DOFM-1.  A dominated source leg remains dominated
after applying `L`:

\[
 L(W_\star)\subseteq L(W_a).
 \tag{DRC.14}
\]

Apply Theorem 3.2 and its coefficient-functor form to the four complexes

\[
 \mathsf F_L,
 \qquad
 \mathsf K_{M\mid L},
 \qquad
 \mathsf F_{ML},
 \qquad
 \mathsf F_{M\mid L}.
 \tag{DRC.15}
\]

The prism homotopy for `F_{M|L}` preserves the subcomplex `F_{ML}`: when `star in J`, adding `a`
does not change `W_J`, and hence does not move a direct-source coefficient out of the direct-source
subcomplex.  It therefore descends to the quotient `R_{M|L}`.

### Theorem 5.1 -- serial-charge presentation invariance

A coefficient-dominated insertion induces compatible chain-homotopy equivalences on

\[
 \boxed{
 \mathsf F_L,
 \quad\mathsf K_{M\mid L},
 \quad\mathsf F_{ML},
 \quad\mathsf F_{M\mid L},
 \quad\mathsf R_{M\mid L}.}
 \tag{DRC.16}
\]

They form maps of both short exact sequences of ULF-DOFM-1.  Consequently every erasure,
retention, and formation-homology group is preserved, and the induced isomorphisms commute with
both long-exact-sequence connecting maps.

### Proof

For the first four complexes use Theorem 3.2 with the corresponding monotone coefficient system.
The explicit maps `iota,r,h` commute with `L`, `M`, and intersection with `K`, so they form a
homotopy equivalence of the erasure short exact sequence.  The preservation observation preceding
the theorem makes them homotopy equivalences of pairs

\[
 (\mathsf F_{M\mid L},\mathsf F_{ML}),
\]

and therefore of the quotient `R_{M|L}`.  Naturality of connecting homomorphisms under maps of
short exact sequences gives the final claim.  QED.

## 6. Exact boundary: join redundancy is insufficient

The containment hypothesis `(DRC.3)` cannot be replaced by the weaker statement that the new leg
lies in the join of the old legs or leaves the total join unchanged.

### Countertheorem 6.1 -- a join-redundant leg creates charge

Let `V=k^2` with basis `e_1,e_2`, let

\[
 W_1=k e_1,
 \qquad
 W_2=k e_2,
 \qquad
 W_3=k(e_1+e_2),
 \tag{DRC.17}
\]

and let `L(x,y)=x+y`.  Then

\[
 W_1+W_2=W_1+W_2+W_3=V,
 \tag{DRC.18}
\]

but

\[
 \boxed{
 \dim\mathsf H_0(L;W_1,W_2)=1,
 \qquad
 \dim\mathsf H_0(L;W_1,W_2,W_3)=2.}
 \tag{DRC.19}
\]

### Proof

All pairwise intersections of the three distinct lines are zero.  Their nonzero observer images
are all `k`.  For two legs the complex in degrees zero and minus one is

\[
 0\longrightarrow k^2\xrightarrow{(x,y)\mapsto x+y}k,
\]

whose degree-zero homology has dimension one.  For three legs it is

\[
 0\longrightarrow k^3\xrightarrow{(x,y,z)\mapsto x+y+z}k,
\]

whose degree-zero homology has dimension two.  The total join is `V` in both presentations, but
`W_3` is contained in neither old leg.  QED.

The same example with `L=id_V` changes source formation homology from zero to one: the relation
`e_1+e_2-(e_1+e_2)=0` is born when the third leg is admitted.  Thus a merely join-redundant leg can
represent a genuine law generator rather than removable presentation noise.

## 7. Presentation core and marked scope

For a finite unmarked family, repeatedly delete legs contained in another leg.  The remaining
distinct maximal legs form an antichain.  Theorem 3.2 shows that every such deletion sequence has
the same formation homology as the original family.  Equal duplicate legs leave a choice of label,
but any choice gives canonically isomorphic unmarked complexes.

This does **not** authorize deletion of a dominated leg carrying an independent prime, orientation,
depth, or source-history mark.  Legal presentation equivalence must declare which marks may be
forgotten.  The theorem says:

\[
 \boxed{
 \text{coefficient domination plus mark-forgetfulness}
 \Longrightarrow
 \text{presentation-invariant charge}.}
 \tag{DRC.20}
\]

It does not say that containment erases constitutive metadata.

## 8. Collision and significance audit

The chain mechanism is classical contiguity/strong-collapse machinery.  Barmak and Minian define a
dominated vertex and prove that replacing it by its dominator gives a simplicial strong
equivalence; see [*Strong homotopy types, nerves and collapses*](https://arxiv.org/abs/0907.2954),
especially Proposition 2.9.  Simplicial homotopy with coefficient systems and algebraic
cancellation are also standard.

The closest internal collision is the already Lean-certified
`ConstitutiveFailureAntichainQuotient.lean`: insertion of a dominated failure kernel preserves
symbolic/executable admission, primitivity, and primitive-degree occurrence.  ULF-DOFM-2 does not
rediscover that semantic theorem.  Its residue is chain-level: it constructs the contraction for
intersection coefficient systems and proves compatibility with both serial short exact sequences,
their quotient complex, and their connecting maps.

The field-level residue is the coefficient-sensitive boundary and its serial compatibility:

1. containment of law legs gives an explicit contraction in every observer doctrine;
2. both kernel erasure and retained-intersection comparison survive the contraction;
3. connecting maps, not only Betti numbers, are presentation-invariant;
4. equality of generated joins is sharply insufficient and can create new charge.

The honest label is `[CLASSICAL HOMOTOPY MACHINERY] [NEW-TO-CORPUS PRESENTATION LAW]`.  No external
priority claim is made.

## 9. Field consequence

ULF-DOFM-2 proves the dominated-refinement part of Conjecture A.  The correct moduli problem is not
the set of arbitrary presentations of one join.  It is the localization of marked formation
families at coefficient-dominated collapses.  Derived observer-formation charge descends to this
localization, while non-dominated join-redundant insertions remain genuine formation events.

This gives a hard anti-theatre test for future arithmetic realizations:

- adding a source leg already contained in another legal leg must not change the charge;
- adding a new prime/depth/reflection leg that is only generated collectively may change it;
- any claimed source action must respect the first distinction and compute the second.

## 10. Lean status

`CoefficientDominatedRefinementCollapse.lean` supplies the missing coefficient-sensitive complex
and contraction. It formalizes ordered alternating boundaries with `∂²=0`, dominated-label
collapse, insertion prism, chain-homotopy identity, collapse idempotence, explicit homology and
presentation-core equivalence, coefficient naturality, pair quotients, serial refinement
certificates, iterated legal-refinement invariance, a sharp `ℚ²` join-redundancy countermodel, and
order-isomorphic relabelling with boundary commutation.

The serial certificate records compatible chain maps and homotopies for the kernel, retained, and
pair-quotient coefficient systems. It does not introduce a second category-theoretic long-exact-
sequence implementation: connecting-map naturality is represented by this chain-level naturality
data. This is the exact normalized retraction/prism gate stated below.

Verification certificate:

- `lake env lean GaloisForLFunctions/HTGeometry/CoefficientDominatedRefinementCollapse.lean` passes;
- `lake build GaloisForLFunctions.HTGeometry.CoefficientDominatedRefinementCollapse` passes;
- repository lint reaches the module and reports no defect in it; current nonzero lint status is
  caused by sixteen unrelated umbrella-reachability errors in the shared worktree;
- `prism_identity_succ`, `presentationCoreHomologyEquiv`,
  `serial_refinement_certificate`, `join_redundancy_creates_charge`, and
  `chainRelabel_comm_boundary` depend only on `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 -> 1: coefficient domination, explicit maps, and sharp non-dominated falsifier
- [x] 1 -> 2: chain contraction, serial-pair compatibility, quotient invariance, and marked scope
- [x] 2 -> 3: Lean formalization of the normalized retraction and prism identity
- [ ] 3 -> 4: literal arithmetic formation family and legal-refinement theorem

## Log

- 2026-08-14 -- dominated-refinement contraction closed on paper; arbitrary join redundancy proved
  insufficient; serial erasure/retention exact laws shown presentation-invariant.
- 2026-08-28 -- formalized coefficient complex, explicit contraction, presentation-core homology,
  serial compatibility, quotient descent, iterated legal-refinement invariance, sharp `ℚ²`
  countermodel, and relabelling naturality. Direct elaboration, targeted leaf build, and capstone
  axiom audit passed; promoted to Stage 3.
