# Hypertranscendental pair localization and boundary noncompression

- **ID:** `hypertranscendental-pair-localization-noncompression`
- **Stage:** 2-fully-proven / unconditional algebraic core formalized / analytic HT status inherits the order-one elliptic-gamma theorem
- **Type:** THEOREM / FOUNDATIONAL STRUCTURE LAW
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]` -- the exact theorem was not located in the checked external literature; the canonical HT witnesses inherit the independently unaudited order-one elliptic-gamma atomic theorem, while realization of every private divisor additionally uses the all-depth exact-image theorem
- **Parents:** `elliptic-gamma-rank-three-da-spectrum`; `all-depth-pair-face-signature-completeness`
- **Statement:** In every generic finite mixed-constraint class, hypertranscendence is rank-two local but pairwise noncompressible. Compatible triptic data on all pair faces determine the complete class modulo differential algebraicity, yet every individual pair supports nonzero private hypertranscendental modes invisible on every other pair. The private sector on a pair is exactly one full transverse coboundary and first occurs at transverse order `d-2`.

## Setup

Let `d >= 3`, let `1,tau_1,...,tau_d` be linearly independent over `Q`, and let

`Q_d={F in Mer(C):F(z+1)=F(z) and product_i Delta_(tau_i)F in C}`.

For a pair `e={i,j}`, put

`H_e=Z+Z tau_i+Z tau_j`,

`A_e=C[delta][C/H_e]`.

For `k notin e`, let

`p_(e,e+k):A_e -> A_(e union {k})`

be finite-support pushforward along the `tau_k`-orbits. Define the **private pair sector**

`Priv_e=intersection_(k notin e) ker p_(e,e+k)`.

It consists of pair-face charges that disappear as soon as they are pushed toward any other face.

## Private-sector identity `[PROVED ON PAPER]`

For every pair `e`,

`Priv_e=(product_(k notin e)(t_(tau_k)-1))A_e`.                 `(1)`

Indeed, the transverse subgroup acts freely on `C/H_e`. On each orbit, `A_e` is a Laurent-polynomial module and `p_(e,e+k)` sets the corresponding Laurent variable to `1`. The multi-telescoping theorem therefore identifies the intersection of the kernels with the product of the transverse augmentation factors.

The sector is nonzero. For any basis charge `[a+H_e]`,

`D_e=product_(k notin e)(t_(tau_k)-1)[a+H_e]`                `(2)`

is nonzero because its `2^(d-2)` translated support points are distinct by rational independence.

The transverse order `d-2` is exact. Equation `(1)` makes every private charge divisible by the product of all `d-2` transverse augmentation factors, while `(2)` realizes that degree. Thus a pair-private mode cannot be hidden with fewer than one difference in every transverse direction.

## Canonical single-pair carrier `[PROVED ON PAPER, CONDITIONAL ONLY ON ORDER-ONE HT]`

Let `Psi_(d-1)` be the logarithmic derivative of the order-`d-1` multiple elliptic gamma function and fix a pair `e`. Put

`F_e=product_(k notin e) Delta_(tau_k) Psi_(d-1)`.           `(3)`

The multiple-gamma hierarchy reduces `F_e`, up to a DA normalization, to the order-one elliptic-gamma logarithmic derivative on the two parameters in `e`. Hence the order-one atomic theorem makes `F_e` hypertranscendental.

Its pair-face signature is computed before using any completeness theorem. On the target pair `e`, the complementary face operation applies the same transverse differences once more, so equivariance of the unit triptic charge gives

`S_e(F_e)=product_(k notin e)(t_(tau_k)-1)[0+H_e]`,          `(4)`

the nonzero private witness `(2)`. If `f != e` is another pair, then `f` contains a direction outside `e`. The `f`-push therefore sets one factor in `(4)` to `1-1=0`. Equivalently, direct hierarchy descent applies a structural difference of the order-one `e`-atom and leaves only a theta layer whose triptic charge is zero. Thus

`S_f(F_e)=0` for every `f != e`.                            `(5)`

This canonical construction proves pairwise noncompression without the all-depth surjectivity theorem. Its only nonformal scientific parent is generic order-one elliptic-gamma HT.

## Arbitrary single-pair realization `[PROVED ON PAPER, CONDITIONAL EXACT-IMAGE PARENT]`

Fix a pair `e` and a nonzero `D_e in Priv_e`. Define a pair-divisor family by

`D_f=0` for `f != e`.

This family satisfies every triple-compatibility law. On a triple containing `e`, the pushforward of `D_e` is zero by definition of `Priv_e`; the other two pair components are zero. On a triple not containing `e`, all three components are zero.

More generally, fix a nonzero `D_e in Priv_e` and set every other pair coordinate to zero. The exact-image theorem

`Q_d/(Q_d intersection Mer_DA) isomorphic to Comp_d`

therefore realizes this family by an element of `Q_d` modulo DA. Its pair-face signature is nonzero exactly on `e`, so it is hypertranscendental while every other pair face reports zero. This stronger statement realizes the whole private sector rather than only the canonical witness `(3)`.

## Boundary noncompression theorem `[PROVED ON PAPER, CONDITIONAL PARENT]`

For every proper subcollection `E` of the `binom(d,2)` pair faces, the restricted signature

`Q_d/(Q_d intersection Mer_DA) -> direct_sum_(e in E) A_e`

is not injective. Choose an omitted pair `e` and use the canonical carrier `(3)`; arbitrary exact-image realization is unnecessary.

Therefore every pair face is necessary. No terminal residue, spanning tree, selected atlas, or other proper deletion of the pair-face coordinates can classify differential algebraicity throughout `Q_d`.

This no-go has a positive exact replacement: all pair faces suffice, triple compatibility is the only gluing law, and every pair contributes a canonical nonzero private sector.

## Direct-sum private field `[PROVED ON PAPER, CONDITIONAL EXACT-IMAGE PARENT]`

Setting all nonmatching pair coordinates to zero gives a canonical inclusion

`direct_sum_(|e|=2) Priv_e -> Comp_d isomorphic to Q_d/(Q_d intersection Mer_DA)`.   `(3)`

Every nonzero vector in this direct sum is an HT class. Hence the universal mixed-constraint quotient contains `binom(d,2)` independently addressable pair sectors. Increasing ambient constraint depth creates new pair-labelled sectors and increases their transverse concealment order, but introduces no new local atom beyond the triptic rank-two class.

## Foundational interpretation

The joint theorem with the all-depth pair-face realization result gives an exact structural law:

1. **locality dimension two:** every finite mixed-constraint HT class is determined by rank-two faces;
2. **gluing dimension three:** equality after pushforward on every triple is necessary and sufficient;
3. **noncompression:** every pair coordinate is indispensable;
4. **thin-boundary concentration:** a private mode is supported on one pair and hidden transversely by exactly `d-2` augmentation factors.

Thus the higher object is neither a scalar charge nor a temporal flow. It is a noncompressible compatible boundary field on the complete `2`-skeleton. Hypertranscendence in this class is unbounded algebraic capacity stored in pair-local charges whose transverse concealment depth grows with the ambient constraint.

## Anti-theatre and significance gate

The Laurent-product identity alone is elementary `[BRIDGE]`. The candidate scientific theorem is the analytic conjunction of exact realization with pair-private noncompression: actual meromorphic HT functions exist with precisely one visible pair face, every pair is necessary, and the complete boundary field is simultaneously `2`-local and irreducible.

This is stronger than a new criterion for one special function. It determines the minimal information architecture of the entire generic mixed-constraint quotient. It should be presented as a central theorem of the all-depth pair-face paper, not as a standalone paper until the depth-two analytic parent and external priority have independent audits.

## External novelty boundary

- Panorbital residues classify summability for one translation on one elliptic curve. They do not construct compatible data across distinct triptic faces or private HT sectors.
- Parameterized difference Galois theory supplies hypertranscendence and telescoping mechanisms for difference equations, not this all-depth boundary realization or its minimality.
- Multivariate rational summability uses orbital decompositions and several shifts in several variables, but not one meromorphic variable with noncommensurable dense periods, differential-algebraic quotients, or pair-private elliptic sectors.
- The elliptic-gamma gerbe and higher geometric elliptic-gamma families supply cocycles and modular coboundaries, not DA/HT completeness, minimal pair observability, or exact transverse concealment order.

Exact, stronger, equivalent, mechanism, and parent-field searches through 2026 located no theorem asserting `(1)`--`(3)` for hypertranscendental mixed-constraint functions. Priority remains provisional pending specialist review.

## Lean formalization

`GaloisForLFunctions.HTGeometry.PairFacePrivateSector` formalizes the unconditional algebraic core on one free transverse orbit:

1. `privateSectorPolynomial_ne_zero`: the private witness is nonzero;
2. `setVariableOne_privateSectorPolynomial_eq_zero`: every transverse push kills it;
3. `privateSectorPolynomial_totalDegree`: its total augmentation degree is the size of the transverse set;
4. `privateSector_card_le_totalDegree_of_dvd`: every nonzero charge divisible by the private product has at least that degree;
5. `pairPrivateWitness_exact`: a pair-private witness has exact degree `d-2`;
6. `pairPrivateWitness_coordinates`: its chosen pair coordinate is unchanged and every other pair coordinate is zero;
7. `pairPrivateWitness_linearIndependent`: the canonical witnesses over all two-element faces are
   linearly independent, by projecting a relation to each private pair coordinate;
8. `pairFaceIndex_card` and `pairPrivateWitness_span_finrank`: the pair index has cardinality
   `choose(d,2)` and the span of the private witnesses has exactly that dimension.

Together with `TelescopeIdeal.iInf_span_singleton_eq_span_prod_of_primes`, this gives the exact private-sector order on each free Laurent orbit. The module was checked directly and by the one cached exact-module build; the formal lint gate passes.

The new linear-independence theorem is the unconditional algebraic direct-sum injection underlying
the card's pair-private field.  The remaining gap is not finite coordinate algebra: it is the
meromorphic exact-image theorem that realizes those independent polynomial coordinates as actual
HT classes.

Do not pretend that this formalizes meromorphic principal-part realization or triptic DA-completeness. Those remain explicit analytic parents.

## Gates

- [x] private pair sector defined
- [x] exact private-sector identity proved
- [x] nonzero private witness proved
- [x] exact transverse order `d-2` proved on paper
- [x] singleton pair family proved triple-compatible
- [x] canonical single-pair carrier constructed directly from the multiple-gamma hierarchy
- [x] canonical carrier's target and off-target signatures computed
- [x] canonical carrier's HT status reduced only to the order-one atomic theorem
- [x] arbitrary private-sector realization reduced to the exact-image parent
- [x] every proper pair-face deletion proved incomplete
- [x] direct-sum private field embedded
- [x] positive theorem paired with the noncompression no-go
- [x] preliminary external parent and novelty attack
- [x] unconditional algebraic core formalized in Lean
- [x] canonical pair-private witness family proved linearly independent in Lean
- [x] exact `choose(d,2)` algebraic private-sector rank formalized in Lean
- [ ] independent audit of the depth-two analytic parent
- [ ] independent specialist proof and priority audit
