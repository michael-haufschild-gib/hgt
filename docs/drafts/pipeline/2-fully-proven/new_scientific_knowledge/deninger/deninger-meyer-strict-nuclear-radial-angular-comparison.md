# Deninger--Meyer strict nuclear radial--angular comparison

- **ID:** `deninger-meyer-strict-nuclear-radial-angular-comparison`
- **Stage:** 2-fully-proven
- **Type:** SOURCE TOPOLOGICAL COMPARISON THEOREM
- **Labels:** `DAC_MEYER_NUCLEAR_RADIAL_STRICTNESS`,
  `DAC_HILBERT_KUMMER_STRICT_ANGULAR_COSHEAF_CONTRACTION`
- **Parent:** `deninger-poisson-relevant-complex-comparison`
- **Statement:** Meyer's Poisson complex is a strict complex of
  nuclear Fréchet spaces, remains strict after tensoring with the
  finite-stage Tate--Milnor coefficient and passing to its strict
  pro-Ind limit, and the Hilbert--Kummer modulus angle contracts by an
  explicit topological chain homotopy without contracting the unitary
  phase.

## 1. Radial nuclear spaces

Write
\[
 \mathcal H_-
 =
 \bigcap_{s\in\mathbb R}
 \mathcal S(\mathbb R_{>0}^{\times})_s,
 \qquad
 \mathcal S(\mathbb R_{>0}^{\times})_s
 =
 \{f:x^sf(x)\in\mathcal S(\mathbb R_{>0}^{\times})\}.
                                                                    \tag{1}
\]
It is enough to intersect over \(s\in\mathbb Z\).  Let
\[
 \mathcal H_\cap
 =
 \{f\in\mathcal S(\mathbb R):
 f(-x)=f(x),\ f(0)=\widehat f(0)=0\}.                              \tag{2}
\]

`[PROVED HERE] [DAC_MEYER_NUCLEAR_RADIAL_STRICTNESS]`

Both `(1)` and `(2)` are nuclear Fréchet spaces.  The Poisson operator
\[
 Z:\mathcal H_\cap\longrightarrow\mathcal H_-,
 \qquad
 Zf(x)=\sum_{n\geq1}f(nx),                                       \tag{3}
\]
is a strict closed embedding.  Consequently
\[
 0\longrightarrow\mathcal H_\cap
 \xrightarrow{Z}\mathcal H_-
 \longrightarrow M_\zeta
 \longrightarrow0                                                \tag{4}
\]
is a strict exact sequence of nuclear Fréchet spaces.

### Proof

The even Schwartz space is a closed subspace of
\(\mathcal S(\mathbb R)\), and `(2)` is the common kernel of two
continuous functionals.  Hence `(2)` is nuclear Fréchet.

Exhausting the weights in `(1)` by the intervals \([-m,m]\) realizes
\(\mathcal H_-\) as the countable projective limit of the nuclear
Fréchet spaces
\[
 \mathcal S(\mathbb R_{>0}^{\times})_{[-m,m]}.
\]
Equivalently it is the closed compatibility subspace of the product
of the integer-weight Schwartz spaces.  Countable products and closed
subspaces of nuclear Fréchet spaces are nuclear Fréchet.

Meyer's zeta estimate and Poisson summation theorem prove that `(3)`
is continuous, has closed range, and is a topological isomorphism
onto its range.  The quotient in `(4)` is therefore Fréchet and
nuclear.

This proof also fixes the support convention.  \(\mathcal H_-\) is
not \(C_c^\infty(\mathbb R_{>0})\); in logarithmic coordinates it is
the nuclear Fréchet space of smooth functions decaying faster than
every exponential at both ends.  Compactly supported smooth functions
form a dense core.

## 2. Strict tensor transport

Let \(E_\nu^\bullet\) be a finite pro-Stein character-lattice and
finite relative Tate--Milnor cell stage.  Every term is a nuclear
Fréchet space: coherent finite-rank analytic pieces over a Stein torus
are nuclear, and finite cones, kernels, quotients, and sums preserve
nuclearity.

Grothendieck exactness for completed projective tensor product with a
nuclear Fréchet space applied degreewise to `(4)` gives
\[
 0\to
 E_\nu^\bullet\widehat\otimes_\pi\mathcal H_\cap
 \xrightarrow{1\widehat\otimes Z}
 E_\nu^\bullet\widehat\otimes_\pi\mathcal H_-
 \to
 E_\nu^\bullet\widehat\otimes_\pi M_\zeta
 \to0                                                           \tag{5}
\]
as a strict exact sequence of complexes.

The pro-Stein Tate--Milnor coefficient is the strict filtered union of
these finite stages in each fixed bidegree.  Filtered colimits of
complex vector spaces are exact, and the topology is the final strict
pro-Ind topology.  Passing `(5)` through the stages therefore gives
the same strict sequence for the full phase coefficient
\(E_{\mathrm{phase}}^\bullet\).

The mixed \(L^1/L^2\) Kummer maps and the nuclear test-space maps are
continuous on every finite stage, hence on the final topology.
Density survives completed tensoring because the algebraic tensor of
dense subspaces is dense.  For the all-prime residue graph no general
tensor-flatness claim is needed:
`DAC_STRICT_PRO_LOG_COLLAR_SECTION` and
`DAC_COMPLETED_ARAKELOV_TRACE_KERNEL` give split strict boundary
sequences, and completed projective tensor product preserves an
explicit continuous splitting.  Thus `(5)` is compatible with:

1. the nuclear Kummer test topology;
2. the mixed \(L^1/L^2\) completion;
3. the completed finite-residue graph;
4. the real homology-current boundary;
5. the two endpoint functionals.

The dilation flow is continuous on `(1)`--`(2)`.  Meyer's theorem,
not a formal interchange of an infinite sum, defines `(3)` in these
topologies.  Deninger's identity
\[
 [F_nP,u]=[P,nu]=\phi^{\log n}[P,u]
\]
then identifies each summand with the corresponding source flow
pullback.

## 3. Angular cosheaf contraction

Let \(H=H_{\mathrm{Kum}}\) and \(S(H)\) be its unit sphere.  Use the
augmented topological singular-chain cosheaf
\[
 \epsilon:C_\bullet^{\mathrm{top}}(S(H))\longrightarrow\mathbb R,
                                                                    \tag{6}
\]
where each chain space has the free locally convex direct-sum topology
on singular simplices.  A continuous map or homotopy induces a
continuous chain map or prism operator.

The explicit contraction in
`DAC_DENINGER_HILBERT_KUMMER_POLAR_ANGULAR_CONTRACTION` gives a
continuous prism homotopy
\[
 \operatorname{id}
 \simeq
 \iota\epsilon                                                   \tag{7}
\]
for a chosen point inclusion \(\iota\).  Hence `(6)` is a split
chain-homotopy equivalence in complete locally convex complexes.

`[PROVED HERE]
[DAC_HILBERT_KUMMER_STRICT_ANGULAR_COSHEAF_CONTRACTION]`

For every complete phase/radial complex \(A^\bullet\), functoriality of
completed projective tensor product extends `(7)` to
\[
 C_\bullet^{\mathrm{top}}(S(H))
 \widehat\otimes_\pi A^\bullet
 \simeq
 A^\bullet.                                                       \tag{8}
\]
This is a continuous chain-homotopy equivalence, so it is stronger
than a bare cohomology isomorphism and remains valid for the nuclear,
mixed, residue-graph, and endpoint topologies above.

The positive rational flow multiplies \(h\in H\) by a positive scalar
and therefore fixes \(h/\|h\|\).  Thus `(8)` commutes with every
Poisson dilation and with their already-defined sum `(3)`.

For compact Galois descent, the augmentation `(6)` is equivariant even
though the chosen contraction need not be.  Continuous invariants are
exact on the complete coefficient modules used here by normalized
Haar averaging.  Applying invariants to `(6)` therefore preserves its
strict quasi-isomorphism.

## 4. Apex and unitary phase

The polar product is
\[
 X_{\mathrm{unit}}\times S(H)\times\mathbb R_{>0}.
\]
Only \(S(H)\) is contracted.  Fibrewise adjoining \(h=0\) forms the
cone on \(S(H)\), so `(8)` extends to
\[
 X_{\mathrm{unit}}\times H
 \rightsquigarrow
 X_{\mathrm{unit}}\times\mathbb R_{\geq0}.                        \tag{9}
\]
The unitary character factor remains the Tate--Milnor phase
coefficient at every radius, including zero.

On the radial Schwartz domain,
`DAC_RADIAL_KAHLER_ENDPOINT_FOURIER_TRACE` identifies the two relative
boundary maps as
\[
 f\longmapsto f(0),
 \qquad
 f\longmapsto\frac{\pi}{2}\widehat f(0).                          \tag{10}
\]
Therefore the relative common kernel is exactly
\(\mathcal H_\cap\).  No angular class and no extra “Fourier boundary
point” survives.

## 5. Arithmetic consequence

The Hilbert--Kummer bounded locus is used as its own fine ringed
source, with the continuous map to Deninger's pointwise coarse
approximation.  Sheafification means derived pushforward along this
map; boundedness need not be a local property of the coarse topology.

Equations `(5)`--`(10)` close the following parts of
`DAC_DENINGER_POISSON_RELEVANT_COMPLEX_COMPARISON`:

- radial nuclear sheaf/cosheaf topology;
- strictness and closed range of the Poisson differential;
- compatibility with mixed Kummer and completed residue topologies;
- strict angular contraction after retaining the phase coefficient;
- correct treatment of the unitary apex and both endpoint maps.

The remaining comparison is arithmetic gluing: identify the
finite-residue/real-boundary totalization of the intrinsic source
middle complex with `(4)`, and prove cup/trace compatibility.

## Hostile audit

- Ordinary contractibility alone is not used to preserve completed
  tensors; the continuous prism homotopy `(7)` supplies explicit
  splittings.
- No Haar probability measure on the infinite-dimensional sphere is
  asserted.
- No compact support is imposed in the angular direction.
- The phase factor is not contracted.
- Meyer's closed-range theorem supplies the infinite Poisson sum; no
  unjustified termwise convergence in a new topology is asserted.
- No zeta zero, spectral divisor, Weil positivity, RH, CCM object, or
  numerical computation enters the construction.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*, especially Theorem 4.1:
  https://arxiv.org/abs/math/0412277.
- Alexander Grothendieck, *Résumé des résultats essentiels dans la
  théorie des produits tensoriels topologiques et des espaces
  nucléaires*, Ann. Inst. Fourier 4 (1952), 73--112:
  https://doi.org/10.5802/aif.46.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  §6 and §12: https://arxiv.org/abs/1807.06400.

## Log

- 2026-07-27 — Proved nuclearity and strict tensor stability of
  Meyer's Poisson complex and upgraded Hilbert--Kummer angular
  contractibility to an explicit strict cosheaf chain contraction.

## Lean status

### What landed

`formal/GaloisForLFunctions/RHTower/DeningerMeyerRadialEndpoints.lean`, 16 declarations, axiom
audit for every one of them: `propext, Classical.choice, Quot.sound`.

**`(2)` and `(10)`, Meyer's space and the two endpoint functionals.**  mathlib has the Schwartz
space and the Fourier transform on it, so this part of the card is buildable on the actual
objects rather than on a shadow.

- `deningerSchwartzEval` — **evaluation of a Schwartz function as a continuous functional**, built
  through the bounded-continuous-function realization; `deningerFourierEval` — evaluation of the
  Fourier transform at the origin, likewise continuous.  These are the two boundary maps `(10)`.
- `deningerEvenSchwartz`, `_mem_iff`, `_isClosed` — the even Schwartz functions, cut out as the
  intersection over all `x` of the kernels of `f ↦ f(-x) - f(x)`, hence closed.
- `DeningerMeyerCap`, `deningerMeyerCap_mem_iff` — **`(2)`**: `ℋ_∩` is exactly the even Schwartz
  functions with `f(0) = 0` and `f̂(0) = 0`.
- `deningerMeyerCap_isClosed` — **`ℋ_∩` is a closed subspace of the Schwartz space**, which is the
  card's own argument that it is "the common kernel of two continuous functionals" inside the
  closed even subspace.  This is the whole content of `(2)` that does not mention nuclearity.
- `deningerFourierEndpoint`, `_ker`, `deningerMeyerCap_eq_endpoints` — **§4's conclusion**: the
  normalization `π/2` of the second endpoint map does not change the subspace it cuts out, so the
  relative common kernel of the two boundary maps of `(10)` is exactly `ℋ_∩` and no extra Fourier
  boundary point survives.

**Two structural ingredients.**

- `deningerIInf_real_eq_int` — **"it is enough to intersect over `s ∈ ℤ`"** in `(1)`: if every real
  weight is dominated by its two neighbouring integer weights, the real-indexed intersection equals
  the integer-indexed one.
- `deningerNormalize_smul` — **the positive rational flow fixes `h/‖h‖`**, the sentence in §3 that
  makes `(8)` commute with every Poisson dilation.

### What cannot be stated in Lean, and why *(superseded 2026-08-02 — see the sections below:*
*the corpus now owns nuclear locally convex spaces, `𝒮(ℝ)` is proved nuclear, and `(1)` and `(2)`*
*are proved nuclear.  Only the strictness/closed-range claims of `(3)`–`(4)` and §3's topological*
*chain cosheaf are still open.)*

Every claim of this card that contains the word *nuclear*, *Fréchet* or *strict* is out of reach,
and so is the Poisson operator itself:

- mathlib has no locally convex spaces beyond normed spaces, hence no nuclear spaces, no Fréchet
  spaces as a class, no strict morphisms, no strict exact sequences and no completed projective
  tensor product.  So `(1)`'s nuclear Fréchet structure, the strictness and closed range of `(3)`,
  the strict exact sequence `(4)`, the tensor transport `(5)` and the tensored contraction `(8)`
  cannot be written down.
- `𝓗_-`, the intersection of the weighted Schwartz spaces on `ℝ_{>0}^×`, is not in mathlib: only
  the unweighted Schwartz space on a normed space is.  `deningerIInf_real_eq_int` is the
  index-reduction step of its construction, stated for an arbitrary family of subspaces.
- §3's cosheaf of topological singular chains with the free locally convex direct-sum topology, and
  the continuous prism homotopy `(7)`, need locally convex direct sums and a topological singular
  chain complex; mathlib has neither.

So the card stays at stage 2.  What is formalized is the part of the theorem that lives inside the
Schwartz space: the two endpoint functionals of `(10)`, the identification of `ℋ_∩` as their common
kernel among even functions, its closedness, the irrelevance of the `π/2` normalization, and the
two structural lemmas used in `(1)` and §3.

### Log

- 2026-08-02 — Formalized `(2)` and `(10)` on mathlib's Schwartz space, together with the
  integer-weight reduction of `(1)` and the flow-invariance of the normalization used in §3.

### Nuclear operators, built

The blocker recorded above says nuclearity cannot be stated because mathlib has no nuclear space
theory.  The first missing piece is now built:
`formal/GaloisForLFunctions/RHTower/DeningerNuclearOperator.lean` (11 declarations, axiom audit
`propext, Classical.choice, Quot.sound` throughout) defines nuclear *operators* between normed
spaces, which mathlib does not have in any form.

- `DeningerIsNuclear T` — `T` is a sum of rank-one maps `x ↦ φ_i(x) • y_i` with `∑ ‖φ_i‖‖y_i‖`
  summable.  The index type is arbitrary, which is equivalent to the usual sequential definition
  because a summable family has countable support, and makes the ideal proofs direct.
- `deningerIsNuclear_zero`, `deningerIsNuclear_smulRight`, `DeningerIsNuclear.add`, `.smul` — the
  nuclear maps form a submodule containing the rank-one maps.
- `DeningerIsNuclear.compL`, `.compR` — **nuclear maps are a two-sided ideal**: composing with any
  bounded map on either side preserves nuclearity.
- `DeningerIsNuclear.hasSum_smulRight` — **a nuclear map is the sum of its rank-one terms in the
  operator norm**, not merely pointwise; and `.norm_le` bounds the operator norm by the nuclear
  sum `∑ ‖φ_i‖‖y_i‖`.
- `deningerSmulRight_isCompactOperator`, `DeningerIsNuclear.isCompactOperator` — **a nuclear map
  is compact**, obtained by exhibiting it as an operator-norm limit of finite sums of rank-one
  maps, each compact because the image of a ball lies in the image of a compact ball of scalars
  under scaling by a fixed vector.

This is the operator-level half of nuclearity.  What still does not exist is the space-level
notion: a locally convex space is nuclear when for every continuous seminorm there is a dominating
one whose induced map between the associated normed quotients is nuclear.  mathlib has
`LocallyConvexSpace` and `WithSeminorms` but no seminormed quotients and no completed projective
tensor product, so the LF and Fréchet claims of this card remain out of reach; the operator input
they rest on is now available.

- 2026-08-02 — Built nuclear operators between normed spaces, the operator-level half of the
  nuclearity gate.

### Nuclear spaces, defined

The space-level half is now built too:
`formal/GaloisForLFunctions/RHTower/DeningerSeminormQuotient.lean` (19 declarations, axiom audit
`propext, Classical.choice, Quot.sound` throughout).  mathlib has `Seminorm`, `WithSeminorms` and
`LocallyConvexSpace`, but it has no normed space attached to a seminorm, so the definition of a
nuclear space could not even be written; that gap is closed.

- `deningerSeminormKer` — the kernel of a seminorm as a submodule, and
  `deningerSeminorm_eq_of_sub_mem`: a seminorm is constant on its cosets.
- `DeningerSeminormSpace p` — **the normed space attached to a seminorm**, the quotient by the
  kernel, with its `NormedAddCommGroup` and `NormedSpace` instances built from an `AddGroupNorm`
  so that no competing norm is introduced.  `deningerSeminormMk_norm` says the norm of a class is
  the seminorm of a representative, by definition.
- `deningerSeminormComparison` — **the comparison map** induced by a domination `p ≤ C q`, with
  `_norm_le` bounding its operator norm by `C`.
- `DeningerIsNuclearSpace P` — **a nuclear locally convex space**: every defining seminorm is
  dominated by one whose comparison map is a nuclear operator, in the sense of
  `DeningerNuclearOperator`.
- `deningerIsNuclear_of_finiteDimensional` — **a map out of a finite-dimensional space is
  nuclear**, expanded over `Module.finBasis` as a finite sum of rank-one maps; hence
  `deningerIsNuclearSpace_of_finiteDimensional`: a space whose seminorm quotients are finite
  dimensional is nuclear.  That is exactly the card's "each finite stage is finite-dimensional and
  nuclear".

What remains between this and the card's claims is the permanence theory — closed subspaces,
countable products and projective limits of nuclear spaces are nuclear — and the completed
projective tensor product, neither of which exists yet.

- 2026-08-02 — Built the normed space attached to a seminorm and the definition of a nuclear
  space, with the finite-dimensional case proved.

### Nuclearity is independent of the defining family

`formal/GaloisForLFunctions/RHTower/DeningerNuclearSpaceInvariance.lean` (7 declarations, axiom
audit `propext, Classical.choice, Quot.sound` throughout) makes the definition usable by proving
it is an invariant of the topology rather than of the chosen seminorms.

- `deningerSeminormComparison_ext` — a map out of a seminorm quotient is determined by its effect
  on classes of vectors; `_congr` — the comparison map does not depend on the domination constant;
  `_trans` — a chain of dominations gives the composite of the comparison maps.
- `deningerIsNuclearSpace_of_dominating` — **if two seminorm families dominate each other, one is
  nuclear exactly when the other is.**  A comparison map of the second family factors as
  `bounded ∘ nuclear ∘ bounded` through a comparison map of the first, and the ideal property of
  nuclear operators finishes it.
- `deningerIsNuclearSpace_comp` — **nuclearity may be tested on a cofinal subfamily**, the
  nuclearity counterpart of the statement that the test topology does not depend on the chosen
  cofinal exhaustion.

- 2026-08-02 — Proved that nuclearity does not depend on the defining seminorm family and may
  be tested on a cofinal subfamily.

### Bridge to the corpus trace-class theory

`formal/GaloisForLFunctions/RHTower/DeningerNuclearSchattenBridge.lean` (2 declarations, axiom
audit `propext, Classical.choice, Quot.sound`) connects the new general notion to the Schatten
machinery the corpus already owns.

- `deningerSmulRight_hasRankLE_one` — a rank-one map has rank at most one in the
  approximation-number sense, its image lying in the line spanned by its vector.
- `DeningerIsNuclear.memSchattenClass_one` — **a nuclear operator on a Hilbert space is trace
  class**.  The operator-norm expansion `DeningerIsNuclear.hasSum_smulRight` is exactly the
  hypothesis of the corpus criterion `memSchattenClass_one_tsum_rankOneTerms_of_summable_norm`,
  which takes an arbitrary index type and needs no enumeration.

So on Hilbert spaces the general definition agrees with the corpus trace class, and the trace
norm, the ideal bounds and the additivity of the Schatten 1-class are available to it.

- 2026-08-02 — Bridged nuclear operators to the corpus Schatten 1-class on Hilbert spaces.

### Products of nuclear spaces

`formal/GaloisForLFunctions/RHTower/DeningerNuclearProduct.lean` (12 declarations, axiom audit
`propext, Classical.choice, Quot.sound` throughout) proves the first permanence property.

- `deningerSeminormInduced` — **the map of normed spaces induced by a bounded linear map**, a
  linear map carrying one seminorm into a multiple of another.  The comparison map of two
  seminorms on one space is the case of the identity; the coordinate projections and the
  coordinate inclusions of a product are the other cases.
- `DeningerIsNuclear.sum` — a finite sum of nuclear maps is nuclear.
- `deningerPiSeminorm`, `deningerPiFamily` — the product presented by the seminorms that add
  finitely many coordinate seminorms, with `_proj_le` and `_single_eq_of_mem` relating it to the
  coordinates.
- `deningerIsNuclearSpace_pi` — **an arbitrary product of nuclear spaces is nuclear**, in
  particular a countable product.  The comparison map of two product seminorms is shown to be the
  finite sum, over the coordinates involved, of the coordinate comparison maps conjugated by the
  projection and the inclusion; each summand is nuclear by the ideal property and the sum by
  `DeningerIsNuclear.sum`.  The identification of that sum with the honest comparison map is the
  observation that a vector and the sum of its coordinate components differ by something the
  product seminorm does not see.

What is still missing for the cards is the other permanence property, closed subspaces.  That one
is not a formal consequence of the ideal property: the vectors of a nuclear representation of a
comparison map need not lie in the subspace, and the classical proof goes through the
Hilbert--Schmidt characterization, where subspaces are complemented.

- 2026-08-02 — Proved that products of nuclear spaces are nuclear.

### Hilbert--Schmidt composites are nuclear

`formal/GaloisForLFunctions/RHTower/DeningerHilbertSchmidtNuclear.lean` (4 declarations, axiom
audit `propext, Classical.choice, Quot.sound` throughout) supplies the bridge on which the
remaining permanence theory rests.

- `DeningerIsHilbertSchmidtOn` — the Hilbert--Schmidt condition relative to a Hilbert basis: the
  images of the basis vectors are square-summable.
- `deningerSummable_mul_of_sq` — a product of square-summable nonnegative families is summable, by
  the arithmetic-geometric mean inequality.  Only summability is needed, so no Cauchy--Schwarz.
- `deningerIsNuclear_comp_of_hilbertSchmidt` — **a composite of Hilbert--Schmidt maps is
  nuclear**.  Expanding a vector in a Hilbert basis `c` of the middle space writes
  `B (A x) = ∑ⱼ ⟨A* cⱼ, x⟩ · B cⱼ`, so the rank-one data is the adjoint of the first factor against
  the images of the second, and the norms `‖A* cⱼ‖ ‖B cⱼ‖` are summable by the previous lemma.
- `deningerMemSchattenClass_one_comp_of_hilbertSchmidt` — the same statement in the corpus
  Schatten language: a composite of Hilbert--Schmidt operators is trace class.

This is the classical route to the permanence properties that remain: subspaces of nuclear spaces
are nuclear because a nuclear map factors through Hilbert spaces, where subspaces are complemented
by orthogonal projection.  Still to build for that: the Hilbertian-seminorm refinement of a
nuclear space, and the converse factorization of a nuclear map through Hilbert--Schmidt maps.

- 2026-08-02 — Proved that a composite of Hilbert--Schmidt maps is nuclear.

### Parseval, and the Hilbert--Schmidt condition is intrinsic

`formal/GaloisForLFunctions/RHTower/DeningerHilbertSchmidtAdjoint.lean` (7 declarations, axiom
audit `propext, Classical.choice, Quot.sound` throughout) removes the basis from the previous
module's hypothesis.

- `deningerParseval_summable`, `deningerParseval` — **Parseval for a Hilbert basis**: the
  coefficients of a vector are square-summable with sum the squared norm.  mathlib has the
  Hilbert-basis isometry onto `ℓ²` but not this identity; it is read off from
  `lp.norm_rpow_eq_tsum` and `Memℓp.summable`.
- `deningerHilbertSchmidt_tsum_eq_adjoint` — **the Hilbert--Schmidt sum of a map equals that of
  its adjoint**.  Both are the sum of the squared absolute values of the matrix coefficients, in
  the two possible orders; the exchange is `ENNReal.tsum_comm`, which needs no summability
  hypothesis, so the statement is unconditional and holds with both sides infinite.
- `deningerIsHilbertSchmidtOn_adjoint_iff`, `deningerIsHilbertSchmidtOn_basis_independent` — the
  Hilbert--Schmidt condition transfers to the adjoint and **does not depend on the chosen basis**,
  so it is a property of the map alone.

Together with the previous module this gives the classical statement "a composite of
Hilbert--Schmidt maps is nuclear" with Hilbert--Schmidt in its usual, intrinsic sense.

- 2026-08-02 — Proved Parseval and the basis-independence of the Hilbert--Schmidt condition.

### Nuclear implies Hilbert--Schmidt

`formal/GaloisForLFunctions/RHTower/DeningerNuclearHilbertSchmidt.lean` (2 declarations, axiom
audit `propext, Classical.choice, Quot.sound`) closes the converse direction on Hilbert spaces.

- `deningerInner_adjoint_comp` — pairing `T* T` against a vector gives the squared norm of its
  image.
- `DeningerIsNuclear.isHilbertSchmidtOn` — **a nuclear operator on a Hilbert space is
  Hilbert--Schmidt**.  If `T` is nuclear so is `T* T`, by the ideal property, hence it is trace
  class and compact; the corpus's Horn-type majorization `sum_norm_inner_le_traceNorm` then bounds
  every finite partial sum of `‖T bₙ‖²` by the trace norm of `T* T`, which is summability.

With the previous two modules this places the nuclear operators inside the Hilbert--Schmidt ones
on Hilbert spaces, in both directions of the classical comparison.

- 2026-08-02 — Proved that a nuclear operator on a Hilbert space is Hilbert--Schmidt.

### Finite-rank maps and the usable nuclearity criterion

`formal/GaloisForLFunctions/RHTower/DeningerNuclearFiniteRank.lean` (2 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `deningerIsNuclear_of_finiteRank` — **a map with finite-dimensional range is nuclear**.  The
  corestriction to the range, expanded over a basis of the range, is a finite sum of rank-one
  maps.  This is the complement of the earlier finite-dimensional-source case: there the basis is
  taken upstairs, here downstairs.
- `deningerIsNuclearSpace_of_finiteRank` — **a space whose comparison maps have finite rank is
  nuclear**.  This is the criterion one actually applies: no nuclear representation need be
  exhibited, only a dominating seminorm whose comparison map has finite-dimensional range.  It
  covers the finite stages of a test space directly, without passing through finite
  dimensionality of the whole stage.

- 2026-08-02 — Proved that finite-rank maps are nuclear, giving the finite-rank criterion for
  nuclear spaces.

### Nuclearity passes to the completions

`formal/GaloisForLFunctions/RHTower/DeningerNuclearCompletion.lean` (4 declarations, axiom audit
`propext, Classical.choice, Quot.sound` throughout).

- `deningerCompletionFunctional`, `_coe`, `_norm_le` — **the extension of a continuous functional
  to the completion**, agreeing with the original on the image and with no larger norm.
- `DeningerIsNuclear.exists_completion` — **a nuclear map extends to a nuclear map of the
  completions**, agreeing with the original on the image of the source.

The extension is built rather than characterized: the functionals of a nuclear representation are
extended, the vectors are pushed into the completion of the target, and the resulting rank-one
family — whose norms are still summable, since extension does not increase functional norms — is
summed in the operator norm.  The extension is therefore nuclear by construction, which avoids
having to re-prove nuclearity for a map obtained by an abstract extension theorem.

This is the step that makes nuclearity of a locally convex space a statement about the *completed*
seminorm quotients, which is the classical definition and the one the permanence theory for closed
subspaces is formulated against.

- 2026-08-02 — Proved that a nuclear map extends to a nuclear map of completions.

### Subspaces, and the exact point where they are not formal

`formal/GaloisForLFunctions/RHTower/DeningerNuclearSubspace.lean` (6 declarations, axiom audit
`propext, Classical.choice, Quot.sound` throughout).

- `DeningerIsNuclear.of_comp_left_inverse` — if the left factor of a nuclear composite has a
  bounded left inverse, the right factor is nuclear.
- `deningerRestrictSeminorm`, `deningerSubspaceEmbedding` — the restriction of a seminorm to a
  subspace, and the induced embedding of quotients, which is isometric because the subspace
  seminorm *is* the restriction.
- `deningerIsNuclearSpace_subspace_of_leftInverse` — **a subspace whose quotient embeddings admit
  bounded left inverses is nuclear**.  The subspace comparison map followed by the embedding equals
  the ambient comparison map preceded by the embedding, which is nuclear by the ideal property;
  the left inverse brings it back.

This isolates the remaining analytic input precisely.  Everything about subspaces is now formal
*except* the complementation of the embedded quotient, and that is genuinely not formal: a nuclear
representation of the composite has its vectors in the ambient quotient, not in the subspace one.
Classically it is supplied by refining the presenting seminorms to Hilbertian ones, where a closed
subspace is complemented by orthogonal projection; that refinement is Grothendieck's factorization
of a nuclear map through a Hilbert space, and is what remains to be built.

- 2026-08-02 — Proved subspace permanence modulo complementation of the quotient embeddings,
  isolating the one remaining analytic input.

### Balancing a nuclear representation

`formal/GaloisForLFunctions/RHTower/DeningerNuclearBalanced.lean` (2 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `DeningerIsNuclear.exists_balanced` — **a nuclear map has a representation in which every
  functional has the same norm as its vector**.  Each rank-one term is rescaled by a real scalar
  and its reciprocal, which changes neither the term nor the product of the two norms; terms where
  one factor vanishes are replaced by zero.
- `DeningerIsNuclear.exists_balanced_summable_sq` — in such a representation the *squares* of the
  functional norms are summable, since they are the terms of the original convergent series.

This is the normalization step of the factorization of a nuclear map through a Hilbert space: with
a balanced representation the coefficient map `x ↦ (φₐ x)ₐ` lands in `ℓ²` with norm at most
`(∑ ‖φₐ‖²)^{1/2} ‖x‖`, and the map is dominated by the resulting Hilbertian seminorm.

The rescaling needs real scalars to act, so it is stated over `RCLike` fields.  That is not an
artefact: over a field whose value group is discrete the norms of scalars cannot be adjusted
continuously, and exact balancing genuinely fails.

- 2026-08-02 — Proved that a nuclear representation can be balanced, with square-summable
  functional norms.

### The Hilbertian domination of a nuclear map

`formal/GaloisForLFunctions/RHTower/DeningerNuclearHilbertFactor.lean` (2 declarations, axiom
audit `propext, Classical.choice, Quot.sound`).

- `deningerTsum_mul_le_sqrt` — **Cauchy--Schwarz for sums**: for nonnegative square-summable
  families, `∑ f g ≤ (∑ f²)^{1/2} (∑ g²)^{1/2}`.  mathlib has the finite version
  `Finset.sum_mul_sq_le_sq_mul_sq` but not the summable one; it is obtained by bounding every
  partial sum.
- `DeningerIsNuclear.exists_hilbert_factor` — **a nuclear map is dominated by a Hilbertian
  seminorm**.  From a balanced representation the coefficient map `x ↦ (φₐ x)ₐ` lands in `ℓ²`, is
  bounded by `(∑ ‖φₐ‖²)^{1/2} ‖x‖`, and dominates the map: `‖T x‖ ≤ (∑ ‖φₐ‖²)^{1/2} ‖A x‖`.

Both inequalities are what the permanence theory needs.  The first says the Hilbertian seminorm
`x ↦ ‖A x‖` is continuous, so it may be inserted into a presenting family; the second says the
original comparison map factors through it.  Iterating this refinement makes a presenting family
Hilbertian, at which point the quotients are pre-Hilbert spaces and the embedding of a subspace
quotient is complemented — the hypothesis of
`deningerIsNuclearSpace_subspace_of_leftInverse`.

- 2026-08-02 — Proved that a nuclear map is dominated by a Hilbertian seminorm, with
  Cauchy--Schwarz for summable families.

### A nuclear space is presented by Hilbertian seminorms

`formal/GaloisForLFunctions/RHTower/DeningerHilbertianRefinement.lean` (3 declarations, axiom
audit `propext, Classical.choice, Quot.sound`).

- `DeningerIsHilbertianSeminorm` — a seminorm given by the norm of a linear map into an `ℓ²`
  space.
- `deningerNuclear_hilbertian_refinement` — **every seminorm of a nuclear space is squeezed by a
  Hilbertian one**: the comparison map is dominated by the norm of its `ℓ²` coefficient map, which
  is in turn dominated by the dominating seminorm.
- `deningerNuclear_exists_hilbertian_family` — **a nuclear space has a nuclear Hilbertian
  presentation**.  Choosing one squeeze per index gives a family that mutually dominates the
  original, and nuclearity transfers by the invariance theorem.

What remains for closed subspaces is a formulation issue rather than a missing theorem.  With a
Hilbertian presentation the seminorm quotients are pre-Hilbert, and the image of a subspace
quotient inside `ℓ²` is complemented by orthogonal projection onto its *closure* — so the left
inverse required by `deningerIsNuclearSpace_subspace_of_leftInverse` exists into the completion of
the subspace quotient, not into the quotient itself.  Closing the argument therefore means
restating nuclearity against the completed quotients, for which
`DeningerIsNuclear.exists_completion` already provides the transfer of nuclear maps.

- 2026-08-02 — Proved that a nuclear space has a nuclear Hilbertian presentation.

### The completed formulation

`formal/GaloisForLFunctions/RHTower/DeningerNuclearSpaceCompleted.lean` (9 declarations, axiom
audit `propext, Classical.choice, Quot.sound` throughout).

- `DeningerSeminormCompletion`, `deningerSeminormMkC`, `_norm` — the Banach space attached to a
  seminorm, and the canonical map into it, whose norm is the seminorm.
- `deningerSeminormComparisonC`, `_coe` — **the completed comparison map**, defined as the
  extension of the composite `E_q → E_p → Ê_p` along the dense isometric embedding of `E_q`, and
  agreeing with the uncompleted comparison map on the image.
- `DeningerIsNuclearSpaceC` — **nuclearity in the classical, completed sense**.
- `DeningerIsNuclearSpace.toC` — **it follows from the uncompleted notion**.  The extension of the
  nuclear comparison map provided by `DeningerIsNuclear.exists_completion` agrees with the
  canonical completed comparison map on a dense set, hence equals it, so the canonical map is
  nuclear.

This is the formulation the closed-subspace argument is stated against: with the Hilbertian
presentation of the previous module, the completed quotients are Hilbert spaces, and the image of a
completed subspace quotient is a *closed* subspace of one, hence complemented by orthogonal
projection.

- 2026-08-02 — Built the completed formulation of nuclearity and derived it from the
  uncompleted one.

### Subspaces in the completed formulation

`formal/GaloisForLFunctions/RHTower/DeningerNuclearSubspaceCompleted.lean` (5 declarations, axiom
audit `propext, Classical.choice, Quot.sound` throughout).

- `deningerSubspaceEmbedding_square` — the comparison square of a subspace before completion.
- `deningerSubspaceEmbeddingC`, `_coe`, `_square` — **the completed embedding of a subspace
  quotient and the completed comparison square**.  Commutativity after completion is inherited:
  both composites are continuous and agree on the dense image of the uncompleted quotient.
- `deningerIsNuclearSpaceC_subspace_of_leftInverse` — **a subspace whose completed quotient
  embeddings admit bounded left inverses is nuclear in the completed sense.**

At the completed level the left-inverse hypothesis is the honest one.  With the Hilbertian
presentation the completed quotients are Hilbert spaces and the image of a completed subspace
quotient is a *closed* subspace, hence complemented by orthogonal projection — whereas before
completion only the closure of the image is complemented, which is exactly why the uncompleted
version of this theorem could not be discharged.

- 2026-08-02 — Proved completed subspace permanence modulo the complementation hypothesis,
  now stated where it is actually satisfiable.

### The `ℓ²` embedding of a Hilbertian quotient

`formal/GaloisForLFunctions/RHTower/DeningerHilbertianEmbedding.lean` (10 declarations, axiom
audit `propext, Classical.choice, Quot.sound` throughout).

- `deningerHilbertianEmbedding`, `_norm`, `_isometry` — a Hilbertian seminorm's defining map kills
  the kernel of the seminorm, so it induces an **isometric embedding of the seminorm quotient into
  `ℓ²`**.
- `deningerHilbertianEmbeddingC`, `_coe`, `_norm`, `_isometry` — the extension to the completion,
  still isometric: the two continuous functions `‖J w‖` and `‖w‖` agree on the dense image.
- `deningerHilbertianEmbeddingC_isClosed_range` — **the extended embedding has closed range**,
  since an isometry out of a complete space has complete, hence closed, range.

A closed subspace of `ℓ²` is complemented by orthogonal projection, so this is the last structural
ingredient of the bounded left inverse that
`deningerIsNuclearSpaceC_subspace_of_leftInverse` requires.

- 2026-08-02 — Built the isometric `ℓ²` embedding of a Hilbertian seminorm quotient and its
  completion, with closed range.

### Subspaces of a Hilbertian nuclear space are nuclear

`formal/GaloisForLFunctions/RHTower/DeningerNuclearSubspaceHilbertian.lean` (16 declarations,
axiom audit `propext, Classical.choice, Quot.sound` throughout).

`deningerIsNuclearSpaceC_subspace_of_hilbertian` and
`deningerIsNuclearSpace_subspace_of_hilbertian`: **a subspace of a nuclear space presented by
Hilbertian seminorms is nuclear.**  The bounded left inverse required by
`deningerIsNuclearSpaceC_subspace_of_leftInverse` is constructed rather than assumed —
`deningerSubspaceLeftInverse` composes the ambient `ℓ²` embedding, the orthogonal projection onto
the closed image `deningerSubspaceRange` of the completed subspace quotient, and the inverse
`deningerSubspaceRangeEquiv` of the corestricted isometry; the compatibility
`deningerHilbertianEmbeddingC_subspace` places the image of a subspace class inside that closed
subspace, where the projection acts as the identity.

This is the permanence property the radial–angular comparison of this card needs: the strict
inductive limit's steps are subspaces of the ambient test space, and their nuclearity no longer
has to be assumed.  It does not by itself finish the card, whose open ingredient remains the
nuclearity of the Schwartz space (the Hermite-coefficient characterisation).

- 2026-08-02 — Subspace permanence for Hilbertian nuclear spaces is unconditional in Lean.

### Permanence under subspaces, for any presentation

`formal/GaloisForLFunctions/RHTower/DeningerNuclearCompletedInvariance.lean` (6 declarations,
axiom audit `propext, Classical.choice, Quot.sound` throughout).

`deningerIsNuclearSpaceC_subspace`: **every subspace of a nuclear space is nuclear**, with no
hypothesis on the presenting family.  The Hilbertian case is transferred along the two dominations
of `deningerNuclear_exists_hilbertian_family` using
`deningerIsNuclearSpaceC_of_dominating`, itself resting on the calculus
`deningerSeminormComparisonC_ext`/`_congr`/`_trans` of completed comparison maps — proved by
density on the classes of vectors.

- 2026-08-02 — Subspace permanence holds for an arbitrary nuclear presentation.

### A nuclear space that is not finite dimensional

`formal/GaloisForLFunctions/RHTower/DeningerRapidSequenceSpace.lean` and
`.../DeningerRapidSequenceNuclear.lean` (25 declarations together, axiom audit `propext,
Classical.choice, Quot.sound`).

`deningerRapid_isNuclearSpace`: **the rapidly decreasing sequences form a nuclear space**, and
`deningerRapid_not_finiteDimensional`: it is not finite dimensional.  The comparison map between
consecutive weighted `ℓ²` seminorms is written as the series of rank one maps given by the
coordinate functionals `deningerRapidCoeff` and the basis classes, with
`‖φ_n‖ ‖[e_n]‖ ≤ (n+1)^{-2}`; the convergence statement `deningerRapid_hasSum_basis` comes from
`lp.hasSum_single` through the isometric `ℓ²` embedding of a Hilbertian quotient.

This supplies the model against which the radial–angular comparison of this card is to be
calibrated, and it makes the permanence theorems of the nuclear test scale non-vacuous: they now
have an infinite dimensional space to act on.

- 2026-08-02 — The nuclear test scale has an infinite dimensional model in Lean.

## Lean: corpus survey before starting (2026-08-02)

Survey of what the formal tree already provides for this card, so the work starts at the real gap.

Already built and usable (`formal/GaloisForLFunctions/RHTower/`):

- `DeningerNuclearOperator` — `DeningerIsNuclear` (rank-one series), sums of nuclear maps.
- `DeningerSeminormQuotient`, `DeningerNuclearSpaceCompleted` — `DeningerIsNuclearSpace`,
  `DeningerIsNuclearSpaceC` and the comparison-map presentation of nuclearity for a seminorm
  family.
- `DeningerNuclearProduct` — **`deningerIsNuclearSpace_pi`: a product of nuclear spaces is
  nuclear**, exactly the permanence the card's proof of `(1)` invokes.
- `DeningerNuclearSubspaceHilbertian`, `DeningerNuclearCompletedInvariance`,
  `DeningerFinestSubspaceNuclear` — **subspaces of nuclear spaces are nuclear**, the other
  permanence the card invokes.
- `DeningerKotheSpace` — Köthe spaces and the Grothendieck–Pietsch criterion
  (`deningerKothe_isNuclearSpace`).
- `DeningerRapidSequenceNuclear` — the space of rapidly decreasing sequences is nuclear.
- `DeningerNuclearTransport(C)` — nuclearity transports along a linear equivalence matching the
  seminorms; `DeningerTensorNuclear` — projective tensor products of nuclear spaces are nuclear.

The real gap for this card: **nuclearity of the Schwartz space itself**, which mathlib does not
have.  The route through the existing toolkit is the classical one: the Hermite coefficient map
identifies `𝒮(ℝ)` with a subspace of the rapidly decreasing sequences, matching the seminorms, so
`deningerRapid_isNuclearSpace` plus subspace permanence plus `deningerIsNuclearSpace_of_linearEquiv`
give it.  What must be built is the Hermite expansion with its two-sided seminorm estimates.

After that, `(2)` is a closed subspace (two continuous functionals) and `(1)` is a countable
product-and-subspace, both by the permanence lemmas above; then the Poisson operator `Z`, its
strictness, and the exact sequence `(4)`.

### Lean: the oscillator number operator and the decay of Hermite coefficients

`formal/GaloisForLFunctions/HTGeometry/HermiteNumberOperator.lean` (7 declarations) and
`formal/GaloisForLFunctions/HTGeometry/HermiteCoefficientDecay.lean` (3 declarations), axiom audit
`propext, Classical.choice, Quot.sound`.

The corpus already owned the oscillator algebra on `𝓢(ℝ,ℂ)` — creation and annihilation operators,
their commutator, the raising and lowering relations on the Hermite functions, the adjointness of
`A` and `B` for the bilinear pairing, and the orthonormality of the Hermite family in `L²`.  These
two modules add the piece the nuclearity argument runs on.

- `numberCLM` — the number operator `N = A B`.
- `numberCLM_hermiteSchwartz` — **the Hermite functions are its eigenfunctions with eigenvalue
  `4πn`**: `B` lowers with factor `2n`, `A` raises back with factor `2π`.
- `schwartzPair_numberCLM` — **`N` is symmetric for the bilinear pairing**, since `A` and `B` are
  adjoint to each other; hence `⟨Nᵏf, g⟩ = ⟨f, Nᵏg⟩`.
- `numberCLM_iterate_hermiteSchwartz`, `schwartzPair_hermiteSchwartz_numberCLM_iterate` — **the
  `n`-th Hermite coefficient of `Nᵏf` is `(4πn)ᵏ` times that of `f`.**
- `schwartzPair_eq_inner_toLp`, `norm_schwartzPair_hermiteSchwartz_le` — the pairing against a
  Hermite function is an `L²` inner product (the Hermite functions are real valued), so
  Cauchy–Schwarz applies.
- `schwartzPair_hermiteSchwartz_decay` — **`(4πn)ᵏ ‖⟨f, hₙ⟩‖ ≤ ‖hₙ‖₂ ‖Nᵏf‖₂`**: the Hermite
  coefficients of a Schwartz function decay faster than any power, with an explicit constant at
  every order.

Remaining chain to `𝒮(ℝ)` nuclear, in order: completeness of the Hermite system in `L²`; the
two-sided comparison between the Schwartz seminorms and the number-operator seminorms
`qₖ(f) = ‖Nᵏf‖₂` (the easy direction is a temperate-growth estimate, the other is the
one-dimensional Sobolev bound `‖g‖∞² ≤ 2‖g‖₂‖g'‖₂` plus the oscillator algebra); then transport
onto the rapidly decreasing sequence space, which the corpus already knows is nuclear, by
`deningerIsNuclearSpace_of_linearEquiv` and subspace permanence.

- 2026-08-02 — Number operator, its eigenrelation and symmetry, and the rapid decay of Hermite
  coefficients: the engine of the Schwartz nuclearity proof.

### Lean: the Hamiltonian, its seminorms, and the easy comparison

`formal/GaloisForLFunctions/HTGeometry/HermiteHamiltonian.lean` (13 declarations) and
`formal/GaloisForLFunctions/HTGeometry/HermiteOscillatorContinuity.lean` (4 declarations), axiom
audit `propext, Classical.choice, Quot.sound`.

- `schwartzPair_add_right`, `_add_left` — additivity of the bilinear pairing in each slot.
- `hamiltonianCLM`, `hamiltonianCLM_two_smul` — the **oscillator Hamiltonian** `H = A B + 2π`,
  shown to be the symmetric combination `(A B + B A)/2` by the commutation relation.
- `hamiltonianCLM_hermiteSchwartz` — **eigenvalue `2π(2n+1)`**, which never vanishes; unlike the
  number operator, the Hamiltonian gives an estimate that is meaningful at the ground state too.
- `schwartzPair_hamiltonianCLM`, `schwartzPair_hamiltonianCLM_iterate` — the Hamiltonian and all
  its powers are symmetric for the bilinear pairing.
- `hamiltonianCLM_iterate_hermiteSchwartz`, `schwartzPair_hermiteSchwartz_hamiltonian_iterate`,
  `schwartzPair_hermiteSchwartz_hamiltonian_decay` — **`(2π(2n+1))ᵏ ‖⟨f, hₙ⟩‖ ≤ ‖hₙ‖₂ ‖Hᵏf‖₂`.**
- `hamiltonianPowCLM`, `oscillatorSeminorm`, `_apply` — **the oscillator seminorms**
  `qₖ(f) = ‖Hᵏf‖₂` as `Seminorm` objects on the Schwartz space, the Hilbertian family in which the
  nuclear structure will be visible; the Hermite functions diagonalize every one of them.
- `oscillatorSeminormFamily`, `oscillatorSeminorm_continuous`,
  `oscillatorSeminorm_le_schwartzSeminorm` — **each oscillator seminorm is continuous, hence
  bounded by finitely many Schwartz seminorms** (`Seminorm.bound_of_continuous` against
  `schwartz_withSeminorms`).  That is one of the two comparisons needed to identify the oscillator
  presentation of the Schwartz topology with the standard one.

Next: the reverse comparison (a Schwartz seminorm bounded by an oscillator seminorm) and
completeness of the Hermite system in `L²`, after which the nuclearity of `𝒮(ℝ)` follows from the
corpus's Köthe/rapid-sequence nuclearity by transport.

- 2026-08-02 — Hamiltonian, its spectrum on the Hermite functions, the oscillator seminorms, and
  the easy half of the seminorm comparison.

### Lean: the Hermite polynomials span, and the vanishing of Gaussian moments

`formal/GaloisForLFunctions/HTGeometry/HermitePolynomialSpan.lean` (11 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `hermitePoly_degree_leadingCoeff`, `_degree`, `_leadingCoeff`, `_coeff_self`,
  `_coeff_eq_zero` — **the `n`-th Hermite polynomial has degree `n` and leading coefficient `2ⁿ`.**
  Each recursion step multiplies by `2X` and subtracts a multiple of the derivative, whose degree
  is strictly smaller, so the top term is untouched.
- `mem_span_hermitePoly_of_degree_lt`, `hermitePoly_span_eq_top` — **the Hermite polynomials span
  the polynomial ring**, by the triangular argument: subtracting the right multiple of the `n`-th
  Hermite polynomial lowers the degree, and one descends on the degree.
- `polyGaussSchwartz_add`, `_smul`, `polyGaussLM` — the Gaussian multiples of polynomials as an
  `ℝ`-linear map into the Schwartz space.
- `schwartzPair_polyGauss_eq_zero` — **a Schwartz function orthogonal to every Hermite function is
  orthogonal to every polynomial multiple of the Gaussian**: all of its Gaussian moments vanish.
  Proved by span induction, so it needs no coordinates.

This is the first step of the completeness of the Hermite system.  What remains for completeness:
the vanishing of all moments of the integrable function `f·e^{−πx²}` forces its Fourier transform
to vanish (its power series at the origin is identically zero and it is entire, since the Gaussian
weight makes every moment bound factorially small), and a function with vanishing Fourier transform
is zero.

- 2026-08-02 — The Hermite polynomials span; orthogonality to the Hermite family kills every
  Gaussian moment.

### Lean: vanishing moments kill every exponential integral

`formal/GaloisForLFunctions/HTGeometry/HermiteGaussianExponential.lean` (5 declarations, axiom
audit `propext, Classical.choice, Quot.sound`).

- `complex_hasSum_exp`, `real_hasSum_exp` — the exponential series in `HasSum` form, over `ℂ` and
  over `ℝ`.
- `gauss_mul_exp_abs_le` — **the Gaussian dominates every exponential**:
  `e^{−πx²}e^{|a||x|} ≤ e^{a²/π} e^{−3πx²/4}`, from `4π|a||x| ≤ 4a² + π²x²`, that is from
  `(2|a| − π|x|)² ≥ 0`.
- `integrable_gauss_mul_exp_abs` — hence the dominating function is integrable.
- `integral_gaussMul_exp_eq_zero` — **a Schwartz function orthogonal to every Hermite function
  integrates to zero against the Gaussian times any complex exponential**:
  `∫ f(x) e^{−πx²} e^{cx} dx = 0` for every `c ∈ ℂ`.  The exponential is expanded into its power
  series and integrated term by term — legitimate by dominated convergence with the bound above —
  and every term is a Gaussian moment, which vanishes by the span step.

Taking `c = −2πit` this says the Fourier transform of `f·e^{−πx²}` vanishes identically.  What
remains for completeness of the Hermite system is the Fourier uniqueness step: an integrable
continuous function whose Fourier transform vanishes is zero, whence `f = 0`.

- 2026-08-02 — Every exponential integral of a Hermite-orthogonal Schwartz function vanishes; only
  Fourier uniqueness is left before completeness.

### Lean: completeness of the Hermite system on the Schwartz space

`formal/GaloisForLFunctions/HTGeometry/HermiteCompleteness.lean` (4 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `gaussMul`, `gaussMul_apply` — the Gaussian multiple of a Schwartz function, itself Schwartz.
- `fourier_gaussMul_eq_zero` — **the Fourier transform of `f·e^{−πx²}` vanishes identically** for a
  Schwartz `f` orthogonal to every Hermite function: it is the exponential integral of the previous
  module at the imaginary exponent `c = −2πit`.
- `hermiteSchwartz_complete` — **a Schwartz function orthogonal to every Hermite function is
  zero.**  Fourier inversion (`Continuous.fourierInv_fourier_eq`) turns the vanishing transform
  into the vanishing of `f·e^{−πx²}`, and the Gaussian never vanishes.

So the Hermite coefficient map is injective on `𝒮(ℝ)`: the Hermite system is complete there.  This
was the remaining blocker; it is the injectivity the nuclearity transport consumes.

What is left for `𝒮(ℝ)` nuclear: the reverse seminorm comparison — a Schwartz seminorm bounded by
an oscillator seminorm `qₖ(f) = ‖Hᵏf‖₂` — after which the coefficient map identifies `𝒮(ℝ)` with a
subspace of the rapidly decreasing sequence space, matching the seminorms, and the corpus's
`deningerRapid_isNuclearSpace` plus subspace permanence and
`deningerIsNuclearSpace_of_linearEquiv` finish it.

- 2026-08-02 — Hermite completeness on the Schwartz space: the coefficient map is injective.

### Lean: `L²` bounds for the oscillator operators

`formal/GaloisForLFunctions/HTGeometry/SchwartzOscillatorL2Bound.lean` (12 declarations, axiom
audit `propext, Classical.choice, Quot.sound`).

The reverse seminorm comparison needs the creation and annihilation operators to be controlled in
`L²` by the number operator.  That is what this module proves, working with the corpus's
conjugation operator `SchwartzMap.conjSLM`.

- `conjSLM_conjSLM`, `schwartzPair_eq_inner`, `norm_toLp_conjSLM`, `norm_schwartzPair_le` — **the
  bilinear pairing is the `L²` inner product against the conjugate**, conjugation is an `L²`
  isometry, and hence **Cauchy–Schwarz holds for the pairing**:
  `‖⟨u, v⟩‖ ≤ ‖u‖₂‖v‖₂`.
- `norm_schwartzPair_conj_self` — the pairing of the conjugate against the function is the square
  of the `L²` norm.
- `conjSLM_derivSCLM`, `conjSLM_mulXCLM`, `conjSLM_creationCLM`, `conjSLM_annihilationCLM` —
  **conjugation commutes with all four operators** (their coefficients are real); the derivative
  case is the chain rule through the `ℝ`-linear conjugation.
- `norm_toLp_creationCLM_sq_le` — **`‖Ag‖₂² ≤ ‖g‖₂‖(N + 4π)g‖₂`**, from adjointness `⟨Ag,h⟩ =
  ⟨g,Bh⟩` and the commutation relation `B A = N + 4π`.
- `norm_toLp_annihilationCLM_sq_le` — **`‖Bg‖₂² ≤ ‖g‖₂‖Ng‖₂`**, likewise with `A B = N`.

Since `x = (A+B)/4π` and `d/dx = (B−A)/2`, iterating these two bounds controls every
`‖x^k ∂^n f‖₂` by oscillator seminorms; combined with the one-dimensional Sobolev estimate
`‖g‖∞² ≤ 2‖g‖₂‖g′‖₂` this will give the reverse comparison and finish the nuclearity of `𝒮(ℝ)`.

- 2026-08-02 — Cauchy–Schwarz for the pairing, conjugation compatibility, and the `L²` bounds for
  the creation and annihilation operators.

### Lean: the supremum bound through the Fourier transform

`formal/GaloisForLFunctions/HTGeometry/SchwartzSupL2Bound.lean` (4 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

The reverse comparison converts an `L²` bound into a bound on the Schwartz sup-seminorms.  The
route chosen avoids the fundamental theorem of calculus: it goes through the Fourier transform,
using that mathlib knows Plancherel for Schwartz functions (`SchwartzMap.norm_fourier_toL2_eq`).

- `norm_toLp_sq_eq_integral` — **`‖f‖₂² = ∫ ‖f t‖² dt`** for a Schwartz function: the `L²` inner
  product of the class with itself, computed pointwise.
- `weightSchwartz`, `_apply` — multiplication by `1 + x²` as an operator on the Schwartz space,
  the weight that will carry the `L¹`-to-`L²` step.
- `norm_apply_le_integral_norm_fourier` — **`‖f x‖ ≤ ∫ ‖𝓕 f‖`**: Fourier inversion writes the
  value as an integral of the transform against a unit complex number, whose modulus is one.

The remaining step of the reverse comparison is the weighted Cauchy–Schwarz
`∫ ‖h‖ ≤ ‖(1+t²)⁻¹‖₂ · ‖(1+t²)h‖₂` (mathlib's `integral_mul_le_Lp_mul_Lq_of_nonneg` at `p = q = 2`),
after which Plancherel turns `‖(1+t²)𝓕f‖₂` into `‖f − f''/4π²‖₂`, an oscillator seminorm.

- 2026-08-02 — `L²` norm as an integral, the quadratic weight, and the supremum bound by the `L¹`
  norm of the transform.

### Lean: the weighted Hölder step

`formal/GaloisForLFunctions/HTGeometry/SchwartzWeightedHolder.lean` (8 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `continuous_inv_one_add_sq`, `integrable_inv_one_add_sq_sq`, `memLp_inv_one_add_sq` — **the
  weight `(1+t²)⁻¹` is square integrable**, because its square is dominated by itself and
  `integrable_inv_one_add_sq` is in mathlib.
- `norm_weightSchwartz_apply`, `memLp_weight_mul_norm` — the quadratic weighting of a Schwartz
  function has pointwise norm `(1+t²)‖h t‖` and lies in `L²`.
- `integral_norm_le_weight` — **`∫‖h‖ ≤ C · ‖(1+t²)h‖₂`**, Hölder at `p = q = 2` on the splitting
  `‖h‖ = (1+t²)⁻¹ · (1+t²)‖h‖`, with `C = ‖(1+t²)⁻¹‖₂`.
- `norm_apply_le_weight_fourier` — **`‖f x‖ ≤ C · ‖(1+t²)·𝓕f‖₂`**, combining with the supremum
  bound by the `L¹` norm of the transform.

So the supremum of a Schwartz function is bounded by an `L²` norm of a quadratic weighting of its
Fourier transform.  What is left of the reverse comparison: Plancherel turns `‖(1+t²)𝓕f‖₂` into
`‖f − f''/4π²‖₂` — mathlib has `SchwartzMap.norm_fourier_toL2_eq` and the transform rules for
multiplication and differentiation are already in the corpus (`fourierSCLM_derivSCLM`,
`derivSCLM_fourierSCLM`) — and then the oscillator algebra `x = (A+B)/4π`, `d/dx = (B−A)/2`
together with the `L²` bounds of the previous module expresses that by oscillator seminorms.

- 2026-08-02 — The weighted Hölder step: supremum bounded by the weighted `L²` norm of the
  transform.

### Lean: the Sobolev estimate

`formal/GaloisForLFunctions/HTGeometry/SchwartzSobolevEstimate.lean` (7 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `sobolevOp`, `_apply` — the elliptic expression `f ↦ f − f''/4π²` as an operator on the Schwartz
  space.
- `mulXCLM_fourierSCLM` — **multiplication by the coordinate on the Fourier side is
  differentiation**: `x·𝓕f = (2πi)⁻¹𝓕(f′)`.
- `weightSchwartz_fourierSCLM` — **`(1+t²)·𝓕f = 𝓕(f − f''/4π²)`**, since `((2πi)⁻¹)² = −(4π²)⁻¹`.
- `norm_weight_fourier_toLp` — Plancherel (`SchwartzMap.norm_fourier_toL2_eq`) turns the weighted
  `L²` norm of the transform into `‖f − f''/4π²‖₂`.
- `norm_apply_le_sobolev` — **the Sobolev estimate `‖f x‖ ≤ C · ‖f − f''/4π²‖₂`**, with the
  explicit constant `‖(1+t²)⁻¹‖₂`.

This is the tool that converts the oscillator `L²` bounds into bounds on the Schwartz
sup-seminorms.  What remains of the reverse comparison is bookkeeping in the oscillator algebra:
apply the Sobolev estimate to `x^k ∂ⁿ f`, write `x = (A+B)/4π` and `∂ = (B−A)/2`, and use
`norm_toLp_creationCLM_sq_le` and `norm_toLp_annihilationCLM_sq_le` repeatedly to bound the
resulting `L²` norm by an oscillator seminorm `qₘ(f) = ‖Hᵐf‖₂`.

- 2026-08-02 — The Sobolev estimate, via the Fourier transform and Plancherel rather than the
  fundamental theorem of calculus.

### Lean: multiplication and differentiation inside the oscillator algebra

`formal/GaloisForLFunctions/HTGeometry/SchwartzOscillatorAlgebra.lean` (10 declarations, axiom
audit `propext, Classical.choice, Quot.sound`).

- `creation_add_annihilation`, `annihilation_sub_creation` — `A + B = 4π·x` and `B − A = 2·d/dx`.
- `mulXCLM_eq_oscillator`, `derivSCLM_eq_oscillator` — **multiplication by the coordinate and
  differentiation expressed in the oscillator operators**: `x = (A+B)/4π`, `d/dx = (B−A)/2`.  So
  every operator built from `x·` and `d/dx` — in particular every Schwartz seminorm's operator and
  the elliptic operator of the Sobolev estimate — is a polynomial in `A` and `B`.
- `numberCLM_creationCLM`, `numberCLM_annihilationCLM` — **the commutators `[N,A] = 4πA` and
  `[N,B] = −4πB`**, which is what lets an iterated `L²` bound be pushed back to a power of the
  number operator instead of accumulating uncontrolled terms.
- `le_half_add_of_sq_le_mul`, `norm_toLp_creationCLM_le`, `norm_toLp_annihilationCLM_le` — the
  quadratic `L²` bounds of the previous module in linear form, by the arithmetic–geometric mean
  inequality: `‖Ag‖₂ ≤ (‖g‖₂ + ‖(N+4π)g‖₂)/2` and `‖Bg‖₂ ≤ (‖g‖₂ + ‖Ng‖₂)/2`.

Everything the reverse comparison needs is now present: the Sobolev estimate converts a Schwartz
sup-seminorm into an `L²` norm of a polynomial in `A` and `B` applied to `f`, the linear bounds
strip the operators one at a time, and the commutators keep the remainder a polynomial in `N`,
that is an oscillator seminorm.

- 2026-08-02 — The oscillator algebra: `x` and `d/dx` in terms of `A` and `B`, the commutators with
  `N`, and the linear `L²` bounds.

### Lean: the shifted number operator dominates everything

`formal/GaloisForLFunctions/HTGeometry/SchwartzShiftedNumberBounds.lean` (11 declarations, axiom
audit `propext, Classical.choice, Quot.sound`).

The word induction would accumulate lower-order terms if the bounds were stated with sums of
oscillator seminorms.  They are not needed: the number operator is *nonnegative*, so a single
power of the shifted operator `K = N + 4π` dominates everything.

- `schwartzPair_conj_self`, `toLp_sub`, `toLp_smul` — the pairing of a conjugate against itself is
  the squared `L²` norm, and `toLp` is linear.
- `schwartzPair_conj_numberCLM` — **the number operator is nonnegative**: its pairing against a
  function is `‖Bg‖₂²`, by adjointness `N = A B`.
- `norm_le_shiftedNumberCLM` — **`4π‖g‖₂ ≤ ‖Kg‖₂`**: Cauchy–Schwarz against the pairing, whose
  value is `‖Bg‖₂² + 4π‖g‖₂²`.
- `norm_creationCLM_sq_le_shifted`, `norm_annihilationCLM_sq_le_shifted` — **`4π‖Ag‖₂² ≤ ‖Kg‖₂²`
  and `2π‖Bg‖₂² ≤ ‖Kg‖₂²`**: the quadratic bounds of two modules ago, with the identity factor
  absorbed into `K` by the previous item.
- `shiftedNumberCLM_creationCLM`, `shiftedNumberCLM_annihilationCLM` — **`K A = A(K + 4π)` and
  `K B = B N`**: commuting the shift past an oscillator operator only shifts it again, so an
  induction on word length stays inside powers of `K` with no extra terms.

That is the last analytic ingredient of the reverse comparison; what remains is the induction on
word length itself, bounding `‖W f‖₂ ≤ C_{|W|}‖K^{|W|} f‖₂` for every word `W` in `A` and `B`, and
then reading the Schwartz seminorms off the Sobolev estimate.

- 2026-08-02 — Nonnegativity of the number operator, and the domination of the oscillator
  operators by a single power of the shifted operator.

### Lean: iterating the shift past the oscillator operators

`formal/GaloisForLFunctions/HTGeometry/SchwartzShiftedIterates.lean` (14 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `shiftedPlusCLM`, `_apply` — the raised shift `K + 4π`; `toLp_add`, `norm_toLp_smul_four_pi` —
  linearity bookkeeping for the `L²` class map.
- `norm_numberCLM_le_two`, `norm_shiftedPlusCLM_le_two` — **`‖Ng‖₂ ≤ 2‖Kg‖₂` and
  `‖(K+4π)g‖₂ ≤ 2‖Kg‖₂`**: both neighbours of the shift are dominated by it, using `4π‖g‖₂ ≤
  ‖Kg‖₂`.
- `shiftedNumberCLM_numberCLM`, `shiftedNumberCLM_shiftedPlusCLM`,
  `numberCLM_iterate_shiftedNumberCLM`, `shiftedPlusCLM_iterate_shiftedNumberCLM` — the shift
  commutes with both neighbours, and with their iterates.
- `norm_numberCLM_iterate_le`, `norm_shiftedPlusCLM_iterate_le` — **`‖Nʲg‖₂ ≤ 2ʲ‖Kʲg‖₂`** and the
  same for the raised shift.  This is the step that makes binomial expansions unnecessary: one
  factor of two per application, since the neighbour commutes with the shift.
- `shiftedNumberCLM_iterate_creationCLM`, `shiftedNumberCLM_iterate_annihilationCLM` — **`Kʲ A =
  A (K+4π)ʲ` and `Kʲ B = B Nʲ`**, the iterated commutation rules.

With these, a power of the shift can be moved across any word in the oscillator operators, at the
cost of a factor `2ʲ` and a change of neighbour, so the word induction `‖Wf‖₂ ≤ C‖K^{|W|}f‖₂`
closes.

- 2026-08-02 — Iterated commutation and domination for the shifted number operator.

### Lean: words in the oscillator operators

`formal/GaloisForLFunctions/HTGeometry/SchwartzOscillatorWord.lean` (10 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `one_le_four_pi`, `one_le_two_pi`, `norm_creationCLM_le_shifted`,
  `norm_annihilationCLM_le_shifted` — since `π ≥ 2`, the quadratic bounds collapse to **`‖Ag‖₂ ≤
  ‖Kg‖₂` and `‖Bg‖₂ ≤ ‖Kg‖₂`**: the oscillator operators are contractions relative to the shift,
  with constant one and no square roots.
- `oscWord` — a word in the two operators, indexed by a list of booleans, applied to a Schwartz
  function.
- `oscWord_shift_bound` — **`‖Kʲ(W g)‖₂ ≤ C·‖K^{j+|W|} g‖₂`**, by induction on the word.  Each step
  moves the power of the shift across the leading operator by the iterated commutation rules,
  replaces the neighbour's power by the shift's at the cost of `2ʲ`, and applies the induction
  hypothesis at `j+1`.
- `oscWord_bound` — the case `j = 0`: **`‖W g‖₂ ≤ C·‖K^{|W|} g‖₂`.**

So every word in `A` and `B` — hence, by `mulXCLM_eq_oscillator` and `derivSCLM_eq_oscillator`,
every operator built from multiplication by the coordinate and differentiation — is bounded in `L²`
by a single power of the shifted number operator.

- 2026-08-02 — The word induction: an arbitrary word in the oscillator operators is bounded by one
  power of the shift.

### Lean: the calculus of controlled operators

`formal/GaloisForLFunctions/HTGeometry/SchwartzShiftControlled.lean` (14 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `shiftedNumberCLM_iterate_add`, `_smul`, `norm_toLp_iterate_le_succ` — the iterated shift is
  linear, and one power of it dominates the previous one with factor `(4π)⁻¹`.
- `L2ShiftControlled T m` — **the control predicate**: every power of the shift applied after `T`
  is `L²`-bounded by that power raised by `m`.
- `L2ShiftControlled.mono`, `.mono_le`, `.add`, `.smul`, `.comp`, `.congr`, `.order_congr` — the
  closure properties.  **Composition adds the orders**, which is what makes the predicate usable:
  control is stated for *all* shift powers precisely so that it survives composition.
- `l2ShiftControlled_oscWord`, `_id`, `_creationCLM`, `_annihilationCLM` — words are controlled at
  their length.
- `l2ShiftControlled_mulXCLM`, `_derivSCLM` — **multiplication by the coordinate and
  differentiation are controlled at order one**, being combinations of the two oscillator
  operators.
- `l2ShiftControlled_sobolevOp` — **the elliptic operator `f ↦ f − f''/4π²` is controlled at order
  two.**

So any composite of multiplications and differentiations is controlled at the sum of its orders,
and composing with the elliptic operator adds two.  Feeding that into the Sobolev estimate bounds
the Schwartz sup-seminorms by `‖K^m f‖₂`, which is the reverse comparison.

- 2026-08-02 — The control calculus: sums, scalars and composition, with the basic operators
  controlled at their natural orders.

### Lean: the reverse comparison is proved

`formal/GaloisForLFunctions/HTGeometry/SchwartzSeminormOscillator.lean` (5 declarations, axiom
audit `propext, Classical.choice, Quot.sound`).

- `coe_derivSCLM_iterate`, `mulXCLM_iterate_apply`, `norm_mulXCLM_iterate_apply` — the iterated
  operators compute what they should: `‖x‖ᵏ‖f⁽ⁿ⁾(x)‖ = ‖(MᵏDⁿf)(x)‖`.
- `l2ShiftControlled_iterate` — iterating a controlled operator multiplies its order.
- `schwartzSeminorm_le_shifted` — **`p_{k,n}(f) ≤ C·‖K^{k+n+2}f‖₂` for every `k`, `n`.**  The
  Schwartz seminorm is bounded through `SchwartzMap.seminorm_le_bound` by the supremum of
  `MᵏDⁿf`, the Sobolev estimate turns that supremum into the `L²` norm of the elliptic operator
  applied to it, and the control calculus turns that into a power of the shifted number operator.

**This is the reverse comparison.**  Together with `oscillatorSeminorm_le_schwartzSeminorm` (each
oscillator seminorm is continuous, hence bounded by finitely many Schwartz seminorms) the two
presentations of the Schwartz topology — the standard seminorms and the `L²` norms of powers of the
oscillator — are equivalent.

Remaining for `𝒮(ℝ)` nuclear: package the shifted family `Q_m(f) = ‖K^m f‖₂` as a `SeminormFamily`
with its continuity (the same two-line argument as for `oscillatorSeminorm`), so that the two
families present the same topology; then nuclearity of that Hilbertian family follows from the
Hermite eigen-decomposition — the coefficient map sends `Q_m` to the weighted `ℓ²` norm with weights
`(4π(n+1))^m`, whose ratios are summable — and transports to `𝒮(ℝ)` by
`deningerIsNuclearSpace_of_linearEquiv` and the corpus's Köthe/rapid-sequence nuclearity.

- 2026-08-02 — The reverse seminorm comparison, the last analytic step: Schwartz seminorms are
  dominated by the oscillator ones.

### Lean: the two seminorm families dominate each other

`formal/GaloisForLFunctions/HTGeometry/SchwartzShiftedSeminorm.lean` (10 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `shiftedPowCLM`, `shiftedSeminorm`, `_apply`, `shiftedSeminormFamily` — the family
  `Q_m(f) = ‖Kᵐf‖₂` as genuine `Seminorm` objects and a `SeminormFamily`.
- `shiftedSeminorm_le_succ`, `shiftedSeminorm_le_of_le` — **the family increases up to constants**:
  `Q_m ≤ (4π)^{-(m'-m)} Q_{m'}` for `m ≤ m'`.  This is what makes it directed, which the Schwartz
  family itself is not (lower derivatives are not controlled by higher ones alone).
- `shiftedSeminorm_continuous`, `shiftedSeminorm_le_schwartzSup` — **each `Q_m` is bounded by a
  constant times a finite supremum of Schwartz seminorms** (`Seminorm.bound_of_continuous`).
- `schwartzSup_le_shiftedSeminorm` — **each finite supremum of Schwartz seminorms is bounded by a
  single `Q_m`**, by induction on the finite set, using the reverse comparison on each member and
  the directedness above to put them all at one index.

These are exactly the two hypotheses of the corpus transfer lemma
`deningerIsNuclearSpaceC_of_dominating`, with the Schwartz side taken in its finite-supremum
presentation.  So once the family `Q_m` is proved nuclear, nuclearity transfers to the Schwartz
space.

Remaining: nuclearity of `Q_m` itself.  The Hermite functions diagonalize `K` with eigenvalues
`4π(n+1)`, and the corpus already owns the Grothendieck–Pietsch criterion for Köthe spaces
(`deningerKothe_isNuclearSpace`) with the summability condition `∑ (w_k/w_m) < ∞`, satisfied here
by `∑ (4π(n+1))^{k-m} < ∞` for `m ≥ k+2`.  The remaining Lean work is the coefficient map:
completeness gives injectivity, the eigenrelation gives the weights.

- 2026-08-02 — Mutual domination of the Schwartz and oscillator seminorm families, in the exact
  form the nuclearity transfer consumes.

### Lean: the normalized Hermite coefficient map

`formal/GaloisForLFunctions/HTGeometry/HermiteCoefficientMap.lean` (6 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `hermiteNorm_pos`, `hermiteCoeff`, `norm_hermiteCoeff` — the coefficient of a Schwartz function
  along the *normalized* `n`-th Hermite function.
- `norm_hermiteCoeff_le` — **`|cₙ(f)| ≤ ‖f‖₂`**, Cauchy–Schwarz against a unit vector.
- `hermiteCoeff_decay` — **`(2π(2n+1))ᵏ|cₙ(f)| ≤ ‖Hᵏf‖₂`**: the coefficients decay faster than any
  power, with an oscillator seminorm as the constant.
- `hermiteCoeff_eq_zero_iff` — **the coefficient map is injective on the Schwartz space**, from the
  completeness theorem.

These are exactly the two inputs the map into a Köthe space needs: the decay says the coefficient
sequence lies in the space of rapidly decreasing sequences with weights `(2π(2n+1))ᵏ`, and the
bound says the map is continuous.  With injectivity, the Schwartz space is identified with a
subspace of that Köthe space.

Remaining for `𝒮(ℝ)` nuclear: the *reverse* estimate, `‖Kᵐf‖₂ ≤ C·(weighted ℓ¹ norm of the
coefficients)`, which is where completeness has to be upgraded from the Schwartz space to `L²` —
the same exponential-integral argument goes through for an `L²` function, since the Gaussian weight
makes `∫|u|e^{−πx²}e^{a|x|}` finite by Cauchy–Schwarz, and the conclusion `𝓕(u·gauss) = 0` then
gives `u = 0` through Plancherel.  After that the corpus's Grothendieck–Pietsch criterion applies
and nuclearity transfers to the Schwartz seminorms by `deningerIsNuclearSpaceC_of_dominating`.

- 2026-08-02 — The normalized coefficient map with its two estimates and its injectivity.

### Lean: polynomial growth of the Hermite seminorms

`formal/GaloisForLFunctions/HTGeometry/HermiteSeminormGrowth.lean` (6 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `shiftedNumberCLM_hermiteSchwartz`, `_iterate_` — **`K hⱼ = 4π(j+1)hⱼ`** and the corresponding
  powers.
- `hermiteUnit`, `norm_toLp_hermiteUnit_shifted` — the normalized Hermite function as a Schwartz
  map, with `‖Kᵐĥⱼ‖₂ = (4π(j+1))ᵐ` exactly.
- `schwartzSeminorm_hermiteUnit_le` — **`p_{k,n}(ĥⱼ) ≤ C·(4π(j+1))^{k+n+2}`**: every Schwartz
  seminorm of the *normalized* Hermite functions grows only polynomially in the index.  The
  normalization is what makes this true — the unnormalized functions have `‖hⱼ‖₂² = j!/π^j·‖h₀‖₂²`,
  factorial growth, which cancels exactly.

This is the second half of the convergence criterion for the Hermite expansion: coefficients decay
faster than any power (`hermiteCoeff_decay`) while the normalized functions grow only polynomially
in each Schwartz seminorm.  So `∑ⱼ cⱼ(f)ĥⱼ` converges absolutely in every Schwartz seminorm, hence
in the Fréchet space `𝒮(ℝ)`, and its sum has the same Hermite coefficients as `f`, so by the
completeness theorem it *is* `f`.

That expansion — convergent in `𝒮(ℝ)`, hence in `L²` — supplies Parseval, which is the reverse
estimate `‖Kᵐf‖₂ ≤ C·(weighted norm of the coefficients)` that the nuclearity transfer still needs.
It also upgrades completeness to `L²` for free, since the span of the Hermite functions is then
dense in the image of `𝒮(ℝ)`, which is dense in `L²`.

- 2026-08-02 — Polynomial growth of the normalized Hermite functions in every Schwartz seminorm.

### Lean: the Hermite expansion is absolutely summable in every seminorm

`formal/GaloisForLFunctions/HTGeometry/HermiteExpansionSummable.lean` (5 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `shifted_le_two_mul_hamiltonian`, `hermiteCoeff_decay_shift` — the coefficient decay restated
  against the *shifted* eigenvalue `4π(j+1)`, which is the one the growth bound uses: the two
  eigenvalues differ by a factor at most two.
- `schwartzSeminorm_hermiteTerm_le` — **each term of the expansion is `O((j+1)⁻²)` in every
  Schwartz seminorm**: taking the decay two orders above the growth `k+n+2` leaves exactly a square
  in the denominator.
- `summable_schwartzSeminorm_hermiteTerm` — **the seminorm series converges**, by comparison with
  the `p`-series at `p = 2`.

So the Hermite expansion of a Schwartz function is absolutely summable in every seminorm of
`𝒮(ℝ)`.  Since `𝒮(ℝ)` is a complete metrizable space, absolute summability in every seminorm gives
a sum there; the sum has the same Hermite coefficients as `f` (the coefficient functionals are
continuous), so completeness identifies it with `f`.  That expansion is the last missing input: it
gives Parseval, hence the reverse estimate for the oscillator seminorms, hence — with the mutual
domination already proved and the corpus's Grothendieck–Pietsch criterion — nuclearity of `𝒮(ℝ)`.

- 2026-08-02 — Absolute summability of the Hermite expansion in every Schwartz seminorm.

### Lean: completeness of the Hermite system in `L²(ℝ)`

`formal/GaloisForLFunctions/HTGeometry/HermiteL2Moments.lean` (6 declarations) and
`formal/GaloisForLFunctions/HTGeometry/HermiteL2Completeness.lean` (10 declarations), axiom audit
`propext, Classical.choice, Quot.sound`.

The route through completeness of the Fréchet space `𝒮(ℝ)` was abandoned: mathlib has no
`CompleteSpace 𝓢(E, F)` instance, and the corpus's nuclearity criterion never needs it — the
comparison maps live on seminorm *quotients*, so only convergence in each individual seminorm is
required, and every one of those seminorms is an `L²` norm.  So completeness of the Hermite system
was upgraded from the Schwartz space to `L²` instead.

- `inner_polyGaussSchwartz_toLp_eq_zero` — an `L²` function orthogonal to every Hermite function is
  orthogonal to every polynomial multiple of the Gaussian (span induction on `hermitePoly`).
- `memLp_gauss_mul_exp_abs`, `integrable_norm_l2_gauss_mul_exp_abs` — the dominating function
  `gauss·e^{|a||x|}` is in `L²`, so its product with an `L²` factor is integrable: this is the
  Hölder replacement for the uniform bound available on a Schwartz function.
- `integral_gaussMul_exp_l2_eq_zero` — **every exponential integral vanishes**, by termwise
  integration of the exponential series under that dominating function.
- `fourier_l2GaussMul_eq_zero` — hence `𝓕(u·gauss) ≡ 0`.
- `integral_l2GaussMul_schwartz_eq_zero` — the self-adjointness of the Fourier transform for the
  integral pairing (`VectorFourier.integral_fourierIntegral_smul_eq_flip`, which needs only
  integrability, not continuity) turns that into vanishing against every Schwartz function, because
  `𝓕` maps `𝒮(ℝ)` onto itself.
- `hermite_l2_complete` — **an `L²` function orthogonal to every Hermite function is zero**, since
  Schwartz functions are dense in `L²` and the Gaussian is nowhere zero.

Note the pointwise Fourier inversion theorem is unusable here (`u·gauss` is not continuous); the
duality route avoids it entirely.

- 2026-08-02 — Completeness of the Hermite system in `L²(ℝ)`.

### Lean: the Hermite expansion converges in `L²`, and the oscillator quotients

`formal/GaloisForLFunctions/HTGeometry/HermiteL2Expansion.lean` (7 declarations) and
`formal/GaloisForLFunctions/HTGeometry/HermiteShiftedCoefficients.lean` (8 declarations), axiom
audit `propext, Classical.choice, Quot.sound`.

- `summable_norm_hermiteCoeff` — the coefficients are absolutely summable (decay at order two).
- `hasSum_hermiteExpansion_toLp` — **`f = ∑ⱼ cⱼ(f)ĥⱼ` in `L²`** for every Schwartz `f`: the series
  converges absolutely in the Banach space `L²`, its sum has the same coefficients as `f`, and the
  Hermite system is complete.
- `norm_toLp_le_tsum_hermiteCoeff` — **`‖f‖₂ ≤ ∑ⱼ|cⱼ(f)|`**, the reverse estimate.  Note this is
  the triangle inequality on the expansion, not Parseval: no orthogonality is needed for it.
- `schwartzPair_shiftedNumberCLM`, `hermiteCoeff_shiftedIterate` — `K` is symmetric for the
  bilinear pairing, so `cⱼ(Kᵐf) = (4π(j+1))ᵐcⱼ(f)`.
- `norm_hermiteCoeff_shifted_le` — **`(4π(j+1))ᵐ|cⱼ(f)| ≤ Qₘ(f)`**, and
  `shiftedSeminorm_hermiteUnit` — **`Qₖ(ĥⱼ) = (4π(j+1))ᵏ`** exactly.

- 2026-08-02 — The `L²` Hermite expansion and the two oscillator estimates.

### Lean: `𝒮(ℝ)` is a nuclear space `[PROVED HERE]`

`formal/GaloisForLFunctions/RHTower/DeningerSchwartzNuclear.lean` (13 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `deningerOscL2CLM`, `deningerOscL2CLM_partialSum` — the oscillator map `f ↦ (Kᵐf).toLp`, and the
  identity that turns a partial sum of the expansion in the `Qₖ`-quotient into a partial sum of the
  `L²` expansion of `Kᵏf`.
- `hasSum_hermiteExpansion_shiftedQuotient` — **the expansion converges in every oscillator
  seminorm quotient.**
- `deningerHermiteCoeffQuotient`, `norm_deningerHermiteCoeffQuotient_le` — the coefficient
  functional on the `Qₘ`-quotient, of norm at most `(4π(j+1))^{-m}`.
- `deningerIsNuclearSpace_shiftedSeminormFamily` — **the oscillator family is nuclear**: the
  comparison map `Q_{k+2} → Qₖ` is `∑ⱼ φⱼ ⊗ [ĥⱼ]` with `∑ⱼ‖φⱼ‖‖[ĥⱼ]‖ ≤ ∑ⱼ(4π(j+1))⁻² < ∞`.
- `deningerIsNuclearSpaceC_schwartzSup` — **the Schwartz space of the line is a nuclear space**,
  transported to the finite suprema of the Schwartz seminorms by
  `deningerIsNuclearSpaceC_of_dominating`.

The statement is for the *directed* family of finite suprema, which is forced: the bare Schwartz
family `p_{k,n}` is not directed — no single `p_{k,n}` dominates another (dilate a bump to see
`p₀,₀ ≰ C·p₀,₁`) — so nuclearity in the corpus's sense is a statement about the directed hull, as
it is in the classical definition.

This closes the first half of `(1)`–`(2)` of the card: the ambient space of `H_∩` is nuclear
Fréchet.  What remains for `(2)` is the permanence step (`H_∩` is the kernel of two continuous
functionals inside the even subspace) and for `(1)` the countable-product-and-subspace
presentation of `H_−`.

- 2026-08-02 — **`𝒮(ℝ)` is a nuclear space, unconditionally in Lean.**

### Lean: both radial spaces of `(1)`–`(2)` are nuclear `[PROVED HERE]`

`formal/GaloisForLFunctions/RHTower/DeningerRadialNuclear.lean` (16 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `H_∩` is the already-formalized `DeningerMeyerCap` of `DeningerMeyerRadialEndpoints.lean`
  (even, `f(0) = 0`, `f̂(0) = 0`); the module reuses it rather than defining a second copy.
- `deningerIsNuclearSpaceC_meyerCap`, `_schwartz` — **`(2)` is nuclear**, in both the oscillator
  and the Schwartz presentation of the restricted seminorms.
- `deningerRadialCompat` — `H_−` in the card's own presentation: the compatibility submodule
  `{(g_s)_{s∈ℤ} : g_s(t) = e^{st}g_0(t)}` of the countable product of the integer-weight copies.
  `deningerRadialCompat_ext` shows a member is determined by `g_0`, so this really is the space of
  functions all of whose integer exponential weightings are Schwartz — and it carries the
  projective-limit family, not the subspace family of one weight.
- `deningerIsNuclearSpaceC_radialCompat` — **`(1)` is nuclear**: a subspace of a countable product
  of nuclear spaces, by `deningerIsNuclearSpace_pi` and `deningerIsNuclearSpaceC_subspace`.
- `deningerMeyerCapWitness`, `deningerRadialGauss` and the two `_ne_bot` theorems — **neither space is
  zero**, so the two nuclearity statements are not vacuous.  The witness for `(2)` is
  `h₄(0)·h₀ − h₀(0)·h₄`: both Hermite functions are even with Fourier eigenvalue `(−i)⁴ = 1`, so
  the combination is its own Fourier transform and vanishing at the origin gives both constraints
  at once — no Gaussian moment computation is needed.  The witness for `(1)` is the Gaussian in
  logarithmic coordinates, whose `s`-th weight `e^{st}e^{−πt²} = e^{s²/4π}·gauss(t − s/2π)` is a
  translate of the Gaussian times a constant.

Note nuclearity needs only the submodule structure; closedness is what makes the two spaces
*Fréchet*, and enters `(3)`–`(4)`, not here.

- 2026-08-02 — **`(1)` and `(2)` of the card are nuclear, unconditionally in Lean.**

### Lean: the Poisson operator `(3)` — values, Euler stability, two-ended decay

`formal/GaloisForLFunctions/HTGeometry/SchwartzEulerOperator.lean` (7 declarations) and
`formal/GaloisForLFunctions/RHTower/DeningerPoissonOperator.lean` (9 declarations), axiom audit
`propext, Classical.choice, Quot.sound`.

The analytic core of `(3)` turned out to be **already in the corpus**:
`CCMRationalArchimedeanSchwartzPoisson.lean` proves the scaled Poisson identity for the full
integer lattice trace `Θ_f(a) = ∑_{n∈ℤ} f(an)` together with arbitrary-power decay at *both*
multiplicative ends under exactly Meyer's two conditions `f(0) = 0` and `∫f = 0`.  For an even `f`
the card's `Zf(a) = ∑_{n≥1} f(na)` is `Θ_f(a)/2`, so those estimates are the estimates for `Z`.

- `eulerSCLM` — the Euler operator `θf(x) = xf'(x)`, with `hasDerivAt_comp_exp`: **it is the
  derivative along the multiplicative flow**, `d/dt f(ae^t) = (θf)(ae^t)`.  This is what converts
  `t`-derivatives of the Poisson sum into Poisson sums of `θᵏf`.
- `fourierSCLM_eulerSCLM` — **`𝓕(θf) = −𝓕f − θ𝓕f`**, from the two Fourier commutation rules;
  hence `𝓕(θf)(0) = −𝓕f(0)`.
- `deningerMeyerCap_eulerSCLM` — **Meyer's space is stable under the Euler operator**: parity, the
  value at the origin, and the Fourier constraint all propagate.  So every multiplicative
  derivative of `Zf` is again a Poisson sum of a member of `ℋ_∩`.
- `deningerPoissonValue`, `deningerPoissonValue_eq_half_latticeTrace` — `Z` and the halving
  identity (`ℤ = {0} ⊔ ℕ₊ ⊔ −ℕ₊`, with the origin term killed and the two halves equal by parity).
- `norm_deningerPoissonValue_le_large`, `_small` — **`‖Zf(a)‖ ≤ C_N/2 · a^{−2N−2}` and
  `≤ C_N'/2 · a^{2N+1}`**: arbitrary-power decay at both ends.

What remains for `(3)`: differentiating the sum term by term (`G^{(k)}(t) = Z(θᵏf)(e^t)`, needing
local uniform convergence), assembling the weights `e^{st}G(t)` into a Schwartz map for each
`s ∈ ℤ`, and the continuity of `f ↦ Zf` — after which `Z : ℋ_∩ → ℋ_−` is defined and continuous.
Strictness and closed range (Meyer's theorem) come after that.

- 2026-08-02 — The Poisson operator's value layer: Euler stability and two-ended decay.

### Lean: the Poisson operator `Z : ℋ_∩ → ℋ_−` is constructed `[PROVED HERE]`

`formal/GaloisForLFunctions/RHTower/DeningerPoissonDerivative.lean` (10 declarations),
`DeningerPoissonWeight.lean` (13), `DeningerPoissonSchwartz.lean` (17); axiom audit
`propext, Classical.choice, Quot.sound` throughout.

- `deningerPoissonLog` — the Poisson sum in the logarithmic coordinate, `G_f(t) = ∑_{n≥1}f(ne^t)`.
  On each half line `t > T` the terms and their derivatives are dominated by
  `p_{2,0}(·)/(n e^T)²`, so `hasDerivAt_tsum_of_isPreconnected` applies and
  **`G_f' = G_{θf}`** (`hasDerivAt_deningerPoissonLog`).  Hence `contDiff_deningerPoissonLog`
  (smooth) and `iteratedDeriv_deningerPoissonLog`: **`G_f^{(k)} = G_{θᵏf}`.**
- `deningerShiftCLM s = s + θ` and `deningerPoissonWeight s f t = e^{st}G_f(t)`.  Linearity of the
  Poisson sum turns the product rule into a single operator identity:
  **`(e^{st}G_f)' = e^{st}G_{A_s f}`**, so the `n`-th derivative is `e^{st}G_{A_sⁿ f}`
  (`iteratedDeriv_deningerPoissonWeight`) — no Leibniz expansion is needed.
- `deningerPoissonDecayIndex s = |s| + 1` — the decay order chosen from the weight.  With it the
  large-end estimate leaves exponent `s − 2|s| − 4 ≤ −1` and the small-end estimate leaves
  `s + 2|s| + 3 ≥ 1`, so both ends are killed by `uᵏe^{−u} ≤ k!`
  (`norm_deningerPoissonWeight_le_of_nonneg`, `_of_nonpos`).
- `deningerPoissonSchwartz` — **each weight is a Schwartz map of the logarithmic coordinate**: the
  smoothness is the tsum differentiation, and the decay at order `(k, n)` is the above bound
  applied to `A_sⁿ f`, which is again in Meyer's space.
- `deningerPoissonFamily_mem` — **the family of all integer weights satisfies the compatibility
  law `g_s(t) = e^{st}g_0(t)`**, hence lies in `deningerRadialCompat`.
- `deningerPoissonLM : DeningerMeyerCap →ₗ[ℂ] deningerRadialCompat` — **the Poisson operator of
  `(3)`, constructed as a linear map.**

So `(3)` now exists as a map between the two spaces of `(1)`–`(2)`, with `Zf` verified to lie in
the radial space.  What remains of `(3)`: continuity (each target seminorm bounded by finitely many
source seminorms — the constants above are already linear in `p_{2(N+1),0}(A_sⁿf)` and
`p_{2(N+1),0}(𝓕A_sⁿf)`, so this is the continuity of the fixed operators `A_sⁿ` and `𝓕`), then
injectivity, closed range and the topological isomorphism onto the range (Meyer's theorem), and
finally the strict exact sequence `(4)`.

- 2026-08-02 — **The Poisson operator `Z : ℋ_∩ → ℋ_−` constructed and shown to land in `ℋ_−`.**

### Lean: the Poisson operator is continuous `[PROVED HERE]`

`formal/GaloisForLFunctions/RHTower/DeningerPoissonContinuous.lean` (8 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

The decay constants of the two-ended estimates are *explicit Schwartz seminorms* —
`ccmRationalArchimedeanDecayConstant h N = p_{2N+2,0}(h)·∑ₙ n^{−2N−2}` — so the whole estimate is
linear in a seminorm of `A_sⁿf` and of `𝓕A_sⁿf`.

- `deningerShiftPowCLM` — the powers of `A_s = s + θ` as continuous linear maps (the function
  iterate of a CLM is not itself packaged as one).
- `exists_bound_seminorm_comp` — for any continuous operator `T` on `𝒮(ℝ)`, `p_{k,0}∘T` is bounded
  by finitely many Schwartz seminorms (`Seminorm.bound_of_continuous` against
  `schwartz_withSeminorms`).
- `exists_bound_seminorm_deningerPoissonSchwartz` — **`p_{k,n}(Z_s f) ≤ C·sup_K p(f)`**, uniformly
  in `f ∈ ℋ_∩`.
- `exists_bound_schwartzSup_deningerPoissonSchwartz`, `exists_bound_shiftedSeminorm_deningerPoisson`,
  `exists_bound_sum_shiftedSeminorm_deningerPoisson` — the same for finite suprema, for the
  oscillator seminorms, and for finite sums over the coordinates.
- `deningerPoissonLM_bound` — **every seminorm of the radial presentation of `Zf` is bounded by
  finitely many Schwartz seminorms of `f`**: the Poisson operator `ℋ_∩ → ℋ_−` is continuous.

Next for `(3)`: injectivity and the reverse estimate.  Both should come from the *same* object —
Möbius inversion `f(x) = ∑_{n≥1} μ(n)(Zf)(nx)`, which converges absolutely because a member of
`ℋ_−` decays faster than every power at *both* multiplicative ends.  That exhibits a continuous
left inverse of `Z` on its range, which is exactly strictness plus injectivity.

- 2026-08-02 — **The Poisson operator is continuous.**

### Lean: Möbius inversion and injectivity of `Z` `[PROVED HERE]`

`formal/GaloisForLFunctions/RHTower/DeningerPoissonMoebius.lean` (9 declarations) and
`DeningerPoissonInjective.lean` (2); axiom audit `propext, Classical.choice, Quot.sound`.

- `deningerMoebiusPair f x (n,m) = μ(n)f(nmx)` — the double family.  Both degenerate index values
  are harmless: `μ(0) = 0` and `f(0) = 0`, so the family is supported on `n,m ≥ 1` without any
  index gymnastics.  `summable_deningerMoebiusPair` bounds it by
  `p_{2,0}(f)/x²·n^{−2}m^{−2}` (division by zero being zero makes the majorant handle the
  degenerate indices too).
- `tsum_deningerMoebiusPair_eq` — summing over `m` first gives `∑_{n} μ(n)(Zf)(nx)`.
- `sum_moebius_divisorsAntidiagonal` — `∑_{de=k} μ(d) = [k = 1]`, from
  `ArithmeticFunction.moebius_mul_coe_zeta`.
- `tsum_fiber_deningerMoebiusPair` — summing along the fibres of `(n,m) ↦ nm` gives
  `[k = 1]·f(kx)` on the fibre over `k`.
- `deningerMoebius_poissonValue` — **`∑_{n≥1} μ(n)(Zf)(nx) = f(x)`** for every `x > 0`: the two
  summation orders of one absolutely summable family.
- `deningerPoissonValue_injOn` — the Poisson sum determines the function on the positive half line.
- `deningerPoissonLM_injective` — **`Z : ℋ_∩ → ℋ_−` is injective**: the zeroth weight of `Zf` is
  the Poisson sum, Möbius inversion recovers `f` on `x > 0`, and evenness with `f(0) = 0` extends
  that to the whole line.  This is exactness of `(4)` at `ℋ_∩`.

- 2026-08-02 — **Möbius inversion of the Poisson sum, and injectivity of `Z`.**

### Lean: the Mellin symbol of `Z` is `ζ` `[PROVED HERE]`

`formal/GaloisForLFunctions/RHTower/DeningerPoissonMellin.lean` (7 declarations, axiom audit
`propext, Classical.choice, Quot.sound`).

- `schwartz_isBigO_atTop`, `schwartz_isBigO_zero`, `mellinConvergent_schwartz` — the Mellin
  transform of a Schwartz function converges for `Re s > 0` (rapid decay at infinity, boundedness
  at the origin, through `mellinConvergent_of_isBigO_rpow`).
- `integral_mellinNorm_comp_mul` — the scaling law `∫₀^∞ x^{σ−1}|f(cx)|dx = c^{−σ}∫₀^∞x^{σ−1}|f|`.
- `tsum_one_add_cpow_eq_zeta` — `∑_{n≥0}(n+1)^{−s} = ζ(s)` for `Re s > 1`.
- `mellin_deningerPoissonValue` — **`M(Zf)(s) = ζ(s)·M(f)(s)` for `Re s > 1`**: each term of the
  Poisson sum is a dilation, the Mellin transform turns a dilation by `n` into `n^{−s}`, and the
  family of dilated integrals is absolutely summable, so the sum comes out of the integral
  (`integral_tsum_of_summable_integral_norm`).

This is the identity that makes `M_ζ` a zeta object: on the Mellin side the Poisson operator *is*
multiplication by `ζ`, so its cokernel is supported exactly on the zero divisor of `ζ`.  It is also
the reason the remaining claim of `(3)` — strictness, i.e. the reverse estimate — is genuinely
deep: dividing by `ζ` on vertical lines needs quantitative lower bounds for `ζ` (Meyer's zeta
estimate).  The naive route through Möbius inversion cannot give it: for `x → 0` the absolute
series `∑ₙ|Zf(nx)|` is of size `1/x` even though `f` is bounded, so the cancellation carried by
`μ` is essential.

- 2026-08-02 — **The Mellin symbol of the Poisson operator is `ζ`.**

### Lean: the image of `Z` vanishes on the zeros of `ζ`, and the cokernel `(4)` `[PROVED HERE]`

`formal/GaloisForLFunctions/RHTower/DeningerPoissonZeroDivisor.lean` (14 declarations) and
`DeningerPoissonCokernel.lean` (19); axiom audit `propext, Classical.choice, Quot.sound`.

- `isBigO_deningerPoissonValue_atTop`, `_zero` — the two-ended decay of `Zf` in `O`-form (any
  power at infinity, any power at the origin, by choosing the decay index).
- `differentiableAt_mellin_deningerPoissonValue` — **`M(Zf)` is entire**; and
  `differentiableAt_mellin_schwartz` gives holomorphy of `M(f)` on `Re s > 0`.
- `mellin_deningerPoissonValue_eq_zeta_mul` — the factorization `M(Zf) = ζ·M(f)` propagates from
  `Re s > 1` to the whole half plane minus the pole, by the identity theorem on
  `{0 < Re, 0 < Im} ∪ {1 < Re}` (two convex opens with nonempty intersection, so preconnected, and
  `1` is in neither).
- `mellin_deningerPoissonValue_eq_zero_of_zeta_eq_zero` — **`M(Zf)(ρ) = 0` at every non-real zero
  `ρ` of `ζ` with `Re ρ > 0`.**
- `norm_deningerRadialValue_le`, `mellinConvergent_deningerRadialValue` — every member of `ℋ_−` is
  `O(x^{−s})` at both ends for *every* integer `s` (its `s`-th weight is Schwartz), so its
  multiplicative Mellin transform converges everywhere; hence the transform is additive and
  homogeneous on `ℋ_−`.
- `DeningerMZeta`, `deningerMZetaMk`, `deningerPoisson_exact` — **the cokernel `M_ζ` and exactness
  at `ℋ_−`**; with `deningerPoissonLM_injective` this is the algebraic exactness of `(4)`.
- `deningerZetaZeroSubspace`, `deningerPoisson_range_le_zetaZero` — **the range of `Z` lies in the
  subspace of `ℋ_−` cut out by the non-real zeros of `ζ` in the right half plane.**  This is the
  mechanism the card's `M_ζ` is named for: the cokernel records the zero divisor of `ζ`.

What is still open on the card: the *topological* half of `(3)`–`(4)` — strictness/closed range
(Meyer's zeta estimate, which needs quantitative lower bounds for `ζ` on vertical lines), and
nuclearity of the quotient `M_ζ` (Grothendieck's quotient permanence, not yet in the corpus's
seminorm framework).  Sections 2–3 additionally need completed projective tensor products and a
topological singular-chain cosheaf.

- 2026-08-02 — **The zero divisor of `ζ` in the image of `Z`, and the cokernel sequence.**

### Lean: quotient seminorms and the quotient criterion for nuclearity

`formal/GaloisForLFunctions/RHTower/DeningerQuotientSeminorm.lean` (12 declarations) and
`DeningerQuotientProjection.lean` (8); axiom audit `propext, Classical.choice, Quot.sound`.

Towards the nuclearity of `M_ζ` (the last permanence property the card's `(4)` needs, and the one
the corpus did not have):

- `deningerQuotientSeminorm` — the infimum of a seminorm over the representatives of a class, built
  as a genuine `Seminorm` on `E ⧸ N` (approximate infima give subadditivity; multiplication by a
  nonzero scalar is a bijection of representative sets, which gives homogeneity).
- `deningerQuotientSeminorm_mk_le`, `_exists_lt`, `_le_of_le` — the three facts everything else
  uses, including that a domination `p ≤ Cq` descends to `p̄ ≤ Cq̄`.
- `deningerQuotientProjection`, `_square`, `deningerQuotientProjectionC`, `_square` — the
  norm-decreasing surjection `E_p → (E/N)_p̄` of seminorm spaces, its commutation with the
  comparison maps, and both after completion.
- `deningerIsNuclearSpaceC_quotient_of_rightInverse` — **the criterion**: if each completed
  projection has a bounded section then nuclearity descends to the quotient, because
  `T̄ = π ∘ T ∘ σ` is then a nuclear map conjugated by bounded maps.  This mirrors the corpus's
  subspace criterion (`..._subspace_of_leftInverse`) with sections in place of retractions.

What remains for quotient nuclearity: the Hilbertian supply of the section.  For `p = ‖A ·‖` with
`A : E → ℓ²`, the quotient seminorm is `‖P_{Mᗮ}A·‖` with `M` the closure of `A(N)`, so the completed
quotient embeds isometrically in `ℓ²` with range inside both `Mᗮ` and the range of the ambient
embedding — and that inclusion *is* the section.  This is the same orthogonal-projection mechanism
the corpus already uses for subspaces, run in the other direction.

- 2026-08-02 — Quotient seminorms, the completed quotient square, and the section criterion.

### Lean: quotients of nuclear spaces are nuclear, and `M_ζ` is nuclear `[PROVED HERE]`

`formal/GaloisForLFunctions/RHTower/DeningerQuotientHilbertian.lean` (9 declarations),
`DeningerQuotientNuclear.lean` (10), `DeningerQuotientNuclearCompleted.lean` (3) and
`DeningerMZetaNuclear.lean` (2); axiom audit `propext, Classical.choice, Quot.sound`.

Grothendieck's quotient permanence, which the corpus did not have, is now proved — by the same
Hilbertian mechanism the corpus uses for subspaces, run in the other direction:

- `deningerQuotientSeminorm_eq_norm_sub_starProjection` — for `p = ‖A·‖` the quotient seminorm by
  `N` is the distance in `ℓ²` from `A x` to the closure `M` of `A(N)`, i.e. `‖A x − P_M(A x)‖`
  (representatives ↔ the coset `A x − A(N)`, `infDist_closure`, and the minimality of the
  orthogonal projection).
- `deningerQuotient_hilbertian` — **the quotient of a Hilbertian seminorm is Hilbertian**, realized
  in the *same* `ℓ²` by the complementary projection; no Hilbert basis is needed.
- `deningerQuotientEmbeddingC_range_le`, `_mem_orthogonal` — the completed quotient realization
  lands inside the ambient range (the projection moves `A x` by an element of `M`, already there)
  and inside `Mᗮ`.
- `deningerQuotientSection`, `deningerQuotientSection_projection` — **the bounded section**: invert
  the ambient realization on its range.  Feeding it to the criterion gives
  `deningerIsNuclearSpaceC_quotient_of_hilbertian` and, via the Hilbertian refinement,
  `deningerIsNuclearSpaceC_quotient` — **quotients of nuclear spaces are nuclear.**
- `deningerNuclear_hilbertian_refinementC`, `_familyC`, `deningerIsNuclearSpaceC_quotient_of_C` —
  the same for the *completed* formulation, which is the one subspace permanence produces and
  therefore the one `ℋ_−` carries.
- `deningerIsNuclearSpaceC_mZeta` — **the cokernel `M_ζ` of the Poisson operator is a nuclear
  space**, as the quotient of the nuclear radial space by the range of `Z`.

So of the card's `(4)`, everything except *strictness* is now proved in Lean: the three spaces are
nuclear, `Z` is continuous and injective, the sequence is exact, and the image is cut out by the
zero divisor of `ζ`.  Strictness (equivalently, closed range plus the reverse estimate) remains the
single open analytic input, and it is exactly Meyer's zeta estimate.

- 2026-08-02 — **Quotient permanence for nuclearity, and `M_ζ` is nuclear.**

### Lean: towards strictness — the elementary zeta bound, the reverse Mellin estimate, and the
### Fourier reflection `[PROVED HERE]`

`formal/GaloisForLFunctions/RHTower/DeningerZetaLowerBound.lean` (4 declarations),
`DeningerPoissonReverseMellin.lean` (2) and `DeningerPoissonFourierReflection.lean` (4); axiom
audit `propext, Classical.choice, Quot.sound`.

- `norm_riemannZeta_ge_of_two_le_re` — **`|ζ(s)| ≥ 1/4` for `Re s ≥ 2`**, proved from the Dirichlet
  series: the tail is at most the Basel tail `π²/6 − 1 < 3/4`.  No zero-free region is involved;
  this is the elementary half of the multiplier estimate.
- `norm_mellin_le_of_two_le_re` — **`‖M(f)(s)‖ ≤ 4‖M(Zf)(s)‖` for `Re s ≥ 2`**: the reverse
  estimate on a line to the right of the Euler product region, i.e. the half of strictness that
  needs nothing about the zeros.  `norm_mellin_le_radial` states it against the radial
  presentation of the image.
- `deningerMeyerCap_fourierSCLM` — **Meyer's space is stable under the Fourier transform**
  (evenness is preserved, and the two boundary constraints exchange under `𝓕`, the second one
  returning by Fourier inversion).
- `deningerPoissonValue_fourier_reflection` — **`Zf(a) = a⁻¹·Z(𝓕f)(a⁻¹)`**: the Poisson operator
  carries the Fourier involution to multiplicative inversion.  This is the theta transformation in
  operator form, and it explains the card's two boundary conditions: they are exactly the two that
  make the scaled Poisson identity boundary-term free.

Where strictness stands after this.  The estimate above controls `f` on a vertical line to the
right; the reflection identity gives the mirror control for `𝓕f`.  What is *not* reachable this
way is the behaviour of `f` near the origin: bounding the Taylor coefficients of `f` at `0` by
`ℋ_−` data is bounding residues of `M(f) = M(Zf)/ζ` at the trivial zeros `s = −2, −4, …`, which
needs `ζ'(−2m) ≠ 0` and a line in `−2 < Re s < 0` where `1/ζ` is polynomially bounded — the latter
via the functional equation and the exact formula `|Γ(1+iy)|² = πy/sinh(πy)` (no Stirling needed).
That is the remaining analytic package for `(3)`–`(4)`; everything else on the card is proved.

- 2026-08-02 — The elementary zeta bound, the reverse Mellin estimate, and the Fourier reflection.

### Lean: the reverse Mellin estimate on the left line `[PROVED HERE]`

`formal/GaloisForLFunctions/RHTower/DeningerZetaLeftLine.lean` (7 declarations),
`DeningerCapVanishing.lean` (3) and `DeningerCapMellinLeft.lean` (11); axiom audit
`propext, Classical.choice, Quot.sound`.

The second vertical line of the strictness argument is now available, and — this is the point —
it needs nothing about the zeros of `ζ` either.

- `norm_Gamma_one_sub_mul_I_sq` — **`|Γ(1 − it)|² = πt/sinh(πt)`**, from Euler's reflection formula
  together with `Γ(z+1) = zΓ(z)` and `Γ(conj z) = conj Γ(z)`.  No Stirling.
- `one_add_sq_le_cosh_sq_mul_gamma` — **`1 + t² ≤ cosh²(πt/2)|Γ(2 − it)|²`**, using the elementary
  `sinh u ≤ u cosh u` (the corpus already owned it in `CothInfra`).
- `norm_riemannZeta_left_line_ge` — **`|ζ(−1+it)| ≥ √(1+t²)/(8π²)`**: the functional equation
  trades the value on `Re s = −1` for one on `Re s = 2`, where the Dirichlet series bounds it, times
  an archimedean factor that only grows.  Hence `1/|ζ|` is *bounded* on that line.
- `deriv_zero_of_even_schwartzMap`, `norm_le_seminorm_mul_sq` — a member of Meyer's space vanishes
  to **second order** at the origin (`‖f x‖ ≤ p₀,₀(f'')x²`), by two mean-value steps.
- `mellinConvergent_cap`, `differentiableAt_mellin_cap` — consequently `M(f)` is holomorphic on
  `Re s > −2`.
- `mellin_deningerPoissonValue_eq_zeta_mul_left` — the factorization `M(Zf) = ζM(f)` propagates to
  that half plane (identity theorem on the same two-convex-open region, now based at `−2`).
- `norm_mellin_le_left_line` — **`‖M(f)(−1+it)‖ ≤ 8π²‖M(Zf)(−1+it)‖` for `t ≠ 0`** (the single
  real point is a null set, so this is all an integral estimate needs).

Both halves of the multiplier estimate are now proved: `Re s = 2` (elementary Dirichlet bound) and
`Re s = −1` (functional equation + exact Gamma modulus).  What remains for strictness is the
inversion plumbing: the log-coordinate weights of a member of Meyer's space are Schwartz, hence
`VerticalIntegrable (mellin f) σ` for `σ ∈ {−1, 2}`, and then `mellinInv_mellin_eq` converts the two
line estimates into `sup`-bounds for `f` — with the Fourier reflection supplying the mirror bounds
for `𝓕f`, which is what controls the derivatives near the origin.

- 2026-08-02 — **The reverse Mellin estimate on a line left of the critical strip.**

### Record — strictness: the inversion machine (Lean)

Five further modules, all built clean under `lake build`, turn the two line estimates for `1/ζ`
into control of `f` by the radial data of `Zf`.

* `RHTower/DeningerCapInversion.lean`
  - `deningerReflect` — reflection of a Schwartz map.
  - `mellin_deningerPoissonValue_eq_fourier` — on a vertical line the Mellin transform of `Zf` is
    the Fourier transform of the reflected logarithmic weight.
  - `verticalIntegrable_mellin_poisson` — hence integrable on every vertical line.
  - `norm_mellinInv_le`, `norm_le_mellin_line` — **the inversion bound**
    `‖f x‖ ≤ (2π)⁻¹ x^{-σ} ∫‖M(f)(σ+iy)‖dy` for every integer `σ ≥ −1`.
* `RHTower/DeningerStrictLineBounds.lean`
  - `deningerLineNorm σ g = ∫‖M(g)(σ+iy)‖dy`.
  - `deningerLineNorm_le_right/_left` — the `1/ζ` multiplier estimates transported to the line
    norms (factor `4` for `σ ≥ 2`, factor `8π²` on `σ = −1`; the left line uses that `{0}` is null).
  - `norm_le_of_poisson_right/_left` — **`‖f x‖ ≤ C x^{-σ}·L_σ(Zf)`** and **`‖f x‖ ≤ C x·L_{-1}(Zf)`**.
  - `integral_norm_le_seminorm` — `∫‖h‖ ≤ π(p₀,₀(h)+p₂,₀(h))` for Schwartz `h`.
  - `deningerLineNorm_poisson_eq/_le`, `exists_bound_deningerLineNorm` — **the line norm of `Zf` is
    bounded by finitely many Schwartz seminorms of the weight `Z_σ f`**, i.e. by radial data.
* `RHTower/DeningerCapSupBound.lean`
  - `abs_pow_mul_norm_le`, `seminorm_zero_le_lineNorm`, `exists_bound_seminorm_zero` —
    **`p_{m,0}(f) ≤ C·(radial data of `Zf` at the two indices `m+2` and `−1`)`**: the far end from
    the line `Re s = m+2`, the origin from the line `Re s = −1`, `x = 0` from `f(0) = 0`, and
    negative `x` from evenness.
* `RHTower/DeningerFourierWeight.lean`
  - `exists_bound_seminorm_comp_pair`, `exists_bound_schwartzSup_comp` — generic seminorm bounds
    for a continuous operator (all bi-indices, and finite suprema).
  - `deningerPoissonSchwartz_fourier` — **the weights of `Z𝓕f` are the reflected weights of `Zf`**,
    `Z_s(𝓕f) = reflect Z_{1−s}(f)`; the Poisson operator carries the Fourier involution to the
    reflection `s ↦ 1 − s` of the weight index.
  - `exists_bound_seminorm_zero_fourier` — **`p_{m,0}(𝓕f)` is bounded by the radial data of `f`**
    (at the indices `1−(m+2)` and `2`).
* `RHTower/DeningerCapDerivBound.lean`
  - `norm_fourier_le_integral`, `norm_le_integral_norm_fourier` — Fourier inversion as a supremum
    bound.
  - `norm_fourier_derivSCLM`, `norm_fourier_iterate_derivSCLM` — the multiplier `(2π|ξ|)^n`.
  - `integral_pow_norm_fourier_le`, `seminorm_zero_deriv_le_fourier` —
    **`p_{0,n}(f) ≤ (2π)^n π (p_{n,0}(𝓕f) + p_{n+2,0}(𝓕f))`**: every derivative supremum of `f` is
    controlled by two weighted suprema of `𝓕f`, hence by the radial data of `Zf`.

What remains for the full strict-morphism statement is the dilation bookkeeping at the far end: the
identity `x^n f^{(n)} = ∑_{j≤n} s(n,j) θ^j f` (signed Stirling numbers, from the recursion
`U_{n+1} = θU_n − nU_n`), which converts the derivative seminorms for `|x| ≥ 1` into supremum
seminorms of the Euler iterates `θ^j f` — themselves members of Meyer's space whose weights are
derivatives of the weights of `f`.  Near the origin the derivative bound above already applies, so
the two regions together give `p_{k,n}(f) ≤ C·(radial data)`, the reverse of
`deningerPoissonLM_bound`.

### Record — the Poisson operator is a strict morphism (Lean, unconditional)

Three further modules close the strictness statement.  `#print axioms` on each headline theorem
returns exactly `[propext, Classical.choice, Quot.sound]`.

* `RHTower/DeningerEulerStirling.lean`
  - `deningerWeightedDerivCLM` — the operator `U_n : f ↦ x^n f^{(n)}`.
  - `deningerWeightedDerivCLM_succ_apply` — **the recursion `U_{n+1} = θU_n − nU_n`** (product rule).
  - `deningerStirling`, `deningerStirling_eq_zero`, `deningerWeightedDerivCLM_eq_sum` —
    **`x^n f^{(n)} = ∑_{j≤n} s(n,j) θ^j f`**, the falling factorial `θ(θ−1)⋯(θ−n+1)`.
  - `seminorm_le_weightedDeriv` — `p_{k,n}(f) ≤ p_{0,n}(f) + p_{k,0}(U_n f)`: the origin is covered
    by the derivative supremum, the far end by the weighted derivative.
  - `seminorm_sum_le`, `seminorm_weightedDeriv_le_euler`.
* `RHTower/DeningerRadialEulerData.lean`
  - `deningerMeyerCap_eulerSCLM_iterate` — Meyer's space is stable under `θ^j`.
  - `deningerEulerWeightCLM`, `deningerPoissonSchwartz_eulerSCLM`,
    `deningerPoissonSchwartz_euler_iterate` — **`Z_τ(θ^j f) = (D − τ)^j Z_τ(f)`**: the Poisson
    operator conjugates the Euler operator into `D − τ` on the `τ`-th weight.
  - `exists_bound_schwartzSup_euler` — hence the radial data of `θ^j f` is bounded by that of `f`.
* `RHTower/DeningerPoissonStrict.lean`
  - `deningerRadialData` — the finite radial datum `∑_{s ∈ S} (sup_K p)(Z_s f)`, with
    monotonicity lemmas.
  - `exists_bound_seminorm_zero_deriv_radial` — the derivative suprema, through the Fourier side.
  - `exists_bound_seminorm_zero_euler_radial`, `exists_bound_sum_euler_radial` — the Euler iterates.
  - `exists_bound_seminorm_radial` — **every Schwartz seminorm `p_{k,n}(f)` of a member of Meyer's
    space is bounded by finitely many seminorms of the radial datum of `Zf`.**
  - `exists_bound_schwartzSup_radial` — the same for finite suprema.
  - `deningerPoissonLM_strict` — **the Poisson operator is a strict morphism**: for every seminorm
    index `K₀` there are a radial index `i` and a constant `C` with
    `p_{K₀}(f) ≤ C · q_i(Z f)` for all `f ∈ ℋ_∩`.

Together with `deningerPoissonLM_bound` (continuity) and `deningerPoissonLM_injective` this makes
`Z : ℋ_∩ → ℋ_−` a topological isomorphism onto its image — statement (3) of the card, proved
unconditionally in Lean.

The mechanism, in one line: on the two vertical lines `Re s = σ ≥ 2` and `Re s = −1` the multiplier
`1/ζ` is bounded (elementary Dirichlet bound on the right, functional equation plus
`|Γ(1−it)|² = πt/sinh(πt)` on the left), so Mellin inversion recovers `f` from `Zf` with control;
the origin is reached through the Fourier involution, which the Poisson operator turns into the
reflection `s ↦ 1 − s` of the weight index; and the far end is reached through the dilation flow,
which the Poisson operator turns into differentiation of the weight.

### Record — closed range, completeness, and the separated cokernel (Lean, unconditional)

The missing analytic ingredient for "closed embedding" was the completeness of Schwartz space,
which mathlib does not have.  It is now proved in the corpus, and statement (3) closes with it.
`#print axioms` on each headline theorem returns `[propext, Classical.choice, Quot.sound]`.

* `HTGeometry/SchwartzComplete.lean` — **`𝓢(ℝ, ℂ)` is complete** (absent from mathlib).
  - `derivPowSCLM` — the iterated derivative as a continuous operator, with the seminorm bounds
    `‖(D^n f)(x)‖ ≤ p_{0,n}(f)` and `|x|^k‖(D^n f)(x)‖ ≤ p_{k,n}(f)`.
  - `schwartzUniformityCountablyGenerated` — the uniformity is countably generated, so sequential
    completeness suffices.
  - `exists_seminorm_lt_of_cauchySeq`, `exists_schwartzSup_lt_of_cauchySeq`,
    `exists_seminorm_bound_of_cauchySeq`, `cauchySeq_of_seminorm` — the Cauchy condition in the
    seminorms, both directions.
  - `schwartzLimitDeriv`, `tendstoUniformly_schwartzLimitDeriv`, `hasDerivAt_schwartzLimitDeriv`,
    `contDiff_schwartzLimitDeriv`, `iteratedDeriv_schwartzLimitDeriv` — each iterated derivative
    converges uniformly, and the limit of the derivatives is the derivative of the limit.
  - `schwartzCauchyLimit`, `tendsto_schwartzCauchyLimit`, `instCompleteSpaceSchwartzMap`.
* `RHTower/DeningerPoissonClosedRange.lean`
  - `deningerPoissonSchwartz_sub` — the weights are linear in the function.
  - `instCompleteSpaceDeningerMeyerCap` — Meyer's space is complete, being closed in `𝓢(ℝ, ℂ)`.
  - `deningerPoisson_range_isClosed` — **the image of the Poisson operator is closed**: a sequence
    in the image whose radial data converge has, by the strictness bounds, a Cauchy sequence of
    preimages; the limit lies in Meyer's space and its Poisson sum is the limit.
* `RHTower/DeningerRadialFrechet.lean`
  - `deningerRadialCompat_isClosed`, `instCompleteSpaceDeningerRadialCompat` — the radial space is
    closed in the countable product, hence complete.
  - `deningerMZeta_t2Space` — **the cokernel `M_ζ` is separated.**
  - `deningerMZetaMk_isOpenMap` — **the projection onto `M_ζ` is open.**

Statement (3) is therefore complete in Lean: `Z : ℋ_∩ → ℋ_−` is continuous
(`deningerPoissonLM_bound`), injective (`deningerPoissonLM_injective`), strict
(`deningerPoissonLM_strict`) and has closed range (`deningerPoisson_range_isClosed`) — a strict
closed embedding.  Statement (4) is a strict exact sequence of nuclear spaces: exactness
(`deningerPoisson_exact`), nuclearity of all three terms
(`deningerIsNuclearSpaceC_meyerCap`, `deningerIsNuclearSpaceC_radialCompat`,
`deningerIsNuclearSpaceC_mZeta`), strictness at `ℋ_∩` and at `ℋ_−`, and separation of the
cokernel; both `ℋ_∩` and `ℋ_−` are complete and first countable, i.e. Fréchet.

### Record — §1 closed out (Lean, unconditional)

* `HTGeometry/SchwartzComplete.lean` also carries `instMetrizableSpaceSchwartzMap`: the uniformity
  is countably generated and the space is separated, so `𝓢(ℝ, ℂ)` is metrizable — with completeness
  this makes it a Fréchet space.
* `RHTower/DeningerFrechetProperties.lean`
  - `instPseudoMetrizableSpaceDeningerMeyerCap`, `instPseudoMetrizableSpaceDeningerRadialCompat` —
    both source spaces are metrizable.
  - `instIsUniformAddGroupDeningerRadialCompat` — the radial space is a uniform additive group.
  - `deningerMZeta_completeSpace` — **the cokernel is complete** (Bourbaki: quotient of a complete
    first countable topological group).

**Section 1 of this card is now fully formalized, unconditionally.**  Statements `(1)`–`(4)`:

| claim | Lean |
|---|---|
| `ℋ_−` nuclear | `deningerIsNuclearSpaceC_radialCompat` |
| `ℋ_∩` nuclear | `deningerIsNuclearSpaceC_meyerCap` |
| both Fréchet | `instCompleteSpaceSchwartzMap`, `instCompleteSpaceDeningerMeyerCap`, `instCompleteSpaceDeningerRadialCompat`, metrizability instances |
| `Z` continuous | `deningerPoissonLM_bound` |
| `Z` injective | `deningerPoissonLM_injective` |
| `Z` strict | `deningerPoissonLM_strict` |
| `Z` closed range | `deningerPoisson_range_isClosed` |
| exactness at `ℋ_−` | `deningerPoisson_exact` |
| `M_ζ` nuclear | `deningerIsNuclearSpaceC_mZeta` |
| `M_ζ` separated, complete | `deningerMZeta_t2Space`, `deningerMZeta_completeSpace` |
| projection strict | `deningerMZetaMk_isOpenMap` |

Remaining on this card: §2 (strict tensor transport) and §3 (angular cosheaf contraction).  Both
need infrastructure absent from mathlib — the completed projective tensor product of locally convex
spaces for §2, and topological singular chains for §3.  Next build unit: the projective tensor
seminorm `p ⊗ q` on `E ⊗[𝕜] F` for seminorms `p, q`, its universal property for bounded bilinear
maps, and the completion of the algebraic tensor product in that topology.
