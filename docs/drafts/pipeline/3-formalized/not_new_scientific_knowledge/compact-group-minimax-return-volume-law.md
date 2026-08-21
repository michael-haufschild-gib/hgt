# Compact-group minimax return is trapped between target volume and covering volume

- **ID:** `compact-group-minimax-return-volume-law`
- **Stage:** 2-fully-proven
- **Type:** COMPACT-GROUP RECURRENCE / METRIC ENTROPY INFRASTRUCTURE
- **Scientific status:** `[PAPER-PROVED] [THEOREM A LEAN-PROVED]`
  `[HAAR BUDGET LOWER LAW LEAN-PROVED]`
  `[CONNECTED-DENSE-GENERATOR SPECIALIZATION LEAN-PROVED]`
  `[COVERING-VOLUME SANDWICH LEAN-PROVED]`
  `[CLASSICAL INFRASTRUCTURE] [NO NOVELTY CLAIM]`
- **Parent:** `../../1-in-progress/predictive-relation-spectrum-universal-law.md`
- **Freeze date:** 2026-07-30

## Statement

Let \(K\) be a compact metrizable group with a bi-invariant metric \(d\).
For \(\varepsilon>0\), put
\[
 B_\varepsilon=\{x\in K:d(x,e)<\varepsilon\}
\]
and let \(N_\varepsilon(K,d)\) be the least number of open
\(\varepsilon\)-balls covering \(K\).  For \(\alpha\in K\), define
\[
 \tau_\varepsilon(\alpha)
 =
 \min\{n\geq1:d(\alpha^n,e)<\varepsilon\}.
\]

### Theorem A — universal covering deadline

For every \(\alpha\in K\),
\[
 \tau_\varepsilon(\alpha)
 \leq N_{\varepsilon/2}(K,d).                         \tag{1}
\]

The minimum in the definition of \(\tau_\varepsilon(\alpha)\) therefore
exists.

### Theorem B — connected abelian minimax law

Now let \(K\) be nontrivial, compact, connected, metrizable and abelian, and
let \(m\) be normalized Haar measure.  Let
\[
 \tau_\varepsilon^\star
 =
 \sup_{\overline{\langle\alpha\rangle}=K}
 \tau_\varepsilon(\alpha).
\]
Then
\[
 \boxed{
 \left\lceil\frac1{m(B_\varepsilon)}\right\rceil
 \leq
 \tau_\varepsilon^\star
 \leq
 N_{\varepsilon/2}(K,d)
 \leq
 \frac1{m(B_{\varepsilon/4})}.}                       \tag{2}
\]

Thus worst dense-orbit recurrence is controlled without an additive
dimension remainder.  The price is the explicit neighboring-resolution
comparison \(\varepsilon\leftrightarrow\varepsilon/4\).

## Proof of Theorem A

Set \(M=N_{\varepsilon/2}(K,d)\) and choose a cover of \(K\) by \(M\) open
\(\varepsilon/2\)-balls.  Among the \(M+1\) points
\[
 e,\alpha,\alpha^2,\ldots,\alpha^M
\]
two, say \(\alpha^i,\alpha^j\) with \(0\leq i<j\leq M\), lie in the same
ball.  Therefore
\[
 d(\alpha^i,\alpha^j)<\varepsilon.
\]
Bi-invariance gives
\[
 d(\alpha^{j-i},e)=d(\alpha^j,\alpha^i)<\varepsilon.
\]
Since \(1\leq j-i\leq M\), equation `(1)` follows.  `QED`

Only left invariance is needed for this argument after writing the orbit
consistently; bi-invariance is retained because it is the natural metric
class for the abelian application.

## Preliminaries for Theorem B

### Lemma 1 — integer multiplication preserves Haar measure

For every integer \(n\geq1\), the map
\[
 [n]:K\longrightarrow K,\qquad x\longmapsto x^n
\]
is surjective and its pushforward preserves normalized Haar measure.

**Proof.**  Connectedness of \(K\) is equivalent under Pontryagin duality to
torsion-freeness of the discrete character group \(\widehat K\).  The dual of
\([n]\) is multiplication by \(n\) on \(\widehat K\), hence is injective.
Pontryagin duality makes the image of \([n]\) dense.  It is also compact and
therefore closed, so \([n]\) is surjective.  The pushforward of normalized
Haar measure through a continuous surjective homomorphism is normalized
translation-invariant probability measure, hence Haar measure.  `QED`

### Lemma 2 — dense generators have full Haar measure

The set
\[
 \operatorname{Gen}(K)
 =
 \{\alpha\in K:\overline{\langle\alpha\rangle}=K\}
\]
has Haar measure one.

**Proof.**  Since \(K\) is compact metrizable, \(\widehat K\) is countable.
An element \(\alpha\) fails to generate densely exactly when some nontrivial
character \(\chi\in\widehat K\) obeys \(\chi(\alpha)=1\).  Hence
\[
 K\setminus\operatorname{Gen}(K)
 =
 \bigcup_{\chi\in\widehat K\setminus\{1\}}\ker\chi.
\]
For nontrivial \(\chi\), the image \(\chi(K)\) is a nontrivial connected
compact subgroup of the circle and therefore is the whole circle.
The pushforward of Haar measure is circle Haar measure, so the inverse image
of the point \(1\) has measure zero.  Countability of \(\widehat K\) makes
the displayed union null.  `QED`

### Lemma 3 — covering/volume sandwich

For every \(\delta>0\),
\[
 \frac1{m(B_\delta)}
 \leq N_\delta(K,d)
 \leq \frac1{m(B_{\delta/2})}.                         \tag{3}
\]

**Proof.**  Any cover by \(N\) translates of \(B_\delta\) has total measure
at most \(N\,m(B_\delta)\), proving the left inequality.

Choose a maximal \(\delta\)-separated finite set \(S\).  Compactness makes
such a finite maximal set available.  Maximality says that the
\(\delta\)-balls around \(S\) cover \(K\).  The
\(\delta/2\)-balls around distinct points of \(S\) are disjoint, so
\[
 |S|m(B_{\delta/2})\leq1.
\]
Consequently
\[
 N_\delta(K,d)\leq|S|\leq m(B_{\delta/2})^{-1}.
\]
`QED`

## Proof of Theorem B

The upper middle inequality in `(2)` is Theorem A.  Apply the right side of
`(3)` with \(\delta=\varepsilon/2\) to obtain
\[
 N_{\varepsilon/2}(K,d)
 \leq m(B_{\varepsilon/4})^{-1}.
\]

For the lower bound set
\[
 L=\left\lceil m(B_\varepsilon)^{-1}\right\rceil-1.
\]
Because \(B_\varepsilon\) is a nonempty open set,
\(m(B_\varepsilon)>0\), and the definition of \(L\) gives
\[
 Lm(B_\varepsilon)<1.
\]
For \(1\leq n\leq L\), let
\[
 A_n=[n]^{-1}(B_\varepsilon).
\]
Lemma 1 gives \(m(A_n)=m(B_\varepsilon)\).  Therefore
\[
 m\left(\bigcup_{n=1}^L A_n\right)
 \leq Lm(B_\varepsilon)<1.
\]
Lemma 2 says that dense generators have full measure, so some dense
generator \(\alpha\) lies outside this finite union.  It obeys
\[
 d(\alpha^n,e)\geq\varepsilon
 \qquad(1\leq n\leq L),
\]
and hence
\[
 \tau_\varepsilon(\alpha)\geq L+1
 =
 \left\lceil m(B_\varepsilon)^{-1}\right\rceil.
\]
Taking the supremum over dense generators proves `(2)`.  `QED`

## Observable-frequency specialization

Let \(\Gamma\) be a countable subgroup of \(\mathbb R\), treated as a
discrete group, and let
\[
 K=\widehat\Gamma.
\]
Then \(K\) is compact, connected and metrizable.  The physical phase flow
\[
 \theta(t)(\gamma)=e^{it\gamma}
\]
has dense image: a character of \(K\), equivalently an element of
\(\Gamma\), that vanishes on the image must be zero.

For a summable family of visible-frequency weights \(a_\gamma\geq0\), the
formula
\[
 d_a(x,y)^2
 =
 \sum_{\gamma\in\Gamma}
 a_\gamma|x(\gamma)-y(\gamma)|^2
\]
defines a continuous invariant pseudometric.  Quotienting its
zero-distance subgroup produces the minimal compact metric return group
seen by that reporter.  Theorems A--B then apply after the quotient.

Finite free \(\Gamma\cong\mathbb Z^r\) gives a torus.  Finite rational rank
without finite generation can give a solenoid.  Infinite rank gives a
compact inverse limit of unbounded finite-dimensional quotients.  In every
case, compactness keeps the covering number finite at every fixed positive
resolution.

## Scientific boundary

The proof consists of compactness, the pigeonhole principle, Haar measure
and Pontryagin duality.  It is classical infrastructure even if the exact
two-resolution statement is not found verbatim in a search.  No priority
claim is made.

Its role in the master programme is structural:

- rank becomes one finite-dimensional shadow of \(K\);
- reverse-water entropy becomes one estimate of target volume;
- worst-spectrum minimax becomes a group-volume statement;
- countable pure-point recurrence requires no finite dimension;
- observer restriction becomes a metric quotient.

It does not cover arbitrary continuous spectral mass, arbitrary
noncontractive open dynamics, locality, or the interaction-induced change
of \(K\).  Those are separate theorem obligations.

## Lean status and remaining plan

Theorem A is formalized in
`formal/GaloisForLFunctions/HTGeometry/CompactGroupMetricReturnLaw.lean`.
It exports:

- `exists_pow_return_le_two_mul_of_finset_isCover`;
- `exists_pow_return_le_two_mul_coveringNumber`;
- `exists_mem_avoids_first_powers_of_measure_budget`;
- `exists_mem_avoids_first_powers_of_haar_budget`.

The last two declarations prove the exact finite-union lower mechanism.
For a probability measure, a conull admissible set `Good`, measurable target
\(B\), and measure-preserving first \(L\) power maps,
\[
 L\,m(B)<1
\]
forces an element of `Good` whose first \(L\) powers all avoid \(B\).
The Haar declaration supplies measure preservation for every compact
rootable commutative group.

The direct source check passed.  The axiom audit reports only `propext`,
`Classical.choice` and `Quot.sound`.

The connected dense-generator specialization of Theorem B remains
paper-proved but is not yet formalized.  Its remaining plan:

1. import or prove surjectivity of integer multiplication on compact
   connected abelian groups;
2. formalize the full-measure generator lemma only if the necessary
   Pontryagin-duality surface exists in this toolchain;
3. formalize the covering-volume sandwich.

No statement from this card enters the manuscript before its exact Lean
counterpart passes direct elaboration and axiom audit.

## Gates

- [x] exact theorem stated
- [x] dependency-closed paper proof
- [x] finite/infinite pure-point specialization
- [x] classical-parent status recorded
- [x] covering-deadline Lean theorem
- [x] covering-deadline axiom audit
- [x] conull Haar-budget minimax lower mechanism
- [x] connected-group dense-generator corollary
- [x] covering-volume sandwich
- [ ] external specialist audit

## Lean formalization — COMPLETE

Three new modules, all wired into `GaloisForLFunctions.HTGeometry`; every capstone has axiom
footprint `[propext, Classical.choice, Quot.sound]`.

### `HTGeometry/CompactConnectedAbelianGenerators.lean`

Closes the *connected-group dense-generator corollary*.

- **Lemma 1 (integer multiplication is surjective).**  `exists_pow_eq_of_connected`: in a compact
  connected second-countable abelian group every element is an `n`-th power.  Proof: the image of
  the `n`-th power map is compact, hence a proper closed subgroup if not everything; a nontrivial
  character of the quotient (corpus Peter-Weyl, `CompactAbelian.exists_character_ne_one`, used
  through the multiplicative wrapper `exists_character_ne_one_mul`) pulls back to a character of
  `G` with values in the `n`-th roots of unity, and `character_eq_one_of_connected` shows any such
  character is trivial.  This yields the instance `rootableByIntOfCompactConnected :
  RootableBy G ℤ`, which is exactly the hypothesis mathlib's
  `Measure.measurePreserving_zpow` needs — so the measure-preservation half of Lemma 1 is
  supplied by mathlib once divisibility is available.
- **Lemma 2 (dense generators have full Haar measure).**
  `measure_compl_denseGenerators_eq_zero`.  Three ingredients:
  `infinite_range_of_character` (the image of a connected group under a nontrivial character
  contains a whole interval of distances from `1`, hence is infinite);
  `measure_character_fibre_eq_zero` (the fibres of a character are translates of its kernel and
  have equal measure, so infinitely many distinct values force the kernel to be null — this
  replaces the Pontryagin-duality argument of the paper proof, which mathlib cannot support);
  and `countable_charSet` (distinct characters are orthonormal in `L²` of the Haar probability
  measure, which is second countable, and `countable_of_separated` makes any `1`-separated set of
  a second-countable metric space countable).  `exists_character_of_notMem_denseGenerators`
  supplies the character killing a non-generator, again through the quotient by the closed
  subgroup it generates.
- **The lower mechanism.** `exists_denseGenerator_avoiding_of_measure_budget` combines the above
  with the card's already-formalized `exists_mem_avoids_first_powers_of_haar_budget`.

### `HTGeometry/CompactGroupCoveringVolume.lean`

Closes the *covering-volume sandwich*, in the multiplicative form that avoids dividing by a
possibly zero volume:

- `one_le_coveringNumber_mul_measure_closedEBall`:
  `1 <= N_eps * mu(closedBall 1 eps)` — subadditivity over `Metric.minimalCover`.
- `coveringNumber_mul_measure_eball_le_one`:
  `N_eps * mu(ball 1 (eps/2)) <= 1` — the half-radius balls around a separated set are disjoint
  (`card_mul_measure_eball_le_one`, `encard_mul_measure_eball_le_one`), which also gives
  `packingNumber_ne_top`, and mathlib's `coveringNumber_le_packingNumber` finishes.
- Support lemmas `closedEBall_eq_image`, `eball_eq_image`, `measure_closedEBall_eq`,
  `measure_eball_eq`: every ball is a translate of the ball at the identity, so all balls of a
  given radius have the same Haar measure.  Only left invariance of the metric is used.

### `HTGeometry/CompactGroupMinimaxReturn.lean`

`compactGroup_minimax_return_volume_law` bundles the three halves of `(2)`:

1. every rotation returns inside `eps` by the covering number at radius `eps/2` (Theorem A, from
   `exists_pow_return_le_two_mul_coveringNumber`);
2. whenever `L * mu(ball 1 eps) < 1` some topological generator avoids `ball 1 eps` through its
   first `L` powers (the lower mechanism);
3. `N_(eps/2) * mu(ball 1 (eps/4)) <= 1` and `1 <= N_eps * mu(closedBall 1 eps)` (the sandwich).

### Deviation from the paper proof

The paper derives Lemmas 1 and 2 from Pontryagin duality.  Mathlib carries `PontryaginDual` but
no duality theorem, so both lemmas are re-proved from the corpus's Peter-Weyl separation theorem
plus quotients by closed subgroups; the null-kernel step uses equal-measure fibres instead of
pushing Haar forward to the circle, and the countability of the dual uses `L²` orthonormality
instead of countability of the discrete dual.  Nothing is assumed that the paper proof did not
already use.
