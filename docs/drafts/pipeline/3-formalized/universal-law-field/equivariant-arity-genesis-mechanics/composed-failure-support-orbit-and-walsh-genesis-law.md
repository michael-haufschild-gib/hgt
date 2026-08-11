# Composed-failure support-orbit and Walsh-genesis law

- **ID:** ULF-EAG-2
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / LAW-GENESIS MECHANISM
- **Source:** ULF-EAG-1 composed-failure question
- **Statement:** Independent unoriented failures force one nontrivial response orbit for every
  nonempty interaction support; the sharp deterministic response size is
  `2^(n+1)-1`, and equality forces the parity/Walsh quotient.
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [LEAN-CERTIFIED] [NOT RH]

## 1. Failure process

Let `I` be a finite set of failure coordinates and write

\[
 G_I=(\mathbb Z/2)^I,
 \qquad
 X_I=\{0,+,-\}^I.
\]

The value `0` means that a failure coordinate is inactive.  The two signs are an unoriented failed
pair.  The group `G_I` flips signs independently and fixes inactive coordinates.  For `x in X_I`
write

\[
 \operatorname{supp}(x)=\{i:x_i\ne0\}.
\]

Let `Y` be an arbitrary `G_I`-set.  A deterministic successor reporter is a map

\[
 q:X_I\longrightarrow Y.
\]

It is **legal** when it obeys two source-first laws.

1. `q` is `G_I`-equivariant.
2. It is contextwise resolving: if `i in supp(x)`, flipping coordinate `i` changes `q(x)`.

The second law is stronger than separating one preferred failed pair.  Every active failure must
remain detectable in every context created by the other failures.

## 2. The theorem

Put `n=|I|`.

### Theorem 2.1 -- support separation and sharp deterministic arity

Every legal deterministic reporter satisfies:

1. if `q(x)=q(z)`, then `supp(x)=supp(z)`;
2. for every nonempty support `S subset I`, the image of the support-`S` orbit has at least two
   elements;
3. therefore

\[
 \boxed{\ |\operatorname{im}q|\ge
  1+2(2^n-1)=2^{n+1}-1.\ }
\tag{EAG2.1}
\]

The bound is attained by the canonical reporter

\[
 q_{\rm can}(x)=
 \begin{cases}
  *,&\operatorname{supp}(x)=\varnothing,\\
  \bigl(\operatorname{supp}(x),
  \sum_{i\in\operatorname{supp}(x)}[x_i=-]\bmod2\bigr),&\text{otherwise}.
 \end{cases}
\tag{EAG2.2}
\]

Hence the minimum deterministic response image has one fixed background value and one two-point
orbit for every nonempty failure support.

### Theorem 2.2 -- equality rigidity

If equality holds in `(EAG2.1)`, then for all `x,z in X_I`,

\[
 q(x)=q(z)
 \quad\Longleftrightarrow\quad
 \operatorname{supp}(x)=\operatorname{supp}(z)
 \text{ and }
 \operatorname{par}(x)=\operatorname{par}(z),
\tag{EAG2.3}
\]

where `par` is the sign parity on the common support.  Consequently the image of every sharp
reporter is uniquely isomorphic, as a marked `G_I`-set, to the image of `q_can`.

Sharp deterministic composition does not merely remember the `n` elementary failures.  It creates
exactly one parity/Walsh channel for every nonempty subset of failures.

### Theorem 2.3 -- block composition and mixed-channel birth

For disjoint finite failure blocks `A,B`, let

\[
 c(A)=2^{|A|}-1
\]

be the number of nontrivial sharp response orbits.  Then

\[
 \boxed{\ c(A\sqcup B)=c(A)+c(B)+c(A)c(B).\ }
\tag{EAG2.4}
\]

The first two summands are the old block channels.  The product term counts supports meeting both
blocks.  Thus composition forces

\[
 2c(A)c(B)
\]

new deterministic response values not present in either block alone.  Two one-failure blocks have
minimum image size seven: one background value, two elementary two-orbits, and one mixed two-orbit.

### Theorem 2.4 -- convex doctrine exchange

Assume `I` is nonempty.  Let the pure outcome set be

\[
 Z_I=I\times\{+,-\},
\]

with coordinate `i` swapping only the two outcomes over `i`.  There is an equivariant,
contextwise-resolving probability reporter

\[
 \mu:X_I\longrightarrow\Delta(Z_I)
\tag{EAG2.5}
\]

using only `2n` pure outcomes.

Explicitly, put `delta=1/(4n)`.  In the pair over `i`, an inactive coordinate gives weights
`(1/(2n),1/(2n))`; an active sign gives weight `1/(2n)+delta` to its matching outcome and
`1/(2n)-delta` to the opposite outcome.  Every pair has total mass `1/n`, so the full mass is one.
All weights are positive.  Independent flips permute the weights, and flipping an active coordinate
changes its unequal pair.

This does not contradict `(EAG2.1)`: the response values now live in a convex continuum, and the
map `(EAG2.5)` is in fact injective.  What changes is the size of the **pure outcome doctrine**.
Deterministic response labels require exponentially many marked values; convex mixtures realize
the same composed failure process with linearly many pure outcomes.

## 3. Proof

### 3.1 Support separation

Suppose `q(x)=q(z)` and their supports differ.  Choose

\[
 i\in\operatorname{supp}(x)\setminus\operatorname{supp}(z)
\]

after exchanging `x,z` if necessary.  Let `e_i in G_I` be the elementary flip.  Since coordinate
`i` is inactive in `z`, `e_i z=z`.  Equivariance gives

\[
 e_i q(x)=e_i q(z)=q(e_i z)=q(z)=q(x).
\]

But `i` is active in `x`, so contextwise resolution says `e_i q(x)=q(e_i x) ne q(x)`, a
contradiction.  Hence equal reporter values have equal support.

### 3.2 Lower bound

For a fixed support `S`, all sign choices form one transitive `G_I`-orbit.  Equivariance therefore
makes their image one target orbit.  If `S` is nonempty, choose `i in S`; the elementary flip
changes the reporter value, so this target orbit contains at least two elements.  The empty-support
stratum contains one source point and contributes one value.

By support separation, target images from distinct supports are disjoint.  There are `2^n-1`
nonempty supports.  Summing the stratum bounds proves `(EAG2.1)`.

### 3.3 Sharp construction

Support is unchanged by every sign flip.  On a nonempty support `S`, a group element `g` changes
the parity in `(EAG2.2)` by

\[
 \chi_S(g)=\sum_{i\in S}g_i\pmod2.
\]

This defines the target action and proves equivariance.  An elementary active flip changes parity,
so the reporter is contextwise resolving.  Every marked support/parity pair is attained, proving
surjectivity and sharpness.

### 3.4 Equality rigidity

Assume equality in `(EAG2.1)`.  Every nonempty support stratum must attain its lower bound exactly,
so its image is a transitive two-point `G_I`-set.  Fix a value `y_S` on this orbit.  Its action gives
a nonzero homomorphism

\[
 \phi_S:G_I\longrightarrow\mathbb Z/2
\]

whose kernel is the stabilizer of `y_S`.  Every elementary flip outside `S` fixes every source
point in the support-`S` stratum and hence lies in `ker(phi_S)`.  Every elementary flip inside `S`
changes the reporter value and hence maps to `1`.  The elementary flips form a basis of `G_I`, so

\[
 \phi_S=\chi_S.
\]

Two support-`S` configurations therefore have the same reporter value exactly when the group
element carrying one to the other has even `S`-parity.  Together with support separation this is
`(EAG2.3)` and gives the marked isomorphism with `q_can`.

### 3.5 Block composition

A nonempty subset of `A disjoint-union B` lies only in `A`, only in `B`, or meets both.  These three
classes have cardinalities

\[
 c(A),\qquad c(B),\qquad c(A)c(B),
\]

respectively.  This proves `(EAG2.4)`.  Each support contributes one two-point response orbit, so
the mixed value count is twice the product term.

### 3.6 Convex repair

The explicit weights in Theorem 2.4 are positive and sum to one.  A coordinate flip exchanges its
two pure outcomes and leaves every other pair fixed, which is exactly the transformation of the
assigned probability vector.  If the source coordinate is active, its two weights differ by
`2 delta`, so the probability vector changes under the flip.  This proves equivariance and
contextwise resolution.

## 4. Mechanism interpretation

This theorem supplies a composition law for ULF-EAG-1.

1. **Failure support is generated state.**  Inactive versus active coordinates have different
   isotropy, and equivariance prevents a legal deterministic test from silently identifying them.
2. **Interactions are forced.**  Combining failure blocks births mixed support channels.  They are
   not optional features added after seeing a target.
3. **Walsh sectors are a sharp quotient.**  At minimum deterministic arity, every support orbit is
   compressed to its unique parity character.
4. **Doctrine changes alter resource scaling.**  Convexification converts exponential deterministic
   label demand into a linear pure-outcome realization while retaining all source configurations as
   distinct mixtures.
5. **Finite composition is not cofinal birth.**  For every fixed `n` the construction is finite and
   has finite ancestry.  It does not cross ULF-GTM-2's finitary-formation barrier.

The result is one law of test-vocabulary genesis, not the universal field core.  Its next higher
question is whether source-generated failure supports themselves can grow under certified mutation,
and whether mixed channels transport a conserved certificate or an exchange residue.

## 5. Hostile boundaries

1. **Contextwise resolution is load-bearing.**  Separating one chosen pair does not force all
   support channels.
2. **Equivariance is load-bearing.**  An arbitrary orientation breaks the source symmetry and can
   lower deterministic arity.
3. **Deterministic and convex resources differ.**  `(EAG2.1)` counts attained deterministic response
   values; Theorem 2.4 counts pure atoms underlying probability-valued responses.
4. **Equality is load-bearing for Walsh rigidity.**  Larger target orbits can retain more than
   parity.
5. **Finiteness is load-bearing.**  Infinite failure sets require a topology, admission law, and
   distinction between finite-support and genuinely cofinal configurations.
6. **No source selector is proved.**  The theorem classifies the least legal successor after a
   failure record is given; it does not explain which failures occur.
7. **No RH claim.**  No route, zero, positivity criterion, or arithmetic source appears.

## 6. Parent mathematics and corpus collision

The signed cube `{0,+,-}^n` is the face monoid of the coordinate hyperplane arrangement.  Its face
semigroup and left-regular-band structure are classical; see Margolis--Saliola--Steinberg,
<https://arxiv.org/abs/1212.6683>, and Saliola,
<https://arxiv.org/abs/math/0511717>.  Stabilizer preservation under equivariant maps and the
two-point quotient argument are ordinary finite `G`-set theory.

The corpus already proves that an `n`-bit Boolean system has exactly `2^n-1` nonconstant Walsh
supports in `LBitTemporalDimensionLaw.lean`, and it proves full Walsh reconstruction in
`PrimeWalshTailConstraint.lean`.  The theorem here supplies a different statement: those supports
arise as the sharp orbit types forced by composed failure isotropy, and it classifies every reporter
attaining the minimum.

No priority claim is made for the ingredients.  Field value is the generative interpretation,
sharp composition/converse, and deterministic-versus-convex doctrine exchange.

## 7. Pipeline gates

- [x] well-posed before route specialization
- [x] complete positive construction
- [x] sharp lower bound
- [x] equality classification
- [x] omitted-hypothesis countermodels stated
- [x] internal collision audited
- [x] primary parent literature audited
- [x] Lean support separation, universal lower bound, canonical exact attainment, canonical
  support/parity fibre, and mixed-channel product closed
- [x] Lean arbitrary-sharp-reporter equality classification
- [x] Lean general convex `2n`-atom construction

## 8. Lean certification boundary

`ConstitutiveComposedFailureGenesis.lean` closes, without route premises:

- `ComposedFailureReporter.support_eq_of_q_eq`;
- `composedFailureReporter_card_lower_bound_closed`;
- `composedFailureCanonicalQ_eq_iff_closed`;
- `composedFailureCanonicalReporter_card_exact_closed`;
- `card_composedFailureMixedChannels_closed`;
- `composedFailureGenesisMechanism_closed`.

These declarations certify the mechanism headline: support strata cannot merge, the minimum image
is `2^(n+1)-1`, the bound is attained by support/parity, and independent blocks force the mixed
product sector.  Theorem 2.2 is now certified as `composedFailureReporter_sharp_eq_iff`, through
the flip-set machinery (`composedFailureFlipSet`, `exists_flipSet_of_support_eq`,
`composedFailureParity_flipSet`, `composedFailureReporter_stratum_two_valued`,
`composedFailureReporter_flipSet_eq_iff_even`).  Theorem 2.4 is certified as the strictly positive
`2n`-atom probability reporter `composedFailureConvexReporter`, with
`composedFailureConvexReporter_sum`, `composedFailureConvexReporter_pos`,
`composedFailureConvexReporter_equivariant`, `composedFailureConvexReporter_resolves`, and
`card_composedFailureOutcome`.

## Log

- 2026-08-10 -- composed-failure question re-aimed against the current RH frontier and ULF
  acceptance gate; route-specific interpretation rejected.
- 2026-08-10 -- sharp deterministic law, Walsh equality classification, mixed-block composition,
  and convex doctrine exchange proved on paper.
- 2026-08-10 -- Lean core closed: lower bound, exact canonical attainment, support/parity fibre,
  and mixed-channel product; stronger equality/convex clauses explicitly left unpromoted.
- 2026-08-11 -- Theorem 2.2 equality rigidity and Theorem 2.4 convex 2n-atom reporter certified in Lean; card promoted to stage 3.
