# Positive degrees see only reduced critical jet blocks

- **ID:** positive-degrees-see-only-reduced-critical-jet-blocks
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Q-II; actual Poisson quotient and finite causal Xi sections.
- **Status:** FORMALIZED. Actual-file checks and transitive axiom audits passed for both finite algebra and positive-degree classification; external novelty unverified.

## Exact statement

Let `A` be the actual Meyer Poisson quotient with convolution and arithmetic sharp.
Let `d:A→C` be complex-linear, Hermitian (`d(a^sharp)=conj(d(a))`), and nonnegative
on every sharp square. On every finite divisor packet, `d` annihilates every off-line
jet block and every positive-order jet at a critical point. On the remaining critical
zeroth-order blocks it has nonnegative real weights. Conversely those weights define
positive Hermitian degrees on the finite packet algebra.

This classifies the restriction to finite packets. It does not claim that arbitrary
linear functionals on the whole infinite quotient are determined by those restrictions;
that would require an additional density or continuity theorem.

## Algebra supplied by actual sources

The finite causal section and full-jet separation give actual quotient classes
`T(rho,j)` with Hasse jet one at `(rho,j)` and all other jets zero. Concretely,
`T(rho,j)=j! [meyerSingleJetSource(rho,j)]`. Hasse convolution gives

`T(rho,j) T(sigma,k)=0` when `rho!=sigma`,
`T(rho,j) T(rho,k)=T(rho,j+k)` when `j+k<m(rho)`, and zero otherwise.

Arithmetic sharp gives
`T(rho,j)^sharp=(-1)^j T(reflect(rho),j)`; reflection preserves multiplicity.
These are equalities in genuine cohomology because all divisor jets agree.
In particular `T(rho,0)` is a block identity, including at a multiple zero.

## Proof

Hermiticity and convolution commutativity make
`B(a,b)=d(a b^sharp)` a Hermitian sesquilinear form. Positivity of its diagonal,
applied to `a+t b` and `a+i t b`, gives Cauchy–Schwarz by the discriminant argument.
Consequently a zero-square vector is orthogonal to every vector.

If `rho` is off the critical line, its block is disjoint from its sharp image.
Every `T(rho,j)` therefore has zero sharp square. Pair it with
`T(reflect(rho),0)`; the resulting product is `T(rho,j)`. Cauchy–Schwarz forces
`d(T(rho,j))=0` for every order in that block.

At a critical point, descend from `j=m(rho)-1` to `j=1`. The sharp square of
`T(rho,j)` is either zero (if `2j>=m`) or `(-1)^j T(rho,2j)`.
In the second case its degree is already zero because `2j>j`. Thus its square degree
vanishes in either case. Pairing with the block identity forces `d(T(rho,j))=0`.
For `j=0`, the block identity is self-adjoint and idempotent, so its degree is real
and nonnegative. Every finite packet is the finite linear combination of these
actual classes with its Hasse coefficients, proving the asserted restriction.

Conversely, after discarding off-line and positive-order coordinates, a sharp square
has coordinate `|a(rho)|²` at each retained critical point. Any nonnegative real
weighted sum of those coordinates is Hermitian and nonnegative.

## Positive survivor and implications

Positive Hermitian degree can retain a multiple critical point, but only its reduced
value coordinate. It necessarily loses its nilpotent jet directions. Off-line blocks
are lost entirely. Faithfulness therefore requires both criticality and simplicity,
while some nonfaithful positive degree is available from Hardy's critical point.
This explains the distinction between ordinary-trace positivity, positive degree
existence, and faithful positivity using actual finite source sections.

## Corpus audit and Lean obligations

Searches for positive Xi-jet functional classification found finite jet independence
and reflection-incidence positivity criteria, not this finite-block classification.
`XiReflectionIncidencePositiveCofinalRegularizationNoGo.lean` was read; its theorem
concerns summability of coefficient-recovering prime masses, not the present algebra.

Existing inputs: finite causal sections, full jet separation, Hasse convolution,
and conjugation/reflection jet formulas. Formal proof components: normalized jet
product and sharp equalities in the quotient, Hermitian-degree Cauchy–Schwarz,
descending jet induction, and the finite-packet weighted evaluation formula.
Do not strengthen this to a classification of arbitrary infinite-quotient degrees.

`MeyerSharpConvolutionAlgebra.lean`, including the complex null-pair lemma,
has passed its actual-file Lean check and standard transitive axiom audit.
The actual `MeyerFiniteJetAlgebra.lean` module formalizes normalized Hasse
class multiplication, sharp laws, and exact finite causal expansion.
Direct check **48574** passed with only `propext`, `Classical.choice`, and
`Quot.sound` in all seven endpoint audits:

- `meyerHasseJetSource_moment`
- `meyerSourceClass_eq_of_hasse_moments_eq`
- `meyerHasseJetClass_product_distinct`
- `meyerHasseJetClass_product_same`
- `meyerHasseJetClass_product_truncated`
- `meyerHasseJetClass_sharp`
- `meyerFiniteXiCausalSection_eq_hasse_sum`

Temporary prints are removed; the finite-jet module is wired and documented.
`PositiveMeyerDegreesSeeReducedCriticalJets.lean` contains off-line and
higher-jet annihilation, the finite causal weighted-value formula, and the
converse positive Hermitian finite-weight construction on the whole quotient.
Direct classifier check **14494** passed with only `propext`, `Classical.choice`,
and `Quot.sound` in all six endpoint audits:

- `meyerPositiveDegree_off_line_jet_zero`
- `meyerPositiveDegree_higher_jet_zero`
- `meyerPositiveDegree_finite_causal_formula`
- `meyerFiniteCriticalDegree_hermitian`
- `meyerFiniteCriticalDegree_nonnegative`
- `meyerFiniteCriticalDegree_hasse_class`

Temporary prints are removed; the classifier is wired and documented. Its
stale scratch draft is deleted. No claim about recovering arbitrary
infinite-quotient functionals is added.
