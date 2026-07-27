# Antagonistic referee report

Review date: 2026-07-27  
Review posture: hostile specialist referee for a reputable general mathematics
journal. This is an internal review, not an external referee report.

## Recommendation

**Acceptable for submission.** The revisions demanded below are incorporated in the
final manuscript, and the final mathematical, build, citation, and page-render audits pass.

The paper does not prove RH and should not be marketed as doing so. It does prove a
clean new theorem at the intersection of analytic number theory and differential
algebra:

\[
\{\,\zeta((m+1)s)^{-1}-\zeta(ms)^{-1}:m\ge2\,\}
\]

is jointly differentially algebraically independent over
\(\mathbb C(s)\langle\zeta\rangle\). Its \(m\ge12\) subfamily is holomorphic and
zero-free on \(\Re s>1/2\), and multiplication by zeta turns it into pairwise
coefficient-disjoint positive Dirichlet series carrying exactly the same zeta zero
divisor. The \(\Omega\)-leading-echelon criterion is reusable beyond this example.

That package is potentially publishable in a strong general mathematics journal.
It is not, on present evidence, an Annals/Inventiones-level RH advance. Priority
language must remain qualified until an external specialist checks the older
Russian differential-independence literature.

## Principal attacks

### 1. “These functions are merely zeta times units.”

**Attack.** Once \(S_m=\zeta H_m\) is written down, equality of zero divisors is
tautological if \(H_m\) is a unit. The paper risks presenting a factorization as an
RH advance.

**Disposition.** Resolved. The manuscript explicitly says same-zero replication
alone is not new and cites Grosswald–Schnitzer. Its main algebraic theorem is
measured after adjoining zeta and every derivative of zeta:

\[
(H_m)_{m\ge2}\text{ is differentially independent over }
\mathbb C(s)\langle\zeta\rangle.
\]

This removes the common factor before significance is measured. The positive
disjoint support and zero-free theorem are then additional structures on the
\(m\ge12\) subfamily.

### 2. “Individual hypertranscendence and Dirichlet-series Jacobians are classical.”

**Attack.** Ostrowski, Postnikov, Shapiro–Sparer, Nagoshi, and Pong make any broad
claim of a first hypertranscendence theorem untenable.

**Disposition.** Resolved. The manuscript claims no novelty for one-source
hypertranscendence, systems of Dirichlet series, or the Jacobian method. The novelty
boundary is the explicit relative family over the zeta differential field, its
tail-immune \(\Omega\)-graded proof, and its simultaneous positive common-divisor
application. Postnikov is now cited explicitly.

### 3. “The threshold 12 is arbitrary and probably nonoptimal.”

**Attack.** A coarse constant should not be sold as a sharp arithmetic boundary.

**Disposition.** Resolved. The manuscript says only that 12 is a sufficient uniform
threshold. It gives the exact rational domination:

\[
29/100 \quad\text{versus}\quad
(512/5)(3^{-6}+4^{-6}+1/2500)<21/100.
\]

The differential theorem is cleanly separated and begins at \(m=2\), so the
analytic convenience threshold does not contaminate the universal law.

### 4. “Differential independence over \(\mathbb C\) does not imply independence over
\(\mathbb C(s)\).”

**Attack.** This is a common and serious error in Dirichlet-series arguments.

**Disposition.** Resolved. The proof includes a polynomial-coefficient
Dirichlet-uniqueness argument. After clearing denominators, a relation over
\(\mathbb C(s)\) becomes

\[
\sum_n Q_n(s)n^{-s}=0
\]

with uniformly bounded polynomial degree. Least-frequency exponential separation
forces every \(Q_n\) to vanish; coefficient comparison returns a relation in the
Dirichlet-convolution domain, where the Jacobian theorem applies.

### 5. “The infinite fusion relation contradicts differential independence.”

**Attack.** The paper has
\(\sum_{m\ge1}S_m=\zeta-1\), apparently an algebraic dependence.

**Disposition.** Resolved. Differential algebraic independence excludes finite
polynomial relations. The fusion is an infinite locally absolutely convergent sum,
coefficientwise finite at every integer. The manuscript states this distinction
explicitly.

### 6. “Positive coefficients do not remain a convergent positive series in the
critical strip.”

**Attack.** Calling an off-line zero a positive-coefficient cancellation may suggest
termwise convergence at the zero, which is false because the original shell series
has abscissa one.

**Disposition.** Requires a wording constraint, adopted in final revision:
off-line zeros are zeros of the meromorphic continuation of a positive-coefficient
Dirichlet series. The paper must not claim that the defining positive series
converges at such a zero or that positivity alone controls the continuation.

### 7. “This is only a decorative RH equivalent.”

**Attack.** The equivalence “\(S_m^\#\) is zero-free iff zeta is zero-free” alone is
mathematically immediate and adds no leverage.

**Disposition.** Resolved as far as the theorem supports, with an explicit limit.
The paper states that the equivalence alone is not the contribution and does not
claim a zero-exclusion estimate. Added structure is:

- countably many pairwise-disjoint \(0/1\) coefficient sources;
- equal-multiplicity replication of any off-line zero in every channel;
- joint relative differential independence of the normalized channels over the
  full zeta differential field;
- a reusable \(\Omega\)-leading-echelon law proving maximal finite-jet rank.

This opens a distinct simultaneous-channel route: any successful use must exploit
analytic continuation estimates, phase, boundary behavior, or genuinely infinite
interaction; finite differential elimination is proved unavailable. This is
structural progress, not quantitative zero-density progress.

### 8. “The paper overclaims that no literature contains the result.”

**Attack.** Formula searches cannot establish priority, especially against older
Russian work.

**Disposition.** Resolved. Main manuscript describes its contribution without
using “first.” Internal literature audit says “no checked source” and recommends
qualified priority language. It separates every classical component from the
candidate new conjunction.

### 9. “The universal theorem is buried behind the RH application.”

**Attack.** A general journal needs a theorem of independent use, not an RH wrapper.

**Disposition.** Resolved. The abstract and introduction now lead with relative
hypertranscendence; a consolidated Main Theorem appears early. The
\(\Omega\)-leading-echelon criterion is stated as a general source theorem and its
proof shows upper-tail immunity.

### 10. “The paper leaves its actual mathematical question unanswered.”

**Attack.** Many RH papers end with speculation rather than a closed theorem.

**Disposition.** Resolved. The paper asks whether exact positive fusion, complete
common-divisor replication, and maximal relative differential rank can coexist.
The exponent-shell family answers yes and classifies the relevant rank exactly.
There is no open-problems section and no conjectural step inside a theorem.

## Detailed correctness audit

- Shell indicator and pairwise disjointness: correct.
- Coefficientwise finite telescope: correct.
- \(m\)-free Euler product and shell factorization: correct.
- Prime-two head estimate: correct.
- Sixth-power tail normalization: correct and strict.
- Denominator zero-freeness: correct because dilated arguments lie in \(\Re z>1\).
- Divisor multiplicities: correct away from the pole because \(H_m\) is a
  holomorphic unit.
- Prime derivation Leibniz law: correct for Dirichlet convolution.
- Lowest \(\Omega\)-grade: correct; equality forces a pure prime power.
- Determinant grade argument: correct; any term above one column minimum would
  require another below its minimum.
- Block decomposition: correct by unique factorization and injectivity of shell
  levels.
- Vandermonde nonvanishing: correct because selected prime logarithms are distinct.
- Transfer to \(\mathbb C(s)\): correct with the polynomial-coefficient uniqueness
  argument.
- Base adjunction: correct by the tower property for algebraic independence of all
  jets.
- Multiplication by \(\zeta^{-1}\): correct as an invertible triangular jet change
  over \(\mathbb C(s)\langle\zeta\rangle\).
- RH equivalences: correct using zero-freeness on \(\Re s\ge1\), the functional
  equation, and zeta/shell divisor equality.

## Publication criteria

| Criterion | Verdict | Reason |
|---|---|---|
| Only unconditional proved claims | **Pass** | Every headline claim has a direct internal theorem endpoint; RH occurs only in equivalences |
| Interesting universal theorem or novel RH route | **Pass, with scope caveat** | Relative hypertranscendence and \(\Omega\)-leading-echelon law are general; RH application creates a new positive disjoint divisor frame, but does not prove a new zero-free region |
| General-journal quality | **Pass for submission** | Self-contained theorem, proof, novelty boundaries, exact constants, and clear limitations; specialist priority check still expected in peer review |
| No unanswered question inside claimed result | **Pass** | Compatibility/classification question is answered completely; no theorem depends on a conjectural bridge |
| No significance from formal verification | **Pass** | Manuscript contains no reference to proof software or formalization |

## Final referee perspective

A skeptical referee should no longer be able to dismiss the paper as “zeta times
arbitrary units.” The units are explicit adjacent reciprocal dilations, zero-free
on the RH-relevant half-plane for \(m\ge12\), and maximally free even over the
complete zeta differential field. Nor can the paper be dismissed as “another
individual hypertranscendence theorem”: the result is joint, relative, countable,
and coupled to an exact positive coefficient partition.

The correct editorial pitch is:

> a universal differential-algebraic separation law with a surprising Riemann
> divisor application.

The incorrect pitch would be:

> a proof of RH, a new zero-free region for zeta, or a sharp numerical shell
> threshold.

Under the correct pitch, the manuscript meets its stated criteria and is ready for
external mathematical review.
