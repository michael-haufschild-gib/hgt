# Spacetime is the causal agreement shared by all matter. Gravity is matter rewriting that agreement.

- **ID:** `universal-causal-closure-law-of-gravity`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL PHYSICS LAW / CONTINUUM GRAVITY / CAUSALITY / HYPERTRANSCENDENCE
- **Scientific status:** `[CONJECTURE] [HOSTILE COLLISION AUDIT ACTIVE]`
- **Parent:** `chronometric-causal-susceptibility-law.md`
- **Demoted machinery:** metric-from-propagator, two-mass self-calibration, clock-probe Schur
  subtraction, conservation balancing, and nonlinear graph rigidity are Methods dependencies, not
  co-equal discoveries.

## Public law

> **Spacetime is the causal agreement shared by all matter. Gravity is matter rewriting that
> agreement.**

Lay translation:

> Every field has different internal dynamics, but a continuum universe makes all matter share one
> answer to the question “which disturbances can reach which events?” That shared answer is
> spacetime. Adding matter changes the shared answer. That change is gravity. If no shared answer
> remains, there is no single continuum spacetime underneath the observations.

This is larger than “clocks measure geometry.” It treats spacetime as the universal common causal
factor of matter dynamics and gravity as the complete conserved-source response of that factor.

## Candidate exact object

Let \(T\) be a controlled conserved stress intervention on a reachable solution branch. For every
independently calibrated physical probe sector \(\alpha\), let
\(\Gamma^{(2),\mathrm{ret}}_{\alpha,T}\) be its gauge-reduced inverse causal response and let
\(p_{\alpha,T}(x,\xi)\) be the reduced characteristic polynomial of its local principal symbol.

Define \(q_T(x,\xi)\), when it exists, to be the maximal square-free nondegenerate Lorentzian
quadratic factor common to every \(p_{\alpha,T}\), modulo multiplication by a nowhere-zero local
unit. Thus

\[
  q_T\mid p_{\alpha,T}\qquad\text{for every physical probe sector }\alpha.       \tag{1}
\]

For a single-metric continuum obeying universal minimal coupling,

\[
  q_T(x,\xi)=g_T^{-1}(x)(\xi,\xi)                              \tag{2}
\]

up to conformal scale. Calibrated mass response, proper time, or local volume fixes that scale.
Write the normalized factor as \(\bar q_T\).

The candidate universal gravity datum is the graph

\[
  \boxed{\mathfrak G_{\mathcal E}
  :=\operatorname{Graph}\!\left(T\longmapsto \bar q_T\right).}                  \tag{3}
\]

Its tangent is the causal susceptibility

\[
  \chi_T[\delta T]:=D_T\bar q_T[\delta T],                                      \tag{4}
\]

and its finite differences retain nonlinear branch information that a linearized susceptibility
loses.

## Universal Causal Closure Theorem — target

For admissible, source-controllable, pure-metric continuum gravity laws on a probed causal diamond,

\[
  \boxed{
  \mathfrak G_{\mathcal E_1}\cong\mathfrak G_{\mathcal E_2}
  \quad\Longleftrightarrow\quad
  \mathcal E_1\simeq\mathcal E_2.}                                               \tag{5}
\]

The quotient on the right includes time-orientation-preserving diffeomorphism, gauge, invertible
local physical field redefinition fixing calibrated matter channels, and variationally trivial
terms. It does not quotient clock-dark propagating sectors.

Equation `(5)` is not claimed for arbitrary formal Lagrangians. Initial admissible class:

1. four-dimensional globally hyperbolic pure-metric theories;
2. a specified hyperbolic gauge and a well-posed retarded source-to-solution germ;
3. universal local matter coupling through one nondegenerate Lorentzian metric;
4. independently calibrated conserved source directions that are locally controllable on the
   reachable solution graph;
5. a separating family of physical probe sectors whose reduced principal symbols have no common
   factor unrelated to causal propagation;
6. a scale channel supplied by calibrated mass, proper time, or volume;
7. no propagating gravitational variable invisible to \(\bar q_T\).

Under these hypotheses, `(5)` has a short algebraic spine. Equality of the common-factor graphs
gives equality of normalized metric/source graphs. Branch-safe graph rigidity then gives equality
of the nonlinear gravity operators on the reachable germ. The open scientific core is proving
that finite physical response data determine the local common factor and its normalized graph
without assuming the spacetime or its point basis in advance.

## Einstein corollary boundary

If one further assumes a local diffeomorphism-covariant pure-metric Euler--Lagrange tensor in four
dimensions, at most second derivatives, and identically conserved field equations, Lovelock
uniqueness restricts the local law to

\[
  a\,G_{ab}+b\,g_{ab}=T_{ab}.                                                     \tag{6}
\]

This is `[LITERATURE]`, not novelty. Its role is a boundary check:

> Inside the Lovelock class, measuring the universal causal response does not merely map a
> spacetime; it fixes the constants and reachable solution graph of Einstein gravity.

Higher-curvature, scalar--tensor, multimetric, and dispersive theories must be treated by their
full characteristic-factor algebra. Calling only their common metric factor “the complete law”
would be false if extra propagating modes are clock-dark.

## Hypertranscendental spacetime-failure theorem — target

Forward propagators can be hypertranscendental in perfectly local QFTs. Hypertranscendence of one
clock response is therefore not evidence against spacetime.

The invariant null test belongs after inversion and common-factor subtraction. For two controlled
minimal scalar probes with distinct calibrated masses and common local endpoint dressing, a local
single-metric continuum forces their inverse-response difference to be a zeroth-order diagonal
operator. Consequently,

\[
  \boxed{
  \text{off-diagonal, derivative-supported, nonlocal, or HT calibrated inverse residual}
  \Longrightarrow
  \text{no model in the admitted local single-metric continuum class}.}          \tag{7}
\]

Equation `(7)` is already dependency-closed algebraically and Lean-formalized in
`HTGeometry/ClockPropagatorSelfCalibration.lean`. A Nature-level paper still needs a
finite-resolution bounded-order/degree rejection hierarchy; finite data cannot certify
unrestricted hypertranscendence.

Public consequence:

> **Matter either shares one causal grammar, or spacetime is not the thing underneath it.**

## Hostile collision audit

The public sentence alone is not new.

1. **Metric from propagators.** Saravani--Aslanbeigi--Kempf and Kempf show that a scalar propagator
   in a position representation contains the metric, including conformal scale under their
   hypotheses. Therefore “one or two clocks recover spacetime” is not the apex.
2. **Matter causal structure to gravity.** Düll--Schuller--Stritzelberger--Wolz gravitational
   closure starts from the principal polynomial of matter equations and derives compatible
   gravitational dynamics; for standard metric matter it recovers general relativity. Therefore
   “matter contains gravity” is not by itself new.
3. **Einstein uniqueness.** Lovelock already classifies local second-order conserved pure-metric
   field equations in four dimensions.
4. **Causal order.** Causal order determines only conformal geometry under standard distinguishing
   hypotheses. A separate scale channel is load-bearing.
5. **All-observable circularity.** Defining the datum as every possible clock or matter outcome
   hides the full theory inside the observation and makes `(5)` nearly tautological. The datum must
   stay at the reduced common characteristic factor plus its controlled stress graph.
6. **Quantum effective metrics.** Vacuum polarization, media, nonminimal couplings, and
   birefringence can make different sectors propagate on different effective cones. Then `(1)` may
   have no Lorentzian quadratic gcd even though a background metric appears in the microscopic
   action.

Candidate novelty can survive only as the conjunction:

1. an operational, gauge-reduced extraction of the maximal common Lorentzian factor from finite
   calibrated response channels;
2. a biconditional between its complete conserved-stress graph and the continuum gravity operator,
   rather than reconstruction of one metric;
3. a finite experimental hierarchy whose limiting violation is the HT/nonlocal obstruction `(7)`;
4. unconditional Lean proofs for every algebraic dependency used in the continuum argument.

No novelty is claimed until formula-level comparison with gravitational closure and characteristic
geometry is complete.

## Kill conditions

Narrow or retire `(5)` if any survives:

1. the maximal common factor is not invariant under allowed gauge reduction, local field
   redefinition, or reporter calibration;
2. two inequivalent admissible gravity operators have the same complete reachable
   \(T\mapsto\bar q_T\) graph;
3. source conservation prevents local controllability of the metric/source graph;
4. extra gravitational modes are physically present but invisible to every admitted common-factor
   response;
5. exact quantum corrections destroy a local principal-factor interpretation at all scales;
6. the operational extraction is equivalent to assuming a position basis or metric beforehand;
7. gravitational closure already proves the same operational biconditional;
8. no finite-resolution statistic can separate the continuum null hierarchy from ordinary
   species-dependent self-energy or calibration error.

## Next obligations

1. Define reduced characteristic polynomials and their common Lorentzian factor invariantly for
   scalar, Dirac, Maxwell, and linearized gravitational sectors.
2. Prove uniqueness of the square-free Lorentzian common factor and identify every unit/conformal
   ambiguity.
3. Show how calibrated mass response or proper-time data fixes the factor's scale without assuming
   the metric.
4. Prove the source-graph biconditional for one nontrivial continuum class without smuggling in
   direct metric observation.
5. Compare theorem statements line by line with gravitational closure, premetric electrodynamics,
   effective-metric, inverse-problem, and AQFT literature.
6. Derive a finite-rank, finite-bandwidth null hierarchy for `(7)` with explicit alternative
   hypotheses.
7. Only after paper closure, formalize the missing UFD/common-factor and quotient machinery in
   Lean.

## Primary collisions

- M. Saravani, S. Aslanbeigi, and A. Kempf,
  *Spacetime Curvature in terms of Scalar Field Propagators*,
  <https://arxiv.org/abs/1510.02725>.
- A. Kempf, *Replacing the Notion of Spacetime Distance by the Notion of Correlation*,
  <https://arxiv.org/abs/2110.08278>.
- M. Düll, F. P. Schuller, N. Stritzelberger, and F. Wolz,
  *Gravitational closure of matter field equations*,
  <https://arxiv.org/abs/1611.08878>.
- F. P. Schuller, *Constructive Gravity: Foundations and Applications*,
  <https://arxiv.org/abs/2003.09726>.
- J. Schneider, F. P. Schuller, N. Stritzelberger, and F. Wolz,
  *Gravitational closure of weakly birefringent electrodynamics*,
  <https://arxiv.org/abs/1708.03870>.

## Log

- 2026-07-28 — created after hostile rejection of all-clock data as circular and two-clock
  metric recovery as a direct collision with propagator reconstruction.
- 2026-07-28 — elevated maximal common causal factor and its conserved-stress graph to the sole
  candidate law; retained clocks only as calibration/readout and HT only as a spacetime null test.
