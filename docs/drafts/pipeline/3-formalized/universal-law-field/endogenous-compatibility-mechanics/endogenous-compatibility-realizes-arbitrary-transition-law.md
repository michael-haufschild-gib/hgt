# Endogenous compatibility realizes arbitrary transition law

- **ID:** ULF-ECM-1
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / MECHANISM VACUITY BOUNDARY
- **Statement:** A state-indexed compatibility relation with a single test can realize every
  prescribed transition relation as an exact test polar.
- **Status:** [PROVED HERE] [DEPENDENCY-CLOSED] [LEAN-CERTIFIED] [MECHANISM BOUNDARY]
  [ARBITRARY ENDOGENEITY VACUOUS] [POSITIVE SURVIVOR] [NOT RH]

## 1. Setup

Let `S` be any set of law states and let

\[
  N:S\longrightarrow \mathcal P(S)
\]

be an arbitrary transition law. Let the test set be the singleton `1={*}`. At each current state
`s`, define a compatibility relation

\[
  x\perp_s * \quad\Longleftrightarrow\quad x\in N(s).
  \tag{EC.1}
\]

For a family of tests `B subset 1`, its test polar at state `s` is

\[
 {}^{\perp_s}B
 =\{x\in S:(\forall y\in B)\ x\perp_s y\}.
 \tag{EC.2}
\]

## 2. Universality theorem

### Theorem 2.1 -- one-test realization

For every set `S`, every transition law `N:S -> P(S)`, and every current state `s`,

\[
  {}^{\perp_s}1=N(s).
  \tag{EC.3}
\]

#### Proof

There is exactly one test. A state `x` belongs to the left-hand side iff it is compatible with `*`.
By (EC.1), this holds iff `x in N(s)`. Hence the two sets are equal. QED.

### Corollary 2.2 -- deterministic realization

Every map `f:S -> S` is realized by taking `N_f(s)={f(s)}`. Then

\[
  {}^{\perp_s}1=\{f(s)\}.
  \tag{EC.4}
\]

Thus arbitrary orbit length, periodicity, branching, recurrence, termination, or apparent chaos can
be encoded directly in a state-dependent compatibility relation.

## 3. Conjugacy naturality

The construction is not rescued by invariance under renaming. If `e:S -> S'` is a bijection and

\[
  N'(e(s))=e[N(s)],
\]

then `e` transports (EC.1) to the corresponding compatibility relation on `S'`, and transports the
polar (EC.3) to `N'(e(s))`. The arbitrary dynamics survives coordinate change. Equivariance under
state relabeling therefore does not make the mechanism predictive.

## 4. Exact consequence

The theorem kills the proposal

> open law genesis is explained once compatibility is allowed to depend on current law state.

State dependence alone is maximally expressive and therefore non-falsifiable. It can model every
possible history because it stores the transition law verbatim.

### Strongest positive survivor

A non-vacuous law-genesis theory must restrict how `perp_s` may change. At minimum, changes must be
generated from exposed witnesses and obey independent constraints such as locality, minimality,
conservation of transported certificates, exchange of independent repairs, and explicit accounting
for new signature or retained history. These restrictions are developed as the ULF-ECM program in
Stage 1.

Together with ULF-RLM-12, this gives a sharp two-sided boundary:

1. fixed exact compatibility has only closure and period-two behavior;
2. arbitrary endogenous compatibility realizes every behavior.

The missing mechanism must lie strictly between collapse and universality.

## 5. Scope

The proof is elementary and uses no topology, probability, positivity, arithmetic, route endpoint,
or RH assumption. Its role is an anti-theatre theorem: any proposed universal field whose entire
dynamics is "choose a state-dependent compatibility" has no empirical or mathematical content until
additional revision laws are proved.

## 6. Lean certification

The one-test realization, deterministic singleton corollary, conjugacy naturality, and closed
universality capstone are
certified in `GaloisForLFunctions.HTGeometry.ConstitutiveEndogenousCompatibility`. The module is
imported by the Universal Law Field umbrella. Direct elaboration, umbrella build, lint, and axiom
audit are recorded in the Stage-3 card.

## Log

- 2026-08-09 -- arbitrary endogenous transition law realized exactly with one test; naive
  self-modifying-polarity proposal closed; structured revision isolated as positive survivor.
- 2026-08-11 -- conjugacy naturality certified; card promoted to stage 3.
