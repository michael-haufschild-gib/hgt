# Adaptive mimic cost, coercivity, and infinite-action boundary law

- **ID:** `adaptive-mimic-cost-coercivity-and-infinite-action-boundary-law`
- **Stage:** 3 — formalized in Lean
- **Type:** THEOREM (Lean)
- **Status:** `[PAPER-PROVED] [UNIVERSAL-LAW FIELD] [ADAPTIVE COST]`
  `[EXPERIMENTAL COERCIVITY] [LEAN-CERTIFIED] [NOT RH]`
- **Parent:**
  `../../3-formalized/universal-law-field/adaptive-experimental-procompletion-effectivity-gap-law.md`
- **Statement:** The canonical effective law that mimics a virtual adaptive transcript is the
  unique inclusion-minimal mimic; it minimizes every nonnegative coordinate cost. Exhaustive
  all-true experiments force exact support cost (N), so their virtual boundary has open,
  unbounded effective history.

## 1. Transcript mimicry

Retain the parent notation. For a finite adaptive experiment (T), virtual profile (b), and
finite effective support (F), say (F) **mimics the transcript** when

\[
  \chi_F(n)=b(n)\qquad(n\in Q(T,b)),
\tag{MC.1}
\]

where (Q(T,b)) is the coordinate set encountered along the run of (T) against (b). The
parent's canonical mimicking support is

\[
  F_{T,b}=\{n\in Q(T,b):b(n)=1\}.
\tag{MC.2}
\]

### Theorem 1.1 — exact minimal transcript support

The support (F_{T,b}) mimics the transcript. If (F) also mimics it, then

\[
  \boxed{F_{T,b}\subseteq F.}
\tag{MC.3}
\]

Hence (F_{T,b}) is the unique inclusion-minimal transcript mimic.

### Proof

The first assertion is the parent's trace-agreement theorem. If (n\in F_{T,b}), then (n) was
queried and (b(n)=1). Transcript mimicry gives (chi_F(n)=1), hence (n\in F). This proves
`(MC.3)`. If (F) is inclusion-minimal, `(MC.3)` and minimality force (F=F_{T,b}). `QED`

## 2. Universal cost minimization

Let (w:\mathbb N\to\mathbb N) be any nonnegative coordinate cost and define

\[
  \mathcal A_w(F)=\sum_{n\in F}w(n).
\tag{MC.4}
\]

### Theorem 2.1 — every positive doctrine has the same minimizer

For every transcript mimic (F),

\[
  \boxed{\mathcal A_w(F_{T,b})\leq\mathcal A_w(F).}
\tag{MC.5}
\]

### Proof

Equation `(MC.3)` and termwise nonnegativity imply monotonicity of the finite sum. Strictness is
not needed for the stated minimization law. `QED`

The point is not the elementary sum. It is that adaptation changes which coordinates enter the
cost, but does not change the exact variational solution: retain precisely the true coordinates on
the actual transcript.

## 3. Exhaustive experiments and exact open history

Let (E_N) be the finite adaptive experiment that queries (0,1,\ldots,N-1) along its all-true
branch. Against the constant-one virtual profile,

\[
  Q(E_N,\mathbf1)=\{0,1,\ldots,N-1\},
  \qquad
  F_{E_N,\mathbf1}=\{0,1,ldots,N-1\}.
\tag{MC.6}
\]

### Theorem 3.1 — exact coercivity profile

Every effective transcript mimic (F) of (E_N) against (mathbf1) satisfies

\[
  \boxed{N\leq |F|.}
\tag{MC.7}
\]

Equality is achieved by (F=\{0,ldots,N-1\}). More generally,

\[
  \boxed{
  \sum_{n<N}w(n)leq\mathcal A_w(F),}
\tag{MC.8}
\]

with equality at the canonical mimic.

### Corollary 3.2 — infinite-action experimental boundary

If

\[
  \sum_{n<N}w(n)\longrightarrow\infty,
\tag{MC.9}
\]

then every sequence of effective laws mimicking the all-true profile on successively exhaustive
experiments has cost tending to infinity. Observation closes at every finite stage, while every
effective lift escapes every bounded cost sublevel.

### Proof

Equation `(MC.6)` follows by induction on (N). Apply Theorem 1.1 and take cardinality or weighted
finite sums. The corollary is immediate from `(MC.8)`. `QED`

## 4. Constitutive interpretation

The parent effectivity gap becomes quantitative. A virtual boundary point has two independent
properties:

1. **experimental closure:** every finite adaptive experiment has an effective mimic;
2. **effective coercivity:** the least cost of such mimics along an exhaustion.

The all-true point is experimentally closed but coercively open. This supplies a precise meaning
for “closed observer projection with open lifted history” without assuming a covering space,
curvature, or physical clock.

The resulting field object is not merely a topology. It is a filtered pair

\[
  (\mathcal L_{\mathrm{eff}},\mathcal A)
  \longrightarrow
  \widehat{\mathcal L}_{\mathrm{exp}}
\tag{MC.10}
\]

whose boundary points carry a **mimic-cost profile**. Different positive doctrines may change the
rate but not the canonical minimizing support.

## 5. All-prime source consequence and exact limitation

Index the literal prime-valuation/Kummer coframe by (mathbb N). Any proposed exactification built
from coordinate-local finite prime events and required to match the first (N) nonzero prime
channels needs at least (N) such events. With Kummer weights (w_p>0), its cost is bounded below
by the corresponding partial weight sum.

This is unconditional **within the coordinate-local event model** and rules out uniformly bounded
local exactification of the full prime coframe. It does not rule out one genuinely nonlocal source
operation acting on infinitely many prime channels at once. On the contrary, it identifies such an
operation—or an admitted infinite-action singular limit—as the only surviving kind of source
relation. Therefore this theorem narrows the live dagger-landing search but does not construct the
landing or prove RH.

## 6. Hostile boundaries

1. Final-output equality is weaker than transcript mimicry: two branches may share an output.
   Minimality is asserted only for exact transcript realization.
2. Zero-cost extra coordinates destroy uniqueness as a cost minimizer but not inclusion minimality.
3. A nonlocal generator may control infinitely many response coordinates at unit cost. The local
   support model cannot exclude it.
4. Divergent mimic cost is not hypertranscendence. It occurs in the elementary Boolean chart.
5. A bounded weighted sum produces a finite-action boundary even though the point remains
   non-effective.
6. The theorem supplies a coercivity obstruction, not source-normality, a Stokes comparison, or a
   Bockstein boundary.

Decision-tree and certificate-cost theory is established machinery; see Blanc--Koch--Lange--Tan,
[arXiv:2201.07736](https://arxiv.org/abs/2201.07736). The constitutive content here is the exact
coupling of adaptive transcript realization, procompletion effectivity, and coercive lifted cost.

## Gates

- [x] dependency-closed paper proof;
- [x] no-go has exact positive survivor: canonical minimal support and its cost;
- [x] Lean certification:
  `GaloisForLFunctions.HTGeometry.ConstitutiveAdaptiveCost`;
- [ ] nonlocal source-event model;
- [ ] literal source-normal dagger comparison.

## Log

- 2026-08-09 — paper theorem closed; arithmetic consequence scoped to coordinate-local events.
- 2026-08-09 — Lean module and dedicated field umbrella built in foreground; axiom audit passed;
  promoted to Stage 3.
