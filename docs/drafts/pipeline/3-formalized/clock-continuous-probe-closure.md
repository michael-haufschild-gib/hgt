# Continuous clock potentials: exact closure of the visible locus

- **ID:** clock-continuous-probe-closure
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) / BRIDGE
- **Source:** `ClockPotentialDetermination`, `ClockProbeSolutionSpace`, `ClockScaleDeterminationLocus`.
- **Statement:** For continuous potentials on a normal T1 space, the exact determination locus of the full solution family is the closure of its nonvanishing locus. For two independently fitted continuous potentials and distinct masses, the exact scale locus is the intersection of the two closures.

## Working plan

1. [x] Read corpus sources, inspect existing probe-existence advances, search overlap.
2. [x] Specify exact classification and complete paper proof.
3. [x] Verify imported names, formalize exact statements without proof debt.
4. [x] Direct leaf audit, axiom audit, umbrella wiring, index and formal lint.
5. [x] Record result and next conjecture; retain the overall corpus research goal.

`update_plan` is unavailable in this session; this file holds the working plan.

## Context and attacks

The older massless-reference and null-frame modules expose probe-existence premises.
Later hyperbolic, variable-speed and product-chart cards already discharge substantial
existence cases. Re-proving those is not a new frontier.

Selected target: `potential_determined_iff_mem_potentialDeterminationSet` allows arbitrary
competing potentials. Its single-point perturbation generally destroys continuity.
The source theorem is correct; its exact visible-set boundary does not describe a
continuous competitor class.

Searches run directly with `scripts/formal_tools.py research`, `--no-refresh`:
`clock inverse`; `massless clock inverse Goursat`; `clock resolvent cross ratio mass calibration`;
`potential determined dense probe common zero`. Searches returned source-only candidates;
semantic coverage was unmeasured, so absence is not a global novelty certificate.
Exact text searches found no continuous closure classification among the clock modules.

External parent theories: Urysohn separation and continuous-function annihilators.
Henriksen–Woods, *Cozero complemented spaces* (2004),
https://scholarship.claremont.edu/hmc_fac_pub/38/ establishes adjacent classical cozero-set
context. The installed mathlib `Topology/ContinuousMap/Ideals.lean` explicitly proves the
interior/support correspondence with Urysohn separation. Thus verdict: **BRIDGE**, not
scientific novelty. A preliminary mass cross-ratio idea was not pursued: noncommutative
cross-ratio theory already exists (https://arxiv.org/abs/1905.01366).

## Exact paper proof [PROVED HERE]

Let X be a normal T1 space, W any map from real functions to real functions, and
V a continuous real potential. Put S(V)={u: Wu+Vu=0 pointwise}, and
D(V)={x: some u in S(V) has u(x) nonzero}. No linearity or regularity of W is needed.

For any other continuous Q, S(V) is contained in S(Q) iff Q=V on closure D(V).
Indeed, subtracting the two equations gives (Q-V)u=0, so Q=V on D(V), hence on its
closure by continuity. Conversely, at any point either a solution u is nonzero and
Q=V there, or u is zero and changing its coefficient changes no equation.
This is a classification of preserving all original solutions, not an assertion that
the competitor has no additional solutions.

Consequently every preserving continuous Q has Q(x)=V(x) iff x is in closure D(V).
The forward implication is sharp: outside that closed set, Urysohn gives a continuous
f equal to zero on it and one at x. For any prescribed real c, the potential
Q=V+(c-V(x))f preserves all original solutions and has Q(x)=c. This also treats an
empty visible locus. Global unique recovery is therefore equivalent to density of D(V).

For two independent species define scale=(V1-V2)/(mu1-mu2), with the corpus's totalized
real division. If mu1=mu2 every scale is zero. Otherwise, a point is fixed for all
independently preserving continuous competitors iff it belongs to
closure D(V1) intersect closure D(V2). Sufficiency follows from the two pointwise
classifications. For necessity, outside either closure, change only that species to
Vj(x)+1 using the separator. The nonzero denominator makes the scale change.
The closures must be taken separately: replacing their intersection by the closure
of the intersection is unjustified for arbitrary probe regularity.

No PDE existence premise is discharged here. The proof burden changes from nonvanishing
at every event to density of the actual full solution visibility set for continuous
potential recovery. This is a useful corpus interface reduction, not an RH result.

## Log

- 2026-10-08 — corpus/source audit and external parent-theory attack complete. Exact paper
  statements closed above; formalization next. Existing unrelated worktree changes preserved.
- 2026-10-08 — six public statements in
  `formal/GaloisForLFunctions/HTGeometry/ClockContinuousPotentialDetermination.lean`
  passed `lake --old env lean` (exit 0, no diagnostics), then direct compilation with
  `-o .lake/build/lib/lean/GaloisForLFunctions/HTGeometry/ClockContinuousPotentialDetermination.olean`.
  Imported `#print axioms` audit passed for all six: only `propext`, `Classical.choice`,
  `Quot.sound`. API-name scratch also passed. Unique HTGeometry umbrella import verified.
  `scripts/formal_tools.py index` exited 0 and generated all six API rows.
  Authoritative `scripts/formal_tools.py lint` exited 1 on six unrelated unreachable
  modules: `ApertureConeCalculus`, `ApertureConeWinding`, `ApertureLogTranslation`,
  `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`, `OneSidedLaplaceAtomRigidity`.
  No owned finding or proof-debt error. No full build, computation experiment, added
  axiom, heartbeat increase, commit or push.
- 2026-10-08 — user explicitly restricted research to the Lean corpus. No further external
  source searches or reads are permitted; this overrides the skill's literature workflow.
- 2026-10-08 — next corpus cycle found a misleading scale-blindness claim: the source
  theorem distinguishes pairs, but its zero-weight witness changes only the defect.
  Exact single-species classification tracked in `clock-single-species-scale-boundary`.

## Assessment and next direction

This increment changes the exact corpus receiver from pointwise nonvanishing to dense
visibility when competing potentials are continuous. It supplies no new PDE existence,
RH conclusion, or established external scientific novelty. It is a completed interface
reduction, with both the positive statement and exact ambiguity outside its boundary.
The next step follows actual channel coupling rather than repeating general probe
existence already available in the corpus.
