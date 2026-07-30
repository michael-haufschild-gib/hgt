# The asymptotic-time boundary principle

- **ID:** `asymptotic-time-boundary-principle`
- **Stage:** 5-failed
- **Type:** FROZEN FOUNDATIONAL CONJECTURE / UNIVERSAL LONG-TIME LAW
- **Status:** `[FALSIFIED AS FROZEN] [NO-GO CLOSED] [NOT A MANUSCRIPT CLAIM]`
- **Date frozen:** 2026-07-30

## Public law

> **There is no single infinite future. Infinity is a geometric boundary,
> and different ways of waiting expose different dimensions of time.**

Shorter:

> **The infinite future has a shape.**

“Different ways of waiting” means different physically controlled joint
scalings of observation time, interaction strength, system size, resolution,
dissipation and other parameters. It does not mean that personal choice
changes an already fixed experiment.

## Frozen truth-hunch

For every physically admissible family of dynamical systems, its long-time
content is not correctly represented by one point called \(T=\infty\), nor by
any privileged order of limits. It has a canonical **asymptotic-time
boundary**
\[
  \partial_\infty\mathfrak T
\]
whose points or strata represent inequivalent scaling directions by which
physical observation approaches infinite time while other physical scales
degenerate, diverge or refine.

Every finite observation law extends to this boundary in a resolved form.
Different boundary strata may have different:

- observer-visible temporal dimension;
- recurrent phase group;
- persistent spectral mass;
- transient sector;
- return distribution;
- effective interaction connectivity;
- thermodynamic phase; and
- continuum completion.

The complete boundary, together with its incidence and transition laws, is
the invariant physical object. A sequential limit is only one boundary
chart.

This statement is frozen before selecting:

- a blow-up, compactification, fan, valuation space, tropical variety,
  renormalization group or nonstandard construction;
- a category of physical systems;
- a definition of admissible scaling;
- a topology or measure on the boundary;
- a finite/open/infinite proof strategy; or
- a Lean representation.

The familiar finite analytic factorization
\(\delta(g)=g^b u(g)\) motivated the hunch but does not define or prove the
universal boundary.

## Ontological reversal

Standard asymptotic analysis asks which value a physical observable approaches
as time tends to infinity, often after fixing or separately limiting other
parameters. The conjecture reverses the role of the limit:

1. \(T=\infty\) is not a value but a boundary with internal geometry;
2. a long-time “phase” is a stratum of that boundary;
3. noncommuting limits are not pathologies to order away but evidence of
   distinct boundary directions;
4. crossover exponents are coordinates of the boundary;
5. temporal dimension is a local invariant of a boundary stratum;
6. a singular weak interaction may change the boundary topology while every
   bounded-time observable remains continuous;
7. an infinite or thermodynamic theory is complete only when all physically
   admissible approaches to its asymptotic boundary are compatible.

Thus the infinite future is treated as physical asymptotic geometry, not as a
formal endpoint appended to finite time.

## Universal statement

The conjecture asserts:

1. **Existence.** Every complete physical scale family has an
   asymptotic-time boundary.
2. **Coordinate invariance.** Regular changes of clocks, couplings,
   resolutions and system-size coordinates transport the boundary without
   changing its physical strata.
3. **Limit completeness.** Every physically admissible joint asymptotic
   regime is represented by a boundary point or stratum; no ordered limit is
   silently discarded.
4. **Wall law.** Long-time recurrence, persistence and temporal-dimension
   phases are locally constant on open strata and can change only across
   classified scaling walls.
5. **Crossover universality.** Systems with the same boundary initial data on
   one stratum have the same rescaled long-time law there, independent of
   higher-order microscopic corrections.
6. **Observer covariance.** Changing observer quotients the boundary's
   temporal sectors but preserves the complete boundary law.
7. **Closed/open unity.** Phase resolution and dissipative decay are two
   real/complex aspects of the same scaling boundary: a mode is unresolved,
   in crossover, or asymptotically completed according to one comparison
   between its characteristic exponent and observation scale.
8. **Finite/infinite compatibility.** Finite-system boundaries form
   compatible restrictions of the infinite or thermodynamic boundary; a
   claimed infinite phase not arising from any compatible boundary family is
   unphysical.
9. **Interaction law.** An arbitrarily weak nonzero interaction may create
   new asymptotic temporal strata even though it cannot create a finite-time
   discontinuity.
10. **No privileged infinity.** Two inequivalent boundary directions cannot
    be identified merely because both are denoted \(T=\infty\).

## Exact finite shadow suggested by the corpus

This section is a post-conjecture theorem target, not the definition of the
principle.

Let a visible spectral character of a finite analytic family have detuning
\[
  \delta_\chi(g)=g^{b_\chi}u_\chi(g),
  \qquad
  u_\chi(0)\ne0.
\]
Observe on a horizon
\[
  T(g)\asymp |g|^{-s}.
\]
Then
\[
  T(g)|\delta_\chi(g)|
  \asymp |g|^{b_\chi-s}.
\]
The predicted three regimes are:
\[
  \begin{array}{c|c}
  s<b_\chi & \text{unresolved / effectively constrained}\\
  s=b_\chi & \text{finite universal crossover}\\
  s>b_\chi & \text{fully phase-resolved}.
  \end{array}
\]

For a contractive mode whose decay defect satisfies
\[
  1-|\lambda_\chi(g)|
  =|g|^{b_\chi}v_\chi(g),
  \qquad v_\chi(0)>0,
\]
the same comparison predicts:
\[
  \begin{array}{c|c}
  s<b_\chi & \text{effectively persistent}\\
  s=b_\chi & \text{finite survival crossover}\\
  s>b_\chi & \text{asymptotically transient}.
  \end{array}
\]

The universal finite theorem sought is not only these scalar estimates. It
must construct the simultaneous observer-visible character filtration,
classify relations among equal-order initial forms, and prove the limiting
return or survival law on every stratum.

## Why the corpus points here

| Corpus fact or failure | Proposed boundary shadow |
|---|---|
| Bounded-time dynamics is continuous as interaction vanishes | Interior convergence toward the singular corner |
| Every nonzero generic bridge can cause an integer asymptotic rank jump | Different boundary strata meet at the corner |
| Temporal characters are born at analytic valuations | Characteristic boundary walls |
| Steiner depth lower-bounds observable birth | Locality supplies lower faces of the boundary |
| Inverse detuning controls observation horizon | Duality between birth order and waiting scale |
| Observer rank grows as constraints break | Stratumwise temporal-dimension staircase |
| Finite minimax clocks depend on resolution | Resolution is another boundary coordinate |
| Contractive dynamics splits peripheral and transient sectors | Open-system faces of the same boundary |
| Pure-point and atomless completions have opposite recurrence phases | Different infinite boundary components |
| All finite moments can miss the global recurrence phase | One formal/local direction does not determine the whole boundary |
| Thermodynamic and infinite limits were previously caveats | They are coordinates of the object, not omissions |
| Source-coordinate sparsity cannot define intrinsic space | Scalar/joint scaling geometry replaces coordinate support as primitive |

The proposed common phenomenon is not “limits sometimes fail to commute.”
It is that all such failures are projections of one resolved asymptotic-time
object with a universal phase law.

## Risky consequences not supplied by the shadows

1. **Finite wall set in analytic finite systems.** Every finite analytic
   family has a finite, exactly classifiable set of temporal scaling walls
   after relations among equal-order initial forms are resolved.
2. **Integer dimension staircase.** Observer-visible temporal dimension on
   power-law horizons is a nondecreasing integer-valued staircase whose jumps
   are ranks of boundary initial-form packets.
3. **Universal crossover law.** At a wall, the rescaled return distribution
   depends only on the leading initial-form character law, not on higher
   analytic coefficients.
4. **Open/closed correspondence.** Phase birth and decay onset obey the same
   wall classification after complexification of characteristic exponents.
5. **Graph geometry as one fan.** For generic finite local Hamiltonians, the
   weighted temporal birth spectrum of the interaction graph is exactly the
   wall multiplicity spectrum of the asymptotic-time boundary.
6. **No universal ordered thermodynamic limit.** If system size \(N\), time
   \(T\) and coupling \(g\) approach their limits on different boundary rays,
   different recurrence phases may be equally physical; one sequential limit
   cannot represent all.
7. **Late-time black-hole target.** Perturbative, plateau, recurrence and
   evaporation regimes must occupy compatible boundary strata of one
   observable scale family. A calculation covering only fixed-order
   perturbation or only \(T=\infty\) is boundary-incomplete.
8. **Experimental collapse.** After rescaling time by the measured leading
   birth or decay exponent, different weak-coupling strengths collapse onto
   one parameter-free crossover curve on each stratum.

Items 4--8 are conjectural. “Black hole” is unauthorized in a manuscript
until a gravitational observable family is constructed and formalized.

## First experiment

Use two finite quantum registers with a tunable bridge \(g\). Measure one
source-complete family of return reporters over observation horizons
\[
  T\propto |g|^{-s}
\]
for several \(s\) and several nonzero \(g\).

The conjecture predicts:

1. bounded-time data converge to the disconnected law as \(g\to0\);
2. temporal rank resolves in integer steps as \(s\) crosses birth exponents;
3. at each crossing, rescaled return data collapse to a common curve
   determined by leading initial forms;
4. sufficiently large \(s\) reaches the nonzero-coupling asymptotic return
   exponent, independent of bridge magnitude;
5. adding controlled loss produces the same wall exponents with persistence
   replaced by survival.

Failure of the collapse after complete calibration falsifies crossover
universality. A continuously varying asymptotic rank falsifies the finite
integer-wall law.

## Why this is not a nearby known statement

- Singular perturbation and matched asymptotics resolve selected limits but
  do not by themselves define a universal observer-relative
  asymptotic-time boundary.
- Renormalization-group flows organize scale dependence but do not generally
  classify exact recurrence groups, rational temporal dimension and
  return-density laws.
- Metastability and prethermalization identify long-lived regimes but do not
  make all joint recurrence/persistence limits strata of one invariant
  boundary.
- Newton polygons and tropical geometry classify valuations but do not by
  themselves supply physical return laws or observer quotients.
- Large-deviation theory controls rare events under chosen scalings but does
  not identify the complete space of physically inequivalent infinities.
- Noncommuting limits are widely known. Novelty requires the existence,
  completeness, wall law, open/closed correspondence and exact
  recurrence-density transport of one boundary object.

If the construction reduces to a standard blow-up or RG phase diagram with
new names, the conjecture is not novel.

## Hard falsifiers

1. physically equivalent regular parameterizations yield inequivalent
   boundary strata;
2. a finite analytic family requires infinitely many unclassifiable scaling
   walls;
3. temporal dimension varies within one open stratum;
4. equal leading boundary data yield different rescaled return laws because
   higher coefficients remain relevant;
5. observer quotienting fails to commute with boundary restriction;
6. phase resolution and decay onset cannot inhabit one characteristic
   boundary law;
7. graph-local temporal birth multiplicities fail to match boundary jumps
   generically;
8. infinite finite-volume restrictions do not define an
   exhaustion-independent boundary object;
9. continuum or thermodynamic phases require extra data absent from every
   finite boundary chart;
10. black-hole late-time regimes cannot be embedded in one observable
    boundary family;
11. primary literature already proves the same complete boundary
    classification and recurrence laws;
12. no experiment distinguishes the principle from ordinary crossover
    scaling;
13. the only universal theorem is the scalar identity
    \(Tg^b\), with every multi-mode and physical claim model-dependent.

## Paper gate

No statement from this card enters the manuscript until:

1. the finite simultaneous boundary object is dependency-closed on paper;
2. its temporal-dimension staircase and stratumwise return laws are proved;
3. the closed/open correspondence is proved in a common formalism;
4. every mathematical claim is formalized unconditionally;
5. external priority is audited across singular perturbation, RG,
   metastability, tropical dynamics, spectral theory and recurrence;
6. one feasible crossover-collapse protocol is derived; and
7. a hostile reviewer agrees that the result is a new boundary law, not a
   repackaged scaling variable.

The existing interaction-created rank jump is one boundary face, not the
universal law.

## Decisive hostile result — arithmetic recurrence has no open wall strata

`[FALSIFIED 2026-07-30]`

The frozen wall law says exact long-time recurrence and temporal-dimension
phases are locally constant on open boundary strata and change only across
classified scaling walls. A three-level analytic family disproves this.

Take projective gaps
\[
  \omega_1(g)=1,\qquad \omega_2(g)=g.
\]
Its exact projective temporal dimension is
\[
  d(g)
  =
  \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}\{1,g\}
  =
  \begin{cases}
  1,&g\in\mathbb Q,\\
  2,&g\notin\mathbb Q.
  \end{cases}
\]
Both \(\mathbb Q\) and its complement are dense in every real interval.
Therefore no nonempty open parameter stratum has constant exact temporal
dimension. The Hamiltonian and every bounded-time unitary observable depend
continuously—indeed analytically—on \(g\), while the completed recurrence
torus dimension changes on two interpenetrating dense sets.

This is not repaired by blowing up the corner \(g=0,T=\infty\). Power-law
valuation distinguishes whether \(Tg\) vanishes, remains finite or diverges,
but it does not distinguish rational from irrational nonzero \(g\). Exact
infinite-time orbit closure retains arithmetic relation data at every
nonzero scale.

The same obstruction holds in arbitrary finite dimension. For
\(\omega\in\mathbb R^n\), every rational rank
\[
  1\le
  \dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
  \{\omega_1,\ldots,\omega_n\}
  \le n
\]
occurs arbitrarily close to every \(\omega\): approximate \(\omega\) inside
a rational \(k\)-plane whose direction is chosen arbitrarily close to the
target direction, then choose coordinates of exact rational rank \(k\)
within that plane. Maximal rank is residual and full measure, while every
lower-rank locus is still dense.

Hence exact recurrence rank is not an ordinary phase label on analytic
parameter space. A finite fan, manifold-with-corners or locally finite wall
stratification cannot carry it.

## No-go closure

- **Exact killing mechanism:** rational and irrational spectral-relation
  strata are simultaneously dense.
- **Strongest positive survivor:** analytic birth/decay valuations do produce
  finite-horizon crossover walls for each fixed finite character family.
  These walls classify operational resolution, not exact completed
  recurrence rank.
- **New insight:** long-time physics has at least two irreducible layers:
  a smooth/valued finite-horizon layer and an arithmetic relation-completion
  layer. Treating both as one ordinary geometric boundary loses exact
  recurrence.
- **Consequent theorem target:** prove nowhere-continuity/dense-realization of
  every temporal rank in Hermitian Hamiltonian space, together with uniform
  bounded-horizon indistinguishability and the induced dense discontinuity of
  exact return-density exponents.
- **Required successor:** a law in which temporal dimension is
  scale-dependent and arithmetic completion is a fiber or limiting
  refinement, not a locally constant phase of the analytic base.
- **Lean status:** no manuscript claim relies on the falsified wall law. The
  finite dense-rank and bounded-time continuity theorems are promising exact
  obligations but are not yet formalized.

## Log

- 2026-07-30 — Frozen after factorization-first conjectures failed under
  source mixing and external subsystem-relativity priority. The repeated
  invariant was the singular joint corner of weak interaction, long
  observation, increasing resolution and infinite completion. No boundary
  construction or proof route was selected before freeze.
- 2026-07-30 — Retired after the analytic family with gaps \(1,g\) showed
  that exact recurrence dimension has dense arithmetic discontinuities and
  cannot obey the proposed open-stratum wall law.
