# Stationary recurrence completion and conversion law

- **ID:** time-return-duality-law
- **Stage:** 1-in-progress
- **Type:** MASTER THEOREM PROGRAM / UNIVERSAL STATIONARY RECURRENCE LAW
- **Source:** recurrence corpus synthesis
- **Statement:** Every stationary quantum return experiment factors through one maximal
  unoriented system--clock quotient.  On its recurrent carrier, one projective detuning map
  splits phase capacity exactly into recurrence constraints and observable temporal directions.
  In finite rank, temporal dimension is twice the small-defect return-volume exponent.
  Centered complete-time sampling has one unique return law for every
  probability spectrum; its moments are exactly additive energy-gap
  collision probabilities. Interaction converts constraints into temporal
  directions one-for-one.

## Goal

Replace novelty-by-assembly with one operational law whose shadows are the
existing constraint-conversion, observer-quotient, water-entropy,
interaction, countable-depth and peripheral-carrier results.

The law is most naturally an exact sequence, not a list:
\[
  0\longrightarrow \mathcal C_H
   \longrightarrow \mathcal X_H
   \xrightarrow{\;\mathcal D_H\;}
   \mathcal T_H
   \longrightarrow 0.                                      \tag{E}
\]
Here \(\mathcal X_H\) is projective phase-character capacity,
\(\mathcal D_H\) evaluates a character on the energy packet,
\(\mathcal C_H=\ker\mathcal D_H\) is the complete exact-recurrence relation
space, and \(\mathcal T_H=\operatorname{im}\mathcal D_H\) is the temporal
gap module visible to completed recurrence.  This formulation survives
infinite carriers: dimensions may cease to be finite, but the kernel,
quotient and image remain exact.

For a finite carrier `(E)` yields the scalar conservation law
\[
  \boxed{\tau+\rho=C},                                      \tag{C}
\]
and the return-volume theorem upgrades it to the operational identity
\[
  \boxed{2s_{\rm ret}+\rho=C},\qquad
  s_{\rm ret}:=
  \lim_{\eta\downarrow0}
    \frac{-\log V(\eta)}{\log(1/\eta)}.                    \tag{R}
\]
Thus every destroyed recurrence constraint reappears as one temporal
direction and adds one half to the high-fidelity return-scarcity exponent:
\[
  \Delta\tau=-\Delta\rho=2\Delta s_{\rm ret}.              \tag{I}
\]

The candidate primitive is no longer the finite-dimensional Weyl exponent.
For an arbitrary probability energy law \(\mu\) and probability clock law
\(\rho\), put
\[
  \nu_\mu=\mu*\widetilde\mu,\qquad
  \sigma_\rho=\frac{\rho+\widetilde\rho}{2},
\]
and define the complete sampled recurrence law
\[
  \mathfrak R(\mu,\rho)
  =
  \bigl(\widehat{\nu_\mu}\bigr)_*\sigma_\rho.
  \tag{URQ}
\]
Here \(\widehat{\nu_\mu}(t)=|\widehat\mu(t)|^2\in[0,1]\).
The corpus already proves that the two quotient maps in `(URQ)` are maximal
under universal cross-testing: systems are indistinguishable to every clock
exactly when their difference laws agree, and clocks are indistinguishable
to every system exactly when their orientation quotients agree.

The stationary-completion theorem is the single weak limit
\[
  \mathfrak R(\mu,\rho_T)
  \Longrightarrow \mathfrak R_\infty(\mu),
  \qquad
  \rho_T=\operatorname{Unif}[-T,T],
  \tag{SC}
\]
which now exists uniquely for every probability energy law, without a
finite, pure-point or absolute-continuity premise, and obeys the complete
moment identity
\[
  \boxed{
  \int_0^1 x^n\,d\mathfrak R_\infty(\mu)(x)
  =
  \bigl(\nu_\mu^{*n}\bigr)(\{0\})
  \quad(n\geq0).
  }
  \tag{M}
\]
Hence the stationary recurrence law is exactly the additive collision
hierarchy of the spectral difference law.  If \(\mu\) is atomless then
\(\mathfrak R_\infty(\mu)=\delta_0\), including singular-continuous spectra
whose pointwise fidelity need not decay.  For countable pure-point packets,
the corpus separately constructs Haar measure on the exact relation hull;
the remaining pure-point bridge is to identify its fidelity pushforward
with this canonical law in one capstone theorem.  The finite Weyl law below
is a local geometric corollary of `(SC)`--`(M)`, not the master law.

The intended physical sentence is:

> **Quantum recurrence reveals the geometry of stationary time, but its
> maximal observable is intrinsically unoriented.**

This wording has two exact obligations.  “Geometry” means the recurrent
atomic relation hull, its observer quotient, target volumes and finite-rank
metric.  “Unoriented” means the proved maximal clock quotient
\(\rho\mapsto\sigma_\rho\), not a claim that all causal observables or all
experiments are time-reversal blind.

For a finite probability-weighted quantum spectrum, let \(K\) be the exact
projective orbit hull, let \(\nu_K\) be Haar measure on \(K\), and let
\[
  V(\eta)=\nu_K\!\left\{z:
    \left|\sum_j w_jz_j\right|\ge 1-\eta\right\}.
\]
Write \(\tau\) for rational rank of visible energy gaps, \(C\) for
projective phase capacity and \(\rho\) for exact balanced-relation rank.
Conjecture:
\[
  \tau
  =2\lim_{\eta\downarrow0}
      \frac{-\log V(\eta)}{\log(1/\eta)}
  =C-\rho.
\]
More sharply, after a primitive \(\tau\)-torus parametrization of the orbit
hull,
\[
  V(\eta)\sim
  \frac{\operatorname{vol}(B_\tau)}
       {(2\pi)^\tau\sqrt{\det G_{\mathcal O}}}
  (2\eta)^{\tau/2},
\]
where \(G_{\mathcal O}\) is the positive temporal metric obtained by
restricting the observer-weighted gap quadratic form to the hull tangent
space. The precise factor \(2\eta\) is for survival amplitude threshold
\(1-\eta\); an observer displacement threshold uses its own quadratic
defect directly.
The metric statement must remain valid after an arbitrary finite observer
quotient. Interaction then obeys
\[
  \Delta\tau=-\Delta\rho
  =2\,\Delta(\text{return-scarcity exponent}).
\]
For summable countable pure-point packets, the finite exponent is replaced
by a running profile whose exact slope is the visible spectral count. For a
finite contraction, the law acts on its peripheral carrier after transient
decay.

## Gates

- [x] 0 → 1 in-progress: well-posed, corpus shadows identified, primary
  novelty kill test started
- [ ] 1 → 2 fully-proven: complete relation-aware small-target proof,
  observer pullback proof, countable and peripheral corollaries
- [ ] 2 → 3 formalized: unconditional Lean theorem(s), foreground
  `lake env lean` verification and standard-axiom audit
- [ ] 3 → 4 publication-ready: master paper rewritten around this identity,
  source-complete priority audit and hostile Nature review

## Approach

1. Kill-test against quantitative recurrence/local-dimension literature.
   Existing mixing theorems do not cover nonmixing quasiperiodic quantum
   phase flows or the exact constraint-conversion identity.
2. Identify the countable pure-point stationary law with the fidelity
   pushforward of Haar measure on its exact relation hull.
3. Represent the finite orbit hull as the image of a full-rank integer map
   from a \(\tau\)-torus after choosing a rational gap basis and clearing
   denominators.
4. Pull the fidelity defect back to that torus. Positive spectral weights
   make its Hessian positive definite modulo the finite kernel. Prove
   two-sided quadratic comparison on a small fundamental neighborhood.
5. Convert quadratic comparison to two-sided Haar-volume bounds
   \(c\eta^{\tau/2}\le V(\eta)\le C\eta^{\tau/2}\).
6. Join with projective rank–nullity, observer action, weak interaction and
   fixed-hopping realization.
7. Recover the existing water entropy as the relation-free finite-resolution
   form and spectral-depth entropy as its countable running form.

## Kill tests

- If zero weights are allowed, invisible coordinates must first be removed;
  otherwise the Hessian is degenerate and the stated exponent is false.
- Finite cyclic orbit hulls have \(\tau=0\) and nonvanishing target mass;
  exponent \(0\), as required.
- Individual first-return exponents of Liouville rotations need not equal
  dimension. The law concerns exact orbit-Haar return scarcity and minimax
  clock entropy, not every fixed spectrum's first-hit asymptotic.
- Atomless spectra do not have a finite torus exponent; existing zero-density
  law is the dispersive branch, not evidence for a finite equality.
- Rank–nullity alone is not novelty. Operational return-volume identity and
  physical interaction conversion are required.

## RH-corpus stress test: the same quotient boundary

The RH corpus was audited as a hostile test of the interpretation, not as a
source of an RH claim for this paper.

The repeated exact pattern is:

1. reflection-invariant positive, quadratic or intensity readers can be
   complete for their even quotient;
2. the source-facing orientation lives in an odd phase/character lift;
3. passing to the quotient preserves collision location or magnitude while
   erasing the first oriented jet;
4. adding more equivalent positive criteria does not recreate the erased
   coordinate.

The clearest formal instances are:

- `Oriented reflection quotient law`: channel exchange sends the odd Cayley
  coordinate \(J\) to \(-J\); invariant entire readers descend through
  \(J^2\) and every differentiable even reader has zero first jet at the
  collision.
- `HedenmalmOrientationUpperSingularityCeilingRH`: the exact RH-facing
  criterion is analyticity of a canonical *oriented* multiplier, not merely
  positivity of a symmetric scalar.
- `SuzukiVolterraCartesianPhaseDefect`: keeping the symmetric Cartesian
  response fixed leaves a nonzero phase half-difference.
- `HorizonBogoliubovGammaObservability`: the reflected intensity core is
  differentially algebraic while the orientation-sensitive phase quotient
  and Wigner--Smith logarithmic delay are hypertranscendental and cannot be
  recovered by a finite differential circuit from intensity.
- `riemann-source-modular-superselection/main.tex`: source clock, collision
  geometry, global magnitude, diagonal positivity, odd orientation and
  global common-test positivity form a strict observable hierarchy.  Its
  central warning is that “complete” must name the quotient for which it is
  complete.

The recurrence corpus has the same architecture in an exact, non-analogical
form:
\[
  \rho\longmapsto\sigma_\rho
  \quad\text{erases clock orientation},\qquad
  \mu\longmapsto\nu_\mu
  \quad\text{erases energy origin and phase-retrieval representatives}.
\]
All return laws factor through these maps, and each map is maximal against
the opposite universal probe family.  Therefore the paper must never call
return data complete for the Hamiltonian, state, clock orientation or causal
arrow.  The allowed statement is stronger and more precise: return data are
complete for the maximal stationary recurrence quotient.

No connection to RH is authorized for the public manuscript unless a new
formal theorem explicitly connects an RH carrier to `(URQ)`.  The present
audit supplies the missing conceptual distinction, not an RH consequence.

## Local many-body generator and physical consequence

The live corpus closes two earlier objections at different proof levels.

1. `FiniteAndersonRecurrenceConstraintConversionLaw.lean` proves that for
   every fixed finite Hermitian hopping matrix, every onsite packet and every
   positive control radius, a change of onsite energies inside that radius
   erases all post-perturbation projective relations, converts the complete
   initial relation rank into temporal dimension, attains the all-order
   replica collision floor and obeys the dimension-free finite-time
   Heisenberg bound.  This is the unconditional local-Hamiltonian transfer
   already available to the manuscript.
2. `HermitianLocalExtensionRelationEscape.lean` proves the hard one-step
   tensor-local generator: a Hermitian nearest-factor extension with
   connected cross-layer lift can erase every balanced relation
   simultaneously.  The dependency-closed qudit-chain induction in
   `nearest-neighbor-qudit-projective-spectral-maximality.md` then predicts
   generic rank \(q^n-1\), exact return density
   \[
     \left(
       \frac{2\arcsin(\varepsilon/2)}{\pi}
     \right)^{q^n-1},
   \]
   and a jump from \(O(n)\) commuting rank to \(q^n-1\) under generic
   nearest-neighbour interaction.  The complete chain induction is not yet
   formalized and therefore remains forbidden in the public paper.

If that final formal bridge closes, the single physical consequence of
`(E)`--`(I)` is:

> **An arbitrarily weak bounded-range interaction can activate exponentially
> many independent temporal phases, making complete quantum repetition
> doubly exponentially rare, while every bounded-time observable remains
> perturbatively close.**

This is not a claim about spacetime dimension.  “Temporal dimension” is the
exact rank of the completed relative-phase orbit.  The possible Nature-level
contribution is the local generator and its noncommutation of weak-coupling
and completed-time limits, not the classical Kronecker--Weyl or
rank--nullity parents.

The collision interpretation supplies a second exact face of the same law.
At fixed positive spectral weights, every nontrivial balanced energy-sum
relation raises at least one long-time return moment above the permutation
floor; zero relation rank is equivalent to attaining that floor at every
order.  Constraint destruction, temporal-rank creation, return scarcity and
all-order collision extremality are therefore one event, not four assembled
results.

## Log

- 2026-07-31 — created in 1-in-progress after rejecting novelty by conjunction.
- 2026-07-31 — proved and formalized local temporal-metric brick in
  `ObserverReturnTemporalMetricLaw.lean`: exact phase defect is bounded above
  by observer Gram energy and, on the principal chart, bounds it below up to
  `π²/4`; positive visible weights make the metric nondegenerate exactly
  when gaps separate temporal coordinates. Foreground compile passed; axiom
  audit uses only `propext`, `Classical.choice`, `Quot.sound`.
- 2026-07-31 — proved and formalized
  `ObserverReturnLocalVolumeLaw.lean`: under positive coercivity constants,
  the local high-fidelity target is trapped between Euclidean balls with
  radii proportional to `√ε`, and its measure is trapped between their
  exact volumes. This proves the local `ε^(τ/2)` Weyl scale without a
  Gaussian or randomness premise.
- 2026-07-31 — removed the remaining local hypotheses in
  `ObserverReturnTemporalCoercivityLaw.lean`: every finite separating
  positively weighted gap family has a positive-definite Gram matrix,
  automatic two-sided quadratic bounds, and an automatic positive principal
  phase radius. `ObserverReturnLocalVolumeLaw.lean` now contains an
  assumption-free local ball sandwich for every such family.
- 2026-07-31 — proved the compact global localization step in
  `ObserverReturnGlobalLocalizationLaw.lean`: on any compact orbit carrier,
  the complete sufficiently small return sublevel lies in any prescribed
  neighborhood of the exact-return set. Foreground compiles passed; axiom
  audit of the new coercivity and automatic local-volume theorems uses only
  `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-07-31 — RH-wide corpus audit and
  `riemann-source-modular-superselection/main.tex` forced a stronger master:
  recurrence is a maximal unoriented quotient followed by stationary atomic
  completion.  The finite recurrence Weyl law is now a corollary.  The audit
  also forbids calling recurrence complete for the source, Hamiltonian or
  arrow of time.
- 2026-07-31 — recast the master as the exact projective detuning sequence
  `(E)` and finite recurrence conservation law `(R)`.  Corpus audit found an
  unconditional fixed-hopping Anderson conversion theorem and a formal
  one-step Hermitian tensor-local relation-erasure theorem.  The remaining
  significance gate is the Lean closure of the dependency-closed
  nearest-neighbour qudit-chain induction and its exact return-scarcity
  consequence.
- 2026-07-31 — closed arbitrary-spectrum stationary completion in
  `StationaryRecurrenceCompletionLaw.lean`.  Centered uniform time sampling
  converges weakly on the exact compact fidelity carrier for every
  probability energy law; every moment of the unique limit is the
  corresponding additive gap-collision probability.  The same module proves
  the full atomless collapse to `δ₀`, including singular-continuous spectra.
  Foreground `lake env lean` verification passed.
- 2026-07-31 — proved point-spectrum universality in
  `StationaryRecurrencePointSpectrumLaw.lean`.  If two arbitrary probability
  energy laws have the same mass at every singleton, then every convolution
  power of their energy-difference laws has the same zero collision mass and
  their complete stationary recurrence laws are identical.  Thus the
  centered-time completed fidelity distribution depends only on atom
  locations and weights; absolutely continuous and singular-continuous
  sectors are recurrence-invisible, and the atomless phase is exactly
  `δ₀`.  Foreground `lake env lean` verification and a capstone axiom audit
  passed with only `propext`, `Classical.choice`, and `Quot.sound`.  This is a
  stronger arbitrary-spectrum spine, but Nature-level novelty remains open:
  a hostile referee may view it as an all-moment Wiener corollary unless it
  yields a new local or open-system physical law.
- 2026-08-01 — rejected further local sharpening as a novelty strategy and
  froze `persistent-phase-conservation-conversion-law.md`.  The new primitive
  is persistent observer-visible phase capacity.  Exact relations, observer
  blindness and temporal directions are complementary kernels/quotients;
  continuous or transient evolution changes the persistent capacity itself.
  The finite one-for-one interaction conversion is already Lean-proved.  New
  open cores are simultaneous saturation for every countable pure-point pair,
  the weakly-almost-periodic open-system factorization, and a replica-two
  operational discriminator.  Point-spectrum scaling is now one shadow, not
  the headline.
