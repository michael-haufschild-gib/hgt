# Static-local quantum complexity law

- **ID:** static-local-complexity-law
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** Brown--Susskind complexity conjecture; master research goal
- **Statement:** Prove the complete growth--plateau--recurrence history for a concrete ensemble of fixed-locality, time-independent Hamiltonians, together with permanent efficient distinguishability from Haar randomness.

## Goal

Unconditionally prove Brown--Susskind's full law in ordinary autonomous
many-body dynamics. The final result must not substitute stochastic driving,
random circuits, growing locality, exact gate complexity, an assumed
complexity-class separation, or a nonphysical exponentially described
Hamiltonian.

### Scientific question and public headline

The paper is to answer a broader question than whether one chosen complexity
metric grows:

> Can an ordinary isolated quantum system computationally skip its own future?

The proposed answer is a **computational arrow-of-time law**.  For the generic
fixed-locality many-body phase, reaching the state at physical time `t` costs
order `t` elementary operations until exponential saturation; the system then
spends almost all time at maximal complexity and returns to a simple state only
on the doubly exponential recurrence scale.  Locality remains efficiently
observable throughout, so maximal complexity is not Haar randomness.

This one theorem would resolve three existing open problems rather than occupy
a gap between them:

1. Brown--Susskind's growth--plateau--recurrence history underlying the proposed
   growth of black-hole interiors.
2. Brown--Freedman--Lin--Susskind Conjecture 2 on exponentially late directional
   cut loci in critical complexity geometry.
3. Atia--Aharonov's open problem of proving that a typical local Hamiltonian
   cannot be fast-forwarded, and thereby identifying a physical origin of the
   computational time--energy uncertainty principle.

### Unifying conjectural jump: autonomous computational time

The research target is not the conjunction of those three problems.  It is the
following proposed law of which they would be consequences:

> **No-Shortcut Law for Autonomous Time.**  After fixing energy scale and
> observational resolution, generic irreducible local quantum matter reaches
> its future state by an essentially shortest local quantum computation until
> its finite state capacity is exhausted.  Thereafter it occupies maximal
> complexity for asymptotic density one and can become simple again only on
> its full spectral-recurrence scale.

For the Choi clock of `H_n`, the falsifiable mathematical form is

\[
 C_\varepsilon(\Phi_{H_n}(t))
   =\widetilde\Theta\!\left(
      \min\{\Lambda(H_n)|t|,\,2^n\}\right)
\]

from the resolution time to exponential saturation, followed by a
`exp(Theta(2^n))` first return to polynomial complexity.  Here `Lambda(H_n)`
is an explicit local interaction-rate normalization, not an adjustable fit
parameter, and the tildes may hide only the polynomial factors stated in the
theorem.  A permanent efficient locality witness must hold on the same event.

This would identify elapsed autonomous time with irreducible preparation work,
not merely correlate two curves.  In a holographic model for which complexity
has a geometric dual, it would say that the growing interior cannot be reached
by a shorter boundary preparation.  That transfer remains forbidden until the
law is proved for the corresponding SYK/CFT model.

Literal quantification over every Hamiltonian is false: `H = 0`, commuting
models, free systems, and finite-order evolutions can be fast-forwarded or
recur immediately.  Universality must therefore be a proved classification:
the no-shortcut phase is characterized by explicit spectral and computational
irreducibility predicates, while the exceptional phases are characterized by
the precise invariant that collapses.  Calling only the generic branch
"universal" without this complementary classification is not allowed.

The first headline theorem must concern robust state complexity (equivalently,
the thermofield-double/Choi trajectory after its fixed linear-size
preparation), not only black-box query complexity or uniform simulation.
Atia--Aharonov explicitly distinguish non-fast-forwarding of a unitary from the
stronger possibility that its distinguished evolved state has a shorter
preparation.  Closing only the former does not close this card.

The minimum target model is the standard all-to-all fixed-`q` Pauli
Hamiltonian ensemble on `n` qubits,

\[
  H_n=\sum_{1\leq |P|\leq q} J_P P,
\]

with fixed `q >= 2`, independent centred Gaussian coefficients under an
explicit normalization, a fixed product input state, and approximate state
circuit complexity relative to a fixed finite universal two-qubit gate set.
The intended extension includes fixed-`q` SYK and geometrically local spin
ensembles; neither extension may be asserted before proof.

## Master theorem target

Fix approximation error `0 < epsilon < epsilon_0`. Prove explicit constants
and a high-probability event in the Hamiltonian ensemble on which all four
parts hold:

1. **Growth.** After the resolution time and before exponential saturation
   time, approximate state circuit complexity has matching linear upper and
   lower bounds, up to explicitly stated polynomial factors in `n`.
2. **Plateau.** Complexity reaches order `2^n` and remains within a fixed
   fraction of maximal state complexity for all but a quantitatively negligible
   fraction of the subsequent time window.
3. **Recurrence.** The first post-saturation return to polynomial complexity
   has matching doubly exponential upper and lower scales.
4. **Complexity without randomness.** At every evolution time, the same
   fixed-locality unitary ensemble is distinguishable from Haar randomness by
   an explicit polynomial-time two-query experiment with inverse-polynomial
   advantage.

Quantifiers over time, probability, approximation error, circuit ancillas,
gate geometry, and norms remain part of the theorem and may not be relegated
to prose. `Chaotic`, `generic`, `black-hole-like`, and `typical` are forbidden
as hypotheses unless replaced by explicit mathematical predicates and then
proved for the target ensemble.

## Gates

- [x] 0 -> 1 in-progress: externally documented open problem; concrete first model; attack decomposition
- [ ] 1 -> 2 fully-proven: complete paper proof of all four parts, `[PROVED HERE]`, no open dependency
- [ ] 2 -> 3 formalized: every mathematical claim has a dependency-closed Lean theorem; no `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
- [ ] 3 -> 4 publication-ready: standalone paper passes hostile specialist and Nature editorial review

## Existing Lean building blocks found before new code

- `FiniteSpectralHaarRecurrenceLaw.lean` proves weak convergence of a
  rationally independent deterministic phase flow to normalized Haar measure
  on its full finite torus.
- `FiniteSpectralRecurrenceFrequencyLaw.lean` transfers that convergence to
  upper and lower long-time frequencies of high-fidelity recurrence targets.
- `ObserverReturnLocalVolumeLaw.lean` proves exact local target-volume bounds
  with exponent equal to half observer temporal dimension.
- `ObserverReturnGlobalLocalizationLaw.lean` localizes sufficiently small
  global return defects into chosen local charts.
- `UniversalProjectiveRecurrenceCapstoneLaw.lean` identifies balanced spectral
  relations and temporal rank.
- `RadialAngularRecurrenceCompletionLaw.lean` contains finite diagonal unitary
  evolution and its integer-time bridge.
- `FiniteAndersonAllTimeRecurrenceLocalitySeparationLaw.lean` supplies concrete
  finite local Hamiltonians with maximal projective recurrence rank, but does
  not supply circuit-complexity growth.
- `FiniteHorizonCStarPerturbationLaw.lean` supplies finite-time Hamiltonian
  distinguishability bounds, but not the unknown-Hamiltonian two-query Haar
  distinguisher.

No circuit/gate complexity definition or theorem was found in the formal
corpus. No Lean code for that layer is authorized until the paper definitions
and mathematical lemmas are dependency-closed.

## Proof obligations

### O1. Robust circuit model

Define approximate state complexity, allowed ancillas, gate placement, metric,
and a finite circuit-net counting theorem with the correct dependence on
`n`, depth, and `epsilon`.

### O2. Static spectral orbit

Prove maximal projective spectral rank and full input-state spectral support
for the concrete fixed-`q` ensemble, then transfer existing spectral Haar laws
to the state orbit.

**Paper-proof progress.** `../2-fully-proven/generic-two-local-spectral-monodromy.md`
proves that the generic two-local Pauli characteristic polynomial has full
`S_(2^n)` spectral monodromy.  It follows that every full-density `q >= 2`
Pauli ensemble has rationally independent projective energy gaps almost surely.
Using the Choi trajectory gives exactly uniform spectral weights, removing the
separate eigenvector-delocalization requirement for the operator-complexity
law.  Lean now certifies the full-symmetric permutation-to-relation-rigidity
step and generation of the full Boolean-hypercube symmetric group by edge
transpositions.  The analytic bridge from the two-local Pauli family to those
branch transpositions remains to be formalized, so O2 is not yet closed.

### O3. Local spectral complexity transversality

Prove that low-complexity state neighborhoods occupy exponentially small Haar
volume on the static spectral orbit. This is the missing replacement for
full-unitary designs, which static fixed-locality evolution cannot form.

**Paper-proof progress.**
`../2-fully-proven/universal-static-choi-complexity-plateau.md` proves an
eigenbasis-free theorem for the Choi/thermofield-double spectral torus.  Every
trace-distance ball has Haar mass at most

\[
  D e^{D/2}\left({\pi(1-\sqrt{1-4\delta^2})\over2}\right)^{(D-1)/2}.
\]

A union over all circuits of size at most `s` gives an explicit
`M^(s+1)` multiple of this bound.  Thus, at fixed small error, all but
`exp(-Omega(D))` of completed time has approximate circuit complexity
`Omega(D/log n)` for local gates, for every eigenbasis.  This closes O3 on
paper once combined with O2.  Lean now certifies translated-cap measure
invariance, controlled-target and finite-dictionary union bounds, the exact
Hilbert--Schmidt geometry of equal-weight Choi phase densities, and the
metric-displacement-to-coherence implication.  Circuit-word counting and the
metric-ball capstone are also compiled; only the completed-time Portmanteau
specialization remains.  The result proves the plateau occupation law; it does
not imply O4's pointwise linear growth or O5's first hitting time.

### O4. Linear no-shortcuts theorem

Prove a robust lower bound matching direct Hamiltonian-simulation complexity
through exponential time. This is the central open core, not a corollary of
recurrence or phase equidistribution.

More precisely, the geometric core is Brown--Freedman--Lin--Susskind
Conjecture 2 (Nature 622, 58--62, 2023): for the critical complexity metric,
a typical fixed-local `H` direction does not meet its directional cut locus
until exponential time.  The paper must replace both informal words by an
explicit fixed-`q` Gaussian ensemble and a quantified high-probability cut-time
bound, then transfer that geometric distance bound to robust finite-gate state
complexity with only the permitted polynomial losses.  Proving only absence of
conjugate points is insufficient: that excludes local variations but not a
globally shorter path.

#### Failed circuitwise entropy route and surviving aggregate word escape

An initial candidate was unrestricted worst-target concentration

\[
 Q_\varepsilon(t)=\sup_\psi
   \Pr_H\{\Delta(\Phi_H(t),\psi)\leq\varepsilon\}.
\]

That candidate is false at the strength needed for O4.  A static `q`-local
ensemble has only `m=poly(n)` Gaussian parameters.  On a coefficient ball of
fixed positive probability, the Duhamel bound makes
`H -> exp(-itH)` `O(t)`-Lipschitz.  An `m`-dimensional parameter net therefore
covers the evolved ensemble by at most

\[
  (C t/\varepsilon)^m
\]

metric balls.  Pigeonhole forces some target ball to have probability at least
`(C t/epsilon)^(-m)`, so unrestricted projective min-entropy is at most
`O(m log(t/epsilon))`.  It cannot certify complexity linear in exponential
time.  This no-go also explains why fixed-order design and ambient-volume
arguments stall.

Restricting the target to computations that would constitute a shortcut does
not rescue the circuitwise union-bound strategy.  Define

\[
 Q_{\varepsilon,s}^{\rm short}(t)=
   \sup_{C:\,|C|\leq s}
   \Pr_H\{\Delta(\Phi_H(t),C\Phi_0)\leq\varepsilon\}.
\]

The identity circuit already gives a sharp obstruction.  Let
`H(J)=sum_(a=1)^m J_a P_a` with `||P_a|| <= 1`, and choose one nonidentity
Pauli word `P_1`.  For every large `t`, choose an integer `k` with
`2 pi k/t` in a fixed positive compact coefficient interval and put
`J^(0)=(2 pi k/t,0,...,0)`.  Then

\[
 e^{-itH(J^{(0)})}=e^{-2\pi i kP_1}=I.
\]

On a coefficient box of radius `c epsilon/(tm)` around `J^(0)`, Duhamel's
inequality keeps the evolution within `epsilon` of the identity.  The Gaussian
density is bounded below on that box, so for constants depending only on the
fixed normalization,

\[
 Q_{\varepsilon,s}^{\rm short}(t)
 \geq c_0^m\left({\varepsilon\over tm}\right)^m
 \qquad(s\geq0).                                      \tag{O4.1}
\]

This obstruction persists on a fixed-energy shell: `J^(0)` has order-one
norm.  Consequently

\[
 -\log Q_{\varepsilon,s}^{\rm short}(t)
 \leq m\log(tm/\varepsilon)+O(m),                     \tag{O4.2}
\]

and therefore cannot satisfy the previously proposed bound

\[
 -\log Q_{\varepsilon,s}^{\rm short}(t)
   \geq (s+1)\log M+\gamma_n(t)
 \quad\text{for }s\asymp t/\operatorname{poly}(n)
\]

once `s` is much larger than `m log t`.  Thus no proof may pay for circuits one
at a time.

The surviving object is the **whole shortcut locus**

\[
 \mathcal B_{\varepsilon,s}(t)
 =\{H:C_\varepsilon(\Phi_H(t))\leq s\}.
\]

The new hard target is an **aggregate autonomous word-escape theorem**.  After
fixing the energy shell, prove directly, without a union over circuit words,

\[
 \Pr_H\!\left\{
 C_\varepsilon(\Phi_H(t))
 \leq {a\Lambda(H)t\over\operatorname{poly}(n)}
 \right\}
 \leq
 \left({A tm\over\varepsilon}\right)^{-c m}           \tag{O4.3}
\]

uniformly from the resolution time through exponential saturation.  The
power-law-in-`t` failure with exponent proportional to parameter dimension is
strong enough for a time net through `t=exp(Theta(n))`, while `(O4.1)` shows
that its functional form is optimal up to constants.  This is a global
intersection theorem between the evolved local-Hamiltonian manifold and the
low-word metric variety; ordinary small-ball estimates and circuit counting
cannot prove it.

Conceptually, the missing invariant is noncommutative.  Exact spectral
relations are the abelianized shadow and control completed recurrence.
Relations between a local one-parameter subgroup and short local-gate words
control pre-saturation computation.  Finite-dimensional matrix identities
force saturation.  The proposed universal law says that generic irreducible
local matter has no robust low-word relations before that capacity boundary.
Its precise new mathematical content is `(O4.3)`, not the terminology.

This is the proposed physical reinterpretation: autonomous time can generate
**computational inaccessibility without statistical randomness**.  The orbit
remains a low-parameter, efficiently non-Haar family, while every center that
captures appreciable mass moves beyond the circuit budget available at that
time.  Kotowski--Oszmaniec--Horodecki obtain an immediate extremal jump for
GUE and Haar-conjugated diagonal generators using load-bearing unitary
invariance; no audited result proves this local ballistic law.

#### Dynamical NLTS equivalence

Fix a trivial gapped parent Hamiltonian `K_0` with unique product ground state
`Phi_0` and define

\[
 K_t=e^{-itH}K_0e^{itH}.
\]

`K_t` is unitarily equivalent to `K_0`, so every eigenvalue and the gap remain
unchanged, while its unique ground state is `Phi_H(t)`.  Bounded-observable
continuity gives the unconditional implication

\[
 \|\phi-\Phi_H(t)\|\leq\varepsilon
 \Longrightarrow
 \langle\phi,K_t\phi\rangle
 \leq E_0+2\|K_t\|\varepsilon.
\]

Consequently O4 follows from a **dynamical NLTS law**: every circuit shorter
than normalized physical time has an extensive energy separation from the
ground energy of `K_t`.  This turns endpoint complexity into an extremal-energy
problem, avoiding the fatal fact that the evolved state has only typical
conserved energy under `H` itself.

The new family has the Heisenberg/Gaussian-chaos expansion

\[
 K_t=\sum_{r\geq0}{(it)^r\over r!}\,\operatorname{ad}_H^r(K_0).
\]

The required new mathematics is uniform control of this hierarchy over the
short-circuit class.  Low-depth dependency-graph methods can access the first
support-growth regime; extending the barrier to exponential circuit size must
use chaos order and circuit entropy after lightcones have saturated.
`DynamicalParentComplexityBridge.lean` now formally proves exact transported
energy covariance, the `2||K_t||` expectation Lipschitz bound, and the strict
energy-barrier certificate.  It does not assume or prove the dynamical NLTS
barrier.

### O5. Quantitative first hitting

Upgrade completed-time occupation to a first-return lower bound from the
simple initial state and match it with a deterministic doubly exponential
upper bound. Unique ergodicity alone is insufficient.

### O6. Permanent locality witness

Formalize an explicit two-query experiment and prove a uniform advantage for
every time in the fixed-locality ensemble. The theorem must expose all
normalizations and query resources.

### O7. Physics transfer

Prove the theorem directly for fixed-`q` SYK before making a black-hole-model
claim. A result only for abstract Pauli ensembles permits quantum-many-body
conclusions, not a claim about real black holes or spacetime interiors.

## State-design route audit

The tempting bridge

\[
  \text{high-order state design}\quad\Longrightarrow\quad
  \text{high state-circuit complexity}
\]

does not presently close O4.  Current autonomous-Hamiltonian results establish
late-time Haar moments only for each fixed design order `k`, or obtain a
finite-time error of order `1/T` while the Haar `k`-frame-potential scale is
of order `D^{-k}`.  The resulting requirement `T \gtrsim D^k` yields at most

\[
  k \lesssim \log_D T,
\]

so design order certifies at most logarithmic-in-time complexity rather than
Brown--Susskind linear growth.  Multiple quenches improve the temporal power
but replace one time-independent Hamiltonian by driven dynamics and therefore
do not satisfy the target.

The only surviving design formulation strong enough for O4 would be a new
fixed-time theorem for the *static local Hamiltonian ensemble*: design order
`k(t) \asymp t` up to `k \asymp D`, together with concentration from the
Hamiltonian ensemble to individual autonomous trajectories and robustness to
polynomial-bit coefficient perturbations.  None of these three statements is
available in the audited literature or corpus.  They remain possible proof
targets, not premises.

## Hard barrier

Robust superpolynomial circuit complexity for exponentially long evolution of
succinct local Hamiltonians is tied to
`PSPACE not subset of BQP/poly`. The proof programme must either establish the
needed separation, find and justify a theorem formulation outside the exact
equivalence while retaining physical meaning, or fail honestly. Continuous
random coefficients do not license hiding exponential information in the
Hamiltonian: robustness and coefficient precision must be audited.

## Literature collision and exact novelty

The slogan “ballistic escape plus entropic return” and the critical-metric
picture are not themselves novel.  Brown--Freedman--Lin--Susskind already
conjecture exponentially late cut loci for typical local directions.  Earlier
work of Balasubramanian--DeCross--Kar--Parrikar excludes *local* obstructions
under the Eigenstate Complexity Hypothesis but explicitly leaves global
shortcuts open.  Brown's Bishop--Gromov argument proves exponential complexity
for typical ambient unitaries, not for the one-parameter orbit of a succinct
static local Hamiltonian.

The admissible novelty claim is therefore exact and falsifiable: first
unconditional proof of the directional critical-metric conjecture for an
ordinary time-independent fixed-locality ensemble, followed by the first
single theorem deriving its growth, plateau, first low-complexity recurrence,
and all-time non-Haar witness.  If the directional cut-time theorem cannot be
proved, no geometric slogan is promoted as a discovery.

## No-go discipline

Failure of O4 kills the master theorem. It does not authorize publication of
O2, O3, O5, or O6 alone as the same universal law. Any positive survivor must
receive a new title and an independent significance audit.

## Log

- 2026-08-01 -- Created in 1-in-progress after literature-first collision
  audit. Existing recurrence and Haar infrastructure inventoried; circuit
  complexity absent; O4 identified as open core.
- 2026-08-01 -- Audited the autonomous state-design route. Fixed-order moment
  convergence and one-quench finite-time estimates imply only
  `k \lesssim log_D T`; they cannot yield linear complexity growth. The route
  survives only as a substantially stronger fixed-time random-static-local-H
  design theorem with concentration and precision robustness.
- 2026-08-01 -- Immediate collision audit identified the proposed global
  minimizing-geodesic mechanism as Brown--Freedman--Lin--Susskind Conjecture 2,
  not a new slogan. O4 is now the exact unconditional resolution of that
  conjecture for a concrete fixed-`q` ensemble, including the global-shortcut
  gap that local conjugate-point arguments do not close.
- 2026-08-01 -- Closed O2 on paper by a full-symmetric spectral-monodromy
  theorem for generic two-local Pauli Hamiltonians. Isolated star-Ising edge
  degeneracies supply all Boolean-hypercube transpositions; the resulting
  `S_(2^n)` monodromy forbids every projective rational resonance almost surely.
  Choi evolution supplies uniform spectral weights. Lean remains pending.
- 2026-08-01 -- Promoted the scientific target from a four-result conjunction
  to the falsifiable No-Shortcut Law for Autonomous Time: normalized physical
  duration equals irreducible endpoint-preparation work until finite-state
  saturation, after which spectral entropy fixes the plateau and return scale.
  Recorded fast-forwardable systems as a required complementary class rather
  than hiding them behind "generic".
- 2026-08-01 -- Formalized exact equal-weight Choi phase-density geometry and
  the displacement-to-coherence implication in
  `StaticChoiPhaseDensity.lean`; the file compiles in isolation.  Together with
  `StaticChoiPhaseTargetEntropy.lean`, this closes the geometric core of O3 in
  Lean, leaving finite circuit counting and completed-time specialization.
- 2026-08-01 -- Retired the circuitwise temporal-min-entropy route.  A
  normalized one-Pauli recurrence point gives the identity circuit capture
  probability at least `t^(-O(m))`, contradicting the `exp(-Omega(s))` bound
  needed by a word-by-word union when `s` is linear in exponential time.
  Replaced it by the aggregate autonomous word-escape target `(O4.3)`, whose
  failure exponent is compatible with this sharp obstruction and sufficient
  for uniform-in-time growth.
- 2026-08-01 -- Lean-proved the dimension-free analytic core of that no-go in
  `FiniteHorizonCStarPerturbationLaw.lean`: an exact periodic Hamiltonian is
  the center of an operator-norm shortcut tube with radius proportional to
  `epsilon/|t|`.  Gaussian box volume remains paper-only and is not a
  manuscript claim.
