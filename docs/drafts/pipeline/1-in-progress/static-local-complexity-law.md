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
metric-ball capstone are also compiled.  The completed-time Portmanteau
specialization is now compiled on the physically correct projective torus as
`completedTime_zeroAnchoredPaddedCircuitTargets`.  Maximal projective spectral
rank alone makes the zero-anchored relative frequencies independent; an exact
measure-preserving global-phase split identifies projective target volume with
the full-torus Choi bound.  Thus traceless local Hamiltonians are included.
The result proves the plateau occupation law; it does
not imply O4's pointwise linear growth or O5's first hitting time.

The plateau now also has an unconditional infinite-time strengthening.
`StaticChoiSyndeticComplexityLaw.lean` proves that whenever the explicit
finite-circuit entropy bound is below one, the complement of the low-circuit
target is nonempty and open; maximal projective rank makes the physical phase
flow dense, and compactness upgrades density to syndetic return.  Hence one
finite target-dependent gap `L` exists such that **every** interval of length
`L`, at every positive or negative epoch, contains a Choi endpoint farther
than `delta` from every word in the stated circuit dictionary.  This is
strictly stronger than completed-time density: high-complexity endpoints
cannot disappear for arbitrarily long intervals.  The theorem is
nonquantitative in `L`, so it does not yet place the first hard endpoint near
the direct-simulation saturation time.

The target semantics are now full-state rather than a spectral-subspace
surrogate.  `StaticChoiFullStateProjectionLaw.lean` defines the full
`D^2`-dimensional Choi density, proves that restriction to the
diagonal--diagonal spectral block is Hilbert--Schmidt contractive, and proves
that the evolved full density restricts exactly to `uniformPhaseDensity`.
Consequently `maximallyProjective_fullChoiCircuitTargets_syndetic` separates
the true full Choi state from every arbitrary full circuit-target density with
no radius or dimension loss.  Only the conversion from this full-state
Hilbert--Schmidt metric to the paper's preferred trace/operator normalization
remains.

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

#### Proved power-amplification bridge and its sharp resolution cost

There is one unconditional backward transfer from a hard late endpoint to an
earlier autonomous endpoint.  For arbitrary unitary elements `U,V` of any
unital C-star algebra,

\[
  \|U^N-V^N\|\leq N\|U-V\|,
  \qquad
  e^{-itH\,N}=e^{-iNtH}.
\]

Consequently, if the repeated circuit endpoint `V^N` misses `e^{-iNtH}` by
at least `epsilon`, then `V` misses `e^{-itH}` by at least `epsilon/N`.
`FiniteHorizonCStarPerturbationLaw.lean` proves all three statements without
dimension, spectrum, locality or commutativity assumptions.  In an exact word
metric this turns a size-`Ns` lower bound at time `Nt` into a size-`s` lower
bound at time `t`; this is the rigorous form of backward hardness
amplification.

The same argument does **not** close robust O4 at fixed resolution: operator
error accumulates linearly under repetition, so a late `epsilon` separation
only certifies early `epsilon/N` separation.  Any successful robust theorem
must prove that coherent shortcut errors cannot track the autonomous orbit,
not merely invoke subadditivity.  This locates the missing content of O4 more
sharply than the cut-locus formulation.

There is, however, a stronger fixed-resolution transfer using autonomous time
addition rather than powers.  If `U(T)` is farther than `epsilon_late` from
every word of length `P`, `U(tau)` has an `r`-gate approximation at error
`epsilon_inc`, and

\[
  \epsilon_{early}+\epsilon_{inc}\leq\epsilon_{late},
\]

then `U(T-tau)` is farther than `epsilon_early` from every word of length
`P-r`.  Concatenating hypothetical approximants would otherwise approximate
`U(T-tau)U(tau)=U(T)`.  The compiled theorem
`circuitWordSeparated_autonomous_backward_cone` proves this for every group
metric satisfying the product-distance inequality.  Thus every hard plateau
endpoint casts a robust linear no-shortcut cone backward through time after
inserting a direct-simulation upper bound for `r(tau)`.  Unlike power
amplification, error is paid once, not divided by elapsed time.

The multiplication premise is now discharged for the physical norm model.
`unitaryCircuitWordSeparated_autonomous_backward_cone` proves the statement in
the operator-norm unitary group of every unital C-star algebra, with no matrix,
dimension, or finite-spectrum premise.  The exact norm identity under left
and right unitary multiplication supplies the joint product Lipschitz bound.

The cone and the new syndetic endpoint law also compose without loss of the
gap.  `unitaryCircuitWordSeparated_syndetic_backward_cones` proves that if
`P`-hard endpoints occur in every interval of length `L`, then for every fixed
lag `tau` the `(P-r(tau))` backward section occurs in every interval of the
same length `L`.  Thus hard endpoints generate infinitely many robust ramps
forever; cone propagation neither divides resolution nor enlarges recurrence
gaps.  A remaining semantic bridge must identify the Choi density dictionary
with the corresponding projective-unitary word targets before this composed
statement can be claimed for physical circuits in the paper.

This does not yet prove Brown--Susskind growth from the initial simple state:
O3 supplies a completed-time density of hard terminal points but no bound
placing the first such point at the direct-simulation saturation time.  The
remaining O4 content is now precisely that first-terminal-time/cut-time bound,
not robustness or infinite recurrence of the backward ramps once hard
endpoints are known.  The new syndetic theorem supplies a finite first hard
time and bounded gaps, but its compactness-produced `L` is not quantitatively
controlled.  O4 therefore requires `L` at the direct-simulation saturation
scale, uniformly with high probability in the local-Hamiltonian ensemble.

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

**Literature closure and formalization status.**  This obligation is no longer
an open research theorem.  Cui--Schuster--Mao--Huang--Brandao, *Random
unitaries from Hamiltonian dynamics*, arXiv:2510.08434 (2025), prove it for an
arbitrary distribution of fixed-`q` Hamiltonians and arbitrary evolution
times.  Their forward-only protocol prepares two copies of a random stabilizer
product state, applies the same sampled `U=exp(-itH)` once to each copy, and
measures the same uniformly sampled allowed Pauli on both copies.  For a local
Pauli dictionary of size `M_q`, its mean squared signal obeys

\[
 E_{\rm local}\geq {3^{-q}\over M_q},
 \qquad
 M_q\leq 4^q n\quad\hbox{(one-dimensional)},
 \qquad
 M_q\leq (4n)^q\quad\hbox{(all-to-all)}.
\]

The bound is uniform in time because `H` itself is the conserved local
observable.  Haar output gives exponentially small signal, yielding the
required inverse-polynomial two-query advantage for fixed `q`.  The final
paper must cite this theorem as an input; it is not part of our novelty.

`ConservedLocalCompressionWitness.lean` now certifies the
dimension-independent algebraic core: autonomous Heisenberg evolution fixes
`H` exactly; every local compression matrix with this nonzero fixed coordinate
has squared Frobenius mass at least one; its uniformly sampled mean transition
weight is at least `1/M_q^2`; and it strictly exceeds an isotropic
`1/(4^n-1)` benchmark whenever `M_q^2<4^n-1`.  Remaining Lean port obligations
are the random stabilizer-product twirl giving `3^{-q}`, the Pauli dictionary
cardinality bounds, and the explicit Haar/two-design comparison.  O6 is
therefore closed in external mathematics but not yet dependency-closed in
Lean.

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
- 2026-08-01 -- Strengthened the formal no-go from a conditional periodic
  center to an explicit fixed-energy non-scalar model.  The two-level sign
  Hamiltonian has norm `|omega|`, returns exactly to the identity at every
  `2 pi k / omega`, and its full self-adjoint perturbation tube obeys the
  dimension-free `|t| ||H-K||` bound.  Therefore neither removal of `H=0` nor
  conditioning on nonzero energy can support a word-by-word exponential
  capture bound.
- 2026-08-01 -- Proved the dimension-free hard-power amplification law in
  `FiniteHorizonCStarPerturbationLaw.lean`: `||U^N-V^N|| <= N||U-V||`, exact
  autonomous endpoint composition, and the converse `epsilon/N` separation
  theorem.  This transfers exact endpoint hardness backward but also exposes
  the unavoidable linear resolution loss, so plateau plus subadditivity alone
  cannot establish fixed-error robust growth.
- 2026-08-01 -- Located complete external closure of O6 in Cui et al.
  (arXiv:2510.08434): a forward-only two-query randomized stabilizer/Pauli test
  distinguishes every fixed-`q` Hamiltonian ensemble from Haar at every time.
  Formalized its conserved-coordinate and inverse-dictionary-squared signal
  core in `ConservedLocalCompressionWitness.lean` and wired the module into the
  HTGeometry umbrella.  Pauli-twirl and Haar benchmark ports remain.
- 2026-08-01 -- Closed O3's completed-time transfer first on the full torus,
  then found and repaired its failure for traceless Hamiltonians.  The new
  compiled projective capstone
  `completedTime_zeroAnchoredPaddedCircuitTargets` proves an exact
  measure-preserving global/projective phase split, derives rational
  independence of physical relative frequencies from maximal projective rank,
  and transfers the explicit Choi circuit-target bound to completed time.
- 2026-08-01 -- Replaced the failed robust power route by a one-step
  autonomous concatenation theorem.  `AutonomousWordComplexityConeLaw.lean`
  proves that a `P`-hard late endpoint and an `r`-gate increment force
  `(P-r)` hardness at the earlier endpoint with only additive fixed error.
  This gives a full backward linear cone below every hard plateau endpoint;
  the first plateau hitting/cut-time bound remains the exact unresolved O4
  core.
- 2026-08-01 -- Strengthened the cone to the operator-norm unitary group of
  every unital C-star algebra and proved syndetic cone propagation: recurring
  hard endpoints generate recurring backward ramps with the same gap bound.
  No Hilbert--Schmidt normalization or `1/N` error collapse remains in this
  transfer layer.
- 2026-08-01 -- Proved `StaticChoiSyndeticComplexityLaw.lean`.  For every
  maximally projective finite spectrum and every finite circuit dictionary
  whose explicit target-volume bound is below one, every interval of one
  finite length contains a hard Choi endpoint.  This upgrades an asymptotic
  plateau fraction to infinite, uniformly recurrent hard endpoints.  The gap
  is nonquantitative; controlling it at exponential saturation scale is the
  remaining first-cut problem.
- 2026-08-01 -- Closed the spectral-subspace target objection in
  `StaticChoiFullStateProjectionLaw.lean`.  Diagonal density restriction from
  the full Choi tensor-square space is contractive, and the true evolved full
  density restricts exactly to the phase density.  The syndetic theorem now
  holds against arbitrary full circuit-target densities without dimension or
  radius loss.
- 2026-08-01 -- Closed the operational-metric objection in
  `StaticChoiTraceDistanceLaw.lean`.  For normalized pure states the full
  density Hilbert--Schmidt distance is proved exactly equal to `sqrt 2` times
  trace distance; the physical diagonal-unitary Choi vector is normalized and
  has exactly the previously used full density.  Hard Choi endpoints are now
  syndetic against normalized pure circuit targets in operational trace
  distance.
- 2026-08-01 -- Replaced the plateau-only statement by an ordered universal
  mechanism.  `denseAddOrbit_disjoint_open_targets_alternate_syndetically`
  proves that every dense real flow on every compact group alternates between
  any two disjoint nonempty open regimes, with one finite bound on every leg.
  `StaticChoiComplexityAlternationLaw.lean` instantiates the regimes as
  recurrence to the identity channel and separation from every circuit of
  bounded depth.  After every starting time there is a strictly ordered
  low--high--low cycle, and this repeats forever.
- 2026-08-01 -- Closed local-Hamiltonian ensemble transfer for the already
  formal finite Anderson family in
  `FiniteAndersonChoiComplexityAlternationLaw.lean`.  For every fixed finite
  Hermitian hopping matrix, the existing corpus proves that qualifying onsite
  potentials are dense, residual, and full Lebesgue measure; every qualifying
  Hamiltonian obeys the operational low--high--low law.  This does not yet
  formalize the separate paper-only nearest-neighbour many-body qudit result.
- 2026-08-01 -- Axiom audit of the trace identity, syndetic trace-hard law,
  ordered alternation law, and finite-Anderson specialization reports only
  `propext`, `Classical.choice`, and `Quot.sound`.  O4 remains narrower and
  harder: a quantitative direct-simulation cut time/no-shortcut theorem.  The
  qualitative infinite alternation and local-H transfer no longer depend on
  O4.
- 2026-08-01 -- Proved the ambient-seed recurrence amplifier in
  `MetricEntropyRecurrenceAmplificationLaw.lean`: if an ambient carrier needs
  more radius-`epsilon` balls than a circuit endpoint dictionary contains, one
  hard seed on one compact autonomous slice generates ordered easy--hard--easy
  epochs forever.  Ambient covering entropy sets circuit depth; recurrence
  amplifies one seed in time.  The slice dimension does not cap a hardness
  certificate imported from its ambient family.
- 2026-08-01 -- Isolated and proved the spectrum/orientation separation law.
  `PeriodicMetricEntropySeparationLaw.lean` gives exact period-one bounds:
  after every start, easy, hard, and easy phases occur in strict order with
  every leg at most one period.  `StarProjectionPeriodicComplexityLaw.lean`
  proves that `1 + (exp(2*pi*i*theta)-1)P` is a continuous unitary subgroup for
  every star projection, proves the exact idempotent exponential formula, and
  identifies it with ordinary time-independent evolution `exp(-itH)` for the
  self-adjoint Hamiltonian `H=-2*pi*P`.  Thus eigenvalues set the recurrence
  clock while eigenspace orientation sets which endpoints the clock contains;
  locality is the extra structure that can couple the two.
- 2026-08-01 -- Removed the remaining entropy premise in a concrete quantum
  model.  `FinTwoProjectorClockComplexityLaw.lean` constructs an injective real
  line of rank-one projections in `M_2(C)`, proves its nontrivial phase carrier
  infinite, and proves: for every finite gate alphabet and every requested
  circuit depth `s`, some exactly one-periodic two-level static Hamiltonian has
  a positively separated depth-`>s` endpoint in every period, bracketed by
  identity-near epochs.  Resolution and Hamiltonian may depend on `s`; the
  theorem does not give fixed-resolution many-body maximal complexity and does
  not close O4.  Axiom audit reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- 2026-08-01 -- Closed the fixed-resolution and many-body-size gaps for the
  nonlocal recurrence/complexity separation theorem.
  `DiagonalProjectorClockPackingLaw.lean` proves that the `2^D` Boolean
  diagonal projections in `M_D(C)` give half-period reflections at pairwise
  operator-norm distance exactly `2`.  Their external covering number at
  radius `1/2` is therefore at least `2^D`.  For every finite gate alphabet of
  size `g` and every depth `s` with
  `sum_(k=0)^s g^k < 2^D`, one diagonal star projection `P` yields the ordinary
  self-adjoint static Hamiltonian `H=-2*pi*P` whose evolution has exact period
  one and, after every start, a strict easy--hard--easy sequence with each leg
  at most one period; the hard endpoint is more than `1/2` in operator norm
  from every word of depth at most `s`.  Thus fixed-resolution exponential
  circuit hardness and immediate exact recurrence are rigorously compatible.
  The selected Boolean spectral projector is generally not fixed-`q` local.
  Hence this theorem proves that recurrence time alone cannot control
  complexity and isolates locality, rather than spectrum, as the remaining
  coupling mechanism.  It does not close O4's static fixed-local no-shortcut
  law.  Axiom audit of the packing, cardinal, fixed-radius recurrence, and
  circuit-hard capstones reports only `propext`, `Classical.choice`, and
  `Quot.sound`.
- 2026-08-02 -- Strengthened O6 from the earlier inverse-dictionary-squared
  compression surrogate to the physical dimension-linear scale.
  `ConservedLocalTwoQuerySignalLaw.lean` proves the exact lower bound
  `3^(-q)/M`, hence `1/(12^q n)` for a one-dimensional fixed-`q` dictionary
  and `1/(12n)^q` all-to-all. `ProductStabilizerPauliTwirlLaw.lean` proves the
  six-state single-qubit twirl, its independent product factorization, exact
  cancellation of distinct Pauli strings, and equality of the operational
  two-copy protocol correlation with that weighted coefficient signal.
  `FiniteUnitaryHaarMeasureLaw.lean` constructs normalized Haar probability
  on every finite complex unitary group and proves the invariance, column
  normalization, permutation symmetry, and explicit coordinate mixers needed
  for the remaining Haar fourth-moment benchmark. All three modules compile
  individually with `lake env lean`; no forbidden declarations occur.
  O6 now lacks only completion of the exact Haar fourth-moment identity and
  dictionary-cardinality instantiation. O4 remains the master open core:
  a maximally hard endpoint by normalized time `O(2^n/poly(n))`, which the
  already compiled autonomous cone converts into the full initial linear
  growth ramp.
