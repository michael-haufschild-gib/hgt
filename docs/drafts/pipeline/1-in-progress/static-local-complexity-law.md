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

#### Frontier reset: what would actually move O4

The fixed-order commutator, Wick, ribbon, and cavity results later in this
card are auxiliary.  They do **not** count as progress on Brown--Susskind
growth unless they imply (O4.3), uniformly in physical time after the
Hamiltonian-dependent circuit selector has been taken.  In particular,
coefficient cancellation, a planar Dyson equation, replica genus, spectral
return, operator spreading, and absence of invariant cavity modes are all
compatible with an unexpectedly short endpoint circuit.

The missing scientific knowledge is one global theorem:

> **Quenched robust word-metric injectivity.**  A typical fixed local
> Hamiltonian one-parameter subgroup has no approximate relation with the
> local-gate word ball of radius `a t/poly(n)` before exponential
> saturation, except on aggregate Hamiltonian mass bounded by (O4.3).

This target is stronger than the literal statement of
Brown--Freedman--Lin--Susskind Conjecture 2, which concerns the critical
penalty schedule and its UV/IR metric universality.  Their discussion
motivates exponentially late typical cut loci, but it does not state the
robust discrete-circuit, quenched, uniform-in-time probability estimate
(O4.3).  The paper must not cite their conjecture as if it already supplied
that equivalence.

This is a nonuniform no-fast-forwarding theorem: the competing circuit may
depend on the realized Hamiltonian.  Oracle lower bounds, fixed-target
anti-concentration, finite-order moments, design comparison, support growth,
and ordinary NLTS do not establish it.  A genuine advance must construct an
endpoint-dependent global word-metric calibration or prove an aggregate
transversality theorem for the whole circuit tube.  Until one of those two
objects is obtained with a bound strong enough to imply (O4.3), the central
frontier has not moved.

This is the proposed physical reinterpretation: autonomous time can generate
**computational inaccessibility without statistical randomness**.  The orbit
remains a low-parameter, efficiently non-Haar family, while every center that
captures appreciable mass moves beyond the circuit budget available at that
time.  Kotowski--Oszmaniec--Horodecki obtain an immediate extremal jump for
GUE and Haar-conjugated diagonal generators using load-bearing unitary
invariance; no audited result proves this local ballistic law.

#### Hard-frontier audit: deterministic complexity production

The preceding formulation still permits misleading auxiliary progress unless
one isolates what the static problem lacks.  If

\[
 H(J)=\sum_{a=1}^{m}J_aP_a,\qquad
 F_t(J)=e^{-itH(J)}\Phi_0 ,
\]

then Duhamel's inequality gives

\[
 d(F_t(J),F_t(J'))\leq |t|\,L_H\|J-J'\|.
 \tag{O4.3a}
\]

Consequently the fixed-resolution metric entropy of the entire quenched
endpoint ensemble on a bounded coefficient set is at most

\[
 \log N_\varepsilon(F_t(K))
 \leq
 m\log\!\left(1+{C|t|\over\varepsilon}\right).
 \tag{O4.3b}
\]

Thus a static `m`-parameter law supplies only `O(m log t)` newly resolvable
coefficient bits by time `t`.  A lower bound of order `t` cannot be an
information-theoretic consequence of fresh disorder, ensemble dimension,
Haar volume, or parameter anti-concentration.  It must prove that a
short-description autonomous law **deterministically expands** those few
resolved bits into an endpoint having word complexity of order `t`.  This is
the quantum-circuit analogue of proving a pseudorandom generator hard against
nonuniform distinguishers; it is precisely the step absent from current
static-Hamiltonian methods.

The approximate-centralizer reformulation does not reduce this difficulty.
Every `epsilon`-approximant `V` to `e^{-itH}` satisfies

\[
 \|[H,V]\|\leq2\epsilon\|H\|,
 \tag{O4.3c}
\]

but the exact commutant of a simple-spectrum `H` already contains every
spectral function `f(H)`, including `e^{-itH}` itself.  Therefore a
"low-circuit approximate-centralizer rigidity" theorem strong enough to
exclude `V` must lower-bound the circuit complexity of nontrivial spectral
functions of `H`; that is O4 again, not a bridge to it.  The identity also
shows that small commutator alone contains no time information.

Likewise, word-height Diophantine extremality can at most explain the
completed plateau.  At fixed resolution it compares the word ball with a
low-dimensional analytic endpoint manifold and can force generic avoidance
near ambient capacity.  It cannot produce the pre-saturation slope: direct
Hamiltonian simulation places `F_t(K)` inside a word tube of radius
`O(t poly(n))`, while the constants measuring finite-time nondegeneracy of
that manifold necessarily collapse at exactly the rate whose lower bound O4
asks for.  Any claimed dynamic consequence that leaves those constants
uncontrolled is circular.

The 2025 spacetime-complexity construction of Du--Liu--Ma is an important
boundary case, not a solution.  It writes a depth-`T` random circuit into
`Theta(T)` spatial columns of a commuting two-dimensional Hamiltonian and
obtains a hard projected endpoint after constant physical time.  The fresh
random description and circuit volume are spatial.  It proves that static
local evolution can *read* extensive complexity already stored across the
Hamiltonian, but not that one fixed finite system produces new word
complexity linearly for exponentially long time.

Hence the actual frontier is narrower and harder than "static chaos":

> **Static seed-expansion theorem.**  Prove that exponentiation of a
> polynomial-description, fixed-locality Hamiltonian is an unconditional
> robust word-metric expander along its own one-parameter orbit, despite zero
> fresh disorder, a Hamiltonian-dependent circuit selector, and exact
> quasiperiodicity.

For a concrete Gaussian ensemble this theorem must be stated as (O4.3).
Spectral ramps, maximal rational rank, designs of fixed order, operator
spreading, NLTS, local distinguishability, commutant rigidity without a
quantitative word bound, and space-for-time encodings do not prove it.  Any
further route is rejected unless its headline estimate already contains the
Hamiltonian-dependent circuit infimum at fixed error.

#### Radial shortcut-codimension equivalence

There is an exact representation of the remaining theorem in which physical
time is no longer a separate variable.  Assume the Hamiltonian map is linear,
write `H(x)=sum_a x_a P_a`, and let `Lambda` be the homogeneous simulation
cost.  Define the fixed radial shortcut locus

\[
 \mathfrak S_{\varepsilon,a}
 =
 \left\{x\in\mathbb R^m:
 C_\varepsilon(e^{-iH(x)}\Phi_0)
 \leq {a\Lambda(H(x))\over\operatorname{poly}(n)}
 \right\}.
 \tag{O4.3d}
\]

For every coefficient direction `J` and every `t>0`, linearity and
homogeneity give the exact identities

\[
 e^{-itH(J)}=e^{-iH(tJ)},\qquad
 t\Lambda(H(J))=\Lambda(H(tJ)).
 \tag{O4.3e}
\]

Hence, on a fixed energy shell with normalized angular measure `sigma`,
(O4.3) is exactly the spherical estimate

\[
 \sigma\{\theta:t\theta\in\mathfrak S_{\varepsilon,a}\}
 \leq C t^{-\kappa},
 \qquad \kappa=cm ,
 \tag{O4.3f}
\]

through the pre-saturation radial range.  The Brown--Susskind cut problem is
therefore a statement that the robust low-relative-word locus loses a fixed
fraction of the local-Hamiltonian parameter dimension at infinity.

For the unconditioned centered Gaussian ensemble the equivalence is a volume
theorem.  Let `gamma_m` be standard Gaussian measure and let `B` be any
measurable subset of `R^m`.  For `0<kappa<m`, the following two estimates are
equivalent up to constants depending only on `m,kappa`:

\[
 \gamma_m\{J:tJ\in B\}\leq Kt^{-\kappa}
 \quad(t\geq1),                                        \tag{O4.3g}
\]

and

\[
 \operatorname{vol}(B\cap B_R)
 \leq K'R^{m-\kappa}
 \quad(R\geq1).                                        \tag{O4.3h}
\]

Indeed, `(O4.3g)` at `t=R` and the lower bound

\[
 (2\pi R^2)^{-m/2}e^{-1/2}
\]

for the `N(0,R^2I_m)` density on `B_R` prove `(O4.3h)`.  Conversely, split
`B` into `B_t` and the dyadic annuli
`B_{2^{j+1}t}\setminus B_{2^jt}`.  On the `j`th annulus the scaled Gaussian
density is at most

\[
 (2\pi t^2)^{-m/2}e^{-2^{2j-1}},
\]

while `(O4.3h)` bounds its volume by
`K'(2^{j+1}t)^{m-\kappa}`.  The resulting series converges and gives
`(O4.3g)`.

Applied to `B=mathfrak S_(epsilon,a)`, this proves:

> **Radial shortcut-codimension theorem.**  Aggregate quenched linear
> complexity growth with failure `t^(-kappa)` is equivalent to polynomial
> volume growth of the complete Hamiltonian-dependent shortcut locus with
> dimension at most `m-kappa`.

This is stronger than saying each fixed circuit has a transverse preimage.
The union over all words whose permitted length grows radially is already
inside `mathfrak S_(epsilon,a)`.  Thus the exact remaining mathematical task
is to prove positive codimension for that single global set.  Word-by-word
transversality, even if sharp, does not imply `(O4.3h)`.

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

#### Connected Pauli-walk reduction and its exact surviving target

The July 2026 Gaussian-process lower bound of Al-Ghattas--Gamarnik does not
extend to O4 by increasing constants.  Its ancilla-uniform circuit entropy is
controlled by backward supports of size `2^depth`; after depth `Theta(log n)`
those supports fill the system and the variance reduction disappears.  It
therefore proves a genuine shallow-depth spin-glass obstruction, not an
exponential gate-count obstruction.

A direct Wick transfer from Brownian to static disorder also fails.  For a
fixed weight-`w` Pauli word `Q`, the exact number of weight-`q` Pauli words
that anticommute with it is

\[
 N_{\rm ac}(w,q)=
 \sum_{j=0}^{\min\{w,q\}}
 {w\choose j}{n-w\choose q-j}3^{q-j}
 {3^j-(-1)^j\over2}.                                 \tag{O4.4}
\]

Indeed `j` is the support-overlap size; on the overlap the odd-parity choices
among the three nonidentity Pauli letters number
`(3^j-(-1)^j)/2`.  In particular, for two independent weight-`q` words,

\[
 \Pr(PQ=-QP)
 ={2q^2\over3n}+O_q(n^{-2}).                          \tag{O4.5}
\]

Thus two random fixed-locality terms commute with probability `1-O(1/n)`.
The non-time-local Wick pairings of one quenched Hamiltonian are not small
perturbations of Brownian pairings, so ordinary Gaussian decoupling cannot
transfer the random-circuit theorem.

The transported parent removes precisely this disconnected obstruction.
Label Pauli words by the binary symplectic space and write `omega` for its
commutation form.  For Pauli labels `p_1,...,p_r,z`,

\[
 \operatorname{ad}_{P_{p_r}}\cdots
 \operatorname{ad}_{P_{p_1}}(P_z)\ne0
 \quad\Longleftrightarrow\quad
 \omega\!\left(p_j,z+\sum_{\ell<j}p_\ell\right)=1
 \quad(1\le j\le r).                                  \tag{O4.6}
\]

When nonzero, the result is a phase times `2^r P_{z+\sum_jp_j}`.  Hence every
coefficient of `ad_H^r(K_0)` is exactly a Gaussian-chaos sum over
parity-admissible walks on the exponential Pauli commutator graph.  Commuting
disconnected words vanish before any probabilistic estimate is taken.

There is an exact source-realization theorem behind this walk language.  For
`S` in the binary symplectic label space, let `cl_omega(S)` be the least set
containing `S` and satisfying

\[
 p,q\in\operatorname{cl}_\omega(S),\quad\omega(p,q)=1
 \quad\Longrightarrow\quad
 p+q\in\operatorname{cl}_\omega(S).
\]

Then

\[
 \operatorname{Lie}_{\mathbb R}\langle iP_p:p\in S\rangle
 =
 \operatorname{span}_{\mathbb R}
 \{iP_z:z\in\operatorname{cl}_\omega(S)\}.             \tag{O4.6a}
\]

The right side contains the generators and is Lie closed because a Pauli
commutator is zero when its labels are symplectically orthogonal and is a
nonzero multiple of `iP_(p+q)` otherwise.  Conversely every closure step is
realized by that nonzero commutator.  Linear independence of distinct Pauli
words proves equality.

For the complete one- and two-local source, this closure saturates rapidly:
every nonzero weight-`w` label belongs after at most `max(0,w-2)` extension
steps.  Inductively, for `w>=3`, choose a weight-`w-1` label `x` that agrees
with the target `z` on `w-2` old sites, has a different nonzero letter on
one old site, and omits the new site.  Then `y=x+z` has weight two, and the
two different nonzero letters on the shared old site give
`omega(x,y)=1`; hence `z=x+y` is the next closure step.  Thus the full Pauli
Lie algebra is already reached at commutator depth `O(n)`.

This is the valid transfer from the source-horizon Riemann-divisor work:
faithful source realization survives, but its Boolean source lattice is
replaced by a symplectic closure lattice.  Hypertranscendence and cofinal
observer collapse do not transfer.  A finite-dimensional static evolution
already satisfies a finite constant-coefficient matrix ODE, and a short
preparation circuit is neither a label-blind observer nor an inverse
spectral decoder.  The quantitative problem is therefore the weighted
injectivity radius inside (O4.6a), not differential independence.

Spectral recurrence is the abelianized shadow of this source closure.
Permanent locality tests retain the original generator labels.  The missing
growth theorem must show that robust low-word relations do not appear in the
full noncommutative group after its Lie closure has already saturated.
Closure depth itself cannot be the complexity invariant.  The required
invariant is the robust group word metric/injectivity radius, or an
equivalent circuit-tube energy.  This is a structural relation among O4,
O5, and O6, not a proof of O4.

There is a sharp counting limit on the source-horizon analogy.  Suppose one
uses only injectivity of a one-parameter orbit, an inverse-conditioning
bound, or the existence of `N_epsilon(T)` distinguishable time cells up to
time `T`.  A finite gate alphabet with `M` choices has `M^(s+1)` words of
length at most `s`.  Such source distinguishability can therefore force at
most

\[
 s\geq\log_M N_\varepsilon(T)=O(\log T),               \tag{O4.6b}
\]

not ballistic `Omega(T/poly(n))` complexity.  A proof of O4 must use the
metric geometry of noncommutative relations inside the closure, not only
faithful recovery of the time/source coordinate.  This rules out importing
the Riemann source's cofinal conditioning theorem as a disguised
no-fast-forwarding proof.

This exposes a narrower surviving theorem than an unspecified “dynamical
NLTS” assumption:

> **Quenched connected-walk escape target.**  Prove an aggregate tube bound
> for `exp(it ad_H)K_0` against the set of conjugates of `K_0` by circuits of
> fewer than `a t/poly(n)` gates, using the parity-admissible walk expansion,
> uniformly until `t=Theta(2^n/poly(n))`.

Unweighted graph expansion or Pauli-support growth is insufficient: a
linear-depth circuit can already populate exponentially many Pauli
coefficients.  The load-bearing estimate must control the joint amplitudes
of the connected Gaussian-chaos walk against the entire low-circuit tube.
Proving only vertex delocalization, Krylov dimension, or a spectral ramp does
not close O4.

#### Exact support-adaptive memory law

The first non-Brownian connected correction can be evaluated exactly.  This
is useful both as a positive theorem and as a falsifier for indiscriminate
Brownian comparison.

Let

\[
 H=\sum_{p\in S}\sqrt{v_p}\,g_pP_p,\qquad
 g_p\mathrel{\mathop\sim}^{\rm iid}N(0,1),
\]

where `S` is any finite set of Pauli labels and `v_p >= 0`.  For a Pauli label
`z`, put

\[
 \lambda_z=\sum_{\omega(p,z)=1}v_p,\qquad
 \beta_p=\sum_{\omega(r,p)=1}v_r,\qquad
 \gamma_{z,p}=\sum_{\substack{\omega(r,p)=1\\\omega(r,z)=1}}v_r .
\]

Then the return component of the second and fourth adjoint moments is

\[
 \mathbb E\,\operatorname{ad}_H^2(P_z)=4\lambda_zP_z,                 \tag{O4.7}
\]

\[
 \mathbb E\,\operatorname{ad}_H^4(P_z)
 =\left[
 48\lambda_z^2+
 16\sum_{\omega(p,z)=1}v_p(\beta_p-3\gamma_{z,p})
 \right]P_z .                                                       \tag{O4.8}
\]

In particular,

\[
 \left\|\mathbb E\,\operatorname{ad}_H^4(P_z)
             -48\lambda_z^2P_z\right\|
 \leq 32\lambda_z\max_{\omega(p,z)=1}\beta_p .                       \tag{O4.9}
\]

**Proof.**  Write `A_p=ad_(P_p)`.  If `p` anticommutes with the current
Pauli label then `A_p` changes that label by `p`, with coefficient of modulus
two; otherwise it kills the word.  Hence
`A_p^2(P_z)=4 P_z` when `omega(p,z)=1`, and it is zero otherwise, proving
(O4.7).

For the fourth moment Wick's rule gives the three words

\[
 A_p^2A_r^2,\qquad A_pA_rA_pA_r,\qquad A_pA_r^2A_p.
\]

Fix `omega(p,z)=1`, and write
`x=omega(r,z)`, `b=omega(r,p)`.  Their respective coefficients, divided by
sixteen, are

\[
 x,\qquad x(1-b),\qquad x\mathbin{\mathsf{xor}}b.
\]

For `b=0` their sum is `3x`; for `b=1` it is one.  Summing first over `r`
therefore gives

\[
 16\sum_{\omega(p,z)=1}v_p
 \left[3(\lambda_z-\gamma_{z,p})+\beta_p\right],
\]

which is (O4.8).  Since `0 <= gamma_(z,p) <= beta_p`,
`|beta_p-3 gamma_(z,p)| <= 2 beta_p`, proving (O4.9).  No asymptotic,
independence approximation, or spectral hypothesis enters the argument.

For the uniform weight-`q` ensemble, (O4.4) makes the bound explicit:

\[
 {\max_p\beta_p\over\sum_rv_r}
 ={2q^2\over3n}+O_q(n^{-2}).
\]

If `|z|/n -> alpha` with `0 < alpha <= 1`, then

\[
 {\lambda_z\over\sum_rv_r}
 ={1-(1-4\alpha/3)^q\over2}+O_q(n^{-1}),                             \tag{O4.10}
\]

so the relative fourth-moment defect in (O4.9) is `O_(q,alpha)(1/n)`.
For a one-site seed, by contrast,
`lambda_z/sum_r v_r=2q/(3n)` and `beta_p/lambda_z -> q`; the same defect
need not vanish.  Quenched static evolution therefore does not begin as a
Brownian process.  Its first possible comparison window opens only after
operator support becomes extensive.

The crude higher-moment comparison has a `k^2/n` collision parameter: in a
Wick word with `k` paired local labels, pairwise commutation reduces the word
to scalar-Gaussian pairing, while (O4.5) bounds the chance of any
anticommuting label pair.  That estimate is not the correct renormalized
barrier, however.  Paired commutator words obey a stronger exact parity law.

Number the paired labels by `a=1,...,k`, and let their two locations in the
application-ordered word be `l_a<r_a`.  Two blocks cross when their endpoints
interlace.  Immediately before a location `j`, let `O_j` be the blocks that
have occurred exactly once.  The current Pauli label is

\[
 z+\sum_{b\in O_j}p_b.
\]

Thus the paired word is nonzero exactly when, at every occurrence of block
`a`,

\[
 \omega\left(p_a,z+\sum_{b\in O_j}p_b\right)=1.                       \tag{O4.11}
\]

Comparing the equations at `l_a` and `r_a` gives the following equivalent
criterion:

\[
 \begin{split}
 \omega(p_a,z)
  +\sum_{b:\ l_b<l_a<r_b}\omega(p_a,p_b)&=1,\\
 \sum_{b:\ a\ {\rm crosses}\ b}\omega(p_a,p_b)&=0
 \qquad\text{for every }a.                                          \tag{O4.12}
 \end{split}
\]

The equivalence is exact.  A block `b` belongs to the symmetric difference
of the open sets at the two endpoints of `a` precisely when the two chords
cross; XOR of the two endpoint equations is therefore the second line of
(O4.12), while the first line is the equation at `l_a`.

Consequently, place an edge between crossing chords `a,b` exactly when
`P_(p_a)` and `P_(p_b)` anticommute.  The second line of (O4.12) says that
this anticommutation subgraph is Eulerian: every vertex has even degree.
Every nonempty crossing-memory component must therefore contain a cycle.  In
particular, one isolated crossing anticommutation kills the Wick word rather
than contributing an error.  Nested and containing chords can change the
first-line seed parity but create no compatibility defect; they belong in a
dressed self-energy, not in the crossing-memory remainder.

The surviving coefficient has an exact topological sign.  At every admissible
step,

\[
 \operatorname{ad}_{P_p}(P_y)=2P_pP_y.
\]

After all `2k` steps, reorder equal Pauli labels until each pair is adjacent.
Two paired labels require one interchange exactly when their chords cross,
and that interchange contributes `(-1)^(omega(p_a,p_b))`.  The equal pairs
then square to the identity.  Hence every word satisfying (O4.12) equals

\[
 4^k(-1)^{\,\sum_{a<b,\ a\ {\rm crosses}\ b}
                    \omega(p_a,p_b)}P_z .                            \tag{O4.12a}
\]

The crossing-memory remainder is therefore a signed Eulerian cycle gas, not
a positive collision gas.  Its first connected polymer is a triangle and
has negative sign.

For three independent uniform weight-`q` labels, the triangle probability
has the sharp fixed-`q` leading term

\[
 \mathbb P\bigl(
 \omega(p_1,p_2)=\omega(p_2,p_3)=\omega(p_3,p_1)=1
 \bigr)
 ={2q^3\over9n^2}+O_q(n^{-3}).                                      \tag{O4.12b}
\]

To see the leading term, fix `p_1`.  With probability
`1-O_q(n^(-1))` conditional on anticommutation, `p_2` meets it at one
site.  Choose that site in `q` ways and the different letter in two ways.
For `p_3` to anticommute with both at order `n^(-1)` rather than
`n^(-2)`, it must use the same site and the unique third Pauli letter.
The remaining supports are pairwise disjoint.  The exact leading count,
conditional on `p_1`, is

\[
 2q{n-q\choose q-1}{n-2q+1\choose q-1}3^{2q-2}
\]

out of `({n\choose q}3^q)^2`; every other support-incidence pattern has at
least three independent coincidences and contributes `O_q(n^(-3))`.

There is also an exact all-orders site factorization, so the cycle gas need
not be treated as an independent-edge surrogate.  Identify the one-site
Pauli alphabet with `A=F_2^2`, write its symplectic form as
`<.,.>`, and let zero denote the identity letter.  Fix a pairing `pi` of
`1,...,2k`; write `b(j)` for the block at location `j` and
`cross_pi(a,c)` for its chord-crossing indicator.  For
`eta in F_2^(2k)` and a one-site seed letter `zeta`, define the polynomial

\[
\begin{aligned}
 \mathscr F_{\pi,\zeta,\eta}(x_1,\ldots,x_k)
 =\sum_{a_1,\ldots,a_k\in\mathbb F_2^2}
 &\prod_{r=1}^k x_r^{\mathbf1_{a_r\ne0}}\\
 {}\times(-1)^{
 &\sum_{r<c}\operatorname{cross}_\pi(r,c)\langle a_r,a_c\rangle}\\
 {}\times(-1)^{
 &\sum_{j=1}^{2k}\eta_j
 \left\langle a_{b(j)},
 \zeta+\sum_{\ell<j}a_{b(\ell)}\right\rangle}.
                                                                    \tag{O4.12c}
\end{aligned}
\]

Let `N_q=3^q {n choose q}` and sample the `k` block labels independently
and uniformly from weight-`q` Pauli words.  Define the normalized signed
survival weight (with the common amplitude `4^k` removed) by

\[
 \mathcal W_\pi(z)=
 \mathbb E\!\left[
 (-1)^{\sum_{a<c}\operatorname{cross}_\pi(a,c)\omega(p_a,p_c)}
 \mathbf1_{\text{\rm(O4.11) holds}}
 \right].
\]

Then

\[
\boxed{
 \mathcal W_\pi(z)
 ={2^{-2k}\over N_q^k}
 \sum_{\eta\in\mathbb F_2^{2k}}(-1)^{\sum_j\eta_j}
 [x_1^q\cdots x_k^q]\,
 \prod_{i=1}^n
 \mathscr F_{\pi,z_i,\eta}(x_1,\ldots,x_k).
 }                                                                  \tag{O4.12d}
\]

**Proof.**  For occurrence `j`, let `c_j` be the bit on the left of
(O4.11).  The admissibility indicator has the Walsh expansion

\[
 \prod_{j=1}^{2k}\mathbf1_{c_j=1}
 =2^{-2k}\sum_{\eta\in\mathbb F_2^{2k}}
   (-1)^{\sum_j\eta_j+\sum_j\eta_jc_j}.
\]

Both `c_j` and the crossing-sign exponent in (O4.12a) are sums of their
one-site symplectic contributions.  Their characters therefore factor over
the `n` sites.  The monomial records whether block `r` is nonidentity at
that site; extracting `x_r^q` enforces weight exactly `q` for every block.
Division by `N_q^k` normalizes the label choices.  This proves (O4.12d).

For a seed of weight `w`, simultaneous one-site Clifford symmetry identifies
all nonzero `z_i`; the product in (O4.12d) consequently has only two local
types, `n-w` zero-seed factors and `w` nonzero-seed factors.  Formula
(O4.12d) is a finite coefficient-extraction problem for every `n,q,k` and
every chord pairing.  It includes repeated labels, all site-sharing
correlations, Eulerian cancellation, and the fixed-weight constraint
exactly.  No Brownian, independent-edge, or large-`n` approximation is
present.

The target ensemble with all weights `1,...,q` requires no new diagram
argument.  If every weight-`r` label has variance `v_r`, replace each
`[x_a^q]` in (O4.12d) by
`\sum_(r=1)^q v_r[x_a^r]` and replace `N_q` by
`\sum_(r=1)^q v_r3^r{n\choose r}`.  Wick block weights are then reproduced
exactly.

Repeated block labels do not need a separate large-order estimate.  For `m`
equal-variance Pauli coefficients write the standard Gaussian vector as

\[
 J=R\Theta,\qquad R=\|J\|_2,\qquad
 \Theta\ \text{uniform on }S^{m-1},
\]

with `R` and `Theta` independent.  Since an `r`-fold nested commutator is
homogeneous of degree `r`,

\[
 \mathbb E_J\,\operatorname{ad}_{H(J)}^r(K_0)
 =
 \mathbb E R^r\,
 \mathbb E_\Theta\operatorname{ad}_{H(\Theta)}^r(K_0).               \tag{O4.12e}
\]

For even order,

\[
 \mathbb E R^{2k}
 =2^k{\Gamma(k+m/2)\over\Gamma(m/2)}
 =m(m+2)\cdots(m+2k-2).                                             \tag{O4.12f}
\]

Thus the exact energy-shell/angular moment is obtained from the Wick sum by
dividing by (O4.12f).  This removes the high-order radial repetitions
without assuming distinct Pauli labels.  Unequal variances give the same
statement after whitening the coefficient ellipsoid.  The remaining
large-order problem is the signed angular site-transfer partition function,
which is the physically relevant fixed-energy-shell object.

Radial phase mixing is not an O4 shortcut.  The theorem normalizes elapsed
time by the interaction rate, which scales with `R`; that normalization
cancels the radial variable.  Any `t^(-m)` dephasing obtained by averaging
over `R` would prove a scale-mixture statement, not the fixed-energy
autonomous law.

The response-Liouvillian corpus gives an exact bridge from these commutator
diagrams to late spectral return.  In an energy eigenbasis of `H`, define for
a Hermitian Pauli observable `Q`

\[
 I_{ab}={1\over D}|Q_{ab}|^2,\qquad
 \mu_{H,Q}=\sum_{a,b}I_{ab}\,\delta_{E_a-E_b}.
\]

Then `mu_(H,Q)` is a finite nonnegative symmetric measure and, for every
`k>=0`,

\[
\begin{aligned}
 {1\over D}\operatorname{Tr}
 \bigl(Q^\dagger\operatorname{ad}_H^{2k}(Q)\bigr)
 &=\int x^{2k}\,d\mu_{H,Q}(x)\\
 &={1\over D}\|\operatorname{ad}_H^k(Q)\|_{\rm HS}^2,                \tag{O4.12g}\\
 {1\over D}\operatorname{Tr}
 \bigl(Q^\dagger e^{itH}Qe^{-itH}\bigr)
 &=\int e^{itx}\,d\mu_{H,Q}(x).                                    \tag{O4.12h}
\end{aligned}
\]

The first identity follows entrywise from
`(ad_H Q)_(a,b)=(E_a-E_b)Q_(a,b)`; self-adjointness of `ad_H` gives the
norm square.  The second is the same diagonal action exponentiated.
`FiniteResponseLiouvillian.lean` already certifies the abstract finite
transition-measure moment identity and odd-moment cancellation; the
basis-change specialization (O4.12g)--(O4.12h) is the physical dictionary.

Therefore the site partition formula (O4.12d) computes exact ensemble
moments of a positive spectral return measure, not merely formal Taylor
coefficients.  This genuinely joins connected operator growth to recurrence.
It does not yet join either one to circuit complexity: one transition
measure contains two-point response data, while a circuit-tube event depends
on a complete replicated endpoint tensor.  The next extension must construct
and control that replica Liouvillian hierarchy.

That hierarchy has an exact aggregate reduction.  Let
`rho_t=|Phi_H(t)><Phi_H(t)|`, let `C_s` be the full size-`s` circuit class,
and put `sigma_C=C rho_0 C^dagger`.  For pure states,

\[
 F_s(t)=\sup_{C\in\mathcal C_s}\operatorname{Tr}(\rho_t\sigma_C)
       =\sup_{C\in\mathcal C_s}|\langle\Phi_H(t),C\Phi_0\rangle|^2.
\]

If trace distance from `rho_t` to some `sigma_C` is at most `epsilon`, then
`F_s(t)>=1-epsilon^2`.  Hence, for every integer `r>=1`,

\[
 \mathbb P\{C_\varepsilon(\Phi_H(t))\leq s\}
 \leq
 (1-\varepsilon^2)^{-r}\,
 \mathbb E\,F_s(t)^r,                                               \tag{O4.12i}
\]

and the moment is exactly

\[
 F_s(t)^r
 =\sup_{C\in\mathcal C_s}
 \operatorname{Tr}\!\left(
   \rho_t^{\otimes r}\sigma_C^{\otimes r}\right).                   \tag{O4.12j}
\]

No circuitwise union has been introduced: the same circuit is repeated on
all replicas and the supremum remains inside the ensemble expectation.

The replicated density evolves under the collective static Liouvillian

\[
 \mathcal L_H^{(r)}
 =\sum_{\ell=1}^r
  1^{\otimes(\ell-1)}\otimes\operatorname{ad}_H
  \otimes1^{\otimes(r-\ell)},\qquad
 \rho_t^{\otimes r}=e^{-it\mathcal L_H^{(r)}}\rho_0^{\otimes r}.     \tag{O4.12k}
\]

In the replicated energy basis its eigenvalues are the sums of gaps

\[
 \sum_{\ell=1}^r(E_{a_\ell}-E_{b_\ell}).                            \tag{O4.12l}
\]

Thus (O4.12j) is a variational matrix coefficient of a finite
self-adjoint response Liouvillian, and every one of its polynomial moments
has a positive transition-measure realization.  The generic
`FiniteResponseLiouvillian` theorem already applies after taking the
multi-index energy
`E^(r)(a_1,\ldots,a_r)=\sum_\ell E_(a_\ell)`.

The site factorization also persists exactly.  Expanding
`(L_H^(r))^k` adds a replica-leg label to every commutator occurrence.
Its commutation and endpoint constraints are still sums of one-site
symplectic bits.  Walsh expansion and the same coefficient extraction as
(O4.12d) therefore factor every replicated matrix coefficient over the
physical sites; the circuit supplies only the replicated boundary tensor
`sigma_C^(tensor r)`.

The remaining O4 estimate is now precise:

\[
 \mathbb E\sup_{C\in\mathcal C_s}
 \operatorname{Tr}\!\left(
 e^{-it\mathcal L_H^{(r)}}\rho_0^{\otimes r}
 \,\sigma_C^{\otimes r}\right)
 \leq
 (1-\varepsilon^2)^r
 \left({A tm\over\varepsilon}\right)^{-cm},                         \tag{O4.12m}
\]

for a replica order and gate budget chosen in the theorem.  Proving
(O4.12m) by a signed angular site-transfer bound would imply (O4.3)
directly and would not pay `M^s` circuit words one at a time.

The circuit supremum itself has an exact recursive form.  Pad shorter words
with the identity and define the replicated circuit body

\[
 \mathfrak K_{s,r}
 =\operatorname{conv}\{
   (C\rho_0C^\dagger)^{\otimes r}:|C|=s\}.
\]

For a Hermitian replicated operator `X`, let

\[
 h_{s,r}(X)=\sup_{Y\in\mathfrak K_{s,r}}\operatorname{Tr}(XY).
\]

If `G_n` is the finite set of allowed one-step local gates including
placements and the identity, then

\[
\begin{aligned}
 h_{0,r}(X)&=\operatorname{Tr}(X\rho_0^{\otimes r}),\\
 h_{s+1,r}(X)
 &=\max_{G\in\mathcal G_n}
   h_{s,r}\!\left((G^\dagger)^{\otimes r}
                   XG^{\otimes r}\right),                           \tag{O4.12n}\\
 F_s(t)^r&=
 h_{s,r}\!\left(e^{-it\mathcal L_H^{(r)}}
                     \rho_0^{\otimes r}\right).                     \tag{O4.12o}
\end{aligned}
\]

Equation (O4.12n) follows by removing the last gate of the word; convexifying
does not change a support function.  It is a Bellman recursion, not a union
bound.  Thus the no-shortcut theorem compares two semigroups:
continuous evolution by the collective static Liouvillian and discrete
optimal control by one local gate per Bellman step.

In the site-factorized replica expansion, one Bellman step inserts one
two-site boundary tensor on all `r` replicas.  This suggests the precise
gate-sensitive estimate that return moments lacked.  Construct a replicated
transfer norm `||.||_(r,*)` and constants `gamma,kappa>0` for which the
signed angular bulk transfer through normalized time `t` gains
`exp(-gamma r Lambda t/poly(n))`, while every local Bellman insertion costs
at most `exp(kappa r)`.  Iteration of (O4.12n) would give

\[
 \mathbb E F_s(t)^r
 \leq
 \exp\!\left(
   \kappa r s-
   {\gamma r\Lambda(H)t\over\operatorname{poly}(n)}
 \right)
 +\text{exceptional angular mass}.                                 \tag{O4.12p}
\]

With the exceptional mass bounded in the optimal form (O4.3), (O4.12p)
would prove ballistic growth for `s<a Lambda(H)t/poly(n)`.  The open
mathematical problem is now a local transfer-norm inequality compatible with
the signed Eulerian site action and the Bellman gate action.

#### Pauli cut rank: an exact gate-sensitive bulk contraction

The required transfer norm can now be constructed for each paired angular
word.  The invariant is neither support size nor the rank of the whole
crossing graph.  It is the sum, over physical sites, of binary cut ranks of
the crossing graph seen by the Pauli letters active at that site.

First consider a bipartite graph with vertex classes `L,R`, `|L|=l`,
`|R|=r`, and binary adjacency matrix `A`.  Put
`rho=rank_(F_2)(A)`.  For nonzero one-qubit Pauli labels
`x_u,y_v in F_2^2\setminus{0}`, define the normalized signed transfer

\[
 (T_{A,\alpha,\beta}f)(x)
 =3^{-r}\sum_y
 (-1)^{
   \sum_{u,v}A_{uv}\omega(x_u,y_v)+\alpha(x)+\beta(y)}
 f(y),
\]

where `alpha,beta` are arbitrary binary-valued functions.  On the uniform
`L^2` spaces of the `3^r` and `3^l` nonzero-letter assignments,

\[
 \boxed{\quad
 \|T_{A,\alpha,\beta}\|_{2\to2}
 \le {2^{\,l+r-\rho}\over 3^{(l+r)/2}} .
 \quad}                                                            \tag{O4.12q}
\]

This estimate is unconditional and uniform in every seed or boundary
character.  To prove it, first allow zero Pauli labels.  The resulting
`4^l` by `4^r` character matrix has bilinear form
`A\otimes J`, where `J` is the nonsingular one-qubit symplectic matrix.
Its binary rank is `2rho`.  Character orthogonality gives unnormalized
operator norm exactly `2^(l+r-rho)`.  Restricting rows and columns to
nonzero labels cannot increase Euclidean operator norm, and conversion to
uniform `L^2` divides by `3^((l+r)/2)`.  The functions `alpha,beta` only
multiply rows and columns by signs.  This proves (O4.12q).

For a fixed support assignment of a paired word, apply (O4.12q) at every
physical site.  If `d_i` chord labels are active at site `i`, and `rho_i`
is the cut rank of their induced crossing matrix, put

\[
 Q=\sum_i d_i,\qquad R=\sum_i\rho_i .
\]

The site-factorized angular transfer therefore obeys

\[
 \|T_{\rm angular}\|_{2\to2}
 \le {2^{Q-R}\over3^{Q/2}}
 =2^{\,(\log_2(2/\sqrt3))Q-R}.                                    \tag{O4.12r}
\]

Here this is the transfer in the selected chord variables, uniformly after
conditioning on every unselected chord label.  Edges to conditioned labels
and the seed contribute only linear forms.  Consequently the same bound
controls the full scalar coefficient of every fixed Pauli boundary branch
after averaging the conditioned labels; it is not a claim that an arbitrary
spectator-dependent boundary function has this norm.

This is the first explicit norm with the required signed bulk contraction.
It also identifies its sharp threshold:

\[
 {R\over Q}>
 \theta_*:=\log_2(2/\sqrt3)=0.207518\ldots .                        \tag{O4.12s}
\]

The threshold is genuinely below the rank density produced by a random
paired word.  Here is an exact proof.  Draw a uniform pairing of `2k`
cyclically ordered commutator positions and split the positions into two
semicircles of size `k`.  Let `b` be the number of chords with one endpoint
in each semicircle.  Order those bridge chords by their first endpoint and
put the first `l=floor(b/2)` in `L` and the remaining `r=ceil(b/2)` in `R`.
Read the `L/R` word in the order of the second endpoints.  The bridge
crossing matrix, after ordering rows and columns by the second endpoints, is
a Ferrers matrix: its `(u,v)` entry is one exactly when the `L` endpoint
precedes the `R` endpoint.  Consequently its binary rank is exactly the
number of `L`-to-`R` transitions in that word.

Now give every bridge chord an independent uniform weight-`q` support.
At site `i`, delete the chords not containing `i` from the second-endpoint
word.  The rank `rho_i` of the resulting Ferrers matrix is again exactly the
number of `L`-to-`R` transitions in the surviving word.  With
`p=q/n`, conditional on `b`,

\[
 \mathbb E\rho_i
 ={lr\over b(b-1)}
   \left(bp-1+(1-p)^b\right).                                     \tag{O4.12t}
\]

Indeed a pair of positions becomes consecutive in the retained word with
total expected count
`E[(N_i-1)_+]=bp-1+(1-p)^b`, and an ordered pair of distinct positions has
types `L,R` with probability `lr/(b(b-1))`.  Since every bridge support has
exactly `q` sites,

\[
 Q=qb,\qquad
 \mathbb ER
 =n{lr\over b(b-1)}
   \left({bq\over n}-1+(1-q/n)^b\right).                            \tag{O4.12u}
\]

In particular, if `bq/n>=64`, then `lr/(b(b-1))>=1/4` and

\[
 \mathbb ER\ge {63\over256}Q.
\]

That bare crossing estimate must still survive the nonzero-commutator
conditions; omitting them would make the result inapplicable to (O4.12d).
Use the equivalent form (O4.12): one first-occurrence constraint and one
even crossing-parity constraint per chord.  Walsh-expand the parity
constraints with bits `xi_a` and the first-occurrence constraints with bits
`eta_a`.  Across the bridge cut `L|R`, all first endpoints in `L` precede
all first endpoints in `R`, and no bridge chord has closed yet.  Hence at
site `i` the complete quadratic cut matrix is

\[
 B_i^{\xi,\eta}(u,v)
 =A_i(u,v)(1+\xi_u+\xi_v)+\eta_v,
 \qquad u\in L_i,\ v\in R_i.                                      \tag{O4.12v}
\]

The first term is the direct sum of the two Ferrers matrices induced by
the `xi=0` and `xi=1` vertices.  The second term has rank at most one.
All conditioned nonbridge labels, all within-side interactions, and the
seed contribute only row or column signs in (O4.12q).

Let `R_xi` be the sum over sites of the ranks of those two induced Ferrers
matrices before the rank-one perturbation.  Filtering a retained word by
the two independent `xi` colors gives

\[
 \mathbb E R_\xi
 =n{lr\over b(b-1)}
 \left({bq\over n}-2+
       2(1-q/(2n))^b\right).
\]

Indeed the two color subsequences have respective retention probability
`p/2`, and their total expected number of adjacent pairs is
`bp-2+2(1-p/2)^b`.  If `bq/n>=256`, then

\[
 \mathbb ER_\xi\ge {127\over512}Q,
 \qquad
 \sum_i\operatorname{rank}B_i^{\xi,\eta}
 \ge R_\xi-n
 \quad\hbox{for every }\eta .
\]

Exposing `xi`, the uniform `L/R` permutation, and the independent supports
gives a bounded-difference martingale.  Changing one `xi` bit changes
`R_xi` by at most `4q`; replacing one support changes it by at most `4q`;
transposing two positions changes it by at most `8q`.  The usual
permutation-exposure proof of bounded differences therefore gives an
absolute `c_0>0` such that

\[
 \Pr\!\left\{
   \sum_i\operatorname{rank}B_i^{\xi,\eta}
   <{15\over64}Q
   \text{ for some }\eta
   \,\middle|\, b\right\}
 \le 4e^{-c_0b}.                                                    \tag{O4.12w}
\]

No independence between physical sites is used.  A second
bounded-difference exposure of the random matching gives
`Pr{b<k/3}<=2e^{-c_1k}` for an absolute `c_1>0`.  Therefore, for
`k>=768n/q`, averaging the two exact Walsh projectors and using
(O4.12q) gives

\[
 \|\mathcal W_{\pi,\rm angular}\|_{\rm branch}
 \le
 2^{-\eta qk/3},\qquad
 \eta={15\over64}-\log_2(2/\sqrt3)>0,                              \tag{O4.12x}
\]

outside total pairing/support/Walsh mass `O(e^{-ck})`.  This is a bound on
the full admissible signed coefficient (O4.12d), conditional on a fixed
Pauli boundary branch, not merely on its bare crossing phase.

The gate tariff is equally explicit.  In the normalized Pauli basis, the
transfer matrix of a `d`-qubit unitary conjugation is real orthogonal.
Every column therefore has `l^1` norm at most
`sqrt(4^d)=2^d`.  On `r` replicas a two-qubit gate has branch variation at
most `4^r`, and `s` gates have variation at most `4^(rs)`.

For one replica, each Pauli branch changes only row or column sign functions
in (O4.12q), because commutation with a fixed boundary Pauli is a symplectic
character.  Combining with (O4.12x), the
uniform-pairing-normalized, gate-expanded signed factor satisfies

\[
 \boxed{\quad
 \text{normalized paired signed factor at order }2k
 \ \le\
 4^s\!\left(2^{-\eta qk/3}+O(e^{-ck})\right)
 \quad}                                                            \tag{O4.12y}
\]

relative to its incoming Pauli-branch norm, whenever `k>=768n/q`.
Thus paired angular order beats an arbitrary `s`-gate boundary
exponentially once

\[
 k>\max\!\left\{{6\over\eta q},{2\log 4\over c}\right\}s .
\]

This bound is uniform for each fixed circuit word.  It does not commute the
Hamiltonian-dependent circuit supremum with ensemble expectation.  Closing
that nonlinear Bellman step, rather than applying a circuitwise union bound,
is part of (O4.12z0).

The `r`-replica Pauli branch tariff `4^(rs)` is exact, but (O4.12y) must not
yet be asserted for the full replicated Wick sum.  Pairings joining
occurrences on different replica legs form multi-backbone diagrams; their
sign matrix is not the one-circle crossing matrix used above.  The estimate
tensorizes over replica-factorized pairing sectors, but cross-replica sectors
require a separate multi-backbone cut-rank theorem.  That requirement is
closed below by the ribbon-genus, forest-contraction, and fixed-weight
elimination theorems (O4.12z1)--(O4.12z10); this paragraph records why those
steps were necessary.

Logically, a replica extension is not necessary if one can directly control
the positive Bellman support function.  Set `r=1` in (O4.12i) and
(O4.12n).  If a genuinely nonlinear single-replica estimate proves

\[
 \mathbb E F_s(t)
 \le e^{\kappa s-\gamma\Lambda(H)t/\operatorname{poly}(n)}
    +\left({A tm\over\varepsilon}\right)^{-cm},                    \tag{O4.12z0}
\]

then Markov's inequality gives

\[
 \Pr\{C_\varepsilon(\Phi_H(t))\le s\}
 \le {1\over1-\varepsilon^2}\,\mathbb EF_s(t).
\]

For `s<=gamma Lambda(H)t/(2 kappa poly(n))`, the first term is
exponentially small in normalized time and is absorbed by the second after
an explicit threshold.  Thus (O4.12z0) implies (O4.3) without any
multi-backbone estimate.  Replicas may sharpen constants later; they must
not block the theorem.

But the route from the signed cut-rank coefficient bound to (O4.12z0) at
first moment is **falsified**.  For a probability space `Omega`, a vector
space `V`, a compact body `K`, and an integrable random vector `X`, signed
transfer estimates control linear functionals of `E X`, whereas the desired
quantity is

\[
 \mathbb E h_K(X)
 =\mathbb E\sup_{y\in K}\langle X,y\rangle .
\]

There is no inequality bounding the latter by cancellation in `E X`.
Already for `V=R`, `K={-1,1}`, and a symmetric Rademacher `X`,
`E X=0` while `E h_K(X)=1`.  Convexifying `K` does not change the example.
In the Hamiltonian problem the maximizing circuit is likewise allowed to
depend on `H`; a fixed-boundary signed Wick estimate cannot commute that
selector through ensemble expectation.  Therefore (O4.12q)--(O4.12y) do
not imply (O4.12z0).

The strongest positive survivor is exact: any proof using the present
signed-transfer representation must control either

1. the positive nonlinear Bellman norm `E h_(s,1)(X_H)` directly, or
2. sufficiently high replicated moments before taking the circuit
   supremum.

The second alternative makes the multi-backbone Wick topology
load-bearing, not optional.  A replacement theorem must also isolate the
common recurrence mass before moment amplification: a rare event of
probability `delta_t` contributes `delta_t` to every positive moment, not
`delta_t^r`.  Paying that mass once is the exact mathematical distinction
between an aggregate theorem and the retired circuitwise union bound.

#### Replica ribbon genus: the exact multi-backbone cancellation invariant

The multi-backbone object has a canonical topological representation.
This is a proved bridge, not yet the required probabilistic estimate.
Take the `2k` commutator occurrences on `r` oriented replica backbones.
Let `sigma` be the permutation whose cycles are the cyclic orders on the
nonempty backbones, and let `alpha` be the fixed-point-free involution
pairing equal Gaussian occurrences.  Thicken each backbone to a vertex disc
and each pair to an untwisted ribbon.  Write

\[
 c=\#\langle\sigma,\alpha\rangle\text{-orbits},\qquad
 f=\#\operatorname{cycles}(\sigma\alpha).
\]

The resulting orientable ribbon surface has `r` vertices, `k` edges, `c`
connected components, `f` boundary components, and total genus

\[
 \boxed{\qquad
 2g=k-r+2c-f .
 \qquad}                                                          \tag{O4.12z1}
\]

This is Euler's identity twice: the surface retracts to the ribbon graph,
so `chi=r-k`, while an orientable surface with those components has
`chi=2c-2g-f`.

The same number is exactly the rank relevant to Pauli cancellation.  At one
physical site, first allow zero letters.  A label assignment is a
`F_2^2`-valued edge 1-chain.  Returning every replica backbone to its
endpoint Pauli label imposes zero boundary at every vertex, so the allowed
assignments are

\[
 Z_1(G;\mathbb F_2)\otimes\mathbb F_2^2 .
\]

Reordering paired Pauli occurrences records the mod-two intersection
pairing of the corresponding cycles in the thickened surface.  The
intersection form on `H_1` has radical generated by the boundary curves,
with one relation per connected component.  Since

\[
\begin{aligned}
 \dim H_1(G;\mathbb F_2)&=k-r+c,\\
 \dim\operatorname{rad}&=f-c,
\end{aligned}
\]

its rank is

\[
 (k-r+c)-(f-c)=k-r+2c-f=2g.                                      \tag{O4.12z2}
\]

Equivalently, choose a spanning forest, close each remaining ribbon edge
to a cycle, and record Pauli swaps in that cycle basis.  Every swap is one
transverse intersection; changing the forest performs a congruence and
does not change rank.  Thus the quadratic Gauss cancellation of the full
alphabet depends only on replica ribbon genus, not on a chosen linear order
or a diagram drawing.

There is also an exact Gauss-sum form.  Put
`h=dim H_1(G;F_2)=k-r+c`.  After endpoint conservation, a full-alphabet
Pauli assignment is a pair of binary cycles, hence an element of
`H_1(G;F_2)\otimes F_2^2`, up to the vertex-boundary gauge already removed
by the spanning forest.  Its sign quadratic form has polar matrix equal to
the surface intersection matrix tensored with the nonsingular one-qubit
symplectic matrix.  The polar rank is therefore `4g`.  Character
orthogonality for a quadratic Gauss sum gives, for every added linear
boundary character,

\[
 \left|
 4^{-h}\!\!
 \sum_{a\in H_1(G;\mathbb F_2)\otimes\mathbb F_2^2}
 (-1)^{q_\Sigma(a)+\ell(a)}
 \right|
 \in\{0,\,2^{-2g}\}.                                               \tag{O4.12z2a}
\]

The value is zero exactly when the linear character is incompatible with
the radical; otherwise its magnitude is `2^(-2g)`.  Thus every replica
handle costs exactly a factor `1/4` before the nonzero-letter restriction,
and every direction not cancelled by handle genus lies in the boundary
radical.

Random multi-backbone topology is already controllable.  Assume every
backbone contains at least two occurrences, so `sigma` has no fixed point,
and let `alpha` be a uniform fixed-point-free involution on `2k` symbols.
Loth and Rattan's conjugacy-class product theorem gives

\[
 \mathbb E f
 =\mathbb E\,\#\operatorname{cycles}(\sigma\alpha)
 \le H_{2k}+1.                                                     \tag{O4.12z2b}
\]

This is a literature input, not our novelty
([Loth--Rattan, arXiv:2310.06659](https://arxiv.org/abs/2310.06659)).
Their theorem applies because the law of `sigma alpha` depends only on the
fixed-point-free conjugacy types of `sigma` and `alpha`.

The required exponential tail follows elementarily.  Switching two matched
edges of `alpha` changes `sigma alpha` by a permutation supported on at most
four symbols and changes its number of cycles by at most two.  Generate the
uniform matching from a uniform random permutation paired in consecutive
positions and expose that permutation.  The bounded-difference inequality
for random permutations therefore gives, with a deliberately nonoptimal
constant,

\[
 \Pr\{f-\mathbb Ef\ge u\}
 \le \exp\!\left(-{u^2\over64k}\right).                            \tag{O4.12z2c}
\]

For `k>=256`, `H_(2k)+1<=k/16`; taking `u=k/16` shows
`f<=k/8` outside `e^(-k/16384)`.  If also `k>=8r`, Euler's law then gives

\[
 2g=k-r+2c-f\ge {3k\over4},
\]

and the exact full-alphabet Gauss factor (O4.12z2a) is at most
`2^(-3k/4)` on that event.  Thus the random replica topology itself is not
the open problem: it creates extensive genus with an exponential tail.
Backbones of occurrence count zero are omitted; singleton backbones form a
separate occupancy event and cost at most one incident ribbon each when
passing to the replica-incidence 2-core.

For one backbone, (O4.12z2) reduces to the familiar rank of the chord
interlacement matrix.  For several replicas it supplies the missing
coordinate-free replacement: tree-like replica connections have genus zero
and cannot cancel, while every handle contributes two independent binary
intersection directions.  The boundary radical `f-c` is the precise
topological carrier of the replica-collision memory that survives signed
bulk cancellation.

`[FALSIFIED — FIRST REPLICA GENUS TRANSPORT LAW.]`  The first formulation
asserted that, in the fixed-`q` angular
Pauli ensemble, after the exact nonzero-letter and first-commutator
projections, a replicated Wick ribbon graph with `k` pairs on `r`
nonempty backbones and `kq >= Cnr` retains site-summed effective
intersection rank

\[
 R_{\rm eff}\ge
 \left(\log_2(2/\sqrt3)+\delta_q\right)(qk-C_qnr)
                                                                    \tag{O4.12z3}
\]

outside mass `e^{-c_q(k-C_qr)}`, uniformly in every Walsh field and circuit
boundary tensor.  The complementary genus-zero/boundary-radical sector
admits a positive decomposition whose total spherical-time contribution is
the common recurrence mass, paid once rather than once per circuit word or
replica.

The recurrence identification is false.  Already for one backbone,
noncrossing pairings have genus zero but carry the order-one Catalan
self-energy governed by (O4.13); they describe ordinary bulk propagation,
not rare recurrence.  Boundary radical likewise records degeneracy of the
intersection form, not by itself a late-time spectral return.  The corrected
scale loss in (O4.12z3) is `O(nr)`, because an admissibility perturbation may
lose `O(r)` rank at each of `n` sites, rather than `O(qr)`.

The positive survivor is (O4.12z1)--(O4.12z2): replica genus is exactly the
signed cancellation rank, while the radical classifies the directions that
need a separate resummation.  Based on what killed the first statement, the
stronger active conjecture is:

The one-boundary planar resummation is already exact at operator level.
Write `A_p=ad_(P_p)` on the finite Hilbert--Schmidt operator space and define
the covariance map

\[
 \boldsymbol\eta(X)=\sum_p v_p A_pXA_p .
\]

Let `M_(2k)^(0)` be the sum of all noncrossing Wick words of length `2k`,
with `M_0^(0)=I` and odd moments zero.  Rooting at the partner of the first
occurrence gives the dependency-closed recursion

\[
 M_{2k}^{(0)}
 =\sum_{j=0}^{k-1}
   \boldsymbol\eta(M_{2j}^{(0)})
   M_{2(k-1-j)}^{(0)}.                                             \tag{O4.12z4}
\]

Indeed the rooted label `p` surrounds the `2j` occurrences inside its
chord, producing `A_p M_(2j)^(0) A_p`, and the remaining word follows on
the right.  Therefore the formal operator-valued Cauchy series

\[
 \mathbf G(z)
 =\sum_{k\ge0}M_{2k}^{(0)}z^{-2k-1}
\]

satisfies

\[
 z\mathbf G(z)
 =I+\boldsymbol\eta(\mathbf G(z))\mathbf G(z),\qquad
 \mathbf G(z)
 =\left(zI-\boldsymbol\eta(\mathbf G(z))\right)^{-1}               \tag{O4.12z5}
\]

whenever the formal inverse is interpreted coefficientwise (and
analytically wherever it exists).  Equation (O4.13) below is the diagonal
Pauli-coordinate shadow of (O4.12z4).  Thus the active conjecture does not
need to invent a planar reference; it must extend this exact Dyson object to
several boundary components and prove compatibility with the Bellman
support norm.

That first extension is combinatorial and can be closed exactly.  It is
useful to retain connected components and genus rather than immediately
summing them away.  Let
`\mathfrak C_(g,r)(C_1,\ldots,C_r)` be the formal sum of connected Wick
ribbon pairings of total genus `g` on `r` nonempty cyclic backbones
`C_1,\ldots,C_r`, with one half-edge `a` of `C_1` marked.  Coefficients may
take values in any tensor category in which disjoint union is a tensor
product and a paired edge is evaluated by the covariance contraction

\[
 \mathcal E_{a,b}
 =\sum_p v_p\,\mathcal A_p^{(a)}\mathcal A_p^{(b)} .
\]

For the admissible Pauli expansion, the object carried by a cut boundary
also records its exposed Pauli seed and Walsh projector bits.  With that
state retained, (O4.12d) supplies precisely such a local edge-contraction
weight; forgetting the state before gluing would be invalid.

Pair `a` with a half-edge `b`.  If `b` lies on a different backbone `C_j`,
contracting the ribbon joins the two cyclic words in the unique
orientation-preserving order, denoted `C_1#_(a,b)C_j`, and preserves genus.
If `b` lies on `C_1`, cut the cyclic word at `a,b` into the two cyclic words
`U_b,V_b`.  The root ribbon is either separating, in which case the other
backbones split into a subset `S` and its complement and the two genera add
to `g`, or nonseparating, in which case cutting it leaves one connected
surface of genus `g-1` with the two new backbones `U_b,V_b`.  Consequently
the connected Wick sums obey the exact rooted join--split identity

\[
\boxed{\begin{aligned}
 \mathfrak C_{g,r}(\mathbf C)
 ={}&
 \sum_{\substack{b\in C_j\\j>1}}
 \mathcal E_{a,b}\,
 \mathfrak C_{g,r-1}
 \bigl(C_1\#_{a,b}C_j,\mathbf C_{\widehat{1,j}}\bigr)\\
 &+\sum_{b\in C_1\setminus\{a\}}\mathcal E_{a,b}
 \Bigg[
 \sum_{\substack{S\subseteq\{2,\ldots,r\}\\g_1+g_2=g}}
 \mathfrak C_{g_1,1+|S|}(U_b,\mathbf C_S)
 \otimes
 \mathfrak C_{g_2,r-|S|}(V_b,\mathbf C_{S^c})\\
 &\hspace{50mm}
 +\mathbf1_{g\ge1}\,
 \mathfrak C_{g-1,r+1}(U_b,V_b,\mathbf C_{\widehat1})
 \Bigg].
\end{aligned}}                                                   \tag{O4.12z6}
\]

Empty arcs use the tensor unit, and unstable empty connected factors are
omitted.  The full, not necessarily connected, Wick sum is recovered by
the ordinary set-partition formula over backbone labels.

**Proof.**  The partner `b` of the marked half-edge is unique.  A ribbon
between distinct vertex discs may be contracted; this decreases both
vertices and edges by one and changes neither component count, faces, nor
genus.  A ribbon whose ends lie on the marked disc becomes, after capping
the boundary curves, a simple closed curve.  On an orientable surface it is
either separating or nonseparating.  In the separating case its two sides
determine `S` uniquely and restriction gives the displayed tensor product.
In the nonseparating case cutting along it raises Euler characteristic by
two and therefore lowers genus by one.  These operations are reversible by
gluing the root ribbon, so the cases are disjoint and exhaustive.  Edge
labels and the carried boundary state are contracted only when the ribbon
is glued, hence the same bijection is weight preserving.

At `g=0,r=1` only the separating line survives and gives (O4.12z4).
At `g=0,r>1`, (O4.12z6) is the required multi-backbone planar
Schwinger--Dyson hierarchy.  At positive genus it says something sharper
than the polymer language above: every handle is created by an explicit
nonseparating self-gluing operation.  Thus multi-boundary planar
resummation itself is no longer conjectural.  The still-open step is
analytic: prove that the solution of this hierarchy, with its exposed
boundary states, is bounded in a norm stable under the Bellman maximum.

There is no need to conjecture the algebraic part of that norm.  For an
`r`-replica Hermitian tensor define the absolute Bellman crossnorm

\[
 \|X\|^\sharp_{s,r}
 =\sup_{C\in\mathcal C_s}
   \left|\operatorname{Tr}\!\left(
      X(C\rho_0C^\dagger)^{\otimes r}\right)\right|.
\]

It has the two exact properties needed by the join--split hierarchy:

\[
\begin{aligned}
 \|X\otimes Z\|^\sharp_{s,r_1+r_2}
 &\le \|X\|^\sharp_{s,r_1}\|Z\|^\sharp_{s,r_2},\\
 \|X\|^\sharp_{s+1,r}
 &=\max_{G\in\mathcal G_n}
   \left\|(G^\dagger)^{\otimes r}XG^{\otimes r}
   \right\|^\sharp_{s,r}.                                         \tag{O4.12z7}
\end{aligned}
\]

The first line follows because evaluation of a tensor product on the same
replicated circuit target factors, and the supremum of a product is at most
the product of the two suprema.  The second is the absolute version of
(O4.12n).  Triangle inequality is immediate, so `\|\cdot\|^\sharp` is a
seminorm (a norm after quotienting the annihilator of the circuit body).
Therefore every separating term of (O4.12z6) is submultiplicative and every
Bellman insertion is represented exactly, without selecting a circuit
before ensemble averaging.  What remains is quantitative rather than
foundational: establish a strict normalized contraction for the joined
cavity and handle operators in this crossnorm.

Replica topology can also be reduced exactly to the already understood
one-backbone geometry.  Let a connected ribbon graph have `r` backbone
vertices and `k` paired ribbons, and choose a spanning tree `T` of its
backbone-incidence multigraph.  Contracting the `r-1` ribbons in `T` merges
the vertex discs into one disc.  The result is a one-vertex chord diagram
with

\[
 K=k-r+1
\]

chords, the same boundary curves, and the same genus.  Its chord
interlacement form is the surface intersection form in the fundamental
cycle basis determined by `T`.  This is not merely a rank comparison: it is
a congruent matrix presentation of the same form.

The reduction is compatible with the random matching before the
fixed-weight coefficient extraction.  Fix `T` as a set of `r-1` disjoint
pairs of occurrence positions.  Conditional on `T` being contained in a
uniform matching of `2k` positions, the residual pairs form a uniform
matching of the remaining `2K` positions.  After contracting `T`, they are
therefore an ordinary uniform one-backbone chord diagram.  If backbone `j`
has `d_j` occurrences, the number of possible occurrence-level spanning
trees is at most

\[
 (2k)^{r-2}\prod_{j=1}^r d_j,
\]

by the weighted Cayley identity
`\sum_T\prod_j d_j^{\deg_T(j)}
=(\sum_jd_j)^{r-2}\prod_jd_j`; choices reusing one occurrence only make
this an overcount.  A specified set of tree pairs occurs in a uniform
matching with probability
`\prod_{\ell=0}^{r-2}(2k-(2\ell+1))^{-1}`.  Hence its total marked mass in
the normalized pairing average is at most

\[
 {\displaystyle(2k)^{r-2}\prod_jd_j\over
  \displaystyle\prod_{\ell=0}^{r-2}(2k-(2\ell+1))}
 \le {1\over4k}\left({4k\over r}\right)^r
 \quad (r\le k/2),                                                 \tag{O4.12z8}
\]

where the last inequality uses
`\prod_jd_j\le(2k/r)^r` and bounds every denominator factor below by
`k`.  Thus marking a contraction tree has explicit
`O(r\log(k/r))` entropy when `k/r` is bounded below, rather than an
uncontrolled replica-diagram entropy.

There is an exact rank statement for the boundary constraints introduced
when the tree variables are removed.  At one site and for one binary
coordinate, write the polar matrix of a quadratic Walsh phase, with the
tree variable first, as

\[
 \begin{pmatrix}0&u^\mathsf T\\u&B\end{pmatrix}.
\]

An affine vertex-conservation equation has the form
`x_0=c+\ell^\mathsf Tx`.  Substitution changes the residual polar matrix
from `B` to

\[
 B+u\ell^\mathsf T+\ell u^\mathsf T,
\]

a perturbation of rank at most two.  Eliminating the two binary Pauli
coordinates of every tree ribbon therefore loses at most four binary polar
directions per contracted ribbon and site.  For `c` connected components,
forest contraction costs at most

\[
 4n(r-c)                                                        \tag{O4.12z9}
\]

in the site-summed binary polar rank.  This proves the previously asserted
`O(nr)` scale at the quadratic-form level and explains it: it is the exact
cost of solving replica-tree flow, not a genus defect.

The apparent fixed-weight obstruction can also be closed.  Let `\mu_q` be
uniform probability measure on weight-`q` Pauli words in
`A^n=(\mathbb F_2^2)^n`.  Solving one tree-flow equation replaces its
independent tree label by an affine function `Lx+c` of the residual cycle
labels and inserts the exact density `\mu_q(Lx+c)`.  Fourier inversion gives

\[
 \mu_q(Lx+c)
 =4^{-n}\sum_{\chi\in\widehat{A^n}}
   \widehat\mu_q(\chi)\chi(c)\chi(Lx),
 \qquad |\widehat\mu_q(\chi)|\le1.
\]

The total absolute coefficient of this expansion is at most one.  Products
of solved tree-label densities retain that bound.  Thus exact weight `q`
does not introduce an exponential coefficient-extraction loss at all; it
only averages the residual transfer over additional linear characters,
against which (O4.12w) is uniform.

The quadratic perturbation (O4.12z9) has a separate explicit cost.  A
binary quadratic phase whose polar perturbation has rank `R` is, after a
linear change of variables, a function of at most `R` essential coordinates
times one linear character.  Fourier expanding those coordinates has total
absolute coefficient at most `2^R`.  Combining this observation with
(O4.12z8)--(O4.12z9) and the one-backbone bound (O4.12x) proves the
following connected-sector transfer theorem.  Put `K=k-r+1`, assume
`r\le k/2` and `K\ge768n/q`, and retain arbitrary affine replica-boundary
data and all commutator Walsh projectors.  Then the normalized paired
angular contribution of the connected `r`-backbone sector, after an
arbitrary `s`-gate boundary, is at most

\[
\boxed{
 {1\over4k}\left({4k\over r}\right)^r
 2^{\,4n(r-1)}4^{rs}
 \left(2^{-\eta qK/3}+O(e^{-cK})\right),
 \qquad
 \eta={15\over64}-\log_2(2/\sqrt3)>0 .
}                                                                  \tag{O4.12z10}
\]

Indeed mark and condition on a spanning tree, contract it, solve its
sitewise flow variables, Fourier-expand their exact weight densities and
the rank-`4n(r-1)` perturbation, and then apply (O4.12x) to the resulting
uniform residual one-circle matching.  Summing the marked-tree overcount
gives (O4.12z8); the circuit boundary gives `4^(rs)`.  Every step is an
inequality in absolute value, so multiple possible spanning trees only
overcount and cannot invalidate the estimate.

Thus the fixed-weight forest-elimination conjecture is proved, with explicit
constants.  In particular the normalized paired factor beats the replica
and circuit boundary tariffs at that fixed order whenever

\[
 \min\!\left\{{\eta q\over3},{c\over\log 2}\right\}(k-r+1)
 >
 4n(r-1)+2rs
 +r\log_2(4k/r)+O(1),
                                                                    \tag{O4.12z11}
\]

where the absolute `O(1)` absorbs the constant in the exceptional matching
term.  Topology, cross-replica pairing, fixed Pauli weight, and the circuit
selector tariff are therefore no longer separate open problems at the
normalized-pairing level.  This does not yet bound the physical series:
restoring the pairing multiplicity (O4.12z) can amplify the exceptional
low-interlacement sector.  Its leading contribution is precisely the planar
cavity governed by (O4.12z6), and it must be resummed before applying
(O4.12z10).

The planar cavity has an exact norm-stable real-time realization.  This
closes item 3 below for one boundary, and for the collective replica
Liouvillian before resolving it into separate backbone boundaries.  Let
`\mathcal V_r` be the `r`-replica Hilbert--Schmidt operator space and put

\[
 A_p^{(r)}
 =\sum_{\ell=1}^r
  I^{\otimes(\ell-1)}\otimes\operatorname{ad}_{P_p}
  \otimes I^{\otimes(r-\ell)} .
\]

On the full Fock space
`\mathcal F(\mathbb C^m)\otimes\mathcal V_r`, with left creation operators
`\ell_p` and vacuum `\Omega`, define the bounded self-adjoint operator

\[
 S_r=\sum_p\sqrt{v_p}\,
  (\ell_p+\ell_p^\dagger)\otimes A_p^{(r)} .
\]

Vacuum compression `E_\Omega` is unital completely positive.  The relations
`\ell_p^\dagger\ell_q=\delta_{pq}I` show by the usual stack reduction,
without an asymptotic limit, that

\[
 E_\Omega(S_r^{2k})=M_{2k,r}^{(0)},\qquad
 E_\Omega(S_r^{2k+1})=0,
\]

where `M_(2k,r)^(0)` is the exact sum of globally noncrossing Wick pairings
for the collective replicated covariance

\[
 \boldsymbol\eta_r(X)=\sum_pv_pA_p^{(r)}XA_p^{(r)} .
\]

Consequently the planar real-time series converges in operator norm for
every real `t` and equals

\[
 U_{0,r}(t)
 =\sum_{k\ge0}{(-1)^kt^{2k}\over(2k)!}M_{2k,r}^{(0)}
 =E_\Omega(e^{-itS_r}),\qquad
 \boxed{\ \|U_{0,r}(t)\|_{\rm op}\le1\ }.                           \tag{O4.12z12}
\]

Self-adjointness uses self-adjointness of every Pauli commutator on
Hilbert--Schmidt space; contractivity follows because vacuum compression is
unital completely positive and `e^(-itS_r)` is unitary.  Also
`\|S_r\|\le2\|\boldsymbol\eta_r(I)\|^{1/2}`, so no formal-series radius is
being hidden.  Applying `U_(0,r)(t)` to a unit Hilbert--Schmidt endpoint and
testing against a pure replicated circuit target gives absolute overlap at
most one, uniformly in `s,r,t`.

This theorem prevents the Catalan multiplicity from blowing up after time
resummation.  It does not yet assert decay: a completely positive
contraction may have an invariant subspace.  Nor does the single collective
ordering by itself sum every annular/multi-boundary planar component in
(O4.12z6).  The remaining planar question is now spectral and explicit:
classify the fixed space of the cavity channel and prove decay on the
traceless Bellman-visible quotient, while solving the cross-boundary join
terms of (O4.12z6).

The fixed space can be classified exactly, and it is larger than the scalar
sector for replicas.  For every `r`,

\[
 \boxed{
 \{v:U_{0,r}(t)v=v\ {\rm for\ all}\ t\}
 =\bigcap_p\ker A_p^{(r)} .
 }                                                                  \tag{O4.12z13}
\]

One inclusion is immediate because `S_r(\Omega\otimes v)=0` on the common
kernel.  Conversely, differentiating `U_(0,r)(t)v=v` twice at zero gives

\[
 0=M_{2,r}^{(0)}v
   =\left(\sum_pv_p(A_p^{(r)})^2\right)v .
\]

Taking the Hilbert--Schmidt inner product with `v` yields
`\sum_pv_p\|A_p^{(r)}v\|^2=0`, hence every summand vanishes.

Suppose now that the Hamiltonian Pauli family generates the full unitary Lie
algebra on the physical Hilbert space under linear combinations and
commutators.  Under
`\mathcal V_r\cong\operatorname{HS}(\mathcal H^{\otimes r})`,
`A_p^(r)` is the infinitesimal diagonal-conjugation action.  Its common
kernel is therefore the commutant of `U^{\otimes r}` for all physical
unitaries `U`.  Schur--Weyl duality gives

\[
 \bigcap_p\ker A_p^{(r)}
 =\operatorname{span}\{W_\pi:\pi\in S_r\}
 \quad (\dim\mathcal H\ge r),                                      \tag{O4.12z14}
\]

where `W_\pi` permutes replica tensor factors.  In particular the
one-replica fixed space is exactly the scalar identity, but the replicated
fixed space contains the whole permutation algebra.

This corrects the target quotient.  “Traceless” is sufficient only at
`r=1`; high-moment decay must be proved modulo the replica-permutation
algebra.  These modes are not a recurrence remainder.  They are universal
purity moments:
`\operatorname{Tr}(W_\pi\sigma^{\otimes r})
=\prod_{c\in\operatorname{cycles}(\pi)}\operatorname{Tr}(\sigma^{|c|})`,
which equals one for every pure circuit target.  They can therefore be
subtracted as a target-independent baseline before the Bellman maximum.
The genuinely selector-sensitive planar problem lives on the orthogonal
complement of (O4.12z14).

`[LITERATURE BOUNDARY.]`  Operator-valued semicircular realization and the
Dyson equation are standard; see Helton--Rashidi Far--Speicher,
[arXiv:math/0703510](https://arxiv.org/abs/math/0703510).  General matrix
Dyson-equation regularity theorems give absolutely continuous densities only
under additional flatness/primitivity assumptions; see Alt--Erdos--Krueger,
[arXiv:1804.07752](https://arxiv.org/abs/1804.07752).  Such assumptions
cannot be quoted here without proof because (O4.12z14) makes the replicated
covariance nonfaithful on the full space.  Matrix-valued semicircular laws
can in fact have atoms for degenerate covariance
([Soltanifar, arXiv:1109.4973](https://arxiv.org/abs/1109.4973)).
Therefore atom-free decay on the permutation quotient is a genuine
model-specific frontier; (O4.12z13) alone does not establish it.

There is nevertheless an unconditional quantitative consequence.  Let
`Q_r` be Hilbert--Schmidt projection onto the orthogonal complement of the
permutation algebra and define the replica Casimir gap

\[
 \lambda_r
 =\lambda_{\min}^{+}\!\left(
   \sum_pv_p(A_p^{(r)})^2\right)>0,\qquad
 R_r=\|S_r\|.
\]

Positivity of `\lambda_r` follows from (O4.12z13)--(O4.12z14) and finite
dimension.  Hence

\[
 \sum_pv_p(A_p^{(r)})^2\ge\lambda_rQ_r .                           \tag{O4.12z15}
\]

For one replica this gap is explicit in the Pauli basis:

\[
 \lambda_1
 =4\min_{z\ne0}\sum_{\omega(p,z)=1}v_p .
\]

If all weight-one Pauli directions occur with variance at least `v_min`,
then `\lambda_1\ge8v_min`, because a nonidentity Pauli word anticommutes
with two one-site letters at any site in its support.

The gap gives a strict, fully controlled short-time cavity contraction.
Odd vacuum moments vanish, so

\[
 U_{0,r}(t)
 =I-\frac{t^2}{2}\sum_pv_p(A_p^{(r)})^2+\mathcal R_4(t),\qquad
 \|\mathcal R_4(t)\|
 \le{(R_r|t|)^4\cosh(R_r|t|)\over24}.
\]

Since `U_(0,r)(t)` is self-adjoint, fixes the permutation algebra, and is a
contraction, (O4.12z15) implies

\[
 \boxed{\quad
 \|Q_rU_{0,r}(t)Q_r\|
 \le1-{\lambda_rt^2\over4}
 \quad}                                                            \tag{O4.12z16}
\]

whenever

\[
 R_r|t|\le\tfrac12,\qquad
 t^2\le {6\lambda_r\over R_r^4\cosh(1/2)} .
\]

The first condition also keeps the spectrum of `U_(0,r)(t)` positive, so
the displayed upper spectral bound is an operator-norm bound.  This proves
genuine loss of every selector-sensitive planar mode at the first
interaction timescale.  It does not prove long-time decay because vacuum
compression is not a semigroup; iterating (O4.12z16) would silently replace
the static Hamiltonian by fresh noise.

`[CONJECTURE — PLANAR-RENORMALIZED REPLICA GENUS LAW.]`  Exactly resum every
genus-zero component of the full admissible replica ribbon expansion into a
positive matrix-valued cavity propagator.  In the connected polymer
expansion relative to that propagator:

1. use the fixed-order contraction (O4.12z10) after, rather than before,
   exact planar dressing, so pairing multiplicity is paid only by the
   cavity propagator;
2. prove the dressed handle polymers are contractive in the Bellman
   crossnorm (O4.12z7);
3. extend the exact collective contraction (O4.12z12) to the joined
   multi-boundary hierarchy and prove decay on the orthogonal complement of
   the exact permutation fixed algebra (O4.12z14); and
4. show the remainder not captured at any finite genus, rather than the planar
   sector, is precisely where the common nonperturbative recurrence mass
   enters and is paid once.

This replacement survives the killing example because it retains the whole
noncrossing Catalan sector in the reference propagator instead of calling it
exceptional.  It is stronger than a coefficient estimate: it asserts a
positive decomposition compatible with the Hamiltonian-dependent circuit
selector.  Its former first open implication, the multi-backbone
Schwinger--Dyson loop identity, is now (O4.12z6).  The first open implication
is therefore a strict normalized cavity/handle contraction in the exact
Bellman crossnorm (O4.12z7) after exact planar dressing.  The fixed-`q`
multi-backbone estimate needed at that point is already (O4.12z10).

This statement does not silently normalize away the number of Wick
pairings.  If the coefficient dictionary has size `m`, conversion from the
uniform pairing-and-label average to the degree-`2k` spherical moment carries
the exact scalar factor

\[
 a_{m,k}
 ={m^k(2k-1)!!\over m(m+2)\cdots(m+2k-2)}.                         \tag{O4.12z}
\]

It is obtained by summing the normalized label average over `m^k` block
labels and the normalized pairing average over `(2k-1)!!` pairings, then
dividing by the angular moment denominator (O4.12f).  The common commutator
amplitude and the chosen interaction-rate normalization must also remain in
the polynomial coefficient.  Thus (O4.12y) is a genuine exponential
contraction of the signed combinatorial factor, but not yet a bound on the
resummed unitary propagator.

Equations (O4.12q)--(O4.12z14) move the open core through the fixed-order
multi-backbone and selector geometry.  The exact remaining analytic task is
to solve the joined planar hierarchy on the complement of its permutation
fixed algebra, dress (O4.12z10) by that solution, and isolate the common
nonperturbative recurrence core once before the spherical/time transform.
Absolute Taylor summation is forbidden: it destroys the unitary
cancellations and introduces an artificial `e^(t\|\mathcal L\|)` loss.

That nested sector can be resummed exactly.  Let `N_k(z)` be the coefficient
of `P_z` obtained by summing the `2k`-th Wick expansion over noncrossing
pairings only, with `N_0(z)=1`.  Decomposing at the chord incident to the
first location gives

\[
 N_k(z)=4\sum_{\omega(p,z)=1}v_p
       \sum_{j=0}^{k-1}N_j(z+p)N_{k-1-j}(z).                          \tag{O4.13}
\]

Indeed the opening commutator moves `z` to `z+p`, the `j` enclosed pairs
return to `z+p`, the closing commutator contributes the second factor of two
and returns to `z`, and the remaining pairs evolve from `z`.  Hence the
formal generating functions

\[
 \mathcal N_z(u)=\sum_{k\geq0}N_k(z)u^k
\]

are the unique coefficientwise solution of the coupled cavity equations

\[
 \mathcal N_z(u)=
 {1\over
  1-4u\sum_{\omega(p,z)=1}v_p\mathcal N_{z+p}(u)}.                    \tag{O4.14}
\]

This is an exact all-orders self-energy law on the Pauli commutator graph.
For example, if `lambda_z <= Lambda` on the reachable component, induction in
(O4.13) yields

\[
 0\leq N_k(z)\leq C_k(4\Lambda)^k,                                  \tag{O4.15}
\]

where `C_k` is the `k`-th Catalan number.  Thus nested growth is not an open
diagrammatic remainder.  Pairings with crossing chords remain: commuting
crossings form the Gaussian background, whereas their nonempty
anticommutation subgraph is constrained by (O4.12) to be Eulerian.

The locality cost of those components has a uniform combinatorial bound.
Take the uniform weight-`q` ensemble and sample the `k` block labels
independently.  For any fixed set of `v` blocks, a connected
anticommutation graph forces their `q`-site supports to be connected by
overlaps.  For a fixed labelled spanning tree, expose it away from a root.
At every new vertex, its independent uniform `q`-subset intersects its
parent's fixed `q`-subset with probability at most

\[
 \mathbb P(S_a\cap S_b\ne\varnothing)
 \leq\mathbb E|S_a\cap S_b|={q^2\over n}.
\]

Cayley's formula and a union bound over the chosen vertices therefore give

\[
 \mathbb P(\text{some nonempty Eulerian crossing component})
 \leq
 \sum_{v=3}^{k}{k\choose v}v^{v-2}
       \left({q^2\over n}\right)^{v-1}.                              \tag{O4.16}
\]

The lower limit is three because a nonempty connected simple Eulerian graph
contains a cycle.  This estimate is uniform in the chord pairing, seed label
`z`, and Pauli letters; anticommutation is stronger than support overlap, so
forgetting letters only enlarges the event.

Writing `x=e q^2 k/n`, the right side is at most

\[
 {n\over q^2}\sum_{v=3}^{k}{x^v\over v^2}.
\]

For `x<=1/2` it is bounded by

\[
 {2e^3q^4k^3\over9n^2}.                                             \tag{O4.17}
\]

Consequently, if `R_(2k)^cross(z)` denotes the absolute Wick contribution
from labelings with a nonempty crossing-memory component, then

\[
 |R_{2k}^{\rm cross}(z)|
 \leq
 4^k(2k-1)!!\left(\sum_pv_p\right)^k
 \sum_{v=3}^{k}{k\choose v}v^{v-2}
       \left({q^2\over n}\right)^{v-1}.                              \tag{O4.18}
\]

Thus genuine crossing memory is negligible uniformly for
`k=o_q(n^(2/3))`, improving the unrenormalized pair-collision window
`k=o_q(sqrt(n))`.  The exponent `2/3` is not asserted sharp: it is the first
cycle threshold of the rigorous tree bound.  Reaching order `n` requires
resumming triangle and higher Eulerian polymers rather than bounding their
occurrence probability.

More generally, suppose every Eulerian crossing component on at most `L`
blocks has been summed into a dressed background.  The absolute unsummed
remainder is supported on a component of size at least `L+1`, and the same
tree argument gives

\[
 \mathbb P(\text{an unsummed component remains})
 \leq
 \sum_{v=L+1}^{k}{k\choose v}v^{v-2}
       \left({q^2\over n}\right)^{v-1}.                              \tag{O4.19}
\]

If `x=e q^2 k/n<=1/2`, this is at most

\[
 {2n\over q^2}\,{x^{L+1}\over(L+1)^2}.                              \tag{O4.20}
\]

For every fixed `L`, exact resummation through size `L` therefore controls
the remainder for

\[
 k=o_q\!\left(n^{L/(L+1)}\right).                                   \tag{O4.21}
\]

The sequence begins with the triangle threshold `n^(2/3)`, then
`n^(3/4)`, and tends to `n` as `L` grows.  This proves that no finite list of
connected corrections reaches the order-`n` transition.  The complete
signed polymer free energy, not another fixed cumulant, is the next
load-bearing object.

The same bound nevertheless reaches order `n` at the structural level.  Let
`k=floor(kappa n)` and assume

\[
 x_\kappa=e q^2\kappa<1.
\]

Choose `L_n=ceil(C log n)` with
`C>1/|log x_kappa|`.  Equation (O4.20) then gives

\[
 \mathbb P\!\left(
 \begin{array}{c}
 \text{some Eulerian crossing-memory component}\\
 \text{contains more than }L_n\text{ blocks}
 \end{array}\right)
 \longrightarrow0.                                                  \tag{O4.22}
\]

Indeed `n x_kappa^(L_n+1)/(L_n+1)^2 -> 0`.  Thus below the explicit
subcritical density `1/(e q^2)`, an order-`n` Wick word decomposes with high
probability into crossing-memory components of logarithmic size.  The
remaining difficulty is not a macroscopic connected diagram; it is the
collective signed free energy of extensively many small components and
their seed-parity dressing.

This Eulerian law moves the live problem beyond the elementary `k^2/n`
collision ceiling.  The next object is a forest-renormalized expansion in
which all nested self-energy insertions are summed exactly and the remaining
polymers are Eulerian crossing components.  For fixed-`q` labels, a connected
component on `v` sampled local words already costs support coincidences; the
Eulerian condition excludes the single-edge component that would have
produced the earliest divergence.  What remains unproved is a uniform
polymer bound after `k` reaches order `n`, followed by a joint-amplitude
version against the complete circuit tube.  Even a complete return-moment
resummation would not by itself prove O4.

A circuit-tube estimate at gate budget `s` must ultimately control entropy at
order comparable to `s`, which reaches `Theta(2^n/poly(n))` at saturation.
Fixed-order moment universality, including (O4.8), still cannot pay that
entropy; the exact gain is that the first nontrivial resummation target is
now a cycle gas rather than an arbitrary collision gas.

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
- 2026-08-02 -- Closed the exact Haar-moment and abstract all-time comparison
  layers of O6. `FiniteUnitaryHaarMeasureLaw.lean` now proves normalized Haar
  is a probability measure, exact first moments, exact same-row and
  distinct-row fourth moments
  `2/(D(D+1))` and `1/(D(D+1))`, and the exact mean-square law
  `1/(D+1)` for every balanced operator-norm-one diagonal probe. It also
  constructs such a probe explicitly in every even dimension, including all
  nontrivial qubit dimensions. `PermanentLocalityHaarSeparationLaw.lean`
  combines that benchmark with the physical product-stabilizer lower bound:
  whenever `M*3^q < D+1`, every Pauli-transfer time slice fixing the nonzero
  local Hamiltonian coordinate has protocol signal strictly above Haar. Both
  modules compile individually with `lake env lean`; the new separator is
  imported by the `HTGeometry` umbrella. Remaining O6 work is the concrete
  fixed-local Hamiltonian-to-Pauli-transfer instantiation and full same-score
  ensemble packaging, not the moment or dimension-linear inequality. The
  explicit balanced diagonal observable is also constructed as a unitary
  matrix and proved to have L2 operator norm exactly one, closing the previous
  Hilbert--Schmidt-normalization objection.
  `SelfAdjointPauliTransferConservationLaw.lean` then removes the abstract
  fixed-vector assumption: in every finite real basis of self-adjoint
  observables, the exact Heisenberg transfer matrix of every nonzero
  time-independent Hamiltonian fixes its nonzero coefficient vector at every
  real time. Combining this with the product-stabilizer theorem gives the
  strict all-time Haar gap directly for the basis-coordinate transfer matrix.
  The module compiles and is imported by `HTGeometry`. Remaining O6 work is a
  fully explicit arbitrary-qubit Pauli-basis realization tying the label
  combinatorics to matrix expectations; O4 remains unchanged and is still the
  master theorem gap.
- 2026-08-02 -- Completed the literal arbitrary-qubit Pauli realization in
  `FiniteQubitPauliBasisLaw.lean`. The module proves exact Pauli-string
  Hilbert--Schmidt orthogonality, constructs the real basis of all Hermitian
  matrices, defines the principal weight-`q` Pauli-transfer block, and proves
  that every nonzero Pauli-`q`-local finite-matrix Hamiltonian supplies a
  nonzero fixed vector of that block at every real time. Consequently its
  local two-query sub-signal strictly exceeds the inverse-Hilbert-dimension
  benchmark whenever `M_q 3^q < 2^n+1`. The module compiles in isolation and
  is wired into `HTGeometry`; the final identical-protocol Haar ensemble
  packaging remains. No new O4 endpoint machinery appeared in the concurrent
  corpus audit: the maximally hard endpoint by time `O(2^n/poly(n))` remains
  the unique growth bottleneck.
