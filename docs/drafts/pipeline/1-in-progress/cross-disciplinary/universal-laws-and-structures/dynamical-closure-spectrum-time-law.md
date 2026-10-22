# The dynamical-closure spectrum of time

- **ID:** `dynamical-closure-spectrum-time-law`
- **Stage:** 1-in-progress
- **Type:** ABDUCTIVE MASTER CONJECTURE / QUANTUM DYNAMICS / OBSERVABILITY /
  RECURRENCE / PREDICTIVE REALIZATION
- **Scientific status:** `[CONJECTURE] [FINITE PURE-POINT CORE PARTLY PROVED]`
  `[LOCAL INTERACTION GENERATOR OPEN] [EXTERNAL NOVELTY UNVERIFIED]`
- **Freeze date:** 2026-07-30

Novelty and significance are judged only against external literature. Internal
results below are evidence, dependencies, and falsifiers; they are never
priority evidence.

## The missed primitive

The recurring object is not a clock parameter, recurrence time, entropy, or
Hamiltonian. It is the complete algebra of exact relations among changes that
one observer can distinguish.

For a dynamics and reporter, close the reporter under every time translate (or
every iterated generator action) and quotient by every exact relation obeyed by
those histories. Call the resulting object the **dynamical closure**. Its
canonical minimal realization is the **temporal spectrum** of that reporter.

> **Abductive law.** An observer's operational time is the minimal autonomous
> state space required to carry every future that the observer can distinguish.
> Its dimensions are the independent changes left after all exact relations
> have been imposed.

This does not identify time with human memory. “Memory” means exact predictive
state: the least hidden phase information required to evolve the reporter
without consulting the inaccessible source again.

## Why this is stronger than “time has an observer-dependent dimension”

Calling rational frequency rank a dimension leaves a reviewer free to call it
renaming. The new claim gives the rank a universal property:

```text
visible frequency relations
        ↓ Pontryagin duality
minimal compact autonomous phase carrier
        ↓ dense physical orbit
all completed reporter laws and recurrence
```

If proved, temporal dimension is not an analogy. It is the minimum dimension of
an exact lossless predictive realization in a specified category.

## Exact finite pure-point target

Let a finite stationary quantum reporter see a finite set of energy gaps
\(S_{\mathcal O}\subset\mathbb R\), and put
\[
 \Gamma_{\mathcal O}=\langle S_{\mathcal O}\rangle_{\mathbb Z}.
\]
Give this abelian group the discrete topology and define
\[
 \mathbb T_{\mathcal O}:=\widehat{\Gamma_{\mathcal O}}
 =\operatorname{Hom}(\Gamma_{\mathcal O},\mathbb T).
\]
Physical time supplies the homomorphism
\[
 \tau_{\mathcal O}(t)(\gamma)=e^{-it\gamma}.
                                                        \tag{1}
\]

### Conjectured universal-property theorem

For every finite pure-point reporter:

1. \(\tau_{\mathcal O}(\mathbb R)\) is dense in
   \(\mathbb T_{\mathcal O}\);
2. every exact visible phase history is a continuous function on
   \(\mathbb T_{\mathcal O}\) evaluated along `(1)`;
3. every compact abelian autonomous carrier with dense real orbit through
   which all visible phases factor has a unique continuous quotient onto
   \(\mathbb T_{\mathcal O}\);
4. completed time average of every continuous reporter is Haar average on
   \(\mathbb T_{\mathcal O}\);
5. exact positive return occurs exactly when `(1)` has a nonzero kernel;
6. observer restriction \(\Gamma_1\subseteq\Gamma_2\) is dual to a canonical
   quotient \(\mathbb T_2\twoheadrightarrow\mathbb T_1\).

When \(\Gamma_{\mathcal O}\cong\mathbb Z^r\),
\(\mathbb T_{\mathcal O}\cong\mathbb T^r\), so
\[
 r=\dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}S_{\mathcal O}
 \]
is both rational phase rank and minimal compact Lie phase dimension.

The infinite pure-point extension is not always a torus. For example,
\(\Gamma=\mathbb Z[1/2]\) has rational rank one but its dual is a solenoid,
explaining how one-dimensional temporal rank can be aperiodic. Countable
infinite-rank groups give infinite-dimensional compact inverse limits. This
repairs the false inference that “rank one” always means “one periodic clock.”

The claims in this section are theorem targets until dependency-closed paper
proofs and Lean proofs exist. Pontryagin duality, Kronecker flows, and unique
ergodicity are classical parents and cannot carry novelty.

## Interaction-induced temporal incompressibility

For an uncoupled \(n\)-site \(q\)-level Hamiltonian, all many-body energies are
sums of onsite energies. Hence its complete projective frequency group has
rank at most
\[
 n(q-1).
                                                        \tag{2}
\]
Its exponentially many amplitudes are exact functions of only linearly many
base phases.

The live local theorem says that for every \(n,q\ge2\), almost every arbitrary
one-site plus nearest-neighbour two-site Hermitian path Hamiltonian has
\[
 \Gamma_H\cong\mathbb Z^{q^n-1}.
                                                        \tag{3}
\]
Consequently its global temporal carrier is the full torus
\[
 \widehat{\Gamma_H}\cong\mathbb T^{q^n-1}.
                                                        \tag{4}
\]
For every observer coherence graph \(G\), the same Hamiltonian gives the
maximal allowed quotient dimension
\[
 \dim\mathbb T_{H,G}=q^n-c(G).
                                                        \tag{5}
\]

Equations `(2)`--`(5)` would prove:

> **Local interaction destroys exact compression of the quantum future.**
> An arbitrarily weak generic nearest-neighbour interaction changes the
> minimal completed predictive phase dimension from at most linear in system
> size to exponential in system size.

The coupling can be arbitrarily weak while the exact completed dimension
jumps; every fixed finite observation record remains continuous in coupling.
Thus finite-horizon observation and exact predictive completion do not
commute. A quantitative activation theorem is required before describing the
jump as a laboratory timescale.

The affine Hermitian one-witness genericity mechanism is already formalized.
The remaining proof obligation is an endpoint-local witness inside every
nearest-neighbour path family. Until that closes, `(3)`--`(5)` and the public
law are not manuscript claims.

## What the corpus is saying

The following are evidence for the conjecture, not evidence of novelty.

1. Quantum recurrence moments count exact additive frequency relations.
2. Exact periodicity is the maximally compressed cyclic visible-gap case.
3. Observer coherence graphs quotient the global relative-phase carrier.
4. Generic Hermitian extension can erase every nonzero balanced integer
   spectral relation simultaneously.
5. Weak interaction can leave every fixed finite record close while changing
   the completed relation group.
6. Relational clocks erase one common origin; adding infinitely many internal
   clocks does not restore it.
7. A proposed observer dynamics descends through a quotient exactly when its
   source action preserves the observer equivalence; failure to descend is a
   memory/anomaly term.
8. Hypertranscendence is the infinite-order analogue: no finite differential
   relation closes the complete jet history.
9. Nonlinear dependence horizons cannot arise from one commuting cyclic
   carrier; interaction, gauge structure, or prolongation is forced.
10. Complete passive histories retain representation gauge, and reconstructed
    geometry does not select dynamics. Physical identification requires
    calibrated interventions, not more passive observations.

The common pattern is:

```text
relations compress change;
interaction breaks relations;
observer restriction adds relations;
recurrence tests whether the remaining independent changes rephase;
hypertranscendence is failure of finite relational closure.
```

## Four risky conjectures

### C1 — temporal-spectrum functor

Every operational dynamical theory has a canonical minimal predictive
completion, functorial under observer restriction. Its reversible
almost-periodic sector is the dual of the observer-visible eigenfrequency
group; its stable and continuous sectors carry irreversible loss and
zero-density return information.

**Falsifiers:** nonunique minimal completions in the declared category;
observer restriction that has no canonical quotient; equal complete
operational histories with inequivalent temporal sectors after all null
states are removed.

### C2 — generic local temporal incompressibility

For every finite local alphabet and every connected bounded-degree interaction
graph, almost every unrestricted one- and edge-local Hermitian Hamiltonian has
maximal projective spectral rank. Every reporter then saturates the capacity
allowed by its coherence graph.

**Falsifiers:** a connected graph/alphabet pair with a forced non-trace
rational spectral relation; failure of one physical local witness; external
literature already proving an equal or stronger theorem.

### C3 — thermodynamic temporal-growth law

For generic finite-range interactions, temporal carriers of a separating
finite-region observer net form an inverse system whose finite-volume
dimensions grow maximally. At any fixed nonzero resolution, the physically
activated dimension grows with the observer's causal volume rather than
jumping instantaneously to the exact infinite-volume value.

**Falsifiers:** generic local symmetries forcing submaximal rank density;
failure of compatible restriction maps; a resolution definition that is not
stable under experimental noise or Lieb--Robinson approximation.

### C4 — horizon as completion defect

A gravitational horizon is not characterized by pure-point versus continuous
spectrum. Instead, its operational invariant is the failure of the global
temporal completion to descend faithfully to the exterior observer algebra.
Black-hole entropy should be recoverable as a finite-resolution growth law of
the fibers or defect between those completions.

**Falsifiers:** horizonless systems with the same functorial defect after
locality and gauge constraints are fixed; black-hole models with faithful
descent but nonzero entropy; dependence on arbitrary representation or probe
normalization.

`C4` is deliberately wild and currently has no proof route. It is not a paper
claim.

## Arrow-of-time correction

Frequency rank and spectral nonreturn do not orient time. A reversible system
can have continuous spectrum and zero-density returns with no preferred
direction. The arrow requires an asymmetric record or intervention structure.

A separate conjectural invariant compares minimal future-predictive and
past-retrodictive completions. Their inequivalence, not temporal dimension
alone, is the candidate operational arrow. This has close parents in causal
states, quantum Markov order, process tensors, and entropy production; no
novelty is assigned without an exact comparison theorem.

## External occupied territory

The following cannot be claimed as discoveries:

- Kronecker factors and maximal equicontinuous factors;
- Pontryagin duality and dense rotations on compact abelian groups;
- Koopman/Krylov observable closure and delay realization;
- Mori--Zwanzig memory generated by projection;
- minimal predictive causal states;
- observer- or instrument-dependent quantum Markov order;
- Page--Wootters and quantum-reference-frame relational time;
- generic statements that interaction, entanglement, or memory makes time
  emerge.

Recent direct collision pressure includes Liu--Xiu (2026), who prove
minimal-order closure and delay representations for observed linear dynamics;
Shalizi--Crutchfield, who prove minimality and uniqueness of causal-state
predictors; and Taranto et al., who prove instrument-specific quantum memory.

Candidate novelty can survive only in the exact conjunction:

1. minimal compact phase carrier equals the dual visible-relation group;
2. its dimension equals observer temporal rank and controls all recurrence
   pushforwards;
3. bounded-degree local interaction generically makes it maximal
   simultaneously for every observer;
4. arbitrary weak coupling causes a proved linear-to-exponential exact
   predictive-dimension transition with a separate finite-resolution
   activation law.

## Research decision

This is presently the strongest coherent explanation of the recurrence,
observer, clock, descent, and hypertranscendence results. It is not yet “what
everybody missed.” That statement becomes defensible only after:

1. proving the universal-property theorem;
2. closing the endpoint-local witness for all \(n,q\);
3. deriving the weak-coupling linear-to-exponential theorem;
4. extending the carrier to countable pure-point and finite contractive
   dynamics;
5. completing a theorem-by-theorem external priority audit;
6. surviving a hostile review that treats “time” as rebranding until the
   minimality and physical consequences are undeniable.
