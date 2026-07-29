# Universal quantum recurrence anatomy law

- **ID:** `universal-quantum-recurrence-anatomy-law`
- **Stage:** 3-formalized
- **Type:** UNIVERSAL CLASSIFICATION / RECURRENCE THRESHOLD--CLOCK--OBSERVER LAW
- **Scientific status:** `[LEAN-PROVED]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`;
  priority remains provisional pending independent expert review
- **Source papers:**
  - `docs/drafts/pipeline/4-publication-ready/projective-quantum-recurrence-rate-distortion/main.tex`
  - `docs/drafts/pipeline/4-publication-ready/multiple-elliptic-gamma-rational-rank-dichotomy/main.tex`

## Exact claim

Quantum recurrence has a universal five-level anatomy.

1. **Whether and how much.** For every finite-dimensional complex Hilbert-space
   contraction `T` and state vector `x`, the squared norm `p_T(x)` of the
   peripheral spectral projection is the exact asymptotic return-amplitude
   ceiling: every lower threshold is attained after every prescribed delay,
   and every higher threshold is eventually impossible.
2. **When.** Conditional on a finite normalized surviving spectral packet,
   the logarithm of the least deadline valid for every compatible phase
   spectrum is trapped, with explicit support-linear constants, around the
   pivot-optimized reverse-water information. The same finite convex program
   is parallel-Gaussian rate--distortion.
3. **What an observer sees.** For every finite family of states or observables,
   the exact return displacement is its coherence-graph phase energy. The
   visible relative-phase dimension is exactly `sectors - components`, and the
   corresponding universal return deadline has that graph rank as exponent.
4. **What fixes all long-time recurrence statistics.** For every probability
   energy spectrum, finite or infinite and of arbitrary spectral type, every
   continuous statistic of survival fidelity has a long-time mean. Its
   `n`-th moment is exactly the zero-sum collision mass of `n` independent
   visible energy gaps.
5. **What cannot decide recurrence.** Complete polynomial local Krylov
   geometry and the complete connected Jacobi rule at every depth do not
   decide the global recurrence phase. Neither does the all-orders
   perturbative theory of every bounded continuous spectral observable on a
   fixed compact positive interval. Exact compact moments do restore global
   determinacy.

The five clauses form one decision hierarchy:

```text
evolution -> persistent spectral sector -> surviving weights
          -> observer-visible gap quotient -> global gap-collision law
```

Local polynomial data stop before the final arrow. Global spectral completion
supplies it.

## Internal frontier

- `[CORPUS]` `finiteContraction_returnThreshold_dichotomy`,
  `finiteContraction_exists_return_at_target_before_waterDeadline` in
  `formal/GaloisForLFunctions/RHTower/DissipativeQuantumReturnInformationTransition.lean`.
- `[CORPUS]`
  `universalWeightedFloquetFidelityRecurrenceTime_entropySandwich`,
  `universalWeightedFloquetFidelityRecurrenceTime_rateDistortionSandwich` in
  the projective weighted recurrence modules.
- `[CORPUS]` `finite_quantum_observer_coherence_law`,
  `exists_finiteQuantumObserver_graphRank_distance_recurrence` in the finite
  observer modules.
- `[CORPUS]`
  `spectralReturnMomentMeanReal_tendsto_collisionHierarchy`,
  `exists_tendsto_spectralReturnStatisticMeanReal` in
  `ObserverRecurrenceDistributionLaw.lean`.
- `[CORPUS]` `quantumRecurrenceGlobalCompletionWitness`,
  `globalCompletion_no_completeLocal_recurrenceClassifier`,
  `compactExactMoments_determine_spectrum` in
  `QuantumRecurrenceGlobalCompletionLaw.lean`.

## External frontier

- Bocchieri--Loinger establishes qualitative finite closed recurrence.
- Kotowski--Oszmaniec (2026) gives tight finite closed-system recurrence-time
  bounds and effective-support refinements.
- Gupta--Short (2026) bounds simultaneous finite-system recurrence using
  Diophantine approximation.
- Liu--Zheng (2024/2026 revision) treats recurrence for time-independent
  non-Hermitian open-system descriptions with real discrete spectrum.
- Bourgain--Grünbaum--Velázquez--Wilkening characterizes monitored subspace
  recurrence through operator-valued Schur functions.
- Barbon--Rabinovici and Cotler et al. make late-time recurrence and spectral
  form factors central diagnostics in black-hole models.
- Classical moment-indeterminacy and Jacobi theory supply parent mechanisms,
  not the joined recurrence classification.

No checked source states the five-level joined law or the exact
threshold--water--observer--collision--nonidentifiability hierarchy.

## Hostile attack

### Attack 1: collage

The clauses use different classes: finite contractions, finite pure-point
packets, finite observer families and arbitrary probability measures.

**Resolution:** they are nested layers, not coextensive assertions. A finite
contraction first reduces exactly to a transient plus a finite peripheral
packet; weights solve its minimax clock; an observer quotients the same phase
packet; the arbitrary-measure collision law is the completed global layer.
The manuscript must show this reduction as one diagram and one master theorem.

### Attack 2: “universal” overreach

No quantitative deadline is proved for arbitrary continuous spectra or
thermodynamic limits.

**Resolution:** universality refers to the complete classification hierarchy,
not one finite deadline formula in every spectral phase. Arbitrary spectra
receive the exact long-time distribution law; finite surviving packets
receive the finite deadline. This boundary must be explicit in title,
abstract and theorem.

### Attack 3: rate--distortion category error

The phase allocation is not an operational source code.

**Resolution:** claim exact equality of finite convex programs only.

### Attack 4: local/global no-go is negative

The no-classifier theorem alone is not a physical law.

**Resolution:** positive survivor is the additive gap-collision hierarchy,
which determines every continuous long-time return statistic, plus compact
moment determinacy as the exact boundary.

### Attack 5: black-hole overclaim

Fixed-spectrum theorems do not solve quantum gravity.

**Resolution:** only a certification consequence is claimed: no rule using
only complete perturbative spectral-form-factor jets can universally certify
an exact late-time plateau. Global nonperturbative completion remains
necessary input.

## Verdict

`SURVIVES PRELIMINARY ATTACK`.

## Complete paper proof

Each clause is an exact specialization or conjunction of the listed corpus
theorems. The logical joins are:

1. peripheral/transient spectral decomposition gives clause 1;
2. normalize the nonzero peripheral weights and invoke the water deadline
   sandwich for clause 2;
3. expand every matrix block in energy sectors and quotient one common phase
   per coherence component for clause 3;
4. represent fidelity powers as characteristic functions of convolution
   powers of the gap law, apply symmetric-window sinc convergence, and use
   polynomial approximation on `[0,1]` for clause 4;
5. use the positive-energy indeterminate-moment completion pair and compact
   flat perturbative pair for the obstruction, then compact moment
   determinacy for the boundary.

No implication between different system classes is asserted beyond the
exact finite-contraction reduction to its peripheral packet.

`[PAPER-PROVED]`. Hostile statement audit found no cross-class implication:
each universal quantifier retains its exact domain, and only the proved
finite-contraction peripheral reduction joins two domains.

## Open core

No mathematical open core remains.

## Exact formal capstone

- File:
  `formal/GaloisForLFunctions/RHTower/UniversalQuantumRecurrenceAnatomyLaw.lean`
- Master theorem: `universalQuantumRecurrenceAnatomyLaw`
- Exact fields:
  - `whetherAndHowMuch`
  - `coupledFiniteDeadline`
  - `whenFinite`
  - `whatObserverSees`
  - `observerDeadline`
  - `globalLongTimeStatistics`
  - `spectralPhaseClassification`
  - `localDataDoNotDecide`
  - `compactExactDataDecide`

Foreground verification passed with
`lake env lean GaloisForLFunctions/RHTower/UniversalQuantumRecurrenceAnatomyLaw.lean`.
The scratch axiom report lists only `propext`, `Classical.choice`, and
`Quot.sound`.
