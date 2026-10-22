# Infinite-jet quantum recurrence separation law

- **ID:** `infinite-jet-quantum-recurrence-separation-law`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / LOCAL-TIME–GLOBAL-MEMORY SEPARATION
- **Lane:** quantum recurrence; observer time; indeterminate Hamburger moments
- **Scientific status:** `[CONJECTURED HERE] [PARTLY PROVED IN CORPUS] [NOVELTY UNVERIFIED]`
- **Working headline:** **Two quantum clocks can agree to every order now and disagree forever**

## Question

Does complete local knowledge of a stationary quantum clock at one instant determine whether the
clock retains recurrent memory at long times?

“Complete local knowledge” means the survival amplitude and every one of its derivatives at the
present instant, equivalently every energy moment. “Recurrent memory” is measured by the
long-window mean survival fidelity and by the density of fixed-fidelity return times.

## Conjectural jump

For every normalized positive-definite indeterminate Hamburger moment sequence `s`, there are two
probability spectral measures `mu_pp` and `mu_c` such that:

1. both have moment sequence `s`;
2. their characteristic functions have identical derivatives of every finite order at time zero;
3. `mu_pp` is carried by a countable closed discrete spectrum, so its observer temporal dimension
   is at most countable;
4. `mu_c` is atomless, so its observer temporal dimension is exactly continuum;
5. the long-window mean survival fidelity of `mu_pp` converges to a strictly positive spectral
   collision mass;
6. the long-window mean survival fidelity of `mu_c` converges to zero;
7. for every fixed positive fidelity threshold, the return-time density of `mu_c` converges to
   zero.

Thus no complete instantaneous Taylor law, no complete energy-moment hierarchy, and no collection
of local quantum-speed quantities derived from them determines the global recurrence phase or the
observer's temporal dimension.

## Candidate universal law

> **Complete local time data do not determine global temporal memory.**
>
> In every normalized indeterminate energy-moment class, one stationary quantum clock can have
> persistent mean recurrence while another has asymptotically vanishing mean recurrence, although
> their survival amplitudes agree to every derivative order at the present instant. The two clocks
> can simultaneously occupy the only two possible uncountable temporal-cardinality regimes:
> at-most-countable and continuum.

The quantifier is “every indeterminate moment class,” not “some engineered example.” The theorem
must also include an explicit nonempty physical realization class before it can anchor a paper.

## Why this is a jump rather than a finite-data loophole

The existing theorem `finiteJet_quantumClock_separation` proves separation after every prescribed
finite jet. A reviewer can dismiss that result because the missing next derivative may encode the
future. Here no derivative is missing: the entire infinite jet agrees. The failure occurs because
the survival amplitudes are smooth but nonanalytic at the observation instant.

## Existing theorem parents

- Classical indeterminate Hamburger moment theory: distinct measures may have all moments equal.
- Classical Nevanlinna theory: every indeterminate moment class has countable pure-point
  N-extremal leaves and atomless barycentres.
- Wiener mean-square law: asymptotic mean fidelity equals spectral collision mass.
- Characteristic-function Taylor theorem: the `n`th derivative at zero is `i^n` times the `n`th
  moment.
- Corpus:
  - `NevExtremalFamily.lean`
  - `NevanlinnaBoundaryKernel.lean`
  - `NevFiberCountable.lean`
  - `NevLeafFunction.lean`
  - `ObserverTemporalDimensionLaw.lean`
  - `FiniteJetRecurrenceSeparation.lean`

None of those ingredients alone is the proposed result. Novelty can reside only in the exact
all-order local-time / recurrence-phase / temporal-cardinality synthesis and its physical
consequences. A priority search must test that synthesis directly.

## Falsifiers

Retire or weaken the conjecture if any of the following occurs:

1. a normalized positive-definite bounded-kernel moment sequence can lack an atomless representing
   probability;
2. a countably carried probability can have zero spectral collision mass;
3. all Hamburger moments do not suffice for all characteristic-function derivatives at zero;
4. the claimed temporal-dimension jump fails for the chosen measures;
5. existing literature already states the same all-orders quantum recurrence-phase separation;
6. no semibounded or otherwise physically credible Hamiltonian class realizes the separation;
7. the result produces no falsifiable consequence beyond a classical moment-problem restatement.

## Immediate proof obligations

1. Build an atomless projective parameter probability without a local-instance leak.
2. Prove every `HasHamburgerMoments` measure has `MemLp id n` for every natural `n`.
3. Derive equality of every characteristic-function derivative at zero.
4. Prove a finite Nevanlinna leaf is not atomless from countable carriedness and probability mass.
5. Deduce strictly positive collision mass and the two incompatible mean-return limits.
6. Couple the countable/continuum temporal-dimension conclusions.
7. Supply a physically credible self-adjoint Hamiltonian realization, preferably semibounded.
8. Audit exact novelty across moment problems, quantum recurrence, Loschmidt amplitudes, quantum
   speed limits, and the problem of time.

## Nonclaims

- The theorem does not say an exact survival-amplitude record on a time interval is insufficient.
- It does not say bounded spectra admit this ambiguity; compact support makes the moment problem
  determinate and the characteristic function analytic.
- It does not predict a black-hole recurrence time or establish a cosmological arrow of time.
- It does not make formal verification part of novelty or scientific significance.
- It does not identify the actual spectral type of any experimental platform without measurement.

## Physics gate

A Nature-level paper needs more than the abstract theorem. It must derive a concrete consequence
for a live physical question. Candidate target:

> Any recurrence forecast inferred solely from all local energy moments, all local survival
> derivatives, quantum speed limits, or their finite combinations is non-universal for unbounded
> spectra. Global spectral regularity is an independent physical datum.

The paper must show how this changes interpretation or experimental design for quantum clocks,
Loschmidt echoes, many-body revivals, or entropy-based recurrence estimates. Black-hole or
cosmological language is allowed only as a rigorously scoped consequence of missing global spectral
information, never as an asserted model of real gravity.

## Log

- 2026-07-28 — Conjecture frozen after rejecting finite-order recurrence separation as too weak.
  Located unconditional Nevanlinna pure-point and atomless carriers in the existing corpus, the
  characteristic-function all-derivative theorem in mathlib, and the universal collision-mass
  return law in `ObserverTemporalDimensionLaw.lean`.
