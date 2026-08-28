# Vanishing-tail recurrence-exponent instability law

- **ID:** `vanishing-tail-recurrence-exponent-instability-law`
- **Stage:** 4-publication-ready
- **Type:** THEOREM / LOCAL QUANTUM RECURRENCE / PREPARATION INSTABILITY
- **Date:** 2026-08-28
- **Status:** `[LITERATURE-FIRST] [CORPUS-GAP] [PAPER-PROVED] [LEAN-CLOSED] [INTEGRATED]`

## Goal

Determine whether exact all-state support stratification has a physically sharp finite-resolution
consequence.  Strong target: one unchanged static nearest-neighbour Hamiltonian should admit pure
states arbitrarily close to an eigenstate whose scalar survival signals remain uniformly close for
all laboratory times, while exact high-accuracy first-return exponent jumps from zero to maximal.

## Literature boundary checked first

- Kotowski--Oszmaniec (arXiv:2601.10409v3, 11 August 2026), Eq. (16), show that deleting a tail of
  probability mass `delta` changes the state orbit by at most `2 sqrt(delta)` in trace distance at
  every time and use effective support for deterministic recurrence upper bounds.  They do not
  prove an exact asymptotic exponent, discontinuity of that exponent, a generic local-family lower
  law, or one-Hamiltonian state-preparation instability.
- Gupta--Short (arXiv:2604.14995v2) prove all-state deterministic recurrence upper bounds.  They do
  not classify exact state-support exponents or their stability under preparation error.
- Monitored first-detection recurrence has quantized mean return times and pointwise discontinuity
  at phase resonances or dark-state boundaries (Grünbaum et al.; Yin et al.).  That protocol inserts
  repeated measurements and concerns mean detected return.  Present target is unmeasured continuous
  survival fidelity and its first post-cutoff high-accuracy return.
- Fidelity-stability and Loschmidt-echo literature studies Hamiltonian perturbations, decay and
  semiclassical regimes, not uniform all-time scalar closeness with different unmeasured recurrence
  exponents under initial-state perturbation.
- Exact web searches for `recurrence exponent` with state perturbation, spectral support,
  preparation error, uniform closeness and discontinuity found no matching statement as of
  28 August 2026.  This is absence evidence, not proof of priority.

## Corpus boundary

`scripts/formal_tools.py research` found:

- exact all-state exponent classification in
  `AllStateSpectralSupportRecurrenceLaw.lean`;
- exact-tail finite recurrence upper bounds in
  `FiniteLocalizedSpectralSupportRecurrenceLaw.lean`;
- spectral-weight and physical-orbit bridges in `SpectralOrbitWindowBridge.lean`;
- no theorem on continuity or discontinuity of first-return exponent under state preparation, no
  vanishing-tail activation theorem, and no uniform-all-time scalar-history instability capstone.

## Conjecture C1: vanishing-tail activation

Let `D >= 3` and let `E_1 < ... < E_D` be an all-support Diophantine-good spectrum: for every
subset of at least three levels, its anchored gap-ratio vector is not very well approximable.  Fix
an anchor level `a`.  For `0 < eta < 1`, define

\[
 u_j=\frac1D,
 \qquad
 p_j^{(\eta)}=(1-\eta)\mathbf 1_{j=a}+\eta u_j.
\]

Then:

1. `p^(eta)` is a strictly positive probability vector and therefore has exact support `D`.
2. It is realized by normalized pure state
   \[
   \psi_\eta=\sum_j\sqrt{p_j^{(\eta)}}\,e_j.
   \]
   Its fidelity with anchor eigenstate obeys
   \[
   |\langle e_a,\psi_\eta\rangle|^2
   =1-\eta+\eta/D\ge1-\eta,
   \]
   so trace distance is at most `sqrt(eta)`.
3. For every real time,
   \[
   0\le 1-|\langle\psi_\eta,e^{-itH}\psi_\eta\rangle|^2\le4\eta.
   \]
   Thus entire scalar survival history is uniformly `4 eta`-close to stationary eigenstate
   history, not merely close on one finite window.
4. For every fixed resolution `delta > 4 eta` and every cutoff `t0`, the state never exits that
   return window and its return functional is exactly `T_(eta)(delta)=t0`.
5. For every fixed `eta>0` and every positive cutoff,
   \[
   \lim_{\delta\downarrow0}
   \frac{\log T_{\eta}(\delta)}{\log(1/\delta)}=\frac{D-2}{2}.
   \]
   Anchor eigenstate has exponent zero.

Consequently finite-resolution and exact-resolution limits do not commute.  Arbitrarily small
spectral tail is invisible at every time above its amplitude scale yet activates every projective
phase direction and maximal asymptotic recurrence exponent.

## Paper proof of C1

### Probability and pure-state realization

Uniform packet sums to one.  Hence convex mixture `p^(eta)` sums to one.  Since `eta/D>0`, every
coordinate is positive.  Orthonormality gives

\[
 \langle e_k,\psi_\eta\rangle=\sqrt{p_k^{(\eta)}},
 \qquad
 \|\psi_\eta\|^2=\sum_kp_k^{(\eta)}=1.
\]

At anchor, squared overlap is `p_a^(eta)=1-eta+eta/D`, proving state-fidelity and trace-distance
bounds.

### Uniform all-time signal bound

Put `z_j(t)=exp(-itE_j)` and `U(t)=D^(-1) sum_j z_j(t)`.  Each `|z_j|=1`, so triangle inequality
gives `|U(t)|<=1`.  Survival amplitude is

\[
 A_\eta(t)=(1-\eta)z_a(t)+\eta U(t).
\]

It is a convex combination of points in closed unit disk, hence `|A_eta(t)|<=1`.  Moreover

\[
 |A_\eta(t)-z_a(t)|
 =\eta|U(t)-z_a(t)|\le2\eta.
\]

Reverse triangle inequality and `|z_a|=1` give

\[
 1-|A_\eta(t)|\le|A_\eta(t)-z_a(t)|\le2\eta.
\]

Therefore

\[
 0\le1-|A_\eta(t)|^2
 =(1-|A_\eta(t)|)(1+|A_\eta(t)|)
 \le4\eta.
\]

If `delta>4 eta`, every `t>=t0` belongs to return set, whose infimum is `t0`.

### Exact exponent

Strict positivity makes support size exactly `D`.  Apply all-state support theorem to fixed
all-support-good spectrum.  This gives exponent `(D-2)/2` for every fixed positive `eta`.  At
`eta=0`, state is eigenstate and fidelity is identically one, hence exponent zero.  No uniform
Diophantine constant in `eta` is used.

## Strong local-many-body capstone

For `n,q>=2`, `D=q^n`, on every nonempty preconnected open simple-spectrum chart of full real
onsite-plus-nearest-neighbour `n`-qudit path coefficient family, one conull Hamiltonian set obeys C1
simultaneously for every anchor eigenlevel, every `0<eta<1`, every positive cutoff and every
resolution above `4 eta`.  Same Hamiltonian also obeys all-state support law.  Thus arbitrarily
small preparation contamination activates maximal exponent `(q^n-2)/2`, exponentially large in
path length, while remaining uniformly invisible to scalar survival at coarser resolution for all
time.

## Hostile audit

1. **Not a finite-horizon trick.** Uniform deficit bound holds for every real time.
2. **Not monitored recurrence.** No intermediate measurement occurs; observable is ordinary
   survival fidelity.
3. **Not Hamiltonian instability.** Hamiltonian is unchanged.  Only initial state changes.
4. **No contradiction with effective support.** Effective support correctly controls every fixed
   coarse resolution.  Exact support controls `delta -> 0`; theorem proves two limits differ.
5. **No state-uniform onset claim.** Onset may diverge as `eta -> 0`; this is mechanism, not gap.
6. **Pure state, not classical mixture.** Square-root amplitudes realize weight packet in energy
   eigenbasis.
7. **Genericity visible.** Maximal exponent is almost-everywhere local statement, not every local
   Hamiltonian.  Uniform `4 eta` signal bound is deterministic for every finite spectrum.
8. **Experimental meaning.** Finite precision can falsify predicted envelope or resolved slope,
   but cannot certify exact zero population.  The theorem predicts crossover under deliberately
   injected spectral tail.

## Novelty verdict

Survives literature and corpus search as a new conjunction.  Individual ingredients—effective
support continuity, monitored-return discontinuity, Diophantine recurrence and pure-state spectral
weights—are known separately.  Candidate novelty is exact horizon-free preparation instability of
unmeasured physical first-return exponent, with maximal activation on one generic static local
Hamiltonian and an explicit finite-resolution/no-exit versus exact-resolution dichotomy.

## Formal closure

Module:
`formal/GaloisForLFunctions/HTGeometry/VanishingTailRecurrenceExponentInstabilityLaw.lean`

Load-bearing declarations:

- `anchorDopedWeights_pos`, `sum_anchorDopedWeights`,
  `spectralWeightSupport_anchorDopedWeights`;
- `spectralReturnDeficit_anchorDopedWeights_le`;
- `fidelityReturnTime_anchorDopedWeights_eq_cutoff`;
- `finiteComplexInner_spectralStateOfWeights_self`,
  `finitePureStateFidelity_anchorDopedState`;
- `tendsto_log_orbitFidelityReturnTime_anchorDopedState`;
- `ae_vanishingTailPreparationInstability_sortedSpectrum`;
- `quditPathVanishingTailPreparationInstabilityLaw_of_two_le`;
- `universalQuditPathVanishingTailPreparationInstabilityLaw`.

Audits:

- direct `lake env lean` source check passed;
- targeted `lake build
  GaloisForLFunctions.HTGeometry.VanishingTailRecurrenceExponentInstabilityLaw` passed;
- source contains no `sorry`, `admit`, `axiom`, `opaque` or `unsafe` declaration;
- `#print axioms` on abstract, physical, chartwise and unconditional capstones reports only
  `[propext, Classical.choice, Quot.sound]`;
- module is imported by `GaloisForLFunctions/HTGeometry.lean`; umbrella was not built.

## Paper integration

Integrated as Corollary `Vanishing-tail activation and resolution singularity` of all-state
support law, not as independent fifth law.  Abstract, public summary, proof appendix, literature
position, claim trace, hostile review and experiment section now state exact finite-resolution
versus exact-resolution boundary.  Publication PDF compiles without undefined references or
layout warnings.

## Log

- 2026-08-28 — literature checked before conjecture; effective-support and monitored-return
  boundaries isolated.
- 2026-08-28 — wide corpus searches found reusable all-state/support infrastructure and no matching
  instability theorem.
- 2026-08-28 — C1 paper proof completed; hostile audit passed; formalization open.
- 2026-08-28 — abstract and physical-state theorem closed in Lean; generic static local qudit-path
  capstone discharges locality and simple-chart existence.
- 2026-08-28 — targeted source/build and axiom audits passed; module wired without umbrella build.
- 2026-08-28 — theorem integrated into unified manuscript and deliberate-tail experimental
  crossover protocol; 51-page PDF compiled and visually audited.
