# Infinite local agreement with opposite quantum recurrence

- **ID:** infinite-local-agreement-opposite-quantum-recurrence
- **Stage:** 5-failed
- **Type:** RETIRED AS PAPER ANCHOR; THEOREM RETAINED
- **Source:** hostile Nature novelty audit of finite-jet recurrence separation
- **Statement:** A continuous-spectrum clock and an integer-spectrum clock can have identical survival amplitudes on an open time interval, yet at one later tick the lattice clock returns exactly while the continuous clock is orthogonal to its initial state.

## Goal

Replace every-finite-order moment separation by exact open-interval
indistinguishability. Construct a nonzero compactly supported smooth packet
`u`, its compactly supported autocorrelation `g`, continuous energy density
`𝓕 g = |𝓕 u|²`, and lattice weights `(𝓕 g)(n)`. Poisson summation should make
the continuous and lattice survival amplitudes equal wherever only the
central periodized copy of `g` is visible. At the lattice period, periodicity
gives amplitude one while support makes the continuous amplitude zero.

## Gates

- [x] 0 → 1 in-progress: exact construction isolated; existing Schwartz Fourier, autocorrelation and Poisson modules found
- [x] 1 → 2 fully-proven: paper proof, positivity, normalization, open-interval equality and return/orthogonality separation
- [x] 2 → 3 formalized: unconditional capstones in `InfiniteLocalRecurrenceSeparation.lean`
- [ ] 3 → 4 publication-ready: blocked by direct prior art and physical-spectrum weakness

## Approach

1. Scale the canonical compactly supported Schwartz cutoff into a packet
   supported in a strict subinterval of one lattice cell.
2. Form its autocorrelation; prove compact support and positive center.
3. Use the existing Fourier autocorrelation identity to obtain a nonnegative
   Schwartz energy density and nonnegative integer samples.
4. Use Schwartz Poisson summation to identify the periodization of the local
   autocorrelation with the discrete survival Fourier series.
5. Normalize at zero; support kills every noncentral translate locally.
6. At one full lattice period, the discrete amplitude equals one and the
   continuous amplitude equals zero.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** Hsu (1954), *On characteristic
  functions which coincide in the neighborhood of zero*, directly
  establishes the underlying probability phenomenon. The construction also
  requires two-sided spectra, so it does not furnish bounded-below quantum
  Hamiltonians.
- **Strongest positive survivor:** finite-dimensional, nonnegative-spectrum
  clocks whose complete survival records are arbitrarily close on every
  strict pre-return window but end at exact return versus exact
  orthogonality.
- **New insight:** Exact open-interval equality is not novel, but forcing
  maximal later separation while retaining finite dimension, a shared
  bounded-below Hamiltonian, every positive time scale, every strict
  observation horizon, and every positive noise level produces a stronger
  operational survivor.
- **Status:** retired as novelty anchor; theorem retained as sharp
  infinite/two-sided boundary case.

## Log

- 2026-07-28 — created directly in stage 1 after hostile novelty audit exposed the finite-jet theorem as vulnerable to classical truncated-moment prior art.
- 2026-07-28 — construction completed and formalized. Hostile novelty search
  found Hsu's 1954 direct collision; bounded-below physical interpretation
  also fails. Moved to failed with positive survivor extracted.
