# Arbitrary-phase observation horizon

- **ID:** bvi-arbitrary-phase-observation-horizon
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** Contributions 005 and 007, exact initial and common-return kernels.
- **Statement:** For every `n,A:ℕ` and real weight `c`, with `N=n+3`, determine whether
  vanishing on `[A,A+2*n+2]` is equivalent to `sieveVariance N c=0`.

## Goal

Resolve the difference between ordered origin observations, reflected common-return
observations, and an arbitrary phase. The proposed universal horizon is `2N-3`
samples. Contribution 007 proves a sharp return-window classification but supplies
no upper bound at arbitrary phases. The conjecture is neither proved nor falsified.

## Established evidence

- 005: first `N-1` observations from the origin determine the entire nonconstant tail.
- 007: at explicit common returns, the complete window kernel is the initial kernel
  plus the reflection defect `H-Σc`; positive radii impose two tail moments.
- For all `N=n+4`, the final normalized triple `(1,-2,1)` produces exactly
  `2N-4` consecutive zeros around the constructed common return, with nonzero
  adjacent values and nonzero variance. This is fully formalized in
  `ReturnWindowTwoMomentKernelsAndSharpZeroBlocks.lean`.
- In `TranslatedWindowStrideAnnihilationAndLcmReturnObservability.lean`:
  - `sievePrefixDiscrepancy_arbitrary_phase_lcm_window_zero_iff` proves full observability on every `sieveLcmPeriod N`-translated return window `[k * L_N - (N-2), k * L_N + (N-1)]` of length `2N - 3`.
  - `exists_two_multiples_in_window_of_le_sub_two` proves that for any starting phase `M₀` and any `1 ≤ d ≤ N - 2`, the window `[M₀ + 1, M₀ + 2N - 3]` contains at least two multiples of `d`, so stride-`d` second differences stay inside the window.
  - `central_single_hit_neighbors_in_window` and `common_multiple_unique_in_window_of_lcm_ge` prove that if `N - 1` or `N` has a single multiple at the window midpoint `M₀ + N - 1`, its coprime neighbor hits `M₀ + N - 2` or `M₀ + N` inside the window, and they share at most one common multiple in the window.
  - `sievePrefixDiscrepancy_arbitrary_phase_three_zero_iff` and `sievePrefixDiscrepancy_arbitrary_phase_four_zero_iff` prove unconditional arbitrary-phase `2N - 3` observability for all `M₀ ∈ ℕ` at `N = 3` and `N = 4`.
- First differences turn a translated zero block into shifted divisor-hit equations.
  For general `N ≥ 5` and off-return phases `M₀ ≢ 0 (mod L_N)`, full rank of the translated `[M₀ + 1, M₀ + 2N - 3]` system remains open.
- Generic periodicity, complete-period covariance and the origin's triangular
  inverse do not close the general `N ≥ 5` off-return gap. The translation closure may have a much larger
  dimension than the original coefficient space; do not conflate them.

## Counting boundary

The return-window kernel, exact lower-bound family and extremal rigidity count
together as contribution 007. A matching uniform upper bound or direct refinement
must not receive a second count for that same package. No credit is assigned here.

## Approach and corpus status

Use symbolic structure of shifted divisor incidence, or find an exact obstruction
and classify its strongest positive survivor. No numerical experiments, no external
research. Refresh the local corpus before new Lean source. Relevant partial deep
audits and all inspected candidate/source-argument counts are recorded on
`docs/drafts/pipeline/3-formalized/bvi-translated-prefix-observability-and-maximal-zero-runs-2026-10-18.md`.
There is no dependency-closed paper proof of this conjecture and no Lean module yet.

## Gates

- [ ] Complete refreshed corpus audit and choose a viable attack.
- [ ] Dependency-closed paper proof or exact obstruction with positive survivor.
- [ ] Formalize the exact surviving statement; named-source and axiom audits.

## No-go closure

The route is open, not retired. If falsified, record the killing mechanism and
extract a sharp corrected horizon, exact phase classification, or another nontrivial
positive invariant. Formalize a dependency-closed survivor before retirement.
