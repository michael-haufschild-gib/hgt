# Scheduled Laplace transport frontier

- **ID:** squarefree-half-laplace-scheduled-frontier
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** multiplicity-parity-ladder-route.md; diagonal Laplace no-go positive survivor
- **Statement:** Any boundary heat schedule whose late samples are uniformly bounded, whose
  adjacent intervals cover a punctured neighbourhood of zero, and whose coefficient-weighted
  adjacent transport cost is uniformly bounded forces the full boundary heat profile to be bounded
  at zero and is therefore impossible.

## Goal

Classify the heat/pole clocks that cannot rescue the convolution-half scalar after the reciprocal
diagonal was closed.  This is source-pure: the only arithmetic input is the canonical
squarefree-convolution-half coefficient stream at `boundaryExteriorPoint`; no RH or zero-location
assumption enters.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem
  `not_exists_bounded_samples_and_weighted_dense_gaps_of_tendsto_zero`, targeted build green,
  explicit axiom audit passed
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Frozen conjecture

Let `F(x)` be `squarefreeHalfBoundaryLaplaceProfile x`.  Suppose there are `N₀`, `ε > 0`, and
`B,K ≥ 0`, and heat times `τ : ℕ → ℝ`, such that for every `N ≥ N₀`:

1. `0 < τ (N+1) ≤ τ N`;
2. every `0 < x ≤ ε` lies in some `[τ (N+1), τ N]` with `N ≥ N₀`;
3. `‖F (τ N)‖ ≤ K`;
4. the adjacent transport majorant
   `(τ N - τ (N+1)) M(τ (N+1)) ≤ B`, where `M(q)` is a proved first-moment
   majorant for the coefficient stream.

Then `SquarefreeHalfBoundaryLaplaceBoundedAtZero`, contradicting the already formalized Mellin
pole obstruction.  First target uses the existing bounded-coefficient majorant
`M(q) = 1 + exp(q) * 2 * q⁻² * Gamma(2)`.  Stronger target replaces exponent `2` by `16/11`
using `‖a_n‖ ≤ n^(-6/11)`.

## Approach

For `x ∈ [τ (N+1), τ N]`, apply the quantitative Laplace interpolation theorem with
`q = τ (N+1)`.  Triangle inequality adds the bounded sample at `τ N`.  Coverage yields a uniform
bound for every `0 < x ≤ ε`; the existing Mellin theorem then contradicts the zeta pole at one.
Audit the `16/11` refinement separately: it requires a toolchain-verified weighted coefficient
bound and a real-power moment estimate, not a recalled asymptotic.

## Surviving RH-chain edge

Exact half-divisor scalar construction remains open.  This card determines which smoothing clocks
cannot supply its missing local boundedness.  Schedules with unbounded weighted transport cost are
the exact survivors; they are candidates only, not evidence for RH.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** `[PROVED HERE]` Boundary coefficient decay gives the sharp
  first-moment transport exponent `16/11`.  A positive heat clock tending to zero automatically
  crosses every sufficiently small time.  If its boundary samples and normalized adjacent gaps
  were both eventually bounded, interpolation would bound the full heat profile at zero; Mellin
  continuation would then contradict the zeta pole at one.
- **Strongest positive survivor:** Weighted mesh escape law: eventual boundedness of canonical
  boundary samples forces adjacent gaps to escape every eventual
  `O(τ(N+1)^(16/11))` bound.  Thus viable smoothing clocks must be genuinely sparse in this exact
  arithmetic metric.
- **New insight:** Pole-degree growth and heat-time decay decouple completely at sample level.
  Pole clearing supplies bounded samples; only weighted mesh sparsity can prevent those samples
  from controlling the full Mellin profile.  Reciprocal and all comparably dense schedules are not
  candidates for the missing scalar.
- **Status:** dependency-closed paper proof; Lean module
  `GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfLaplaceScheduledNoGo`; direct check and
  targeted build passed; all ten audited public theorems use only `propext`, `Classical.choice`,
  and `Quot.sound`; umbrella-wired; no forbidden declarations.

## Log

- 2026-09-04 — created in Stage 1 after reciprocal diagonal no-go exposed the transport invariant;
  conjecture and RH-chain edge frozen before Lean work.  Proved with stronger arithmetic exponent
  `16/11`, formalized and retired to Stage 5 after axiom audit.
