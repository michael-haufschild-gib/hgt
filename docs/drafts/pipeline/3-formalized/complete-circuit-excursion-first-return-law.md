# Complete-circuit excursion first-return law

- **Stage:** 3 -- formalized in Lean 4
- **Status:** `[FORMALIZED] [SAME DRAW] [NOVELTY UNVERIFIED]`
- **Date:** 2026-08-21

## New theorem

Let one continuous static-Hamiltonian Choi orbit have a closed finite circuit-capture set

`S_eps = {t : exists depth-s circuit w, D_tr(Psi(t),w) <= eps}`.

If `[u,u+W]` avoids `S_eps` and the same orbit visits `S_eps` on both sides, compactness selects the
last capture `t_exit <= u` and first later capture `t_return >= u+W`.  They satisfy

`t_return - t_exit >= W`

and there is no capture by **any** depth-`s` circuit at an intermediate time.  Thus `t_return` is a
literal first re-entry to the entire circuit set, not a recurrence statement about the initial
state alone.

For a maximally projective finite-spectrum Hamiltonian, identity-channel recurrence is syndetic.
The completed-occupation hard-block theorem therefore supplies both bracketing visits
automatically.  Its explicit width condition is retained:

`b < mesh/(W+mesh)`, `mesh=(eps_w-eps_n)/projectiveChoiSpeed(E)`.

For every parameter in the ordinary nearest-neighbour Gaussian growth-maximal event, one fixed
Hamiltonian simultaneously has the existing robust laboratory ramp and these arbitrarily late,
quantitative complete-circuit first-reentry gaps.  No redraw occurs.

## Lean certificate

- `HTGeometry/ContinuousFirstReturnGapLaw.lean`
  - `exists_consecutive_mem_separated_by_avoided_Icc`
- `RHTower/StaticChoiCircuitExcursionFirstReturnLaw.lean`
  - `isClosed_finite_pureStateTraceDistance_captureTimeSet`
  - `maximallyProjective_pureChoiRecurrence_syndetic`
  - `maximallyProjective_pureChoiCircuitTarget_consecutiveVisitGaps`
  - `maximallyProjective_pureChoiCircuitTarget_explicit_consecutiveVisitGap`
- `RHTower/NearestNeighborGaussianSameDrawCircuitExcursionFirstReturnLaw.lean`
  - `nearestNeighborPath_sameDraw_growth_consecutiveCircuitFirstReturnGaps`
  - `nearestNeighborPath_sameDraw_growth_explicitConsecutiveCircuitFirstReturnGap`

All modules are umbrella-wired.  Targeted source checks pass.

## Hostile boundary

This closes the logical gap between a late hard block and first re-entry to the **complete** circuit
set.  It does not prove that the departure is the initial `t=0` departure, control the first plateau
onset, or connect every intermediate time from the laboratory ramp to the late plateau.  Those are
exactly the autonomous Bellman-escape problem; no Brown--Susskind completion is claimed.
