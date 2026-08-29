# Coefficient-recovering finite-prefix regularization no-go for LI

- **ID:** LI-CAB9
- **Stage:** 3-formalized
- **Type:** THEOREM / ROUTE KILL
- **Source:** `LiEvenCrossCompletedAbelFiniteCriticalPrefixOscillationNoGo.lean` and `LiEvenCrossCompletedAbelSublinearTailRepairNoGo.lean`
- **Statement:** Every nonempty finite packet of genuine critical-line Xi copies retains cofinal linear-size adjacent-current excursions of both signs after arbitrary coefficientwise-recovering adaptive reweighting; no `o(n)` residual can make the regularized current nonnegative in every Li mode.

## Route killed

Exact attempted RH chain:

coefficient-recovering adaptive finite prefix plus `o(n)` residual
`=>` interior completed-Abel current nonnegative in every mode
`=>` LI-CAB5 endpoint nonnegative
`=>` LI-CAB3
`=>` RH.

The theorem kills its first implication for every nonempty finite genuine critical packet. Weights
may be mode-adaptive, unbounded at early modes, and transiently signed. The only constraint is that
each fixed coefficient tends to its genuine value. Repeated zeros and rational phase relations are
allowed.

## Theorem and proof

**[PROVED HERE] Coefficient-recovering regularization no-go.** Let `d > 0`, let `q_i` be any
`d` genuine critical-line Xi resolvent copies, and let `w_m(i) -> 1` for every `i`. Write

`J_n^w = sum_i w_(n+1)(i) Re(flux_n(q_i))`.

Then some `c > 0` has both properties cofinally in `n`:

`J_n^w > c(n+1)` and `J_n^w < -c(n+1)`.

Hence any `R_n` satisfying `J_n^w + R_n >= 0` for every `n` has cofinally
`R_n > c(n+1)`. In particular, no `R_n = o(n)` can make the current nonnegative in every mode.

Proof:

1. Exact algebra writes the weighted packet error as
   `sum_i sin(m omega_i) a_i (w_m(i)-1)`.
2. Each summand tends to zero because `|sin| <= 1` and `w_m(i)-1 -> 0`; finiteness of `Fin d`
   makes the whole error tend to zero.
3. Existing delayed simultaneous recurrence gives the unweighted positive sine packet uniform
   cofinal excursions `> c` and `< -c`, with no independence hypothesis on the frequencies.
4. Eventually the weighted error has magnitude `< c/2`; both cofinal excursion directions survive
   with margin `c/2`.
5. The exact critical-atom sine identity multiplies the packet by `n+1`, producing cofinal linear
   excursions of the actual weighted completed-Abel current.
6. On every negative excursion, all-mode nonnegativity forces `R_n > c(n+1)`, contradicting
   `R_n/(n+1) -> 0`.

All dependencies are already proved in the Lean corpus; no conjectural analytic input is used.

## Lean status

- Module: `GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelCoefficientRecoveringRegularizationNoGo`
- Umbrella: imported by `GaloisForLFunctions.RHTower`
- Main capstone:
  `not_exists_nonempty_finiteCriticalPacket_coefficientRecoveringRegularization_sublinearRepair_all_nonnegative`
- Sharp survivor:
  `cofinal_linear_tail_forced_of_coefficientRegularized_all_nonnegative`
- Direct source check: passed with `lake env lean`
- Targeted module build: passed with `lake build GaloisForLFunctions.RHTower.LiEvenCrossCompletedAbelCoefficientRecoveringRegularizationNoGo`
- Axiom audit for all six exported proof theorems: only `propext`, `Classical.choice`, `Quot.sound`
- Formal lint: no forbidden declaration or reachability failure for this module; repository-wide lint
  remains red on 23 unrelated pre-existing unreachable modules in `RHTower` and `HTGeometry`.

## No-go closure

- **Exact killing mechanism:** finite coefficientwise recovery makes regularization asymptotically
  invisible at packet scale, while simultaneous recurrence supplies a fixed cofinal margin. The Li
  mode factor promotes that margin to linear current excursions.
- **Strongest positive survivor:** any viable LI cancellation must remain genuinely infinite before
  the Li-mode limit, or supply cofinally linear countercurrent. A finite recovered prefix plus an
  `o(n)` remainder is impossible.
- **New insight:** coefficient recovery and finite-prefix decomposition do not commute with Li
  positivity. Transient sign changes, adaptive damping, and arbitrarily slow recovery do not evade
  the obstruction.

## Novelty audit

Corpus search found generalized Li criteria, completed-Abel landing identities, finite critical
packet recurrence, and sublinear-tail no-go results, but no coefficient-recovering adaptive version.
A bounded primary-literature audit covered Freitas on zero-free half-plane Li criteria, Coffey and
Sekatskii on generalized Li coefficients, Gonek on finite Euler-product approximations, and the
Hardy--Littlewood recurrence background. None states this exact adaptive coefficient-recovery
classification. External novelty remains **NOVELTY UNVERIFIED** pending a broader expert audit.

## Log

- 2026-08-29 — corpus-derived LI-CAB9 conjecture fixed with exact RH chain.
- 2026-08-29 — paper proof closed; strongest positive survivor extracted.
- 2026-08-29 — Lean formalization, source check, axiom audit, umbrella wiring, and targeted build completed.
