# Reflected Grid Completed Charge Parity

- **ID:** reflected-grid-completed-charge-parity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../rh-monodromy-weight-mismatch/104-checkpoint-deadends-and-open-routes.md
- **Statement:** For the concrete completed finite carrier `completedGN N`, a reflected grid-center assignment paired by `s ↦ 1-s`, lying in the strip with diagonal center `1/2` and finite local orders, has even reflected analytic charge and trivial level-two deck reduction.

## Goal

Instantiate the analytic reflected-grid charge package with the actual completed AFE carrier rather than an abstract analytic germ family. This proves that the completed carrier supplies the parity side of the saddle-grid charge bridge once the remaining geometric center assignment is provided.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, consumes `completedGN_orderAt_one_sub` and local reflection parity
- [x] 1 → 2  fully-proven: local reflection parity for analytic germs plus completed-carrier FE order equivariance
- [x] 2 → 3  formalized: Lean theorems `RHTower.analyticOrderAt_even_of_reflection_eventually`, `RHTower.completedGN_eventually_reflection_half`, `RHTower.reflectedGridCompletedCharge_even_of_center_swap`, and `RHTower.reflectedGridCompletedCharge_deckRed_two_eq_one_of_center_swap`; `lake build GaloisForLFunctions.RHTower` green; `/tmp` axiom check at project baseline
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

First localize reflection parity from an entire-function theorem to an analytic germ theorem: eventual equality `f(2c-s)=f(s)` near `c` forces even finite local order. Then instantiate `reflectedGridAnalyticCharge` with `completedGN N`. Off-diagonal order-swap invariance comes from `completedGN_orderAt_one_sub`; the diagonal fixed point uses `completedGN_one_sub` near `1/2`.

## Log

- 2026-07-06 — formalized in `formal/GaloisForLFunctions/RHTower/ReflectedGridCompletedCharge.lean`, with the local reflection theorem added to `formal/GaloisForLFunctions/RHTower/ReflectionParity.lean`; umbrella import and generated API/overview updated.
