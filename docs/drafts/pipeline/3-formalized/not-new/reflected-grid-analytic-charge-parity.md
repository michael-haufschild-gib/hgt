# Reflected Grid Analytic Charge Parity

- **ID:** reflected-grid-analytic-charge-parity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../rh-monodromy-weight-mismatch/104-checkpoint-deadends-and-open-routes.md
- **Statement:** If the reflected grid charge weight is an analytic local order, factor-swap invariance of those orders plus reflection symmetry at diagonal fixed germs forces even total charge and trivial level-two deck reduction.

## Goal

Discharge the fixed-square weight condition from the weighted reflected-grid charge theorem when the weight is the vanishing order of a local analytic germ. The square fixed point is then handled by the existing reflection-parity theorem, not by a separate parity assumption.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, consumes `ReflectedGridCharge` and `analyticOrderAt_even_of_reflection`
- [x] 1 → 2  fully-proven: weighted charge parity plus reflection-forces-even-order at diagonal fixed germs
- [x] 2 → 3  formalized: Lean theorems `RHTower.reflectedGridAnalyticCharge_even_of_swap_order_even_fixed`, `RHTower.reflectedGridAnalyticCharge_deckRed_two_eq_one_of_swap_order_even_fixed`, and `RHTower.reflectedGridAnalyticCharge_even_of_swap_order_square_reflection`; `lake build GaloisForLFunctions.RHTower` green; `/tmp` axiom check at project baseline
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Define `reflectedGridAnalyticCharge C F center` by assigning to each collision `x` the local order `(analyticOrderAt (F x) (center x)).toNat`. The non-diagonal contribution pairs by factor swap once local orders are swap-invariant. On the diagonal, `analyticOrderAt_even_of_reflection` supplies evenness from analytic reflection symmetry and finite order.

## Log

- 2026-07-06 — formalized in `formal/GaloisForLFunctions/RHTower/ReflectedGridAnalyticCharge.lean`; umbrella import and generated API/overview updated.
