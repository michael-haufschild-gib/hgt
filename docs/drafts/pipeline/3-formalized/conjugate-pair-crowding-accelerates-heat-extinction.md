# Conjugate-pair crowding accelerates heat extinction

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacles:** B13, B112; quantitative survival of finite nonreal heat layers.
- **Statement:** For each `a>0`, an actual-source radius `R>0` exists such that,
  for every `b≥a`, putting `n=N(b)` and `κ=max(n−2,0)/R²`,
  `exp(κ(b−a))[κE(b)+2n]≤κE(a)+2n`.
  Here `E` is the full multiplicity-weighted squared-depth energy and `N`
  the nonreal zero count. No initial energy or zero confinement is assumed.
- **Contribution count:** 11; finite-packet coercivity, actual-divisor transfer,
  collision comparison, and the survival corollary count together.
- **Novelty boundary:** Existing elapsed-depth moments discard the interaction
  magnitude of distinct pairs. This candidate retains it; it does not claim
  an RH proof or an initial-time confinement estimate.

## Proof

1. The pair force for constant spatial weight is `−4(y_i−y_j)²/|z_i−z_j|²`.
   Each nonreal self-reflected ordered pair contributes exactly `−4`.
   Every remaining squared distance is at most `4R²`.
2. Conjugation gives `Σy_i=0`. Thus the full ordered squared-gap sum is
   `2mE`, where `m` counts all packet zeros. Removing reflected pairs leaves
   `2(m−2)E`. Division by two for unordered forces proves
   `packet drift≤−2N−(m−2)E/R²`. Real zeros also increase the damping rate.
3. The even order-one partial fraction expansion and the removable simple
   logarithmic pole identify actual velocities. All real exterior work is
   nonpositive. At simple times the packet has `m≥N`, giving
   `E′≤−2N−(N−2)E/R²`.
4. The corpus supplies uniform nonreal confinement after every `a>0`,
   continuity of `E`, and a simple forward interval after every positive
   time. Fix `b≥a`. If `n≤2`, then `κ=0` and the statement is equality.
   Otherwise count monotonicity yields `E′+κE+2n≤0` on each regular interval.
5. The integrating factor `exp(κ(s−a))(κE(s)+2n)` has nonpositive derivative
   there. Forward-interval comparison passes through all collisions and
   proves the displayed bound. Nonnegative final energy also gives
   `2n(exp(κ(b−a))−1)≤κE(a)`.

## Lean certificate

Paths are relative to `formal/GaloisForLFunctions/ArithmeticElectrostatics/`.

| Module | Capstone |
|---|---|
| `ConfinedZeroPacketsDissipateFaster.lean` | `heatPacketPairDrift_le_crowding` |
| `TheHeatDivisorPaysForCrowding.lean` | `heatGlobalPacket_crowding_drift_le` |
| `TheHeatDivisorPaysForCrowding.lean` | `exists_heat_crowding_exponential_budget` |
| `TheHeatDivisorPaysForCrowding.lean` | `exists_heat_crowding_survival_budget` |

Both modules pass direct `lake --old env lean` checking without warnings.
All displayed capstones have only `propext`, `Classical.choice`, and
`Quot.sound` as transitive axioms. Both modules are wired into their umbrella.

The rate is positive when at least two upper pairs survive. No uniform bound
on `R` as `a→0` is proved, so this does not exclude a finite initial off-line
layer or establish RH.
