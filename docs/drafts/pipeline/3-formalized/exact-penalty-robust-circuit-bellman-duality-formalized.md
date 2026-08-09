# Exact-penalty robust circuit Bellman duality — formalized closure

- **ID:** `exact-penalty-robust-circuit-bellman-duality-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `./exact-penalty-robust-circuit-bellman-duality.md`
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [BRIDGE]`

## Lean module

`GaloisForLFunctions.HTGeometry.ExactPenaltyCircuitBellman`
(umbrella: `GaloisForLFunctions.HTGeometry`).

The gate family is a topological index type `Γ` acting by isometries `act : Γ → X → X` with an
inverse assignment `inv : Γ → Γ`.  Finite alphabets and compact continuous gate families are both
instances; compactness is used only where the paper uses it, namely for Theorem C.

## Formal theorem chain

Definitions: `wordAct` (head of the list is the last gate), `reachSet` `(2)`, `layerDist` `(2)`,
`approxComplexity` `(3)`, `wordCost` and `penaltyValue` `(4)`, `IsBellmanSubsolution` `(9)`.

**Theorem A**
1. `penaltyValue_le_wordCost`, `le_penaltyValue`, `penaltyValue_nonneg` — the value is the
   infimum of the word costs and is nonnegative.
2. `penaltyValue_le_add_dist`, `lipschitzWith_penaltyValue` — `V` is `λ`-Lipschitz.
3. `act_inv_inv`, `dist_act_left`, `wordCost_cons` — the exact last-gate identity `(8)`.
4. `penaltyValue_eq_min` — the Bellman equation `(5)`.
5. `penaltyValue_le_of_reachable` — the bound `(6)`.
6. `penaltyValue_le_one_add_inv`, `penaltyValue_le_one_add`,
   `abs_penaltyValue_act_sub_le_one` — the unit gate step `(7)`.

**Theorem B**
7. `IsBellmanSubsolution.le_wordCost`, `IsBellmanSubsolution.le_penaltyValue`,
   `isBellmanSubsolution_penaltyValue` — every subsolution is dominated by `V`, and `V` is one.
8. `penaltyValue_isGreatest`, `penaltyValue_isGreatest_lipschitz` — the duality `(10)`, also after
   restricting to `λ`-Lipschitz subsolutions.

**Theorem C** (compact gate family, continuous evaluation)
9. `reachSet_zero`, `reachSet_succ`, `isCompact_reachSet`, `exists_dist_eq_layerDist` — every
   reachable layer is compact, so the layer distance is attained.
10. `lt_layerDist_of_lt_approxComplexity` — below the complexity every layer stays strictly
    outside the slack ball, so the denominators of `(12)` are positive.
11. `penaltyThreshold` `(12)`, `le_penaltyThreshold`,
    `penaltyValue_eq_approxComplexity`, `penaltyValue_eq_approxComplexity_of_penaltyThreshold_le`
    `(13)`, and `penaltyValue_eq_zero_of_approxComplexity_eq_zero` (the `c = 0` clause).
12. `approxComplexity_isGreatest` — equation `(14)`: approximate circuit complexity is the largest
    value at `x` of a Bellman subsolution at some nonnegative penalty, attained at the finite
    threshold.  This is the exact statement behind the corollary that the calibration-existence
    route is circular.

**Certificate condition number** (used by the child card)
13. `le_lipschitzConstant_of_certificate`,
    `le_mul_lipschitzConstant_of_certificate_of_linear_approach`.

## Verification

- `lake env lean GaloisForLFunctions/HTGeometry/ExactPenaltyCircuitBellman.lean` — clean, no
  warnings.
- `lake build GaloisForLFunctions.HTGeometry.ExactPenaltyCircuitBellman` — green.
- `#print axioms` on all thirteen groups: `propext`, `Classical.choice`, `Quot.sound` only.
- Umbrella import present.

## Gates

- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready

The open core `C3` (an external reuse-sensitive Bellman subsolution) is a research gate on the
parent card, not formalization debt.
