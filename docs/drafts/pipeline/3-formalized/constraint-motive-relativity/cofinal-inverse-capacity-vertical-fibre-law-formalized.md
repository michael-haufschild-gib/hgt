# Cofinal inverse-capacity and vertical-fibre law — Lean certificate

- **ID:** `cmr-cofinal-inverse-capacity-vertical-fibre-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `cofinal-inverse-capacity-vertical-fibre-law.md` (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean modules

| Module | Content |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/CofinalInverseCapacity.lean` | stage filling norm, cofinal port tower, limiting filling seminorm, vertical-fibre identity, closability criterion, scalar dichotomy |
| `formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/CofinalInverseCapacityHilbert.lean` | Gram operator, inverse capacity, minimum-norm lift, monotonicity, limiting inverse capacity `Q_∞` |
| `formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/AugmentationPortCapacity.lean` | the augmentation port of an orthonormal family (prime-port instantiation) |

All three are imported by the area umbrella `GaloisForLFunctions.HTGeometry`.

Namespace: `HTGeometry.ConstraintMotiveRelativity`.

## Formal statement chain

1. `portFillNorm T S y` — `(IC.1)`, the least norm of a lift of `y` inside the port stage `S`,
   with `portFillNorm_nonneg`, `portFillNorm_le`, `portFillNorm_antitone`, `portFillNorm_zero`,
   `portFillNorm_add_le`, `portFillNorm_smul`.
2. `PortTower T` — a monotone exhaustion `stage : ℕ → Submodule 𝕜 X` with
   `⨆ n, stage n = T.domain` and eventual surjectivity `filling`.
3. `PortTower.fillNormInf` — `q_∞`, with `PortTower.tendsto_fillNorm` (the stage norms decrease to
   it) and `PortTower.fillSeminorm : Seminorm 𝕜 Y`, the seminorm claim of Theorem 1.1.
4. `PortTower.exists_fillNorm_bound` — the uniform bound `q_k(y) ≤ C ‖y‖`, obtained from a linear
   right inverse of the base stage, continuous because `Y` is finite dimensional.
5. **`PortTower.multivaluedHorizon_eq`** — `(IC.3)`:
   `multivaluedHorizon T = {y | P.fillNormInf y = 0}`.
6. **`PortTower.isClosable_iff`** — `T.IsClosable ↔ ∀ y, q_∞ y = 0 → y = 0`.
7. `multivaluedHorizonSubmodule`, `coe_multivaluedHorizonSubmodule`,
   `multivaluedHorizon_eq_univ_of_mem` — the horizon is a subspace, so one nonzero scalar vertical
   direction already fills the output (§5, case 1).
8. `mem_multivaluedHorizon_of_tendsto` — the vanishing-lift criterion `(IC.16)`: lifts of a fixed
   output with norms tending to `0` put that output in the horizon.
9. **`PortTower.scalar_horizon_dichotomy`** — `(IC.12)`: for scalar output the horizon is `{0}`
   or all of `𝕜`.
10. `portStageMap`, `portCoLift`, `portGram`, `portCapacity` — `(IC.4)`, `G_S = T_S T_S^*` and its
    quadratic form, with `portCapacity_eq` and `portCapacity_mono` (the Gram family increases).
11. `portGram_injective`, `portInvGram` — `Q_S = G_S⁻¹` exists on a filling stage.
12. `portMinLift`, `map_portMinLift`, `norm_portMinLift_le`, `portFillNorm_eq` — `x_S(y) = T_S^* Q_S y`
    is the unique minimum-norm lift.
13. **`portFillNorm_sq`** — `(IC.5)`: `q_S(y)^2 = re ⟪Q_S y, y⟫`.
14. `HilbertPortTower` — a port tower with finite-dimensional stages;
    `HilbertPortTower.re_inner_gram_mono` and `HilbertPortTower.re_inner_invGram_antitone` are the
    Loewner monotonicity statements of `(IC.10)`–`(IC.11)` in quadratic-form shape.
15. `HilbertPortTower.inner_minLift_sub`, `normSq_minLift_sub`, `inner_invGram_sub`,
    `norm_invGram_le`, `norm_invGram_sub_le`, `cauchySeq_invGram` — the exact Cauchy estimates.
16. `HilbertPortTower.limitInvGram` — `Q_∞`, with `tendsto_limitInvGram` and
    **`re_inner_limitInvGram`**: `re ⟪Q_∞ y, y⟫ = q_∞(y)^2`.
17. **`HilbertPortTower.multivaluedHorizon_eq_ker`** — `(IC.6)`:
    `multivaluedHorizon T = ker Q_∞`.
18. `augPort`, `augTower` — `(IC.13)`, the augmentation functional of an orthonormal family with
    its finite-section tower; `normSq_augEmbed_augUniform` gives `‖x_n‖^2 = 1/n`,
    **`augPort_multivaluedHorizon`** gives `multivaluedHorizon (augPort e he) = Set.univ`, and
    `augTower_fillNormInf` gives `q_∞ ≡ 0`.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/CofinalInverseCapacity.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/CofinalInverseCapacityHilbert.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/AugmentationPortCapacity.lean
lake build GaloisForLFunctions.HTGeometry
```

All green with no warnings from these modules.

`#print axioms` on `PortTower.multivaluedHorizon_eq`, `PortTower.isClosable_iff`,
`PortTower.fillSeminorm`, `PortTower.scalar_horizon_dichotomy`,
`HilbertPortTower.multivaluedHorizon_eq_ker`, `HilbertPortTower.re_inner_limitInvGram`,
`HilbertPortTower.re_inner_gram_mono`, `HilbertPortTower.re_inner_invGram_antitone`,
`portFillNorm_sq`, `norm_portMinLift_le`, `augPort_multivaluedHorizon`, `augTower_fillNormInf`
reports only `propext`, `Classical.choice`, `Quot.sound`.

## Scope notes

The Lean development drops the density hypothesis of the paper card, which the proof never uses:
the exhaustion condition is `⨆ n, stage n = T.domain`, and the ambient space enters only through
the graph closure.  The multivalued horizon is the corpus definition
`GaloisForLFunctions.HTGeometry.multivaluedHorizon` from `ObserverHorizonStability.lean`.
