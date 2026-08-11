# Cofinal capacity-polar horizon and Moore--Penrose law — Lean certificate

- **ID:** `cmr-cofinal-capacity-polar-horizon-moore-penrose-formalized`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:** `cofinal-capacity-polar-horizon-moore-penrose-law.md` (same directory).
- **Status:** `[UNCONDITIONAL]` `[NO SORRY / NO AXIOM / NO PROP INTERFACE]`

## Lean modules

| Module | Content |
|---|---|
| `formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/CapacityPolarHorizon.lean` | `CapacityChart`, the Fenchel identity, the limiting cometric, the polar horizon law, the Moore–Penrose realization, the polar duality |
| `formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/CapacityPolarPortBridge.lean` | Corollary 2.2: the chart of a real Hilbert port tower and the orthogonal split of its output |
| `formal/GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/CapacityPolarCountermodels.lean` | the three sharp boundary countermodels of §7 |

All three are imported by the area umbrella `GaloisForLFunctions.HTGeometry`.
Namespace: `HTGeometry.ConstraintMotiveRelativity`.

## Formal statement chain

The chart is realized on a finite-dimensional real inner product space, with `V*` identified with
`V` by the auxiliary inner product the card itself permits; the annihilator `K°` of `(CPH.5)` is
then the orthogonal complement `Kᗮ`, and `(CPH.7a)` is literal.

1. `CapacityChart V` — `(CPH.1)`: `gram : ℕ → V →ₗ[ℝ] V` symmetric, positive definite, with
   increasing quadratic forms.
2. `CapacityChart.cometric` — `(CPH.2)`, `q_n = g_n⁻¹`, with `cometric_symm`.
3. **`CapacityChart.fenchel`** — `(CPH.9)` in exact form
   `2⟪α,x⟫ - ⟪Q_n α, α⟫ = ⟪G_n x, x⟫ - ⟪G_n (x - Q_n α), x - Q_n α⟫`, with `fenchel_le` and
   `fenchel_eq` (the supremum is attained at `α = G_n x`).
4. **`CapacityChart.cometricForm_antitone`** — inversion reverses the order.
5. `cometricFormInf`, `tendsto_cometricForm`, `cometric_polarization`, `tendsto_inner_cometric`,
   `exists_tendsto_cometric` — the limiting form and its polarization.
6. `CapacityChart.cometricLimit` — the limiting cometric `q`, with `tendsto_cometricLimit`,
   `inner_cometricLimit_self`, `cometricLimit_symm`, `cometricLimit_nonneg`.
7. `CapacityChart.boundedCapacity` — `(CPH.4)`, `W_cap`.
8. `polar_le`, `gram_le_of_mem_range`, `tendsto_gram_of_mem_range` — `(CPH.12)` and the convergent
   half of `(CPH.6)`.
9. **`CapacityChart.not_bddAbove_of_not_mem_orthogonal`** — the divergent half of `(CPH.6)`.
10. `orthogonal_range_cometricLimit`, **`range_cometricLimit_eq_orthogonal`** — `(CPH.11)`.
11. **`CapacityChart.boundedCapacity_eq`** and **`boundedCapacity_eq_orthogonal`** — `(CPH.5)`:
    `W_cap = ran q = K°`.
12. `reduced_wellDefined` — the reduced inverse form is well defined.
13. `sectorMap`, `sectorMap_injective`, `sectorEquiv`, **`pseudoInverse`**,
    `cometricLimit_pseudoInverse` — the Moore–Penrose inverse of `q`.
14. **`CapacityChart.tendsto_gram_pseudoInverse`** — `(CPH.7a)`: on `W_cap` the direct capacities
    converge to `⟪Q_∞^† x, x⟫`.
15. `boundedCapacitySubmodule`, **`isCompl_boundedCapacity`** — the polar sector and the collapse
    kernel are complementary.
16. **`isGreatest_cometricLimit`** — `(CPH.12a)`, the reverse polar identity; and
    **`isGreatest_gram_limit`** — `(CPH.9)`/`(CPH.10)` for the limiting pair.
17. `HilbertPortTower.capacityChart`, `capacityChart_cometric`, `capacityChart_cometricLimit` —
    the chart of a real Hilbert port tower, matching the cometric of the parent card.
18. **`HilbertPortTower.multivaluedHorizon_eq_orthogonal_boundedCapacity`** and
    **`isCompl_boundedCapacity_horizon`** — Corollary 2.2, `(CPH.8)`:
    `mul (closure Γ(T)) = W_capᗮ` and `Y = W_cap ⊕ mul (closure Γ(T))`.

### Sharp boundary countermodels (§7)

* §7.1 — `momentGram`, `momentMetric`, `momentMetric_mul_momentGram`, **`momentGram_mono`**
  (the integral form `Q_t - Q_s = ∫ₛᵗ (1,u)ᵀ(1,u) du` is positive semidefinite, proved through the
  exact identity `4(t-s)·Q = (2(t-s)a + (t²-s²)b)² + (t-s)⁴b²/3`), `momentMetric_form`
  (`= 4/(4+t)`), `momentMetric_apply_snd` (`= -6/(t(4+t))`),
  **`tendsto_momentMetric_form`** (the reduced form converges to `1`) and
  **`not_bddBelow_momentMetric_snd`** (the uncompressed vectors do not converge).
* §7.2 — `rotatingOff`, `rotatingGram`, `rotatingMetric`, `rotatingMetric_mul_rotatingGram`,
  **`rotatingGram_posDef`**, `tendsto_rotatingGram_entry` (convergence to `diag(1,0)`),
  `rotatingMetric_form` (`= 1/c`) and **`tendsto_rotatingMetric_form_atTop`**: monotonicity cannot
  be dropped.
* §7.3 — `finsetSum_iSup_of_monotone`, `tsum_iSup_of_monotone`, `diagWeight`, `diagEnergyTerm`,
  `diagLimitTerm`, `iSup_diagEnergyTerm`, **`iSup_diagEnergy`** (the monotone-convergence
  computation `supₙ ⟪G_n x, x⟫ = ∑ₖ k²|x_k|²`), `diagWitness`,
  **`diagLimitEnergy_diagWitness_ne_top`** and **`diagWitness_preimage_not_summable`**: the
  witness `x_k = (k+1)⁻²` has finite direct capacity but no square-summable preimage, so finite
  dimension is essential.

## Verification

```
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/CapacityPolarHorizon.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/CapacityPolarPortBridge.lean
lake env lean GaloisForLFunctions/HTGeometry/ConstraintMotiveRelativity/CapacityPolarCountermodels.lean
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CapacityPolarPortBridge
lake build GaloisForLFunctions.HTGeometry.ConstraintMotiveRelativity.CapacityPolarCountermodels
```

All green with no warnings from these modules.

`#print axioms` on `CapacityChart.boundedCapacity_eq`, `boundedCapacity_eq_orthogonal`,
`range_cometricLimit_eq_orthogonal`, `tendsto_gram_pseudoInverse`,
`not_bddAbove_of_not_mem_orthogonal`, `isGreatest_cometricLimit`, `isCompl_boundedCapacity`,
`HilbertPortTower.multivaluedHorizon_eq_orthogonal_boundedCapacity`,
`isCompl_boundedCapacity_horizon`, `momentGram_mono`, `tendsto_momentMetric_form`,
`not_bddBelow_momentMetric_snd`, `rotatingGram_posDef`, `tendsto_rotatingMetric_form_atTop`,
`iSup_diagEnergy` and `diagWitness_preimage_not_summable` reports only `propext`,
`Classical.choice`, `Quot.sound`.

## Scope notes

`(CPH.13)` (the Pontryagin exact sequence attached to a rational vertical fibre) is the content of
the sibling card `finite-lattice-direction-capacity-verticality-pontryagin-law.md` and is
formalized there, not here.
