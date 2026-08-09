# Formalized: Burnol cofinite Cartier wall trace and complete-jet horizon

- **ID:** `burnol-cofinite-cartier-wall-trace-horizon-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `burnol-cofinite-cartier-wall-trace-horizon.md` (same directory)

## Lean modules

| Module | Role |
|---|---|
| `GaloisForLFunctions.RHTower.BurnolPrimeCartierWallTrace` | the pole lattice, the zero-wall derivative trace, the sideband residues, the horizon gap |
| `GaloisForLFunctions.RHTower.BurnolCofiniteHorizonGerm` | the cofinite radius law, the interior decay estimate, the nonclosed-range witness, the reflected orientation |
| `GaloisForLFunctions.RHTower.BurnolAllPrimeCompletionWall` | the completion multiplier and the `ℓ²` wall `(CH21)` |

## Formal theorem chain

1. `burnolSidebandSet`, `burnolSidebandSet_re` — the genuine pole set lies on the imaginary axis.
2. `burnolSideband_re_le_infDist` — every forward pole is at distance at least `σ` from `ρ`.
3. `burnolSideband_exists_index` — a nonzero lattice index within `3π/L` of `t`, uniformly in the
   sign of `t` (the `t = 0` case uses `k = 1`, the rest use the nearest integer).
4. `burnolSideband_infDist_le` — the upper horizon bound `√(σ² + 9π²/L²)`.
5. **`burnolSideband_infDist_tendsto`** — `(CH10)`, forward half: the pole-free radius converges
   exactly to `σ`.  `burnolSidebandReflected_infDist_tendsto` — reflected half, `1 - σ`.
6. `burnolHorizonGap`, `burnolHorizonGap_eq`, `burnolHorizonGap_pos_iff` — `(CH12)`.
7. **`burnolGerm_uniform_decay`** — `(CH15)`: `|C_p(ρ+z)| ≤ A p^{-(σ-R)}` uniformly on
   `‖z‖ ≤ R < σ`, for every prime past an explicit threshold, from `p^{σ-R} ≥ 2`.
8. `burnolDecay_eventually_lt`, **`burnolGerm_unit_tendsto_zero`** — `(CH16)`: the unit
   coordinates go to zero uniformly on every safe disc, while `‖e_p‖ = 1`.
9. **`burnolGermReflected_uniform_decay`** — `(CH17)`, by reflecting `ρ ↦ 1 - ρ`, `z ↦ -z`.
10. **`burnolGermJoint_unit_tendsto_zero`** — `(CH14)`: the collapse is simultaneous in both
    orientations.
11. **Nonclosed range**, `(CH13)`--`(CH17)`, without the open mapping theorem:
    `burnolGermWitness_summable` (the germ data of `u_p = p^{-1/2}` is square summable on every
    safe disc, so the truncations converge in every compact-open seminorm),
    `burnolGerm_preimage_forced` (the only possible preimage is `u` itself, since `C_p(ρ) ≠ 0` in
    the open strip), `burnolGermWitness_not_summable` (`∑ 1/p = ∞`).
12. `tendsto_burnolCartierZeroWallTrace` — `(CH2)`, `(CH7)`, `(CH8)`, forward half;
    `tendsto_burnolAllPrimeCompletionReflected_div_one` — reflected half.
13. `tendsto_burnolAllPrimeCompletion_sidebandResidue` — `(CH5)`;
    **`tendsto_burnolAllPrimeCompletionReflected_sidebandResidue`** — `(CH6)`, by composing with
    `s ↦ 1 - s` on the punctured neighbourhood (`burnolTendsto_reflect_nhdsWithin`).
14. `tendsto_burnolCartierSidebandTrace`,
    **`tendsto_burnolCartierReflectedSidebandTrace`** — `(CH4)`, `(CH18)`, `(CH19)`: unit-gain
    coefficient recovery in both orientations at every nonzero sideband.
15. `summable_burnolAllPrimeInverseCompletionCoefficient_sq_iff` — `(CH20)`, `(CH21)`.
16. `xiDivisor_burnolCartier_headEnergyDefect_eq_horizonGap_mul_headFlux` — `(CH22)`, `(CH23)`.

## Verification

- `lake env lean` clean, no warnings, on each module.
- `lake build GaloisForLFunctions.RHTower` compiles them inside the area umbrella.
- `#print axioms` on the numbered theorems: `propext`, `Classical.choice`, `Quot.sound` only.
- Imported by `GaloisForLFunctions.RHTower`.

## Open beyond the card

The card's own producer — **singular Cartier trace dissipativity**, the Stokes boundary form on the
trace graph and the sign of its reflection-odd zero-wall marginal — is not a theorem of this card
and is not formalized here.
