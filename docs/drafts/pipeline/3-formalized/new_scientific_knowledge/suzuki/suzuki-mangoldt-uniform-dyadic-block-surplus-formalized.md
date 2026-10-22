# Sharp geometric-bracket minimax and Suzuki--Mangoldt absolute surplus -- Lean certificate

- **ID:** `suzuki-mangoldt-uniform-dyadic-block-surplus`
- **Stage:** 3 -- formalized in Lean 4
- **Paper proof:** `./suzuki-mangoldt-uniform-dyadic-block-surplus.md`
- **Lean modules:** `GaloisForLFunctions.HTGeometry.TiltedTentGeometricBracketMinimax`;
  `GaloisForLFunctions.RHTower.Suzuki.SuzukiMangoldtApexCrossPrimeBlock`
- **Status:** unconditional

## Formal theorem map

Exact support classification:

```lean
suzukiMangoldtAlignedApex_sample_pos_iff_openAnnulus
```

Prime straddling, mass comparison, strict flank surplus, and three-atom dilution:

```lean
exists_prime_straddling_multiplicativeAnnulus
mangoldtLogHaarAtomMass_le_lowerPrimeFlank
mangoldtLogHaarAtomMass_lt_twice_upperPrimeFlank
exists_suzukiMangoldtCrossPrimeFlankSurplus
exists_suzukiMangoldtCrossPrimeThreeAtomBlockDilution
```

Universal sharp tilted-tent minimax law:

```lean
tiltedTentBalance_mem_Ioo
tiltedTent_balance_identity
tiltedTent_geometricBracket_minimax
tiltedTent_geometricBracket_minimax_sharp
tiltedTent_profiles_eq_iff
tiltedTentSharpContraction_mem_Ioo
```

Sharp dyadic specialization, strict improvement, and mass floor:

```lean
exists_dyadic_far_suzukiMangoldtFlank
suzukiMangoldtDyadicSharpContraction_closedForm
suzukiMangoldtDyadicSharpContraction_mem_Ioo
suzukiMangoldtDyadicSharpContraction_lt_sqrtTwo_div_two
exists_dyadic_sharp_suzukiMangoldtFlankDilution
exists_dyadic_uniform_suzukiMangoldtFlankDilution
sqrtTwo_div_two_lt_one
```

Explicit source-surplus definition and lower bound:

```lean
suzukiMangoldtAlignedFlankSurplus
exists_dyadic_sharp_quantitative_suzukiMangoldtFlankSurplus
suzukiMangoldt_logTwo_div_mul_alignedApex_eq
exists_dyadic_absolute_suzukiMangoldtFlankSurplus
exists_dyadic_quantitative_suzukiMangoldtFlankSurplus
suzukiMangoldtDyadicApex_successor_sample_eq_zero
suzukiMangoldtDyadicApex_successor_surplus_eq_and_pos
```

Supporting strict-max connector:

```lean
mangoldtLogHaarNode_injective_of_two_le
suzukiMangoldtAlignedApex_sample_lt_self_of_ne
```

## Audit

- Direct `lake env lean` checks of both modules: passed.
- Final `lake build GaloisForLFunctions.RHTower.Suzuki.SuzukiMangoldtApexCrossPrimeBlock`: passed.
- Repository formal lint gate: passed.
- Capstone axiom surfaces: only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration occurs in the module.
- No RH or `MangoldtLogHaarCapacity` premise occurs in any theorem.

## Exact frontier after formalization

Lean now proves the exact universal tilted-tent geometric-bracket minimax law, its sharp continuous
factor, a strictly improved Suzuki contraction, a dyadic mass floor, and an absolute positive
source surplus `(1-C_*)(log 2)^2/sqrt(n)` at every aligned apex. Missing theorem is a target-side
completed-kernel capacity construction dominating that explicit surplus with disjoint blocks and
residual Gamma mass. This card does not claim that connector or RH.
