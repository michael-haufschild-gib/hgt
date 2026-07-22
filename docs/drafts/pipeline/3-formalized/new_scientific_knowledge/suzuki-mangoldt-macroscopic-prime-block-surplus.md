# Suzuki--Mangoldt macroscopic prime-block surplus

- **Status:** Stage 3 -- formalized in Lean 4
- **Labels:** `[NEW]` `[SUZUKI]` `[SOURCE-SPECIFIC]` `[UNCONDITIONAL]`
- **Stage 2 proof:** `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-mangoldt-macroscopic-prime-block-surplus.md`
- **Universal module:** `formal/GaloisForLFunctions/HTGeometry/TiltedTentRightFlank.lean`
- **Suzuki module:** `formal/GaloisForLFunctions/RHTower/SuzukiMangoldtMacroscopicPrimeBlock.lean`

## Formalized theorem package

Universal geometry:

- `tiltedTentRightProfile_strictAntiOn`: subcritical tilted right flanks are strictly decreasing;
- `tiltedTentRightProfile_tail_bound_iff`: left endpoint is exact least ceiling of every tail;
- `tiltedTentRightProfile_lt_one`: every positive displacement strictly contracts.

Sharp width-five Suzuki geometry:

- `suzukiMangoldtFiveAlignedApex_sample_eq`;
- `suzukiMangoldtFiveAlignedApex_self_eq`;
- `suzukiMangoldtFiveFlankContraction_mem_Ioo`;
- `suzukiMangoldtFiveFlankContraction_isSharp`;
- `suzukiMangoldtFivePrimeBlock_sample_le`.

Arithmetic supply and capstone:

- `chebyshev_fivePrimeBlock_logMass_floor`;
- `suzukiMangoldtFivePrimeBlock_atomMass_floor`;
- `suzukiMangoldtFivePrimeBlockSurplus_lower`;
- `suzukiMangoldtFivePrimeBlockSurplus_pos`;
- `suzukiMangoldtFivePrimeBlockSurplus_unbounded`.

For every natural `n` with `exp 20 <= n`, Lean proves

```text
sum_(p prime, 2n<p<=5n) 2log(p)/p >= 1/10

S5(n) >= ((1-q5)/10) sqrt(n) log(5) > 0,
q5 = sqrt(2) (1-log(2)/log(5)),  0<q5<1.
```

It also proves that `q5` is optimal on the full continuous tail and that `S5` exceeds every real
level.  The threshold is an explicit domain restriction proved sufficient from Chebyshev bounds;
it is not an assumed arithmetic statement.

## Formal audit

Direct source checks pass.  Axiom surfaces of sharp tail ceiling, sharp width-five contraction,
Chebyshev mass floor, surplus lower bound, positivity, and unboundedness are exactly:

```text
propext
Classical.choice
Quot.sound
```

No declaration in either new module uses `sorry`, `admit`, a user `axiom`, `opaque`, or `unsafe`.
Final targeted build

```text
lake build GaloisForLFunctions.RHTower.SuzukiMangoldtMacroscopicPrimeBlock
```

passes `9414/9414`.  Repository lint no longer reports either new module or its two immediate
Suzuki/geometry predecessors as unreachable.  Global lint remains red on 21 unrelated modules
created elsewhere in the shared tree.

## Frontier effect

This closes `SUZUKI-APEX-BLOCK-TRANSPORT` only on source scaling.  Existing single-flank surplus
decays as `n^(-1/2)`; actual width-five prime blocks have unbounded surplus bounded below on the
`sqrt(n)` scale.  Remaining open core is target-capacity domination of this explicit source block,
including disjointness and Gamma boundary reserve.  RH is not proved here.
