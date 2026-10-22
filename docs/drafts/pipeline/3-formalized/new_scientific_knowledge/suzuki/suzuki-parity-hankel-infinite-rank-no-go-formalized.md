# Suzuki parity-Hankel infinite-rank no-go — Lean certificate

- **ID:** `suzuki-parity-hankel-infinite-rank-no-go-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-parity-hankel-infinite-rank-no-go.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiArchimedeanParityHankelInfiniteRank.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiArchimedeanParityHankelInfiniteNegativeIndex.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.Suzuki.SuzukiArchimedeanParityHankelInfiniteRank`:

```text
RHTower.HasPositiveOpenSquareSeparationRankAtMost
RHTower.archHankelKernel_not_hasPositiveOpenSquareSeparationRankAtMost
RHTower.archHankelProfile
RHTower.archTranslatePacket_coeff_zero_of_posReal_lt
RHTower.clearedArchRelation
RHTower.clearedArchRelation_eq_zero_of_posReal_lt
RHTower.coeff_zero_real_nodes
RHTower.fullDenominator_mul_archTranslatePacket
RHTower.linearIndependent_archHankelKernel_translates_on_posReal_lt
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 9 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.
