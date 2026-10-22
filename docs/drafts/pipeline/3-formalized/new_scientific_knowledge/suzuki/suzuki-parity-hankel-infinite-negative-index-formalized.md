# Suzuki parity-Hankel infinite-negative-index classification — Lean certificate

- **ID:** `suzuki-parity-hankel-infinite-negative-index-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-parity-hankel-infinite-negative-index.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiArchimedeanParityHankelInfiniteNegativeIndex.lean`
- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPrimeSeamParityHankelStrongIndefiniteness.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.Suzuki.SuzukiArchimedeanParityHankelInfiniteNegativeIndex`:

```text
RHTower.ArchHankelHasAtLeastNegativeSquaresOn
RHTower.archHankel_positive_subspace_finrank_le_one
RHTower.archKernelGramQuadratic_eq_moments
RHTower.archNegativeMode
RHTower.archPositiveMode
RHTower.coeff_eq_zero_of_archNegativeMoment_zero
RHTower.hasSum_archNegativeMode_product
RHTower.realArchHankelProfile
RHTower.realArchHankelProfile_eq_mode_tsum
RHTower.realArchHankelProfile_hasAtLeastNegativeSquaresOn
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 10 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.
