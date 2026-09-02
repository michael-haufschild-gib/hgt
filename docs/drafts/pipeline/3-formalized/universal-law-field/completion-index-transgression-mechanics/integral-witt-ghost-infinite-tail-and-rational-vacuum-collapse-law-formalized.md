# Integral Witt ghost infinite tail and rational vacuum collapse — Lean certification

- **ID:** `ULF-IWG-1`
- **Stage:** 3-formalized
- **Paper card:** `completion-index-transgression-mechanics/integral-witt-ghost-infinite-tail-and-rational-vacuum-collapse-law.md`
- **Lean module:** `GaloisForLFunctions.RHTower.IntegralWittGhostInfiniteTail`

## Certified declarations

- `integralWittGhost_primeExtension`: exact IWG-1 coprime prime-extension congruence.
- `integralWittGhost_prime_ne_zero_of_natAbs_lt`: exact prime-tail consequence; a nonzero first
  ghost forces every sufficiently large prime ghost to remain nonzero.

## Verification

Direct `lake env lean` check and targeted `lake build` passed. Targeted axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. Module is wired into `RHTower.lean` and
`HTGeometry.UniversalLawField`; no umbrella build was run.
