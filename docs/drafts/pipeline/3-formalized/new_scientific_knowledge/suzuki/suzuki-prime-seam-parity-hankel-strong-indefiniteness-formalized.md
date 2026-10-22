# Suzuki prime-seam parity-Hankel strong indefiniteness — Lean certificate

- **ID:** `suzuki-prime-seam-parity-hankel-strong-indefiniteness-formalized`
- **Stage:** 3 — formalized in Lean 4
- **Paper proof:** `./suzuki-prime-seam-parity-hankel-strong-indefiniteness.md`
- **Status:** `[LEAN-PROVED] [UNCONDITIONAL] [AXIOM-CLEAN]`

## Lean modules

- `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPrimeSeamParityHankelStrongIndefiniteness.lean`

## Formal theorem surface

Every declaration below was resolved against the tree and its axiom surface checked.

`GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimeSeamParityHankelStrongIndefiniteness`:

```text
RHTower.primeSeamAtomQuadratic
RHTower.primeSeamAtomQuadratic_even
RHTower.primeSeamAtomQuadratic_odd
RHTower.primeSeamEvenEmbedding
RHTower.primeSeamOddEmbedding
RHTower.primeSeamPacketNormSq
RHTower.primeSeamPerturbedQuadratic_even_neg
RHTower.primeSeamPerturbedQuadratic_odd_pos
RHTower.suzukiPrimeSeamWeight
RHTower.suzukiPrimeSeamWeight_prime_pos
RHTower.suzukiPrimeSeam_add_smallPerturbation_signedPackets
RHTower.suzukiPrimeSeam_midpoint_in_aperture
```

## Verification

- every module above passes `lake env lean`;
- `#print axioms` on all 12 resolved declarations reports only `propext`,
  `Classical.choice`, `Quot.sound`;
- no `sorry`, `admit`, user `axiom`, `opaque`, or `unsafe` declaration is reachable;
- no RH premise and no numerical computation is used.
