# Centered-prime-mark collision rigidity and PPM source/receiver terminal

- **ID:** `ppm-centered-prime-mark-collision-rigidity`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** retired PPM route `prime-power-centered-mark-finite-monodromy-rh`
- **Statement:** Genuine centered-prime power collision forces the critical line; source-first
  finite monodromy and faithful quotient collision are impossible in the strict right half-plane.

## Goal

Close PPM's only remaining producer gate without importing Xi divisor location, and retain the
strongest positive rigidity law exposed by the obstruction.

## Gates

- [x] 0 → 1 in-progress: exact PPM source/receiver fork isolated
- [x] 1 → 2 fully-proven: dependency-closed norm/power-injectivity proof
- [x] 2 → 3 formalized: Lean module built and axiom-audited
- [ ] 3 → 4 publication-ready: external expert novelty review and standalone exposition

## Theorem

For `p > 1`, `a < b`, and `s : ℂ`,

```text
centeredPrimeMark p s ^ a = centeredPrimeMark p s ^ b
  -> Re(s) = 1/2.
```

Moreover, every natural-power orbit is injective on `Re(s)>1/2`; every quotient collision there
forces the quotient map to be non-injective. The closed base-two terminal certificate combines
this with canonical Big-Witt orbit injectivity and the already proved equivalence between
zero-indexed collision and RH.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/PrimePowerCenteredMarkSourceReceiverNoGo.lean`
- Main theorems:
  - `centeredPrimeMark_re_eq_half_of_pow_eq`
  - `centeredPrimeMark_pow_injective_of_mem_rightHalf`
  - `not_rightHalfPrimePowerMarkFiniteMonodromy`
  - `centeredPrimeMark_quotientCollision_not_injective`
  - `primePowerCenteredMark_source_receiver_terminal`
- Verification: direct `lake env lean` passed; targeted `lake build` passed.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.

## Consequence

PPM is retired as an independent RH route. A source-first quotient cannot create finite monodromy
without erasing the centered mark, while a zero-restricted collision assertion is exactly RH.

## Log

- 2026-08-29 — paper proof, Lean proof, targeted build, and axiom audit complete.
