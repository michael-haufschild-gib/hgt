# Failed route: FZZ same-scale Laurent critical fusion

- **Route:** Fuse the monotone Fermi radial coordinate and fixed-quintic phase at one source scale by a fixed Laurent monomial, then identify that scalar with each dyadic Mellin divisor character.
- **Status:** RETIRED — unconditional Lean no-go.
- **Exact killing theorem:** `RHTower.fzzCigarParitySameScaleLaurentCriticalRouteKilled_all`.

## Why it fails

Every nonzero radial exponent changes modulus away from one: positive powers are strictly subunit and negative powers strictly superunit. Hence neither can admit critical-line Mellin characters. Exponent zero has complete critical phase capacity but is exactly the collision-prone quintic phase and cannot determine physical scale.

## Strongest positive survivor

`RHTower.fzzCigarParitySameScaleLaurentEncoding_eq_dyadicMellinCharacter_forces_sector` proves exponent-sign/horizontal-chamber rigidity: positive, zero, and negative radial exponents force left, critical, and right chambers respectively.

Pair-valued same-scale encoding remains phase-complete and scale-injective. Any surviving FZZ-P dynamics must keep its radial coordinate separate, introduce a target-side radial observable, or use a non-Laurent coupling. Scalar Laurent fusion is terminal.

## Verification

Module `GaloisForLFunctions.RHTower.FZZCigarParitySameScaleLaurentCriticalNoGo` passes direct Lean checking and targeted `lake build`; audited theorem dependencies use only standard Lean quotient/classical axioms. Frontier map was not modified.
