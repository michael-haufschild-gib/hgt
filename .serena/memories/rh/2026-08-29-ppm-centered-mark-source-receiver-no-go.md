# PPM centered-mark source/receiver no-go (2026-08-29)

Route PPM retired as an independent RH route.

## Lean
- New module: `formal/GaloisForLFunctions/RHTower/PrimePowerCenteredMarkSourceReceiverNoGo.lean`
- Wired into `formal/GaloisForLFunctions/RHTower.lean`.
- `centeredPrimeMark_re_eq_half_of_pow_eq`: for `p > 1`, a collision of two distinct natural powers forces `Re(s)=1/2`.
- `centeredPrimeMark_pow_injective_of_mem_rightHalf`: full natural-power orbit injective on strict right half-plane.
- `not_rightHalfPrimePowerMarkFiniteMonodromy`: divisor-independent finite monodromy on all right-half labels is false.
- `centeredPrimeMark_quotientCollision_not_injective`: every quotient collision at a right-half label forces quotient map non-injective, so it loses exact mark faithfulness needed by endpoint.
- `primePowerCenteredMark_source_receiver_terminal`: bundles source-free orbit, universal no-go, faithful quotient no-go, canonical Big-Witt right-fiber injectivity, and `XiRightPrimePowerMarkCollision 2 ↔ RH`.

## Interpretation
Exact PPM fork is terminal: source-first faithful collision impossible; canonical Big-Witt gives no collision; any quotient collision erases required scalar equality; restricting collision to Xi zeros is precisely RH and hence receiver-first/circular. Strongest positive survivor is global collision rigidity.

## Verification
- Scratch and in-tree `lake env lean` passed.
- Targeted `lake build GaloisForLFunctions.RHTower.PrimePowerCenteredMarkSourceReceiverNoGo` passed.
- Axioms for all new main theorems: `[propext, Classical.choice, Quot.sound]`.
- `scripts/formal_tools.py lint` reports unrelated pre-existing unreachable modules, none involving new PPM module.
- No stale Lean process from this work.

## Pipeline
- Failed card: `docs/drafts/pipeline/5-failed/prime-power-centered-mark-finite-monodromy-rh.md`
- Formalized card: `docs/drafts/pipeline/3-formalized/ppm-centered-prime-mark-collision-rigidity.md`
- Frontier map remained read-only.