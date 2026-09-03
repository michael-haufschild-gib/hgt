# Brick 152 — full constructed-range Type-I consumer

Added `formal/GaloisForLFunctions/RHTower/Sieve/MatomakiTeravainenTypeIConstructedRange.lean`.

New unconditional theorem declarations:
- `RHTower.Sieve.exists_setIntegral_mtTypeI_amplified_constructedRange`
- `RHTower.Sieve.exists_setIntegral_mtTypeI_primeAmplifier_constructedRange`

They propagate all five alternatives from `exists_integral_mtDI_lemma35_constructedRange` through restricted Cauchy–Schwarz and, in the second theorem, the literal powered-prime block cover and amplifier lower bound. The public statements do not expose analytic-estimate, coefficient-energy, amplifier-lower-bound, or cover premises.

Verification passed:
- direct `lake env lean` source check
- targeted build `lake build GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenTypeIConstructedRange`
- both declarations have axioms `[propext, Classical.choice, Quot.sound]`

The leaf is imported by `formal/GaloisForLFunctions/RHTower.lean`; umbrella was not built. Remaining gap: prove every actual source-schedule block satisfies the five-region disjunction. No Stage-2 card moved.