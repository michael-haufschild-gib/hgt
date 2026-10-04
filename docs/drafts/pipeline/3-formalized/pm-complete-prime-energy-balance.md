# PM complete signed prime-energy balance

- **Status:** formalized and audited, 2026-10-04.
- **Route:** PM; complete signed compensation.
- **Module:** `formal/GaloisForLFunctions/RHTower/PMPowerDampedMobiusPrimeEnergyBalance.lean`.

## Exact result

For every real epsilon and natural N>=1, the actual full-source energy
above physical horizon 1/N satisfies

`E_epsilon(N) = seed(N) + Q_epsilon(N) - 2*(Mplus_epsilon(N)-Mminus_epsilon(N))`.

Here E integrates the squared norm of the literal full PM source, seed
integrates the first Fermi generator, Q is the existing positive quadratic
prime-update current, and Mplus/Mminus integrate the positive/negative
parts of the actual weighted mixed density over the same physical domain.
The module also defines the complete signed current M and proves
`M=Mplus-Mminus`. Every finite physical truncation is integrable without
assuming canonical admission on the entire half-line.

## Proof

Induct over canonical prime apertures. Composite steps leave the aperture
unchanged; a prime step uses the exact insertion law and the complex
squared-norm identity. This telescopes pointwise for every t>0.
Above 1/N the aperture contains every prime needed by the finite source
sum, so the canonical core equals the actual full source. Each finite core
is in L2, its positive dilation is in L2, and the mixed product is
integrable. Finite integration therefore preserves the entire identity.
The scalar positive/negative-part identity reconstructs M exactly.

## Audit

- Eight exports, all indexed and wired once into RHTower.
- Targeted `lake --old build +GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeEnergyBalance:olean` passed; only this leaf newly built.
- Final `lake env lean GaloisForLFunctions/RHTower/PMPowerDampedMobiusPrimeEnergyBalance.lean` passed with empty output.
- All eight separate `/tmp` axiom audits report only `propext`, `Classical.choice`, `Quot.sound`.
- Global lint reports twelve unrelated unreachable modules and no PM failure; not a global lint pass.
- No numerical experiment, added axiom, placeholder, resource-limit increase, umbrella build, commit or push.

## Remaining hard problem

The negative part is proved power-sized. Integrating the actual log-four
source envelope now proves leading positive compensation,
`Mplus >= (1-o(1))*Mminus`, along the square horizons; see
`pm-leading-prime-compensation.md`. The stronger required lower bound
`Mplus-Mminus-Q/2 >= -C_epsilon` remains open. The exact balance itself is not an energy upper bound or RH proof.
