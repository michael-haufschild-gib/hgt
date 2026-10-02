# Initial-prime physical energy escape

- **ID:** MC-INITIAL-PHYSICAL-ESCAPE-2026-10-01
- **Stage:** 3-formalized
- **Type:** UNCONDITIONAL POSITIVE SURVIVOR
- **Route:** MC

## Hard question

Can the limiting squared physical energy stay uniformly controlled for consecutive initial-prime cores, even though literal terminal prime windows have superpolynomial tail escape? This is the natural completion case left open by `MobiusDivisorPrimeBlockEnergyEscape`. No RH bound is claimed.

## Candidate

For `P_y={p prime | p≤y}`, the tail `∫_(y^A,∞) H_(P_y)(x)^2/x^3 dx`, divided by any fixed power of `y`, tends to infinity for every `A>0`. Density weighting should preserve it.

## Paper mechanism to audit

Use the existing resonance band `[pi/log y,4pi/(3log y)]`. Every prime `sqrt(y)≤p≤y` has phase in `[pi/2,4pi/3]`, hence cosine nonpositive and squared local Euler modulus at least one. The terminal window `(y/3,y]` retains the already-proved exponential amplification. All primes below `sqrt(y)` have local norm at least `1-1/sqrt(p)`, whose log is at least `-4/sqrt(p)` since `p≥2` gives `1/sqrt(p)≤3/4`.

The inspected theorem `PrimeMassLowerBound.sum_one_div_sqrt_le` improves the preliminary split: the small-prime reciprocal-root sum is at most `2 sqrt(sqrt(y))`. Thus the total squared-modulus loss is at most `exp(-16 sqrt(sqrt(y)))`, smaller than the terminal-window gain `exp(sqrt(y)/(6log y))`. The source Mellin weight and finite-prefix envelope then transfer the surviving exponential gain to physical tail energy.

## Status

Fully formalized and audited. This excludes a uniform bounded limiting-energy coefficient even along the natural exhaustive prime sequence. It does not control signed finite-clock energy at the current cutoff or prove/falsify RH.

## Corpus evidence

Current searches for initial-prime critical Euler energy found no applicable bound (coverage snapshot; some compiler metadata pending/stale). Existing fixed-core interpolation and finite-clock payment theorems do not provide uniform exhaustion. The stronger candidate is derived from the inspected `MobiusCriticalPrimeBlockGammaBand` phase proof and actual Euler factorization.


## Formalization checkpoint

The exact finite initial-prime product comparison has passed elaboration in the combined scratch file: on the resonance band its squared norm is at least

`exp(-16 sqrt(sqrt y)) * (1+1/sqrt y)^card(P_y)`.

The proof retains every prime, partitions off the terminal window, bounds each low-prime loss with the inspected logarithm inequality, and uses the existing reciprocal-square-root summation estimate. Full combined compilation has not yet passed: the source-weight positivity step in the physical integral transfer needed an explicit unfolding. That fix and the stronger physical tail statements are now under audit. No production initial-prime theorem is claimed yet.


Combined scratch compilation now passed with no warnings, including the initial-prime exponential lower bound, every polynomially rescaled tail, and density-weighted tail divergence. Production leaf builds and final audits remain pending.


## Final theorem and audit

For the entire literal initial-prime set `Q_y=windowPrimes 0 y`, some `c>0` satisfies eventually

`K(Q_y,1) ≥ c exp(sqrt(y)/(12log y))/log y`.

For every `A>0` and every real `B`, the physical squared tail beyond `y^A`, divided by `y^B`, tends to infinity. Literal core-density weighting still leaves divergent tail energy. This is a qualitative failure of uniform limiting-profile control under natural exhaustive prime selection, not a refinement of the terminal-window constant and not an RH counterexample.

Production modules:

- `formal/GaloisForLFunctions/RHTower/MobiusCriticalInitialPrimeResonance.lean`: exact full initial-prime product comparison, retaining all small-prime losses.
- `formal/GaloisForLFunctions/RHTower/MobiusDivisorPrimeBlockEnergyEscape.lean`: initial-prime exponential energy, polynomially rescaled tails, and density-weighted tails; terminal-window theorems retained.

Targeted `lake --old build GaloisForLFunctions.RHTower.MobiusDivisorPrimeBlockEnergyEscape` passed; only the two changed leaves built and dependencies replayed. Final direct `lake --old env lean` audits of **both** leaves passed without warnings. `/tmp` name/axiom audit passed for all seven public theorems across the two leaves, with exactly `[propext, Classical.choice, Quot.sound]`. Both leaves are wired into `RHTower.lean`; no umbrella/full build, commit, push, numerical experiment or heartbeat increase.

Repository lint failed on eleven unrelated unwired modules, with no forbidden declaration or error naming either new leaf. Do not claim the global lint gate passed.

## Research consequence

The bounded infinite-clock coefficient strategy is falsified even for natural initial-prime cores; the exact positive survivor is the energy-escape law above. Do not continue sharpening its constants. The active hard target is the complete signed current-cutoff gcd cross sum in `../1-in-progress/mc-complete-signed-correlation.md`. No complete-source cancellation exponent has improved.
