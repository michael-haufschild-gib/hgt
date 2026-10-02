# Literal prime-block physical energy escape

- **ID:** MC-PHYSICAL-ESCAPE-2026-10-01
- **Stage:** 3-formalized
- **Type:** UNCONDITIONAL POSITIVE SURVIVOR
- **Route:** MC

## Goal

Test a proposed growing-core bound on the actual limiting divisor energy before using it to infer complete-source cancellation. A core-uniform limit bound would need to survive actual prime-window cores, not merely arbitrary-vector tests. This is not an RH proof or falsification.

## Candidate and paper argument

Let `P_y` be the literal primes in `(y/3,y]`, and `H_P` the corpus continuous processed divisor head. Candidate positive statement: for every fixed `A>0`, the actual squared energy beyond `y^A`,

`∫_(y^A,∞) H_(P_y)(x)^2 / x^3 dx`,

tends to infinity as `y→∞`, even after division by any fixed real power of `y`. The stronger full-energy bound is `c exp(sqrt(y)/(6 log y))/log y` for some `c>0`. Density weighting preserves divergence: the elementary product lower bound `∏_(p∈P_y) p/(p+1) ≥ 1/(y+1)` suffices.

Source-based proof plan:

1. `DivisorContinuousHeadMellin` identifies the physical Mellin transform with the literal finite Euler product times the unit transform. The unit transform is continuous and nonzero at frequency zero, by positivity of the original unit head.
2. The exact physical Mellin pairing in `MobiusDivisorDilationMean` identifies its squared norm with `∫ H_P²/x³`.
3. `MobiusCriticalPrimeBlockGammaBand` supplies the lower bound `(1+1/sqrt y)^card(P_y)` throughout a band of width `pi/(3 log y)` tending to zero. Its continuous-weight lemma applies to the unit source's squared Mellin modulus.
4. Actual prime-window supply gives `card(P_y) ≫ y/log y`. Since `log(1+1/sqrt y) ≥ 1/(2 sqrt y)` eventually, the full physical energy has the claimed exponential lower bound.
5. `MobiusDivisorPhysicalCutoff.abs_mobiusDivisorContinuousHead_le` gives `|H_P(x)|≤(3/5)x^(3/2)`, uniformly in all cores. Energy before `y^A` is consequently at most `(9/25)y^A`. Subtracting any such polynomial prefix leaves divergent positive tail energy.

## What this would settle

It would rule out uniform energy control over arbitrary growing processed cores and expose superpolynomial delay before their limiting profile becomes relevant. The terminal-window statement alone does not address cores containing every prime below a cutoff. The separate initial-prime extension is now also formalized; see `mc-initial-prime-physical-energy-escape.md`. It does not refute cancellation of the fully completed source at its current cutoff.

The positive survivor is a quantitative escape law for the literal arithmetic source, not a generic coefficient counterexample. If verified, future MC arguments must estimate the finite clock directly rather than use a core-uniform approximation by the infinite physical profile.

## Status

Paper mechanism and exact positive survivor fully formalized in `formal/GaloisForLFunctions/RHTower/MobiusDivisorPrimeBlockEnergyEscape.lean`. Source inspection found `MobiusDivisorDyadicShellDebtGrowth`: it already proves unbounded physical and density-weighted energy for `(2N,3N]` using a single-prime expansion near `4N`. Therefore unboundedness alone is not new. The present target must retain its stronger conclusion: energy escaping beyond **every polynomial** of the prime-window scale, where arbitrarily many product grades contribute. The Mellin-band argument provides a superpolynomial lower bound; a wrapper for existing shell divergence would not suffice.

## Log

- 2026-10-01 — Created after finite-field and repeated-debt-payment screens. Begin with the exact physical energy lower bound; require actual divergence and tail escape before calling this route test complete.


## Final verification

- Targeted `lake --old build GaloisForLFunctions.RHTower.MobiusDivisorPrimeBlockEnergyEscape`: passed (new leaf built; dependency traces replayed).
- Final `lake --old env lean GaloisForLFunctions/RHTower/MobiusDivisorPrimeBlockEnergyEscape.lean`: passed, no warnings.
- `/tmp` name/axiom audit: passed. All three public theorems depend exactly on `[propext, Classical.choice, Quot.sound]`; no added axiom or unproved mathematical premise.
- Umbrella import added to `formal/GaloisForLFunctions/RHTower.lean`; no umbrella/full build, commit or push.
- `scripts/formal_tools.py lint`: failed on ten unrelated unwired modules. No forbidden declaration or new-leaf error reported. Whole-repository lint is not claimed clean.

The unrestricted uniform limiting-energy conjecture is falsified by the stronger tail escape law. The initial-prime version is now separately proved and audited in `mc-initial-prime-physical-energy-escape.md`. RH and its signed finite-clock cancellation problem remain open.
