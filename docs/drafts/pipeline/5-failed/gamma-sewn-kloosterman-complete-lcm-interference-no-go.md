# Gamma-sewn Kloosterman complete-lcm interference no-go

## Status

Paper proof and unconditional Lean formalization complete.

## Killed weld

Gamma synchronized-lcm pair weight → complete squarefree `p*r` physical window → Route-E
distinct-prime Kloosterman interference → collective signed cancellation.

For distinct primes, CRT separates one `p*r` period. Each nontrivial Kloosterman column has zero
first-variable mean, so cross correlation vanishes for every column pair. Gamma pair coefficient
is strictly positive: source coefficient is retained, while complete-lcm synchronization itself
erases interference.

## Positive survivor

For arbitrary `[1,M]`, entire coprime cross-modulus correlation equals explicit product-period
residue-discrepancy remainder. No cross-modulus bulk remains. Viable weld must control this literal
incomplete product-shell boundary collectively; complete lcm windows cannot supply Route-E sign.

## Lean

- `RHTower.Sieve.KloostermanCoprimeProductPeriodCompletion`
- `RHTower.GammaSewnKloostermanLcmInterferenceNoGo`
- `kloostermanCrossModulusCorrelation_Icc_eq_coprime_remainder`
- `gammaSewnKloostermanPair_completeLcm_erases_interference`

Axiom audit: `propext`, `Classical.choice`, `Quot.sound` only.
