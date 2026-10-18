# Recovery from affine data and one zero-lag sixth moment

- **Stage:** 5-failed
- **Type:** NO-GO with an exact positive survivor, formalized in Lean
- **Wall:** 15, support versus orientation; field research only
- **Positive survivor:** [complete finite-family sixth-order recovery](../3-formalized/wall15-sixth-order-recovery-for-finite-odd-prime-mode-families.md)

## Retired claim and exact obstruction

All affine quadratic data, all translated moments through degree five, and the single zero-lag sixth moment do not determine a finite odd-prime family up to one common sign. This obstruction concerns that specific scalar observation; it does not rule out the explicit Fourier readouts proved on the survivor card.

At every cutoff N+14, use the actual four-divisor atoms

`A_p(d)=1_(d=1)−2·1_(d=2)−p·1_(d=p)+2p·1_(d=2p)`.

Let `u=5^(1/3)>0`, `v=2^(1/3)>0`. Compare `A_3+u A_5−v A_7` and `A_3−u A_5+v A_7`, realized by `primeFamilyWeight (N+14) scalarCollisionLeft` and its right counterpart. `threePrime_scalar_collision` proves equality of all stated observations. `threePrime_collision_not_common_sign` proves that their coefficient vectors are not related by one common sign. The fixed cube-root identities and positivity are proved in Lean; they are not assumptions on the counterexample.

The mechanism is exact cancellation. Write the literal responses as `parity·(X+W)` and `parity·(X−W)`, where `X=R_3` and `W=uR_5−vR_7` are centered prime residue rows. At degree six,

`(X+W)^6−(X−W)^6=12X^5W+40X^3W^3+12XW^5`.

CRT separates X from W. Their first moments vanish, and `E[W^3]=12u^3−30v^3=0`, so the sixth zero-lag averages agree. Equal coefficient squares preserve all affine data and all through-five lags. Every odd translated moment also vanishes by the proved antiperiod, so adjoining the entire odd hierarchy does not repair this obstruction. No complete residue period is enumerated.

## Strongest positive survivor

The discarded relative signs remain observable in the full sixth lag family. The selected prime-3/prime-5 sixth Fourier readouts differ by exactly `10((N+14)!)^6`, which is positive. `threePrime_collision_readout_gap` proves this exact identity, and `threePrime_some_sixth_lag_separates` proves that some literal sixth lag separates the same witnesses.

More generally, the explicit pair readout equals `P^6(a_p a_q)^3`. Cube injectivity recovers every signed pair product; the complete outer-product matrix determines the family up to one common sign, including empty and zero cases. `primeFamily_readouts_iff_common_sign` and `primeFamily_sixth_iff_common_sign` formalize this exact classification. Affine data are redundant once full sixth data are supplied.

The stronger survivor requires no prime-support assumption: for arbitrary actual divisor weights, explicit sixth readouts recover signed coordinate products within each fixed power-of-two valuation class. `sixthPairReadout_eq_iff`, `sixth_readouts_eq_iff_valuation_sign` and `sixth_moments_recover_valuation_block` certify that statement. No classification of signs across different valuation blocks is claimed.

The survivor has a dependency-closed paper proof and completed actual-object Lean certificates. The nine-leaf package's complete signature, definition, API, axiom and integration evidence is recorded on its [formalized card](../3-formalized/wall15-sixth-order-recovery-for-finite-odd-prime-mode-families.md) and in `/tmp/bsu-family-phase-manifest.json`. Repository lint status is recorded separately there; it is not conflated with the checked theorem certificates.

## Scope

This closes the scalar-observation route and formalizes its strongest positive salvage. Wall 15 remains open. No stability theorem, arbitrary multi-block classification, positivity producer or external novelty claim follows. No new route was started after the user requested completion of this package.
