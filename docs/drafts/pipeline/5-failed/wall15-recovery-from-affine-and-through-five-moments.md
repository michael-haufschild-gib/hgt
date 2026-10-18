# Recovery from affine and through-five translated moments

- **Stage:** 5-failed
- **Type:** NO-GO with a sharp positive survivor, formalized in Lean
- **Wall:** 15, support versus orientation; field research only
- **Positive survivor:** [sharp sixth-moment recovery](../3-formalized/wall15-sixth-moment-recovery-in-the-even-prime-pair-sector.md)

## Retired claim and exact obstruction

All affine quadratic observations together with all translated moments of degree at most five do not determine the even prime-pair sector up to one common sign. They do not even determine its sixth zero-lag moment.

At every cutoff N+10, take the actual weights `evenPairReal 1 1` and `evenPairReal 1 (-1)`, whose only nonzero multiples coordinates are `(Y6,Y10)=(1,1)` and `(1,-1)`. Every affine observation and every translated moment through degree five agrees, while their zero-lag sixth moments differ by exactly 960. `exists_same_affine_through_five_distinct_sixth` certifies this literal witness. In addition, `evenPair_odd_zero` annihilates every odd-degree translated moment for both weights, so adjoining the entire odd hierarchy does not repair the obstruction.

The mechanism is structural. The common parity anti-period kills all odd moments. At degree four, every term sensitive to an independent coefficient sign has a lone centered prime row; CRT factorization kills its average. This covers every lag vector, not only zero lag.

## Strongest positive survivor

For arbitrary real coefficients a,b, the exact sixth moment is

`22a⁶+360a⁴b²+480a³b³+1560a²b⁴+820b⁶`.

Affine data determine exactly a² and b². Subtracting the known even-power terms recovers `(ab)³`, hence ab. The exact theorem `evenPair_recovery_iff` proves that equality of affine data plus this one sixth moment is equivalent to equality up to a common sign, with every zero-coordinate case included. Degree six is sharp for this observation family and sector. The general even-degree CRT bridge is also formalized.

This is a dependency-closed paper proof and an actual-sieve Lean certificate, not a replacement hypothesis or an assumed spectral model. The two production leaves contribute 20 public exports; both final original-source checks passed with no diagnostics. All 20 signatures and axiom closures plus seven definition bodies were inspected: only `propext`, `Classical.choice`, `Quot.sound`. Evidence: `/tmp/bsu-sixth-phase-manifest.json` and `/tmp/bsu-sixth-public-audit-r1.log`. Repository lint status is recorded on the survivor card and is separate from the verified theorem certificate.

## Scope and next question

Wall 15 remains open. No arbitrary divisor-support reconstruction, quantitative stability, or external novelty claim follows. The [finite odd-prime-family follow-up](../3-formalized/wall15-sixth-order-recovery-for-finite-odd-prime-mode-families.md) is now formalized: full sixth-order lag data recover every finite odd-prime coefficient family up to common sign, while one zero-lag sixth scalar can still fail in dimension three. The exact [scalar-observation no-go and positive survivor](wall15-recovery-from-affine-and-one-zero-lag-sixth-moment.md) are both certified.
