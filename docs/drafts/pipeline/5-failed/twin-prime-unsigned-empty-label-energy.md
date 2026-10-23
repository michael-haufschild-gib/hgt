# Failure of unsigned energy after every mark is consumed

- **ID:** twin-prime-unsigned-empty-label-energy
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** [fully consumed signed endpoint](../1-in-progress/twin-prime-consumed-mark-determinant.md)
- **Statement:** The zero-frequency empty-label energy cannot satisfy `E_0 << X/(log X)^D` for any fixed `D>0` on all balanced blocks.

## Exact killing mechanism

Set `X=T^2`, use factor blocks `(T,2T]`, and keep the actual coefficients `mu(m)R_z(m)` and `c_V(n)R_z(n)`. For any natural cutoffs `z,V<=T`, products of distinct block primes have coefficient `-log(pr)`. Their nonnegative squared contributions alone give `E_0>=X/25` eventually. Hence even `E_0=o(X)` is false.

The obstruction applies to discarding the remaining cofactor sign and seeking a logarithmic saving in the resulting energy. It does not refute cancellation in the original signed endpoint.

## No-go closure

- **Strongest positive survivor established:** exact semiprime coefficient, injectivity of ordered prime products, finite lower bound by four times the two prime logarithmic masses, and the cutoff-uniform eventual bound `E_0>=X/25`.
- **New insight for this route:** the bulk comes from an explicit arithmetic subset with aligned factorization signs. A replacement argument must use cancellation involving the remaining cofactor sign or subtract and control a structured component; positivity alone cannot supply the missing saving.
- **Paper and Lean status:** [complete survivor proof and certificate](../3-formalized/twin-prime-semiprime-energy-lower-bound.md). Exact capstones `TwinPrime.eventually_emptyLabelEnergy_ge` and `TwinPrime.emptyLabelEnergy_not_isLittleO`, in `twin-prime/SemiprimeEnergy.lean`, passed leaf and standard-axiom audits.
- **Second pass:** retained arbitrary cutoff families and proved the exact prime-pair coefficient before taking the lower bound. These positive statements are known consequences of unique factorization and PNT; no scientific novelty is claimed.

## Continuation

The [signed determinant problem](../1-in-progress/twin-prime-consumed-mark-determinant.md) remains active. Its equation `mn-qh=-2` retains both `mu(m)` and `mu(h)`. Neither the no-go nor its positive survivor proves twin-prime infinitude.

## Log

- 2026-10-23 — Retired only the unsigned-energy shortcut after completing and auditing its positive survivor. Kept the signed analytic target open.
