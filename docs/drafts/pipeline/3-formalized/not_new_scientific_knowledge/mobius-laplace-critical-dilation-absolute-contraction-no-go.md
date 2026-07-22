# Möbius--Laplace critical dilation absolute-contraction no-go

- **ID:** `mobius-laplace-critical-dilation-absolute-contraction-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / candidate Lean theorem
- **Source:** Möbius--Laplace critical renewal law
- **Statement:** Prime critical mass prevents any absolutely summable correction from making the
  Lambert dilation equation an absolute half-weight contraction.

## Goal

Close the tempting route which isolates the first term in

```text
sum_(k>=1) Phi(kx) = exp(-x)
```

and attempts to bound the remaining dilates by an `l1` contraction after critical normalization.
The route must be rejected by an exact boundary theorem, not by a heuristic divergence claim.

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, hostile target fixed
- [x] 1 -> 2 fully-proven: dependency-closed proof and scientific classification
- [x] 2 -> 3 formalized: Lean theorem and targeted source check
- [ ] 3 -> 4 publication-ready: ineligible unless literature audit finds genuine external delta

## Approach

On prime dilation indices the critical weight is `p^(-1/2)`.  Let `b(p)` be any proposed
correction.  If both corrected forcing coefficients `b(p)` and contraction coefficients
`1+b(p)` had absolutely summable critical mass, then

```text
p^(-1/2) <= (|b(p)| + |1+b(p)|) p^(-1/2)
```

would make `sum_p p^(-1/2)` converge.  This contradicts the prime `p`-series boundary
(`sum_p p^r` converges exactly for `r < -1`).  Finite correction is the special case where
`b(p)=0` eventually, so the corrected coefficient remains exactly `1` on all sufficiently large
primes.

## No-go closure

- **Exact killing theorem/mechanism:** divergent prime critical mass; simultaneous absolute
  control of forcing and contraction coefficients is impossible.
- **Strongest positive survivor:** a sharp two-sided correction obstruction at exponent `1/2`,
  stronger than observing that the uncorrected renewal weights are not summable.
- **New insight:** any viable dilation proof must use conditional signed cancellation of the
  distinguished Möbius solution; finite multipliers, `l1` Neumann series, and absolutely
  controlled infinite corrections cannot cross the critical wall.
- **Status:** paper proof drafted; Lean and literature audits pending.

## Log

- 2026-07-22 -- created after the additive-triangle bridge exposed the remaining arithmetic source
  and the alternative Lambert-contraction attack reached the prime half-weight wall.

## Dependency-closed proof and Lean milestone

For any real `r >= -1`, Mathlib's prime `p`-series classification gives

```text
not Summable (p |-> p^r).
```

For arbitrary `b : Primes -> C`, the triangle inequality gives pointwise

```text
1 = |(1+b(p))-b(p)| <= |b(p)|+|1+b(p)|.
```

Multiplication by the nonnegative weight `p^r` shows that simultaneous summability of the two
weighted norms would majorize `sum_p p^r`, contradiction.  At `r=-1/2` this is exactly the
Möbius--Laplace critical renewal wall.  If `b` is eventually zero, `1+b` is eventually one, giving
the finite-correction corollary directly by cofinite invariance of summability.  `[PROVED HERE]`

Formal module:

```text
formal/GaloisForLFunctions/RHTower/MobiusLaplaceCriticalDilationNoGo.lean
```

Principal declarations:

- `not_summable_primeRpow_of_negOne_le`;
- `no_simultaneous_summable_primeRpowCorrection`;
- `no_simultaneous_summable_primeCriticalDilationCorrection`;
- `not_summable_primeCriticalDilationCorrection_of_eventually_zero`;
- `not_summable_prime_mobiusLaplaceCriticalRenewalWeight`.

Targeted verification passed with no diagnostics:

```text
lake env lean GaloisForLFunctions/RHTower/MobiusLaplaceCriticalDilationNoGo.lean
```

Scientific classification: `[NEW TO CORPUS] [CLASSICAL CONSEQUENCE]
[NOT NEW SCIENTIFIC KNOWLEDGE]`.  Prime `p`-series divergence and the triangle inequality absorb
the mathematical mechanism; no external novelty claim is made.  Strongest source-specific
survivor is the exact simultaneous-correction theorem, which excludes finite and absolutely
controlled infinite multiplier repairs in one statement.

### Gate update

- [x] dependency-closed paper proof
- [x] direct Lean source verification
- [x] axiom audit: principal correction and renewal-weight theorems use only `propext`,
  `Classical.choice`, and `Quot.sound`
- [ ] final `lake build` intentionally deferred until an unconditional RH closure exists under the
  requested build discipline

- 2026-07-22 -- proved the sharp `r >= -1` correction obstruction and formalized its critical
  renewal and finite-correction specializations.
