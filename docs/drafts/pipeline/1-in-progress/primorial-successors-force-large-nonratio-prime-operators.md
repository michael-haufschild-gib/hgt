# Primorial successors and the non-ratio prime operator

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Statement:** For the fixed explicit plateau and every `c>1`, the actual normalized
  non-ratio prime matrices have no horizon-uniform Euclidean operator-norm bound.
- **Scope:** The prime correction alone; no claim about the sign of the complete Weil form.
- **Lean draft:** `TransMetzlerWeilPositivity/FactorialSuccessorsForceUnboundedPrimeCorrections.lean`;
  finite-row lower bound, cofinal action divergence, and exact eventual-boundedness boundary.
  Supporting API and arithmetic scratch proofs passed; full module audit is pending.

## Candidate mechanism

Let `P` be the product of primes through `Y` and use horizon `N=P-1`. For each such prime `p`,
the coefficient at `n=P/p` has product `pn=P=N+1`. All these edges have the same profile lag,
approaching `1/c`, where the plateau autocorrelation is strictly positive. Their prime weights
are `log p/√p`. Distinct primes give distinct column indices. A lower bound on this one row's
squared Euclidean norm should therefore contain
`(bumpCorr φ(1/c)/∫φ²)^2 Σ_(p≤Y)(log p)^2/p`.

A convenient unconditional indexing choice is `P=2Y!`, `N=P-1`, and
`n_p=2(Y!/p)`, for `Y≥2`. Then `pn_p=P`, `2≤n_p≤N`, and `N≥Y`.
Since `n_p` divides `N+1`, it is coprime to `N`; neither index divides the other.
Consequently the exact-ratio kernel vanishes on every selected entry. Distinct primes
give distinct quotients. This version needs no separate primorial growth estimate.

The corpus already supplies the explicit divergence estimate
`Σ_(p≤Y)(log p)^2/p ≥ (log Y)^2/2 - 39 log Y - 25` in
`RHTower.Sieve.sum_prime_log_sq_div_ge` (`RHTower/Sieve/PrimeLogSqLower.lean`).
`CriticalArithmeticCorrelationTheory.fullWeilNonRatioMatrix` is the actual normalized
prime-pairing matrix minus the exact-ratio kernel. Its existing operator estimates cover `c≤1`.

## Remaining proof obligations

- Prove the selected prime terms survive subtraction of the ratio kernel, with exact
  normalization and a positive lower bound uniform over this row.
- Verify horizon membership, distinct quotient indices, and divergence of the chosen horizons.
- Transfer the row's squared norm to an actual Euclidean operator-norm lower bound.
- Audit all dependencies and formalize the result. No Lean claim is certified yet.

The existing logarithmic weighted-divisor-fiber law alone does not prove this conjecture:
its Schur weights are different from the Euclidean norm used here.

## Finite-row proof target

Write `N_Y=2Y!-1`, `Mφ=∫φ²`, and
`q(c,N)=bumpCorr φ(firstExteriorOverlap N/c)/Mφ`.
For every prime `p≤Y`, set `n_p=2(Y!/p)`. The negative-shift term at prime `p`
in the literal prime pairing is
`(log p/√p) w bumpCorr φ(firstExteriorOverlap N_Y/c)`.
Every other term is nonnegative. Since the exact-ratio kernel on `(N_Y,n_p)` is zero,
division by atom mass `wMφ` gives
`fullWeilNonRatioMatrix φ c N_Y (N_Y,n_p) ≥ q(c,N_Y) log p/√p`.

The distinct indices `n_p` therefore give the exact finite-horizon lower bound
`‖A_Y e_(N_Y)‖² ≥ q(c,N_Y)² Σ_(p≤Y)(log p)²/p`, using symmetry of the actual matrix.
For `c>1`, continuity and `firstExteriorOverlap N→1` give
`q(c,N_Y)→bumpCorr φ(1/c)/Mφ>0`. The existing explicit prime-sum estimate then forces
`‖A_Y e_(N_Y)‖→∞`, while `‖e_(N_Y)‖=1` and `N_Y≥Y`.
This proves the proposed cofinal obstruction once these exact entry and finite-sum identities
are kernel checked. No claim about the complete matrix follows by discarding its other terms.

## Candidate sharp boundary

The corpus already proves that the actual correction tends to zero in operator action,
uniformly for `0<c≤1`. A cofinal unbounded-action theorem for every fixed `c>1` would therefore
classify eventual operator boundedness exactly by `c≤1`. This would explain why even a small
fixed excess above touching cannot be paid by a horizon-uniform absolute operator bound,
while remaining compatible with positivity of the complete Weil form.

For the paid prefix `M≈N/c`, every fixed prime `p>c` eventually gives a selected column
`(N+1)/p≤M`, while row `N` lies in the tail. Removing the finitely many primes `p≤c`
does not remove divergence of the prime square sum. This suggests that the same obstruction
is already present in the mixed prime block of the actual prefix decomposition. Identifying
its relation to the complete mixed block and its inverse-prefix Schur cost remains open.
