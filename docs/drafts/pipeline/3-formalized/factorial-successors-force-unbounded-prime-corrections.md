# Factorial successors classify prime-correction boundedness

- **ID:** factorial-successors-force-unbounded-prime-corrections
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-2910/fable2.md`, §1.3; the actual CACT non-ratio matrix.
- **Statement:** For the fixed explicit plateau and `c>0`, the normalized non-ratio prime
  matrices have an eventual uniform Euclidean action bound exactly when `c≤1`.

## Finite-column proof

Let `N_Y=2Y!-1`, `Mφ=∫φ²`, and `q(c,N)=Cφ(t_N/c)/Mφ`, where
`t_N=N log((N+1)/N)`. For each prime `p≤Y`, set `n_p=2(Y!/p)`.
Then `pn_p=N_Y+1`, `2≤n_p≤N_Y`, `N_Y≥Y`, and distinct primes give distinct indices.
Neither `N_Y` nor `n_p` divides the other: a divisor of both consecutive integers would
divide one. Hence their exact-ratio kernel entry vanishes.

The selected negative-shift prime term in the literal pairing is
`(log p/√p)w Cφ(t_N/c)`. All other prime terms are nonnegative. Dividing by
atom mass `wMφ` gives the actual entry bound `A(N_Y,n_p)≥q(c,N_Y)log p/√p`.
Symmetry and summation over the distinct coordinates therefore give

`‖A e_(N_Y)‖² ≥ q(c,N_Y)² Σ_(p≤Y)(log p)²/p`.

For fixed `c>1`, continuity and `t_N→1` give
`q(c,N_Y)→Cφ(1/c)/Mφ>0`. The existing unconditional prime-sum theorem gives
`Σ_(p≤Y)(log p)²/p ≥ (log Y)²/2-39log Y-25`, which diverges.
Thus the image of this unit coordinate tends to infinity along a cofinal horizon sequence.
The existing uniform vanishing-action estimate for `0<c≤1` proves the converse and the
exact boundedness classification. No assertion about the complete Weil matrix sign follows
by dropping its archimedean or polar terms.

## Lean verification

Module: `GaloisForLFunctions/TransMetzlerWeilPositivity/FactorialSuccessorsForceUnboundedPrimeCorrections.lean`.
Main declarations:

- `fullWeilNonRatioMatrix_successor_entry_ge`;
- `factorialSuccessor_action_sq_ge`;
- `factorialSuccessor_action_atTop` and `exists_large_fullWeilNonRatio_action`;
- `eventually_bounded_fullWeilNonRatio_action_iff`.

Direct `lake --old env lean` check passed with default limits. All four transitive axiom
audits contain only `propext`, `Classical.choice`, `Quot.sound`.
Imported by the TransMetzlerWeilPositivity umbrella.

## Open extension

For a paid prefix `M≈N/c`, the same prime coordinates suggest unboundedness already
in the mixed prime block after removing finitely many primes. A precise prefix schedule,
uniform membership argument, and relation to the complete mixed block and inverse-prefix
Schur cost remain unproved. They are outside the theorem above.
