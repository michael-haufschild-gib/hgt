# The sieve eigenbasis is density-weighted Ramanujan

- **ID:** sieve-eigenbasis-density-weighted-ramanujan
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** For supported positive integers `m,n` and a finite prime sieve `Q`, the existing complete eigenbasis satisfies `e_m(n)=sqrt(sieveDensity(Q)/n)·normalizedRamanujanMode(m,n)`.

## Proof

At a prime `p`, put `q=p^(-1/2)` and `v=v_p(n)`. The geometric ground coefficient is `sqrt(1-q²)q^v`. For conductor `p^k`, `k≥1`, the normalized Ramanujan value is `sqrt(φ(p^k))` times the valuation step: `1` for `v≥k`, `-1/(p-1)` for `v=k-1`, and `0` below. The identity `sqrt(φ(p^k))q^k=sqrt(1-q²)` shows that multiplication by the ground coefficient gives exactly the Blaschke coefficient: `(1-q²)q^(v-k)`, `-q`, or `0`, respectively. Conductor one gives the ground coefficient itself.

The complete sieve basis is the product of these local coefficients. Unique factorization reconstructs `m` from its prime powers. Ramanujan coefficients and totients are multiplicative across coprime conductors, so the normalized local modes multiply to the normalized mode of conductor `m`. The product ground weight is positive and its square is `sieveDensity(Q)/n`, proving the formula.

For `m=1`, the normalized mode is identically one. The ground vector has unit norm, so `Σ_(n supported on Q) sieveDensity(Q)/n=1`.

## Scope

`TheSieveEigenbasisIsTheRamanujanBasis.lean` proves `sieveAdjunctionBasis_eq_normalizedRamanujan` and the probability identity `hasSum_sieveClassDensity`. Direct Lean check passed; transitive axioms: `propext`, `Classical.choice`, `Quot.sound`. Imported by the theory umbrella.

This identifies the spectral coefficients used in the proved logarithmic conductor-tail estimate. Quantitative comparison with finite-horizon harmonic weights remains unproved.
