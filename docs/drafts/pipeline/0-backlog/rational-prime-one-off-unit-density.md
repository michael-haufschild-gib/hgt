# A rational-prime one-off with unit counting density

- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Statement:** Strengthen `RationalPrimeOneOff.exists_rational_prime_multiplicative_linear_count_one_off` to counting density `A=1`, preserving natural multiplicative coefficients and its exact zero pair on `Re s>17/30`.

## Candidate mechanism

Finite changes of prime factors preserve the divisor on `Re s>0`. Adding finitely many factors at `2` raises the residue. Deleting a finite prefix of the original prime labels should then place it in `[1/2,1)`; divergence of their reciprocal sum follows from the original atom divergence and the summable rounding correction at `1`.

For a remaining logarithmic correction `δ∈(0,log 2]`, choose a prime of size comparable to `1/δ` and subtract `log(p/(p−1))`. Bertrand's theorem should make the remainders decrease geometrically while staying positive. The selected prime norms then grow geometrically, so their Euler product converges normally on every `Re s>0`, is nonvanishing there, and has the prescribed value at `1`.

## Missing formal work

Prove the greedy recursion bounds, the exact product value, prefix residue reduction, and the coefficient-preserving assembly of prime labels. No unit-density theorem is claimed yet.
