# A rational-prime one-off with unit counting density

- **Stage:** 0-backlog
- **Type:** CANDIDATE
- **Statement:** Strengthen `RationalPrimeOneOff.exists_rational_prime_multiplicative_linear_count_one_off` to counting density `A=1`, preserving natural multiplicative coefficients and its exact zero pair on `Re s>17/30`.

## Candidate mechanism

Finite changes of prime factors preserve the divisor on `Re s>0`. Adding finitely many factors at `2` raises the residue. Deleting a finite prefix of the original prime labels should then place it in `[1/2,1)`; divergence of their reciprocal sum follows from the original atom divergence and the summable rounding correction at `1`.

For a remaining logarithmic correction `δ∈(0,log 2]`, choose a prime of size comparable to `1/δ` and subtract `log(p/(p−1))`. Bertrand's theorem should make the remainders decrease geometrically while staying positive. The selected prime norms then grow geometrically, so their Euler product converges normally on every `Re s>0`, is nonvanishing there, and has the prescribed value at `1`.

## Proof bounds

For `0<δ≤1`, take the least prime `p≥4/δ`. Bertrand gives `p≤10/δ`.
The logarithmic increment satisfies
`δ/10≤1/p≤log(p/(p−1))≤1/(p−1)≤δ/3`.
Thus the new remainder lies in `[2δ/3,9δ/10]`. Telescoping gives the exact
logarithmic product value; the geometric remainder bound makes `Σp_n^(-a)`
converge for every `a>0`.

Finite prefix deletion first makes the original residue at most `1`; divergence
of its reciprocal prime sum ensures such a prefix exists. If its logarithmic
deficit exceeds `1`, split that deficit into finitely many pieces. Multiplying
the corresponding sparse Euler products changes the residue to `1` and leaves
the divisor unchanged on the positive half-plane.

## Missing formal work

Prove the greedy recursion bounds, the exact product value, prefix residue reduction, and the coefficient-preserving assembly of prime labels. No unit-density theorem is claimed yet.
