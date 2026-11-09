# Odd ordinate relations force annihilator frequency cost

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacles:** B13, B112; simultaneous positive annihilation of finite vertical patterns.
- **Statement:** For an odd list of `q` target ordinates, put `Delta=abs(sum gamma_j)`, let `H` be positive tail mass at abscissa `beta`, and let `J=sum w_d log(n_d)` be its first logarithmic moment. If every target evaluation has norm at most `epsilon`, then `2H <= Delta J + q sqrt(2H(H-1+epsilon))`. Signed repetitions encode arbitrary odd integer relations. Exact zero-sum lists therefore force `(q^2-2)H >= q^2` at exact annihilation.
- **Novelty:** The consecutive-harmonic and sparse first/fourth-harmonic bounds do not control arbitrary approximate additive relations or the first frequency moment. This candidate retains relation error and weighted frequency cost together.

## Mechanism

For a monomial of log frequency `L`, multiply its `q` target phases. Their product is `exp(-i L sum gamma_j)`, while the product of `q` ideal cancelling phases is `-1`. Telescoping gives
`2 <= L Delta + sum_j abs(1+exp(-i L gamma_j))`.
Integrate against the positive damped coefficients. At each target, the exact squared phase defect is `2(H-1+Re P(beta+i gamma_j))`. Weighted Cauchy-Schwarz bounds the first phase defect by `sqrt(2H(H-1+epsilon))`, giving the claimed tradeoff.

## Proof gate

Check the product estimate, exact phase-energy identity, and weighted Cauchy-Schwarz against corpus statements. Formalize the general accuracy tradeoff and exact-relation mass gap together; no result counted yet.
