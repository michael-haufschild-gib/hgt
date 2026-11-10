# Gaussian localization reverses the prime cross sign

- **ID:** b13-gaussian-prime-cross-sign
- **Stage:** 1-in-progress
- **Type:** CONJECTURE under proof.
- **Obstacle:** B13; attempted transfer of invariant Ramanujan covariance.

## Candidate and positive statement

Let `w_η(n)=|pmPowerDampedRamanujanWeight η n|`, `η>0`, and
`D_p=p^(1+η)−1`. The exact corpus law gives total mass one and
`w_η(pn)=w_η(n)/D_p` when `p` is prime and does not divide `n`.
Let `χ_p(n)=1` on multiples of `p`, and `−1/D_p` otherwise.

For `r≥1`, set

`G_r,Q(n)=(n/Q)^(4r−1)exp(4[1−(n/Q)^2])`.

This is the squared norm of the critical-abscissa Gaussian moment at
`n`, divided by its squared norm at `Q`, when `Re ε Q²=2`.
The even-cofactor mask `A(n)=1_(2|n)` is invariant under every odd prime.
It is, up to sign, the periodic extension `P_2−P_1` of the actual
short cofactor at cutoffs `V=1`, `W=2`.

The proposed exact sign law is, uniformly in every order `r≥1`,

`D_p Σ_(n≤2p) w_η(n) χ_p(n) A(n) G_r,2p(n) → w_η(2)>0`

as primes `p→∞`. Hence the Gaussian-weighted cross form is strictly
positive at all sufficiently large odd primes. Prime invariance of the
cofactor mask alone does not preserve the negative cross-form theorem.

## Proof mechanism

At cutoff `Q=2p`, the only nonzero even multiple of the odd prime `p`
is `2p`. Its scaled mass is exactly `w_η(2)`, since `G_r,2p(2p)=1`.
All remaining entries are nonpositive. For `0≤n≤Q` and `r≥1`,

`0≤G_r,Q(n)≤exp(4)(n/Q)^3≤exp(4)`.

The remaining absolute mass is bounded, independently of `r`, by
`exp(4) Σ_(n≤Q) w_η(n)(n/Q)^3`. This tends to zero: split the
summable mass into a fixed finite head and a small tail, then let `Q`
grow. No prime-distribution estimate or zero-location input is used.

## Scope

This tests a specific sign-transfer proposal, not the centred Vaughan
bound itself. The positive survivor is the exact nonzero scaled limit,
uniform in the Gaussian moment order. Its connection to the literal
complex moment and the transitive Lean audits remain to be completed.
