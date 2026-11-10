# Gaussian localization reverses the prime cross sign

- **ID:** b13-gaussian-prime-cross-sign
- **Stage:** 5-failed — invariant-sign transfer retired.
- **Type:** FALSIFIED transfer; positive limit THEOREM (Lean).
- **Obstacle:** B13 / centred cofactor cancellation.

## Exact obstruction and positive survivor

Let `w_η(n)=|pmPowerDampedRamanujanWeight η n|`, `η>0`, and
`D_p=p^(1+η)−1`. The corpus law gives total mass one and
`w_η(pn)=w_η(n)/D_p` when `p` is prime and does not divide `n`.
Let `χ_p(n)=1` on multiples of `p`, and `−1/D_p` otherwise.
For `r≥1`, set

`G_r,Q(n)=(n/Q)^(4r−1)exp(4[1−(n/Q)^2])`.

The even mask `A(n)=1_(2|n)` is invariant under every odd prime.
For positive integers it is the negative of the periodic cofactor
`P_2−P_1`, where `P_V(n)=Σ_(d|n,d≤V)μ(d)`.

Uniformly over every order `r≥1`,

`D_p Σ_(n≤2p) w_η(n)χ_p(n)A(n)G_r,2p(n) → w_η(2)>0`

as primes tend to infinity. In particular the cross form is eventually
strictly positive. This refutes the claim that prime invariance of the
cofactor mask alone preserves the negative cross sign after Gaussian
weighting.

The statement concerns the literal critical moment

`F_r(n)=(ε/t)^r n^(2r−1/2−it)exp(−εn²)`.

For `Re ε Q²=2`, Lean proves exactly

`|F_r(n)|²=|F_r(Q)|² G_r,Q(n)`.

For `t≠0`, the scale factor is positive. Hence the literal cross form
`Σ_(n≤2p)w_η(n)χ_p(n)A(n)|F_r(n)|²` is eventually positive,
uniformly over `r≥1`, `t≠0`, and every complex `ε` satisfying the scale
relation. The physical Gaussian sector is included.

## Dependency-closed proof

At `Q=2p`, the only nonzero even multiple of the odd prime `p` is
`2p`. Its scaled mass is `w_η(2)`, since `G_r,2p(2p)=1`.
The exact decomposition is

`scaled cross = w_η(2)−Σ_(n≤2p,p∤n,2|n)w_η(n)G_r,2p(n)`.

For `0≤n≤Q` and `r≥1`,

`0≤G_r,Q(n)≤exp(4)(n/Q)^3≤exp(4)`.

The absolute remainder is at most
`exp(4)Σ_(n≤Q)w_η(n)(n/Q)^3`, independently of `r`.
Dominated convergence against the summable mass makes this tend to
zero. The prime recursion and positive density give `w_η(2)>0`.
Finally, the exact complex-power and exponential norm formulas give
`|F_r(n)|²=|ε/t|^(2r)n^(4r−1)exp(−2 Re ε n²)`, proving the
literal Gaussian normalization and positivity.

## Lean and no-go closure

Module: `GaloisForLFunctions.ExceptionalLayerTheory.GaussianRamanujanPrimeCross`.
Main declarations:

- `gaussianEvenPrimeCross_eq_atom_sub`
- `eventually_gaussianEvenPrimeCross_near_atom`
- `norm_sq_gaussianHigherPrimeMomentWeight_eq_relative`
- `gaussianEvenMomentPrimeCross_scaled`
- `eventually_gaussianEvenMomentPrimeCross_pos`
- `evenMask_prime_invariant`

Direct source check passed without warnings. Seven transitive axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
The module is wired into its umbrella.

**New insight:** the Gaussian source-change term carries a surviving
positive prime atom; it cannot be discarded on cofactor invariance
alone. The positive survivor is the exact nonzero scaled limit, with
an error uniform in the moment order, proved for the actual weights.

**Scope:** positive damping and the cofactor mask are fixed. No joint
limit with damping tending to zero or with growing cofactor cutoffs is
claimed. The centred Vaughan cancellation bound and B13 remain open.
