# Exact gaps for an arbitrary finite set of prime flips

- **ID:** ACP-FINITE-PRIME-SECULAR-GAP
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Source:** Single-prime secular classification; finite-prime harmonic density.
- **Statement:** Extend the exact constrained spectral gap from one flipped prime to every finite nonempty set of flipped primes.

For a finite prime set F put `c_F=prod_(p in F) (p-1)/(p+1)`.
The proposed normalized squared spectral weights are

`w_F(m)=4^(number of distinct prime factors of m)/phi(m)`

when every prime divisor of m belongs to F, and zero otherwise, with
w_F(1)=1. The actual squared coefficients should be `c_F^2 w_F(m)`.
The Möbius transform of the finite-flip sign is multiplicative; at p^k
its nontrivial local factor is `2(-1)^k` for p in F and zero otherwise.
This supplies the proposed coefficient formula from the existing finite
harmonic density count, after extending the mixed-coordinate bridge.

The squared mass identity should follow from the finite Euler product:

`sum_m w_F(m)=prod_(p in F)(1+4p/(p-1)^2)=1/c_F^2`.

The positive energies are `D_m=log m+tameDifferent(m)`. The proposed exact
gap is `min(2 log 2,alpha_F)`, where alpha_F is the unique first-gap root
of `-1/s+sum_(m>1) w_F(m)/(D_m-s)=0`. The empty set is the already proved
untwisted case and should be treated separately.

Required work: prove the mixed harmonic count for finite F; evaluate its
Möbius transform and total squared mass; order the first positive supported
energy; establish summability and root existence; transfer finite packets
to the whole actual resolvent; then prove the exact hyperplane gap. No
missing analytic or spectral input may become an assumption of the endpoint.

The corpus search for broader flip-gap results surfaced the existing
positive finite-prime density bound and cofinite zero-gap theorem, not this
exact finite-set classification. A dedicated source and literature audit
remains necessary. This card claims neither a closed paper proof nor Lean
formalization. Finish the current single-prime exact-gap audit first.

## Positive consequences to audit

The normalized weights increase when F grows. The root comparison should
therefore show that the greatest finite-flip gap decreases under inclusion
of flipped-prime sets, strictly below the universal ceiling whenever a new
local factor changes the active root.

For any fixed prime cutoff B, investigate whether flipping all primes
between B and Q makes the greatest finite-stage gap tend to zero as Q
grows. Every singleton beyond eleven has the maximal gap, so this would
isolate the effect of joint prime flips. The proposed secular proof uses
divergence of `sum 1/(m log m)` on integers coprime to the finitely many
primes below B: their positive reciprocal weights satisfy
`w_F(m)>=1/m` and `D_m<=2 log m`. Each fixed finite collection of those
conductors is eventually supported by the growing prime set. These
estimates and the series divergence still require exact proofs and audits.
Pointwise convergence to a cofinite zero-gap gauge alone does not prove
convergence of the finite-stage greatest gaps.

An infinite-prime extension requires a separate audit. Pointwise prime
exhaustion does not preserve gaps; convergence of finite-cutoff roots alone
cannot justify an infinite-gauge theorem. Any such extension must supply
its own horizon-uniform transfer and relative coefficient estimates.
