# A logarithmic finite-rank critical collar

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Wall:** Σ6
- **Target:** There is `c>0`, independent of rank, such that every actual signed theta Hankel section of size `n≤N` is positive definite whenever `|a−1/2| < c/(1+log(N+1))`.

The checked Xi logarithmic-derivative sign is nonnegative on
`Re s ≥ 1−1/[58 log(|Im s|+1/2)]` above height four, and on the
whole low-height rectangle. Hence the actual Fourier current is
nonnegative on `|b|≤T` when `a` lies in the corresponding collar.
A fixed small interval retains a positive current floor by continuity.

The remaining negative tail has an exponential majorant. For a polynomial
of degree below `N`, its quadratic contribution is bounded by
`C N K^(2N)(2N)! exp(−κT)‖v‖²`. The compact positive interval supplies
`m r^(2N+1)‖v‖²/[N!((2N)!)^N]`, by the factorial coercivity argument.
Taking `T=D(N+1)^3` should make the tail smaller than half this floor,
with fixed `D`. The zero-free collar then has width comparable to
`1/(1+log(N+1))`.

**Unproved:** the signed truncation comparison, uniform tail estimate,
and rank-uniform factorial/exponential comparison. No logarithmic collar
has been formalized. The factorial collar is the existing weaker bound.
