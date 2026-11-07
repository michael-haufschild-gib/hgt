# Conductor control of radial regularization

- **ID:** hhac-conductor-controlled-regularization
- **Stage:** 1-in-progress
- **Type:** CANDIDATE

## Exact target

For primitive torsion orbits of orders `m,n`, the inverse squared chord cost
of distinct ordered pairs satisfies

`C(m,n) ≤ (mn)² c(m,n)`.

Together with the finite-radius decomposition this gives a conductor-explicit
error bound, including for signed finite pairings. The constant is deliberately
coarse; the point is uniformity as the conductors grow.

## Paper proof

If `u≠1`, `|u|=1`, and `u^L=1` with `L>0`, the geometric sum is zero.
Therefore `L=Σ_{k<L}(1−u^k)`. Telescoping gives
`|1−u^k|≤k|1−u|≤L|1−u|`, so `1≤L|1−u|`.
Consequently `|1−u|⁻²≤L²`.

For distinct `z∈O_m`, `w∈O_n`, take `u=z conjugate(w)` and `L=mn`.
Both orders are positive, `u^L=1`, and `|1−u|=|z−w|`.
Sum the preceding bound over the actual punctured orbit pairs.

The signed-pairing radial error is thus bounded by
`(1−r)²/(2r) Σ |a(m,n)|(mn)² c(m,n)`.
This removes geometric separation constants from the finite-radius certificate.
It does not control the diagonal self-energy or prove a global positive height.

## Prior work and proof status

The corpus already proves a sharper trigonometric root-separation bound in
`RHTower.RootOfUnityIntervalCompletion.norm_exp_sub_one_ge`.
The elementary geometric-sum argument here avoids angular parametrization;
its application to the new radial remainder is the proposed tool.
Lean formalization remains required.
