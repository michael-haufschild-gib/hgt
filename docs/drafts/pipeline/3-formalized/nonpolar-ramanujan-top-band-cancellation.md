# Nonpolar Ramanujan top-band cancellation

- **ID:** SSH-RAMANUJAN-TOP-BAND
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/review-3010/obstacles-summary.md` Q1/A1.
- **Statement:** For conductor `m>1`, the joint shell–pole coefficient on
  `u_m+ηu_m1_T` is at most `Kφ m φ(m) G(1+log N)` in absolute value,
  uniformly for `1≤c≤N/4` and `N≥8`, where `u_m(n)=c_m(n)/√(φ(m)n)`.

## Paper argument

For a bounded base coefficient `a`, group the Mangoldt sum by its product:
`H_a(ℓ)=Σ_(d|ℓ,ℓ/d≤N) Λ(d)a(ℓ/d)` satisfies
`|H_a(ℓ)|≤B log ℓ` whenever `|a|≤B`.
Sum first over the perturbed top-band partner `n`, keeping `ℓ` fixed.
A mean-zero periodic coefficient `ψ`, bounded by `U` with period `q`, has
partial sums bounded by `2qU` on every interval. Abel summation gives
`|Σ_(n∈T) ψ(n)n^(-1/2)β(log ℓ−log n)|≤Cφ qU G/√ℓ`.

The summation interval intersects `[ℓe^(-w),ℓe^w]`; its length is
`O(wℓ+1)`. The kernel derivative is `O((G+A₁)/ℓ^(3/2))`.
Visible products satisfy `N/2<ℓ≤2N`, so `wℓ≥c/2≥1/2` absorbs the boundary
cost. The identity `G=w∫φ²` removes overlap dependence. Bounded harmonic
mass on `[N/2,2N]` then gives `Oφ(BqU G(1+log N))` for the shell coefficient,
including the removed ratio term.

Choose `A₁≥0` bounding the derivative of the profile autocorrelation and put
`r=1/4+A₁/∫φ²`. Abel summation bounds the weighted partner sum by
`(4+56r)qUG/ℓ`: its interval has length at most `7wℓ`, and
`w(G+A₁)≤rG`. There are at most `2N` visible products, each exceeding
`N/2`, so their total costs at most `4(4+56r)BqUG(1+log N)`.
The removed ratio diagonal costs at most `2BUG log N`.

Both polar cross terms retain their literal moments. The base moments are
bounded by `B(1+log N)` and `BN`; the top-band moments are bounded by
`4qU/N` and `2qU`. The atom's moment product is at most `4wG≤G`.
Their combined cost is at most `6BqUG(1+log N)`.
Thus `Kφ=24+224r` pays the joint coefficient. This holds for an arbitrary
bounded base `a` and an independent mean-zero periodic perturbation `ψ`.
For the normalized Ramanujan mode, `B=U=√φ(m)` and `q=m`.

The actual shell–pole block has linear term `2η` times this coefficient.
Its quadratic term is exactly twice the product of the two perturbed pole
moments: the top band never occurs as a nonzero shell base.

## Lean

Three modules in `SuccessorShellArithmetic/TopBand/`:

- `PeriodicShellWindows`: `abs_topBand_shellPartnerKernel_sum_le`.
- `WeightedBaseCollapse`: `shellTopCoefficient_eq_product_sum` and
  `jointBlock_topBandPerturbedProfile` retain every base coefficient,
  the removed ratio diagonal, and both exact pole moments.
- `NonpolarJointCancellation`:
  `exists_abs_jointTopCoefficient_le_uniform_overlap`,
  `exists_abs_ramanujan_jointTopCoefficient_le`, and
  `jointBlock_ramanujanTopBandProfile`.

All three passed direct `lake --old env lean` checks. Every capstone's
transitive axioms are exactly `propext`, `Classical.choice`, and `Quot.sound`.
The modules are wired into the umbrella. The full agreement-shell
decomposition remains separate.
