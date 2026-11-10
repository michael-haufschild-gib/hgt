# A complete arithmetic bound for Gaussian prime blocks

- **Obstacle:** B13.
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)

## Statement

Let `σ,α,ξ≥0`, `t>0`, `U<A≤B`, and `B−1≤L`. Put

`W(n)=n^(−σ) exp(−αn²+i(ξn²−t log n))`,
`c=Λ_{≤U}*μ_{≤V}`, `a=Λ−Λ_{≤U}`, `b=δ−𝟙*μ_{≤V}`.

For `1≤P≤Q`, set

`λ=ξ/π+t/(2πQ²)`, `H=(ξ/π+t/(2πP²))/λ`,
`D(ξ,t;P,Q)=min(Q−P,8(Q−P)H√λ+12/√λ)`.

For each divisor `k`, let `P_k=(A−1)/k+1`, `Q_k=(B−1)/k+1`
using natural division, and define

`F_k=k^(−σ) P_k^(−σ) exp(−αk²P_k²) D(ξk²,t;P_k,Q_k)`.

Then

`|Σ_{A≤n<B} Λ(n)W(n)| ≤ Σ_{k=1}^L [|c(k)|+2|μ_{≤V}(k)|log(Q_k−1)] F_k + √E`,

where `log 0=0` and

`E=(Σ_{d=1}^L |a(d)d^(−σ)|²)`
`  × Σ_{m₁,m₂=1}^L |b(m₁)m₁^(−σ)b(m₂)m₂^(−σ)| K(m₁,m₂)`.

Here `K` is the Gaussian pair bound already proved in
`../3-formalized/b13-gaussian-vaughan-bilinear-cancellation.md`:
on the intersection `[P,Q)` of both product-cutoff fibres within `[1,L+1)`,
it equals `exp(−α(m₁²+m₂²)P²) quadraticSumBound(Q−P,ξ(m₁²−m₂²))`.
Exact truncated coefficients retain their support without a further estimate.
No zero-location or finite-layer assumption enters the bound.

## Proof

The phase `g(x)=(ξx²−t log x)/(2π)` has derivative
`ξx/π−t/(2πx)` and second derivative `ξ/π+t/(2πx²)>0`.
On every prefix of `[P,Q)`, the second derivative lies in `[λ,Hλ]`.
For `λ≤1`, the corpus second-derivative test gives
`8(R−P)H√λ+12/√λ` on `[P,R)`. For `λ>1`, the trivial cardinality bound
is smaller than that expression because `H≥1`. Taking the smaller bound
and using `R≤Q` gives the uniform prefix bound `D`.

The weight `x^(−σ)exp(−αx²)` is nonnegative and decreasing on `x≥1`.
Decreasing-weight Abel summation costs only its value at `P` and gives
uniform weighted-prefix control. Increasing-weight Abel summation for
`log n` costs at most `2 log(Q−1)`. Empty intervals contribute zero.

Dilation gives exactly

`W(ak)=k^(−σ)exp(−it log k) W_{σ,αk²,ξk²,t}(a)`.

Thus the two type-I fibres have bounds `F_k` and `2F_k log(Q_k−1)`.
Exact divisor rearrangement and triangle inequalities give the displayed
outer coefficient sums. Vaughan's block identity is
`Λ=−𝟙*c+log*μ_{≤V}+a*b` above `U`. Its third term has squared norm at
most `E` by the Gaussian bilinear theorem. Taking a square root and adding
all three bounds proves the claim.

If `H√λ≤1/32` and `(Q−P)√λ≥48`, then `D≤(Q−P)/2`:
the two curvature terms are separately at most `(Q−P)/4`.
This strict type-I saving retains the entire initial Gaussian factor.

## Scope

For `ε.re≥0` and `ε.im≤0`, choose `α=ε.re`, `ξ=−ε.im`.
The weight is exactly `n^(−σ−it)exp(−εn²)`. Hence the estimate applies
to the literal complex Gaussian Dirichlet block, including lower-half
interior rotations.

This closes the missing Gaussian type-I estimates and assembles an
independent bound for a complete block. It does not establish an improved
asymptotic bound for the complete filtered current. Dyadic aggregation,
infinite tails, pole cancellation and all contracting filter factors must
survive before comparison with the selected divisor signal. B13 remains open.

## Lean status

In namespace `GaloisForLFunctions.ExceptionalLayerTheory`:

- `GaussianVaughanTypeI.lean`: `norm_sum_gaussianPrimePhase_zero_prefix_le`,
  `norm_sum_gaussianPrimeWeight_prefix_le`, `norm_sum_log_gaussianPrimeWeight_le`,
  `gaussianPrimeWeight_dilate`, `norm_sum_gaussianPrimeWeight_fibre_le`,
  `norm_sum_log_gaussianPrimeWeight_fibre_le`, `gaussianTypeIBound_le_half`.
- `GaussianVaughanPrimeBlocks.lean`: `norm_gaussian_vonMangoldt_block_le`,
  `norm_complexGaussian_vonMangoldt_block_le`,
  `norm_rotatedGaussian_vonMangoldt_block_le`.

Both modules pass final `lake --old env lean` source audits without warnings.
All ten printed transitive axiom lists contain only `propext`,
`Classical.choice`, and `Quot.sound`. Both modules are imported by the
programme umbrella; the umbrella was not compiled.
