# SC finite skew-adjoint additive determinant no-go

- **ID:** SC-FSA-NOGO
- **Stage:** 3-formalized
- **Type:** FALSIFIED
- **Source:** `../1-in-progress/rh-current-frontier-map.md` · SC
- **Statement:** No cutoff-dependent sequence of finite-rank entire centered trace-free additive matrix stages with holomorphic skew-adjoint reflection can converge compact-open to normalized centered Xi through ordinary determinants.

## RH chain closed

`finite trace-free skew-adjoint additive SC stages → Xi determinant landing → SC divisor/orientation endpoint → RH`

The first arrow is impossible.

## Proof

For `K=M′(0)`, complex Jacobi second variation and `tr M≡0` give
`(det(I+M))″(0)=−tr(K²)`. Reflection gives `Kⱼᵢ=−conj(Kᵢⱼ)`, hence
`−Re tr(K²)=∑ᵢⱼ|Kᵢⱼ|²≥0`. Rank may vary with cutoff. Cauchy convergence transfers this closed sign to the limit, contradicting the strictly negative central second jet of normalized Xi.

## Closure

- **Lean:** `RHTower.not_tendstoLocallyUniformly_finiteSkewAdjointAdditiveSCMatrix_normalizedXiC`
- **Module:** `GaloisForLFunctions.RHTower.SourceHorizontalHolomorphicFiniteSkewAdjointAdditiveNoGo`
- **Sharp survivor:** opposite Hermitian sign has the Xi-compatible curvature sign; non-trace-free completions, regularized infinite-dimensional determinants, and nondeterminantal readings remain open.
- **Novelty audit:** corpus search found only the rank-two case and separate determinant-jet/trace-square infrastructure. Targeted literature search through 2026-08-31 found general trace-ideal/Fredholm and RH determinant programs, but no dimension-free Xi-landing obstruction from this central sign law.
