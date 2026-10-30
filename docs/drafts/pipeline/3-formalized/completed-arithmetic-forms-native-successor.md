# Exact Gaussian successor reserves for the native theta tail

- **ID:** completed-arithmetic-forms-native-successor
- **Stage:** 3-formalized
- **Type:** THEOREM

## Gamma model

Write `(r)_n=∏_(j<n)(r+j)`. For the Hankel matrix `H_N(r)=[(r)_(i+j)]_(i,j<N)`,

`det H_N(r)=∏_(j<N) j! (r)_j`.

For moments `m_k=g w^k(r)_k`, with `g,w,r>0`, the exact order-`N` successor Schur
reserve is

`m_(2N)−vᵀH_N(m)⁻¹v = g w^(2N) N! (r)_N`.

Factor column `j` of `H_N(r)` by `(r)_j`. The remaining entry in row `i` is the monic
ascending factorial polynomial of degree `i` evaluated at `r+j`. Its determinant is the
Vandermonde of consecutive nodes. Evaluating monic falling factorials at `0,…,N−1`
gives an upper triangular matrix with diagonal `j!`, so that Vandermonde equals `∏j!`.
Diagonal scaling gives the determinant formula for `m`; the ratio of successive determinants
gives the Schur reserve. All head matrices are positive definite by the actual Gamma moment law.

## Native theta source

Let `f(x)` be the first theta source atom, `q(x)` its reflection scale, and `R_n(x)` the
complete native reflection jet. Define the literal balanced source moments

`σ_(s,k)(x)=(-1)^(s+k) R_(2(s+k))(x)/(f(x)² q(x)^(s+k))`.

At each fixed shift `s` and order `N`, their successor Schur reserve tends to

`C_(N,s)=16^(s+2N) (1/2)_s N! (s+1/2)_N > 0`.

The complete-source Gaussian jet limit gives entrywise convergence of each finite head
and successor. Determinants converge, the limiting head determinant is positive, and the
exact determinant quotient gives the stated limit. Consequently the balanced native reserve
lies between `C_(N,s)/2` and `3C_(N,s)/2` on a cofinal ray.

The comparison holds for the entire quadratic form. Writing `A_(N,s)(x)` for the
balanced native head and `G_(N,s)` for its Gamma limit, both

`A_(N,s)(x)−G_(N,s)/2` and `3G_(N,s)/2−A_(N,s)(x)`

are positive definite on a cofinal ray. Each difference converges entrywise to the
positive definite matrix `G_(N,s)/2`. Openness of finite-dimensional positive
definiteness proves the assertion. Thus one tail threshold controls every vector
in the fixed head, including all mixed entries, in the full Gamma norm.

The order and shift are fixed before choosing that ray. This is a quantitative reserve for
the literal native tail; it does not control the compact source region or an exhaustion in rank.

## Relative reserve and rank degeneration

For the scaled Gamma source, mass and dilation cancel from the ratio to the new diagonal:

`Schur_N(m)/m_(2N)=N!/(r+N)_N`.

If `r≥1/2`, every factor `r+N+j`, `j<N`, is at least `(3/2)(j+1)`.
Multiplication therefore gives

`N!/(r+N)_N≤(2/3)^N`.

The actual balanced native ratio converges to this exact value with `r=s+1/2`.
In particular it is eventually at most `2(2/3)^N` at each fixed rank and shift.
Thus absolute growth of the Gamma reserve coexists with exponential loss relative
to the new diagonal. A rank-uniform positive fraction of that diagonal cannot
be extracted from this tail model.

More precisely, for each fixed shift `s` and every `δ>0`, some finite rank has
native successor-to-diagonal ratio below `δ` on a cofinal ray. Hence no positive
`δ` works simultaneously for all ranks, even when each rank may choose its own
tail threshold. The positive comparison that survives is in the full Gamma
quadratic norm, together with the exact rank-dependent Schur reserve.

## Dependencies

- `gammaShapeMoment_momentHankelMatrix_posDef`.
- `det_ascPochhammerEvalMatrix`, `eval_fallingFactorialPoly`.
- `finiteHankelMatrix_succ_det_eq_schur`.
- `native_scaled_jet_tendsto`, `profile_signed_even_jet`.

Lean: `CompletedArithmeticForms/GammaSuccessorReserve.lean` and
`CompletedArithmeticForms/NativeTailReserve.lean`, particularly
`scaledGamma_successorSchur`, `nativeBalancedSuccessor_tendsto`,
`nativeBalancedHead_relative_posDef_eventually`, and
`not_native_rank_uniform_relative_reserve`.
Kernel dependencies: `propext`, `Classical.choice`, `Quot.sound`.
