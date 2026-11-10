# The minimal branch of the adelic Green kernel

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** B133: select the actual local Green kernel at and above the tempered edge.
- **Statement:** For `s≥1/2`, the actual vertex kernel `G_{p,s}` is the
  convergent weighted walk sum at `λ_s=p^s+p^(1−s)` and the least
  nonnegative supersolution of `(λ_s−A_p)u≥δ_x`. For `0<s<1/2`, it is
  a nonminimal point-source solution at the same eigenvalue as `G_{p,1−s}`.

## Proof

For `s>1/2`, the tempered profile dominates `G_{p,s}` because `0<R≤1`.
For `P=A_p/(p+1)`, powers of the tempered profile contract by
`ρ=2√p/(p+1)`. The weighted remainder therefore contracts by
`2√p/λ_s<1`; telescope to identify the walk sum and prove minimality.

At `s=1/2`, nonnegative weighted partial sums are bounded by the known
critical source kernel. Their sum dominates every supercritical walk sum.
Continuity of the explicit kernels as `s↓1/2` gives the reverse inequality.
Minimality follows by comparison with the same supercritical kernels.

Below `1/2`, `λ_s=λ_{1−s}` while the diagonal coefficient of `G_{p,s}`
is strictly larger. The reflected branch gives a smaller nonnegative
solution, so the lower branch is not minimal.

The surviving lower-branch remainder is exactly `G_{p,s}−G_{p,1−s}`:
it is nonnegative, harmonic for `λ_s−A_p`, strictly positive on the diagonal,
and is the limit of the weighted walk iterates of `G_{p,s}`. Thus the
classification also identifies the boundary term discarded by the walk sum.

## Lean status

`TheMinimalBranchOfTheAdelicGreenKernel.lean`, namespace `MinimalGreen`:

- `hasSum_above`, `hasSum_critical`, `hasSum_kernel`: actual weighted occupation sums,
  including pointwise convergence at the tempered endpoint.
- `localGreen_isLeast_of_half_le`, `minimal_branch_iff`: minimality exactly on
  the upper branch, among all nonnegative supersolutions without a growth hypothesis.
- `lower_branch_harmonic_defect`, `lower_branch_remainder_tendsto`: the exact
  nonnegative harmonic excess and its nonvanishing diagonal.
- `hasSum_weilPrimeKernel`: Weil's prime-power coefficient is the normalized
  critical occupation sum between actual apartment vertices.

Plain `lake --old env lean` passes without warnings. All seven audited
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
This identifies a pointwise minimal Green kernel, not a bounded Hilbert-space
inverse at the spectral edge. No global adelic gluing is claimed.
