# Finite-index Haar dilation limits are exactly nonpositive

- **ID:** HAAR-PUNCTURED-DILATION-LIMITS
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** [Canonical Haar splitting](finite-index-haar-carriers-split-modulo-polynomial-kernels.md); `AdelicKreinGeometry/Haar/ContinuousDilationsNeedInfiniteIndex.lean`.
- **Statement:** A complex number is the punctured real-topology limit at one of the positive-rational dilation reading of a Hermitian finite-index integer-Haar kernel exactly when it is real and nonpositive. The least possible index is zero for limit zero and one for every negative limit. Every such kernel has identity value one, so an existing punctured limit differs from it by at least one.

## Proof route

The limit is taken through positive rational units other than one, in the usual real topology. Inversion preserves this punctured approach, so Hermitian symmetry makes the common limit `L` real.

The zero-axis polynomial correction preserves dilation values and leaves an integer-invariant finite-index Haar kernel. On every fixed near-identity grid, its cyclic fixed-projection Gram has diagonal tending to zero. The moving off-diagonal pairings tend to zero by the reciprocal-denominator bound, while the full off-diagonal pairings tend to `L`. Hence the fixed-projection Grams tend to `L(J−I)`. If `L>0`, their zero-sum hyperplanes give arbitrarily large negative dimension. Lower semicontinuity contradicts finite index. Thus `L≤0`. This argument uses the audited cyclic projections directly and is independent of canonical splitting.

For every positive Haar carrier `P`, the audited bound `|P(D_u)|²≤|u−1|` gives punctured limit zero: choose `δ=ε²` in the limit definition.

Conversely, for `a≥0`, use `k=P+a(δ_1−1)∘slope`, where `P` is the Haar state and `δ_1` is the positive identity indicator on rational units. The slope correction has index at most one: its restriction to the coefficient-sum-zero hyperplane is positive. If `a>0`, its Gram on two distinct units has one negative square. Exact Haar slope-index preservation therefore gives index one and punctured limit `−a`. Taking `a=0` gives a positive carrier with limit zero. A positive carrier cannot have a negative limit by the proved vanishing bound, so these indices are minimal.

The same explicit family has a sharp sign transition: `κ(k_a)=0` for `a=0`, `1` for `a>0`, and `∞` for `a<0`. In the last case its punctured limit `−a` is positive, so the cyclic Gram obstruction applies. The same cyclic Gram obstruction proves this third case.

## Lean verification

- `AdelicKreinGeometry/Haar/PuncturedLimits.lean`: `HasPuncturedDilationLimit`, `haar_punctured_limit_real_nonpositive`, and `hasPuncturedDilationLimit_zero_of_positive` prove the limit transport, real nonpositive constraint, and positive-carrier vanishing.
- `HeckeKreinToeplitz/Index/SubgroupJumpKernels.lean`: `negIndex_scaled_subgroupJumpKernel` computes the one-square correction.
- `AdelicKreinGeometry/Haar/SharpDilationLimits.lean`: `exists_finite_index_haar_punctured_limit_iff` gives the exact classification; `exists_haar_punctured_zero_index_zero`, `exists_haar_negative_limit_index_one`, and `one_le_negIndex_of_negative_punctured_limit` give sharp minimum indices. `negIndex_haarJumpCarrier` proves the full sign transition, and `one_le_norm_haar_identity_sub_punctured_limit` proves the identity gap.

All modules passed direct `lake --old env lean` checks. The printed transitive axiom closures contain only `propext`, `Classical.choice`, and `Quot.sound`. No assertion concerns a carrier whose punctured limit fails to exist.
