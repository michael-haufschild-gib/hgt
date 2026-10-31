# Cyclic Haar averages force infinite index at continuous dilations

- **ID:** HAAR-CYCLIC-AVERAGE-INFINITE-INDEX
- **Stage:** 1-in-progress
- **Type:** THEOREM
- **Parent:** [Finite-index Mautner rigidity](finite-index-mautner-rigidity-for-the-haar-successor.md)
- **Statement:** A Hermitian rational affine kernel with integer Haar successor and a dilation reading continuous at one has infinite negative index.

## Reduction and positive subspaces

The formalized [normalized polynomial correction](../3-formalized/finite-index-periodic-affine-kernels-have-a-zero-axis-polynomial-correction.md) reduces a putative finite-index example to a bi-integer-invariant kernel with unchanged axis readings. In its column representation, every rational translation acts locally periodically. The [dilation-replication argument](../3-formalized/bi-integer-invariant-haar-kernels-split-into-positive-and-slope-parts.md#positivity-of-the-moving-subspaces) makes each `range(T_b−1)` nonnegative.

Local periodicity gives the canonical projection `P_b` onto `Fix(T_b)` along `range(T_b−1)`, equal on each vector to its finite orbit average. It is self-adjoint for the column pairing `B` and commutes with every translation.

For the moving-space positivity, take `x=(T_b−1)y` with `T_b^m y=y`, and put `U=D_(1/m)`. Then `T_b U=U T_b^m`, `T_b^m x=x`, and `Σ_(j<m)T_b^j x=0`. Every `U^n x`, `n≥1`, is fixed by `T_b`, hence orthogonal to `x`. Isometry of `U` makes all distinct `U^i x` mutually orthogonal with the same norm. A negative norm would contradict finite negative index.

## Finite cyclic Hecke bound

Write `v_a=v_(D_a)`, with arbitrary nonzero rational `a` and `c` a nonzero natural multiple of `b`. Put `u_a=(1−P_b)v_a`, `u_c=(1−P_b)v_c`, and `d=den(c/a)`. The first `d` translates `T_(jc)v_a` are orthonormal by the Haar reading. Their projected fixed parts all equal `P_bv_a`. Consequently

`B(Σ_(j<d) T_(jc)u_a, Σ_(j<d) T_(jc)u_a) = d−d² B(P_bv_a,P_bv_a) ≤ d`.

Indeed, the `T_b` orbit of `v_a` has length `den(b/a)` and is orthonormal, so `B(P_bv_a,P_bv_a)=1/den(b/a)>0`.

Every summand has the same pairing with `u_c`, since `T_cu_c=u_c`. Also `0≤B(u_c,u_c)≤1`. Cauchy–Schwarz on the nonnegative moving subspace gives

`|B(u_a,u_c)|²≤1/d≤|c/a−1|` for `a≠c`.

The last inequality follows from the nonzero integer `num(c/a)−den(c/a)`. This estimate needs no affine-invariant limiting form or positive-plus-slope decomposition.

## Negative Gram limit

For a fixed finite index set take `a_(N,i)=1+i/(N+1)` and `b_N=1/(N+1)²`. Then `a_(N,i)/b_N=(N+1)(N+1+i)` is a positive integer. Haar averaging gives

`B(P_(b_N)v_(a_(N,i)),P_(b_N)v_(a_(N,i))) = 1/((N+1)(N+1+i)) → 0`.

For distinct `i,j`, the moving pairing tends to zero by the cyclic bound. Continuity of the original dilation reading gives `B(v_(a_(N,i)),v_(a_(N,j)))→1`. Orthogonality of fixed and moving parts therefore makes the projected Gram matrices converge to `J−I`. Their negative index is bounded by the column-space index, while `J−I` on `n+1` coordinates has `n` negative directions. Stability of negative inertia contradicts every finite bound.

## Positive slopes and adelic carriers

The positive-slope subgroup has two cosets, represented by identity and dilation by `−1`. Extending its kernel by zero gives a Hermitian kernel on the full rational affine group and multiplies negative index by two, by the verified `negIndex_extendFromSubgroup` law. Translation readings and positive dilation readings are unchanged.

For the actual group `ℚ⁺ ⋉ (ℝ × 𝔸_f)`, embed rational translations by `b↦(0,b_f)` and retain rational dilations. This is an affine homomorphism because finite diagonal embedding is rational-linear. A rational diagonal belongs to `∏ₚℤₚ` exactly when its denominator is one: integrality at every height-one valuation implies membership in `ℤ`, and integers are integral everywhere. The critical finite Haar reading therefore pulls back to `1_ℤ`; the dilation reading is unchanged. Pullback cannot increase negative index, so the rational obstruction applies to this adelic group.

This reading is the actual Haar translation coefficient. For `U=∏ₚℤₚ` and additive Haar measure `μ(U)=1`, it is `∫_U 1_U(x−b) dμ(x)`. For `x∈U`, subgroup closure gives `x−b∈U ↔ b∈U`; the integral is therefore `1_U(b)`. This identifies the required translation reading without assuming an unproved integral formula.

The argument also covers every nonzero Haar multiple `c·1_ℤ`. Hermitian symmetry makes `c` real. For `c<0`, distinct rational translation cosets already give arbitrarily large negative diagonal Grams. For `c>0`, division by `c` preserves finite index and dilation continuity and normalizes the Haar reading.

## Verification boundary

Formalized, with direct audits and standard axiom closures:

- `BiarithmeticGeometry/Affine/PositiveAffineIndex.lean` and `PositiveAffineAction.lean`: positive slopes have index two; injective rational-linear translation maps induce injective positive affine homomorphisms.
- `AdelicKreinGeometry/Haar/AdelicObstruction.lean`: `not_exists_finite_index_adelic_haar_coefficient_weil_state` excludes the actual nonzero finite-adelic Haar coefficient and pure Weil dilation reading on `ℚ⁺ ⋉ (ℝ × 𝔸_f)`, with positive rational scalars acting on both components. Integrality of a rational diagonal is proved equivalent to denominator one.
- `AdelicKreinGeometry/Haar/FiniteAdelicReading.lean`: `finiteAdelicHaarTranslation_eq` identifies the actual normalized Haar overlap integral with the integral-adele indicator.
- `AdelicKreinGeometry/Haar/PositiveAffineObstruction.lean`: `negIndex_posAffine_eq_top_of_nonzero_haar_continuous_dilation` transfers the obstruction to positive slopes by extension with index bound `2r`.
- `AdelicKreinGeometry/Haar/ScaledHaarObstruction.lean`: every nonzero Haar multiple has infinite index with continuous dilations. Negative scalars already have infinite translation index; positive scalars normalize to the integer successor.
- `AdelicKreinGeometry/Haar/FiniteIndexObstruction.lean`: `negIndex_eq_top_of_haar_continuous_dilation` proves the stated rational-affine obstruction without an integer-invariance premise, using the zero-axis polynomial correction.
- `AdelicKreinGeometry/Haar/CyclicGramLimit.lean`: fixed-projection Grams converge to `J−I`. `BiarithmeticGeometry/Affine/NearIdentityGrids.lean` supplies the rational grids; `HeckeKreinToeplitz/Index/ConstantMatrixInertia.lean` supplies their limiting negative directions.
- `AdelicKreinGeometry/Haar/CyclicHecke.lean`: squared moving-column correlations are bounded by the reciprocal denominator of the dilation ratio. Its inputs are cyclic orthogonal projections, moving-subspace positivity, Haar orbit norms, and Cauchy–Schwarz.

The [unique positive/slope/polynomial decomposition](../3-formalized/finite-index-haar-carriers-split-modulo-polynomial-kernels.md) and exact residual index are formalized. The [sharp punctured-limit classification](../3-formalized/finite-index-haar-dilation-limits-are-exactly-nonpositive.md) gives precisely real limits `L≤0`, with minimum index zero at `L=0` and one at `L<0`. The [subgroup-indicator classification](../3-formalized/continuous-affine-dilations-classify-subgroup-indicator-successors.md) is also formalized: finite-index continuous-dilation carriers exist exactly for `H={0}` and `H=ℚ`, both with positive witnesses. Only the completed paper proof of [proper-subgroup polynomial index preservation](proper-subgroup-carriers-preserve-polynomial-fibre-indices.md) still awaits its Lean audit.
