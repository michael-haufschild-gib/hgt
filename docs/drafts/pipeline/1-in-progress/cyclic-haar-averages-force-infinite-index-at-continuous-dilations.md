# Cyclic Haar averages force infinite index at continuous dilations

- **ID:** HAAR-CYCLIC-AVERAGE-INFINITE-INDEX
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Parent:** [Finite-index Mautner rigidity](finite-index-mautner-rigidity-for-the-haar-successor.md)
- **Statement:** A Hermitian rational affine kernel with integer Haar successor and a dilation reading continuous at one has infinite negative index.

## Reduction and positive subspaces

The formalized [normalized polynomial correction](../3-formalized/finite-index-periodic-affine-kernels-have-a-zero-axis-polynomial-correction.md) reduces a putative finite-index example to a bi-integer-invariant kernel with unchanged axis readings. In its column representation, every rational translation acts locally periodically. The [dilation-replication argument](bi-integer-invariant-haar-kernels-split-into-positive-and-slope-parts.md#positivity-of-the-moving-subspaces) makes each `range(T_b−1)` nonnegative.

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

The argument also covers every nonzero Haar multiple `c·1_ℤ`. Hermitian symmetry makes `c` real. For `c<0`, distinct rational translation cosets already give arbitrarily large negative diagonal Grams. For `c>0`, division by `c` preserves finite index and dilation continuity and normalizes the Haar reading.

## Verification boundary

Formalized, with direct audits and standard axiom closures:

- The normalized zero-axis polynomial correction.
- `HeckeKreinToeplitz/Index/ColumnInertia.lean`: every finite column-space Gram family retains the kernel's index bound.
- `HeckeKreinToeplitz/Index/LocallyPeriodicProjection.lean`: fixed and moving vectors are complementary; the fixed projection equals every complete orbit average and commutes with the operator's commutant.
- `HeckeKreinToeplitz/Index/ColumnProjections.lean`: fixed and moving vectors are orthogonal; the fixed projection is self-adjoint and its Gram entries are finite cyclic averages.
- `BiarithmeticGeometry/Affine/PeriodicTranslations.lean`: right integer invariance makes every rational translation locally periodic on the column space, with period `den(b/a)` on a column of slope `a`.
- `HeckeKreinToeplitz/Index/PeriodicDilationPositivity.lean`: if `t a=a t^m`, every `m`-periodic, zero-mean vector for `t` has nonnegative norm in a finite-index column representation.
- `AdelicKreinGeometry/Haar/TranslationMovingPositivity.lean`: a finite-index integer-invariant affine kernel is nonnegative on every rational translation difference range.
- `HeckeKreinToeplitz/Index/ColumnPositivity.lean`: Cauchy–Schwarz holds on every nonnegative column subspace.
- `AdelicKreinGeometry/Haar/CyclicOrbits.lean`: complete Haar translation orbits are orthogonal with the Haar scalar as squared norm; normalized fixed projections have squared norm `1/den(b/a)`.

- `AdelicKreinGeometry/Haar/CyclicHecke.lean`: squared moving-column correlations are bounded by the reciprocal denominator of the dilation ratio.
- `BiarithmeticGeometry/Affine/NearIdentityGrids.lean`: near-identity grid points share a rational lattice with explicit orbit denominators; reciprocal denominators are bounded by distance from one.

- `HeckeKreinToeplitz/Index/ConstantMatrixInertia.lean`: a constant perturbation of negative identity on `n+1` coordinates retains at least `n` negative directions.

- `AdelicKreinGeometry/Haar/CyclicGramLimit.lean`: near-identity fixed-projection Grams converge to `J−I`; every integer-invariant Haar kernel with continuous dilation reading has infinite negative index.

Required Lean results: removal of the integer-invariance restriction; positive-slope extension and the actual adelic restriction. The positive structural conclusions are the nonnegative moving subspaces and their finite cyclic bound. The stronger positive-plus-slope decomposition remains a separate conjecture.
