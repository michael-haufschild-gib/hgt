# Null kernels of index one have subgroup zero sets

- **ID:** NULL-KERNEL-SUBGROUP
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Axis-invisible affine polynomials](axis-invisible-affine-polynomials-realize-arbitrary-finite-index.md)
- **Statement:** If a Hermitian group kernel satisfies `k(1)=0` and `κ(k)≤1`, then `{g : k(g)=0}` is a subgroup. Consequently, a nonzero Hermitian kernel on `Aff(ℚ)` vanishing on translations and dilations has index at least two.

## Dependency-closed paper proof

If the kernel is zero, its zero set is the whole group. Otherwise choose `w` with `z=k(w)≠0`. The Gram block on `1,w` is the hyperbolic plane `A=[[0,z],[conj z,0]]`, with one negative direction. For two zeros `x,y`, the four-point Gram matrix has blocks `[[A,B],[B*,C]]`, where the first row of `B` vanishes and `C=[[0,k(x⁻¹y)],[conj k(x⁻¹y),0]]`.

The inverse of `A` has zero diagonal, so `B*A⁻¹B=0`. Haynsworth additivity gives negative index `1+κ(C)`. The global bound forces `κ(C)=0`. A nonzero off-diagonal entry in a zero-diagonal Hermitian two-by-two matrix gives one negative direction, so `k(x⁻¹y)=0`. The zero set contains identity and is closed under `x⁻¹y`, hence is a subgroup.

Every affine element is a translation followed by a dilation. If both subgroups are contained in the zero set, the zero set is the whole affine group. Contraposition and the integral nature of the index give the lower bound two.

## Scope

This is an algebraic rigidity law for kernels normalized by `k(1)=0`, not a classification of Haar-successor carriers, whose identity value is one. The linear polynomial candidate in the parent card would attain the lower bound.

## Lean

- `HeckeKreinToeplitz/Index/NullKernelRigidity.lean`: `inv_mul_eq_zero_of_negIndex_le_one`, `nullKernelZeroSubgroup`, `eq_zero_of_subgroup_readings`.
- `AdelicKreinGeometry/Haar/AxisInvisibility.lean`: `eq_zero_of_zero_axes_of_negIndex_le_one`, `two_le_negIndex_of_zero_axes`.
- Both direct `lake --old env lean` checks pass. All five declarations depend only on `propext`, `Classical.choice`, and `Quot.sound`. Both modules are wired into their umbrellas.
