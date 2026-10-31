# Axis-invisible finite-index kernels have finite rank

- **ID:** AXIS-INVISIBLE-FINITE-RANK
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Axis-invisible affine polynomials](axis-invisible-affine-polynomials-realize-arbitrary-finite-index.md)
- **Statement:** Let `G=HD`, with `H` normal and `D` a subgroup. A Hermitian kernel vanishing on both subgroups and having negative index at most `r<∞` has column span of dimension at most `r²`. Consequently every finite Gram matrix has rank at most `r²`.

## Dependency-closed paper proof

Write `v_g(x)=k(x⁻¹g)`. The finite-index decomposition supplies `Φ:G→ℂʳ` such that `P(x,y)=k(x⁻¹y)+⟨Φ(x),Φ(y)⟩` is positive semidefinite. If `a_j∈H` and `Σc_jΦ(a_j)=0`, then the corresponding `P`-quadratic form vanishes: all `k(a_i⁻¹a_j)` vanish. Positivity makes this combination orthogonal to every point. Its feature pairing also vanishes, so `Σc_jv_(a_j)=0`.

Choose a basis of `span Φ(H)` among its generating vectors. Its cardinality is at most `r`; the preceding relation transfer shows that the corresponding columns span all `H`-columns. The same argument supplies at most `r` generators `v_(d_j)` for the `D`-columns.

Left translation acts linearly on columns by `L_av_b=v_(ab)`. For `g=hd`, expand `v_d` in the `D`-generators. Normality gives `hd_j=d_j(d_j⁻¹hd_j)` with `d_j⁻¹hd_j∈H`. Expanding these `H`-columns shows that all columns lie in the span of the at most `r²` columns `v_(d_jh_i)`. Evaluation on a finite family cannot increase dimension, proving the Gram-rank bound.

## Lean

`HeckeKreinToeplitz/Index/NullSubgroupRank.lean` proves `exists_null_subgroup_column_generators`, `exists_column_generators_of_zero_subgroups`, `finite_columnSpan_of_zero_subgroups`, and `rank_gram_le_square_of_zero_subgroups`.

`AdelicKreinGeometry/Haar/FiniteRankPerturbations.lean` specializes these to `Aff(ℚ)` in `finite_columnSpan_of_zero_axes` and `rank_gram_le_square_of_zero_axes`.

Both leaf files pass direct `lake --old env lean` checks. All six declarations use only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella imports are wired.

## Scope

This treats zero axis readings, not arbitrary Haar-successor carriers. The [polynomial-fibre theorem](finite-rank-affine-kernels-have-polynomial-translation-fibres.md) proves that these finite-rank kernels are polynomial along each translation fibre.
