# Finite-index periodic affine kernels have a zero-axis polynomial correction

- **ID:** AFFINE-CANONICAL-POLYNOMIAL-CORRECTION
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Relative Haar splitting](finite-index-haar-carriers-split-modulo-polynomial-kernels.md)
- **Statement:** Every Hermitian finite-index affine kernel with period-one translation reading has a unique polynomial-fibre kernel `Q`, zero on dilations, such that `k−Q` is right invariant under integer translations. This `Q` is Hermitian, has finite column rank, and vanishes on translations. Consequently `k−Q` is Hermitian of finite negative index and invariant under integer translations on both sides, with both axis readings unchanged.

## Construction

On the [finite period-defect space](../3-formalized/haar-period-defects-have-a-finite-affine-orbit.md), let `ρ` be the affine action, `w=v_(T_1)−v_1`, and `L` evaluation at identity. Then `f(g)=k(gT_1)−k(g)=Lρ(g)w`. Put `d=dim S` and `N=ρ(T_1)−1`. The existing rational unipotence and Newton-coefficient theorems give `ρ(T_t)=Σ_(j<d) binom(t,j)N^j`.

Take its Newton antiderivative, normalized to vanish at `t=0`:

`Q(D_aT_t)=Σ_(j<d) Lρ(D_a)N^j w · binom(t,j+1)`.

Each coefficient is a finite-dimensional dilation coefficient; its pullback by the slope homomorphism remains finite rank. The function `t(g)=b/a` has column rank at most two, since `t(x⁻¹g)=t(g)−b_x/a_g`. Finite-rank kernels are closed under sums, products, and polynomial evaluations: their column spaces lie in finite sums or products of finite-dimensional function spaces. Thus this formula gives finite rank of `Q`. The Newton difference identity gives `Q(gT_1)−Q(g)=f(g)`. The normalized polynomial primitives can also be obtained from the corpus's `surjective_shiftDiffPoly` and `eq_C_of_shiftDiff_eq_zero`.

## Hermitian and axis audit

Let `h=k−Q` and `Q*(g)=conj(Q(g⁻¹))`. For fixed rational slope `a=p/q≠0`, `h(a,·)` has period `a`, while `h*(a,·)` has period one. Both therefore have the common nonzero period `p`. Their difference `h−h*=Q*−Q` is polynomial on that fibre, hence constant; its value at zero vanishes because `Q` is zero on dilations. Thus `Q*=Q`. At slope one, `f` vanishes by the translation period of `k`, so the normalized antiderivative is zero. This gives both zero-axis identities. Uniqueness follows because a periodic polynomial is constant and the dilation normalization fixes that constant.

## Finite index of the remainder

Let `D=dim columnSpan(Q)`. Every sampled Gram matrix of `Q` has rank at most `D`, since its columns are evaluations of kernel columns. For every finite sample, intersect a maximal negative subspace of `gram(k−Q)` with the kernel of `gram(Q)`. This loses at most `D` dimensions, and on the intersection the forms of `k−Q` and `k` agree. Hence `κ(k−Q)≤κ(k)+D`; this is the corpus's matrix inequality `hermNegIndex_le_add_rank`. The Hermitian identity above makes the remainder a Hermitian finite-index kernel.

## Lean

[`AdelicKreinGeometry/Haar/PolynomialCorrection.lean`](../../../../formal/GaloisForLFunctions/AdelicKreinGeometry/Haar/PolynomialCorrection.lean) proves the complete result in `exists_zero_axis_polynomial_correction`. `polynomial_period_correction_unique` supplies uniqueness; `isHermKernel_of_polynomial_correction` proves the Hermitian normalization.

`HeckeKreinToeplitz/Index/FiniteColumns.lean` formalizes finite-rank closure under sums, products, polynomial evaluation, and homomorphism pullback. `BiarithmeticGeometry/Affine/PolynomialAntidifferences.lean` formalizes the normalized primitive of every finite-dimensional affine coefficient, including its finite rank and exact right difference. `BiarithmeticGeometry/Affine/PolynomialFibres.lean` proves closure under conjugate inversion and rigidity of periodic polynomial fibres. `HeckeKreinToeplitz/Index/FiniteRankPerturbations.lean` proves `κ(k−Q)≤κ(k)+dim columnSpan(Q)`. All have direct Lean checks and standard axiom closures.

The complete correction has a direct Lean audit with only `propext`, `Classical.choice`, and `Quot.sound`. The further decomposition of the bi-integer-invariant Haar remainder into a positive affine kernel plus a slope kernel remains open.
