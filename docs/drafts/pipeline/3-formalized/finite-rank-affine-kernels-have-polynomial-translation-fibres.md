# Finite-rank affine kernels have polynomial translation fibres

- **ID:** AFFINE-FINITE-RANK-POLYNOMIAL
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** [Axis-invisible affine kernels](axis-invisible-affine-polynomials-realize-arbitrary-finite-index.md)
- **Statement:** A nonzero function `k:Aff(ℚ)→ℂ` with column-space dimension `d<∞` has, for each slope `u`, a polynomial `P_u∈ℂ[X]` of degree less than `d` such that `k(T_bD_u)=P_u(b)` for every rational `b`. No continuity or Hermitian hypothesis is needed.

## Paper argument

Left translation preserves the column space: `L_av_g=v_(ag)`. Evaluation at identity recovers the kernel from this cyclic representation. The existing rational affine unipotence theorem gives `(ρ(T_b)−I)^d=0`.

For a linear reading `L` of endomorphisms, set

`P_L(X)=Σ_(j<d) L((ρ(T_1)−I)^j) X(X−1)…(X−j+1)/j!`.

The binomial formula and nilpotence give `P_L(n)=L(ρ(T_n))` for every natural `n`. For each positive integer denominator `m`, use the same construction with `ρ(T_(1/m))` and substitute `mX`. At every natural input its value is again `L(ρ(T_n))`; polynomial uniqueness identifies it with `P_L`. Evaluating at `n/m` proves the identity at every nonnegative rational.

For arbitrary `q∈ℚ`, apply this result to `L_q(A)=L(Aρ(T_q))`. Choose a natural `N` with `N+q≥0`. For every natural `n`, `P_(L_q)(n+N)=P_L(n+N+q)`. Thus `P_(L_q)(X)=P_L(X+q)` by infinitely many distinct evaluations. Evaluation at zero gives `L(ρ(T_q))=P_L(q)`.

For slope `u`, take `L(A)=ℓ(Aρ(D_u)v_1)`. Each summand has degree at most `j<d`, giving the claimed fibre polynomial. Nonzero `k` makes its column space nonzero, hence `d>0`.

## Lean

`HeckeKreinToeplitz/Index/ColumnRepresentation.lean` proves the group action and coefficient recovery. `BiarithmeticGeometry/Affine/PolynomialCoefficients.lean` proves `unipotent_rational_coefficient` and `exists_polynomial_affine_translation_coefficient`. `BiarithmeticGeometry/Affine/FiniteRankKernels.lean` proves `exists_polynomial_translation_fibre`.

All three direct source checks pass. Public theorem axiom audits contain only `propext`, `Classical.choice`, and `Quot.sound`. Both programme umbrellas import the new leaves.

Combined with the [zero-axis rank bound](axis-invisible-finite-index-kernels-have-finite-rank.md), this classifies every finite-index zero-axis kernel as polynomial along each translation fibre. It does not supply a decomposition for arbitrary Haar-successor kernels.
