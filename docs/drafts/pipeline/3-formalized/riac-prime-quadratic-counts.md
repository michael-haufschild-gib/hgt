# Prime-quadratic orientation and different counts

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md)

## Actual arithmetic objects

For `n>0`, form `F_n(X)=∏_(p^a∥n)(X²+p)^a` from prime factorization alone.
Let `r=Ω(n)` and `Δ_n` be the product of all pairwise differences in the
prime-factor list. The real and rational fibres solve the same integral
equation `y²=disc(F_n)`. The finite-place object is the actual different
quotient `A_n=ℤ[X]/(F_n,F_n')`.

## Exact comparisons

`disc(F_n)=(-4)^r n Δ_n^4`, nonzero exactly when `n` is squarefree.
Its sign is `μ(n)`. The real fibre therefore has `1+μ(n)` points, with
one point at repeated factors. Its actual disjoint union through `N` has
`R_N=N+M(N)` points. For `N≥1`, the original relative singular indices satisfy
`Σ_p index_p(N)=N+1−R_N`.

The different quotient is finite exactly at squarefree conductors, with
cardinality `C_n=4^r n |Δ_n|^4=|disc(F_n)|`; otherwise it is infinite.
The zero `Nat.card` in the latter case never denotes an empty finite ring.
For proper intersections its prime-local order multiplicities satisfy
`Σ_p v_p(C_n)log p=log|disc(F_n)|`.

Conductor multiplication obeys `F_(mn)=F_mF_n` and
`C_(mn)=C_m C_n |Res(F_m,F_n)|²`. Every nontrivial conductor square has
an infinite different quotient, so these counts do not give a finite Tate
family under conductor powers.

## Global rational branch and positive survivor

The absolute discriminant is `n(2^rΔ_n²)²`. A rational point on a squarefree
fibre with `n>1` would make `n` a square in `ℚ`, hence in `ℤ`, contradicting
squarefreeness. Rational fibres have two points at `n=1`, zero at other
squarefree conductors, and one at repeated factors. Their total is
`N+2−Q(N)` for `N≥1`, where `Q(N)` counts squarefree integers through `N`.
Thus the global rational count retains support but loses Möbius orientation.
The positive survivor is the complete fibre classification, the real
local-index comparison, and the same-equation finite-place product formula.

## Proof mechanism

Each quadratic has discriminant `−4p` and pairwise resultant `(q−p)²`.
The monic product-discriminant law gives the fourth-power cross term.
Its vanishing detects repeated factors. Real quadratic equations then give
zero, one or two actual roots. The singular-index theorem supplies the
final comparison with the original topological source.

The actual different quotient is integrally equivalent to a Sylvester
cokernel. For a singular integral map, a nonzero dual-kernel functional
descends to the cokernel and distinguishes all integer multiples of a
detected vector. This proves infinitude and extends determinant cardinality
to all integral maps. The proper case and ordinary prime factorization give
the product formula.

## Remaining mathematical gap

The real count is an archimedean count, not an integer- or rational-point
count. No coherent family with uniformly controlled geometry or bound for
`|N+1−R_N|` has been proved. The separate
[residue-duality theorem](monic-residue-duality.md) identifies the actual
trace cokernel with the different quotient and proves equality of absolute
trace and polynomial discriminants, including nonreduced factors. Their
signed equality has not been formalized here. No RH-scale signed cancellation or Weil-form
Tate height follows.

## Lean statements

All source paths below are relative to `formal/GaloisForLFunctions/`.

| Module | Audited comparison |
|---|---|
| [RIAC/PrimeQuadraticDiscriminant](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/PrimeQuadraticDiscriminant.lean) | `primeQuadraticPolynomial_discr`, `_discr_ne_zero`, `_discr_sign` |
| [RIAC/PrimeQuadraticOrientationCounts](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/PrimeQuadraticOrientationCounts.lean) | `primeQuadraticOrientation_card`, `primeQuadraticOrientationCount_eq`, `_localIndices` |
| [HTGeometry/SingularIntegralCokernel](../../../../formal/GaloisForLFunctions/HTGeometry/SingularIntegralCokernel.lean) | `LinearMap.infinite_quotient_range_of_det_eq_zero`, `LinearMap.card_quotient_range_eq_natAbs_det_all` |
| [RIAC/PrimeQuadraticDifferentCounts](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/PrimeQuadraticDifferentCounts.lean) | `monicDifferent_count`, `primeQuadraticDifferentCount_eq`, `primeQuadraticDifferent_productFormula`, `primeQuadraticDifferentCount_mul`, `primeQuadraticDifferent_square_infinite` |
| [RIAC/PrimeQuadraticRationalFibres](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/PrimeQuadraticRationalFibres.lean) | `primeQuadratic_no_rational_root`, `primeQuadraticRationalRootSet_eq`, `primeQuadraticRationalCount_eq` |

Five direct module checks pass. All 27 printed axiom audits contain only
`propext`, `Classical.choice`, and `Quot.sound`.
