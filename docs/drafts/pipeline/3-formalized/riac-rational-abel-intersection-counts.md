# Rational Abel energy and arithmetic self-intersection counts

- **ID:** RIAC-rational-Abel-counts
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [RIAC](../1-in-progress/renormalized-intersection-arithmetic-counts.md)
- **Module:** [RationalAbelArithmeticCounts.lean](../../../../formal/GaloisForLFunctions/RenormalizedIntersectionArithmeticCounts/RationalAbelArithmeticCounts.lean)
- **Statement:** Actual integral radial intersection counts realize Abel energy; an explicit residual exact sequence removes the coincident-root factor and specializes to the cyclotomic discriminant.

## Objects and identities

For positive conductors `m,n` and integers `0≤a<b`, let
`P_{n,a}=scaleRoots(Φ_n,a)` and define

`C_{m,n}(a,b)=# ℤ[X]/(P_{m,a},P_{n,b})`.

The equations are monic, their root circles are disjoint, and the ring is
finite. Its independent count satisfies

`log C_{m,n}(a,b)=φ(m)φ(n)log b−T_{a/b}(m,n)`.

Common integral dilation by `k>0` multiplies the count by
`k^(φ(m)φ(n))`. The generic thickening theorem gives bilinear prime-local
multiplicities and logarithmic heights for these actual divisors.

For a monic integral polynomial `P` of degree `d`, define the integral
radial divided difference by

`coeff_i D_{a,b}=coeff_i(P) Σ_{j<d−i} b^j a^(d−i−1−j)`.

Then `P_b−P_a=(b−a)D_{a,b}`, including coincident radii by polynomial
specialization. The residual object is the actual ring
`ℤ[X]/(P_a,D_{a,b})`; write its cardinality for `P=Φ_n` as `R_n(a,b)`.
It is finite at distinct radii, and

`C_{n,n}(a,b)=(b−a)^d R_n(a,b)`, `d=φ(n)`.

At each prime, the exact integer multiplicity law is
`v_p(C_{n,n})=d·v_p(b−a)+v_p(R_n)`.

For `O=ℤ[X]/(P_a)`, multiplication and reduction give an actual exact
sequence

`0→O/(D) --×(b−a)→ O/((b−a)D) → O/(b−a) →0`.

At coincidence, `D_{1,1}=dP−XP′`. The diagonal cyclotomic residue ring is
finite and

`R_n(1,1)=|disc Φ_n|`, `log R_n(1,1)=I(n,n)`.

Common dilation multiplies the residual count by `k^(d(d−1))`.
For `0<a<b`, `r=a/b`, and `L=log R_n(a,b)`, the exact analytic comparison is

`L−(d²−d)log b−torsionPairCount(n,n)·log r/2 = I(n,n)+E_r(n,n)`,

where `0≤E_r≤(1−r)²/(2r)·torsionInverseChordCost(n,n)`.
In particular,

`log R_n(k,k+1)−(d²−d)log(k+1) → log R_n(1,1)`.

## Proof

Monic division and the Sylvester presentation identify the finite residue
cardinality with the absolute resultant. Complex factorization gives
`∏_{ζ,η}(aζ−bη)`; splitting off `b` from each difference gives the Abel
identity. Resultant homogeneity proves common dilation.

The geometric power-difference identity proves the integral factorization
of `P_b−P_a`. Adding a multiple of `P_a` and extracting the scalar from
the resultant proves the residual count factor. The quotient maps are
multiplication by `b−a` and reduction modulo `b−a`. Monic division shows
that a nonzero integer can be cancelled modulo `P_a`, proving injectivity;
writing ideal membership as a two-generator relation proves exactness and
surjectivity. The original and factored radial pairs generate the same ideal.

At `a=b=1`, the coefficient formula gives the Euler derivative. Its
resultant is `P(0) Res(P,P′)`. Cyclotomic constant coefficients are units;
separability over `ℚ` proves properness. The derivative-resultant formula
then gives the absolute discriminant. Splitting off each linear root
factor identifies its logarithm with the noncoincident root-pair sum.

The established HHAC finite-radius identity gives the signed error law.
The Abel self-energy limit, composed with `k/(k+1)→1`, gives convergence
of normalized actual counts to the diagonal count. No limiting height is
assumed or defined from the desired Weil form.

## Lean audit

`radialTorsionCount_log`, `radialTorsionCount_self_factor`,
`radialSelfIntersection_exact_sequence`, `radialSelfCount_diagonal`,
`cyclotomic_log_discriminant`, `radialSelfCount_dilation`,
`radialSelfCount_error_bounds`, `radialSelfCount_diagonal_limit`,
`radialSelfCount_local_factor`.

Direct `lake --old env lean` check and transitive axiom audit: only
`propext`, `Classical.choice`, `Quot.sound`.

## Cancellation boundary

The governing target remains `Σ_p index_p(N)=1−M(N)` at scale
`N^(1/2+ε)`. These theorems construct arithmetic counts and self-interaction
removal, including exact maps and an error with a proved sign. They give
no bound for the signed local-index sum. Positive residual cardinalities
do not imply positivity of signed conductor combinations or of the critical
Weil form. A quantitative comparison controlling those signed combinations
remains missing.

## Literature boundary

The [proper intersection count](riac-thickened-intersection-counts.md)
and HHAC finite-radius error law are the corpus foundations.
[Apostol's scaled cyclotomic resultants](https://doi.org/10.1090/S0025-5718-1975-0366801-7)
and the classical `q`-discriminant, described in
[Tran, §1](https://arxiv.org/html/1601.04382v1) with attribution to Ismail,
provide prior arithmetic context. The contribution is the actual integral
residual quotient and exact sequence, their formal comparison with torsion
energy, and the diagonal limit of normalized counts. No classical
resultant or discriminant identity is claimed as new mathematics.
