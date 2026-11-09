# Prime-quadratic arithmetic orientation cover

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Parent:** [RIAC](renormalized-intersection-arithmetic-counts.md)
- **Established comparisons:** [Prime-quadratic counts](../3-formalized/riac-prime-quadratic-counts.md)

## Constructed source

For `n>0`, define `F_n(X)=∏_(p^a∥n)(X²+p)^a` using prime factorization.
The actual real fibres `y²=disc(F_n)` have aggregate count `R_N=N+M(N)`.
For `N≥1`, the original relative singular indices satisfy
`Σ_p index_p(N)=N+1−R_N`.
The same integral equation gives actual different quotients
`ℤ[X]/(F_n,F_n')`, their finite/infinite classification, and prime-local
product-formula heights. These comparisons are formalized.
The [residue-duality comparison](../3-formalized/monic-residue-duality.md)
identifies the actual integral trace cokernel with this different quotient,
including repeated factors. It proves equality of absolute trace and polynomial
discriminants and the same product-formula height.

## Remaining theorems

1. Identify the signs of the polynomial and monomial-basis trace discriminants
   of `ℤ[X]/(F_n)`. Their absolute values and actual cokernel counts are
   identified; the signed equality remains open.
2. Construct compatible geometry across the integer conductor cutoff with
   an independent estimate `|N+1−R_N|≪ε N^(1/2+ε)` for every `ε>0`.
   The real fibre identity alone supplies no such estimate or transfer of
   the finite-field curve bound.

## Closed variants and positive survivors

For `N≥1`, global rational fibres have total `N+2−Q(N)`, where `Q` counts
squarefree integers. Their complete classification is formalized: two points at one,
zero at other squarefree conductors, and one at repeated factors. They
retain support and lose Möbius orientation.

Conductor multiplication satisfies `F_(mn)=F_mF_n`, with the exact actual
count law `C(mn)=C(m)C(n)|Res(F_m,F_n)|²`. Every nontrivial conductor square
has an infinite different quotient. Thus this family cannot itself supply
finite Tate counts under conductor powers. The cross-intersection law,
proper product formula, and real signed comparison are the formalized
positive survivors.
