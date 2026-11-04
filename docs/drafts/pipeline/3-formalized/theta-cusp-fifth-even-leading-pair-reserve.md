# Fifth even leading-pair reserve

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Σ6
- **Lean:** `ThetaCuspSections/FifthEvenLeadingPairReserve.lean`

Let `Pₖ(p,s)` be the signed radial reflection polynomial and
`Mᵢⱼ(q,z)=[P_(i+j)(q²,2q)+8z P_(i+j)(4q²,5q)]/q^(i+j)`, `i,j<5`.
Let `B` be the explicit lower-triangular Gaussian basis in `gaussianBasis`.
For every `q≥5`,

`B M(q,exp(-3q)) Bᵀ − M₀₀(q,exp(-3q)) I/1000 ⪰ 0`,

hence `B M(q,exp(-3q)) Bᵀ ⪰ (49/1000) I`.

**Proof.** The stationary exponential inequality gives
`exp(-3q)≤z₊(q)=9765625/(1024q^15)`. Clear denominators at the two affine
endpoints `z=0,z₊`: multiply by `q^7` and `128q^22`, respectively.
Their expansions in `q−5` have ten and twenty-five moment matrices. After
Gaussian congruence and subtraction of one thousandth of each zeroth
moment, every coefficient matrix has positive leading Schur pivots.
Two exact square completions prove positive definiteness of each matrix;
nonnegative polynomial sums and affine interpolation give the reserve.
Finally `M₀₀≥(2q−3)²≥49`.

Public certificates:
- `FifthLeadingPair.source_reserve_posSemidef`
- `FifthLeadingPair.source_floor_posSemidef`

This signs the first atom and its two ordered cross pairs with atom two.
The complete source still requires the unequal pairs involving atom three
and the remaining Cauchy tail; pure-atom matrices are already positive.
