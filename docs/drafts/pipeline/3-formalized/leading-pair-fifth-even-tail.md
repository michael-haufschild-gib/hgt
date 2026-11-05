# The first atom pays the leading unequal-pair fifth tail

- **Stage:** 3-formalized
- **Wall:** Σ6
- **Scope:** Ordered pairs `(1,1)`, `(1,2)`, `(2,1)`; complete theta tail remains open.

For `0≤i,j<5`, integrate the signed order-`2(i+j)` reflection jets of
these three ordered pairs over `s>r`, with reflection centre `s/2`.
Their sum is positive definite whenever `q=πexp(r)≥3`, hence for every
`r≥0`.

## Proof

Write `E(q)=q^(3/2)exp(−2q)`. The first-atom tail is
`E(q)M(q,z₂)`, where `z₂≥1/2+3/(8q)` and increasing `z₂` adds a
positive definite constant matrix.

The unequal pair has density `q^(3/2)exp(−5q)` and normalized moments
`J₀=z₅`, `J_(n+1)=q^(n+1)/5+(2n+5)Jₙ/10`. Linear scale change gives
`z₅(q)=(2/5)z₂(5q/2)`.

Twice integrating by parts isolates the reciprocal-square-root remainder.
Its pointwise bounds

`q^(−1/2)−(t−q)/(2q^(3/2)) ≤ t^(−1/2) ≤ q^(−1/2)`, for `t≥q>0`,

give

`zL(q)=1/5+3/(50q)+3/(500q²)−3/(5000q³) ≤ z₅(q)`

`≤ zU(q)=1/5+3/(50q)+3/(500q²)`.

The lower pointwise bound reduces to `(u−v)²(u+2v)≥0`, with
`u=√t`, `v=√q`. The two ordered pairs have relative weight
`8exp(−3q)`. The stationary exponential bound and `exp(3)≥20` imply
`exp(−3q)≤19683/(8000q⁹)`.

Retain first-atom mass `1/2+3/(8q)`. At the upper exponential weight,
clear `q¹²` from each gamma endpoint matrix. Its entries are

`q¹¹ L₁(F_n)+19683 L₁₂(C_n)/1000`,

where `F_n=qJ_n^(2)` and `C_n=q³J_n^(5)` obey polynomial recurrences.
For both gamma endpoints, the five cleared Schur signs have positive
constant terms and nonnegative remaining coefficients in `q−3`.
The exact coefficient certificates are checked in Lean.

Convexity covers the gamma interval and then the exponential-weight
interval. The unused first-atom gamma mass adds a positive semidefinite
matrix. Multiplication by `E(q)>0` and the exponential coordinate change
preserve strict positivity.

The comparison leaves the explicit matrix reserve
`E(q)(3/(32q²)−3/(128q³))A`, where `A=M(0,1)>0`.
This follows from the cubic lower bound for the first-atom gamma mass.

## Formalization

Namespace `GaloisForLFunctions.ThetaCuspSections.FifthMixedTail`:
`leadingModel_posDef`, `leadingTailMatrix_posDef_of_scale`,
`leadingTailMatrix_posDef`, `leadingRadialTailMatrix_gamma_reserve`.

`FifthEvenLeadingTailModel.lean` proves the interval comparison;
`FifthEvenTailGammaBounds.lean` proves the gamma enclosure in namespace
`FifthAtomTail`; `FifthEvenLeadingTail.lean` identifies the literal integrals.
All 22 audited capstones use only `propext`, `Classical.choice`, `Quot.sound`.
Direct `lake --old env lean` checks pass for all four changed modules.
All three new modules are wired into `ThetaCuspSections.lean`.

The other five unequal pairs among four retained atoms and the infinite
remainder remain unpaid in the complete integrated matrix.
