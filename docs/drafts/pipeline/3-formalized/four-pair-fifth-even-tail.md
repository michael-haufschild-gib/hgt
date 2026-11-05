# Cubic-reserve payments for four theta pairs

- **Stage:** 3-formalized
- **Wall:** Σ6
- **Scope:** Ordered pairs from `(1,4)`, `(2,3)`, `(2,4)`, `(3,4)`.

Set `E(q)=q^(3/2)exp(−2q)`, `A=M(0,1)>0`, and
`c(q)=3/(32q²)−3/(128q³)`. For each listed pair `(m,n)`, the literal
radial tail

`R_mn(q)ᵢⱼ = 2m²n² ∫_(t>q) t^(3/2)exp(−(m²+n²)t) P_(i+j)(m²n²t²;(m²+n²)t) dt`

satisfies `R_mn(q)+E(q)c(q)A/8 > 0` for every `q≥3`.

Write `b=m²+n²`, `d=b−2`, `N=3d`. The rate-`b` gamma enclosure and
`exp(−dq)≤3^N/(20^d q^N)` reduce the claim to two rational endpoint
matrices. Clear `q^(N+3)`, put `q=3(1+y)`, and divide by `3^(N+3)`.
The coefficient at degree `j` has mass part

`(12 binom(N+1,j)−binom(N,j))A/9216`.

The pair contribution vanishes above degree 21, and the two gamma
endpoints differ only at degree zero. Thus 23 fixed positive matrices
per pair suffice. All 92 have exact Schur certificates. Higher mass
coefficients are positive because `binom(N,j)≤binom(N+1,j)`.
Positive matrix sums and convex interpolation cover the entire radial,
gamma, and exponential-weight intervals. Exact power-moment integrals
identify these models with the literal tails.

Namespace `GaloisForLFunctions.ThetaCuspSections.FifthOtherTail`,
subnamespaces `p14`, `p23`, `p24`, `p34`:
`coefficientMatrix_posDef`, `clearedMatrix_posDef`, `reserveModel_posDef`,
`pair_radial_tail_eq`, `pairRadialTailMatrix_reserve_posDef`.

Files: `FifthEvenOtherTailData.lean`, `FifthEvenOtherTailCoefficients.lean`,
`FifthEvenOtherTailModel.lean`, `FifthEvenOtherTail.lean`.
The capstones use only `propext`, `Classical.choice`, and `Quot.sound`.
