# Uniform Gamma-small tails for the literal mixed square source

- **ID:** acs-square-mixed-source-uniform-tail
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For every ε>0 there exists A≥1 such that all q,d,X satisfy
  `|B₂(q,1_[A,∞)d,X)|≤εΓ(completePairProfile q d X)`.
  Here `B₂(q,d,X)=S₂(g+h)−S₂(g)−S₂(h)` for the original pair averages g
  and Haar details h; S₂ includes every even prime power.

## Proof

On the interior of pair a, the average profile is the constant q_a.
The a-th Haar profile is supported on that pair and has zero integral.
Endpoints have zero measure. Thus `∫g h_a=q_a∫h_a=0`; finite summation
gives `∫gh=0`. Also `∫h=0`. Hence
`∫(g+h)=∫g` and `∫(g+h)²=∫g²+∫h²`.
The mixed centred source Q therefore equals the literal mixed source B₂.

Write K for the proved positive Haar Gamma upper constant and
`E=Γ(completePairProfile q d X)`, using the original untruncated d.
The existing projection estimate gives `Γg≤(2+12K)E`.
For `d_tail=1_[A,∞)d`, its logarithmically weighted square mass is at most
that of d, which is at most E. Therefore `Γh_tail≤4KE` and
`Γg+Γh_tail≤PE`, where `P=2+16K>0` is independent of q,d,X,A.

Apply the centred physical-source theorem with η=ε/(2P). It gives C≥0
such that
`|B₂(q,d_tail,X)|≤η(Γg+Γh_tail)+C∫h_tail²`.

Choose an integer `A>exp(2C/ε)`. Then A≥1 and the reciprocal-width
weight satisfies `cellGammaWeight A≥log A>2C/ε`.
The exact tail estimate in the original source is
`cellGammaWeight A * ∫h_tail²≤E`. Multiplying by ε/2 shows
`C∫h_tail²≤εE/2`. The Gamma term is also at most εE/2, proving the claim.

No support-dependent cutoff, projected source energy, or uncontrolled
coarse square mass occurs.

## Route consequence

This discharges the square-prime mixed-tail input for the joint full-detail
payment. First-prime mixing, coarse signed terms, polar cross terms, and
finite heads remain unpaid. This theorem alone does not prove RH.

## Lean verification

`ArithmeticIndexDescent/TheMixedSquareSourceHasUniformSmallTails.lean`.

Declarations:

- `integral_average_mul_haarSection`
- `integral_completePairProfile_sq`
- `squarePrimeMixedSource_eq_centered`
- `exists_squarePrimeMixed_gamma_mass_bound`
- `exists_uniform_small_squarePrimeMixed_tail`

Direct check passed, without diagnostics:

```
lake --old env lean GaloisForLFunctions/ArithmeticIndexDescent/TheMixedSquareSourceHasUniformSmallTails.lean
```

No web search, novelty checks, numerical experiments or axiom checks.
