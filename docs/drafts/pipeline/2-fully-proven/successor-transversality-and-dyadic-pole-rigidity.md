# Successor transversality and dyadic pole rigidity

- **ID:** critical-rigidity-successor-dyadic
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `critical-scale-arithmetic-rigidity`, joint arithmetic rigidity
- **Statement:** Complete-period successor approximation and the dyadic pole defect jointly control every nonconstant Ramanujan packet, with optimal constant three quarters.

## Objects

Let `c_m` be the actual Ramanujan sum, `M=Q!`, and

`F_a(n)=Σ_{1≤m≤Q} a_m c_m(n)`.

Write `r_m(h)=c_m(h)/φ(m)`. The projection coefficients of the shifted packet are `a_m r_m(h)`.

## Dependency-closed paper proof

Complete-period shifted orthogonality gives, for arbitrary real coefficient families `a,b`,

`mean (F_a(n+h)−F_b(n))²`
`=Σ_m φ(m)(b_m−r_m(h)a_m)² + Σ_m φ(m)(1−r_m(h)²)a_m²`.

This is an exact identity, obtained by expanding both squares and using
`mean c_m(n+h)c_l(n)=1_(m=l)c_m(h)`. No positivity input is assumed.

At `h=1`, `c_m(1)=μ(m)`. For `m≥3`, `φ(m)≥2` and `|μ(m)|≤1`, so
`φ(m)(1−r_m(1)²)≥3φ(m)/4`. At conductors one and two the leakage is zero.

The affine conductor selection formula gives

`mean (F_a(2n)−F_a(n)) = 1_(2≤Q) a_2`.

Indeed a dilation by two reaches conductor one only from conductors one and two; the conductor-one terms cancel and `φ(2)=1`.

Dropping the nonnegative projection error and adding the squared dyadic mean yields

`(3/4) Σ_{2≤m≤Q} φ(m)a_m²`
`≤ mean (F_a(n+1)−F_b(n))² + [mean (F_a(2n)−F_a(n))]²`.

Equality is attained by the conductor-three packet with its exact shifted projection: `φ(3)=2`, `μ(3)=−1`, and the dyadic mean vanishes. Hence the constant is optimal.

The common zero fibre consists exactly of constant packets with matching approximants. The inequality also gives uniform quantitative control of the nonconstant coefficient mass from the two observed defects.

## Scope and novelty

The proof uses existing affine Ramanujan orthogonality and classical Möbius/totient facts. The proposed contribution is their joint, quantitative successor-transversality and pole-preserving dilation inequality, including all mixed packet coefficients and the sharp constant. Corpus searches found the constituent diagonalization, prime-dilation square energy, and gauge successor rigidity, but no such joint estimate.

This is a complete-period statement. It does not supply a growing-horizon bound when the horizon is shorter than the common period, and it does not identify these positive defects with the complete Weil form. Those transfers remain separate questions.

## Lean

Formalization in `CriticalScaleArithmeticRigidity/SuccessorProjection.lean` and `DyadicPoleRigidity.lean`; mathematical inputs must remain the literal source identities above.
