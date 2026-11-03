# Gamma remainder and joint first-fold floor

- **ID:** F1-GR
- **Stage:** 2-fully-proven; Lean audit pending
- **Type:** THEOREM (paper)
- **Source:** [Joint first-fold payment](../1-in-progress/f1-joint-cubic-prime-payment.md)
- **Statement:** For every real odd C² unit-window test, the complete form satisfies
  `Q(F)≥P(F)+E/64`.
  Here `E=∫F²` and `P` is the source card's exact retained Gamma/prime/pole form.

## Proof

The exact omitted terms are `∫₀¹r(t)(E−C(t))dt+2δE`, with nonnegative first term and
`δ=Ω(1)−log2−π/4+1/4−1/96`. The positive Laplace expansion gives

`Ω(1)≥2[z+z⁵/5+z⁹/9]`, `z=e^(−1/2)>20/33`.

Indeed `ω(t)=Σₖ≥₀e^{−(2k+1/2)t}` has positive terms. Integrating its first three terms
on `(1,∞)` gives the displayed bound. From `e<2.7182818286<(33/20)²` follows
`z>20/33`. The rational inequality

`693147181/10⁹+(31416/10⁴)/4−1/4+1/96+1/128
 <2[20/33+(20/33)⁵/5+(20/33)⁹/9]`

and the proved upper bounds on `log2` and `π` give `δ>1/128`.
The nonnegative lag deficit and kernel remainder then give `Q−P≥2δE≥E/64`.
All integrals exist by compact C² regularity; the three retained modes are integrable
exponentials. Prime and pole terms cancel exactly in this comparison.

**Lean:** `TheGammaComparisonRetainsItsLagMoments` now retains the exact exterior tail.
`TheGammaRemainderPaysAUniformReserve` contains the three-mode and complete-form proofs;
individual source and transitive-axiom audits remain pending.

## Remaining sign

The separate conjecture `P(F)≥−E/64` retains both primitive moment squares, primitive
mass, signed prime reflection and pole. The proved quintic counterexample to `P≥0`
does not establish or refute this weaker floor. A proof must control the two low odd
moments and their cross terms with the coercive complement; prime-only Harnack
payment does not settle this joint inequality.
