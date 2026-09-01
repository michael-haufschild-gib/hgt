# Second-level concavity does not force TCD rank-three D1

- **ID:** TCD-SECOND-LEVEL-D1-NOGO
- **Stage:** 3-formalized
- **Type:** NO-GO + positive survivor
- **RH chain tested:** Planat--Solé second-level concavity → reflected rank-three D1 → finite TCD → theta--Xi incidence → Weil positivity → RH.

## Result

For `F(r)=exp(-r⁴)`, `s(t)=F(√t)=exp(-t²)` has positive first Laguerre expression and globally strict second-level logarithmic concavity. Yet `P(t)=F(t)F(-t)=exp(-2t⁴)` has even jets
`(P⁽⁰⁾,P⁽²⁾,P⁽⁴⁾,P⁽⁶⁾,P⁽⁸⁾)(0)=(1,0,-48,0,80640)` and signed rank-three determinant `-3760128`.

Hence second-level concavity alone cannot supply TCD D1. Theta-specific structure remains necessary; refined-cone D1 is unaffected.

Positive survivor: if `f=s₁²-s₀s₂`, then
`f f''-(f')² = s₀ det[s_{i+j}]_{0≤i,j≤2}` exactly. Thus the [August 2026 theorem](https://arxiv.org/abs/2608.19160) controls the ordinary consecutive-derivative Hankel determinant, not the centered reflected even-jet determinant.

## Formal proof

- Module: `GaloisForLFunctions.HilbertMetric.SecondLevelConcavityRankThreeD1NoGo`
- Capstone: `HilbertMetric.exists_secondLevelStrict_kernel_with_reflectedRankThreeD1Failure`
- Survivor: `HilbertMetric.secondLevelCurvature_eq_mul_derivativeHankelThreeDet`
- Targeted build: passed.
- Axioms: `propext`, `Classical.choice`, `Quot.sound` only.
- Novelty audit: internal corpus search and primary-source search found no exact reflected-D1 counterexample through 2026-08.
