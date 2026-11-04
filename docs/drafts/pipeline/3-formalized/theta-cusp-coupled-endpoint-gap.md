# A common positive cross-load for both fifth-section endpoints

- **Stage:** 3-formalized
- **Type:** THEOREM
- **Wall:** Σ6
- **Statement:** One explicit positive matrix `V` repairs the complete fifth even source at zero and `x₇=½log(7/π)`. Its weighted flux preserves every mixed integral and is positive at `2x₇` for every positive aperture.

Let `H(x)=nativeShiftedMatrix 5 0 x`, `G(x)=thetaCuspCenterCompensationSource x`,
and let `L` have rows `(0,0,1,420,0)` and `(0,0,0,1,1568)`.
Then `V≻0`, `H(0)+G(0)LᵀVL≻0`, and `H(x₇)+G(x₇)LᵀVL≻0`.

## Exact coefficient

Use common-kernel columns `e₀,e₁,(0,0,−420,1,−1/1568)` and load complement
`e₂,e₃−420e₂`. Write `S(m)` for the complementary Schur form of a Hankel
moment sequence `m` in these coordinates. Put

`γ=2(401/1000)(1000001/1000000)(1791/200)−3`, `r=19/25000000000`,

`m₇(k)=[Pₖ(49,14)+8rPₖ(196,35)+16r²Pₖ(784,56)]/121`,

`Δ=S(M(191/10))/(3M₀(191/10))+S(m₇)/γ`, `V=S(m₇)/γ−5Δ/32`.

Here `Mₖ(X)=EvenFiveOrigin.originMomentPolynomial X k` are the exact origin
moments and `Pₖ(a,t)=(thetaPairRadialEvenPolynomial a k).eval t`.
`V` is the literal rational matrix `EvenFiveEndpoint.paidSevenSchur`.

## Proof

Both leading minors of `V` are strictly positive rational certificates.
At the actual origin, `H(0)/G(0)=M(X)/(3M₀(X))` with
`191/10<X<96/5`. The common-kernel block is positive. The corrected Schur
numerator has positive first minor and determinant `κR`, where `κ>0` is
that kernel determinant. The degree-30 polynomial `R` is positive throughout
the parameter interval: after `z=10X−191`, its constant exceeds the sum of
all negative coefficients, while the other terms are nonnegative.

At scale seven, normalize the three retained kernel pivots and two pivots of
`Δ`. The retained model minus `LᵀVL` is exactly
`diag(1,1,1,5/32,5/32)`. Each complete-source entry error is strictly below
`1/32`: all three polarized error contributions are below `1/96`.
The finite maximum is therefore `ε<1/32`; its quadratic error is at most
`5ε‖v‖²`. This proves `H(x₇)/(γf₇²)−LᵀVL≻0`, where
`f₇=thetaCuspSourceTerm x₇ 1`. The complete compensation bound
`G(x₇)≥−γf₇²` finishes the source repair.

For `w=r sinh(ar)`, the weighted repair is
`wH(r/2)+Flux′ₐ(r)LᵀVL`. The derivative flux integrates to zero, so every
entry has its original mixed integral for `0≤a<1/2`. Aperture slack
`Flux′ₐ(r)−wG(r/2)≥0` gives strict positivity at `r=2x₇` for every `a>0`.

Continuity gives positive neighborhoods of both endpoints. For the tail,
`tr(V)I−V` is a rotation congruence of `V`, hence positive semidefinite.
Where `G<0`, the cross-load repair dominates the existing scalar coupled
repair with coefficient `tr(V)`. Thus the same `V` is positive on a cofinal
ray; only a compact set away from the endpoint neighborhoods remains.

## Lean

Owner: `GaloisForLFunctions/ThetaCuspSections/`.

- `FifthEvenEndpointBounds.lean`: exact coefficient, polynomial and strict complete-source error bounds.
- `FifthEvenCoupledEndpointGap.lean`: `crossCoefficient_posDef`, `origin_cross_load_posDef`,
  `scaleSeven_cross_load_posDef`, `coupled_endpoints_posDef`,
  `weightedCrossRepair_integrable`, `weightedCrossRepair_integral`,
  `weightedCrossRepair_scale_seven_posDef`.
- `FifthEvenCrossLoadContinuation.lean`: `crossRepair_endpoint_neighborhoods`,
  `crossRepair_posDef_eventually`, `crossRepair_compact_gap`.

Canonical checks and transitive axiom audits use only `propext`, `Classical.choice`,
and `Quot.sound`. All three modules are imported by `ThetaCuspSections.lean`.

**Open:** positivity on the remaining compact source set; the integrated ninth
section and Σ6 remain open. Endpoint compatibility alone does not prove them.
