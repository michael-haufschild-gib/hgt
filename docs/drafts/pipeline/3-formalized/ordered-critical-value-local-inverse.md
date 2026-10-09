# Local inverse of the actual critical-value map

- **ID:** ORDERED-CRITICAL-VALUE-LOCAL-INVERSE-20261009
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); realization bridge
- **Parent:** `../1-in-progress/finite-planar-polynomial-realization.md`
- **Statement:** The constructed additive-constant critical-value map is a local homeomorphism at every parameter with distinct critical positions.

## Local inverse at distinct critical positions [PROVED HERE on paper]

For the additive-constant map B, if all ordered positions aⱼ(c) are distinct, its complex differential is invertible. Consequently B is a local homeomorphism there by the inspected finite-dimensional inverse function theorem. Distinct critical values imply distinct positions, so this suffices on the preimage of the distinct-value configuration space. This statement is stronger than requiring distinct critical values at the local-inverse stage.

Proof. The coefficient formula already used for continuity shows that B and every coefficient of P=dA(Q_c)+b are complex polynomial functions of the parameters. Hence they are complex smooth. Fix a tangent vector (u,v), and let δaⱼ be the corresponding linear variations of the critical positions. Let δP be the polynomial obtained by differentiating each coefficient of P in this parameter direction. Monicity and centering make the top two coefficient variations vanish, so deg δP≤d−2 (including δP=0). Its constant term is v. Differentiating the finite coefficient identity P′=dQ commutes with the polynomial derivative and gives

δP′=−d∑ⱼ δaⱼ∏_{k≠j}(X−a_k).

At the j-th critical value, the parameter chain rule gives (DB·(u,v))ⱼ=δP(aⱼ)+P′(aⱼ)δaⱼ=δP(aⱼ). Suppose DB·(u,v)=0. The polynomial δP of degree at most d−2 then has d−1 distinct roots aⱼ, so the inspected root-count bound forces δP=0. Evaluate its derivative identity at aⱼ. All summands except j vanish, yielding 0=−d δaⱼ∏_{k≠j}(aⱼ−a_k). The product and d are nonzero, so δaⱼ=0 for every j. The last n positions are the original independent coordinates, so u=0. The constant coefficient of δP is v, so v=0. Thus DB is injective. Domain and codomain both have complex dimension n+1, so DB is bijective and, in finite dimension, a continuous linear equivalence. The inspected complex smooth inverse function theorem gives the claimed local coordinate.

Lean verifies the coefficientwise parameter-derivative adapter, the chain-rule identity at a critical position, the finite root count, and the finite-dimensional equivalence. No uniformization or polynomial realization is used. Global realization still requires the configuration-space and monodromy steps.

## Lean certificate

`HTGeometry/OrderedCriticalValueDifferential.lean` is wired into the umbrella. Its production leaf build, all 30 explicit public axiom audits, and final `lake env lean` actual-source check pass; the final log is empty and every axiom list contains only `propext`, `Classical.choice`, and `Quot.sound`.

The formal proof constructs the additive polynomial family and its smooth coefficient functions, the coefficientwise tangent polynomial of degree at most n, and joint evaluation. The chain rule at a critical point eliminates motion of that evaluation point. The finite root count kills a kernel tangent polynomial; differentiating the critical product then kills every critical-position variation, and evaluation at zero kills the constant variation. Equal finite dimensions and the installed complex inverse function theorem give the actual local homeomorphism.

Decisive declarations in namespace `GaloisForLFunctions.HTGeometry.OrderedCriticalValueMap` are `exists_openPartialHomeomorph_valuesWithConstant` and `isLocalHomeomorphOn_valuesWithConstant_distinct`. Critical values need not be distinct for the first theorem; distinct critical positions suffice.

This is a verified construction ingredient, not prescribed monodromy realization or Xi uniformization. External novelty remains unverified. The subsequent surjectivity theorem is now fully audited in `ordered-critical-value-surjectivity.md`.
