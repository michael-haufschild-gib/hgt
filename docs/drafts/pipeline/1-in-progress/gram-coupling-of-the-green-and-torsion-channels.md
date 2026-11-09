# Gram coupling of the Green and torsion channels

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B135, finite coupled locking on overlapping smooth packets.

## Exact construction

For a compact continuous profile g, set v₀=0 and vₙ=g(·−log n) in real L² for n≥1. Let eₙ be their ordered normalized Gram–Schmidt vectors; retain zero vectors when a step is dependent. For f=Σ₁≤n≤N xₙvₙ, put yₙ=⟨eₙ,f⟩. Prefix reconstruction gives yₙ=0 for n>N and Σ₁≤n≤N yₙ²=∫f². The coordinates depend on g and f, independently of unused degrees in a presentation.

Couple the actual torsion form Qρ(y) to pole(f)−smoothGreenEnergy(r,f), with ρ=1−exp(−selfEnergy(r)−c). Its torsion part stays positive. Its two divergent masses agree, including overlaps. Conjectured limit:

`weilQuad(f)+primeSum(f)−atomicWeilForm(N,y)+(c−2a₀)∫f²−Σyₙ² selfIntersection(n)`,

where a₀=gammaHardyPhaseRate 0. Below the atom spacing, y=√M x with M=∫g², recovering the separated scalar lift.

## Required closure

Construct the coordinates from actual smooth translates; prove prefix reconstruction, mass equality, vanishing tail and presentation compatibility; prove positivity of the coupled torsion channel, finite locking and the full defect against Weil; recover the separated regime. No assumed mass-matching interface replaces the construction.

A finite positive Gram square root supplies mass matching but need not respect adjoining unused degrees. Ordered triangular factorization addresses this compatibility. The theorem concerns finite limits and their defect, not positivity of Weil's form.
