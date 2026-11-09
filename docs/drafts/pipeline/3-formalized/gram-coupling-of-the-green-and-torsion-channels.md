# Gram coupling of the Green and torsion channels

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean).
- **Obstacle:** B135, finite coupled locking on overlapping smooth packets — constructed, with exact defect.

## Construction

For a compact continuous profile g, set v₀=0 and vₙ=g(·−log n) in real L² for n≥1. Let eₙ be their ordered normalized Gram–Schmidt vectors, retaining zero vectors at dependent steps. For f=Σ₁≤n≤N xₙvₙ, put yₙ=⟨eₙ,f⟩. Define

`Lᵍ_c(r,f)=pole(f)−smoothGreenEnergy(r,f)+torsionForm(ρ_c(r),Icc 1 N,y)`,

with `ρ_c(r)=1−exp(−selfEnergy(r)−c)`. The coordinate map is linear. The torsion summand is the actual positive Abel torsion form on these transformed coefficients.

## Proof

Normalized Gram–Schmidt preserves every prefix span; its nonzero vectors have norm one and are pairwise orthogonal. Hence f=Σ₀≤n≤N⟨eₙ,f⟩eₙ. Taking its inner product with f gives Σyₙ²=∫f², since e₀=0. Later eⱼ are orthogonal to the entire earlier prefix, so yⱼ=0 for j>N. Equal actual packets have equal L² vectors and therefore identical coordinates. The vanishing tail makes their finite torsion sums equal even when their cutoffs differ.

Write H=∫f² and Z=selfEnergy. The existing actual-channel asymptotics give

`Green_r(f)−HZ(r) → −levyEnergy(f)`,

`torsionForm(ρ_c(r),y)−(Z(r)+c)H → −atomicWeilForm(N,y)−Σyₙ² selfIntersection(n)`.

Their divergent terms cancel for every compact C² packet, with arbitrary overlap. Combining the finite terms with the exact Weil identity yields

`Lᵍ_c(r,f) → weilQuad(f)+primeSum(f)−atomicWeilForm(N,y)+(c−2a₀)H−Σyₙ² selfIntersection(n)`,

where a₀=gammaHardyPhaseRate 0. The torsion summand is nonnegative whenever 0≤ρ<1, and the common radius eventually lies in (0,1).

Below the atom spacing the translated atoms are orthogonal and each has squared norm M=∫g². Ordered orthogonalization therefore gives yₙ=√M xₙ on the prefix, including M=0. Quadratic homogeneity gives exact equality with the original scalar-locked family, before taking limits.

## Scope

This constructs a single linear coupling for each fixed profile, compatible with every finite cutoff, and calculates its full finite defect. A finite positive Gram square root alone need not have that compatibility. The construction uses the natural order of degrees; it asserts neither independence of the profile nor Hecke covariance. Positivity of the torsion summand supplies no sign for the difference with the Green channel or for Weil's form.

## Lean

`HyperbolicArakelovTheory/TheGramCouplingOfTheGreenAndTorsionChannels.lean`:
`sum_sq_gramTorsionCoordinates`, `gramLockedPacket_eq_of_packet_eq`,
`gramCoupledTorsion_nonneg`, `tendsto_gramLockedPacket`,
`gramLockedPacket_of_separated`.

Final source audit: `lake --old env lean GaloisForLFunctions/HyperbolicArakelovTheory/TheGramCouplingOfTheGreenAndTorsionChannels.lean` passes without warnings. All six audited capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`. Imported by the HyperbolicArakelovTheory umbrella, which is imported by MainTheorems.
