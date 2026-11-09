# Gram coupling of the Green and torsion channels

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Obstacle:** B135, finite coupled locking on overlapping smooth packets.

## Exact construction

For `f=Σ_{1≤n≤N}x_n g(·−log n)`, let `G_{mn}=∫g(u−log m)g(u−log n)du` be its actual L² Gram matrix. Put `C=G^(1/2)`, the positive square root, and `y=Cx`. Define the coupled torsion channel as the actual `torsionForm(ρ,Icc 1 N,y)`. It is positive whenever the raw torsion channel is positive, and its divergent coefficient is `Σy_n²=xᵀGx=∫f²`.

Conjecture: with `ρ_c(r)=1−exp(−selfEnergy(r)−c)`, pole minus the actual smooth Green energy plus this coupled torsion channel converges for every compact C² profile and every packet, with no separation condition. The limit is

`weilQuad(f)+primeSum(f)−atomicWeilForm(N,y)+(c−2a₀)∫f²−Σy_n² selfIntersection(n)`,

where `a₀=gammaHardyPhaseRate 0`. Below the atom spacing, `G=M I`, so `y=√M x` and this construction reduces exactly to the raw packet lift already proved.

## Required closure

Prove the Gram positivity and square-root mass identity for actual smooth translates; construct the coupled positive torsion family and prove its finite limit; calculate the full defect against Weil's form; recover the separated regime. No abstract Gram-matching premise may replace the actual construction.

The construction is indexed by a finite packet presentation. Independence under changes of presentation or refinement is a separate question and must not be silently assumed. The result concerns existence and the explicit defect, not positivity of the limiting Weil form.
