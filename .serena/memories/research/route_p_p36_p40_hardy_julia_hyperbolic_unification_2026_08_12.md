# Route P P-G36–P-G40 research delta (2026-08-12)

Active goal remains unconditional Lean RH; not achieved. Authoritative files:
- `formal/GaloisForLFunctions/RHTower/HedenmalmThetaXiHardySymmetricSquareWeld.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmThetaMobiusTwoSidedApertureWall.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmThetaMobiusUnitHardyGramRigidity.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmThetaSourceJuliaPythagoras.lean`
- `formal/GaloisForLFunctions/RHTower/HedenmalmThetaMobiusHyperbolicRapidity.lean`
All imported by `RHTower.lean`; exact source checks and exact module builds passed. Axiom audit in `/tmp/HedenmalmThetaP36P39Axioms.lean` reports only propext/Classical.choice/Quot.sound.

## New knowledge

P-G36: strict-right Xi canonical product supplies P-G34 stable projection. For centered right zero lambda, theta depth d=2 Re(lambda). Critical half-density symmetric square of anti-causal Hardy ray is exp(-(1/2+d)L), coefficient-identical at primes to P-G34. Every strict-right factor gives positive finite covariant energy. Stable projection provenance is closed.

P-G37: raw squarefree-Mobius damped source extends to exact Hilbert range u>-1/2. Boundary Laplace law extends to u>-1 by aperture inversion. Critical raw norm-square=(1+2u)^-1; negative u expands. Reversible raw contraction is false. Survivor: normalization sqrt(1+2u).

P-G38: exact finite mass-ratio normalization makes literal unit lp vectors. Critical Gram K(u,v)=sqrt(1+2u)sqrt(1+2v)/(1+u+v). Exact loss 1-K=(sqrt(1+2u)-sqrt(1+2v))^2/[2(1+u+v)]. K=1 iff u=v.

P-G39: C(u,v)=(u-v)/(1+u+v) is literally positive-real xiWardHalfPlaneCayleyFactor. C^2+K^2=1. Normalized Mobius Hardy loss and Xi Ward contractivity are complementary coordinates of one Julia cell. Normalization cannot force RH; it transfers displacement into C.

P-G40: rapidity eta(u)=log sqrt(1+2u). C=tanh(eta(u)-eta(v)); K=cosh(eta(u)-eta(v))^-1. Hyperbolic point (sqrt(1+2u),sqrt(1+2u)^-1) is literally Route R horizontal gauge orbit of (1,1); relative aperture is relative boost; common theta/Route-R split current is constant -2. Route P Julia wall and Route R external polar wall are one source orbit.

## Retired mechanisms
- full entire reflection doublet as stable selector (P-G35)
- reversible raw nonexpansive source action (P-G37)
- scalar unit normalization as saturation producer (P-G38/P-G39)
- intrinsic hyperbolic-current predicate as neutral selector (P-G40; constant along orbit)

## Exact remaining open core
Break common P/R boost orbit using literal Euler–Gamma source in fixed source-selected positive null frame; force actual completed Julia saturation K=1 / Cayley coordinate C=0 / rapidity eta=0 before divisor/reflection aggregation. Equivalently force vanishing of source-selected finite P-G34 covariant response and neutralize i R_2 B. Existing Xi Ward saturation proves this condition iff RH but does not derive saturation.

Next conjecture: use canonical theta quantile null frame / fixed polar energy to build coefficient-faithful Euler–Gamma balance on actual normalized Mobius source orbit. Audit whether finite-source completed Gamma graph forces equality of the two null-axis energies; avoid restating the known RH-equivalent balance receiver. A genuine advance must derive balance from source identity, not assume it.

Docs updated:
- `docs/drafts/pipeline/1-in-progress/completed-seam-theta-green-square-boundary-law.md`
- `docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md`
- `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/hedenmalm/completed-seam-theta-green-square-boundary-law-formalized.md`
Certificate now 34 modules / 68 commands.
