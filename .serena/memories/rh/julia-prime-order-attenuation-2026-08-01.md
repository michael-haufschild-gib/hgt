# RH whole-corpus frontier — Julia prime-order attenuation (2026-08-01)

Status: JPOA-1 paper-proved and Lean-proved; NOT RH.

New modules:
- formal/GaloisForLFunctions/HTGeometry/JuliaDefectAttenuation.lean
- formal/GaloisForLFunctions/RHTower/GammaSewnMobiusJuliaPrimeOrderAttenuation.lean

Card:
- docs/drafts/pipeline/3-formalized/needs-audit/ccm-julia-prime-order-attenuation-law.md

Main theorem:
R(y)=4/(3y^2)*(1-cosh(y/2)^2/sqrt(cosh(2y))) is strictly decreasing for y>0.
Literal arithmetic Julia hard mass satisfies hard_x(u,p^e)^2 = R(x log p)*boundary(u,p^e)^2.
At first CCM clock, every admitted multi-mode prime p is smaller than every one-mode outer q, hence R(x log q)<R(x log p) for x>0. Exact relative budget gain: R_q(G-B)<R_p G-R_q B for G>0.

Sharp no-go:
Same positive factor applies to all exponents in a p-tower, so tower sign is unchanged. Negative one-mode towers and p=2,3 two-mode exceptions are not locally repaired. Attenuation tends coefficientwise to 1 as x→0+. Remaining open core: aggregate theorem coupling favorable cross-prime attenuation to continuous/Gamma budget and dominating full bad residual under a boundary-layer schedule.

Verification:
- direct Lean checks green
- lake build HT profile 2787/2787
- lake build RHT connector 9525/9525
- 8 capstones axioms exactly [propext, Classical.choice, Quot.sound]
- lint new modules clean; global lint fails only 5 unrelated pre-existing umbrella reachability gaps
- full RHTower umbrella audit was intentionally stopped after 13746/13780 when it expanded into unrelated uncached modules; no Lean/lake process from this work remains.

Working log:
- docs/drafts/pipeline/1-in-progress/rh-whole-formal-corpus-frontier-audit.md
