# Route L: Deninger one-sided framed mate curvature (2026-08-03)

Current research unit completed; Route L/RH remains open.

## New construction
For affine top-conormal transport A_n = [[n,n-1],[0,1]], scalar coherent monomial sectors are affine coboundaries and flat. Introduce Deninger half-density mate gain chi_s(n)=||n^(1/2-s)||^(-2), acting only on conormal term:
T_chi(n)=diag(chi_s(n),1) A_n.
Exact composition curvature:
F_chi(m,n)=T_chi(m)T_chi(n)-T_chi(mn)
=[[0, chi_s(m)(m-1)(1-chi_s(n))],[0,0]].
It satisfies nonabelian Bianchi. Reduced curvature f_chi(n)=1-chi_s(n). Source/dual polarization is
f_{chi^-1}(n)-f_chi(n)=chi_s(n)-chi_s(n)^(-1)=K_n(s).
At forced degree 6, ordered (2,3) Gamma boundary is positive calibration times this polarization.

## Files
- Paper proof: docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/deninger-one-sided-framed-mate-curvature-transgression.md
- Lean: formal/GaloisForLFunctions/RHTower/DeningerOneSidedFramedMateCurvatureTransgression.lean
- Stage-3 certificate: docs/drafts/pipeline/3-formalized/deninger-one-sided-framed-mate-curvature-transgression.md
- Umbrella import: formal/GaloisForLFunctions/RHTower.lean
- Frontier updates: docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md and source-reporter-ambidexterity-categorical-half-density-law.md

## Verification
- lake env lean target file: PASS
- targeted lake build module: PASS (no full build)
- axiom audit: headline theorems only propext, Classical.choice, Quot.sound; classification corollary propext, Quot.sound
- forbidden token audit and git diff --check: clean
- no stale Lean process from this work

## Exact remaining hard core
[FRAMED_MATE_CURVATURE_SINGULAR_STOKES_ANNIHILATION]:
extend rank-two curvature coefficient-faithfully to completed Xi Green incidence/common-test before diagonal sewing; construct source-native singular Cartier residue/Stokes functional; prove an independent arithmetic boundary law annihilates source/dual curvature polarization while preserving Green provenance. Bianchi is insufficient because curvature exists off-line; assuming K/Gamma vanishing is circular/RH.

Relevant prior memories: `mem:research/route_l_affine_gauge_and_finite_fibre_frontier_2026_08_02`, `mem:research/route_l_hellinger_relative_residue_frontier_2026_08_02`.