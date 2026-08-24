# Hawking Parikh–Wilczek Borel partner endpoint (2026-08-24)

Files:
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingParikhWilczekBorelPartnerEndpoint.lean
- docs/reports/endpoints.md, section "2026-08-24 Parikh--Wilczek Borel-partner endpoint"

Source-faithful finite-mass results:
- physical endpoint x_max = 1/(2 epsilon)
- nth winding endpoint action A_n=(n+1)/4, strictly increasing
- first Borel winding coefficient b_k(s)=Gamma(s+2k)/(k!)^2
- edge/growth numerator E_k(s)=(s+2k)(s+2k+1)
- partner growth difference is 4(2k+1)(s-1/2)/(k+1)^2
- full-winding first Borel wall is xi=1/4; higher windings are analytic there
- Euler mirror gauge has squeeze r_s=(1/2-Re s) log(1-z); canonical SU(1,1) completion mixes every tilted sector

New phase-sensitive survivor:
- recoil holonomy H_k(s)=E_k(s)E_k(1-s)
- Im H_k(s) = -2 Im(s)(2 Re(s)-1) * ((2k+Re(s)+1/2)(2k+3/2-Re(s))+Im(s)^2+1/4)
- bracket is positive in 0<Re(s)<1
- for nonreal strip s, Im H_k(s)=0 iff Re(s)=1/2
- positive diagonal symmetrization condition E_k(1-s)=q conjugate(E_k(s)), q>0, holds iff Re(s)=1/2
- Lean formalizes formula, zero-phase iff, symmetrizable=>zero phase, q=1 critical-line construction, and final symmetrizable iff.
- Targeted endpoint compile passed.
- Axioms of all five new theorems: [propext, Classical.choice, Quot.sound].

Hostile verdict:
- Generic KMS is rate-level and phase blind.
- SU(1,1), CCR, inverse, Krein, group, and positive diagonal grade metrics do not select zero mixing.
- Treating Borel grade as physical ladder or functional reflection 1-s as actual CTP reverse transition is circular.
- Exact open physical core: derive from finite-mass CTP winding influence functional that the actual gauge-invariant forward/reverse amplitude holonomy is H_k(s), or exhibit its extra phase.
- No RH proof claimed.

Lint on 2026-08-24: endpoint caused no lint error. Global lint failed only for unrelated unreachable HTGeometry modules HardyHorizontalLayerLeakage, HorizontalLayerBlaschke, HorizontalLayerProjective, ProjectiveBoundaryMultiplier.
No git used. Scratch files removed.