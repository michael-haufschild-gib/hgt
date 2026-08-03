# Route L — Burnol conormal radial Deninger comparison (2026-08-03)

## Completed research unit
Physical multiplicity-exact Burnol co-Poisson Mellin jets now compare directly with the concrete Deninger cofinal Tate top-boundary class.

For Xi divisor rho of exact zeta order m and L=log n, n>=2:
- B_L(w)=zeta(w)(exp(Lw)-1)/w.
- B_L^(m)(rho)=(exp(L rho)-1) zeta^(m)(rho)/rho != 0.
- Nested ratio B_(2L)^(m)/B_L^(m)-1=exp(L rho).
- Centered actual character u_n(rho)=exp(-L/2)*ratio=exp(L(rho-1/2)).
- |u_n(rho)|^2=deningerHalfDensityMateGain n rho.
- Under Xi reflection rho#=1-conj rho,
  E_B(n,rho):=|u_n(rho)|^2-|u_n(rho#)|^2
  = chi_rho(n)-chi_rho(n)^(-1)
  = deningerTensorSquareRadialMateCurvature n rho.
- E_B is exactly the reflected relative cofinal Tate top-coordinate.
- At n=6 actual Gamma/CW defect is positive calibration times E_B.
- Completed cross-prime incidence decodes to E_B*w_pq, w_pq != 0.
- E_B=0 iff Re rho=1/2.

## Anti-theatre conclusion
Mellin differentiation/Bockstein is not missing annihilator. Exact conormal jet is nonzero at every Xi divisor and retains horizontal coordinate losslessly. Generic mixed Stokes gives only vertical-cycle membership. Declaring Bockstein or radial defect zero is RH-bearing assumption.

## Files
- docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/deninger-burnol-conormal-radial-top-boundary-comparison.md
- formal/GaloisForLFunctions/RHTower/DeningerBurnolConormalRadialTopBoundaryComparison.lean
- docs/drafts/pipeline/3-formalized/deninger-burnol-conormal-radial-top-boundary-comparison.md
- formal/GaloisForLFunctions/RHTower.lean wired
- docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md updated

## Verification
- lake env lean target: pass.
- targeted source-module olean build: pass.
- axiom audit: only propext, Classical.choice, Quot.sound.
- no forbidden declarations in new module.
- no stale Route-L Lean/Lake process remains.

## Exact open core
[ORDINARY_INTEGER_GREEN_STOKES_ANNIHILATION]: construct pre-specialization nonseparable prime-provenance-retaining ordinary-integer relation on global completed/cofinal Xi Green primitive; prove its image under physical Burnol/Deninger radial comparison is zero; keep strict through source completion. Must not assume E_B=0, Gamma/Hardy kernel membership, RH-equivalent compactness, reflection oddness, static capacity, RH-equivalent positivity, or RH.