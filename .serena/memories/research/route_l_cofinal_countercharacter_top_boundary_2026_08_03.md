# Route L cofinal countercharacter top-boundary transgression (2026-08-03)

Paper: docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/deninger/deninger-cofinal-countercharacter-top-boundary-transgression.md
Lean: formal/GaloisForLFunctions/RHTower/DeningerCofinalCountercharacterTopBoundaryTransgression.lean
Certificate: docs/drafts/pipeline/3-formalized/deninger-cofinal-countercharacter-top-boundary-transgression.md

New exact cross-identification:
- finite Tate forward naturality defect for scalar gain g is g * beta_m, where beta_m is nonzero rank-one cofinal top boundary;
- raw Deninger gain is chi_s(n), countertransported gain is 1;
- flat-minus-raw relative defect is (1-chi_s(n))*beta_m = R_s(n)*beta_m;
- critical reflection polarization is K_n(s)*beta_m;
- new-top-coordinate reader sends beta_m(e_m) to 1, hence recovers K_n(s) exactly and class vanishes iff Re(s)=1/2 for n>=2;
- n=6 reader equals actual ordered (2,3) Gamma/Calderon-Witt boundary coefficient up to existing positive calibration;
- finite-support Xi vector lands isometrically in completed cross-prime incidence and decodes to K_6(rho)*w_pq, w_pq nonzero; decoded vanishing iff actual Gamma coefficient vanishing.

Verification:
- lake env lean target: pass;
- targeted lake build module: pass; no full build;
- axioms only propext, Classical.choice, Quot.sound;
- umbrella import present;
- global formal lint sees new module but fails on unrelated concurrent unreachable cyclic/adelic/sieve modules.

Exact remaining core [ORDINARY_INTEGER_GREEN_STOKES_ANNIHILATION]: construct ordinary-integer source comparison from global completed/cofinal Xi Green primitive to this relative Tate top-boundary class, compatible with actual Gamma/co-Poisson Hodge boundary and completed Calderon-Witt incidence, then prove source Stokes vanishing without assuming K6/Gamma/Hardy vanishing, static capacity, positivity equivalent to RH, or RH. Generic mapping-cone/cyclic/finite exactness cannot do it because top-coordinate reader is an explicit left inverse.