Resolved whether nonlinear boundary dynamics forces orthogonal-helicity flux to vanish.

Result: FALSE at first nonlinear Einstein/second-harmonic order. For nonzero seed A and arbitrary non-self-dual orthogonal coefficient m, exact gauge-fixed BM radiation is (Gd,TGd,Gm,TGm), d=A^2 C(rho), with C,G,T nonzero on every Xi divisor. Since Im(lambda)=2 Im(rho)(1/2-Re(rho)) and Im(rho) != 0, global optical helicity flux, horizon part, and normalizable AdS boundary-response energy vanish iff Re(rho)=1/2; all three are strictly positive off line. Reflecting/fixed-boundary AdS conditions can make net symplectic current through infinity zero but do not annihilate normalizable response TGd. Higher regular perturbative orders cannot make flux identically zero near A=0 because off-line leading coefficient is positive.

Lean:
- formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingNonlinearBoundaryHelicityFluxDichotomy.lean
- imported by formal/GaloisForLFunctions/RHTower.lean
Key theorem: d4ThetaFullEinsteinGaugeFixedOrthogonalHelicityFlux_offCritical_strictlyPositive.
Annihilation classification: d4ThetaFullEinsteinBoundaryHelicityResponseAnnihilation_iff and off-critical no-go.
Docs updated: docs/reports/endpoints.md and docs/drafts/pipeline/1-in-progress/rh-current-frontier-map.md.
Verification: direct Lean passed; targeted module build passed; all 10 new theorem axiom audits only [propext, Classical.choice, Quot.sound]; lint only pre-existing unreachable modules; custom corpus research finds declarations; /tmp axiom scratch removed. No git.