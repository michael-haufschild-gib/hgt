# HB-B2 literal Peierls facts

- Literal chain: full seed/corrected future two-jets → finite two-leg action plus combined cap → compare with `contactField`.
- `streamAngularAction` uses angular first jets and diagonal angular Hessian; four-current `streamCurl` also uses angular–time/radial mixed Hessian entries (`ThetaCuspHawkingBMMixedRadialActionCurrent.lean:263`).
- `ThetaCuspHawkingBMPlebanskiAngularPolarizationNoGo` proves value/first-jet/Laplacian-only angular reduction cannot determine physical source. No trace-only substitute is admissible.
- Full-circle corpus proves all *radial* derivatives and strict growth of value/radial derivative. No proved strict-growth theorem for base-coordinate derivatives of `angularMean` found by corpus search/source audit.
- Thus current hard gate: prove literal base-coordinate and mixed derivative growth for full circle mean, then interchange those derivatives with full seed transport; this is required before an actual `ScalarTwoJet` and cyclic action can be formed.
