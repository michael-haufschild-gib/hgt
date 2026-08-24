Created formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingHorizonRedshiftWindingLadder.lean and imported it from RHTower.lean.

Genuine Fulling–Davies result:
A_kappa(eta,omega)=∫ exp(i eta exp(-kappa v)) exp(-i omega v) thetaSource(v) dv.
For every n:
iteratedDeriv n A_kappa(0,omega)=I^n XiC(omega-I n kappa).
Proof uses all real exponential moments of thetaCuspFullSource and an all-order differentiated winding-amplitude ladder.

New Hawking-native consequence: any lower-half-plane XiC zero omega creates dark deformation jets at every n>0 at surface gravities kappa_n=-omega.im/n. These are positive and tend toward zero surface gravity: cold/large-mass limit for Schwarzschild, extremal analogue only for charged or rotating holes. Defined ThetaCuspHawkingEvaporationWindingObservable and proved it iff RiemannHypothesis.

Honest producer gap: ordinary scattering allows transmission zeros. Need theta-specific horizon observability or phase-sensitive optical theorem showing backreaction cannot hide a nonzero mirror-deformation jet. Generic KMS/CCR/Krein/unitarity/Cayley do not provide this.

Conjectural next test (not formalized): in the present dimensionless theta-source clock and at carrier omega=0, complex-eta analyticity likely has sharp peeling/cusp transition: entire for kappa<2, radius pi at kappa=2, zero Taylor radius for kappa>2, from exp(kappa|v|) versus first theta atom exp(-pi exp(2|v|)).

Validation: targeted direct Lean compile passed. All new public theorem axiom audits show only propext, Classical.choice, Quot.sound. Lint reached pre-existing unrelated umbrella failure: owned module GaloisForLFunctions.HTGeometry.ClockCalibrationHasse unreachable from HTGeometry. Scratch and temporary oleans removed. No git commands used.