2026 Connes--Consani frontier formalized.

Modules:
- formal/GaloisForLFunctions/RHTower/CCMConnesConsaniArithmeticJacobianPrimeFibre.lean
- formal/GaloisForLFunctions/RHTower/CCMConnesConsaniZetaCycleCompletedXiNaturality.lean

Key results:
- Actual arithmetic-Jacobian prime fiber is twisted quotient (Additive DeningerPacketUnits p × R) / Z*(Frob_p, log p), not the existing quotient-product DeningerPrimeFibreCandidate.
- Canonical collapse onto (K/closure<p>) × AddCircle(log p) is continuous, surjective, and noninjective; it kills a provably nonzero horizontal Frobenius class.
- Existing exact Connes--Consani zeta-cycle character survival is equivalent to nonemptiness of the corresponding completed-Xi theta spectral fiber.
- Prime cover (L,m) -> (pL,pm) fixes centered Xi spectral label -2πm/L and induces a dependent fiber equivalence before zero selection.
- At p=2 this combines with Big-Witt Frobenius into ccmArithmeticJacobianBigWittCompletedXi_actualCrossFiberNaturality.
- Remaining open core: global full adelic arithmetic-Jacobian source map into completed-Xi cohomology, retaining horizontal Frobenius; it cannot factor through collapsed quotient-product receiver.

Verification:
- Direct lake env lean passes for both files.
- Targeted lake build passes for both modules.
- #print axioms reports only propext, Classical.choice, Quot.sound.
- Umbrella imports appended; umbrella deliberately not built.
- Research card: docs/drafts/pipeline/1-in-progress/ccm-jacobian-prime-fibre-frontier.md