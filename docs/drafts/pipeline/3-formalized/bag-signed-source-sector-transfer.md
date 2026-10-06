# BAG signed full-plane transfer of the original growing source

01ax. Route BAG. Paper proof: P2 bag-signed-source-sector-transfer.

Lean: `GaloisForLFunctions/RHTower/ChiRamanujanSignedSourceTransfer.lean`
(520 lines, one public theorem),
`RHTower.BAGTrace.criticalCompletedConeEuler_schwartz_integral_tendsto`.
For each fixed positive rho_i and Schwartz Phi on R², the original complete
source integral against Phi, divided by logN, tends to zero. Both growing
cofactors, both exclusions, allowed collision and signed sectors retained.
No analytic, cancellation, uniformity or RH premise.

Exact label exchange, nearest-axis partition and rescaling reduce to an
integrable order58 Schwartz majorant. Almost-everywhere actual mixed-source
convergence and the zero signed vertical profile integral cancel both
sectors by dominated convergence. Full unscaled integrability and integral
assembly are formalized. No joint-box or compact-uniform remainder needed.

Audits: scratch30915 PASS; production50199 empty PASS with
`lake --old env lean GaloisForLFunctions/RHTower/ChiRamanujanSignedSourceTransfer.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/ChiRamanujanSignedSourceTransfer.olean`.
Final /tmp axiom85157 PASS: propext, Classical.choice, Quot.sound only.
Index8884 PASS, public API row verified; umbrella import once, no full build.
Lint39568 terminal1: unrelated HTGeometry HankelTangentSpace,
SourceResponseFormationEnergy and ZariskiTangentDual unreachable; no owned
error. No new axiom, placeholder or increased resource limit.

Hard remaining problem: actual N-dependent physical profile transfer;
fixed-test convergence cannot be applied directly. P1
bag-physical-height-averaging-transfer and bag-curved-frequency-energy.
No physical cubic saving or RH conclusion yet.
