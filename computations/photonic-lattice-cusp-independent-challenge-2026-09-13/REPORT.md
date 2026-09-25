# Finite-energy cusp geometry depends on the optical reader

Numerical experiment; no zeta input, Riemann-zero computation, Lean proof, or physical scattering identification.

## Question and measured objects

For an optical oscillator with [q,p]=i, take dim-d ideal lattice code columns comb_j(q)=sum_n delta(q-sqrt(2*pi*d)*(n+j/d)), j=0,...,d-1. Prepare Psi=exp(-delta H0) U(R(theta) M(x,y)) comb, H0=(q^2+p^2)/2, M=[[1/sqrt(y),x/sqrt(y)],[0,sqrt(y)]], and retain all columns. G=Psi^*Psi is the Gram matrix.

Compare support projector P=Psi G^-1 Psi^* with the normalized canonical mixture rho=Psi Psi^*/Tr(G). The former gives every surviving logical direction equal support weight; the latter retains the preparation's Gram weights. Root fidelity between two mixtures is ||Psi_a^*Psi_b||_1/sqrt(Tr(G_a)Tr(G_b)). The support metric is Tr(dP dP)/2; the density metric comes from squared Bures distance 2(1-root fidelity). Both full 3D tensors in x,y,theta are saved. A separately chosen rotation-insensitive reader uses the Schur complement Q_ij=g_ij-g_i,theta*g_theta,j/g_theta,theta.

H2 was frozen before computation: retaining the actual mixture weights could restore a common hyperbolic cusp geometry even where the support metric failed. It was not predictable from the algebraic difference between readers whether this would occur. The test of standard marked hyperbolic geometry uses Qxx/Qyy=1, Qxy=0 and constant y^2 sqrt(det Q). It does not classify intrinsic curvature under arbitrary coordinates.

## Outcome and validation

All36 production cases completed: d=1,2,3,4; fixed x=.3; delta=.1,.05,.025; coupled cusp paths delta*y=.2,.8, plus fixed y=1 controls. All16 independent challenge tasks passed at100/160 working digits, replacing the inner finite comb sum with infinite Jacobi summation, doubling the outer truncation, reducing finite-difference steps from1e-6 to1e-8/1e-10, and replacing eigenvalues of X^*X with direct complex SVD for fidelity. No Gram eigenvalue or logical channel was discarded. Whole families took84.394s and211.574s.

Largest100/160 full-tensor component discrepancy, divided by max(component magnitude,1e-8): 6.94e-13. Largest production/challenge discrepancy: 6.94e-09. Pure-state d=1 reader ratio discrepancy in production: 1e-10. Working precision is not a claim of that many accurate derivative digits; no interval enclosures.

| d | y | delta | Support Qxx/Qyy | Mixture Qxx/Qyy | Gram condition |
|---|---:|---:|---:|---:|---:|
|1|8.0|.025|1.04701422778|1.04701422778|1|
|1|32.0|.025|5.99249306661|5.99249306661|1|
|2|8.0|.025|0.951444156506|0.975519957107|1.0819746|
|2|32.0|.025|0.00687954072745|0.0419907235559|6.169944|
|3|32.0|.025|0.157579772971|0.176116997266|5.3048466|
|4|32.0|.025|0.00230404740906|0.00632864874404|76.12328|
|3|1|.025|1|1|1|
|4|1|.025|0.999999999977|0.999999999989|1.0000006|

Fixed y=1 data approach the marked hyperbolic ratio as delta shrinks. Along delta*y=.8, the mixture at delta=.025 instead gives ratios about5.99249, .0419907, .176117, .00632865 for d=1,2,3,4. The mixture changes the cusp response but does not restore standard hyperbolic proportionality at these finite coupled points. In the d=2 example the Gram condition is only6.17, so blaming the discrepancy solely on numerically discarded tiny channels would be false. The scan does not establish any infinite cusp limit.

## Consequence for the whole route

The data challenge the specific proposal that finite-energy optical distinguishability automatically chooses the standard modular metric, uniformly into the cusp. Reader weights are physically consequential. An abstract lattice quotient alone does not identify its measured response with scalar modular scattering. Odd d uses a fixed zero-stabilizer-phase section, which is not globally invariant under the full modular group; those cases cannot silently be assigned to that scalar quotient. Phase-correct variations are a separate experiment.

Positive salvage: this does not kill the native geodesic-flow construction. On the ideal lattice space SL(2,R)/SL(2,Z), left multiplication by a hyperbolic PTC monodromy is conjugate, after inversion, to a time sample of modular geodesic flow. That dynamical identification does not require the Bures or support metric to be hyperbolic. Its unresolved bridge is a physical reader/preparation that preserves the relevant flow response, including phase and envelope data. More local metric scans cannot substitute for that bridge.

These preparations have the order E_delta U(M). Actual unitary evolution of a prepared state has order U(M) E_delta. These differ for a squeeze. Thus the present experiment is an encoding/reader-geometry test, not an actual temporal evolution simulation. The next decisive question concerns the full lifted transport and its measured response, not another improvement of these ratios.

For the standard modular cusp receiver, Riemann zeros rho map to spectral resonances u=rho/2; RH would constrain Re(u)=1/4, whereas scattering unitarity applies on Re(u)=1/2. Optical geometry or unitarity alone cannot close that gap. The full physical response generator, phase/logical/metaplectic channels, cusp boundary law, primitive normalization, material/pump terms and RH-independent confinement mechanism remain open. No HB physical-action identification is claimed.

Primary input: optical lattice/phase-bundle geometry (arXiv2407.03270,2410.07332), finite-energy encoding (arXiv2605.28784), PTC quantum geometry (arXiv2511.17317). Current cached deep searches and source inspection support the finite-column trace-norm fidelity identity but provide no checked continuum optical cusp theorem. No Lean builds or historical novelty claim. All raw tensors, Gram spectra, protocols, methods, code and provenance are retained.
