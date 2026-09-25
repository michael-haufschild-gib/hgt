# Frozen native photonic loop-response experiment

## Question and prediction attempt

Does physical time-crystal evolution combined with monitoring its finite-energy lattice code preserve the ideal modular logical transport, even when geometric monitoring alone and free evolution alone do not? This is an exploratory physical-identification experiment, not a proposed universal law or a proof strategy selected for ease of formalization. Its motivation is the previous distinction between native ideal-lattice geodesic dynamics and nonhyperbolic finite-energy information metrics, together with the observed importance of stabilizer phases.

The predictable facts are excluded from discovery: free squeezing changes a lab-fixed envelope; repeated projections have finite-step loss; a closed-code change of frame conjugates holonomy. None determines whether the combined projected commutator produces a noncentral logical response after refinement. Competing explanations: the two transports cancel all noncentral error; they agree only at compact fixed-energy limits; or monitoring selects a different logical operator cocycle. We test those operator alternatives, not an optimized fidelity constant.

## Actual drive, native lattice, and retained structures

Use dq/dt=p/epsilon(t), dp/dt=-q for a transverse canonical mode in an ideal nondispersive, lossless time-varying dielectric with k=1. Temporal interfaces preserve q,p. For integer m>2 set lambda=(m+sqrt(m^2-4))/2. One physical period has epsilon1=1,duration pi/2, then epsilon2=lambda^2,duration lambda*pi/2. Each segment advances its oscillator by pi/2. The exact period matrix is F(T)=-diag(lambda^-1,lambda).

Let A=[[m,-1],[1,0]], and g=[[lambda^-1,-1],[lambda,-1]]/sqrt(lambda-lambda^-1). Then det(g)=1 and F(T)g=-gA. This chooses a closed optical displacement lattice cycle from the drive, without primes, zeta values or spectral zeros. The integral trace condition selects closed lattice orbits, not Riemann data. Stroboscopic hyperbolic motion has a geodesic interpretation on the ideal lattice quotient; the actual intra-period two-layer path is retained and is not called a geodesic at every instant.

For [q,p]=i, dim-d code columns are comb_j(q)=sum_n exp(2*pi*i*b*n)delta(q-sqrt(2*pi*d)*(n+(j+a)/d)). Use(a,b)=(0,0)for even d2 and(.5,.5)for odd d3, the modularly invariant sign sectors. E_delta=exp(-delta H0),H0=(q^2+p^2)/2. Prepare Psi_i=E_delta U(F_i g)comb; Gram G_i=Psi_i^*Psi_i; W_i=Psi_i G_i^-1/2. Every logical column/eigenvalue is retained. The ideal relabeling J=W_0^*W_final is unitary when the infinite comb closure is exact; finite truncation is checked.

Compare:
1. Geometric monitoring: K_g=J product_i(W_(i+1)^*W_i).
2. Driven monitoring: K_d=J product_i(W_(i+1)^*U(F_(i+1)F_i^-1)W_i).
3. Unmonitored evolution with final code reader: K_u=W_0^*U(F(T))W_0.

Products are chronologically ordered with later maps on the left. Projective measurements/postselection are explicit additions to the driven dielectric, not an implicit claim about ordinary PTCs. Retain rejection probabilities. No microscopic detector implementation is supplied. Each U retains exact piecewise canonical evolution. Complex heat matrix C_delta=[[cosh(delta),-i sinh(delta)],[i sinh(delta),cosh(delta)]] gives the Gaussian kernels. The propagated source has matrix (F_(i+1)F_i^-1) C_delta F_i g, not C_delta F_(i+1)g. Continue the square-root prefactor in small physical steps; do not reset the metaplectic phase indiscriminately. The final projective comparison does not identify an absolute cusp character.

## Measurements, frozen portfolio, validation

Record full complex maps, all singular values, mean/worst survival, polar unitary, its eigenvalues and phase-insensitive Frobenius distance to J. Record full Gram spectra and selected kernel/cross-Gram steps. Pair d2/3, m3/6, delta.2/.05 and64/128steps; add m10,delta.1,d2/3,64/128steps:20cases. N=ceil(5sqrt(m/(delta*d)))+4 per comb. No zeta inputs. No Monte Carlo or hidden random seed.

One600secondwhole-family guard,14workers,native threads1,3GiB/process,2GiBscratch. First full task is a sizing pilot; stop above60s or any control failure. Endpoint code closure, unitary propagation of each finite comb, and contraction of each projected step must agree to1e-7in complex128. These checks can detect a wrong kernel, phase, ordering or insufficient truncation; they are not discoveries. Partial outputs survive timeout.

A surprise requires independent50/100/160digit checks, larger outer sums and infinite-inner Jacobi evaluation, plus step refinement. Finite monitoring and finite energy are separate parameters. Full continuum/no-energy-limit claims are forbidden. Initial exploratory matrices alone are not appended as validated facts.

## Whole-route consequence and source audit

A physical realization of the modular lattice space must identify its operator response, not only its topology or a chosen metric. Noncentral transport changes would mean that the correct object is a logical matrix cocycle over lattice dynamics; silently replacing it by a scalar modular Laplacian would fail. A surviving scalar sector would still require a physical ensemble/reader, cusp boundary conditions, primitive normalization and a reason independent of RH for resonance confinement. On the standard scalar modular receiver, rho/2 lies on Re(u)=1/4under RH, not the unitary axis Re(u)=1/2.

Broad recent searches found continuous-measurement bosonic holonomy (arXiv2608.11369,Aug2026); only its framework motivates the monitoring control, not its gate formulas or finite-energy estimates. The optical GKP phase bundle (arXiv2410.07332) supplies ideal geometric context. PTC quantum geometry (arXiv2511.17317) supplies symplectic dynamics, independently derived above. Faure's May2026geodesic-to-wave construction(arXiv2605.28243) assumes a compact quotient and does not supply the required modular cusp theorem. The Series flow exposition(arXiv2605.09230) retains return times; a bare Gauss map cannot replace physical time.

Current cached deep/method search is partial with pending coverage. Source inspection of discreteConnectionTransport_gauge_closed confirms gauge-conjugacy algebra; FirstOrderConnectionIntervalClassification concerns a finite-rank connection on a finite interval and does not identify an optical modular resonance spectrum. No new Lean build, theorem, unconditional RH result or historical novelty claim. Material dispersion, finite bandwidth, detector construction, pump backreaction and HB action blocks remain explicit unresolved physical extensions.

## All24 method operations

1. **Split**: Measure three distinct maps on the same closed lattice cycle: unmonitored physical evolution; products of code projectors; physical evolution interleaved with those projectors. Retain scalar survival and logical rotation separately.
2. **Falsify**: A stable noncentral mismatch after step/precision refinement falsifies the proposed finite-energy identification with the ideal modular gate. A scalar phase alone does not.
3. **Reverse**: Start from an actual positive-permittivity temporal cycle. Determine its naturally closed lattice, rather than choosing a Riemann zero and engineering a drive.
4. **Viewpoint**: The object is a transported optical lattice and its readout holonomy, not a metric imposed on parameter space.
5. **Visual**: Plot reader-dependent survival against projective mismatch, paired by physical cycle and envelope; show refinement arrows.
6. **Action**: A pump transports the field; projections retain or reject code components. These operations are interleaved explicitly, never commuted through the energy envelope.
7. **Essentials**: Exact ideal two-layer Maxwell canonical matching, full Gaussian kernels, all logical Gram channels, phase-correct stabilizers, and metaplectic short-step continuation are retained.
8. **Similar**: Compare code dimensions2/3, modular trace3/6/10 and three readers. No transfer from a different code or compact surface is assumed.
9. **Small**: First full64-step d2,m3,delta.2case is a sizing pilot inside the same guard. Exact monodromy/closure/contraction checks are implementation controls.
10. **Extreme**: Trace10makes a larger hyperbolic excursion; smaller envelope approaches ideal energy.64/128steps independently expose finite-monitoring loss.
11. **Experiment**: 20jobs,14workers,one600secondcap. Complex128discovery; selected results require50/100/160working digits and independent inner sums before a validated ledger claim.
12. **Invariant**: The same integral endpoint matrix labels every reader comparison. Singular values and projective distance separate loss from logical twist; frame gauge conjugacy is not a discovery.
13. **Monotone**: Increasing monitoring frequency may reduce leakage but is not assumed to restore the ideal logical holonomy. The two observables test that separation.
14. **Weaker bridge**: The equation F(T)g=-gA is an exact derived kinematic bridge. It is not a physical wave/scattering identity or the headline conjecture.
15. **New hunch**: This is an exploratory identification test, not an admitted universal RH conjecture. The risky candidate is that combined physical transport and code monitoring preserves ideal projective loop transport even where either operation alone does not.
16. **Minimal counterexample**: Same code, trace and delta with only reader changed isolates the proposed cancellation between physical evolution and moving measurement.
17. **Representation**: Use complex symplectic Gaussian kernels and cross-Gram matrices instead of a Fock truncation. Store matrices for independent high-precision evaluation.
18. **Technique**: Continuous-measurement holonomy motivates the reader; Gaussian composition and frame normalization are independently derived. Recent source formulas are not copied as authoritative numerics.
19. **Fake proof**: Both transports follow the same ideal lattice, hence their finite-energy holonomies agree. Gap: E_delta U and U E_delta differ, and the projected commutator can act noncentrally on logical channels.
20. **Missing lemma**: Uniform identification of the phase-correct finite-energy physical transport/reader with ideal automorphic transport, including long cusp excursions.
21. **Dependency**: PTC evolution -> integral-lattice closed cycle -> measured operator holonomy -> justified scalar or vector response on lattice space -> cusp scattering -> RH-independent confinement. This family tests only the middle transport bridge.
22. **Nearby false**: Projector geometry alone is not actual evolution; bare unitary evolution does not reset the lab envelope. Removing either term changes the experiment and is a paired control.
23. **Boundary**: Keep ideal temporal interfaces exact; two segments have physical durations pi/2 and lambda*pi/2. Parameter t allocates half the mesh to each, not equal physical durations. Pump work is retained through nonorthogonal symplectic evolution; material dispersion/backreaction remain absent from this explicitly ideal model.
24. **Salvage**: If combined transport changes the logical response, retain the measured operator cocycle as new primitive rather than discarding its phase/weight. If it survives, investigate whether a physical ensemble reader exposes scalar cusp resonances. Neither outcome proves RH.
