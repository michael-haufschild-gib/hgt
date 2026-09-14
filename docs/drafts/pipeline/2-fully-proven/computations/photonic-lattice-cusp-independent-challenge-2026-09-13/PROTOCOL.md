# Frozen optical-lattice cusp and reader intervention

H2: the canonical probability-weighted finite-energy code mixture may restore a common hyperbolic cusp geometry even when the support projector does not. Freeze separately from H1, which remains unchanged. Evidence motivating the question: production40-case metrics approach hyperbolicity on compact shapes but develop opposite cusp anisotropy for dim1/2; validation is still separate. Existing finite-energy isometry is at fixed lattice. Merely showing two reader metrics differ is predictable and not the discovery target. Unknown: whether joint cusp/energy limits select different end geometries, and whether retaining probabilities removes the apparent encoding dependence.

Native model uses no zeta values/zeros: psi_j=exp(-delta H0) U(M(x,y)) comb_j, with H0=(q^2+p^2)/2, comb_j=sum_n delta(q-sqrt(2*pi*d)*(n+j/d)), M=[[1/sqrt(y),x/sqrt(y)],[0,sqrt(y)]]. Rotation is retained in derivatives. This is the kinematic GKP/PTC construction defined in metric.py; all logical channels and canonical matching are kept. Ideal lattice encodings require a non-Gaussian preparation, and are an explicit extension of a Gaussian PTC. The choice of finite-energy preparation is part of the model, not imposed by topology.

Let Psi be the column operator, G=Psi^*Psi. The first reader uses P=Psi G^-1 Psi^*, a code-support projector. The second uses rho=Psi Psi^*/Tr(G), the normalized density associated with equal ideal logical mixture and the specified common envelope. We do not claim every physical preparation has these probabilities. Cross-Gram X_ab=Psi_a^*Psi_b gives Tr(P_a P_b)=Tr(G_a^-1 X_ab G_b^-1 X_ab^*) and root fidelity f(rho_a,rho_b)=||X_ab||_1/sqrt(TrG_a TrG_b), derived from the singular values of the finite-rank purification overlap. Bures distance squared is2(1-f). Central mixed differences use denominators8h^2 for projector metric and4h^2 for root-fidelity metric. For a pure rank1 state these local metrics coincide; this is only a control.

New variations: dimensions1,2,3,4; fixed x=.3; joint paths delta*y=.2 or.8 with delta=.1,.05,.025; fixed y=1 controls at same regulators. Total36cases. Both full3D tensors and rotation Schur complements retained; ratio, cross and scale reported. Record Gram spectrum, condition, normalized density spectrum and purity. Finite truncation uses same explicit N heuristic as firstfamily;50working digits and step1e-6, not50claimed accurate digits. All36tasks including pilot share600seconds with max14workers/native threads1. No comparison with known zeta zeros.

Small negative eigenvalues of X^*X from roundoff may be clipped only when within10^(-dps+15)times its largest eigenvalue; larger negativity is a recorded error. No physical Gram eigenvalue is dropped or rank threshold imposed. Selected finite results need100/160digits, step and cutoff refinement, independent inner Jacobi sums, and independent direct singular-value fidelity evaluation.

Current corpus search partial/source-only, output retained. Source-read operatorBuresRootFidelity_eq_finiteMatrix has positive-operator assumptions and a direct matrix/trace bridge; related rectangular-incidence identity is a candidate. Neither establishes this infinite ideal encoding or derivative limit. No Lean builds.

Broad recent fidelity search: Ju/Moller/Tzeng, Fidelity and quantum geometry approach to Dirac exceptional points in diamond nitrogen-vacancy centers, arXiv2602.00666v2, April1,2026; primary abstract inspected. It motivates retaining directional anisotropy and dark directions instead of summarizing a scalar susceptibility; its non-Hermitian negative-metric results do not apply to positive Bures geometry here. Other broad fidelity results from wildfire/vision are not adopted. Mayrand/Royer arXiv2605.28784 Theorem5.2 remains fixed-lattice, not a uniform-cusp licence.

Whole-route consequence: if one natural physical preparation has a different limiting end, arithmetic topology does not itself determine the Riemann receiver. A surviving scalar geometry must be tied to that preparation and actual dynamics. If common hyperbolicity survives, this remains a metric bridge and does not prove the full scattering operator or RH confinement. Full PTC material/pump dynamics, stabilizer-phase transport, modular boundary scattering, and HB SS/SV/VV/contact/remainder blocks remain unresolved, not zeroed.

## All24 method variations

1. **Split**: Two physical preparation/readout geometries, four logical dimensions, compact and two coupled cusp paths.
2. **Falsify**: Test H2 that the canonical mixture restores one hyperbolic end; retained anisotropy or dimension dependence falsifies finite versions and challenges limiting claim.
3. **Reverse**: Inspect Gram eigenvalues to determine whether normalizing code support magnifies weak channels; do not infer causality from correlation.
4. **Viewpoint**: Replace uniform probability on code support by actual canonical mixture density; topology alone does not specify probabilities.
5. **Visual**: Plot both metric ratios and density purity versus regulator on fixed-cusp-product paths.
6. **Action**: Mix logical inputs before normalization; combine this reader change with stronger squeezing and energy-envelope removal.
7. **Essentials**: Retain entire cross-Gram and its singular values. No deletion of small logical eigenvalues except recorded roundoff handling.
8. **Similar**: Dimensions1,2,3,4 distinguish pure state from several code capacities; d1 readers must agree as a cheap check.
9. **Small**: Pilot is one complete d1 case within cap, including both metrics; identity of pure-state readers checks implementation.
10. **Extreme**: delta decreases while y=c/delta increases; fixed-y compact controls distinguish limits. No infinite-limit claim from three scales.
11. **Experiment**: 36cases,14workers,one600secondcap; selected outcomes demand100/160 independent challenge.
12. **Invariant**: Symplectic area2pi*d and common lattice shape within each reader pair; mixture invariant under unitary logical basis relabeling.
13. **Monotone**: Measure purity and Gram conditioning without assuming either alone predicts metric directionality.
14. **Weaker bridge**: Compact-region agreement survives separately even if H1/H2 uniform cusp claim fails.
15. **New hunch**: H2 is separately frozen: canonical mixture may restore common hyperbolic end. It does not redefine H1.
16. **Minimal counterexample**: Seek first dimension/cusp path where stable mixture and projector geometries disagree qualitatively.
17. **Representation**: Bures root fidelity from singular values of cross-Gram, contrasted with support-projector overlaps. Validate SVD/eigen and theta/recurrence separately.
18. **Technique**: Current corpus has operator/matrix Bures and rectangular-incidence identities; no claimed GKP derivative or cusp theorem.
19. **Fake proof**: Fixed-lattice isometry allows replacing Gram by scalar identity uniformly at the cusp. The missing uniform bound is precisely tested.
20. **Missing lemma**: Preparation-independent physical cusp geometry, or a justified unique preparation and surviving response generator.
21. **Dependency**: Native quantum lattice -> canonical finite-energy density -> full physical distinguishability -> end geometry -> scattering. Later arrows remain open.
22. **Nearby false**: Support projector and probability-weighted density share support but need not have the same metric. Difference alone is known; its limiting geometric form is the discovery target.
23. **Boundary**: Track all Gram eigenvalues and positivity, finite sums and finite-difference scales. Small singular values retained; no hard rank cutoff.
24. **Salvage**: Identify which channels/limits carry hyperbolic geometry. If no universal metric survives, specify the actual density/reader needed for further dynamics instead of declaring all photonic approaches dead.

## Frozen independent density/cusp challenge
Eight selected configurations, each at100/160digits: strongest coupled-limit points for dim1/2 onboth cpaths, dim3/4 atc=.8, plus compact dim3/4 references. Replace inner finite comb sum by Jacobi theta, double outer cutoff, reduce derivative steps to1e-8/1e-10, and replace square-root eigenvalues of X^*X by direct complex SVD of X. Exact mpmath1.3.0 API was inspected on authorized pod before use. Full metrics and Gram/purity data retained. Accept only if every taskstatusok and100/160component discrepancy<1e-5relative, with absolute floor1e-8 for vanishing tensor components;production comparison<1e-3relative. Eigenvalue positivity and dim1 equality are separately audited. All16tasks including pilot shareone600secondcap. Main operator formula is supported by source-inspected rectTraceNorm_sheetTargetIncidence_eq_operatorBuresRootFidelity (no rank/injectivity/closed-range premise); no claim that ideal GKP or derivative limits are formalized. All24method operations remain instantiated through reader×regulator×dimension interactions, full matrices, adverse precision/representation and cusp-versus-compact controls.
