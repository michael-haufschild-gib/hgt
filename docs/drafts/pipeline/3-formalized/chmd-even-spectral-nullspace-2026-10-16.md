# CHMD: exact even spectral nullspace

Status: FORMALIZED. Dependency-closed paper proof, targeted builds, direct Lean audits and axiom audits pass; index refreshed. Global lint reports five unrelated module-reachability errors, listed below. Overall goal remains premise-free RH.

## Structural target and attack

For every vector p in the original complete arithmetic graph whose literal real source is even almost everywhere, let C_p denote the literal cosine readout. Proved: if C_p vanishes at every Xi zero, then

  p - 2 Re(C_p(i/2)) ground belongs to the full signed radical.

Consequently, on the even sector, radical membership is exactly simultaneous vanishing of all Xi-zero cosine samples and the polar cosine sample. The signed energy of an even spectrally invisible vector is exactly -2 Re(C_p(i/2))^2. Thus the only non-radical even direction invisible to all zero samples is the already known ground direction. This is an exact classification on the full maximal graph, not an RH equivalence, improved estimate, or assumed completeness receiver.

The prior cardinal projection result proves necessity of zero-sample vanishing but not this converse. The abstract multiplier radical theorem does not apply to arbitrary completed graph vectors. The recent EvenSectorPolarCompletion result still assumes positivity of an arithmetic source cone and does not settle this graph classification. A full-corpus deep search was nonpartial (72,660 indexed files); its generic compact-support suggestions were not applicable. Direct corpus/dependency inspection found the unconditional compact Fourier zero-sum summability theorem. External novelty audit omitted under the user's explicit instruction; no beyond-corpus novelty claim.

Verdict: PAPER PROVED AND LEAN VERIFIED within the checked corpus. Potential failure point was exchanging completion with the infinite zero sum. The proof below supplies an operator-norm summable mixed series.

## Dependency-closed paper proof

Write mu(dx)=Phi(x) cosh(x/2) dx, with mu(R)=1/2. For |Im(z)|<=1/2, the Fourier kernel k_z(x)=exp(i z x)/cosh(x/2) satisfies |k_z(x)|<=2: exp(-Im(z)x)<=exp(|x|/2)<=2 cosh(x/2). Thus its real and imaginary parts belong to L2(mu), uniformly bounded in norm. Their inner products with the actual source coordinate of p give a continuous real-linear functional F_p(z), with operator norm bounded uniformly throughout the closed critical strip. The weighted integral identity identifies it with the absolutely integrable literal paper Fourier transform of Phi times the source coordinate. Real sources give conjugate F_p(conjugate z)=F_p(-z). At both poles F_p is real.

For every compact real C2 test q, the existing unconditional EF_zero_sum_summable theorem gives absolute summability of mult_rho F_q(gamma_rho). Applying the same theorem to q(-x) gives absolute summability with -gamma_rho. Therefore the continuous real-linear maps

  p |-> mult_rho [F_p(gamma_rho) F_q(-gamma_rho) + F_p(-gamma_rho) F_q(gamma_rho)]

are summable in operator norm. Their sum is a continuous functional on the complete original graph. Add the two explicit polar products and take the real part divided by two for the zero term. For compact p, expand the full signed energy of p+q only after establishing summability of both diagonals and the mixed series. Real Fourier conjugation identifies this functional exactly with the existing signed graph pairing. Compact-test graph density extends the identity to every graph p.

If p has even literal source almost everywhere, change variable x -> -x in its integral to obtain F_p(-z)=F_p(z); hence F_p(z)=C_p(z). If all Xi-zero cosine samples vanish, the entire mixed zero term is zero. Let c=Re(C_p(i/2)); evenness makes both polar Fourier values equal to this real c. For every compact q the identity becomes

  B(p,q) = -2 c Re(C_q(i/2)) = 2 c B(ground,q).

Both sides are continuous in q, so density gives the same equality for every graph q. Therefore p-2c ground belongs to the full signed radical. Taking q=p gives E(p)=-2c^2. The ground has source Phi, Fourier transform Xi, and polar cosine value 1/2, so it is itself zero-silent. The earlier universal cardinal pairing proves every radical vector has all zero samples zero; its pairing with ground proves the polar sample is zero. These facts give both directions of the stated classification and uniqueness of the ground coefficient.

Every ingredient is unconditional: actual theta mass, actual compact EF summability, actual compact core density, and actual cardinal graph admission. No primitive positivity, spectral completeness, or RH premise occurs.

## Plan

1. DONE: Literal strip Fourier functionals with uniform operator norm control and symmetry.
2. DONE: Operator-norm summable mixed zero functional and compact explicit-formula polarization.
3. DONE: Full-graph extension, exact even nullspace decomposition, energy law and radical classification.
4. DONE: Leaf builds; final plain Lean audits; API/axiom checks; umbrella wiring; index/lint execution; exact owned-scratch cleanup.

## Formalization progress

All six new leaves pass targeted `lake --old build` checks and are wired exactly once into `RHTower.lean`. The generic complex-kernel functional, literal strip Fourier readout, operator-norm summable mixed series, full-graph mixed explicit formula, polar ground identification, and exact even nullspace classification are formalized. The density extension has no source regularity or assumed convergence premise. The actual ground belongs to the even spectral nullspace, so the classified ground direction is inhabited.

Main declarations, all in `RHTower.CHMDDoobGraph`:

- `sourcePair_testLift_eq_mixed`: arbitrary graph vector against every genuine compact C2 test.
- `even_nullspace_pair`: every pairing of an even zero-silent vector is fixed by its polar sample.
- `groundResidual_mem_signedRadical`: canonical ground subtraction lands in the full signed radical.
- `even_nullspace_energy`: exact energy `-2 Re(C_p(i/2))^2`.
- `even_nullspace_unique_ground_coefficient`: unique residual-radical coefficient.
- `evenSpectralNullspace_eq_ground_add_radical`: unconditional set-level ground-plus-radical classification.
- `even_signedRadical_eq_joint_kernel`: unconditional set-level identification of the even radical with the joint Xi-zero/polar kernel.

Lean-specific repairs: use `ContinuousLinearMap.opNorm_smul_le` and `opNorm_add_le` for real-linear maps with complex output; the generic `NormSMulClass` route did not synthesize in this toolchain. Supplying the operator-space parameter to `Summable.of_norm_bounded` eliminates the costly inference. Explicit real-to-complex test types keep Fourier coefficient sums syntactically aligned. No heartbeat increases.

## Research audit

Structural obstacle removed: the completed graph previously had only a necessary spectral vanishing condition for radical membership. The exact converse is now proved on its full even sector, including arbitrary nonsmooth graph vectors, and the sole polar obstruction is explicitly split off as the actual ground vector. The argument proves convergence before using the infinite series and proves equality by the existing genuine compact core. No completeness receiver, primitive positivity hypothesis, truncation experiment, or finite-dimensional surrogate replaces the original graph. The remaining positivity problem is not concealed by the classification: nonreal cardinal directions are still not excluded. External novelty remains unassessed, as requested.

## Verification

- Six new leaves, 666 lines, 69 declarations; each passes targeted `lake --old build` and final direct `lake env lean <leaf>`.
- All six final direct audits exit 0 without warnings. Source hashes remained unchanged throughout the audit.
- All 69 new declarations audited using `#print axioms` only in `/tmp`; dependencies are limited to `propext`, `Classical.choice`, and `Quot.sound`.
- 92 exact-name `have := @Name` API probes pass in two `/tmp` scratch files.
- Six imports occur exactly once in `RHTower.lean`; root reachability confirmed through `MainTheorems.lean`.
- Prior graph cosine readout, universal cardinal pairing, and continuous orbit projection source hashes remain unchanged.
- Guarded `scripts/formal_tools.py index` exits 0; generated API/gap/overview documents refreshed, with 9 changed indexed modules including concurrent work.
- Guarded `scripts/formal_tools.py lint` exits 1 solely on missing theorem-area umbrella reachability for five modules outside this turn's write scope: `CHMDPolarJumpForm`, `DeningerMeyerCohomologyExponential`, `DeningerMeyerConvolutionTopology`, `DeningerMeyerGaugeJets`, and `PaperThetaConvolutionGauge`. No error names any of the six new leaves. These unrelated modules were not modified.
- All 30 owned scratch files removed and verified absent after rechecking all six source hashes. All owned build/audit/index/lint processes reached terminal status.
- No full or umbrella build, numerical experiment, heartbeat increase, commit, or push. RH goal remains active.

## Boundary

No primitive positivity or exclusion of nonreal zeros is claimed. This classifies the even zero-invisible sector; it does not identify the radical as the closure of the existing translated theta modes. Odd-sector detection remains separate. RH goal stays active.
