# CHMD: full Fourier detection and the polar plane

Status: FORMALIZED. Dependency-closed paper proof and all six Lean leaves verified. RH goal remains active. Repository-wide lint still fails on eight unrelated unwired modules, listed below.

## Target and corpus audit

Remove the even-source restriction from the graph radical theorem. Prove on the original maximal graph that the full signed radical is exactly the joint kernel of all literal Xi-zero Fourier samples and both polar Fourier samples. Construct the full zero-sample nullspace as an explicit two-dimensional polar plane plus the signed radical, with its exact Lorentz signature and unique coefficients.

The previous turn classified only even sources. Its cosine readout cannot see odd Fourier data. Existing small theta translates are admitted, but translated cardinal vectors and their full-graph pairings were absent from the checked corpus. The deep search covered 72,687 indexed files without partial results; coverage snapshot lagged one generation and semantic coverage was unavailable. Generic parity/radical hits did not resolve this. Its actual useful leads were compact translation invariance, theta-relative graph admission, and cardinal graph frames. A follow-up lexical search and whole-source rg found no translated cardinal graph or graph sine detection theorem. Existing RadicalDetectionKernel supplies Fourier translation identities, not this completed-graph classification. No external novelty claim.

## Dependency-closed proof

1. Small translations of every theta-dominated Lipschitz C2 source f enter the original graph. Let t satisfy the existing strict theta-translate admission inequality. The inverse-Doob translate is bounded by M times the already-admitted theta ratio. Bulk cutoffs translated by t converge in source L2 by dominated convergence. Signed energies of their differences equal those of unshifted cutoffs by exact arithmetic translation invariance. The existing energy-transfer Cauchy theorem supplies strong graph convergence. Hence no graph translation-boundedness assumption is needed.

2. For an admitted translated source vector T_t(f), compact polarization and strong limits give

   B(T_t(f), test(q)) = B(f, test(q shifted by -t)).

   Instantiate f with the real and imaginary cardinal sources at each actual Xi zero a with positive real part. The existing cardinal pairing then detects the real and imaginary parts of

   D_t(p,a) = [exp(-i a t) F_p(a) + exp(i a t) F_p(-a)] / 2

   for every graph p. Continuity of the strip Fourier readouts and compact-core density justify this full-graph extension.

3. If p is in the full signed radical, all D_t(p,a) vanish for every sufficiently small real t. At t=0 this gives F_p(a)+F_p(-a)=0. Differentiate the identically zero local function at t=0 to get -i a F_p(a)+i a F_p(-a)=0. Since a is nonzero, both samples vanish. The negative-real-part zeros follow by Xi symmetry. This discharges the missing sine detection on arbitrary graph sources.

4. Let a_p=Re F_p(i/2), b_p=Re F_p(-i/2), C_p=(a_p+b_p)/2 and S_p=(b_p-a_p)/2. Both pole samples are real for every graph source. For p whose full Fourier samples vanish at every Xi zero, the already-proved mixed explicit formula has zero mixed series. Compact density in its second slot gives

   B(p,q) = -(a_p b_q+b_p a_q) = -2 C_p C_q+2 S_p S_q

   for every graph q, with no parity restriction.

5. The existing actual ground g has transform Xi, C_g=1/2 and S_g=0. Fix the existing positive admissible theta shift tau. Let

   h = [T_tau(Phi)-T_-tau(Phi)]/[2 sinh(tau/2)].

   Fourier translation gives F_h(z)=i sin(tau z) Xi(z)/sinh(tau/2). Thus h has all Xi-zero samples zero, C_h=0 and S_h=1/2. Its signed pairings are B(g,q)=-C_q, B(h,q)=S_q. In particular B(g,g)=-1/2, B(h,h)=1/2, B(g,h)=0: an actual nondegenerate polar plane.

6. Every full-zero-sample vector p has unique decomposition

   p = 2 C_p g + 2 S_p h + r,   r in the full signed radical.

   Its exact energy is -2 C_p^2+2 S_p^2. Every radical vector has both polar samples zero by pairing with g and h, and every Xi-zero sample zero by Step 3. Conversely vanishing of all these samples makes every mixed pairing zero by Step 4. This proves an unconditional set-level classification, with no assumed detection frame, positivity, or convergence premise.

## Plan

1. Prove translated theta-relative source admission and compact pairing transport.
2. Admit translated cardinal vectors, identify shifted cosine readouts, and prove full Fourier radical detection by local differentiation.
3. Construct the concrete polar plane and prove the full radical/nullspace classification and energy law.
4. Targeted leaf builds, final direct Lean audits, scratch API/axiom probes, umbrella wiring, index/lint, exact cleanup, memory.

## Boundary

This closes parity blindness and determines the entire invisible sector. It does not prove primitive positivity or exclude the existing possible nonreal cardinal blocks. It does not assert a bounded translation group on the entire weighted graph or a stable infinite cardinal expansion. Goal completion still requires premise-free RH.

## Verified result and research audit

The hard obstacle was parity blindness on the full completed graph: the existing actual cardinal frames detected only cosine samples. Small translations of theta-relative sources now enter the original graph through source L2 convergence and exact transfer of the full arithmetic energy of differences. Universal translated-cardinal pairings recover both exponential phases. Differentiating only this explicit scalar phase identity separates the two Fourier samples; no bounded translation group or graph generator is assumed.

The positive structural result is stronger than detection alone. The full Xi-zero sample kernel is exactly the concrete nondegenerate polar plane plus the full signed radical, with both polar coefficients uniquely forced. The full radical is exactly the joint kernel of every Xi-zero Fourier sample and both pole samples. These are unconditional set identities on the original real source graph. Neither an admitted frame, convergence premise, spectral expansion, nor primitive positivity is assumed. No new RH equivalence or receiver is used as the contribution. External novelty was not assessed, as requested.

Main declarations:
- `RHTower.CHMDDoobGraph.radical_graphFourierReadout_zero` in `CHMDTranslatedCardinalDetection.lean`.
- `RHTower.CHMDDoobGraph.polarPlane_gram` in `CHMDPolarPlane.lean`: Gram matrix `diag(-1/2,1/2)` for the ground vector and the normalized antisymmetric theta difference.
- `RHTower.CHMDDoobGraph.full_nullspace_unique_polar_coefficients` in `CHMDFullSpectralNullspace.lean`.
- `RHTower.CHMDDoobGraph.fullSpectralNullspace_eq_polarPlane_add_radical` in `CHMDFullSpectralNullspace.lean`.
- `RHTower.CHMDDoobGraph.signedRadical_eq_full_joint_kernel` in `CHMDFullSpectralNullspace.lean`.

## Verification

- Six targeted `lake --old build GaloisForLFunctions.RHTower.<leaf>` checks passed. No full or umbrella build.
- Final `lake env lean GaloisForLFunctions/RHTower/<leaf>.lean` passed for each of the six leaves below. All six direct logs were empty: no errors or warnings.
- 33 mathlib API probes passed in a `/tmp` scratch file with `have := @Name` declarations.
- `#print axioms` audited all 59 new declarations in a separate `/tmp` file. Every entry used only `propext`, `Classical.choice`, and `Quot.sound` (or a subset); no added axiom.
- 661 source lines across six leaves; every leaf imported exactly once by `formal/GaloisForLFunctions/RHTower.lean`.
- Final source hashes matched the built and directly audited versions.
- Corpus refresh returned the new main declarations. A cached module-filtered follow-up located `exponential_pair_separation`, completing verification that all six new modules are searchable. Lexical output used `fts5` and supplied no `partial`, coverage, or compiler-freshness fields; direct Lean checks establish compilation, not index metadata.
- `scripts/formal_tools.py lint` ran under `scripts/run_guarded.py --timeout 600` and exited 1. Its only errors were eight unreachable modules outside these six leaves. No own module was flagged; no active forbidden declaration was reported.

Unrelated global lint errors:
- `GaloisForLFunctions.RHTower.CHMDComplexJumpGraph`
- `GaloisForLFunctions.RHTower.CHMDComplexWeilForm`
- `GaloisForLFunctions.RHTower.PaperThetaArithmeticHolomorphy`
- `GaloisForLFunctions.RHTower.PaperThetaUniformCutControl`
- `GaloisForLFunctions.HTGeometry.CanonicalProductSubquadraticType`
- `GaloisForLFunctions.HTGeometry.EvenHermitianCanonicalFactor`
- `GaloisForLFunctions.HTGeometry.HankelHeatAdmissionFlow`
- `GaloisForLFunctions.HTGeometry.MeromorphicPolePrimitive`

## Source snapshots

All paths below are under `formal/GaloisForLFunctions/RHTower/`.

| Leaf | Lines | Declarations | SHA256 |
|---|---:|---:|---|
| `CHMDTranslatedRelativeGraph.lean` | 141 | 8 | `df2372cc14d14695d69633c0132268d7d282c35a87903b9af296b28c1eceef1e` |
| `CHMDShiftedFourierReadout.lean` | 87 | 9 | `e4a86f1b5612fd9f79f1957049370b0f88cd453433629839a0e3418d25c00716` |
| `CHMDTranslatedCardinalDetection.lean` | 101 | 4 | `c70d9dbb998fd1ad0ce26e2628ca62d1afabd9f5a896fd3c66b5e168d1b7a7b2` |
| `CHMDFullSpectralPairing.lean` | 103 | 15 | `fc40c05026be2e23084a2f8c21150ca053a67dd5682611900921b16717dbaaaf` |
| `CHMDPolarPlane.lean` | 120 | 13 | `8d1c849a74c473ad182a25b410bb13008d2b7a36138c3466d079a560ca225973` |
| `CHMDFullSpectralNullspace.lean` | 109 | 10 | `348552f8786f1daa65a7d5003569899da1b42d6f5a5c3b2f718a78e239f06eb8` |

No commit or push. Goal remains active: primitive positivity and exclusion of nonreal cardinal blocks remain unproved.

Cleanup complete: 25 explicitly owned `/tmp` search/probe/build/audit files removed; all owned compiler, search, and lint processes had exited.
