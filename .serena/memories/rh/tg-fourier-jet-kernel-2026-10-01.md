# Route TG: literal Fourier–radial-jet kernel (2026-10-01)

Goal remains active: unconditional actual RH or its negation, not achieved. No subagents, numeric experiments, new axioms/holes, heartbeat increases, full/umbrella builds, commits/pushes. One foreground owned Lean process at a time; final leaf audit lake --old env lean.

## New audited result
formal/GaloisForLFunctions/RHTower/PrimeBurnolFourierJetKernel.lean (255 lines).
Concrete burnolSquarePosition M = maximalRealL2Mul volume (fun x => x^2).
primeBurnolFourierJetSynthesis E : D(M)×D(M) → H×H, E(f,g)=(f+F g,M f+F M g).
primeBurnolFourierJetSynthesis_injective proves injectivity on full physical complex L2, hence even carrier. No external analytic premise.
Every literal primeBurnolEvenFeatureLp pe is in D(M); burnolSquarePosition_primeBurnolSquareColumn identifies its actual AE image with primeBurnolRadialJet pe 2 |x|.

Proof builds maximal-domain dilation covariance M U_r=r^-2 U_r M. For g=F f and M g=F M f, formal symmetry gives <M f,U_r f>=r^-2<f,U_r M f>, actual Fourier covariance gives r^2 instead. For r>1 inner vanishes; strong dilation continuity at1 gives <f,M f>=0. Exact positive energy integral and null singleton give f0. No derivative regularity, decay or boundary assumption.

Scratch and production leaf checks pass; production no warnings. Separate import #print axioms audit all four public theorems passes with only propext/Classical.choice/Quot.sound. Umbrella wired; index refreshed. Lint exit1 on eleven unrelated unwired leaves, exact list in P3 card. No TG lint error. Owned scratch/search/audit files cleaned using apply_patch; keep production olean. Final production repetition after cosmetic comment/EOF cleanup also exited0 without warnings. No owned process remains. Scoped tracked-file whitespace check and new-leaf whitespace check are clean.

## Cards/log
P3 docs/drafts/pipeline/3-formalized/tg-fourier-radial-jet-kernel.md
P1 parent tg-fourier-radial-jet-completion.md
P1 next tg-fourier-jet-weak-kernel.md
Main log tg-source-conjecture-loop-2026-10-01.md checkpoint updated through C9.1.
TG frontier map updated.

## Hard next target C9.2: weak kernel and actual closed graph
C9.1 does NOT prove graph-closure injectivity, bounded neutral transport, graph-core density, Gamma–Xi identity, Hardy transfer, or sub-unit action.
A graph limit may cancel two jets that are not separately in L2.

Corpus-backed paper proof now on C9.2 card:
1. Actual Schwartz oscillator C=2πQ-D, B=2πQ+D, C²+B²=8π²Q²+2D².
2. Corpus Hermite h_n: C h_n=2πh_(n+1), B h_(n+1)=2(n+1)h_n. Nonzero orthogonal; normalized orthonormal and L2 complete.
3. Weak annihilation of Q²+(4π²)^-1D² gives π² b_(n+4)+(n+1)(n+2)b_n=0 with b_n=<h_n,u>.
4. Norms d_(n+1)=(n+1)d_n/π. Thus a_n=|b_n|²/d_n satisfy a_(n+4)=[(n+1)(n+2)/((n+3)(n+4))] a_n, and Bessel makes a summable.
5. Stronger simplification: no initial-mode or residue case split needed. For any r≥0, A_k=a_(4k+r) has ratio≥k/(k+1), because positive numerator difference is (4r+2)k+(r+1)(r+2). Hence A_k≥A_1/k for k≥1. Harmonic divergence forces A_1=0, recurrence positivity forces a_r=0. All coefficients0; completeness gives u0.
6. Source graph passage: test second output at Fφ, φ Schwartz. <Fφ,Mf_j+FMg_j>=<MFφ,f_j>+<Mφ,g_j>. These are continuous linear equations in physical graph coordinates, so pass to topological closure via closed kernels, no sequence extraction required. Zero first output gives f=-Fg. Actual F(D²φ)=-4π²M(Fφ) then yields weak kernel equation. This should prove closure injectivity, and closability follows similarly using Schwartz density. Literal finite source graph closure is included; equality with whole maximal graph domain is separate.
All of C9.2 remains to formalize. Do not label the paper proof Lean-audited.

## Actual corpus sources inspected
HTGeometry/SchwartzOscillatorAlgebra.lean: creation_add_annihilation, annihilation_sub_creation, mulXCLM_eq_oscillator, derivSCLM_eq_oscillator.
HTGeometry/HermiteOrthogonality.lean: creationCLM_hermiteSchwartz, annihilationCLM_hermiteSchwartz, schwartzPair_hermiteSchwartz_self_succ, orthonormal_hermiteSchwartz_toLp.
HTGeometry/HermiteFourierEigen.lean: actual Schwartz Fourier derivative identities and eigenphases.
HTGeometry/HermiteL2Completeness.lean: hermite_l2_complete (∀n inner h_n u=0)->u0.
HTGeometry/HermiteL2Expansion.lean: normalized Hermite definitions (read first80).
RHTower/DilationGeneratorNoPointSpectrum.lean exists but conjugacy here would need metaplectic/domain proof; Hermite recurrence uses already available actual tests.
Mathlib Analysis/PSeries.lean has Real.summable_one_div_nat_pow; check exact API in scratch before use.
Documented corpus searches performed and results inspected. Deep searches often partial deadlines; no absence claim. Lexical oscillator/Hermite searches supplied decisive ladder APIs. Prefer this precise route over broad noisy queries.