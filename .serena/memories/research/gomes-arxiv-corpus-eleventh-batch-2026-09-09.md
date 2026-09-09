# Gomes arXiv corpus experiment — eleventh verified batch

Goal remains active. User wants as many mechanical corpus applications as possible of arXiv:2607.24901, 2509.25276 (latest v7; do not resurrect the old withdrawn equivalence), 2404.10461. New files explicitly describe corpus applications of reconstruction/frame/tensor viewpoints, not numbered paper transcriptions. Do not claim whole papers formalized.

## Rules
Only Lean corpus research via scripts/formal_tools.py research; no cards/docs reads. Closed data-parametric theorems and complete iff classifications; no supplied mathematical proof hypotheses, sorry, admit, added axioms, opaque, unsafe. No numerical computation tactics. One foreground Lean invocation per agent; scratch lake env lean /tmp/..., final lake build Exact.Module only. No full or umbrella builds, wire own modules, no commits/push/subagents. Others edit shared tree: do not wire unfinished unrelated modules or kill their processes. Serena symbol operations returned Lean paths ignored; fallback bounded edits after scratch verification.

## Verified result
94 new theorems, 19 definitions, 12 new modules. Cumulative experiment: 603 theorems / 70 modules (previous 509/58). Added .favard logMass diagonal logLower to existing GomesMomentModel and proved its positivity internally. Rebuilt model-dependent geometry through GomesMomentFluxReconstruction. All 12 new targets built. Axiom audit covers 181 declarations across 12 new + 7 earlier affected/context modules including model type, four constructors, recursor. Only propext, Classical.choice, Quot.sound; no extra axioms. All 19 source hashes rechecked unchanged after audit. No owned Lean process left.

All new modules wired into respective umbrellas. Global lint failed only on unrelated RHTower.FokasLenellsOperatorNormObstruction and FokasLenellsOperatorNormRegularity being unwired. Do not wire those. Generated index refreshed. Artifacts: /tmp/hgt-gomes/eleventh/{progress.json,modules.json,reaudit-modules.json,counts.json,totals.json,build-status.json,leaf-build-status.json,axiom-audit.json,AxiomAudit.lean,axioms.log,lint.log}. prepare_audit.py strips nested comments/strings correctly (older naïve parsers miscounted comment text). Goal not marked complete.

## New modules (namespace GaloisForLFunctions.HTGeometry unless RHTower specified)
GomesFavardData 5 thms/2defs
GomesMomentMassScale 12/1
GomesFavardParameterReconstruction 7/0
GomesCanonicalMomentGeometry 10/1
GomesUniformTailFrameGeometry 4/1
RHTower.GomesSemilocalGammaFrameGeometry 12/3
RHTower.GomesLognormalFrameGeometry 4/2
RHTower.GomesResetCounterFrameGeometry 4/1
RHTower.GomesDilatedArcsineFrameGeometry 5/2
GomesFockObservationFrameGeometry 11/3
RHTower.GomesStieltjesAtomicFrameGeometry 9/2
GomesMomentMassTensorCovariance 11/1

## Core results and APIs
Underlying moment infrastructure has root namespace HTGeometry. GomesFavardLower q 0=0, successor=exp(q n). GomesFavardMoment r a q n=exp r * favardMoment a (lower q) n.
gomesFavard_canonical_reconstruction_iff s: s=gomesFavardMoment(log(s0))(monicOrthoAlpha s)(fun n=>log(monicOrthoBeta s(n+1))) iff PositiveMomentForm s. Converse/inverse Favard proof built by recurrence identification and triangular strong induction, not assumed. gomesFavard_positive_iff_exists_data gives exact all-positive coverage. gomesFavard_mass_reconstruction_iff a b s is arbitrary-mass Favard reconstruction iff positive-degree Favard polynomials are annihilated by the source functional, without positivity assumptions.
gomesMomentMassScale r s n=exp r*s n. For arbitrary even degenerate s, monicOrtho, alpha/beta, recurrence coefficients, secondKind, real frame, monicOrthoC, secondKindC invariant; inner and normSq scale by exp r; positivity iff original.
gomesFavardMoment_{monicOrtho,alpha,beta_succ,normSq} recover parameters. _injective_data: full source equality iff all logMass, diagonal and logLower data equal. _frame_mass_invariant and _full_frame_incomplete: every real frame at every level/point forgets mass, with explicit distinct r versus r+1 sources.
gomesCanonicalMomentModel s extracts canonical .favard data. _moments_iff: model.moments=s iff PositiveMomentForm s. gomesMomentModel_exists_iff covers exactly all positive sources. gomesCanonicalMomentModel_recovery M identifies existing models exactly; frame/quotient/gram/flux recovery follow. gomesMomentModel_jacobi_reconstruction: source equality iff mass and all alpha/successor beta coefficients equal. gomesMomentNormalizedFlux_mass_probe: D_0(I)_(0,0)=complex cast(2/M.moments0). gomesMomentModel_tensor_reconstruction: all alpha/beta + this one fixed tensor entry reconstruct source.

gomesMassScaledModel M r=canonicalModel(massScale r M.moments). _moments exact, _zero source identity, _comp additive logarithmic action. _frame, _quotient, _wave invariant. _energy=exp(-r)*original; _gram and _flux=exp(-r) • original. _source_injective: scaled sources equal iff r=t. _flux_stabilizer: scaled flux=original iff r=0 OR z.im=0, for every level including zero. Thus nonreal flux detects mass exactly while the real boundary loses it.

## Ten concrete source families
Each family proves exact source representation, a strict height iff for the actual monicOrthoC source quotient, full normalized-flux positive-definite iff (0<z.im AND n≠0), and mass probe identifying the ORIGINAL source mass. No hidden normalization.
Uniform reciprocalTailClock (uniform [0,1]); completedPrimeGammaFarRightMoment (signed moments, mass 1/2); ccmMetaplecticGammaMoment; semilocalFinitePrimeCyclicMoment with primes supplied by arbitrary indices Nat.nth Nat.Prime; positiveRecurrenceSeparationMoments with variance NNReal(exp r); resetCounterMoment a (exp r)(exp t); coordinateDilatedMoment with both signs of exp r; completed Fock coordinate observations; completed Fock vector affine-chart observations; finite atomic squared-weight moments plus stieltjesPerturbedSequence.
Root source namespaces: RHTower, reset nested RHTower.XiShiftedCanonicalAdmission, dilation nested RHTower.XiShiftedArcsineAdmission.
GomesFockObservationFrameGeometry adds gomesFockVector_positive_iff B x and _canonical_recovery_iff: exactly x≠0. gomesFockObservationVector y=Fin.cons 1 y supplies nonzero data for all y. B : Fin k → Matrix(Fin(d+1))(Fin(d+1)) Complex, completed generators from prior module.
GomesStieltjesAtomicFrameGeometry: gomesAtomicMoment S w n=sum x∈S,(w x)^2*x^n. _inner=sum (w x*p.eval x)^2. _nonnegative. _kernel exact zero-energy iff all weighted evaluations vanish. _not_positive via monic annihilator product(X-Cx), for every finite S including empty. Positive survivor gomesAtomicStieltjes_positive proves every positive uniform-tail perturbation removes kernel; full source frame/tensor results formalized. No route-card reads/writes per user instruction.

## Next reusable candidate (already searched)
Search freeFockVectorMoment smul found existing theorem; DO NOT duplicate it. FreeFockMatrixValuedSpectralLaw.lean:489 gives freeFockVectorMoment A (c•x) n = Complex.normSq c * freeFockVectorMoment A x n, unconditional. Read 489–556 this turn: existing parallelogram, spectral-measure scaling too. Potential next experiment: classify phase/amplitude ambiguity of canonical Fock frames and flux using this homogeneity plus new mass covariance; zero-vector/c=0 degeneracy needs exact closed iff handling.

## Lean lessons
Use NNReal type explicitly if scope notation ℝ≥0 is unavailable. Mathlib API verification scratch needs explicit universe levels when bare have := @genericName has unresolved universes: e.g. @smul_left_injective.{0,0}, @mul_right_cancel₀.{0}, @Polynomial.monic_prod_of_monic.{0,0}, @Finset.prod_eq_zero.{0,0}. smul_left_injective R hm takes scalar ring explicitly. Mass probe simp needs div_eq_mul_inv. gomesMassScaledModel tensor covariance proofs simplify mass-scaled norms, use Real.exp_neg, smul_smul, mul_inv_rev, and commutativity. Nat.prime_nth_prime n verified in scratch. Atomic kernel uses Finset.sum_eq_zero_iff_of_nonneg and sq_eq_zero_iff; annihilator nonzero via monic_prod_of_monic and monic_X_sub_C.
