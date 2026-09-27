# Finite prime stabilization and negative continuous invariant (2026-09-27)

Active user goal remains prove RH via arithmetic conservation/Noether and conjecture→proof/fail→learn. RH neither proved nor falsified. Do not mark goal complete or blocked because mathematically hard. Preserve concurrent work. Repo /Users/michael/Documents/code/hgt/formal. No commits/pushes/subagents. One own foreground Lean process; leaf audits lake --old env lean file, -o .lake/build/lib/lean/...olean for downstream imports. No full umbrella builds, numerical experiments, sorry/new axioms/heartbeat hacks. Search actual Lean using ../scripts/formal_tools.py research + rg, no cards.

## Five new modules, finished and wired
All five passed final `lake --old env lean <leaf> -o ...olean` audits with no diagnostics. 19 theorem axiom audit passed; only propext, Classical.choice, Quot.sound. Temporary CCMContinuousLocalizationAxiomAudit.lean removed. Umbrella GaloisForLFunctions/RHTower.lean imports at ~19820–19824. No other mathematical source edits this turn. Generated metadata first index succeeded. Repo-wide lint failed on unrelated unwired MoebiusMollified*, XiGaussianCubicTimeControl, XiHankelCubicTimeRegion, ZetaZeroDensityPowerSaving, HTGeometry CompletedPseudoDiffOp* and DifferentialVariationalOppositeBoundaryPair; also concurrent LEAN_API.md drift. None of our five modules was reported. Final metadata refresh (session 66771) succeeded after lint, exit 0. All own processes finished; scratch removed. No full/umbrella builds.

1. CCMPrimeLocalizationStabilization.lean
- ccmThetaChainPrimeDensity_eq_twice_of_small_pieces: complete finite localization (remainder pointwise zero) with every piece supported in ball radius delta and 2delta≤log2 ⇒ chain prime density equals 2 original theta prime cross density, pointwise for all n,x.
- ccmLocalizationPrimeTotal_stabilized: integrated version P_total=2 thetaPrimeScalingCross original source.
- exists_ccmFiniteLocalization_stabilized_prime_total: every a,u has actual compact smooth finite angles with pieces in balls log2/4, zero remainder, and exact stabilized prime total.
Proof: active vonMangoldt implies prime power, hence n≥2; every prime translation is long range relative to pieces; invoke existing ccmThetaChainCross_eq_twice_correlation_of_far. No limiting/refinement sequence.

2. CCMContinuousLocalizationInvariant.lean
- def ccmContinuousArithmeticQuadratic u = integral thetaGammaPolarQuadraticDensity −2 archConstant.re*thetaGroundNormSq.
- def ccmLocalizationCompensatedEnergy u angles = Q(remainder)+sum Q(pieces)+ContinuousTotal.
- continuous arithmetic physical identity = Re(integral polar correlation on Ioc0(2a) − archimedean Weil distribution).
- ccmContinuousArithmeticQuadratic_eq_weil_add_prime: C(u)=Q(u)+2P(u).
- ccmLocalizationCompensatedEnergy_eq: compensated=Q(u)+PrimeTotal for any finite chain.
- ..._stabilized: complete pieces diameter≤log2 ⇒ compensated=C(u).
- exists_ccmFiniteLocalization_continuous_invariant: actual compact finite cover for every source with zero remainder and both compensated=C and sumQpieces+ContinuousTotal=C.
This isolates a partition-independent actual continuous quantity; it does NOT prove its sign or RH comparison 2P≤C.

3. CCMOddContinuousNegativeTail.lean
Imports CCMRestrictedWeilOddPrimeBudget, CCMRestrictedWeilPoleBoundaryBounds, Mathlib.Analysis.SpecialFunctions.Exp.
- exists_ccmOddPoleGammaPolarBalance_negative_tail: ∃A>0∀positive a≥A, literal ccmOddPoleGammaPolarBalance a ≤ −(exp a)^2/4.
- ccmOddPoleGammaPolarBalance_unbounded_below R: actual aperture a with balance<R.
Symbolic proof: c=−gamma−log(2pi), C=2log2+pi+1, K=|c|+C+2. Exponential domination gives (2a+1)exp(−a)≤1/2, 2a²exp(−a)≤1, expa≥8K. b=2sinha−2a is between expa/2 and expa; b²≥expa²/4. Boundary self≤Cexpa, cross≥0. nlinarith combines inequalities. No numerical evaluation.

4. CCMContinuousNegativeSmoothSources.lean
- def ccmContinuousFormQuadratic a v = Q(a,v)+Re inner(primeOperator(ToAperture v),ToAperture v).
- continuous_ccmContinuousFormQuadratic.
- ccmFinitePrimeOperator_ccmSource_eq_thetaPrime: actual smooth prime operator diagonal=2 thetaPrimeScalingCross.
- ccmContinuousFormQuadratic_ccmSmooth: extended quadratic agrees with C(u).
- ccmContinuousFormQuadratic_oddPole: at ccmPolarParityFormVector a (−1), equals literal ccmOddPoleGammaPolarBalance.
- exists_ccmSmoothSource_continuous_below R: actual compact smooth a,u with C(u)<R (density in complete form norm transfers strict inequality from odd pole).
- exists_ccmFineLocalization_continuous_invariant_below R: actual compact finite log2/4 cover, zero remainder, exact invariant, compensated<R.

5. CCMContinuousRayleighUnbounded.lean
- exists_ccmOddPole_continuous_below_mass R: actual a with C_form(odd)<R*norm(ToAperture odd)^2.
- exists_ccmSmoothSource_continuous_below_mass R: actual a,u with strictly positive physical mass and C(u)<R*mass. Thus negativity is not amplitude scaling; no uniform lower bound per mass as aperture varies.
- exists_ccmPositivePieces_continuous_below_mass R: actual a,u,compact finite angles,Cgap>0, original mass>0; remainder zero; EACH piece Q(v)≥Cgap*mass(v); exact masssum=mass(u); compensated=C(u)<R*mass(u). Zero pieces may occur; every nonzero physical piece is strictly positive. Pick radius min(existing universal local gap radius,log2/4).

## Meaning and next mathematics
Exact identity: Q(u)=C(u)−2P(u). Complete fine localization yields sumQpieces+ContinuousTotal=C(u) independent of partition. C(u)/mass can be arbitrarily negative, even with all local pieces satisfying a positive gap. Therefore local positivity and conservation alone cannot establish RH; they must retain and control signed prime–continuous cancellation. Negative C is NOT a negative full Q and is NOT an RH counterexample.
Actual obstruction strengthens previous turn: earlier continuous correction diverged under varying partitions of a fixed positive source. Here invariant itself is negative on constructed smooth sources, and per mass unbounded below across apertures.
Candidate continuation: study exact residual after cancelling exponentially large prime/pole terms, preserving sign; avoid merely restating existing RH criteria. Corpus already relates full pole matrix to integrated Chebyshev deficit and entry/age prime budgets; search these before duplicating.

## Existing APIs inspected for continuation
- CCMRestrictedWeilPoleIntegratedPrimeError: ccmWeilPoleCross_eq_integratedError gives cross=ccmPoleIntegratedChebyshevDeficit + c*(2a)+exp(−2a)−1+crossBoundary−integratedReciprocalError. Reciprocal error bounded linearly by (log4+5)*2a.
- CCMRestrictedWeilPoleDiagonalBounds: abs_ccmWeilPoleDiagonal_le ≤ explicit constant*exp a unconditionally. Positive pole compression gives same scale for integrated Chebyshev deficit.
- CCMRestrictedWeilPoleCompressionRHCriterion: riemannHypothesis_of_logChebyshevDeficitPrimitive_bound and riemannHypothesis_of_weilPoleCompression_nonneg already exist; parity-pole nonnegativity for every aperture is an exact RH criterion. Do not duplicate.
- CCMRestrictedWeilPoleEntryAgeSource: odd full Q=2*(DiagonalSmooth−CrossSmooth)+OddEntryTangentBudget−PrimeAgeBudget; even Q=2*(DiagonalSmooth+CrossSmooth)−EvenEntryTangentBudget−PrimeAgeBudget. All3 budgets≥0. Exact simultaneous parity comparison exists.
- PrimeTransportPoleSchurNorm:902 exists_one_sub_le_norm_ccmFinitePrimeOperator uses actual PNT tendsto_chebyshevPsiReal_div to prove operatornorm≥(1−epsilon)exp a eventually; valid epsilon>0<1. Could supply leading cancellation infrastructure, not RH-scale error by itself.

## Lean lessons
- To transfer strict inequalities by density: build explicit hi : Iio R ∈ nhds (F v) using Iio_mem_nhds, then hmem := continuousF.continuousAt hi. `apply ContinuousAt.preimage_mem_nhds` failed to infer set against set-builder goal.
- `(denseRange_ccmComplexSmoothInteriorSource_toCCMFormVector a).mem_nhds hmem` produces smooth u.
- Physical mass from ToAperture vs FormEmbedding norm is definitionally compatible; existing localization mass identity can be used directly.
- Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n; `.const_mul`, `.add`, `.eventually_le_const`; exp tends atTop provides `.eventually_ge_atTop`.
- Preserve nlinarith only lists for stable small proofs. No raised budgets needed.
- Actual smooth source combo is u.combo v w alpha beta = u+alpha*v+beta*w (THREE sources), not a two-source scalar combination; combo_toCCMFormVector matches.
