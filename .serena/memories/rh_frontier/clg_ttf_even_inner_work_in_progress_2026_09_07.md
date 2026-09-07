# CLG/TTF inner determinant checkpoint, 2026-09-07

Mission remains unconditional closed Lean RH proof/falsification. RH is unproved; goal stays ACTIVE.
Full chain: literal theta source → every signed center-mixed Hankel section nonnegative → Fourier-current sign → Xi Bezoutian orientation → RH.

## Current mathematical gate
Missing: HTGeometry.evenCompactRawDet u a w = evenCompactRawPolynomial u a w.
All 21 shear identities, 22 Horner stages, 12 block grades and landing in T≥1/1000 remain checked. UnitDet(u²,t,v)=RawDet(u,A,u(1+v/4)), RawPolynomial shear/gap transports and exact actual source normalization are checked. Inner positivity for 0≤x≤8/95 is STILL A TARGET. Current proved near-zero endpoint is existential; x≥6/5 is proved. Middle, rank-seven integral and all-order signs remain open.

## Fifteen new checked gap modules; total inner manifest 113
Under formal/GaloisForLFunctions/HTGeometry:
PolynomialODEEvenCompactGapLift, GapDet, GapSourceCoefficients, GapConvolution, GapTop, GapReflection, GapReversedDet, GapLowCoefficients (each prefixed PolynomialODEEvenCompact); GapCoefficient0,1,16,17,18,19,20.
Each separately checked by foreground lake env lean in /tmp staging, exact bytes installed, exactly one HTGeometry umbrella import, needed olean emitted. No umbrella/full/cascade builds.

GapLift copies existing source expression syntax into Polynomial ℝ in gap a; no coefficient arithmetic. All 7 source eval identities/degrees 1,3,…,8 are proved.
GapDet gives exact determinant/table evaluations and natDegree≤20 for both. Its cofactor degree proof is manual; compute_degree on abstract polynomials timed out.
GapSourceCoefficients copies monomial expressions into scalar coefficient expressions with index tests, separately proves all 7 extraction identities.
GapTop proves weighted top coefficient of H4 from degree pattern2,3,…,8. Coeff20 is the existing negative rational RawGapGrade20, checked.
GapReflection proves entire weighted polynomial reflection of H4. GapReversedDet proves reflect20 GapDet=ReversedDet, coeff(20−n)=reversed coeffn for n≤20. Correction degree≤2, first six reflected coefficients vanish.
GapLowCoefficients proves exact unrolled product formulas for indices2..5.

Checked determinant-to-RawGapGrade coefficient identities: 0,1,16,17,18,19,20. OPEN: 2–15 and final polynomial-extensional assembly. Raw table coefficient simplification/assembly is not yet a final theorem.

## Efficient proof shape
Use local irreducible attributes on seven source polynomial definitions to prevent accidental expansion.
First norm_num extracts coefficients using Polynomial.mul_coeff_zero, Polynomial.mul_coeff_one, the unrolled mul_2..mul_5 lemmas and pow_succ; source coefficients remain named.
Second norm_num uses the seven source-coefficient lemmas and scalar coefficient functions.
Then unfold exact RawGapGradeN and ring1.
Do NOT globally replace substring coeff_one when templating: it corrupts Polynomial.mul_coeff_one.
Generic convolution inside symbolic Finset indices causes huge terms. Split phases and use fixed-index formulas.
For reversed checks, prove local hcorr (n)(2<n): correction.coeff n=0 using its degree bound and include hcorr in first norm_num; the reflected-zero lemma alone may be rewritten away before its condition is discharged.

## Remaining resource failures / no unchanged retries
Full raw unfold;ring1 hit57.4GB; dsimp variant12.6GB: already stopped previous turn.
Coefficient1 now PASSES at500000 heartbeats, measured1.6GB footprint.
Coefficient2 with direct formulas reaches expensive FoldConsts/partitionPreDefs traversal,4.4GB. as_aux_lemma around final ring1 bypasses that phase and reaches kernel checking,6.4GB, but did not finish within3minutes. Both interrupted, exit130. No Coeff2 installed/checked.
Coefficient15 direct reversed form fails500000-heartbeat whnf. No Coeff15 installed.
Need split these algebraic identities further into smaller coefficients/cofactors; no blind limit increases.
Pending degree2 plain/aux forms, degree15, and untested degrees3–5 are preserved in incidence/pending-lean outside formal, along with old raw/main determinant and actual-source capstone candidates.

## Audit and docs
Nineteen NEW capstones audited ONCE using /tmp scratch; every result only [propext,Classical.choice,Quot.sound]. Exact names stored in checked-modules.json gapCapstoneAudit. Do NOT re-audit them or earlier98 again.
Static formal lint exit1: unrelated unwired RHTower.ConstrainedWeilPolarDerivativeTest, RetainedPrimeDivisorConvolution, RetainedPrimeMobiusEulerIdentity. No new owned module among errors. Do not wire unverified foreign work.
Current docs updated: incidence/STATUS.md, incidence/checked-modules.json, clg-ttf-center-integration-compensation.md, rh-current-frontier-map.md. Frontier has concurrent maintainers: read exact current paragraph and patch narrowly. Universal STATUS unchanged: existing finite/all-order and full-source rules cover this bridge; compiler notes do not belong there.

## Computation and process discipline
No new numerical/external symbolic experiments. User permits only surprising hypothesis-discriminating short experiments on Runpod, with multicore Python and downloaded records; read scientific-method.md before any. No more predictable coefficient-generation runs. All earlier owned Runpod dirs removed.
One foreground Lean at a time. All checks/audits and interrupted processes have exited. All owned /tmp/clg_even_inner* staging, scratch and profiling files are removed. No owned Lean process or incomplete build output remains. Checked bytes and pending candidates are persisted in repo. No commits/push.
