# WP03 C30d: ordinary harmonic sign fully formalized
Goal ACTIVE/OPEN, unbudgeted. Exact WP03 is the bounded-height literal quotient detector from arbitrary WeilPositiveFull lam, not just harmonic sign. Read docs/reports/weil-work/03-singular-arithmetic-detection.md and docs/reports/rh-current-frontier-map.md WP03 row. Continue hgtl7 every turn, fresh corpus search, paper before Lean. No subagents authorized, no commits/push, no computations, no full/umbrella builds, one foreground Lean/Lake process, targeted --old and final lake env lean source audits. Write scope: WeilWorkSingularArithmetic*.lean, WP03 card/results and relevant frontier row; unrelated modules read-only.

Authoritative card:
docs/drafts/pipeline/1-in-progress/weil-work-03-singular-arithmetic.md
Results: docs/reports/weil-work/results/03-singular-arithmetic/{RESULT,PROOF,EVIDENCE}.md
PROOF is >500 lines: rg/targeted offsets, not full read.
Previous context: mem:research/weil-work-03-c30c-signed-gaussian-bound-2026-10-07

## C30d complete, iteration PROGRESS
Five new leaves, all targeted --old builds AND final direct lake env lean file.lean checks exit0, no warnings. All12 public definitions/theorems individually #print axioms in /tmp: only propext, Classical.choice, Quot.sound. All imports wired in RHTower. No owned jobs/unverified source remain. All25 owned C30d scratch/log/research files including C31 research JSON removed after jobs exited. Raw build logs removed; evidence recorded in EVIDENCE.

1. WeilWorkSingularArithmeticGaussianProfile.lean:
sourceGaussianProfile lam t := sum_n sourceSquareCoeff lam n * exp(-pi*n²*t).
hasSum_sourceGaussianProfile hW ht.
exists_norm_sourceGaussianProfile_le hW: exists C>=0 forall t>0, norm H(t)<=C/t.
exists_re_sourceGaussianProfile_le hW: exists C>=0 forall 0<t<=1, Re H(t)<=C*t^(-5/12).
Normalization T=sqrt(4*pi/t); no coefficient sign premise.

2. WeilWorkSingularArithmeticMellin.lean:
mellinConvergent_sourceGaussianProfile hW hs for Re s>1, argument s/2.
mellin_sourceGaussianProfile hW hs:
mellin H (s/2)=Complex.Gammaℝ s * sourceZetaSquare hW s.
Convergence separately proved using norm Fubini, not default-valued integral identity.
Private integrable_tsum_of_norm_integrals: AEMeasurable.tsum + ENNReal sum bound.
Private mellinConvergent_of_exponential_series adapts mathlib hasSum_mellin norm-integral proof.
Actual normsum supplied by sourceSquareCoeff_summable, no extra hypothesis.

3. WeilWorkSingularArithmeticMellinBound.lean:
exists_re_mellin_sourceGaussianProfile_le hW:
exists B forall real 1<sigma<3/2, Re(mellin H (sigma/2))<=B.
Uses fixed integrable upper envelope C*t^-11/12 on(0,1] + D*t^-5/4 on(1,infty).
It is only an upper envelope; actual integrability comes independently from Mellin.

4. WeilWorkSingularArithmeticPoleSign.lean:
tendsto_sq_mul_re_mellin_sourceGaussianProfile hW:
(sigma-1)^2 Re Mellin -> Re(sourcePoleNumerator hW 1), sigma->1+.
re_sourcePoleNumerator_one_nonpos hW:
Re(sourcePoleNumerator hW 1)<=0.
Gamma_R1=1, continuity via reciprocal Gamma_R. Existing RHTower.tendsto_ofReal_nhdsWithin_ne_one reused.

5. WeilWorkSingularArithmeticHarmonicSign.lean:
centered_source_dirichletSum_one hW:
dirichletSum (fun n=>lamC lam(n+1)-1)1 =
sourcePoleNumerator hW1 -2*gamma.
Uses centered source ordinary convergence at3/4 -> continuity at1 and absolute DS identity to right of1, plus existing zeta Laurent limit.
tendsto_coneDeviation_harmonic_pole hW:
sum_(n in range(N+1)) coneDeviation lam n/n -> Re P(1).
exists_nonpos_tendsto_coneDeviation_harmonic hW:
exists L<=0 with that ordinary convergence.

This removes NotchSmall from older WeilConeHarmonicPinning.nonpos_of_tendsto_harmonicSum.
No nonnegative coefficients, local absolute mass, RH or zero-free premise added.
Mellin machinery classical; no publication novelty claim. Actual source harmonic sign is the corpus delta.
WP03 still needs uniform-height bounded zeta*G. Scalar sign is not equality or localization.

## Verification snapshots
Lint exits1 only seven unrelated unreachable modules:
RHTower.WeilWorkHigherDenominatorBesselBoundary,
RHTower.WeilWorkHigherDenominatorFourierBoundary,
HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation,
ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra.
No WP03-owned/prohibited-declaration error. Do not claim global green or fix unrelated scope.
Index exits0; generated formal/LEAN_API.md, LEAN_GAPS.md, LEAN_OVERVIEW.md have no Git diff.
Owned whitespace clean. Main frontier WP03 row updated to ordinary harmonic limit L<=0 and equality still open.

## Next C31 candidate, NOT proved
Given fresh corpus frontier, multiply actual source Gaussian test by
q(s)=Q(s)Q(1-s), Q(s)=1-(3/2)*2^(-s).
On critical line q=|Q|²>=0; symmetric under s->1-s, entire, bounded on strips.
q(1)=-1/8, so the SAME upper-envelope pole-sign argument, if actual weighted extraction is paid, forces reverse inequality -> Re P(1)=0.

Exact three-dilate profile:
Hq(t)=(17/8)H(t)-(3/4)H(t/4)-(3/2)H(4*t).
Exact Mellin factor:
q(s)=17/8-(3/4)*2^s-(3/2)*2^(-s).
Negative coefficients mean C30 upper bounds CANNOT simply be combined.
Must derive Hq upper bound from NEW positive boundary pairing with |Q|².

Corpus exact scaled transform checked:
ZetaLeftLineGaussianIntegrals.lean:192 integral_zetaChi_mul_LSeries
integral chi(w)L(a,1-w) r^w g_T(w) dt =
2*pi*r*sum_n(if n=0 then0 else a(n)*leftKernel T(n*r)).
Keep factor r. General Q=sum c_m m^-s:
q(s)=sum_(m,k)c_m*c_k/m*(m/k)^(1-s).
Profile=sum_(m,k)c_m*c_k/k*H((m/k)^2*t).
Mellin factor q(s) exactly.

Unpaid C31 gates: weighted canonical reflection and spectral positivity; actual contour transport and residue q(1); absolute convergence for finite positive dilates; real-frequency kernel error (do NOT claim J scales like Gaussian); exact Mellin scaling with convergence. Existing kernel pointwise near/far estimates apply to positive real y; C30 aggregate theorem specializes to integers. Can generalize proof to y>0 or derive fixed-r bound with r-dependent constant. Do paper dependency closure and kill audit first.

Do NOT conflate harmonic equality with exposed-point equality:
WeilFullConeExposedPoint.weilFullCone_exposed_at_vonMangoldt concerns atomPairing(...,riemannKernelAutocorr), a different functional.
WeilConeCriticalZeroCarriedRigidity.eq_vonMangoldt_of_boundaryMeasure_criticalZeros still needs boundary measure carried by critical zeta zeros. None supplied by scalar sign.

## Searches/external audit
C30d deep:68538 files,generation1281256, partial from reranking deadline. All candidate/source statements and ingredient sets read.
C31 deep:68550 files,generation1281376,partial=false; all20 candidate+20 source statements and proposed ingredients inspected. No shortcut; proposed regular/nonnegative/pointwise routes retain their explicit premises.
External DLMF2.5 and Miller--Schmid https://arxiv.org/html/math/0403030: classical Mellin methods with explicit convergence/growth, no arbitrary-source WP03 closure.

## Lean elaboration lessons
- integral_re is ROOT, not MeasureTheory.integral_re. Import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap.
- Rewriting RCLike.re into Complex.re may fail; exact (integral_re hi).symm.trans ... works after simp only[mellin,smul_eq_mul].
- Use explicit IntegrableOn.congr_fun h and IntegrableOn.integrable_indicator h; dot notation on h.const_mul can reduce to And and fail.
- Gamma_R continuity: typed h : ContinuousAt (fun s:complex=>(Gamma_R s)^-1)1; hi:=h.inv₀ nonzero; change ContinuousAt(fun s=>((Gamma_R s)^-1)^-1)1 at hi; simpa only[inv_inv] using hi.
- Function.comp_def may be needed in Tendsto simpa.
- Explicit Filter.Eventually.filter_mono with typed neighbourhood membership avoids failed dot inference.
- Real.norm_of_nonneg is namespaced.
- Summability .sub can pick Summable.sub on term sequences; use explicit LSeriesSummable.sub when coefficient subtraction is intended.
- Cast real absolute values as ((|(n:real)|:real):complex), otherwise complex abs/Lattice can be inferred.
- Nat.abs_cast avoids ambiguous abs_of_nonneg cast metavariables.
