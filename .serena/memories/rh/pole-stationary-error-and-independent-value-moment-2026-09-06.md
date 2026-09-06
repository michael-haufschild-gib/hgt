# Actual stationary pole error and independent value moment

Active RH goal remains open; never mark complete without actual mathlib RH proof/disproof. This turn completed three leaves, 26 public theorems + 8 definitions; no added axiom, oracle, numerical experiment, subagent or commit.

## Proof chain and exact new knowledge
Actual prime–Gamma pole positivity → uniform logarithmic integrated Chebyshev error at exp(T/2) → bounded actual unit-Riesz critical resolvent → mathlib RH. Previous exact criterion, odd prime-power checkpoints, common age loss and unique late even-gap minimum remain in force. The even minimum value was the live target; this turn derived exact stationarity and a genuine estimate at its location, then isolated the missing value moment.

All leaves namespace RHTower, formal/GaloisForLFunctions/RHTower/:
1. CCMRestrictedWeilPoleFirstJets (129 lines; 7 theorems, 2 definitions).
- ccmWeilPoleDiagonalSlope a s and ccmWeilPoleCrossSlope a s are explicit derivatives of the frozen chamber (not differentiating a moving floor).
- hasDerivAt_ccmWeilPoleChamberDiagonal/Cross, hasDerivAt_ccmWeilEvenPoleChamber.
- ccmWeilPrimeChamberWeight_eq_cumulatives: W=psi(X)+M1(X), X=exp(2a).
- Exact self-radius derivatives, kappa=-EulerGamma-log(2pi), EM(t)=M1(exp t)-t, L(t)=-log(1-exp(-t)):
  A'_a(a)=2kappa cosh(a)+(3-2EM(2a))exp(a)+(2a-3-2psi(X))exp(-a)+B1'(a).
  C'_a(a)=2[kappa+X-psi(X)-exp(-2a)+L(2a)-EM(2a)].
- ccmWeilEvenPole_stationary_prime_error:
  deriv(EvenChamber a)a=0 implies X-psi(X)=-A'_a(a)/2-kappa+exp(-2a)-L(2a)+EM(2a).

2. CCMRestrictedWeilPoleStationaryError (192 lines; 9 theorems, 2 definitions).
- ccmGammaPoleBoundaryLog_nonneg t>=0, ccmGammaPoleBoundaryLog_two_mul_le t>=0, ccmGammaPoleBoundaryLog_le_one t>=2.
- abs_ccmGammaPoleSelfBoundarySlope_le a ha>=2:
  |B1'(a)| <= (KB+4)exp(a), KB=2log2+pi+1.
  Proof retains positive primitives F=expa/2 integral0..2a e^-t L2t,
  G=e^-a integral0..2a e^t(Lt-L2t/2); F,G>=0, F+G=B1<=KBexpa.
  B1'=F-G+e^-a L4a+2expa(L2a-L4a/2).
- ccmWeilPoleUniformSlopeBound KJ=2|kappa|+KB+12+2(log4+5)+2(log4+4)>0.
- abs_ccmWeilPoleDiagonalSlope_le a ha>=2: |A'_a(a)|<=KJexpa using exact cancellation, |EM| bound and Chebyshev linear bound.
- ccmWeilEvenStationaryPrimeErrorBound KS=KJ/2+|kappa|+log4+7>0.
- abs_prime_error_le_of_ccmWeilEvenPole_stationary a ha hstat: |X-psi(X)|<=KS sqrtX (written expa).
- abs_prime_error_le_at_ccmWeilEvenPole_gap_minimum a b c ha hc hfree hmin:
  a>=2, c interior Ioo(a,b), no prime powers entering inside gap, actual even minimum c => same pointwise bound at c.
  Proof transfers incoming derivative using ENTIRE chamber function equality.
  No later curvature threshold needed if actual minimum supplied.
  No statement at arbitrary radii, no energy sign, boundary minima excluded.

3. CCMRestrictedWeilPoleLogMoment (172 lines; 10 theorems, 4 definitions).
- ccmWeilPolePrimeLogMoment a H=Σvisible Lambda(n)(1+1/n)log n.
- ccmWeilPoleChamberCross_eq_logMoment: Cch(a,s)=Csm(s)-2s(psiX+M1X)+H(a).
- ccmWeilEvenPole_nonneg_iff_logMoment: actual even Q>=0 iff
  H(a)>=2a(psiX+M1X)-A(a)-Csm(a). Still open arithmetic threshold!
- Auxiliary arbitrary nonnegative weights u,v,w at genuine prime powers 2,3,4:
  ccmWeilThreeAtomDiagonal=sum2weight(exps/n-e^-s).
  ccmWeilThreeAtomCross=sumweight(1+1/n)(2s-logn).
  NOT actual Mangoldt coefficients.
- ccmWeilThreeAtom_mass_classification:
  nonnegative u,v,w, total6 and reciprocal total2 iff
  ∃t∈[0,1], (u,v,w)=(2t,6(1-t),4t).
- family diagonal =4exps-12e^-s for all t;
  cross =16s-8log3-tDelta, Delta=13log2-8log3>0 by exact3^8<2^13.
- cross derivative=16 for all t. Unconditional equal_jets_different_values witness at t=1 vs0.
  IMPORTANT terminology: equal derivative profiles and entire diagonal, NOT equal jets if jet includes function value.
- ccmWeilThreeAtomCross_range_iff: ∃nonnegative triple with these masses and cross=y iff
  16s-13log2<=y<=16s-8log3. EVERY value realized, endpoints sharp.
- This closes generic derivative/mass-only recovery; does not reject actual arithmetic value control or RH.

## Documents
- formalized paper: docs/drafts/pipeline/3-formalized/weil-pole-stationary-error-and-value-moment.md (full proof, classification, sharp attainable interval, audit).
- failed shortcut: 5-failed/weil-pole-first-jet-value-recovery.md; exact positive survivor and actual-source scope.
- active: 1-in-progress/weil-pole-stationary-value.md, all mathematical/audit checkboxes finished, actual value comparison live.
- main source-sign card: 1-in-progress/weil-two-pole-compression-prime-error.md updated.
- frontier Route O paragraph “Actual stationary error and independent value moment” appended after age-loss/gap-shape paragraph; current state only.
- universal STATUS two route-independent Must/Cannot entries: locating extrema vs signs; two mass totals insufficient for weighted log value.
- RHTower.lean imports all3 immediately after CCMRestrictedWeilPoleGapShape, before ThetaTiltLogDensity. Do not umbrella-build.

## Audits/process discipline
Scratch dir /tmp/hgt-pole-stationary.HKnfTH: Jet.lean, Bounds.lean, Moment.lean passed lake env lean with cwd formal.
All3 named leaf builds passed lake --old --log-level=error build exactmodule.
Axioms.lean printed ALL34 public declarations: each exactly [propext, Classical.choice, Quot.sound].
Formal lint passed (existing large-file warnings), git diff --check passed, new card links resolve.
Research index refreshed and all4 stationary prime-error query matches retrieved.
ALL owned foreground Lean/Lake sessions finished. Final ps showed unrelated concurrent lake env lean GaloisForLFunctions/RHTower/ThetaTiltLogDensity.lean; not ours, left untouched.
Shared worktree has many other tasks' edits; don't commit, revert, or kill unrelated processes.

## Live next conjecturing directions
Need actual H lower threshold at unique even minima, not more derivative-only equivalences. Use literal Mangoldt structure, not arbitrary weight models. Stationarity supplies psiX=X+O(sqrtX), but H still depends on cumulative history. Test source inequalities for H, with boundary minima and bounded radius treated separately. A generic positivity bound may lose X loglogX scale; audit exact loss before claiming it reaches sqrtX.
Potential investigation from derived equations (not proved): stationary value normalization E-E'/2 cancels the exp(2a) polar term, possibly exposes a critical-scale log-history defect. Need exact algebra + whole-corpus search before adopting. Do not assume this supplies positivity.
Any no-go must retain strongest positive survivor. Route O not retired. Odd prime-power checkpoints and small-radius signs remain open alongside even value sign.
