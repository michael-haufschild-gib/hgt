# BAG independent recurrence producer checkpoint
Only task: independent coefficient-faithful quantitative recurrence producer. Goal unconditional RH remains ACTIVE/OPEN. No deterministic common-height return count, full AFE/boundary target event, or RH completion. Never mark complete.

## Workflow
One owned foreground Lean at a time. Must see write_stdin terminal exit before next Lean. Final leaf lake --old env lean Foo.lean -o matching .olean, no umbrella/full build, no heartbeat increase, no numerics, no agents, no commits. Append umbrella imports only. Public #print axioms only /tmp; expect propext, Classical.choice, Quot.sound. Audit predecessor through successor scratch, strip audit before final. Lint + exact lexical index per leaf. Unrelated unreachable files are other sessions, do not edit. Persistent BAG card/working log and frontier row authoritative.

## Current runtime (must recheck, may age)
Sole Lean F126 scratch session14923:
lake --old env lean /tmp/BagGaussianIndependentCutoffMean.lean > /tmp/bag-gaussian-independent-cutoff-mean-scratch.log 2>&1
workdir formal. Includes five F125 audits.
F125 final56782 terminal0 warning-free; index126; lint84030 terminal1 eleven unrelated modules. Card/frontier FINAL only through F124 pending F125 audits.
Search34164 pending: /tmp/bag-reflected-window-tail-source.json. Search75183 terminal0 primeCounting twice with modulePrimeWindowCount, only2cappedhits, no new ingredient used.
No other owned Lean.

## Closed
F112 actual full Gaussian cofactor mean A exp(z²)/z unconditionally.
F116 finite compatible full-mode packets on separated real-scale blocks with arbitrary mean-weighted budgets.
F119 all modes on one fixed positive-radius character cell respecting any original finite phase prescription.
F120 exact real-scale full-channel normalization.
F121 full Gaussian source energy arbitrary H*N/logN for every node direction on that cell, free window largePrimes N (N/(2K)).
F122 SteinhausFullGaussianTruncation: phase-uniform finite cofactor approximation over bounded positive real scales; coherent finite-node normalized approximation for1<=R<=U. Final97061 exit0, 3audits inF123scratch81732 standard-only. index27, lint82290 twelve unrelated. FINAL docs.
F123 SmoothAFEReflectedTruncatedGaussianTransfer: exact literal reflected channel at independent smoothing N, polynomial L = chi*p^(s_tau-1)*truncatedFullGaussianCofactor(s_fixed,N/p,L/p,logPhaseShift omega tau). Final89281 exit0, auditF124scratch93161 standard-only. index12, lint89108 thirteen unrelated. FINAL docs.
F124 SteinhausFreePrimeWindow: retain S=primesLE L minus largePrimes N Y. UnderY<=N<=L,L<Y², frozen length-L carrier = literal S-smooth background +sumfree charFactor1(eta p)*original length-L channel. General finite-S projection identifies background. Final5404 exit0, auditF125scratch10167 standard-only, index17 lint6240 eleven unrelated. FINAL docs.
F125 SteinhausTruncatedGaussianChannelEnergy: final compiled warning-free, audit PENDING currentF126.
  normalizedTruncatedGaussianCofactorChannel s R L omega = R * truncated(s,R,L)*R^-s.
  Public5: normalizedTruncatedGaussianCofactorChannel_eq_mode;
  norm_normalizedTruncatedGaussianCofactorChannel_dot_eq;
  truncatedGaussian_prime_channel_factor;
  exists_truncatedGaussianCofactor_mode_cell_blocks;
  exists_normalizedTruncatedGaussianCofactorChannel_energy_cell_lower.
  Last: fixed omega',K,B,D,delta; eventuallyN and ALL L>=N*D, everyeta in fixedcell and everyu, truncated channel energy >=H*N/logN*normu². Actual cofactor cutoffL/p>=D byp<=N. Still needs conductor transfer.

## Pending scratch drafts (no repo files)
F126 /tmp/BagGaussianIndependentCutoffMean.lean CURRENT COMPILING.
 Planned SteinhausGaussianIndependentCutoffMean.lean.
 Public3: exists_sum_norm_gaussian_direct_le gamma in(0,1): entire absolute mass C*N^(1-gamma) for ALL polynomialL andN>=1. Uses head sum_rpow_sub_one_le and existing direct tail at cutoffN, exponentA=1, total series split.
 exists_steinhausGaussianAbelSqrtCost_uniform_cutoff beta in(0,.5): C*N^(.5-beta) uniformlyL, via exact positive Abel cost and gamma=beta+.5.
 eventually_integral_norm_steinhausGaussianWeight_independent_cutoff_le: original first mean/N^(.5-beta)<=delta uniformly allL, from summatory sqrt envelope and cost. No new input assumed.

F127 /tmp/BagReflectedWindowConditionalEnergy.lean UNCOMPILED.
 Planned SmoothAFEReflectedWindowConditionalEnergy.lean.
 ImportsF125,F123,oldSmoothAFEReflectedConditionalEnergy.
 Public3: reflectedPrimalChannel_eq_normalized_truncatedGaussian (exactchi conductor andcommonunitrowphase);
 norm_reflectedPrimalWindowChannel_dot_eq_normalized;
 exists_reflectedPrimalWindowConditional_energy_cell_lower: actual H/logN Gram floor, fixedcell, all L>=N*D, fulltauwindow[5N/4,7N/4], r=1.
 Uses existing nodeScale lower. Does not imposeaffineseamL<Y² yet.

F128 /tmp/BagReflectedWindowFirstMean.lean UNCOMPILED.
 Planned SmoothAFEReflectedWindowFirstMean.lean.
 ImportsF126,oldreflectedfirstmean,F84projection.
 Public5: integral_norm_steinhausGaussianWindow_phase_eq (independentL);
 integral_norm_reflectedPrimalWindowCarrier_eq;
 eventually_integral_norm_steinhausGaussianWindow_div_rpow_le;
 eventually_integral_norm_reflectedPrimalWindowCarrier_le (uniformALL L,tau>=N,r=1);
 eventually_integral_norm_reflectedPrimalWindowSmooth_le (ANY finite retainedS).
 Exact GaussianWeight_coe_eq signature verified beta one_pos hN hn.

F129 /tmp/BagReflectedWindowChannelUpper.lean UNCOMPILED.
 Planned SmoothAFEReflectedWindowChannelUpper.lean.
 ImportsF126,F123,oldchannelupper.
 Public4: exists_truncatedFullGaussianCofactor_norm_bound (all0<R<=U,allL,allphase);
 exists_reflectedPrimalWindowChannel_upper (freewindow(N/D,N], actual channel <=C*N^-1/2 uniformly allL,tau>=N);
 exists_eventually_reflectedPrimalWindowChannel_dot_upper (allfinite nodes andcommonheightwindow);
 exists_eventually_reflectedPrimalWindowConditional_energy_upper (directional C/logN upper allL).
 Cofactor bound uses F126 absoluteGaussian mass atintegerU and monotonic V to dominateR<=U. Copied privatepcount bound fromoldmodule; rest finite-node trace adaptation.

## Strategy / quantifiers
Free primes only (Y,N], retain all otherprimes throughL, especially aboveN. At mostpi(N) freecolumns, boundedrealR=N/p<=2K. UnderL<Y² each termhasonefreeprime exponent1. Arbitrary finite-S original resampling/Jensen alreadyavailable. This avoids weightedprime-tail varianceoverprimes throughL.
Polynomialcutoff option smoothing/heightN=n²,L=n³. ThenL/p>=n forp<=n²; L<Y² eventually. FullGaussianabsolutetail beyondL is arbitrarily power-small, unlikefinitecarrierthroughN. Squarewindows only valid retaining full quantitative return COUNT (notone returnpersquare).
F126 uniform-in-L mean repairs background scaling; F129 upper controls freeenergy. Then reuse original affine-circle targetlaw/F88-F105 with arbitraryretainedS, fixedmasscell, boundedbackground.
Full AFE complementaryedge/boundary interpolation and deterministic growing-prime quantitative orbit transfer remain OPEN.

## Immediate next
1 terminalpoll F126, inspectall5F125axioms; thenF125FINAL docs evenifF126prooferrors.
2 fixF126scratch,finalleaf,wiring,lint,index; queue3auditsF127.
3 compileF127; queue3auditsF128; thenF128 andF129.
4 finite polynomial cutoff arithmetic seam and fulltail, actualtargeteventassembly; don'tclaimrecurrence.
