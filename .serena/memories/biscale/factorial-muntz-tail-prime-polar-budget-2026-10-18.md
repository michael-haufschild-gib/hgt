# Actual correction-tail prime and polar budget — 2026-10-18

Goal remains unconditional RH in Lean; not achieved. This goal turn completed an unconditional quantitative tail contribution on WL/RW, following `mem:biscale/factorial-muntz-zero-side-limit-2026-10-18` and `mem:biscale/factorial-muntz-smooth-weil-transfer-2026-10-18`.

## Completed artifacts

Card: `docs/drafts/pipeline/3-formalized/factorial-muntz-tail-prime-polar-budget-2026-10-18.md`. Parent `docs/drafts/pipeline/1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md` updated. Two new leaves in `formal/GaloisForLFunctions/BiScaleUncertainty`, imported exactly once by its umbrella:

- `FactorialMuntzTailSmoothing.lean`: 7 public theorems, 2 definitions. SHA256 `311a1ae439a78974ad3d58e9a6d3a201b3b4704895cf2f2c048ba8107bb17022`.
- `FactorialMuntzTailPrimePolarBudget.lean`: 10 public theorems, 3 definitions. SHA256 `a62698204369b179ef40bf2a57178ada583f37b5690c9658600ae1ab18920f5d`.

Namespace `GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar`.

## Exact contribution

Let N=n+1, T_n=`factorialMuntzCorrectedTail n`=G_n-r_n, U_(n,k)=`factorialMuntzSmoothedTail n k`, the literal real convolution of CHMDDoobGraph.mollifier k and T_n.

`factorialMuntzCorrectedTail_integrable` derives real integrability from the existing complex readout at s=1/2. `factorialMuntzCorrectedTail_exp_bound` preserves the strong global rate 3/2: |T_n(x)| <=12 exp(-3|x|/2)/sqrt(N). Kernel nonnegativity, support in [-1,1], and mass one give `factorialMuntzSmoothedTail_exp_bound`: |U(x)| <=12 exp(3/2) exp(-3|x|/2)/sqrt(N), uniformly in k. The previously formalized compact-convolution theorem supplies actual C2 and derivative decay at rate one; `factorialMuntzSmoothedTail_expDecayTest` has no unproved source/domain premise. Its derivative constant may depend on k.

`factorialMuntzSmoothedTail_readout` gives actual integrability and exact kernel-times-tail transform factorization for Re s>-1. `factorialMuntzSmoothedTail_paperFT_bound` gives the strip norm bound exp(1)*12/[sqrt(N)*(Re s+1)] for 0<=Re s<=1. `factorialMuntzTailPolarTerm` is the complete doubled product 2 Re(FT(U)(i/2)*conj FT(U)(-i/2)); `factorialMuntzTailPolarTerm_bound` proves absolute value <=144 exp(1)^2/N, keeping both poles.

Let J=integral exp(-|t|/4), D=`factorialMuntzTailCorrelationConstant`=144 exp(3/2)^2 J. Existing `RHTower.EvenSector.abs_crossCorr_le_of_decay` with b=3/2 and b1=5/4 yields `factorialMuntzSmoothedTail_crossCorr_bound`: |crossCorr(U,U)(y)| <= D exp(-5|y|/4)/N. J is integrable by positive-rate exponential integrability. The elementary unconditional Lambda growth bound then gives `factorialMuntzTailPrimeAtom_bound`: absolute ordinary prime atom <=(2D/N)*(1+log j)*j^(-5/4). Existing `summable_one_add_log_mul_rpow` proves the majorant summable; `factorialMuntzTailPrimeAtom_abs_summable` prevents relying on a default nonsummable tsum value.

`factorialMuntzTailPrimeBudget` B=2D*sum_j (1+log j)*j^(-5/4) is fixed and nonnegative. `factorialMuntzTailPrimeSum_bound` gives |ordinary prime sum|<=B/N. `factorialMuntzSmoothedTail_abelPrimePairing_eq` identifies it with the actual Abel pairing by uniqueness of the two justified truncation limits (`tendsto_atomPairing_truncTest_of_growth` and `tendsto_atomPairing_truncTest_abelPrimePairing`), including the actual von Mangoldt partial-sum bound. `factorialMuntzSmoothedTail_abelPrimePairing_bound` gives the actual B/N endpoint.

`factorialMuntzSmoothedTail_prime_polar_log_scale` (line149): for every epsilon>0, eventually n, for EVERY k, absolute prime pairing + absolute complete polar term <=epsilon*log(n+2)/(n+1). Thus the threshold permits arbitrary n-dependent smoothing schedules.

`factorialMuntzSmoothedTail_zero_arch_budget` (line172): |Re W(U,U) -(1/(2pi))*integral |paperFT U(r)|^2 gammaBracket(r)| <=(B+144 exp(1)^2)/N. Uses the actual unconditional decay-class full Weil identity. These endpoint statements have no unresolved source, convergence, positivity or RH premise.

## Verification and gate state

Both leaves passed direct `lake --old env lean -j 1 <leaf> -o ...` without errors or warnings. API probes plus all 22 public declarations passed `/tmp/bsu-tail-axioms.lean`; only propext, Classical.choice, Quot.sound. Both final source hashes rechecked unchanged. Four card links resolve. Evidence `/tmp/bsu-tail-verification.json`; axiom log `/tmp/bsu-tail-axioms.log`.

`scripts/formal_tools.py index` passed. `lint --check-generated` exited1 solely for unrelated missing umbrella import `GaloisForLFunctions.BezoutValuationIncidence.DiscretePrimitiveEnergyAndJordanComparison`, plus381 file-size warnings. Earlier unrelated six failures had been fixed by concurrent work. Generated catalogs current at this gate. Logs `/tmp/bsu-tail-index.log`, `/tmp/bsu-tail-lint.log`. No forbidden declaration or new-leaf import error. No own process or temporary build snapshot remains. No full build, heartbeat increase, numerical experiment, web search, novelty audit, commit or push. Preserve concurrent unrelated work.

Corpus search `/tmp/bsu-muntz-tail-energy-search.json`: all20 candidate and20 source-argument summaries inspected; partial=false, background refresh incomplete, substantial compiler-pending/stale coverage. Relevant APIs checked in source and actual Lean. Do not claim exhaustive compiler-fresh research coverage.

## Remaining mathematical frontier

The new result removes the non-archimedean costs of the literal tail diagonal at scale1/N. It does NOT prove the oscillatory tail's logarithmic archimedean lower bound, mixed-term control, the original compact-ramp coupled margin B_n>=2*|P_n|+factorialWeilGramError n, all-source RW positivity, or RH. The corrected family's prior uniform positivity only concerns a single zero-readout profile up to scalar. Next useful work: exploit exact clamped-lattice/Bernoulli remainder for tail archimedean energy and mixed terms. A lower bound must allow sufficiently fine smoothing; do not assume it uniformly for every k as n grows. No generic premise-wrapper or assumed energy-continuity transfer should replace this missing mathematics.
