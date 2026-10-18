# Uniform prime and polar budget for the actual correction tail

- **Stage:** 3-formalized
- **Routes:** WL/RW; transfer from corrected sources to the original factorial ramp.
- **Parent:** [actual diagonal margin](../1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md).
- **Predecessor:** [actual zero-side limit](factorial-muntz-zero-side-limit-2026-10-18.md).
- **Objective:** Discharge uniform prime and polar error control for the literal smoothed correction tails. Prove actual decay-class membership, identify the ordinary absolutely convergent prime sum with its Abel pairing, and bound these non-archimedean terms at scale `1/(n+1)` independently of smoothing.

## Plan

1. Completed: corpus autocorrelation decay, prime-series/Abel identification and polar-moment audit.
2. Completed: normalized-kernel envelope and actual decay-class membership.
3. Completed: absolute prime convergence, Abel identification, uniform quadratic budget and both polar branches.
4. Completed: direct leaf/axiom checks, umbrella wiring, index/lint and handoff.

## Dependency-closed paper proof

Let `T_n=G_n-r_n`, `N=n+1`, and `U_(n,k)=kappa_k*T_n`.

1. The established one-sided bound gives `|T_n(x)|<=12*exp(-3|x|/2)/sqrt(N)` globally. Its readout at `s=1/2` supplies actual integrability.
2. Each kernel is nonnegative, has mass one, and is supported in `[-1,1]`. The triangle inequality therefore gives `|U_(n,k)(x)|<=12*exp(3/2)*exp(-3|x|/2)/sqrt(N)`, uniformly in `k`. Compact convolution supplies C2 regularity and common value/derivative decay at rate one, producing actual `ExpDecayTest`. Its derivative constant may depend on `k`.
3. Set `J=integral exp(-|t|/4)` and `D=144*exp(3/2)^2*J`. The corpus autocorrelation estimate gives `|crossCorr(U,U)(y)|<=D*exp(-5|y|/4)/N`. The integral defining `J` converges by positive-rate exponential integrability.
4. The elementary bound `Lambda(j)<=sqrt(j)*(1+log j)` gives the absolute prime-atom majorant `(2D/N)*(1+log j)*j^(-5/4)`. Its series `S` converges. Consequently the ordinary prime sum converges absolutely and has absolute value at most `B/N`, where `B=2D*S`. Truncated prime pairings converge both to this ordinary sum and to the Abel pairing; uniqueness of limits identifies them without a leftover boundary term.
5. At `s=0,1`, exact convolution factorization and the kernel strip bound give readout norms at most `12*exp(1)/sqrt(N)` and `6*exp(1)/sqrt(N)`. Thus the complete doubled polar product `P_(n,k)` satisfies `|P_(n,k)|<=144*exp(1)^2/N`.
6. The actual decay-class Weil identity yields `Re W(U,U)-Arch(U)=P_(n,k)-Prime(U)`. Therefore its absolute value is at most `(B+144*exp(1)^2)/N`. For every positive epsilon, divergence of `log(n+2)` gives one threshold in `n` beyond which the sum of the absolute prime and pole terms is at most `epsilon*log(n+2)/N`, simultaneously for all `k`.

**New insight:** the repaired arithmetic tail's prime and pole costs are uniformly below the logarithmic energy scale, even for a smoothing schedule depending on `n`. No uniform derivative bound or prime-series regularization assumption remains at the actual endpoints.

**Remaining frontier:** prove the relevant archimedean lower bound for the oscillatory tail and control the mixed terms in the transfer to the original compact ramp. Its coupled diagonal margin, all-source RW positivity and RH remain open. A lower bound cannot be assumed uniform over every smoothing choice; its quantifiers must allow sufficiently fine smoothing.

## Evidence

Both leaves pass direct `lake --old env lean -j 1` checks with no errors or warnings:

- [FactorialMuntzTailSmoothing.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailSmoothing.lean): seven public theorems, two definitions. SHA256 `311a1ae439a78974ad3d58e9a6d3a201b3b4704895cf2f2c048ba8107bb17022`.
- [FactorialMuntzTailPrimePolarBudget.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailPrimePolarBudget.lean): ten public theorems, three definitions. SHA256 `a62698204369b179ef40bf2a57178ada583f37b5690c9658600ae1ab18920f5d`.

All 22 public declarations pass the `/tmp/bsu-tail-axioms.lean` audit with only `propext`, `Classical.choice`, `Quot.sound`; the same scratch check verifies the used APIs. The actual endpoint types carry no source/domain/convergence/positivity premise. Both leaves are imported exactly once by the BiScaleUncertainty umbrella. Evidence: `/tmp/bsu-tail-verification.json`, `/tmp/bsu-tail-axioms.log`.

`scripts/formal_tools.py index` passes. `lint --check-generated` reports one unrelated missing umbrella import: `GaloisForLFunctions.BezoutValuationIncidence.DiscretePrimitiveEnergyAndJordanComparison`, plus 381 file-size warnings. Generated catalogs are current at that check; no forbidden declaration or new-leaf import failure is reported. Logs: `/tmp/bsu-tail-index.log`, `/tmp/bsu-tail-lint.log`.

Predecessor source hashes matched the verified zero-side package. Corpus search: `/tmp/bsu-muntz-tail-energy-search.json`; all 20 candidate and 20 source-argument summaries inspected. Search reports `partial=false`, with background refresh incomplete and substantial compiler-pending/stale coverage; applicable source APIs were checked directly. No numerical experiments, web search, novelty audit, heartbeat increase, full build or commit. No owned Lean process or temporary build snapshot remains.
