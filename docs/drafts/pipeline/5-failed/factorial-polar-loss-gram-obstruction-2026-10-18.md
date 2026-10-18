# Actual factorial polar loss exceeds the Gram-error scale

- **Stage:** 5-failed: only the proposed eventual absorption `factorialPolarLoss <= factorialWeilGramError` is false. Both the obstruction and its positive survivor have dependency-closed paper proofs and verified Lean proofs.
- **Parent:** [actual ramp diagonal margin](../1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md), still in progress.
- **Scope:** quantitative obstruction to absorbing the actual polar loss into the existing mixed-Gram error. This does not retire WL/RW or prove the diagonal margin or RH.
- **Positive survivor:** sharp finite harmonic and binomial bounds, the actual normalized polar-loss limit `1/4`, the signed diagonal-pole limit `-1/2`, and `GramError/actualPolarLoss -> 0`. All 25 theorems are formalized; all 27 public declarations use only standard Lean axioms. See the [positive-result card](../3-formalized/factorial-polar-loss-asymptotic-2026-10-18.md).

## Plan

1. Audit corpus bounds and exact current definitions.
2. Prove both central-binomial doubling-ratio bounds using the exact recurrence.
3. Prove sharp harmonic bounds and the actual logarithmic polar-loss lower bound; extract and prove the exact asymptotic coefficient.
4. Compare the actual polar loss with the existing Gram error and formalize both the obstruction and positive survivor.
5. Audit every public declaration, wire completed modules, index, lint and remove the temporary dependency cache.

Write scope: `CentralBinomialRatioGrowth.lean`, `FactorialPolarLossLowerBound.lean`, `FactorialPolarLossAsymptotic.lean`, and `FactorialPolarGramScaleSeparation.lean` under `formal/GaloisForLFunctions/BiScaleUncertainty/`, plus the area umbrella, required generated indexes, this card, its positive-result card and the parent margin card. Concurrent research modules remain read-only.

## Exact paper statements

Let `N=n+1`, `f=factorialRampSource n`, `epsilon=sourceFactorialCollar N`, `H_N=harmonicCorrection N`, and `C_N=chebyshevBiNullProducer N`. Write

`P_n = integral_[0,infinity) polarDensity(x)*autocorr(f)(x)`.

The already formalized identity is `P_n=-(1+epsilon/2)*H_N*C_N/N`.

The target positive survivors are

- `log(N+1)/2 <= C_N` for every natural `N`;
- `1/4 <= H_N` for `N>=1`;
- `log(N+1)/(8N) <= |P_n|`, hence `P_n<0`, for the actual source family;
- `GramError_n/|P_n| -> 0`, hence eventually `GramError_n < |P_n|`.

The existing `O(log N/N)` upper bound and the new explicit lower bound fix the actual logarithmic scale of the polar loss. A proposed eventual bound `|P_n| <= GramError_n` is false. The coupled archimedean/logarithmic/polar estimate remains necessary.

## Dependency-closed paper proof

Put `b_N=choose(4N,2N)/choose(2N,N)^2>0`. The central-binomial recurrence `(N+1)*centralBinom(N+1)=2(2N+1)*centralBinom(N)` gives

`b_(N+1)/b_N = ((4N+1)(4N+3)(N+1))/(2(2N+1)^3)`.

For `x>=0`, let `A=(4x+1)(4x+3)(x+1)` and `B=2(2x+1)^3`. Exact expansion yields

`A^2*(x+1)-B^2*(x+2) = 160x^5+384x^4+345x^3+139x^2+23x+1 >= 0`.

Since `B>0`, the recurrence multiplier squared is at least `(N+2)/(N+1)`. Induction from `b_0=1` yields `b_N^2>=N+1`. Taking logarithms gives `C_N=log(b_N)>=log(N+1)/2`. This uses no asymptotic formula or prime-distribution assumption.

The exact harmonic-pair identity is

`H_N=4N*sum_(k=0)^(N-1) 1/((2(N+k)+1)(2(N+k)+2))`.

For `0<=k<N`, both positive factors are at most `4N`, so each summand is at least `1/(16N^2)`. There are exactly `N` terms, giving `H_N>=1/4`.

Because `epsilon>0`, the signed pole identity now gives

`|P_n| >= (1/4)*(log(N+1)/2)/N = log(N+1)/(8N) > 0`.

Let `E_n=factorialWeilMixedBound n`. The existing source proves `E_n->0` and defines `GramError_n=E_n^2/(2N)`. Thus `N*GramError_n=E_n^2/2->0`. Also `N*|P_n|>=log(2)/8>0`, since `N>=1`. Consequently

`0 <= GramError_n/|P_n| <= (8/log(2))*N*GramError_n -> 0`.

This supplies both the negative obstruction and a quantitative positive replacement. No lower bound for the full ramp diagonal is asserted.

## Sharper positive survivor: exact asymptotic coefficient

A second paper pass sharpens the survivor to `N*|P_n|/log(N+1) -> 1/4`.

For the same `A,B`, exact expansion gives

`B^2*(x+1)-A^2*x = (x+1)*(96x^4+192x^3+135x^2+39x+4) >= 0`.

Thus the squared recurrence multiplier times `N` is at most `N+1`. Induction from `b_1=3/2` gives `b_N^2 <= (9/4)*N` for `N>=1`. Together with the lower bound, this implies

`log(N+1)/2 <= C_N <= log(N)/2+log(9/4)/2`,

and hence `C_N/log(N+1) -> 1/2`.

Put `j=N+k`. The harmonic pair equals

`1/((2j+1)(2j+2)) = [2j/(2j+1)] * [1/(4j)-1/(4(j+1))]`.

For `j>=N>=1`, the bracketed prefactor lies between `2N/(2N+1)` and `1`. The remaining positive differences telescope over `j=N,...,2N-1`. Multiplication by `4N` yields the exact finite bounds

`N/(2N+1) <= H_N <= 1/2`.

In particular `H_N -> 1/2`; the former `1/4` bound is a weaker corollary. The actual collar budget gives `epsilon -> 0`. Divide the already verified identity `N*|P_n|=(1+epsilon/2)*H_N*C_N` by `log(N+1)>0` and multiply these three limits. This proves the coefficient `1/4` on paper, with no limit passage through the Weil form. Since `P_n=-|P_n|`, the signed term `2*P_n` in the actual diagonal has normalized limit `N*(2*P_n)/log(N+1) -> -1/2`.

All lower-bound, asymptotic and scale-separation statements above are now formalized. The no-go closes only the absorption shortcut; the entire WL/RW route remains active. No sign of the full ramp diagonal has been proved.

## Corpus and verification status

- `/tmp/bsu-ramp-margin-current-search.json` returned partial results: semantic deadline expired, filter worker disconnected, semantic coverage unmeasured, background refresh incomplete. Available hits included the current exact-pole identity and concurrent Müntz-tail/readout files, not the required full-form lower bound.
- `/tmp/bsu-central-binomial-ratio-search.json` returned partial results: reranking deadline expired, semantic coverage unmeasured, background refresh incomplete. Available hits were checked. Existing Wallis/asymptotic normalization bounds and the differently defined CCM ratio do not state the finite doubling-ratio inequality used here. Direct mathlib source located `Nat.succ_mul_centralBinom_succ`, `Nat.centralBinom_pos`, and `Nat.centralBinom_eq_two_mul_choose` in `Mathlib/Data/Nat/Choose/Central.lean`.
- `/tmp/bsu-polar-scale-api.lean` passed direct `lake --old env lean -j 1` verification after removing an unused nonexistent convenience name (`Filter.Eventually.not`). The completed contradiction proof uses conjunction and `Eventually.exists`.
- All four direct leaves passed with empty logs: `CentralBinomialRatioGrowth.lean` (seven public theorems), `FactorialPolarLossLowerBound.lean` (nine), `FactorialPolarLossAsymptotic.lean` (five), and `FactorialPolarGramScaleSeparation.lean` (four). The lower-bound tool result was truncated; verification recovered its terminal process, empty log and fresh object, then both dependent leaves imported that object successfully. No compiler exit code will be invented for the lost tool result. All four finished modules are now wired into the area umbrella.
- `/tmp/bsu-polar-scale-limit-api.lean` passed: `squeeze_zero` and `div_lt_iff₀` exist in this toolchain.
- The temporary copy-on-write cache at `/tmp/bsu-polar-scale-cache` contained 8,737 existing dependency objects. Four own modules used fresh normal-cache artifacts in the `--setup` maps, never preserved copies. After all compiler jobs terminated, every temporary file was validated as an owned `.olean` copy and removed; the empty cache directory was removed too. Normal-cache artifacts and all verification logs remain. The corresponding temporary setup maps must be regenerated before reuse.
- `/tmp/bsu-polar-asymptotic-api.lean` passed after qualifying `Filter.tendsto_add_atTop_nat`. The lower-bound checks isolated a single proof-shape issue in the finite telescoping sum: `ring` could not normalize reciprocal denominators, while `field_simp` then closed the goal completely. Removing the redundant trailing `ring` resolved the reported `No goals to be solved`; the recheck passed. Logs: `/tmp/bsu-polar-asymptotic-api.log`, `/tmp/bsu-FactorialPolarLossLowerBound.log`.
- The first asymptotic check reported only two redundant `ring` calls after `field_simp` had closed their identities. Both were removed and its recheck passed; the corresponding cancellation in the Gram leaf also uses `field_simp` alone. No passed unchanged leaf was rechecked.
- The first Gram check likewise reported only one redundant `ring` after `field_simp`, in the positive constant-cancellation identity. Removing it resolved the error; its recheck passed. No passed unchanged leaf was rerun.
- The final audit passed from `/tmp/biscale_polar_scale_axioms.lean`: all 27 public declarations (25 theorems, two definitions) depend only on `propext`, `Classical.choice`, and `Quot.sound`. Full output: `/tmp/bsu-polar-scale-axioms.log`.
- `scripts/formal_tools.py index` passed. Global `lint --check-generated` exited 1 on three unrelated missing umbrella imports: `MertensValuationBudget`, `RobinMovingValuationDefect`, and `StationaryResolventMarkovPositivityAndNodalDefectProducer`. None names these four modules. Full output: `/tmp/bsu-polar-scale-lint.log`; no global lint pass is claimed.
- `/tmp/bsu-polar-scale-verification.json` records all 27 axiom results, source hashes, compiler evidence, index/lint outcomes and confirmed cache removal. Final metadata checks confirmed all four source hashes, retained compiled objects and exactly one umbrella import per module. Durable source hashes are also recorded on the positive-result card.
