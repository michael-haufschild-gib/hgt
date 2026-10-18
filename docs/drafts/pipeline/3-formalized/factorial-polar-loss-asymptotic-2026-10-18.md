# Exact factorial polar-loss scale and Gram separation

- **Stage:** 3-formalized.
- **Route:** WL/RW actual factorial ramp; [parent margin problem](../1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md) remains open.
- **Paper proof:** dependency-closed finite recurrence, telescoping and scalar-limit proof on the [failed absorption-shortcut card](../5-failed/factorial-polar-loss-gram-obstruction-2026-10-18.md).
- **Lean status:** four verified leaf modules; all 27 public declarations (25 theorems, two definitions) audited using only `propext`, `Classical.choice`, and `Quot.sound`.
- **Novelty status:** no external novelty claim or audit; corpus searches were partial, as recorded on the paper-proof card.

## Exact result

Let `N=n+1`, let `P_n` be the actual half-line integral of `polarDensity * autocorr(factorialRampSource n)`, and let `G_n=factorialWeilGramError n`.

1. For `b_N=centralBinom(2N)/centralBinom(N)^2`, `N+1 <= b_N^2` for all `N`, and `b_N^2 <= (9/4)*N` for `N>=1`. Consequently the actual binomial logarithm `C_N` satisfies `log(N+1)/2 <= C_N <= log(N)/2+log(9/4)/2` for `N>=1`.
2. The actual harmonic correction obeys `N/(2N+1) <= H_N <= 1/2` for `N>=1`, hence `H_N -> 1/2`.
3. `P_n < 0`, `|P_n| >= log(N+1)/(8N)`, and `N*|P_n|/log(N+1) -> 1/4`.
4. The signed pole contribution in the actual full diagonal has `N*(2*P_n)/log(N+1) -> -1/2`.
5. `N*G_n -> 0` and `G_n/|P_n| -> 0`. Thus eventually `G_n < |P_n|`; eventual absorption `|P_n| <= G_n` is false.

These are statements about the actual source family. The limits concern explicit scalar quantities; no limit passage through the full Weil form is used.

## Lean implementation

All files are under `formal/GaloisForLFunctions/BiScaleUncertainty/` and use namespace `GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar`.

| File | Verified contribution |
| --- | --- |
| `CentralBinomialRatioGrowth.lean` | Exact ratio recurrence and both finite growth bounds; seven theorems and one definition. |
| `FactorialPolarLossLowerBound.lean` | Sharp harmonic bounds, actual loss identity, logarithmic lower bound and strict sign; nine theorems and one definition. |
| `FactorialPolarLossAsymptotic.lean` | Five limits, including `factorialPolarLoss_normalized_tendsto_quarter` and `factorialRamp_polarContribution_normalized_tendsto`. |
| `FactorialPolarGramScaleSeparation.lean` | Four theorems, including `factorialWeilGramError_div_polarLoss_tendsto` and `not_eventually_factorialPolarLoss_le_gramError`. |

## Verification

- Direct sequential `lake --old env lean -j 1` leaf checks; all final logs are empty. No umbrella or full build, heartbeat increase, or concurrent own Lean process.
- The original lower-bound tool result was truncated. Its terminal process, empty log, fresh compiled object, successful dependent imports and complete axiom audit provide the recorded evidence; its unavailable process exit code is not fabricated.
- All 27 declarations were audited from `/tmp/biscale_polar_scale_axioms.lean`; complete output: `/tmp/bsu-polar-scale-axioms.log`.
- Four imports are wired into `formal/GaloisForLFunctions/BiScaleUncertainty.lean`. `scripts/formal_tools.py index` passed. Global `lint --check-generated` exited 1 on three unrelated missing umbrella imports: `MertensValuationBudget`, `RobinMovingValuationDefect`, and `StationaryResolventMarkovPositivityAndNodalDefectProducer`. No error names these four modules. Full output: `/tmp/bsu-polar-scale-lint.log`.
- `/tmp/bsu-polar-scale-verification.json` records complete axiom coverage, source hashes, compiler evidence, index/lint outcomes and cache cleanup. All 8,737 temporary dependency copies were removed after the compiler jobs terminated. Fresh normal-cache objects and logs remain; old temporary setup maps require regeneration before reuse.
- Final metadata checks confirmed unchanged source hashes, retained compiled objects and exactly one umbrella import per module. No global lint pass is claimed.

Source SHA-256 values at verification:

```text
CentralBinomialRatioGrowth.lean       e29d0279f4dc4c4211478e2b661b2cb2770beb9c95c764ef1719de1c6aca1b9d
FactorialPolarLossLowerBound.lean      1007532adb368d5220e913461a8ea7c682f12c0457ee4891735da22678da725b
FactorialPolarLossAsymptotic.lean      b743dd20150170569dbb11eb43652f88a5ab334c9f621cd6a2499d297519651b
FactorialPolarGramScaleSeparation.lean 3169c329a897c6b6b6946d77a2e7fe808df3f2fd446da985b7877543e5e802b5
```

## Remaining frontier

The absorption shortcut is closed. The positive result is the exact polar scale and its sharp finite bounds. The parent still requires a lower bound for the archimedean-minus-logarithmic part large enough to pay both `2*|P_n|` and the Gram error. The full diagonal margin and unconditional RH remain unproved.
