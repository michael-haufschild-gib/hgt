# Actual tail archimedean growth

- **Stage:** 3-formalized
- **Routes:** WL/RW; actual correction-tail Weil energy and original ramp transfer.
- **Parent:** [actual diagonal margin](../1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md).
- **Predecessor:** [primitive suppression](../3-formalized/factorial-muntz-tail-primitive-suppression-2026-10-18.md).
- **Objective:** Finish the three drafted leaves: remove the compact-support obstacle for the actual smoothed tails, derive logarithmic archimedean growth from their verified primitive-energy and source-mass bounds, then combine the literal prime/polar budget to obtain an actual Weil-energy lower bound. The user cleared the RH goal; this completion task ends after verification and handoff.

## Completed scope

1. Established noncompact Fourier-square integrability, convergence of truncated Fourier mass, exact Parseval normalization, and gamma-weighted integrability for every `ExpDecayTest`.
2. Proved the spectral quarter estimate for the actual smoothed tails, with every analytic obligation discharged.
3. Used `b=log(N)/2`, primitive budget `C/N^3`, and physical mass lower `1/(512*N)` to obtain logarithmic growth.
4. Transferred through the actual zero/arch budget, verified all three leaves and public declarations, wired imports, refreshed the index, and ran the formal gate. The unrelated global reachability failures are recorded below.

## Initial evidence

Previous turn was verified progress: four leaves and all 29 public declarations passed. Current hashes of the predecessor readout, primitive-energy, source-mass, and prime/polar-budget leaves match that evidence. The compact theorem `RHTower.ExposingRayPrimitive.quarter_bound` uses compact support to obtain three integrability claims; its core is the unconditional pointwise `exposing_archimedean_scalar_quarter` inequality. This package proves the noncompact analytic prerequisites and applies that scalar inequality directly to the actual tails.

Corpus search `/tmp/bsu-tail-arch-search.json` completed with `partial=false`, no reported errors. All 20 candidate and 20 source-argument summaries were inspected. Compiler coverage remains a mixed snapshot (generation 1451196; refresh incomplete because background indexing is active), so these are source leads rather than an exhaustive compiler-fresh audit.

`WeilConeXiDivisibleBlindTest.lean` supplies pointwise Fourier convergence, uniform `M/(1+|r|)` bounds for compact truncations, autocorrelation convergence, and archimedean/pole convergence for `ExpDecayTest`. The new bridge uses these endpoints and dominated convergence. All three new leaves passed direct Lean with no diagnostics; every public declaration passed its axiom audit.

The user cleared the persistent RH goal and explicitly requested completion of work already started. These three leaves are complete. Stop after this handoff; do not automatically resume RH research or start a further branch.

## Dependency-closed paper mechanism

Write `m=integral U^2`, `M=integral |FT(U)|^2=2*pi*m`, `P=integral |FT(U)|^2/(r^2+1/4)^2`, and `A=(1/(2*pi))*integral |FT(U)|^2*gammaBracket`. The actual exponential test supplies all three integrability conditions. Integrating the existing scalar quarter estimate yields

`(b-coercivityConst+1/4)*m <= A + exp(b)^4/(8*pi)*P`.

Set `b=log(N)/2`, so `exp(b)^4=N^2`. The predecessor gives `P<=C/N^3` for every smoothing index, while `m>=1/(512*N)` eventually in smoothing index for fixed `n`. Therefore

`(log(N)/2-coercivityConst-64*C/pi)*m <= A`.

The verified actual prime/polar mass budget gives `|Re(W)-A|<=K*m`, with fixed `K=512*(primeBudget+144*exp(1)^2)`. Thus `Re(W)>=(log(N)/2-D)*m` with explicit constant `D=coercivityConst+64*C/pi+K`. In particular, every fixed multiple of source mass is eventually dominated by actual tail Weil energy, with smoothing threshold allowed to depend on `n`. The original ramp mixed terms are still separate obligations.

## Formal endpoints

- [ExpDecayFourierMass.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/ExpDecayFourierMass.lean): six theorems establishing the analytic bridge for `ExpDecayTest`.
- [FactorialMuntzTailArchimedeanGrowth.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailArchimedeanGrowth.lean): two definitions and four theorems specializing Parseval and gamma integrability, integrating the scalar quarter bound, and proving `(log(N)/2-ArchLoss)*m <= A` eventually in `k` for each `n`.
- [FactorialMuntzTailWeilGrowth.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailWeilGrowth.lean): one definition and four theorems giving the actual Weil lower bound, domination of every fixed multiple of mass, the literal bound `log(N)/(2048*N) <= Re(W(U,U))`, and strict positivity eventually in `n` and then `k`.

The constant is `C=32*(360*exp(1))^2*pi` and `D=coercivityConst+64*C/pi+512*(primeBudget+144*exp(1)^2)`. The last two eventual statements allow the threshold in `k` to depend on `n`. No compact-support premise, RH premise, or all-source Weil-positivity premise remains in these actual-tail endpoints.

## Verification and formal gate

- Three direct checks used `lake --old env lean -j 1`, emitted dependency oleans, and exited 0 with empty logs: `/tmp/bsu-exp-decay-fourier-mass-leaf.log`, `/tmp/bsu-tail-arch-growth-leaf.log`, `/tmp/bsu-tail-weil-growth-leaf.log`.
- Combined API scratch and all 17 public axiom audits (14 theorems, three definitions) exited 0. Every declaration uses only `propext`, `Classical.choice`, and `Quot.sound`. Audit source and output: `/tmp/bsu-tail-arch-axioms.lean` and `/tmp/bsu-tail-arch-axioms.log`.
- Each new module is imported exactly once by `GaloisForLFunctions/BiScaleUncertainty.lean`. Final source hashes and exhaustive declaration inventory are recorded in `/tmp/bsu-tail-arch-verification.json`.
- `scripts/formal_tools.py index` exited 0 and refreshed generated API/gap/overview files and the search index. Log: `/tmp/bsu-tail-arch-index.log`.
- `scripts/formal_tools.py lint --check-generated` exited 1. Its six errors concern unrelated concurrent modules unreachable from their theorem-area umbrellas: `BiScaleUncertainty.ThreePrimeScalarPhaseCollision`; `BezoutValuationIncidence.ActiveDeletedMartingaleAndShiftedEulerConvergence`; `BezoutValuationIncidence.ArithmeticLagSchedulesAndSharpRecoveryHorizon`; `BezoutValuationIncidence.RamanujanLagCoefficientAndTotientQuotient`; `BezoutValuationIncidence.TrueTranslationPredictionAndExactCompression`; `BezoutValuationIncidence.ValuationVisibilityClockAndRamanujanSupport`. The run also reports 381 existing large-file warnings. No error names a module in this package; no forbidden declaration or generated-file freshness error was reported. Log: `/tmp/bsu-tail-arch-lint.log`.

## Remaining mathematical boundary

This package completes the noncompact domain bridge and actual correction-tail logarithmic Weil growth. It does not control the original ramp's mixed Weil terms or prove its sufficient coupled diagonal margin. The Weil form is not known positive on all sources, so a positive-form Cauchy–Schwarz argument cannot be assumed. The parent problem, all-source RW, and RH remain unproved; they are outside the user's finish-only scope.
