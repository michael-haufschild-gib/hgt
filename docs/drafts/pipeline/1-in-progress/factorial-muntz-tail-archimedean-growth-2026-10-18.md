# Actual tail archimedean growth

- **Stage:** 1-in-progress
- **Routes:** WL/RW; actual correction-tail Weil energy and original ramp transfer.
- **Parent:** [actual diagonal margin](factorial-ramp-diagonal-margin-2026-10-18.md).
- **Predecessor:** [primitive suppression](../3-formalized/factorial-muntz-tail-primitive-suppression-2026-10-18.md).
- **Objective:** Finish the three drafted leaves: remove the compact-support obstacle for the actual smoothed tails, derive logarithmic archimedean growth from their verified primitive-energy and source-mass bounds, then combine the literal prime/polar budget to obtain an actual Weil-energy lower bound. The user cleared the RH goal; this completion task ends after verification and handoff.

## Plan

1. Audit the corpus's noncompact Fourier/Parseval and archimedean-integrability endpoints.
2. Prove a dependency-closed spectral quarter estimate for the actual smoothed tails, with every analytic obligation discharged.
3. Use the explicit parameter `b=log(N)/2`, primitive budget `C/N^3`, and physical mass lower `1/(512*N)` to obtain logarithmic growth. This may avoid optimizing a logarithmic quotient or imposing a compact approximation.
4. Transfer through the existing actual zero/arch budget, verify direct Lean/API/axiom checks, wire leaves, index/lint, and record the exact remaining ramp obstruction.

## Initial evidence

Previous turn was verified progress: four leaves and all 29 public declarations passed. Current hashes of `FactorialMuntzTailReadoutDecay.lean` and `FactorialMuntzTailPrimitiveEnergy.lean` match that evidence. The compact theorem `RHTower.ExposingRayPrimitive.quarter_bound` uses compact support to obtain three integrability claims; its core is the unconditional pointwise `exposing_archimedean_scalar_quarter` inequality. Its proof suggests direct application to actual tails once their Fourier mass, archimedean integrability, and Parseval normalization are established. No such noncompact bridge has yet been claimed.

Corpus search `/tmp/bsu-tail-arch-search.json` completed with `partial=false`, no reported errors. All 20 candidate and 20 source-argument summaries were inspected. Compiler coverage remains a mixed snapshot (generation 1451196; refresh incomplete because background indexing is active), so these are source leads rather than an exhaustive compiler-fresh audit.

`WeilConeXiDivisibleBlindTest.lean` already proves pointwise Fourier convergence, uniform `M/(1+|r|)` bounds for compact truncations, autocorrelation convergence, and archimedean/pole convergence for `ExpDecayTest`. New `ExpDecayFourierMass.lean` passed direct Lean with empty output, proving Fourier-square integrability, a dominated Fourier-mass limit, exact noncompact Parseval with factor `2*pi`, and gamma-weighted integrability. Initial API scratch passed. Drafts `FactorialMuntzTailArchimedeanGrowth.lean` and `FactorialMuntzTailWeilGrowth.lean` contain the actual archimedean and Weil lower bounds; verification is in progress.

The user cleared the persistent RH goal and explicitly requested completion of work already started. Current scope is therefore to finish and verify these three drafted leaves, complete wiring/index/lint and handoff, and stop without starting a further research branch.

## Dependency-closed paper mechanism

Write `m=integral U^2`, `M=integral |FT(U)|^2=2*pi*m`, `P=integral |FT(U)|^2/(r^2+1/4)^2`, and `A=(1/(2*pi))*integral |FT(U)|^2*gammaBracket`. The actual exponential test supplies all three integrability conditions. Integrating the existing scalar quarter estimate yields

`(b-coercivityConst+1/4)*m <= A + exp(b)^4/(8*pi)*P`.

Set `b=log(N)/2`, so `exp(b)^4=N^2`. The predecessor gives `P<=C/N^3` for every smoothing index, while `m>=1/(512*N)` eventually in smoothing index for fixed `n`. Therefore

`(log(N)/2-coercivityConst-64*C/pi)*m <= A`.

The verified actual prime/polar mass budget gives `|Re(W)-A|<=K*m`, with fixed `K=512*(primeBudget+144*exp(1)^2)`. Thus `Re(W)>=(log(N)/2-D)*m` with explicit constant `D=coercivityConst+64*C/pi+K`. In particular, every fixed multiple of source mass is eventually dominated by actual tail Weil energy, with smoothing threshold allowed to depend on `n`. The original ramp mixed terms are still separate obligations.
