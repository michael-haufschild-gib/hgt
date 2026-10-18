# Exact arithmetic phase cells and correction-tail mass

- **Stage:** 1-in-progress
- **Routes:** WL/RW; logarithmic archimedean tail energy and compact-ramp transfer.
- **Parent:** [actual diagonal margin](factorial-ramp-diagonal-margin-2026-10-18.md).
- **Predecessor:** [tail prime/polar budget](../3-formalized/factorial-muntz-tail-prime-polar-budget-2026-10-18.md).
- **Objective:** Prove an unconditional lower bound of order `1/(n+1)` for the actual correction tail's squared L2 mass, using exact repeated arithmetic phase cells. Transfer a positive fraction of that bound to sufficiently fine actual smoothings. This supplies the mass side of the missing logarithmic archimedean estimate; low-frequency control and mixed terms remain separate mathematical obligations.

## Plan

1. Audit the exact lattice formula and relevant corpus energy results.
2. Prove a sharp enough actual collar bound and identify repeated cells where the arithmetic completion is zero.
3. Integrate the exact positive repaired tail on disjoint cells; derive an explicit L2 lower bound and its smoothing consequence.
4. Direct Lean and axiom checks, umbrella wiring, index/lint and handoff.

## Conjectured mechanism

Put `N=n+1`, `epsilon=sourceFactorialCollar N`, `y=N/exp(x)`. The exact cubic collar identity implies `N*epsilon<=1/12`. On `y=j+u`, `N<=j<2N`, `0<=u<=1/16`, one has `epsilon*y<=1/6`. For each `d=1,2,4`, the scaled clamped sum has exactly `d*j` unit samples and all later samples vanish: `d*y*(1+epsilon)<=d*j+1`. Thus the three sums are `4j,2j,j`, and their signed combination is zero. This direct counting proof includes integer endpoints. The actual corrected tail is therefore `exp(x/2)/(2*sqrt(N))` throughout those cells.

There are `N` disjoint logarithmic cells between `-log(2)` and zero. Their exact squared-tail integrals are `1/4*(1/j-1/(j+1/16))`, each bounded below by `1/(256*N^2)`. Summing should give mass at least `1/(256*N)` already inside that fixed window. Normalized smoothing returns almost everywhere. Its uniform exponential square envelope supplies dominated convergence of the complete squared-mass integral, which should retain eventually at least `1/(512*N)`. Combining with the predecessor gives a fixed bound for the zero-side/archimedean error relative to the actual smoothed source mass.

No numerical experiment or assumed oscillatory cancellation is used. The mass claim and constants remain conjectural until checked against the literal definitions and verified in Lean.

## Evidence

Predecessor hashes match the verified package. Corpus search `/tmp/bsu-tail-arch-search.json` completed; all candidate and source-argument summaries inspected. `partial=false`, refresh incomplete because the background indexer is running, with substantial compiler-pending/stale coverage. `FactorialMuntzTailPhaseCells.lean` passes direct Lean without errors or warnings. Its arithmetic-zero theorem is stronger than planned: no lower bound on `j` is needed; the lower bound enters only the negative logarithmic cell geometry. `FactorialMuntzTailMass.lean` direct check running. Full API/axiom audit pending.

Next source lead: `RHTower.ExposingRayPrimitive.logarithmic_mass_ratio_bound` in `WeilWorkExposingRayPrimitiveSharpness.lean` bounds archimedean energy using the Fourier-mass / weighted-primitive-mass ratio, for compact C2 sources. The new fixed-window lower bound supplies localized physical mass. Actual primitive suppression and the compact localization/domain bridge remain to be proved; neither is inferred here.

A concrete next conjecture comes from the already exact quadratic remainder `R(y)={y}(1-{y})/2`. The cubic `Q(r)=r^2/4-r^3/6-r/12` has equal endpoint values and derivative `R(r)-1/12`; its periodic extension could provide a bounded primitive of each difference `R(a*(1+epsilon)*y)-R(a*y)`. Integration by parts against the actual Mellin weight would then aim at a tail readout bound `C*(1+|tau|)/N^(3/2)` on the critical line. Such a bound would control the weighted primitive mass with denominator `(tau^2+1/4)^2` at scale `N^(-3)`, while this card supplies source mass at scale `N^(-1)`. This cancellation estimate and every associated analytic exchange remain conjectural, not prerequisites silently imported into this card's theorems.
