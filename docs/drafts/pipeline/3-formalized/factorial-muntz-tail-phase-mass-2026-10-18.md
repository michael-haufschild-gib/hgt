# Exact arithmetic phase cells and correction-tail mass

- **Stage:** 3-formalized
- **Routes:** WL/RW; logarithmic archimedean tail energy and compact-ramp transfer.
- **Parent:** [actual diagonal margin](../1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md).
- **Predecessor:** [tail prime/polar budget](factorial-muntz-tail-prime-polar-budget-2026-10-18.md).
- **Objective:** Prove an unconditional lower bound of order `1/(n+1)` for the actual correction tail's squared L2 mass, using exact repeated arithmetic phase cells. Transfer a positive fraction of that bound to sufficiently fine actual smoothings. This supplies the mass side of the missing logarithmic archimedean estimate; low-frequency control and mixed terms remain separate mathematical obligations.

## Plan

1. Completed: exact lattice formula and corpus energy audit.
2. Completed: actual collar bound and repeated arithmetic-zero cells.
3. Completed: exact disjoint-cell integrals, fixed-window L2 lower bound and smoothing transfer.
4. Completed: direct leaves, API/axiom audit, umbrella wiring, index/lint and handoff.

## Dependency-closed paper proof

Put `N=n+1`, `epsilon=sourceFactorialCollar N`, `y=N/exp(x)`. The exact cubic collar identity implies `N*epsilon<=1/12`. On `y=j+u`, `N<=j<2N`, `0<=u<=1/16`, one has `epsilon*y<=1/6`. For each `d=1,2,4`, the scaled clamped sum has exactly `d*j` unit samples and all later samples vanish: `d*y*(1+epsilon)<=d*j+1`. Thus the three sums are `4j,2j,j`, and their signed combination is zero. This direct counting proof includes integer endpoints. The actual corrected tail is therefore `exp(x/2)/(2*sqrt(N))` throughout those cells.

There are `N` disjoint logarithmic cells between `-log(2)` and zero. Their exact squared-tail integrals are `1/4*(1/j-1/(j+1/16))`, each at least `1/(256*N^2)`. Summing proves mass at least `1/(256*N)` already inside that fixed window. Normalized smoothing returns almost everywhere. Its uniform exponential square envelope supplies dominated convergence of the complete squared-mass integral, retaining eventually at least `1/(512*N)` for each fixed `n`. Combining with the predecessor gives `|Re W(U,U)-Arch(U)| <= 512*(B+144*exp(1)^2)*integral U^2` for sufficiently fine smoothing. The constant is independent of `n`; the required smoothing threshold may depend on `n`.

**New insight:** an explicit positive fraction of normalized tail mass persists on a fixed logarithmic interval. The proof uses exact sample counts and exact integrals, with all source and convergence hypotheses discharged at the actual endpoints. Frequency suppression, logarithmic archimedean growth, mixed terms, the original compact-ramp margin and RH remain open.

## Evidence

Both leaves pass direct `lake --old env lean -j 1` checks without errors or warnings, and are imported exactly once by the BiScaleUncertainty umbrella:

- [FactorialMuntzTailPhaseCells.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailPhaseCells.lean): six public theorems and one definition. SHA256 `868a0b72a7dc0ca2b424af13f3d4f3565cbf6deb3635edf61187c089ec1068c9`.
- [FactorialMuntzTailMass.lean](../../../../formal/GaloisForLFunctions/BiScaleUncertainty/FactorialMuntzTailMass.lean): eleven public theorems. SHA256 `810e6f1953bddd0cbab112581e4a7e645019f91fdc8ac58dfcf776258a63ce67`.

The arithmetic-zero theorem is stronger than planned: no lower bound on `j` is needed; that bound enters only the negative logarithmic cell geometry. Full API and all 18 public-declaration axiom checks pass in `/tmp/bsu-tail-mass-axioms.lean`, using only `propext`, `Classical.choice`, `Quot.sound`. Final source hashes were rechecked unchanged. Evidence: `/tmp/bsu-tail-mass-verification.json`, `/tmp/bsu-tail-mass-leaf.log`, `/tmp/bsu-tail-mass-axioms.log`.

`scripts/formal_tools.py index` passes. `lint --check-generated` reports one unrelated missing umbrella import: `GaloisForLFunctions.RHTower.GammaThetaFullSupportCreation`, plus 381 file-size warnings. Generated catalogs are current at that check; no new-leaf import failure or forbidden declaration is reported. Logs: `/tmp/bsu-tail-mass-index.log`, `/tmp/bsu-tail-mass-lint.log`.

Predecessor hashes match the verified package. Corpus search `/tmp/bsu-tail-arch-search.json` completed; all candidate and source-argument summaries inspected. `partial=false`, refresh incomplete because the background indexer is running, with substantial compiler-pending/stale coverage. Relevant source APIs were checked directly. No numerical experiments, web search, novelty audit, heartbeat increase, full build or commit. All owned process handles are terminal; no temporary build snapshot was created.

Next source lead: `RHTower.ExposingRayPrimitive.logarithmic_mass_ratio_bound` in `WeilWorkExposingRayPrimitiveSharpness.lean` bounds archimedean energy using the Fourier-mass / weighted-primitive-mass ratio, for compact C2 sources. The new fixed-window lower bound supplies localized physical mass. Actual primitive suppression and the compact localization/domain bridge remain to be proved; neither is inferred here.

A concrete next conjecture comes from the already exact quadratic remainder `R(y)={y}(1-{y})/2`. The cubic `Q(r)=r^2/4-r^3/6-r/12` has equal endpoint values and derivative `R(r)-1/12`; its periodic extension could provide a bounded primitive of each difference `R(a*(1+epsilon)*y)-R(a*y)`. Integration by parts against the actual Mellin weight would then aim at a tail readout bound `C*(1+|tau|)/N^(3/2)` on the critical line. Such a bound would control the weighted primitive mass with denominator `(tau^2+1/4)^2` at scale `N^(-3)`, while this card supplies source mass at scale `N^(-1)`. This cancellation estimate and every associated analytic exchange remain conjectural, not prerequisites silently imported into this card's theorems.
