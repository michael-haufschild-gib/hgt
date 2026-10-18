# Actual tail primitive and low-frequency suppression

- **Stage:** 3-formalized
- **Routes:** WL/RW; logarithmic archimedean tail energy and compact-ramp transfer.
- **Parent:** [actual diagonal margin](../1-in-progress/factorial-ramp-diagonal-margin-2026-10-18.md).
- **Predecessor:** [exact phase-cell mass](../3-formalized/factorial-muntz-tail-phase-mass-2026-10-18.md).
- **Objective:** Derive an unconditional extra inverse power in the actual corrected-tail Fourier/Mellin readout from its exact arithmetic remainder. Discharge bounded-primitive, differentiation, integration-by-parts and endpoint obligations; propagate the bound to actual normalized smoothings and their weighted primitive energy.

## Completed work

1. Audited the existing periodic Bernoulli primitive and improper integration APIs.
2. Connected the exact clamped lattice remainder to a bounded primitive of the literal dyadic tail.
3. Integrated the actual exponential tilt by parts, retaining its endpoint, and proved the `N^(-3/2)*(1+|tau|)` readout bound and normalized smoothing version.
4. Proved weighted primitive integrability, absolute and relative mass bounds; completed direct Lean/API/axiom checks, umbrella wiring, index/lint and handoff.

## Dependency-closed paper proof

Write `N=n+1`, `epsilon=sourceFactorialCollar N`, `R(y)={y}(1-{y})/2`. The corpus already proves that `bernoulliCenteredPrimitive` is bounded by one and integrates `bernoulliPeriodic+1/12`, with `bernoulliPeriodic=-R` on positive arguments. Thus
`H_a(y)=-B(a*(1+epsilon)*y)/(a*(1+epsilon))+B(a*y)/a`
has derivative `R(a*(1+epsilon)*y)-R(a*y)` and absolute value at most `2/a`. Set `C(y)=H_4(y)/4-2*H_2(y)+4*H_1(y)`; `|C|<=12` uniformly. The exact lattice formula identifies the literal tail with its derivative after the logarithmic substitution.

For `V_n(x)=C(N*exp(-x))` and `A_n=1/(N^2*epsilon*sqrt(N))`, the exact identity on `x<=0` is
`exp((s-1/2)*x)*T_n(x)=-A_n*exp((s+2)*x)*V_n'(x)`.
Integration by parts on the negative half-line retains `V_n(0)` and gives the readout
`A_n*((s+2)*integral_(-infinity,0] exp((s+2)*x)*V_n(x) dx - V_n(0))`.
The existing lower collar budget gives `A_n<=15/(N*sqrt(N))`. For `Re(s)>-1`, the tilted tail is absolutely integrable by the predecessor bound. Boundedness of `V_n` makes the other integration-by-parts term absolutely integrable and makes the boundary at negative infinity vanish. The boundary at zero is retained. Hence the readout bound is
`180/(N*sqrt(N))*(1+norm(s+2)/(Re(s)+2))`.
For all `Re(s)>=0`, use `norm(s+2)<=Re(s)+2+|Im(s)|` to obtain `360*(1+|Im(s)|)/(N*sqrt(N))`. On the critical line this is `360*(1+|tau|)/(N*sqrt(N))`; actual normalized smoothing adds the already proved kernel factor `exp(1)`.

The elementary inequality `(1+|tau|)^2/(tau^2+1/4)^2<=32/(1+tau^2)` gives an integrable majorant. Its full-line integral is `32*pi`. Since `(N*sqrt(N))^2=N^3`, the actual smoothed weighted primitive mass is at most `C/N^3`, with `C=32*(360*exp(1))^2*pi`, uniformly in smoothing index. The predecessor proves physical squared mass at least `1/(512*N)` eventually in smoothing index for each fixed `n`; multiplying gives primitive mass at most `(512*C/N^2)` times physical squared mass.

This does not discharge compact localization for the existing logarithmic mass-ratio theorem or control mixed terms in the original ramp. The parent diagonal margin and all-source RW/RH remain open.

## Evidence

Predecessor hashes match. Search `/tmp/bsu-tail-primitive-search.json` completed (`partial=false`, no errors; compiler coverage remains a mixed snapshot while background indexing runs). `EulerDeletionRemainderFirstCoefficient.lean` and `EulerDeletionQuarticRemainder.lean` expose the bounded primitive and exact cubic; derivative API is private, so its public integral definition and FTC supply the required derivative locally without editing those files.

All four leaves passed direct `lake --old env lean -j 1` with no diagnostics. This verifies the exact remainder/Bernoulli identity, derivative through integer joins, uniform primitive bounds, actual dyadic remainder, logarithmic primitive derivative, scale estimate, improper integration by parts including both endpoints, the `360*exp(1)*(1+|tau|)/(N*sqrt(N))` Fourier bound for every actual smoothing index, weighted integrability, and the primitive-to-source mass bound. No endpoint has been dropped and no compact-support premise has been assumed.

Leaf logs: `/tmp/bsu-clamped-primitive-leaf.log`, `/tmp/bsu-tail-primitive-leaf.log`, `/tmp/bsu-tail-readout-decay-leaf.log`, and `/tmp/bsu-tail-primitive-energy-leaf.log`. Each exited 0 with empty output. Only one own Lean process ran at a time. The verified weighted energy budget is `32*(360*exp(1))^2*pi`; the verified relative bound is `512*budget/N^2` times physical squared mass, eventually in smoothing index for each fixed `n`.

All four leaves are imported exactly once by the area umbrella. The final combined API/axiom scratch exited 0. All 29 public declarations (23 theorems and six definitions) use only `propext`, `Classical.choice`, and `Quot.sound`; all API checks passed. All four predecessor source hashes still match their prior verified versions. Hashes and declaration inventory: `/tmp/bsu-tail-primitive-verification.json`; audit source: `/tmp/bsu-tail-primitive-axioms.lean`; audit log: `/tmp/bsu-tail-primitive-axioms.log`.

`scripts/formal_tools.py index` exited 0 and regenerated the three formal overview files. After the first lint found unrelated missing imports and stale generated API output, a second index exited 0 and refreshed the generated files. Final `lint --check-generated` exited 1 solely because the unrelated module `GaloisForLFunctions.BiScaleUncertainty.FiniteCoprimeMomentCalculus` is unreachable from its area umbrella. There are 381 existing size warnings, none naming these four leaves. The final generated-file check has no error. Logs: `/tmp/bsu-tail-primitive-index-final.log` and `/tmp/bsu-tail-primitive-lint.log`; first-pass lint is preserved at `/tmp/bsu-tail-primitive-lint-first.log`.

## Remaining obligations

Inspect whether the compact-support hypotheses in `RHTower.ExposingRayPrimitive.logarithmic_mass_ratio_bound` can be replaced by the integrability and Fourier identities already proved for these actual tails, or supply a justified compact approximation. No such bridge is proved here. Control the mixed terms required by the original ramp diagonal separately. Neither tail estimates nor positivity on a finite source span establish all-source RW or RH.
