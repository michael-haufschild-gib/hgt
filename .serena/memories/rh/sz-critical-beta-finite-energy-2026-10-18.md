# SZ critical Beta atom and finite-energy first variation — 2026-10-18

RH remains open. This is an unconditional source-kernel result, not Weil positivity.

## Certified result
Canonical leaf: formal/GaloisForLFunctions/RHTower/SuzukiCriticalBetaKernel.lean.
Formalized card: docs/drafts/pipeline/3-formalized/sz-critical-beta-finite-energy-2026-10-18.md.
Capstone: RHTower.tendsto_suzukiCriticalPrimaryPairing_firstVariation.

The literal density is B_w(t) = pi^w exp(-t/2) Re(suzukiPrimaryBetaKernel w (exp(-t))).
Its mass for 0<w<5/2 is M_w = pi^w Gamma(5/4-w/2)/Gamma(5/4+w/2).
Its regular coefficient is a_w = pi^w/Gamma(1+w), tending to 1.
For 0<w<=2 and t>0, B_w(t)/w <= a_w * 2 exp(-t/2)/(1-exp(-2t)).
Away from zero, B_w/w tends to K(t)=2 exp(-5t/2)/(1-exp(-2t)).
M'_0 = log pi - Re(digamma(5/4)).

For a real a.e. strongly measurable C on (0,infinity), |C(t)|<=C(0) a.e., and integrable (C(0)-C(t))*w_arch(t), the capstone proves
(integral C(t) B_w(t) dt - C(0))/w ->
(log pi-Re(digamma(5/4)))*C(0) - integral (C(0)-C(t))*K(t) dt,
as w->0+. Neither smoothness nor compact support nor innerness/RH is assumed.
This tracks the forming Gamma atom as well as the compensated remainder. K differs from w_arch by 2 exp(-t/2).

## Verification
Direct canonical compilation with -j 1, -o and -i passed. One informational ring suggestion; no compiler error or linter warning.
All 19 public declarations (including definitions) were audited via /tmp/hgt_sz_beta_axioms.lean.
Only [propext, Classical.choice, Quot.sound] occur.
Source SHA256: 09a74d61dd9c1dfa54a20b0ded5995d2cb1356520cd919bc3ba4c45791ff08da.
Logs: /tmp/hgt-sz-beta-final.log, /tmp/hgt-sz-beta-axioms.log.
Manifest: /tmp/hgt-sz-beta-audit-manifest.json.
RHTower umbrella wired. Index passed. Final lint --check-generated failed solely for unrelated unreachable BiScale modules FactorialMuntzBoundaryRepair, StationaryResolventMarkovPositivityAndNodalDefectProducer, TwoLagArithmeticCone. Generated files current; no own-module/forbidden-declaration error.
Logs: /tmp/hgt-sz-final-index.log, /tmp/hgt-sz-final-lint.log.
Obsolete failed proof/API scratch copies removed. All owned jobs finished.

## Larger paper result and remaining work
docs/drafts/pipeline/2-fully-proven/sz-critical-source-first-variation-2026-10-18.md contains a complete paper proof recovering the complete Weil form as the first variation of literal suzukiSourceHFinite.
Only the primary component above is formalized. The translated-cusp bound, compactly tested pole convolution, arithmetic finite sum, and full signed-source limit are NOT yet formalized here.
Paper cusp estimate: |integral B_w(t)(C(u+t)-C(u)) dt|^2 <= 2 R M_w a_w w J, uniformly in u, from Krein and weighted Cauchy-Schwarz. Full pole term contributes an explicit <=2 w M_w R A exp(A/2); retain all arithmetic coefficients through the head sum T_w(A).
Do not apply the capstone directly to translated C(u+t): its value C(u) need not dominate its absolute values. Use the separately proved Krein/weak-identity argument.
Do not claim uniform first-variation convergence on an R+J ball. No such theorem was proved.
The complete pole density grows for small w; all pole arguments must retain the compact test aperture.
No positivity or RH conclusion follows from this limit.

Internal audit: actual suzukiPrimaryBetaKernel references outside the new module occur only in its defining Mellin file and arithmetic measurability. Retrieved real-Beta asymptotics are spatial endpoint limits at fixed w. No external novelty audit/claim (user requires corpus-only).