# Actual clock growth and the cumulative lower-bound target

Owner: critical-clock product task. Status: hostile-test bridge formalized;
requested cumulative payment bound remains open.

The requested RH-bearing result is a cumulative lower bound on signed mixed
payments plus copied diagonals minus cutoff growth, along a constructed
exhaustive prime/clock path. Neither that construction nor its bound is proved.

## Hostile test [BRIDGE]

For every fixed finite prime core P, the actual first quotient cell has
strictly positive limiting quadratic mass. On that cell r>M/2, so the
previously defined finite clock energy satisfies

`W_1(P,M)/M² ≥ a_P log(M/2)` eventually, with `a_P>0`.

Consequently arbitrary cutoff schedules cannot have a common cumulative
payment bound. Given any prescribed sequence of finite prime cores (including
an exhaustive sequence) and any prescribed target heights, cutoffs can be
chosen strictly increasing, beyond every core prime, so that the actual
normalized clock energy exceeds those heights at every stage.

This does not exclude a deliberately coupled prime/clock schedule. It tests
the quantifier that would allow uncontrolled cutoff changes.

## Proved source argument

1. At quotient one the processed head equals the unit head, independently of P.
   Its square-root slope is `primeFreeDivisorDefect 1`, strictly positive by
   the established first-open-block source positivity.
2. The first block mass is exactly
   `rho_P * (primeFreeDivisorDefect 1)^2 *
       ((2/3) sqrt(1/2) - 11/24)`, a positive number.
3. The proved finite-count block limit gives eventually at least half that
   normalized mass. Monotonicity of log on r>M/2 supplies the displayed lower bound.
4. The logarithm diverges. Choosing successive cutoffs past the source
   thresholds constructs arbitrary prescribed growth, retaining the actual
   finite counting measure throughout.

The positive survivor is exact, before any limit:

`E_first(P,M) = (primeFreeDivisorDefect 1)^2 *
  sum_{r in S_P(M), M/r=1} (sqrt M - sqrt r)^2`.

The core changes only which squarefree cofactors are counted. This is an
actual source contribution that every proposed cancellation mechanism must
pay, rather than a freely chosen test profile.

## Lean audit

Module: `formal/GaloisForLFunctions/RHTower/MobiusDivisorFiniteClockCutoffGrowth.lean`.

- `mobiusDivisorFixedCoreBlockEnergy_first_eq`: exact surviving source.
- `exists_mobiusDivisorFiniteClockEnergy_log_lower`: eventual positive
  logarithmic lower bound at every finite prime core.
- `tendsto_mobiusDivisorFiniteClockEnergy_div_sq_atTop`: divergence at each core.
- `exists_mobiusDivisorFiniteClockEnergy_growing_cutoffs`: for every core
  sequence and target-height sequence, produces strictly increasing cutoffs,
  each beyond every prime in its core, attaining all prescribed heights.

All four passed `lake env lean` in scratch. `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`. Named final audit passed:
`lake build GaloisForLFunctions.RHTower.MobiusDivisorFiniteClockCutoffGrowth`.
Module wired into `RHTower.lean`; no full or umbrella build.
Index refresh passed. Global lint still fails on the same four unrelated
unreachable modules recorded in `rh-finite-clock-counting-facts.md`; no new
failure was reported. Owned Lean processes exited and both scratch Lean
files were removed. Audit logs: `/tmp/hgt-clock-growth-{proof,final-build,index,lint}.log`.

## Route interpretation

`CCMFUSuzukiMobiusDivisorAbelSubpower` already proves that every positive
power bound on the original normalized action implies RH. Thus logarithmic
loss alone is not a route obstruction. No additional RH receiver is needed.
The missing content remains a source estimate for a chosen coupled path.

Write `A_n=W_1(P_n,M_n)/M_n^2`. For a fresh-prime history, let `C_n` be
the signed mixed payment plus copied diagonal from the previous exact finite
identity, evaluated at `M_(n+1)` and divided by `M_(n+1)^2`. Let
`G_n=A(P_n,M_(n+1))-A(P_n,M_n)` be cutoff growth. The previous identity
telescopes to `sum_{n<N}(C_n-G_n)=A_0-A_N`. The new cutoff producer with
target heights `N` therefore makes these cumulative payments unbounded below
even for a prescribed exhaustive core sequence. This last telescoping
interpretation is a paper consequence, not an additional audited declaration.

**Failed target and next problem:** no lower bound was obtained along a
deliberately coupled exhaustive schedule. Local copied-square dissipation
does not pay arbitrary clock advance; the first cell supplies a positive
growth mechanism. The remaining problem is to produce a specific advancing
core/cutoff rule and control its actual signed payments across every required
integer wall. Fixed-core convergence thresholds cannot be silently made
uniform in that growing core. Another endpoint receiver would not address it.

Two new deep corpus searches completed with `partial=false`. They supplied
the existing quotient-cell limit and subpower endpoint criterion; the exact
first-cell source, log-growth deduction, and adverse schedule above were
derived and then proved in Lean. No numerical experiment was used.

The broad 2026 compensator search found Yu–Lin,
[arXiv:2603.12439](https://arxiv.org/abs/2603.12439). Its abstract assumes
stabilizability/observability before obtaining delay compensation; no such
arithmetic hypothesis is established here, and no theorem is imported.
