# Is the de Bruijn–Newman constant Λ a period?

- **ID:** is-lambda-a-period
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Priority:** FUTURE
- **Source:** ../../door/bucket-the-no-margin.md (#85 SEED-W) · 00-status row #95
- **Statement:** Is the de Bruijn–Newman constant `Λ` (RH ⟺ `Λ = 0`; Rodgers–Tao `Λ ≥ 0`) itself a
  **period / transcendental**? Its arithmetic nature is unstudied; the field places it among the
  `{P_k(t)}`-periods — `Λ` is the **Face-A-criticality time** of the moment flow (positivity marginal,
  Face B flow-invariant).

## Goal
A bite-size, self-contained probe that ties the **no-margin constant** to the transcendence axis (A2):
if `Λ` is a period of the moment flow it sits inside the field's secular-period algebra; if it is
transcendentally fresh it is another instance of regularization-freshness
(`regularization-freshness.md`). Either outcome is a concrete data point on whether the no-margin lives
on the period or non-period side of the seam.

## Door passport
- **Door-3:** `Λ` as a value of the native moment-flow (dBN heat flow) invariant, not a renamed classical
  constant — *if* it can be expressed in the `{P_k(t)}`-period coordinates.
- **Door-2:** the arithmetic-nature question is genuinely new (`Λ`'s transcendence is unstudied), but the
  tools are classical transcendence theory — grade likely BRIDGE; the *placement* among the field's
  periods is the native content.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure (a constant of the flow, not of the zeros); attack idea
  (PSLQ probe) and Door sketch
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized
- [ ] 3 → 4  publication-ready

## Approach
A **PSLQ probe** of `Λ` (using the best rigorous numerical bounds / the Rodgers–Tao framework) against
the secular-period basis `{π, ζ(odd), γ_n, log 2π, …}` to detect (or rule out, to the available
precision) a period relation. Archive any run under `computations/`. Then a writeup placing `Λ` in the
period/non-period dichotomy. (Numerical only as a probe; the arithmetic statement is the deliverable.)

## Cross-references
- `no-margin-uniform-bound.md` — `Λ = 0` is the no-margin's dBN coordinate.
- `regularization-freshness.md` — if `Λ` is fresh, it is a regularization-freshness instance.

## Log
- 2026-06-19 — created in 0-backlog. The arithmetic nature of the dBN constant `Λ` (SEED-W); a bite-size
  PSLQ probe + writeup tying the no-margin to the transcendence axis.
