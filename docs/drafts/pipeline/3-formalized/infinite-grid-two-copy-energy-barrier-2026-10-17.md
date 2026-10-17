# Infinite-grid two-copy energy barrier

- **ID:** infinite-grid-two-copy-energy-barrier-2026-10-17
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `../1-in-progress/infinite-grid-tail-rigidity-2026-10-17.md`
- **Statement:** Preserving the canonical distant logarithmic sample forces normalized Levy
  energy at least `exp(-1/2) T/4` for both base and copy, whenever `T>D+1`.

## Exact domain and conclusion

For a compact C² real source with positive origin energy and correlation support radius `D`,
let `g(u)=f(u)-a f(u-T)`, with `a!=0` and `T>D+1`. If
`h_g(log(ceil(exp T)))=0`, then `J(f)/h_f(0)` and `J(g)/h_g(0)` are both at least
`exp(-1/2)T/4`. Canonical polar copies are included. Sources and coefficients may vary.
The Lean endpoint proves the division-free statement, covers zero energy, and derives `D`.

## Mechanism and positive survivor

The logarithmic node has displacement `0<=delta<=exp(-T)` from the copy center.
Its exact sample is `-a h_f(delta)`. A zero therefore forces a complete translation-square
defect at that shrinking displacement. Integrating the chord inequality gives
`(R-h(delta)) integral_delta^b w <= 4 integral_0^b (R-h(x))w(x) dx`.
This exposes the logarithmic energy cost and rules out bounded-energy single-copy escape.
For fixed compact continuous sources, the rescaled canonical polar sample tends to `-R`.

## Gates and evidence

- [x] Dependency-closed paper proof: `docs/reports/BiScaleUncertainty/InfiniteGridTailRigidity.md`.
- [x] Exact Lean leaves: `InfiniteGridTailRigidity.lean`, `LogarithmicIncrementEnergy.lean`.
- [x] Direct `lake --old env lean` audits passed; 22 scratch axiom audits use only standard logic.
- [x] Umbrella imports and generated API verified.
- [ ] Publication novelty audit: not claimed; classical parent inequalities acknowledged.

Global lint currently fails on three concurrent modules missing umbrella imports, unrelated
to these leaves. See the paper for names and logs. No full or umbrella build was run.

## Limits and counting

One significant package, including helper lemmas and the error-sensitive sample law.
General polar tails, multiple-copy interference, optimal constants, and the remaining
99-contribution target are unfinished. No claim that infinite-grid polar infima have a premium.
