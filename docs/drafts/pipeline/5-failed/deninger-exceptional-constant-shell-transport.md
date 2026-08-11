# Deninger exceptional constant shell transport

- **ID:** deninger-exceptional-constant-shell-transport
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `rh-current-frontier-map.md` cross-corpus weld: completed-exponent blow-up × Gamma-six shell principal ideal × Wold clock
- **Statement:** A coordinate-independent exceptional scalar transports Gamma-six powers `lambda_n^(1-delta)` to `lambda_n^(1+delta)` for every shell grade.

## Goal
Use degree-one source blow-up covariance to identify both retained shell orientations before trace or norm scalarization. If true for each Xi divisor, neutral horizontal grade and RH follow.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `deningerGammaSix_constantScalarShellTransport_iff`; source file elaborates
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach
Compare one shell coordinate with its Wold successor. Since `lambda_(W n) = lambda_n/6`, forward and reflected powers acquire factors `(1/6)^(1-delta)` and `(1/6)^(1+delta)`. A common scalar cancels, so injectivity of real powers at base `1/6` forces `delta = 0`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** `[PROVED HERE]` For real `c, delta`,
  `forall n, c * lambda_n^(1-delta) = lambda_n^(1+delta)` iff `c = 1` and `delta = 0`. Ordinary tensoring or any degree-one coordinate-independent exceptional coefficient cannot repair an off-line shell mismatch.
- **Strongest positive survivor:** Unique coefficient-faithful diagonal carrier is exactly `d_delta(n) = lambda_n^(2*delta)`. It obeys exact Wold drift `d_delta(W n) = (1/6)^(2*delta) d_delta(n)` and is Wold-stationary iff `delta = 0`. A pointwise TFAE theorem identifies exceptional isometry, full shell transport, and cyclic physical descent.
- **New insight:** Blow-up covariance and shell selection are separated by grade dependence, not lack of a reflected carrier. Missing source law must kill Wold drift of the unique carrier. This is a sharper target than equality of two scalarized moments and explains why moment-neutral scalar/tensor amplification fails.
- **Status:** Internal corpus audit found no prior theorem with this completed-exponent/Gamma-six weld. External arXiv audit found operator/spectral RH and blow-up reflection work, but no coefficient-faithful reflected shell carrier or Wold-stationarity classification. Complete paper proof and unconditional Lean formalization: `GaloisForLFunctions.RHTower.DeningerExponentGammaSixShellTransportRigidity`.

## Log
- 2026-08-11 — C0 conjectured: exceptional degree-one scalar intertwines both shell orientations.
- 2026-08-11 — C0 failed by one Wold-step comparison; positive carrier classification C1 extracted.
- 2026-08-11 — C1 and exact constant-transport no-go proved in Lean without assumptions.
- 2026-08-11 — Source-side stationarity pivot also closed: it is exactly the pre-existing cyclic-descent obstruction, so only target-side anomaly absorption survives.
