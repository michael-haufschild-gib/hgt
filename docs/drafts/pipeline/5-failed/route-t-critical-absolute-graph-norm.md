# Route T critical absolute graph norm

- **ID:** route-t-critical-absolute-graph-norm
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/rh-current-frontier-map.md · Route T item 40
- **Statement:** The two endpoint sums
  `sum (|R_N|+|R_(N+1)|) Delta h_N exp(h_N/2)` converge.

## Goal

This single norm was intended to force both critical prime-gap energy and holomorphy of the
residual Hardy source on `Im z<1/2`, then close RH by the shifted-zeta first-order ODE.

## Gates

- [x] 0 → 1 in-progress: exact endpoint norm and RH handoff formalized
- [x] 1 → 2 fully-proven: falsity and positive survivor have dependency-closed paper proofs
- [x] 2 → 3 formalized: exact no-go and survivor pass direct `lake env lean` checks
- [ ] 3 → 4 publication-ready: final umbrella build, lint, and axiom audit pending

## Approach

Reassemble the valuation-two Euler row through `-zeta'(2s)/zeta(2s)`, continue the
higher-valuation tail to nonreal points on `Re s=1/2`, and compare the resulting critical Wold
residue with radial limits forced by endpoint domination.

## No-go closure

- **Exact killing theorem/mechanism:** `not_half_residualUpperVariation_and_primeGapCriticalEnergy`
  proves that left endpoint variation already contradicts critical mesh energy. Endpoint
  variation gives dominated radial convergence of the raw residual Hardy series. Critical energy
  gives dominated radial convergence of the mesh. Their interior ODE identity forces RH, hence an
  unconditional nontrivial zeta zero lies on `Re rho=1/2`; the critical Wold continuation has
  residue `-m(rho)` at `rho-1`, while every radially convergent term has zero residue.
- **Strongest positive survivor:**
  `exists_criticalZero_residualLowerHardyKernel_radial_residue` proves that open-half-strip
  holomorphy plus critical mesh energy forces some critical zero at which the residual Hardy
  carrier itself has exact radial residue `-m`. Mesh and holonomy have zero radial residue. Thus a
  valid Route-T boundary space must retain signed principal parts; it cannot have an absolute
  critical trace. `exists_criticalZero_residualLowerHardyKernel_radial_norm_atTop` strengthens this
  to norm divergence to `+infinity` along the same radial approach: the boundary obstruction is a
  forced quantitative blow-up.
- **New insight:** Route T has an open-wall/closed-wall dichotomy. Holomorphy on every strict
  subhalf strip is compatible with RH; absolute convergence at the closed critical wall is
  stronger than RH and impossible because it erases genuine critical zeros. Live target is
  signed/coherent or distributional boundary continuation, not stronger domination.
- **Status:** Dependency-closed Lean in
  `XiPrimeLogHigherValuationCriticalBoundary.lean`,
  `XiHeatCassiniWoldCriticalBoundaryPole.lean`, and
  `XiHeatCassiniWoldCriticalGraphNoGo.lean`. Direct checks pass. Umbrella build/lint/axiom audit
  remain final-session gates.

## Log

- 2026-08-11 — critical valuation-two continuation and critical Wold residue formalized.
- 2026-08-11 — absolute graph norm falsified; exact residual radial-pole survivor formalized.
- 2026-08-11 — residual radial-pole survivor strengthened to norm divergence at the critical wall.
