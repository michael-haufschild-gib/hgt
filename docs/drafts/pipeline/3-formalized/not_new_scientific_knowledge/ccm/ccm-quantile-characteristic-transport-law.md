# CCM quantile characteristic-transport law

- **ID:** ccm-quantile-characteristic-transport-law
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `CCMActualHeadOutgoingQuantileCharacteristicTransport.lean`
- **Statement:** The finite outgoing-quantile phase symbol is exactly the cosine-characteristic
  discrepancy between continuous outgoing polar mass on `[0,b_N]` and atomic prime mass at
  `log n`, coupled cellwise by equal mass; its curvature telescopes to the corresponding global
  second-moment discrepancy.

## Goal

Replace cellwise phase bookkeeping by one transported Fourier--Stieltjes source without losing the
monotone quantile coupling. This exposes transport cost and moment structure to Hilbert-space
positivity tools. It is a bridge theorem, not an RH proof.

## Gates

- [x] 0 → 1 in-progress: exact source definitions and proof route identified; corpus search found
  no aggregate characteristic-discrepancy theorem
- [x] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3 formalized: nine Lean theorems, targeted source/build/axiom audit
- [ ] 3 → 4 publication-ready: standalone proof and external novelty audit

## Theorem A — characteristic discrepancy `[PROVED HERE]`

For `b_N = ccmOutgoingPrimeQuantileBoundary N` and frequency `xi`,

`Q_N(xi) = ∫_[0,b_N] exp(h/2) cos(2*pi*h*xi) dh
  - sum_(n<N) w_n cos(2*pi*log(n)*xi)`.

This is not the ordinary same-window prime cutoff: atomic nodes retain quantile transport order and
may lie outside their polar cell. It is the characteristic discrepancy of the explicit coupling.

## Theorem B — global curvature `[PROVED HERE]`

`Q_N''(0) = 4*pi^2 * (
  sum_(n<N) w_n*(log n)^2 - ∫_[0,b_N] exp(h/2)*h^2 dh)`.

The right side is the second-moment difference of the two equal-mass finite measures.

## Theorem C — quadratic transport bound `[PROVED HERE]`

Define the literal absolute second-moment work

`A_N = sum_(n<N) ∫_[b_n,b_(n+1)] exp(h/2) * |h^2 - (log n)^2| dh`.

Then

`|Q_N(xi)| ≤ (2*pi*xi)^2/2 * A_N`.

The proof uses the new global inequality

`|cos x - cos y| ≤ |x^2-y^2|/2`,

obtained from the exact product formula for `cos x - cos y` and `|sin u| ≤ |u|`. This is stronger
at low frequency than a generic Lipschitz bound. It formalizes a useful separation: signed
second-moment work determines curvature, while absolute second-moment work controls magnitude.

## Approach

1. Use exact quantile cell mass to split each profile into polar cosine mass minus atom cosine mass.
2. Induct over consecutive boundaries to telescope continuous cell integrals.
3. Differentiate the finite sum using already proved cell jets and telescope second moments.
4. Compare the characteristic discrepancy with `HTGeometry.QuantileCoupling` and
   `HTGeometry.QuadraticTransportCost`; import them only if a theorem uses their measure-level API.

All four steps are closed. Measure-level imports were not needed: the corpus's literal cell
coupling supports a sharper direct quadratic estimate.

## Hostile audit

- Equal mass gives `Q_N(0)=0` but no pointwise sign.
- Second-moment difference is signed and is not quadratic transport cost.
- Atomic support is indexed by transport cells, not clipped by `log n ≤ b_N`.
- Any bound must retain frequency scaling and cannot replace exact phase identity by absolute mass.

## Novelty audit

- Internal research search found general monotone-coupling and quadratic-cost theorems plus the new
  cell phase module, but no theorem identifying this CCM finite symbol with a transported
  characteristic discrepancy.
- Labels: `[BRIDGE] [INTERNAL CANDIDATE] [NOT AN RH PROOF]`.

## Lean formalization

Module: `formal/GaloisForLFunctions/RHTower/CCM/CCMActualHeadOutgoingQuantileCharacteristicTransport.lean`

- exact consecutive-cell telescope to `[0,b_N]`
- exact cell polar-minus-atom characteristic identity
- exact finite characteristic-discrepancy identity
- finite first- and second-jet derivative theorems
- exact global curvature/second-moment theorem
- global cosine square-difference inequality
- cellwise and finite quadratic transport bounds

Audit:

- `lake env lean GaloisForLFunctions/RHTower/CCM/CCMActualHeadOutgoingQuantileCharacteristicTransport.lean`
  passed
- targeted `lake build GaloisForLFunctions.RHTower.CCM.CCMActualHeadOutgoingQuantileCharacteristicTransport`
  passed; no umbrella build run
- all nine theorem axiom audits report only `propext`, `Classical.choice`, `Quot.sound`
- forbidden-token scan empty
- wired into `GaloisForLFunctions/RHTower.lean`
- `python3 scripts/formal_tools.py lint` passed after wiring

## Log

- 2026-08-21 — created directly in Stage 1 after source and corpus-absence audit.
- 2026-08-21 — Conjectures A, B, and stronger quadratic C closed in Lean; promoted to Stage 3.
