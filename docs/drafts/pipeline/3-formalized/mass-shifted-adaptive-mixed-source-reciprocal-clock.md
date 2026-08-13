# Mass-shifted adaptive mixed source reciprocal clock

- **ID:** mass-shifted-source-reciprocal-clock
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, (9.3.815)--(9.3.817)
- **Statement:** Reciprocal normalized flux has exact derivative equal to adaptive mixed source clock; raw clock is strictly above one, tends to two at fixed degree, and is not tail-integrable.

## Goal

Test whether nonlinear reciprocal source speed supplies missing diagonal capital; retain exact
hyperbolic propagation after proving raw finite-capital route impossible.

## Gates

- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven
- [x] 2 → 3 formalized: `XiShiftedCanonicalAdmissionAdaptiveMixedSourceReciprocalClock.lean`, targeted build green, standard-axiom audit
- [ ] 3 → 4 publication-ready

## Approach

Divide mass-normalized literal source action by squared normalized current flux.  Exact Riccati
law becomes derivative of reciprocal flux.  Then compare with fixed-degree arcsine recession.

## No-go closure

- **Exact killing theorem/mechanism:** `K_n>1` on terminal ray and `K_n(w²)→2`; raw clock cannot have finite tail capital.
- **Strongest positive survivor:** exact integral reciprocal-flux displacement and `(b-a)U_n(b)≤1`; vacuum-renormalized clock is exactly `(U_n⁻¹-2y)'`.
- **New insight:** diagonal budget must remove two forced vacuum units before any summability claim.
- **Status:** paper and Lean proofs dependency-closed; route novelty unverified.

## Log

- 2026-08-13 — formalized exact clock, hyperbolic bound, vacuum limit, and raw-clock no-go.
