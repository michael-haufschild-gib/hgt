# Route U — strict-aperture direct-limit boundary defect

- **Status:** `[FAILED—DERIVATIVE] [NO POSITIVE SALVAGE FOUND] [NO RH CLAIM]`
- **Date:** 2026-08-16

## Conjecture

Package the first-contact null state as a point in the closure but outside the algebraic union of
strict-subaperture completed form domains, with canonical inward approximants of positive energy
tending to zero.

## Verdict

The statement is true and was closed in Lean scratch, but it is a direct consequence of existing
`CCMRestrictedWeilStrictApertureClosure` plus `SuzukiFirstContactBoundaryRoughness`. It does not
advance Route U's RH-bearing open core: incoming source-specific PSD/strictness and exclusion of a
pre-wall nonzero null state remain exactly unchanged. No production module was retained or wired.

## Why retired

This is a repackaging of known closure behavior, not a new obstruction-removing theorem. The only
apparent positive survivor—the dense nonclosed direct-limit image—is already implicit in canonical
inward dilation and endpoint closure. `NO POSITIVE SALVAGE FOUND` beyond existing corpus.

## Verification record

- Rejected scratch: `/tmp/RouteUDirectLimit.lean`.
- `lake env lean /tmp/RouteUDirectLimit.lean` — PASS.
- Route map remained read-only.
- No numerical computation used.
