# Mass-shifted arcsine-centered source-wall nonintegrability

- **ID:** mass-shifted-centered-wall-nonintegrability
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3, (9.3.820)
- **Statement:** Positive finite strict-frontier contact residue forces literal and arcsine-centered source quotients outside local `L¹`; false RH creates such germs cofinally.

## Goal

Determine whether frontier contact itself supplies nonintegrable arithmetic source needed for
global contradiction.

## Gates

- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven
- [x] 2 → 3 formalized: `XiShiftedArcsineCenteredSourceWallNonintegrability.lean`, targeted build green, standard-axiom audit
- [ ] 3 → 4 publication-ready

## Approach

Convert positive order-`d` residue to `u⁻¹` lower bound and use exact arcsine-centering contact
invariance.

## No-go closure

- **Exact killing theorem/mechanism:** pole-free arcsine-vacuum completed source charge remains finite and positive; quotient pole comes from collapsing norm.
- **Strongest positive survivor:** exact local `L¹` classification of every positive finite-order quotient germ, cofinally under false RH.
- **New insight:** closing singularity must live in pole-free producer or independent quotient admission, not quotient formation alone.
- **Status:** paper and Lean proofs dependency-closed; route novelty unverified.

## Log

- 2026-08-13 — formalized generic residue nonintegrability and cofinal centered-wall consequence; classified quotient route as no-go.
