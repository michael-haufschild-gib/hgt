# Theta-cusp C5 refined projective-cone no-go

- **ID:** C5-REFINED-PROJECTIVE-CONE
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** ../1-in-progress/theta-cusp-c5-orbit-first-contact.md
- **Statement:** Refined parabolic projective clocks, scale floor, source positivity, and exact
  scale/gap reconstruction do not force nonnegative corrected completed-C5 slope.

## Goal and RH chain

Test whether corpus projective laws

`(13/32+z²/32)z < v < (33/80+z²/16)z`,
`191/10+(37/5)z² < R²`, `0<z<3/10`,

together with `U=Rv`, `B=R(z-v)/3`, `gap=R²(1-z²)`, and positive source, force corrected C5
slope nonnegative.  This premise would orient completed C5 growth, then direct fixed-action
Jacobians, compact/tail rank-four and Ptolemy assembly, CLG/TTF or Weil positivity, and RH.

## Exact no-go

Set `R=10`, `z=s`, `v=131s/320`.  Then

`U=131s/32`, `B=63s/32`, `gap=100(1-s²)`.

For every sufficiently small `s>0`, all refined clock and scale inequalities are strict, exact
reconstruction holds, and source coordinate `Q` is positive.  At `s=0` the state is exactly the
corpus's `X=100` seam, where corrected C5 slope is strictly negative.  Polynomial continuity
therefore gives a negative-slope witness inside the open refined projective chamber.

Lean theorem:
`not_forall_refinedParabolicClockCone_c5ExactCompletedSeamSlope_nonneg` in
`GaloisForLFunctions.HTGeometry.ExactCompletedC5RefinedParabolicConeNoGo`.

## No-go closure

- **Killed:** Any first-contact proof using refined projective clocks and scale floor without the
  independent physical gap cap.
- **Positive survivor:** Joint capped-refined chamber remains untested.  A viable static argument
  must couple `gap<20` to the refined scale/projective constraints; actual-orbit history is the
  other surviving mechanism.
- **Boundary:** Witness has gap near `100`, so it does not kill joint capped-refined chamber.  This
  limitation is part of theorem interpretation, not hidden in proof.

## Novelty audit

Corpus search found no theorem coupling corrected C5 slope to this refined projective chamber.
Planat--Solé (arXiv:2608.19160) proves second-level theta-kernel concavity through a lower-order
quartic cone; Salazar (arXiv:2606.31647) develops order-moment Hankel transport.  Neither states
this spatial C5 counter-ray or no-go.

## Log

- 2026-08-29 — Exact continuity counter-ray formalized; refined projective-only C5 barrier killed.
