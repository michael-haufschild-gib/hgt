# Theta-Cusp C5 Static Thin-Clock First Contact

- **ID:** CLG-TTF-C5-static-thin-clock-first-contact
- **Stage:** 5-failed
- **Status:** formally refuted
- **Failure theorem:**
  `not_forall_strictSourcePositiveThinClockCone_c5ExactCompletedSeamSlope_pos`

## Failed proposal

Use physical projective clock localization alone to force positive corrected C5 slope on every
orientation boundary state. In adapted coordinates `r=U+3B`, the relevant static cone is

`U,B,Q>0`, `gap>0`, and `5B<r<6B`.

This would have closed

`thin-clock localization`
→ `C5 first-contact positivity`
→ `global exact completed C5 orientation`
→ `direct-J seam closure`
→ `CLG/TTF or Weil positivity`
→ `RH`.

## Exact obstruction

The negative `X=100` C5 seam persists under strict perturbation. Along
`U=(5/2)ε`, `B=ε`, `Q=47/8`, sufficiently small `ε>0` gives positive coordinates, positive gap,
`5B<U+3B<6B`, and negative corrected slope. Hence pointwise thin-clock inequalities cannot be an
inward barrier.

## Positive survivor

Actual theta trajectory is not an arbitrary point of this cone. Surviving statement is the compact
physical-orbit incidence theorem: centre-anchored orbit history or a new dynamical invariant must
exclude the negative connected component of `Ω=0`. Far-tail positivity is already formalized, so
only this compact incidence burden remains.

**Lean status:** obstruction fully formalized. Survivor remains open on paper and in Lean.
