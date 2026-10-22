# Leg structured midpoint-equilibrium universality law

Status: exact `lake env lean` audit passed; final module/lint/axiom audit pending.

## Lean sources

- `cothField_root_exists`
- `midpoint_push_of_deficit`

## Survivor

For a structured decreasing-gap two-train pole configuration with simple gap-edge poles, the
paired mean-value deficit budget produces a genuine equilibrium at level `-(2M+E+2)`.  That
equilibrium is necessarily to the right of the gap midpoint, equivalently its distance from the
ahead edge is less than half the gap.

This removes the hypothetical equilibrium premise from the midpoint-push theorem.

## Proof skeleton

The block hypotheses imply every non-edge pole lies outside the open gap.  Endpoint membership and
simplicity let the pole blow-up/IVT theorem construct an interior root at the Leg level.  Feed that
root into the paired-deficit midpoint theorem.

## Novelty audit

Pending post-formalization literature search.
