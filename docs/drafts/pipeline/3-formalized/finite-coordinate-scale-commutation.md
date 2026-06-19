# Finite coordinate-scale commutation

- **ID:** finite-coordinate-scale-commutation
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Priority:** FOUNDATIONAL
- **Source:** split from `../2-fully-proven/completed-base-archimedean-coordinate.md` section 3
- **Statement:** On a finite-support Bohr coordinate base, single-coordinate scalings commute with each other,
  coordinatewise scalings commute with each other, and a single-coordinate scaling commutes with a simultaneous
  coordinatewise scaling.

## Goal
This banks the finite torus-coordinate map algebra behind the completed-base commutation claims
`[sigma_p,sigma_q]=0` and `[sigma_infty,sigma_p]=0` on the prime-coordinate base. It does not formalize the
Gamma symbol, digamma recurrence, analytic derivation `partial_s`, the full difference-differential ring `R+`,
or the `R+` action on the archimedean symbol.

## Paper Proof
Let `x : I -> G` be a point of a commutative multiplicative coordinate torus.

For a single coordinate scaling, define

`S_p(c)(x)_r = c x_p` if `r=p`, and `x_r` otherwise.

For a coordinatewise scaling, define

`S(c)(x)_r = c_r x_r`.

For two single-coordinate scalings `S_p(c)` and `S_q(d)`, evaluate at an arbitrary coordinate `r`. If `r`
is neither updated coordinate, both composites return `x_r`. If exactly one update hits, both composites
return the same one scaled coordinate. If both updates hit the same coordinate, the two composites differ
only by the order of multiplication, `c d x_r` versus `d c x_r`, equal by commutativity.

The same coordinatewise evaluation proves `S(c) S(d) = S(d) S(c)`: at each coordinate the two values are
`c_r d_r x_r` and `d_r c_r x_r`.

Finally, `S_p(d)` commutes with `S(c)` for the same reason: away from `p`, both act as `c_r x_r`; at `p`,
the two values are `d c_p x_p` and `c_p d x_p`, equal by commutativity.

## Gates
- [x] 0 -> 1  in-progress: finite scale-commutation identities extracted from the completed-base card.
- [x] 1 -> 2  fully-proven: paper proof above by coordinate evaluation and commutativity.
- [x] 2 -> 3  formalized: Lean theorems `scaleCoordinate_commute`,
  `scaleAllCoordinates_commute`, and `scaleCoordinate_scaleAllCoordinates_commute` in
  `formal/GaloisForLFunctions/BohrGenerators.lean`; scratch `#check` / `#print axioms`, `lake build`, and
  `scripts/check_axioms.sh` pass.
- [ ] 3 -> 4  publication-ready: cite as the finite coordinate-map commutation certificate for the completed
  base.

## Log
- 2026-06-19 - Leaner split this exact finite coordinate-map lemma from
  `completed-base-archimedean-coordinate` section 3. The parent card remains in `2-fully-proven` because
  the Gamma symbol, digamma recurrence, analytic derivation, full difference-differential ring `R+`, and
  archimedean-symbol action are not fully Lean-formalized.
