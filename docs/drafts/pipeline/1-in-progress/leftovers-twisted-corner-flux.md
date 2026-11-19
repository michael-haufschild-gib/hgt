# Corner flux of smooth modular boundary data

- **ID:** leftovers-twisted-corner-flux
- **Stage:** 1-in-progress
- **Type:** FALSIFIED ancillary estimate; explicit boundary-jet classification
- **Source:** [twisted minimum principle](../2-fully-proven/leftovers/twisted-minimum-principle.md), input (C1).
- **Statement:** Smooth boundary data do not force the Dirichlet extension's flux to vanish at the modular corner.

## Exact obstruction

Let `y₀=√3/2`, `P=(1/2,y₀)`, `k=4π` and
`W(u,y)=K₀(ky) cos(ku)`. This is an even, one-periodic,
bounded solution of `div(y∇W)=0` on the fundamental strip, smooth in an
open neighborhood of its closure at every finite height. Its trace is
admissible smooth even boundary data. Uniqueness in (C1) therefore makes
its bounded Dirichlet extension exactly `W`.

The radial normal derivative on the unit arc is

`F(u)=-k u K₀(k y(u)) sin(ku)-k y(u) K₁(k y(u)) cos(ku)`,
where `y(u)=√(1-u²)`. It extends continuously to the corner and

`F(1/2)=-4π y₀ K₁(4π y₀)<0`.

Multiplying by the positive conormal weight `y(u)`, or reversing normal
orientation, cannot make this limit zero. Hence the assertion in (C1)
that every smooth datum has flux `O(r^(1/2))` is false. Here `r` can be
Euclidean distance to `P` or any equivalent corner coordinate. The
nonzero limit is incompatible with every positive power of `r`.

## Positive survivor and exact correction

The obstruction identifies the missing boundary jet. Every finite
Whittaker sum has the exact endpoint flux

`-y₀ Σ_m a_m (2πm) K₁(2πm y₀) (-1)^m`.

Thus vanishing corner flux is a specific linear constraint on coefficients,
not a consequence of smoothness. The precise identity, its continuity,
and the single-mode strict sign will be formalized against the actual
`kMoment` Bessel integral and actual radial derivative. No assumed
Dirichlet producer is needed for these identities.

There is also a general geometric classification. For any smooth even
periodic extension, `W_u(P)=0`. Its trace derivative is
`g'(1/2)=-(1/(2y₀))W_y(P)`, whereas its radial derivative is
`F(P)=y₀W_y(P)`. Hence `F(P)=-(3/2)g'(1/2)`. Corner flux vanishes
exactly when the trace has zero endpoint derivative. Here smoothness
means ordinary smoothness on the closed arc, as for the actual growing
trace `J|A`; imposing a periodically matched trace derivative at the
glued corner would be an additional boundary-jet restriction.

For the main potential construction the appropriate regular remainder is
`J-D_(J|A)`, which has zero boundary trace. The homogeneous corner law
(C3), rather than the false flux statement for `D_g` itself, gives its
`O(r^(1/2))` flux. This preserves the intended main theorem. Proving the
global Dirichlet/ Martin producers, the homogeneous corner expansion,
Green regularization and uniqueness remains part of the full programme.

## Lean formalization

`formal/GaloisForLFunctions/RHTower/WhittakerCornerFlux.lean`, namespace `RHTower.ModularCorner`,
wired into `RHTower.lean`; standard axioms only.

| Claim | Declarations |
|---|---|
| Modes are smooth, even, 1-periodic, bounded on the strip, and solve div(y∇W) = 0 | `contDiffOn_cosineMode`, `cosineMode_even`, `cosineMode_periodic`, `cosineMode_modular_strip_bound`, `cosineMode_axisymmetric_equation` |
| Corner jet law F(P) = −(3/2) g′(1/2) for every differentiable even periodic W | `corner_radial_deriv_eq_trace_deriv` |
| Exact finite-mode corner flux; vanishing iff the trace slope vanishes | `cosineArcFlux_corner`, `cosineArcFlux_corner_eq_slope`, `sum_cosineArcFlux_corner_eq_slope`, `sum_cosineArcFlux_corner_eq_zero_iff` |
| The mode k = 4π has flux −4πy₀K₁(4πy₀) < 0 at the corner, continuous there | `cosineArcFlux_second_corner_neg`, `continuousAt_cosineArcFlux_corner` |
| The flux is not O(r^{1/2}) at the corner | `not_isBigO_cosineArcFlux_corner_sqrt_distance`, `not_isBigO_cosineMode_corner_radial_deriv` |

The corrected main-construction statement (homogeneous corner law (C3) for `J − D_g`) belongs to
the open primal-construction items on the twisted-minimum-principle card.
