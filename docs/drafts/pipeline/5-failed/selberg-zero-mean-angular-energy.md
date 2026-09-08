# Zero mean does not force positive integrated angular residual

- **ID:** SELBERG-ZERO-MEAN-ANGULAR-ENERGY
- **Stage:** 5-failed — this smooth periodic shortcut only.
- **Parent:** Selberg conjecturing loop, cycle 27.
- **Full Selberg goal:** Active and unproved.

## Exact failure

For a real profile `h`, subtract the squared-amplitude radial slope:

`R_h = (h' - (h²)'/(2h²)*h)²`.

If `h` is differentiable, this residual is zero off its nodal set and equals `h'²` at its zeros. The exact cosine profile is smooth, periodic, nonzero, and has zero mean and strictly positive squared mass over one period. Its nodal set is countable, so its residual is genuinely integrable and has zero integral, although its value at `pi/2` is one. Direction reversal through zeros defeats the proposed strictly positive integrated residual.

Lean witness: `SelbergNodalAngularToy.zero_mean_does_not_force_angular_energy`, with `cosine_residual_integrable` ruling out an undefined-integral fallback. The toy is not asserted to satisfy the Maass equation, cuspidality, or modular inversion. No impossibility theorem about estimates retaining those constraints is claimed.

## Strongest positive survivor

The actual normalized finite Maass family preserves the full modular permutation action, reconstructs every original component including at common zeros, and retains its actual zero complex mean with an amplitude weight. Where density is positive, its weighted derivative energy equals the radial residual exactly.

Original nonvanishing and actual zero means force normalized directions with squared distance strictly greater than two at the same height. More precisely, amplitude times the squared distance from any fixed positive direction equals an expression in the continuous original source correlation. It therefore stays continuous through common zeros, and its mean over every level period is exactly twice the amplitude mean.

**New insight:** integrated angular derivatives can miss nodal direction reversals; the exact weighted squared-distance invariant retains them without asserting smoothness across the zeros. The actual side/inversion permutation constraints remain available for the missing core estimate.

**Paper proof and Lean audit:** [actual directions and nodal reversal](../3-formalized/selberg-source-directions-and-nodal-reversal.md). The exact source survivor is formalized in `SelbergMaassTraceDirection`, particularly `direction_equivariant`, `radialResidual_eq_direction_energy`, `source_direction_separation`, `weighted_distance_slice_continuous`, and `weighted_direction_distance_mean`. Both targeted final builds and all 35 public-declaration axiom checks passed; complete results and the unrelated repository lint failure are recorded on the linked card.
