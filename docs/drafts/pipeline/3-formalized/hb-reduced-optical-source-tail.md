# HB: reduced source, fixed clock and rational optical primitive

Status: six closed Lean theorems. The two-sided physical current transport is analytical; complete physical extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The [two-sided source reduction](../1-in-progress/hb-two-sided-source-current-reduction.md) applies the corpus's existing angular-gradient absorption in both slots of the complete physical current. Its remaining source is a scalar coefficient times the full half-square. The earlier onset derivative supplies a fixed rational correction. The new leaf proves that coefficient, the clock identities, and the resulting radial primitive with the actual native spin-two angular field.

Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMReducedOpticalTail`.
Namespace: `RHTower.D4BMReducedOpticalTail`.

- `timeReducedCoefficient_closed`: evaluates the existing `timeReducedCoefficient` on the original source amplitude and fixed onset, retaining its first derivative. This supplies the scalar coefficient in the wave equation after the actual gradient-absorbing lift is subtracted.
- `finite_clock_contact`: proves `∫_0^b exp(-6v)chi'(v)dv=exp(-6b)chi(b)+6∫_0^b exp(-6v)chi(v)dv` for every real terminal value `b`.
- `tailClock_integral`: identifies the explicit finite transition integral plus `exp(-6)/6` with the actual half-line integral `∫_0^infinity exp(-6v)chi(v)dv`, proving its integrability.
- `tail_clock_contact`: integrates the source-onset derivative over its full transition interval and obtains exactly six times that tail clock.
- `primitive_derivative`: the constructed five-inverse-power primitive differentiates to all three rows of the reduced radial density, including the onset correction and the actual `-Delta(Delta-2)` native circle field, on either physical Xi branch.
- `density_integral`: evaluates that complete radial density between arbitrary positive endpoints by the primitive difference; interval integrability is discharged.

All parameters and endpoint domains are explicit data. No source equation, angular eigenvalue, derivative, boundary cancellation, causal admission or RH premise is supplied to these theorems. The module adds no axioms and uses no computational proof oracle.

The finite physical Green transport, its comparison with the earlier optical cross-section current, the full causal source-pairing identification, compact optical transition, terminal/cusp limits and independent SS/VV coefficients remain outside this leaf. In particular, the radial primitive's lack of a logarithmic term does not make the full action vanish: the lift's fixed physical currents remain attached. Its horizon self-current uses `∫chi² exp(-6v)`, which is not replaced by the linear-onset clock proved here.

Validation: source and clock proofs passed foreground `lake env lean` scratch checks without warnings. The final foreground `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMReducedOpticalTail` passed in 69 seconds against 3,986 frozen existing own-module caches and eleven external package caches. No existing module or umbrella was rebuilt. Only the six new public theorems were axiom-audited; each reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Installed source, `.olean` and `.ilean` were byte-compared with the audited copies. The import is wired into `GaloisForLFunctions/RHTower.lean`.

The corpus index was refreshed and `scripts/formal_tools.py lint` passed, with existing large-file warnings. Scoped whitespace checks passed. No mathematical computations were run.
