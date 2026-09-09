# HB: exact optical source boundary caps

Status: four closed Lean theorems. The finite optical current transport is proved on paper; complete physical extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The [source-polynomial boundary calculation](../1-in-progress/hb-optical-source-boundary-matching.md) keeps the physical spin-two operator angular and transfers only the two original source polynomials. Its four radial rows have powers `(m,n)=(1,1),(1,3),(3,1),(3,3)`. Their interface differences and source-edge values are short radial integrals. The new module proves their actual integral formulas, smoothness and vanishing jets; it does not assume those jets vanish.

Module: `GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOpticalBoundaryCaps`.
Namespace: `RHTower.D4BMOpticalBoundaryCaps`.

- `cap_integral`: for optical time `L>2` and either sign of cap length `-1<x<1`, the explicit primitive equals `∫_0^x y^m(y+c-x)^n/(L+y)^6 dy`.
- `cap_flat_jet`: every derivative of order less than `m+1` of that primitive vanishes at zero, for every real target endpoint `c`.
- `interface_cap_flat_jet`: the reflected interface cap, with `c=-1` and argument `-x`, has the same vanishing jets.
- `cap_joint_smooth`: the cap is jointly smooth in optical time and cap length at every `(L,0)` with `L>2`.

The proof reuses `HTGeometry/IteratedDerivVanishing.lean` to turn the actual derivative factor `x^m` into vanishing primitive jets. The moving target factor is retained in the four explicit moment combinations. It supplies the boundary orders needed by the source current: order one for `f13`, order one for `f31`, and order three for `f33`. Multiplication by the original smooth Mellin factors, mixed-jet matching, the assembled current traces, and the moving-domain Green formula remain the analytical steps documented in the linked card. No theorem here identifies the optical cross-section functional with the complete physical flux.

Validation: final source passed `lake env lean` in scratch without warnings. Foreground `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOpticalBoundaryCaps` passed in 15 seconds against frozen existing caches: one existing own-module dependency and eleven external package caches. No existing module or umbrella was rebuilt. Only these four new public theorems were axiom-audited; each reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Installed source, `.olean` and `.ilean` were byte-compared with the audited copies. The import is wired into `GaloisForLFunctions/RHTower.lean`.

The corpus index was refreshed and `scripts/formal_tools.py lint` passed, with existing large-file warnings. No mathematical computations were run.
