# HB: optical source primitive and principal-cusp removal

Status: four closed Lean theorems; complete physical extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The [analytical optical-coordinate calculation](../1-in-progress/hb-optical-source-tail.md) removes the complementary complex powers from the radial variables and exposes an explicit rational/logarithmic primitive in the long-delay source pairing. These leaves formalize the exact primitive with the native circle field, and removal of the entire principal cusp field by the physical logarithmic angular channel.

`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOpticalSourceTail`, namespace `RHTower.D4BMOpticalSourceTail`:

- `sourcePrimitive_derivative`: the constructed rational/logarithmic primitive differentiates to the complete transformed radial density, with the actual native circle mean and its first two angular Laplacians.
- `sourceDensity_integral`: every positive-endpoint radial integral equals the difference of the explicit primitive's endpoint values. Integrability is discharged; no angular eigenvalue or cancellation premise is supplied.
- `sourceCoefficients_log_channel`: the two literal source coefficients multiply to `(lambda-2)(lambda-6)/64` times the actual circle field's operator `Delta²-2(4lambda+1)Delta+4lambda(4lambda+1)`.

`GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOpticalLogCusp`, namespace `RHTower.D4BMOpticalLogCusp`:

- `principalSquare_logarithmicChannel`: the actual differential operator `-Delta(Delta-2)[Delta²-2(4lambda+1)Delta+4lambda(4lambda+1)]` annihilates the literal principal half-square on every upper-half-plane point at every Xi occurrence. The proof derives its repeated Laplacians from the full three-term principal expansion, including both original Weyl coefficients and their cross term.

The full causal change of variables, odd extension of the direct/image domain, integrated current transport, compact optical transition, finite temporal remainder, and angular boundary transport remain analytical. Neither leaf proves that the remaining Fourier-remainder pairing vanishes. The next cancellation calculation is the finite differential test and its fixed first boundary primitive in equations (13)–(15) of the analytical card.

Validation: both final sources passed `lake env lean` scratch checks without warnings. Foreground exact-module final builds passed in 19 seconds and 22 seconds, using 3,946 frozen existing own-module dependencies; no existing module or umbrella was rebuilt. Only the four new public theorems were axiom-audited: each reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Installed sources and required `.olean`/`.ilean` artifacts were byte-compared with the audited copies. Both imports are wired into `GaloisForLFunctions/RHTower.lean`.
