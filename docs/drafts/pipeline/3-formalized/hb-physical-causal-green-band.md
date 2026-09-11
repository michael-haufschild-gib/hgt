# HB: actual physical causal response in the Green band

Stage: 3-formalized. The original full joint causal response, its physical projection, radial derivatives, trace and cleared Green identity are identified in an open part of the physical Green band. QNM-boundary continuation/current limits, full left-current orientation, fixed-clock extinction and RH remain unproved.

Chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Original full response

Let B(q)<2 be the common actual principal-kernel rate from [NativeGreenBand](hb-native-green-band.md). For every Re(w)>B(q), the already constructed `causalJointForcedResponse` has an absolutely convergent Bochner Laplace transform. It equals the original `jointEmbedding (jointWaveResponse …)` applied to the literal complete cusp-residual vector, retaining all principal cutoff channels. This transform belongs to the original unbounded operator domain and satisfies

A Û+(w²−1)Û=F̂.

No new physical response is selected. For any B(q)<c<Re(w), the actual full source-resolvent product defines a Cauchy-bounded Hilbert map shifted by c. The [full-half-plane Hilbert theorem](hilbert-half-plane-full-causal.md) inverts that map without the old extra unit shift. A common large exponential damping places this auxiliary vector and the previously constructed physical response in Bochner L². Their scalar Laplace transforms are the same original frequency response; scalar injectivity and Bochner probe totality identify the vectors almost everywhere. This transfers the smaller convergence region to the existing response.

`actualJointCausal_original_green_band` supplies the explicit nonreal point w=(B(q)+2)/2+i, with 3/2<Re(w)<2, absolute convergence and the original operator-domain equation with the literal residual source.

## Physical projection and original radial data

Inside the band, with nonzero imaginary part, the original/continued source equality identifies the actual transform with the existing complete spatial response. Its proved height admission therefore applies to the actual Bochner transform. The new `causalPhysicalProjection` is the literal physical angular map of that admitted height-weighted class. It equals `physicalCuspResponse`.

The actual causal projection has the complete physical Green representative. `causalPhysicalProjection_original_profile` gives one continuous representative, its almost-everywhere equality with the actual projection, zero Dirichlet trace, both classical radial derivatives, the full projected source equation, and

physicalAngularGapProduct(q,r)·profile=clearedPhysicalGreen(q,r).

All angular collisions remain in this identity. No angular noncollision or vanished boundary current is assumed. The radial derivatives and trace belong to the representative of the actual transformed response; no unjustified derivative interchange with its time integral is asserted.

## Formal result and next obstacle

Module: [ThetaCuspHawkingBMPhysicalCausalGreenBand.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMPhysicalCausalGreenBand.lean), namespace `RHTower.D4BMNativeLaplace`. New full-response API: `causalJointForcedResponse_integrable_of_native`, `causalJointForcedResponse_laplace_of_native`, `causalJointForcedResponse_original_green`, `causalJointForcedResponse_operator_of_native`, `actualJointCausal_original_green_band`. The physical-projection API follows these.

The exact source passed combined `lake env lean` checking and the final exact leaf build using cached dependencies. Its source and five artifacts are installed and one import is wired into `RHTower.lean`. No umbrella/full build, axiom-print check or numerical experiment ran.

The previous convergence and projected-Green transfer obstruction is closed in this open overlap. The remaining mathematical work is to continue this identified causal object to the relevant QNM boundary, control required jets and current limits there, retain collision/source-contact contributions, and assemble/orient the full Einstein and left-QNM current before fixed-clock extinction. These are not consequences of Green-band admission alone. The [working card](../1-in-progress/hb-principal-growth-energy.md) records the analytical bridge and outstanding scope. Frontier map remains read-only.

Final formal lint passed with existing large-file warnings. Module imports and local report links were verified. All owned checks completed; temporary audit and scratch files were removed. No owned Lean process remains.
