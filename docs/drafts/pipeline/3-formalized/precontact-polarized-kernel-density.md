# The polarized Weil kernel has its actual endpoint density

- **ID:** precontact-polarized-kernel-density
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Wall:** Σ35; Σ75.
- **Statement:** Every complex precontact kernel entry is locally absolutely continuous, with exact two-trace density and integral reconstruction.

For the actual endpoint traces, set
`D_a(w,z)=conj(τ_L(a,z))τ_L(a,w)+conj(τ_R(a,z))τ_R(a,w)`.
Then `∂⁺_a K_a(w,z)=D_a(w,z)` at every precontact aperture. On every
compact precontact interval, `D` is integrable, `K_b−K_a=∫_a^b D`,
and the ordinary derivative equals `D` almost everywhere.

## Proof

Polarize the four finite evaluation Grams `‖E_z+cE_w‖²`,
`c∈{1,−1,i,−i}`. Their verified right derivatives and exact integral
identities polarize to the displayed density. Absolute continuity is
preserved by this finite linear combination. Differentiation of the
integral gives the ordinary derivative almost everywhere.

## Lean

Module `CanonicalSystemOfTheWindowTower/TheWeilKernelHasItsPolarizedEndpointSlope`,
namespace `CriticalHardyTheoryOfTheWindowCone`, wired into its umbrella:

- `hasDerivWithinAt_precontactKernel_right`
- `absolutelyContinuousOnInterval_precontactKernel`
- `intervalIntegrable_precontactKernelEndpointDensity`
- `integral_precontactKernelEndpointDensity`
- `ae_hasDerivAt_precontactKernel`

Final `lake --old env lean` source audit passed. All five transitive axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
No bound uniform at contact follows.
