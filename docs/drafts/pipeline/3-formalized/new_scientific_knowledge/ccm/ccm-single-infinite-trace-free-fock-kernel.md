# Single infinite trace-free Fock kernel for matched CCM packets

Status: formalized unconditionally in
`GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedPhaseInfiniteFockKernel`.

## New knowledge

Finite trace-free Fock tomography does not require a cofinal matrix limit.  For arbitrary label
type `ι`, complex scalar extension of

`exp ⟪feature a, feature b⟫`

is one `IsPSDKernel` on the infinite augmented label space containing both tomography anchors and
all arithmetic atoms.  Proof uses two corpus mechanisms that had not previously been welded here:

1. real PSD matrices remain PSD after complexification, by splitting every complex coefficient
   vector into independent real and imaginary quadratic energies;
2. `HTGeometry.isPSDKernel_of_forall_posSemidef` promotes positivity of every finite restriction to
   the finitely-supported energy definition of an infinite PSD kernel.

Specializing labels to `ℕ` gives one global kernel.  Every finite matched CCM source symbol, and
therefore every finite actual matched prime-polar block, is an exact nonlinear reporter of a
restriction of this same kernel.  No compatible Cholesky choices, common cutoff, compactness,
uniform tail, or projective inverse limit is involved.

## Principal theorems

- `realMatrix_posSemidef_map_complex`
- `ccmActualHeadMatchedPhaseInfiniteFockKernel_isPSDKernel`
- `ccmActualHeadMatchedPhaseGlobalFockKernel_isPSDKernel`
- `ccmActualHeadMatchedPhaseGlobalFockReporter_eq_orientedPhaseSymbol_re`
- `ccmActualHeadMatchedPrimePolarFiniteBlock_eq_globalPhaseFockKernel`

## Frontier changed

Positive-carrier assembly is closed.  Kernel positivity alone still does not control signed
logarithmic anchor readouts under spectral integration.  Next conjecture replaces the external
three-term anchor reporter by a projective ratio internal to one higher-dimensional Fock kernel:
an arithmetic feature `(w, C-w, S)` paired with opposite rotating probes
`±(cos θ, cos θ, sin θ)`.  Half the logarithm of their kernel-entry ratio is exactly the intact
oriented CCM source.  This would reinterpret source as a multiplicative positive-kernel cocycle,
not an arbitrary signed linear functional.

No RH claim is made by this card.
