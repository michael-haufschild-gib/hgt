import GaloisForLFunctions.CompactHyperbolicSurfaces.HorocyclicSlices
import GaloisForLFunctions.CompactHyperbolicSurfaces.CocompactGroups
import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventKernels
import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventKernelBounds
import GaloisForLFunctions.CompactHyperbolicSurfaces.ConvolutionProfiles
import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventIdentity
import GaloisForLFunctions.CompactHyperbolicSurfaces.AutomorphicKernels
import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventOperators
import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventOperatorIdentity
import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventCompactness
import GaloisForLFunctions.CompactHyperbolicSurfaces.ResolventSpectrum
import GaloisForLFunctions.CompactHyperbolicSurfaces.MercerRepresentatives
import GaloisForLFunctions.CompactHyperbolicSurfaces.MercerBound
import GaloisForLFunctions.CompactHyperbolicSurfaces.MercerTrace
import GaloisForLFunctions.CompactHyperbolicSurfaces.QuaternionOrder
import GaloisForLFunctions.CompactHyperbolicSurfaces.QuaternionGroup
import GaloisForLFunctions.CompactHyperbolicSurfaces.QuaternionCocompact

/-!
# Compact hyperbolic surfaces

Spectral theory of `Γ\ℍ` for a cocompact group acting freely, built from the resolvent kernels
alone: the Abel calculus of the point-pair kernels `k_s`, the resolvent identity, the compact
self-adjoint operators `T_s` on `L²(F)`, their common eigenbasis with spectral parameters `λ_j ≥ 0`,
and Mercer's theorem for `T_a − T_b`, giving `Σ_j ν_j = ∫_F K(z, z) dz`.

An explicit example: the congruence subgroups `Γ(N)`, `N ≥ 3`, of the norm-one units of the order
`ℤ⟨1, i, j, ij⟩` in the division algebra `(2, 3)_ℚ` are cocompact and act freely
(`isCocompactFree_congGroup`), so `Γ(N)\ℍ` is a `CompactQuotient`.
-/
