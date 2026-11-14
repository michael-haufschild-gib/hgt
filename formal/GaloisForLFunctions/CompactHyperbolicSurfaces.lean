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
import GaloisForLFunctions.CompactHyperbolicSurfaces.HyperbolicElements
import GaloisForLFunctions.CompactHyperbolicSurfaces.CongruenceTraceGap
import GaloisForLFunctions.CompactHyperbolicSurfaces.Centralizers
import GaloisForLFunctions.CompactHyperbolicSurfaces.ClassOrbitalIntegrals
import GaloisForLFunctions.CompactHyperbolicSurfaces.DiffKernelDiagonal
import GaloisForLFunctions.CompactHyperbolicSurfaces.TraceFormula
import GaloisForLFunctions.CompactHyperbolicSurfaces.PrimitiveClasses
import GaloisForLFunctions.CompactHyperbolicSurfaces.LengthSeries
import GaloisForLFunctions.CompactHyperbolicSurfaces.SelbergEulerProduct
import GaloisForLFunctions.CompactHyperbolicSurfaces.SpectralProduct
import GaloisForLFunctions.CompactHyperbolicSurfaces.PsiSeries
import GaloisForLFunctions.CompactHyperbolicSurfaces.SelbergZeta
import GaloisForLFunctions.CompactHyperbolicSurfaces.QuaternionWalls
import GaloisForLFunctions.CompactHyperbolicSurfaces.WallCrossing
import GaloisForLFunctions.CompactHyperbolicSurfaces.DirichletEnergy
import GaloisForLFunctions.CompactHyperbolicSurfaces.CyclicCovers
import GaloisForLFunctions.CompactHyperbolicSurfaces.SmallEigenvalueZeta
import GaloisForLFunctions.CompactHyperbolicSurfaces.BergmanKernel
import GaloisForLFunctions.CompactHyperbolicSurfaces.BergmanProjection
import GaloisForLFunctions.CompactHyperbolicSurfaces.AreaIntegrality
import GaloisForLFunctions.CompactHyperbolicSurfaces.EntireSelbergZeta

/-!
# Compact hyperbolic surfaces

Spectral theory of `Γ\ℍ` for a cocompact group acting freely, built from the resolvent kernels
alone: the Abel calculus of the point-pair kernels `k_s`, the resolvent identity, the compact
self-adjoint operators `T_s` on `L²(F)`, their common eigenbasis with spectral parameters `λ_j ≥ 0`,
and Mercer's theorem for `T_a − T_b`, giving `Σ_j ν_j = ∫_F K(z, z) dz`.

An explicit example: the congruence subgroups `Γ(N)`, `N ≥ 3`, of the norm-one units of the order
`ℤ⟨1, i, j, ij⟩` in the division algebra `(2, 3)_ℚ` are cocompact and act freely
(`isCocompactFree_congGroup`), so `Γ(N)\ℍ` is a `CompactQuotient`.

The trace formula, the Selberg zeta function (Euler product, holomorphy on `Re s > 0`, functional
equation, zeros at `λ_j + s(s − 1) = 0`), and a surface with an eigenvalue in `(0, ¼)`: walls of the
quaternion order give `χ : Γ(5) → ℤ` with `χ(η) = −2`, and the cyclic covers `ker(χ mod n)` carry
the test functions `e^{2πiθ/n}`.

Bergman projections give the integrality of the area: the weight-`2(j+2)` projection has trace
`(2j + 3)|F|/4π + O(j q^j)`, a natural number, so `|F| = 2πN` (`exists_nat_volume_F_eq`), and the
Selberg zeta function continues to an entire function (`entireZeta`,
`exists_selbergZeta_small_eigenvalue`).
-/
