# Explicit camera heights

Namespace `GaloisForLFunctions.ZeroConfigurationGeometry`.

`cameraPointHeight` gives polynomial isolation and multiplicity readout to error
`1/4`. `cameraMomentHeight J` gives every moment through order `J`, with error
`N r^(j+1) T^(M+κ_λ)+exp(−K′log³(T/2π))`. Both are finite expressions.

| Module | Content |
|---|---|
| `LocalZetaCount` | Sharp count from height `10`, additive constant `200`; explicit camera density bound |
| `SpectralMass` | Actual ζ Lorentzian mass `<33/100` |
| `LatticeRate` | Lattice mass `≤5`; finite relative-rate constant |
| `Heights` | Point and moment height formulas |
| `PointReadout` | Isolation, multiplicities, polynomial and reciprocal-logarithmic near-collisions |
| `MomentReadout` | Explicit normalized cluster-moment readout |
| `ClusterConsequences` | Centres, squared gaps, dipole collapse |
| `ImageConsequences` | Hankel gap, discriminant, bordered cluster-location polynomial |
| `ZetaReadout` | Actual ζ specialization at every aperture factor `λ>1/2` |

The actual ζ heights choose `θ=λ+1/2`, insert the proved count and mass bounds,
and retain the stated geometric isolation conditions. The two Hankel cluster
outputs use moment orders `2k−2` and `2k−1`; the pair gap uses order `2`.
