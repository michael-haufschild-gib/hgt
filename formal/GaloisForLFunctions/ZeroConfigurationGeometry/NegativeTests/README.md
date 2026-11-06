# Negative cluster tests

For every `λ>1` and `c≥0`, `zetaNegativeCameraHeight λ c` is an explicit
finite starting height. At `T` above it, any ζ zero with
`|Re ρ−1/2|≥exp(−c log³(T/2π))` produces a negative diagonal Weil test
supported in `[-λL_T,λL_T]`, where `L_T=½log(T/2π)`.
The theorem allows arbitrary multiplicities and internal cluster spacings.

Consequently, positivity at fixed aperture `a` bounds every zero with
`T₀≤|Im ρ|≤2πexp(2a/λ)` by `|Re ρ−1/2|<exp(−c log³|Im ρ|)`.
Here `T₀=max(zetaNegativeCameraHeight λ (8c),(2π)²)`.
This implication uses positivity as its input and supplies no new positive aperture.

## Construction

Write `μ=λ/2`, `u=log(T/2π)`, and `B=slowExponent μ+2`.
The ζ local count gives an empty annulus of outer radius `η` and inner
radius `r=ηT⁻ᴮ` around any sufficiently deep zero, with
`max(0,log(1/η))≤(c+2+8B·zetaClusterCountConstant μ)u³`.
Multiplying the relative camera variation by `η` removes its isolation
singularity. A quartic-logarithmic spline order pays the cubic-logarithmic
isolation cost and gives absolute Fourier tail at most `1/4`.

Convolution doubles the aperture and gives one Fourier transform close to
one on the cluster, zero at all other nearby zeros. Subtract the camera
for its reflected cluster. Each local point-image is nonpositive, and one
is at most `−7/16`; the quadratic far tail is at most `(1/4+1/4)²`.
Their sum is strictly negative.

## Modules

| Module | Result |
|---|---|
| `FourierTail` | Quadratic tail bounded by squared absolute Fourier tail; opposite-value sign estimate |
| `ClusterRate` | Radius-normalized variation and quarter-error bound |
| `CubicTail` | Quartic spline order and explicit tail inequality |
| `ConvolutionCamera` | A camera pair becomes one normalized Fourier transform |
| `CubicCamera` | Explicit cluster-camera height for bounded count and mass |
| `NegativeCluster` | Local negative sign survives a small absolute tail |
| `ZetaClusters` | Actual ζ inputs and empty-annulus construction |
| `SharpLocation` | Negative tests and fixed-aperture depth bounds, at either sign of the ordinate |
| `SharpLocationHeight` | `log(T₀(λ,c)/2π) ≤ max(4/(λ−1), 7Ω log(792Ω²/(λ−1)))`, `Ω=2.2·10¹⁷(c+51395)`, `1<λ≤2`; fixed-aperture depth bound with that height |
