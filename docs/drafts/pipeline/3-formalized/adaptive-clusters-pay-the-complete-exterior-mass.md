# Adaptive clusters pay the complete exterior mass

- **Stage:** 3-formalized
- **Target:** Exterior-mass control for an actual ζ cluster.
- **Claim:** For every sufficiently high zero above the cubic-logarithmic
  depth threshold, select a finite cluster and a smooth logarithmic-aperture
  camera whose complete exterior Fourier norm mass is at most `1/4`, with
  all multiplicities. The transform differs from one by at most `1/4`
  throughout the cluster. No isolation or mass premise remains.

Precisely, fix `λ>1`, `c≥0`, `L=log(T/(2π))`, and
`T≥zetaNegativeCameraHeight λ c`. Every actual zero `p` at height `T`
with `|Re p−1/2|≥exp(-cL³)` admits a finite cluster `s` containing `p`
and a smooth camera of aperture `λL/2` such that

`Σ_(ρ∉s) multρ |FT(f)(gammaOf ρ)| ≤ 1/4`.

The series is summable; the same bound holds for every finite exterior
set. On `s`, `|FT(f)(gammaOf ρ)−1|≤1/4`. The cluster is exactly the
set of zeros in a disc about `p` of radius less than `|Re p−1/2|`.

Combine `exists_zeta_camera_cluster` with `zeta_cluster_camera_explicit`.
Local exterior terms vanish exactly; all remaining terms are dominated by
the proved summable distant tail. The finite cluster lies in the disc of
radius strictly smaller than the target depth.

This assembles existing camera results into the full exterior estimate.
It is not a new significant contribution toward the 250 target. It changes
the camera and does not discharge the original fixed-profile `ClusterAt`.
The centre-dependent prime mean-square cost remains open.

Lean: `exists_zeta_cluster_with_complete_exterior_mass` in
`ZeroConfigurationGeometry/NegativeTests/CompleteExteriorMass.lean`.
Single-file `lake --old env lean` check passed; umbrella wired.
