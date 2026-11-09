# Boundary energy of the Euler–FE defect

- **ID:** euler-fe-boundary-energy
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Programme:** Euler–FE transport theory; defect calculus.
- **Statement:** For an integrable, square-integrable defect `g`, its actual Hamburger
  boundary `J_g(iy)` satisfies `∫ℝ |J_g(iy)|² dy = π⁻¹ ∫ℝ |g(t)|² dt`.

## Mechanism

Euler reflection gives the kernel `z^(-1/2+2it)/sin(π/4+πit)`.
On the two imaginary rays its Mellin multipliers have squared moduli
`4/(1+exp(4πt))` and `4/(1+exp(-4πt))`, whose sum is exactly `4`.

For a nonzero `z` in the closed right half-plane, put
`f_z(t) = g(t) boundaryPairKernel(2t,z)` and
`Ψ_z(σ+iv) = ½ f_z(-v/2)`. The existing kernel bound makes `f_z ∈ L¹ ∩ L²`.
Positive dilation of the kernel and the change of variable `v=-2t` give

    J_g(yz) = MellinInv_(1/2)(Ψ_z)(y),                         y>0,
    ∫₀∞ |J_g(yz)|² dy = (1/(4π)) ∫ℝ |f_z(t)|² dt.

The second equality follows from Mellin–Plancherel: its weight at `σ=½` is `1`,
and `∫ |Ψ_z(½+iv)|² dv = ½∫ |f_z(t)|² dt`.
Take `z=i,-i`, add the two convergent integrals, and use the complementary
multiplier identity. The two boundary rays jointly preserve the entire defect energy.

## Research consequence and remaining gap

`euler-fe-finite-energy-boundary.md` formalizes the unique continuous extension to all
`L²` defects, including data outside `L¹`, with the same exact norm.
Extending the atomic-gap and origin-pairing rigidity proof still requires identification
with the actual weak Laplace boundary and an `L²` version of the tent pairings.
Neither the energy identity nor its completion proves same-depth replication or AAL.

## Lean proof

Module: `formal/GaloisForLFunctions/EulerFETransportTheory/TheBoundaryPreservesDefectEnergy.lean`.

- `closedDefectLaplace_ray_energy`: ray integrability and the exact weighted energy.
- `memLp_defectBoundary`: square-integrable full boundary.
- `integral_norm_sq_defectBoundary`: total energy equals `π⁻¹` times source energy.

Direct `lake --old env lean` check passed. All three declarations depend only on
`propext`, `Classical.choice`, and `Quot.sound`. The programme umbrella imports the module.
No classification claim for general `L²` defects follows from this theorem alone.
