# Rigidity of ζ's archimedean datum under positivity (2026-10-03)

## Computed
- Weil form (B-spline span, hk = 0.05) with all integer weights free.
- The ζ datum deformed one direction at a time:
  - pole residue `w`;
  - archimedean scale `α`;
  - Gamma shift `Γ_ℝ(s+μ)`;
  - pole location `s = 1+τ`;
  - a joint `(μ, w)` grid.
- Two quantities:
  - the projection of the feasible set onto each deformation parameter at `q = 1` (preconditioned SDP);
  - the prime-free threshold `q*(datum) = exp(−max_λ min eig)`.
- A random sweep of 59 degree-1 and degree-2 data.

## Results
- **Pinning at `q = 1`, `L = 1.6`:**
  - `w − 1 ∈ [−3.6e-10, 3.0e-6]`;
  - `α − 1 ∈ [−2.3e-8, 6.4e-9]`.
- **Gamma shift:** `q*(μ)` has a strict local minimum, exactly 1, at `μ = 0`.
  - Slopes of `κ*`: +0.38 on the left, −0.048 on the right.
  - Values: `q*(±0.2) = 1.081 / 1.0065`, `q*(±0.01) = 1.0038 / 1.00048`.
  - `λ_c(μ)` passes smoothly through `Λ`.
- **Pole location:** maximum of `κ*` at `τ = 0`, with a kink (−0.0034 at `τ = −0.1`, −0.058 at `τ = +0.1`).
- **Residue scan:** `κ*(0, w) = 1.39532(w − 1)` for `w ∈ [0, 1]`, exactly linear.
  - The no-pole extremal certificate is ζ-null, by the spectral gap below 14.13.
- **Sweep:** `q* < 1` for large shifts with a pole (`μ = 3`: 0.91; `μ = 2`: 0.965; `μ = 1`: 0.998).
  - ζ is not a global minimum. The level set `q* = 1` is a hypersurface, touched by ζ with a kink.

## Interpretation
- ζ's datum is a vertex of the positivity region: every deformation except increasing the conductor destroys positivity at `q = 1`, with linear (kink) cost.
- The kink comes from the null face of ζ-null prime-blind certificates being rich in every direction, the same mechanism as weight pinning.
- No global "conductor ≥ 1" law holds.
