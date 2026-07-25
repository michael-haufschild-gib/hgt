# Gaussian smooth-AFE Mellin contour and unit residue

- **ID:** `gaussian-smooth-afe-mellin-contour-and-residue`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) `[LEAN-PROVED] [BRIDGE]`
- **Source:** Classical inverse-Mellin contour underlying the smooth approximate
  functional equation; Iwaniec--Kowalski, Theorem 5.3 method.
- **Statement:** For `G(w) = exp(w²)`, the integrands `G(w)/w` and
  `x⁻ʷG(w)/w` are absolutely integrable on every nonzero vertical line.
  Their inverse-Mellin integral is invariant among positive abscissae and
  changes by exactly one when shifted from a positive abscissa across zero
  to a negative abscissa.

## Goal

Close Gaussian cutoff's convergence, contour-deformation, removable-part,
and unit-residue interfaces required by the smooth symmetric approximate
functional equation. This card does not assert the zeta AFE itself.

## Gates

- [x] 0 → 1 in-progress: exact kernel, contour, and residue statements fixed.
- [x] 1 → 2 fully-proven: Gaussian majorants, rectangle limits, and reciprocal
  integral calculation closed without an analytic hypothesis.
- [x] 2 → 3 formalized: Lean modules compile; axiom audit and formal lint pass.
- [ ] 3 → 4 publication-ready: include in final Bourgain source crosswalk.

## Lean certificate

Core declarations:

- `RHTower.norm_smoothAFEGaussianKernel_vertical_le`
- `RHTower.smoothAFEGaussianKernel_verticalIntegrable`
- `RHTower.smoothAFEMellinIntegrand_verticalIntegrable_of_ne`
- `RHTower.smoothAFECutoffAt_eq`
- `RHTower.differentiable_smoothAFERegularPart`
- `RHTower.tendsto_integral_vertical_inv_of_pos`
- `RHTower.tendsto_integral_vertical_inv_of_neg`
- `RHTower.integral_smoothAFEMellinIntegrand_residue_crossing`
- `RHTower.smoothAFECutoffAt_sub_eq_one`
- `RHTower.smoothAFECutoffAt_eq_smoothAFECutoff_sub_one`

Modules:

- `formal/GaloisForLFunctions/RHTower/SmoothAFEGaussianKernel.lean`
- `formal/GaloisForLFunctions/RHTower/SmoothAFEGaussianNonzero.lean`
- `formal/GaloisForLFunctions/RHTower/SmoothAFEGaussianContour.lean`
- `formal/GaloisForLFunctions/RHTower/SmoothAFEGaussianResidue.lean`
- `formal/GaloisForLFunctions/RHTower/SmoothAFEGaussianReciprocalContour.lean`
- `formal/GaloisForLFunctions/RHTower/SmoothAFEGaussianResidueCrossing.lean`

Verification:

- Targeted builds pass.
- Representative `#print axioms` output is exactly
  `[propext, Classical.choice, Quot.sound]`.
- Modules are wired into `RHTower.lean`.

## Paper proof

On `w = σ + it`,
`|exp(w²)| = exp(σ²) exp(-t²)` and `|w| ≥ |σ|`; hence both
`exp(w²)/w` and `x⁻ʷexp(w²)/w` have explicit integrable Gaussian
majorants for `σ ≠ 0`. Between two positive abscissae, the integrand is
holomorphic and horizontal rectangle edges vanish like `exp(-T²)`, so the
vertical integrals agree.

For a contour crossing zero, write
`H(w) = x⁻ʷexp(w²)`. Since `H(0) = 1`,
`H(w)/w = 1/w + dslope H 0 w` away from zero; the divided difference is
entire. Its rectangle integral is zero. Direct real integration gives
`∫_{-T}^{T}(σ+it)⁻¹dt → π` for `σ>0` and `→ -π` for `σ<0`,
while both horizontal reciprocal integrals vanish. Thus positive minus
negative vertical integrals equal `2π`, and normalization by `1/(2π)`
gives the exact jump `1`.

## Scientific status

`[BRIDGE] [LEAN-PROVED] [REDISCOVERED]`. Mathematics is classical. New
corpus value is a dependency-closed Lean certificate for the exact Gaussian
Mellin contour used by the planned smooth AFE.

Remaining AFE core: justify the zeta Dirichlet-series interchange, shift
`ζ(s+w)`, apply the zeta functional equation, and control the Gamma-factor
ratio uniformly by Stirling. Bourgain's decoupling and spacing estimates
remain further downstream.

Follow-up status: `SmoothAFEZetaMellin.lean` closes the absolute-half-plane
zeta Dirichlet-series interchange by explicit `p`-series/Gaussian domination,
and `SmoothAFEZetaDirichletExpansion.lean` identifies its terms with the
canonical cutoff, giving the exact first smoothed Dirichlet series. Remaining
AFE core starts with the residue-bearing zeta contour shift.

## Log

- 2026-07-25 — Gaussian vertical convergence, positive contour invariance,
  removable principal part, reciprocal contour limits, and exact unit residue
  formalized and wired into the RHTower umbrella.
