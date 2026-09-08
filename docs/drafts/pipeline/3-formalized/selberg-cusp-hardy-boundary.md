# Cusp Hardy identity with the boundary retained

- **ID:** SELBERG-CUSP-HARDY-BOUNDARY
- **Stage:** 3-formalized
- **Parent:** [Constructive Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycles 1 and 11.
- **Scope:** Actual derivatives and integrals of compact real `C¹` profiles on the positive half-line. This proves a cusp-tail inequality, not the all-congruence Selberg theorem.

## Exact identity

For such a profile `f`, cutoff `Y>0`, and arbitrary real `k`,

`integral_Y^infinity (f'^2+k^2*f^2-f^2/(4*y^2))`

`= integral_Y^infinity (f'+(k-1/(2*y))*f)^2`

`  + integral_Y^infinity (k/y)*f^2 + (k-1/(2*Y))*f(Y)^2`.

All integrands are proved integrable. The value `f(Y)` is unrestricted: the profile's support lies in the positive half-line, not necessarily strictly above the cutoff.

At `k=0`, the identity specializes to

`integral_Y^infinity (f'^2-f^2/(4*y^2))`

`= integral_Y^infinity (f'-f/(2*y))^2-f(Y)^2/(2*Y)`.

This is the exact lower boundary cost isolated in cycle 1.

## Positive cusp-tail theorem

When `k*Y>=1/2`, every term on the right of the first identity is nonnegative. Thus

`(1/4)*integral_Y^infinity f^2/y^2 <= integral_Y^infinity (f'^2+k^2*f^2)`.

Lean uses `Y=exp(h)` and `k=(1/2+u^2)/exp(h)`, so the capstone has no frequency-inequality premise. A separate closed range theorem proves that this parameterization covers exactly all `k>=1/(2*Y)`. This is a sufficient threshold; necessity is not claimed.

## Dependency-closed paper proof

Put `v=f/y` and `J=k*f^2-f*v/2`. Because `f` has compact support inside the positive ray, it vanishes near zero; hence `v` and `J` extend as `C¹` functions with compact support on the real line. For positive `y`,

`J'=2*k*f*f'-f'*v+v^2/2`.

Expanding the square gives

`f'^2+k^2*f^2-v^2/4=(f'+k*f-v/2)^2+k*f*v-J'`.

The compact-support fundamental theorem of calculus gives `integral_Y^infinity J'=-J(Y)`. Substitution proves the identity with the correct lower boundary sign. Positivity under the stated threshold gives the quarter inequality. Only `C¹` regularity is needed by this proof; no higher derivative is used.

## Lean implementation

Module: `GaloisForLFunctions.RHTower.SelbergCuspHardyBoundary`.

`Profile` is mathlib's bundled `TestFunction` of differentiability order one supported in the open positive ray. The implementation proves regularity of division by height, compact support of the flux, its actual derivative, all required integrability, and the actual improper set-integral identity.

Capstones: `cusp_hardy_identity`, `pure_hardy_boundary_identity`, `range_tailFrequency`, `cusp_hardy_nonneg`, and `cusp_tail_quarter`.

## Verification

- Scratch name checks and the full scratch proof passed.
- Final direct `lake env lean` check passed without warnings.
- The module is wired into the `RHTower` umbrella.
- Targeted `lake build GaloisForLFunctions.RHTower.SelbergCuspHardyBoundary` passed; only this target was rebuilt. No umbrella build ran.
- Six capstone axiom checks report only `propext`, `Classical.choice`, and `Quot.sound`.
- Index refresh and whitespace checks passed; no Lean/Lake process remained. Repository-wide lint failed on 11 unrelated unwired modules, listed in the parent verification log. It reported no error in this module.

## What remains for Selberg

The frequency `k` must next be related to the actual Fourier modes of an automorphic cusp form. Passing from compact profiles to the full cusp space requires the appropriate approximation and energy control. The compact part of the quotient and its gluing still need a congruence-uniform argument. None of these steps is hidden in the proved inequality.
