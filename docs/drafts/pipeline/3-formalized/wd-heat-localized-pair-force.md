# Localized pair dissipation without an inverse-gap loss

- **ID:** wd-heat-localized-pair-force
- **Stage:** 3-formalized
- **Source:** [Localized heat energy](wd-heat-localized-energy-flux.md)
- **Lean:** `RHTower/Heat/LocalizedHeatPairForce.lean`
- **Declarations:** `localizedHeatPairForce_le`, `localizedHeatPairForce_conjugate`

## Statement

Let `w` be a differentiable real cutoff with derivative `v`, and suppose
`|v(x)-v(x')| <= M |x-x'|`, `M >= 0`. For two distinct complex points
`x+iy`, `x'+iy'`, put `d=x-x'`, `e=y-y'`. Their combined formal heat-force
contribution to the weighted squared-height energy is

`F = 2 ((v(x)y^2-v(x')y'^2)d - 2(w(x)y-w(x')y')e)/(d^2+e^2)`.

Then

`F <= -2(w(x)+w(x'))e^2/(d^2+e^2) + 2M(y^2+y'^2)`.

There is no inverse-gap factor in the error. For a conjugate pair of
nonzero height, `F = -4 w(x)` exactly.

## Proof

The numerator before the outside factor two equals

`-(w(x)+w(x'))e^2 + (v(x)-v(x'))d(y^2+y'^2)/2`
`+ ((v(x)+v(x'))d/2-(w(x)-w(x')))(y+y')e`.

The first error is at most `M d^2(y^2+y'^2)/2`. For the second, the
trapezoid remainder is at most `M d^2/2`, while
`|(y+y')e| = |y^2-y'^2| <= y^2+y'^2`. Divide their sum by
`d^2+e^2 >= d^2` and retain the negative interaction unchanged.

For completeness, the trapezoid bound is proved by the mean value
theorem applied to `w(r)-(v(x)+v(x'))r/2`. Between the endpoints its
derivative has absolute value at most `M |x-x'|/2`.

## Verification and scope

Final plain Lean check passed without errors or warnings:

`lake --old env lean GaloisForLFunctions/RHTower/Heat/LocalizedHeatPairForce.lean`

The module is wired into `RHTower.lean` and remains exported by
`HTGeometry.lean`; neither umbrella was compiled.
This is a proved calculus and pair-force estimate for the stated cutoff
class. It does not assume or assert an evolution equation for the actual
heat-zero measure. Applying it to that measure and passing through
collisions remain part of the active flux task.
