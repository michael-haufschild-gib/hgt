# PW-B unique reversible Gamma-source density

- **ID:** PW-B-GAMMA-REVERSIBLE-DENSITY-2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4)
- **Statement:** The actual forward and reciprocal jump-rate formulas have the positive reversible density w(x)=exp(-x-1/x)/x. Every density satisfying all positive-ray pair balances is a constant multiple of w. This density is integrable, invariant under inversion with its Jacobian, and agrees with the existing singular source geometry.

## Density-level proof

The existing source-normalized translations move x to x+h and to
x/(1+h*x), respectively, retaining exp(-h). At 0<x<y the forward rate is

`k_plus(x,y)=exp(-(y-x))/(y-x)`.

The reciprocal displacement from y to x is h=1/x-1/y, with derivative
-1/x^2 in x. Retaining this Jacobian gives the exact identity

`exp(-(1/x-1/y))/(1/x-1/y)/x^2`
`= k_minus(y,x) = (y/x)*exp(-(1/x-1/y))/(y-x)`.

Multiplication by w in both directions gives the same strictly positive
off-diagonal density

`exp(-y-1/x)/(x*(y-x))`.

For any competing density rho satisfying every such pair balance,
cancellation of the nonzero forward rate gives rho(x)/w(x)=rho(y)/w(y).
Comparing each positive x with 1 proves rho=c*w on the positive ray.
Positivity of rho, if required, makes c positive. The uniqueness theorem
does not require positivity or regularity of the competing density.

Direct algebra also proves w(1/x)/x^2=w(x). The actual original-source
density eta(x)=exp(x-1/x)/x^2 satisfies

`eta(x)*norm(Q(x))^2=w(x)` for Q(x)=sqrt(x)*exp(-x).

Its log-coordinate density equals the existing singular gain exactly:

`eta(exp(t))*exp(t)=pwLogSingularGain(t)`.

Finally, the exponential bound (1/x)*exp(-1/x)<=1 gives
w(x)<=exp(-x) on the positive ray. Continuity there and this admitted
majorant prove actual integrability of w.

## Mathematical limit of this result

This determines the density within the class requiring the stated pair
balance. It does not establish that a physical Ward law must impose that
class. The Jacobian theorem is a pointwise rate identity, not an integral
substitution theorem. Individual rates diverge at zero displacement;
pointwise balance alone proves no adjoint, operator closure, quadratic
form identity or stationarity.

The [continuing pairing attack](../1-in-progress/pw-b-gamma-reversible-pairing.md)
retains the predicted logarithmic cutoff correction and tests actual
Gamma source modes. Common operator domains, the full signed arithmetic
source, actual Xi spectral occurrence and independently forced fixed-grade
balance remain open. RH is not proved.

## Verification and research

Module: `formal/GaloisForLFunctions/RHTower/ThetaCusp/ThetaCuspHawkingParikhWilczekGammaReversibleDensity.lean`.
The final scratch passes all18 public declarations with only propext,
Classical.choice and Quot.sound. Identical proof bodies are promoted;
the one-copy RHTower umbrella import is wired. The targeted leaf build
passed in12s, building only this leaf. Index regeneration passed and
refreshed LEAN_API, LEAN_GAPS and LEAN_OVERVIEW (eleven changed entries,
zero removals in the shared tree). All18 public names occur exactly once
in the API and source corpus; proof bodies match the passing scratch.

Repository formal lint passed. The earlier unrelated CubicCuspPresentation
import failure is absent from this result. All owned Lean, research, build,
index and lint sessions are terminal. No full or umbrella build, numerical
experiment, added axiom, commit or push was used.

[Partial deep-search records](../1-in-progress/pw-b-gamma-reversible-pairing-searches.json)
retain candidate statements, source arguments and ingredient sets.
The source-specific density was derived from the literal translation
identities; no generic finite-fibre balance or bounded-weight theorem
was used to assume the desired operator law.
