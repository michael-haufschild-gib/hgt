# Green damping detects the complete Weil form domain

- **Stage:** 1-in-progress
- **Type:** CONJECTURE / construction
- **Obstacle:** B133: identify the closed form behind the arithmetic Green construction.
- **Target:** Extend the Green finite part from compact smooth packets to the complete source-defined Weil form domain, and prove that finite convergence characterizes that domain.

## Proposed statement

For a compactly supported complex `L²` state `f`, let

`J_r(f)=∫_(t>0) archDamped(r,t) ‖f−f(·+t)‖₂² dt`, `0≤r<1`.

Conjecture: `J_r(f)` increases to the extended critical jump energy. Its
limit is finite exactly when
`∫ (1+log(1+|ξ|)) |Fourier(f)(ξ)|² dξ` is finite. On this domain,
adding the geometric scalar, polar term, and saturated prime term gives
the existing literal closed Weil form, hence its source-defined Friedrichs
operator. No positivity of the full Weil form is assumed.

## Mechanism

The corpus identifies the extended critical jump energy with the Gamma
Fourier multiplier and constructs the complete weighted Fourier form
domain. Monotone convergence of the actual damped kernels should identify
the domain, rather than merely convergence on a smooth core. On a fixed
aperture the prime clock saturates at one common finite threshold; all
remaining prime and polar terms are bounded forms.

## Required proof

Prove boundedness and continuity of each damped form on physical `L²`;
the extended monotone limit and finite-limit criterion; the exact comparison
with the complete aperture form and its operator. Check every analytic
input in Lean. Strong or norm resolvent convergence is not yet asserted.

## Boundary

This uses translation-averaged Green channels and the arithmetic clock.
It does not identify an invariant single-carrier torus Robin mass with
Weil's diagonal. The accepted gluing obstruction remains in force.
