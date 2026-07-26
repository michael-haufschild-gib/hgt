# Digamma-orientation vertical-rigidity universality law

Status: Stage 3 — formalized in Lean 4; final umbrella audit pending  
Lean target: `GaloisForLFunctions.RHTower.DigammaOrientationVerticalRigidityUniversalityLaw`  
Novelty: `[NOVELTY UNVERIFIED]`

## Theorem-generated discovery

`ExplicitDigammaOrientationLimit.signedDigammaBooleanCompletion_nonneg_iff_allPositive` proves that
the all-positive residue orientation is the unique Boolean Gauss completion with nonnegative
imaginary part throughout the upper half-plane.  The same module identifies that orientation with
the shifted-digamma source off its pole lattice.

Independently, `DigammaVerticalMinimum.re_digamma_mono_of_abs_le` proves that the real part of
ordinary digamma is nondecreasing with absolute height on every vertical line in the right
half-plane.  The corpus contains no theorem transporting this vertical law through the orientation
classification.

## Statement

For a Boolean residue orientation `ε`, let `H(ε)` assert that its signed Gauss completion has
nonnegative imaginary part on the open upper half-plane.  Then `H(ε)` is equivalent to the
simultaneous certificate:

1. every residue is positively oriented (`ε` is constantly `false`);
2. the completion equals the explicit shifted-digamma Herglotz source at every point off the
   half-integer pole lattice;
3. on every vertical line `Re w = a` with `a > -1/2`, its real part is nondecreasing as `|Im w|`
   increases.

In particular, the global Herglotz condition alone forces the new vertical-height rigidity law.

## Dependency-closed proof

1. Infinite signed orientation classification sends `H(ε)` to `ε = false`.
2. Substitute the all-positive orientation.  The existing Gauss-series identity identifies the
   completion with `ψ(w + 1/2) + γ` away from the pole lattice.
3. If `a > -1/2`, then `a + 1/2 > 0`, so both points on the vertical line are off every nonpositive
   integer pole.
4. Apply digamma height monotonicity at positive abscissa `a + 1/2`.
5. Addition of real Euler constant preserves real-part order.
6. Conversely, the simultaneous certificate includes `ε = false`; the existing classification
   returns `H(ε)`.

No computation, new analytic premise, or pointwise sign estimate is added.

## Novelty audit

Corpus audit: source identity, orientation classification, and vertical digamma monotonicity occur
in separate modules.  No theorem states the classification-to-height-rigidity transport or the
three-part simultaneous certificate.

Literature audit: deferred until exact Lean proof succeeds, per research protocol.

## Lean verification

- Exact source check passed:
  `lake env lean GaloisForLFunctions/RHTower/DigammaOrientationVerticalRigidityUniversalityLaw.lean`.
- Wired into `GaloisForLFunctions.RHTower`.
