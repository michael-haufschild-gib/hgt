# Horizontal phase-modulus rigidity at finite carrier depths one and two

- **ID:** carrier-horizontal-phase-modulus-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Lean:** `formal/GaloisForLFunctions/RHTower/CarrierHorizontalRigidity.lean` and
  `formal/GaloisForLFunctions/RHTower/CarrierDepthTwoRigidity.lean`

## Statement

1. At depth one, every zero of `completedGN 1` in the open critical strip with
   `|Im s| ≥ 12` lies on `Re s = 1/2` and is simple.  The high right half-strip is
   zero-free and admits a nonvanishing analytic `2^k`-th root of `completedGN 1` for
   every `k`; these roots assemble into a coherent Kummer tower.
2. There is an absolute height `A > 0` such that every zero of `completedGN 2` in the
   open critical strip with `|Im s| ≥ A` lies on `Re s = 1/2` and is simple.  Above the
   same kind of absolute threshold, the high right half-strip is zero-free and admits a
   nonvanishing analytic `2^k`-th root of `completedGN 2` for every `k`; the roots assemble
   into a coherent Kummer tower.

The capstones are
`completedGN_one_zero_re_eq_half_of_abs_im_ge`,
`completedGN_one_zero_simple_of_abs_im_ge`,
`exists_completedGN_one_root_carrierOneHighRight`,
`completedGN_one_coherentTower_carrierOneHighRight`,
`exists_height_completedGN_two_zero_simple_of_abs_im_ge`, and
`exists_height_completedGN_two_root_highRight`, and
`exists_height_completedGN_two_coherentTower_highRight`.

## Proof

For a nonvanishing analytic function `F`, the horizontal derivative of `log ‖F‖` is the
real part of `F'/F`.  Applied to `archFactor`, this is exactly `stripWindingRate`, whose
existing explicit lower bound is positive from height `12` and tends to infinity.

At depth one,

`completedGN 1 s = archFactor s + archFactor (1-s)`.

At a zero the two reflected summands have equal norm.  Strict horizontal monotonicity of
`log ‖archFactor(σ+iτ)‖` forces `σ = 1-σ`, hence `σ = 1/2`.  The positive winding rate
then makes the line zero transverse.

At depth two,

`dirichletPoly 2 s = 1 + 2^{-s}`.

Writing `q = 2^{-s}`, one has `‖q‖ < 1` in the open right half-plane and the exact Cayley
bound

`Re(q/(1+q)) < 1/2`.

Consequently the horizontal log-rate of the depth-two Dirichlet factor is strictly greater
than `-(log 2)/2`, uniformly in the height and abscissa.  The archimedean rate eventually
beats this fixed counter-rate, so the direct completed summand
`archFactor s * dirichletPoly 2 s` has strictly increasing horizontal log-modulus throughout
the strip.  Reflection and equal norm at a completed-carrier zero again force
`Re s = 1/2`.  The same strict net rate proves simplicity.  Convexity and simple
connectivity of the high right half-strip then give analytic dyadic roots.

## Dual gate

- **NOVEL:** the corpus previously used vertical phase advance to produce critical-line carrier
  zeros but did not use the Cauchy-Riemann dual horizontal modulus rate to exclude off-line
  carrier zeros.  The depth-two Cayley bound is the first nonconstant arithmetic factor for
  which this exclusion is unconditional.
- **SIGNIFICANT:** these are unconditional divisor and Kummer-tower theorems, not local center
  existence statements.  They replace an unknown peel radius by zero-free regional geometry at
  the first two carrier depths and identify the exact obstruction to extending the argument:
  a uniform lower bound for the horizontal log-rate of the arithmetic direct factor at the
  approximation depths used by the Euler-Maclaurin carrier.

## Remaining open core

`[OPEN CORE]` The depth-two contraction is not an approximation theorem for `xi`.  At depths
`N ≥ 3`, the direct Dirichlet factor is no longer a one-term unit-disc perturbation, so the
Cayley bound does not apply termwise.  Unconditionality requires a divisor/deck constraint that
survives the large finite depth selected by the symmetrized Euler-Maclaurin annulus supply, or a
new aggregate horizontal-rate inequality for that finite member.  No boundary nonvanishing or
peel-radius assumption may be inserted under a new name.

## Verification

- Focused Lean builds pass.
- Axiom audits of all capstones report only `propext`, `Classical.choice`, and `Quot.sound`.
