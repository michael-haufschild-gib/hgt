# Hankel Atom Displacement Tangents Are Indefinite

- **ID:** hankel-atom-displacement-tangent-indefinite
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / source-transfer guardrail
- **Source:** `c5-jensen-prime-kernel.md`,
  `positive-source-weights-require-pointwise-hankel-kernels.md`,
  `axis-positivity-does-not-imply-hankel-positivity.md`,
  `source-selector-repair-obligation-ledger.md`
- **Statement:** A positive atom in a Hankel moment matrix is positive
  semidefinite, but the first-order form created by moving that atom is
  indefinite. Therefore positive prime amplitudes attached to atom/root
  displacement cannot be used as pointwise PSD source kernels in the
  Jensen/Hankel chart.

## Setup

Fix degree `d>=1`. For `r in R`, let

`v_d(r)=(1,r,r^2,...,r^d)^T`.

The rank-one moment contribution of a positive atom of mass `m>0` at `r` is

`H_r=m v_d(r)v_d(r)^T`.

If the atom is displaced to `r+epsilon`, then

`H_{r+epsilon}=H_r+epsilon T_r+O(epsilon^2)`,

where

`T_r=m(v_d'(r)v_d(r)^T+v_d(r)v_d'(r)^T)`.

## Theorem

For every `d>=1`, `m>0`, and `r in R`, the tangent form `T_r` is indefinite.
It is neither positive semidefinite nor negative semidefinite.

## Proof

Identify a vector of coefficients `a=(a_0,...,a_d)` with the polynomial

`q_a(x)=sum_{j=0}^d a_j x^j`.

Then

`a^T v_d(r)=q_a(r)`,

and

`a^T v_d'(r)=q_a'(r)`.

Therefore the quadratic form of the tangent is

`a^T T_r a=2m q_a(r)q_a'(r)`.

Since `d>=1`, the affine polynomials

`q_+(x)=1+(x-r)` and `q_-(x)=1-(x-r)`

belong to the test space. They satisfy

`q_+(r)=q_-(r)=1`, `q_+'(r)=1`, and `q_-'(r)=-1`.

Hence

`T_r[q_+]=2m>0`,

while

`T_r[q_-]=-2m<0`.

Thus `T_r` has both positive and negative values on the same real test space,
so it is indefinite.

## Consequence For The Jensen/Hankel Prime Kernel

`c5-jensen-prime-kernel.md` records the first-order Hankel contribution of root
motion in the form

`sum_l epsilon_l(t) * 2 V(r_l)V'(r_l)`.

The theorem above gives the invariant reason this contribution is not a PSD
source kernel: for each moved atom/root, the tangent quadratic form is

`2 epsilon_l(t) q(r_l)q'(r_l)`,

which changes sign as the test polynomial changes.

Thus a positive prime amplitude such as `p^{-1/2}` does not make the
first-order Hankel displacement positive. It only weights an indefinite tangent
direction.

## Relation To Positive-Weight Transfer

`positive-source-weights-require-pointwise-hankel-kernels.md` says that a
linear positive-weight proof of Hankel positivity needs pointwise PSD source
kernels. This theorem shows that atom/root displacement tangents fail that
pointwise test immediately.

Therefore a proof in this chart cannot have the form

`positive Euler weights + atom displacement kernels => Hankel positivity`.

It must instead use one of the following stronger mechanisms:

1. a nonlinear comparison of full moment matrices, not their displacement
   tangents;
2. a completed explicit-formula identity that couples all displacement
   directions before the square test;
3. a sign-correlation or boundary-index theorem that is not reducible to
   pointwise PSD kernels.

## Route Impact

This theorem does not prove RH. It removes a concrete false source-transfer
shape from the rank-one/Jensen/Hankel route.

The live bridge remains:

`actual Euler/Gamma/FE source data => kernel exhaustion + full Schur/index sign`.

For the atom-motion chart, that bridge cannot be obtained by assigning positive
weights to the first-order prime displacement kernels. Those kernels are
intrinsically indefinite.

## Gates

- [x] 0 -> 1 in-progress: atom-displacement tangent isolated.
- [x] 1 -> 2 fully-proven: quadratic-form proof completed.
- [x] 2 -> 3 formalized: unconditional positive-atom theorem
  `HTGeometry.hankelAtom_posSemidef` and all-degree sign-changing tangent
  theorem `HTGeometry.hankelAtomDisplacementTangent_indefinite` in
  `formal/GaloisForLFunctions/HTGeometry/FiniteSourceGuardrails.lean`; exact
  target build passed and the capstone audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`.

## Log

- 2026-06-24 -- Codex: created to turn the Jensen-kernel indefiniteness
  observation into a reusable source-transfer guardrail.
