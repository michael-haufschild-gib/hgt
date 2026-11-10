# Admissible gauge tangents are isozeric directions

- **ID:** B130-isozeric-tangents
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Power saving for prime tangents of joint gauge families.

## Target

For bounded real prime speeds `a_p`, the following are equivalent:

1. `i a_p` are the prime derivatives at zero of an actual bounded
   holomorphic gauge family with joint pole regularization at `(0,1)`.
2. `Σ_p |a_p| p^(-σ)` converges for some `σ<1`.
3. The linear phase flow `u_p(z)=exp(i a_p z)` has such a joint
   regularization and, on some half-plane extending left of one,
   each real fibre is ζ times a nowhere-zero holomorphic factor.

This identifies which infinitesimal directions the regularity assumptions
permit and asks whether every permitted direction integrates without
moving any zero. It does not assert that an arbitrary nonlinear family
with this tangent preserves zeros globally.

## Paper proof

The tangent power gap gives `Σ a_p² p^(-(1-δ))<∞`.
Cauchy–Schwarz with `Σ p^(-(1+δ/2))<∞` gives
`Σ |a_p| p^(-(1-δ/4))<∞`, proving necessity.

For sufficiency, choose `max(σ,1/2)<c<1` and `q=2^(-c)<1`.
Choose `M>1` with `Mq<1`. Bounded speeds give a common complex disk
`|z|<r` on which `|u_p(z)|≤M` and
`|u_p(z)-1|≤C|z||a_p|` for `u_p(z)=exp(i a_p z)`.
On `Re s>c`, set

`L_p(z,s)=log(1-p^(-s))-log(1-u_p(z)p^(-s))`.

Both logarithms have arguments in the disk about one of radius `Mq<1`.
The logarithm is Lipschitz there with constant `1/(1-Mq)`, hence

`|L_p(z,s)| ≤ C r |a_p| p^(-c)/(1-Mq)`.

The right side is summable, since `c>σ`. The summands are jointly
holomorphic, so their normally convergent sum `L` is jointly holomorphic.
Let `Z(s)` be the entire ζ residue factor and put

`U(z,s)=Z(s)exp(L(z,s))`.

For real `t`, the gauge with prime coordinates `t a_p/(2π)` has twist
`u_p(t)`. On `Re s>1`, absolute Euler logarithm convergence gives
`exp L(t,s)=F_t(s)/ζ(s)`, hence `U(t,s)=(s-1)F_t(s)`.
The complexified prime phases have derivative `i a_p` at zero and a
common bound on every fixed parameter disk. Thus this is an actual
jointly regularized family with the prescribed tangent.

For every real `t`, `|exp(i t a_p)-1|≤C_t|a_p|` with a constant independent
of `p`. Its prime perturbation is absolutely summable at `σ`. After
increasing `σ` into `(1/2,1)` if necessary, `exists_isozeric` gives a
nowhere-zero holomorphic factor on `Re s>σ`, preserving all ζ zero
multiplicities there. This proves the third condition; it implies the
first by the constructed family.

## Corpus boundary

`EulerDeformationsOfZetaAreIsozeric.exists_isozeric` already gives the
isozeric conclusion from absolute prime perturbation summability.
The new content sought is the exact characterization of tangents to
actual jointly regularized families and their integration by linear
phase flows. Corpus searches found finite Euler flows and the existing
residue tangent metric, not this characterization. No external novelty
claim.

The proof uses the corpus finite-dimensional Weierstrass theorem for
joint normal convergence. No arithmetic Stepanov producer follows from
this characterization.

## Lean result

`GaugeDeformations/IsozericTangentFlow.lean` proves necessity
(`gauge_tangent_absolute_power_saving`), realizes the exact prime
velocities (`deriv_linearPrimePhase_zero`), and proves the real linear
flow is isozeric (`linearPhaseGauge_isozeric`).

`GaugeDeformations/JointTangentRealization.lean` constructs the actual
joint continuation (`analyticAt_linearFlowRegularization`), proves its
Euler identity (`linearFlowRegularization_eq_gaugeFibre`), and closes
the equivalence (`bounded_prime_tangent_admissible_iff`). The integrating
flow preserves each zero multiplicity (`linearPhaseGauge_zero_order`).
The formal equivalence chooses the summability exponent in `(1/2,1)`;
this is equivalent to some exponent below one by monotonicity.

Both modules passed final direct Lean checks. All nine capstone axiom
audits contain only `propext`, `Classical.choice`, and `Quot.sound`.
No unproved continuation or summability premise is hidden in the family
realization.

## Stronger result for individual fibres

[Local residue classification](nonzero-gauge-residues-force-isozeric-continuation.md)
proves that a nonzero local regularized residue at one forces an
individual fibre into an isozeric class below one. This classifies whole
fibres under a local pole condition.
