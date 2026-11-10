# Pole residue curvature of analytic gauge families

- **ID:** B130-pole-curvature
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** B130/F3 specialization at the jump fibre; ArithmeticWeightTheory.
- **Statement:** A jointly meromorphic gauge family through ζ with its pole fixed at one has residue curvature equal to an explicit convergent prime quadratic form.

## Theorem

Let `u_p(t)` be holomorphic on one complex disk, uniformly bounded there,
with `u_p(0)=1` and `|u_p(t)|=1` for real `t`. On `Re s>1`, form the actual
Euler product `F(t,s)=∏_p(1-u_p(t)p^(-s))^(-1)`. Suppose its regularization
`U(t,s)=(s-1)F(t,s)` extends jointly holomorphically near `(0,1)`.
Write `r(t)=U(t,1)` and `u_p'(0)=i a_p`, with `a_p` real.

Exact identity:

`-(d²/dt²) log|r(t)| at t=0 = Σ_p a_p² p/(p-1)² < ∞`.

For several real parameters, the corresponding Hessian is the
prime Gram form `Σ_p p/(p-1)² a_p⊗a_p`. Its null directions are exactly
those invisible to every first prime-phase variation.

## Derivation

Cauchy's estimate gives a common smaller parameter disk on which
`|u_p(t)|≤3/2`. For `q=p^(-σ)`, `σ>1`, one has `q≤1/2`, so
`|q u_p(t)|≤3/4` and `|-log(1-q u_p(t))|≤6q`. Since `Σ_pq<∞`,
the logarithmic Euler sum is holomorphic on that disk and can be
differentiated termwise twice.

Differentiate `u_p(t) conj(u_p(t))=1` along the real axis. At zero,
`Re u_p'(0)=0` and `Re u_p''(0)=-a_p²`. Direct differentiation gives

`Re [-log(1-q u_p)]''(0) = -a_p² q/(1-q)²`.

Thus imaginary phase acceleration cancels. The actual Euler-product
identity and `log|exp z|=Re z` imply

`-∂²_t log|U(t,σ)| at zero = Σ_p a_p² p^σ/(p^σ-1)²`.

The factor `σ-1` contributes a constant in the parameter. At the trivial
fibre, the zeta residue gives `U(0,1)=1`. Hence `log U` is jointly
holomorphic near `(0,1)`, and its second parameter derivative is
continuous in `σ` there. The left side therefore has a finite limit.

Every finite prime sum tends to its boundary sum and is bounded by the
full positive sum. Passing to the limit bounds every finite boundary sum
by the finite curvature limit, proving boundary summability. Each
approximating term is bounded by its boundary value; dominated convergence
then identifies the full boundary sum with that limit. Neither
summability nor an interchange of differentiation at the boundary is an
assumption.

For several parameters, restrict to each real line through the origin.
The prime speed is linear in its direction. Polarizing the directional
identity yields the Gram form. All weights are strictly positive, so
its null directions are exactly those annihilated by every prime speed.

## Corpus audit and boundary

- `TheJumpLocusIsThePretentiousArchimedeanLine.lean` characterizes radial
  pole growth by finite pretentious distance; it does not assert joint
  meromorphic continuation of a parameter family.
- `EulerDeformationsOfZetaAreIsozeric.lean` treats prime perturbations
  absolutely summable in a half-plane. The tangent condition is
  quadratic at the pole.
- `EulerFisherCurvature.lean` proves a moment-determinant curvature law for
  the prime-power spectrum at `β>1`. It does not identify the Hessian of a
  continued gauge family's pole residue or force tangent summability there.
- Searches for pole curvature, pretentious second derivatives, and
  square-summable gauge tangents found these inputs, not the target identity.
- A second search for the exact residue Hessian and prime weights found
  phase asymptotics and logarithmic derivatives of other functions, not
  this family identity. No external novelty claim.

The common phase direction `a_p=1` would be excluded by divergence of
`Σ_p1/p`. The positive target is the exact residue metric and its nullspace,
not merely this exclusion. No family satisfying the joint continuation
condition is constructed, and no purity specialization or Stepanov bound
follows yet.

## Lean status

`ArithmeticWeightTheory/GaugeDeformations/PoleResidueCurvature.lean` proves
the scalar identity (`gauge_residue_curvature_hasSum`) and its exact tangent
classification (`gauge_residue_tangent_classification`). Finite energy is
equivalent to `Σ_p a_p²/p<∞`; zero curvature means every complex first
prime derivative vanishes. The constant unit prime speed is excluded.
Final direct audit passed with only `propext`, `Classical.choice`, and
`Quot.sound`. Analytic ingredients reside in `EulerPhaseCurvature.lean`.

`PoleResidueHessian.lean` proves the full finite-parameter Gram identity
(`gauge_residue_hessian_hasSum`), positivity
(`gauge_residue_metric_positive_and_kernel`), and exact kernel in the
complex prime differentials (`gauge_residue_hessian_kernel`). These use
the actual real Fréchet Hessian of `log|U(v,1)|`. Convergence of mixed
entries follows by polarization, without a separate summability premise.
All three modules passed final direct audits with the standard three axioms.

## Further question

[Power saving for prime tangents](../3-formalized/power-saving-for-prime-tangents-of-joint-gauge-families.md)
proves that joint continuation forces convergence of the tangent energy
at some real exponent below one.
