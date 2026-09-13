# Positive convolution square does not bound source growth

- **Status:** generic inference refuted in Lean; targeted builds and axiom audit passed. Actual dyadic-root route remains open.
- **Rejected claim:** a real causal source with a nonnegative, integrable, decaying convolution square inherits absolute Laplace convergence throughout every positive half-plane.

## Exact construction

All kernels below vanish for `t<=0`. Put
`B_w(t)=t^(-1/2)*exp(-w*t)/Gamma(1/2)`, `A(t)=exp(-3*t)`,
`R_w=B_w-(3-w)*(A*B_w)`, and
`g0=R_(1+2i)*R_(1-2i)`. Both filters are integrable; conjugation and convolution
commutativity prove `g0` real. On `Re(s)>=0`,

`L(g0)(s)^2=((s+1)^2+4)/(s+3)^4`.

The complex-rate Gamma integral proves the filter transforms. L1 Fourier uniqueness
then gives the full almost-everywhere identity

`g0*g0=exp(-3*t)*(t-2*t^2+4*t^3/3)` on the positive ray.

If `exp(5*t/4)*g0` were integrable, its Laplace transform would be holomorphic near
`rho=-1+2i`. The admitted convolution identity would identify its square with the
rational transform there. That transform has a simple zero at `rho`; the square of
a differentiable function cannot have a nonzero derivative at its zero.

Set `g(t)=exp(2*t)*g0(t)`. Then `exp(-2*t)*g` is integrable, whereas
`exp(-3*t/4)*g` is not. Nevertheless,

`g*g=K`, `K(t)=exp(-t)*t*((1-t)^2+t^2/3)`.

`K` is strictly positive for `t>0`, integrable, and tends to zero. This includes an
explicit source and its convolution identity; it is not only a target-transform test.

## Positive survivor and scope

- The construction supplies a real source, a proved convergence weight, exact filter
  transforms, and its complete positive convolution square. These statements and the
  failed stronger weight are closed in Lean scratch with default heartbeats.
- `CausalGammaHalfLaplace` isolates the reusable positive-rate Gamma and exponential-filter
  calculus; its targeted production build passed.
- At real rate `w=2`, the same filter equals the existing pole-cleared half-kernel
  multiplied by `exp(-3*t)/Gamma(1/2)`. The exact identification, integrability, and
  square-transform formula passed a separate Lean scratch check.
- No novelty claim. No estimate for the actual arithmetic baseline follows. The actual
  source has additional arithmetic coefficients and logarithmic singularities not
  represented by this counterexample. Their effect remains to be proved.

## Source audit

- Local complex-rate Euler integral: `HTGeometry/BarnesMellinRepresentation.lean:217`.
- Local L1 Fourier uniqueness: `HTGeometry/FourierUniquenessL1.lean:113`.
- Local Laplace holomorphy from absolute convergence:
  `HTGeometry/BochnerLaplaceHolomorphy.lean:58`.
- Complete scratch: `/tmp/dyadic-positive-laplace.JLS3Bp/GammaSource.lean`.
- Production leaves `HTGeometry/CausalGammaHalfLaplace.lean`,
  `HTGeometry/PositiveConvolutionSquareGrowth.lean`, and
  `HTGeometry/GammaHalfPoleClearing.lean` are wired and passed targeted builds.
  All 55 public theorems were audited in `/tmp/dyadic-positive-laplace.JLS3Bp/Axioms.lean`:
  only `propext`, `Classical.choice`, and `Quot.sound`. Default heartbeats.
