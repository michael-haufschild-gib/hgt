# Elliptic radial kernels integrate to the global zeta ratio

- **Stage:** 3-formalized
- **Parent:** [Arithmetic unfolding](../1-in-progress/finite-field-eisenstein-unfolding.md).
- **Statement:** For every complex `s` with `Re(s)>1`, the actual adelic radial
  kernel `K_s(a)=∏_v max(1,|a_v|)^(-s-1)` is absolutely integrable and
  `∫ K_s(a) da = ζ_K(u)/ζ_K(u/3)`, where `u=exp(-s log 3)`.

## Proof

Restricted-product integrality makes the logarithmic local height finitely
supported away from infinity. The audited global kernel is its spectral
exponential. Integral translations preserve every local height, so this
kernel is continuous.

The open finite cylinders, indexed by all finite sets of finite places,
form a countable directed exhaustion of the actual adeles. Their audited
Haar coordinate identity makes each kernel integral exactly the finite
product of normalized local spectral factors, including infinity. The
[unordered Euler-product quotient](../3-formalized/elliptic-local-spectral-products-converge-to-the-zeta-ratio.md)
converges to `ζ_K(u)/ζ_K(u/3)`, with direct Lean and axiom audits.

Pointwise, `|K_s|=Re(K_Re(s))`. Hence cylinder norm integrals converge to the
finite real part of the zeta ratio at `Re(s)`. The nonnegative functions
`1_C |K_s|` increase along the directed cylinder family and have pointwise
supremum `|K_s|`. Directed monotone convergence identifies the global norm
integral with the supremum of the cylinder norm integrals. Their proved
finite limit makes this supremum finite, proving absolute integrability.

Exhaustion convergence for the now-integrable complex kernel identifies
its global integral with the same finite-product limit. Uniqueness of the
complex limit gives the stated zeta ratio. No infinite product measure is
assumed and no sum/integral exchange precedes integrability.

## Lean

`ArithmeticEffectivityTheory/FiniteFieldEllipticGlobalSpectralIntegral.lean`:
`ellipticAdeleSpectralKernel_integrable` and
`integral_ellipticAdeleSpectralKernel`. Direct Lean audit passed; both
transitive axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`.

Identifying this radial kernel with the actual loop Iwasawa section remains
a separate input to arithmetic unfolding.
