# The geometric scattering tower detects the Weil form domain

- **Stage:** 1-in-progress
- **Type:** CONJECTURE / construction
- **Obstacle:** B133: extend the intrinsic raw geometric diagonal from smooth packets to the actual closed Weil form.

## Target

On each physical aperture, extend the finite raw primitive-pair scattering
energies continuously to L², identify their exact arithmetic jump form,
and prove that their finite limiting domain is precisely the complete Weil
form domain. On that domain the limit must equal the literal closed Weil
form; outside it the energies must diverge to positive infinity.

## Mechanism to establish

At tower height `N`, the completed-symbol telescope suggests the jump
kernel `(1−exp(−Nt)) archLevyDensity(t)` and prime contacts multiplied by
`1−n^(−N)`. The polar operator is unchanged. The scalar term should be
`2θ′(0)−2 Re(logDeriv Γℝ(N+½))+2 Re(robinCounterterm(N+3/2))`.
The scalar correction tends to `2θ′(0)`; the prime correction is bounded
and converges in norm on each aperture. The positive jump kernels increase
to the exact critical Green kernel. For every integer height, the Laplace
identity is
`∫₀∞ κ_N(t) exp(−(s−½)t) dt = logDeriv Γℝ(s+N)−logDeriv Γℝ(s)`
on `Re s>0`. Gauss
digamma limits and dominated convergence give this identity; tilted Fourier
inversion then identifies the finite geometric packet form.

## Exact finite-height identity to formalize

For `k=f⋆f̃` and `c=3/2`, the raw primitive-pair energy must equal

`2 robinCounterterm(c+N) k(0) + H_k(0) + H_k(1)`
`− ∫₀∞ κ_N(t)(k(t)+k(−t)) dt`
`− Σ_n Λ(n)(1−n^(−N))/√n · (k(log n)+k(−log n))`.

Here `κ_N(t)=(1−exp(−Nt)) archLevyDensity(t)`. The identity fixes the
normalization before passage to the complete form domain. Its smooth-source
specialization must agree with the continuous finite-height L² form.
Defining an unrelated cutoff energy would not establish this bridge.

The formalization is unfinished; no complete-domain theorem is claimed.

## Boundary

The raw scattering construction retains its arithmetic data and separate
polar terms. No invariant torus-orbit gluing or unshifted positivity is
assumed. This does not identify a single invariant Green kernel on the
adelic quotient with Weil's diagonal.
