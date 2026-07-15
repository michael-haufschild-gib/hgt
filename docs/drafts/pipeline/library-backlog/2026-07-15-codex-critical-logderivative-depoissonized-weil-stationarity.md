# Library update ticket: Euler-safe de-Poissonized Weil stationarity

Please add the following stage-2 paper theorem to the Door/library indexes during the next
single-writer index pass:

- `docs/drafts/pipeline/2-fully-proven/not_new_scientific_knowledge/critical-logderivative-euler-safe-depoissonized-weil-stationarity.md`

Index summary:

```text
The absolute-Euler boundary densities h_a(t)=Re(X'/X)(a+it) form one Poisson semigroup orbit.
After the exact tail-Laplace rewrite of the safe Cauchy-loss inequality, its minimum-kernel
subtraction contributes the inverse factor exp(a|u|), which cancels the Poisson damping.  Hence
every safe offset presents one stationary critical quadratic form.  At prime-power frequency
u=+-log n, the safe coefficient -Lambda(n)n^(-1/2-a)/2 becomes exactly
-Lambda(n)n^(-1/2)/2; the completion terms and the existing two-channel resolvent identity
identify the whole form with the completed Weil distribution on the finite exponential span.
Thus the safe offset is not a tunable proof parameter: going farther into absolute convergence
only smooths a form that the Cauchy loss de-Poissonizes exactly.  The theorem is a source-value
relation and route simplification, not an RH proof.
```

No Lean module was added.  The Fourier transform is distributional because the boundary density
has logarithmic growth, so the exponentially weighted object is defined only through the
convergent finite-exponential quadratic pairing.  Formal extension requires distributional
Fourier/Herglotz infrastructure and a continuity theorem for the selected source space.
Verification was intentionally not run under the active no-computation boundary.
