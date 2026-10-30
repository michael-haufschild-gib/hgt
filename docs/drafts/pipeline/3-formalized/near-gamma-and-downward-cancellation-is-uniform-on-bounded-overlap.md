# Near Gamma and downward cancellation is uniform on bounded overlap

- **ID:** near-gamma-and-downward-cancellation-is-uniform-on-bounded-overlap
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** one-horizon-makes-every-bounded-overlap-positive

## Statement

For every compact `C²` unit profile of positive squared mass and fixed
conductor, near Gamma minus the full downward prime action tends to zero
in normalized norm uniformly for `1≤c≤K`. The near center block has the
same uniform limit.

## Proof [PROVED HERE]

Write `R(c)=2c exp(2c)`. The local archimedean expansion has one bounded
remainder independent of the width. The exact Mangoldt divisor identity
cancels its logarithm against the interior downward action. The remaining
coefficient is bounded by
`(C_arch+R(c)+|log c|)ϕ(m)+J_m`.
On `1≤c≤K`, replace `R(c)` and `|log c|` by `R(K)` and `log K`.
The near-row geometry then bounds squared row mass by `4R(K)³E²`.

Exterior products lie in at most `B=⌈K exp K⌉` extra product positions and
at most `B+1` receiving rows. The exact signed truncated divisor sum is at
most `ϕ(m)log ℓ`; hence its squared row mass is at most
`(B+1)(2ϕ(m)B)²`. Subtracting this boundary vector from the interior
residual gives the full downward cancellation. Each squared normalized
norm is bounded by a constant divided by `log N`.

For the near center block, its coefficient is at most
`α(K)(1+exp(1/2)) Σ_{i<m}|u_m(i)|`, once `N≥2K`, since the pole shift
`α(c)=c(∫φ)²/∫φ²` is nonnegative and increasing. Apply the same near-row
geometry and divide by `log N`.

## Lean formalization

`CriticalArithmeticCorrelationTheory/TheNearGammaDownwardCancellationIsUniformOnBoundedOverlap.lean`:

- `eventually_normalizedFullNearGammaDownwardVector_norm_uniform_overlap`
- `eventually_nearCenterVector_norm_uniform_overlap`
- `eventually_tiltedUnitSpline_fullNearGammaDownward_norm_uniform_overlap`

Direct Lean audit passed. All three transitive axiom audits contain only
`propext`, `Classical.choice`, `Quot.sound`. Supporting cancellation estimate;
no separate contribution count.
