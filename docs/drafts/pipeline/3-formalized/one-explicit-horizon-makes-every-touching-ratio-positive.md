# One explicit horizon makes every touching ratio positive

- **ID:** one-explicit-horizon-makes-every-touching-ratio-positive
- **Stage:** 3-formalized
- **Statement:** There are a conductor bound `Q≥2` and `B>0` such that
  `N≥Q⁴` and `log N≥max(1,36B/e²)` make the actual complete tilted-spline
  Weil matrix positive definite for every `0<c≤1`. Here `e>0` is its
  endpoint conductor Fourier-tail floor.

## Proof

The six exact conductor residual terms have squared norm at most
`K_m/log N`, uniformly through touching. The prime and cross estimates
already have this rate. The center and pole estimates use `c²,c⁴≤1`.
The self and boundary terms use the direct periodic norm bound, together
with `log(N+1)≤2log N` and `(log N/N)²≤1/log N`.

The explicit defect reserve at every `N≥2` gives one conductor cutoff for
all nonpositive unit packets. Choose approximation error `1/4` and enlarge
its cutoff to `Q≥2`. At `N≥Q⁴`, the Ramanujan frame retains coordinate
mass at least `1/18` in every such packet. On a nonpositive eigenvector,
the conductor energy floor `e` bounds each squared coordinate by
`K_m/(e² log N)`. Take `B=1+Σ_{1≤m≤Q}K_m`. The logarithmic horizon makes
the total at most `1/36`, a contradiction.

## Lean

`CriticalArithmeticCorrelationTheory/CompleteConductorResidualsRetainTheirHorizonDecay.lean`:
`exists_completeWeil_touching_residual_explicit_horizon_bound` and
`exists_tiltedUnitSpline_completeWeilMatrix_posDef_explicit_through_touching`.
Direct `lake --old env lean` check passed. Both transitive axiom audits contain
only `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import present.
