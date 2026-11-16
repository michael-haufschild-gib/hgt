# The critical state has vanishing average wall mass

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Target:** ECS Q9; boundary decay of the actual critical state.
- **Statement:** `log(2/h) ∫(-h,0) F² ≤ C h` for `0<h≤1`; consequently
  the terminal average square mass tends to zero.

## Connection

For `T_hF=F(.+h)` and `c=⟨F,T_hF⟩`, put `J_h=F-cT_hF`.
The spectral gap bounds its square mass by `O(h)`: its square norm equals
that of the orthogonal residual `T_hF-cF`. Since `F` is a null direction,
`Q(J_h)=c²Q(T_hF)=O(h)` and `c²≤1`.

Full-energy coercivity gives `W₈(G)≤(Q(G)+B‖G‖²)/(a/2)`.
Prime and negative polar bounds, followed by
`exponentialSourceMass(G)≤‖G‖²+W₈(G)`, therefore give
`levyEnergy G≤L Q(G)+M‖G‖²` with fixed `L,M≥0`.
Thus `levyEnergy J_h=O(h)`. On `(-h,0)`, `J_h=F`;
the existing logarithmic boundary inequality gives the claimed bound.
This closes the paper argument; Lean verification is in progress.

## Consequences to prove

Vanishing average wall mass should force `t LF(t)→0`. Quantitative
weighted Laplace estimates should give
`|LF(t)|=O(1/(t sqrt(log t)))` and sharpen the archimedean head bound
toward its leading asymptotic. No boundary value or arithmetic exclusion
is assumed. No contribution counted.

## Inputs

- `criticalHalfLineFullEnergy_transverse_L2_gap`
- `criticalHalfLineFullEnergy_causal_ground_shear`
- `terminal_square_logarithmic_boundary_bound`
