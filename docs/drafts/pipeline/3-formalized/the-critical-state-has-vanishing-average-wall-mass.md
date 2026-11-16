# The critical state has vanishing average wall mass

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Target:** ECS Q9; boundary decay of the actual critical state.
- **Statement:** `log(2/h) ∫(-h,0) F² ≤ C h` for `0<h≤1`; consequently
  the terminal average square mass tends to zero and
  `σ |LF(σ+iy)|→0` uniformly in `y` as `σ→∞`.

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

## Uniform transform consequence

Given `ε>0`, choose `δ>0` such that `∫(-h,0)F²≤ε²h` for `0<h≤δ`.
Truncation to `(-δ,0)` satisfies this bound at every positive scale.
The cumulative-mass Laplace estimate bounds its transform by `ε/t`.
The complementary transform is at most `‖F‖₁ exp(-δt)`.
Multiplication by `t` and passage to infinity therefore give `t LF(t)→0`.
The same proof for `|F|`, together with
`|LF(σ+iy)|≤∫|F(u)|exp(σu)du`, makes the conclusion uniform in `y`.

No pointwise boundary trace is asserted. No arithmetic exclusion follows.

## Lean

- `HTGeometry/Analysis/VanishingCumulativeLaplaceBound.lean`:
  `terminal_average_tendsto_zero_of_log_bound`,
  `abs_laplace_le_of_local_terminal_square_mass`,
  `tendsto_mul_laplace_of_vanishing_terminal_square_average`.
- `ExclusionOfTheCriticalState/TheCriticalStateHasVanishingAverageWallMass.lean`:
  `criticalState_terminal_square_mass_logarithmic_gain`,
  `criticalState_terminal_average_tendsto_zero`,
  `criticalState_uniform_right_laplace_o_inv`,
  `riemannHypothesis_or_criticalState_vanishing_wall_trace`.

Both modules passed final `lake --old env lean` checks and are umbrella-wired.
The entire boundary-regularity package counts once; the earlier linear bound
and generic analytic helpers carry no separate count.

## Further questions

The quantitative estimate `|LF(t)|=O(1/(t sqrt(log t)))`, its transfer to
the archimedean head, and the leading asymptotic remain unformalized.

## Inputs

- `criticalHalfLineFullEnergy_transverse_L2_gap`
- `criticalHalfLineFullEnergy_causal_ground_shear`
- `terminal_square_logarithmic_boundary_bound`
