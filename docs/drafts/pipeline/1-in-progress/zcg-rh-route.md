# ZCG route to RH: archimedean domination, carried down by a collision-free descent

- **ID:** zcg-rh-route
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** docs/reports/review-0311/fable-zero-configuration-geometry.md (Q0, Q3, Q4) · formal/GaloisForLFunctions/ZeroConfigurationGeometry/README.md §10
- **Statement:** RH follows from either of two statements. (O1) The heat flow is dominated down
  to `t = 0` at every height. (O3) No collision occurs in the last stretch
  `t ∈ (0, (2/3+ε)/log X]` of the heat descent at any height. The local camera (O2) turns O3 into a
  statement about the reality of coalescent near-collisions.

## Goal
A route to RH whose decisive mechanism is specific to `ζ` and sign-free. The ζ-specific mechanism
is the archimedean contraction of the functional equation:
`log|χ(σ+it)| ≤ −(σ − ½) log(t/2π) + O(1/t)`. It dominates Euler carriers above height
`2π e^{2ψ(N)+1}`, and the heat flow `H_t` above height `2π e^{(2/3+ε)/t}`. The route carries this
domination down to `t = 0` at every height. No positivity of a form, no spectrum, no count is used
as the decisive step.

## The chain

| # | Statement | Status | Lean |
|---|---|---|---|
| 1 | At height `X`, `H_t` is real and simple for `t ≥ t_X = (2/3+ε)/log X` | proved | `eventually_localNewmanConstant_le_twoThirds`, `riemannHeat_zeros_real_simple_twoThirds` |
| 2 | RH ⇔ `Λ_X = 0` for every `X` | proved | `riemannHypothesis_iff_forall_localNewmanConstant_eq_zero` |
| 3 | Along the descent, reality is lost only at a double zero | proved | `riemannHypothesis_iff_forall_zeros_simple`, `exists_first_collision` |
| 4 | A zero of depth `d` at height `X` forces `Λ_X ≥ c d²/log X` | proved | `exists_le_localNewmanConstant_of_offLine_zero` |
| 5 | At `t = 0`, the only time the image is arithmetic, the image at bandwidth `λ > ½` determines the isolated points near height `X`, and reads near-collisions at second order | proved for `ζ` at isolated points (`π/(λ log X)`); near-collisions open (O2) | `multDiff_zeta_eq_zero_of_isolated`, `one_add_pow_le_of_isolated_cancellation`, `exists_card_le_sharp_centred`, `norm_pairSignal_sub_sq_mul_curvature_le`, `deriv_deriv_primeChannel_modulate` |
| 6 | The configuration fixed in step 5 has no shallow tilt and no cluster that collides in the last stretch | open (O1, O3) | — |

## Obstacles
- **O1 Domination below the mean spacing.** The horizon constant `2/3 = 4μ(½)` is the floor of the
  Gaussian domination method (`KiKimLeeTwoThirdsHorizon`). Subconvexity lowers it (Bourgain:
  `13/21`). Lindelöf gives only `Λ_X = o(1/log X)`. Closing needs domination that sees the
  configuration at scale `1/log X`.
- **O2 Local camera below the isolation scale (programme-internal, next target).** Proved: for
  `λ > 1/4 + πμ/2` and large `X`, a tempered mimic of `ζ` at aperture `λ log X` with local density
  `≤ μ log X` agrees with `ζ` at every `π/(λ log X)`-isolated point of height `X`
  (`multDiff_zeta_eq_zero_of_isolated`; `μ = 1/2π` gives `λ > ½`). The constant is `e^{O((log X)²)}`
  and decay order `k ≍ log X` beats it. Open: cluster points closer than `π/(λ log X)`, i.e. the local
  form of the Ingham-scale resolution (`exists_depth_resolving_at_ingham_scale`) for near-collisions.
- **O3 Repulsion in the last stretch (arithmetic).** Every tilt at height `X` must collide before
  heat `t_X`. An isolated pair of squared half-gap `−δ²` collides at heat `δ²/2` (single-pair law,
  proved for polynomials), so isolated tilts would be shallow, `δ² ≲ 1/log X`. Deeper ones need a
  cluster at the heat scale `√t_X`. O3 asks the arithmetic image at `t = 0` to exclude both. Shallow
  tilts are read only at second order, through coalescent prime pairs below the mean spacing
  (`primeCoalSum_eq_oddEvenShiftPrimeCoalSum`). It must use the Euler product with the strict Euler
  bound: the twins are dominated above their horizon and still have tilted columns. The gap is
  exact (`twin_tilt_costs_weight`, `exists_twin_tilt_beyond_every_weight`): a tilted carrier zero at
  height `t` costs weight `≥ log(t/2π) − 6/t`, and the twins' tilts are reached once the weight grows
  like `log` height, as `W_Λ` does. O3 must therefore use cancellation of the prime sum, not its size.
- **Endpoint calibration.** `Λ ≥ 0` (Rodgers–Tao): the descent must use a property that holds
  exactly at `t = 0`. The Euler product has this property; the heat flow destroys it for `t > 0`.

## Gates
- [x] 0 → 1  in-progress: well-posed, ζ-specific mechanism identified, chain steps 1–4 proved in the
  corpus
- [ ] 1 → 2  fully-proven: O1 or (O2 and O3) on paper
- [ ] 2 → 3  formalized

## Approach
Step 5 is a theorem about `ζ` for isolated points. Next: the local Ingham-scale resolution for
near-collisions, the point where step 5 meets O3. Then formulate O3 as an exact
statement about the heat-deformed coalescent channel at height `X`, and calibrate it against the
twins, sparse flips and Davenport–Heilbronn data before attacking it.

## Log
- 2026-11-04 — created; chain steps 1–4 anchored in the corpus, step 5 in ZCG
