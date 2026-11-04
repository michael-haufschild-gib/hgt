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
| 5 | At `t = 0`, the only time the image is arithmetic, the image at bandwidth `λ > ½` determines the isolated points near height `X`, and reads near-collisions at second order | local form proved with non-explicit `B`; explicit `B` open (O2) | `one_add_pow_le_of_isolated_cancellation`, `exists_card_le_sharp_centred`, `norm_pairSignal_sub_sq_mul_curvature_le`, `deriv_deriv_primeChannel_modulate` |
| 6 | The configuration fixed in step 5 has no shallow tilt and no cluster that collides in the last stretch | open (O1, O3) | — |

## Obstacles
- **O1 Domination below the mean spacing.** The horizon constant `2/3 = 4μ(½)` is the floor of the
  Gaussian domination method (`KiKimLeeTwoThirdsHorizon`). Subconvexity lowers it (Bourgain:
  `13/21`). Lindelöf gives only `Λ_X = o(1/log X)`. Closing needs domination that sees the
  configuration at scale `1/log X`.
- **O2 Local camera (programme-internal, next target).** Proved: an `η`-isolated cancelling point at
  height `X` forces the cluster count `(D, C₀)`, `πD < 2a`, to fail within `R` with
  `(1+R)^{2k−2} ≤ B(a,D,C₀,η,k)(1+|X|)² Σ|c|/(1+|γ|²)` (`one_add_pow_le_of_isolated_cancellation`).
  The sharp count input for `ζ` is proved (`exists_card_le_sharp_centred`). Open: `B` explicit. For
  `ζ` one has `a = λ log X`, `D, C₀ ≍ log X`, `η ≍ 1/log X`, and the theorem must apply with
  `R ≤ X/2`. Every factor of `B = M² e^a/c²` is explicit except the bump decay constant. The product
  constant and floor are `X^{±O(log(1/η) log log X)}`, so an explicit-decay bump (`sinc^m` factor)
  should give `B ≤ X^{O((log log X)²)}`, `k ≍ (log log X)²`, `R = X^δ`. Also open: the local form of
  the Ingham-scale resolution (`exists_depth_resolving_at_ingham_scale`) for near-collisions.
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
Finish O2 first: make `B` explicit (bump with explicit decay, then the explicit form of
`exists_uniform_isolating_window`), so step 5 becomes a theorem about `ζ` at every `λ > ½`. Then formulate O3 as an exact
statement about the heat-deformed coalescent channel at height `X`, and calibrate it against the
twins, sparse flips and Davenport–Heilbronn data before attacking it.

## Log
- 2026-11-04 — created; chain steps 1–4 anchored in the corpus, step 5 in ZCG
