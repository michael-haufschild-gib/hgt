# ZCG route to RH: archimedean domination, carried down by a collision-free descent

- **ID:** zcg-rh-route
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** docs/reports/review-0311/fable-zero-configuration-geometry.md (Q0, Q3, Q4) · docs/reports/review-0411/obstacles-summary_v2.md (1.9, 1.10, 2.5.5, 2.6.5, B44, B49, B51) · formal/GaloisForLFunctions/ZeroConfigurationGeometry/README.md §10
- **Statement:** Steps 1–5 of the descent are proved ([L] and [P]); the remaining step 6 reduces to
  (a) reality inside near-coincidence clusters of `ζ` smaller than `X^{−M}` (B44) and (b) no
  collision of `H_t` near `X` for `t ∈ (0, ½/log X]` (B49). The camera fixes the configuration of
  `ζ` at `t = 0` outside such clusters; it produces nothing alone.

## Goal
A route to RH whose decisive mechanism is specific to `ζ` and sign-free: the archimedean contraction
of the functional equation, carried down to `ζ` along the heat deformation. No positivity of a form,
no spectrum, no count is used as the decisive step.

## The chain

| # | Statement | Status | Lean / card |
|---|---|---|---|
| 1 | Near `X`, `H_t` is real and simple for `t ≥ (6600/9991 + ε)/log X` | `(2/3 + ε)` [L]; `6600/9991` [P]; above `½/log X`, so carries no zero information | `eventually_localNewmanConstant_le_twoThirds`; `zcg-heat-scale-source-repulsion` |
| 2 | RH ⇔ `Λ_X = 0` for every `X` | [L] | `riemannHypothesis_iff_forall_localNewmanConstant_eq_zero` |
| 3 | Along the descent, reality is lost only at a double zero; simplicity = phase speed of the symmetric half `Q_t` | [L]; phase-speed law [P] | `riemannHypothesis_iff_forall_zeros_simple`, `exists_first_collision`; `zcg-heat-scale-source-repulsion` |
| 4 | A zero of depth `d` at height `X` forces `Λ_X ≥ c d²/log X` | [L] | `exists_le_localNewmanConstant_of_offLine_zero` |
| 5 | At `t = 0`, the image at every aperture above `L = ½ log(X/2π)` fixes the configuration of `ζ` outside near-coincidence clusters | [L] at `exp(−κ log X/(1 + log log X))`; [P] uniformly at `X^{−M}`, Lean assembly in progress | `multDiff_zeta_eq_zero_of_nearly_isolated`, `exists_near_coincidence_of_zeta_mimic`; `zcg-square-root-local-inversion` |
| 6 | No collision near `X` for `t ∈ (0, ½/log X]`, and reality inside near-coincidence clusters | open: (a) B44, (b) B49 | — |

## The residual
- **(a) B44.** Reality at near-coincident clusters below the isolation scale. Second-order local
  inversion (B51) fixes centre and squared gap `w²` of every near-coincident pair, uniformly in
  height [L]: pairs closer than `X^{−(M' + κ_λ + 1)}` and `X^{−M'}`-isolated agree in centre to
  `O(r² X^{M' + κ_λ})` and in `w²` to `O(r³ X^{M' + κ_λ})`, up to `e^{−K' log³ X}`
  (`pair_centre_and_gap_rvm`); isolated dipoles collapse below `2e^{−K' log³ X}`
  (`dipole_collapse_rvm`); card `zcg-second-order-local-inversion`. A single image reads the
  squared gap of every such pair through the Hankel ratio `4(W₁² − W₀W₂)/W₀²` of three window
  images [L] (`pair_hankel_rvm`, card `zcg-image-hankel-reads-squared-gap`): B44 is the sign of an
  image Hankel determinant at every near-coincident pair. The squared gap is read linearly through the `(log n)²`-weighted
  coalescent channel (`norm_pairSignal_sub_sq_mul_curvature_le`, `deriv_deriv_primeChannel_modulate`).
  Its sign is B44 in prime form.
- **(b) B49.** A Hermite–Biehler half `Q` from Euler and Gamma data with `H_t = Q + Q^#` and
  `|Q^#| < |Q|` off the line for `t ∈ (0, ½/log X]`. Below `½/log X` the Gaussian saddle
  `σ* = ½ + t log(X/2π)` lies in the strip, so domination needs a lower bound for `ζ` on a horizontal
  segment inside the strip: zero-free-region information. The twins (`twin_tilt_costs_weight`,
  `exists_twin_tilt_beyond_every_weight`) force it to come from cancellation of the prime sum, not its
  size.
- **Killed: the camera as a producer.** Identification is complete and sign-free and decides nothing
  alone. The residual is a precision problem (square-root-type cancellation at the saddle), not an
  identification problem.

## Gates
- [x] 0 → 1  in-progress: well-posed, ζ-specific mechanism identified, chain steps 1–5 proved
- [ ] 1 → 2  fully-proven: (a) and (b) on paper
- [ ] 2 → 3  formalized

## Approach
The camera–heat assembly is formalization: `X^{−M}` local inversion, the symmetric-half collision
law and the four-piece horizon (cards `zcg-square-root-local-inversion`,
`zcg-heat-scale-source-repulsion`). The research core is (b): a mollified Euler–Gamma half that is
one-sided below `½/log X`. First test: one `τ < ½` on almost all unit windows near `X`.

## Log
- 2026-11-04 — created; chain steps 1–4 anchored in the corpus, step 5 in ZCG
- 2026-11-04 — step 5 for `ζ` in Lean; residual stated as B44 and B49
