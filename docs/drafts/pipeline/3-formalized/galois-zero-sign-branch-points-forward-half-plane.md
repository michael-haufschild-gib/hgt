# The sign branch points of the heat cover lie in the forward half-plane

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Question:** review-1211 §2.19 Q5 (position of the branch points with monodromy `r`).

`c(τ) = H_τ(0) = ∫ Φ(x) e^{τx²} dx`, `Φ` the Riemann kernel. The zeros of `c` are the times at
which pairs `±z` of zeros of `H_τ` collide at the centre.

## Theorems

1. (Sine transforms.) If `g` is strictly decreasing on `(0, ∞)` and `g(t) sin(yt)` is
   integrable there, `y > 0`, then `∫₀^∞ g(t) sin(yt) dt > 0`. No continuity; `g` may be
   unbounded at `0`.
2. `Im c(τ) = 2 ∫₀^∞ g_r(u) sin(bu) du` for `τ = r + ib`, `g_r(u) = Φ(√u) e^{ru}/(2√u)`.
3. For `r ≤ 0`, `g_r` is strictly decreasing on `(0, ∞)`.
4. If `Re τ ≤ 0`: `Im c(τ) > 0` for `Im τ > 0`, `Im c(τ) < 0` for `Im τ < 0`, `c(τ) > 0` for
   real `τ`. So `c(τ) ∈ ℂ ∖ (−∞, 0]`.
5. Every zero of `c` has `Re τ > 0` and `Im τ ≠ 0`. Every collision at the centre happens at
   such a time.
6. `√c` (principal branch) is analytic at every time with `Re τ ≤ 0`.
7. For `Re τ ≤ 0`: `Σ 1/z² = c'(τ)/c(τ)` over the zeros of `H_τ`.

## Proof

1. `h = π/y`. Write `sin = sin⁺ − sin⁻`. `sin⁻(yt) = sin⁺(y(t − h))`, and `sin⁻(yt) = 0` on
   `(0, h]`. So `∫₀^∞ g sin⁻ = ∫_h^∞ g(t) sin⁺(y(t−h)) dt = ∫₀^∞ g(t+h) sin⁺(yt) dt`, and
   `∫₀^∞ g sin = ∫₀^∞ (g(t) − g(t+h)) sin⁺(yt) dt`. The integrand is `≥ 0` and positive on
   `(0, h)`. Integrability of the two parts: restriction of `g sin` to the measurable sets
   `{sin > 0}`, `{sin < 0}`.
2. `Im(Φ(x)e^{τx²}) = Φ(x) e^{rx²} sin(bx²)`, even in `x`; substitute `u = x²`.
3. `Φ > 0` and `Φ` decreases on `[0, ∞)`; `e^{ru}` does not increase; `1/√u` decreases
   strictly.
4. 1–3 for `Im τ > 0`; conjugation `c(τ̄) = \overline{c(τ)}` for `Im τ < 0`; positivity of
   the real integrand for real `τ`.
5. 4, and the centre value is positive at real times.
6. `log` is analytic on the slit plane.
7. 5 and the trace formula of the fibre.

## Formalization

`HTGeometry/DecreasingSineTransformPositivity.lean`:
`integral_Ioi_mul_sin_pos_of_strictAntiOn_Ioi`.

`GaloisTheoryOfZeros/TheSignBranchPointsLieInTheForwardHalfPlane.lean`: `im_centreValue`,
`foldedWeight`, `strictAntiOn_foldedWeight`, `integral_Ioi_weight_mul_sin`,
`im_centreValue_pos`, `im_centreValue_neg`, `centreValue_mem_slitPlane`,
`centreValue_ne_zero_of_re_nonpos`, `re_pos_of_centreValue_eq_zero`,
`IsCollision.re_pos_of_center`, `hasSum_inv_sq_zeros_complexHeat_of_re_nonpos`,
`analyticAt_sqrtCentreValue`.

Checked with `lake --old env lean`; umbrella import wired.

## Open

A zero-free half-plane `Re τ ≤ a` with `a > 0`; simplicity of the zeros of `c`.
