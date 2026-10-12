# Off-centre Turán window: log-concavity of the slice coefficients above (½ − x₀ + ε) log t

- **ID:** wd-off-centre-turan-window
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** `wd-goal-loop-2026-10-09.md` row 289; builds on `wd-off-centre-window` (row 288)
- **Statement:** For 0 < ε ≤ 1/8 there is t₀ such that for t ≥ t₀, ε ≤ x₀ ≤ ½, n ≥ 1 and (½ − x₀ + ε) log t ≤ n ≤ log t, the coefficients a_m = g_t^{(m)}(x₀)/m! of g_t(x) = ξ(½+x+it)ξ(½−x+it) satisfy a_{n−1}a_{n+1} < a_n².

## Paper proof
Saddle radius R of the order n (R L(x₀+R) = n), arc value G(θ) = f(Re^{iθ})e^{−inθ}/f(R), f(w) = g_t(x₀+w). Cauchy on the same circle for m = n−1, n, n+1: a_m = C R^{n−m} ∫₀^π Re(G e^{−i(m−n)θ}), C = |ξ(½+x₀+R+it)|²/(πRⁿ). So a_n = C I₀, a_{n∓1} = C R^{±1}(A ∓ B), with I₀ = ∫Re G, A = ∫Re G cos θ, B = ∫Im G sin θ. Hence a_n² − a_{n−1}a_{n+1} = C²(I₀² − A² + B²) ≥ C²(I₀ − A)(I₀ + A), and I₀ ∓ A = ∫Re G (1 ∓ cos θ). Both are positive by the saddle argument with weight w ∈ [0, 2]: on [δ₀/2, δ₀] (δ₀ = Λ^{−1/2}) Re G ≥ 7/40 and 1 − cos θ ≥ δ₀²/20, so the core gives ≥ (7/1600)δ₀³; the middle arc costs ≤ (2/1000)e^{−Λ^{1/5}/8} and the tail ≤ 2πE with E ≪ t^{−c}. The thresholds are Λ^{3/2}e^{−Λ^{1/5}/8} < ½ and πE ≤ Λ^{−3/2}/2000.

## Lean
`RHTower/XiSliceOffCentreTuranWindow.lean`: `exists_xiSliceProduct_turan_offCentre` (main), `xiSliceProduct_turan_of_saddle_shift`, `turan_of_three_forms`, `turan_of_weighted_pos`, `integral_weighted_pos_of_arc_bounds_scaled`, `iteratedDeriv_xiSliceProduct_eq_half_circle_freq`, `integral_two_pi_eq_two_re_of_conj`, `tail_budget_le_three_halves`, `tendsto_rpow_three_halves_mul_exp_neg_fifth_root`. Standard axioms.

## Gates
- [x] 0 → 1
- [x] 1 → 2
- [x] 2 → 3

## Extensions
- DONE (row 290): contiguous k×k Toeplitz minors positive above the window, every k. Lean: `exists_xiSliceProduct_toeplitzDet_pos_offCentre` (`RHTower/XiSliceOffCentreToeplitzWindow`), with the short-arc bound `exists_integral_shortArcTrigPoly_sq_ge` and `det_pos_of_quadForm_pos` (HTGeometry).
- Open: Fekete's criterion turns this into TP_k of the window block.
- Centre-0 version for the even sequence c_{2k}(t), with frequencies 0, ±2 and the quarter fold.

## Log
- 2026-10-11 — proved and formalized (row 289).
- 2026-10-11 — every-order extension proved (row 290).
