# The cutoff Eisenstein constant term vanishes only on the critical line

- **ID:** EIS-CUTOFF-LINE-LAW
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); positive survivor of loop row 98 (`rh-goal-loop-opus-2026-09-29.md`)
- **STATUS:** MUST-625

## Theorem [L]

`RHTower.lagariasSuzuki_ne_zero`: for `Y > 1` and `0 < Re s < 1`, `Re s ≠ ½`, `Im s ≠ 0`,

`Λ(2s) Y^s + Λ(2s − 1) Y^{1−s} ≠ 0`,   `Λ = Γ_ℝ · ζ` (`reflectedCompletedLambda`).

This is the Lax–Phillips (pseudo-Laplacian) / Lagarias–Suzuki line law in the strip. The parameter form is `cutoffConstant_ne_zero`.

Axioms: `propext, Classical.choice, Quot.sound`. Module `R:EisensteinCutoffConstantTermLineLaw`.

## Proof

1. Set `s = ½ + u` with `u, −ū ∈ Ω`. Apply the corpus Maass–Selberg relation on `Ω × Ω` (`maassSelberg_lineModel`) at `v = −ū`. Combined with `integral_norm_sq_eq_truncatedPairing`, this gives `(u+ū)(u−ū)∫_𝒟‖Λ^Y E_u‖² = R(u, −ū, Y)`.
2. `msRight_neg_conj_eq_zero`: if `c_u(Y) = 0`, then `B = −A Y^{2u}` and `R(u,−ū,Y) = 0` identically. Uses `msA_neg_conj`, `msB_neg_conj`, `conj Y^u = Y^{ū}`.
3. Since `Re u ≠ 0` and `Im u ≠ 0`, the truncated series has zero norm and vanishes a.e. on `𝒟` (bounded on `𝒟`, finite volume).
4. `cutoffConstant_eq_zero_of_norm_zero`: pairing with `conj c(y)` over the band `1 < Im z ≤ Y` (`setIntegral_band_mul_line`) gives `∫_1^Y |c(y)|² y^{−2} = 0`. Hence `c ≡ 0` on `(1, Y)`.
5. At two heights `|y^{2u}|` differs, which forces `A = B = 0`. That contradicts `msA_ne_zero_or_msB_ne_zero`: one of `1 ± 2u` has real part `≥ 1`.

## Significance

A self-adjoint operator (the cutoff Laplacian) forces the zeros of an explicit function built from `ζ` onto the critical line, unconditionally. The zeros of `ζ` enter `c_Y` only as resonances: `Λ(2s) = 0` at `Re s < ½`, and `Λ(2s−1) = 0` at `Re s > ½`. The theorem is therefore RH-blind, the same mechanism as the retired HB route (row 98).
