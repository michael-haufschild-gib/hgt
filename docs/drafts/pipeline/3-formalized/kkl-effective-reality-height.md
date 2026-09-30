# Ki–Kim–Lee reality with an explicit height

- **ID:** KKL-EFFECTIVE-HEIGHT
- **Stage:** 3-formalized
- **Type:** QUANTITATIVE UPGRADE (heat lane; route LA, de Bruijn–Newman)
- **Parent:** `rh-goal-loop-opus-2026-09-29.md`, cycle 62
- **STATUS:** MUST-590

## Theorem [L]

`RHTower.DeBruijn.riemannHeat_zeros_real_of_le_re`: for `0 < t ≤ 1/8`, every zero `z` of
`H_t(z) = ∫Φ(x)e^{tx²}e^{izx}dx` with `|Re z| ≥ 2π e^{40/t}` is real. Axioms standard.

Previously only `∃ X₀(t)` (`exists_riemannHeat_zeros_real`, `exists_riemannHeat_zeros_real_uniform`).

## Mechanism

- `kklErrorUniform_le_of_mul_ge`: if `tα ≥ 20`, `t ≤ 1/8`, then `kklErrorUniform t α ≤ 1/8`.
  - Each of the five terms is `≤ e^{−α}`, using `α ≥ 160`, `1/t ≤ α/20` and
    `(4πt)^{−1/2} ≤ 1 + 1/(4πt) ≤ e^{α}` (`rpow_neg_half_le_one_add_inv`).
  - `23400 ≤ e^{9α}` comes from `x²/2 ≤ e^x`.
- `riemannHeat_ne_zero_of_le`: the Ki–Kim–Lee slope criterion (`re_slope_mul_conj_pos`, `window_fits`)
  at the explicit height.
- Reflection `H_t(−z) = H_t(z)` handles `Re z < 0`.

Module: `formal/GaloisForLFunctions/RHTower/KiKimLeeEffectiveReality.lean` (wired, clean, no collisions).

## Limits

The constant 40 is not optimized (the natural threshold is `tα ≳ 6`). The radius blows up as `t → 0`.
Bounding `Λ < 1/8 − c` explicitly would need, in addition, a quantitative descent of the top zero,
which the corpus has only in its contradiction form (`newmanConstant_lt_eighth`).
