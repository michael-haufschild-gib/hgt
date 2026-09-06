# Mertens' theorem with the Euler constant, and the archimedean genus limit (Lean)

- **ID:** `mertens-euler-constant-lean`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean, unconditional)
- **Lean:** `RHTower.MertensVonMangoldtEulerConstant`, `RHTower.PoleSelfEnergyLimit`,
  `RHTower.PoleBoundaryLogSharpConstant` (all Mathlib/PNTPlus-only, wired into `RHTower`, axioms
  `[propext, Classical.choice, Quot.sound]`).
- **Parent:** `1-in-progress/fixed-pole-zero-margin-law.md`.

## Statements

1. `tendsto_neg_logDeriv_riemannZeta_sub_one_div`: `−ζ'(s)/ζ(s) − 1/(s−1) → −γ` as `s → 1`.
2. `integral_chebyshevError_div_sq`: `∫_1^∞ (ψ(t) − t)/t² dt = −γ − 1`.
3. `tendsto_sum_vonMangoldt_div_sub_log`: `Σ_{n≤x} Λ(n)/n − log x → −γ`.
4. `tendsto_poleDiagonalExplicit_div_exp`: `A(a)e^{−a} → 2 + γ − log 4π` for the explicit diagonal
   pole entry `A(a) = κ·2sinh a − e^a + (1−2a)e^{−a} + B₁(a) − 2e^aE_M(2a) + 2e^{−a}ψ(e^{2a})`.
5. `poleSharpConstant_pos`, `eventually_poleDiagonalExplicit_pos`.

## Proof

Removable singularity of `ζ(s) − 1/(s−1)` at `1` (Mathlib's limit `γ`), giving the Laurent constant
of `−ζ'/ζ`; Abel summation (`tendsto_sum_mul_atTop_nhds_one_sub_integral₀`) for the Mellin identity
`Σ Λ(n)n^{−s} = s∫_1^∞ ψ(t)t^{−s−1}dt`; the PNT with error term (`MediumPNT`) for integrability of
`(ψ − t)/t²`; dominated convergence as `s → 1⁺`; a second Abel summation for the reciprocal sum;
the closed antiderivative `G(e^{−t})`, `G(u) = (u−1)log(1−u) + (u+1)log(1+u) − 2u`, for the
weighted Gamma boundary mass; `γ > eulerMascheroniSeq 15 = H₁₅ − log 16` and the alternating series
for `log(3/2)` for the sign of the constant.

## Novelty

Mertens' theorem with the exact constant is classical (Mertens 1874); it is new in Mathlib and in
this corpus. The identification of the pole self-energy's leading coefficient with
`2 + γ − log 4π = Σ_ρ 1/(ρ(1−ρ))` and its reading as the archimedean genus of the fixed-pole Weil
criterion are the corpus's own (CANNOT-323/324, MUST-229/230); the zero-sum identity is on paper.
