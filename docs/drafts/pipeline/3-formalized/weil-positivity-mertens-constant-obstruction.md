# Weil positivity forces a nonpositive Mertens constant

- **ID:** weil-mertens-constant-obstruction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** HF card `1-in-progress/hf-positive-hodge-attack/krein-producer-loops.md`, loop L50; STATUS MUST-357 (heavy-perturbation open core)
- **Statement:** If `∑_{2≤n≤x}(λ(n)−Λ(n))n^{−1/2} = A log x + B + o(1)` and the finite-atom Weil symbol with weights `λ` has nonnegative energy on every polar-constrained `C²` test at every level, then `B ≤ 0`. Deleting the even prime powers gives `B = γ > 0`, so positivity fails.

## Goal
MUST-357 proved rigidity of Weil positivity only for light perturbations, `∑|w_n| log x_n/√x_n < ∞`, using cosine-series uniqueness. Heavy perturbations were the open core. This card gives a mechanism that works for heavy perturbations. The low-frequency constant of the perturbation's summatory function enters the symbol energy of near-radical wide tests with weight `−4π‖f‖₂²`.

## Gates
- [x] 0 → 1: well-posed statement. Attack: near-radical spread tests plus Abel summation.
- [x] 1 → 2: complete paper proof below.
- [x] 2 → 3:
  - Lean theorems `RHTower.mertens_constant_nonpos_of_weilAtomSymbol_nonneg` and `RHTower.squareDeletedVonMangoldt_weilAtomSymbol_not_nonneg`, in modules `RHTower/WeilSymbolMertensExpansion.lean` (394 lines) and `RHTower/WeilPositivityMertensConstantObstruction.lean` (1067 lines).
  - Both oleans built with no diagnostics. Axioms: propext, Classical.choice, Quot.sound.
  - Both modules are wired into `RHTower.lean`.

## Setting
- `S_λ(ξ) = Re ψ(¼+iπξ) − log π − 2∑_{2≤n≤N} λ(n) n^{−1/2} cos(2πξ log n)`, with `N = ⌊e^{2a}⌋`. This is the corpus `weilAtomSymbol`.
- Test class at level `a`: `f ∈ C²`, `supp f ⊆ [−a,a]`, `h_f(±i/2) = 0`.
- For `λ = Λ`, `∫|h_f|² S_Λ = 2π W(f)`, the zero side of `ζ` (corpus `zeta_W_eq_integral_weilAtomSymbol_vonMangoldt`). Nonnegativity at all levels ⟺ RH.

## Paper proof

**Step 1 (symbol difference).** Write `k = f⋆f̃` and `φ(u) = Re(k(u)+k(−u))`. Then `∫|h_f|² cos(τy) dτ = π(k(y)+k(−y))`, so
`∫|h_f|² S_λ = 2π Re W(f) − 2π ∑_{2≤n≤N} c_n φ(log n)`, with `c_n = (λ(n)−Λ(n))/√n`.

**Step 2 (exact Mertens expansion).** `φ` vanishes on `[2a+1, ∞)`. Put `C(t) = ∑_{n≤t} c_n` (so `c_0 = c_1 = 0`) and `F = φ∘log`. Abel summation on `[1, e^{2a+1}]` gives
`∑ c_n φ(log n) = −∫_1^{b} F'(t) C(t) dt`.
Split `C = A log t + B + ε(t)`.
- `∫ F' = −φ(0) = −2‖f‖₂²`.
- `∫ F'(t) log t dt = −∫_0^{2a+1} φ = −|h_f(0)|²`. This uses `Ψ(t) = F(t) log t − ∫_0^{log t} φ` and `∫_ℝ k = |h_f(0)|²`.

Hence
`∫|h_f|² S_λ = 2π Re W(f) − 2π(A|h_f(0)|² + 2B‖f‖₂²) + 2π ∫_1^b F' ε`.
This identity is exact for every `A, B`.

**Step 3 (remainder).** Suppose `|φ'| ≤ M`, `|ε| ≤ E` on `[1,T]` and `|ε| ≤ η` on `[T,∞)`. Then
`|∫F'ε| ≤ M E log T + M η log b`.

**Step 4 (test family).** Fix:
- `κ`, a smooth bump equal to 1 on `[−1/8, 1/8]` and supported in `(−1/4, 1/4)`;
- `κ₂ = κ'' − κ/4`;
- `f_R = Φ_{≤R−1/4} ⋆ κ₂`, the corpus truncated radical test;
- `g(x) = κ(x−½) − κ(x+½)`, which has mean zero and is `L_g`-Lipschitz with `|g| ≤ 1`.

Put `f = f_R ⋆ g(·/S)` with `R = log S`. It is `C²`, supported in `[−(R+S), R+S]`, and `h_f = h_{f_R} · ĝ_S`. So `h_f(±i/2) = 0` and `h_f(0) = 0`.
- *Uniform constants.*
  - `‖f_R‖₁ ≤ C₁ := ‖Φ‖₁‖κ₂‖₁`, by Young's inequality applied to `|Φ| ⋆ |κ₂|`.
  - For `R ≥ L₁`, `|h_{f_R}(0)| ≥ |ξ(½)|/32`: we have `h_{f_R}(0) = (ξ(½) − tail̂)·(−¼∫κ)` and `∫κ ≥ ¼`.
  - `ξ(½) ≠ 0` because `ζ(½) ≠ 0`.
- *Mass.*
  - `f(x) = g(x/S) h_{f_R}(0) + r(x)` with `|r| ≤ L_g R C₁/S`, since `|g((x−t)/S) − g(x/S)| ≤ L_g|t|/S`.
  - This gives `‖f‖₂² ≥ ½ c₀² S‖g‖₂² − 2(R+S)(L_g R C₁/S)² ≥ cS`, using `R² ≤ 4S`.
- *Lipschitz.*
  - `f` is `C₁L_g/S`-Lipschitz and `‖f‖₁ ≤ 2(R+S)C₁`.
  - So `k` is `‖f‖₁·C₁L_g/S`-Lipschitz, and `|φ'| ≤ 8C₁²L_g =: M₀`, uniformly in `S`.
- *Zero side.* Every Weil summand of `f` is a summand of `f_R` times `ĝ_S(γ)·conj ĝ_S(conj γ)`, with `|ĝ_S| ≤ e^{S/2} S‖g‖₁` in the strip. The `f_R` factor carries the tail `ε_R ≤ E₀e^{6R}exp(−πe^{2R−1/2}) ≤ E₀S⁶e^{−πS²/2}` and the `C²` decay. Hence `‖W(f)‖ ≤ K S^{10} e^{−S}`.

**Step 5 (conclusion).** Suppose `B > 0` and take `η = Bc/(10(M₀+1))`. Choose `T` from the Mertens limit, then `S` large. The symbol energy is at most
`2π(BcS/2 − 2BcS + BcS/2 + BcS/2) = −πBcS < 0`. ∎

**Corollary (even prime powers).** Put `λ = Λ·1_{non-square}`. Then
`∑_{2≤n≤x}(λ−Λ)/√n = −∑_{m≤√x} Λ(m)/m = −(½ log x − γ + o(1))`,
by Mertens' theorem with Euler's constant (corpus `tendsto_real_sum_vonMangoldt_div_sub_log`). So `A = −½` and `B = γ > ½`, and positivity fails.

## Attack (Phase 4)
- **False?** The sign chain is consistent with the symbol heuristic `Re(−ζ'/ζ(1+2iτ)) → −γ` as `τ → 0`: the energy change is `≈ −4πγ‖f‖²`.
- **Circular?** No zero information is used. The zero side is bounded unconditionally through the radical tail, and the Mertens constant is unconditional.
- **Known?** The corpus had only light rigidity (MUST-357). Web search (2026-09-28) found Bombieri's quadratic-functional papers and the classical `log x − γ` Mertens refinement, but no statement linking perturbed prime weights to the Mertens constant through Weil positivity.
- **Verdict:** SURVIVES.

## Positive content / new insight
- Weil positivity at `Λ` has a **low-frequency constraint**. Every admissible deformation must have a nonpositive Mertens constant.
- The near-radical spread tests see exactly the constant `B`. The slope `A` is killed by `h_f(0) = 0`.
- Even prime powers are load-bearing: their contribution to positivity is exactly Euler's constant.
- Frequency-modulated tests, `g(x)cos(τ₀x)` in place of `g`, should give `Re D_w(½+iτ₀) ≤ 0` wherever the Dirichlet series of the perturbation converges. This extension is not formalized.

## Log
- 2026-09-28 — conjectured (L50), proved on paper, formalized; both modules built and wired.
