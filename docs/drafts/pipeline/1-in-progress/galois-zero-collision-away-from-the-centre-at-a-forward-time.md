# A collision away from the centre exists at a forward time

- **ID:** gtz-m4-off-centre-collision
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** review-1311 §2.19 question 1 (B193), milestone M4; programme card
  `gtz-galois-theory-of-zeros-programme.md`, open core item 6.
- **Statement:** there are `τ`, `ζ` with `Re τ > 0`, `ζ ≠ 0`, `H_τ(ζ) = 0`, `H_τ'(ζ) = 0`.

## Goal

With the criterion `forwardMonodromy_preserves_pairs_iff` the statement gives: `G₊` does not
preserve the pairs `{z, −z}`; it contains an exchange of two zeros that are not negatives of
each other. Unconditional (no use of RH or of its negation).

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Objects

`Φ(x) = Σ_{n≥1} T_n(x)`, `T_n(x) = e^{x/2} R(n²e^{2x}) e^{−πn²e^{2x}}`, `R = 4π²X² + …` of degree
two, holomorphic and even on the strip `|Im x| < π/4` (`RHTower.KernelStrip.kernelC`).
`H_τ(z) = ∫_ℝ Φ(x) e^{τx² + izx} dx`.

Saddle parameter `a = σ + iη`, `δ = π/4 − η`:

- `P(a) = πe^{2a}`, `τ(a) = P/a`, `f(a) = P(a − 1)`, `λ(a) = 2P − τ`, `p = Re P = πe^{2σ} sin 2δ`.
- `a` is the saddle of `x ↦ τ(a)x² − πe^{2x}`, and with `ψ(v) = 1 + 2v − e^{2v}`
  `τ(a+v)² − πe^{2(a+v)} = f(a) + Pψ(v) + τv²`.
- Region `Ω(σ₀)`: `σ ≥ σ₀`, `1/(4σ) ≤ δ ≤ 1/σ`. On it `δ ≤ sin 2δ ≤ 2δ`,
  `πe^{2σ}/(4σ) ≤ p ≤ 2πe^{2σ}/σ`, `2e^{2σ}/σ² ≤ Re τ ≤ 5p/σ ≤ p/8`, `πe^{2σ} ≤ |λ| ≤ 3πe^{2σ}`,
  `Re λ ≥ p`.
- `B₀(a) = iΦ(0)(π/τ)^{1/2}` (bulk), `S₀(a) = 4π² e^{9a/2 + f(a)} (π/λ)^{1/2}` (saddle),
  `q = 2S₀/B₀`.

## Theorems

1. (Corner.) For every `τ, z` and `0 ≤ η < π/4`, with `h(τ,z) = ∫_0^∞ Φ(x)e^{τx²+izx}dx`:
   `H_τ(z) = h(τ,z) + h(τ,−z)` and
   `h(τ,z) = i∫_0^η Φ(iv) e^{−τv² − zv} dv + ∫_0^∞ Φ(s+iη) e^{τ(s+iη)² + iz(s+iη)} ds`.
2. (Laplace.) Let `P, τ, κ ∈ ℂ`, `p = Re P ≥ 18`, `0 ≤ 8 Re τ ≤ p`, `|κ| ≤ 6`, `λ = 2P − τ`. Then
   `|∫_{−1/2}^∞ e^{κv + Pψ(v) + τv²} dv − (π/λ)^{1/2}| ≤ C(1 + |P|/p)/p`, `C` absolute.
3. (Bulk.) On `Ω(σ₀)`, `|z| ≤ 1`:
   `|i∫_0^η Φ(iv)e^{−τv²−zv}dv − B₀(a)/2| ≤ C σ⁵ e^{−2σ}`.
4. (Saddle.) On `Ω(σ₀)`, `|z||a| ≤ 8`:
   `|∫_0^∞ Φ(s+iη)e^{τ(s+iη)²+iz(s+iη)}ds − S₀(a)e^{iza}| ≤ Cσ⁵e^{−σ}(|S₀(a)| + |B₀(a)|)`.
5. (Model.) On `Ω(σ₀)`, `|ζ| ≤ 8`:
   `|H_{τ(a)}(ζ/a) − B₀(a) − 2S₀(a) cos ζ| ≤ Cσ⁵e^{−σ}(|B₀(a)| + |S₀(a)|)`.
6. (Collision.) There are `τ`, `ζ ≠ 0` with `Re τ > 0`, `H_τ(ζ) = H_τ'(ζ) = 0`.
7. (Exchange.) For every forward base time `b` off the branch times, `G₊(b)` contains an
   element `σ` and a zero `z` with `σz ∉ {z, −z}`.

## Proof

1. `Φ` is even, so `∫_{−∞}^0 = h(τ,−z)`. Cauchy on the rectangle `[0,N] × [0,η]` for
   `F(x) = Φ(x)e^{τx²+izx}`; on the strip `|Φ(x)| ≤ K e^{Re x/2} e^{−a' e^{2 Re x}}`,
   `a' = (π/2)cos 2η`, so the side at `N` tends to `0` and both rays converge.
2. For `v ≥ −1/2`: `ψ(v) ≤ −(4/3)v²`, so `Re(Pψ(v) + τv²) ≤ −pv²`, and `Re(−λv²) ≤ −pv²`.
   `Pψ(v) + τv² + λv² = Pψ₃(v)`, `ψ₃(v) = 1 + 2v + 2v² − e^{2v}`, `|ψ₃(v)| ≤ 16|v|³e^{2|v|}`.
   With `|e^{w₁} − e^{w₂}| ≤ |w₁ − w₂| e^{max Re}` and `|e^{κv} − 1| ≤ 6|v|e^{6|v|}`:
   `|e^{κv+Pψ+τv²} − e^{−λv²}| ≤ (6|v|e^{6|v|} + 16|P||v|³e^{2|v|}) e^{−pv²}`. Integrate
   (`e^{6|v|}e^{−pv²/2} ≤ e`); the Gaussian tail `∫_{−∞}^{−1/2}` is `≤ 1/p`;
   `∫_ℝ e^{−λv²} = (π/λ)^{1/2}`.
3. `iΦ(0)∫_0^∞ e^{−τv²}dv = B₀/2`. On `[0,η]`: `|Φ(iv)| ≤ K_η ≤ Cσ³` (term bound with
   `a' ≥ π/(8σ)`), and `|Φ(iv) − Φ(0)| ≤ Lv` with `L ≤ C(1 + K_η)` (Cauchy estimate on
   `|x| ≤ 1/2`, trivial bound beyond). So `|Φ(iv)e^{−zv} − Φ(0)| ≤ C(L + 1)v`,
   `∫_0^∞ v e^{−Re τ v²} = 1/(2 Re τ)`, tail `∫_η^∞ ≤ 1/Re τ`, and `Re τ ≥ 2e^{2σ}/σ²`.
4. `x = a + v`, `v ≥ −σ`; `|e^{iz(a+v)}| ≤ e^{9}e^{|v|}`.
   - *Right part* `v ≥ −1/2`. `T₁ = 4π²e^{9x/2}e^{−πe^{2x}} + (low)`. The leading part is
     `4π²e^{9a/2+f(a)+iza} ∫_{−1/2}^∞ e^{κv+Pψ(v)+τv²}dv`, `κ = 9/2 + iz`; apply 2
     (`|P|/p ≤ 4σ`, `|(π/λ)^{1/2}| ≥ e^{−σ}/√3`). The low part has modulus
     `≤ C e^{5σ/2} e^{5|v|/2} e^{Re f(a) − pv²}`. For `n ≥ 2`: `|T_n(x)| ≤ K e^{s/2}e^{−(p/2)n²e^{2v}}`
     and `|e^{τx²}| = e^{Re f(a) + pψ(v) + Re τ v² + pe^{2v}}`, and `−(p/2)(n²−2)e^{2v} ≤ −pn/(2e)`.
   - *Left part* `s = Re x ∈ [0, σ − 1/2]`. `|Φ(x)| ≤ K_η e^{σ/2} e^{−(p/2)e^{2v}}`.
     On `[0, σ−1]`: `Re τx² = Re τ(s² − η²) − 2 Im τ·sη` is a convex quadratic in `s`, so
     `|e^{τx²}| ≤ max(e^{−η² Re τ}, e^{Re f(a) − p + Re τ})`. On `v ∈ [−1, −1/2]`:
     `Re f(a) + p(1 + 2v − e^{2v}/2) + Re τ v² ≤ Re f(a) − p/20`.
   - `e^{−η² Re τ}σK_η e^{σ/2} ≤ e^{−σ}|B₀|` and `e^{−p/20}σK_ηe^{σ/2} ≤ e^{−σ}·e^{9σ/2}e^{−σ}` for
     `σ ≥ σ₀`.
5. 1, 3, 4 at `±z`, `z = ζ/a`.
6. Let `g(δ) = (σ−1) sin 2δ − (π/4 − δ) cos 2δ`, so `Re f(a) = πe^{2σ}g(δ)`; `g(1/(3σ)) < 0 <
   g(1/(2σ))`, hence `a₁ = σ + i(π/4 − δ₁)` with `Re f(a₁) = 0`, `δ₁ ∈ [1/(3σ), 1/(2σ)]`. Then
   `1 ≤ |q(a₁)| ≤ e^{5σ}`. Let `ω = −Log q(a₁)`, `ϱ = 1/4`, `ξ₀(s) = ϱe^{iπs}`,
   `ϖ(s) = −Log cos ξ₀(s)` and
   `a(s) = a₁ + (ω + ϖ(s))/f'(a₁)`, `f'(a₁) = P(a₁)(2a₁ − 1)`. Then `a(1) = a(0)`,
   `|a(s) − a₁| ≤ Cσe^{−2σ}/σ`, `a(s) ∈ Ω`, and
   `f(a₁+h) − f(a₁) − f'(a₁)h = P₁[(e^{2h} − 1 − 2h)(a₁ − 1) + (e^{2h} − 1)h]`, so
   `q(a(s)) = (1 + ε₃(s))/cos ξ₀(s)`, `|ε₃| ≤ Cσ²e^{−2σ}` (the square roots vary by a relative
   `O(|h|)`: `|w^{1/2} − w₁^{1/2}| ≤ √2|w − w₁|/|w₁|^{1/2}` for `Re w₁ ≥ 0`).
   `F_s(ζ) = H_{τ(a(s))}(ζ/a(s))/B₀(a(s))`; by 5, `|F_s(ζ) − 1 − q(a(s)) cos ζ| ≤ ε` on
   `|ζ| ≤ 8`. With `ζ = π + ξ`:
   `1 − q cos ξ = [2 sin((ξ+ξ₀)/2) sin((ξ−ξ₀)/2) − ε₃ cos ξ]/cos ξ₀`.
   - `|F_s(π + ξ)| > 0` for `ϱ/4 ≤ |ξ − ξ₀(s)| ≤ ϱ/2`; `|F_s(π + ξ₀(s))| ≤ 2ε`;
     `|F_s(0)| ≥ 1`.
   - `γ(s) = τ(a(s))` is a closed path of forward times with `H_{γ(s)}(0) ≠ 0`. If some `γ(s)`
     is a branch time, its multiple zero is not `0`: done. Otherwise `γ` is a forward loop.
     `H_{γ(0)}` has a zero `z₀` with `|a(0)z₀ − π − ϱ| < ϱ/4` (minimum modulus on the disc).
     Its lift `z(s)` has `d(s) = |a(s)z(s) − π − ξ₀(s)| ∉ [ϱ/4, ϱ/2]`, `d` continuous,
     `d(0) < ϱ/4`, so `d(1) < ϱ/4`: `a(0)z(1)` is within `ϱ/4` of `π − ϱ`. Hence
     `z(1) ≠ z₀` and `z(1) ≠ −z₀`. Detector `exists_multipleZero_ne_zero_of_transports` with
     `D = {Re τ > 0}`.
7. 6 and `forwardMonodromy_preserves_pairs_iff`.

## Formalization

Planned modules in `GaloisTheoryOfZeros/`:

| Module | Content | Status |
|---|---|---|
| `TheHeatFamilyIsAnIntegralThroughTheOriginAndTheSaddle` | theorem 1 | not started |
| `TheGaussianAtTheSaddleOfTheKernel` | theorem 2 | not started |
| `TheBulkAndTheSaddleTermOfTheHeatFamily` | theorems 3, 4, 5 | not started |
| `ACollisionAwayFromTheCentreExistsAtAForwardTime` | theorems 6, 7 | not started |

## Log
- 2026-11-13 — created; paper proof written.
