# A collision away from the centre exists at a forward time

- **ID:** gtz-m4-off-centre-collision
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** review-1311 §2.19 question 1 (B193), milestone M4; programme card
  `gtz-galois-theory-of-zeros-programme.md`, open core item 6.
- **Statement:** for every `T` there are `τ`, `ζ` with `Re τ > max(T, 0)`, `ζ ≠ 0`, `H_τ(ζ) = 0`,
  `H_τ'(ζ) = 0`.

## Goal

With the criterion `forwardMonodromy_preserves_pairs_iff` the statement gives: `G₊` does not
preserve the pairs `{z, −z}`; it contains an exchange of two zeros that are not negatives of
each other. Unconditional (no use of RH or of its negation).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven
- [x] 2 → 3  formalized

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
   `|∫_{−1}^∞ e^{κv + Pψ(v) + τv²} dv − (π/λ)^{1/2}| ≤ 64e⁴(1 + |P|/p)/p`.
3. (Bulk.) For `Re τ > 0`, `1/2 ≤ η < π/4`, `|z| ≤ 1`:
   `|i∫_0^η Φ(iv)e^{−τv²−zv}dv − (iΦ(0)/2)(π/τ)^{1/2}| ≤ C(1 + K_η)/Re τ`, `K_η` the constant of
   the strip bound `|Φ(x)| ≤ K_η e^{Re x/2}` on `|Im x| ≤ η`, `Re x ≥ 0`.
4. (Saddle.) For `Re a ≥ 1`, `0 ≤ Im a < π/4`, `p ≥ 18`, `0 ≤ 8 Re τ ≤ p`, `|z| ≤ 1`,
   `|z| Re a ≤ 8`:
   `|∫_0^∞ Φ(s+iη)e^{τ(s+iη)²+iz(s+iη)}ds − S₀(a)e^{iza}| ≤ leftErr(a) + e^{Re f(a) − Im(za)} saddleErr(a)`.
5. (Model.) On `Ω(σ₀)`, `|ζ| ≤ 8`:
   `|H_{τ(a)}(ζ/a) − B₀(a) − 2S₀(a) cos ζ| ≤ Cσ⁵e^{−σ}(|B₀(a)| + |S₀(a)|)`.
6. (Collision.) For every `T` there are `τ`, `ζ ≠ 0` with `Re τ > max(T, 0)`,
   `H_τ(ζ) = H_τ'(ζ) = 0`.
7. (Exchange.) For every forward base time `b` off the branch times, `G₊(b)` contains an
   element `σ` and a zero `z` with `σz ∉ {z, −z}`. In particular `G₊(b)` does not preserve the
   pairs.

## Proof

1. `Φ` is even, so `∫_{−∞}^0 = h(τ,−z)`. Cauchy on the rectangle `[0,N] × [0,η]` for
   `F(x) = Φ(x)e^{τx²+izx}`; on the strip `|Φ(x)| ≤ K e^{Re x/2} e^{−a' e^{2 Re x}}`,
   `a' = (π/2)cos 2η`, so the side at `N` tends to `0` and both rays converge.
2. For `v ≥ −1`: `ψ(v) ≤ −v²`, so with `8 Re τ ≤ p`, `Re(Pψ(v) + τv²) ≤ −(7/8)pv²`, and
   `Re(−λv²) ≤ −(7/8)pv²`. `Pψ(v) + τv² + λv² = P(ψ(v) + 2v²)`, `|ψ(v) + 2v²| ≤ 8|v|³e^{2|v|}`.
   With `|e^{w₁} − e^{w₂}| ≤ |w₁ − w₂| e^{max Re}`:
   `|e^{κv+Pψ+τv²} − e^{−λv²}| ≤ (6|v| + 8|P||v|³) e^{6|v|} e^{−(7/8)pv²}`, and
   `e^{6|v|}e^{−(7/8)pv²} ≤ e⁴ e^{−(p/2)v²} e^{−(p/4)v²}` for `p ≥ 18`. Integrate; the Gaussian
   tail `∫_{−∞}^{−1}` is `≤ 1/p`; `∫_ℝ e^{−λv²} = (π/λ)^{1/2}`.
3. `iΦ(0)∫_0^∞ e^{−τv²}dv = (iΦ(0)/2)(π/τ)^{1/2}`. On `[0,η]`: `|Φ(iv)| ≤ K_η`, and
   `|Φ(x) − Φ(0)| ≤ L|x|` on `|x| ≤ 1/2` (mean value on the disc). So
   `|Φ(iv)e^{−zv} − Φ(0)| ≤ C(1 + K_η)v`, `∫_0^∞ v e^{−Re τ v²} = 1/(2 Re τ)`, tail
   `∫_η^∞ e^{−Re τ v²} ≤ 1/(η Re τ)`.
4. `x = a + v`.
   - *Kernel.* For `Re x ≥ 0`, `(π/2)cos(2 Im x)e^{2 Re x} ≥ 1`:
     `|Φ(x) − 4π²e^{9x/2}e^{−πe^{2x}}| ≤ (2B + K)e^{5 Re x/2}|e^{−πe^{2x}}|`: the lower terms of
     `T₁` (`R(w) − 4π²w²` has degree one), and for `n ≥ 2` the term bound with `(m+2)² ≥ 2 + (m+1)`
     and a geometric series of ratio `≤ 1/2`.
   - *Right part* `v ≥ −1`. The leading part is `4π²e^{9a/2+f(a)+iza} ∫_{−1}^∞ e^{κv+Pψ(v)+τv²}dv`,
     `κ = 9/2 + iz`; apply 2. The remainder has modulus
     `≤ C e^{5σ/2} e^{Re f(a) − Im(za)} e⁴ e^{−(p/4)v²}`, and `∫_ℝ e^{−(p/4)v²} ≤ 4/√p`.
   - *Left part* `s = Re x ∈ [0, σ − 1]`. `|Φ(x)| ≤ K_η e^{σ/2}`; `Re τx² = Re τ(s² − η²) −
     2 Im τ·sη` is a convex quadratic in `s`, so `|e^{τx²}| ≤ e^{−η² Re τ} + e^{Re f(a) − p + Re τ}`
     (`τ(a−1)² = f(a) − P + τ`); `|e^{izx}| ≤ e⁸`.
5. 1, 3, 4 at `±z`, `z = ζ/a`. On `Ω(50)`: `η ≥ 1/2`, `cos 2η = sin 2δ ∈ [1/(4σ), 2/σ]`,
   `sin 2η ≥ 1/2`, `πe^{2σ} ≤ 4σp`, `p ≥ 18`, `πe^{2σ}/(8σ²) ≤ Re τ ≤ p/8`, `|τ| ≤ πe^{2σ}`,
   `K_η ≤ 324Bσ³`, `η² Re τ ≥ 3σ`, `|B₀| ≥ |Φ(0)|e^{−σ}`, `|S₀| ≥ e^{7σ/2 + Re f(a)}`. Hence the
   three errors are `≤ Cσ⁵e^{−σ}(|B₀| + |S₀|)`.
6. *The squared ratio.* `λ = τ(2a − 1)`, so
   `(2S₀)² = Q(a) B₀²`, `Q(a) = −64π⁴ e^{9a + 2f(a)} / (Φ(0)²(2a − 1))`: no square roots.
   - *Base point.* For `0 < δ ≤ 1/100` let `η = π/4 − δ`, `a₁ = 1 + η cot 2δ + iη`. Then
     `Re f(a₁) = πe^{2σ}[(σ−1) sin 2δ − η cos 2δ] = 0` and `3/10 ≤ δσ ≤ 7/10`. So
     `|Q(a₁)| = c₀e^{9σ}/|2a₁ − 1|`, `c₀ = 64π⁴/Φ(0)²`, and `|Log Q(a₁)| ≤ |log c₀| + 11σ + π`.
   - *Loop.* `ξ₀(s) = e^{iπs}/4`, `D₁ = f'(a₁) = P₁(2a₁ − 1)`,
     `a(s) = a₁ + h(s)`, `h(s) = (−Log Q(a₁) − 2 Log cos ξ₀(s))/(2D₁)`. Then `a(1) = a(0)`,
     `|h| ≤ Me^{−2σ}`, `M = |log c₀| + 12`. With `K = (1+M)²σ⁴e^{−σ} ≤ 1/300000`:
     `|h|σ ≤ K`, `πe^{2σ}(σ+1)|h|² ≤ K`, `a(s) ∈ Ω(50)`, `Re a(s) ≥ σ − 1`. Exactly,
     `f(a₁+h) − f(a₁) − D₁h = P₁[(e^{2h} − 1 − 2h)(a₁ − 1) + (e^{2h} − 1)h] =: P₁R(h)`, hence
     `Q(a(s)) cos² ξ₀(s) = e^{2P₁R(h) + 9h} (2a₁ − 1)/(2a₁ − 1 + 2h) = 1 + e₂(s)`,
     `|e₂| ≤ 70K ≤ 1/4096`.
   - *Sign.* `u(s) = 2S₀(a(s)) cos ξ₀(s)/B₀(a(s))` is continuous (`Re τ, Re λ > 0`) and
     `u² = 1 + e₂`, so `Re u` never vanishes: `|u − 1| ≤ |e₂|` for all `s`, or `|u + 1| ≤ |e₂|`
     for all `s`. Let `θ = π` in the first case, `θ = 2π` in the second: `sin θ = 0` and
     `|2S₀ cos θ cos ξ₀ + B₀| ≤ |B₀|/4096` for all `s`.
   - *Model*, relative error `1/16384`, and `|S₀| ≤ |B₀|` (from `|Q| ≤ 4`):
     `|H_{τ(a(s))}(ζ/a(s)) − B₀ − 2S₀ cos ζ| ≤ |B₀|/8192`, `|ζ| ≤ 8`. With `ζ = θ + ξ`:
     `(B₀ + 2S₀ cos θ cos ξ) cos ξ₀ = B₀(cos ξ₀ − cos ξ) + (2S₀ cos θ cos ξ₀ + B₀) cos ξ`,
     `cos ξ₀ − cos ξ = 2 sin((ξ+ξ₀)/2) sin((ξ−ξ₀)/2)`, `|sin w| ≥ |w|/2` on `|w| ≤ 1`.
     - annulus `1/16 ≤ |ξ − ξ₀(s)| ≤ 1/8`: `|H| ≥ (9/8192)|B₀|`;
     - centre `ξ = ξ₀(s)`: `|H| ≤ (3/8192)|B₀|`;
     - `ζ = 0`: `(B₀+2S₀)(B₀−2S₀) = B₀²(1 − Q)`, `(1 − Q)cos² ξ₀ = −sin² ξ₀ − e₂`, so
       `|B₀ + 2S₀| ≥ (21/8192)|B₀|` and `H_{τ(a(s))}(0) ≠ 0`.
   - *Tracking.* `γ(s) = τ(a(s))` is a closed path of forward times. If some `γ(s)` is a branch
     time, its multiple zero is not `0`: done. Otherwise `γ` is a forward loop. `H_{γ(0)}` has a
     zero `z₀` with `|a(0)z₀ − θ − ξ₀(0)| < 1/16` (minimum modulus). For its lift `z(s)`,
     `m(s) = a(s)z(s) − θ − ξ₀(s)` is continuous with `|m(s)| ∉ [1/16, 1/8]`, `|m(0)| < 1/16`, so
     `|m(1)| < 1/16`. With `a(1) = a(0)`, `ξ₀(1) = −ξ₀(0) = −1/4`:
     `a(0)(z(1) − z₀) = −1/2 + m(1) − m(0) ≠ 0` and `a(0)(z(1) + z₀) = 2θ + m(1) + m(0) ≠ 0`.
     Detector `exists_multipleZero_ne_zero_of_transports` with `D = {Re τ > max(T, 0)}`; the
     loop lies in `D` because `Re τ(a) ≥ Re a` on `Ω(50)` and `Re a(s) ≥ T + 1`.
7. 6 and `exists_mem_forwardMonodromy_moving_pair`.

## Consequence for the programme

The sufficient condition "`G₊` preserves the pairs `{z, −z}`"
(`riemannHypothesis_of_forwardMonodromy_preserves_pairs`) is false: the forward group is strictly
larger than a group of sign changes, and it is not commutative of exponent two by that route.
The collisions found here are at complex forward times close to the imaginary direction
(`Re τ ≍ e^{2σ}/σ²`, `|τ| ≍ e^{2σ}/σ`), at places `|ζ| ≍ 1/σ`, between the two zeros of
`B₀ + 2S₀ cos(az)` near `az = θ ± ξ₀`; RH concerns collisions at real positive times. Not
decided: which of `θ = π`, `θ = 2π` occurs (the sign of `2S₀/B₀` at the base point).

## Formalization

Modules in `GaloisTheoryOfZeros/`, all compiled, wired into the umbrella; axioms of theorems 6
and 7: `propext`, `Classical.choice`, `Quot.sound`.

| Module | Content | Lean |
|---|---|---|
| `TheHeatFamilyIsAnIntegralThroughTheOriginAndTheSaddle` | theorem 1 | `complexHeat_eq_kernelHalf_add`, `complexHeat_eq_corner` |
| `TheGaussianAtTheSaddleOfTheKernel` | theorem 2 | `norm_integral_saddleIntegrand_sub_le` |
| `TheSegmentThroughTheOriginIsAGaussianAtTheCentreValue` | theorem 3 | `exists_norm_bulkHalf_sub_le` |
| `TheLineThroughTheSaddleIsAGaussianAtTheSaddleValue` | theorem 4 | `norm_lineHalf_sub_le` |
| `TheHeatFamilyAtASaddleTimeIsAConstantPlusACosine` | theorem 5 | `exists_norm_complexHeat_sub_model_le`, `exists_forall_norm_complexHeat_sub_model_le` |
| `ALoopOfSaddlesTurnsTheSquaredRatioOfTheTwoTermsAroundOne` | squared ratio, base point, loop | `two_mul_saddleTerm_sq`, `exists_basePoint`, `saddleRatioSq_add`, `loopSaddle_spec`, `exists_loopSaddle` |
| `ACollisionAwayFromTheCentreExistsAtAForwardTime` | sign, annulus, centre, tracking; theorems 6, 7 | `norm_sub_le_or_norm_add_le`, `le_norm_of_mem_annulus`, `ne_zero_at_centre`, `IsModelLoop.exists_turn`, `IsModelLoop.exists_multipleZero`, `exists_forward_multipleZero_ne_zero`, `exists_mem_forwardMonodromy_moving_a_pair`, `not_forwardMonodromy_preserves_pairs` |

Lean names: `f = saddlePhaseValue`, `P = saddleP`, `τ(a) = saddleTime`, `Q = saddleRatioSq`,
`B₀ = bulkTerm`, `S₀ = saddleTerm`, `Ω(50) = SaddleRegion`, `ξ₀ = turnPoint`, `a(s) = loopSaddle`.

## Log
- 2026-11-13 — created; paper proof written.
- 2026-11-13 — formalized in seven modules; theorem 6 holds with `Re τ` arbitrarily large.
