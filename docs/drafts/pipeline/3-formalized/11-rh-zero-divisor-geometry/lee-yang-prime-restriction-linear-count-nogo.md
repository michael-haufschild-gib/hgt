# Lee–Yang restrictions in prime fields have linear zero counts: no stability route reaches Ξ

- **ID:** lee-yang-prime-restriction-linear-count-nogo
- **Stage:** 3-formalized (Lean, standard axioms; STATUS MUST-806)
- **Type:** THEOREM (no-go for the whole prime-variable stability route class)
- **Kills (as stated):** `prime-kirchhoff-matroid-half-plane-rh` (OPEN CORE D),
  `prime-source-ferromagnetic-ising-lee-yang-limit-rh`, and every route whose finite approximants are
  multivariate Lee–Yang / half-plane-stable polynomials evaluated at the prime fields
  `u_p(z) = e^{−iz log p}` and converging locally uniformly to a zero-free factor times `XiC`.
- **Source:** geometric loop G75 (my 2026-10-07 note "density law … design rule" was wrong: the
  discrepancy is bounded by the density, which makes it an obstruction).

## Statement

**Lee–Yang datum.** A polynomial `P ∈ ℂ[u₁,…,u_n]` with multidegree `d` (`dⱼ = deg_{uⱼ} P`) such that
`P ≠ 0` on the open polydisk `𝔻ⁿ` and its reflected polynomial `P^♯(v) = v^d · conj P(1/v̄)` is
also `≠ 0` on `𝔻ⁿ`. Equivalently, `P ≠ 0` on `𝔻ⁿ` and on `(ℂ∖𝔻̄)ⁿ` with top coefficient `c_d ≠ 0`.
Frequencies `λⱼ > 0`, and `f(t) = P(e^{−iλ₁t},…,e^{−iλ_n t})`.

**Lemma (linear count).** All zeros of `f` are real. For real `a < b` with `f(a)f(b) ≠ 0`,
the number `N(a,b)` of zeros in `(a,b)`, with multiplicity, satisfies

`|N(a,b) − (b−a)·D| ≤ 2S`,  with `D = (1/2π)Σⱼ dⱼλⱼ` and `S = Σⱼ dⱼ`.

**Theorem (no-go).** Let `λ₀ > 0`. Suppose there are Lee–Yang data `(Pₙ, λ⁽ⁿ⁾)` with all frequencies
`≥ λ₀`, entire zero-free `hₙ` and `E`, such that `hₙ fₙ → E · XiC` locally uniformly on `ℂ`.
This is impossible, unconditionally.

## Proof

**Reality.** For `Im t < 0` every `|uⱼ| = e^{λⱼ Im t} < 1`, so `f(t) = P(u) ≠ 0`. For `Im t > 0`
every `|uⱼ| > 1`, and `P(u) = u^d conj P^♯(1/ū)` with `1/ū ∈ 𝔻ⁿ`, so `f(t) ≠ 0`.

**Count.** Apply the argument principle to the rectangle `[a,b]×[−η,η]`. Every zero is real, so the
enclosed count is `N(a,b)` for every `η > 0`. The vertical edges contribute `o(1)` as `η → 0`, since
`f(a), f(b) ≠ 0`. Write `w_t = u(t)e^{−λη}`; for real `t`, `|uⱼ(t)| = 1`, so `w_t ∈ 𝔻ⁿ`.

- *Lower edge.* `f(t − iη) = P(w_t)`. For `w ∈ 𝔻ⁿ` the univariate polynomial `q_w(s) = P(sw)` has
  degree `≤ S` and no zero on `[0,1]`. So `Λ(w) = Log P(0) + ∫₀¹ q_w'/q_w ds` is a continuous logarithm
  of `P` along `t ↦ w_t`: `e^{Λ(w_t)} = P(w_t)`, and differentiating in `t` gives
  `Δ_{[a,b]} arg f(t−iη) = Im Λ(w_b) − Im Λ(w_a)`. Factor `q_w = c ∏(s − r_k)`. Each
  `Im ∫₀¹ ds/(s − r_k)` is the angle subtended at `r_k` by `[0,1]`, hence `< π`. So
  `|Im Λ(w) − arg P(0)| ≤ πS`, and the lower-edge variation is `≤ 2πS` in absolute value.
- *Upper edge.* Since `|u(t)| = 1`, `f(t + iη) = P(u e^{λη}) = u(t)^d e^{⟨d,λ⟩η} conj P^♯(w_t)`. So
  `Δ arg f(t+iη) = −⟨d,λ⟩(b−a) − (Im Λ^♯(w_b) − Im Λ^♯(w_a))`, where the second term is again
  `≤ 2πS` in absolute value.
- Combining the edges: `2π N(a,b) = Δ_lower − Δ_upper + o(1) = ⟨d,λ⟩(b−a) + O(4πS)`.

**No-go.**
- With all `λⱼ ≥ λ₀` we have `D ≥ λ₀S/2π`, i.e. `S ≤ κD` with `κ = 2π/λ₀`. Put `n(T) = N(−T,T)`.
  Then `D(2T − 2κ) ≤ n(T) ≤ D(2T + 2κ)`.
- Take non-ordinates `T₁ < T₀` with `T₁ > κ`. Hurwitz on the rectangles `[−T,T]×[−1,1]` (no zero of
  `XiC` on their boundaries; all zeros of `hₙfₙ` are real) gives, for large `n`,
  `nₙ(T) = n_Ξ(T) := #{zeros of XiC with |Re| ≤ T}`.
- Hence `n_Ξ(T₀)(2T₁ − 2κ) ≤ D·(2T₀+2κ)(2T₁−2κ) ≤ n_Ξ(T₁)(2T₀ + 2κ)`.
- By Riemann–von Mangoldt (corpus `exists_xiZeroCount_close`), `n_Ξ(T) = (T/π)log T·(1+o(1))`. With
  `T₁ = √T₀` the inequality reads `log T₀ ≤ ½ log T₀·(1 + o(1))`, which is false for large `T₀`. ∎

## What it says

- **Must:** a stability or Lee–Yang mechanism that produces `Ξ` as a limit must use variables whose
  frequencies accumulate at `0`. In arithmetic terms: log-ratios `log((m+1)/m)` of near-coincident
  integers, i.e. the additive structure `m ↦ m+1`, not prime fields alone. Prime-field stability
  produces zero sets of asymptotically constant density (bounded relative discrepancy). `Ξ`'s
  density grows like `log T`, and its counting function has `T log T` curvature.
- **Cannot:** the bound does not exclude Lee–Yang data with frequencies `→ 0`. For example,
  `∏ₖ (1 − e^{iθₖ}((mₖ+1)/mₖ)^{−iz})` approximates any real-rooted polynomial locally uniformly.
  It is also silent on mechanisms that are not Lee–Yang restrictions (matching polynomials in a
  rotated variable, Eulerian limits).

## Lean

| Module | Content |
|---|---|
| `HTGeometry/PolynomialSegmentArgument` | `abs_integral_im_logDeriv_le` (segment bound), `exp_log_add_integral_logDeriv`, `hasDerivAt_of_exp_eq` |
| `HTGeometry/PolydiskRadialLogarithm` | `radialLog`, `exp_radialLog`, `abs_im_radialLog_sub_le`, `continuous_radialLog_comp` |
| `RHTower/LeeYangRestrictionZeroCount` | `LeeYangDatum`, `dualPoly`, `eval_eq_prod_mul_conj_dual`, `restr_im_eq_zero_of_eq_zero`, `integral_lower_edge`, `integral_upper_edge`, `abs_zeroCount_sub_le` (linear count, bound `2S`) |
| `RHTower/LeeYangPrimeStabilityNoGo` | `LYApprox`, `abs_zeroSumBall_sub_le`, `zeroSumBall_mul_le_of_tendsto` (quasi-linear limit counts), `xiZeroCount_le_zeroSumBall`, **`not_tendsto_lyApprox_mul_XiC`** |

All four modules are wired into their umbrellas, and `#print axioms` shows only `propext`,
`Classical.choice`, `Quot.sound`. The formal Lee–Yang datum asks for nonvanishing of `P` and of
`P^♯` on the open polydisk. For `P^♯` this includes points with zero coordinates, i.e. the top
coefficient `c_D ≠ 0`. Corpus inputs: `exists_entire_argument_variation_rectangle`,
`eventually_zeroSumBall_eq_of_tendstoLocallyUniformly`, `exists_zeroSet_zeroSumBall`,
`exists_xiZeroCount_close`, `xiZeroCount_eq_pos_sum`, `analyticOrderAt_XiC_centeredCoordinate`.

## Gates
- [x] 0 → 1
- [x] 1 → 2 (paper proof above)
- [x] 2 → 3 formalized (2026-10-07)
- [ ] 3 → 4

## Log
- 2026-10-07 — found while testing the density law of the HPP matroid card; paper proof complete.
- 2026-10-07 — formalized (MUST-806). The vertical edges are handled by `η → 0`, which avoids
  the multivariable homotopy. Arguments are lifted along radial segments (`radialLog`), and the
  monodromy is controlled by the one-variable segment bound.
