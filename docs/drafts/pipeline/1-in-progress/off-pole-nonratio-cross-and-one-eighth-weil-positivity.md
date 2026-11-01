# Off-Pole Non-Ratio Cross Norm and Weil Positivity Up to the Eighth-Root Ceiling

- **ID:** off-pole-nonratio-cross-and-one-eighth-weil-positivity
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** docs/reports/review-3110/obstacles-summary.md · Q1 / Σ-2 / Σ-3 (remaining `c⁹ → c⁸`)
- **Statement:** For every `0 < α < 1/8`, eventually in `N` and uniformly across `1 ≤ c ≤ (log N)^α`,
  `completeWeilMatrix tiltedUnitSpline c N` is positive definite on all vectors.

## Goal
Matches the eighth-root receiver (`RH ⇔` eventual sign at every `α > 1/8`): the unconditional
exponent would equal the RH-detection exponent of the tilted spline, so
`log edge(N)/log log N → 1/8` along falsifying subsequences under `¬RH`.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Approach
The `1/9` proof loses `c⁹` (vs. the necessary `c⁸`) at three places; each must drop to `c⁸·polylog c`.

1. **Two-region reserve (`K c⁹ ≤ θ₁ log N`).** On `w ∈ V_{R₁}^⊥`, reserves are `≍ log N · P`
   (prefix `[1, M]`, `M = N/L_c`) and `≍ (log N / c⁷) S` (terminal `(M, N]`). The prefix→terminal
   non-ratio block `NR_{PT}` has Schur row `≍ c` (prefix) and column `≍ c log N` (terminal), hence
   `‖NR_{PT}‖² ≲ c² log N`; paying it needs `c² log N ≤ log N · log N/c⁷`, i.e. `c⁹ ≤ log N`.
   *Tightness:* the column `Σ_{|j|≤ec} Σ_{k | n−j} Λ(k) ≈ 2ec log n` is pointwise sharp, and the
   Schur test is attained near the Perron vector `n ↦ n^{−1/2}`, i.e. the pole mode `v_{1,N}`.
2. **Band–terminal cross (`c⁹(1+log c)/log N`).** Same block, paired against `u ∈ V_{R₁} ∩ V_1^⊥`.
3. **Inverse-energy residual sum (`Σ_{m≤Q₁} ‖r_m‖²/E_m ≪ c⁹/log N`).** `‖r_m‖² ≍ c²/log N` comes
   from near-center/near-gamma rows on `N/(R_c+1) < n ≤ N`; on `[1, M]` those rows vanish.

**Terminal-pole-orthogonality is not enough (refuted).** The bound
`|⟨NR_PT x, y⟩|² ≤ C c (1+log c)^A log N ‖x‖²‖y‖²` for `y ⊥ v_{1,N}` is false. Take `x = P v₁`
(prefix pole) and `y(n) = n^{−1/2}(log n − μ_S)` on `S = (M, N]`, with `μ_S` the `1/n`-weighted mean,
so `y ⊥ v_{1,N}`. The prefix-pole column is exact, `Σ_{k | n'} Λ(k) = log n'`, so
`Σ_m NR(m,n) m^{−1/2} ≈ n^{−1/2} |W(n)| log N` with window `|W(n)| ≈ 2cn/N`. The pairing reads the
*unweighted* moment `(c/N) Σ_{n∈S} Y(n) ≍ c log c`, not the pole moment `Σ Y(n)/n = 0`:
`⟨NR_PT x, y⟩ ≍ c log c log N`, `‖x‖² ≍ log N`, `‖y‖² ≍ (log c)³`, ratio to the bound `≍ c/(log c)^{A+1}`.
No PNT enters; only the divisor identity. The orthogonality that can work is the global one below.

## Global orthogonality and the coherent cross term

The actual condition is `w ⟂ v₁` before the prefix–terminal split. Neither
piece is separately pole-orthogonal. If `p=P v₁` and `q=S v₁`, then
`⟨Pw,p⟩=−⟨Sw,q⟩`; hence
`|⟨Pw,p/‖p‖⟩|≤(‖q‖/‖p‖)‖Sw‖`.
For cutoff `M≈N/c`, the ratio is `O(sqrt(log c/log N))`.

A second candidate is therefore an input-pole decomposition
`NR_PT = a ⊗ (p/‖p‖) + E`, with
`‖a‖=O(c sqrt(log N))` and `‖E‖²=O(c·polylog(c)·log N)`.
Global orthogonality would reduce the coherent cross payment to
`O(c sqrt(log c))‖Sw‖²`; the terminal reserve then asks only for
`c⁸ sqrt(log c)=o(log N)`. The remainder has the desired eighth-power
Schur cost. The divisor-jet cancellation with the near-Gamma row is the
available source identity for identifying `a`.

This decomposition is unproved. The earlier output-pole projection alone
does not supply it; the coherent output need not be proportional to `q`.
Band–terminal and inverse-energy residual improvements remain required.

## Structure of `NR_PT` (paper, heuristic where marked)

- **The coherent part is rank one.** `NR_PTᵀ â ∝ p` with `â(n) ∝ √n` on `S`, because
  `Σ_{k≤X} Λ(k) k ≈ X²/2`. Star poles and low conductors are coherent only through their overlap with
  `p`: `NR_PT(P x_d) ≈ (c log N/d) â`. So `a = σ â`, `σ ≍ c √log N`.
- **The remainder on `x ⊥ p` is a shifted-correlation problem.** With `X(m) = √m x(m)` and
  `F = Λ ∗ X`, `‖NR_PT x‖² ≈ Σ_{|h|≤2c} ω_h Σ_{n∈S} F(n)F(n−h)/n`, `Σ ω_h ≍ c²`. The `h = 0` term is
  `≤ 2c log c log N ‖x‖²` (Cauchy–Schwarz over `k | n`), which is the target level. The `h ≠ 0`
  terms count prime pairs `km − k'm' = h`; no unconditional bound with a saving is available.
- **What suffices.** With reserves `θ log N · P` and `κ log N/c⁷ · S`, positivity needs
  `‖E‖² ≤ c (log N)^{1+δ}`, `δ = 1 − 8α`: a saving `(log N)^{9α−1}` over the trivial `c² log N`.
- **Terminal reserve is small on two families.** `archForm` of a terminal atomic test is
  `≈ ∫ |φ̂(wξ)|² |D_y(ξ)|² Θ(ξ) dξ`, `D_y(ξ) = Σ y_n n^{−iξ}`. It is `≈ (κ/c⁷) log N` per unit mass
  for Mellin-smooth `y` (`|ξ| ≲ 1`) and for destructive-overlap `y` (local period `< c`, where
  `φ̂(wξ)` is small). It is `≈ c log|t|` per unit mass at Mellin frequency `|t| ≪ N/c`.

## Route (open steps)

1. Split terminal `y` at Mellin frequency `T₀ = exp(C c log c)`. The high part is paid by
   `c log T₀ ≥ C' c² log c` against the trivial `‖NR_PT‖² ≍ c² log N log c` (open: the arch
   inequality per Mellin band, including destructive-overlap patterns).
2. Low part: `NR_PTᵀ y_low = (coherent)·p + O(PNT error)` row by row. Rows `m ≤ N/X₀`,
   `log X₀ ≍ (log N)^{1/4}`: Route-T twisted Chebyshev (zero-free width
   `≳ (log t)^{−9/10}(log log t)^{−2}`, `RHTower.Sieve.exists_norm_partialSum_vonMangoldtTwist_routeT_uniform`)
   gives relative error `exp(−log X/(log T₀)^{0.9+})`. Remaining rows cost `c² log X₀/log c` in total.
   Open: near-orthogonality across Mellin bands on the discrete prefix (Gallagher type).
3. Band–terminal cross: band vectors carry only `log Q₁` reserve, so the high-frequency trade of
   step 1 does not pay it; needs the coherent structure of `NR_PT` on conductor packets (open).
4. `y–z` Schur: localize `r_m` on the terminal and pay `|⟨r₁, z_S⟩|²` with the terminal reserve:
   `c²/log N ≤ c^{−7} · κ log N/c⁷` is `c⁸ ≲ log N` (needs the reserve of step 1 inside the Schur).
5. Elementary: the tail–tail column is
   `Σ_{k ≤ eL} Λ(k)(2ec/k + 1) = O(c(1 + log c))` (multiples of `k` in a window), not `O(c²)`.

## No-go closure
- **Killed:** terminal-pole-orthogonal smallness of `NR_PT` (counterexample above).
- **Positive survivor:** rank-one coherent structure `NR_PT ≈ σ â ⊗ p̂ + E`; exact prefix-pole
  column law from `Σ_{k|n} Λ(k) = log n`; target `‖E‖² ≤ c (log N)^{1+δ}`.
- **Status:** paper only; no Lean.
