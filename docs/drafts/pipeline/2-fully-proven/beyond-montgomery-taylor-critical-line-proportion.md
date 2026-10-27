# Strictly Beyond the Montgomery–Taylor `67.25%` Critical-Line Zero Proportion via Disjoint-Pair Schur–Jensen Pinching and Non-Lattice Gabor Kernel Incommensurability

- **ID:** beyond-montgomery-taylor-critical-line-proportion
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `RHTower` · `Zeta23` Theorem D zero-side Schur–Jensen seam
- **Statement:** Unconditionally for `ζ(s)` (`Mathlib.riemannZeta`), for every `ε > 0` there exists `T₀` such that for all `T ≥ T₀`, `(HD(1) + 1/10^8 - ε) N(T, 2T) ≤ N₀^simple(T, 2T)` and `(HD(1) + 1/10^8 - ε) N(0, T) ≤ N₀^simple(0, T)` (and a fortiori for `N₀*(0, T)` and `N₀(0, T)`), and `(GD(1) + 1/(2·10^8) - ε) N(0, T) ≤ N_d(0, T)`, where `HD(1) = 3/2 - cot(1/√2)/√2 = 0.6725007036…` and `GD(1) = (HD(1) + 1)/2 = 0.8362503518…`.

## Goal
Break the unconditional `HD(1) = 0.6725007036…` world-record simple-critical-line zero proportion of Alpöge–Furman (`arXiv:2609.02882`, formalized in `Zeta23.ThmD.thmD₀_simple_mult`) and the `GD(1) = 0.8362503518…` distinct-zero proportion (`Zeta23.ThmD.thmD₀_dist_mult`) **strictly below the pair-correlation barrier (`λ < 1`)**, requiring zero new prime-side off-diagonal estimates.

## Gates
- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, hostile Phase-4 audit (`SURVIVES PRELIMINARY ATTACK`)
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorems `RHTower.beyond_HD_one_simple_critical_dyadic`, `RHTower.beyond_HD_one_simple_critical_cumulative`, `RHTower.beyond_HD_one_critical_cumulative`, `RHTower.beyond_GD_one_distinct_cumulative`, `RHTower.HD_one_add_pos_le_liminf_xiSimpleCriticalRatio`

## Approach
In `Zeta23.ZeroSide.RankTraceMult`, Lemma R bounds the eigenvalues `μ_i(M)` of the on-line Gram matrix `M = Wᴴ W` along the piecewise-quadratic convex function `g_c(t) = t² - c t - ((t - c)_+)²` (`k_c(t) = c t - g_c(t) = c² - ((c - t)_+)²`) by dropping the Schur–Jensen pinching slack `∑_i g_c(μ_i(M)) - ∑_z g_c(M_{zz}) ≥ 0`. Crucially:
1. Prior `RHTower` refinements (`ClusteredBlockPacket.lean`) moved representatives `q ∈ S₁` into the Lamzouri absorbing subspace (`c² = 4` ceiling), which pays `+1` per representative and only gains when `|⟨v̂_x, v̂_q⟩| > 1/√2` (very close pairs `Δ ≪ 1`).
2. By contrast, for **any two distinct simple critical zeros `x, y ∈ S₁`** (`m_x = m_y = 1`) with normalized frame vectors `‖v̂_x‖² ≤ 1` and `‖v̂_y‖² ≤ 1`, **every** orthogonal rotation `(v̂'_x, v̂'_y) = (α v̂_x + β v̂_y, -β v̂_x + α v̂_y)` (`α² + β² = 1`) preserves `P = W Wᴴ` identically AND satisfies `‖v̂'_x‖² + ‖v̂'_y‖² = ‖v̂_x‖² + ‖v̂_y‖² ≤ 2 ≤ c` for every `c ≥ 2`. Hence **neither rotated norm ever crosses the kink `t = c` of `k_c`**, so `k_c(t) = 2 c t - t²` remains purely quadratic on both coordinates! Choosing `(α, β)` to diagonalize the real `2 × 2` Gram block extracts the exact unconditional quadratic slack **`+2 ⟨v̂_x, v̂_y⟩²`** for *every* disjoint pair, regardless of how small `|⟨v̂_x, v̂_y⟩|` is.
3. Why isn't `⟨v̂_x, v̂_y⟩ = 0` on all short pairs? For the flat-top boxcar window, `(φ²)^` is the cardinal sine `sinc(π Δ)`, whose zeros form the **exact additive lattice `ℤ \ {0}`**, so an adversary can place all simple critical zeros on `2π/L · ℤ` (`s₁ = (2/3) N`, pairwise orthogonal) with zero off-diagonal slack. For the **Montgomery–Taylor cosine window** `φ_D(u)² = cos(√2 λ u / L) · taper(u)²`, the untapered normalized correlation kernel is
   $$K_\lambda(\Delta) = \frac{a}{2 \sin a}\left(\operatorname{sinc}(\pi \Delta - a) + \operatorname{sinc}(\pi \Delta + a)\right) = \frac{a \big(\pi \Delta \cos a \sin(\pi \Delta) - a \sin a \cos(\pi \Delta)\big)}{\sin a \cdot ((\pi \Delta)^2 - a^2)}, \quad a = \frac{\lambda}{\sqrt{2}},$$
   whose roots near `λ = 1` are **additively incommensurable** (`r₁ ≈ 1.0573`, `r₂ ≈ 2.0301`, `2 r₁ ≈ 2.1146 > r₂`, `r₁ + r₂ ≈ 3.0873 > 3`), AND simultaneously `Zeta23.ThmD.thmD₀_simple_mult` already forces **`s₁ ≥ (HD(1) - o(1)) N > (2/3 + 43/7500 - o(1)) N`**, strictly exceeding the `2/3` triple-packing threshold at span `ℓ = 3`!

---

## Complete Dependency-Closed Paper Proof (`[PROVED HERE]`)

### Lemma 1 (Disjoint-Pair Unitary Column Rotation for Lemma R; `[PROVED HERE]`)
Let `𝕜` be `ℝ` or `ℂ` (`[RCLike 𝕜]`), `n, ι` finite index types, `m : ι → ℝ` with `∀ j, 0 ≤ m j`, `v : ι → n → 𝕜` with `∀ j, xsq v j ≤ 1` (`xsq v j := ∑_a ‖v j a‖²`), and `Q : Matrix n n 𝕜` Hermitian with `posIndex hQ ≤ b`. Let `c ≥ 2` be real.
Suppose `r : Finset κ` indexes a family of pairs `(x_p, y_p)` (`p ∈ r`) in `ι` such that:
1. For every `p ∈ r`, `x_p ≠ y_p` and `m (x_p) = 1` and `m (y_p) = 1`;
2. Pairwise disjointness: for distinct `p, q ∈ r`, `{x_p, y_p} ∩ {x_q, y_q} = ∅`.

Define the real inner product of each pair `p ∈ r`:
$$\rho_p := \sum_{a \in n} \operatorname{Re}\!\big(v(x_p, a) \overline{v(y_p, a)}\big) \in \mathbb{R}.$$
Then for `P := Pmat m v = Wmat m v * (Wmat m v)ᴴ`:
$$2 c \operatorname{rtrace}(P + Q) - \operatorname{frobSq}(P + Q) + 2 \sum_{p \in r} \rho_p^2 \le \sum_{j \in \iota} k_c(m_j) + c^2 b.$$

**Proof.**
1. **Single-pair algebraic rotation.** Let `u, w : n → 𝕜` satisfy `A := ∑_a ‖u a‖² ≤ 1` and `B := ∑_a ‖w a‖² ≤ 1`, and set `ρ := ∑_a Re(u a * conj(w a))`. For any real numbers `α, β ∈ ℝ` with `α² + β² = 1`, define `u' a := α u a + β w a` and `w' a := -β u a + α w a`.
   - For every `a, b ∈ n`, expanding products over `𝕜` using `α, β ∈ ℝ` gives
     $$u'(a)\overline{u'(b)} + w'(a)\overline{w'(b)} = (\alpha^2 + \beta^2)\big(u(a)\overline{u(b)} + w(a)\overline{w(b)}\big) = u(a)\overline{u(b)} + w(a)\overline{w(b)}.$$
   - Setting `A' := ∑_a ‖u' a‖² ≥ 0` and `B' := ∑_a ‖w' a‖² ≥ 0`, expanding `‖α u a + β w a‖² = α² ‖u a‖² + β² ‖w a‖² + 2 α β Re(u a * conj(w a))` and summing over `a ∈ n` yields:
     $$A' = \alpha^2 A + \beta^2 B + 2 \alpha \beta \rho, \qquad B' = \beta^2 A + \alpha^2 B - 2 \alpha \beta \rho.$$
     Hence `A' + B' = (α² + β²)(A + B) = A + B ≤ 2`, and `A' - B' = (α² - β²)(A - B) + 4 α β ρ`.
   - Choose `(α, β)` explicitly as follows: let `D := √((A - B)² + 4 ρ²) ≥ 0`.
     * If `D = 0`, then `A = B` and `ρ = 0`; set `α = 1, β = 0`. Then `α² + β² = 1` and `(A' - B')² = 0 = (A - B)² + 4 ρ²`.
     * If `D > 0`, note `|A - B| ≤ D`, so `u_+ := (1 + (A - B)/D)/2 ≥ 0` and `u_- := (1 - (A - B)/D)/2 ≥ 0`. Set `α := √u_+` and `β := σ √u_-` where `σ = 1` if `ρ ≥ 0` and `σ = -1` if `ρ < 0` (`σ² = 1`, `σ |ρ| = ρ`). Then:
       - `α² + β² = u_+ + u_- = 1`,
       - `α² - β² = u_+ - u_- = (A - B)/D`,
       - `2 α β = 2 σ √(u_+ u_-) = 2 σ √((1 - (A - B)²/D²)/4) = 2 σ √(ρ² / D²) = 2 σ |ρ| / D = 2 ρ / D`.
       Hence `A' - B' = ((A - B)² + 4 ρ²) / D = D`, so `(A' - B')² = D² = (A - B)² + 4 ρ²`.
   - In both cases, `A'² + B'² = ((A' + B')² + (A' - B')²)/2 = ((A + B)² + (A - B)² + 4 ρ²)/2 = A² + B² + 2 ρ²`.
   - Since `0 ≤ A'`, `0 ≤ B'`, and `A' + B' ≤ 2 ≤ c`, both `A' ≤ c` and `B' ≤ c`. Also `A ≤ 1 ≤ c` and `B ≤ 1 ≤ c`. By `Zeta23.ZeroSide.RankTraceMult.kc_of_le` (`k_c(t) = 2 c t - t²` for `t ≤ c`) and `kc_mono` (`k_c(A) ≤ k_c(1)`, `k_c(B) ≤ k_c(1)` since `c ≥ 2 > 0`):
     $$k_c(A') + k_c(B') = 2 c (A' + B') - (A'^2 + B'^2) = 2 c (A + B) - (A^2 + B^2 + 2 \rho^2) = k_c(A) + k_c(B) - 2 \rho^2 \le 2 k_c(1) - 2 \rho^2.$$

2. **Simultaneous rotation on pairwise disjoint pairs.** By pairwise disjointness of `{x_p, y_p}` (`p ∈ r`), define `v' : ι → n → 𝕜` to equal the rotated pair `(u'_p, w'_p)` on `{x_p, y_p}` for each `p ∈ r`, and `v' j := v j` on `S_rest := univ \ ⋃_{p ∈ r} {x_p, y_p}`.
   - Since `m(x_p) = m(y_p) = 1` for every `p ∈ r`, decomposing `∑_{j ∈ ι} m_j v'(j, a) conj(v'(j, b))` into `S_rest` plus `∑_{p ∈ r}` over `{x_p, y_p}` (`x_p ≠ y_p`) shows `Pmat m v' = Pmat m v = P` (`Zeta23.ZeroSide.RankTraceMult.Pmat_apply`).
   - Applying `Zeta23.ZeroSide.RankTraceMult.rank_trace_mult_k` (`0 < 2 ≤ c`) to `(m, v')` gives:
     $$2 c \operatorname{rtrace}(P + Q) - \operatorname{frobSq}(P + Q) \le \sum_{j \in \iota} k_c(m_j \cdot \operatorname{xsq}(v', j)) + c^2 b.$$
   - Splitting `∑_{j ∈ ι}` into `S_rest` and `∑_{p ∈ r}` over `{x_p, y_p}`:
     * For `j ∈ S_rest`, `v' j = v j`, so `m_j · xsq(v', j) ≤ m_j` and `k_c(m_j · xsq(v', j)) ≤ k_c(m_j)` by `kc_mono`.
     * For `p ∈ r`, `m(x_p) = m(y_p) = 1`, so `k_c(m(x_p) xsq(v', x_p)) + k_c(m(y_p) xsq(v', y_p)) ≤ k_c(m(x_p)) + k_c(m(y_p)) - 2 ρ_p²`.
   - Recombining `S_rest` and `⋃_{p ∈ r} {x_p, y_p}` yields the claimed inequality. ∎

**Immediate Block & Seam Corollaries (`[PROVED HERE]`):**
Instantiating Lemma 1 on `ZeroBlockData` (`Zeta23/ZeroSide/Mult.lean`) with `vhat c_0` (`c_0 = a L² > 0`) and `Pr : D.PairReps`, where `x_p, y_p ∈ D.S₁` (`m = 1`, on-line so `D.v z k` is real), and decorating with `Zeta23.Assembly.ctr_sub_frobSq_perturb` exactly as in `Zeta23.Assembly.seamA_mult2` / `seamA_mult3` gives, for any family `r` of pairwise disjoint pairs `(x_p, y_p)` in `(blockData Z T P hconj).S₁`:
- **(`c = 2`, simple critical zeros):**
  $$4 \operatorname{rtrace}(\hat{G}_z) - \operatorname{frobSq}(\hat{G}_z) - 2 N(T, 2T) - 3 N(I' \setminus I) - B(4 + 2\sqrt{\operatorname{frobSq}(\hat{G}_z)} + B) + 2 \sum_{p \in r} \rho_p^2 \le N_0^{\text{simple}}(T, 2T),$$
- **(`c = 3`, distinct zeros):**
  $$6 \operatorname{rtrace}(\hat{G}_z) - \operatorname{frobSq}(\hat{G}_z) - 3 N(T, 2T) - 5 N(I' \setminus I) - B(6 + 2\sqrt{\operatorname{frobSq}(\hat{G}_z)} + B) + 2 \sum_{p \in r} \rho_p^2 \le 2 N_d(T, 2T),$$
where `B = θ₀ / (a L)` and `ρ_p = (a L²)⁻¹ ∑_{k < d} φ̂_R(γ_{x_p} - τ_k) φ̂_R(γ_{y_p} - τ_k)`.

---

### Lemma 2 (Uniform Bulk Finite-Grid Overlap Approximation to the Untapered Cosine Kernel; `[PROVED HERE]`)
Let `P : Params` satisfy `P.Valid` (`0 < λ ≤ 1`, `1 ≤ w`). Define the untapered cosine kernel numerator and normalized kernel for `λ ∈ (0, 1]` and `Δ ∈ ℝ`:
$$N_\lambda(\Delta) := \int_{-1/2}^{1/2} \cos(\sqrt{2}\lambda v) \cos(2\pi \Delta v)\, dv, \qquad a_*(\lambda) := \int_{-1/2}^{1/2} \cos(\sqrt{2}\lambda v)\, dv = \frac{\sin(\lambda/\sqrt{2})}{\lambda/\sqrt{2}}, \qquad K_\lambda(\Delta) := \frac{N_\lambda(\Delta)}{a_*(\lambda)}.$$
At height `T` with `T ≥ 16`, `8 w ≤ L := P.L T`, `4 w / a_*(λ) ≤ L / 2`, and `2π / L ≤ √T / 2`, let `Q := P.atD T` (`Q.phi T = P.phiD T`, `Q.L T = L`, `a_D := Q.a T`).
For any two on-line zeros `x, y ∈ (blockData Z T Q hconj).onLine` whose ordinates `γ_x := Im x`, `γ_y := Im y` lie in the bulk sub-window `[T + √T, 2T - √T]`, let `Δ := (L / (2π)) (γ_x - γ_y)` and let
$$\rho(x, y) := \frac{1}{a_D L^2} \sum_{k=0}^{d-1} \operatorname{vHatR}(\varphi_D)(\gamma_x - \tau_k) \operatorname{vHatR}(\varphi_D)(\gamma_y - \tau_k).$$
Then:
$$\big|\rho(x, y) - K_\lambda(\Delta)\big| \le \frac{4 (c_{DT} / w)^2}{a_D T} + \frac{8 w}{a_*(\lambda) L},$$
where `c_{DT} = cDT P.ϱ P.lam` is the `AdmWindow` second-derivative constant of `BridgeD.admWindow_params`. In particular, as `T → ∞` at fixed `P`, the right-hand side tends to `0` (`≤ 1 / 500` eventually, uniformly over all bulk pairs `x, y`).

**Proof.**
Let `φ := P.phiD T`, so `hW : AdmWindow φ L w c_{DT}` holds (`BridgeD.admWindow_params`). Note `a_D = L⁻¹ ∫ φ² > 0` (for `L` large, `a_D ≥ 1/2` by `tendsto_aD` / `aD_close`).
1. **Full-grid identity (`k ∈ ℤ`).** By `AdmWindow.hasSum_vHatR_mul T γ_x γ_y`,
   $$\sum_{k \in \mathbb{Z}} \operatorname{vHatR}(\varphi)(\gamma_x - \tau_k) \operatorname{vHatR}(\varphi)(\gamma_y - \tau_k) = L \cdot \operatorname{VPhiR}(\varphi)(\gamma_x - \gamma_y),$$
   where `VPhiR(φ)(r) = Re ∫_ℝ φ(u)² e^{i r u} du = ∫_{-L/2}^{L/2} φ(u)² cos(r u) du` (since `φ` vanishes outside `[-L/2, L/2]`). Dividing by `a_D L²` gives `I_full(x, y) := VPhiR(φ)(γ_x - γ_y) / (a_D L)`.
2. **Grid-tail bound (`k ∉ [0, d)`).** Let `s := image (coe : Fin d → ℤ) univ = Finset.Ico 0 d`.
   - For `γ ∈ [T + √T, 2T - √T]` and `k ∈ ℤ \ s`:
     * If `k < 0`, then `k ≤ -1`, so `τ_k = T + k(2π/L) ≤ T - 2π/L < T`, whence `γ - τ_k ≥ √T ≥ √T / 2`.
     * If `k ≥ d`, since `d = ⌊L T / (2π)⌋₊`, we have `d · (2π/L) > T - 2π/L`, so `τ_k ≥ T + d(2π/L) > 2T - 2π/L ≥ 2T - √T / 2`, whence `τ_k - γ ≥ √T / 2`.
     Thus `(γ - τ_k)² ≥ T / 4` for all `k ∉ s`.
   - Since `φ ≥ 0` everywhere (`hW.nonneg`) and `φ(u) = 0` for `|u| ≥ L/2` (`hW.support`), every `u` with `|u| ≥ L/2` is a global minimum of `φ`, so `deriv φ u = 0` (`IsLocalMin.deriv_eq_zero`). For `u ∈ [-L/2, L/2]`, `φ ∈ C²` (`hW.contDiff`) and FTC from `-L/2` (`deriv φ (-L/2) = 0`) give `|deriv φ u| = |∫_{-L/2}^u deriv(deriv φ)| ≤ ∫_ℝ |deriv(deriv φ)| ≤ c_{DT} / w` (`hW.l1_deriv2`).
   - By `Zeta23.paperFT_deriv`, `paperFT (deriv φ) r = -(i r) paperFT φ r`, so `‖paperFT (deriv φ) r‖² = r² ‖paperFT φ r‖² ≥ r² (vHatR φ r)²`.
   - Applying `RHTower.sum_norm_sq_paperFT_grid_le` to `ψ = deriv φ` on any finite set `t ⊆ ℤ \ s` gives:
     $$\frac{T}{4} \sum_{k \in t} \operatorname{vHatR}(\varphi)(\gamma - \tau_k)^2 \le \sum_{k \in t} (\gamma - \tau_k)^2 \operatorname{vHatR}(\varphi)(\gamma - \tau_k)^2 \le L \int_{-L/2}^{L/2} (\operatorname{deriv}\varphi(u))^2\, du \le L^2 (c_{DT}/w)^2.$$
   - Dividing by `(T/4) a_D L²` shows that for both `γ = γ_x` and `γ = γ_y`, `∑_{k ∈ t} F_γ(k)² ≤ 4 (c_{DT}/w)² / (a_D T)`, where `F_γ(k) := vHatR(φ)(γ - τ_k) / √(a_D L²)`. By `2|F_x(k) F_y(k)| ≤ F_x(k)² + F_y(k)²`, every finite subset `t ⊆ ℤ \ s` satisfies `|∑_{k ∈ t} F_x(k) F_y(k)| ≤ 4 (c_{DT}/w)² / (a_D T)`. Taking the `HasSum` limit over `u ⊇ s` (`u \ s ⊆ ℤ \ s`) gives `|ρ(x, y) - I_full(x, y)| ≤ 4 (c_{DT}/w)² / (a_D T)`.
3. **Taper comparison (`I_full(x, y)` vs `K_λ(Δ)`).** Changing variables `u = L v` (`du = L dv`, `(γ_x - γ_y) u = 2π Δ v`):
   - `L⁻¹ VPhiR(φ)(γ_x - γ_y) = ∫_{-1/2}^{1/2} φ(L v)² cos(2π Δ v) dv` and `a_D = ∫_{-1/2}^{1/2} φ(L v)² dv`.
   - On `|L v| ≤ L/2 - w` (i.e. `|v| ≤ 1/2 - w/L`), `Taper.phi = 1`, so `φ(L v)² = cos(√2 λ v)` identically (`HorizontalTradeoffWindowDeficit.lean`). On the two edge strips `[-1/2, -1/2 + w/L]` and `[1/2 - w/L, 1/2]` (total length `2w/L`), both `φ(L v)²` and `cos(√2 λ v)` lie in `[0, 1]`, so `|φ(L v)² - cos(√2 λ v)| ≤ 1` and `|cos(2π Δ v)| ≤ 1`.
   - Hence `|L⁻¹ VPhiR(φ)(γ_x - γ_y) - N_λ(Δ)| ≤ 2w / L` and `|a_D - a_*(λ)| ≤ 2w / L` (also proved in `aD_close` as `≤ 4w/L`).
   - Since `|N_λ(Δ)| ≤ a_*(λ)` (as `|cos(2π Δ v)| ≤ 1` and `cos(√2 λ v) ≥ 0` on `[-1/2, 1/2]`),
     $$\left|\frac{L^{-1}\operatorname{VPhiR}(\varphi)(\gamma_x - \gamma_y)}{a_D} - \frac{N_\lambda(\Delta)}{a_*(\lambda)}\right| = \frac{\big|(L^{-1}\operatorname{VPhiR} - N_\lambda) a_*(\lambda) + N_\lambda (a_*(\lambda) - a_D)\big|}{a_D a_*(\lambda)} \le \frac{2w/L \cdot a_*(\lambda) + a_*(\lambda) \cdot 2w/L}{a_D a_*(\lambda)} = \frac{4w}{a_D L}.$$
   - For `a_D ≥ a_*(λ) / 2` (since `2w/L ≤ a_*(λ)/2`), `4w / (a_D L) ≤ 8w / (a_*(λ) L)`. Triangle inequality yields Lemma 2. ∎

---

### Lemma 3 (Non-Lattice Floor of `K_λ(Δ)` on `[0, 3]` and Triple Sumset Disjointness; `[PROVED HERE]`)
Let `λ ∈ [999/1000, 1]`, and define `I₁ := (26/25, 43/40) = (1.040, 1.075)` and `I₂ := (503/250, 256/125) = (2.012, 2.048)`.
1. **Pointwise floor outside `I₁ ∪ I₂`:** For every `Δ ∈ [0, 3]` with `Δ ∉ I₁` and `Δ ∉ I₂`,
   $$|K_\lambda(\Delta)| \ge |N_\lambda(\Delta)| \ge \frac{1}{250}.$$
2. **Triple sumset disjointness:** For any `Δ₁ > 0` and `Δ₂ > 0` with `Δ₁ + Δ₂ ≤ 3`, at least one of the three spacings `Δ₁, Δ₂, Δ₁ + Δ₂` lies in `[0, 3] \ (I₁ ∪ I₂)`, and hence satisfies `|K_λ| ≥ 1 / 250`.

**Proof.**
**(1) Closed form and enclosures.** Set `a := λ / √2` and `x := π Δ`.
- First, `0 < a_*(λ) = ∫_{-1/2}^{1/2} cos(2 a v) dv ≤ ∫_{-1/2}^{1/2} 1 dv = 1`, so `|K_λ(Δ)| = |N_λ(Δ)| / a_*(λ) ≥ |N_λ(Δ)|`.
- Since `999/1000 ≤ λ ≤ 1`, `a² = λ² / 2 ∈ [998001/2000000, 1/2]` and `0 < a ≤ 1/√2 < 3/4`.
  * By `Real.one_sub_sq_div_two_le_cos`, `cos a ≥ 1 - a²/2 ≥ 1 - 1/4 = 3/4 = 0.75`.
  * Integrating `sin t ≥ t - t³/6` (`Real.sin_gt_sub_cube` on `(0, a]`) gives `1 - cos a ≥ a²/2 - a⁴/24`, so `cos a ≤ 1 - a²/2 + a⁴/24 ≤ 1 - 998001/4000000 + (1/4)/24 < 77/100 = 0.77`.
  * By `Real.sin_gt_sub_cube`, `a sin a ≥ a² (1 - a²/6) ≥ (998001/2000000) · (11/12) > 9/20 = 0.45`.
  * By `sin a = 2 sin(a/2) cos(a/2)` with `sin(a/2) ≤ a/2` (`Real.sin_le`) and `cos(a/2) ≤ 1 - (a/2)²/2 + (a/2)⁴/24`, `a sin a ≤ a² (1 - a²/8 + a⁴/384) ≤ (1/2)(1 - (998001/2000000)/8 + 1/1536) < 47/100 = 0.47`.
- On `Δ ∈ [0, 2/5]` (`[0, 0.40]`): for every `v ∈ [-1/2, 1/2]`, `|2 a v| ≤ a < 1` so `cos(2 a v) ≥ 1 - 1/2 = 1/2`, and `|2π Δ v| ≤ (2/5) π < 1.26` (`π < 3.1416`, `Real.pi_lt_d4`) so `cos(2π Δ v) ≥ 1 - 1.26²/2 > 1/5`. Integrating over `[-1/2, 1/2]` gives `N_λ(Δ) ≥ (1/2)(1/5) = 1/10 ≥ 1/250`.
- For `Δ ∈ [2/5, 3]`, `x = π Δ ≥ (2/5) · 3.1415 > 1.25 > 3/4 > a`, so `x² - a² > 0` and `x ± a ≠ 0`. Using `2 cos(2 a v) cos(2 x v) = cos(2(x - a)v) + cos(2(x + a)v)` and `HasDerivAt` (`∫_{-1/2}^{1/2} cos(2 t v) dv = sin t / t` for `t ≠ 0`):
  $$N_\lambda(\Delta) = \frac{1}{2}\left(\frac{\sin(x - a)}{x - a} + \frac{\sin(x + a)}{x + a}\right) = \frac{x \cos a \sin x - a \sin a \cos x}{x^2 - a^2} =: \frac{f(a, x)}{x^2 - a^2}.$$
  Since `x² - a² < x²`, it suffices to show `|f(a, x)| ≥ x² / 250` on each of the 10 elementary subintervals covering `[2/5, 3] \ (I₁ ∪ I₂)` using `3.1415 < π < 3.1416` (`Real.pi_gt_d4`, `Real.pi_lt_d4`), `Real.sin_le`, `Real.sin_gt_sub_cube`, `Real.one_sub_sq_div_two_le_cos`, and `Real.mul_le_sin`:
  * **S2 `[0.40, 0.50]` (`x ∈ [0.4π, π/2]`):** `x ≥ 1.256`, `sin x ≥ 1.256 - 1.256³/6 > 0.92`, `0 ≤ cos x = sin(π/2 - x) ≤ π/2 - x < 0.315`, so `f ≥ 1.256 · 0.75 · 0.92 - 0.47 · 0.315 > 0.71 ≥ (1.58)² / 250`.
  * **S3 `[0.50, 1.00]` (`t = π - x ∈ [0, π/2]`):** `sin x = sin t ≥ 0`, `cos x = -cos t ≤ 0`, so `f = x cos a sin t + a sin a cos t`. If `t ≤ π/4`, `cos t ≥ 1 - (π/4)²/2 > 0.69`, `f ≥ 0.45 · 0.69 > 0.31 ≥ π²/250`; if `t ≥ π/4`, `sin t ≥ (2/π) t ≥ 1/2`, `f ≥ 1.57 · 0.75 · 0.5 > 0.58 ≥ π²/250`.
  * **S4 `[1.00, 1.040]` (`x = π + t`, `t ∈ [0, 0.04π]`):** `t < 0.1257`, `cos t ≥ 1 - t²/2 > 0.992`, `sin t ≤ t < 0.1257`, `x < 3.268`, so `f = a sin a cos t - x cos a sin t ≥ 0.45 · 0.992 - 3.268 · 0.77 · 0.1257 > 0.130 ≥ 3.268² / 250` (`0.0428`).
  * **S5 `[1.075, 1.25]` (`x = π + t`, `t ∈ [0.075π, 0.25π]`):** `0.2356 < t < 0.7854`, `sin t ≥ t - t³/6 ≥ 0.2356 - 0.236³/6 > 0.2334` (as `u - u³/6` is strictly increasing on `[0, 1]`), `cos t ≤ 1 - t²/2 + t⁴/24 ≤ 1 - 0.2356²/2 + 0.236⁴/24 < 0.973` (as `cos` is decreasing on `[0, π]`), `x > 3.377`, `x < 3.927`, so `-f = x cos a sin t - a sin a cos t ≥ 3.377 · 0.75 · 0.2334 - 0.47 · 0.973 > 0.133 ≥ 3.927² / 250` (`0.0617`).
  * **S6 `[1.25, 1.50]` (`x = π + t`, `t ∈ [π/4, π/2]`):** `sin t ≥ (2/π) t ≥ 1/2`, `cos t ≤ 1`, `x > 3.92`, `x < 4.72`, so `-f ≥ 3.92 · 0.75 · 0.5 - 0.47 = 1.00 ≥ 4.72² / 250` (`0.0892`).
  * **S7 `[1.50, 2.00]` (`t = 2π - x ∈ [0, π/2]`):** `sin x = -sin t`, `cos x = cos t`, so `-f = x cos a sin t + a sin a cos t`. If `t ≤ π/4`, `cos t > 0.69`, `-f > 0.31 ≥ (2π)²/250` (`0.158`); if `t ≥ π/4`, `sin t ≥ 1/2`, `x > 4.71`, `-f > 1.76 ≥ 0.158`.
  * **S8 `[2.00, 2.012]` (`x = 2π + t`, `t ∈ [0, 0.012π]`):** `t < 0.03770`, `cos t ≥ 1 - t²/2 > 0.9992`, `sin t ≤ t < 0.03770`, `x < 6.321`, so `-f = a sin a cos t - x cos a sin t ≥ 0.45 · 0.9992 - 6.321 · 0.77 · 0.03770 > 0.266 ≥ 6.321² / 250` (`0.1599`).
  * **S9 `[2.048, 2.15]` (`x = 2π + t`, `t ∈ [0.048π, 0.15π]`):** `0.1507 < t < 0.4713`, `sin t ≥ 0.1507 - 0.151³/6 > 0.1501`, `cos t ≤ 1 - 0.1507²/2 + 0.151⁴/24 < 0.9887`, `6.433 < x < 6.755`, so `f = x cos a sin t - a sin a cos t ≥ 6.433 · 0.75 · 0.1501 - 0.47 · 0.9887 > 0.259 ≥ 6.755² / 250` (`0.1826`).
  * **S10 `[2.15, 2.50]` (`x = 2π + t`, `t ∈ [0.15π, π/2]`):** `sin t ≥ (2/π) t ≥ 0.30`, `cos t ≤ 1`, `6.75 < x < 7.86`, so `f ≥ 6.75 · 0.75 · 0.30 - 0.47 > 1.04 ≥ 7.86² / 250` (`0.2472`).
  * **S11 `[2.50, 3.00]` (`t = 3π - x ∈ [0, π/2]`):** `sin x = sin t ≥ 0`, `cos x = -cos t ≤ 0`, so `f = x cos a sin t + a sin a cos t` and `x < 3 · 3.1416 = 9.425` (`x² / 250 < 0.3554`). If `t ∈ [0, 0.2]`, `sin t ≥ t - t³/6 ≥ 0.99 t`, `cos t ≥ 1 - t²/2`, `x > 9.22`, so `f ≥ 9.22 · 0.75 · 0.99 t + 0.45(1 - t²/2) = 0.45 + t(6.84 - 0.225 t) ≥ 0.45 ≥ 0.3554`. If `t ∈ [0.2, π/2]`, `sin t ≥ (2/π) · 0.2 > 0.127`, `cos t ≥ 0`, `x > 7.85`, so `f ≥ 7.85 · 0.75 · 0.127 > 0.74 ≥ 0.3554`.

**(2) Sumset disjointness.** Suppose for contradiction that `Δ₁, Δ₂ > 0`, `Δ₁ + Δ₂ ≤ 3`, and all three of `Δ₁, Δ₂, Δ₁ + Δ₂` belong to `I₁ ∪ I₂ = (1.040, 1.075) ∪ (2.012, 2.048)`.
- If `Δ₁ ∈ I₁` and `Δ₂ ∈ I₁`, then `Δ₁ + Δ₂ > 1.040 + 1.040 = 2.080 > 2.048`, so `Δ₁ + Δ₂` exceeds the upper endpoint of both `I₁` and `I₂`, contradiction.
- Otherwise at least one of `Δ₁, Δ₂` lies in `I₂` (`> 2.012`) while the other lies in `I₁ ∪ I₂` (`> 1.040`), so `Δ₁ + Δ₂ > 2.012 + 1.040 = 3.052 > 3`, contradicting `Δ₁ + Δ₂ ≤ 3`. ∎

---

### Lemma 4 (Consecutive-Triple Mod-3 Packing and Asymptotic Assembly; `[PROVED HERE]`)
1. **Combinatorial consecutive-triple packing:** Let `γ_0 < γ_1 < \dots < γ_{m-1}` be any strictly increasing sequence of `m` real numbers in `[a, b]` (`a ≤ b`), let `α > 0`, and set `s_j := α (γ_{j+2} - γ_j)` for `0 ≤ j < m - 2`. Let `G := {j ∈ Finset.range (m - 2) | s_j ≤ 3}`.
   - **Telescoping span bound:** `∑_{j=0}^{m-3} s_j = α ∑_{j=0}^{m-3} ((γ_{j+1} - γ_j) + (γ_{j+2} - γ_{j+1})) ≤ 2 α (b - a)`.
   - **Markov inequality:** `3 ((m - 2) - #G) ≤ ∑_{j ∈ range(m-2) \ G} s_j ≤ 2 α (b - a)`, so `(m - 2 : ℝ) - (2/3) α (b - a) ≤ #G`.
   - **Mod-3 Pigeonhole:** Partitioning `G = G_0 ⊔ G_1 ⊔ G_2` by `j % 3 ∈ {0, 1, 2}`, there exists `r ∈ {0, 1, 2}` with `3 #G_r ≥ #G`. For distinct `j, j' ∈ G_r`, `j % 3 = j' % 3` and `j ≠ j'` imply `|j - j'| ≥ 3`, so the index triples `{j, j+1, j+2}` and `{j', j'+1, j'+2}` are **disjoint**, and hence `{γ_j, γ_{j+1}, γ_{j+2}}` and `{γ_{j'}, γ_{j'+1}, γ_{j'+2}}` are pairwise disjoint subsets!

2. **Fixed-`λ` gain for `λ ∈ [999999/1000000, 1)`:**
   Let `(Z, H)` satisfy `PaperInputs Z` (specialized to `zetaZeroConfig` and `paperInputs_zeta`), and let `λ ∈ [999999/1000000, 1)` with `P := paramsOf stdProfile λ` (`w = 1`, `P.Valid`).
   - By `cStar_lipschitzOn` and `cStar_ge_lb` (`Limit.lean` lines 196–228), `HD 1 - HD λ ≤ 56 π² (1 - λ) ≤ 56 · 10 · 10⁻⁶ = 0.00056`. Combined with `RHTower.HD_one_ge : 1681/2500 ≤ HD 1` (`0.6724`), we obtain `HD λ ≥ 0.67184`.
   - Applying `Zeta23.ThmD.thmD_mult_lam_abstract` at `ε_0 = 0.0001` gives, for all large `T`, `Z.N0s T (2T) ≥ 0.67174 N(T, 2T)`.
   - Let `S_{1, bulk} := {z ∈ (blockData Z T (P.atD T) hconj).S₁ | T + √T < Im z ∧ Im z ≤ 2T - √T}`. Every simple critical zero of `Z` in `(T, 2T]` either lies in `S_{1, bulk}` or lies in `(T, T + √T] ∪ (2T - √T, 2T]`. For `T ≥ 9`, `(T, T + √T] ⊆ (U₀ - √U₀, U₀]` (`U₀ = T + √T`) and `(2T - √T, 2T] ⊆ (2U₁, 2U₁ + √U₁] ∪ (2U₂, 2U₂ + √U₂]` (`U₁ = T - (2/3)√T`, `U₂ = T - (1/3)√T`), so the missing count is bounded by `NII Z U₀ + NII Z U₁ + NII Z U₂ = O(√T l(T)) = o(N(T, 2T))` (`Tail.eventually_NII_le`). Thus eventually `m := #S_{1, bulk} ≥ 0.6716 N(T, 2T) + 2`.
   - Distinct points of `S_{1, bulk}` have `Re z = 1/2`, hence `Im : S_{1, bulk} → ℝ` is injective (`Complex.ext`). Ordering `S_{1, bulk}` by `Im` via `Finset.orderEmbOfFin` gives `γ_0 < \dots < γ_{m-1}` in `[T + √T, 2T - √T] ⊆ [T, 2T]`.
   - With `α = L / (2π)`, `α (2T - T) = λ T l(T) / (2π) < T l(T) / (2π)`. By `H.RvM.main` (`N(T, 2T) = T ell1(T) / (2π) + O(log T)` with `ell1(T) = l(T) + 2 log 2 - 1 > l(T)` since `e < 4`), eventually `α T ≤ N(T, 2T)`.
   - Hence `#G ≥ (m - 2) - (2/3) α T ≥ (0.6716 - 2/3) N(T, 2T) > (1 / 250) N(T, 2T)`, and mod-3 Pigeonhole yields `K := #G_r ≥ (1 / 750) N(T, 2T)` pairwise disjoint index triples `C_j = {x_j, x_{j+1}, x_{j+2}} ⊆ S_{1, bulk}` of scaled span `s_j ≤ 3`.
   - By Lemma 3(2), each `C_j` (`j ∈ G_r`) contains a pair `(u_j, v_j)` (`u_j ≠ v_j`) with `|K_λ(Δ)| ≥ 1/250`. By Lemma 2, for all large `T` the uniform approximation error is `≤ 1/500`, so `|ρ(u_j, v_j)| ≥ 1/250 - 1/500 = 1/500`, giving `2 ρ(u_j, v_j)² ≥ 2 / 250000 = 1 / 125000`.
   - Since `{u_j, v_j} ⊆ C_j` and the triples `C_j` (`j ∈ G_r`) are pairwise disjoint, the pairs `(u_j, v_j)` (`j ∈ G_r`) are pairwise disjoint in `S₁`, and their total Schur–Jensen contribution satisfies:
     $$2 \sum_{j \in G_r} \rho(u_j, v_j)^2 \ge \frac{1}{750} \cdot \frac{1}{125000} N(T, 2T) = \frac{1}{93{,}750{,}000} N(T, 2T) \ge \frac{1}{10^8} N(T, 2T).$$

3. **Seam Assembly, `λ → 1⁻`, and Dyadic-to-Cumulative Lift:**
   - **(`c = 2`):** Subtracting `(1 / 10^8) N(T, 2T)` from both sides of the `c = 2` corollary of Lemma 1 shows that `Cnt(T) := N₀^simple(T, 2T) - (1 / 10^8) N(T, 2T)` eventually dominates the unmodified `Zeta23` multiplicity-aware seam! Feeding `Cnt` directly into `RHTower.thmD_count_of_seam` (`HorizontallyIsolatedSimpleZeros.lean` line 236) yields, for every `λ ∈ [999999/1000000, 1)` and `ε > 0`, `(HD(λ) + 1/10^8 - ε) N(T, 2T) ≤ N₀^simple(T, 2T)` eventually.
   - **(`c = 3`):** Likewise, feeding the `c = 3` corollary of Lemma 1 into the `c = 3` fixed-`T` algebra (`Nd_lower_c3`) yields `(GD(λ) + 1/(2·10^8) - ε) N(T, 2T) ≤ N_d(T, 2T)` eventually.
   - **(`λ → 1⁻`):** Applying `Zeta23.ThmD.eps_form_of_approx` (`Limit.lean` line 109, choosing `λ = max (999999/1000000) (1 - δ / (56 π²))`) upgrades both dyadic inequalities to `HD(1) + 1/10^8` and `GD(1) + 1/(2·10^8)`.
   - **Cumulative & `ξ`-census corollaries:** `Zeta23.cumulative_of_dyadic` (`Main.lean` line 51) lifts both dyadic bounds to `(0, T]` for `N0simple 0 T` and `Ndist 0 T`; `Zeta23.trivial_chain zetaSeam` transfers `N0simple` to `N0star`, `N0`, and `Nsimple`; and `RHTower.zeta23_Ncount_zero_eq_xiPosZeroCount` + `RHTower.zeta23_N0simple_zero_eq_xiSimpleCriticalZeroCount` transfer to `HD(1) + 1/10^8 ≤ liminf_{T → ∞} xiSimpleCriticalRatio(T)`. ∎

## Log
- 2026-10-27 — Phase 1–4 contextualization, hostile audit (`SURVIVES PRELIMINARY ATTACK`), and complete dependency-closed paper proof written in `2-fully-proven`. Proceeding immediately to Lean 4 formalization.
