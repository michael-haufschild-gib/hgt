# Zero-free-window rigidity: square-summable deviations on log-separated supports

- **ID:** L160 / weil-cone-zero-free-window-rigidity
- **Stage:** 2-fully-proven (Lean in progress)
- **Type:** THEOREM (paper, complete)
- **Source:** hf-positive-hodge-attack/krein-producer-loops.md (L160)

## Statement
Let `lam` be full-cone Weil-positive (`WeilPositiveFull`). Write `a(n) = (lam(n) − Λ(n))/√n` for `n ≥ 2`, with `a(n) = 0` otherwise, and `S = {n : a(n) ≠ 0}`. Suppose:
- **(Sq)** `Σ_n a(n)² < ∞`;
- **(Gap)** there are `c > 0` and `D ≥ 0` with `|log m − log n| ≥ c(1 + log m + log n)^{−D}` for all distinct `m, n ∈ S`.

Then `a ≡ 0`, i.e. `lam = Λ` on `n ≥ 2`.

**Corollary (Baker).** Let `P` be a finite set of primes. A full-cone Weil-positive system whose normalized deviation from `Λ` is square-summable and supported on `P`-smooth numbers equals `Λ`.
- *Proof.* Baker–Wüstholz/Matveev gives `|Σ b_p log p| ≥ C_P(1 + max|b_p|)^{−D_P}` for nonzero integer vectors `b`, which is (Gap).

## Goal
Rigidity so far was proved on **separated** supports (L158/L159: log-gaps `≥ log 2`) and for absolutely summable deviations (L64). Here the support's logarithms may **accumulate**, with gaps shrinking polynomially: examples are `⟨2,3⟩` or `{⌊e^{√j}⌋}`. Deviations may be non-summable.

The mechanism is new: sampling on **windows free of zeta zeros**, instead of the kernel incoherence of L156–L159.

## Paper proof
Notation:
- `𝓕f(ξ) = ∫e^{−2πixξ}f(x)dx`.
- `Φ` is Riemann's kernel and `K(y) = ∫Φ(t)Φ(t−y)dt`.
- `X(ξ) := 𝓕Φ(ξ) = Ξ(2πξ)`, which is real, smooth, and has `𝓕K = X²`.
- `Z = {ξ ∈ ℝ : X(ξ) = 0}`, the critical-line zero ordinates divided by `2π`.

**Step 0 (counting).** Points of `S` with `log n ∈ [j, j+1)` are `c(3+2j)^{−D}`-separated in `log n`, so there are at most `1 + (3+2j)^D/c` of them. Hence `Z_S(s) := Σ_{n∈S}(1 + log n)^{−s} < ∞` for `s > D + 1`. Also `|a(n)| ≤ ‖a‖₂ =: A`.

**Step 1 (near-null positivity for Schwartz tests).** For `g ∈ 𝓢(ℝ, ℂ)` put `G = g ⋆ g̃`, with `g̃(x) = conj g(−x)`. Then
`Re Σ_n a(n)[(K⋆G)(log n) + (K⋆G)(−log n)] ≤ 0`.
- (a) Take `g ∈ C_c^∞` and the test `f_L = Φχ_L ⋆ g` (smooth, compactly supported).
  - Its autocorrelation is `K_L ⋆ G`.
  - Its transform is `paperFT(Φχ_L)·paperFT(g)`, so the zero side is at most `(5/4)ζInvSq·(∫|g|e^{|x|/2})²·E_L² → 0`.
  - Weil positivity with `weilFullFunctional_eq_sub` gives `Re Σ a(n)(K_L⋆G)(±log n) ≤ ‖W(f_L,f_L)‖`.
  - As `L → ∞`, `K_L → K` pointwise with `0 ≤ K_L ≤ K`. The sums converge dominatedly, since `K⋆|G|` decays double-exponentially and `|a(n)| ≤ A`.
- (b) For general `g`, truncate: `g_M = gχ(·/M) ∈ C_c^∞`.
  - With `w_s(x) = (1+|x|)^s`, the weighted norms satisfy `‖w_s(φ⋆ψ)‖_{L¹} ≤ ‖w_sφ‖_{L¹}‖w_sψ‖_{L¹}` and `sup w_s(K⋆H) ≤ sup(w_sK)·‖w_sH‖_{L¹}`.
  - So `Σ_{n∈S}|a(n)||(K⋆(G−G_M))(±log n)| ≤ A·Z_S(s)·sup w_s|K⋆(G−G_M)| → 0`.

**Step 2 (spectral localization).** Fix `β ∈ C_c^∞((−1,1))` even, with `β ≥ 0` and `β ≢ 0`, and put `B := 𝓕(β²)`. Then `B` is real and even, `B(0) = ∫β² > 0`, and `|B(x)| ≤ ‖B‖_k(1+|x|)^{−k}`.

For `0 < η ≤ 1` and `ξ₀` with `dist(ξ₀, Z) ≥ η`:
- set `u(ξ) := β((ξ−ξ₀)/η)/X(ξ)` (smooth, compactly supported) and `g := 𝓕⁻u ∈ 𝓢`;
- then `𝓕(K⋆G) = X²|u|² = β((·−ξ₀)/η)²`, so `(K⋆G)(x) = η e^{2πixξ₀} B(ηx)`.

Step 1 then gives
`Y_η(ξ₀) := Σ_n a(n)B(η log n)cos(2πξ₀ log n) ≤ 0` whenever `dist(ξ₀, Z) ≥ η`.

**Step 3 (bad set).** The local zero count (`ncard_xiOrdinateWindow_le_log`) gives `#(Z ∩ [T−1, 2T+1]) ≤ C₁T log T` for `T ≥ 2`. So `Bad_T := {ξ ∈ [T,2T] : dist(ξ, Z) < η}` has measure at most `2ηC₁T log T`.

**Step 4 (mean values).** Put `c_n = a(n)B(η log n)` and `Q_η = Σ|c_n|(1+log n)^D`.
- Using `(1+ηx) ≥ η(1+x)`: `Q_η ≤ A‖B‖_kη^{−k}Z_S(k−D)` with `k = 2D + 2`.
- `cos α cos β = ½cos(α−β) + ½cos(α+β)`, `|∫_T^{2T}cos(2πξλ)dξ| ≤ 1/(π|λ|)` and (Gap) give:
  - (i) `|∫_T^{2T}Y| ≤ Q_η/(π log 2)`;
  - (ii) `|∫_T^{2T}Y² − (T/2)Σc_n²| ≤ C₂Q_η²`;
  - (iii) `|∫_T^{2T}Y(ξ)cos(2πξ log m)dξ − (T/2)c_m| ≤ C₂Q_η(1+log m)^D`.
- Here `C₂` depends only on `c` and `D`, and the off-diagonal weight is `(1 + log m + log n)^D ≤ 2^D(1+log m)^D(1+log n)^D`.

**Step 5 (assembly).** `Y ≤ 0` on `[T,2T] \ Bad_T`. Hence
`∫|Y| = 2∫Y⁺ − ∫Y ≤ 2√(|Bad_T|·∫Y²) + |∫Y|`,
and by (iii)
`|c_m| ≤ 4√(2ηC₁ log T·(½Σc_n² + C₂Q_η²/T)) + O(Q_η(1+log m)^D/T)`.

Now `Σc_n² ≤ ‖B‖_∞²Σa²`. Take `T = η^{−3k}`. Then:
- `η log T = 3kη log(1/η) → 0`;
- `Q_η²/T ≤ Cη^{k} → 0` and `Q_η/T → 0`.

So `c_m → 0` as `η → 0`. But `c_m = a(m)B(η log m) → a(m)B(0)` with `B(0) > 0`, hence `a(m) = 0`. ∎

## Phase 4
- **False?** No counterexample. Each step is elementary given Weil positivity. Only near-null positivity is used (no zero atoms), and no RH.
- **Circular?** No: RH is neither assumed nor concluded.
- **Rediscovered?** The free-weight Weil cone is not studied in the literature. The ingredients are classical (Weil explicit formula, Riemann–von Mangoldt, mean values of generalized Dirichlet polynomials), but their combination with the division by `Ξ` on zero-free windows is new.
- **Significance.**
  - It is the first rigidity theorem on supports whose logarithms accumulate, and with Baker it covers every finitely generated multiplicative semigroup.
  - It locates the obstruction for the full support `ℕ` exactly. Resolving at scale `η` needs zero-free windows, i.e. `η log T → 0`, and hence mean values of Dirichlet polynomials of length `e^{R/η}` at height `T`. That is possible only when the support's log-gaps at height `X` are `e^{−o(X)}`. The integers have gaps `e^{−X}`, exactly the boundary: the "α ≥ 1 wall" of L127/L133/L149 is this uncertainty-principle balance between zero density `log T/2π` and the Liouville spacing of `log ℕ`.
- **Verdict:** SURVIVES.

## Gates
- [x] 0 → 1
- [x] 1 → 2 (paper proof above)
- [ ] 2 → 3: Lean module `RHTower/WeilFullConeZeroFreeWindowRigidity` (in progress; see Log)
- [ ] 3 → 4 (not pursued)

## Log
- 2026-09-30 — L160: conjecture, kill attempts and paper proof.
- **Lean plan, in order:**
  1. convolution near-null tests `Φχ_L ⋆ g` for `g ∈ C_c^∞`;
  2. truncation to Schwartz `g`;
  3. `𝓕K = X²` and the localized identity;
  4. bad-set measure from `ncard_xiOrdinateWindow_le_log`;
  5. mean values under (Gap);
  6. assembly.
