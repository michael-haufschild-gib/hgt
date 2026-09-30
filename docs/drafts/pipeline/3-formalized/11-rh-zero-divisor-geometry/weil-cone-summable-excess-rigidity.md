# A Weil-positive system with summable excess over Λ is Λ

- **ID:** MC-WEIL-SUMMABLE-EXCESS
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** MC conjecture loop, cycle 157 (`1-in-progress/mc-conjecture-loop-2026-09-28.md`). It is the downward half of Theorem C′ (cycle 155) and the mirror of `3-formalized/11-rh-zero-divisor-geometry/weil-cone-summable-deficit-rigidity.md`.
- **Statement:** If `lam` is full-cone Weil-positive (`WeilPositiveFull lam`) and `Σ_{n≥2} (lam(n) − Λ(n))⁺ n^{−½} < ∞`, then `lam(n) = Λ(n)` for every `n ≥ 2`. Nothing is assumed about the deficit.

## Goal
- **Consequence.** Every Weil-positive `lam ≠ Λ` has infinite excess **and** infinite deficit, in the `n^{−½}` weight. The two-sided statement follows from this card together with the summable-deficit theorem.
- **The mechanism differs from the deficit side.** The deficit-side theorems (minorant and summable deficit) use only the shape of Riemann's kernel `K = Φ⋆Φ̃`, through point evaluations of positive-definite forms. The excess side needs a global spectral argument: a Fejér kernel with spectral gap below `log 2`, plus the size of the zero sum `Σ_ρ 1/(ρ(1−ρ)) = 2 + γ − log 4π`. On the excess side, local near-null tests cannot rule out a small-`n` excess that compensates a spread-out deficit. The mean density of the deficit is what forces rigidity.
- **Corollary.** RH ⟺ some full-cone Weil-positive `lam` has summable excess.

## Notation
- `a(n) = (lam(n) − Λ(n))/√n` for `n ≥ 2`. Write `e = a⁺` (the excess, summable by hypothesis) and `v = a⁻` (the deficit, no hypothesis).
- `W_a = Σ_{n≥2} a(n)(δ_{log n} + δ_{−log n})`, a measure on the `u`-line. Similarly `W_v` and `W_e`.
- `K(y) = ∫Φ(t)Φ(t−y)dt` (`riemannAutocorr`). It satisfies `K > 0`, `K` even, and `K(y) ≤ Ce^{−2|y|}`. Its Fourier transform is `∫K(y)e^{ity}dy = Ξ(t)²`, where `Ξ(t) = xi(½+it)` is real on `ℝ`.
- `Z = {t ∈ ℝ : Ξ(t) = 0}` is the set of real ordinates of critical-line zeros. It is closed and discrete, and `|t| > 4.5` on `Z` (corpus `four_half_lt_abs_im_of_xiZeroCopy`).
- `ψ(y) = Σ_n a(n)(K(y − log n) + K(y + log n)) = (K⋆W_a)(y)`.

## Paper proof

### Step 0: near-null positive definiteness
For real `c_1,…,c_N` and shifts `x_j`, let `f_L = Σ c_j Φχ_L(· − x_j)`.
- Its transform is `(Σ c_j e^{izx_j})·(Φχ_L)^`. The multiplier is at most `Σ|c_j|e^{|x_j|/2}` on the strip, so the zero side `W(f_L,f_L) → 0` as `L → ∞` (near-radical estimate).
- The autocorrelation is `Σ_{i,j} c_ic_j K_L(y + x_j − x_i)`.
- Weil positivity gives `Σ_n a(n)Σ_{i,j}c_ic_j[K_L(log n + x_j − x_i) + K_L(−log n + x_j − x_i)] ≤ Re W(f_L,f_L)`.
- Weil positivity also gives `|lam(n) − Λ(n)| ≪ n^{3/4}`, and `K_L ≤ K ≤ Ce^{−2|y|}`. So dominated convergence over `n` applies, and in the limit `Σ_{i,j}c_ic_j ψ(x_j − x_i) ≤ 0`.
- `ψ` is real and even, so `−ψ` is positive definite with complex coefficients too, and `−ψ` is continuous.

### Step 1: translation boundedness of the deficit
- `−ψ(y) ≤ −ψ(0)` gives `(K⋆W_v)(y) ≤ −ψ(0) + (K⋆W_e)(y) ≤ −ψ(0) + 2‖e‖₁ max K =: B`.
- With `κ = min_{[−1,1]}K > 0`, this gives `W_v([y−1,y+1]) ≤ B/κ` for every `y`.
- So `W_a` is a translation-bounded signed measure, and it is integrable against any `φ` with `Σ_k sup_{[k,k+1]}|φ| < ∞`.

### Step 2: the near-null inequality (Bochner)
- By Bochner, `−ψ = charFun σ` for a finite positive measure `σ`.
- Let `g ≥ 0` be continuous, compactly supported and Lipschitz, and set `h = Ξ²g`. Write `ȟ(u) = (1/2π)∫h(t)e^{itu}dt`, and similarly `ǧ`.
- The convolution theorem gives `ȟ = K⋆ǧ`, so `∫ȟ dW_a = ∫ψ ǧ = −∫(∫ǧ(y)e^{iyt}dy)dσ(t) = −∫ g(−t) dσ(t) ≤ 0`, with equality iff `g(−·) = 0` σ-a.e.
- (NN) Hence, if `R ≥ 0` vanishes on a neighbourhood of `Z`, then `∫Ř dW_a = −∫(R/Ξ²)(−t)dσ(t) ≤ 0`.

### Step 3: flattened positive-definite packets
Fix a compactly supported `C²` function `ρ₀` with `‖ρ₀‖₂ = 1` and put `G = ρ₀⋆ρ̃₀`. Then:
- `G(0) = 1`, `0 ≤ … `, `|G| ≤ 1`;
- `G` is compactly supported;
- `Ǧ = |ρ̌₀|²·2π ≥ 0`, so `‖Ǧ‖₁ = G(0) = 1`.

For `0 < ε < 1`, let `β_ε = G + (1−G)B(·/ε)`, where `B` is a smooth `[0,1]`-valued bump equal to `1` on `[−1,1]`. Then:
- `β_ε = 1` on `[−ε,ε]`, `β_ε ≤ 1`, and `β_ε` is compactly supported.
- `‖(β_ε − G)ˇ‖₁ → 0` as `ε → 0`. Indeed, `φ_ε = (1−G)B(·/ε)` has `‖φ_ε‖₁ = O(ε³)` and `‖φ_ε''‖₁ = O(ε)`. The estimate `‖φ̌‖₁ ≤ (2/π)√(‖φ‖₁‖φ''‖₁)` then gives `O(ε²)`.

### Step 4: the Fejér identity with spectral gap
- Fix `b = 2/3 < log 2`. Let `F(t) = 2(1 − cos bt)/t²`, so that `Ť(u) := F̌(u) = (1/2π)(b − |u|)⁺`, `F ≥ 0`, `F(0) = b²` and `F(t) ≤ 4/t²`.
- `W_a` vanishes on `(−log 2, log 2) ⊃ [−b, b]`, so `∫F̌(u)e^{−iτu}dW_a(u) = 0` for every `τ`. This is the Fejér identity for `F(· − τ)`.
- Decompose `F(·−τ)χ_Γ` as follows, where `χ_Γ = χ(·/Γ)` is a `[0,1]` cutoff and `Z_Γ = Z ∩ [−2Γ−1, 2Γ+1]` is finite:
  - packets at `0` (only for `τ = 0`) and at each `γ ∈ Z_Γ`: `P_γ = F(·−τ)χ_Γ β_ε((· − γ)/δ)`;
  - the remainder `R = F(·−τ)χ_Γ(1 − Σ_γ β_ε((·−γ)/δ))`.

  For `δ` small the packets are disjoint, so `R ≥ 0` and `R` vanishes near `Z_Γ` and outside `[−2Γ, 2Γ]`. (NN) gives `∫Ř dW_a ≤ 0`.
- Tail: `‖F̌ − (Fχ_Γ)ˇ‖` in the amalgam norm tends to `0` as `Γ → ∞`, because `(Fχ_Γ)ˇ = F̌ ⋆ Γχ̌(Γ·)` and `F̌` is Lipschitz with compact support.

### Step 5: packet estimates
Put `A_δ := ∫δǦ(δu)dW_v(u) ≥ 0`. By translation boundedness, `A_δ` stays bounded as `δ → 0`.
- **γ-packets.** `P̌_γ(u) = δ e^{iγu}[F(γ−τ)χ_Γ(γ)(Ǧ + (β_ε−G)ˇ)(δu) + O(δ)]`. Therefore:
  - `|∫P̌_γ dW_v| ≤ F(γ−τ)A_δ + c(ε) + O(δ)`, with `c(ε) → 0`, using Step 1 and Step 3;
  - `|∫P̌_γ dW_e| ≤ ‖e‖₁·sup|P̌_γ| = O(δ)`.
- **0-packet** (`τ = 0`). `∫P̌_0 dW_v ≥ F(0)A_δ − c(ε) − O(δ)`, and `|∫P̌_0 dW_e| = O(δ)`.
- **Conclusion at `τ = 0`.** `0 ≤ −F(0)A_δ + Σ_{γ∈Z_Γ} F(γ)A_δ + |Z_Γ|c(ε) + O_Γ(δ) + tail(Γ)`. Let `δ → 0`, then `ε → 0` (in the order `c(ε)` first, then `δ`), then `Γ → ∞`. This gives `limsup_{δ→0} A_δ·(F(0) − Σ_{γ∈Z}F(γ)) ≤ 0`.

### Step 6: the zero sum
- By the Hadamard product (corpus `logDeriv_xi_sub_eq` at `s = 1`, with `logDeriv xi 0 = −Λ₀(0)` and the functional equation), `Σ_{copies ρ} 1/(ρ(1−ρ)) = 2Λ₀(0) = 2 + γ − log 4π < 0.0462`.
- Every term has positive real part. A real ordinate `t` gives the term `1/(¼+t²)`, and `|t| > 4.5` there.
- Hence `Σ_{t∈Z} F(t) ≤ Σ 4/t² ≤ 4(1 + 1/81)(0.0462) < 0.19 < 4/9 = F(0)`.
- So `A_δ → 0`: the deficit has mean density zero.

### Step 7: σ vanishes off Z
- Run Step 5 for arbitrary `τ`, with no 0-packet. Every packet term is `≤ F(γ−τ)A_δ + c(ε) + O(δ) → 0`, so `∫(R/Ξ²)(−t)dσ(t) ≤ o(1)`.
- As `δ, ε → 0` and `Γ → ∞`, `R/Ξ²` increases to `F(t−τ)/Ξ(t)²` on `ℝ∖Z` (for monotonically chosen parameters). By monotone convergence, `∫_{ℝ∖Z}F(−t−τ)Ξ(t)^{−2}dσ(t) = 0`.
- Taking `τ ∈ {0, π/b}` covers the zeros of `F`. So `σ(ℝ∖Z) = 0`.

### Step 8: W_a = 0
- For any continuous, compactly supported, Lipschitz `φ` with `R_φ = φ(1−Σβ_γ)` vanishing near `Z`, Step 2 gives `∫Ř_φ dW_a = −∫(R_φ/Ξ²)(−t)dσ = 0`. The integrand vanishes on `Z`, and `σ` lives on `Z`.
- Packets contribute `≤ |φ(γ)|A_δ + c(ε) + O(δ) → 0`. So `∫φ̌ dW_a = 0` for all such `φ` (with the same tail argument when `φ` is not compactly supported).
- Take `φ(t) = F_c(t)e^{−itx₀}`, with `F_c` the Fejér kernel of width `c`. Then `φ̌` is the triangle `(1/2π)(c−|u−x₀|)⁺`. With `x₀ = log n` and `c` less than the gap to `log(n±1)`, this gives `a(n)c/(2π) = 0`.

## Lean plan
1. `RHTower/WeilFullConeNearNullPositiveDefinite`: Step 0 (shift combs with real coefficients, then the limit `L → ∞`).
2. `RHTower/XiRealZeroFejerSum`: Step 6.
3. Fourier layer (`HTGeometry`): the convolution theorem for `K`; the L¹ bound `‖φ̌‖₁ ≤ (2/π)√(‖φ‖₁‖φ''‖₁)`; flattened packets; window limits.
4. `RHTower/WeilFullConeSummableExcessRigidity`: Steps 1–8.

## Log
- 2026-09-30 — created (MC cycle 157); paper proof complete. Lean started.
- 2026-09-30 — Lean progress. Compiled, `sorry`-free modules in `formal/GaloisForLFunctions/RHTower/`, not yet wired:
  - `XiRealZeroFejerSum`: `Σ_{t∈s} 4/t² ≤ 3/8` over real zeros of `Ξ`.
  - `WeilFullConeNearNullPositiveDefinite`: `positiveDefiniteOnReal_neg_deviationPotential` (Step 0).
  - `WeilDeviationTranslationBound`: kernel domination; `exists_tsum_deficit_cauchyProfile_le` (Step 1).
  - `RiemannAutocorrFourier`: `𝓕K = Ξ²` and `Ξ(ξ) = XiC(2πξ)`.
  - `WeilDeviationSpectralPairing`: Lemma NN, `deviationPairing_fourier_riemannXi_sq_mul` (Step 2).
  - `WeilDeviationPacketLimit`: the packet-limit lemma `norm_weightPairing_fourier_mul_packet_sub_le` (Step 5 engine).
- Design choices for the rest:
  - Fejér test `F = (𝓕ρ)²` with `ρ = 1_{[−a,a]} ⋆ m` (`a = 0.31`, `m` supported in `[−0.03, 0.03]`). Then `F(0) = 4a²`, `F(ξ) ≤ 1/(πξ)²`, and `𝓕F` is supported in `|u| ≤ 2(a + 0.03) < log 2`.
  - Step 7 by a finite cover of `supp g` with translates of `F`. Step 8 with `φ_T(ξ) = ρ₀(ξ/T) e^{2πiξ log m}`.
- 2026-09-30 — More compiled modules, all in namespace `RHTower.WeilExcess`:
  - `WeilDeviationBumps`: smooth-amplitude Fourier profiles; the positive-definite packet `G` with `𝓕G ≥ 0`; the flat bump and flattened packet.
  - `WeilDeviationFejerTest`: `F = |𝓕ρ|²`, with `F(0) = 0.4356`, `F(ξ) ≤ 1/(πξ)²`, `𝓕F = 0` on `|u| > 17/25`, and zero budget at most `3/8`.
  - `WeilDeviationDecomposition`: finite zero windows, division by `Ξ²`, the excess/deficit split, and `tendsto_deviationPairing_tail`.
- The flattening error does not need second derivatives. It is the packet-limit lemma applied at scale `εδ` with amplitude `h₁((·−γ)/δ)`, where `h₁(0) = 0`; by scale covariance the error is `ε·∫|𝓕h₁||t|(1+t²)`.
- 2026-09-30 — FORMALIZED. Stage 3. Fourteen modules, all in namespace `RHTower.WeilExcess`, wired into `RHTower.lean` after `WeilFullConeSummableDeficitRigidity`. `#print axioms` gives `propext, Classical.choice, Quot.sound` only.
  - `WeilFullConeSummableExcessRigidity`:
    - `eq_vonMangoldt_of_weilPositiveFull_of_summable_excess`, the main theorem, stated with the hypothesis in the form `Summable fun n => max (lam n − Λ n) 0 / √n`.
    - `riemannHypothesis_iff_exists_weilPositiveFull_summable_excess`.
    - `not_summable_excess_of_ne` and `not_summable_deficit_of_ne`: a Weil-positive `lam ≠ Λ` has infinite excess and infinite deficit.
  - `WeilDeviationDeficitMeanVanishes`: `tendsto_deficitMean` (Steps 5–6). The deficit mean `A_δ` tends to 0.
  - `WeilDeviationFourierAnnihilation`: `deviationPairing_fourier_eq_zero` (Step 7). `Σ a(n)(𝓕h(log n) + 𝓕h(−log n)) = 0` for every smooth compactly supported `h`.
- Changes from the paper plan:
  - **Step 7 needs no measure-support statement.** The remainder of `h` is dominated pointwise by `C` times the remainder of the cut-off dilated Fejér test `F(·/s)χ(·/Γ)`, and `F(ξ/s) ≥ F(0)/2` on `supp h` once `s` is large. The remainder of the Fejér test is controlled by the triangle inequality: its full pairing is minus the tail, and its packets are small. So `σ(ℝ∖Z) = 0` is never stated.
  - Dilation keeps the Fourier support inside `|u| ≤ 17/25`.
  - **Step 8** uses `Φ(ξ) = F(ξ/(m+1))e^{2πiξ log m}`. The gap `|log n − log m| ≥ 1/(m+1)` isolates `log m`, and `∫F > 0`. The cut-off tests pair to zero, and the tail lemma passes to the limit.
- 2026-09-30 — (MC cycle 161) **Generalized from summable excess to density-zero excess, and made quantitative.** The whole chain now assumes only a translation-bounded excess (`CauchyBounded (deviationExcess lam) Dₑ`); summable excess is recovered via `cauchyBounded_of_summable` and `excessMeanVanishes_of_summable`.
  - **Mean balance** (`RHTower.WeilExcess.meanBalance`). For every full-cone Weil-positive `lam` with translation-bounded excess, `(F(0) − 3/8)·A_δ ≤ (F(0) + 3/8)·E_δ + o(1)`, where `A_δ` and `E_δ` are the deficit and excess means over windows of length `1/δ`. The deficit density is at most about 13.4 times the excess density.
    - Proof: the origin packet now carries `F(0)(E_δ − A_δ)`, each zero packet carries `F(γ)(A_δ + E_δ)`, and the zero budget is `3/8`.
  - **Density rigidity** (`eq_vonMangoldt_of_weilPositiveFull_of_excessMeanVanishes`). If the excess is translation-bounded with vanishing mean, then `lam = Λ`.
    - `not_excessMeanVanishes_of_ne`: a second member of the cone with translation-bounded excess has an excess of positive upper density.
  - Only the one direction `A ≲ E` holds. The remainder sign `P(𝓕R) ≤ 0` is one-sided, so no bound `E ≲ A` follows from this mechanism.
- 2026-09-30 — (MC cycle 162) **Two-sided comparison and density-zero deficit rigidity.** Module `WeilDeviationMeanComparison`.
  - **`exists_excessMean_le_deficitMean`: `E_δ ≤ A_δ + Cδ`.** Near-null positivity applied to `g = χG_δ ≥ 0` gives `W_a(𝓕(Ξ²χG_δ)) ≤ 0`, and the packet limit gives `W_w(𝓕(Ξ²χG_δ)) = Ξ(0)²M_δ(w) + O(δ)`.
  - **Symmetric translation bound** (`exists_tsum_excess_cauchyProfile_le`). A translation-bounded deficit forces a translation-bounded excess, because `|ψ| ≤ −ψ(0)` works in both directions.
  - **`eq_vonMangoldt_of_weilPositiveFull_of_deficitMeanVanishes`.** A translation-bounded deficit with vanishing mean forces `lam = Λ`. This extends HF's summable-deficit rigidity from `ℓ¹` to density zero.
  - **Two-sided law.** For every Weil-positive `lam` with translation-bounded deviation: `E_δ ≤ A_δ + o(1)` and `A_δ ≤ 13.4·E_δ + o(1)`. Excess and deficit densities are comparable, and either vanishes only at `Λ`.
