# The complete Weil family is positive at a critical multiple

- **Stage:** 1-in-progress
- **Type:** CONJECTURE; endpoint assembly incomplete
- **Wall:** Σ1b, Σ1k; route obstacles B4 (`2.5.4`) and B5 (`2.8`)
- **Statement:** There exists `K₁ > 0` such that eventually in `N` and uniformly across `1 ≤ c ≤ 2 K₁ (log N)^{1/8}`, `spectralFloorWeilMatrix c N` and `completeWeilMatrix tiltedUnitSpline c N` are positive definite on `EuclideanSpace ℝ (PrimeHorizonIndex N)`.

## Goal

Resolves Section 2.8 of `obstacles-summary.md` in the affirmative on the whole space: there is a fixed positive critical multiple `K₁ > 0` at which `completeWeilMatrix tiltedUnitSpline (2 K (log N)^{1/8}) N` is eventually positive definite on all vectors (hence also positive on the pole hyperplane `v₁^⊥`, satisfying Hodge–Riemann and hard Lefschetz) for every `0 < K ≤ K₁`, with a common `K₁ > 0` simultaneously inside the aperture-independent window-pencil range of `OneCriticalMultiplePaysEveryWindow`.

## Proof sketch — unresolved dependencies

The cutoff `Q₁ = ⌊L^(5/16)⌋` below does not make the cited mid-band error
`c√c(1+log c)/√Q₁` small at `c ≍ L^(1/8)`: its power is `L^(1/32)`.
Use `Q₁ = ⌊L^(13/32)⌋` instead; the power becomes `L^(-1/64)`.
The log-free residual module states that larger cutoff but does not yet pass
a direct Lean check. Step 3 also omits the terminal leakage in the prefix
pole-defect bound and needs a weighted complement theorem. The argument is
therefore not dependency-closed.

Current bridge: [F2 assembly](f2-complete-family-assembly.md).

Write `L = log N` and split `[1, 2 K₁ L^{1/8}] = [1, L^{1/16}] ∪ [L^{1/16}, 2 K₁ L^{1/8}]`. On `[1, L^{1/16}]`, `eventually_tiltedUnitSpline_spectralFloorWeilMatrix_posDef_below_one_eighth` at `α = 1/16 < 1/8` gives `(spectralFloorWeilMatrix c N).PosDef`. Assume `L^{1/16} ≤ c ≤ 2 K₁ L^{1/8}` with `0 < K₁ ≤ 1/2`.

### 1. Dyadic seventh-power reserve on the top collar

Let `M = min N ⌊N / linearDefectCutoff c⌋₊` (`linearDefectCutoff c = 4 max(2 c e^2, 512 c + 1) ≤ 2049 c`) and define the weighted top-collar mass
`S_7(x) = Σ_{n ∈ (M, N]} (N/n)^7 x_n^2 ≥ Σ_{n ∈ (M, N]} x_n^2`.

Let `B ∈ C_c^∞(ℝ)` satisfy `0 ≤ B ≤ 1`, `B = 1` on `[-1, 1]`, and `supp B ⊆ (-2, 2)` (`ContDiffBump 0` with `rIn = 1, rOut = 2`). For `0 ≤ k ≤ K_max = ⌊log_2(linearDefectCutoff c)⌋₊`, set `a_k = log N - (k + 1) log 2` and `χ_k(u) = B(u - a_k)`. Since `log 2 < 1`, `χ_k = 1` on `[log N - (k + 1) log 2, log N - k log 2]`; since `1/2 < log 2`, at most `9` cutoffs `χ_k` are nonzero at any point. Using `archLevyDensity(x) x^2 ≤ 34 e^{-x/4}` on `(0, ∞)` (`∫_{x>0} archLevyDensity(x) x^2 ≤ 136`), every `h ∈ C_c^2(ℝ)` satisfies `levyEnergy(h) ≤ 136 ∫ (h')^2`, and Lipschitz localization of `χ_k` gives
`Σ_{k=0}^{K_max} levyEnergy(χ_k f) ≤ 18 levyEnergy(f) + C_IMS ∫ f^2`.

For `y_n = x_n 1_{n > M}` and `f = atomicTest N y g` (`g = atomDilate tiltedUnitSpline (c/N)`, `G = ∫ g^2 = (c/N) ∫ φ^2`), compare `χ_k f` with the localized atomic test
`F_k = Σ_{n=1}^{N_k} χ_k(log n) y_n g(· - log n)` at sub-horizon `N_k = min N ⌊4 N / 2^k⌋₊` and local overlap `c_k = c N_k / N` (`c_k / N_k = c / N`). Because `2^k ≤ linearDefectCutoff c ≤ 2049 c`, every shell satisfies `c_k ≥ 1/2049` and `log N_k ≥ L/2` eventually. On `c_k ≥ 1`, `archForm_atomicTest_ge_growing` gives an archimedean floor `(b_grow / c_k^7 · log N_k - C_grow c_k) G Σ χ_k(log n)^2 y_n^2`; on `1/2049 ≤ c_k < 1`, nonvanishing of `paperFT tiltedUnitSpline` on `ℝ` (`tiltedUnitSpline_highBand_mass`) gives `(c_0 log N_k - b_0) G Σ χ_k(log n)^2 y_n^2`, which dominates `(δ_0 / c_k^7 · log N_k - C_0 c_k) G Σ χ_k(log n)^2 y_n^2` since `c_k ≥ 1/2049`. The commutator `R_k = χ_k f - F_k` has derivative supported on `{n : |log n - a_k| ≤ 3}` with `|χ_k(u) - χ_k(log n)| ≤ L_B (c/N)`, canceling the `(N/c)` derivative scaling of `g'` so that `levyEnergy(R_k) ≤ 136 ∫ (R_k')^2 ≤ C_comm c G Σ_{|log n - a_k| ≤ 3} y_n^2`. Since `c_k ≤ 4 c / 2^k` implies `c_k^{-7} ≥ 4^{-7} 2^{7k} c^{-7}` and `(N/n) ∈ [2^k, 2^{k+1})` implies `χ_k(log n) = 1` with `2^{7k} ≥ 2^{-7} (N/n)^7`, summing over `0 ≤ k ≤ K_max` yields
`archForm(f) ≥ G ((δ_7 / c^7) L S_7(x) - C_arch c S_7(x))` with an explicit constant `δ_7 > 0`.

For the top-collar prime sum, `abs_lagForm_le_lagWin` restricts `(k, m, n)` to `|log(k m) - log n| ≤ c/N`. Applying `Λ(k) ≤ k` and `2 |y_m y_n| ≤ k^4 y_m^2 + k^{-4} y_n^2`: the `y_n^2` weight sums over `k ≥ 2` as `Σ_{k ≥ 2} k^{-3} O(c) = O(c)`, while the `y_m^2` weight sums over `k ≤ ⌊e N / m⌋` as `Σ_{k ≤ e N/m} k^5 O(c k m / N + 1) = O(c (N/m)^7)`, removing the `log c` factor of the unweighted top prime bound and giving `|primeSum(f)| ≤ G C_prime c S_7(x)`. Similarly, for `z ∈ V_1^⊥`, Cauchy–Schwarz on `m_1(x) = -Σ_{n > M} x_n / √n` gives `m_1(x)^2 ≤ (Σ_{n=1}^N n^6 / N^7) S_7(x) ≤ S_7(x)` without `log c`. Combining with the window-averaged prefix-top decomposition of `TheFarReserveThroughTheWindowAverage` at `λ = L^{3/16}`, `T = e^λ`, `h = e^{-λ}/L`, every `z ∈ V_1^⊥` satisfies eventually (for `2 K₁^8 ≤ δ_7 / (64 (C_arch + C_prime + 4))`):
`completeWeilEnergy tiltedUnitSpline c N z ≥ (3/4) poleDefect M x + (δ_7 / (8 c^7)) L S_7(x) - θ_N L P`,
where `P = Σ_{n ≤ M} x_n^2` and `θ_N = 1 / (64 D_0 (1 + log L)^5)`.

### 2. Logarithm-free critical-curve conductor residuals

Set `Q₁ = ⌊L^{5/16}⌋₊`. On `1 ≤ m ≤ Q₁`, channels 1–5 of the residual `r_m = W v_m - E_m(c) v_m` already satisfy `‖r_m^{(j)}‖^2 = O(m (1 + log m)^2 c^2 / L)` and `|⟨r_m^{(j)}, v_l⟩| = O(√(m l) (1 + log m) c / L)` without `log c` or `L^{1/k}` factors. Three critical-curve improvements close `1 ≤ m, l ≤ ⌈c⌉`:

1. **Near Gamma + downward cancellation (channels 6 + 7):** Set `U_m = φ(m)^{-1/2} normalizedFullNearGammaDownwardVector c N m + nearCenterVector c N m`. At `m = 1`, on interior rows `N / (4 e^2 c) < n < N - ⌈2 e^2 c⌉₊`, the pole-shift term `+(c (I^2/M) log c √n)/(N √L)` of channel 7 and the downward/near-Gamma mean `-(c (I^2/M) log c √n)/(N √L)` of channel 6 cancel identically (`∫_{-1}^1 shellAutocorr φ = I^2`, `completeWeilPoleShift φ c = c I^2 / M`). Only boundary rows `n ≥ N - ⌈2 e^2 c⌉₊` and the `(1 + log(N/n))` / `(1 + log c)/√(n L)` remainders survive on `n > N / (4 e^2 c)`, giving `‖U_1‖^2 = O(c^2 / L)` and `|⟨U_1, v_l⟩| = O(√l c / L)` via `(1 + log c)^3 = O(c)`. For `m ≥ 2`, `c_m(j)` is `m`-periodic of mean zero; summation by parts in `h = |j - n|` against Lipschitz continuity of `shellAutocorr` (channel 6) and monotonicity of `archLevyDensity` on `(0, ∞)` (channel 7) replaces `log c` by bounded endpoint variation, giving `‖U_m‖^2 = O(m^3 c^2 / L)` and `|⟨U_m, v_l⟩| = O(m^{3/2} √l c / L)`.
2. **Upward prime bilinear pairing (channel 8):** By exact transpose `⟨upwardPrimeVector c N v_m, v_l⟩ = ⟨v_m, downwardPrimeVector c N v_l⟩`, expanding `downwardPrimeVector c N v_l` via `downwardRamanujanRow_sub_interior_eq`, `interiorDownwardPrimeRow_eq_divisors`, and the exact divisor-jet identity `Σ_{d|n} Λ(d) c_l(n/d) = c_l(n) log n - ramanujanDivisorJet l n`, every smooth `(log n)/n` profile cancels off the diagonal by shifted Ramanujan orthogonality (`sum_range_ramanujanLagCoefficient_shift_mul`), leaving `O((m l)^2 c / L + (m l)^2 c^4 / N)` with no `log c` and no `L^{1/k}` loss.
3. **Top-collar `S_7`-weighted residual norm:** For `1 ≤ m ≤ ⌈c⌉`, `up_row_le` (`|(upwardPrimeVector c N v_m)_n| ≤ O(c) √(m / (n L))`) and `|shellCorrection c m| = O(c)` combine with `Σ_{n > M} (n/N)^7 / n ≤ 1` to give `W_7(r_m) := Σ_{n ∈ (M, N]} (n/N)^7 r_m(n)^2 ≤ C_2 m^3 c^2 / L`.

Dividing the bilinear errors by `√(E_m(c) E_l(c))`: for `1 ≤ m, l ≤ ⌈c⌉`, `E_m(c) ≥ κ_0 m^7 / c^7` gives off-diagonal terms `O((m l)^{-3/2} c^8 / L)` whose Hilbert–Schmidt norm is `O(c^8 / L) = O(K₁^8) ≤ 1/16` for small `K₁ > 0`; for `max(m, l) > ⌈c⌉` up to `Q₁ = ⌊L^{5/16}⌋₊`, `E_{\max}(c) ≥ κ_0` and the variable-rate bilinear bound at `k = 16` gives `O(L^{-1/8} (log L)^4) → 0`. Hence `(1/4) Σ_{m=1}^{Q₁} E_m(c) a_m^2 ≤ ⟨spectralFloorWeilMatrix c N y, y⟩` for all `y ∈ V_{Q₁}`.

### 3. Quasi-polynomial complement and split Schur synthesis

Decompose `x = y + u₀ + u₁ + w` orthogonally along `V_{Q₁} ⊂ V_{R₀} ⊂ V_{R₁}` with `Q₁ = ⌊L^{5/16}⌋₊`, `R₀ = ⌊exp √L⌋₊`, and quasi-polynomial far cutoff `R₁ = ⌊exp(L / (1 + log L)^5)⌋₊`.
- **Mid bands `u₀ ∈ V_{R₀} ∩ V_{Q₁}^⊥` and `u₁ ∈ V_{R₁} ∩ V_{R₀}^⊥`:** Since `(3/4) · (5/16) - 1/8 = 7/64 > 0`, `log(Q₁^{3/4} / c) ≥ (7/64) L_log → +∞`, so the packet floor retains `μ₀ = 1` on `u₀` and `μ₁ = √L / 32` on `u₁`.
- **Far band `w ∈ V_{R₁}^⊥` and band–far cross:** On `w ∈ V_{R₁}^⊥`, `conductor_tail_floor` gives `poleDefect M w ≥ k₁ P(w)` with `k₁ = log R₁ / (2 D_0) ≥ 4 θ_N L`, so Step 1 yields `(k₁ / 4) P(w) + (δ_7 / (8 c^7)) L S_7(w)` on `w`. Applying `exists_band_far_cross_le_channels` with `s_1 = s_2 = k₁ / 64`, `t_1 = t_2 = δ_7 L / (256 c^7)` (using `Σ_{n > M} w_n^2 ≤ S_7(w)`), and `γ = δ_7 L / (64 c^7)` (valid since `c ≥ L^{1/16}` gives `γ = O(L^{9/16}) ≪ k₁ / 32` and `(1 + log R₁)/L = O((1 + log L)^{-5})` beats `c^8 (1 + log c) Sg_1^2 = O((log L)^3)` by `(log L)^{-2} → 0`) absorbs `2|⟨W(u₀ + u₁), w⟩|` into half the mid-band and far-band reserves.
- **Conductor–complement Schur pairing `Σ_{m=1}^{Q₁} ⟨r_m, u₀ + u₁ + w⟩^2 / E_m(c)`:**
  - Against `u₀`: `deep_inverse_energy_mass_le` gives `Ψ_D = O((c^7 + Q₁^2 (1 + log Q₁)^2)/L) = O(L^{-1/8}) → 0`, and `Ψ ρ_top = O(L^{1/8 + 1/16 - 1/2} (log L)^3) → 0`.
  - Against `u₁` and `w|_{≤ M}`: `Ψ = O(L^{3/16} (log L)^3)` is strictly dominated by `μ₁ = √L / 32` and `k₁ / 32 ≍ L / (1 + log L)^5`.
  - Against `w|_{> M}`: Cauchy–Schwarz with weight `(N/n)^7` bounds `(Σ_{n > M} r_m(n) w_n)^2 ≤ W_7(r_m) S_7(w)`. Summing `W_7(r_m) / E_m(c)` gives `Σ_{m ≤ ⌈c⌉} (C_2 m^3 c^2 / L) / (κ_0 m^7 / c^7) ≤ (2 C_2 / κ_0) c^9 / L ≤ (2 C_2 / κ_0) (2 K₁)^9 L^{1/8}` plus `Σ_{⌈c⌉ < m ≤ Q₁} ‖r_m‖^2 / κ_0 = O(Q₁^2 c^2 (log L)^3 L^{1/16} / L) = O(L^{-1/16} (log L)^3) → 0`, which is absorbed by `(δ_7 / (128 c^7)) L ≥ (δ_7 / (128 (2 K₁)^7)) L^{1/8}` once `(2 K₁)^{16} ≤ δ_7 κ_0 / (512 C_2)`.

Thus `(spectralFloorWeilMatrix c N).PosDef` holds across `1 ≤ c ≤ 2 K₁ L^{1/8}`, giving `completeWeilEnergy tiltedUnitSpline c N x ≥ (κ_0 / (2 c^7)) ‖x‖^2` and whole-space positive definiteness.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea
- [ ] 1 → 2  fully-proven: corrected cutoff, residual proofs, prefix leakage and all cross payments
- [ ] 2 → 3  formalized: Lean theorems, foreground `lake --old env lean` checks, `#print axioms` PASS
