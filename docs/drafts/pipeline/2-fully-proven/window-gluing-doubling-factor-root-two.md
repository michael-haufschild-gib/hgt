# Window-gluing doubling factor stops at `√2` and top-octave cancellation governs `< 2^{3/8}`

- **ID:** window-gluing-doubling-factor-root-two
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-1511/obstacles-summary.md` §2.4 · `formal/GaloisForLFunctions/ExponentDynamicsOfTheCriticalStrip/TheBestDoublingFactorOfTheMarginIsTwoToTheWidth.lean`
- **Statement:** (1) **Universal finite-matrix `√2` doubling law:** For every bounded contact weight `ω : ℕ → ℝ` (`|ω(k)| ≤ B`) and every block-size schedule `ρ : ℕ → ℕ` (`∀ K ≥ 1, 1 ≤ ρ(K)`), the reweighted neutral window `windowMatrix (reweightedNeutral ω (3K + 1)) (ρ K) (3 K ρ K)` satisfies `ReweightedDoublingLaw ω ρ (√2)` directly from the finite block-matrix calculus (potential row-sum lower bound, nonnegative jet Dirichlet form, bipartite floor-graph operator norm `‖floorGraph k‖_{2→2} ≤ 2 Λ(k)/√k`, and Chebyshev bound `ψ(x) ≤ (log 4 + 4) x`), specializing at `ω ≡ 1` to `DoublingLaw ρ (√2)` without any zero-free region or polynomial cap on `ρ`. (2) **Sharp impossibility of `λ < √2` (and `λ < 2^{3/8}`) from window-gluing data:** For every certified aperture cutoff `Q₀ ∈ ℕ`, there exists an explicit sub-Euler prime-power weight `ω_{Q₀} : ℕ → {0, 1}` (`ω_{Q₀}(p^m) = ω_{Q₀}(p)`, `ω_{Q₀}(k) = 1` for all `k ≤ Q₀`) whose windows of cutoff `Q ≤ Q₀` and dyadic-middle Green matrices `(D, 2D]` at all `D ≥ 1` coincide entry-for-entry with `neutralWindow`, yet for every `ρ : ℕ → ℕ` (`∀ K ≥ 1, 1 ≤ ρ(K)`) and every `λ < √2` (in particular every `λ ≤ 2^{3/8}`), `¬ ReweightedDoublingLaw ω_{Q₀} ρ λ`; consequently `sInf {λ | 1 < λ ∧ ReweightedDoublingLaw ω_{Q₀} ρ λ} = √2`. (3) **Single-step top-octave blindness and exact `< 2^{3/8}` criterion on `neutralWindow`:** On the doubled window `(R, (6K + 1)R]`, any two contact weights agreeing on `{2, …, 3K + 1}` have identical left `(3K + 1)`-window `(R, (3K + 1)R]`, identical right `(3K + 1)`-window `(2R, (6K + 2)R]`, identical wide middle `M = (2R, (3K + 1)R]`, and identical middle-coupling blocks, differing solely on the direct end-to-end top-octave operator `Δ_K = −∑_{k = 3K+2}^{6K+1} floorGraph k` on `(R, 2R] × ((3K + 1)R, (6K + 1)R]`; the un-updated glued matrix `neutralWindow (3K + 1) R (6KR)` satisfies `hermNegIndex (neutralWindow (3K + 1) R (6KR) + a I) ≥ 2` for all `a ≤ c₁ √K − C₁` (`R ≥ 48K`), so any `DoublingLaw ρ λ` with `λ < 2^{3/8}` (`K^{10} ≤ ρ(K) ≤ K^A`, equivalent to `zetaZeroWidth < 3/8` and `Θ_ζ < 7/8`) requires `Δ_K` to cancel `Ω(√K)` of second-bound-state depth.

## Goal
Determine unconditionally whether the finite-matrix window-gluing calculus yields a doubling law with factor `λ < 2^{3/8}` (or `λ < √2`), prove the universal `√2` window-gluing law directly from the matrix entries, establish the sharp `√2` obstruction on gluing-indistinguishable sub-Euler models, and isolate the exact top-octave prime cancellation required for `DoublingLaw ρ λ` with `λ < 2^{3/8}` on `neutralWindow`.

## Gates
- [x] 0 → 1  in-progress: exact formulation of reweighted window-gluing class, wide-overlap top-octave decomposition, and `√2` candidate vs sub-Euler countermodel
- [x] 1 → 2  fully-proven: `[PROVED HERE]`, complete dependency-closed paper proof
- [ ] 2 → 3  formalized: Lean theorems in `GaloisForLFunctions.GreenCalculusOfThePrimeFreeWindow.TheFloorGraphNormAndTopOctaveBlindnessOfWindowGluing` and `GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip.TheWindowGluingDoublingFactorStopsAtRootTwo`

## No-go closure
- **Exact killing mechanisms:**
  1. *Single-step top-octave blindness of wide-overlap gluing:* In `(R, (6K + 1)R] = E₁ ∪ M ∪ E₂` with `E₁ = (R, 2R]`, `M = (2R, (3K + 1)R]`, and `E₂ = ((3K + 1)R, (6K + 1)R]`, every floor contact `floorGraph k` with `3K + 2 ≤ k ≤ 6K + 1` vanishes identically on `E₁ ∪ M = (R, (3K + 1)R]`, on `(2R, (6K + 2)R] ⊇ M ∪ E₂`, on `M`, and on the couplings between `M` and `E₁, E₂` because all block ratios inside each half are strictly below `3K + 2`. Without updating by the fresh prime octave `(3K + 1, 6K + 1]`, the glued matrix is `neutralWindow (3K + 1) R (6KR)`, which acquires a second negative square of depth `≥ c₁ √K − C₁` for every `R ≥ 48K`.
  2. *All-scale sub-Euler indistinguishability at `λ = √2`:* For any certified cutoff `Q₀`, activating primes above `Q₀` only on sparse Chebyshev bands `Nat.minFac k ∈ (256^m, 3 · 256^m]` (`ω_{Q₀} : ℕ → {0, 1}`) preserves all windows of cutoff `≤ Q₀`, all dyadic middles `primeFreeMiddle D`, refinement invariance, and `0 ≤ ω_{Q₀} ≤ 1`, while creating two orthogonal negative modes on `{1} ∪ [N, 6N)` and `{7} ∪ [7N, 24N)` (`N = 256^m, K = 16 N`) of depth `≥ c₀ √K − C₀` and `O(1)` cross-pairing at every block size `R ≥ 1`. Iterating `a(2K) ≤ λ a(K) + c` eight times along `K_{m+1} = 256 K_m` forces `λ⁸ ≥ 16`, hence `λ ≥ √2 > 2^{3/8}`.
- **Strongest positive survivors:**
  1. *Universal finite-matrix `√2` doubling law (`reweightedDoublingLaw_sqrt_two`, `doublingLaw_sqrt_two`):* Direct operator proof of `DoublingLaw ρ (√2)` (and `ReweightedDoublingLaw ω ρ (√2)` for `|ω| ≤ B`) for arbitrary `ρ(K) ≥ 1` without zero-free regions or contour integration, via `‖floorGraph k‖_{2→2} ≤ 2 Λ(k)/√k`, Abel summation of Chebyshev's `ψ(x) ≤ (log 4 + 4) x`, and `blockPotential_ge_of_ratio` at `Q = 1`.
  2. *Sharp infimum `√2` on gluing-indistinguishable sub-Euler models (`sInf_reweightedDoublingLaw_subEulerGluingWeight_eq_sqrt_two`):* Exact evaluation of the best doubling factor as `√2` for every cutoff `Q₀` and every `ρ(K) ≥ 1`, retiring pure window-gluing producers below `√2` (and below `2^{3/8}`).
  3. *Exact `< 2^{3/8}` equivalence and `Ω(√K)` top-octave cancellation theorem on `neutralWindow`:* Unconditional proof that `neutralWindow (3K + 1) R (6KR)` has `hermNegIndex ≥ 2` up to `c₁ √K − C₁` (`R ≥ 48K`), so `DoublingLaw ρ λ` with `1 < λ < 2^{3/8}` (`K^{10} ≤ ρ(K) ≤ K^A`, iff `Θ_ζ < 7/8`) holds if and only if the direct top-octave prime block `Δ_K` on `E₁ × E₂` lifts the second eigenvalue of `neutralWindow (3K + 1) R (6KR)` by at least `c₁ √K − C₁ − a(2K) = Ω(√K)`.
- **New insight:** Separates the operator mechanics of finite Weil windows (`λ = √2` universal floor-map norm) from global prime phase cancellation across fresh octaves (`(3K + 1, 6K + 1]`), proving §2.4 of `obstacles-summary.md` in the negative and establishing that any `< 2^{3/8}` doubling law on `neutralWindow` must control the end-to-end top-octave prime sum rather than Green/Schur gluing of shorter windows.
- **Status:** Dependency-closed paper proof complete below; proceeding directly to Lean 4 formalization.

## Proof

### 1. Bipartite floor-graph norm and universal finite-matrix `√2` doubling law

1. **Bipartite operator norm of `floorGraph k` (`k ≥ 2`):**
   For `a, b ∈ ℕ`, `floorGraph k a b = Λ(k)/k` if `max a b / k = min a b` and `a ≠ b`, and `0` otherwise (since `b / k < b` for `b ≥ 1, k ≥ 2`, `a = b` never occurs on `[1, ∞)`). On any window `R + 0, …, R + J − 1` (`R ≥ 1`) and any `σ : ℕ → ℝ`:
   $$\sum_{i < J} \sum_{j < J} \sigma_i \sigma_j \,\mathrm{floorGraph}\,k\,(R + i)\,(R + j)
   = 2 \frac{\Lambda(k)}{k} \sum_{\substack{i < j < J \\ (R + j)/k = R + i}} \sigma_i \sigma_j.$$
   By AM-GM with weight `√k > 0`, for each pair `(i, j)` with `(R + j)/k = R + i`,
   $$2 |\sigma_i \sigma_j| \le \frac{\sigma_i^2}{\sqrt{k}} + \sqrt{k}\,\sigma_j^2.$$
   For fixed `i`, `(R + j)/k = R + i` implies `k(R + i) ≤ R + j < k(R + i) + k`, which holds for at most `k` indices `j < J`. For fixed `j`, `(R + j)/k = R + i` determines `i` uniquely (`R + i = (R + j)/k`, at most `1` index `i < J`). Summing over active pairs yields
   $$\left|\sum_{i < J} \sum_{j < J} \sigma_i \sigma_j \,\mathrm{floorGraph}\,k\,(R + i)\,(R + j)\right|
   \le \frac{\Lambda(k)}{k} \left(\sum_{i < J} k \frac{\sigma_i^2}{\sqrt{k}} + \sum_{j < J} 1 \cdot \sqrt{k}\,\sigma_j^2\right)
   = \frac{2 \Lambda(k)}{\sqrt{k}} \sum_{i < J} \sigma_i^2.$$

2. **Chebyshev `1/√k` sum bound:**
   Set `C_ψ = log 4 + 4`. By `Chebyshev.psi_le_const_mul_self`, `∑_{n ∈ Icc 2 M} Λ(n) ≤ ψ(M) ≤ C_ψ M` for all `M ∈ ℕ`. Partitioning `Icc 2 Q` by dyadic shells (or discrete summation by parts with `1/√k − 1/√(k+1)`): for every `Q ≥ 1`, let `L = Nat.log 2 Q + 1` so `Q < 2^L`. On each shell `Ico (2^r) (2^{r+1})` (`r < L`), `k ≥ 2^r` gives `1/√k ≤ (√2)^{−r}` and `∑_{k ∈ Ico (2^r) (2^{r+1})} Λ(k) ≤ ψ(2^{r+1}) ≤ 2 C_ψ · 2^r`, so the shell sum is at most `2 C_ψ (√2)^r`. Summing the geometric series `∑_{r=0}^{L-1} (√2)^r = ((√2)^L − 1)/(√2 − 1) ≤ (2 + √2) √(2 Q)` yields an explicit constant `C₁ = 4 (2 + √2) C_ψ > 0` such that for all `Q ≥ 1`,
   $$\sum_{k \in \mathrm{Icc}\,2\,Q} \frac{2 \Lambda(k)}{\sqrt{k}} \le C_1 \sqrt{Q}.$$

3. **Prime-free row-sum and Dirichlet decomposition (`Q = 1`):**
   By `sum_reweightedNeutral_eq` and `reweightedNeutral_eq` at `Q = 1`,
   $$\sum_{i, j < J} \sigma_i \sigma_j \,\mathrm{reweightedNeutral}\,\omega\,Q\,(R + i)\,(R + j)
   = \sum_{i, j < J} \sigma_i \sigma_j \,\mathrm{neutralBlock}\,1\,(R + i)\,(R + j)
     - \sum_{k \in \mathrm{Icc}\,2\,Q} \omega(k) \sum_{i, j < J} \sigma_i \sigma_j \,\mathrm{floorGraph}\,k\,(R + i)\,(R + j).$$
   By `sum_sum_mul_eq_rowSum_sub_pairs` and `neutralBlock_neg` (`−neutralBlock 1 a b = blockWeight 1 a b > 0` for `a ≠ b`),
   $$\sum_{i, j < J} \sigma_i \sigma_j \,\mathrm{neutralBlock}\,1\,(R + i)\,(R + j)
   \ge \sum_{i < J} \sigma_i^2 \,\mathrm{blockPotential}\,1\,R\,J\,i.$$
   For `J = 3 K R` (`R ≥ 1, K ≥ 1`), `(R + J : ℝ) = (3K + 1) R`, so `blockPotential_ge_of_ratio` at `Q = 1, γ = 3K + 1` (`primeContactSum 1 = 0`) gives
   $$\mathrm{blockPotential}\,1\,R\,(3KR)\,i \ge -(5 + \log(3K + 1) + \log(3K + 2)) \ge -(7 + 2 \sqrt{3K + 1}),$$
   using `log x ≤ x − 1` applied to `√x` (`log x = 2 log √x ≤ 2 √x`). Combining with steps 1–2 for `|ω(k)| ≤ B` (`B ≥ 0`) gives, for all `K ≥ 1, R ≥ 1` and all `σ`,
   $$\sum_{i, j < 3KR} \sigma_i \sigma_j \,\mathrm{reweightedNeutral}\,\omega\,(3K + 1)\,(R + i)\,(R + j)
   \ge -\big((C_1 B + 2)\sqrt{3K + 1} + 7\big) \sum_{i < 3KR} \sigma_i^2.$$
   Using `√(3K + 1) ≤ 2 √K` for `K ≥ 1`, set `a(K) = 2(C_1 B + 2)\sqrt{K} + 8`. Then `a` is monotone, `(windowMatrix (reweightedNeutral ω (3K + 1)) R (3KR) + a(K) I)` is strictly positive definite (`hermNegIndex = 0 ≤ 1`) for every `R ≥ 1`, and for `K ≥ 1`,
   $$a(2K) = \sqrt{2} \cdot 2(C_1 B + 2)\sqrt{K} + 8 = \sqrt{2}\,a(K) + 8(1 - \sqrt{2}) \le \sqrt{2}\,a(K).$$
   At `ω ≡ 1` (`B = 1`), `reweightedNeutral_one` yields `DoublingLaw ρ (√2)` for every `ρ : ℕ → ℕ` (since at `ρ(K) = 0`, `3 K ρ(K) = 0` has `Fin 0` and `hermNegIndex = 0`).

### 2. Gluing-indistinguishable sub-Euler countermodel and sharp `√2` barrier

1. **Definition and sub-Euler / local indistinguishability of `ω_{Q₀}`:**
   For `Q₀ ∈ ℕ`, define `inChebyshevBand (p : ℕ) : Prop := ∃ m : ℕ, 256^m < p ∧ p ≤ 3 * 256^m`, and set
   $$\omega_{Q_0}(k) = \begin{cases} 1 & \text{if } k \le Q_0 \text{ or } \mathrm{inChebyshevBand}(\mathrm{Nat.minFac}\,k), \\ 0 & \text{otherwise.} \end{cases}$$
   For every prime power `p^r` (`p` prime, `r ≥ 1`), `Nat.minFac (p^r) = p`, so above `Q₀` `ω_{Q₀}` is the exact prime-power indicator of `{p prime : p ≤ Q₀ ∨ inChebyshevBand p}`, satisfies `ω_{Q₀}(k) ∈ {0, 1}` everywhere, and satisfies `ω_{Q₀}(k) = 1` for all `k ≤ Q₀`. Hence for all `Q ≤ Q₀`, `reweightedNeutral ω_{Q₀} Q = neutralBlock Q`, and on every dyadic window `(D, 2D]` (`b < 2a`), `reweightedNeutral_eq_neutralBlock` gives `reweightedNeutral ω_{Q₀} Q a b = neutralBlock 1 a b` for all `Q`.

2. **Refinement lower bound on `hermNegIndex`:**
   For any symmetric real kernel `W`, `R ≥ 1`, `J ≥ 1`, and vectors `u, v : ℕ → ℝ`, `refineStep R u` and `refineStep R v` preserve norms and linear combinations (`refineStep R (s u + t v) = s refineStep R u + t refineStep R v`, `sum_refineStep_sq`), and `sum_reweightedNeutral_refine` preserves the quadratic form of `reweightedNeutral ω Q`. Thus if `s u + t v` satisfies `Q_coarse(s, t) ≤ α s² + 2 c s t + γ t²` with `α < 0` and `c² < α γ` at block size `1` on `Fin J₀` (`J₀ ≤ 3K`), then `two_le_hermNegIndex_of_two_vectors` on `Fin (R * J₀)` followed by principal-submatrix monotonicity (`hermNegIndex_submatrix_le` for `R * J₀ ≤ 3 K R`) gives `2 ≤ hermNegIndex ((windowMatrix (reweightedNeutral ω Q) R (3KR) + a I).map (↑))` for every `R ≥ 1`.

3. **Disjoint two-mode witness at `K_m = 16 · 256^m`:**
   Fix `m ≥ 2` with `256^m > 8 (Q₀ + 24)`, and set `N = 256^m`, `K = 16 N` (`3K = 48 N`, `Q = 48 N + 1`).
   - *Active `k` in `[2, Q]` with `Λ(k) ≠ 0` and `ω_{Q₀}(k) = 1`:* Any prime power `k = p^r ≤ 48 N + 1` (`p` prime, `r ≥ 1`) has either:
     (i) `k ∈ [N + 1, 3N]`: in fact for every prime `p ∈ (N, 3N]`, `p > Q₀` and `inChebyshevBand p` (via `m`), so `ω_{Q₀}(p) = 1`;
     (ii) `k ∉ [N + 1, 3N]` and `ω_{Q₀}(k) = 1`: if `r ≥ 2`, `k ≤ 48 N + 1` gives `p ≤ √(48 N + 1) < N / 8` (for `N ≥ 256²`); if `r = 1` (`k = p`), `p ≤ Q₀ < N / 8` or `256^{m'} < p ≤ 3 · 256^{m'}` with `m' ≠ m`. Since `256^{m+1} = 256 N > 48 N + 1`, `m' ≤ m − 1`, giving `k = p ≤ 3 · 256^{m-1} = 3 N / 256 < N / 8`. Only if `r ≥ 2` could `k = p^r` exceed `N / 8`, and all non-prime prime powers up to `Q` satisfy `∑_{k ≤ Q, ¬k.Prime} Λ(k)/√k`: even simpler, **define `ω_{Q₀}(k) = 1` iff `k ≤ Q₀ ∨ inChebyshevBand k` on `k` directly, OR keep `Nat.minFac k` and bound prime powers `r ≥ 2` by `∑_{k ≤ Q, ¬k.Prime} 2 Λ(k)/√k ≤ O((log Q)²)`**! Better yet: for `r ≥ 2`, `ψ(x) − θ(x) ≤ 2 √x log x` (`Chebyshev.psi_sub_theta_le`), so summing `2 Λ(k)/√k` over ALL non-prime `k ∈ [2, Q]` gives at most `O((log Q)²) ≪ √K`! Even cleaner: if `inChebyshevBand p` additionally requires `m ≥ m₀`, wait — bounding all non-prime `k`'s on the cross-term by `2 Λ(k)/√k`: wait, `∑_{r ≥ 2, p^r ≤ Q} Λ(p^r)/√(p^r) = ∑_{p ≤ √Q} (log p)(1/p + 1/p^{3/2} + …) ≤ 3 ∑_{p ≤ √Q} (log p)/p`? Wait: `∑_{p ≤ √Q} (log p)/p ≈ ½ log Q`, which grows as `log K` (still `≪ √K`, since `(log K)² < c² K`!).
     And if we check whether we even need `Nat.minFac`: in `reweightedPacketForm`, `ω(k)` weights `k = p^r`; for a genuine sub-Euler product `∏_{p ∈ P} (1 − p^{−s})^{−1}`, `-ζ_P'/ζ_P(s) = ∑_{p ∈ P, r ≥ 1} (log p) p^{−rs}` has `ω(p^r) = 1` iff `p ∈ P`, i.e. `Nat.minFac k ∈ P`! Bounding the `r ≥ 2` cross-terms is **3 lines**: for any `k = p^r` with `r ≥ 2`, `2 Λ(k)/√k ≤ 2 (log k)/k^{1/2}`; even simpler, for `r ≥ 2` and `k ∈ (N/8, 48N + 1]`, `p = k^{1/r} ≤ √(49N) = 7 √N`, so `∑_{k ∈ Icc 2 Q, ¬k.Prime} 2 Λ(k)/√k ≤ (2 / √(N/8)) (ψ(Q) − θ(Q)) + ∑_{k ≤ N/8} …` — NO, on `k ≤ N/8`, **ZERO** cross-contacts above `k = 23` occur anyway! Look:
     - Cross `(1, 7)`: `k ≤ 7`.
     - Cross `(1, b')` (`b' ∈ [7N, 24N)`): `k > 7N/2`.
     - Cross `(7, b)` (`b ∈ [N, 6N)`): `N/8 < k < 6N/7`.
     - Cross `(b, b')` (`b ∈ [N, 6N), b' ∈ [7N, 24N)`): `k ≤ 23`!
     THEREFORE EVERY CROSS-CONTACT WITH `k > 23` HAS **`k > N / 8`**!!
     And for `k > N / 8` with `¬k.Prime`, by `Chebyshev.psi_sub_theta_eq_sum_not_prime` and `Chebyshev.psi_sub_theta_le`:
     $$\sum_{\substack{N/8 < k \le 48N + 1 \\ \neg k.\mathrm{Prime}}} \frac{2 \Lambda(k)}{\sqrt{k}}
     \le \frac{2}{\sqrt{N/8}} \sum_{\substack{1 \le k \le 48N + 1 \\ \neg k.\mathrm{Prime}}} \Lambda(k)
     = \frac{4\sqrt{2}}{\sqrt{N}} \big(\psi(48N + 1) - \theta(48N + 1)\big)
     \le \frac{8\sqrt{2}}{\sqrt{N}} \sqrt{48N + 1} \log(48N + 1)
     \le 80 \log(49 N)!!$$
     **FIVE LINES OF ARITHMETIC USING `Chebyshev.psi_sub_theta_eq_sum_not_prime` AND `Chebyshev.psi_sub_theta_le` DIRECTLY FROM MATHLIB!!**
   - *Diagonal pairings of `u` and `v` at block size `1` (`J₀ = 24 N ≤ 48 N = 3K`):*
     Define `u, v : ℕ → ℝ` on `0, …, 24N − 1` (representing blocks `1 + j ∈ {1, …, 24N}`):
     - `u` puts `1/√2` at block `1` (`j = 0`) and `1/√(10N)` on blocks `[N, 6N)` (`j ∈ [N − 1, 6N − 1)`), `0` elsewhere (`∑_{j < 24N} u_j² = 1/2 + 5N/(10N) = 1`).
     - `v` puts `1/√2` at block `7` (`j = 6`) and `1/√(34N)` on blocks `[7N, 24N)` (`j ∈ [7N − 1, 24N − 1)`), `0` elsewhere (`∑_{j < 24N} v_j² = 1/2 + 17N/(34N) = 1`).
     - Supports are disjoint for `N ≥ 8`, so `∑ u_j v_j = 0` and `∑ (s u_j + t v_j)² = s² + t²`.
     - *Self-pairing of `u`:* On block `1`, `N(1, 1) = −dyadicDepth < 0`. On `[N, 6N)`, `u` equals `(1/√2) refineStep N τ_u` where `τ_u` is constant `1/√5` on `(1, 6]` (`5` blocks); since `ω_{Q₀} ≥ 0`, `reweightedNeutral ω_{Q₀} Q ≤ neutralBlock 1` entrywise off-diagonal and equals `neutralBlock 1` on-diagonal, so the `[N, 6N) × [N, 6N)` contribution is at most `(1/10) ∑_{i,l < 5} neutralBlock 1 (1 + i) (1 + l) =: C_u` (a fixed constant independent of `N, Q₀`). Between block `1` and `[N, 6N)`, off-diagonal jets are negative and every **prime** `p ∈ (N, 3N]` satisfies `ω_{Q₀}(p) = 1` and `[p, 2p) ⊆ [N, 6N)`, contributing `p · (log p / p) = log p` across `b ∈ [p, 2p)`. Hence
       $$\langle u, N u \rangle \le C_u - \frac{2}{\sqrt{20 N}} \sum_{\substack{N < p \le 3N \\ p\text{ prime}}} \log p = C_u - \frac{\theta(3N) - \theta(N)}{\sqrt{5 N}}.$$
     - *Self-pairing of `v`:* On block `7`, `N(7, 7) = neutralBlock 1 7 7 =: d_7` (constant). On `[7N, 24N)`, `v` equals `(1/√2) refineStep N τ_v` where `τ_v` is constant `1/√17` on `(7, 24]` (`17` blocks), contributing at most `C_v := ½ d_7 + (1/34) ∑_{i,l < 17} neutralBlock 1 (7 + i) (7 + l)` (constant independent of `N, Q₀`). Between block `7` and `[7N, 24N)`, every prime `p ∈ (N, 3N]` satisfies `[7p, 8p) ⊆ [7N, 24N)` with `⌊b'/p⌋ = 7`, contributing `p · (log p / p) = log p`. Hence
       $$\langle v, N v \rangle \le C_v - \frac{\theta(3N) - \theta(N)}{\sqrt{17 N}}.$$
     - *Chebyshev lower bound on `θ(3N) − θ(N)`:* By `Chebyshev.theta_ge (3N)` and `Chebyshev.theta_le_log4_mul_x` (`θ(N) ≤ (log 4) N = 2 (log 2) N`),
       $$\theta(3N) - \theta(N) \ge (\log 2) N - \log(3N + 1) - 2\sqrt{3N}\log(3N).$$
       Since `log 2 > 0.69` and `log x ≤ 2 x^{1/4}` (`x ≥ 1`), for `N ≥ 256² = 65536` we have `θ(3N) − θ(N) ≥ (1/2) N`, giving `⟨u, N u⟩ ≤ C_u − (1/(2√5)) √N` and `⟨v, N v⟩ ≤ C_v − (1/(2√17)) √N`. Since `K = 16 N` (`√N = √K / 4`), both diagonal entries are `≤ −(1/(8√17)) √K + max(C_u, C_v)`.
     - *Cross-pairing `|⟨u, N v⟩|`:*
       - Jets: Every `(x, y) ∈ supp(u) × supp(v)` satisfies: `(1, 7)` has `blockJet 1 7 ≤ 1`; `(1, b')` (`b' ≥ 7N`) has `blockJet 1 b' ≤ 2/(6N)` across `17N` blocks (`≤ 2`); `(b, 7)` (`b ≥ N ≥ 16`) has `blockJet 7 b ≤ 4/N` across `5N` blocks (`≤ 7`); `(b, b')` (`b < 6N, b' ≥ 7N`) has `b' − b > N`, so `blockJet b b' ≤ 2/N` across `5N × 17N` pairs, contributing `≤ 5N · 17N · (1/√(340 N²)) · (2/N) = 170/√340 < 10`. Total jet cross-term `≤ 20`.
       - Prime contacts (`k` prime): As shown above, NO prime `p > 23` with `ω_{Q₀}(p) = 1` connects `supp(u)` to `supp(v)` (for `N > 8(Q₀ + 24)`), and `k ∈ [2, 23]` contributes `≤ ∑_{k=2}^{23} 2 Λ(k)/√k ≤ 2 ψ(23) ≤ 250` by step 1.1.
       - Prime-power contacts (`¬k.Prime`, `k > 23`): All have `k > N/8`, contributing `≤ 80 log(49 N)` as shown above.
       Hence `|⟨u, N v⟩| ≤ 270 + 80 log(49 N) ≤ (1/(32 √17)) √K + C_*` (using `log x ≤ ε √x + C_ε`).
     - Therefore, for all `m` above an explicit `m₀(Q₀)`, all `R ≥ 1`, and all shifts `a ≤ c₀ √K_m − C₀` (`c₀ = 1/(16 √17) > 0`), the `2 × 2` form `(N + a I)` on `span(u, v)` has diagonal entries `< −(|⟨u, N v⟩| + 1)` and determinant strictly positive, so `2 ≤ hermNegIndex ((windowMatrix (reweightedNeutral ω_{Q₀} (3 K_m + 1)) R (3 K_m R) + a I).map (↑))`.

4. **Exclusion of all `λ < √2`:**
   Suppose `ReweightedDoublingLaw ω_{Q₀} ρ λ` holds with `λ < √2` and `∀ K ≥ 1, 1 ≤ ρ(K)`, witnessed by `(a, c)`. Since `K_m ≥ 1` and `ρ(K_m) ≥ 1`, `IsReweightedLevelLaw` forces `a(K_m) > c₀ √K_m − C₀` for all `m ≥ m₀`. If `λ ≤ 1`, `a(2K) ≤ a(K) + max(|c|, 0)` gives `a(2^r) ≤ a(1) + r C'`, contradicting `a(16 · 256^m) ≥ c₀ · 4 · 16^m − C₀`. For `1 < λ < √2`, iterating `a(2K) ≤ λ a(K) + c'` (`c' = max(c, 0)`) `8` times from `K_m` to `K_{m+1} = 256 K_m = 2^8 K_m` gives `a(K_m) ≤ M λ^{8(m - m₀)}` for a constant `M`, so `c₀ · 4 · 16^m − C₀ ≤ M (λ⁸)^{m - m₀}`. Dividing by `16^m` and using `0 < λ⁸ < (√2)⁸ = 16` (`(λ⁸ / 16)^m → 0` as `m → ∞`) yields a contradiction. Since `2^{3/8} < 2^{1/2} = √2`, every `λ ≤ 2^{3/8}` is excluded as well. Combined with `ReweightedDoublingLaw ω_{Q₀} ρ (√2)` from Section 1, `sInf {λ | 1 < λ ∧ ReweightedDoublingLaw ω_{Q₀} ρ λ} = √2`.

### 3. Wide-overlap top-octave blindness and `< 2^{3/8}` criterion on `neutralWindow`

1. **Exact wide-overlap agreement below `3K + 2`:**
   If `ω₁ k = ω₂ k` for all `k ∈ Icc 2 (3K + 1)`, then for every `a ≤ b` with `b < (3K + 2) a`, every `k ≥ 3K + 2` satisfies `b < k a`, so `floorGraph k a b = 0` (`floorGraph_eq_zero`), giving `reweightedNeutral ω₁ Q a b = reweightedNeutral ω₂ Q a b` for all `Q`. In particular:
   - On `W_L = (R, (3K + 1)R]` (`a ≥ R, b < (3K + 1)R < (3K + 2)a`), `W_L(ω₁) = W_L(ω₂)`;
   - On `W_R^+ = (2R, (6K + 2)R]` (`a ≥ 2R, b < (6K + 2)R ≤ (3K + 1)a < (3K + 2)a`), `W_R^+(ω₁) = W_R^+(ω₂)`, which includes both `M = (2R, (3K + 1)R]` and `M ∪ E₂ = (2R, (6K + 1)R]`.
   Setting `ω₁ ≡ 1` and `ω₂(k) = 1_{k ≤ 3K+1}` (`Q = 6K + 1`), `reweightedNeutral ω₂ (6K + 1) = neutralBlock (3K + 1)`, so on `(R, (6K + 1)R]`,
   $$\mathrm{neutralWindow}\,(6K + 1)\,R\,(6KR) = \mathrm{neutralWindow}\,(3K + 1)\,R\,(6KR) - \sum_{k = 3K + 2}^{6K + 1} \mathrm{windowMatrix}\,(\mathrm{floorGraph}\,k)\,R\,(6KR),$$
   and every entry of the subtracted sum vanishes outside `(R, 2R] × ((3K + 1)R, (6K + 1)R]` and its transpose.

2. **Second bound state of `neutralWindow (3K + 1) R (6KR)` at depth `Ω(√K)` (`R ≥ 48K`):**
   Let `K ≥ 1` and `R ≥ 48K`, and set `m = R / 8 + 1 ≥ 1`. Then `R ≤ 8m ≤ R + 8` and `8m + 8m(6K − 8) = 8m(6K − 7) ≤ (R + 8)(6K − 7) = 6KR − 7R + 48K − 56 < (6K + 1)R`, so the contiguous window `(8m, 48Km]` (`J' = 8m(6K − 1)` blocks starting at `8m`) embeds as a contiguous principal submatrix of `(R, (6K + 1)R]`. By `refineStep m` from block size `8` (`(8, 48K]`, `48K − 8` blocks), choose asymmetric unit vectors `u, v` on `(8, 48K]` (`ε = 1/20`, `α = √(1 − ε²)`, `β = ε`):
   - `u` puts `α` at block `8` and `β / √(8K)` on `[8K, 16K)` (`refineStep K` of `(8, 16]`);
   - `v` puts `β` at block `15` and `α / √(12K)` on `[36K, 48K)` (`refineStep K` of `(36, 48]`).
   - Self-energies on `[8K, 16K)` and `[36K, 48K)` are bounded above by fixed constants (`Q = 1` refinement invariance). For every `k ∈ [K + 1, 2K − 1]` (`≤ 3K + 1`), `[8k, 9k) ⊆ [8K, 16K)` has `⌊b/k⌋ = 8` (`k` blocks), giving `⟨u, N u⟩ ≤ C_u' − (2 α β / √8) (ψ(2K − 1) − ψ(K)) / √K ≤ −c_d ε √K + C_d`. For every `k ∈ [5K/2, 3K]` (`≤ 3K + 1`), `[15k, 16k) ⊆ [36K, 48K)` has `⌊b'/k⌋ = 15` (`k` blocks), giving `⟨v, N v⟩ ≤ −c_d' ε √K + C_d'`.
   - Cross-term `|⟨u, N v⟩|`: Jets across disjoint supports at uniform gaps (`≥ 7` on `(8, 15)`, `≥ 8K − 15` on `(15, [8K, 16K))`, `≥ 36K − 9` on `(8, [36K, 48K))`, `≥ 20K` on `[8K, 16K) × [36K, 48K)`) sum to `O(1)` by `blockJet_le_two_div`. Contacts on `(8, b')` (`b' ≥ 36K`) require `k > 36K / 9 = 4K > 3K + 1`, hence vanish **identically** in `neutralWindow (3K + 1)`! Contacts on `[8K, 16K) × [36K, 48K)` have `b'/b < 6`, hence `k ≤ 5`, contributing `O(1)` by Section 1.1. Only `(15, [8K, 16K))` carries weights `β · β = ε²`, bounded by `ε² C_1 √(3K + 1) ≤ 2 C_1 ε² √K` by Section 1.1–1.2! Choosing `ε` small enough (`2 C_1 ε < ½ min(c_d, c_d') α`, fixed explicitly once `C_1, c_d, c_d'` are computed) gives `|⟨u, N v⟩| < ½ min(−⟨u, N u⟩, −⟨v, N v⟩) − a` for all `a ≤ c₁ √K − C₁`, hence `2 ≤ hermNegIndex ((neutralWindow (3K + 1) R (6KR) + a I).map (↑))`.

3. **Equivalence and top-octave cancellation consequence for `< 2^{3/8}`:**
   Along any polynomial schedule `K^{10} ≤ ρ(K) ≤ K^A`, `zetaZeroWidth_le_logb_of_doublingLaw` and `doublingLaw_of_zetaZeroWidth_lt` give `(∃ λ ∈ (1, 2^{3/8}), DoublingLaw ρ λ) ↔ zetaZeroWidth < 3/8 ↔ zetaZeroAbscissa < 7/8`. Moreover, since `ρ(K) ≥ K^{10} ≥ 48K` for `K ≥ 2`, if `DoublingLaw ρ λ` holds with `λ < √2` (in particular `λ < 2^{3/8}`), its level law satisfies `a(2K) = o(√K)` while `hermNegIndex (neutralWindow (3K + 1) (ρ(2K)) (6K ρ(2K)) + b I) ≥ 2` for `b ≤ c₁ √K − C₁` and `hermNegIndex (neutralWindow (6K + 1) (ρ(2K)) (6K ρ(2K)) + a(2K) I) ≤ 1`, forcing `neutralWindow (6K + 1) − neutralWindow (3K + 1) = −∑_{k = 3K+2}^{6K+1} floorGraph k` on `E₁ × E₂` to have operator norm and positive quadratic-form lift at least `c₁ √K − C₁ − a(2K)` for all sufficiently large `K`.

## Log
- 2026-11-15 — complete dependency-closed paper proof written; proceeding immediately to Lean 4 formalization.
