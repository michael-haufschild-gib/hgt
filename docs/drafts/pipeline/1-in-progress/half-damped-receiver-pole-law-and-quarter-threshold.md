# The half-damped receiver reads the Dirichlet series at the critical point

- **ID:** half-damped-pole-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** THIM README §5 "The parity pair" (open: is a completely multiplicative `±1` sign
  whose `−1`-primes have relative density `δ` paid at half damping exactly when `δ > 1/4`? only the
  sparse necessary condition is proved); THIM §3.16 pole law (proved only for `k ⋆ q`).
- **Statement:** For every weight `|c(d)| ≤ K d^{−1/2}` the Mellin pairing of its centred prefix is
  `Φ_c(s) = ζ(s)(C(s) − C(1))`, `C(s) = Σ c(d)d^{−s}`, on `Re s > 1/2`, `s ≠ 1`; a paid receiver
  forces `|C(σ) − C(1)| = O((σ − 1/2)^{−1/2})`; hence a `±1` pattern whose flipped primes have upper
  Dirichlet density `< 1/4` is never paid.

## Goal

THIM's pole law decides the receiver only for convolutions `k ⋆ q` with `k` in the critical Wiener
algebra; the density-`δ` sign patterns are outside it (`μ ⋆ f` has `Σ_{p∈P}1/p = ∞`). The identity
below decides the receiver at half damping for **every** weight of the half-damped class by one
analytic datum, the size of its Dirichlet series as `σ ↓ 1/2`. It settles the necessary half of the
`1/4` law.

## Paper proof

Fix `c` with `c(0) = 0`, `|c(d)| ≤ K d^{−1/2}`, `m = Σ c(d)/d`, `A(n) = weightCenteredPrefix c m n`.
Put `α_d(n) = ⌊n/d⌋ − n/d` (`|α_d(n)| ≤ min(1, n/d)`), cells `Δ_n(s) = n^{−s} − (n+1)^{−s}`.

1. **Prefix as a modulus sum.** `A(n) = Σ_d c(d) α_d(n)` (from `weightCenteredPrefix_eq_split`; for
   `d > n`, `α_d(n) = −n/d`).
2. **One modulus.** For `d ≥ 1`, `Re s > 0`, `s ≠ 1`: `Σ_n α_d(n)Δ_n(s) = ζ(s)(d^{−s} − 1/d)`.
   The series converges absolutely (`|Δ_n(s)| ≤ |s| n^{−σ−1}`). Summation by parts with
   `α_d(n) − α_d(n−1) = [d ∣ n] − 1/d`, `α_d(0) = 0` gives the partial sum to `N`:
   `Σ_{n≤N}([d∣n] − 1/d)n^{−s} − α_d(N)(N+1)^{−s}`. Along `N = dM`, `α_d(dM) = 0` and
   `Σ_{n ≤ dM}[d∣n]n^{−s} = d^{−s}S_M`, `S_M = Σ_{k≤M}k^{−s}`; with `S_M = M^{1−s}/(1−s) + R_M`,
   `R_M → ζ(s)` (`RHTower.tendsto_sum_cpow_sub_pow`), the two main terms
   `d^{−s}M^{1−s} = d^{−1}(dM)^{1−s}` cancel exactly, leaving `d^{−s}R_M − R_{dM}/d → ζ(s)(d^{−s} − 1/d)`.
3. **Fubini.** With `θ = (σ + 1/2)/2 ∈ (1/2, σ)`, `min(1, n/d) ≤ (n/d)^θ`, so
   `Σ_{n,d}|c(d)α_d(n)Δ_n(s)| ≤ K|s| Σ_d d^{−1/2−θ} Σ_n n^{θ−σ−1} < ∞`. Hence
   `Φ_c(s) := Σ_n A(n)Δ_n(s) = Σ_d c(d)ζ(s)(d^{−s} − 1/d) = ζ(s)(C(s) − m)`.
4. **ζ on `(1/2, 1)`.** For real `σ ∈ (0,1)`, `Σ_{k≤N}k^{−σ} − N^{1−σ}/(1−σ) ≤ 1 − 1/(1−σ)` (integral
   comparison), so `Re ζ(σ) ≤ −σ/(1−σ)` and `|ζ(σ)| ≥ σ/(1−σ) ≥ 1` on `[1/2, 1)`.
5. **General pole law.** If every pronic energy is `≤ E`, then `|Φ_c(σ)| ≤ √E√(2σ²(1 + 1/(2σ−1)))`
   (`abs_tsum_mul_mellinCell_le`), so `|C(σ) − m| ≤ ((1−σ)/σ)√E√(2σ²(1 + 1/(2σ−1)))`.
6. **The quarter law, necessary half.** Let `f` be completely multiplicative with `f(p) = ±1`,
   `P = {p : f(p) = −1}`, and suppose `Σ_{p∈P}p^{−w} ≤ δ log(1/(w−1)) + B` on `w ∈ (1, 3/2)` with
   `δ < 1/4`. For `c(d) = f(d)d^{−1/2}`, `C(σ) = F(σ + 1/2)`, `F(w) = Σ f(n)n^{−w} =
   Π_p(1 − f(p)p^{−w})^{−1} ≥ exp(Σ_p f(p)p^{−w})` (`(1−x)^{−1} ≥ e^x`), and
   `Σ_p f(p)p^{−w} = Σ_p p^{−w} − 2Σ_{p∈P}p^{−w} ≥ (1−2δ)log(1/(w−1)) − 1 − 2B` (from
   `ζ(w) ≥ 1/(w−1)` and `(1−x)^{−1} ≤ e^{x+x²}`). So `C(σ) ≥ e^{−1−2B}(σ − 1/2)^{−(1−2δ)}`, while
   step 5 caps it by `O((σ−1/2)^{−1/2})`; `1 − 2δ > 1/2` gives the contradiction as `σ ↓ 1/2`.

## Phase 2: the exact spectral formula and the sharp law for the constant-sign model

7. **Complex cells.** `|Δ_n(s)| ≤ (|s|/σ)Δ_n(σ)` (FTC for `x ↦ x^{−s}`). Steps 2–3 run verbatim for
   complex `s`, `1/2 < Re s < 1`: `Φ_c(s) = ζ(s)(C(s) − m)`.
8. **Plancherel.** For `σ > 1/2` put `h(u) = A(⌊e^u⌋)e^{−σu}` on `u ≥ 0` (`|h| ≤ 5K e^{(1/2−σ)u}`, so
   `h ∈ L¹ ∩ L²`). Its Fourier transform at `t/2π` is `Φ_c(σ+it)/(σ+it)` (the step decomposition
   `[log n, log(n+1))`), and `∫|h|² = Σ_n A(n)²Δ_n(2σ)/(2σ)`. Hence
   `Σ_n A(n)²Δ_n(2σ) = (σ/π)∫|ζ(s)(C(s) − m)/s|² dt`, an identity in `[0, ∞)` for every `σ > 1/2`.
9. **Receiver from line energy.** For each `T`, `Σ_{n≤T}A(n)²Δ_n(2σ) → E_T` as `σ ↓ 1/2`, so
   `sup_T E_T ≤ (3/4π) sup_{σ∈(1/2,3/4)}∫|ζ(s)(C(s)−m)/s|²dt`; conversely Fatou gives the reverse.
   The half-damped receiver **is** the boundary `H²` energy of `ζ(s)(C(s) − C(1))/s` on `Re s = 1/2`.
10. **The constant-sign model.** `f_z(n) = z^{Ω(n)}`, `0 ≤ z < 1/2`. Euler product and
    `|log(1+y) − y| ≤ |y|²` give `|F_z(w)| ≤ e^{2S}|ζ(w)|^z` on `Re w > 1` (`S = Σ_p p^{−2}`). With
    `|ζ(w)| ≤ log|Im w| + 5` (`norm_riemannZeta_le_log_add`, `|Im w| ≥ 2`) and `|ζ(w)| ≤ C/|w−1|`
    near `w = 1`: `|C(s) − m| ≤ C(1 + |t|^{−z})log(2+|t|)`. Split `|t| ≤ 2` (continuity of `ζ`,
    `∫|t|^{−2z} < ∞` since `2z < 1`) and `|t| ≥ 2` (dyadic windows,
    `∫_T^{2T}|ζ|² ≤ C T(1+log T)³`, weight `T^{2z−2}·log^{2z}`: summable since `2z < 1`).
    Hence `f_z(d)d^{−1/2}` is paid for every `0 ≤ z < 1/2`; for `z > 1/2` it is not (pole law with
    `F_z(w) ≥ κ(w−1)^{−z}`). The threshold `z = 1/2` (`δ = 1/4`) is exact.

## Phase 3: the pole law below half damping, without factorisation

11. **Uniform pole law.** If `Σ|c(d)|d^{−θ} < ∞` for every `θ > a`, `1/2 < a < 1`, step 5 holds for
    every `σ ∈ (a, 1)` with `θ = (a+σ)/2`, and `((1−σ)/σ)√(2σ²(1 + 1/(2σ−1))) ≤ √(2(1 + 1/(2a−1)))`.
    So a paid `c` has `|C(σ) − m| ≤ √E√(2(1 + 1/(2a−1)))` on `(a, 1)`; `|C(σ)| → ∞` as `σ ↓ a`
    forces an unbounded receiver. On `𝒞(K, ε)`, `ε < 1/2`: `a = 1 − ε`.
12. **Product law.** `Σ(k⋆q)(n)n^{−σ} = K(σ)Q(σ)` for absolutely convergent `K, Q` (fiberwise
    summation over `n = jd`, `n^{−σ} = j^{−σ}d^{−σ}`); `|k⋆q| ≤ |k|⋆|q|` gives absolute convergence.
13. **Convolutions.** `q ≥ 0` in `𝒞(K, ε)`, `Σ q(d)d^{−(1−ε)} = ∞`, `Σ|k(j)|j^{−(1−ε)} < ∞`,
    `K(1−ε) ≠ 0`: dominated convergence gives `K(σ) → K(1−ε)`; finite partial sums are continuous
    and `Q(σ) ≥` any partial sum, so `Q(σ) → ∞`. Step 11 makes `k⋆q` unpaid. This contains
    `not_receiverBounded_dirichletConv_of_drift_critical` for `ε < 1/2`: there `k` must be in the
    critical Wiener algebra (`Σ|k|j^{−1/2} < ∞`) and `q` must have the drift
    `nΣ_{(n,2n]}q(d)/d ≥ κn^{1−ε}`, which implies `Σ_{(n,2n]}q(d)d^{−(1−ε)} ≥ κ` per dyadic block.

## Phase 4: the boundary `z = 1/2` is unpaid

14. **Lower Euler bound.** For `0 ≤ z ≤ 1`, `Re w > 1`, `x_p = p^{−w}`: `|−log(1−zx) − zx| ≤ z²|x|²`
    and `|z log(1−x) + zx| ≤ z|x|²` (`|x| ≤ 1/2`), so `|log F_z(w) − z log ζ(w)| ≤ 2S` and
    `|F_z(w)| ≥ e^{−2S}|ζ(w)|^z` (the reverse of step 10's bound, same bracket).
15. **Near the pole.** `ζ(w) − 1/(w−1)` is bounded by `B` on `0 < |w−1| ≤ 1`, so
    `|ζ(w)| ≥ 1/(2|w−1|)` for `|w−1| ≤ ρ = 1/(2B+2)`. Near `s = 1/2`: `|ζ(1/2)| ≥ 1` (step 4) and
    continuity give `|ζ(s)| ≥ 1/2` on `|s − 1/2| ≤ r₁`.
16. **Log divergence.** With `s = σ+it`, `u = σ − 1/2`, `w = s + 1/2`, `|t| ≤ r = min(ρ, r₁)/2`,
    `u ≤ r`: `|C(s)|² = |F_{1/2}(w)|² ≥ e^{−4S}/(2|u+it|)`, `(|C| − |m|)² ≥ |C|²/2 − m²`, `|s| ≤ 1`.
    So `∫|ζ(s)(C(s)−m)/s|²dt ≥ (1/4)∫_{|t|≤r}(e^{−4S}/(4|u+it|) − m²)dt ≥ κ log(1/u) − B'`
    (`∫_{−r}^{r}dt/|u+it| = 2 arsinh(r/u)`).
17. **Contradiction.** `Δ_n(2σ) ≤ 2σn^{−2σ−1} ≤ 4σ/(n(n+1))` for `σ ≥ 1/2`, so a paid receiver has
    `Σ_n A(n)²Δ_n(2σ) ≤ 4σE`, and step 8 gives `∫|ζ(C−m)/s|²dt ≤ 4πE` for every `σ ∈ (1/2, 1)`,
    contradicting step 16 as `u ↓ 0`. Hence `f_z(d)d^{−1/2}` is paid **iff** `0 ≤ z < 1/2`.

## Phase 5: negative `z`, the full interval `[−1, 1]`

18. For `−1 ≤ z < 0` the Euler-factor bracket bound holds verbatim with `|z| ≤ 1`, so
    `|F_z(w)| ≤ e^{2S}(1/|ζ(w)|)^{|z|}`. On `Re w > 1`: `1/|ζ| ≤ (20/A)log⁷|t|` on the de la Vallée
    Poussin strip (`RHTower.norm_inv_riemannZeta_le`), `−log|ζ| ≤ (3/4)log(1 + 1/(σ−1)) +
    (1/4)log B(2t)` beyond it (`RHTower.Sieve.neg_log_norm_riemannZeta_le_of_bound`), and
    `|ζ(w)| ≥ 1/(2|w−1|)` plus compactness on `|t| ≤ 9`. So `|C(s)|² ≪ 1 + log^{14}|t| ≪ |t|^{1/2}`
    and the dyadic mean square of step 10 pays the line energy: paid for every `z ∈ [−1, 0)`.
    With steps 10, 16–17: `z^{Ω(d)}d^{−1/2}` is paid **iff** `z < 1/2`, for all `z ∈ [−1, 1]`; the
    interior `(−1, 1)` is pretentious to no character, outside `receiver_trichotomy`.

## Selectivity and scope

- The density hypothesis is on `P` only through a Dirichlet upper density; it covers primes in
  residue classes of total density `< 1/4`. Liouville (`δ = 1`) and real characters (`δ = 1/2`) sit
  on the paid side, consistent with the corpus parity pairs.
- Sufficiency (`δ > 1/4 ⇒ paid`) is not claimed here; it needs bounds of `F` on `Re w ∈ (1, 3/2]`
  off the real axis (planned via the Plancherel form of step 3 for the constant-sign model
  `f(p) ≡ z`, `z = 1 − 2δ`).

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven on paper (steps 1–17)
- [x] 2 → 3  formalized (steps 1–18)
- [ ] 3 → 4  publication-ready

## Log
- 2026-10-23 — formalized: `TheHalfDampedReceiverReadsTheDirichletSeriesAtTheCriticalPoint`,
  `APaidReceiverBoundsTheDirichletSeriesUpToItsAbscissa`,
  `TheHalfDampedReceiverIsTheBoundaryEnergyOfItsDirichletSeries`,
  `TheQuarterLawOfTheConstantSignPattern` (THIM), all wired, axioms clean. The δ < 1/4 statement
  for general patterns is a criterion (density premise), not an unconditional instance.
- 2026-10-23 — step 18 formalized: `TheQuarterLawOfTheConstantSignPatternOnTheFullRange`
  (`receiverBounded_constantSign_iff_full`), wired, axioms clean.
- 2026-10-23 — created; paper proof complete. Novelty: corpus search finds the pole law only for
  `k ⋆ q` (`not_receiverBounded_dirichletConv_of_drift_critical`) and the sparse-flip law.
