# Review-0311 §2.5: breakthrough questions below RH

- **ID:** R0311-25
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (loop)
- **Source:** `docs/reports/review-0311/obstacles-summary.md` §2.5.1–2.5.4
- **Statement:** Give a definite, Lean-formalized answer to each of the four §2.5 questions.

## Questions

| # | Question | Owner folder | Status |
|---|---|---|---|
| 2.5.1 | Two-collar recursion: `S^N_ε`, its evolution law, closed collar coupling at stages 1, 2 | `CanonicalSystemOfTheWindowTower/` | answered, Lean: `3-formalized/r0311-two-collar-recursion.md` |
| 2.5.2 | Hecke-equivariant completion: exact Weil = Krein identity with Hecke ↔ `T_p − Id` | `RenormalizedIntersectionTheory/MayerScattering/` | answered, Lean: `3-formalized/r0311-hecke-equivariant-completion.md` |
| 2.5.3 | Log-free unit-window occupancy `D_win` | `RHTower/WD/` | open |
| 2.5.4 | Growing conductors at the critical curve, then `M(N) → N` | `ArithmeticHodgeTheoryOfDegenerations/` | answered, Lean: `3-formalized/r0311-growing-conductors-at-the-critical-curve.md` |

## 2.5.3 — working notes

`D_win` ⟺ thin-Planck-shadow windows are `o(V)` (corpus): the total shadow measure of deep zeros is
`≤ Ce^{−rA}V/A` unconditionally, so `D_win` fails only through windows holding few, spread-out deep
zeros. Every deep zero is detected only on its own `1/log V` neighbourhood; a unit window holds
`log V` such cells.

Strength: a density bound `N(½ + δ, T) ≪ T^{1−cδ} log T` gives `≪ e^{−cA} T log T` deep zeros at
`δ = A/log T` for every fixed `c`, including the density hypothesis (`c = 2`); none is log-free. So
`D_win` is not implied by any density estimate of this shape, including DH. It needs either the
log-free count `D_zero` or a clustering law for deep zeros. Neither exists unconditionally.

## Ledger

| # | Conjecture | Result |
|---|---|---|
| 1 | Source Hecke for general `p` from a rational kernel identity as at `p = 2` | replaced: the number of cones grows with `p`; the cone count (tiling) is the uniform mechanism |
| 2 | Continue the general-`p` eigenvalue in `a` from a segment as at `p = 2, 3` | replaced: branch arguments leave the Mayer disc for `p ≥ 5`; continuation in `w` at every `a > 0` instead |
| 3 | `D_win` from Selberg's density `N(½ + A/log V, 2V) ≪ e^{−A/4}V log V` | fails by one `log V`: consistent with an `e^{−cA}` fraction of zeros deep and one per window |
| 4 | `D_win` from Littlewood's lemma on each Burnol window at `σ₁ = ½ + A/(2 log V)` | the linear and quadratic Taylor terms of `log ζM` have window averages `O(e^{−cA/2}/log V)` (signal `A/log V` wins), but the cubic remainder `∫|ζM − 1|³` has no cancellation and is `e^{−cA}` per window: loses `log V` |
| 5 | `D_win` from a Laguerre-inequality violation at a deep pair | the pair gives `2/δ² = 2log²V/A²`, the real zeros `≍ log²V`: no violation for large `A` |
| 6 | Sup-norm zero detection by `ζM ≈ 1` on unit windows | the mollified residual has `≍ log V` independent values per window; its maximum is `≍ e^{−Aθ}√(log log V)` → ∞ for fixed `A` |
| 7 | `D_win` from a nonnegative window functional `F_m ≥ 1` on deep windows with `ΣF_m ≤ ε(A)V`, `F_m = (log V/A)Σ_{ρ∈m}(β − σ₁)₊` | `Σ(β − σ₁)₊ ≪ e^{−cA/2}V` (integrated density) gives `ΣF_m ≪ e^{−cA/2}V log V/A`: one `log V` short, the same gap as the log-free density `D_zero` |
| 8 | `D_win` from a limit law for the window Littlewood functional `W_m log V` (review B20: a rate in a Selberg-type limit law) | the random-model limit is Gaussian with variance `≍ e^{−cA}`, so the limit law would give `D_win`; proving it needs the window integral of `log ζ − P_x` at precision `o(1/log V)` per window, which carries the deep-zero contribution itself: circular with current error terms |
| 9 | Missing sign changes of `Z(t)`: a deep pair forces `N − N₀ ≥ 2` in its window | shallow off-line pairs force the same; `N₀ ≥ κN` with `κ < 1` leaves `(1 − κ)V log V` |
| 10 | `D_win` from Planck-volume data (`unitWindow_planckShadow_sum_le`, mesoscopic push) | refuted as a route: `sparseModel_uniformPlanckVolume_not_windowOccupancy` satisfies every Planck-window bound for all `A, B ≤ log V` and violates `D_win` on 100% of windows |
| 11 | `D_win` from per-window moments `Σ_m N_m^p` | refuted as a route: the clustered model keeps `Σ N_m² ≥ c_A V log²V` under `D_win`, and `exists_logSpacingModel_zeroDensity_not_linearSqMoment` shows `O(V)` second moments exceed even `D_zero` |
| 12 | `D_win` from the growth rate of `rightHalfPort` (abscissa = maximal depth, `rightHalfPort_uniformBounded_tfae`) | per window the on-line zeros give a random-phase trace of size `≍ √log V`; a depth-`A/log V` zero shows only once `x^{δ} ≳ √log V` with `x ≤ V`, i.e. `A ≳ log log V`: the double-log stage (`almostAll_unitWindow_rightHalfPort_doubleLog_decay`). The log stage needs aggregation across windows, which reintroduces the `log V` covering loss |
| 13 | Zero detection by a mollifier `ζM_X − 1` (Selberg λ_d) at unit-spaced points, one per bad window | Selberg's mollifier makes `Σ_{n>X}|c_n|²n^{−2β} ≪ e^{−2Aθ}/A` log-free, but sampling at unit spacing (Gallagher) costs `∫|D||D'| ∼ log N`: the detector varies on scale `1/log N`. Random model: false-positive rate per window `≈ θ log V·exp(−A e^{2Aθ}/9)`, so the detector fires in almost every window as `V → ∞` |
| 14 | Window statistic with cancellation: `I_W = ∫_W log|ζM(σ₁+it)|dt`, Chebyshev on `I_W²` (log-free iff `E I_W² ≪ e^{−cA}/log²V`) | the prime part `∫_W Re P` has mean square `e^{−cA}/(θ log V)²` ✓; the error part `∫_W Re E` is exactly the deep-zero signal plus edge terms (interior on-line zeros integrate to `0` by contour shift). No mean value of `log|ζ|` independent of the zeros exists at precision `1/log V`: circular |
| 15 | Upper bound `log|1+ε| ≤ Re ε − Re ε²/2 + … + C_K|ε|^{K+1}` in `I_W` | the oscillatory terms cancel to `O(1/log V)`, the remainder needs `E|ε|^{K+1} ≪ 1/log V`; Gaussian moments give this only for `e^{cA} ≳ log log V` (a triple-log stage), and needs `∫|ζM − 1|^{2k}` for `k ≈ e^{cA}`, beyond the known moments (`k ≤ 2`) |
| 16 | Integer-valued window statistic (Wiener–Hopf index = right zeros of the window) | its total over windows is the deep-zero count `≪ e^{−rA}V log V/A`; integer signal does not help when deep zeros are spread |
| 17 | Clustering law: a window with one zero of depth `≥ A/log V` holds `≥ c(A) log V` zeros of depth `≥ A/(2log V)`; with `e^{−rA/2}/c(A) → 0` this gives `D_win` from `deepExtendedShell_orderSum_le` | needs arithmetic input: density data admit a single deep pair per window (corpus strip-zero countermodels); no mechanism found that couples one deep zero to `log V` others |
| 18 | Explicit formula, window-twisted primes `S(x, γ₀) = Σ_{n∼x} Λ(n)n^{−iγ₀}` | the large sieve gives `|S|² ≈ x log x` on average, i.e. on-line zeros contribute `√x·√log V`; a deep zero adds `x^{½+δ} = √x·e^{Aθ'}`: detectable only for `A ≳ log log V` |
| 19 | A functional vanishing on on-line zeros, nonzero on off-line ones | must be holomorphic for an explicit formula, and a holomorphic function vanishing on the critical line is `0`; reflection-antisymmetric functionals sum to `0` over the symmetric zero set |
| 20 | Sign-change deficit of `Z(t)` with depth read off from the size of the missed crossing | the deficit counts shallow pairs as well; reading depth off the missed crossing needs the local curvature, which is again a `1/log V`-scale quantity sampled `log V` times per window |
| 21 | Hermite–Biehler `E_h(z) = ξ(½ + h − iz)` at `h = A/log V` | `E_h` is HB at a height iff no zero is deeper than `h` there: the failure count is the `D_win` count restated |
| 22 | Short increments of `S(t)`: a deep pair turns two unit jumps into a smooth rise over width `δ`, so `∫|S(t+h) − S(t)|²` at `h ≪ 1/log V` counts on-line zeros | the known increment moments (Fujii, Tsang) have error `O(T)`, as large as the counting term at `h ≍ 1/log T`; resolving it would prove 100% of zeros on the line, which is stronger than `D_win` |
| 23 | Poisson defect `D(t) = P_1 * log|ζM|(σ₁ + i·)(t) − log|ζM(σ₁ + 1 + it)| = Σ_{β>σ₁} G(σ₁+1+it, ρ) ≥ 0`: a window-scale (width 1) nonnegative statistic, `≥ c'A/log V` on every bad window, with `∫_V^{2V} D = 2πΣ(β − σ₁)₊` | gives `#bad ≤ (log V/A)·2πΣ(β−σ₁)₊`; Selberg gives `Σ(β−σ₁)₊ ≪ Ve^{−cA}`, one `log V` short. `D_win` follows from the log-mean law `∫_V^{2V} log|ζM(½ + A/(2log V) + it)|dt = o_A(V/log V)` (random model: mean `0`), which is the open log-mean form B17 at this scale |
| 24 | Weil-functional detection per window: `W(g_γ) = Σ_ρ ĝ(t_ρ)conj(ĝ(t̄_ρ))` with `g` of log-length `L = λ log V/A`; on-line zeros give the positive background `≍ L²A/λ`, a deep pair gives `2Re[ĝ(γ+iδ)conj ĝ(γ−iδ)]` of size `L²e^{λ}`, so `λ = log A` makes the window's `W` negative; `W` = archimedean − twisted prime sum, mean square `≍ L⁴` | per point the deviation probability is `(log A/A)²` — `V`-free. But `W(g_γ)` sees the deep zero only for `|γ − γ_ρ| ≲ 1/L`, a window holds `≍ L ≍ log V` independent points, and the prime-sum maximum over a window is `≍ L²√(log log V)`. Since the Mellin length is capped at `V^{O(1)}`, the amplification `e^{λ}` is at most `e^{O(A)}`: for fixed `A` the noise maximum beats the deep-zero signal in almost every window. **No-go:** any proof that detects deep zeros through large values of Dirichlet polynomials of length `≤ V^{O(1)}` inside windows reaches at best `A ≳ log log log V`. `D_win` at fixed `A` needs a mechanism that is not large-value detection (clustering, or an exact window identity) |

