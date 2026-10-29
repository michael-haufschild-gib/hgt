# Small-time growth of the de Bruijn–Newman nonreal count (Q-II)

- **ID:** heat-count-small-time-growth
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (the three rungs); paper-level REDUCTION (the dictionary below)
- **Source:** `docs/reports/review-2810/obstacles-summary.md` Q-II; receivers in `index-exit-hodge-defect-collision-count`
- **Statement:** As `t ↓ 0`, `N(t) := nonrealZeroCount t ≤ e^{o(1/t)}`, then `N(t) ≤ C t^{−A}`, then `N(t) ≤ C`.

## Goal
`N(t)` bounded is `FiniteOffLine` (`finite_nonreal_zeros_iff_exists_nonrealZeroCount_le`,
`index_exit_first_rung_tfae`, Lean). An effective bound reduces RH to a finite computation.

## Gates
- [x] 0 → 1  in-progress: receivers and tools located in Lean; reduction found (below)
- [ ] 1 → 2  fully-proven
- [ ] 2 → 3  formalized

## Current state [Lean]
- `exists_nonrealZeroCount_and_collisionMass_le_interiorLindelof`: `N(t) ≤ C R log R`,
  `R = 2π e^{(27/40+ε)/t}`, so `κ := limsup_{t→0} t log N(t) ≤ 27/40`.
- The constant `27/40` comes from the pointwise horizon threshold `(c − w)² > 4c μ(1/2 + w)` on
  `w ∈ [0, 1/2]`, binding on the chord `μ(1/2) ≤ 1/6`, `μ(5/7) ≤ 1/14`. The Euler anchor needs
  `c > 1/2`, so the pointwise horizon gives at best `e^{(1/2+ε)/t}`, even under Lindelöf.

## The dictionary: the heat count is a zero-density count
Coordinates: a zero `z` of `H_0 = Ξ` has `Im z = β − 1/2`, and the Gaussian average defining `H_t`
at ordinate `x` has its saddle at abscissa `1/2 + w`, `w = t log(x/2π)`.

**Mean-field rate.** A nonreal zero `x + iy` obeys
`ẏ = −2 Σ_{j} (y − y_j)/|z − z_j|²`.
- Its conjugate contributes `−1/y`. This term alone is the energy-transition rate: `y²` drops by
  `2t`.
- The real zeros near `x`, of density `(1/2π) log(x/2π)`, contribute about `−log(x/2π)`.

So depth `δ` at ordinate `x` survives until `t ≈ δ / log x`, and is absorbed once
`t log x > δ`. With `δ < 1/2` this reproduces the sharp horizon `c = 1/2`.

**Claims.** Let `E(σ) := limsup_T log N(σ, T)/log T` be the zero-density exponent.
- **(S) Sufficiency [paper sketch].** `κ ≤ sup_{0<w<1/2} w·E(1/2 + w)`. Proof route:
  - replace the Euler anchor by an interior anchor at `w = t log x`;
  - the small values of `ζ` at the anchor occur near zeros with `β ≥ 1/2 + w − o(1)` (zero density) or on a Dirichlet-polynomial large-deviation set;
  - large values left of the saddle are controlled by mean values (moments) instead of `μ`;
  - sum over dyadic `x`, using `#zeros ≤ x^{E}` at depth `t log x`.
- **(N) Necessity [paper sketch].** `N_off(δ, T) ≤ C log T · N(c δ²/log T)`. Proof route:
  - window energy `Σ_window y²`;
  - pair terms `(y_k − y_j)²/|z_k − z_j|² ≤ 1`, at most `C log x` partners per zero;
  - nonreal zeros are not created forward in time (`nonrealZeroCount_antitoneOn`);
  - so the energy of `k` zeros of depth `≥ δ` lasts until `t ≈ δ²/(C log x)`.

  Consequence: `E(1/2 + δ) ≤ κ/(c δ²)`.

**Rungs translated (S + N).**

| Rung | Equivalent density statement | Known? |
|---|---|---|
| `N(t) ≤ e^{o(1/t)}` (`κ = 0`) | `N(σ, T) = T^{o(1)}` for every `σ > 1/2` | Open; beyond the density hypothesis and beyond Lindelöf (Lindelöf gives only `E ≤ 2(1 − σ)`) |
| `N(t) ≤ C t^{−A}` | `N_off(δ, T) ≤ C (log T/δ²)^{A'}` (polylog off-line density) | Open |
| `N(t) ≤ C` | `FiniteOffLine` | Open; equivalence [Lean] |

**Exponent values under (S)** (`κ ≤ sup_w w E(1/2+w)`):

| Density input | Bound on `κ` |
|---|---|
| trivial `E ≤ 1` | `1/2` (the sharp horizon) |
| corpus power saving `E(1/2+δ) ≤ 1 − δ/40` (`exists_zetaZeroDensity_powerSaving`) | `79/160` |
| Huxley `12/5` | `3/20` |
| Guth–Maynard `30/13` | `15/104` |
| density hypothesis | `1/8` |
| RH | `0` |

## Tool barriers
- **Energy transition** (`riemannHeat_upper_energy_le`):
  - The law is global in the ordinate. Its right side `Σ_ρ ((Im ρ)² − 2t − c)_+` is infinite unless only finitely many zeros have `(Im ρ)² > 2t + c`, so it is vacuous before finiteness.
  - Its rate `2t` is the conjugate self-interaction. The mean-field rate `t log x` is absent.
- **KKL horizon with Lindelöf chords:** pointwise, so the threshold is `c ≥ 1/2` (Euler anchor). It cannot go below `e^{(1/2+ε)/t}`.
- **Quadratic cost** (`resolventIndexCharge_le_packetCharge`):
  - It is a lower bound: `k` right copies cost `≥ 50k² − 3k/2`.
  - Combined with a work bound `W(t)`, it gives `N ≲ √W`. The upper estimate on `W(t)` is the same open problem.
- **Q-II premise is false.** The count is not "dynamical instead of arithmetic". Under (S) + (N) it is the density function `N(1/2 + t log x, x)` summed over `x`.

## Open core
- A sub-power zero-density theorem `N(σ, T) = T^{o(1)}`, `σ > 1/2`. Rung 1 needs it by (N).
- Without it, the reachable improvements are the constant only:
  - `27/40 → 1/2`: large-value counting;
  - `→ 79/160`: corpus density, with (S);
  - `→ 15/104`: Guth–Maynard, with (S).

## Necessity: what is provable
**(N₂) Polylog rate [Lean, static proof below].** `N_off(δ, [X, 2X]) ≤ C log X · N(c δ²/log⁴ X)`.
- **Rung 2 ⇒ polylog density:** `N(t) ≤ A t^{−a}` ⇒ `N_off(δ, [X, 2X]) = O((log X)^{4a+1})`.
- Rung 1 gives nothing at this rate: `e^{o(1/t)}` with `1/t ≍ log⁴ X` is superpolynomial.

**(N₁) Mean-field rate, needed for rung 1 [OPEN].** Rung 1 ⇒ sub-power density needs
survival `≥ c(δ)/log X`. Every energy or threshold functional tried fails at the same point,
**threshold crowding**:
- Pair drains are bounded per pair, so the drain is `≲ (log x/θ) · #{zeros above θ}`.
- The budget is the excess above `2θ`.
- Zeros just above `θ` count fully in the drain and carry no budget.

Variants tried:
- convex ramps;
- threshold first moments `M_θ` with the exact cross-line identity `dM_θ/ds = −2 Σ_{y_k>θ>y_j} (y_k − y_j)/|z_kj|²`;
- `θ`-averaging;
- recursion over crowd levels.

All lose at least a factor `(log x)^{1/m}` or `e^{c√(log log x)}`. That factor makes `e^{ε/τ}` superpolynomial.

Physically the crowd is harmless: zeros at depth `≥ θ` survive `≍ θ²/log x` on their own. The missing ingredient is an argument that charges crowd drains to the crowd.

**Inputs a dynamics proof of (N₁) would need:**
- zero ODE for `H_s`, with collisions;
- local zero counts for `H_s` uniform in `s`;
- flux control (horizontal velocities, with symmetrised near-field terms).

Zero dynamics give `dE/ds = −4 Σ_{pairs} φ̄ (y_k − y_j)²/|z_k − z_j|² + (φ′-flux)` for the window
energy `E = Σ φ(x_k) y_k²`.  Each pair term is `≤ 1`, which is where the crowding loss enters.

A static contour version (Hermite/Gram negative index from `∮ G H′/H`) fails: real zeros' Gram mass swamps the pair's negative eigenvalue.

## Lowering the exponent: routes
The pointwise threshold is `c > sup_w θ_w`, where `θ_w` solves `(c − w)² = 4c μ(1/2 + w)`. Its floor is
`4 μ(1/2) = 2/3` with Weyl's exponent.
- **Derivative tests.** The `k`-th derivative test points are `(1 − k/(2^k−2), 1/(2^k−2))`, i.e. `(1/2, 1/6), (5/7, 1/14), (5/6, 1/30), …`. Their convex hull binds on the chord `(1/2, 1/6)–(5/7, 1/14)` of slope `4/9`, which gives `27/40` (current Lean). It is the limit of derivative tests.
- **`2/3` [paper check].** Add `μ(11/18) ≤ 1/9`, from the exponent pair `(1/9, 13/18) = A(2/7, 4/7) = ABA(1/6, 2/3)` (two `B`-processes). The profile is then tight at `c = 2/3`: at `w = 0` (slope `1/2`) and at `w = 1/3` on the chord `(5/7, 1/14)–(1, 0)`. Every `c > 2/3` works. This needs van der Corput's `B`-process (Poisson summation with stationary phase), which the corpus lacks; `ExponentPairSelfDuality` is bookkeeping only.
- **`4·13/84 = 13/21`:** Bourgain; out of reach.
- **`1/2 + ε`:** counting instead of pointwise reality. Bad ordinates are controlled by mean values of `ζ` in the strip. `1/2` is the Euler-anchor barrier.

## Exponent `2/3`: the build plan (chosen 2026-10-28)
Target: `μ(11/18) ≤ 1/9`, then the horizon threshold `2/3 + ε` (numerically checked: with the profile
`(1/2,1/6)–(11/18,1/9)–(5/7,1/14)–(1,0)`, `min_w (c−w)² − 4cμ(1/2+w)` is `0` at `c = 2/3` and
positive for `c > 2/3`).

Why the `B`-process is unavoidable:
- Optimising the corpus derivative tests (Kuzmin–Landau, second to `k`-th) block by block gives
  `μ(11/18) ≤ 0.11728`, the chord value, for blocks up to `N = t`.
- With the approximate functional equation the dual sum gives `1/9`, but the direct sum over
  `N ≤ √t` still gives `0.11728`.

So `1/9` needs `(1/9, 13/18) = A(2/7, 4/7)`, `(2/7, 4/7) = B(1/14, 11/14)`: Weyl-difference the block, then apply `B` to the differenced sums, then the fourth derivative test.

Lemma chain, none of it in the corpus:
1. truncated Poisson summation: `Σ_{a<n≤b} e(f(n)) = Σ_{α−η<ν<β+η} ∫_a^b e(f(x) − νx)dx + O(log(β−α+2))`, for monotone `f′` (Titchmarsh 4.7);
2. stationary phase with explicit error, for `f″ ≍ λ₂` and `|f‴| ≪ λ₃` (Titchmarsh 4.6);
3. the `B`-process lemma (Titchmarsh 4.9), with explicit constants;
4. the zeta block at `σ = 11/18`: Weyl differencing with `H ≍ N^{?}`, `B` on each differenced sum, and the fourth derivative test on the transformed sums. The result is `block ≪ t^{1/9} N^{11/18}` up to logs;
5. the profile point `μ(11/18) ≤ 1/9` in `KiKimLeeInteriorLindelofHorizon`'s strip exponent, and re-run the threshold to get `2/3 + ε`.

## (N₂) static proof — the build plan (chosen 2026-10-28)
Any polylog survival rate gives rung 2 ⇒ polylog density. A static Rouché argument at each deep zero
gives rate `δ²/log⁴ X` without zero dynamics.

**Theorem N₂.** For `0 < δ ≤ 1/2` there are `c, C, X₀` with: for `X ≥ X₀`, `0 < t ≤ c δ²/log⁴ X`,
every finite set `F` of zero copies with ordinate in `[X, 2X]` and depth `|β − 1/2| ≥ δ` satisfies
`#F ≤ C log X · N(t)`.
Corollary: `N(t) ≤ A t^{−a}` ⇒ `#{depth ≥ δ, ordinate ≤ T} ≪ (log T)^{4a+2}`.

**Proof.** Work in `XiC` coordinates: zero `ζ = x + iy`, `|y| = depth`.
1. *Near/far split.*
   - `Z` = copies with ordinate within 2 of `x`; `m = #Z ≤ C log X` (`exists_card_near_xi_zeros_le`).
   - On `B(c, 3)`, `c = x − 2i` (Euler point), `XiC = P·g`, `P = ∏_Z (w − ζ_q)`, `g` zero-free (`exists_finset_zeroFree_factorization`).
   - From `logDeriv_xi_eq_partialFraction`, the weighted density `exists_tsum_weighted_density_le` and `|logDeriv ξ(2+iT)| ≪ log T`: `|g′/g| ≤ K = C log X` on `B(c, 3)`.
2. *Circle.* Choose `r ∈ [δ/4, δ/2]` at distance `≥ d = δ/(8(m+1))` from every `|ζ_q − ζ|` (pigeonhole). On `Γ = ∂B(ζ, r)`: `S := Σ_Z 1/|z − ζ_q| ≤ m/d`.
3. *Ratio and Cauchy.* For `w` near `z ∈ Γ`, `|XiC(w)| ≤ |XiC(z)| e^{(S+K)|w−z|}`. Cauchy at radius `1/(S+K)` gives `|XiC″(w)| ≤ 2e (S+K)² e^{(S+K)|w−z|} |XiC(z)|`.
4. *Gaussian.*
   - `H_t(z) − XiC(z) = ∫ g_t(u)[XiC(z−iu) − XiC(z) + iu XiC′(z)] du`; the odd moment vanishes.
   - Local part `≤ C t (S+K)² |XiC(z)|` for `t(S+K)² ≤ 1`.
   - Tail `|u| ≥ 2`: global growth of `XiC` along horizontal lines, relative to `|XiC(c)|`, together with `|XiC(c)| ≤ (3/d)^m e^{3K} |XiC(z)|`. Its cost `e^{−1/(8t)}` is negligible when `1/t ≫ log X · log(log X/δ)`.
5. *Rouché* (`exists_zero_mem_ball_of_norm_sub_lt`). `H_t` vanishes in `B(ζ, r)`, so it has a nonreal zero, since `r ≤ δ/2`.
6. *Counting.* A `δ`-separated subfamily of `F` gives disjoint discs, hence `N(t) ≥ #F/(C log X)`.

Status: **(N₂) formalized** (file checks pass; wired into `RHTower.lean`; umbrella not compiled).
- `RHTower/XiZeroFreeCofactorNearAnOrdinate.lean` — `exists_xi_cofactor_near_ordinate`: on `B(2+iT, 12)`, `ξ = ∏(s−ρ)^{m_ρ}·g`, `Σ m_ρ ≤ C log T`, `‖g′/g‖ ≤ C log T` on `B(2+iT, 11)`.
- `RHTower/GaussianAverageOfALocallyTameFunction.lean` — `norm_integral_gaussDensity_mul_sub_le`: if `‖F(w)‖ ≤ ‖F(z)‖e^{a‖w−z‖}` (`‖w−z‖ ≤ 2`) and `‖F(z−iu)‖ ≤ B‖F(z)‖e^{b|u|}e^{u²/8t}` (`|u| > 1`), then `‖∫g_t(u)F(z−iu)du − F(z)‖ ≤ t‖F(z)‖(42a²e^{4a²t} + 20(B+1+4a)e^{−λ+8(b+λ)²t})`.
- `RHTower/HeatFlowNearADeepXiZero.lean` — `norm_riemannHeat_sub_XiC_lt`: `‖H_t(z) − Ξ(z)‖ < ‖Ξ(z)‖` for `t ≤ 1/(1000A²)`, `A = Σ m_ρ/‖σ(z)−ρ‖ + K + log Im σ(z) + 3`.
- `RHTower/DeepOffLineZerosAreCountedByTheHeatFlow.lean`:
  - `exists_card_deep_le_mul_nonrealZeroCount`: `#{copies, ordinate ∈ [X,2X], |β−1/2| ≥ δ} ≤ C log X · N(t)` for `t ≤ δ²/(C log⁴ X)`;
  - `polylog_deep_density_of_polynomial_nonrealZeroCount`: `N(t) ≤ A t^{−a}` ⇒ that count is `O((log X)^{4a+1})`.

## Survivors to formalize (not dependency-closed)
- (N₁), the mean-field necessity (rung 1 ⇒ sub-power density): open on paper (threshold crowding).
- (S), the sufficiency transfer. Needs:
  - interior anchors with small-value control;
  - mean values of `ζ` in the strip.

## Log
- 2026-10-29 — (N₂) formalized: rung 2 ⇒ polylog deep density (static Rouché, no zero dynamics).
- 2026-10-28 — necessity: polylog rate (N₂) on paper; mean-field rate (N₁) open (threshold crowding); exponent routes mapped (`2/3` needs `μ(11/18) ≤ 1/9`).
- 2026-10-28 — created; dictionary `κ = sup_w w E(1/2+w)` found (paper sketch); rung 1 identified with sub-power density.
