# Paley–Wiener rigid side of the excursion threshold

## Problem

Setting: a configuration with positive summable weights `c_i` and exponents
`w_i = δ_i + iω_i`, `0 < δ_i < Θ`. Its lag function is `Φ(t) = Σ_i c_i e^{δ_i t} cos(ω_i t)` and
`E = {t ≥ 0 : Φ(t) > 0}`.

Known:

- **Blind** (`R:WeilLagSubexponentialExcursionBlind`): Fejér blocks achieve
  `|E ∩ [k, k+1)| ≤ e^{−f(k)k}` whenever `Σ_b f(2^b) < ∞`, i.e. `∫ f/t < ∞`.
- **Rigid, exponential** (MUST-1386): `∫_E e^{κt} < ∞` for some `κ > 0` forces `δ_i ≤ 0`.

Open: does `∫^∞ F(t) dt/t² = ∞`, with `F(t) = f(t) t`, force rigidity?

JAS consequence (no side condition): RH would hold whenever JAS level-one interval positivity holds
off log-scales of density `e^{−F}`, `∫ F/t² = ∞`. This sits between MUST-1390 (exponentially thin)
and MUST-1393 (lower density zero, which needs no chain).

## Reformulations (paper)

1. **Two-parameter PD family.** For lattice frequencies `m_i`, set `x_i = β* − δ_i` and
   `A_m(σ) = Σ_{m_i = m} c_i e^{−σ x_i}` (completely monotone in `σ`). Then
   `Φ(t) e^{−β* t} = P_t(t)` with `P_σ(u) = Σ_m A_m(σ) cos(m u)`. Thinness says that the positive set
   of the frozen PD kernel `P_σ` has measure `≲ e^{−F(σ)}` along the diagonal.
2. **Phase sampling.** `Φ(2πj + u) = Σ_i b_i(u) e^{2π δ_i j}` is a real-exponential sum in `j`. If
   `Σ_j e^{−F(2πj)} < ∞`, then for a.e. `u` it is `≤ 0` for all large `j` (Borel–Cantelli).
3. **Top-rate integrability.** If `∫ (Φ − M)_+ e^{−αt} < ∞` (`α` = top rate), Landau at real points
   gives `∫ |Φ| e^{−αt} < ∞`; for an attained top this is impossible.

## What linear bounds give, and why they fail

PD test functions yield exactly the max-coefficient bound `A_m(t) ≤ C e^{−F(t)} Z(t)`. Fejér tests
yield the low-pass bound `Σ_{m ≤ N} A_m ≤ C N e^{−F} Z`. Frequencies are free, so these allow any
sublinear `F`. Example: a log-smooth profile spread over doubly exponential frequency blocks satisfies
all linear bounds, and even L¹-smallness, with `F ≈ t/log t`. Yet its positive set is fat at
threshold `0`: positive lobes appear wherever the low-frequency offset is absent.

## Mechanism (paper, block models)

- **Compensation capacity ≤ mass × sharpness.** A mean-zero PD kernel with peak `H` and positive
  density `ε` has negative mass `≤ H ε`.
- **Growth ⇒ persistence.** Every off-line component grows, so its excursions above any fixed
  threshold persist unless a component with low-frequency spread negativity covers them.
- **Visibility.** In a Fejér-block configuration, a block whose peak exceeds `≈ 3e^Θ` times the total
  level `A(t) = Σ a_b(t)` has its core `|ω_b t − 2πk| ≤ 1/K_b` inside `E`. So visible blocks need
  `K_b ≳ e^{F(t)}`. A block is *blunt* at `t` once `K_b < c e^{F(t)}`, i.e. past its sharpness time
  `τ_b`. A blunt block must lie below `≈ 3e^Θ` times the level of the sharp blocks, each discounted by
  its own sharpness `e^{−F(τ_{b'})}`.
- **Provider relay.** Level providers `b_0, b_1, …` with blunting times `τ_0 < τ_1 < …` need the peak
  gap `Δ_k(τ_{k−1}) ≥ F(τ_k) − c`. Mass summability bounds `Σ_k log(m_k/m_{k−1})`. Hence
  `Σ_k G'_k τ_{k−1} ≥ Σ_k F(τ_k) − O(k)`, and by
  `F(τ_k)/τ_{k−1} ≥ F(τ_k)(1/τ_{k−1} − 1/τ_k) ≥ ∫_{τ_{k−1}}^{τ_k} F/t²` we get
  `Θ ≥ Σ G'_k ≥ ∫ F/t² − O(1)`.
- **Spread regime.** When all blocks are invisible, mean-zero mass balance forces
  `A(t)/M(t) ≲ e^{−F(t)}`. Clusters of `≈ e^F` comparable blocks must be handed over with rate gaps
  `≳ f`, so the cost is again `∫ f/t`.
- **ζ weights.** For the ζ-type weights `1/|ρ|²` with RvM counting, flattening a block of `e^F` zeros
  consumes a real-part band `2f`. Zero-density forces AP spacing `ω ≥ e^{cF}`. The threshold stays the
  PW one.

## Open lemmas

1. **Covering principle (general, lattice).** At threshold `0`, a thin positive set forces a
   low-frequency negative compensator that dominates the tails of every higher-frequency structure.
   Its capacity must be `≤` mass × sharpness. Delsarte combs give a necessary arithmetic condition:
   if `E` is a single cluster of width `w` at the returns, then `Σ_{j} A_{jK} ≤ Z/K` for
   `K ≤ π/w`.
2. **Entropy control in the relay.** When many sharp providers carry the level, a `log N_s` loss
   appears; bridge it with the spread-regime bound.

## Status

Paper: block-model rigidity argued (relay plus Abel summation); general case open.

Lean: the Fejér-block converse is done (MUST-1401, card
`3-formalized/fejer-block-excursion-threshold.md`). The abstract level budget
`LevelBudget.sum_div_two_pow_le` replaces the relay with Markov, Cauchy–Schwarz in time and
telescoping.

Lean, general lattice case: done (MUST-1403, card `3-formalized/lattice-excursion-level-budget.md`).
Every positive lattice configuration with a finite frequency moment `Σ c m^α < ∞` obeys the PW budget.
Here sharpness is the frequency, and the share hypothesis comes from period positivity
(`π A_k(T) ≤ 2A(T)e^{2πΘ}v(T)`). The cycle-207b handover counterexamples need an infinite moment.

Open:

- (a) non-lattice configurations, such as the ζ lag configuration (finite α-moment for every `α < 1`);
- (b) lattice configurations with infinite moment outside the Fejér class.
