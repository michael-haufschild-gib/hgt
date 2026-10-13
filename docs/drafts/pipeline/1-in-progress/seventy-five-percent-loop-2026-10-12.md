# 75% critical-line goal loop (2026-10-12)

- **ID:** g75-1012
- **Stage:** 1-in-progress
- **Type:** CONJECTURE loop
- **Statement:** Unconditional Lean proof that `liminf N₀(T)/N(T) ≥ 3/4` (zeros on the line counted with multiplicity).

## Frontier (from Lean corpus only)
- Vendored `Zeta23`: unconditional `N₀ˢ ≥ 2/3`, Montgomery–Taylor window `0.6725` (simple + critical), distinct `0.83625`.
- Zeta23 zero side: `Â = P + Q`, `rank P ≤ s₁+s₂`, `n₊(Q) ≤ p`, `tr P + 2p ≤ N`; certificate
  `rank_trace_ineq` with parameter `c`. `c = 2` gives `N₀* ≥ 4trÂ − 2N − ‖Â‖²`.
- Corpus 75% receivers (HCF, Ward, translated lattice …) all reduce to one source estimate; HCF baseline `4π/3`, gate `π`.

## Structural facts established this loop (paper level)
- F1 (pair-block trace invariance): `Re Σ_k φ̂(γ−τ_k)²` is independent of `Im γ` when `φ̂²` has no aliasing, so the
  Zeta23 accounting sees every off-line pair as an on-line double zero, at every displacement.
- F2 (continuity barrier): every certificate built from functionals continuous in the zero configuration gives the
  same bound for an on-line double zero and for an off-line pair at displacement `δ → 0`. Hence a continuous-functional
  proof of `N₀ ≥ 3/4` also proves `≥ 3/4` of zeros are simple-like; this beats the RH-conditional simple-zero record (19/27).
- F3 (LP): in the Zeta23 zero side, `N₀ ≥ 3/4` follows from `n₊(Â) ≥ 7/8·N`; quadratic certificates give at most ≈ 0.836.
- F4 (CGG sign law): in `Σ_ρ ζ'(ρ)ζ'(1−ρ)h(ρ)`, an off-line pair at displacement `δ` contributes ≈ `−2δ²|Z''|²h`,
  the analytic continuation `ε² → −δ²` of an on-line close pair. Near-line pairs are negative for ζ'-weights, positive
  (double-like) for unweighted Gram matrices.
- F5 (moment problem): with `m₁ = 1, m₂ = 4/3` (Fejér, λ = 1) the third moment adds nothing without an upper spectral
  bound (mass at infinity); a global (all-ℝ) certificate must have even degree, and degree 4 needs `tr Â⁴`, outside the
  Rudnick–Sarnak range at λ = 1.

## Log
- 2026-10-12 — created; corpus mapped (Zeta23 Main/ZeroSide/Assembly/RankTrace, HCF receivers, memory hubs).
- F6 (CGG threshold, RH world): the CGG Cauchy–Schwarz gives `N_s ≥ 1 − (1+θ)^{−3}` for mollifier length `θ`
  (θ = 1/2 → 19/27, θ = 1 → 7/8). Hence `3/4` simple needs `θ ≥ 4^{1/3} − 1 ≈ 0.5874`, just past Conrey's `4/7`
  (`4/7` would give `988/1331 ≈ 0.742`).
- F7 (coherence–balance tradeoff): CGG's first moment is coherent only because `ζ'(ρ) = −i e^{−iθ(γ)}Z'(γ)` carries the
  `χ^{1/2}` phase; any J-balanced weight (`ξ'`-type, no off-line growth) makes `Σ_S G` alternate. With coherent weights an
  off-line pair costs `|G(σρ)|² ≍ e^{2a}|G(ρ)|²` (`a = (β−½)log T`), so unconditional CGG needs near-line density decay
  rate `> 2`, i.e. density mollifier length `> 1`: the (L) wall again.
- F8 (cubic Montgomery certificate): `N_s ≥ (4N − Σ_distinct m³)/3`; RS-range triple test functions give
  `Σ m³ ≳ 3N`, worse than the pair bound. Higher correlation levels do not help.

## Cycle 1 verdict
- Conjecture "some combination of corpus-available unconditional statistics reaches 3/4": **BLOCKED** (each route
  reduces to (L) or to beyond-Nyquist prime correlations; see F2, F5, F7, F8).
- Positive survivor: the reduction chain `75% on-line ⇒ 75% simple-like ⇒ beyond RH-SOTA (19/27)`; the CGG threshold
  `θ* = 4^{1/3} − 1`; the far-pair cost law `e^{2a}` for coherent weights.

## Cycle 2 — spectral slack law (C2)
- **Statement (Lean, matrix level).** `RHTower.rank_trace_ineq_slack`: with `P ⪰ 0`, `rank P ≤ r`, `n₊(Q) ≤ b`, `c > 0`,
  `c trP − (c²/4) r + 2c trQ − c² b + Σ_{q∈spec Q, q>0}(q−c)² ≤ ‖P+Q‖_F²`; `posSlack_ge_sq` gives slack
  `≥ (‖Q₊‖_F − c√b)²`; `zeroside_rank_core_slack` is the `c = 2` zero-side form
  `4trÂ − 2N − ‖Â‖² + Σ_{q>0}(q−2)² ≤ s₁+s₂`. Module `RHTower/RankTraceSpectralSlack.lean`, axioms clean, wired.
- **Paper consequence (not yet in Lean).** For ζ: `Σ_{q∈spec Q̂, q>0}(q−2)² ≤ N₀*(T,2T) − (H(λ)−ε)N` eventually.
  An isolated off-line pair at displacement `a` has `q ≈ 1 + g_λ(a)`, `g_λ(a) = ∫φ²e^{λaξ}/∫φ²` (≈ `sinh(λa)/(λa)`
  for flat `φ²`), so isolated far zeros have density `≤ (N/3)/(g_λ(a)−1)²`: rate `2λ`, but useful only for `a ≳ 3`.
  Off-line far zeros force more on-line zeros than two thirds.
- **Verdict:** SURVIVES as a modest new structural law; it does not touch the 75% crux.
- **Crux identified (both sides):** RH side: CGG at `θ ≥ 4^{1/3}−1`. Unconditional side: off-line zeros at displacement
  `a ∈ [0.3, 2]` (in units of `1/log T`) must be `≤ ~N/8`; the adversary (2/3 simple + 1/6 pairs at `a ≈ 1`) defeats
  Zeta23, C2 (slack `≈ 0.03` per pair) and unconditional CGG (negative J-terms inflate `S₁²/S₂`).
- **Open:** ζ-level instantiation of C2 (concrete `blockQ`, growth of `|x_ρ|²`, isolation); cluster cancellation
  (two far pairs with `u₂ ≈ i u₁` cancel in `Q`).

## Cycle 3 — negative-mass slack and hybrid detectors
- **Lean (extended).** `rank_trace_ineq_slack` now also keeps `c · tr Q₋` (first elementary step:
  `(p−m)² − cp + c²/4 + cm = (p − c/2 − m)²`). Zero side at `c = 2`:
  `4trÂ − 2N − ‖Â‖² + 2 trQ₋ + Σ_{q>0}(q−2)² ≤ s₁+s₂`.
- **Isolated-pair LP (paper).** With trace invariance an isolated pair has `q₊ = g+1`, `q₋ = −(g−1)`; the full
  certificate gives `p/N ≤ (σ − c + c²/4)/((g+1−c/2)² + c²/4)`, optimum `c = 2`: `p/N ≤ (1/3)/(g²+1)`
  (`σ = 4/3`). So off-line zeros at displacement `a` are `≤ 2/(3(g(a)²+1))`: `1/3` at `a → 0`, `0.28` at `a = 1`.
- **Quarter-phase couples (paper, negative).** Two far pairs with equal displacement and `x₂ ∥ y₁`, `y₂ ∥ x₁` give
  `Q = 2I₂`: zero slack at every displacement. Single-kernel certificates cannot bound far off-line zeros that come
  in such couples (heights about half a mean spacing apart). Exact cancellation `Q = 0` is impossible because each
  block has invariant trace `2m`.
- **Multi-kernel (killed).** Concatenating Gram vectors over kernels `K_j` equals the single averaged kernel
  `avg_j K_j`; block-diagonal stacking averages the bounds. Quadratic certificates stay at the Montgomery–Taylor value.
- **Hybrid Z-slack + unconditional CGG (killed quantitatively).** Z-bonus per pair ≈ `a²/6`, CGG cost per pair
  ≈ `4κa²` (curvature factor `κ` large exactly for pairs in frame holes). The adversary at `a ≈ 0.28` keeps ≈ 0.672.
- **CGG threshold robustness.** Every form consistent with `19/27` at `θ = 1/2` and the limits `θ → 0, ∞` puts the 3/4
  threshold at `θ* ∈ [0.54, 0.60]`.
- **Verdict:** no route from corpus-available unconditional statistics; the unconditional crux is near-line density
  at `a ≈ 0.3` with constant `≤ 1/8` (an (L)-wall statement).

## Cycle 3b — ζ-level Theorem A with off-line spectral slack (Lean, unconditional)
- `RHTower.thmA_lam_spectralSlack` (module `RHTower/Zeta23TheoremASpectralSlack.lean`, wired, axioms clean):
  for `λ ∈ (0,1)`, `ε > 0`, eventually
  `(H(λ) − ε)·N(T,2T) + S_λ(T) ≤ N₀*(T,2T)` with `S_λ(T) = 2 tr Q̂₋ + Σ_{q>0}(q−2)² ≥ 0` for the concrete hat-unit
  off-line block of ζ's zeros. Pieces: `offLineSpectralSlack`, `seamA_spectralSlack`,
  `thmA_abstract_err_spectralSlack` (Alpöge–Furman assembly with the slack core), `eventually_poissonSq`.
- Geometry of `S` (paper, Lean open): an isolated off-line pair at displacement `a` has `|x|² − |y|² = c∫φ²`
  (invariant) and `|x|²+|y|² = c∫φ²e^{2δξ}`; its block contributes `2m(g−1) + m²(g−1)²` with
  `g = ∫φ² cosh(λaξ)/∫φ²`. Quarter-phase couples of far pairs contribute 0.

## Cycles 4–5 — discontinuous detectors
- **Laguerre / phase statistic (paper).** `V = −(Ξ'/Ξ)' = Σ_ρ (t−γ_ρ)^{−2}`: near-line pairs give exactly two real zeros of
  `V` (discontinuous at δ = 0: doubles give a double pole, no zero). Equivalently the phase of `E_κ = Ξ' − iκΞ` makes a
  forward and a backward half-turn at each near pair; its net change is `π·N₀*` and the excess total variation
  is `≈ 2π·#near pairs`. Counting the UHP zeros of `E_κ` (heights `≈ κδ²/2`) through Jensen on `Im z = −η`
  is exactly Levinson's method (`E_κ(t−iη) ∝ (ξ' − κξ)(½+η+it)`, i.e. `G = ξ + ξ'/κ` at `σ₀ = ½ − η`).
  Verdict: REDISCOVERED (Levinson); the only loss is Jensen's.
- **Removing Jensen's loss with fractional moments (killed: circular).** `(2s)^{−1} log ∫|GΨ|^{2s} → log-mean(G) +
  log-mean(Ψ)` as `s → 0`; the mollifier only helps through Jensen, and `log-mean(G)` is the zero sum being bounded.
- **Pair-correlation variance correction to Jensen (killed).** The mollified log-variance lives at frequencies `α > θ`,
  i.e. pair correlation beyond Nyquist.
- **Hadamard square / tensor Gram, trace of `P`, multiplicity LP (killed):** no new constraint.

## Requirements map (paper, after cycles 1–6)
Unconditional `N₀ ≥ 3/4` by any mean-value / explicit-formula / inertia / argument-principle method needs **both**:
1. **Near-line control (L₀):** all but `ε₁N` off-line zeros have displacement `a = (β−½)log T < a₀` with
   `a₀ ≈ 0.1`. Reason: unconditional CGG pays `≈ 4κa²` per near pair (κ = local curvature factor), so its
   `θ = 1/2` value 0.704 stays above 0.6725 only if `4κa₀²π_p ≲ 0.04`. Best known: Zeta23 bounds every off-line
   zero by `0.3275N`; moment bounds (`Σa ≤ 0.336N`, `Σa² ≲ 2.6N`) are useless at `a₀ ≤ 1`.
2. **Simple-zero efficiency beyond RH-SOTA:** CGG mean values at `θ ≳ 0.59` (Conrey/BFI ranges stop at 4/7), or
   any new simple-zero mechanism worth `> 3/4` under RH.
Each item is a recognised open problem; no corpus asset supplies either.
Barriers proved on paper: continuity (pairs ≈ doubles), Nyquist (sub-Nyquist frames cannot resolve pairs),
Jensen (the discontinuous Levinson count loses exactly the log-variance, which lives above the mollifier
length), Rudnick–Sarnak range (odd-degree certificates need spectral tails; quartic needs λ < ½).

## Backlog (positive survivors not yet formalized)
- B1: isolated-pair density from `thmA_lam_spectralSlack`: needs Poisson for `|φ̂(·−iδ)|²` on the grid
  (`Σ_k|φ̂(z−τ_k)|² = (2π/h)∫φ²e^{2δξ}`), decay-based isolation errors, frame bound for `{ŷ_ρ}`.
  Gives `#{isolated pairs, a ≥ A} ≤ (1/3+ε)N / (2(g−1) + (g−1)² + 2)`, `g = ∫φ²cosh(λAξ)/∫φ²`.

## Cycle 7 — cubic spectral certificates, new-record attempt (paper)
- `m₃ = lim tr Ĝ³/N` is computable at λ < 1 from the prime side (`trT³ + 3tr(TE²) + small`; `tr E³` only sees
  `n₁n₂ = n₃` prime-power coincidences).
- Far off-line pairs contribute near-symmetric `±e` eigenvalue pairs; the cubic certificate
  `f(μ) = 2μ − 1.25μ² + 0.2315μ³` (Fejér, `M = 3`) satisfies `6c + 2b < 0`, so such pairs do not overcount.
- By Cauchy–Schwarz `m₃ ≥ m₂²`, and the two-point extremal attains it, so cubic data helps only with an upper
  spectral tail `Σ_{μ>M} μ³ ≤ τN`, `τ < m₃ − m₂²` (Fejér: 0.22). Ideal gain (`τ = 0`): `n₊ ≥ 0.796`
  (`M = 3`), `5/6` (`M = 2`).
- Tail = clusters of `≥ 4` zeros within one spacing: a 4-level, bandwidth-1 statistic, outside the RS range.
  The only non-circular source is Selberg-method moments of `S(t+h) − S(t)` at `hL ≍ 1`, whose unconditional
  constants are O(1)-imprecise. Verdict: BLOCKED (cluster tails).
- Also killed: half-AFE Hermite–Biehler (`Z = Re(2e^{iθ}D_M)`): in the Steinhaus model half the zeros of `D_M` lie
  right of ½, so it caps near 50%; Selberg trace formula / scattering poles (resonance pair correlation mixes with
  the Maass spectrum); Levinson–Montgomery `N_left(ζ') = N_left(ζ)` (same Jensen family).

## Cleanest single sufficient input (paper)
- Zero side (any bandwidth): `N₀* ≥ 4trÂ − 2N − ‖Â‖_F²` with `trÂ ≈ N` (one-level, computable for λ < 2), so
  `‖Â_λ‖_F² ≤ (5/4 + ε)N` at **one** bandwidth `λ ∈ (0,2)` gives 75%. Fejér at `λ = 4/3`:
  `‖Â‖²/N = 2/a − 2/(3a²)·… ` gives exactly `3/4` when `F(α) ≤ 2` on average over `[1, 4/3]`
  (GUE value `F ≡ 1` gives `1 − 1/(3a²) = 0.8125`).
- Equivalent prime input: an upper bound for prime-pair correlations at relative scale `x^{−1/α}`, `α ∈ [1,4/3]`,
  with constant `2`; sieve bounds fail by the mean term (`3h²x ≫ hx log x`), averaged Hardy–Littlewood needs power
  savings at `H = x^{c}`, `c ≤ 1/4` (unknown).
- Alternative: an upper bound `tr Â⁴ ≤ (16/5+ε)N` at λ = 1 (Uniform[0,2] value, see below) gives `n₊ ≥ 8/9N` and
  `N₀* ≥ 7/9N`.
- Conjecture (Nyquist frame law): for the sine process the sinc Gram at density one has spectral law Uniform[0,2]
  (checked: moments `1, 4/3, 2` agree; `m₄ = 16/5` predicted).

## Cycle 8 — explicit-formula Λ-detector and prime-variance inputs (paper)
- Λ-weighted explicit-formula detector: rate `2λ` only for far zeros outside phase-balanced near-doublets.
  This is the known large-values obstruction. Verdict: INSIGNIFICANT.
- Corpus prime-variance tools: `PrimeAlmostAllShortIntervals`, Huxley asymptotic, the Ivić input
  `shortIntervalVarianceInput` (`x h^{4/3}` type), Turán–Kubilius. All work at almost-all precision
  (`H²/log^A`). The 75% input needs **variance** precision.
- Exact form of the input (Fejér, `λ = 4/3`, flat profile): `‖Â‖²/N = 9/8 + c/16`, where `c` is the
  `(1 − 3α/4)`-weighted mean of the bilinear form factor on `[1, 4/3]`. Then `3/4 ⟺ c ≤ 2`.
- In prime terms: `Var_y(ψ(y+H) − ψ(y)) ≤ 2·H log(x/H)` on average at `H ≈ x^{1/4}`. Even under RH only
  Selberg's `≪ H log² x` is known, so this input is open under RH too.
- Optimal flat-profile bandwidth: `c_max(λ) = [5λ²/4 − 2λ + 2/3]/(λ−1)²` peaks at `λ = 4/3` with value `2`.

## Cycle 9 — the corner and the moment problem (paper)
- **Corner adversary:** the on-line frame is a Parseval frame on a `2N/3`-dimensional subspace (`P` a
  projection); `N/6` doubled sites (near-line pairs or quarter-phase couples) sit in the complement with
  eigenvalue `2`. Its spectrum is `{1: 2/3, 2: 1/6}`.
- **Moment matching:** the corner's spectral moments are `m₁ = 1`, `m₂ = 4/3`, `m₃ = 2`. These equal the
  conjectured sine-process Gram law Uniform[0,2] (`1, 4/3, 2`). The corner is its Markov–Krein
  two-atom principal representation. The first separating moment is `m₄`: `10/3` versus `16/5`.
- So no certificate built from `tr Â^k`, `k ≤ 3`, at `λ ≤ 1` can pass `2/3` against the corner. This
  explains the cubic block of cycle 7 without any tail argument.
- `m₄` at `λ = 1` needs 4-level correlations at `Σ|ξ| ≤ 4`. Their off-diagonal terms are
  `Σ_{|h|≤√x} w(h) Σ_m b(m)b(m+h)` with `b = Λ*Λ`. On the `q = 1` arc this equals the short-interval
  variance of `Λ*Λ`, which the explicit formula for `(ζ'/ζ)²` turns into the two-point form factor at
  `α = 2`. Verdict: CIRCULAR — the quartic route is the bandwidth wall again.

## Cycle 10 — displacement order and the length law (paper)
- **Order law:** every explicit-formula statistic is `Σ_ρ h(γ_ρ)` with `h` analytic. A pair `t ± iδ`
  enters only through `h(t−iδ) + h(t+iδ)`, so it is even in `δ`: second order in `a`. Off-line near pairs
  are analytic continuations of on-line close pairs (`ε² ↦ −δ²`). First order in `a` needs
  non-analytic statistics: Littlewood/Jensen on `log|ζΨ|`, which pay the Jensen gap.
- **Couples are Frobenius-blind, explained:** for large `a` the pair vectors sit at opposite ends of the
  `u`-window (`φe^{∓δu}`). A second pair at height `t + π/L` has edge phases `e^{±iπ/2}`, so
  `Q₂ ≈ −Q₁` on the edge blocks, and only the trace-carrying interior survives (`Q = 2I`).
  Without couples, `‖Â_λ‖² ≈ (1/λ + λ/3)N` would imply `N(σ,T) ≪ T^{1−2λ(σ−½)}`, i.e. the density
  hypothesis at `λ → 1`. So unconditional far-zero control from the frame must defeat couples.
- **Length law (summary of all routes):** every 75% route needs a mean value of length `T^{1+η}`:
  - Zeta23 at bandwidth `λ ≈ 1.14`;
  - CGG twisted second moment of `ζ'` with `½ + θ ≈ 1.087` (`θ ≥ 4^{1/3} − 1`; Conrey's `4/7` gives 0.742);
  - Levinson with `θ ≫ 1`.
  Beyond length `T`, off-diagonal additive correlations are needed. CGG/Levinson additionally need
  near-line control unconditionally; the Zeta23 `c = 2` certificate does not, since it is pair-neutral.
- Under RH the target is "75% simple zeros", which is above the RH-conditional record `19/27`.

## Cycle 11 — exact couple spectrum; joint slack + unconditional CGG (paper)
- **Exact couple reduction (flat profile, λ = 1).** Write `α = δL`, `β = ΔL`, `s = sinh α/α`,
  `c = E(iβ)`, `z = E(−2α − iβ)`, where `E(w) = sinh(w/2)/(w/2)`. The reflection
  `(1 4)(2 3)` commutes with `JG`. The nonzero spectrum of the couple's `Q` is
  `1 + Re z ± √((s+c)² − (Im z)²)` together with `1 − Re z ± √((s−c)² − (Im z)²)`.
- **Correction to cycle 3** ("quarter-phase couples give `Q = 2I`"). At `β = π` the edge terms cancel only
  to first order: the residual eigenvalues are `≍ e^α/α²`, against `≍ e^α/α` for an isolated pair.
  Exactly `Q = 2I` occurs only at `α = 0`, `β = 2π` (two orthogonal doubles).
  Clusters of `K` pairs whose phases satisfy `Σ e^{iθ_j}θ_j^k = 0` for `k < K` leave an `α^{−K}` residual.
  This is why `‖Â‖²` does not imply the density hypothesis: hiding needs clusters of `≍ log T/log log T`.
- **Near-line slack per pair** (`c = 2`): isolated `s² − 1 ≈ α²/3`. Example `α = 1.5`: isolated `1.015`,
  couple at `β = π` `2.80`, `β = 3π/2` `0.70`, `β = 2π` `0.78`. Clusters save at most a bounded factor.
- **Unconditional CGG cost of near pairs.** Locally `ζ ≈ C(s−ρ)(s−ρ')`, so `x_ρ = ζ'M(ρ) ≈ 2CδM` and `x_{ρ'} ≈ −x_ρ`.
  The first moment is unchanged to `O(δ²)`. The bilinear second moment loses `8δ²|CM|²` per pair, so
  `N_{s,on} ≥ (19/27)N/(1 + (1/N)Σ_pairs 0.2κa²)`, with `κ` the relative curvature at the pair.
  For a couple the bilinear term is `∝ −δ²Δ²(Δ² − 4δ²)`, which vanishes at `Δ = 2δ`.
- **Joint minimax (heuristic, isolated pairs, κ = 1):** Zeta23 gives `r ≥ 2/3 + π_p(s²−1)` and CGG gives
  `r ≥ 0.7037/(1 + π_p·0.2a²)`, with `r + 2π_p = 1`. The adversary's best is `a ≈ 0.65`, giving
  `r ≈ 0.69`. The corner itself (`a → 0`) is killed by CGG.
- Verdict: BRIDGE to a possible record of about `0.68–0.69`, not to 3/4. It needs unconditional CGG discrete moments
  (none in the corpus) and control of `Σκ` (e.g. through `∫|ζ''M|²`). Parked as **B2**.

## Cycle 12 — log-energy / discrete log-mean of ζ' (paper)
- Near pairs are first-order visible in `Σ_ρ log|ζ'(ρ)/L|` (each pair gives `≈ 2 log(2aκ)`). This is the
  log-energy `Σ_{ρ≠ρ'} log|ρ−ρ'|` of the zero set (Hadamard).
- A **lower** bound `Σ_ρ log|ζ'(ρ)/L| ≥ −BN` would give `#{pairs with a < ε} ≤ BN/log(1/ε)`. Jensen and Littlewood only
  give upper bounds for log-means; lower bounds are repulsion statements with no unconditional source.
  Verdict: BLOCKED (wrong direction of Jensen).

## Cycle 13 — nodal topology of Re ξ(½ + h + it) (paper)
- `Re ξ` is harmonic in `(h, t)`. On `h = 0` it is `Ξ(t)`. On `h = H` the phase is monotone away from zeros deeper than `H`
  (pair sign law), so it has `≈ N(1 − ε_deep)` nodal endpoints.
- Nodal curves have no interior endpoints and no closed loops. Hence `N₀(Ξ) = N_top − 2#caps + 2#cups − O(log T)`.
- Every innermost cap carries a zero of `ξ`: along the cap `ξ` is purely imaginary, and the top phase advances by `π`.
- A near pair is a long thin U: its vertex sits at depth `δ` and its arms rise between the neighbours' verticals.
  Inside the U, `Re ξ` decays like `e^{−A/(2c_w)}`, the same rate as a normal inter-zero strip.
- Verdict: REDISCOVERED (this is phase monotonicity / Levinson; the topology only re-expresses `N − 2p`).

## Cycle 14 — Frobenius norm ⟹ density hypothesis? (paper)
- An isolated far pair gives `‖Q_j‖² = 2 + 2s_j²` with `s_j = sinh α_j/α_j`. If the pairs did not interfere,
  `‖Â_λ‖² ≈ (1/λ + λ/3)N` would give `#{β ≥ β₀} ≪ T^{2−2β₀}(log T)³` for `a ≥ C log log T`, which is the density
  hypothesis.
- **Flaw:** `tr(Q_jQ_k) ≈ 2e^{2α}Re(c·e^{iΔθ})/(α² + Δθ²/4)`, a Hilbert-type kernel. The edge vectors of a zero at
  depth `δ` stay coherent over height windows of length `≍ δ` (absolute). Unless pairs are separated by `πδ`,
  interference is of order one, and clusters of `≍ δ log T` far zeros with cancelling phases can hide.
  The remaining off-line zeros cannot be dropped, so no thinning argument works.
- This is the Montgomery–Huxley large-values barrier in frame language: DH for interference-free
  configurations only. Verdict: REDISCOVERED.

## Cycle 15 — can unconditional fourth moments escape the length law? (paper)
- Ingham's `∫|ζ|⁴ ~ T log⁴T/(2π²)` and the shifted or twisted fourth moments (Motohashi; `θ < 1/4` twists) are
  unconditional mean values **beyond length `T`**: they solve the additive divisor off-diagonal.
  They are the only such inputs available.
- Their leading constants contain a local (RMT) factor `g₂ = 2`. The corner configuration (Parseval
  2/3 plus doubled sites) would change the local factor of `E|Z_X|⁴` in the hybrid Euler–Hadamard
  model. So *if* the splitting `E|ζ|⁴ ≈ E|P_X|⁴·E|Z_X|⁴` held with an error at the constant level,
  Ingham would constrain local zero statistics.
- Obstructions:
  - the splitting is unproven, and its error terms sit exactly at the constant level;
  - a moment is a multiplicative functional of the configuration. The only proved conversion from moments
    to zero counts is Littlewood/Jensen, and Hölder makes higher moments **worse**:
    `(1/2k) log E|X|^{2k}` decreases as `k ↓ 0`;
  - fractional moments (`k → 0`) are circular. Unconditional sharp upper bounds for them lose an
    `O(1/θ)` exponent from the zero term, so the Jensen gap stays `≍ 1/θ`.
- Verdict: BLOCKED. The fourth moment is the right *kind* of input but has no zero-count transfer.

## Cycle 16 — settling κ for B2 (paper)
- Corrected normalization: `|x_ρ|² ≈ 4δ²|CM|²`. With `κ := |CM|²/(c₂L⁴)` and `c₂L² = E|ζ'M(ρ)|²`, the bilinear CGG cost
  of a near pair is `8κa²` per typical zero. Two merged typical zeros have `|C| ≈ |ζ'|/spacing`, i.e.
  `κ ≈ 1/(4π²)`. That is cycle 11's `0.2a²`.
- The adversary chooses `κ`. Three regimes:
  - Mean square `∫|ζM|²` alone allows `κ ≫ 1/(4π²)`.
  - A mollified fourth moment caps `κ ≲ 0.35`, giving a joint value ≈ 0.673: no gain over Theorem D.
  - The heuristic cap: zeros are anti-biased against large prime fluctuations `G`, Landau–Gonek discrete means
    of `|A(ρ)|²` are computable, and putting all pairs on the top third of `G` gives `κ_pairs ≲ 2.3κ_typ ≈ 0.06`.
    Then the joint value is ≈ 0.687.
- Verdict for B2: INSIGNIFICANT for 3/4. The best case is a new record of about 0.687. It needs (i) unconditional
  bilinear CGG moments, (ii) a rigorous local pair model, and (iii) a Landau–Gonek control of `κ`. None of them
  is in the corpus.
- Side fact: the bilinear form factor is **unconditionally** `≥ 0`, because `{γ_ρ}` is closed under conjugation:
  `Σ_{ρ,ρ'} e^{iy(γ_ρ−γ_ρ')} = |Σ_ρ e^{iyγ_ρ}|²`. Certificates that exploit it need `k̂ < 0` beyond 1, and then
  `k(2iδ)` grows like `cosh(2a(1+η))`, up to `T^η` for far pairs. So positivity beyond 1 is true but
  unusable without density rate `> 2`.

## Cycle 17 — universality of the continuity barrier (paper)
- Levinson is not exempt. Take `G = ζ − λζ'` with `λ = c/L`.
  - A near pair `½ ± δ + iγ` gives G-zeros at `m + 2λ` and `m − δ²/(2λ)`.
  - An on-line double gives `m + 2λ` and `m`.
  - At Littlewood abscissa `σ₀ = ½ − R/L` both configurations have the same Jensen weights up to `O(δ²)`. The
    left/on-line distinction enters only in the final count, which Jensen cannot see.
- Sign changes of `Z` also treat doubles and near pairs alike (neither changes sign).
- **Meta-law:** every known method bounds `N₀` through a functional that is continuous in the zero
  configuration. So an unconditional `N₀ ≥ 3/4` by such a method also proves that, under RH,
  `≥ 3/4` of zeros are simple-like.
- **Necessary open core:** 75% simple zeros under RH. The two known routes each fall short:
  - CGG needs `θ_eff ≈ 0.587` (Conrey `4/7` gives 0.742);
  - pair correlation needs `λ ≈ 1.14`, i.e. prime variance within a factor 2.
- Heuristic: in the lognormal model the CGG loss is the prime fluctuation over `[T^θ, T]`. That model predicts
  `≈ √θ` (0.756 at `θ = 4/7`), above the CGG-law value 0.742. So the shape of the mollifier at Conrey length is
  the cheapest place where 3/4 could appear, under RH only.

## Cycle 18 — family / large-sieve localisation of the q = 1 arc (paper)
- Conjecture: Barban–Davenport–Halberstam-type averaging, in which ζ's short-interval variance is one non-negative term,
  bounds that variance at `H ≈ x^{1/4}` within a factor 2.
- By Gallagher, `Var_H ≍ H²∫_{|β|≤1/H}|S − M|²`. The large sieve bounds the **sum** over well-spaced
  arcs by `‖S − M‖₂² ≈ x log x`. For the single `q = 1` arc this gives `Var_H ≲ H² log x`, a factor `H` too weak.
- Family positivity (`F_ζ ≤ Σ_χ F_χ`, each `F_χ ≥ 0` unconditionally in bilinear form) loses `φ(q)`, or `Q`
  after summing over moduli.
- The missing statement is "no concentration of `|S − M|²` on the `q = 1` arc relative to the Farey average". By
  Goldston–Montgomery duality this is pair correlation beyond 1 again. Verdict: BLOCKED (single-arc concentration).

## Cycle 19 — sign structure of the prime-side Frobenius beyond Nyquist (paper and corpus)
- Zeta23 (`PrimeSideB.Facts`) splits `tr G̃² = 𝓜[ν_X,ν_X] + O(L l log l (l²+X))`. The prime off-diagonal
  `𝓜[Π_X,Π_X] ≪ LX/T` is negligible only for `X ≤ T`. `calE` contains `(l²+X) log l/(T l)`, so the whole
  assembly is wired to `λ ≤ 1`.
- No sign trick: `‖Π − Γ‖²` is a positive-definite form in `Λ − 1` with Fejér-type kernel `Ŵ(T log(n/m))`, i.e.
  exactly the smoothed short-interval variance. The mean part cancels only against the Γ cross term, so the
  off-diagonal cannot be dropped.
- Other spread certificates need non-integer moments (`tr P^q`, `q < 2`, not explicit-formula computable) or higher
  integer moments (beyond Rudnick–Sarnak).
- An abstract "Theorem A for `λ < 2` with unevaluated prime Frobenius" would need `calE` re-engineered. It would be
  a formal reduction only, already implicit in the Zeta23 audit (supports 1.04/1.26/1.70). Verdict: INSIGNIFICANT as
  new knowledge; not built.
- Heat-flow (de Bruijn–Newman) proportions: near-line pairs collapse at local time `τ ≈ Y²`, i.e. absolute
  `t ≈ a²/log²T`. The backward window `t ∈ [0, 1/8]` is `≈ (log T)²/8` local time units, so no constraint.
  Verdict: INSIGNIFICANT.

## Cycle 20 — locating the exact open core (paper)
- Fejér-smoothed variance: `x·Var_H ≈ H x log x + Σ_{0<|h|<H}(H−|h|)(Σ_nΛ(n)Λ(n+h) − x)`. The needed `−H log H`
  comes from the singular-series average. So 75% at `λ = 4/3` ⟺ averaged Hardy–Littlewood for `h ≤ x^{1/4}` with
  error `O(xH log x)` in the Fejér-weighted signed sum, i.e. relative error `H^{−1}log x`.
- `x^{1/4}` lies inside the Matomäki–Radziwiłł–Tao long-shift range (`8/33 < 1/4`), but their saving is `log^{−A}`.
  Through the L² average one needs `Σ_{h≤H}|E(h)|² ≪ Hx^{3/2}` (square-root saving); the signed statistic is
  equivalent to the variance itself, so it gives no reduction.
- Under RH Selberg gives `Var_H ≪ H log²x`, still a factor `log x` short. Unconditionally, off-line zeros only
  enlarge the bilinear variance (`cosh(2αa)`). **So the Zeta23 route to 3/4 needs a second-order prime statement
  stronger than what RH supplies.**
- Exotic inputs, all killed:
  - LI of ordinates says nothing about multiplicities;
  - Selberg-class classification has no zero information;
  - Pólya/Riemann-kernel saddle points: the `n = 1` term is Gram's law (caps 66–70%), and the `n ≥ 2` terms are the
    Riemann–Siegel sum;
  - `Ξ + iκΞ'` Hermite–Biehler: Levinson again.
- Big-picture law: every unconditional 75% route needs either (I) RH-plus second-order prime statistics in
  intervals `x^{1/4}`, or (II) moment technology at mollifier length `θ ≈ 0.9` (CGG) / `θ ≫ 1` (Levinson), plus
  near-pair curvature control. Spectral (Kuznetsov) methods reach `4/7`.

## Cycle 21 — what the CGG route actually needs (paper)
- Identity: a near pair's CGG cost is `c_j = 8δ_j²|C_jM|² = 2|ζ'M(ρ_j)|²`, i.e. twice its own CGG weight. Curvature
  control means `Σ_{off-line ρ}|ζ'M(ρ)|² ≤ K·Σ_pairs σ_j`, where `σ_j ≈ (δ_jL)²/3` is the Zeta23 slack.
- With `c_j ≤ Kσ_j`, the two valid inequalities give `r ≥ max(2/3 + s, V/(1 + K's))`, with `K' = 24κ` for isolated
  pairs. A single combined certificate built from the same data cannot beat this crossing value.
- 3/4 at the crossing needs `V ≥ 3/4·(1 + K'/12) = 3/4 + 1.5κ` (isolated pairs). With typical
  `κ = 1/(4π²)` this is `V ≈ 0.788`. Clusters cut the slack by up to ~40%, giving `V ≈ 0.81`.
  By the CGG law that is `θ_CGG ≈ 0.67–0.74`, against Conrey's `4/7 → 0.742`.
- Stronger weights `x = ζ'²M` make pair costs fourth order, so slack would dominate for `κa ≲ 0.58`. But the
  Cauchy–Schwarz ratio then needs a fourth moment of `ζ'` at zeros: heavy tails, short mollifiers. Not viable.
- Refined requirement for any unconditional proof (route II'):
  (a) bilinear CGG discrete moments with value `≥ 0.79` (mollifier length `≈ T^{0.67}`, beyond Kuznetsov's `4/7`);
  (b) the aggregate curvature bound above;
  (c) cluster-robust Zeta23 slack.
  Route (I) instead needs RH-plus short-interval prime variance.

## Cycle 22 — odd-moment neutrality of pair blocks (paper)
- An isolated pair block has spectrum `{1 + s, 1 − s}` (trace 2), symmetric about 1. So for every odd `g`,
  `g(s) + g(−s) = 0`: pairs contribute **zero** to `tr g(Â − I)`. Example: `tr Q_j³ = 2 + 6s²`,
  `tr Q_j² = 2 + 2s²`, and `f(x) = x(x−1)(x−2) = (x−1)³ − (x−1)` gives `f(1+s) + f(1−s) = 0`.
  **Correction to the "cubic: far pairs grow like `e^{3λa}`" kill:** for isolated pairs the cubic growth cancels.
  Growth enters only through `P`–`Q` cross terms and clusters.
- For orthogonal blocks, `m₃ − 3m₂ + 2m₁ = Σ_{P-eig} μ(μ−1)(μ−2)`: a pair-neutral cubic statistic of the on-line
  spectrum.
- Cubic certificate LP (`h = Bx + Cx² + Dx³`; `h ≤ 1` on `x > 0`; pair condition `2C + 6D ≤ 0`; doubled sites
  `B + 2C + 4D ≤ 0`). It gives `V = (2/3)c + d(4 − m₃)` with `u = c + 3d`, `u + d²/(4u) ≤ 1`. So it beats 2/3
  iff `m₃ < 3m₂ − 2`, i.e. iff the spectrum is skewed below 1. Example: `m₃ = 1.9` gives `+0.015`.
- At `λ = 1` with the flat profile, the conjectured Uniform[0,2] law is symmetric about 1, so `m₃ = 3m₂ − 2 = 2`
  exactly and there is no gain. This sharpens cycle 9: the corner and the GUE law share all odd central moments to
  third order.
- Open: `m₃(λ, p)` for `λ < 1` or non-flat profiles, and `P`–`Q` cross terms (`tr P²Q`, `tr PQ²`) when the blocks are not
  orthogonal. The best case is a small record near the configuration-wise ceiling 0.68185, not 3/4.
  Verdict: BRIDGE (record-scale only).

## Cycle 23 — third moments for non-flat profiles (paper, Gaussian–Toeplitz model)
- Model: `S = N D² + DTD` with `D² = diag(p(k/d)/d)`, `T_kl = tr U^{k−l}`, `E|T_m|² = |m|`, and `E tr(DTD)³ ≈ 0`
  (Diaconis–Shahshahani). Then
  `m₂ = ∫p²/λ + λ∬p(x)p(y)|x−y|` (flat: `1/λ + λ/3` ✓) and
  `m₃ = ∫p³/λ² + 3∬p(x)²p(y)|x−y|` (flat: `1/λ² + 1`).
- Skew relative to the pair-neutral cubic: `Δ := 3m₂ − 2 − m₃`. Flat profile at `λ < 1`: `Δ = −(1−λ)³/λ² ≤ 0`.
  At `λ = 1`, with `p = 1 + εq`: `Δ = −3ε∫q x² + O(ε²)` and `X₂ = 2 − m₂ = 2/3 − 2ε∫q x² + O(ε²)`, so
  `Δ ≈ (3/2)(X₂ − 2/3)`. At the Montgomery–Taylor optimum, `Δ ≈ 0.009`.
- The cubic LP optimum (`u = c + 3d`, `u + d²/(4u) ≤ 1`) gains `Δ²/X₂ ≈ 10⁻⁴`.
  Verdict: INSIGNIFICANT. The Nyquist-frame spectrum is nearly symmetric about 1, so odd moments carry almost no
  rank information.

## Cycle 24 — number-variance constants as a source of F beyond 1 (paper)
- The `O(1)` term in `∫(S(t+h) − S(t))²` (or Goldston's constant in `∫S²`, under RH) equals
  `(1/π²)∫_1^∞F(α)α^{−2}dα` plus arithmetic constants. Unconditionally it is not known (Selberg/Tsang give `O(T)`
  error). So it is circular.
- Even if `I = ∫_1^∞Fα^{−2} = 1` were known, with `F ≥ 0` (unconditional, bilinear) a tail average does not localise:
  `g(1+η) ≤ 4/3 + η(2I − 2/3)` gains only if `I < 1/3`. The certificate needs **second-order** (in `η`) control of
  `F` near `α = 1⁺`. Verdict: CIRCULAR / INSIGNIFICANT.
- κ control for B2 revisited: the needed `Σ_pairs δ²|CM|² ≤ K·Σ_pairs δ²L²` is a non-analytic `(β−½)²`-weighted
  discrete moment, which contour methods cannot reach. B2 stays capped at `0.673` provably.

## Cycle 25 — Heath-Brown/Vaughan dispersion for input (I) (paper)
- Conjecture: a Type I/II split of `Λ` gives the Fejér-smoothed variance at `H = x^{1/4}` with constant 2.
- Type I (`d ≤ U`) costs `≍ U² log²x`, harmless for `U ≤ H^{1/2−ε}`.
- Type II pieces need variance precision `O(H log x)` against a mean `H²`. Dispersion, Kloosterman and large-sieve
  methods deliver `o(H²)`-type (first-order) asymptotics only.
- Pieces combine by Minkowski, so constants add. The true variance `H log(x/H)` has no prime-side origin: its
  `−H log H` part is the singular-series average, and by Goldston–Montgomery the full asymptotic is spectral
  (zeros of ζ). There is no Voronoi formula for `Λ`. Linnik's identity (`d_k*`) needs `k ≍ log x` divisor
  variances, each open for `k ≥ 3` at `H = x^{1/4}`.
- Verdict: BLOCKED. Variance-level information on `Λ` exists only on the zero side. The function-field analogue
  (Keating–Rudnick via Katz monodromy, `q → ∞`) has no number-field mechanism.

## Cycle 26 — Motohashi spectral fourth moment as an F-beyond-1 source (paper)
- Motohashi's explicit fourth-moment formula is a fully spectral, second-order, beyond-length-`T` identity.
- Pair correlation is a **ratio** statistic (`ζ'/ζ · ζ'/ζ`). Moments contain no denominators and determine ratios only
  through conjectural recipes (CFKRS/ratios). Derivatives in the shifts give `|ζ'|²|ζ|²`-type moments, never
  `|ζ'/ζ|²`. Verdict: BLOCKED (moments ↛ ratios; cf. cycle 15).
- State after 26 cycles: every unconditional mechanism at bandwidth ≤ 1 is closed, and each
  beyond-length input is either zero-side (circular) or beyond the technology (mollifier
  `T^{0.67}`). The only remaining necessary sub-goal reachable by known technology is RH-conditional:
  CGG at Conrey length `θ = 4/7` with a multi-piece mollifier (law gives 0.742; shape gain needed `≈ 0.008`).

## Cycles 27–29 — derivative-zero routes (paper, quick kills)
- **27 (Speiser/Levinson–Montgomery transfer).** `N⁻(ζ') = N⁻(ζ) + O(log T)`, so 3/4 ⟺ at most `N/8` zeros of `ζ'`
  in `σ < ½`. Write `ζ'(s) = χ(s)[(χ'/χ)(s)ζ(1−s) − ζ'(1−s)]`. With `χ'/χ ≈ −L` this is `χ(s)·G(1−s)`, where
  `G = −(Lζ + ζ')` is Levinson's function. Counting left zeros of `ζ'` is Levinson's method verbatim
  (Jensen-limited). REDISCOVERED.
- **28 (Zeta23 frame for zeros of `G` or `ζ'`).** No Euler product, so no explicit formula and no computable Gram.
  BLOCKED.
- **29 (frame for zeros of `Ξ'`).** `Ξ''/Ξ' = Ξ'/Ξ + (log Σ_ρ(s−ρ)^{−1})'`: the second term is a nonlinear function
  of the zero configuration with no prime side. BLOCKED.
- Interrogation: what survives is mean values of `ζ'`-type objects (CGG), whose analysis needs `χ`-twisted
  stationary phase (Gonek's lemma) and is length-limited. This confirms the RH-conditional CGG shape problem at
  `θ = 4/7` as the one constructive sub-goal.

## Cycle 30 — the extremal is a decorated crystal with its Bragg peak at Nyquist (paper)
- Equality in the `c = 2` rank–trace bound forces `P` to be a projection with `rank P = #` on-line sites, i.e. the
  on-line vectors are orthonormal. For the flat profile `⟨v_γ, v_γ'⟩ = sinc((γ−γ')L/2)`, and this vanishes iff
  `γ − γ' ∈ (2π/L)ℤ∖{0}`. **Equality ⟺ on-line zeros sit on a lattice of exactly the mean spacing, and the doubled
  sites (near pairs) occupy other lattice points**, orthogonal to `P`.
- Such a crystal has its first Bragg peak at `α = 1`, the boundary of the computable range, where the Fejér weight
  vanishes. Its diffuse part must mimic `F = α` on `[0, 1 − ε]` through correlated (hyperuniform) decorations, which
  the configuration-wise ceiling 0.68185 reflects.
- Interpretation: the 2/3 wall is not a technical artefact. The extremal object's spectral signature sits exactly at
  Nyquist, so **any** improvement must read `F` (or a substitute) at `α = 1⁺` with second-order precision (cycle 24).
  This is the structural reason behind the length law.
- RH-conditional CGG shape problem at `θ = 4/7`: deferred. A closed-form two-piece Euler–Lagrange solution is
  required (numerical optimisation is excluded by the loop rules). Its [OPEN CORE] — twisted discrete second
  moments of `ζ'` at zeros with `θ > ½` (Kloosterman off-diagonal) — is unproved in the literature, and the result
  would be RH-conditional, not the target.

## Cycle 31 — the all-profile certificate as a duality problem (paper)
- With sites of multiplicity `m_j` (near pairs count as doubles by pair-neutrality):
  `N_s ≥ Σ_j(2m_j − m_j²) = 2N − Σm_j²`, exact when every `m_j ≤ 2`. Also `X_p = Σm_j² + D_p` with
  `D_p = Σ_{j≠k}m_jm_kK_p(γ_j−γ_k)² ≥ 0`. The only unknown is `μ₂ = Σm²/N`.
- The pair measure `R = Σ_{j≠k}m_jm_kδ_{γ_j−γ_k} ≥ 0` has `R̂(α) = N(α − μ₂)` on `(0,1]`, plus the density delta.
  Testing with `g ≥ 0` and `supp ĝ ⊂ [−1,1]` gives `μ₂ ≤ (ĝ(0) + ∫ĝ|α|)/∫ĝ`. Fejér gives `4/3`, i.e. 2/3. The optimum
  over `g` is Montgomery–Taylor (0.6725). **So MT is the exact optimum of the positivity LP.** Mixtures of profiles add
  nothing (linear objective; cycle-7 kill confirmed).
- Gains toward Zeta23's configuration-wise ceiling 0.68185 must use constraints beyond positivity of `R`:
  - realizability of `R` as a two-point function (three-point positivity, `R₃ ≥ 0`, a Lasserre-type hierarchy);
  - `F ≥ 0` beyond 1 (sign-uncertainty tests). This holds unconditionally in bilinear form but costs `cosh(2a(1+η))`
    for far pairs (cycle 16).
- Verdict: BRIDGE, record-scale only (`≤ +0.009`). Parked.

## Cycle 32 — airtightness of the continuity barrier (paper)
- On-line double versus near pair `½ ± δ + iγ`, compared statistic by statistic:
  - `Z` has no sign change in either case, so sign statistics agree;
  - `log|Z|` is `2log|t−γ|` versus `log((t−γ)² + δ²)`, which converge in `L¹`, so Jensen/Littlewood agree;
  - Littlewood at `σ₀ = ½` gives `Σ(β−½)⁺ = δ → 0`;
  - for the argument principle, see cycle 17;
  - frame traces and moments agree by the order law.
- Only **pointwise exactness** (`Z(γ) = 0` versus `|Z| ≈ |C|δ² > 0`) separates them, and asymptotic proofs only see
  averages. Hence (meta-theorem, not a Lean statement): any averaging proof of `N₀ ≥ 3/4` also proves "3/4 of zeros
  are simple-like" in the RH world. The 75% target is at least as hard as **75% simple zeros under RH**, whose
  records are 19/27 (CGG) and 0.6725 (pair correlation).

## Cycle 33 — Laguerre duality (paper)
- `Λ(s) := ξ'(s)² − ξ(s)ξ''(s) = −ξ²(ξ'/ξ)'`. It is entire of order 1, `Λ(1−s) = Λ(s)`, real on the critical line
  (`Λ(½+it) = Ξ(t)Ξ''(t) − Ξ'(t)²`), and has `≈ 2N` zeros at heights in `[T, 2T]`.
- **Local duality.**
  - Near pair `ξ ≈ C((s−m)² − δ²)` gives `Λ = 2C²((s−m)² + δ²)`: zeros at `m ± iδ`, **on** the line (vertical split).
  - On-line close pair `ξ ≈ C((s−m)² + ε²)` gives `Λ = 2C²((s−m)² − ε²)`: zeros at `m ± ε`, **off** the line
    (horizontal split).
  - A double gives a double zero of `Λ` at `m`.
  So `Λ` exchanges on-line and off-line local structure. The on-line zeros of `Λ` are the Laguerre-violation
  intervals `{Ξ'² − ΞΞ'' < 0}`, matching the corpus Laguerre-disk law.
- Reformulation: `N₀(ξ) ≥ 3/4N` ⟺ at most `N/4` of the `≈ 2N` zeros of `Λ` lie on the line, i.e. an **upper** bound on
  `Λ`'s on-line proportion.
- Littlewood for `Λ` between `½` and `½ + c/L` needs a lower bound on `∫log|Λ(½+it)| = 2∫log|Ξ| + ∫log|(Ξ'/Ξ)'|`.
  The first term is bounded below by Littlewood for `ξ`. The second is a log-integral, so it is continuous in the
  configuration: both `δ → 0` and `ε → 0` send `Λ`'s zeros to the line. The cycle-32 barrier applies.
- Verdict: structural duality (likely classical, Laguerre/Jensen); no route.

## Cycle 34 — where the CGG off-diagonal blocks beyond θ = ½ (paper, RH-world)
- `Σ_ρ ζ'(ρ)ζ'(1−ρ)h^{−ρ}k^{ρ−1} = (1/2πi)∮(ζ'/ζ)(s)ζ'(s)ζ'(1−s)h^{−s}k^{s−1}ds`. On the right line the
  functional equation turns `ζ'(1−s)` into `χ(1−s)·(ζ, ζ')(s)`. Gonek's stationary phase then leaves
  `Σ_{n ≍ kT/h} c(n)e(−nh̄/k)`, where `c` is a log-weighted `Λ * d`-type convolution coming from `(ζ'/ζ)·ζ'·ζ`.
- Summed over mollifier pairs `h, k ≤ y = T^θ`, the error terms are **distribution of `Λ*d` in arithmetic progressions /
  additive twists to moduli `≤ T^θ`**. The trivial or Bombieri–Vinogradov range stops at `θ = ½`; well-factorable
  Bombieri–Friedlander–Iwaniec-type levels reach `4/7`.
- Hence even under RH the CGG technology ceiling is `θ ≈ 4/7` (law 0.742; shape gain needed `≈ 0.008` for 3/4).
- Unconditional route (II′) needs `θ ≈ 0.67` (cycle 21), i.e. a level of distribution `≈ 2/3` for well-factorable
  `Λ`-type weights. That is **Elliott–Halberstam-type** input beyond BFI.
- Heuristic bridge (not a theorem): EH-type level `≈ 2/3`, the CGG law, and aggregate near-pair curvature control
  together give unconditional `N₀ ≥ 3/4`. At level 1, `V → 7/8 ≥ 0.79`.
- Verdict: BRIDGE to EH-type conjectures. It is conditional, so not usable for the target, but it locates (II′) on the
  prime side: the beyond-length input is a level-of-distribution problem.

## Cycle 35 — level of distribution beyond ½; positive survivor formalised
- The corpus has no level-of-distribution result for primes beyond ½: `research` finds only smooth-number and
  Möbius-rough mean squares. Restricting CGG mollifiers to smooth or densely divisible moduli loses a positive
  fraction of the mollification, lowering the effective `θ`. Known external levels for fixed residues
  (≈ 0.57–0.62) also fall short of the `≈ 0.67` that (II′) needs with varying residues `h̄ mod k`.
  Verdict: BLOCKED.
- **Positive survivor of cycles 9/30 (no-go closure discipline):** the rank–trace step loses exactly three
  nonnegative quantities. The on-line one, `S_on = Σ_{p≠0}(p − c/2 − m)²`, measures the departure of the on-line
  frame from a Parseval frame. Equality forces orthonormal on-line vectors, i.e. the decorated-crystal extremal.
- **Lean [built, wired, standard axioms]:**
  - `RHTower/RankTraceSpectralSlack.lean`: `sum_sq_diff_lower_slack` now keeps the pointwise slack;
    `onSlack`, `onSlack_nonneg`; `rank_trace_ineq_slack` and `zeroside_rank_core_slack` carry `+ S_on`.
  - `RHTower/Zeta23TheoremASpectralSlack.lean`: `onLineParsevalDefect`, `zeroSideSlack` (off-line slack plus
    on-line defect), `zeroSideSlack_nonneg`; `seamA_spectralSlack` and `thmA_lam_spectralSlack` now give
    `(H(λ) − ε)N + S_off + S_on ≤ N₀*` for `ζ`, unconditionally.
  - `#print axioms`: `[propext, Classical.choice, Quot.sound]`. `lake env lean` is clean on both files; no lint
    findings.
- Meaning: any zero configuration within `ηN` of the two-thirds bound has total slack `≤ (η + ε)N`. So its on-line
  frame is nearly Parseval (nearly a crystal) **and** its off-line part is nearly neutral. This is a stability
  form of Theorem A; it does not raise the bound.

## Cycle 36 — can the stability law raise the bound across bandwidths? (paper)
- Decorated lattice (spacing `2π/L`, 2/3 of sites on-line, 1/6 doubled) seen at `λ' = 1 − δ`:
  `sinc(πmλ') = (−1)^{m+1}sin(πmδ)/(πm(1−δ))`, and `Σ_{m≠0}sinc²(πmλ') = 1/λ' − 1` (Poisson: the triangle
  `FT` is supported in `|k| < λ' ≤ 1`). The on-line Parseval defect is therefore `D' ≈ |S|·(2/3)·δ = (4/9)δN`,
  while `H(λ') ≈ 2/3 − (2/3)δ`. Net `H(λ') + D' ≈ 2/3 − (2/9)δ`: **no gain**. The defect grows at rate `4/9`, below
  `H'(1) = 2/3`.
- Structural reason: `D_λ = Σ_{on j≠k}K_λ(γ_j−γ_k)²` is linear in the on-line pair measure, and in
  `2N − X_λ + D_λ` the on–on pairs cancel. What remains is `2N − Σm² −` (cross terms with doubled sites): an exact
  accounting, not new information. All information is in the computed `X_λ`, i.e. `F` on `[0,1]`. Gains beyond
  Montgomery–Taylor therefore need configuration realizability (cycle 31; ceiling 0.68185).
- Local `F` near `1⁺` over a shrinking window `η(T) → 0` gives `r ≥ 2/3 + (2/3)η − O(Cη²) → 2/3`. A **fixed**
  `η > 0` is needed, i.e. variance precision at power-size `H` (core I).
- Verdict: the stability theorem is an exact accounting identity. INSIGNIFICANT for raising the bound; BRIDGE only
  via the realizability SDP.

## Cycle 37 — three-point positivity (realizability, first level) (paper)
- With multiplicities `m ∈ {1,2}`, `Σm³ = 3Σm² − 2N` identically, so three-level data cannot see doubles through moments
  alone. It enters only through spatial weights such as `Σ_j m_j(Σ_k m_k h(γ_j − γ_k))² ≥ 0`.
- Rudnick–Sarnak range for three-level tests `h(x−y)h(x−z)`: vertex frequencies satisfy
  `Σ|ξ| ≤ 2(|ξ₁| + |ξ₂|) < 2`, so each `ĥ` is supported in `[−½, ½]`. That is a two-spacing resolution, weaker than the
  frame's own `tr Â³` at `λ < 1`, which cycle 23 showed gains `≈ 10⁻⁴`.
- Verdict: INSIGNIFICANT. The realizability route offers at most a few thousandths, and needs SDP-type computation.

## Cycle 38 — degree transfer and lower bounds on F (paper)
- `L(s, f×f̄) = ζ(s)L(s, sym²f)` contains ζ's zeros. Its pair correlation in its own normalization is
  diagonal-dominated for `α_L ≤ 1/m` (`m = 4`), i.e. Dirichlet length `X ≤ T`. In ζ's units that is again `α ≤ 1`.
  **The barrier is the absolute length `X ≤ T` of the mean-value theorem, independent of degree.** BLOCKED.
- Proven or GRH lower bounds on `F` beyond 1 (Goldston–Gonek–Özlük–Snyder type, `F ≥ 3/2 − α`) bound `‖Â_λ‖²`
  from below, which works against `N₀*` lower bounds. No certificate for `N₀` from below can use them.
  Verdict: wrong direction.

## Cycle 39 — structural RH lanes: do they have proportion versions? (corpus)
- `XiWindowNonrealBudget.encard_nonrealCopies_le_iff_window`: the **global** nonreal count of `Ξ` equals the minimal
  nonreal-root budget of real polynomials converging on any window. By analytic continuation any window sees the
  global count. A height-`T` proportion analogue would need quantitative approximants on `[T, 2T]` that resolve every
  zero (Rouché at zero scale), with at most `N/4` nonreal roots. That is a producer problem as hard as the target.
- `XiCosineShiftDeepZeroBudget` (`cos(hD)Ξ = Re Ξ(t+ih)` has `≤ 2#{depth > h}` defects): with `h = A/log T` and
  density for deep zeros, `Re Ξ(·+ih)` has `≥ (1 − 2ε(A))N` real zeros locally. But shallow pairs, exactly the corner's
  near pairs, become real under `cos(hD)`, so this bounds deep zeros only.
- de Bruijn–Newman (`DeBruijnNonrealCountFinitenessTransition`): nonreal counts of `H_t` decrease in `t`. A lower bound
  at `t = 0` needs the opposite direction.
- Weil-cone / localized positivity `Â_λ ⪰ 0` gives only `r ≥ #`(pairs with non-negligible negative part).
- Verdict: no structural lane has a proportion version that avoids the producer problem. All of them see near pairs
  only through continuous functionals (cycle 32).

## Cycle 40 — one-sided sieve majorant for the Fejér twin-prime statistic (paper)
- Write `Λ = Λ⁺ − E` with `E ≥ 0`, where `Λ⁺` is a Selberg/β-sieve majorant of level `D ≤ x^{½−ε}`. Then
  `Σ_nΛ(n)Λ(n+h) ≤ Σ_nΛ(n)Λ⁺(n+h) = Σ_d λ_d ψ(x; d, −h)`. Bombieri–Vinogradov gives this as `x·S⁺(h) + o(x)`, with
  `S⁺(h) = E_p[Λ⁺(p+h)]`.
- Needed: `Σ_h(1−|h|/H)(S⁺(h) − 𝔖(h)) = O(log x)`, i.e. the majorant's excess mass on shifted primes must be
  `O(H^{−1}log x)`. Parity forces the excess of any sieve majorant of the primes to be `≫ 1` (relative), so the bound
  overshoots by `≍ xH`.
- Variances are not monotone under majorants, so no second-order transfer exists. Verdict: BLOCKED (parity versus
  variance precision).

## Cycle 41 — non-averaging principles (paper)
- The only feature separating an on-line double from a near pair is pointwise: `ζ'(ρ) = 0` versus `|ζ'(ρ)| ≈ 2|C|δ`.
  Statistics that are unbounded as `δ → 0` see it:
  - **Negative discrete moments** `J_{−1} = Σ_ρ|ζ'(ρ)|^{−2}`. An upper bound `J_{−1} ≪ T` excludes doubles outright and
    limits near pairs by `Σ δ^{−2}|C|^{−2}`. But upper bounds on `J_{−1}` are open even under RH: finiteness alone means
    all zeros are simple. In bilinear form near pairs contribute `−1/(4δ²|C|²)` (wrong sign), forcing compensating close
    on-line pairs rather than a contradiction. Contour methods reach `Σ 1/ζ'(ρ)` only through `1/ζ` (Mertens), with
    lower bounds only.
  - **Small values of ζ** (lower bounds for `|ζ|` off the zeros): open.
  - **Gram conditioning** (`σ_min` of the on-line Gram): Ingham-type separation of zeros, open.
- Verdict: every non-averaging principle needs a pointwise lower bound that is at least as strong as a
  simple-zero / separation conjecture. BLOCKED.
- Summary after 41 cycles: (a) averaging methods meet the continuity barrier (cycle 32); (b) beyond it, input (I)
  meets RH-log-loss and parity (cycles 20, 25, 40), and input (II′) is Elliott–Halberstam-type (cycle 34);
  (c) non-averaging principles need simple-zero / separation conjectures (this cycle).

## Cycle 42 — regularised negative moments (paper)
- `Σ_ρ|ζ'M(ρ)|^{−2s}`, `s > 0`, is infinite if a single double zero exists. An upper bound for any `s > 0` implies all zeros in
  the window are simple, which is beyond the simple-zero conjecture's known reach. Dirichlet-polynomial methods cannot
  produce negative powers of `ζ'` (lower bounds only, via Cauchy–Schwarz).
- Truncations `Σ min(|ζ'/L|^{−2s}, K)` are bounded, hence continuous. With `K = K(T) → ∞` an upper bound only controls
  zeros with `|ζ'/L| < K^{−1/(2s)} → 0`, i.e. pairs with **vanishing** displacement `a → 0`. The adversary's fixed-`a` pairs
  (`a ≈ 0.2–0.65`) are untouched.
- **Dichotomy.** A statistic is either bounded on near pairs (continuous, so the barrier applies at `a → 0`, and at fixed
  `a` the cost is `∝ a²`, the CGG/Zeta23 trade-off of cycle 21), or unbounded (and then its upper bound needs
  simple-zero-type conjectures). Fixed-`a` near pairs are the quantitative core in either case.
- Verdict: BLOCKED. The classification of cycle 41 stands, refined: the binding adversary is fixed-`a` near pairs, priced
  at `a²` by every available statistic.

## Cycle 43 — log-determinant of the frame (paper)
- `log|det Â| = Σ log|μ|`. A near pair contributes `log(1+s) + log(s−1) ≈ log 2 + log(a²/6)`, first order in `log a`.
  An on-line close pair at separation `ε` contributes `≈ log 2 + log(cε²)`. Matching `ε ↔ a` makes them equal, so `|μ|`
  is again continuous across the configuration families. Only the **sign** of the small eigenvalue differs
  (negative for off-line pairs).
- The inertia count `n₋(Â)` would see the sign, but `P ⪰ 0` absorbs the pair's tiny negative direction, which is the
  derivative bump `v'(t)`, overlapped by the neighbours' vectors. So `n₋(Â)` is typically far below `p`.
- `tr log Â` needs all spectral moments. Jensen gives only `tr log Â ≤ d log(tr Â/d)` (upper); no lower bound is computable.
- Verdict: BLOCKED. Neither the frame log-determinant nor the inertia prices fixed-`a` pairs at order `a¹` through
  computable data.

## Cycle 44 — corpus first-order statistics against the fixed-a adversary (corpus + paper)
- Corpus first-order bounds:
  - off-line moment `Σ(β−½)⁺ ≤ μV`, `μ = 67/1000`. In `a`-units, `Σ_{right zeros} a ≤ 2πμ N ≈ 0.42N`;
  - tail law `4πΣ(β − ½ − R/log V)⁺ ≤ (log c − 2R + η)V`, which only reaches `a > R`;
  - Selberg near-line barrier: a lower bound, wrong direction.
- Joint adversary (cycles 16/21, `κ` heuristic): `π_p ≈ 0.157`, `a ≈ 0.65`, so `Σa ≈ 0.10N`. **The moment bound is not
  binding**: it would need `2πμ ≲ 0.10`, i.e. `μ ≲ 0.016`. The corpus's best `μ` is `0.067` (`θ = 21/50`), and the
  mollifier floor is `≈ 0.06` even at `θ = ½`. Since `μ → 0` only as `θ → ∞`, binding needs `θ ≫ 1`.
- An upper bound on `Σa` gives no upper bound on `Σa²` (Cauchy–Schwarz runs the other way), so it cannot cap the CGG
  cost either.
- Verdict: INSIGNIFICANT. Order-`a¹` information exists, but its constant is about 4× too weak. Strengthening it is
  Levinson's mollifier-length problem (`θ ≫ 1`).

## Cycle 45 — three-way joint certificate by convex duality (paper)
- The adversary chooses a pair-displacement measure `ν` (mass `≤ (1−r)/2`) subject to:
  - Zeta23: `∫σ dν ≤ r − 2/3`, with `σ(a) = (sinh a/a)² − 1 = a²/3 + 2a⁴/45 + …`;
  - CGG: `∫c dν ≥ V/r − 1`, with `c(a) = 8κa²`;
  - moment: `∫a dν ≤ 2πμ ≈ 0.42`.
- `c/σ` is maximal as `a → 0` (`→ 24κ`) and `σ` is convex in `a²`, so an optimal `ν` is a point mass at a single `a`. At the
  two-way optimum (`a ≈ 0.65`, mass `≈ 0.157`), `∫a dν ≈ 0.10 < 0.42`. **The moment constraint is slack, and the three-way
  crossing equals the two-way one** (≈ 0.687 with the heuristic `κ` cap; ≈ 0.673 with a provable cap).
- Verdict: INSIGNIFICANT. To bind, the moment constant must fall below the adversary's `M_p·a`, i.e.
  `μ < 0.016` (cycle 44).

## Cycle 46 — other zero-side objects: a-points, antisymmetric combinations, phases of ξ'(ρ) (paper)
- `ζ(s) − ζ(1−s) = ζ(s)(1 − χ(1−s))`: its zeros are ζ's zeros plus solutions of `χ(1−s) = 1`. No new information.
- a-points of `ζ` lie mostly left of the line (Levinson) and have no zero-pairing structure. No handle on near pairs.
- **Phase coherence:** `ξ'(½+iγ) = −iΞ'(γ)` is purely imaginary at on-line zeros, while at a near pair
  `ξ'(ρ) = 2Cδ` is real (`C` real because `ξ` is real on the line): a `π/2` phase gap for every `δ > 0`. But
  `ξ'(1−s) = −ξ'(s)` makes the analytic statistic `Σ_ρ ξ'(ρ)ξ'(1−ρ) = −Σ ξ'(ρ)²` exactly CGG's bilinear second moment. On-line
  zeros give `+Ξ'²`, near pairs `−4C²δ²` each: the phase gap is visible only through the magnitude `δ²`. First moments
  cancel within a pair to `O(δ²)` (order law, cycle 10).
- Verdict: REDISCOVERED (the CGG cost). A first-order phase detector would need `|ξ'(ρ)|` (non-analytic), which no
  contour method computes.

## Cycle 47 — two-variable statistics with the conjugate zero (paper)
- `ξ'(ρ̄) = conj ξ'(ρ)`, so `Σ_ρ ξ'(ρ)ξ'(ρ̄)h(ρ) = Σ|ξ'(ρ)|²h(ρ)` is the true Hermitian moment. There near pairs count
  positively, which is what a certificate wants.
- On the zero set, `ρ ↦ ρ̄` agrees with the analytic involution `ρ ↦ 1 − ρ` exactly on the critical line, and
  `ρ̄ = (1−ρ) + (2β − 1)`. Every statistic that separates the Hermitian moment from the bilinear one depends on
  `β − ½ = Re ρ − ½`, which is non-analytic in `ρ`. Contour methods evaluate only `Σ_ρ G(ρ)` with `G` analytic, and a
  double contour cannot impose `ρ' = ρ̄`. Verdict: BLOCKED (order law, cycle 10, in two-variable form).

## Cycle 48 — prime-blind tests and rank-sharpened Jensen (corpus + paper)
- Prime-blind tests (corpus PBAP / (N1): `g(log n) = 0` for all `n`) make the explicit formula exact without primes:
  `Σ_ρ ĝ(γ_ρ) = Γ-part`. Still `Σ_ρ ĝ(γ_ρ)` is analytic in the zeros, so a near pair contributes
  `ĝ(t+iδ) + ĝ(t−iδ) = 2ĝ(t) − δ²ĝ''(t) + …` (order law). The exact total therefore bounds deep zeros (cosh growth)
  but not near pairs. Moreover, blindness at bandwidth `λ log T` forces `g` to vanish on the `e^{−L}`-dense set
  `{log n}`, which pushes `ĝ` to frequencies `≍ T^λ`. Only support `< log 2` is blind for free, and that has no local
  resolution at height `T`.
- Rank-sharpened Jensen: Levinson's loss is `log E|GM|² − E log|GM|²`. A Gram of several mollified functions only
  re-optimizes the mollifier (already done by Levinson–Conrey). No rank or inertia quantity enters Littlewood's
  identity.
- Verdict: BLOCKED.
- Converged picture after 48 cycles: analytic statistics see near pairs at order `δ²` (order law). The only
  non-analytic tools (Jensen/Littlewood, rank/inertia) are fed by analytic data (mean squares, traces), so their
  outputs inherit the same limits. Breaking `3/4` needs either new beyond-length-`T` analytic input (I or II′) or a
  pointwise principle (separation or small-value conjectures).

## Cycle 49 — corpus pair-correlation assets near α = 1⁺ (corpus)
- `MontgomeryPairCorrelationUniform.eventually_montgomeryForm_div_leadingOrder_uniform`: unconditional
  `montgomeryForm(T^α) ~ (T/2π)·α log T` uniformly for `α ∈ [a, b] ⊂ (0,1)`. The form is the **Hermitian** one,
  `Σ_{j,k} x^{ρ_j + ρ̄_k − 1}·w`, so off-line zeros enter with weight `x^{2(β−½)}`.
- `MontgomeryPairCorrelationShortLength.eventually_montgomeryForm_lower_uniform`: a lower bound for
  `x ∈ [(log T)³, T^{1/8}]` only.
- No corpus statement reaches `α ≥ 1` (closed endpoint or beyond), in either direction. The Hermitian form at
  `α → 1⁻` is uniform on compact subsets of `(0,1)` only, with no rate at the endpoint.
- Verdict: BLOCKED. The corpus's pair-correlation knowledge stops at the Montgomery range `(0,1)`, exactly where the
  decorated-crystal extremal hides its Bragg peak (cycle 30).

## Cycle 50 — endpoint Montgomery with rate (paper)
- A uniform `F(α) = α + O(1/log T)` up to the closed endpoint `α = 1` would let the `c = 2` certificate run at
  `λ = 1 − O(1/log T)` with explicit constants. Zeta23 already takes `λ → 1⁻`, and `H(1) = 2/3`, so the limiting
  proportion is unchanged. The beyond-1 input that matters is variance-level (core I), and endpoint precision does not
  feed it: the Bragg peak of the extremal sits at `α = 1` with weight zero in every `λ ≤ 1` certificate.
- Verdict: INSIGNIFICANT (no change to the proportion). Not built.

## Cycle 51 — Hermitian minus bilinear pair form (corpus + paper)
- The corpus Hermitian form `H(x) = Σ_{j,k} x^{ρ_j+ρ̄_k−1}w` (unconditional asymptotic on `(0,1)`) and the bilinear form
  `B(x) = Σ_{j,k} x^{ρ_j−ρ_k}w` (Zeta23) agree on on-line zeros. For off-line `k`,
  `x^{ρ̄_k−1} − x^{−ρ_k} = x^{−iγ_k−½}·2sinh(δ_k log x)`, which looks first order in `δ_k`.
- But the pair `{½ ± δ + iγ}` enters with both signs of `δ` at the same `γ`. The `sinh` terms cancel, and the residual
  comes from `w(ρ_j+ρ̄_k−1)` differing by `2δ`, giving `O(δ·sinh(δ log x)) = O(δ²)`. So `H − B` is even in `δ`.
- **Clean form of the order law:** the zero multiset depends on each pair only through `|δ|`. Hence every functional of the
  configuration is a function of `|δ|`, and every functional that is smooth in the configuration (anything built from
  analytic test functions) is a smooth function of `δ²`, i.e. `O(δ²)`. First order needs non-smooth dependence on `|δ|`,
  which only log-modulus (Littlewood/Jensen) functionals supply.
- Verdict: BLOCKED (order law, now proved in one line).

## Cycle 52 — Selberg's formula for log ζ as a Jensen-free first-order route (paper)
- Littlewood: `Σ(β−σ₀)⁺ = (1/2π)∫log|ζ(σ₀+it)|dt + O(log T)`. Selberg's formula writes
  `log ζ(s) = Σ_{n≤x²}Λ_x(n)/(n^s log n) + Σ_ρ`(terms `≍ x^{ρ−s}/(s−ρ)²`). The prime part has mean zero in `t`, so the
  off-line first moment equals the mean of the zero part, with no Jensen loss.
- But the zero part involves `x^{β−σ}` for `β > σ`. Bounding it needs a density estimate near `σ₀`, which is circular. On
  average Selberg's moment bounds give `E|log ζ − P| ≪ 1`: an `O(1)` mean, not `o(1)`. That matches the mollifier floor
  `μ ≍ const`.
- Verdict: CIRCULAR. The log-modulus route's constant is the Jensen/mollifier floor however it is expressed
  (cycle 44: `μ` must drop from 0.067 to 0.016).

## Cycle 53 — two-line Littlewood difference (paper)
- `Σ_ρ min(β−½, c/L)⁺ = (1/2π)∫[log|ζ(½+it)| − log|ζ(½+c/L+it)|]dt` prices pairs by `min(a, c)` (first order).
- Upper bound: Jensen on the first line, with mollifier (the corpus gate). Lower bound on the second line: Littlewood
  positivity gives only `∫log|ζ(σ₁+it)| ≥ ∫log|ζ(σ_large+it)| ≈ 0`, which is trivial. So the difference carries the full
  single-line Jensen loss. A non-trivial lower bound is `2πΣ(β−σ₁)⁺ + const`, which is circular.
- Jensen on the ratio `ζ(½+it)/ζ(½+c/L+it)` needs mean values with `1/ζ` in the denominator, i.e. a shifted mollifier,
  which is already inside the Levinson–Conrey optimisation.
- Localising to frame windows does not help: the frame cannot locate near pairs (they enter it at order `δ²`).
- Verdict: BLOCKED (Jensen floor).

## Cycle 54 — evaluating (not bounding) the Jensen gap (paper)
- Split `log|GM(σ₀+it)| = A(t) + Z(t)`, where `A` is the prime fluctuation beyond the mollifier and `Z = Σ_ρ log|σ₀+it−ρ|`
  (smoothed at scale `R/L`). `Var Z` is a pair statistic, computable at bandwidth `< 1` up to `e^{−R}` tails. But the
  gap `log E e^{2Z} − 2E Z` involves all cumulants, and `A`, `Z` are not independent.
- Reverse Jensen from positive moments fails: with `W = |GM|²`, `E W = m₁`, `E W² = m₂ > m₁²` fixed, the two-point
  laws `(1−ε)δ_{m₁} + εδ_{w₂}` reach `sup E log W = log m₁` as `ε → 0`. Rare large values carry the variance at no log
  cost. Any finite set of positive moments gives zero guaranteed gap; a gap needs lower-tail information (negative or
  fractional moments), which is circular or not computable (cycles 5, 42).
- Verdict: BLOCKED. The Jensen floor cannot be lowered by more moment data. It needs lower-tail control of `|ζM|`,
  i.e. small-value estimates.

## Cycle 55 — unconditional lower-tail information for ζM at the Levinson line (paper)
- The lower tail of `log|GM(σ₀+it)|`, `σ₀ = ½ − R/L`, comes from zeros of `G` (and of `ζ` left of the line) near
  `σ₀ + it`. Small-value estimates there are zero-density statements at distance `≍ 1/log T`, i.e. the target itself.
  CIRCULAR.
- Selberg's CLT has error `≍ (log log T)^{−1/2}` relative to variance `½ log log T`. After mollification the variance is
  `O(1)` (`½ log(1/θ)` plus local zeros) and no limit theorem applies. Large-deviation methods (Soundararajan-type) give
  upper tails (moment bounds), not lower tails.
- Verdict: BLOCKED. The four walls reinforce each other: the lower-tail floor of the log-modulus route is again near-line
  zero density.

## Cycle 56 — Zeta23 slack absorbing far pairs in sign-uncertainty certificates (paper)
- Certificates that use the unconditional bilinear `F ≥ 0` beyond 1 (aiming at the configuration-wise ceiling 0.68185)
  need `k̂ < 0` on `[1, 1+η]` with negative mass `m`. A far isolated pair costs `≈ m·cosh(2(1+η)a)`. The Zeta23 slack it
  generates is `s(a)² − 1 ≈ e^{2a}/(4a²)`. The ratio is `≈ 4ma²e^{2ηa}`, unbounded as `a → (½)log T`. Clusters lower the
  slack further (cycle 11), and the corpus tail law decays only at rate `2θ ≈ 0.84 < 2`.
- Absorption needs `η ≲ log a_max/a_max ≍ log log T/log T` or `m ≲ (log T)^{−C}`. Either way the gain tends to 0.
- Verdict: BLOCKED. Even the record-scale improvement toward 0.68185 is out of unconditional reach. The corpus record
  0.6725 (Montgomery–Taylor window) is the unconditional optimum of every certificate class examined.

## Cycle 57 — where averaging exists, the 3/4 barrier falls (paper sketch; positive survivor)
- Cause of ζ's obstruction (cycles 8, 20, 25, 40): in `‖Â_λ‖² = ‖Γ − Π‖²` the prime part `Π` has mean `≈ Γ` (prime number
  theorem), so the off-diagonal prime pairs carry a huge mean that cancels only at variance precision.
- **Twisted family:** for a nonprincipal `χ`, `Π_χ` has no mean, so `‖Â_χ‖² ≈ ‖Γ‖² + ‖Π_χ‖²` with no cancellation needed.
  Averaged over primitive `χ mod q`, `q ∈ [Q, 2Q]`, and heights `[T, 2T]`, the hybrid large sieve
  `Σ_q Σ*_χ ∫|Σ_n a_nχ(n)n^{−it}|² ≪ (Q²T + X)Σ|a_n|²` bounds the off-diagonal by `X/(Q²T)` times the diagonal. In
  family units (conductor `≍ QT`, `X = (QT)^λ`): `F_fam(α) ≤ 1 + c(QT)^α/(Q²T)` for `α ∈ [1, λ]`.
- Zeta23's per-`L` `c = 2` certificate (Theorem E, pair-neutral, no GRH) is linear, so it averages:
  `avg N₀*(χ) ≥ (2 − avg‖Â_χ‖²/N)·N`. With the closed form of cycle 17, `r ≥ (2C−1)/(3C−2)`, or directly
  `r ≥ 1 − 1/(3λ²)` when `C → 1`:
  - `T ≤ Q^{2−ε}` gives `C ≤ 2` at `λ = 4/3`, hence average proportion `≥ 3/4`;
  - `T = Q^{1/κ}`, `κ → ∞`, gives `λ_max → 2`, `C → 1`, hence `≥ 1 − 1/12 = 11/12`.
- **Conjecture F57 (exact).** For `Q, T → ∞` with `T ≤ Q^{2−ε}`:
  `Σ_{Q<q≤2Q} Σ*_{χ mod q} N₀*(χ; T, 2T) ≥ (3/4 − o(1)) Σ_{q,χ} N(χ; T, 2T)`, unconditionally. With `T ≤ Q^{ε}` the
  constant becomes `11/12 − ε`.
- Comparison (internal reasoning; the loop rules exclude external checks): the unconditional family record by
  Levinson-type methods is 56% (Conrey–Iwaniec–Soundararajan). 11/12 is the GRH-conditional simple-zero value
  (Chandee–Lee–Liu–Radziwiłł, asymptotic large sieve), and Zeta23's pair-neutrality removes GRH.
- [OPEN CORE] Zeta23's Theorem E machinery uniformly in the conductor (`q ≍ Q → ∞` together with `T`): Poisson grid,
  tails, Riemann–von Mangoldt `O(log qT)`, trace evaluation for `λ < 2`. Plus the hybrid large sieve in the exact form
  needed (corpus: `LargeSieveGallagher`, `FareyHybridLargeSieve` pieces).
- Verdict: SURVIVES PRELIMINARY ATTACK. It is **not** the ζ target: ζ is a single member, and the family average
  cannot isolate it (cycle 18). It is the positive survivor of the whole loop: the 75% obstruction for ζ is exactly the
  absence of averaging over a family.

## Cycle 58 — F57 paper proof, first pass: error inventory and the large-sieve constant (paper)
- **Uniformity inventory** (`Zeta23/ThmE`, `PaperInputsChi`: EF, RvM, Chebyshev–Mertens coprime, MV–Hilbert,
  Γ-facts). Theorem E is proved for **fixed** `q` (constants `∃C`, `T → ∞`). The family version needs each input
  uniform in `q`:
  - RvM: `N(T,χ) = (T/2π)log(qT/2πe) + O(log qT)`, classical and uniform;
  - Chebyshev/Mertens coprime: `O(log q)` errors;
  - MV–Hilbert: absolute;
  - Γ-facts: uniform;
  - tails: through local RvM.
  Routine but large; the per-`χ` errors are `o(N_χ)` once `T → ∞`.
- **Trace average.** `Σ*_χ` kills `n ≢ 1 (mod q)`, so the prime part is `≪ #F·√X/Q`, which is `o(#F·T log)` iff
  `X ≤ (QT)^{2−ε}` (family one-level support `< 2`). ✓
- **Frobenius average, crude route.** The sharp large sieve (`Σ_q (q/φ(q))Σ*_χ|Σa_nχ(n)|² ≤ (Q² + N)Σ|a_n|²`) is not sharp on
  the diagonal: `Σ_{q≤Q}(q/φ(q))φ*(q) ≈ 0.3Q²`. So it gives off-diagonal `≤ (≈ 2.3)·diag + X/(Q²T)·diag`, i.e. `C ≈ 3.3`
  and `r ≥ (2C−1)/(3C−2) ≈ 0.709`. **This is already beyond 0.6725 and beyond the 56% family record**, using only
  the large sieve (corpus `LargeSieveGallagher`).
- **Frobenius average, sharp route.** Primitive orthogonality `Σ*_χ χ(n)χ̄(m) = Σ_{d|q, d|n−m} μ(q/d)φ(d)` cancels the
  Hardy–Littlewood main terms of the shifts `h = kq` (`|k| ≤ X/(qT)`). Evaluating the remainder needs an asymptotic
  large sieve for `Λ`-coefficients: Bombieri–Vinogradov to moduli `≍ Q ≤ X^{1/2}`, i.e. `Q ≤ T^{2}` at `λ = 4/3`, in the
  Conrey–Iwaniec–Soundararajan style. That gives `C → 1+` and `r ≥ 1 − 1/(3λ²)`.
- Refined F57: (a) unconditional `≥ 0.70` family average from Zeta23 (uniform) + the sharp large sieve; (b) `≥ 3/4`
  (towards 11/12) with the asymptotic large sieve for `Λ` (Bombieri–Vinogradov range).

## Cycle 59 — the crude-route constant for F57a (paper computation)
- For each shift `u`, the Frobenius prime part is a family mean square `Σ_χΣ_k|Σ_n b_n(u)χ(n)n^{−iτ_k}|²` with
  `b_n(u) = Λ(n)n^{−½}φ(u)φ(u − log n)`. Split `n ≤ QT` (orthogonality exact, `F₀ = α` on `[0,1]`) from `n > QT`. The sharp
  large sieve bounds the latter by `R·diag`, with
  `R = Q²/Σ_{q≤Q}(q/φ(q))φ*(q) ≈ 3.3` (all `q ≤ Q`; a dyadic family `q ∈ [Q,2Q]` is worse, `≈ 4.4`).
- Flat profile, `F₀ ≤ Rα` on `[1, λ]`, cross terms ignored (optimistic):
  `m₂ = (1/λ)[1 + 2∫_0^1(1−α/λ)α dα + 2R∫_1^λ(1−α/λ)α dα]`.
  Values: `λ = 1.05 → r ≥ 0.692`; `1.10 → 0.704`; `1.12 → 0.706`; `1.15 → 0.706`; `1.20 → 0.699`.
  The optimum is `≈ 0.706`. A Montgomery–Taylor profile adds `≈ 0.006`, so `≈ 0.71`.
- **F57a (refined):** unconditionally, averaged over primitive `χ mod q ≤ Q` at heights `[T, 2T]` with `T ≤ Q^{2−ε}`, at
  least `≈ 0.70` of the zeros lie on the critical line. It needs (i) a conductor-uniform Theorem E seam and (ii) the
  sharp large sieve (corpus `LargeSieveGallagher`). Cross terms between the `n ≤ QT` and `n > QT` blocks have to be
  bounded (Cauchy–Schwarz, `O(√R)` relative to the small block), which may cost a little.
- Why ζ gets nothing: for `q = 1` the mean-value theorem gives `R = 1 + X/T = 1 + T^{α−1}`, unbounded beyond 1. Families
  help through the `Q²` count of members.

## Cycle 60 — CORRECTION: the crude large-sieve route (F57a) fails; F57b needs an asymptotic large sieve (paper)
- The large sieve bounds only the **total** family mean square: `offdiag ≤ (R − 1)·diag(all)`. In certificate units that
  is `∫_1^λ(1−α/λ)F₀ ≤ ∫_1^λ(1−α/λ)α + (R−1)λ²/6`. The excess is `O(R − 1)`, order one, while the gain from `λ > 1` is
  first order, `(2/3)(λ − 1)`.
- A Cauchy–Schwarz split into blocks `n ≤ QT` and `n > QT` gives `m₂ ≈ 4/3 − δ(2/3 − 2√(R/3))`, a gain only if
  `R < 1/3`. **So any non-asymptotic large sieve (`R > 1`) gives nothing.** Cycle 59's `≈ 0.70` ignored cross terms and is
  withdrawn. F57a is FALSE as a route.
- **F57b needs `R = 1 + o(1)`**, i.e. an asymptotic evaluation of the family off-diagonal:
  `Σ_{q~Q}Σ_{d|q}μ(q/d)φ(d) Σ_{0<|h|≤X/T, d|h} Σ_nΛ(n)Λ(n+h)`. Its Hardy–Littlewood main terms carry the
  primitive-character Möbius cancellation. When `X ≤ Q²T log X` the off-diagonal main term is `≲ diag`, so
  **relative `o(1)` precision suffices** (no variance precision, unlike ζ).
- Candidate input: L² averaged Hardy–Littlewood, `Σ_{h≤H}|Σ_nΛ(n)Λ(n+h) − 𝔖(h)X|² ≪ HX²(log X)^{−A}` for
  `H ≥ X^{8/33+ε}` (Matomäki–Radziwiłł–Tao type, unconditional). Then Cauchy–Schwarz against the divisor weight
  `ν(h) = #{d ~ Q : d | h, h/d ≤ K}` with `Σν² ≪ H(log)^c` gives error `o(main)`. Range: `H = X/T ≥ X^{8/33}`.
- Revised F57b: unconditional family average `≥ 3/4` (towards `1 − 1/(3λ²)`). Inputs: conductor-uniform Theorem E,
  L² averaged Hardy–Littlewood, and an exact main-term computation showing `F₀ ≈ 1` beyond 1.
  Status: SURVIVES (sketch); [OPEN CORE] the main-term identity and the MRT-type input.
- Lesson: for ζ the needed precision is variance-level because Γ-cancellation forces subtracting the mean. For
  families, relative-`o(1)` asymptotics of averaged correlations suffice, and those are known-type results.

## Cycle 61 — main term of the family off-diagonal (paper, heuristic level)
- Off-diagonal: `Σ_{q~Q}Σ_{d|q}μ(q/d)φ(d)Σ_{k≠0, |kd|≤X/T}Σ_nΛ(n)Λ(n+kd)·V`. With Hardy–Littlewood main terms
  `𝔖(kd)X`, the `d`-sum with `μ(q/d)φ(d)` and the average of `𝔖` over multiples of `d` form the
  Bogomolny–Keating structure. Singular series summed against the Ramanujan-type kernel reproduce the GUE term,
  `F(α) = 1` for `1 < α < 2` in family units. This is consistent with the GRH-conditional family pair correlation in the
  internal comparison of cycle 57.
- Hence F57b predicts an unconditional family average `≥ 1 − 1/(3λ²)` (flat profile; Montgomery–Taylor adds a little),
  i.e. `≥ 0.8125` at `λ = 4/3` and `→ 11/12` as `λ → 2` (`T = Q^{o(1)}`). The unconditional inputs needed:
  - L² averaged Hardy–Littlewood (Matomäki–Radziwiłł–Tao type) over `h ≤ X/T`, with `X/T ≥ X^{8/33+ε}`, against divisor
    weights. Cauchy–Schwarz with `Σν² ≪ H(log)^c` gives error `o(main)`;
  - conductor-uniform Theorem E;
  - exact main-term evaluation (Bogomolny–Keating identity, made rigorous).
- Corpus: the averaged-correlation consequences exist only as hypotheses (`MRFromCorrelations`,
  `AveragedCorrelationSmall`); there is no Lean Matomäki–Radziwiłł–Tao theorem.
- Status: F57b is a coherent multi-component research program for the **Dirichlet family**. It does not touch ζ
  (cycle 18).

## Cycle 62 — can ζ's frame be twisted to remove the prime mean? (paper)
- Multiplicative twists `n^{iT₀}` keep ζ's zeros, but on the off-diagonal (`|n−m| ≤ n/T`) the phase
  `(n/m)^{iT₀} ≈ e^{iT₀(n−m)/n}` varies by at most `T₀/T`. The twist only shifts the height, and the prime-number-theorem
  mean survives.
- Twists that kill the mean must oscillate at scale `|n−m| ≍ 1` (characters, additive phases). Characters change the
  L-function. Additive twists destroy the Euler product, so there is no explicit formula over ζ's zeros.
- Containing families: `ζ_K = ζ·L(s,χ_K)` (or `L(s,χ₀ mod q)`). Averaging over `K` gives `N₀(ζ) ≥ cN(ζ) − (1−c)·avgN(L)`,
  and `N(L) ≳ N(ζ)`, so this is useless. In the frame, the ζ–ζ block is untouched by family averaging; ζ–L cross terms
  vanish on average.
- Verdict: BLOCKED. The prime mean is intrinsic to the single member ζ. This is the precise form of cycle 18's
  "single-arc" obstruction.

## Cycle 63 — internal "families" of ζ (paper)
- Real shifts `ζ(s+v)` give prime weights `Λ(n)n^{−v}`, smooth in `n`, so the mean survives. Imaginary shifts only
  relabel heights. Products `ζ(s)ζ(s+iu)`: the ζ–ζ block is unchanged (cycle 62).
- Height and length averaging (`x ∈ [X,2X]`, Fejér over `H`) are already part of the Goldston–Montgomery variance.
  The variance needs subtraction of `h²` against `Σ(h−|k|)S(k)`, and any sieve upper bound has constant `> 1` by
  parity (cycle 40).
- Verdict: BLOCKED. ζ has no internal averaging that cancels the prime mean. The single-function obstruction is
  complete.

## Cycle 64 — inertia spectral flow and ordinate coincidences (paper)
- **Spectral flow of the sliding prime-side Gram `Gp(T)`.** An on-line zero entering the window raises `n₊`. An off-line
  pair raises `n₊` and `n₋` *unless absorbed*. A near pair's negative direction is the derivative bump `v'(t)`, and
  neighbouring on-line vectors `v(γ_j) ≈ v(t) + (γ_j − t)v'(t)` give `P` an `O(1)` quadratic form on it, which absorbs
  `−a²/6`. So jumps of `n₋` do not count near pairs. BLOCKED.
- **Ordinate coincidences.** Doubled sites are ordinate gaps `0` (or `2iδ` in bilinear form). Counting them needs `F` at
  large `α` (the self-term `Σm²/N`, or `cosh(2αa)` growth): the beyond-1 core again. BLOCKED.

## Cycle 65 — local window certification (paper)
- Idea: certify window by window that the local frame spectrum has no eigenvalue near 2 (no doubled site), then count
  on-line zeros exactly in certified windows.
- Local Gram entries at a specific window are prime sums at a specific height, so their values are not asymptotically
  computable. Only window averages are. "Most windows have no doubled site" is a statement about the distribution of
  the local largest eigenvalue, i.e. local pair correlation at resolution below one spacing. That is `F` beyond the
  Nyquist frequency again (the doubled-site signature sits at `α ≥ 1`, cycle 30).
- Verdict: BLOCKED (beyond-1 core).

## Cycle 66 — F57b paper proof, part 1: the conductor scale of the frame (corpus + paper)
- `Zeta23/ThmE/AssemblyQ`: Theorem E keeps `L = λ·log(T/2π)` (prime length `X = (T/2π)^λ`), while the zero density is
  `ℓ_{1,χ} = log(qT/2π) + 2log2 − 1`. So `λ₁ = L/ℓ_{1,χ} = λ log T/(log T + log q) → λ` only for **fixed** `q`. For
  `q = T^κ` a single `L(s,χ)` gets bandwidth `λ/(1+κ)` relative to its conductor, and Theorem E degrades to
  `H(λ/(1+κ)) < 2/3`. For one character, `t`-integration alone is diagonal only up to `X ≤ T`.
- F57b design (consistent with this):
  - set `L = λ·log(QT/2π)` (so `X = (QT)^λ`) for every `χ` in the family;
  - per `χ`, the seam (zero side = prime side, pair-neutral `c = 2` certificate) is an exact identity plus errors
    (Poisson, tails through local RvM `O(log qT)`, `NII`) that are uniform in `q`;
  - the trace and the Frobenius are evaluated **only on family average**: character orthogonality gives diagonal
    dominance up to `X ≤ QT` (`λ ≤ 1`), and the asymptotic large sieve plus Matomäki–Radziwiłł–Tao input up to `λ < 2`.
- Consequence already at `λ ≤ 1`, using only orthogonality: the family average reaches `H(1) = 2/3` (Montgomery–Taylor:
  0.6725) **uniformly in the `q`-aspect**, where single-`χ` Theorem E gives only `H(1/(1+κ))`. This lower half of F57b
  needs no new analytic input beyond orthogonality and uniform errors. It is the first formalizable piece.

## Cycle 67 — F57b lower half: exact statement and proof skeleton (paper)
- **Conjecture F57b-low.** Let `Q, T → ∞` with `log Q ≪ log T`, `λ ∈ (0,1)`, `L = λ log(QT/2π)`. Then, unconditionally,
  `Σ_{q≤Q}Σ*_{χ mod q} N₀*(χ; T, 2T) ≥ (H(λ) − ε)·Σ_{q,χ} N(χ; T, 2T)`, and `→ 2/3` (Montgomery–Taylor: 0.6725) as
  `λ → 1⁻`, uniformly in the `q`-aspect.
- Skeleton:
  1. Per `χ`, seam: `N₀*(χ) ≥ 4tr Ĝ_χ − ‖Ĝ_χ‖² − 2N_χ − E_χ` (Zeta23 `seamA` for `L(s,χ)`, pair-neutral, exact up to
     Poisson, tails and `NII`). The zero-side trace is `N_χ(1 + O(w/L))` by Poisson, with no prime side needed.
  2. `Gz_χ = Gp_χ + Err_χ` (explicit formula for `L(s,χ)` with test `φ̂(·−τ_k)φ̂(·−τ_l)`; errors from zeros outside the
     window, `O(log qT)` local counts uniform in `q`).
  3. `Σ_χ‖Gp_χ‖²`: expand `Gp_χ = Γ_χ − Π_χ`. Then `Σ_χ⟨Γ_χ, Π_χ⟩` only sees `n ≡ 1 (mod q)`, so it is `≪ √X/Q`.
     `Σ_χ‖Π_χ‖²` uses orthogonality `Σ*_χ χ(n)χ̄(m)` and the grid kernel `Ŵ(T log(n/m))`. Off-diagonal needs `q | (n−m)`
     with `|n−m| ≤ X/T ≤ Q`, and only small `q` survive. So small moduli need care: restrict to `q ∈ [Q/2, Q]`, or keep
     `X/T < Q/2` so `kq` with `k ≠ 0` is impossible.
  4. Diagonal: `Σ_n Λ(n)²/n·g(log n)` per character, giving `(1/λ + λ/3)N` (flat) exactly as for ζ.
  5. Average and conclude.
- [OPEN CORE] for the lower half: only the uniform-in-`q` error bookkeeping of steps 1–2 (Zeta23 ThmE constants are
  `q`-dependent) and the small-moduli restriction in step 3. No new analytic input.
- Expected novelty (internal): a family average of 2/3 to 0.6725 uniformly in the conductor, against 56% for
  Levinson-type methods. The upper half (`λ > 1`) remains as in cycles 60–61.

## Cycle 68 — q-dependence of Theorem E's error terms (corpus inventory)
- `RiemannVonMangoldtChi.main`: `|N(T,2T;χ) − (T/2π)ℓ_{1,χ}| ≤ C log T` for `T ≥ T₀(q)`. The uniform classical version is
  `≤ C log(qT)` for `T ≥ 2`, `C` absolute. ✓
- `local_count`: `N(t,t+1) ≤ A₀ log(|t|+3)`. Uniform: `≤ A₀ log(q(|t|+3))`. ✓
- `GammaFactsChi`: `μ_χ(τ) = (1/2π)log(q|τ|/2π) + O(τ^{−2})`, uniform in `q`. ✓
- `NIIChi`: `O(√T·log(qT)) = o(N)`. ✓
- Tails (`tailPackageChi`): `θ₀ ≤ C·l·T^{λ/2−1}`, from `e^{L/4}`-scaled `φ̂` decay at window margin `√T`. With
  `L = λ log(QT)` this is `≍ (QT)^{λ/2}T^{−1}log(qT)`, so `o(1)` iff `Q ≤ T^{(2−λ)/λ − ε}`, i.e. `Q ≤ T^{1−ε}` at `λ → 1`. With
  the `C³` taper (`|φ̂(x)| ≲ e^{L/2}(w|x|)^{−3}`) and margin `√T`, the bound improves to `Q ≤ T^{(3−λ)/λ}`; a wider margin
  or smoother taper allows any fixed power `Q ≤ T^A`.
- Family Frobenius at `λ < 1`, dyadic `q ∈ [Q/2, Q]`: off-diagonal needs `kq` with `k ≠ 0` and `|kq| ≤ X/T = Q^λT^{λ−1} < Q/2`,
  impossible. So diagonal only. ✓
- **Conclusion:** F57b-low holds on paper for `T^ε ≤ Q ≤ T^{1−ε}` (Zeta23's parameters) and plausibly for `Q ≤ T^A`
  (retuned taper/margin): family average `≥ H(λ) − ε`, so `2/3` (Montgomery–Taylor 0.6725), uniformly in the conductor.
  Remaining work is bookkeeping only. Formalising it would mean re-proving ThmE's `∃C` hypotheses with explicit
  `q`-uniform constants. Large but routine.

## Cycle 69 — amplifying the family toward ζ (paper)
- Weight the family certificates by `A(χ) = |Σ_{ℓ≤ℓ₀}x_ℓχ(ℓ)|²`. Then `A(χ₀) ≍ ℓ₀²` and the typical `A(χ) ≍ ℓ₀`. For ζ (via `χ₀`) to dominate
  the weighted average, `ℓ₀² ≳ #F·ℓ₀`, i.e. `ℓ₀ ≳ #F ≍ Q²`.
- The weighted Frobenius is a family mean square of the product polynomial (length `ℓ₀X`). The large sieve is
  diagonal-dominant only for `ℓ₀X ≲ Q²T`, and with `ℓ₀ ≍ Q²` this means `X ≲ T`, i.e. `λ ≤ 1` for ζ.
- Verdict: BLOCKED. Amplification spends exactly the `Q²` family gain on isolating ζ. This is the standard
  amplifier/large-sieve trade-off, here pinned to the Nyquist barrier.

## Cycle 70 — F57b-low: dependency-closed proof plan (paper)
Notation: `F_Q = {χ primitive mod q, Q/2 < q ≤ Q}`, `T^ε ≤ Q ≤ T^{1−ε}`, `L = λ log(QT/2π)` (`0 < λ < 1`), flat profile
with `C³` taper of width `w`, grid `τ_k = T + 2πk/L`, `0 ≤ k < d = ⌊LT/2π⌋`.
- **L1 (per-χ seam).** For each `χ ∈ F_Q`:
  `N₀*(χ;T,2T) ≥ 4tr Ĝ_χ − ‖Ĝ_χ‖_F² − 2N(χ;T,2T) − 3N_χ(I′∖I) − B_χ(4 + 2‖Ĝ_χ‖_F + B_χ)`.
  Source: `Zeta23.Assembly.seamA` (pure linear algebra plus `ZeroSide`), applied to `LZeros χ`. It needs only
  `PhiHatConj` and `PoissonSq`, both `χ`-free, so it is uniform.
- **L2 (uniform local counts).** `N(χ; t, t+1) ≤ A₀ log(q(|t|+3))` with `A₀` absolute. Source: Jensen on a disc with the
  convexity bound for `L(s,χ)`. The corpus has the `ζ` version (`XiWindowZeroCount`); it needs the `χ` port.
- **L3 (uniform tails).** From L2 and the `C³` taper: `B_χ ≤ C log(QT)·(QT)^{λ/2}T^{−1}`, which is `o(1)`, so
  `Σ_χ B_χ‖Ĝ_χ‖ = o(Σ_χ N_χ)`. Source: `Zeta23.Tail` with `l` replaced by `log(QT)`.
- **L4 (uniform RvM).** `N(χ;T,2T) = (T/2π)ℓ_{1,χ} + O(log qT)`, and `N_χ(I′∖I) = O(√T log qT)`.
- **L5 (zero-side trace).** `tr Ĝ_χ = N_on(χ) + 2p_χ + O(…) = N_χ(1 + O(w/L))` by Poisson (`ZeroSide.rtrace_hatP_le`
  and its equality form). Uniform.
- **L6 (explicit formula for `χ`, matrix form).** `Gz_χ = Gp_χ + E_χ` with `‖E_χ‖_F = o(N_χ^{1/2}·…)`.
  Source: `ThmE.GzGpChi`, with constants tracked in `q`.
- **L7 (family Frobenius).** `Σ_{χ∈F_Q}‖Ĝp_χ‖_F² = (1/λ + λ/3 + o(1))Σ_χ N_χ`. Proof: expand `Ĝp_χ = Γ_χ − Π_χ`. Then
  `Σ_χΠ_χ(k,l)Π̄_χ(k,l)` uses `Σ*_χ χ(n)χ̄(m)`; for `n ≠ m` this needs `q | n−m` with `|n−m| ≤ X/T < Q/2 < q`, which is
  impossible. Diagonal: Montgomery–Vaughan as in `Zeta23.PrimeSideB` (the `PP` term). Cross term
  `Σ_χ⟨Γ_χ,Π_χ⟩ ≪ #F_Q·√X·L/Q`.
- **L8 (assembly).** Sum L1 over `F_Q`, insert L5, L7 and L3–L4, and use Cauchy–Schwarz on `Σ_χ‖Ĝ_χ‖`. This gives
  `Σ N₀* ≥ (H(λ) − o(1))Σ N`.
- Status: L1, L5 are in the corpus (uniform as stated). L2–L4 and L6 are classical uniform estimates; ports needed. L7 is
  new but elementary (orthogonality plus the existing diagonal analysis).

## Cycle 71 — L7 (family Frobenius) worked out (paper)
- Poisson on the grid: `Σ_kφ̂(τ−τ_k)φ̂(τ'−τ_k) ≈ (L/2π)Φ(τ−τ')`, with `Φ = FT(φ²)`. So
  `‖Gp_χ‖_F² ≈ (L/2π)²∬Φ(τ−τ')²ν_χ(τ)ν_χ(τ')`, with `ν_χ = μ_χ + Π_χ (+P_χ)`.
- `Π_χΠ_χ` terms: only conjugate pairs `χ(n)χ̄(m)(n/m)^{iτ}` survive the `τ`-integration (unconjugated
  `χ(nm)(nm)^{iτ}` has no stationary point, since `nm ≥ 4`). Primitive orthogonality for `(nm,q) = 1`:
  `Σ*_χχ(n)χ̄(m) = Σ_{d|q, d|n−m}μ(q/d)φ(d)`.
  - `d = q` would need `q | n−m` with `0 < |n−m| ≤ X/T < q`, so it contributes nothing.
  - `d < q`: weight `≤ φ(d)` against the diagonal weight `φ*(q) ≍ q`. The pair count with `d | n−m`, `|n−m| ≤ X/T` is
    `≍ X²/(Td)`. Relative to the diagonal this is `≪ τ(q)·X/(Tq) = Q^{λ−1+ε}T^{λ−1} → 0` for `λ < 1`.
  - Diagonal `n = m`: `|χ(n)|² = 1_{(n,q)=1}`, i.e. Zeta23's `MPP` term up to primes dividing `q`.
- `μ_χΠ_χ` cross terms: `Σ*_χχ(n)` is large only for `n ≡ 1 (mod q)`, and `∫_T^{2T}cos(τ log n)dτ = O(1/log n)`, so they
  are negligible. `μ_χμ_χ`: the Γ-density `(1/2π)log(q|τ|/2π)` matches `N_χ`.
- **Result:** `Σ_{χ∈F_Q}‖Ĝp_χ‖_F² = (1/λ + λ/3 + o(1))·Σ_χN_χ` for `λ < 1`, `T^ε ≤ Q ≤ T^{1−ε}`. L7 holds on paper.
- F57b-low is now dependency-closed on paper **modulo the classical uniform estimates L2–L4, L6** (local count, tails,
  RvM, and the explicit-formula matrix bound, all with `log(qT)` errors). Next, per the no-go closure discipline: port
  those and formalise. This is a family theorem (Dirichlet L-functions), not the ζ target.

## Cycle 72 — F57b-low Lean foundations: corpus gap and build plan
- Corpus gap, confirmed by `research`: every Dirichlet-L zero-count module (`DirichletLZeroDensityBox`, `…Family`, `…Range`,
  `…Primitive`, and Zeta23 `ThmE.localCountChi`) has constants **depending on the character**. Each says explicitly
  "not a conductor-uniform … theorem". `ThmE.localCountChi` rests on `LFunction_growth_right` (`∃A C`, `χ`-dependent).
- Mathlib assets (checked in `/tmp/g75`):
  - `DirichletCharacter.IsPrimitive.completedLFunction_one_sub`: `Λ(1−s,χ) = N^{s−½}·ε(χ)·Λ(s,χ⁻¹)`;
  - `LFunction_eq_completed_div_gammaFactor`;
  - `gammaFactor` (`Gammaℝ s` or `Gammaℝ (s+1)` by parity);
  - `rootNumber` (Gauss-sum based);
  - `PhragmenLindelof.vertical_strip`;
  - `differentiable_LFunction`.
- Build plan (`RHTower/DirichletLUniformConvexity.lean`):
  1. `‖rootNumber χ‖ = 1` for primitive `χ` (Gauss-sum norm `√N`; search the corpus first).
  2. A uniform Γ-ratio bound `‖gammaFactor χ (1−s)/gammaFactor χ s‖ ≤ C(|t|+3)^{½−σ}` on `σ ∈ [−½, 0]` (Stirling; Zeta23
     `Analytic/Stirling`).
  3. Left edge: `‖L(−δ+it,χ)‖ ≤ C·N^{½+δ}(|t|+3)^{½+δ}ζ(1+δ)`. Right edge: `‖L(1+δ+it,χ)‖ ≤ ζ(1+δ)`.
  4. Phragmén–Lindelöf on `[−δ, 1+δ]` for `L(s,χ)·(N(s+3))^{−(½+δ)(1+δ−s)/(1+2δ)}`-type normalisation (a priori growth from
     `LFunction_growth_right`), giving the uniform convexity bound `‖L(σ+it,χ)‖ ≤ C_δ(N(|t|+3))^{(1+δ−σ)/2+δ}`.
  5. Uniform local count `N(χ; t, t+1) ≤ A₀ log(N(|t|+3))` (port of `ThmE.localCountChi` with `B` depending on `N`).
- This foundation is reusable for any conductor-uniform family statement. It is not on the ζ path.
- Cycle 72 addendum (corpus): the Chen–Gupta–Li lane already has
  - `cglLemma62_primitive_rootNumber_norm_one` (`‖ε(χ)‖ = 1`, built to make CGL's far-left estimate uniform in the
    character);
  - `exists_bound_LFunction_left_edge` (`Re w = −2`, constant `∝ N^{5/2}·C`);
  - `cglLemma62_exists_bound_inducedLFunction_strip` (cubic envelope on `[−1, 2]`, `∃E`, character-dependent);
  - a full character-Gram / large-values toolkit (`ChenGuptaLiCharacterGram*`, `…Orthogonality`,
    `…PacketSecondMoment/OffDiagonal/FourthMoment`).
  So step 1 of the plan exists. Steps 2–4 (uniform Γ-ratio, edges, Phragmén–Lindelöf) remain, and the character-Gram
  toolkit is the natural home for L7 (family Frobenius) and possibly the F57b upper half.

## Cycle 73 — F57b foundation, first brick (Lean, built)
- Found in Zeta23: `ThmE.LFunction_growth_right_uniform`, `‖L(s,χ)‖ ≤ 8q(|Im s| + 3)` for `Re s ≥ 0.15`, with absolute
  constants. So the uniform convexity plan of cycle 72 was not needed for the local count.
- **Lean [built, wired after `Zeta23TheoremASpectralSlack`, axioms `[propext, Classical.choice, Quot.sound]`, no
  heartbeat options, no lint findings]:** `RHTower/DirichletLUniformLocalCount.lean`:
  - `log_uniform_disc_bound`;
  - `norm_gfunL_le_uniform`;
  - `uniform_localCount`: for `q > 1`, primitive `χ`, every `t`,
    `N_χ(t,t+1] ≤ 2(log 24 + 2)/log(0.95/0.84) · log(q(|t|+3))`;
  - `exists_uniform_localCount`: one absolute `A₀` for all `q`, `χ`, `t`.
  This is the conductor-uniform local count that every corpus Dirichlet zero-count module lacked (L2 of the F57b-low
  plan).
- Next F57b-low bricks: uniform tails (L3) and uniform RvM (L4).

## Cycle 74 — uniform boundary count (Lean, built) and the Params obstacle
- **Lean [built, axioms standard, no lint findings]:** `DirichletLUniformLocalCount.lean` adds
  - `one_le_uniformLocalCountConst`;
  - `uniform_localCount_log` (`N_χ(t,t+1] ≤ A₀(1 + log q)log(|t|+3)`, the form consumed by `Zeta23.Tail`);
  - `uniform_NII_le` (`T ≥ 300 ⇒ NII ≤ 3A₀(1 + log q)√T log 4T`), through `Tail.NII_le` with explicit thresholds.
  So L4's boundary part is uniform.
- **Obstacle for L3 (tails) and the seam:** `Zeta23.Params` fixes `L = lam·log(T/2π)`, and `Params.Valid` requires
  `lam ≤ 1`. The family frame needs `L = λ log(QT)`, i.e. `lam = λ(1+κ)` for `Q = T^κ`, which can exceed 1. `Tail.theta0_le`
  itself never uses `lam ≤ 1` (grep: no `lam_le_one` in `Tail.lean`), but it takes `hP : P.Valid`. Next step: a
  `ValidFamily` variant with `lam < 2`, and re-export the tail and seam lemmas under it, copied with weakened
  hypotheses into `RHTower`. The prime-side lemmas that use `X ≤ T` are replaced by family orthogonality (L7).

## Cycle 75 — where `lam ≤ 1` is actually used in Zeta23 (corpus audit)
- `Tail.theta0_le` uses only `hP.lam_pos`. `Tail.eventually_tailInputs` uses `P.Valid` only through `tendsto_L_atTop`
  (`lam_pos`) and the taper decay. `eventually_poissonSq` uses the taper and `w`. `ZeroSide`, `ThmE/GzGpChi` and the seam
  `seamA` (no `Valid` argument) never use `lam ≤ 1`.
- `lam ≤ 1` enters only through `Assembly.X_le_T` (used by `calE_tendsto_zero`, the prime-side trace error rate
  `(l² + X)log l/(T l)`) and the prime-side trace files (`PrimeSideB`, `ThmE/TracesChi`), which the family argument replaces
  by L7.
- **Formalisation plan for F57b-low, confirmed feasible:**
  (i) `ParamsValidFamily := taper ∧ 0 < lam ∧ 1 ≤ w`, no upper bound on `lam`;
  (ii) re-export the tail package and Poisson under it (copy `Tail.lean`'s top-level lemmas with the weakened hypothesis;
  Apache-2.0 attribution);
  (iii) per-χ seam: reuse `seamA` / `seamA_spectralSlack` verbatim;
  (iv) L7: family Frobenius via primitive orthogonality (new module);
  (v) assembly with the uniform counts of cycles 73–74.
- No mathematical obstacles remain for F57b-low. The rest is engineering.

## Cycle 76 — family bandwidth inputs (Lean, built)
- **Lean [built, wired after `DirichletLUniformLocalCount`, axioms standard, no lint findings]:**
  `RHTower/Zeta23FamilyBandwidth.lean`:
  - `ParamsValidFam` (taper, `λ > 0`, `w ≥ 1`; **no `λ ≤ 1`**);
  - `half_le_a_fam`, `C1_le_fam`, `norm_phiHat_sub_I_mul_le_fam`;
  - `poissonSq_fam` (`ZeroSide.PoissonSq` at any bandwidth);
  - `tailInputs_fam` (`Assembly.TailInputs` for `T ≥ 300`, `2 ≤ L`, `8w ≤ L`, any configuration with unit-window counts
    `≤ A₀ log(|t|+3)`);
  - `theta0_le_fam`.
  All come from Zeta23's `L`-generic `Taper` lemmas, so nothing was copied except `theta0_le`'s short calculation.
- With `uniform_localCount_log` (cycle 74) these give **per-χ tail inputs for the family**, with constant
  `A₀(1 + log q)` and explicit thresholds, at bandwidth `λ(1+κ) > 1`. The per-χ seam `seamA_spectralSlack` needs only
  `PoissonSq`, `TailInputs`, `a > 0` and `L > 0`, so it is now available at family bandwidths.
- Remaining F57b-low pieces: L6 (explicit-formula matrix identity `Gz = Gp + E` for `χ` at family bandwidth; check
  `ThmE.GzGpChi` for `λ ≤ 1` use), L7 (family Frobenius), and the assembly.

## Cycle 77 — L6 at family bandwidth is free; L7 is the remaining analytic core (corpus audit)
- `ZeroConfig.Gz_eq_GpChi` needs only the χ explicit formula (`EF_lit_chi_L`, unconditional in `ThmE/Final`), `L > 0`,
  `φ ∈ C²` and `supp φ ⊆ [−L/2, L/2]`. The last two come from generic `Taper` lemmas, so there is no `λ ≤ 1`.
  **So `Gz_χ = Gp_χ` holds exactly at family bandwidths**: L6 is done (as an exact identity; tails are in `TailInputs`).
- The per-χ seam (`seamA_spectralSlack`) now has all inputs at family bandwidth: Poisson, tails (cycle 76), uniform counts
  (cycles 73–74), `Gz = Gp`.
- **Remaining core: L7, the family Frobenius** `Σ_{χ∈F_Q}‖hat(Gp_χ)‖_F²`. This is Zeta23's prime-side Frobenius analysis
  (`PrimeSideB`: `MPP` diagonal, `cross_*`, `MPiPi ≪ LX/T`) redone with an outer character sum. Primitive orthogonality turns
  `MPiPi` into `≪ (LX/T)·τ(q)/q` per character, and this is `o(N)` exactly when `X/T < Q`, i.e. `λ < 1` in family units. The
  trace can come from the zero side (Poisson, minus boundary zeros through `uniform_NII_le`).
- Size estimate of the remaining work: a family version of `PrimeSideB` (diagonal plus four cross terms with character
  sums) plus the assembly. Long, but each step mirrors existing Zeta23 code.

## Cycle 78 — L7 simplified: a single prime modulus suffices (paper + corpus)
- Take the family `F_q = {χ ≠ χ₀ mod q}` for **one prime** `q` (all nonprincipal characters are primitive). Orthogonality
  is exact: `Σ_{χ mod q} χ(n)χ̄(m) = φ(q)·1_{n≡m (q), q∤nm}`. The principal character contributes `ζ·(1 − q^{−s})` with
  weight `1/φ(q)`, which is negligible or can be excluded.
- Then `Σ_χ∫|Σ_n a_nχ(n)n^{−it}|² = φ(q)Σ_{a mod q}∫|Σ_{n≡a}a_n n^{−it}|²`. Within a residue class the frequencies
  `log n` are spaced by `≥ q/n`, so Montgomery–Vaughan (Zeta23 `MV.Final.mv_hilbert`, arbitrary frequencies and spacings,
  unconditional) gives `= φ(q)Σ_n(T + O(n/q))|a_n|²`. The relative off-diagonal error is `X/(qT) → 0` iff `λ < 1` in units
  of the conductor `qT`.
- So L7 for `F_q` is Zeta23's prime-side Frobenius analysis (`PrimeSideB` facts `MPP`, `cross_*`, `MPiPi`) with the MV step
  replaced by "MV per residue class". There is no pole term (`Π_X`) for nonprincipal `χ`, and `μ_χ` is the `χ`-Γ density.
- **F57b-low, sharpened:** for prime `q ≤ T^{1−ε}`, `avg_{χ≠χ₀ mod q} N₀*(χ;T,2T) ≥ (H(λ_q) − ε)avg N(χ;T,2T)`, with
  `λ_q = λ log(qT)/log T` allowed up to `log(qT)/log T`. The family reaches `2/3` (0.6725) uniformly, where single-`χ`
  Theorem E gives `H(1/(1+κ))`.

## Cycle 79 — design of the family PP term (paper + corpus)
- For a nonprincipal `χ` the prime density is `P_χ(τ) = −(1/π)Re Σ_{n≤X}Λ(n)n^{−½}χ(n)n^{−iτ}`. Summing over all `χ mod q`:
  `Σ_χ P_χ(τ)P_χ(τ') = (φ(q)/2π²)Σ_{n≡m (q), q∤nm}(ΛΛ/√(nm))cos(τ log n − τ' log m) + (φ(q)/2π²)Σ_{nm≡1 (q)}(…)`.
  Subtract the principal character, which has weight `1/φ(q)` relative to the family.
- So the family PP term is Zeta23's `PrimeSideB/PP` bilinear form restricted to `n ≡ m (mod q)` (plus the `nm ≡ 1` part,
  which has no stationary phase on `[T, 2T]`). The diagonal `n = m` is literally Zeta23's `MPP`. The off-diagonal
  (`PPOffDiag.O1_bound`, through `PPKernel.MV_primeRange` and `MVHilbert`) gets spacing `|log n − log m| ≥ q/max(n,m)` in place of
  `1/max(n,m)`, which gains the factor `1/q`: off-diagonal `≪ L²X/q` against main `≍ T L³`, so `o` once `X ≤ qT^{1−ε}`.
- Formalisation route: generalise `PPKernel.MV_primeRange` and `PPOffDiag.O1_bound` to coefficient families supported on a
  residue class (spacing parameter `q`). Then the family `MPP` follows from the ζ proof with `q` threaded through.
  Mechanical; about 10³ lines mirroring `PrimeSideB/PP*`.

## Cycle 80 — Montgomery–Vaughan on a residue class (Lean, built)
- **Lean [built, wired after `Zeta23FamilyBandwidth`, axioms standard, no lint findings]:** `RHTower/MVResidueClass.lean`:
  - `spacing_log_of_modEq`: distinct positive `n ≡ m (mod q)` satisfy `q/(n+q) ≤ |log n − log m|`;
  - `mv_residueClass`: for `S` pairwise congruent mod `q`,
    `‖Σ_{n≠m} x_n z̄_m/(log n − log m)‖ ≤ C(Σ‖x_n‖²(n+q)/q)^{1/2}(Σ‖z_n‖²(n+q)/q)^{1/2}`, from Zeta23's proved
    `MVHilbert`.
  The weight `(n+q)/q` replaces `2n`: the factor-`q` gain that makes character averages of length `≤ qT^{1−ε}`
  diagonal.
- Next: thread this into a family version of `PPKernel.MV_real` / `PPOffDiag.O1_bound` (residue-class split of the
  prime-power range), then the family `MPP`.
- Cycle 81: `mv_real_residueClass` (cosine and sine forms with a common phase on a residue class) added to
  `MVResidueClass.lean`. Built; axioms standard. This mirrors `PPKernel.MV_real` with weights `(n+q)/q`.

## Cycle 82 — family mean square of the prime polynomials (Lean, built)
- **Lean [built, wired after `MVResidueClass`, axioms standard, no lint findings]:**
  `RHTower/DirichletFamilyPrimeMeanSquare.lean` (897 lines):
  - `sum_dirichletChar_mul_conj`, `sum_dirichletChar_mul`: `Σ_χ χ(a)χ̄(b) = φ(q)[b unit, a = b]`, `Σ_χ χ(a)χ(b) = φ(q)[ab = 1]`;
  - `integral_square_cos_sub/add`: `∬_{[T,2T]²}Φ(τ−τ')²cos(τy ∓ τ'y') = A^∓(y,y')`;
  - `sum_PXc_mul_PXc_dirichlet` (pointwise) and `sum_Mform_PXc_dirichlet` (exact):
    `Σ_χ 𝓜[P_χ,P_χ] = φ(q)/(2π²)·(Σ_{n≡m,(m,q)=1} a_n a_m A⁻ + Σ_{nm≡1} a_n a_m A⁺)`;
  - `offDiag_Aminus_le_of_mvReal` (8-sum split on any MV-spaced set), `sum_sameUnitClass_eq_sum_classes`,
    `offDiag_residueClass_bound`: off-diagonal `≤ 8C(∫Φ²)Σ_{n≤X} a_n²(n+q)/q`;
  - `sum_inverseClass_eq_sum_classes`, `sum_inv_add_le_of_residueClass` (`Σ_{n≡r} 1/(n+q) ≤ (1+log(⌊X⌋+1))/q`),
    `sq_classSum_acoef_le`, `sum_inverseClass_acoef_le` (pairing `r ↔ r⁻¹` + AM-GM), `sumFreq_inverseClass_bound`;
  - `sum_Mform_PXc_dirichlet_sub_diag_le`: `|Σ_χ 𝓜[P_χ,P_χ] − φ(q)/(2π²)Σ_{(n,q)=1} a_n² A⁻(y_n,y_n)|
    ≤ φ(q)/(2π²)·(∫Φ²)/q·(8C+2+2log(⌊X⌋+1))·Σ_{n≤X} a_n²(n+q)`.
- Size: `Σ a_n²(n+q) = ΣΛ² + qΣΛ²/n ≍ XL + qL²`, so the error is `≪ φ(q)·L²(XL/q + L²)` against the main term
  `φ(q)·TL³/(6π)`: negligible for `X ≤ qT^{1−ε}`. This is L7's PP component for `F57b-low`.
- Verdict on novelty: REDISCOVERED (hybrid mean value theorem for characters, Montgomery/Gallagher). The formal
  content is new infrastructure; it is not new mathematics.
- Still open for `F57b-low`: family diagonal (from `abs_Aminus_diag_sub_le`), family `lem_ends` (per-χ error is
  linear in `X` — needs the averaged pointwise bound `Σ_χ P_χ(τ)² ≤ (φ(q)/π²)Σ_r(Σ_{n≡r}a_n)²`, which
  `sq_classSum_acoef_le` already controls), family cross term `𝓜[μ_χ,P_χ]` (linear in χ: orthogonality kills it),
  Cauchy–Schwarz over χ for the rank–trace, then assembly.
- ζ goal: unchanged. 75% for ζ still requires the beyond-RH prime-pair input (cycles 1–72).

## Cycle 83 — all-moduli family re-examined; family end effects (paper + Lean, built)
- **Conjecture F57c (refinement of F57b-upper):** for `T = Q^{o(1)}`, `T → ∞`, the average over `q ∈ (Q,2Q]` and
  primitive `χ mod q` of the on-line proportion in `[T,2T]` is `≥ 1 − 1/(3λ²) − ε` for every `λ < 2` (`→ 11/12`), with
  Bombieri–Vinogradov/Siegel–Walfisz as the only arithmetic input. Mechanism: primitive orthogonality
  `Σ*_χ χ(n)χ̄(m) = Σ_{d|(q,n−m)} μ(q/d)φ(d)`; write `q = de`; the Möbius sum over `e ~ Q/d` concentrates the
  off-diagonal on `d ≍ Q/e`, `e` small; then `n − m = dk`, `k ≲ eX/(QT)`, and switching to `m ≡ n (mod k)` needs `Λ` in
  progressions to moduli `k f ≤ Q^θ F` (truncating `φ(d)/d = Σ_{f|d}μ(f)/f` at `f ≤ F`, error `O(1/F)`), inside the
  BV range when `θ < 1`.
- Kill attempt: REDISCOVERED internally (cycles 57–61: same programme; the log had MRT-type averaged
  Hardy–Littlewood as the input). The refinement "BV suffices when `T = Q^{o(1)}`" is new to the log; status
  SURVIVES (sketch). [OPEN CORE] (a) the exact main-term identity `F_fam(α) = 1` on `(1, 2)`; (b) Siegel–Walfisz and
  Bombieri–Vinogradov are absent from the corpus (exhaustive `rg`); (c) conductor-uniform Theorem E.
- Not ζ: ζ remains blocked by the variance/pair-correlation input (any gain over 0.6725 via bandwidth needs
  `∫_1^{1+δ}F < δ/3`-type control, i.e. variance of primes in intervals `X^δ` beyond Selberg's RH bound).
- **Lean [built, wired after `DirichletFamilyPrimeMeanSquare`, axioms standard, no lint findings]:**
  - `RHTower/DirichletFamilyBilinearForms.lean` (411 lines): `sum_dirichletChar_re_mul_re` etc.;
    `trigPoly`, `IsTrigBilin`, `IsTrigLinear`; `sum_bilin_PXc_dirichlet`: for any form bilinear on trigonometric
    polynomials, `Σ_χ β(P_χ,P_χ) = φ(q)/(2π²) Σ_{r unit}(β(C_r,C_r) + β(S_r,S_r) + β(C_r,C_{r⁻¹}) − β(S_r,S_{r⁻¹}))`;
    closure (`add/sub/const_mul/sum/mul`), `isTrigBilin_Mform`, polarisation.
  - `RHTower/DirichletFamilyEndEffects.lean` (544 lines): `endForm` (`L⁻²ΣG(u)G(v) − 𝓜[u,v]`), linearity,
    `isTrigBilin_endForm`, `endForm_add_add/sub_sub` (with the archimedean density), and
    `abs_sum_endForm_dirichlet_le`: `|Σ_χ E(μ+P_χ, μ+P_χ)| ≤ C L l log l · φ(q) · (B_μ² + (B_μ+A₁)²
    + (2π²)⁻¹Σ_r(2(l+A_r)² + (l+A_r+A_{r⁻¹})²))`, from Zeta23's single-density `lem_ends_nu_W` (valid for `L ≤ 2l`).
  - Size: `Σ_r A_r² ≤ (1+log X)/q · Σ a_n²(n+q) ≍ L²X/q + L³` (cycle 82's `sq_classSum_acoef_le`), so the family
    end error is `≪ φ(q)·L l log l·(l²φ(q) + L²X/q + L³)` against main `φ(q)TL³`: negligible for `q ≤ T^{1−ε}`,
    `X ≤ qT^{1−ε}`.
- Remaining for F57b-low: family trace (linear; per-χ error `L√X` already fine), cross term `𝓜[μ,P]` family form,
  conductor-uniform constants (Γ-facts, Chebyshev coprime, per-χ seam), Cauchy–Schwarz over χ, assembly.

## Cycle 84 — ζ structural question re-checked; F57c critical path = Siegel–Walfisz (paper + Lean brick 1)
- **ζ, bandwidth just above 1.** With the flat certificate `m₂(λ) = (1/λ)(2 − 2/(3λ)) + (2/λ)∫_1^λ(1−α/λ)F`, the
  base part drops by `(2/3)δ` at `λ = 1+δ`, while the `F` part is `≤ (2δ/λ²)∫_1^{1+δ}F`. A gain needs
  `∫_1^{1+δ}F < 1/3` (pointwise `F ≤ C` would make it `O(δ²)`). Unit-interval averages (`∫_β^{β+1}F ≪ 1` under RH)
  cannot exclude a mass `≈ 1` near `1⁺`; sieve upper bounds `ΛΛ(n+h) ≤ 4𝔖(h)X` exclude it only for
  `δ ≪ log log T/log T`. Verdict for "small-δ gain without variance": FALSE as a route (no unconditional input
  bounds `F` on `(1, 1+δ]` for fixed `δ`). Positive survivor: the spike-exclusion window `δ_T ≍ log log T/log T`
  (sieve), INSIGNIFICANT (gain → 0).
- **F57c error structure (paper).** After switching to `k = (n−m)/d`, the error is a bilinear form in `Λ ⊗ Λ`
  over characters `ψ mod kf` (with `φ(d)/d = Σ_{f|d}μ(f)/f` truncated at `F`), and the coupling `(n/m)^{iτ}`,
  `Ψ((n−m)e/(kQ))` separates through `n^{iτ}m^{−iτ}` and a Fourier integral in additive frequency. So:
  conductors in `(log^B X, Q^θF]` are handled by the hybrid multiplicative large sieve (no Vaughan identity
  needed: both factors are `Λ`-sums), and conductors `≤ log^B X` by Siegel–Walfisz. A Siegel zero would
  enter with sign `+μ(1)|A_ψ₁|²` (wrong direction), so Siegel's theorem is unavoidable.
- **Critical path for any family ≥ 3/4 theorem:** Siegel (`L(1,χ) ≫_ε q^{−ε}`) → zero-free region for `L(s,χ)`
  uniform in `q` with at most one exceptional zero → explicit formula for `ψ(x,χ)` → Siegel–Walfisz →
  hybrid multiplicative large sieve → family main term (`F_fam = 1` on `(1,2)`) → conductor-uniform Theorem E →
  assembly.
- **Lean brick 1 [built, wired after `DirichletFamilyEndEffects`, axioms standard, no lint findings]:**
  `RHTower/SiegelProductCoefficients.lean`: `siegelCoeff χ₁ χ₂ = (1⋆χ₁) ⋆ (χ₂·(1⋆χ₁))`
  (`charTwist_zetaMul`: `= ζ⋆χ₁⋆χ₂⋆χ₁χ₂`), `siegelCoeff_comm`, `isMultiplicative_siegelCoeff`,
  `siegelCoeff_prime_pow`, and `siegelCoeff_nonneg`: for quadratic `χ₁, χ₂` all coefficients of
  `ζ(s)L(s,χ₁)L(s,χ₂)L(s,χ₁χ₂)` are `≥ 0` (case split per prime, swapping the two characters when
  `χ₂(p) = −1 ≠ χ₁(p)`).
- Next bricks: (2) `LSeries siegelCoeff = ζ·L·L·L` for `Re s > 1` and the entire part `F − λ/(s−1)`;
  (3) Goldfeld's inequality `F(σ) ≥ 1/2 − λ(M+2λ)^{c(1−σ)}/(1−σ)` from nonneg Taylor coefficients at `s = 2`
  (Mathlib `LSeries.iteratedDeriv_alternating`, Cauchy estimates); (4) growth `M ≪ (q₁q₂)^C` on `|s−2| = 3/2`
  (Zeta23 `LFunction_growth_right_uniform`); (5) `L(1,χ) ≪ log q`; (6) Siegel's theorem.

## Cycle 85 — Siegel bricks 2–3 (Lean, built)
- **`RHTower/SiegelGoldfeldInequality.lean`** [built, wired, axioms standard]: for `F = Σ a_n n^{−s}` with `a ≥ 0`,
  `a_1 = 1`, abscissa `≤ 1`, `F = G + λ/(s−1)` (`G` entire, `λ ≥ 0`), `|G| ≤ M` on `|s−2| = 3/2`:
  `goldfeld_lower_bound`: `Re G(σ) − λ/(1−σ) ≥ 1/2 − 2λ(2−σ)^K/(1−σ)` whenever `4M(3/4)^K ≤ 1/2`, `K ≥ 1`;
  `goldfeld_lower_bound'`: `≥ 1/2 − 2eλ(8M+8)^{4(1−σ)}/(1−σ)` for `7/8 ≤ σ < 1`.
  Proof: Taylor at 2 (`hasSum_taylorSeries_of_entire`), coefficients `(−1)^m(β_m − λ)` with
  `β_m = (−1)^m F^{(m)}(2)/m! ≥ 0` (`LSeries.iteratedDeriv_alternating`), `β_0 ≥ 1`, Cauchy estimate
  `|β_m − λ| ≤ M(2/3)^m` (`norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le`).
- **`RHTower/SiegelProductLFunction.lean`** [built, wired, axioms standard]: `productChar χ₁ χ₂` (mod `N₁N₂`,
  `productChar_apply`), `LSeries_siegelCoeff` (`= ζ L(χ₁) L(χ₂) L(χ₁χ₂)` for `Re s > 1`), entire part
  `siegelG = dslope ((s−1)ζ·L·L·L) 1` (`differentiable_siegelG`), `siegelRes_nonneg` (residue `λ ≥ 0` real, as a
  limit of `(σ−1)F(σ) ≥ 0`), `exists_norm_siegelG_le` (`|G| ≤ C₀(N₁N₂)²` on the circle, absolute `C₀`, from
  Zeta23's `LFunction_growth_right_uniform` and compactness for `(s−1)ζ(s)`), and
  `siegel_goldfeld_bound`: `Re F(σ) ≥ 1/2 − 2eλ(8C₀(N₁N₂)²+8)^{4(1−σ)}/(1−σ)` for `7/8 ≤ σ < 1`.
- Remaining for Siegel's theorem: (5) `|L(1,ψ)| ≤ log q + 2` (partial summation) — the crude `24q` loses `N¹`;
  (6) real-valuedness of `L(σ,ψ)`, `ζ(σ)` on real `σ`; positivity of `L(σ,ψ)` on `[β,1]` without real zeros;
  `ζ(σ) < 0` just left of 1 (from `tendsto_riemannZeta_sub_one_div`); (7) the two-case argument
  (exceptional zero exists or not) giving `L(1,χ) ≥ c(ε)N^{−ε}`; (8) handling `χ₁χ` trivial (χ equivalent to χ₁).
- ζ: no change (variance barrier).

## Cycle 86 — Siegel's theorem (Lean, built, unconditional)
- **`RHTower/SiegelTheorem.lean`: `siegel_LFunction_one`** — for every `ε > 0` there is `c > 0` with
  `c·N^{−ε} ≤ L(1,χ)` for every nontrivial quadratic Dirichlet character `χ mod N`. Axioms standard
  (`propext, Classical.choice, Quot.sound`); ineffective constant (depends on the auxiliary `χ₁, β`).
- Supporting modules [all built, wired after `SiegelProductLFunction`, no lint findings]:
  - `SiegelRealAxis.lean`: `norm_LFunction_one_le_log` (`|L(1,χ)| ≤ log N + 5`, via the corpus truncation
    `norm_LFunction_sub_character_partial_le`), `LFunction_ofReal_im` (quadratic `L(σ,χ)` real for `σ > 0`, limit of
    real partial sums), `riemannZeta_ofReal_im`, `LFunction_two_re_pos`, `LFunction_re_pos_of_no_zero` (IVT),
    `exists_riemannZeta_neg` (`ζ(σ) < 0` on `(1−δ₀,1)`, from `tendsto_riemannZeta_sub_one_div`).
  - `SiegelTheoremAux.lean`: `exists_prod_one_sub_inv_ge` (`∏_{p|M}(1−1/p) ≥ C_δ M^{−δ}`), `LFunction_one_pos`,
    `productChar_sq`, `LFunction_one_ge_of_productChar_eq_one` (equivalent characters, via
    `LFunction_changeLevel` at level `N₁N`), `chiFour`.
  - `SiegelTheorem.lean`: `exists_siegel_auxiliary` (exceptional zero in `[1−η,1)` or `χ₄` with `β = 1−η`; in both
    cases `F(β) ≤ 0`), `siegel_numeric`, `siegel_LFunction_one`.
- Next on the F57c path: (a) zero form — `L(σ,χ) ≠ 0` for `σ > 1 − c(ε)N^{−ε}` (needs `|L'| ≪ log²N` near 1);
  (b) zero-free region for `L(s,χ)` uniform in the modulus with at most one exceptional real zero;
  (c) explicit formula for `ψ(x,χ)`; (d) Siegel–Walfisz.

## Cycle 87 — Siegel zero-free form (Lean, built); ζ conjecture: Siegel-zero dichotomy (killed)
- **`RHTower/SiegelZeroFree.lean`** [built, wired after `SiegelTheorem`, axioms standard]:
  `norm_LFunction_le_near_one` (`|L(z,χ)| ≤ 2(log N + 11)` on `Re z ≥ 1 − 2r_N`, `|z| ≤ 2`, `r_N = 1/(4log(N+3))`),
  `norm_deriv_LFunction_le_near_one` (`|L'(σ,χ)| ≤ 8(log N + 11)log(N+3)` on `[1 − r_N, 1]`, Cauchy estimate),
  **`siegel_zero_free`**: `∀ ε > 0 ∃ c > 0`, nontrivial quadratic `L(σ,χ) ≠ 0` for real `σ > 1 − cN^{−ε}`.
- **ζ conjecture C87 (Siegel-zero dichotomy).** If a Siegel zero `β_D` exists with `1 − β_D ≤ (log D)^{−A}`, then
  `Λ ≈ Λ·(1 − χ_D)` makes averaged Hardy–Littlewood sums computable (Heath-Brown), so `F(α)` is known on `(1, 2)` for
  `T` in a range `D^{a} ≤ T ≤ D^{b}`, and the A–F certificate gives `> 3/4` on-line there. Kill: the conclusion holds
  only for `T` in ranges tied to hypothetical exceptional moduli; in the no-Siegel-zero world nothing changes. Not an
  unconditional statement for all large `T`. Verdict: INSIGNIFICANT for the goal (and close to Conrey–Iwaniec's
  Siegel-zero spacing results, by internal reasoning only).
- Assessment of the F57c chain: next classical bricks are a modulus-uniform zero-free region (corpus has the general
  `Sieve/LandauLemma.landau_logDeriv`, `ArgumentVariation.borel_caratheodory`, and the ζ de la Vallée Poussin argument
  `Sieve/ZeroFreeRegionKappaOne`), the explicit formula for `ψ(x,χ)`, and Siegel–Walfisz. Before more classical
  infrastructure, the research core (family off-diagonal main term = GUE `F = 1` on `(1,2)`, unconditional prime side)
  needs a complete paper proof.

## Cycle 88 — Phase 5 for F57c: paper skeleton of the family off-diagonal main term
Setting: `S = Σ_q W(q/Q) Σ*_{χ mod q} ∫ w(t/T) |Σ_n a_nχ(n)n^{−it}|² dt`, `a_n = Λ(n)n^{−½}v(n/X)`, `X = Q^{1+θ}T`,
`K := X/(QT)`. Primitive orthogonality `Σ*_χ χ(n)χ̄(m) = Σ_{d|(q,n−m)} φ(d)μ(q/d)` for `(nm,q) = 1`.
1. **Diagonal** `n = m`: `T·ŵ(0)·Σ_q Wφ*(q)·Σ|a_n|²` (coprimality to `q` automatic for primes `> 2Q`).
2. **Möbius reduction** (`q = de`): `O = Σ_{d,e} W(de/Q)φ(d)μ(e) Σ_{n≡m (d), n≠m} a_nā_m Tŵ(T log(n/m))`. Large `e`
   (`> E = (log Q)^A`) cancel: `Σ_{e~Q/d, (e,nm)=1} μ(e) W(de/Q) ≪ (Q/d)e^{−c√log(Q/d)}` (PNT for `μ` with a
   coprimality twist; the twist costs `≪ log log`). [L1, classical; corpus has PNT-strength `μ` estimates]
3. **No off-diagonal below `λ = 1`:** `|n − m| ≲ X/T`, `d ≍ Q/e`, so `k = (n−m)/d` has `|k| ≤ 2eK`; for
   `X ≤ QT/(log)^{A+1}` only `k = 0` survives. (Consistent with F57b-low.)
4. **Switching** (`K > 1`): `O_{e,k} = Σ_{n≡m (k)} a_nā_m φ((n−m)/k) W((n−m)e/(kQ)) Tŵ(T log(n/m))`; expand
   `φ(j) = jΣ_{f|j}μ(f)/f`, truncate `f ≤ F` (relative error `O(1/F)` on average), so moduli `r = kf ≤ 2EKF`.
5. **Principal-character main term** mod `r`, with `Λ` replaced by density 1 (primes `> r` are automatically coprime):
   `M_{e,k,f} = μ(f)/(fφ(kf)) ∫∫ (xy)^{−½}v v ((x−y)/k)W((x−y)e/(kQ))Tŵ(T log(x/y))`. Needs PNT in **almost all**
   short intervals of length `≍ kQ/e ≥ X^{1/(1+θ)−o(1)}` (corpus `PrimeAlmostAllShortIntervalsAsymptotic`, `θ_short > 1/6`).
6. **Evaluating the `k`-sum:** `Σ_{k≠0}(k/φ(kf))g(k/(eK)) = c_f eK∫g − c'_f g(0) + o(1)` (Poisson/Euler–Maclaurin with the
   mean of `k/φ(kf)`). The `eK∫g` part carries `Σ_e μ(e)/e → 0` (Möbius cancels the "mean" term — no principal
   character in a primitive family); the `−g(0)` part carries `Σ_e μ(e)/e² = 6/π²`: a **negative** off-diagonal main
   term independent of `X`. In pair-correlation units this is the `1 − α` that turns the diagonal `α` into the GUE
   `F(α) = 1` on `(1, 2)`. [L6: exact constant bookkeeping — open in this log]
7. **Non-principal characters mod `r` (errors):** separate the coupling via `n^{iτ}m^{−iτ}` (Mellin) and an additive
   frequency `e(ξ(n−m))`, `|ξ| ≲ e/(kQ)`; then `|E| ≤ Σ_r φ(r)^{−1}Σ_{ψ≠ψ₀}∫∫|ĝ||A_ψ(ξ,τ)|²` with
   `A_ψ = Σ Λ(n)ψ(n)e(ξn)n^{−½+iτ}v(n/X)`.
   - conductor `> (log X)^B`: hybrid multiplicative large sieve `Σ_{r≤R}Σ*_ψ ∫|·|² ≪ (X + R²T')Σ|a|²`, relative error
     `≪ (log X)^{−B} + R²/X`; `R ≍ K·polylog` so this needs `X ≤ (QT)^{2−ε}` (λ < 2). [L7a: large sieve over moduli
     via Gauss sums from the additive large sieve — corpus has `largeSieve_gallagher`, `FareyHybridLargeSieve`]
   - conductor `≤ (log X)^B`: Siegel–Walfisz with a smooth weight varying on scale `kQ/e` (short-interval SW;
     needs zero-density for `L(s,ψ)` of small conductor or a direct short-interval argument). [L7b, open: the
     most delicate input; it depends on Siegel (done) + log-free/zero-density estimates for small conductors]
8. **Conclusion (if L1–L7 hold):** `F_fam(α) = α` on `[0,1]`, `F_fam(α) = 1` on `(1, 2)` (relative to `log(QT)`), hence the
   A–F certificate (pair-neutral, linear in Frobenius) gives family average on-line proportion `≥ 1 − 1/(3λ²) − ε`.
- Status: Phase 5 INCOMPLETE. Open cores: L6 (exact main-term bookkeeping, research-level but standard-type), L7b
  (short-interval SW for small conductors). Classical inputs to build in Lean: L1, L5 (have), L7a, uniform ZFR, ψ(x,χ)
  explicit formula, SW.
- **Cycle 88 Lean [built, wired after `SiegelZeroFree`, axioms standard, no lint findings]:**
  `RHTower/MultiplicativeLargeSieve.lean`: `sum_stdChar_mul_sub` (additive orthogonality on `ℤ/r`),
  `sum_normSq_stdChar_transform` (Parseval on `ℤ/r`), `normSq_gaussSum_of_isPrimitive` (`|τ(ψ)|² = r` for primitive `ψ`,
  any `r`), `conj_mul_gaussSum_of_isPrimitive` (`ψ̄(a)τ(ψ) = Σ_b ψ(b)e(ab)`), `sum_dirichletChar_normSq` (character
  Parseval), `sum_primitive_normSq_le` (`Σ_{ψ prim}|Σ c_nψ̄(n)|² ≤ (φ(r)/r)Σ_{b unit}|S(b)|²`), `stdChar_natCast_mul`,
  `sum_units_eq_sum_coprime`, and **`multiplicative_largeSieve`**:
  `Σ_{q≤R}(q/φ(q))Σ*_{ψ mod q}|Σ_{n<N}c_nψ̄(n)|² ≤ (N + R²(1+log(R²/2+1)))Σ|c_n|²` (from the corpus Farey large sieve).
  This is L7a without the `t`-aspect (the hybrid version is next).

## Cycle 89 — L6 resolved at paper level: the family GUE term is a hybrid Montgomery–Hooley term
- In step 6 of cycle 88 the `k`-sum weight is `h(k) = k/φ(kf)`. Its Dirichlet series
  `D_h(s) = Σ_k (k/φ(kf)) k^{−s}` behaves like `ζ(s)ζ(s+1)H_f(s)` (the local factors `1 + 1/(p^s(p−1))` give `ζ(s+1)`),
  so `D_h` has a pole at `s = 0`. With the Mellin transform `G̃(s)` of the `k`-kernel (simple pole at `0`, residue
  `G(0)`), the shifted contour picks up a **double pole** at `s = 0`: the constant term is
  `−½(log Y + c_f)G(0)`, not `−½G(0)` (cycle 88 missed the `ζ(s+1)` factor).
- With `Y = ex/(TQ)` and `Σ_e μ(e)/e² = 6/π²`, integrating over `x ≈ X` gives an off-diagonal main term
  `∝ −log(X/(QT))·Q²T` relative to the diagonal `∝ log X·Q²T`, i.e. `F_fam(α) = α − (α − 1) = 1` on `(1, 2)`: the GUE value.
- Structural identification: this is exactly the mechanism of the Montgomery–Hooley asymptotic
  `Σ_{q≤Q}Σ_a(ψ(x;q,a) − x/φ(q))² ∼ Qx log Q` (the `log` from `Σ (k/φ(k))k^{−s}` at `s = 0`). So **L6 = a hybrid
  (t-aspect) Montgomery–Hooley theorem for primitive characters**, whose unconditional proof needs SW + large sieve
  (Hooley's method), not GRH. For ζ the analogue is the variance of primes in short intervals (no `q`-average): the
  same main term would need Hardy–Littlewood's secondary term `−½log H` at variance precision — unprovable now.
  This pins the ζ/family dichotomy to one fact: **averaging over moduli makes the variance of primes provable.**
- Status of F57c Phase 5: L6 reduced to a standard-type asymptotic (hybrid Montgomery–Hooley); L7b (short-interval
  SW for small conductors) remains the hardest analytic input. Verdict: SURVIVES.
- **Cycle 89 Lean [built, wired after `MultiplicativeLargeSieve`, axioms standard, no lint findings]:**
  `RHTower/FamilyRankTraceSeam.lean`: **`family_seamA`** — Zeta23's linear rank–trace seam summed over a finite family of
  zero configurations: `4(N − R) − Φ − 2N − 3ΣN_II − (θ₀/aL)(4|F| + 2√(|F|Φ) + |F|θ₀/aL) ≤ Σ N₀*`, given family trace
  `≥ N − R` and family Frobenius `≤ Φ` (Cauchy–Schwarz on the tail term). This is the zero-side half of every family
  theorem (F57b-low and F57c): only family-averaged prime-side estimates are needed.

## Cycle 90 — Riemann–von Mangoldt uniform in the modulus (Lean, built); ζ conjecture: dilation-averaged frames (killed)
- **Lean [built, wired after `FamilyRankTraceSeam`, axioms standard, no heartbeat options, no lint findings]:**
  - `RHTower/DirichletLUniformBacklund.lean`: `reZeroSetL_card_le_uniform` (zeros of `Re L(σ+iT,χ)` on `[½,2]`
    `≤ (log 48 + log q + 2log|T|)/log(9/8)` for `|T| ≥ 4`), `backlund_horizontal_uniform`
    (`|Im∫_{½}^{2} L'/L(σ+iT,χ)dσ| ≤ 2π(1 + (log 48 + log q + 2log|T|)/log(9/8))`).
  - `RHTower/DirichletLUniformRvM.lean`: `localCountChi_uniform'`, `backlund_horizontal_uniform'`, `abs_muq_le`
    (`|μ_χ(τ)| ≤ (|C|+3)(log q + log(τ+3))`), `mainChi_aux_uniform`, and **`mainChi_uniform`**: absolute `C, T₀` with
    `|N_χ(T,2T) − (T/2π)(log(qT/2π) + 2log2 − 1)| ≤ C(log q + log T)` for every `q > 1`, primitive `χ`, `T ≥ T₀`.
    This is the conductor-uniform Riemann–von Mangoldt formula (L4 of F57b-low); Zeta23's `mainChi` had `C, T₀`
    depending on `q`.
- Process incident: a generated file reused the name `DirichletLUniformLocalCount.lean` (cycle 73's uncommitted module)
  and overwrote it; restored verbatim from the session transcript (Write at cycle 73 + cycle-74 edit), recompiled,
  axioms re-audited. The RvM module now consumes the restored `uniform_localCount`.
- **ζ conjecture C90 (dilation-averaged frames).** Averaging the Gram frame over dilations `{(n/k)^{−s}}_{k≤K}` imitates
  the family average and turns the beyond-Nyquist prime correlation into an averaged Hardy–Littlewood problem over linear
  forms `kn − k'm = h`, which might be provable as averages over moduli are (Montgomery–Hooley).
  **Verdict: INSIGNIFICANT (zero-set invariance).** Every such frame is a Gram matrix of vectors indexed by the same zero
  set of ζ; changing the frame changes the test functions, not the configuration. The family mechanism needs distinct
  zero sets: the off-diagonal in the family is `Σ_q Σ_{n≡m (q)}`, which is a sum over moduli of a *diagonal-type*
  condition, while any frame for ζ keeps the off-diagonal `Σ_{n≠m}Λ(n)Λ(m)·K(log n/m)`; a `k`-average only reweights `K`.
  The precision needed is still the `O(xH)` (secondary-term) level of averaged HL, equal in difficulty to F(α) on `[1, 1+δ]`.
- **Lesson (big picture).** Every ζ route tried in 90 cycles that gains over `0.6725` needs a statistic that separates
  ζ's zero set from a configuration with `1/6` far pairs at displacement `≈ 1/log T`; only averages over *distinct*
  L-functions supply such a statistic unconditionally.

## Cycle 91 — F57c retracted: the family off-diagonal needs Hooley-range Montgomery–Hooley (paper)
- **Error bookkeeping redone (paper).** Family `S = Σ_q W(q/Q)Σ*_χ ∫w(t/T)|Σ a_nχ(n)n^{−it}|²`, `a_n = Λ(n)n^{−½}v(n/X)`,
  `K = X/(QT)`. After `q = de`, `d | n−m`, `n − m = kd`, `φ(d) = dΣ_{f|d}μ(f)/f`, the off-diagonal is
  `Σ_k Σ_f (μ(f)/f) Σ_{n≡m (kf)} a_n a_m G(n−m) Tŵ_T(n,m)` with `G(h) = (h/k)M(Qk/h)`, `M(Y) = Σ_e μ(e)W(e/Y)`.
  - Principal character mod `r = kf`: each `k ≤ K` contributes `≍ Q²T` (not small); the GUE term `≍ Q²T log K` appears
    only after summing over `k`, where the bulk `∝ K` cancels through `∫M(Y)Y^{−2}dY = Σ_e μ(e)/e · ∫W = 0`.
  - Hence the non-principal errors must satisfy `Σ_{k≤K}|err_k| = o(Q²T log K)` while each `k`-term is `≍ Q²T`:
    **relative error `≪ (log K)/K` per dual modulus — a power saving.**
  - Large sieve (dual conductor `U`): error `≪ Q log R·log X·(X/U + UT)` against main `≍ Q²T log X`, i.e. relative
    `≪ K/U + R/Q`. It covers only dual conductors `U ≫ K·polylog`. SW covers `U ≤ (log X)^B`. **The gap
    `(log X)^B < U < K` is exactly the Montgomery–Hooley problem in Hooley's conditional range** (dual moduli a power
    of `X`): BV/BDH give only `log`-power savings (`x²/log^A`), zero-density + ZFR give only a constant factor
    (`exp(−c/κ)` for `U = X^κ`). Unconditionally unprovable with known tools; GRH (or power-saving equidistribution of
    `Λ` on average over moduli up to `K`) is needed. A one-sided version fails too: dropping non-principal terms needs
    a sign the dual kernel does not have, and sieve upper bounds lose a factor 2.
- **Verdict on F57c (and F57b-upper): BLOCKED (CIRCULAR at the arithmetic input).** The family Frobenius beyond
  bandwidth 1 needs Hooley-range Montgomery–Hooley, the family analogue of the ζ variance barrier. Cycle 83/89's
  "SURVIVES" was wrong: it overlooked that the per-`k` principal terms are individually large and cancel only in sum.
  Consistent with the GRH-conditional literature shape (family pair correlation for `α < 2` under GRH), by internal
  reasoning only.
- **Positive survivor (no-go discipline).** Sharp boundary: the family off-diagonal is unconditionally controllable
  exactly when every dual modulus is `≤ (log X)^B` (SW) or `≥ K·polylog` (large sieve). With `K ≤ (log X)^B` this is
  `λ ≤ 1 + B log log X/log X`: gain `o(1)` — INSIGNIFICANT for proportions. F57b-low (bandwidth `≤ 1` in conductor
  units: uniform 2/3 for the family `χ mod q`, `q ≤ T^{1−ε}`) is unaffected: it has no off-diagonal main term.
- **Big-picture law (new, unifying cycles 1–91).** *The Nyquist barrier is a level-of-distribution barrier.* Every gain
  over the bandwidth-1 certificate needs power-saving equidistribution of `Λ`: in short intervals for ζ (variance,
  HL secondary terms), in progressions to dual moduli up to `K = (QT)^{λ−1}` for families (Hooley range). Averaging over
  moduli moves the barrier only by `polylog`. Routes whose arithmetic side is divisor-like (mollified moments, where
  Kloosterman/Weil give power savings) are the only ones whose arithmetic input exists at power level.
- Lean: unchanged this cycle (cycle 90's uniform RvM stands; it serves F57b-low).

## Cycle 92 — target fixed: Theorem E uniform in the modulus (A–F's open hybrid-range remark); ζ conjecture C92 killed
- **ζ conjecture C92 (divisor-side Gram certificate).** Weight the Zeta23 Gram vectors by a mollifier `M(ρ)` (Levinson
  data, divisor arithmetic with Kloosterman power savings up to `θ = 4/7`), hoping the product certificate sees the
  near-line pairs that the plain Gram matrix cannot. Kill: every sum over zeros `Σ_ρ M(ρ)M̄(ρ)x^ρ` is evaluated by the
  explicit formula (Landau–Gonek), so its arithmetic side is `Λ⋆(mollifier)`, i.e. prime-type with level of
  distribution ≤ BV/BFI (cycle 34); the divisor-only (power-saving) side exists only for continuous moments, which
  detect zeros through Littlewood/Jensen and cap at Levinson's range. **Verdict: CIRCULAR** (the cycle-91 law).
- **Positive target (UTE).** Zeta23's Theorem E has constants depending on `q`, and its docstrings record the
  hybrid range as an open remark ([rem:otherL](i)). UTE: for `λ < 1`, `ε > 0`, `A > 0` there is `T₀` with
  `(H(λ_{1,χ}) − ε)·N_χ(T,2T) ≤ N₀*_χ(T,2T)` for all `T ≥ T₀`, all `1 < q ≤ T^A`, all primitive `χ mod q`, where
  `λ_{1,χ} = L/ℓ_{1,χ} = λ log(T/2π)/(log(qT/2π) + 2log2 − 1)`. Corollary: 2/3 − ε uniformly for `q ≤ T^{o(1)}`.
- **Uniformisation without replaying the heavy proofs.** `μ_q = μ_1 + (log q)/(2π)` exactly. Hence:
  - mumu error is quadratic in `c = log q/2π`: `E(c) = E(0) + 2cX₁ + c²X₂`; Zeta23's fixed-`q` statements at
    `q = 1, 2, 3` determine `X₁, X₂`, so `|E(c)| ≤ C(1 + c + c²)l² log L` with `C` absolute;
  - trace error is affine in `c` (and the `P_χ` part is bounded explicitly by `sum_P_part_chi_bound`): `q = 1, 2`;
  - NuBound for `μ_q` from `q = 1` by the shift; `lem_ends`, cross term and the coprime sums need short replays with the
    coefficient sequence quantified inside; `prop_PP_chi_uniform` already exists; RvM and local counts: cycles 73, 90.
  - The (1 + log q)^k losses are polylogarithmic against main terms of size `T·polylog`, except the coprime
    Chebyshev–Mertens error, where Zeta23's `(1+log q)²` must be sharpened to `(1 + log log q)²`
    (`Σ_{p|q} log²p/p ≤ C(log log q)²`).
- Build order: (1) shift + interpolated mumu/trace/NuBound; (2) cross + ends replays; (3) coprime sums; (4) tails/NII;
  (5) pointwise uniform assembly (seamA, seamBChi, `N0star_lower_H` are already pointwise).
- **Cycle 92 Lean [built, wired after `DirichletLUniformRvM`, axioms standard, no heartbeat options, no lint findings]:**
  - `ThmEUniformArchimedean.lean`: `muq_eq_muq_one_add` (`μ_q = μ_1 + log q/2π`), `abs_quad_le_of_interp`
    (Lagrange interpolation at `0 < a < b ≤ 1`), `Mform_shift`, `mumuShiftErr_eq_quadratic`,
    **`prop_mumu_uniform`**: `|𝓜[μ_q,μ_q] − 2πbL∫μ_q²| ≤ C(1+log q)² l² log L` (from `q = 1, 2, 3`).
  - `ThmEUniformTrace.lean`: `GentryChiA_diag_shift`, `trGtChiA_shift` (exact: `tr G̃(q,c) = tr G̃(1,0) + 2πad·log q/2π +
    L⁻¹Σ_k∫φ̂²P_c`), **`prop_trace_uniform`**: `|tr G̃ − aLN| ≤ C(1+log q)L√X`, uniform in `q` and the coefficients.
  - `ThmEUniformCross.lean`: `abs_Mform_PXc_le` (any `C¹` density), **`prop_cross_uniform`** (`≤ C(1+log q) l√X`).
  - `ThmEUniformEnds.lean`: `abs_PXc_le_uniform`, `muq_nuBound_uniform`, **`prop_ends_uniform`**
    (`≤ C(1+log q)² L l log l (l² + X)`).
  - `ThmEUniformCoprimeSums.lean`: `log_sq_div_antitoneOn`, `card_primeFactors_mul_log_two_le`,
    **`sum_primeFactors_log_sq_div_le`** (`Σ_{p|q} log²p/p ≤ K log²(log q + 8)`), `removed_le_sharp`,
    `coprime_cheb2b_uniform`, `sumA2gCoprime_upper/lower_uniform` (error `(B + K log²(log q + 8))L²`, i.e. `o(L³)` for
    `q ≤ T^A`; Zeta23's version lost `(1 + log q)²`).
- Remaining for UTE: `Msplit` (bilinearity, uniform), PP (`prop_PP_chi_uniform` exists), tails/NII/blocks with
  `(1 + log q)` constants, and the pointwise uniform assembly (`seamA`, `seamBChi`, `N0star_lower_H`).

## Cycle 93 — Theorem E uniform in the modulus: PROVED in Lean (unconditional)
- **`RHTower.thmE_uniform`** (`ThmEUniform.lean`): for `λ ∈ (0,1)`, `A ≥ 0`, `ε > 0` there is `T₀` with
  `(H(λ_{1,q}(T)) − ε)·N_χ(T,2T) ≤ N₀*_χ(T,2T)` for all `T ≥ T₀`, all `1 < q ≤ T^A`, all primitive `χ mod q`
  (`H(x) = 2 − 1/x − x/3`, `λ_{1,q} = λ log(T/2π)/ℓ_{1,q}(T)`). `T₀` depends only on `λ, A, ε`.
- **`RHTower.thmE_uniform_two_thirds`**: `∀ε>0 ∃κ>0 ∃T₀ ∀T≥T₀ ∀ 1<q≤T^κ ∀χ primitive: (2/3 − ε)N ≤ N₀*`.
- Axioms `[propext, Classical.choice, Quot.sound]`; no heartbeat options; no lint findings; wired after
  `DirichletLUniformRvM`.
- Modules (cycle 92–93): `ThmEUniform{Archimedean, Trace, Cross, Ends, CoprimeSums, TraceSquare, Seam, ErrorBudget,
  Rates}` + `ThmEUniform`. Proof: rank–trace certificate at one height (`seam_at`, Zeta23's pointwise
  `seamA`/`seamBChi`/`N0star_lower_H`), uniform inputs, error budget (`seam_error_le`), modulus-free rates
  (`ThmEUniformRates`, `eventually_rhoE_le`, `ET_le_rhoE`, `clam_le`).
- **Status relative to the frontier:** answers the hybrid-range remark recorded (open) in Zeta23's Theorem E
  ([rem:otherL](i)): the A–F 2/3 holds uniformly for conductors `q ≤ T^{o(1)}`, and the bandwidth-loss law
  `H(λ/(1+κ))` holds uniformly for `q ≤ T^κ`. New relative to the corpus; modest relative to the ζ goal.
- ζ goal: unchanged (level-of-distribution barrier, cycle 91).
- Next: F57b-low family boost (`X` up to `qT^{1−ε}` via family PP, cycles 82–83) now has uniform per-χ inputs; the family
  version would lift `H(λ/(1+κ))` to `H(λ)` on average over `χ mod q`, `q ≤ T^{1−ε}`.

## Cycle 94 — ζ conjecture C94 (height averaging) killed; family boost F57b-low planned
- **C94.** Average the A–F certificate over heights `T ∈ [T₀, T₀^{1+δ}]` (cumulative proportion only needs most dyadic
  windows): the needed `F(α)`, `α ∈ (1, 1.16)`, becomes an average over `T`. Kill: averaging over `T` averages the
  prime-pair variance over the scale `x = T^α` and the interval length `x/T` jointly; the main-term cancellation
  (pole vs Hardy–Littlewood mean) still needs the secondary term at precision `O(x log x)` against `xH`, for every
  `x` in the range — the same power-saving input. **Verdict: CIRCULAR.**
- **F57b-low plan (on top of `thmE_uniform`).** Family `χ ≠ χ₀ mod q`, `q` prime, `q ≤ T^{1−ε}`, bandwidth
  `X = (T/2π)^{λ'}`, `λ' = λ log(qT)/log T ∈ (1, 2)`:
  FB1 `LocalHypsCoreW` for the concrete taper at `λ' > 1` (wrappers with `ParamsValidFam`);
  FB2 uniform trace/mumu/cross at the `CoreW` layer; FB3 family `𝓜[P,P]` main term (cycles 82–83) in the concrete
  normalisation; FB4 assembly with `family_seamA` and an error budget. Target: family average `≥ H(λ) − ε → 2/3`.
- **Cycle 94 Lean [built, wired after `ThmEUniform`, axioms standard, no lint findings]:**
  `FamilyTaperBridge.lean` (`localHypsCoreW_concrete_fam`, `localHypsCoreW_eventually_fam`: the concrete taper data
  satisfy `LocalHypsCoreW` at every bandwidth `λ > 0`), `FamilyTraceWide.lean` (`trace_mu_wide`, `trace_comb`,
  `trace_final`, `trace_uniform_combine`, **`prop_trace_uniform_wide`**: `|tr G̃ − aLN| ≤ C(1+log q)L(1 + log T + √X)`
  at any bandwidth, uniform in `q` and the coefficients). FB1 done; FB2 trace done; next mumu/cross at `CoreW`.
- Cycle 94 (cont.) Lean [built, wired after `FamilyTraceWide`, axioms standard, no lint findings]:
  `FamilyMuMuWide.lean` (`mumu_core_wide`, `mumu_fixed_wide`, `mumu_uniform_of_three_wide`,
  **`prop_mumu_uniform_wide`**), `FamilyCrossWide.lean` (**`prop_cross_uniform_wide`**). FB2 complete.
- **FB3 design (paper).** Parity: odd and even characters have different archimedean densities, but
  `δ := μ_{1,q} − μ_{0,q} = μ_{1,1} − μ_{0,1}` is `q`-independent and `O(1/τ)`. Write `G(ν_χ) = G(μ_{0,q} + P_χ) + ε_χ G(δ)` and use
  `‖a + b‖² ≤ (1+η)‖a‖² + (1+1/η)‖b‖²` with `η = 1/l`: then the family Frobenius needs only the common-density sum
  `Σ_{all χ}` (cycle-82 mean square, cycle-83 end effects with `μ = μ_{0,q}`, `B_μ = (C₀ + log q) l`), plus
  `φ(q)(1 + l)·tr G̃²(δ) ≪ φ(q)(1+l)(TL + L l³ log l)`, relative `O(1/l)`. Nonprincipal family `≤` full family
  (each `tr G̃² ≥ 0`); the factor `φ(q)/(φ(q) − 1) → 1` needs `q → ∞`, which is the only regime where the family is
  needed (`q ≤ T^κ` is covered per character by `thmE_uniform`). Bandwidth: finitely many `Params` with
  `λ_j = λ(1 + κ_j)` on a `κ`-mesh of `[κ₀, 1 − ε]`.

## Cycle 95 — FB3: the family Frobenius bound (Lean, built); ζ conjecture C95 killed
- **Lean [built, wired after `FamilyCrossWide`, axioms standard, no heartbeat options, no lint findings]:**
  - `FamilyParityPerturbation.lean`: `parityShift` (`δ = μ_{1,1} − μ_{0,1}`, `q`-independent), `muq_one_eq_add`,
    `exists_abs_parityShift_le` (`δ` bounded on `ℝ`: equal Stirling main terms), `sq_add_le_eta`, `trGt2Nu`,
    `abs_PXc_le_sum`, **`trGt2_odd_le`** (`tr G̃²(μ_{1,q}+P) ≤ (1+η)tr G̃²(μ_{0,q}+P) + (1+1/η)tr G̃²(δ)`),
    **`trGt2_parityShift_le`** (`tr G̃²(δ) ≤ M²T∫Φ² + C L l log l (l+M)²`).
  - `FamilyPrimeDiagonal.lean`: `sumA2gCoprime_upper_uniform_wide`, `sameUnitClass_self`, **`family_PP_le`**
    (`Σ_χ 𝓜[P_χ,P_χ] ≤ φ(q)(T/π)Σ_{(n,q)=1}Λ²/n·g + φ(q)/(2π²)(Σa²)∫Φ²|x| + off-diagonal`).
  - `FamilyFrobenius.lean`: `coeffOK_dirichlet`, `Msplit_wide`, `trGt2Nu_eq_split`, **`family_frob_le`**:
    `Σ_{χ mod q} tr G̃²(μ_{0,q}+P_χ) ≤ φ(q)(TL/2π)(ℓ_{1,q}² + L²/3) + [explicit errors]` at every bandwidth `0 < λ ≤ 2`.
- **ζ conjecture C95 (family-to-ζ transfer through the principal character).** The family Frobenius sums over *all*
  characters, including `χ₀` whose `L`-function is `ζ(s)∏_{p|q}(1 − p^{−s})`. Could the family bound, minus the
  nonprincipal part, bound `ζ`'s Frobenius at bandwidth `> 1`? Kill: the family bound is an upper bound on a sum of
  nonnegative terms; isolating `χ₀` needs *lower* bounds for the `φ(q) − 1` nonprincipal Frobenius norms at the same
  precision, i.e. the asymptotic large sieve for each modulus — and a lower bound for `Σ_{χ≠χ₀}` with error
  `o(T L l²)` (one character's worth) is the variance problem again. **Verdict: CIRCULAR.**
- **FB4 plan.** (a) rates: class masses `Σ_{n≡r}Λ(n)/√n ≤ log X (1 + 2√X/q)`, `Σ a_n²(n+q) ≪ X log X + q log²X`; every
  `family_frob_le` error is `o(φ(q) T L l²)` for `q ≤ T^{1−ε}`, `X ≤ qT^{1−ε/2}`; (b) `GzGpChi` and block/tail inputs at
  `ParamsValidFam`; (c) unit conversion and `family_seamA`; (d) κ-mesh + `thmE_uniform` for small `q`.

## Cycle 96 (2026-10-13) — FB4 closed: family two-thirds theorem in Lean; C96 cubic certificates killed

**Lean (all axiom-clean: propext, Classical.choice, Quot.sound; wired after FamilyFrobenius; lint clean):**
- FamilyZeroSide: emptyZeroConfig, isPrimitive_of_prime, famZ, GzGpChi_at_fam, frobSq_hat_eq_fam, rtrace_hat_ge_fam.
- FamilySeamAssembly: family_budget (real), nontrivChars, card_nontrivChars, famZ_N/N0star, family_seam_at.
- FamilyClassMass: card_Ioc_residue_class_le, classMass_sq_le, sum_classMass_sq_le (∑_r A_r² ≤ (X/q+1)∑a_n²), sum_units_classMass_bracket_le, oneClassMass_sq_le.
- FamilyFrobeniusNontrivial: famMaj (explicit 6-term majorant), family_frob_all_le, family_frob_nontriv.
- FamilyCellBudget: main_frob_eq, family_phi_budget.  FamilyCellRates: famMaj_le_bound, eventually_famMaj_le, eventually_parity_le.
- FamilyCell: family_cell_at.  FamilyCellTheorem: **family_cell** (cell T^κlo ≤ q ≤ T^κhi, λ<2, λ−κlo<1, κhi<1: (H(λ₁)−ε)∑_{χ≠1}N_χ ≤ ∑N₀*_χ).
- FamilyTwoThirds: Hfun_one_sub_ge, lam1q_mesh_bounds, **family_two_thirds**: ∀ε>0 ∃T₀ ∀T≥T₀ ∀ prime q ≤ T^{1−ε}: (2/3−ε)∑_{χ≠1 mod q} N_χ(T,2T) ≤ ∑_{χ≠1} N₀*_χ(T,2T).
  Mechanism: q ≤ T^{κ₀} by thmE_uniform_two_thirds per character; larger q in mesh cells with bandwidth λ_j = 1+κ_j−δ > 1 (absolute), λ₁ ≥ 1−2δ−5/l relative to conductor; residue-class MV error X/q ≤ T^{1−δ}.
- Structural lesson: the family reaches relative bandwidth λ₁ → 1 from below only (X/q ≪ T ⇔ X ≪ qT = conductor) — family averaging over one modulus does not beat Nyquist relative to the conductor; consistent with cycle-91 law.

**C96 (ζ conjecture): degree-3 concave trace certificate (uses tr Ĝ³, Rudnick–Sarnak range) beats 2/3.**
- Paper: concave cubic g=ax+bx²+cx³ (b,c≤0 for unbounded multiplicities) with g(1)≤1, g(2)≤0; majorization (eigenvalues majorize diagonal multiplicities) gives N₀* ≥ ∑g(μ_i). LP edge: value = (2−c₂) + c·D₃, D₃ := (S₃−3S₂+2S₁)/N = normalized distinct-triple sum.
- GUE sine-kernel computation (K̂=(1/λ)1_{[−λ/2,λ/2]}): c₂ = 1/λ+λ/3 (λ≤1), 1+1/(3λ²) (λ≥1); c₃ = 1+1/λ² (all λ); **D₃ = (1−λ)₊³/λ²**.
- Verdict: FALSE (no gain): c≤0 and D₃≥0 ⇒ quadratic optimal; c>0 breaks concavity at m=2 unless c≤1/3, and even then max at λ=1 is 2/3.
- Positive survivor (CANNOT law): cubic trace certificates gain exactly c·(1−λ)₊³/λ² over Alpöge–Furman; the connected triple sum vanishes identically for λ ≥ 1. Paper only; Lean not attempted (needs sine-kernel Fourier integrals).
- The ζ goal (75%) is still not met.

## Cycle 97 (2026-10-13) — C97 killed: the Alpöge–Furman counting step is sharp; the 1/3 deficit is RH-proximate

**C97:** a sharper matrix inequality (same inputs tr Â ≈ N, ‖Â‖_F² ≈ cN, Â = P + Q, P ⪰ 0 on-line, Q off-line pair blocks with n₊(Q) ≤ b, N_on + 2b ≤ N) beats 2 − c.
- Paper: commuting LP: f ≥ A²/r + B²/p, B ≥ 2p ⇒ r ≥ A²/(2A − (2−c)N), minimised at A = (2−c)N ⇒ r_min = (2−c)N exactly. Extremal: (2−c)N orthogonal simple on-line zeros (eigenvalue 1) + (c−1)N/2 coalesced off-line pairs (eigenvalue 2). Spectrum on {0,1,2} ⇒ S₃ = 3S₂ − 2S₁ — identical to the sine-kernel relation at λ = 1 (explains the cycle-96 cubic tie).
- Verdict: FALSE. Lean: ZerosideRankSharpness.lean — `zeroside_rank_core_sharp` (diagonal P = I_r, Q = 2·I_b attain 4 tr − 2N − ‖·‖² = rank P), `critical_line_bound_optimal`, `extremal_third_moment`; axiom-clean, wired after FamilyTwoThirds, lint clean.
- Off-line pair geometry (paper): block = f fᵀ + f̄ f̄ᵀ = 2(aaᵀ − bbᵀ), f = φ̂(τ − γ + iy) = a + ib, tr = 2 independent of y, Frobenius ≥ 4 + 8(‖a‖²‖b‖² − ⟨a,b⟩²); ‖b‖² ≍ y²L². So the deficit consists of off-line pairs at distance ≪ 1/L — RH-proximate configurations.
- C98 (combine with Selberg near-line density [corpus: exists_selberg_nearLine_zeroDensity], Littlewood Σ(β−1/2), Levinson): FALSE — all bound zeros far from the line or total off-line mass ≥ 58%; none constrains infinitesimally-off-line pairs at proportion 1/3. Full pair-correlation shape on [−1,1] only reaches the Montgomery–Taylor/CCLM-type cap ≈ 0.6727.
- CANNOT law (survivor): beating 2/3 requires either F(α) on (1, 1.16) (prime-pair power savings) or on-line sign detection at resolution ≪ 1/log T separating sign-change pairs from coalesced off-line pairs.
- The ζ goal (75%) is still not met.

## Cycle 98 (2026-10-13) — Levinson–AF hybrid killed; exact exchange rate H*(B) = (2B−1)/(3B−2) in Lean

**C98:** combine the AF certificate with Levinson's mechanism (corpus: XiHermiteBiehlerCount — ξ + λξ' and ξ have the same zeros right of the line).
- Paper: a coalesced off-line pair at distance y gives V-zeros at 1/2 + y²/(2λ) and ≈ 1/2 − 2λ; a simple on-line zero gives a V-zero at ≈ 1/2 − λ/(1 + λG). Levinson's Littlewood count bounds the pair count p by (1 − κ_Lev)N/2 ≈ 0.29N; AF bounds p ≤ N/6. Independent linear constraints on p ⇒ min = AF. Verdict: FALSE (no synergy). Levinson's displacement law is classical (REDISCOVERED).

**Exchange-rate law (Lean: PairCorrelationExchangeRate.lean, axiom-clean, wired, lint clean):**
- frobenius_density_integral: c(λ) = 1/λ + (2/λ²)[∫₀¹(λ−α)α + ∫₁^λ(λ−α)B] = 2/λ − 2/(3λ²) + B(λ−1)²/λ².
- certOpt_sub_certValue / certValue_le_opt / certValue_at_opt: max_λ (2 − c(λ)) = (2B−1)/(3B−2) at λ* = (3B−2)/(3(B−1)) (exact square identity, linear_combination).
- opt_sub_two_thirds: gain over 2/3 is exactly 1/(3(3B−2)) for every finite B; opt_ge_three_quarters_iff: ≥ 3/4 ⟺ B ≤ 2; certOpt_one = 1; certValue_four_thirds_two = 3/4.
- Meaning: the beyond-Nyquist obstruction is BOUNDEDNESS of F just above 1 (no spike at α = 1⁺), not its value. 75% ⟺ (for this certificate) F ≤ 2 on (1, 4/3).

**C99:** "F ≤ B on (1, 1 + 1/(3(B−1))) for some finite B" (enough to beat 2/3).
- Prime side: equivalent to RH-quality variance Var(ψ on [x, x+H]) ≤ B·H log x for H ≤ x^{1/(3B−2)}. Known unconditionally: only almost-all asymptotics with log-savings relative to H² (Guth–Maynard range H ≥ x^{2/15}); sieve upper bounds lose the oscillating phase (n/m)^{iT} and give ratio T^η/log T. Verdict: OPEN, beyond SOTA — the precise frontier statement; neither killed nor provable with current inputs.
- The ζ goal (75%) is still not met.

## Cycle 99 (2026-10-13) — Landau–Gonek circular; augmented (Z'-weighted) certificate survives with three open cores

**C99′:** uniform Landau–Gonek ∑_{γ≤T} x^ρ = −(T/2π)Λ(x) + O(x log 2xT log log 3x) + … plus Gram positivity excludes a spike of F at 1⁺.
- Corpus: no uniform Landau–Gonek. Paper: for x = T^{1+η} the O(x log x) error is exactly the off-diagonal prime-pair term; the main term −(T/2π)Λ(x) is the diagonal. Positivity already in the certificate. Verdict: CIRCULAR.
- Also: under RH, Selberg's variance bound is H log²X (one log too many), so even RH does not give F ≤ B pointwise beyond 1 — the AF route to 75% needs input beyond RH (GUE-type), although 75% itself is implied by RH.

**C100 (new structure):** augment the zero vectors to u_ρ ⊗ (1, t g(ρ)), g = (χ^{-1/2}ζ)' (real on the line; opposite signs at consecutive simple zeros). Same P + Q structure (on-line V V*, off-line pair V V'* + V' V*), Hermitian via ρ ↦ 1 − ρ̄.
- Certificate = AF + (−2t²O₁ − t⁴M₄) − 2t²(S_on − S) where S = ∑_ρ g(ρ)g(1−ρ) (CGG-type, analytic ⇒ unconditional), O₁ = Re ∑_{ρ≠ρ'} |K(γ−γ')|² g(ρ)ḡ(ρ'), M₄ = ∑ |K|²|g|²|g'|². Max gain O₁²/M₄ iff O₁ < 0 (sign alternation of Z' at close zeros; |K|² concentrated below one mean spacing).
- AF extremal (coalesced off-line pairs, g ≈ 2cy → 0) gets no gain by itself; exclusion comes from the prime-side values.
- Verdict: SURVIVES PRELIMINARY ATTACK as a route to ANY gain over 2/3 with non-pair-correlation information. [OPEN CORE]: (i) O₁ < 0 asymptotically — prime side is a Λ × ζ'-type (Titchmarsh-divisor-like) correlation; (ii) M₄ ≪ N·scale² — mollified discrete fourth moment of ζ' at zeros (unknown); (iii) off-line |g|² control for S_on ≤ S + small. Expected gain small (repulsion makes |g||g'| ∝ δ² for close pairs). Not a 75% route.
- Lean: AugmentedRankTraceCertificate.lean — `zeroside_rank_core_excess` (counting step with on-line trace excess E), `augmented_gain_le`, `augmented_gain_max` (max_s (−2sO₁ − s²M₄) = O₁²/M₄ at s = −O₁/M₄), `augmented_gain_nonpos_of_nonneg`; axiom-clean, wired, lint clean.
- The ζ goal (75%) is still not met.

## Cycle 100 (2026-10-13) — C100 (Z'-augmented) computability horizon; C101 (heat flow) gives no count

**C100 decided (open core (i)):** sign of O₁ = Re Σ_{ρ≠ρ'} |K(γ−γ')|² g(ρ)ḡ(ρ'), g = (χ^{-1/2}ζ)'·M(s)M(1−s) (analytic, real on the line).
- Random-matrix heuristic: close pairs (d < 1 spacing) are adjacent, g g' ≈ −a²d² < 0 ⇒ O₁ < 0; rough size O₁/N ≈ −0.1a², M₄/N ≈ a⁴ ⇒ ideal gain O₁²/M₄ ≈ 0.005N.
- Prime side: O₁ + diag = ∫(K̂∗K̂)(ξ)|Σ_ρ e^{iξγ}g(ρ)|²dξ; each bracket is a residue integral of (ζ'/ζ)·(χ^{-1/2}ζ)'·MM — coefficients (Λ∗log∗m)(n) plus functional-equation dual terms of length ~T. Its ξ-mean square is a twisted-fourth-moment-type object (two ζ' factors); diagonal-dominated only for twist lengths ≲ T^{1/4} (Hughes–Young / BBLR range) ⇒ usable bandwidth λ ≲ 1/4 where H(λ) < 0; without a mollifier, log-normal |ζ'| inflates M₄ by powers of log T.
- Verdict: INSIGNIFICANT for the goal (ideal gain ≈ 0.005, computability horizon far below bandwidth 1). Survivor: the gain law O₁²/M₄ (Lean, cycle 99) and the identification of O₁ as a twisted-fourth-moment-type mean square.

**C101:** de Bruijn–Newman heat flow (corpus: KiKimLeeWeylHorizon — zeros of H_t with |Re z| ≥ 2π e^{(3/2+ε)/t} real and simple) bounds off-line zeros of H₀ = ζ.
- Forward flow: complex pairs land (two real zeros appear), real zeros stay real; #off-line pairs of H₀ near height X = #landings in [0, t*], t* = (3/2+ε)/log X. Landing time ≈ y₀²/4 only for isolated pairs; interactions are nonlocal, so neither a count of landings nor a location bound |β − 1/2| ≪ (log T)^{-1/2} follows (the latter would be far beyond any known zero-free region).
- Verdict: INSIGNIFICANT (monotonicity of real-zero count gives no lower bound for N_real(H₀)). NO POSITIVE SALVAGE FOUND beyond the bookkeeping identity N_real(H₀) = N − 2·#landings.
- The ζ goal (75%) is still not met.

## Cycle 101 (2026-10-13) — averaged exchange rate: MR variance and S(t)-variance both too coarse

Requirement (from PairCorrelationExchangeRate): W(λ) = ∫₁^λ (λ−α)F(α)dα ≤ 2·W_GUE(λ) near λ* = 4/3 for 75%, or W(1+η) = O(η²) for any gain; precision needed ≍ η·N on pair sums at scale 1/(λ log T).

**C102:** Matomäki–Radziwiłł short-interval variance (corpus: PrimeAlmostAllShortIntervals, MatomakiTeravainenAllIntervalTheorem, PairFibreMeanSquare) gives the averaged exchange rate.
- MR-type bounds save (log h)^{-c} relative to h² (variance of the mean); W needs Var(H) ≪ B·H log X (saving H/log X relative to H²) for log X ≤ H ≤ X^{1/4}. Gap: power vs log-power. For Λ the MR range is further restricted (H ≥ X^{2/15+ε} via zero density). Verdict: FALSE (insufficient by a factor H/(log)^{c}).

**C103:** Selberg–Fujii–Tsang variance of N(t+h) − N(t) (unconditional: ∫_T^{2T}(S(t+h)−S(t))² = (T/π²)log(2 + h log T) + O(T√log(2+h log T))) pins F beyond 1 through Fejér averages ∫F(α)(sin πcα/πα)² for all c = h log T.
- At c ≍ 1 the error is O(T), i.e. relative O(1); a spike of mass m at α = 1⁺ changes the Fejér average by m·sin²(πc)/π² — detectable only with error o(m)T. Selberg's method approximates S by Dirichlet polynomials of length T^ε, blind below scale 1/log T. Corpus: no S-variance module. Verdict: FALSE (precision O(1) where O(η) is required).
- Structural note: spikes of F at 1⁺ are invisible to every known unconditional statistic: prime side (needs RH-quality variance), positivity (allows O(1) mass), S-moments (O(1) error at scale 1/log T).
- The ζ goal (75%) is still not met.

## Cycle 102 (2026-10-13) — Levinson long-mollifier killed; Lean reduction: ζ 75% ⟸ one prime-side mean-value inequality

**C104:** Levinson with longer mollifiers (corpus: LevinsonLinearOptimizationInterior, linear mollifier, > 1/3 at θ < 1/2) reaches 75%.
- Provable mollifier lengths stop at θ = 4/7 (Conrey, special coefficients; 17/33 general, BCR) ⇒ ≈ 0.417; 75% needs θ ≫ 1 (twisted second moments of ζ with Dirichlet polynomials longer than T). No synergy with AF (cycle 98). Verdict: FALSE with current inputs.

**C105 (survivor, formalized): the precise reduction.** At bandwidth λ = 4/3 (X = (T/2π)^{4/3}) every certificate input is unconditional except the Frobenius norm:
- ZetaTraceWide.lean: `mu_eq_muq` (μ = μ_{0,1}), `PX_eq_PXc_one`, W-versions of Π-part bound / integrability / diagonal decomposition (`GentryA_diag_eq_W`), `trGtA_split` (tr G̃ = tr G̃(1,0) + Π-part + P-part), `prop_trace_zeta_wide`: |tr G̃ − aLN| ≤ C L(1 + log T + √X) at every λ > 0.
- ZetaThreeQuartersReduction.lean: `FrobeniusFourThirds` := ∀ε>0, eventually tr G̃²(T) ≤ (5/4+ε)(aL)² Tℓ₁(T)/2π for params43 = stdParams (4/3); `zeta_three_quarters_of_frobenius`: FrobeniusFourThirds ⇒ ∀ε ∃T₀ ∀T≥T₀, (3/4−ε)N(T,2T) ≤ N₀*(T,2T); `zeta_three_quarters_cumulative_of_frobenius`: (3/4−ε)N(T) ≤ N₀*(T); `frobenius_target_gue`: 2 − c(4/3,2) = 5/4 and GUE value 19/16 < 5/4.
- Proof: seamA at ParamsValidFam (blocks, tailInputs_fam, Gz_eq_Gp with taper smoothness), wide trace with RvM, error budget (√X = T^{2/3}, NII ≪ √T log T, θ₀ ≪ T^{-1/3} log T).
- All axiom-clean, wired after AugmentedRankTraceCertificate, lint clean. No RH, no zero-location hypothesis: the single hypothesis is an explicit mean value of ν_X = μ + Π_X + P_X with X = T^{4/3} against the Gram kernel — a weak pair-correlation statement on (1, 4/3).
- The ζ goal (75%) is still not met: FrobeniusFourThirds is open (equivalent to RH-quality prime variance in intervals ≤ x^{1/4}, cycle 98–101).

## Cycle 103 (2026-10-13) — anatomy of FrobeniusFourThirds; Fejér-window sieve route killed; feasibility region in Lean

**Anatomy (paper):** at λ = 4/3 the prime-side Frobenius splits as μμ + 2μP + PP + Π-terms + ends.
- μμ and μ×P: wide family machinery at q = 1 applies (cross error ≪ l·√X = T^{2/3}l ≪ TL³).
- Π-part: |Π_X| ≤ 3√X/(1+|τ|) ⇒ contribution ≪ XL/T = T^{1/3}L ≪ TL³ (negligible).
- PP diagonal = (T/π)Σ a_n² g(log n) + O(L⁴) — gives the "diagonal-only" value 1/λ + λ/3 = 43/36 at λ = 4/3; margin to the target 5/4 is exactly 1/18 (GUE off-diagonal ≈ −1/144).
- Ends: Zeta23's lem:ends uses sup|ν| ≍ √X at λ > 1 ⇒ bound ≍ X L l log l ≫ TL³; a correct bound needs local mean squares of P_X near the window edges — the same arithmetic input as the off-diagonal.
- Conclusion: every λ > 1 difficulty is one object — mean squares of P_X (X = T^{4/3}) over [T,2T] and its sub-windows, with the off-diagonal prime pairs allowed a surplus of 1/18 of the normalised count.

**C106:** symmetric Fejér window (ŵ ≥ 0) makes the off-diagonal kernel nonnegative, so Selberg-sieve upper bounds for prime pairs suffice.
- The off-diagonal main term ≍ Σ_{n≤X}Λ(n) ≍ X (density of primes) must cancel against the μ×P cross term; sieve constants θ > 1 leave (θ−1)X ≫ TL³ (X = T^{4/3}). Verdict: FALSE (the needed statement is a variance; positivity cannot supply it).

**Lean (PairCorrelationExchangeRate.lean, extended):** `three_quarters_le_certValue_iff` (3/4 ≤ certValue λ B ⟺ B(λ−1)² ≤ (5/4)λ² − 2λ + 2/3), `feasibility_le_two` ((5/4)λ² − 2λ + 2/3 = 2(λ−1)² − (3/4)(λ−4/3)²: B = 2 is the universal ceiling, attained only at λ = 4/3), `three_quarters_le_certValue_one_iff` (with B = 1 need λ² ≥ 4/3). Axiom-clean, lint clean.
- The ζ goal (75%) is still not met.

## Cycle 104 (2026-10-13) — Type-II route killed; zero-side (pair-correlation) form of the reduction in Lean

**C107:** a Type-II (Heath-Brown/Vaughan bilinear) decomposition of Λ bounds the mean square of P_X (X = T^{4/3}) over [T,2T] well enough for the 1/18 margin.
- Bilinear/Hölder mean-value bounds give ∫|P_X|² ≪ T(log T)^C with combinatorial constants and extra log powers; the certificate needs the asymptotic within ≈4% of the main term (target 5/4 vs diagonal-only 43/36). Verdict: FALSE (order-of-magnitude bounds cannot meet a constant-exact margin). Same for η = c(log log T)/log T bandwidth excess: gain → 0.

**Lean (ZetaThreeQuartersReduction.lean, extended):** `PairCorrelationFourThirds` (zero side: frobSq(Ĝ) ≤ (5/4+ε)N(T,2T) at bandwidth 4/3 — for on-line zeros Σ_{ρ,ρ'}K(γ−γ')²), `frobeniusFourThirds_of_pairCorrelation` (bridge Gz = Gp + Riemann–von Mangoldt), `zeta_three_quarters_of_pair_correlation`: PairCorrelationFourThirds ⇒ (3/4−ε)N(T) ≤ N₀*(T). Axiom-clean, lint clean.
- The ζ goal (75%) is still not met; its single missing input is now stated in Lean both on the zero side (pair-correlation sum) and on the prime side (Frobenius mean value).

## Cycle 105 (2026-10-13) — the uniform window is not optimal beyond bandwidth one: 75% tolerates F ≤ 14/5

**C108:** at bandwidth > 1 a non-uniform window density ψ (ψ = |φ|², certificate value 2 − Q(ψ), Q = ∫ψ² + E f(|X−Y|), f = u on [0,1], f = B beyond) tolerates B > 2 for 75%.
- First variation: V₀ = ψ₀ + f∗ψ₀ for the uniform ψ₀ on [−2/3, 2/3] is smaller at the centre than at the edges (f increasing, jump to B at 1) ⇒ moving mass inward lowers Q ⇒ uniform not optimal.
- Explicit two-window mixture ψ_ε = (1−ε)U[−2/3,2/3] + εU[−1/2,1/2]: Q_s = 9/8 + B/16, Q₁ = 4/3, cross Q_× = 971/864 + B/48 (trapezoid density of X − Y). At B = 2, ε ≈ 0.335: value ≈ 0.778 (vs 3/4); 75% holds up to B ≈ 2.85 (Lean: B ≤ 14/5 with ε = 7/16).
- Under B = 1 (GUE) the mixture does not lower the minimal bandwidth noticeably (s = 1.1: Q ≈ 1.273 > 5/4).
- Verdict: SURVIVES (proved in the pair-correlation model). Significance: the open input for 75% weakens from F ≤ 2 to F ≤ 14/5 on (1, 4/3) (for a smoothed mixture taper); it stays open — no finite bound for F beyond 1 is known.
- Lean: PairCorrelationMixtureWindow.lean — `cross_density_integral` (2∫ trapezoid·f = 323/864 + B/48), `mixQ`, `mixQ_zero`, `mixture_beats_uniform` (3/4 < 2 − mixQ 2 (1/3)), `mixture_three_quarters` (B ≤ 14/5 ⇒ 3/4 ≤ 2 − mixQ B (7/16)). Axiom-clean, wired after ZetaThreeQuartersReduction, lint clean. Not yet connected to the ζ prime side (needs a smooth taper realising ψ_ε and its Frobenius main term).
- The ζ goal (75%) is still not met.

## Cycle 106 (2026-10-13) — window optimisation beyond one: exact cross formula, B_max ≈ 2.9, limit structure

**General cross term** (X ~ U[−s/2,s/2], Y ~ U[−t/2,t/2], t ≤ 1 ≤ (s+t)/2, a = (s−t)/2, b = (s+t)/2; trapezoid density of X−Y with plateau 1/s on |d| ≤ a, slope (b−d)/(st) on [a,b]):
E f(|X−Y|) = a²/s + (1/(st))[b(1−a²) − (2/3)(1−a³)] + B(b−1)²/(st); check (4/3,1): 323/864 + B/48 ✓.
- Two-mixture with t = 1: B = 3 gives H ≈ 0.7458 (s = 4/3), 0.7433 (s = 5/4), 0.7365 (s = 3/2) ⇒ B_max(two-mixtures) ≈ 2.87, attained near s = 4/3 (Lean certificate: 14/5).
- Variational equation for the optimal ψ on [−s/2, s/2] (V = ψ + f∗ψ constant on supp ψ): differentiating twice, ψ'' + 2ψ = (B−1)[ψ'(x+1) − ψ'(x−1)] (delay-differential; the jump of f at 1 couples x ± 1). For B = 1 it reduces to MT's cos(√2 x) profile. Not solved in closed form.
- Limits: B → ∞ forces s → 1⁺ and the value → HD 1 = 3/2 − cot(1/√2)/√2 ≈ 0.6725 (Theorem D, corpus) < 3/4, so B_max is finite; B = 1 (GUE) needs s ≥ ≈ 1.15 even with optimisation (mixtures at s = 1.1 give ≈ 0.727).
- Verdict C109 ("an optimised window reaches 75% with no information beyond 1"): FALSE (support ≤ 1 caps at the MT/CCLM optimum ≈ 0.6725–0.6727). Survivor: finite B_max ∈ [14/5, ∞) with the delay-DE characterisation.
- No Lean this cycle (numerical scan only; the proved tolerance 14/5 is already in PairCorrelationMixtureWindow.lean).
- The ζ goal (75%) is still not met.

## Cycle 107 (2026-10-13) — heat-flow two-point dynamics give no pair correlation beyond one

Corpus check: unconditional Montgomery pair form only for α ∈ (0,1) (MontgomeryPairCorrelationLeadingOrder/Uniform/ShortLength (down to x = (log T)³), MontgomeryAveragedForm); no statement beyond α = 1; prime short-interval results are almost-all/Huxley-type (PrimeAlmostAllShortIntervals*, PrimeShortIntervalsHuxleyAsymptotic), none of RH-quality variance.

**C110:** the de Bruijn–Newman flow (KKL horizon t*(X) = (3/2+ε)/log X, corpus KiKimLeeWeylHorizon) transfers pair-correlation information beyond 1 to H₀ = ξ.
- H_t = e^{−t∂²}H₀ is a Gaussian average of ξ along the vertical direction (width ≍ √t ≍ (log X)^{-1/2}); it has no Euler product and no explicit formula, so its pair correlation beyond 1 is as unknown as ξ's. KKL gives reality of H_t-zeros, not their correlations. Zero dynamics ẋ_j = 2Σ 1/(x_j − x_k) are nonlocal; only the global top-zero bound d(Y²)/dt ≤ −2 is available (de Bruijn's Λ ≤ 1/2). Rodgers–Tao's Λ ≥ 0 uses F on (0,1) only.
- Verdict: INSIGNIFICANT (no new information beyond α = 1). NO POSITIVE SALVAGE FOUND.
- The ζ goal (75%) is still not met.

## Cycle 108 (2026-10-13) — Gram-point sign statistics do not bound off-line pairs

Corpus: no Gram-point/Gram-law infrastructure (only generic sign-alternation lemmas: WindowProducer, SignAlternationHyperbolicity).

**C111:** the AF extremal (coalesced off-line pairs, cycle 97) shows up as Gram-law failures; discrete moments of ζ at Gram points (Σ_n (−1)^n Z(g_n) ~ 2N, Σ_n Z(g_n)² ~ N log T, mollified versions) bound the proportion of Gram intervals without a sign change from above, and with AF give > 2/3.
- Discrete moments at Gram points are Selberg-type: Cauchy–Schwarz gives a positive but small lower proportion of sign changes (mollification needed to remove the log; the resulting constants are of Selberg-method size, far below 2/3); they give no upper bound on failures. Each Gram interval can also contain 0 or 2 zeros legitimately (close on-line pairs), so a failure is not a certificate of an off-line pair. Known: Gram's law fails for a positive proportion of n (Selberg), so the constraint is not binding at the AF extremal (1/3 of zeros in pairs).
- Verdict: INSIGNIFICANT. NO POSITIVE SALVAGE FOUND.

**Status (unchanged):** the only route found reduces 75% (in Lean) to PairCorrelationFourThirds; that input is pair correlation beyond α = 1, not known even under RH for any α > 1. Every unconditional tool tested in cycles 96–108 fails for an identified reason.
- The ζ goal (75%) is still not met.

## Cycle 109 (2026-10-13) — the missing input is not supplied by GRH, EH, or positivity

**C112:** GRH (or Elliott–Halberstam) implies PairCorrelationFourThirds.
- PairCorrelationFourThirds needs the weighted average ∫₁^{4/3}(4/3−α)F(α)dα ≤ 1/9 (twice the GUE value 1/18), i.e. on the prime side RH-quality-with-constant variance Var(ψ; x, x+h) ≤ B h log x for x^{0} ≤ h ≤ x^{1/4}.
- Under RH/GRH the known bound is Selberg's Var ≪ h log²(x/h) (one log too many ⇒ F ≪ log beyond 1); the q = 1 major arc in short ranges IS this variance, so the circle method under GRH does not evaluate it. EH controls primes in progressions to large moduli on average, not prime pairs at short shifts weighted by e(Th/n) (parity-sensitive). Verdict: FALSE by every known argument (no implication available); the input lies beyond GRH and EH.

**C113:** positivity of F (Gram positivity) plus F = δ + |u| on [−1,1] excludes a spike at 1⁺ large enough to matter.
- Needed: spike mass c ≤ 1/6 per side (uniform window s = 4/3: Q = 9/8 + 2W', W' ≤ 1/16 ⇔ ∫₁^{4/3}(4/3−u)F ≤ 1/9; GUE background uses 1/18).
- With GUE background, positivity (F̂ ≥ 0: 2c cos(2πx) ≥ −(1 − sinc²x), binding at x = 1/2) allows c ≤ (1 − 4/π²)/2 ≈ 0.297 > 1/6. LP duality: any certificate built from [−1,1] data plus positivity is capped at the bandwidth-one optimum (MT ≈ 0.6725, CCLM-type ≈ 0.6727). Verdict: FALSE.
- Survivor (paper): explicit spike threshold — positivity permits spike mass (1 − 4/π²)/2 at α = 1⁺, while 75% via the s = 4/3 window tolerates only 1/6.
- The ζ goal (75%) is still not met.

## Cycle 110 (2026-10-13) — sign-pair hybrid killed; the open input also proves 3/4 simple zeros (Lean)

**C114 (sign-pair hybrid):** the rank–trace bound 2 tr P − ‖P‖² ≤ rank P is slack by Σ(μ_i − 1)² over the
nonzero eigenvalues of the on-line Gram P (close on-line pairs give eigenvalues ≈ 2 and ≈ 0 and are credited
0). A lower bound E_on ≥ N/12 for the Frobenius mass of distinct on-line pairs (two sign changes of Z within
≈ 0.75 mean spacing) would add E_on to the certificate and give 3/4 at bandwidth 1.
- Kill: E_on is a correlation of the *on-line* zeros, so it needs a non-analytic (sign) statistic (every
  explicit-formula statistic is even in the displacement y of a reflected pair, hence y²-blind). The only
  unconditional sign technology (Selberg/Hardy: compare |∫Φ| with ∫|Φ| for mollified Z on intervals of
  length h) detects one sign change per interval of length ≫ mean spacing with a small positive proportion;
  it cannot certify two sign changes inside 0.75 spacing, let alone a mass N/12. Levinson sees y linearly but
  only counts (cycle 98: no synergy). Verdict: FALSE with current tools.

**C115 (hardness witness, survivor):** the bandwidth-4/3 hypothesis also proves three quarters of the zeros
simple and on the line, since the multiplicity-aware seam has the same left side (Zeta23 seamA_mult2).
- Lean (ZetaThreeQuartersReduction.lean, refactored): `Seam43 Y` (the seam inequality with count Y),
  `three_quarters_of_frobenius_seam` (FrobeniusFourThirds ∧ Seam43 Y ⇒ (3/4−ε)N ≤ Y), `seam43_N0star`
  (block structure), `seam43_N0simple` (multiplicity-aware block structure), `zeta_three_quarters_of_frobenius`
  (now a corollary), `zeta_three_quarters_simple_of_frobenius`, `zeta_three_quarters_simple_cumulative_of_frobenius`,
  `zeta_three_quarters_simple_of_pair_correlation`. Compiles, `lake build` ok, axioms [propext,
  Classical.choice, Quot.sound], lint clean, no name collisions.
- Meaning: any proof of PairCorrelationFourThirds proves ≥ 3/4 simple zeros, a statement that pair correlation
  on [0,1] cannot give (cap ≈ 0.6727 for simple zeros) even with RH assumed. The route's input is therefore
  at least as strong as a simple-zero theorem beyond the RH-conditional pair-correlation range.
- The ζ goal (75%) is still not met.

## Cycle 111 (2026-10-13) — Levinson left-strip credit and large-bandwidth traces: both killed

Corpus (search "Levinson zeros of V left of critical line Littlewood"): LevinsonDetectorDefectCount
(`two_pi_mul_offLine_add_multiplicityDefect_le_levinsonBoundary`: budget ≥ 2π(1/2−σ₀)(N_right(ξ) + on-line
multiplicity defect), λ(½log(T/2π)+1/20) < 1), LevinsonDetectorRightCount (`exists_xi_zero_disk_of_levinsonG_eq_zero`:
right zeros of ζ+λζ' lie in Speiser disks). Nothing localizes left zeros of the detector.

**C116 (Levinson credit for left detector zeros in the strip (σ₀, ½)):** Littlewood's sum counts every zero of
G = ζ + (κ/L)ζ' right of σ₀ = ½ − R/L; on-line zeros of ζ produce left G-zeros, and if these sit inside the
strip they add credit, which together with AF's pair budget would beat both bounds.
- Displacement law (paper, regular configuration): with ζ'/ζ = ξ'/ξ − L/2 + o(1), the G-zero attached to an
  on-line zero of a picket fence of spacing 2π/L lies at Lx = log(1/(1−κ)) left of the line
  (coth(Lx/2) = 2/κ − 1); for κ ≥ 1 there is no attached zero on that horizontal line. Hence regular on-line
  zeros give credit only if κ < 1 − e^{−R} (≈ 0.73 at R = 1.3). Credit comes only from irregular
  neighbourhoods (close neighbours), and pointwise localization of left G-zeros is unproved.
- On AF's extremal configuration (orthogonal on-line zeros + coalesced pairs) the left G-zeros fall outside the
  strip, so Levinson's constraint reads p·R/L ≤ budget with p = N/6 < 0.296N (θ = 4/7). Not binding.
  Verdict: FALSE (no synergy). Survivor: the displacement law Lx = log(1/(1−κ)) (model fact).

**C117 (trace at bandwidth λ ∈ (1,2), Frobenius majorized at bandwidth 1):** the trace is unconditional up to
λ < 2 (`prop_trace_zeta_wide`); majorize K_λ² by M ≥ K_λ² with supp M̂ ⊂ [−1,1].
- The certificate becomes 2 − ∫M̂F over M ≥ 0, M(0) ≥ 1, supp M̂ ⊂ [−1,1] (narrow K_λ forces M to majorize
  a spike at 0): exactly the Montgomery multiplicity LP, optimum ≈ 1.3275 ⇒ value ≈ 0.6725. Verdict: FALSE
  (same LP cap as cycle 113).
- No Lean this cycle.
- The ζ goal (75%) is still not met.

## Cycle 112 (2026-10-13) — the certificate's own average, realizability, and triple consistency: all at the Nyquist wall

Corpus search ("short interval variance primes power saving pair correlation beyond one"): only exponent
bookkeeping (LindelofPivotCoincidences: Ivić's divisor short-interval variance x h^{4/3}), Turán–Kubilius
variance, aperture shift cutoffs. No RH-quality prime variance, no F beyond 1.

**C118 (the specific average is easier):** FrobeniusFourThirds needs only the average over m ≤ X = T^{4/3}
(weight Λ(m)g(log m)/m) of E_m = Σ_h Λ(m+h)W(Th/m), W(u) = e^{−3iu/2}sinc(u/2) with ∫W = 0 (the τ-window
avoids 0, so the mean of Λ(m+h) cancels by itself).
- What remains is Σ_m (Λ(m)/m)g(log m)E_m = HL secondary term + error, with error tolerance (1/18)·log²X;
  trivially |E_m| ≪ H = m/T, so the needed saving is H/log H on average (power saving, H up to T^{1/3}).
  The 1/m weight only averages F over α ∈ (1, 4/3); averaging over scales gives no extra structure. Sieve
  bounds lose a constant factor of H; MR/almost-all methods save (log)^{−c}. Verdict: FALSE.
- Side note (heuristic, not rigorous): RH-quality variance at x^{1/4} forces N(½+δ, T) ≪ T^{1−(8/3)δ}log T
  (zeros at β = ½+δ contribute H²x^{2δ−1}N(½+δ,T)), a near-line density exponent 8/3 > 2. The input is
  therefore beyond density-hypothesis strength near the line.

**C119 (point-process realizability cuts the LP cap 0.6725):** actual zeros form a point set with integer
counts, so (n_I − k)(n_I − k − 1) ≥ 0, and similar constraints for differences of counts, hold beyond F̂ ≥ 0.
- All such integrality constraints are lower bounds on averages of F against nonnegative kernels
  (E n_I² and E(n_I − n_J)² have kernels sinc²·(…)² ≥ 0). The adversary's extra mass beyond α = 1 only helps
  satisfy them. Verdict: FALSE (realizability cannot exclude the spike at 1⁺; SDP-type refinements move the
  cap by ~10⁻⁴).

**C120 (triple correlations in the Rudnick–Sarnak range exclude the spike):** a pair density modulation
c·cos(2πx) (spike at α = 1⁺) should leave a 3-point signature.
- Its leading 3-point frequency triple is (1⁺, −1⁺, 0), with Σ|ξ| = 2⁺, just outside the RS range Σ|ξ| < 2;
  marginal consistency of the 3-point and 2-point functions lives on ξ₃ = 0, |ξ₁| < 1. Verdict: FALSE
  (the spike is invisible to all known n-level data; the RS boundary coincides with the Nyquist wall).
- Big-picture law: every unconditional statistic about ζ zeros — pair (α < 1), n-level (Σ|ξ| < 2), positivity,
  integrality, families (Hooley range) — stops exactly where the spike adversary lives. 75% needs the first
  statistic that crosses α = 1.
- No Lean this cycle.
- The ζ goal (75%) is still not met.

## Cycle 113 (2026-10-13) — the mollifier wall: the CGG–AF hybrid needs two open cores; Kac–Rice counting killed

Corpus (search tool): mollifier second moments (InghamMollifierSecondMoment, MollifiedTwistedMeanValueError,
ZetaOffLineFirstMomentMollifierCredit — Littlewood with mollifier-zero credit), Kloosterman/Kuznetsov
infrastructure (KuznetsovOppositeSign, `large_sieve_spectral`, BourgainDoubleLargeSieve), and the
Deshouillers–Iwaniec input only as a Prop interface (`MTDeshouillersIwaniecBound`). Nothing beyond θ = 4/7.

**C121 (75% reduced to a divisor-type input via the CGG–AF hybrid):** unconditional holomorphic CGG
(x_ρ = ζ'M(ρ), S₁ = Σ x_ρ, S₂ = Σ x_ρ·conj x_{1−ρ̄}, both evaluable by residues over all zeros) gives
N₀ˢ ≥ |S₁ − Σ_off x_ρ|² / (S₂ − Σ_pairs 2Re(x_ρ x̄_{ρ*})); coalesced pairs drop out (x_ρ → 0), so CGG kills AF's
extremal, while AF's Frobenius penalizes non-coalesced pairs (∝ y²).
- Isolated-pair model (κ = σ = 1): constraints π ≤ 1/(6 + 24a²) (AF) and (1 − 2π)(1 + 8a²π) ≥ r_CGG.
  At r_CGG = 0.742 (θ = 4/7) the adversary reaches π ≈ 0.145 ⇒ r ≈ 0.71. 3/4 forces π ≤ 1/8, which needs
  r_CGG ≥ 0.8125 ⇔ θ ≈ 0.75 by the CGG law 1 − (1+θ)^{−3}.
- Open cores: (i) bilinear twisted second moments of ζ' at θ ≈ 0.75 (divisor-type; Conrey/DI stop at 4/7);
  (ii) a rigorous bound for Σ_off |ζ'M(ρ)|² in terms of AF's geometric penalty (needs ζ' at off-line zeros
  as a function of zero geometry; sub-mean-value bounds give O(1)·S₂ with unspecified constant; the
  fourth-moment route needs M₄ at zeros, heavy-tailed). (ii) has no known technique.
  Verdict: BLOCKED (not CIRCULAR: (i) is divisor-type, (ii) a zero-side value problem). Consistent with cycles
  11, 21 (threshold θ ≈ 0.67–0.75 depending on κ).

**C122 (Kac–Rice / Banach indicatrix):** N₀ ≥ (1/2ε)∫1_{|Z|<ε}|Z'| − 2#{critical points of Z with |Z| < ε}.
- Both terms are density-level small-value statistics of (Z, Z'); Selberg's CLT controls log|Z| only at scale
  √(log log T). The critical points with small |Z| are exactly the coalesced pairs (|Z| ≍ y² there).
  Verdict: FALSE (same spike, different coordinates).
- Insight (paper): locally Z(t₀+u) ≈ Re Σ_n a_n e^{iu(θ' − log n)} has flat spectral density on [0, Λ],
  Λ = ½log(t/2π); a Gaussian process with that spectrum has Rice zero density Λ/(π√3), i.e. only
  1/√3 ≈ 57.7% of ζ's zero density. Second-order (Gaussian) information about Z alone cannot explain a large
  on-line proportion; the multiplicative (Euler-product) structure is what puts zeros on the line.
- No Lean this cycle.
- The ζ goal (75%) is still not met.

## Cycle 114 (2026-10-13) — the rank–trace inequality is not sharp in Q₋: credit c·tr Q₋ (Lean); core (ii) stays open

**C123 (refined counting step):** the Alpöge–Furman/Zeta23 rank–trace inequality
c·trP − (c²/4)r + 2c·trQ − c²b ≤ ‖P+Q‖² loses c·tr Q₋. Its proof pairs eigenvalues p of P with m of Q₋ and uses
(p−m)² ≥ cp − c²/4 − 2cm; the sharp pointwise bound is (p−m)² ≥ cp − c²/4 − cm (difference (p−m−c/2)²;
for p = 0, m² ≥ −cm).
- Lean (RHTower/RankTraceNegativePartCredit.lean, new): `sum_sq_diff_lower_sharp`, `rank_trace_ineq_negPart`
  (c·trP − (c²/4)r + 2c·trQ − c²b + c·tr Q₋ ≤ ‖P+Q‖²), `rank_trace_ineq_two_negPart`, `zeroside_rank_core_negPart`
  (4 tr Â − 2N − ‖Â‖² + 2 tr Q₋ ≤ rank P), `rtrace_hermNegPart_nonneg`. Compiles, `lake build` ok, axioms
  [propext, Classical.choice, Quot.sound], lint clean, unique names, wired after PairCorrelationMixtureWindow.
  Corpus check (search tool): both rank–trace copies (Zeta23 RHLinalg, HTGeometry RiemannGaussian.HermitianRankTrace)
  have only the non-sharp form.
- Meaning: each off-line pair is charged 1 + its negative-part trace: p + tr Q̂₋ ≤ (c−1)N/2. For a block
  2(aaᵀ − bbᵀ) with a ⊥ b, tr Q₋ = 2‖b‖² ∝ (displacement · L)². So configurations attaining AF's bound must have
  tr Q̂₋ = o(N): their off-line pairs coalesce in aggregate. The credit does not move the proportion (the
  adversary coalesces), but it is the exact geometric penalty a hybrid needs on the AF side.

**C124 (core (ii) of C121: CGG pair cost ≤ K · AF credit):** pointwise FALSE — the CGG cost of a pair at
displacement y is ≈ y²|ζ''M(s₀)|² (local model), its AF credit ≈ y²L²σ_φ²; the ratio |ζ''M|²/(L²·mean) is a
local value of the mollified function and is unbounded over configurations. Averaged control needs the fourth
moment of ζ'M at zeros (cycle 100: heavy-tailed, unknown). Verdict: OPEN core, no technique.
- The ζ goal (75%) is still not met.

**C125 (averaged core (ii) via segment mean value + Hölder):** for a reflected pair ζ(ρ) = ζ(ρ*) = 0 gives
∫_{ρ*}^{ρ} ζ' = 0, hence |ζ'M(ρ)| ≲ 2y·sup_{segment}|(ζM)''| + (mollifier variation); sub-mean-value on discs of
radius ≍ 1/L and Hölder give Σ_off |x_ρ|² ≲ (Σ y⁴L⁴)^{1/2}·(local fourth moments of (ζM)'')^{1/2}.
- The fourth moment must be taken with the CGG mollifier itself (length θ ≈ 0.75 for 3/4), but mollified/twisted
  fourth moments are controlled only for twist length < 1/4 (Hughes–Young/BBLR range; cycle 100). Without the
  y-factor (pure size bound) the cost is ≍ √(p/N)·S₂, which does not vanish for coalesced pairs.
  Verdict: FALSE (horizon mismatch 0.75 vs 1/4). The CGG–AF hybrid stays BLOCKED at both cores.

## Cycle 115 (2026-10-13) — the CGG–AF hybrid with the sharp credit: rigorous on coalesced pairs, broken by concentration

Corpus (search tool): unmollified fourth moment (Ingham, SmoothAFEZetaSquareInghamCriticalMoment), mollified
mean-square gates (ZetaOffLineMomentSelberg*), MollifiedTwistedMeanValueError; no mollified moment of order > 2.

**C126 (sharp credit + Selberg near-line density, corpus `exists_selberg_nearLine_zeroDensity`):** density
bounds pairs at displacement u/L by e^{−κu}N; the AF adversary uses u → 0. Verdict: FALSE (trivially).

**C127 (rigorous CGG–AF hybrid):** G = ζM, x_ρ = G'(ρ) (= ζ'M(ρ) at zeros). Exact lemma (paper): for a reflected
pair G(ρ) = G(ρ*) = 0, |ρ − ρ*| = 2y, G'(ρ)(ρ − ρ*) = ∫_{ρ*}^{ρ}(G'(ρ) − G'(s))ds gives |G'(ρ)| ≤ y·sup_{[ρ*,ρ]}|G''|.
With the sub-mean-value inequality on discs of radius ≍ 1/L, Σ_{pairs}|x|² ≤ (L²/π)∫∫ w|G''|², w = Σ y_ρ²1_{D_ρ}.
- Coalesced pairs (yL ≤ ε, bounded overlap) cost ≤ (8c₃/c₂)Kε²·S₂: CGG handles AF's extremal rigorously, given the
  unconditional holomorphic moments S₁, S₂ (residue evaluation over all zeros, as in CGG without the RH step).
- Model with sharp credit (flat window: pair cost 1 + a²/6, a = yL; CGG relative cost (2/π²)κ a² per pair):
  AF: r ≥ 2/3 + z/3, CGG: r ≥ r_C/(1 + (2/π²)κ z), z = Σ_B a²/N. κ = 1: θ = 1/2 (r_C = 19/27) ⇒ ≈ 0.693;
  θ = 4/7 (0.742) ⇒ ≈ 0.720; 3/4 needs r_C ≥ 0.7875 ⇔ θ ≈ 0.68.
- Kill: κ is a local mean square of G'' and the adversary concentrates the non-coalesced pairs on the large-value
  set of G'': δN pairs with κ ≈ 1/δ (allowed by the second moment alone) make the CGG cost ≈ 0.2a² while AF gains
  only z = a²δ ≈ 0, so the bound falls back to 2/3. Excluding concentration needs Σ κ^{1+η} ≪ N, i.e. a mollified
  moment of order > 2 at the CGG length (θ ≥ 1/2); mollified/twisted fourth moments are known only for twist
  length < 1/4, and Hölder interpolation needs the same fourth moment. Verdict: FALSE with current inputs.
- Survivor (CANNOT law): any CGG-type hybrid needs (a) holomorphic CGG moments at θ (θ = 1/2 proven-type for 0.69,
  ≈ 0.68 for 3/4) AND (b) a mollified moment of order 2 + η at the same θ. (b) is the binding obstruction even for the
  0.69 record.
- No Lean this cycle.
- The ζ goal (75%) is still not met.

**C128 (bound the pair costs by a large sieve over zeros):** the pairs' CGG cost satisfies
2Σ_B cost ≤ Σ_all|G'(ρ)|² − S₂ (non-holomorphic sum over all zeros minus the holomorphic one); a sampling
inequality Σ_ρ|G'(ρ)|² ≤ (1 + η)S₂ would settle core (ii) with no moments above 2.
- Kill: G = ζM has local spectral width (1 + θ)·(L/2π)-Nyquist (Z spans [−Λ, Λ], M adds θ log T). The sharp sampling
  constant for a zero set on Paley–Wiener functions of that bandwidth is the upper frame bound of the zeros at
  bandwidth 1 + θ, i.e. ‖Ĝ_{1+θ}‖_op ≥ ‖Ĝ_{1+θ}‖_F²/tr — pair correlation up to α = 1 + θ. Verdict: CIRCULAR.
- Insight (unification): in every moment method the mollifier of length θ pushes the detector's bandwidth to 1 + θ,
  so controlling off-line zeros inside the method needs pair-correlation-type information up to α = 1 + θ. The
  mollifier wall (θ) and the Nyquist wall (α = 1) are the same wall seen from two sides; without a mollifier
  (θ = 0, bandwidth exactly Nyquist) the frame bound is available but CGG degenerates (ratio ≍ 3/L).

## Cycle 116 (2026-10-13) — the spike at α = 1⁺ is a Gram-lattice lock; sieve controls it only within log log T/log T

Corpus scan (search tool, "proportion of zeros on the critical line", "form factor beyond Nyquist"): no ζ result above
0.6725 (XiCriticalScaleDiscSeamProportion uses Montgomery–Taylor HD(1); HorizontalSingletonFiberCharging ≥ 0.628;
ZeroLatticeDepthNyquistLaw: off-line lattice configurations are invisible at bandwidth ≤ Nyquist). No F beyond 1.

**C129 (γ ↦ −γ symmetry + trace up to bandwidth 2 constrains the jump of F at 1):** cross pairs (γ, −γ') sit at
γ + γ' ≈ 2T, far from the diagonal; the 1-level density at a point t₀ is mean + P_X(t₀), whose mean square is pair
correlation beyond 1. Verdict: FALSE.

**C130 (chirp statistics):** since 2θ'(t) = log(t/2π), e^{2iκθ(γ)} ≈ (t/2π)^{iκγ}: local chirp sums over zeros probe F
at α = κ. Explicit formula + stationary phase (2κθ'(u) = log n ⇔ n = (u/2π)^κ; at κ = 1 the phase 2θ(2πn) − 2πn log n
= −2πn − π/4 is constant):
- Σ_{γ near t} e^{2iκθ(γ)}w ≈ −c·Σ_{n near (t/2π)^κ} Λ(n)·(smooth weight), over an n-interval of length
  H ≍ κ(t/2π)^{κ−1}W for a t-window of width W.
- κ = 1: H ≍ W bounded — the local lock of zeros to the Gram lattice is a sum of Λ over O(W) integers near t/2π.
  Its mean square is W log T (diagonal) + O(W²) (Selberg-sieve upper bound for Λ(n)Λ(n+h), h < W), so the average of
  F over |α − 1| ≲ 1/(W log T) is ≤ 1 + O(W/log T): no spike of positive mass within O(log log T/log T) of 1.
- κ > 1: H = x^{1−1/κ}W ≫ log x, the Goldston–Montgomery short-interval variance; sieve constants > 1 leave
  (C−1)H² ≫ H log x. Verdict: FALSE beyond α = 1 + O(log log T/log T) (gain o(1)).
- Structural meaning (survivor, paper): a spike of F at 1⁺ is a coherent offset of the zeros relative to the Gram
  lattice θ(t) ∈ πℤ; its unconditional exclusion holds exactly as far as sieve bounds on primes in intervals of length
  O(log x) reach. The wall α = 1 is the transition from bounded prime gaps (sieve-controllable) to power-length intervals.
- No Lean this cycle.
- The ζ goal (75%) is still not met.

## Cycle 117 (2026-10-13) — renormalization loop circular; holomorphic detection forces negative pair cost

**C131 (renormalization across heights):** F(α) at height T ↔ variance of primes at x ≍ T^α in intervals
H = x^{1−1/α} (chirp/Goldston–Montgomery) ↔ (explicit formula for ψ(x+H) − ψ(x)) zeros up to height x/H = T with
weight x^{i(γ−γ')} = T^{iα(γ−γ')}. The loop returns to the same height and the same α: it is an identity, not a
map between different (height, α). Verdict: CIRCULAR.

**C132 (sign-definite holomorphic detector):** look for holomorphic x with reflection pairing x̃_ρ = conj x(1−ρ̄)
such that on-line zeros contribute |x_ρ|² ≥ 0 and coalesced off-line pairs contribute ≥ 0, so that the
Cauchy–Schwarz denominator Σ_on|x|² ≤ S₂ holds without off-line control.
- Dichotomy (paper): a reflected pair at ρ = s₀ ± y contributes 2Re(x(ρ)·conj x(ρ*)). If x does not vanish at
  zeros, x(ρ*) → x(ρ) and the pair contributes +2|x|², i.e. it counts as a double on-line zero (no detection). If
  x = G'·h with G vanishing at the zeros, x(ρ*) = −x(ρ) + O(y²) and the pair contributes −2|G''h|²y² + O(y³) < 0.
  By continuity no holomorphic x does both. Verdict: FALSE.
- Law: in holomorphic (explicit-formula or residue) statistics, *detection of coalescence costs a negative pair
  term*, so moment methods need non-holomorphic control of Σ_off|x|² (cycle 115: frame bounds at bandwidth 1 + θ,
  or moments of order > 2 at length θ).
- Consolidated barrier: every gain over 0.6725 needs (P) prime-pair correlations beyond α = 1 (power-saving HL in
  intervals x^{1−1/α}), or (M) mollified moments of order > 2 at mollifier length ≥ 1/2 together with CGG second
  moments at θ ≈ 0.68. Both are open; (M) is divisor-type.
- No Lean this cycle (no formal target that is not an already-known lemma or a model computation).
- The ζ goal (75%) is still not met.

## Cycle 118 (2026-10-13) — input (M) attacked: log-moments, gap statistics, convexity all give only polynomial tails

Target (from cycle 115): exclude δN non-coalesced off-line pairs with local curvature factor κ ≍ 1/δ
(κ_ρ ≍ |(ζM)''(s₀)|²/(L⁴·mean)); this needs Σκ^{1+η} ≪ N, i.e. P(κ ≥ V) = O(V^{−1−η}).

**C133 (Selberg's unconditional fixed-order moments of log ζ − P, via near-line density):** Gaussian-type moments of
log|ζM| of every fixed order give P(log κ ≥ u) ≪_k u^{−2k}; concentration needs P(κ ≥ 1/δ) ≥ δ, which is allowed since
(log 1/δ)^{−2k} ≫ δ. Exponential moments of log κ = moments of κ are required. Verdict: FALSE.

**C134 (large curvature ⇒ big gap, excluded by known number variance):** κ_ρ is large iff the pair sits in a large gap
(|C| = ½|ζ''(s₀)| is the product over the other zeros); a gap of g mean spacings gives log κ ≍ g log g. Known pair
correlation on [0,1] gives Var(n_I) ≍ (1/π²)log g, so P(gap ≥ g) ≪ log g/g² (Chebyshev) — polynomial, while
κ ≥ 1/δ needs only g log g ≍ ½ log(1/δ), probability ≫ δ. Verdict: FALSE.

**C135 (Gabriel/Hardy–Ingham–Pólya convexity in σ):** interpolating the mollified mean square at σ₁ = ½ − a/L with
sup|ζM| ≤ C on σ₂ = 1 + ε gives exponent 2 + O(a/L) only; a constant η needs σ₁ = ½ − c, where |ζ| grows like t^c.
Verdict: FALSE (η ≍ 1/log T).
- Summary: (M) needs exponential (large-deviation) control of the mollified log|ζM| at mollifier length ≥ ½, i.e. a
  mollified moment of order 2 + η; all unconditional tools give polynomial tails or η ≍ 1/log T.
- No Lean this cycle.
- The ζ goal (75%) is still not met.

## Cycle 119 (2026-10-13) — restricted Weil positivity and local Hermite forms: both blind at the zero spacing

Corpus (search tool "Weil positivity small support Yoshida…"): CCMRestrictedWeilStrictApertureClosure
(restricted Weil quadratic form, apertures), WeilFullConeCCMBridge, WeilPositivityLogDensityMaximality,
GaussianPositivityCertificate (Gaussian explicit formula ⟺ RH, prime-energy budgets).

**C136 (positivity of the Weil form on test functions of support ≤ a feeds the sharp rank–trace credit):** support
≤ a (fixed) involves only primes ≤ e^a, so the positivity is a finite arithmetic identity; the Gram kernel |f̂|² then
has width ≍ 1/a ≫ 1/log T and averages over ≍ log T/a zeros. A reflected pair at displacement y ≪ 1/a contributes
like a double on-line zero; only pairs with y ≳ 1/a can produce negativity (zero-density territory). The rank–trace
certificate needs support ≍ log T. Verdict: INSIGNIFICANT.

**C137 (local Hermite/Schur–Cohn forms with exactly computable entries):** with z = t + ic, the Hermitian form
Σ_ρ h(γ_ρ)·conj h(conj γ_ρ), h = Σ_j x_j(γ − z)^{−j}, has on-line zeros PSD and reflected pairs of signature (1,1); its
entries are partial-fraction combinations of (log Ξ)^{(m)}(z) and (log Ξ)^{(m)}(z̄), i.e. absolutely convergent prime
sums when c > ½ — no averaging over t needed.
- Resolution: |γ − z|^{−j} has width ≍ c/√j, so resolving the spacing 1/log T needs j ≍ c²log²T, and the signature
  of a d ≍ log²T form must be controlled for every t ∈ [T, 2T]. Pointwise in t this is Turing-type local
  verification; uniform control in t needs moments again. With c ≍ 1/log T the entries are dominated by nearby
  zeros (circular). The Fourier weight e^{−c|u|} = T^{−cα} sees F only near α = 0. Verdict: FALSE.
- No Lean this cycle.
- The ζ goal (75%) is still not met.

## Cycle 120 (2026-10-13) — the open input reduced to the prime-pair surplus (Lean)

**C140 (survivor, formalized):** at bandwidth 4/3 every part of the Frobenius norm except the prime-pair surplus is
unconditional, with total exactly 43/36 of the normalisation; 75% follows from "surplus ≤ 1/18".
- Lean, RHTower/ZetaFrobeniusSurplusSplit.lean: `ppDiag`, `ppOffDiag` (Σ_{n≠m≤X} a_n a_m A⁻(log n, log m)), `ppSumFreq`
  (Σ a_n a_m A⁺), `frobSurplus` = (1/2π²)(𝒪₁ + 𝒪₂) + 2𝓜[P_X,Π_X] + E(ν_X,ν_X); `trGt2Nu_nuX_split` (exact identity at every
  bandwidth: tr G̃² = 𝓜[μ,μ] + (1/2π²)𝒟 + 2𝓜[μ,P] + 2𝓜[μ,Π] + 𝓜[Π,Π] + 𝒮), `trGtildeSq_eq_split` (params43).
- Lean, RHTower/ZetaThreeQuartersOfSurplus.lean: `diagonal_main_le` ((TL/2π)(ℓ₁² + L²/3) ≤ (43/36 + ε/2)(aL)²Tℓ₁/2π for
  l ≥ 14/ε), `sumA2g_le_wide`, `sum_acoef_sq_le_wide`, `diagonal_part_le` (unconditional: the non-surplus part ≤
  (TL/2π)(ℓ₁² + L²/3) + K·Tl² + K'·log²T·T^{2/3}, via wide mumu/cross, Stirling ∫μ², Chebyshev–Mertens, |Π_X| ≤ 3√X/T),
  `SurplusFourThirds` (∀ε, eventually 𝒮 ≤ (1/18 + ε)(aL)²Tℓ₁/2π), `one_sub_le_a_params43`, `frobeniusFourThirds_of_surplus`,
  `zeta_three_quarters_of_surplus`, `zeta_three_quarters_simple_of_surplus`.
- All compile, `lake build` ok, axioms [propext, Classical.choice, Quot.sound], lint clean, unique names, wired after
  RankTraceNegativePartCredit.
- Meaning: the open input is now an explicit arithmetic statement — the off-diagonal prime pairs n ≠ m ≤ T^{4/3}
  (|log n/m| ≲ 1/T), the sum frequencies, the prime–pole cross term and the grid end correction together contribute at
  most 1/18 of (aL)²Tℓ₁/2π. Random-matrix prediction for 𝒮: −1/144 (margin 1/16). The diagonal value 43/36 at λ = 4/3 is a
  theorem.
- The ζ goal (75%) is still not met: SurplusFourThirds is open (prime-pair correlations beyond α = 1).

## Cycle 121 (2026-10-13) — the prime–pole cross term is negligible at every bandwidth (Lean); open input = prime surplus

**C141 (survivor, formalized):** |𝓜[P_X, Π_X]| = O(X/(T δ) + log X·Xδ) for every resonance width δ, hence O(T^{5/6} log² T) at
X = T^{4/3}, δ = T^{−1/2} — negligible against T log³ T, unconditionally (only Chebyshev Σ Λ(n)/√n ≤ 3√X).
- Paper: Π_X(τ) = (√X/π)(τ sin(τ log X) + ½cos(τ log X))/(¼ + τ²) (the constant terms cancel exactly); integration by parts
  against the decreasing amplitudes t/(¼+t²), (¼+t²)⁻¹ bounds |∫ cos(τy + φ)Π_X| ≤ (3√X/2πT)(1/(log X + y) + 1/|log X − y|)
  on every subinterval of [T, ∞); the shear form 𝓜 = ∫Φ(x)² ∫_{Ix} … transfers it to 𝓜[cos(·y+φ), Π_X]; primes with
  log n < log X − δ use it, the resonant ones (n > Xe^{−δ}, at most Xδ + 1 of them, each a_n ≤ 2 log X/√X) the trivial bound.
- Lean, RHTower/ZetaPrimePoleCross.lean: `PiX_eq_closed`, `abs_integral_mul_sin_antitone_le` (|∫ h sin(ωt+φ)| ≤ 2h(a)/|ω| for
  decreasing h ≥ 0), `hasDerivAt_amp₁/₂`, `cos_mul_PiX_eq`, `abs_integral_cos_mul_PiX_le`, `abs_Mform_cos_PiX_le`,
  `Mform_PX_left_eq_sum`, `abs_Mform_PX_PiX_le` (|𝓜[P_X,Π_X]| ≤ (∫Φ²)/π·(9X/(πTδ) + 6 log X (Xδ + 1))).
- Lean, RHTower/ZetaThreeQuartersOfPrimeSurplus.lean: `primeSurplus` = (1/2π²)(𝒪₁ + 𝒪₂) + E(ν_X,ν_X),
  `frobSurplus_eq_primeSurplus`, `PrimeSurplusFourThirds`, `abs_Mform_PX_PiX_params43_le` (2|𝓜[P,Π]| ≤ (320/3)log²T·T^{5/6}
  eventually), `surplusFourThirds_of_primeSurplus`, `zeta_three_quarters_of_prime_surplus`,
  `zeta_three_quarters_simple_of_prime_surplus`.
- All compile, `lake build` ok, axioms [propext, Classical.choice, Quot.sound], lint clean, unique names, wired after
  ZetaThreeQuartersOfSurplus.
- The open input is now: off-diagonal prime pairs 𝒪₁, sum frequencies 𝒪₂ and the grid end correction E at bandwidth
  4/3 total ≤ (1/18 + ε)·(aL)²Tℓ₁/2π. 𝒪₂ and E are boundary terms (values of P_X near T and 2T); 𝒪₁ is the genuine
  prime-pair correlation beyond α = 1.
- The ζ goal (75%) is still not met.

## Cycle 122 (2026-10-13) — the remaining surplus: two boundary terms and the true obstacle

**Structure of 𝒪₂ (paper, from Zeta23's kernel):** A⁺(y,y') = ∫_{|x|≤T}Φ(x)² Jker(y+y', xy, α(x), β(x)) with
Jker = [sin((y+y')β + xy) − sin((y+y')α + xy)]/(y+y'), α(x) = max(T−x, T), β(x) = min(2T−x, 2T). So 𝒪₂ is a boundary
form: with 1/log(nm) = ∫₀^∞(nm)^{−u}du it is an integral over u of products of twisted prime polynomials
Σ_n a_n n^{−u+iκT} H(log n) evaluated at κ = 1, 2 (the window edges). Pointwise in T only |Σ a_n| ≤ 3√X is available
(𝒪₂ ≲ X/log X ≫ T log³T at X = T^{4/3}); on average over the window position the mean value theorem gives
≍ (1 + X/T)log²X = T^{1/3}log²T, negligible. The end correction E behaves the same way (Zeta23's lem_ends uses
sup|ν| ≍ √X). Both are artefacts of the sharp window [T, 2T]; a smooth taper of the grid weights removes them.

**C142 (Matomäki–Radziwiłł–Tao averaged Hardy–Littlewood):** at X = T^{4/3} the relevant shifts are h ≤ H = X/T = X^{1/4},
inside the MRT range H ≥ X^{8/33+ε} (8/33 < 1/4). MRT gives Σ_{n≤x}Λ(n)Λ(n+h) = 𝔖(h)x + O(x log^{−A}x) for all but
O(H log^{−A}) shifts. The surplus needs the smoothly weighted average error over h ≤ H to be ≪ x log x/H = x^{3/4}log x per
shift: a power saving x^{−1/4}, with no exceptional set. Verdict: FALSE (log-power savings + exceptional shifts).
Survivor: the exact strength needed — averaged Hardy–Littlewood in the shift range H = x^{1/4} with power saving
x^{−1/4}, i.e. RH-quality variance (cycles 99, 112).

**C143 (dual Montgomery–Hooley at moduli ≍ x^{3/4}):** the short-interval variance is the q = 1 major arc only;
Montgomery–Hooley averages over all q ≤ Q and is unconditional only for Q ≥ x(log x)^{−A}; isolating q = 1 is the family
isolation already shown circular (cycle 18, 91). Verdict: CIRCULAR.

- Plan recorded: a weighted-grid (smooth taper) version of the counting step would turn PrimeSurplusFourThirds into
  a statement about the smoothly weighted off-diagonal prime pairs only. First formal step: the weighted rank–trace
  counting inequality (congruence D P D, weighted trace and weighted pair count).
- No Lean this cycle.
- The ζ goal (75%) is still not met.

## Cycle 123 (2026-10-13) — anatomy of 𝒪₁; positivity forces the excess where the certificate looks; density shadow

**C144 (excess-mass law, paper):** for a configuration whose zeros carry diagonal mass D = Σ m²/N = 1 + f (f = fraction
in coincident or coalesced sites) and F(α) = α on [0, 1], the pair density at 0⁺ is ρ₂(0⁺) = 2 − 2D + 2∫₁^∞(F − D)dα, so
ρ₂ ≥ 0 forces ∫₁^∞(F − D) ≥ f. The base density ρ₂_base(x) = 1 − sinc²(x)·… − f·sin(2πx)/(πx) is negative on
[0, x₁(f)), x₁ ≈ √(6f)/π (≈ 0.45 at f = 1/3), so the excess must be a positive bump of width ≍ x₁ in x, i.e. spread
over α ≲ 1/x₁ ≈ 2.2 — inside (1, s) for every useful bandwidth s. Constant F = B > 1 beyond 1 is not admissible.
Meaning: off-line coalescence and large F just beyond 1 are the same phenomenon; no certificate can separate them
without upper bounds on F there. Verdict: survivor (structural), no new bound.

**C145 (𝒪₁ decomposition, paper):** with G = g(y) + g(y'), Δ = H(y') − H(y) (H the half-line sine transform of Φ²),
A⁻(y,y') = πG·[sin 2Tθ − sin Tθ]/θ + Δ·[cos 2Tθ + cos Tθ]/θ, θ = y − y'. The first part summed over n ≠ m is
2π∫_T^{2T} Re[P_g(τ)·conj P(τ)]dτ − 2πT Σ a_n² g(y_n) (P_g = Σ a_n g(log n) n^{iτ}); the second is another window-edge
term. So the genuine open core is the mean value over [T, 2T] of the product of two prime Dirichlet polynomials of
length X = T^{4/3}, to precision (1/18)·T log³T against a trivial error X log X: a power saving T^{−1/3} beyond the
Montgomery–Vaughan range. Heath-Brown/Vaughan decompositions turn it into binary additive problems (prime pairs
averaged over shifts h ≤ X/T), where only log savings are known (C142).

**C146 (density shadow, heuristic):** the sharp counting step (cycle 114) gives ‖Ĝ‖² ≥ N + 2 tr Q̂₋; a pair at
displacement y has tr Q₋ ≈ X^{y}/(yL) when pairs are nearly orthogonal. Hence FrobeniusFourThirds would force
N(½ + δ, T) ≪ T^{1 − (4/3)δ} log²T: a near-line density exponent 4/3, beyond the mollifier range (exponent 2θ = 8/7 at
Conrey's θ = 4/7). Rigour needs near-orthogonality of the pair vectors (or the tail machinery run in reverse).
- No Lean this cycle.
- The ζ goal (75%) is still not met.

## Cycle 124 (2026-10-13) — the density/zero-free shadow of the open input: true heuristically, rigour blocked by clusters

**C147 (quasi-RH shadow):** a zero ρ₀ = ½ + y + iγ₀ makes the truncated explicit formula put a bump
−X^{y}e^{i(γ₀−τ)log X}/(y + i(γ₀ − τ)) into P_X(τ) near γ₀, with L²-mass ≍ X^{2y}/y. A Frobenius (mean-square) bound
≍ T log³T at bandwidth λ (X = T^λ) then forces 2λy ≤ 1, i.e. no zeros with β > ½ + 1/(2λ): λ = 1 gives the trivial
β ≤ 1 (consistent with Zeta23), λ = 4/3 gives β ≤ 7/8 + o(1). Conjecture: FrobeniusFourThirds ⟹ ζ(s) ≠ 0 for
Re s > 7/8 (a zero-free strip, unknown today), and with the counting form the near-line density
N(½ + δ, T) ≪ T^{1−(4/3)δ}log²T.
- Supporting identity (paper): with the full-grid Poisson sum, the zero-side Frobenius is
  ∫_{−L}^{L} g(x)|Σ_ρ m_ρ e^{ixγ_ρ}|² dx ≥ 0 (g = φ²⋆φ² ≥ 0; the reflection ρ ↦ 1 − ρ̄ makes Σ e^{−ixγ_σ} the conjugate),
  and a far zero contributes e^{x y} e^{ixγ}, of size X^{y} near x = L.
- Rigour obstacle: other far zeros within ordinate distance ≲ 1 could cancel the bump. Coefficients are positive
  (multiplicities), so coincident or 1/L-close far zeros add constructively, but clusters at mutual distance
  ≍ 1/L … 1 have rotating phases. Known tools: Hilbert/Montgomery–Vaughan inequalities need separation; Turán's power-sum
  and Turán–Nazarov lower bounds lose e^{O(n)} with n ≍ log T terms, i.e. T^{O(1)}. Corpus: no Turán second main theorem.
  Verdict: SURVIVES PRELIMINARY ATTACK as a conjecture (strong hardness witness); [OPEN CORE] a cancellation-free lower
  bound for Σ_ρ m_ρ X^{ρ−s}/(ρ − s) near a far zero.
- No Lean this cycle.
- The ζ goal (75%) is still not met.

## Cycle 125 (2026-10-13) — C147 rigour: only cluster statements; ζ'/ζ mean square near the line is the same input

**C147 attack (paper):** a far zero ρ₀ (β₀ = ½ + y) contributes to the bandwidth-λ Gram block around γ₀ the matrix
2(aaᵀ − bbᵀ) with ‖a‖² ≈ ‖b‖² ≍ X^{y}/(yL) (hat units), whose Frobenius norm ≍ X^{2y}/(yL)² is phase-free (eigenvalues
≈ ±‖v‖²). Single diagonal entries are not usable (the grid offset |γ₀ − τ_k| ≤ π/L rotates φ̂(γ₀ − τ_k − iy)² by up to π).
On-line zeros contribute ≤ L² per entry. Hence FrobeniusFourThirds ⟹ no ISOLATED zero with β > 7/8 + ε (isolated: no
other zero with displacement > y₀/2 within ordinate distance 1). The zero of maximal displacement in a cluster is never
isolated in this sense, so the argument yields only "far zeros come in clusters"; excluding clusters needs a
Turán-type lower bound with ≍ log T terms (loss T^{O(1)}). Verdict: the zero-free-strip implication stays a conjecture;
the isolated version is too weak to formalize usefully.
- Classical comparison: mean values of long polynomials give zero DENSITY (zero detection with mollifier identities +
  large values), not zero-free regions; the conjecture would be a zero-free consequence of a mean-square bound, which
  needs the count of detected points to drop below 1 — exactly the cluster issue.

**C148 (Goldston–Gonek–Montgomery mean square of ζ'/ζ near the line):** ∫_T^{2T}|ζ'/ζ(½ + a/L + it)|² dt is the pair
correlation integrated against a Cauchy-type kernel with Fourier weight e^{−2a|α|}, i.e. F at ALL α (beyond 1 with weight
≈ 1 for small a). An unconditional asymptotic at one fixed a would give averaged F beyond 1. Corpus: only Selberg-type
mean squares and mollified gates (ZetaOffLineFirstMoment*, SelbergNearLineCriticalGateDensity); near the line ζ'/ζ is
dominated by nearby zeros. Verdict: CIRCULAR (equivalent to the open input; GGM's equivalence is RH-conditional).
- Saturation note: cycles 96–125 map every tested mechanism onto one core — mean values of prime Dirichlet polynomials of
  length T^{4/3} over [T, 2T] (equivalently F on (1, 4/3), RH-quality short-interval prime variance), or mollified moments
  above order 2. Formal state: 75% ⟸ PrimeSurplusFourThirds (Lean), everything else unconditional.
- No Lean this cycle.
- The ζ goal (75%) is still not met.

## Cycle 126 (2026-10-13) — Project W, step W1: the weighted counting step (Lean)

**Pivot (from cycle 125):** Project W replaces the sharp grid [T, 2T] by smooth grid weights, so that the window-edge
terms (𝒪₂, the end correction E, the edge part of 𝒪₁) disappear and the open input becomes the smoothly weighted
off-diagonal prime pairs; end goal: averaged power-saving Hardy–Littlewood ⟹ 75% (W6).

**W1 (Lean, RHTower/ZeroSideWeightedCertificate.lean):** `weightBlock` (multiply the k-th coordinate of every evaluation
vector by w_k ∈ ℝ; the reflection symmetry u_{1−ρ̄} = conj u_ρ survives), `weightBlock_blockA_apply` (weighted Gram =
diag(w) A diag(w)), `weightBlock_hPois` (|w_k| ≤ 1 keeps the Poisson trace bound), `weightPairReps`,
`weighted_rank_certificate` (4 tr Â_w − 2N − ‖Â_w‖² ≤ s₁ + s₂ for every |w_k| ≤ 1), all from Zeta23's block lemmas
applied to the weighted data. Compiles, `lake build` ok, axioms [propext, Classical.choice, Quot.sound], lint clean, unique
names, wired after ZetaThreeQuartersOfPrimeSurplus.
- Next (W1b): the ζ instance with tails — Ẽ_w = D Ẽ D keeps the operator-norm bound θ₀, but TailInputs stores only |tr Ê|
  and ‖Ê‖_F; the weighted trace needs the trace-norm bound ‖Ê‖₁ ≤ θ₀/(aL) from inside Zeta23's tail proof.
- Conjecture C149 (cos-modulated weights alias α ∈ (1, 4/3) onto known ranges): modulation shifts the prime side to
  pairs n/m ≈ e^{±c} (fixed ratios), not to near-diagonal pairs, and halves the trace. Verdict: FALSE.
- The ζ goal (75%) is still not met.

## Cycle 127 (2026-10-13) — Project W, step W1b: the weighted seam for ζ (Lean); two kernel conjectures killed

**W1b (Lean, RHTower/ZetaWeightedSeam.lean):** `wmat w M = (w_k w_l M_kl)` with `wmat_add`, `wmat_smul`,
`wmat_isHermitian`, `wmat_vecMulVec`, `hasSum_wmat`; `traceNorm_hat_wmat_Ez_le` (for |w_k| ≤ 1 the weighted tail keeps
‖Ê_w‖₁ ≤ θ₀/(aL): Ê_w = Σ_tail m_ρ (w·u_ρ)(w·u_ρ)ᵀ/(aL²) and ‖w·u_ρ‖ ≤ ‖u_ρ‖, fed to Zeta23's
`traceNorm_le_of_hasSum_vecMulVec` with `TailHyp.hasSum_Ez/summable_tail/tsum_tail_le`); `seamA_weighted`:
4 tr Ĝ_w − ‖Ĝ_w‖² − 2N(T,2T) − 3N(I′∖I) − B₀(4 + 2‖Ĝ_w‖_F + B₀) ≤ N₀*(T,2T), B₀ = θ₀/(aL), for every |w_k| ≤ 1
(window part = weighted block Gram matrix via `weighted_rank_certificate`, tail via the trace-norm bound, assembly via
Zeta23's `four_tr_sub_frobSq_perturb`, `s1_add_s2_le`, `NIprime_eq`, `N0star_lower_explicit`). Compiles, `lake build` ok,
axioms [propext, Classical.choice, Quot.sound], lint clean (only other agents' HTGeometry reachability errors), unique
names, wired after ZeroSideWeightedCertificate. The zero side of Project W is complete.

**W2 design (prime side, paper):** with W_k = w_k² = W(τ_k), the twisted Poisson identity gives
Σ_k W(τ_k) φ̂(τ−τ_k)φ̂(τ'−τ_k) = (L/2π)∫W(s)φ̂(τ−s)φ̂(τ'−s) ds + aliasing, the aliasing coming only from the j = ±1 terms
whose overlap has length |ξ| ≲ 1/width. Hence ‖G_w‖² ≈ (L/2π)²∬W(s)W(s')G(s,s')² (continuous Gram kernel) and the prime
pairs carry the kernel (W²)^(log(m/n)) — sum frequencies decay like (width·log nm)^{−A}, no window edges at all.

**C150 (sign-definite height kernel):** choose W² = ξ₀²g + g'' ≥ 0 so that (W²)^(θ) = (ξ₀² − θ²)ĝ(θ) ≤ 0 for |θ| ≥ ξ₀;
then far prime pairs contribute ≤ 0 and only very close pairs |log(m/n)| < ξ₀ ~ π/T remain, bounded by the sieve
(≤ 4 × Hardy–Littlewood). Attack: Σ_{h∈ℤ}(W²)^(h/n) = 2πn Σ_j W²(2πnj) = 0 exactly (Poisson; W² vanishes at 0 and at
2πnj ≥ 2πT), so the positive part near θ = 0 has mass ≈ (n/T)·(W²)^(0) per n — about X/T = T^{1/3} times the diagonal —
and only cancellation against the negative far part brings the total back to O(diagonal). Dropping the far part (or
bounding the close part by any upper-bound sieve) loses a factor T^{1/3}. Verdict: FALSE.
- Positive content (exact law): for every admissible height weight, the off-diagonal prime-pair form equals
  −(diagonal) + Σ_{h≠0}(𝔖(h) − 1)-type corrections + (prime-pair fluctuation), and the fluctuation is
  n∫|S_Λ(θ)|²W²(2πnθ)dθ over θ ∈ [T/2πn, 2T/2πn] (Gallagher arc of width X^{−1/4}); the Nyquist mass T^{1/3} is the
  quantitative form of the power saving T^{−1/3} required in cycles 101–123.

**C151 (degree-2 lift through ζ_K = ζ·L(·,χ_d)):** the ζ_K certificate at its own bandwidth λ_K < 1 reaches primes up
to (T²)^{λ_K}, i.e. ζ-scale α < 2; subtract the L(χ_d) part and the cross term. Attack: the mean value theorem resolves a
prime pair (n, m) over [T, 2T] iff |log(m/n)| ≫ 1/T, independently of the degree, so Montgomery-type pair correlation of a
degree-d L-function is unconditional only for α_K < 1/d — exactly ζ-scale α < 1 again; the cross term is a χ-twisted
prime-pair sum with the same Nyquist defect. Verdict: FALSE (the wall is the window length, not the conductor).
- The ζ goal (75%) is still not met.

## Cycle 128 (2026-10-13) — W2a: modulated Poisson summation (Lean); arc, Pólya and Bragg conjectures killed

**W2a (Lean, RHTower/ZetaTwistedPoisson.lean, namespace RHTower.TwistedPoisson):** two-window Gabor Poisson summation
`hasSum_paperFT_mul_paperFT_two` (φ₁, φ₂ vanishing outside (−A, A), (−B, B), A + B ≤ 2L:
Σ_{k∈ℤ} φ̂₁(τ−τ_k)φ̂₂(τ'−τ_k) = G(−1) + G(0) + G(1), G(η) = L∫φ₁(u)φ₂(Lη−u)e^{i(τu+τ'(Lη−u)−TLη)}du, generalising
Zeta23's single-window proof: `Gaux2_eq_zero`, `fourier_Gaux2`, Mathlib Poisson at x = 0); overlap bounds
`norm_Gaux2_one_le`, `norm_Gaux2_neg_one_le` (‖G(±1)‖ ≤ L M₁M₂(A + B − L)); `paperFT_shift`
((φ(·+ξ))^(z) = e^{−iξz}φ̂(z)); `hasSum_twisted_phiHat` (|ξ| ≤ L: Σ_k e^{iξτ_k}φ̂(τ−τ_k)φ̂(τ'−τ_k) =
e^{iξτ'}(G_ξ(−1) + G_ξ(0) + G_ξ(1))); `norm_twisted_alias_le` (‖G_ξ(−1) + G_ξ(1)‖ ≤ 2LM²|ξ|); `Gaux2_zero_twist`
(G_ξ(0) = L∫φ(u)φ(ξ−u)e^{i(τ−τ')u}du). Compiles warning-free, `lake build` ok, axioms [propext, Classical.choice,
Quot.sound], lint clean, unique names, wired after ZetaWeightedSeam.
- Consequence for W2: for W(s) = ∫ψ(ξ)e^{iξs}dξ with supp ψ ⊂ [−L, L], Σ_k W(τ_k)φ̂(τ−τ_k)φ̂(τ'−τ_k) =
  ∫ψ(ξ)e^{iξτ'}G_ξ(0)dξ + R, |R| ≤ 2LM²∫|ξ||ψ(ξ)|dξ = O(L/width). Next W2b: the ξ-integration (Fubini of Σ_k and ∫dξ)
  and the weighted trace.

**C152 (circle-method arc):** the open input is n∫|S_Λ(θ)|²W²(2πnθ)dθ on the shell θ ≍ T/X; decompose S_Λ there by the
explicit formula. Stationary phase: zeros with |γ| ≈ 2πθu contribute (γ/2πeθ)^{iγ}, so the shell mean square is
Σ_{γ,γ'≈T} (X/2π)^{i(γ−γ')}k(γ−γ') with k of width O(1): Montgomery's F(log X/log T) = F(4/3) smoothed over an α-window
of width 1/log T. Verdict: CIRCULAR (the shell is exactly F at α = 4/3).

**C153 (Ξ' real zeros / Pólya):** count real zeros of Ξ' (Conrey: ≥ 81% of ξ' zeros on the line) to bound off-line
pairs of Ξ. A coalesced pair γ ± iδ makes Ξ' have a real zero (a local extremum that does not cross); Pólya's inequality
(#non-real zeros of Ξ' ≤ #non-real zeros of Ξ) points the wrong way. The 2/3-extremal (2/3 simple + 1/6 coalesced pairs)
has ≈ N real zeros of Ξ', consistent with 81%. Verdict: FALSE.

**C154 (no Bragg peak beyond 1):** the 2/3-extremal is a decorated crystal (Bragg peak at α = 1); exclude local
crystalline order by linear statistics. Unconditionally Σ_γ w(γ)x^{iγ} = O(√x log) for x = T^{α₀}, α₀ < 2, so
global Bragg peaks are excluded on (0, 2). With a window of length H the prime side runs over [x(1 − 1/H), x(1 + 1/H)],
which Brun–Titchmarsh bounds by O(√x), useful only when (HL)² ≫ T^{α₀/2}. So crystal domains of up to ≈ T^{α₀/4}
zeros with independent phases escape, and they carry an F-spike of any mass. Verdict: FALSE.
- Positive content: linear statistics exclude coherent (global) Fourier structure of the zero set at every frequency
  α log T, α ∈ (0, 2); the spike that blocks 75% must be incoherent (finite crystalline domains, size ≤ T^{1/3}), which
  is a pair-correlation, not a linear, phenomenon.
- The ζ goal (75%) is still not met.

## Cycle 129 (2026-10-13) — W2b: weighted Poisson summation (Lean); three bandwidth conjectures killed

**W2b (Lean, RHTower/ZetaWeightedPoisson.lean):** `summable_norm_phiHat_mul` (Σ_k ‖φ̂(τ−τ_k)φ̂(τ'−τ_k)‖ < ∞ from the
decay (1 + s²)⁻¹, via Zeta23's `isBigO_of_decay`); `hasSum_weighted_phiHat` (ψ integrable, supp ψ ⊂ [−L, L]:
Σ_k (∫ψ(ξ)e^{iξτ_k}dξ)φ̂(τ−τ_k)φ̂(τ'−τ_k) = ∫ψ(ξ)e^{iξτ'}(G_ξ(−1) + G_ξ(0) + G_ξ(1))dξ, interchange by
`hasSum_integral_of_summable_integral_norm`); `continuous_Gaux2_shift`, `norm_Gaux2_shift_le` (‖G_ξ(η)‖ ≤ L²M²),
`integrable_psi_cexp_mul_bdd`; `norm_weighted_sub_main_le` (weighted grid kernel − main term ∫ψ e^{iξτ'}G_ξ(0) has norm
≤ 2LM²∫|ξ|‖ψ‖ — no integrability premises left). Compiles warning-free, `lake build` ok, axioms [propext,
Classical.choice, Quot.sound], lint clean, unique names (helper renamed to avoid a clash with ZeroGapWindowPrimePolynomial),
wired after ZetaTwistedPoisson.
- Main term identity (paper): ∫ψ(ξ)e^{iξτ'}G_ξ(0)dξ = (L/2π)∫W(s)φ̂(τ−s)φ̂(τ'−s)ds, W = ψ^∨; so the weighted Gram
  matrix is the continuous Gram kernel G(s,s') = ∫φ̂(τ−s)φ̂(τ−s')dν(τ) sampled against W, up to O(L/width).
- Next W2c: finite grid k ∈ [0, d) (tail of W outside [T, 2T]), then ‖Ĝ_w‖² = (L/2π)²∬W(s)W(s')G(s,s')² + errors.

**C155 (Selberg S-moments bound the F-spike):** a spike of F at α = 1 + ε needs locally dense crystalline domains of
D ≈ 1/ε zeros with an excess of ≈ 1 zero; Selberg's unconditional moments of S(t+h) − S(t) should cap their frequency.
Attack: the domains live at bounded scale D ≈ 3–10 zeros, where Selberg's asymptotics (main term (1/π²)log(hL), error
O(1)) say nothing; the O(1) term is exactly ∫_1^∞F(α)α⁻²dα/π², i.e. the unknown. Sparse domains (second harmonic in
(1, 4/3)) are excluded by F on (1/2, 2/3), dense ones are not. Verdict: FALSE (agrees with cycle 101).

**C156 (two-bandwidth rank inequality):** rank(P) ≥ |tr(PB)|²/(‖P‖_F²‖B‖_op²) with B carrying a wide linear statistic.
f_B(γ) = u_ρᵀBu_ρ has the bandwidth of P, so B cannot widen it; the optimum B = I gives the usual certificate, B ∝ P
gives the stable rank ‖P‖_F²/‖P‖_op² (cluster-limited). Cross Gram matrices of bandwidths λ₁, λ₂ involve F up to
(λ₁ + λ₂)/2. Verdict: FALSE (a rank bound is limited by its own Frobenius bandwidth).

**C157 (long height window):** a window [T, H] with H = T^{4/3} resolves prime pairs up to X = H. But the local
density at height t is log t/2π, so the relative bandwidth λ log T/log t ≤ 1 for all but a fraction T^{−1/3} of the
zeros. The wall is X ≤ height of the zeros, not window length per se. Verdict: FALSE.
- Structural summary: ζ-based mean values (moments, Levinson, CGG) are limited by mollifier length; ζ'/ζ-based ones
  (explicit formula, Montgomery, Zeta23) by X ≤ t. The Riemann–Siegel length √t keeps ζ-moments diagonal, while ζ'/ζ has
  no approximate functional equation; this asymmetry is why the two walls differ.
- The ζ goal (75%) is still not met.

## Cycle 130 (2026-10-13) — W2c: the weighted prime-side Gram matrix as integrals (Lean); two conjectures

**W2c (Lean, RHTower/ZetaWeightedGramIntegral.lean):** `KfunW` (K_W(τ,τ') = Σ_{k<d} W_k φ̂(τ−τ_k)φ̂(τ'−τ_k)),
`trG2integrandW`, `sum_W_gkl_mul_gkl`, `eq_trG2intW` (Σ_{k,l} W_kW_l G_kl² = ∬K_W²νν', absolute convergence from
Zeta23's `gkl_integrable`), `eq_trG1intW` (Σ_k W_k G_kk = ∫K_W(τ,τ)ν(τ)dτ), `rtrace_hat_wmat_Gp`
(tr Ĝ_w = (aL²)⁻¹Σ_k w_k²G_kk), `frobSq_hat_wmat_Gp` (‖Ĝ_w‖² = (aL²)⁻²Σ_{k,l}w_k²w_l²G_kl²). Compiles warning-free,
`lake build` ok, axioms [propext, Classical.choice, Quot.sound], lint clean, unique names, wired after
ZetaWeightedPoisson. Together with ZetaWeightedPoisson: K_W on the finite grid = (full-lattice weighted sum) − (tail
outside [0, d)) and the full-lattice sum = main term + alias ≤ 2LM²∫|ξ||ψ|.
- Remaining W2 work: (W2d) a concrete weight ψ (W = 1_I ⋆ β_Δ with β_Δ = |ĉ_Δ|² ≥ 0, so 0 ≤ W ≤ 1, ψ supported in
  |ξ| ≤ 1/Δ, ∫|ξ||ψ| ≪ 1/Δ, W ≤ ε outside I); (W2e) tail and alias errors integrated against ν (need decaying bounds,
  since the alias bound is uniform in τ); (W2f) main-term evaluation with ν = μ + Π + P.

**C158 (approximate functional equation for a mollified ζ'/ζ):** replace the explicit formula's prime sum by a short
representation of (ζ'M)/(ζM) so that ζ-type diagonal control enters. Attack: Σ_ρ h(ρ) is the residue sum of hζ'/ζ, and
ζ'/ζ = Σ_{|γ−t|<1}1/(s−ρ) + O(log T) has poles exactly at the zeros being counted; any Dirichlet polynomial of length
T^θ misses them within 1/L, and the mean square of ζ'/ζ at σ = ½ + a/L is the pair correlation at all α (GGM).
Changing to (ζ'M)/(ζM) adds poles at the zeros of M and leaves the residues at ρ unchanged. Verdict: FALSE.

**C159 (zero-adapted Plancherel–Pólya for the CGG damage):** the unconditional CGG damage is Σ_off|(ζM)'(ρ)|² over
off-line zeros, where ζM − 1 =: F has F(ρ) = −1 and small mean square on σ ≥ ½ + c/L. Cauchy plus exponential-type
Plancherel–Pólya give |F'(ρ)|² ≲ r⁻⁴∬_{D(ρ,2r)}|F|², so Σ_off|A(ρ)|² ≲ r⁻⁴∬|F|²·n_off(s) with n_off the local count of
off-line zeros. Clusters of k zeros make F' small at their zeros (|F'| ≲ max|F|·(δ/r)^{k−1}), so clusters at scale
δ ≪ r are harmless; the loss is only for k ≍ log T zeros spread at scale ≈ r = c/L. Verdict: NOT SUFFICIENT — it
replaces the (2+η)-moment by a bound on the |F|²-weighted density of off-line zeros, which is the same concentration
question; the surviving lemma (Σ over zeros of F of |F'|² ≤ C r⁻⁴∬|F|²·n) is standard.
- The ζ goal (75%) is still not met.

## Cycle 131 (2026-10-13) — W2d: a band-limited Fejér window (Lean); the CGG damage localised on the line

**W2d (Lean, RHTower/ZetaFejerWeight.lean, namespace RHTower.FejerWeight):** profile
F_b(v) = ∫_{−b}^{b}Λ_b(ξ)e^{iξv}dξ = (2 − 2cos(bv))/(bv²) (`fejerBandProfile`, `integral_triangle_cexp_eq_profile`, via the
corpus triangle transform `HTGeometry.integral_triangleFn_cexp`), 0 ≤ F_b ≤ b, F_b ≤ 4/(bv²), F_b ≥ (43/48)b on |v| ≤ 1/b
(`Real.cos_bound`), integrable, mass κ_b > 0 (`fejerMass_pos`), tails ∫_{v>D}, ∫_{v<−D} ≤ 4/(bD); the window
W(s) = κ_b⁻¹∫_{s−s₁}^{s−s₀}F_b (`fejerWindow`) with 0 ≤ W ≤ 1, W ≥ 1 − κ_b⁻¹(4/(b(s₁−s)) + 4/(b(s−s₀))) inside,
W ≤ 4/(κ_b bD) at distance D outside (`fejerWindow_le_right/left`, by reflection); the Fourier side
ψ(ξ) = κ_b⁻¹Λ_b(ξ)∫_{s₀}^{s₁}e^{−iξu}du (`fejerPsi`): continuous, compact support in [−b, b], integrable, and
`integral_fejerPsi_mul_cexp`: ∫ψ(ξ)e^{iξs}dξ = W(s) (band restriction, Fubini on the finite product measure, profile
identity, change of variables); `integral_abs_mul_norm_fejerPsi_le`: ∫|ξ|‖ψ‖ ≤ 2b/κ_b (|ξ||Î(ξ)| ≤ 2 from the
explicit interval transform). Compiles warning-free, `lake build` ok, axioms [propext, Classical.choice, Quot.sound],
lint clean; names prefixed (fejerBandProfile, fejerMass) to avoid clashes with WeilDeviationFejerTest; wired after
ZetaWeightedGramIntegral.
- With b = 1/Δ, b ≤ L: the alias error of ZetaWeightedPoisson is ≤ 2LM²·2b/κ_b = O(L/Δ), weights in [0, 1], ≈ 1 at
  distance ≫ Δ inside [T, 2T], ≤ O(Δ/D) at distance D outside — every input of W2e is now available.

**C160 (localising the CGG damage on the critical line):** for an off-line pair ρ, ρ' = ½ ± y + iγ of F = ζM,
F(s) = (s−ρ)(s−ρ')g(s), so the damage |F'(ρ)|² = 4y²|g|² and F(½ + iγ) = −y²g: damage = 4|F(½ + iγ)|²/y², and
∫_{|t−γ|≤1/L}|F(½+it)|² ≳ |g|²L⁻⁵, giving damage ≲ 4a²L³∫_{window}|ζM|² (a = yL). Coalesced pairs (a → 0) cost
nothing; mid-range pairs cost L³∫_{window}|ζM|², and summing over pairs needs Σ_pairs∫_{W_ρ}|ζM|² ≪ ∫|ζM|², i.e.
that the mass of |ζM|² on the critical line does not concentrate on the δT-set of pair windows. Cauchy–Schwarz turns
that into the mollified fourth moment of ζ on the line, known only for short mollifiers (θ ≲ 1/4), where CGG gives
≈ 0.49 < 0.6725. Verdict: REDUCES to the continuous mollified (2+η)-moment (same core as cycles 115/118); positive
content: the exact local damage law 4|ζM(½+iγ)|²/y² and the line-localised damage bound.
- The ζ goal (75%) is still not met.

## Cycle 132 (2026-10-13) — W2e(i): the window's transform is band-limited (Lean); uniform integrability as the CGG core

**W2e(i) (Lean, RHTower/ZetaFejerWeight.lean, extended in place):** `fejerBandProfile_eq_sinc` (F_b(v) = b sinc(bv/2)²),
`fejerBandProfile_eq_fourier` (F_b(v) = 𝓕Λ_b(−v/2π), via the corpus `HTGeometry.fourier_triangleFn`),
`integrable_fourier_triangleFn`, `integral_fejerBandProfile_mul_cexp` (Fourier inversion
`Continuous.fourierInv_fourier_eq` + change of variables: ∫F_b(v)e^{−iyv}dv = 2πΛ_b(y)), `fejerMass_eq` (κ_b = 2π),
`integral_fejerWindow_mul_cexp` (∫W(τ)e^{−iyτ}dτ = κ_b⁻¹·2πΛ_b(y)·∫_{s₀}^{s₁}e^{−iyu}du, Fubini through
`integrable_prod_iff'` with the constant fibre mass κ_b), `integral_fejerWindow_mul_cexp_eq_zero` (= 0 for |y| ≥ b).
Lemma names unified to the `fejerBandProfile` prefix. Compiles silently, `lake build` ok, axioms [propext,
Classical.choice, Quot.sound], lint clean, no duplicate names.
- Consequence: for b < log 2 the main term aL²∫W(τ)ν(τ)dτ of the weighted trace has no prime contribution at all, and
  by the explicit formula Σ_ρ W(γ_ρ) = ∫W(μ + Π) exactly (no prime terms) — the weighted zero count is closed-form.

**C161 (uniform integrability of the mollified ζ):** C160 reduced the unconditional CGG damage to the non-concentration
of |ζM(½+it)|² on the δT-set of pair windows. It suffices that |ζM|² is uniformly integrable on [T, 2T]:
ε(K) = limsup (1/T)∫_{|ζM|>K}|ζM|² → 0 as K → ∞ (then ∫_E|ζM|² ≤ K²|E| + ε(K)T). Mechanism: by the standard lemma
(Y_T ≥ 0, Y_T → Y in law and E Y_T → E Y < ∞ ⟹ uniform integrability), UI follows from a limiting distribution of
ζM whose second moment equals Conrey's mollified mean value. Test: with log ζ ≈ Σp^{−s} and Levinson's mollifier
P(x) = x, log|ζM| ≈ Re Σ_p p^{−1/2−it}(1 − P(1 − log p/log y)), variance ½(log(1/θ) + ½), lognormal second moment
e^{1/2}/θ ≈ 1.65/θ versus the true mollified mean square 1 + 1/θ (θ = ½: 3.30 vs 3). The Gaussian model does not
reproduce the second moment, so the true limit law (if any) is not lognormal and UI is not implied by known CLTs.
Verdict: OPEN CORE (UI of |ζM|² for θ ≈ ½; weaker than any (2+η)-moment, still unproven; under RH Soundararajan's
upper bound for log|ζ| would give it, unconditionally nothing does).
- The ζ goal (75%) is still not met.

## Cycle 133 (2026-10-13) — W2e(ii): weighted grid character sums vanish off the aliases (Lean); C162 killed

**W2e(ii) (Lean, RHTower/ZetaFejerGridSum.lean, namespace RHTower.FejerWeight):** `fejerWindow_le_sq_right/left`
(W(s) ≤ κ_b⁻¹(s₁−s₀)·4/(dist²·b) outside the interval), `continuous_fejerWindow`, `gridChar`
(x ↦ W(T + x·2π/L)e^{iy(T + x·2π/L)}), `norm_gridChar`, `continuous_gridChar`, `gridChar_isBigO` (O(|x|⁻²) on the
cocompact filter), `fourier_gridChar_eq_zero` (𝓕gridChar(w) = 0 when |wL − y| ≥ b: substitution s = T + hx,
modulation identity, `integral_fejerWindow_mul_cexp_eq_zero`), `hasSum_fejer_grid_char_eq_zero` (Mathlib Poisson
`Real.tsum_eq_tsum_fourier_of_rpow_decay` at x = 0: if |jL − y| ≥ b for all j ∈ ℤ then
Σ_{k∈ℤ} W(τ_k)e^{iyτ_k} = 0). Compiles silently, `lake build` ok, axioms [propext, Classical.choice, Quot.sound],
lint clean, no duplicate names, wired after ZetaFejerWeight.
- Use in W2e(iii): by Zeta23's `P_part_eq`, the prime part of the weighted trace is
  −2Σ_n a_n A_φ(log n)Σ_{k<d}W_k cos(τ_k log n); on the full lattice the inner sum is 0 for b ≤ log n ≤ L − b, and the
  aliased band log n ∈ (L − b, L] carries A_φ(log n) ≤ L − log n < b. What remains is the finite-grid tail
  Σ_{k∉[0,d)}W(τ_k) ≤ (L/2π)·O(TΔ/D) (quadratic decay), i.e. an O(√X·TΔ/(aD)) trace error.

**C162 (the Gram certificate forces non-concentration of |ζM|² at pairs):** damage needs pairs where |g| = |ζ|/|s−ρ||s−ρ'|
is large, i.e. pairs sitting inside regions of large ζ-values, which occur in large gaps between zeros. The Frobenius
certificate at bandwidth ≤ 1 constrains short-range pair correlation and gives lower bounds for the proportion of large
gaps, never upper bounds; a configuration with off-line pairs placed in the middle of large gaps changes F only at O(1)
scale and is consistent with every unconditional statistic. Verdict: FALSE.
- The ζ goal (75%) is still not met.

## Cycle 134 (2026-10-13) — the Fejér window is too heavy-tailed at X = T^{4/3}; Jackson window (Lean); C163 killed

**Finding (W budget):** the weighted trace's prime part is −2Σ_n a_n A_φ(log n)Σ_{k<d}W_k cos(τ_k log n). On the full
lattice the inner sum vanishes off the aliases (cycle 133); two errors remain. Alias band log n ∈ (L − b, L]:
A_φ ≤ b, mass ≈ b√X·b, normalised error b²√X·T/(aL) — needs b ≪ X^{−1/4}L, i.e. Δ = 1/b ≫ T^{1/3}. Finite-grid tail
Σ_{k∉[0,d)}W(τ_k): the Fejér window has W(s) ≍ Δ/dist (tail of ∫_{v>D}F_b ≍ Δ/D), so the tail is ≍ (L/2π)Δ·log T
and the normalised error √XΔ log T/a ≪ TL needs Δ ≪ T^{1/3}. The two constraints meet exactly at Δ ≍ T^{1/3} with
no room: **the Fejér window cannot evaluate the weighted trace at bandwidth 4/3.** A window with tails (Δ/d)³ gives a
tail error √XΔ³/(aD²) with D ≍ T, i.e. Δ ≪ T^{7/9}, compatible with Δ ≫ T^{1/3}.

**Lean (RHTower/ZetaJacksonProfile.lean, RHTower/ZetaJacksonGridSum.lean, namespace RHTower.FejerWeight):**
the Jackson profile F_b² (`jacksonProfile`): ≤ b², ≤ 16/(b²v⁴), integrable, continuous, even;
`integral_jacksonProfile_mul_cexp` (∫F_b²e^{−iyv} = 2π∫Λ_b(ξ)Λ_b(y−ξ)dξ via F_b = ∫Λ_b e^{iξv}, Fubini against the
majorant F_b(v)Λ_b(ξ), and the Fejér inversion) and `_eq_zero` (|y| ≥ 2b); tails ∫_{v>D} ≤ 16/(3b²D³); mass κ₂ > 0;
`jacksonWindow` ∈ [0, 1] with bulk loss and outside bound O(κ₂⁻¹/(b²D³)); generic
`integral_profileWindow_mul_cexp` (transform of any interval-averaged profile) and generic Poisson lemma
`hasSum_grid_char_eq_zero_of_window` (continuous window, quadratic decay, transform vanishing beyond B ⟹ grid
character sums vanish off the aliases |jL − y| < B); instance `hasSum_jackson_grid_char_eq_zero` (B = 2b) with
`abs_jacksonWindow_le_inv_sq`. Both compile silently, `lake build` ok, axioms [propext, Classical.choice, Quot.sound],
lint clean, no duplicates, wired after ZetaFejerGridSum.
- Still needed for the twisted Poisson (W2b): the representation W₂ = ψ₂^∨ with ψ₂ = κ₂⁻¹(Λ_b⋆Λ_b)·Î supported in
  [−2b, 2b] (from F_b² = ∫(Λ_b⋆Λ_b)(ζ)e^{iζv}dζ).

**C163 (large gaps cannot host off-line pairs):** a real entire function may have a non-real pair between two distant
real zeros (polynomial models do); under the heat flow off-line pairs are born at collisions (small gaps), which is a
dynamical tendency of H_t, not a constraint on ζ = H_0; Λ ≤ 0.2 only gives |β − ½| ≤ 0.32. Verdict: FALSE (no local
obstruction; the CGG damage configuration "pairs inside large gaps" is consistent with all known constraints).
- The ζ goal (75%) is still not met.

## Cycle 135 (2026-10-13) — Jackson window as inverse transform (Lean); dimension cap for higher-order certificates

**Lean (RHTower/ZetaJacksonFourier.lean):** `triConv` (C_b = Λ_b ⋆ Λ_b: nonnegative, ≤ b, continuous, support
[−2b, 2b], integrable, ∫C_b = b² by Fubini + translation), `jacksonProfile_eq_integral` (F_b(v)² = ∫C_b(ζ)e^{iζv}dζ:
product of the two triangle integrals, shear ζ = ξ + η, Fubini via `integrable_prod_iff` with fibre mass b·Λ_b(ξ)),
`jacksonPsi` (ψ₂ = κ₂⁻¹C_b·Î), `jacksonPsi_eq_zero` (|ζ| ≥ 2b), continuity, compact support, integrability,
`abs_mul_norm_jacksonPsi_le` (|ζ|‖ψ₂‖ ≤ 2κ₂⁻¹C_b(ζ)), `integral_abs_mul_norm_jacksonPsi_le` (∫|ζ|‖ψ₂‖ ≤ 2b²/κ₂),
`integral_jacksonPsi_mul_cexp` (∫ψ₂(ζ)e^{iζs}dζ = W₂(s)). Compiles silently, `lake build` ok, axioms [propext,
Classical.choice, Quot.sound], lint clean, no duplicates, wired after ZetaJacksonGridSum. The Jackson window now meets
every hypothesis of `hasSum_weighted_phiHat` / `norm_weighted_sub_main_le` (needs 2b ≤ L), of the grid-sum vanishing,
and has cubic tails — the window side of Project W is complete.

**C164 (dispersion over the window position):** average the bandwidth-4/3 certificate over window positions T' to
dilute close prime pairs. Pairs (m, n) are resolved by a window of length H iff |log(m/n)| ≫ 1/H, whatever the
position; averaging positions inside [T, 2T] is a longer window at best (cycle 129: wall X ≤ height). Verdict: FALSE.

**C165 (quartic Gram certificate under RH):** the eigenvalue law of the normalised Gram matrix at λ = 1 has GUE moments
1, 4/3, 2, 16/5 (Uniform[0,2]); the 2/3-extremal matches the first three but has m₄ = 10/3, and the degree-4 bound
rank/N ≥ 1 − min E[(1 − sX + pX²)²] = 1 − 1/9 = 8/9 (s = 2, p = 5/6) would follow from m₄ = 16/5, giving 8/9 distinct
and 7/9 simple zeros under RH. Attack: tr Ĝ⁴ = Σ_{ρ₁..ρ₄}ΠK(γ_i − γ_{i+1}) with each K of α-support [−λ/2, λ/2], so
the 4-cycle has Σ|ξ_j| ≤ 4λ and Rudnick–Sarnak gives it only for λ < 1/2; but the Gram matrix has dimension
d = λN, so rank ≤ λN < N/2 and every certificate at λ < 1/2 is capped at λ. Verdict: FALSE (dimension cap:
k-th order certificates need 2kλ ≤ 2 for the n-level input but λ ≥ 1 for full dimension; only k = 2 meets both, at
λ = 1). Unconditionally, higher traces also carry far-zero growth e^{kλL(β−½)}.
- Positive content (dimension–support law): for a Gram/rank certificate built from k-th traces of a bandwidth-λ Gabor
  system, the rank bound is ≤ min(λ, ·) and the n-level input needs kλ < 1 (RS support); hence k ≥ 3 never beats the
  pair certificate, and the only escape is pair correlation beyond α = 1 (as in cycles 96–110).
- The ζ goal (75%) is still not met.

## Cycle 136 (2026-10-13) — the prime part of the weighted trace (Lean); pair-Gram certificate killed

**Lean (RHTower/ZetaWeightedTracePrime.lean):** `norm_sum_le_tsum_compl_of_hasSum_zero` (finite part of a vanishing
lattice sum ≤ complementary mass), `abs_sum_range_cos_le_of_hasSum_zero` (|Σ_{k<d}W(τ_k)cos(τ_k y)| ≤ Σ_{k∉[0,d)}W(τ_k)
when the full-lattice character sum vanishes), `weighted_P_part_eq` (Σ_k W_k G^P_kk = −2Σ_n a_n A_φ(y_n)Σ_k W_k cos(τ_k y_n),
from Zeta23's `P_part_eq`), `abs_weighted_P_part_le` (|Σ_k W_k G^P_kk| ≤ 2(Σ_{n≤X}a_n)(L·E + B·d) given the cosine bound E
on the band log 2 ≤ y_n ≤ L − B; a₁ = 0, A_φ(y) ≤ (L − y)₊), and in FejerWeight: `window_grid_isBigO`,
`summable_jacksonWindow_grid`, `two_mul_le_abs_alias` (every alias of y ∈ [2b, L − 2b] is ≥ 2b away when 4b ≤ L),
`abs_sum_range_jackson_cos_le` (the Jackson cosine sums on the finite grid are ≤ the outer mass). Compiles silently,
`lake build` ok, axioms [propext, Classical.choice, Quot.sound], lint clean, no duplicates, wired after
ZetaJacksonFourier.
- Remaining for the weighted trace: explicit outer-mass bound E ≤ (L/2π)·O(κ₂⁻¹b⁻²M⁻²) (cubic tails at margin M),
  the μ-part Σ_k W_k G^μ_kk ≈ (2π/L)·aL²Σ_k W_kμ(τ_k) (Zeta23 `mu_part_bound`) and the Π-part.

**C166 (Gram matrix over pairs of zeros):** v_{ρρ'} = u_ρ ⊗ u_ρ' with a short-range weight w(γ − γ') has dimension d² ≫
#pairs (no dimension cap) and its Frobenius norm is a 4-point statistic. Attack: with K of α-support λ/2 per factor and
ŵ of support σ, the 4-point Fourier support is Σ|ξ| ≤ 2λ + 2σ; inside Rudnick–Sarnak (Σ|ξ| < 2) the per-difference
resolution is α < 1, as for pair correlation. The statistic separating the 2/3-extremal (m₄ = 10/3 vs GUE 16/5) needs
Σ|ξ| ≤ 4, outside that range; coalesced off-line pairs and on-line doubles stay indistinguishable at resolution α < 1
in any n-point statistic. Verdict: FALSE.
- Positive content: for every n-point certificate with known (RS-range) input the effective resolution per zero
  difference is α < 1; near-doubles at scale ≪ 1/log T are invisible to all of them, consistent with the continuity
  barrier.
- The ζ goal (75%) is still not met.

## Cycle 137 (2026-10-13) — weighted trace prime part: band split and explicit outer mass (Lean); C167 reduced

**Lean (RHTower/ZetaWeightedTracePrime.lean, extended):** `abs_weighted_P_part_le_band`
(|Σ_k W_k G^P_kk| ≤ 2(L·E·Σ_{n≤X}a_n + B·d·Σ_{n≤X, y_n>L−B}a_n): the trivial grid bound is paid only on the alias
band), `tsum_inv_sq_grid_shift_le` (telescoping Σ_{m≥0}(M+(m+1)h)⁻² ≤ 1/(hM)), `div_cube_le_div_mul_inv_sq`,
`tsum_compl_jacksonWindow_le` (window at distance M inside the grid range ⟹ outer mass
E ≤ κ₂⁻¹(16/(3b²))(1/M³ + 2/(hM²)), via indicator sums, `tsum_of_nat_of_neg_add_one`, `sum_add_tsum_nat_add` and the
cubic Jackson tails). Compiles silently, `lake build` ok, axioms [propext, Classical.choice, Quot.sound], lint clean;
helper renamed after a name scan (three corpus `tsum_inv_sq_shift_le`).
- Budget (bandwidth 4/3, X = T^{4/3}, h = 2π/L, κ₂ ≍ b): outer mass E ≍ L/(b³M²); trace error from the bulk band
  2LEΣa_n/(aL²) ≍ √X·L/(ab³M²); from the alias band 2Bd·Σ_{band}a_n/(aL²) with B = 2b and
  Σ_{X e^{−2b}<n≤X}a_n ≲ 4b√X log X: ≍ b²√X T log X/(aL). With Δ = 1/b and M ≍ T^{0.9}: bulk ≍ T^{2/3}Δ³L/T^{1.8},
  alias ≍ T^{5/3}log/(Δ²L) ≪ TL ⟸ Δ ≫ T^{1/3}. Any Δ ∈ [T^{0.34}, T^{0.7}] makes the weighted trace's prime part
  o(N) — a window choice exists (unlike Fejér, cycle 134).

**C167 (statistics with arithmetic weights per zero):** sums Σ_ρ w(ρ)f(γ_ρ) with w = |ζ'M|²-type weights are linear in the
zeros (no pair correlation needed) and can exceed the α < 1 resolution — they are CGG's discrete moments. Their
unconditional obstruction is the off-line damage, i.e. uniform integrability of |ζM|² near pair windows (C160–C162).
Verdict: REDUCES to C161 (no new mechanism).
- The ζ goal (75%) is still not met.

## Cycle 138 (2026-10-13) — the weighted trace (Lean); UI core sharpened to a far-zero budget question

**Lean (RHTower/ZetaWeightedTrace.lean):** `tau_ge_T`, `abs_weighted_mu_part_sub_le`
(|Σ_k W_kG^μ_kk − 2πaLΣ_k W_kμ(τ_k)| ≤ d(K∫φ̂²|r| + 10∫φ̂²r²)/T from Zeta23's `mu_part_bound`), `abs_weighted_Pi_part_le`
(|Σ_k W_kG^Π_kk| ≤ d((6√X/T)2πaL + (12√X/T²)∫φ̂²r²) from `Pi_part_bound`), `abs_weighted_trace_sub_le`
(|Σ_k W_kG_kk − 2πaLΣ_k W_kμ(τ_k)| ≤ μ-error + Π-error + |weighted P-part|, via `GentryA_diag_eq`). Compiles silently,
`lake build` ok, axioms [propext, Classical.choice, Quot.sound], lint clean, no duplicates, wired after
ZetaWeightedTracePrime. (Trap again: `W k * ∫ r, f r − …` parses the subtraction inside the integral — parenthesise.)
- With ZetaWeightedTracePrime the weighted trace is now tr Ĝ_w = (2π/L)Σ_k W_kμ(τ_k) + O(√X/a) + o(N) for the Jackson
  window with Δ ∈ [T^{0.34}, T^{0.7}]. Remaining for the trace side: the Riemann sum (2π/L)Σ_k W_kμ(τ_k) vs N(T, 2T)
  (bulk W ≥ 1 − O((Δ/dist)³), RvM).

**C168 (UI for short mollifiers via the known twisted fourth moment):** where the mollified fourth moment is known
(θ ≲ 1/4), UI holds by Hölder, but CGG(θ = 1/4) = 1 − (5/4)⁻³ ≈ 0.488 < 0.6725 even under RH, and the Gram-extremal
(2/3 simple + 1/6 coalesced pairs) satisfies it. Verdict: INSIGNIFICANT.

**C169 (unconditional Soundararajan inequality):** log|ζ(½+it)| − log|ζ(σ₀+it)| = Σ_ρ(log|½+it−ρ| − log|σ₀+it−ρ|); the
term is ≤ 0 for every zero with β ≤ (½+σ₀)/2, so with σ₀ = ½ + λ/log x, x = T^ε, only zeros with a = (β−½)log T >
λ/(2ε) contribute positively: coalesced and mid-range off-line pairs drop out of the upper bound entirely, and
log|ζ| ≤ Re P_x + C(λ)/ε + O(1) + (far-zero corrections). The far zeros are rare (corpus near-line density ≪ e^{−a/14}),
so the exceptional set where the bound fails has small measure — but UI on that exceptional set is again what is
needed (mass of |ζM|² there). A budget argument would close it if one had a matching *lower* bound for ∫_{good}|ζM|²
(then ∫_{bad} = total − good is small). Verdict: OPEN (core sharpened: the CGG damage is now only a far-zero question
plus a good-set lower second moment; mid-range pairs are harmless).
- The ζ goal (75%) is still not met.

## Cycle 139 (2026-10-13) — weight deficit lemmas (Lean); far-zero correction = ratio moments (circular)

**Lean (RHTower/ZetaWeightedTrace.lean, extended):** `sum_one_sub_le_of_bulk` (W ≥ 0 and W ≥ 1 − η on S ⟹
Σ_{k<d}(1 − W_k) ≤ #(range d ∖ S) + ηd), `FejerWeight.one_sub_le_jacksonWindow_of_dist` (at distance D inside the
interval: W ≥ 1 − κ₂⁻¹·32/(3b²D³)). Rebuilt, lint clean, unique names. Use: weighted trace = unweighted trace (Zeta23
prop:trace) − Σ_k(1 − W_k)G_kk; the μ-part of the deficit costs ≤ 2πaL·max μ·[#margin indices + ηd], i.e. after
normalisation O((M + D)log T + T(Δ/D)³ log T) = o(N) for D = ΔT^{1/3}, M = o(T); the prime parts of the deficit are the
unweighted (Zeta23) and weighted (cycle 137) prime parts.

**C170 (lower second moment on the good set, to close C169):** the far-zero correction at t is
Σ_ρ ½log[((β−½)² + u²)/((β−σ₀)² + u²)]⁺ (u = t − γ); each zero contributes ≤ log(δ/(δ − η)) ≤ 2η/δ pointwise
(δ = β − ½ ≥ 2η, η = σ₀ − ½) and exactly πη in total integral (∫log((a²+u²)/(b²+u²))du = 2π(a − b)), so the
correction has small L¹ mass (≤ π η·#{far zeros} ≪ e^{−c/ε}T/ε by near-line density). But controlling ∫|ζM|²e^{2·corr}
needs exponential moments of the correction, and Π_ρ|½+it−ρ|/|σ₀+it−ρ| = |ζ(½+it)/ζ(σ₀+it)| (Γ-normalised): these are
ratio moments ∫|ζ(½+it)|²/|ζ(σ₀+it)|² — negative moments of ζ just right of the line, unknown unconditionally.
Verdict: CIRCULAR (UI ⟸ ratio moments near the line ⟸ zero-density control at σ₀ beyond what is known).
- Positive content: the far-zero correction has L¹ mass exactly π(σ₀−½) per contributing zero, independent of its
  distance — the obstruction is purely an exponential-moment (large deviation) question for the correction field.
- The ζ goal (75%) is still not met.

## Cycle 140 (2026-10-13) — weighted kernel main term = continuous Gram kernel (Lean); C171 killed

**Lean (RHTower/ZetaWeightedKernelMain.lean):** `integrable_paperFT_of_decay`, `integral_paperFT_mul_cexp_neg`
(Fourier inversion in the paper's normalisation: ∫φ̂(r)e^{−iyr}dr = 2πφ(y), via `Continuous.fourierInv_fourier_eq` and
Zeta23's `fourier_eq_paperFT`), `integral_cexp_mul_phiHat_mul_phiHat`
(∫e^{iξs}φ̂(τ−s)φ̂(τ'−s)ds = 2πe^{iξτ'}∫φ(u)φ(ξ−u)e^{i(τ−τ')u}du: expand φ̂(τ−s), Fubini against
‖φ̂(τ'−s)‖‖φ(u)‖, inversion in the inner variable), `integral_psi_mul_Gaux2_zero_eq` (for W = ψ^∨ with ψ integrable:
∫ψ(ξ)e^{iξτ'}G_ξ(0)dξ = (L/2π)∫W(s)φ̂(τ−s)φ̂(τ'−s)ds). Compiles silently, `lake build` ok, axioms [propext,
Classical.choice, Quot.sound], lint clean, unique names, wired after ZetaWeightedTrace.
- With W2a/b: Σ_k W(τ_k)φ̂(τ−τ_k)φ̂(τ'−τ_k) = (L/2π)∫W(s)φ̂(τ−s)φ̂(τ'−s)ds + alias, |alias| ≤ 2LM²∫|ξ||ψ| — so
  ‖Ĝ_w‖² = (aL²)⁻²(L/2π)²∬W(s)W(s')G(s,s')²dsds' + (alias, tail) errors, with G(s,s') = ∫φ̂(τ−s)φ̂(τ−s')ν(τ)dτ the
  continuous Gram kernel. Next: the four-fold Fubini for ∬K_main²νν' and the expansion of G(s,s') for ν = μ + Π + P.

**C171 (large deviations of the far-zero correction from Littlewood at several abscissae):** Littlewood's lemma gives
L¹ information Σ_ρ(β − σ)⁺ at each σ but no exponential moments; and Π_ρ|½+it−ρ|/|σ₀+it−ρ| = |ζ(½+it)/ζ(σ₀+it)| has
a non-integrable singularity |t − γ|⁻² at every zero with β = σ₀, so ∫e^{2·corr} = ∞ whenever a zero lies on the
abscissa, and averaging over σ₀ leaves a logarithmically divergent 2-D integral. Verdict: FALSE (the exponential moment
is genuinely infinite in general; Soundararajan's abscissa trick needs the absence of zeros right of ½, i.e. RH).
- The ζ goal (75%) is still not met.

## Cycle 141 (2026-10-13) — closed-form prime-frequency Gram entries (Lean); spectral alias structure; C172–C174

**Lean (RHTower/ZetaWeightedKernelMain.lean, extended):** `paperFT_neg_of_even`, `paperFT_im_eq_zero_of_even` (even real
window ⟹ φ̂ even and real on ℝ), `integral_phiHat_mul_phiHat_mul_cos`
(∫φ̂(τ−τ_a)φ̂(τ−τ_b)cos(yτ)dτ = Re[2πe^{iyτ_b}∫φ(u)φ(y−u)e^{i(τ_a−τ_b)u}du], via `integral_re` and the
product-transform identity). Rebuilt, axioms [propext, Classical.choice, Quot.sound], lint clean. With Zeta23's
P_X = −(1/π)Σa_n cos(τ y_n): G^P_kl = −2Σ_n a_n Re[e^{iy_nτ_l}A_n(τ_k − τ_l)], A_n(δ) = ∫φ(u)φ(y_n − u)e^{iδu}du —
every prime-side Gram entry is an explicit finite sum (the k = l case is Zeta23's `P_part_eq`).

**Finding (W at bandwidth 4/3):** sup-norm control of the alias kernel fails: ∬|alias||ν||ν'| with
∫_{[T,2T]}|P_X| ≈ √(T·X)L = T^{7/6}L forces ‖alias‖ ≪ L³T^{−4/3}, i.e. Δ ≫ T^{4/3}. The alias kernel is however a
superposition of plane waves e^{i(τu + τ'(L−u))} with u in an overlap of length |ξ| ≤ 2b around L/2, so against
P_X(τ)P_X(τ') it only sees prime pairs with |y_n − L/2|, |y_m − L/2| ≲ 2b: Σa_n over that band ≈ 4bX^{1/4}, total
≈ 16b³X^{1/2}L — negligible. The W error analysis must be spectral (resolve the alias kernel's frequencies), not sup-norm.

**C172 (average the certificate over the bandwidth λ ∈ [1, 4/3]):** cycle 112 already showed the scale average is an
α-average of F with the same power-saving requirement. Verdict: REDISCOVERED.
**C173 (filtered rank–trace: rank ≥ (tr PB)²/tr((PB)²) for a Toeplitz filter B ≻ 0):** P^{1/2}BP^{1/2} has the same rank,
but B acts on the zero vectors as u ↦ B^{1/2}u, i.e. replaces the test function φ̂ by a filtered one; the optimum over
filters is the optimum over test functions (Montgomery–Taylor). Verdict: FALSE.
**C174 (long-window upper bound ∫_T^{2T}|P_X|² ≤ ∫_T^{X}|P_X|²):** positivity discards the oscillation; the long
window gives ≈ XΣa_n², a factor X/T = T^{1/3} above the needed TΣa_n². Verdict: FALSE.
- The ζ goal (75%) is still not met.

## Cycle 142 (2026-10-13) — product windows are band-limited (Lean); two counting conjectures killed

**Lean (RHTower/ZetaJacksonProductWindow.lean):** `integrable_jacksonWindow` (majorant (R² + 1 + 2C)/(1 + s²)),
`integral_jacksonProduct_mul_cexp_eq_zero` (∫W(s+a)W(s)e^{−iηs}ds = 0 for |η| ≥ 4b: W(s+a) = ∫ψ₂(ξ)e^{iξ(s+a)}dξ,
Fubini against ‖ψ₂‖·|W|, and the window transform vanishes at |η − ξ| ≥ 2b), `hasSum_jacksonProduct_grid_char_eq_zero`
(grid character sums of W(τ_l + a)W(τ_l) vanish unless |jL − y| < 4b, via the generic Poisson lemma). Compiles
silently, `lake build` ok, axioms [propext, Classical.choice, Quot.sound], lint clean, unique names, wired after
ZetaWeightedKernelMain.
- Use: with the closed form G^P_kl = −2Σ_n a_n Re[e^{iy_nτ_l}A_n(τ_k − τ_l)] and Re x·Re y = ½Re(x ȳ) + ½Re(xy),
  Σ_{k,l}W_kW_l(G^P_kl)² = 2Σ_{n,m}a_na_m Σ_r Re[(A_nĀ_m)(rh)·Σ_l W_{l+r}W_l e^{i(y_n−y_m)τ_l} + (A_nA_m)(rh)·Σ_l W_{l+r}W_l e^{i(y_n+y_m)τ_l}];
  on the full lattice each inner sum vanishes unless y_n ∓ y_m lies within 4b of a multiple of L — the difference
  terms leave the close pairs |log(n/m)| < 4b (the open core 𝒪₁^W), the sum terms leave only y_n + y_m ≈ L, 2L.

**C175 (second-order precision):** a coalesced pair at displacement a/L differs from an on-line double by O(a²) in every
analytic statistic; computing the Frobenius norm to precision o(a²N) cannot help because the adversary takes a → 0,
reaching exact doubles, which pair-correlation information already allows at density 1/3 (Montgomery). Verdict: FALSE.
**C176 (S(t)/Turing increments):** an off-line pair adds 2 to N(t) at its height exactly like an on-line double, and
Turing's ∫S = O(log T) bounds are insensitive to the split; asymptotic proportions get nothing. Verdict: FALSE.
- The ζ goal (75%) is still not met.

## Cycle 143 (2026-10-13) — PP Frobenius expansion identity (Lean); parity invariants are blind (C177)

**Lean (RHTower/ZetaWeightedFrobeniusPP.lean):** `re_mul_re_eq_half` (renamed: `RHTower.re_mul_re_eq` exists in BaezDuarteSmoothZeroDual; Re a·Re b = ½(Re(a b̄) + Re(ab))), `sq_sum_mul_re_eq`
((Σc_n Re z_n)² = ½Σ_{n,m}c_nc_m(Re(z_n z̄_m) + Re(z_n z_m))), `weighted_sq_sum_mul_re_eq` (the weighted grid version:
Σ_{k,l}W_kW_l(Σ_n c_n Re z_n(k,l))² = ½Σ_{n,m}c_nc_mΣ_{k,l}W_kW_l(Re(z_n z̄_m) + Re(z_n z_m))(k,l)). Compiles silently,
`lake build` ok, axioms [propext, Classical.choice, Quot.sound], lint clean, unique names, wired after
ZetaJacksonProductWindow. With z_n(k,l) = e^{iy_nτ_l}A_n(τ_k − τ_l) this is the split of the prime–prime Frobenius sum
into difference (y_n − y_m) and sum (y_n + y_m) frequencies.

**C177 (discontinuous invariants: parity/sign patterns of Z):** off-line zeros come in pairs at a common height, so
for every window sgn(Z(a)Z(b)) = (−1)^{N₀(a,b)} = (−1)^{N(a,b)}, and N(a,b) = (θ(b)−θ(a))/π + S(b) − S(a) counts all
zeros. Every parity-type invariant of the sign process is a function of total counts and carries no on/off-line
information; only the number of sign changes does, and its known lower bounds (Selberg, Levinson) are continuous
functionals. Integer invariants of Gram matrices (rank, n₊) are already used and are bounded only through continuous
traces. Verdict: FALSE.
- Positive content (parity blindness law): E[sgn Z(t)Z(t+h)] = E[(−1)^{N(t,t+h)}] exactly, for every h — the sign
  correlations of Z are statistics of S(t) increments mod 2.
- The ζ goal (75%) is still not met.

## Cycle 144 (2026-10-13) — offset reindexing and admissible lattice sums (Lean); C178 killed

**Lean (RHTower/ZetaGridReindex.lean):** `sum_sum_eq_sum_offset` (Σ_{k,l∈[0,d)}F(k,l) = Σ_{r∈(−d,d)}Σ_{l∈[0,d), l+r∈[0,d)}F(l+r,l),
via `Finset.sum_nbij'` and `Finset.sum_comm'`), `norm_sum_admissible_le` (if Σ_{l∈ℤ}c_l = 0, ‖c_l‖ ≤ v_l and
‖c_l‖ ≤ u_{l+r}, then ‖Σ_{l∈S, l+r∈S}c_l‖ ≤ Σ_{k∉S}u_k + Σ_{l∉S}v_l, through indicator tsums and the shift
`Equiv.addRight r`). Compiles silently, `lake build` ok, axioms [propext, Classical.choice, Quot.sound], lint clean, unique
names, wired after ZetaWeightedFrobeniusPP. (Trap: `(Equiv.addRight r).summable_iff.mpr` on indicator-of-Finset
functions timed out in `whnf`; naming the function first and rewriting `Equiv.coe_addRight` fixes it.)
- Use: for each offset r the weighted grid sum Σ_{l admissible}W_{l+r}W_l e^{iθτ_l} is ≤ 2E (E = outer Jackson mass,
  `tsum_compl_jacksonWindow_le`) whenever θ is ≥ 4b from every alias (`hasSum_jacksonProduct_grid_char_eq_zero`); with
  Σ_r|C_{nm}(rh)| ≲ L³ and Σa_n ≍ √X the non-aliased prime pairs cost ≲ X L³E, i.e. o((aL²)²N) once
  M ≫ T^{1/6}Δ^{3/2}.

**C178 (Selberg-type sign-change counting with a long mollifier):** Selberg's criterion
|∫_t^{t+h}Z|M|²| < ∫_t^{t+h}|Z||M|² detects a sign change; the resulting lower bound for N₀ is a continuous functional
of mean values (|∫ZM²|² and ∫|Z||M|²), so the continuity barrier applies, and the method's proportion is far below
Levinson's even with long mollifiers. Verdict: FALSE (continuous input ⇒ continuous bound, whatever the discrete
output).
- The ζ goal (75%) is still not met.

## Cycle 145 (2026-10-13) — non-close prime pairs in the weighted Frobenius norm (Lean); n-point lifts are inert (C179)

**Lean (RHTower/ZetaWeightedFrobeniusFar.lean, namespace RHTower.FejerWeight):** `image_range_natCast_eq_Ico`,
`tsum_indicator_compl_jacksonWindow_le` (outer Jackson mass E₀ off [0,d) as an indicator tsum),
`norm_sum_admissible_jacksonProduct_le` (for every offset r and every frequency y at distance ≥ 4b from all aliases jL:
‖Σ_{l∈[0,d), l+r∈[0,d)} W(τ_{l+r})W(τ_l)e^{iyτ_l}‖ ≤ 2E₀), `norm_sum_sum_jacksonDifference_le`
(‖Σ_{k,l}W_kW_l e^{iθτ_l}B(k−l)‖ ≤ 2E₀ Σ_{|r|<d}‖B(r)‖ off the aliases), `cexp_mul_conj_cexp`, `cexp_mul_cexp_I`,
`abs_sum_sum_mul_re_le`, `abs_weighted_pair_le` (a prime pair (n,m) with y_n − y_m and y_n + y_m both 4b-far from
the aliases contributes ≤ 2E₀ Σ_r ‖A_n(r)‖‖A_m(r)‖ to the weighted PP Frobenius expansion). Compiles silently,
`lake build` ok, axioms [propext, Classical.choice, Quot.sound], lint clean, names unique (a same-statement
`HTGeometry.norm_cexp_I_mul_ofReal_mul` exists outside the import closure — inlined instead of duplicated), wired after
ZetaGridReindex. Project W status: every non-close prime pair of the weighted Frobenius norm is now formally
bounded; what remains is exactly the close-pair core |log(n/m) − jL| < 4b.

**Threshold in F-language.** The λ-certificate's prime side is tr G̃²/norm = λ⁻¹∫_{−λ}^{λ}F(α)(1 − |α|/λ)dα (GUE at
λ = 4/3: 19/16 ✓). FrobeniusFourThirds (≤ 5/4) ⟺ ∫_1^{4/3}(4/3 − α)F(α)dα ≤ 1/9, i.e. twice the GUE value 1/18
(matches 𝒮 ≤ 1/18). Montgomery's shift inequality (k̂ ≥ 0 ⇒ ∫F(α)k(α − b) ≤ ∫F k; Fejér triangle of half-width 1
shifted by 1/3, known part 28/27 of 36/27) gives, under RH, ∫_1^{4/3}(4/3 − α)F ≤ 8/27 — the gap to 3/27 is a
factor 8/3 (other half-widths h ∈ [2/3, 1] are worse, e.g. h = 2/3 gives 145/243).

**C179 (Lasserre lift).** Conjecture: positivity of the 3-point (n-point) correlation measure together with
Rudnick–Sarnak data on the hexagon H = {max(|ξ₁|, |ξ₂|, |ξ₁+ξ₂|) < 1} and the marginal identity
∫R₃(x, y)dy = cR₂(x) improves the 2-point LP bound for ∫_1^{4/3}(4/3 − α)F. The dual does admit 3-point minorants
(a(x, y) ≤ g(x), a ∈ PW(H)) that certify slack, so the lift is not trivially empty. Verdict: FALSE (asymptotically
no gain), by a spreading construction: for any 2-point-feasible R₂ = R₂^{GUE} + δR₂ with spec δR₂ ⊂ {|α| ≥ 1 + η},
put δR₃(x, y) = δR₂(x)·v(y)(1 − κ(y − x))/n(x) with v ≥ 0 spread over |y| ≍ Y and vanishing near 0, κ the
narrow-band Fejér bump (band < η, so 1 − κ(z) ≍ η²z² near 0), n(x) the normaliser. All factors are band-limited
below η, so spec δR₃ ⊂ {|ξ₁| ≥ 1} misses H; the marginal is cδR₂; R₃^{GUE} + δR₃ ≥ 0 for Y large because
|δR₂| ≤ R₂^{GUE} where δR₂ < 0, R₃^{GUE}(x, y) → ρR₂^{GUE}(x) for spread y, and near y = x the factor η²(y − x)²
sits under the GUE repulsion. Induction gives the same for every n.
- Positive survivor (spreading law): RS-range n-point data plus positivity, for every n, gives exactly the 2-point LP
  for every pair functional supported on |α| ≥ 1. Together with the dimension–support law (C165/C166) this means
  correlation data in the RS range has no use for 75%: beyond the MT ceiling 0.6725 the only inputs are arithmetic
  twists (CGG θ ≥ 4^{1/3} − 1) or prime pairs past α = 1 (∫_1^{4/3}(4/3 − α)F ≤ 1/9).
- The ζ goal (75%) is still not met.

## Cycle 146 (2026-10-13) — close prime pairs: the continuous kernel (Lean); CGG θ-gap is a level-of-distribution bridge (C180)

**Lean.** `RHTower/ZetaGridReindex.lean` generalised: `norm_sum_admissible_sub_le` (if Σ_{l∈ℤ}c_l = M then the
admissible finite part differs from M by at most the outer masses); `norm_sum_admissible_le` is now its M = 0 case.
New `RHTower/ZetaWeightedFrobeniusClose.lean` (namespace RHTower.FejerWeight):
`hasSum_grid_char_of_window` (Poisson on the Gabor grid with one surviving alias: if |jL − y| ≥ B for all j ≠ 0 then
Σ_k W(τ_k)e^{iyτ_k} = (L/2π)∫W(s)e^{iys}ds), `jacksonPairKernel` K_r(θ) = (L/2π)∫W(s + rh)W(s)e^{iθs}ds,
`hasSum_jacksonProduct_grid_char`, `norm_sum_admissible_jacksonProduct_sub_le` (finite admissible sum = K_r(θ) up to
2E₀), `norm_sum_sum_jacksonDifference_sub_le` (‖Σ_{k,l}W_kW_l e^{iθτ_l}B(k−l) − Σ_r B(r)K_r(θ)‖ ≤ 2E₀Σ_r‖B(r)‖),
`abs_weighted_close_pair_sub_le` (a close pair contributes ½Re Σ_r A_n(r)Ā_m(r)K_r(y_n − y_m) up to
2E₀Σ_r‖A_n(r)‖‖A_m(r)‖). Compiles silently, `lake build` ok (dependants rebuilt), axioms
[propext, Classical.choice, Quot.sound], lint clean, names unique, wired after ZetaWeightedFrobeniusFar.
- Project W status: every prime pair of the weighted PP Frobenius norm is now formally either negligible (far pairs,
  cycle 145) or equal to an explicit continuous kernel (close pairs). The open core is the smoothed prime-pair
  correlation Σ_{n,m close} c_nc_m ½Re Σ_r A_nĀ_m K_r(log n − log m). K_r(θ) is the transform of W(·+rh)W at θ:
  a main lobe |θ| ≲ 1/T (intervals of length X/T = X^{1/4}) plus the Jackson-smoothed tail 1/T ≲ |θ| < 4b
  (intervals up to X/Δ). Both are mean squares of the length-X prime polynomial over a window shorter than X, i.e.
  F on (1, 4/3) — the same open input as the F-threshold of cycle 145, now without edge artefacts.

**C180 (Kloosterman breach for discrete CGG).** Conjecture: the discrete mollified moment Σ_ρ|ζ'M(ρ)|² over zeros
extends from θ = ½ to θ = 4/7 by the Deshouillers–Iwaniec bilinear technology, giving (under RH) the CGG proportion
1 − (1 + 4/7)^{−3} = 1 − 343/1331 = 988/1331 ≈ 0.7423. Attack: the θ = ½ barrier is the Gonek-lemma error
min(T, x/⟨x⟩) at x = nh/k near prime powers; for θ > ½ the near-misses nh − kp = ℓ ≠ 0 appear, i.e. primes in
classes p ≡ −ℓk̄ (mod h) with bilinear mollifier weights in (h, k), so the barrier is the Bombieri–Vinogradov level
with residues that vary with the second mollifier variable (fixed-residue BFI does not apply directly; the corpus
has no BFI-type theorem). Verdict: BRIDGE (to a level-of-distribution statement with bilinearly varying residues) and
INSIGNIFICANT for the goal: even θ = 4/7 leaves 988/1331 < 3/4 under RH, and the unconditional version still needs UI
(C161).
- Positive content: the single-piece CGG route to 3/4 must exceed the Kloosterman level 4/7 by
  (4^{1/3} − 1) − 4/7 ≈ 0.0160 in θ; at θ = 4/7 it falls short by 3/4 − 988/1331 = 89/5324 ≈ 0.0167 in proportion.
  The only remaining freedom inside the method is the mollifier shape (multi-piece/Feng), which is the next test.
- The ζ goal (75%) is still not met.
