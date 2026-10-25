# 75% critical-line loop, second campaign (2026-10-25)

- **ID:** g75-1025
- **Stage:** 1-in-progress
- **Type:** CONJECTURE loop
- **Source:** `seventy-five-percent-loop-2026-10-12.md` (cycles 1–148), `TransThresholdPairCorrelation/README.md`
- **Statement:** Unconditional Lean proof of `∀ ε > 0, ∀ᶠ T, (3/4 − ε)·N(T) ≤ N₀(T)`.

## Frontier entering this campaign (corpus only)
- Proved: `two_thirds_le_liminf_xiSimpleCriticalRatio` (Zeta23 Thm B); Montgomery–Taylor `0.6725` (Zeta23 Thm D).
- TTPC: `N₀*(T,2T) ≥ (29/36 − ε)N − coalescentSurplus` at bandwidth `4/3`; `3/4` ⟸ surplus `≤ (1/18 + o(1))N`.
- Walls recorded in g75-1012: Nyquist/length law (pair correlation beyond `α = 1`), continuity barrier
  (averaging proofs cannot separate on-line doubles from coalescing pairs, so 75% on-line ⟹ 75% simple-like,
  above the RH-conditional record), Jensen floor (Levinson/CGG), parity (sieves bound close pairs only by size).

## Conjecture ledger (this campaign)
- **C1 two-window sign trick** (two windows on `[T,2T]` whose coalescent kernels sum `≤ 0`, so one surplus is `≤ 0`):
  FALSE. Every window `Ω ≥ 0` on `[T,2T]` has `Ω̂ > 0` on `|θ| ≲ 1/T`; a sum of windows is a window.
- **C2 positive-definite height window** (`Ŵ ≥ 0` makes the pair sum monotone, so a sieve majorant bounds it):
  FALSE. `W` PD forces `W(0) = max`, so the window covers `τ ≈ 0`, where the pole makes the Poisson continuum `≍ X`;
  pole subtraction makes the coefficients `Λ − 1` signed. Same wall as the "spectral sieve `Υ = 2`" model.
- **C3 eighth-moment Chebyshev** (`#{μ ≤ 0} ≤ tr(Â₁ − I)⁸ ≤ N/8 ⟹ n₊ ≥ 7N/8 ⟹ 3/4`): reduction TRUE
  (Uniform[0,2] gives `N/9`); input is an 8-level statistic at support 8 with signed height phase. BLOCKED.
- **C4 low-rank prime modes** (`Â_λ` positive on a subspace of codimension `#primes ≤ X`): FALSE. A frequency mode
  compressed to a window of length `T` is a multiplication operator, not rank two.
- **C5 parity of interval counts** (`N₀ ≥ #{I : N(I) odd}`): REDISCOVERED. `(−1)^{N(t)} = −sgn Z(t)`, so parity
  statistics are sign statistics of `Z` (Selberg's method).
- **C6 complex-shifted bilinear/Hermitian Gram `C_η`**: order law again; a pair block's negative eigenvalue is `−Θ(β²)`.
- **C7 displaced product `ξ(s+δ)ξ(s−δ)`**: consistency identity only; the certificate needs bandwidth `2`.
- **C8 Speiser–Levinson–Montgomery form** (`3/4 ⟺ N⁻(ζ') ≤ N/8 + O(log T)`): TRUE (classical); no leverage.
- **C9 curvature control by the bilinear `ζ''M` moment**: a near pair's CGG cost is `δ²×` its (positive) bilinear
  `ζ''M`-contribution, so the `a → 0` corner dies once far pairs' signed `ζ''` terms are bounded. Far pairs need
  near-line density rate `> 2` (the Zeta23 isolated-pair slack has rate `2λ = 2` at `λ = 1`: borderline, couples
  excluded). REDISCOVERED (g75-1012 cycle 11 "control of Σκ through ∫|ζ''M|²").
- **C10 Hermitian discrete moment by subharmonicity + Hölder** (mollified fourth moment of `ζ'` × Selberg moments of
  local zero counts): gives `Σ_ρ|ζ'M(ρ)|² ≤ K·N` with a constant loss. The adversary puts that whole budget on the
  pairs; the certificate needs the asymptotic. FALSE as a route.
- **C11 decorated crystal is not admissible**: on a lattice the form factor is 1-periodic and even, which contradicts
  `F(α) = α` on `(0,1)` except at `α = 1/2`, so `P = I_r` is never exact. TRUE, but already priced: the
  positivity-LP optimum is Montgomery–Taylor `0.6725`.
- **C12 hardness of the `λ = 4/3` surplus**: an off-line pair enters the bilinear Frobenius with weight `cosh(2λa)`, so
  without interference `surplus ≤ N/18` would force `N(σ,T) ≪ T^{1−(8/3)(σ−½)}`, i.e. beyond the density hypothesis and
  a zero-free strip `σ > 7/8`. Interference (g75-1012 cycle 14) keeps this heuristic. Sharpens the TTPC hardness
  witness; no route.

- **C13 bilinear CGG against the corner:** the `a → 0` corner is the RH-world configuration
  "2/3 simple + 1/6 doubles", which CGG's `19/27` excludes; bilinear CGG moments are continuous, so they
  exclude the near-pair corner too. The binding adversary moves to fixed `a ≈ 0.3–0.65` with large local
  curvature `κ`. Aggregate curvature control from the bilinear `ζ''M` moment (near pairs enter it with
  `+|2CM|²`) caps `κ` on average at `O(1)`, giving ≈ 0.673. REDISCOVERED (g75-1012 cycles 11/16/21).
- **C14 longer certificates over the zero index:** a `d × d` mollified Gram is capped by `rank ≤ d = λN`
  with `λ + 2θ ≤ 1`; several mollifiers in one Cauchy–Schwarz only re-optimize CGG's mollifier. No gain.
- **C15 signature as an eta invariant:** `sign Â = π^{-1/2}∫₀^∞ t^{-1/2} tr(Â e^{−tÂ²})dt` needs all odd
  moments and is dominated at large `t` by the tiny pair eigenvalues. BLOCKED.
- **C16 Littlewood derivative:** the jump of `∂_σ ∫ log|ξ(σ+it)|dt` across `σ = 1/2` is `2πN₀` exactly,
  i.e. `N₀ = N − 2 lim_{η↓0} N(1/2+η,T)`; the near-line density at `η → 0` is the target itself.
  REDISCOVERED (argument principle).

- **C17 the ζ'-zero of a near pair:** from `ζ'/ζ ≈ 2u/(u² − δ²) − L/2` the pair `½ ± δ + iγ` gives ζ'-zeros at
  `½ − δ²L/4` and `½ + 4/L`: the Speiser–Levinson–Montgomery left zero sits at second-order displacement.
  Same continuity barrier.
- **C19 finite-node center-mixed positivity:** `k`-node positive-definiteness of the theta center-mixed
  density at fixed `k` is a low-resolution statement; a positive proportion of off-line zeros at height `T`
  is invisible to it unless `k ≳ log T`, where the all-node wall is RH. No proportion transfer.
- **C18 B2 with the C9 curvature cap:** near-pair CGG cost `≤ δ_max²·B₂` uniformly in the number of pairs,
  so pairs with `a ≤ a₀` cost at most `c·a₀²` in total; with `c ≈ 0.2` the CGG/AF crossing is ≈ 0.69, with
  `c ≈ 1` ≈ 0.677. Any such hybrid stays below the CGG value `19/27` (θ = ½), so it can't reach 3/4.
  Far pairs: the bilinear correction grows like `e^{a}` and the first-moment correction like
  `e^{(1+θ)a}`, against isolated-pair density `≲ A²e^{−2A}` from the Zeta23 slack. The constants
  integrate to `O(N|G|)`, comparable to `S₁`; couples and clusters are excluded. BLOCKED at the
  rate-2 border (coherence–balance, g75-1012 F7). A record candidate only, not a 75% route.

- **C20–C27 (quick kills):** Davenport–Heilbronn/Epstein comparisons (no Euler product, no transfer);
  reflecting the Vinogradov–Korobov region (nothing near ½); convexity of `N(σ,T)` in σ (unproved, and blind
  at σ → ½); large-sieve zero detection near the line (constant `≫ 1` as `A → 0`); displacement moment problems
  (moments cannot bound the atom at displacement 0 from below: order law); all-`c` rank–trace LP (`c = 2`
  is optimal for simple pairs: `p ≤ (κ−1)/(4c − 2 − c²)`, maximal denominator at `c = 2`); symmetric windows
  `[−2T,−T] ∪ [T,2T]` (same zeros reflected). All FALSE or BLOCKED.
- **C28 Hermitian Montgomery form as a density bound:** `(2/π)∫|Σ_ρ x^{ρ−½}/(1+(t−γ)²)|²dt` is known for
  `x = T^α`, `α < 1` (BGSTB, corpus `montgomeryForm_eq_integral_height`); an isolated zero at displacement
  `A/L` forces mass `≍ e^{2αA}`, so isolated far zeros have density `≪ e^{−2αA}N` (rate → 2). Couples with
  cancelling phases hide. REDISCOVERED (g75-1012 cycle 14); this is exactly the border rate of C18.

- **C29 displacement-damping analytic weights** (CGG weights `G·W` with `|W| ≈ e^{−cL²x²}` at displacement
  `x`, to kill far pairs): an entire `W` that decays in displacement grows like `e^{cL²(γ−γ₀)²}` in height
  (`W = exp(−c(s−½−iγ₀)²)`), so localization survives only on windows `≍ 1/L`, and the contour integral
  along `Re s = 1 + ε` diverges. Analytic weights cannot localize in both directions (Phragmén–Lindelöf;
  cf. Lamzouri: no nonconstant entire kernel has `Re K ≥ 0` on `ℂ`). FALSE.
- **C30 variance by sieve majorants** (a "spectral sieve" `F ≤ Υ` on `(1, 4/3)`): `F` there is a short-interval
  prime variance, a small difference of two quantities of size `H²`; a sieve majorant overcounts the mean by
  `(Υ − 1)H² ≫ H log x`. FALSE (g75-1012 cycle 40). The TTPC `Υ = 2` model is not a sieve theorem.

- **C31 negative SDP tail (Chirre–Gonçalves–de Laat `0.6792`)**: discards `∫_{|α|>1} F r̂ ≤ 0`
  using real-ordinate `F ≥ 0`; the off-RH compression has a positive frame metric, so the tail cannot
  be negative. REDISCOVERED (`zeta-analysis/zeta23-beyond-bandwidth-one-proportion.md`).
- **C32 averaged Hardy–Littlewood (long shift ranges) for the TTPC surplus**: at `λ = 4/3` the shifts
  are `h ≤ H = X^{1/4} > X^{8/33}`, but the surplus main term is `≍ H` times the budget, so it needs a
  power saving `H^{-1}` in `Σ_h w(h)(Σ_n Λ(n)Λ(n+h) − 𝔖(h)X)`; long-shift-range averages save only
  powers of `log X`, and the Cauchy–Schwarz route needs the short-interval prime variance. FALSE.
- **C33 heat-flow landing count**: under forward heat flow a complex pair at height `y` obeys
  `(y²)' ≤ −2`, so pairs within `A/L` are real by time `t_A ≍ A²/L²`; then
  `N − N₀ ≤ (far copies ≤ N/A) + 2·#(close real pairs of H_{t_A} at gap ≲ A/L)`. Bounding the close
  pairs at `A ≍ 10` needs pair correlation at several mean spacings, and small `A` loses the far
  bound. Continuity again (the flow is a continuous deformation). BLOCKED.
- **C34 per-zero cost table of the `c`-family**: off-line pair `c²/2`, on-line double
  `k_c(2)/2 = 2c − 2`, simple `2c − 1`; `c²/2 − (2c − 2) = (c − 2)²/2 ≥ 0`, so no `c` charges a near
  pair less than a double, and pairs cost more than simple zeros once `c > 2 + √2`. TRUE; this is the
  certificate form of the continuity barrier: inside the explicit-formula Gram paradigm (traces of
  order `≤ 2`, bandwidth `≤ 1`) the `0.6725` LP optimum is final.

- **C35 Laguerre zeros as a discontinuous census**: `(log Ξ)''(t) = −Σ(t − γ_ρ)^{−2}` has two *real*
  zeros `γ ± δ` at an off-line pair, none at an on-line double, and two at `γ ± iε` for an on-line
  pair of gap `2ε`. Real zeros of `L = Ξ'² − ΞΞ''` count off-line pairs exactly, but every Jensen,
  Littlewood or `L²` bound on them is continuous across the collision `ε → 0 → δ`. BLOCKED (the corpus
  `xiSliceCoeff_two_re_neg_near_offLine_pair` is the local sign statement).
- **C36 sign changes at Gram-type grids by second and fourth moments**: the count of opposite-sign
  neighbours is `≥ (Σ_opp|Z_nZ_{n+1}|)²/Σ(Z_nZ_{n+1})²`; at Gram spacing the anticorrelation is
  moderate (Gram's law fails a positive proportion of the time), at finer grids the crossing products
  vanish. Sign-change detection by moments stays far below `3/4`. FALSE as a route.
- **C37 barrier classification**: every quantitative zero statistic in the corpus is either an
  analytic test sum (order law, continuous), a `log|·|` integral (Littlewood/Jensen, continuous) or a
  mean square (continuous). The only discontinuous inputs are sign changes of real functions on the
  line (Hardy `Z`, Gram/Rosser) and exact multiplicity integrality (rank–trace `k_c`); the first gives
  only lower bounds at low efficiency, the second cannot separate a near pair from a double (C34).
  Hence `3/4` needs, for any continuous method, `≤ 1/4` of the zeros in doubles under the same inputs,
  i.e. a new simple-zero theorem beyond the RH-conditional record `19/27`.

- **C38 the `c`-family LP**: with `k = 1 − HD(1)`, the level-`c` certificate reads
  `A(c)S_off + B(c)M_off ≤ k` (per copy, `A = 2c − 1 − c²/2`, `B = 2c − 1 − c²/4` for doubled pairs).
  `max S_off + M_off = k` at `c = 2` (no level does better: `A ≤ 1`); `max M_off = k/(3/2 + √2)` at
  `c = 2 + √2` where `A = 0` (Lamzouri's `0.8876`). TRUE; the second is formalized
  (`Zeta23SimpleOrCriticalOptimal.lean`), the first is the final word of the paradigm for `3/4`.
- **C39 Chebyshev-system sign detection** (`Z` has `≥ k` sign changes on `I` if `|∫_I Zp| < ∫_I|Z||p|`
  for every `p` of degree `< k` with roots in `I`): exact, but evaluating the supremum needs the local
  law of `Z` at scale `1/L`. BLOCKED.
- **C40 families with larger bandwidth** (Dirichlet characters mod `q`, hybrid large sieve: `H(√3) = 0.845`
  on family average): `ζ` is a `1/φ(q)` fraction of the family, so no transfer to `ζ`. FALSE.
- **C41 negative discrete moments** (`J_{−1} = Σ|ζ'(ρ)|^{−2}` charges a near pair `≍ δ^{−2}`): an upper
  bound for `J_{−1}` is open even under RH. BLOCKED.

- **C42 unconditional Weil positivity on short support** (Connes–Consani, `|log x| ≤ ½ log 2`): fixed
  support is bandwidth `→ 0` in units of `log T`; it cannot resolve individual zeros at height `T`. FALSE.
- **C43 Jensen-polynomial hyperbolicity** (Griffin–Ono–Rolen–Zagier: `J^{d,n}` hyperbolic for `n ≥ N(d)`):
  a statement about Taylor data of `Ξ` at the centre; no census at height `T`. FALSE.
- **C44 winding along `Re s = ½ + δ`**: `#{β > ½ + δ}` equals the defect between the continuous
  vertical winding and `θ + πS_δ`; computing it needs `arg ζ` along the whole line, not its endpoints.
  REDISCOVERED (argument principle).
- **C45 mixed-bandwidth or cubic spectral tests**: `tr(Ĝ_{λ₁}Ĝ_{λ₂})` needs `F` on `(λ₁ + λ₂)/2 ≤ 1`, cubic
  traces need `3λ ≤ 1` (Rudnick–Sarnak), where the Gram rank is `≤ N/3` and `H(1/3) < 0`. FALSE.

- **C46 Hermite signature** (for real test functions, `u ↦ Σ_ρ m_ρ u(γ_ρ)²` has `n₋ = #` off-line
  pairs it separates): exact and discontinuous, but `n₋` is invisible to the two computable moments;
  near pairs give eigenvalues `−O(a²)`. REDISCOVERED (C15, rank–trace `n₊(Q) ≤ p`).
- **C47 Hermite–Biehler decompositions `ξ = G + G*`** (`N₀ ≥ N − 2N⁺(G)` exactly, any odd `H` in
  `G = ½ξ + H`): any `H` built continuously from `ξ` vanishes at a coalesced pair's centre to leading
  order, so `G` keeps a right zero `≍ δ²` per pair and `N⁺(G)` is again bounded only by Littlewood.
  BLOCKED (Levinson's Jensen floor, every `H`).
- **C48 negative moments `∫|ζ(½+it)|^{−2s}`, `¼ < s < ½`**: finite at simple zeros, infinite at doubles,
  `≍ δ^{1−4s}` at near pairs, so an upper bound would separate; no unconditional upper bound exists
  (one multiple critical zero already makes it infinite). FALSE as a route.
- **C49 HC75 anti-causal energy** (`E_W ≥ 2Σ m_j²/a_j`, `N_off < E_W/2`): the `1/a` weight escapes
  continuity, and `E_W ≤ (½ + o(1))N` would give `3/4`; its global form is RH-equivalent and no
  height-local source bound is known. BLOCKED (other agents' lane, `zeta23-beyond-bandwidth-one-proportion.md`).
- **C50 variance at `x^{1/4}` decomposed**: `Var(ψ, x^{1/4}) ≪ H log x` needs both
  `Σ_ρ e^{2λ a_ρ} ≤ (1 + c)N` at `λ = 4/3` (near-line exponential moment, beyond density
  hypothesis) and ordinate pair correlation beyond `1`. Two independent walls. BLOCKED.

- **C51 circle method for the coalescent surplus**: the surplus is `∫|S(α)|² Hψ̂(Hα)dα` with a zero-mean
  shape `ψ` at `H = X^{1/4}`; the zero mean removes the `α = 0` peak, but minor arcs inside
  `|α| ≲ 1/H` carry `≍ X log X` by Parseval, the same order as the budget, and pointwise Vinogradov
  bounds are `≥ X^{3/2}`. An asymptotic needs cancellation in `∫_minor |S|²ψ̂`, i.e. the variance
  itself. BLOCKED.
- **C52 integrality of the Gram rank**: `n₋(Â) ≤ p` and `rank Â ≥ (tr Â)²/‖Â‖² = N/κ` bound `p` from
  below or not at all; upper bounds on `p` come only from `n₊(Q) ≤ p` (rank–trace). FALSE.

- **C53 `a`-points as `a → 0`**: near a simple zero the `a`-point moves by `a/ζ'(ρ)`, near a double or a
  coalesced pair by `≍ √a`, so displacement moments of `a`-points detect double-like clusters; but
  their Littlewood form needs `∫ log|ζ(½+it) − a|`, whose `a`-expansion involves `∫ 1/ζ(½+it)` (C48).
  BLOCKED; and they would not separate pairs from doubles anyway.
- **C54 Dedekind zeta of quadratic fields** (`ζ_K = ζ·L(·, χ_d)` averaged over `d`): the `ζ–ζ` block is
  common to every member, so the large sieve over `d` leaves `ζ`'s own bandwidth-`1` Gram untouched.
  REDISCOVERED (g75-1012 cycle 66).
- **S2 (formalized, side result)**: by the far-mass bound at `A = 4`, at least `3/4` of the zero copies
  in `(T, 2T]` lie within `4/log T` of the critical line (`three_quarters_within_four_div_log`). Distance,
  not membership.

- **C55 Möbius explicit formula** (`M(x) = Σ x^ρ/(ρζ'(ρ))`): a coalescing pair contributes
  `x^ρ log x/(cρ)` in the limit, continuously; mean-square upper bounds for `M(x)/x^{1/2}` are
  RH-strength. FALSE.
- **C56 vector-valued windows** (stack several profiles, rank–trace on `u_ρ = (φ_i(γ_ρ))_i`): the
  Frobenius kernel `‖K(x)‖_F²` is a sum of autocorrelations of functions supported in `[−λ, λ]`,
  and in one dimension every such positive-definite function is a single autocorrelation
  (Krein–Boas–Kac); per-zero costs are unchanged. Montgomery–Taylor's scalar optimum is also the
  vector optimum. FALSE.
- **C57 frame/Riesz structure at Nyquist density**: at `λ = 1` the zeros have exactly the Nyquist
  density of `PW_λ`, and a Riesz sequence cannot coalesce; but the Gram's spectrum beyond its first
  two moments is not source-computable, and complete interpolation for the de Branges space of
  `ξ` presupposes RH. BLOCKED.

- **C58 Selberg's unconditional `S(t)` variance as a real-ordinate statistic**: `N(t+h) − N(t)` counts
  by ordinate, so an off-line pair is an ordinate double there; independent random doubling would
  add variance linear in `hL`, against Selberg's `(1/π²)log(hL)`. But every configuration with
  `F(α) ≈ α` on `[0, 1]` already has logarithmic number variance (small `α` governs large scales),
  and at `h ≍ 1/L` Selberg's error term is as large as the main term. Real-ordinate Montgomery
  reproduces `2/3` (an ordinate of multiplicity `1` is a simple critical zero). FALSE.

- **C59 Hermite–Biehler with the exact approximate-functional-equation half**
  (`G(s) = (2πi)^{−1}∫ξ(s + w)e^{w²}dw/w`, `ξ = G + G*`): `N₀ ≥ N − 2N⁺(G)` is exact, but `G` is the
  smoothed Dirichlet half of length `√t`, with no dominant term on `σ > ½`; `N⁺(G)` is again bounded
  only through `∫ log|GM|`. REDISCOVERED (Levinson, C47).
- **C60 strength of the anti-causal budget**: in natural units a strict-right zero at displacement
  `c/L` costs `≍ L/c` in `E_W`, so `E_W ≤ (½ + o(1))N` forces `o(N)` off-line zeros within any `c/L`.
  That is an almost-all-on-the-line statement, far stronger than `3/4`; it is not an intermediate
  step. TRUE as an assessment of C49.
- **S3 (formalized, side result)**: the optimal level `2 + √2` runs through Theorem D for `L(s, χ)`:
  `≥ 0.8876…` simple-or-critical for every primitive `χ` (`Zeta23DirichletSimpleOrCriticalOptimal.lean`).

- **C61 trace-aware rank–trace** (replace `2c tr Q₊ − ‖Q₊‖² ≤ c²b` by
  `≤ bφ_c(T/b)`, `T = tr Q ≥ N_off − δN`, `φ_c(u) = c²` for `u ≤ c`, `2cu − u²` for `u ≥ c`, by
  Cauchy–Schwarz on the positive spectrum): over all levels the constraint becomes
  `b·u(u − 1) ≤ 1 − HD(1)` with `u = N_off/b ∈ [2, 4]`, since `sup_c[(2c − 1)u − φ_c(u)] = u(u − 1)`.
  Off-line copies: `N_off ≤ (1 − HD)/(u − 1) ≤ 1 − HD` (no gain for `3/4`); off-line double copies:
  `M_off ≤ (1 − HD)·max_α (1 − α²)/(3 − α) = (6 − 4√2)(1 − HD)`, attained at simple-pair fraction
  `α = 3 − 2√2`. This equals `(1 − HD)/(3/2 + √2)`: Lamzouri's constant is optimal for the
  trace-aware certificate too. TRUE, no gain.

- **C62 Vaughan/Heath-Brown decomposition of the coalescent surplus**: Type-I pieces need primes in
  progressions with power saving (Bombieri–Vinogradov saves only logarithms), Type-II pieces meet the
  parity barrier; long-range exceptional-set methods (power saving in `L²` over shifts) lose `√H` when
  paired with the smooth zero-mean weight. BLOCKED.
- **C63 large sieve over the ordinates**: `∫_a^b F ≤ (b − a) + C/(δL)` needs ordinate separation `δ`,
  which is the clustering being bounded: beyond `α = 1`, `F` is the close-pair statistic itself. The
  only exit is the prime side (short-interval variance). CIRCULAR.
- **C64 stability of the Montgomery–Taylor extremum**: near-extremal configurations would have to be
  excluded by an extra constraint; `n`-level Rudnick–Sarnak data plus positivity reproduce the
  two-point LP exactly (g75-1012), and the integrality of counts gives only lower bounds on the
  number variance, which doubles satisfy more easily. FALSE.

- **C65 Laguerre non-concavity measure**: `(log|Ξ|)'' = −Σ Re (t − γ_ρ)^{−2}` is negative except near
  off-line pairs, and a pair at depth `δ` contributes `∫((log|Ξ|)'')₊ ≈ 2/δ`, an anti-continuous weight
  (corpus local signs: `xiSliceCoeff_two_re_neg_near_offLine_pair`, `xiSliceCoeff_re_pos_of_offLine_nearDouble`).
  But the critical zeros make `(log|Ξ|)''` a finite-part distribution, so its positive part is not
  a boundary term, and any bound `≪ N` would force `o(N)` near-line pairs (RH-adjacent, like C60).
  BLOCKED.

- **C66 Kloosterman/Kuznetsov averaging for the beyond-Nyquist off-diagonal**: the `GL(2)` spectrum
  is the hidden family behind mollifiers past `θ = ½` (Conrey's `4/7`); it handles shifted
  convolutions of divisor-type coefficients (`μ ⋆ P`), but the pair-correlation off-diagonal has
  `Λ ⋆ Λ` coefficients, which are parity-blocked. A mollified Gram trades bandwidth for mollifier
  length (C14). FALSE.
- **C67 CGG at the Kloosterman length** (`θ = 4/7`): `988/1331 = 0.7423 < 3/4` even under RH
  (`CGGMollifier.ratio_bound_four_sevenths`); `3/4` needs `θ ≥ 4^{1/3} − 1 = 0.5874`. FALSE.
- **C68 small gaps feed CGG**: if a proportion `a` of simple zeros had `|ζ'M(ρ)| ≤ ε`, splitting the
  Cauchy–Schwarz gains `≈ a`; pair correlation on `[0, 1]` forces gaps `< 0.77` mean spacings
  (Montgomery–Odlyzko), giving only `|ζ'| ≍ g` with `g` bounded below, not tiny values. Gain small;
  REDISCOVERED (g75-1012 C100).

- **C69 the RH-side twin of the barrier**: under RH the zeros of `ζ'` on the critical line are exactly
  the multiple zeros of `ζ` (Speiser), and a close simple pair puts a `ζ'`-zero at distance
  `≍ g²L` from the line; Littlewood counts cannot separate the two. CGG escapes only because its
  conclusion (simple zeros with `ζ'M` not small) is itself continuous, and it reaches `3/4` only at
  `θ ≥ 0.5874`. So the unconditional `3/4` needs both walls at once: a CGG length beyond Kloosterman
  and an off-line (bilinear) transfer past the rate-`2` border. BLOCKED.

- **C70 variants on the line** (all REDISCOVERED or FALSE): shifted products `ζ(s)ζ(s + iα)` (pair
  correlation at shift `α`, same data); test functions in `|s − ½|²` (not analytic, no prime side);
  realness of `e^{iθ}ζ` on the line (holds for every configuration); counting critical points of `Z`
  (`≤ N_ξ' ≈ N`, no contradiction with off-line pairs); TTPC narrow strip by unsigned sieves
  (`T^{2δ}` times the budget at fixed `δ`; quadratic only for `δ ≪ 1/log T`).
- **S4 (formalized, side result)**: at the Montgomery–Taylor constant the ordinate census reads
  `≥ 2HD(1)/(1 + HD(1)) − ε = 0.8042…` (`critical_ordinates_montgomeryTaylor`, `HD_one_le_one`).

- **C72 non-even windows to get a first-order displacement term**: for the reflected pair
  `γ ± ia`, a linear statistic gives `h(γ − ia) + h(γ + ia)` and a Gram statistic gives
  `K(2ia)K*(2ia) + K(−2ia)K*(−2ia)`; in both the odd orders in `a` cancel between the two members of
  the pair, whatever the symmetry of `h` or `K`. TRUE as a structural law: the functional-equation
  pairing makes every analytic source statistic even in the displacement, so `O(a²)` (the order
  law) is forced, not a feature of the chosen window. Only `log|·|` statistics (Littlewood) reach
  first order (`Σ(β − ½)⁺`), and nothing reaches order `0`. FALSE as a route.
- **C73 small values of `|ζ(½ + it)|` (Selberg CLT)**: a near pair lowers `|ζ|` by `≍ a²` on an interval
  of length `≍ a/L`; the CLT resolves `log|ζ|` only at scale `√(log log T)`. FALSE.

- **C74 first moment of `ζ'/ζ` along `Re s = ½ + η`**: `∫_T^{2T} Re(ζ'/ζ)(½ + η + it)dt = π(N − 2R_η)` up to
  edge and smooth terms, an order-`0` count; but the integral is the vertical change of `arg ζ`, so
  evaluating it is the argument principle (C44), and no mean-value theorem linearizes `ζ'/ζ` below
  `σ = 1`. REDISCOVERED.
- **C75 dominance mechanism of Bombieri–Hejhal**: linear combinations of `L`-functions with one
  functional equation have almost all zeros on the line because one summand dominates at most
  heights (independent Selberg Gaussians); `ζ` alone has no second summand to dominate. FALSE for `ζ`,
  but it shows the obstruction is not the Euler product as such.

- **C76 Riemann–Siegel phase monotonicity**: `Z = 2|D| cos(θ + arg D)` with `D` the Riemann–Siegel
  sum; all zeros in `[T, 2T]` are critical if `(arg D)' > −L/2` throughout, and off-line pairs are
  exactly the backtracks of the phase across `πℤ`. The measure of the backtrack set is `≍ Σ δ_p`
  (continuous), and counting backtracks is Levinson's `N⁺` of the approximate-functional-equation
  half (C59). REDISCOVERED.
- **C77 unconditional bilinear CGG as a milestone below `3/4`**: far pairs at macroscopic depth
  `η` contribute `≍ T^{(1+θ)η}` against density `T^{1 − cη}` with `c ≤ 8/7 < 1 + θ` near the line, so
  even a weak unconditional CGG proportion needs density-hypothesis-strength input. FALSE.

- **C78 windows with vanishing moments to kill the inner lobe**: the coalescent kernel is
  `cosTransform Ω` with `Ω = u⁴ ≥ 0`, so `∫Ω > 0` and no moment can vanish; the inner lobe's positive
  mass `≍ T` is balanced only by the outer lobes (`∫ Ω̂ = 2πΩ(0) = 0`). Per dyadic block `P ≍ T^{4/3}`
  the requirement is `|Σ_h ψ(h/H)(Σ_{p∼P}Λ(p)Λ(p+h) − 𝔖(h)P)| ≪ P log T` with `H = P/T`; by
  Cauchy–Schwarz this needs the mean-square error over shifts at `≪ HP`, i.e. square-root
  cancellation on average (Mikawa saves only `log^A`). FALSE (sharpens C51/C62).

- **C79 low-rank non-self-adjointness**: a model `H + iK` puts at most `rank K` eigenvalues off the real
  axis, an order-`0` bound. For ζ the natural operator is the aperture-truncated Weil form, whose
  negative index counts the visible off-line pairs (`P + Q`, `n₋ ≤ p`); but only its trace and
  Frobenius norm are evaluable from primes (Montgomery–Vaughan), while entrywise prime sums do not
  determine the inertia; Schur's `Σ|Im λ|² ≤ ‖Im A‖_F²` is order `a²`. FALSE.

- **C80 angular Hecke families over `ℚ(i)`**: `ζ_{ℚ(i)} = ζ·L(·, χ₋₄)` is the `k = 0` member of the family of
  angular Grössencharacter `L`-functions, whose large sieve exceeds bandwidth `1` on family average;
  `ζ` remains a vanishing fraction of the family (C40, C54). FALSE.

- **C81 dominance of the first Riemann–Siegel term**: `Z = 2cos θ + P`, `P = 2Σ_{2≤n≤√(t/2π)} n^{−1/2}cos(θ − t log n)`;
  `2cos θ` alone has exactly the mean number of zeros, but `‖P‖₂² ≍ log T`, so `|P| < 2` fails at most
  Gram points; Gram's-law statistics are not dominance statistics. Turing's comparison of `∫S` with
  the sign-change count needs the sign-change count itself. FALSE.
- **C83 Cauchy-transform test functions** (`h(z) = ∫w(t)(z − t − iε)^{−1}dt`): `Σ_ρ m_ρ Im h(γ_ρ)` counts critical zeros
  as `π`, pairs with depth `< ε` as `2π` and deeper pairs as `0`, an order-`0` statistic; but `h` is
  singular on `Im z = ε` inside the strip, so it is not an admissible explicit-formula test, and its
  value is the vertical argument change (C44, C74). TRUE as the reason for the barrier: explicit-formula
  tests are analytic across the strip, and order-`0` counting needs a singularity there. FALSE as a route.
- **C84 Goldston–Yıldırım splitting `Λ = Λ_R + E`** in the bandwidth-`4/3` Frobenius `‖Γ − Π_Λ‖²`: the
  `Λ_R`-parts are divisor sums (computable through Bombieri–Vinogradov and Kloosterman), but
  `‖Γ − Π_{Λ_R} − Π_E‖² ≤ (1 + η)‖Γ − Π_{Λ_R}‖² + (1 + η^{−1})‖Π_E‖²` leaves `‖Π_E‖²`, whose Montgomery–Vaughan
  size `Σ_{n≤X}|E(n)|² n ≍ X²(1 − θ)log X` exceeds the budget by `T^{1/3}`; sieve majorants `Λ⁺ ≥ Λ` need a
  nonnegative kernel and then overcount the mean by `(Υ² − 1)`. REDISCOVERED (C30).
- **C85 negative inertia and determinant parity**: each non-degenerate pair block has inertia `(1, 1)`
  whatever its depth, so `n₋(Q) = p` is order `0`; but in any certificate built from `tr` and `‖·‖²` a
  negative eigenvalue `−η` enters as `−2cη − η² = O(a²)`, and `n₋(Â)`, `sgn det Â = (−1)^{n₋(Â)}` need the
  whole spectrum (`tr log|Â|`). FALSE.
- **C86 bandwidth `1 + O(1/log T)` (prime length `X = CT`)**: Montgomery–Vaughan's off-diagonal term
  `O(Σ n|a_n|²)` stays within a constant `B(C)` of the budget, so `F ≤ B` on average over
  `(1, 1 + log C/log T]` and the exchange rate gains `≍ log C/log T → 0`; any fixed `δ > 0` costs
  `T^δ`. Windows with Gaussian tails put negligible weight beyond `α = 1`. FALSE (no fixed gain).
- **C87 sign changes on a fine grid** (the one discontinuous route): with `t_n = nδ/L`, the count of
  `Z(t_n)Z(t_{n+1}) < 0` reaches most odd-order critical zeros as `δ → 0` (GUE: `≈ 0.9N` already at
  `δ = π`). Lower bounds need `Σ|Z_nZ_{n+1}| ≥ (ΣY²)^{3/2}/(ΣY⁴)^{1/2}`, i.e. shifted eighth moments
  (unknown); with a mollifier `M`, `Σ(ZM²)_n(ZM²)_{n+1}` would count sign changes exactly only if
  `|ζM|² ≡ 1`, while at `θ = 4/7` the mollified mean square stays `≍ (1 + c/θ)T`. Efficiency of known
  forms is a few percent. BLOCKED.
- **C88 what the discontinuous route must prove**: sign changes count distinct odd-order critical zeros,
  so near pairs and doubles are both excluded and the continuity barrier does not bind; but a
  sign-change proof of `3/4` proves `≥ 3/4` distinct odd critical zeros, which under RH is beyond the
  record `19/27` (Montgomery–Taylor/CGdL give only `N_d − (κ − 1)N/2 ≥ 0.60N`). Both routes therefore end
  at an RH-conditional open problem: double-like zeros `≤ 1/4` (continuous) or odd distinct `≥ 3/4`
  (discontinuous). TRUE as a classification; no route.
- **C89 Montgomery's method for the weighted zero measure `Σ_ρ ζ'M(ρ)δ_{γ_ρ}`**: the weights vanish at
  multiple zeros, so its Gram `P_w` has rank `≤ N_s`, and `N_s ≥ (tr P_w)²/‖P_w‖_F²`; `tr P_w` is CGG's
  Hermitian moment, but `‖P_w‖_F²` carries the diagonal `Σ|ζ'M(ρ)|⁴` (mollified discrete fourth moment
  of `ζ'`, unknown) and a `|ζ'M|²`-weighted pair correlation. REDISCOVERED (g75-1012 C100, open core
  `M₄`). This is the RH-side input that a pair-correlation proof of `3/4` simple zeros would need.
- **C90 joint Gram of the zeros of `ζ` and of one `L(s, χ)`**: the union has twice the density, the prime
  side is the Dirichlet polynomial with coefficients `Λ(n)(1 + χ(n))`, and Montgomery–Vaughan still caps
  its length at `T`, so the bandwidth relative to the union is halved; independence of the two zero
  sets is visible only on average over `χ`. FALSE.
- **C91 operator-norm rank bound** (`N_s ≥ rank P_w ≥ tr P_w/‖P_w‖_op`): `‖P_w‖_op` is a weighted large sieve
  over the zeros, dominated by `max_ρ|ζ'M(ρ)|²`. FALSE.
- **C92 discrete log-moment `Σ_ρ log|ζ'(ρ)|`**: a near pair gives `log|ζ'| ≈ log δ` and a double `−∞`, so a lower
  bound `≥ cN` would cap them with weight `log(1/δ)`; by the resultant identity it equals
  `Σ_{ζ'(ρ')=0} log|ζ(ρ')|` plus boundary terms. Jensen gives only upper bounds on log-moments;
  lower bounds are small-value problems (open even under RH). BLOCKED.
- **C93 contour sums of `(ξ'/ξ)²h`** (to reach `m_ρ²` through double poles; the right edge is the
  Dirichlet series of `Λ ⋆ Λ`): the residues give `Σ m_ρ²h'(γ_ρ)` plus the pair statistic
  `Σ_{ρ≠ρ'} m m'(h(γ_ρ) − h(γ_ρ'))/(ρ − ρ')`; for a coalescing pair the divided difference tends to the
  derivative and the sum tends to the double's `4h'(γ)`. Divided differences are confluent, hence
  continuous. FALSE.
- **C94 Selberg trace formula for `SL₂(ℤ)` and Kuznetsov**: the zeros of `ζ` are resonances of the modular
  surface (poles of `ξ(2s − 1)/ξ(2s)` at `s = ρ/2`) and contribute `≍ x^{β/2} ≤ x^{1/2}` to the prime geodesic
  counting function, below its known error `x^{25/36}`; Kuznetsov averages the `GL(2)` spectrum and
  reaches shifted convolutions of `d(n)` (Motohashi), not of `Λ` (parity). No new constraint on `ζ`'s
  zeros. FALSE.
- **C95 the adjacent target where averaging exists** (g75-1012 F57b): for primitive `χ` mod `q ∈ [Q, 2Q]`
  averaged with heights, an asymptotic large sieve (`R = 1 + o(1)` for the family off-diagonal, the
  Conrey–Iwaniec–Soundararajan type) together with a conductor-uniform Theorem E would give a family
  average `≥ 1 − 1/(3λ²)` (`≥ 3/4` at `λ = 4/3`) with no GRH. It is the strongest `3/4` statement within
  reach of known technology, but `ζ` is one member of measure zero in the family. REDISCOVERED; recorded
  as the adjacent milestone, not a route.
- **C96 amplifying `χ₀` inside the family**: weights `|Σ_{ℓ≤ℓ₀} x_ℓ χ(ℓ)|²` give `χ₀` the share `≍ ℓ₀/φ(q)`, and the
  weighted large sieve admits prime length `X ≲ q²T/ℓ₀²`; a positive share for `ζ` (`ℓ₀ ≍ q`) returns `X ≲ T`,
  bandwidth `1`. The trade `ζ-share × bandwidth gain ≲ 1` is exact. REDISCOVERED (g75-1012 cycle 69).
- **C97 real-rootedness counts for `Ξ`** (Newton/Hutchinson sign rules on Taylor coefficients, Jensen
  polynomials at a shifted centre `T`): coefficient rules are global in height, and low-degree Jensen
  hyperbolicity at centre `T` is the local Laguerre inequality (C35), failing on a set of measure
  `≍ Σ δ_p`. FALSE.
- **C98 backward heat flow from `Λ ≤ 0.22`**: all zeros of `Ξ_{0.22}` are real; going back to `t = 0`, two
  real zeros at gap `d` collide within time `≍ d²/8`, and at height `T` the mean gap is `≍ 1/log T`, so every
  gap may collide on the window `[0, 0.22]`; the informative time scale is `1/log²T`, where the flow
  only reproduces the continuity barrier (C33). FALSE.
- **C99 Lamzouri's positive-part terms** (`spectral_four_trace_bound_positivePart`: `+2Σ positivePartForm` on
  simple critical zeros and `+max(Σ‖w_P‖² − 2#pairs, 0)²/#pairs`): the second term is the trace-aware
  correction of C61 (no change at `u = 2`), the first selects which simple critical zeros are counted
  (horizontal isolation) without raising the count. REDISCOVERED; the joint census
  `S + 2M ≤ 1 − HD`, `(3/2 + √2)M ≤ 1 − HD` leaves `N₀ ≥ HD` final.
- **C100 almost-all short-interval PNT into zero sums** (short-interval explicit formula S5 with
  `H = x/T = X^θ`, `θ > 1/6`, corpus `tendsto_volume_psi_short_asymptotic`): `|ψ(x + H) − ψ(x) − H| ≤ εH`
  for almost all `x` gives `|Σ_ρ x^{iγ_ρ}ŵ(γ_ρ/T)| ≤ ε√x + O(√T)`, weaker than the trivial `T log T` for
  bandwidth `α = 1/(1 − θ) < 2`. Information flows from zero density to primes, not back. FALSE.
- **C101 one-sided prime side** (`w ≥ 0` makes `T Σ Λ(n)n^{−1/2}w(T log(n/x)) ≥ 0`): gives
  `Re Σ_ρ x^{iγ_ρ}ŵ ≤ √x ŵ(−i/2T) + O(√T/log x)` for every `x`, i.e. the explicit formula with a nonnegative
  test. Upper bounds on one-level sums only; pair statistics need squares, whose prime sides are prime
  pairs. REDISCOVERED (Weil/Odlyzko positivity).
- **C102 Levinson against the rank–trace adversary**: for `V = ζ + ζ'/L`, locally
  `V/ζ ≈ 1/2 + Σ 1/(u − u_ρ)` (`u = (s − ½ − iγ)L`); two simple critical zeros give two `V`-zeros at
  `Re u = −2`, an off-line pair at `±a` gives `u = −2 ± √(4 + a²)`, one right of the line, and a critical
  double gives `u = 0` (on the line). Near pairs and doubles both cost one `V⁺`-zero: Levinson is
  continuous and counts simple critical zeros. The rank–trace extremal configuration
  (`2/3` simple + near pairs) meets Levinson's `N_V⁺ ≤ 0.29N`, so the joint LP stays at `HD(1)`. TRUE as a
  classification; no gain.
- **C103 every known counting method counts simple-or-odd critical zeros**: rank–trace (continuous),
  Levinson (simple, Heath-Brown/Selberg), sign changes (odd order). A `3/4` proof by any of them
  proves `≥ 3/4` simple-like zeros, under RH beyond `19/27`. The open core of the loop is therefore
  the simple-zero problem plus removing RH. TRUE (classification).
- **C82 ordinate certificates**: an off-line pair is an ordinate double in every real-ordinate
  statistic, and real-ordinate Gram data are not source-computable off RH (C31, C58); the ordinate
  census `4/5` (`#pairs ≤ N/6`) cannot be pushed to the needed `N/8` from ordinates alone. FALSE.

## Requirement map after S1 and C13
Unconditional 75% needs, beyond what is proved: (i) bilinear CGG-type discrete moments of `ζ'M` with
mollifier length `θ` large enough that `1 − (1+θ)^{−3}` clears `3/4` plus curvature and far-pair losses
(`θ ≳ 0.67–0.74`; Kloosterman technology stops at `4/7`), together with aggregate curvature and far-pair
control; or (ii) short-interval prime variance of RH-plus quality at `H = x^{1/4}`. Both lie beyond the
RH-conditional record for simple zeros (`19/27`).

Barrier, in one paragraph (C34, C37, C61, C72). Every source-computable statistic of the zeros is an
analytic test sum, a Gram moment, a `log|·|` integral or a mean square. By the functional-equation
pairing `ρ ↔ 1 − ρ̄`, analytic statistics are even in the displacement (order `a²`); `log|·|` integrals
reach order `a`; none reaches order `0`. A coalesced off-line pair is therefore indistinguishable from
a critical double zero, so a proof of `3/4` by these inputs also proves, under RH, that at most a
quarter of the zeros are double-like. Inside the rank–trace paradigm (traces of order `≤ 2`,
bandwidth `≤ 1`) the LP over all levels and the trace-aware refinement give exactly
`N₀ ≥ HD(1)N` and simple-or-critical `≥ 1 − (1 − HD(1))/(3/2 + √2)`, both formalized; `3/4` needs new
arithmetic input of type (i) or (ii).

## Survivors to formalize
- **S1 (formalized):** off-line multiple zeros are charged twice by the `c = 2` certificate:
  `(2/3 − ε)N + M_off ≤ N₀ˢ`, so `S_off + 2M_off ≤ (1/3 + ε)N` and either `N₀ ≥ 3N/4` or
  `S_off ≥ (1/6 − ε)N`; at the Montgomery–Taylor constant `S_off ≥ (HD(1) − 1/2 − ε)N = 0.1725N`.
  The 75% problem is a bound on simple off-line zeros. The `c = 3` law adds `M_off ≤ (8/11)(1 − GD(1) + ε)N`:
  ≈ 88.1% of zeros are simple or on the line (`Zeta23SimpleOrCriticalCensus.lean`); the `c`-family
  LP is optimal at `c = 2 + √2`, giving Lamzouri's `0.8876…` (`Zeta23SimpleOrCriticalOptimal.lean`).
  Localized: either `N₀ ≥ 3N/4` or `≥ (HD(1) − 1/2 − 1/A − ε)N` simple off-line zeros lie within
  `A/log T` of the line (`Zeta23SimpleOffLineNearLine.lean`).
  By ordinate: `≥ (4/5 − ε)` of the zero ordinates carry a critical zero
  (`Zeta23CriticalOrdinateCensus.lean`); the copy count `3/4` is the ordinate count with each
  off-line ordinate charged twice.
  Card `3-formalized/zeta-off-line-multiple-exclusion-and-simple-off-line-core.md`; module
  `RHTower/Zeta23OffLineMultipleExclusion.lean`, `…MontgomeryTaylor.lean`.
- **S5 (formalized):** smoothed Landau formula over all zeros, unconditional:
  `|Σ_ρ m_ρ x^{ρ−½}ŵ(γ_ρ/T) + T w(0)Λ(x)/√x| ≤ 2e^{1/2}‖w‖₁√x + K√T/log x` for `T ≥ x + 2`
  (`RHTower/ZetaSmoothedLandauFormula.lean`, card `3-formalized/zeta-smoothed-landau-formula.md`).
  Input for discrete moments over zeros.

## Log
- 2026-10-25 — created; corpus frontier re-read (Zeta23, TTPC, ACS, g75-1012).
