# Horizontal Lamzouri inequality: unconditional horizontal simplicity of zeta zeros

- **ID:** horizontal-lamzouri-inequality-loop
- **Stage:** 1-in-progress
- **Type:** CONJECTURE loop (hgtl7), route WD (RH ⇔ ordinate injectivity)
- **Source:** Lamzouri, arXiv 2609.02882 (Prop. 2.1); Alpöge–Furman 2608.13637 (Zeta23 in the corpus);
  BGST 2501.14545 (horizontal multiplicity under a narrow-box hypothesis, Soundararajan's notion);
  corpus `R:XiHorizontalSingletonFiberHalfDensity` (singleton-fibre ratio ≥ (3·HD(1)−1)/2 ≈ 0.5087).
- **Statement (target).** A zero is *horizontally simple* if it is the only zero (with multiplicity) on its
  horizontal line `Im s = γ`. Target: `liminf #{horizontally simple, 0<γ≤T}/N(T) ≥ C₀ = 0.67250…`
  unconditionally (corpus has 0.5087; BGST have horizontal results only under a box hypothesis).

## Frontier audit behind this loop (2026-09-26)
- External SOTA (Sept 2026): unconditional 67.25% simple-critical (Alpöge–Furman; Lamzouri; Wang +6.7e-8),
  short intervals (Wang 2609.07918), prime-modulus families at 0.6725 (Hua–Yang 2608.16034, 2609.27808).
  CGdL 0.6792 and CGG 19/27 are conditional on RH.
- Bandwidth wall for ζ: any unconditional pair-correlation input beyond |α|≤1 needs prime-pair asymptotics.
  Sieve upper bounds (constant 4) make the off-diagonal ≍ H/log x, usable only for α−1 ≲ log log T/log T
  (improvement → 0). Triple correlations with Σ|u|<2 give a third-moment bound B₃ ≈ 11 ≫ 1.98 needed. Both KILLED.
- Mollifier-free near-line density from the pair form: KILLED (clusters at the typical scale absorb the
  e^{2bL} self-excess; corpus `offline-isolation-dichotomy` 2026-09-19 cycle).
- Dominant/spaced off-line zeros obey DH: REDISCOVERED (corpus `MontgomerySpacedZeroDetection`; Maynard–Pratt).
- Family (q-aspect, bandwidth 2 via Montgomery–Hooley/asymptotic large sieve) + inertia would plausibly give an
  unconditional ≈ 86–91% for the Dirichlet family: SURVIVES but is GRH-for-families, not RH. Parked.

## Kernel setting (Lamzouri)
`η` real even, `supp η ⊂ (−λ,λ)`, `K := (η²)^`, `K(0)=∫η²=1`; `ρ := η²*η²`, `ρ̂ = K²`.
For a conjugation-invariant multiset `Z`: `E := Σ_{z,s} K(z−s)² = ∫ρ(σ)|S(σ)|²dσ`, `S(σ)=Σ_z e^{−2πizσ}`.
Horizontal classes `C_g = {z : Re z = g}`, sizes `H(g)`. Within a class, `K(i v) = ∫η² cosh(2πvu) ≥ 1`.

## Cycle H1 — horizontal Montgomery inequality (H'): `E ≥ Σ_g H(g)²`
- Would give horizontally-simple ≥ 2 − C_MT directly (and a horizontal second-moment bound).
- **Verdict: FALSE** (for the admissible indicator kernel `η = 1_{(−1/2,1/2)}`, `K = sinc`).
  Countermodel: pair `±iy` (small `y`) and triple real points at `d = ±1,…,±D`. Using `K(d)=0` at integers,
  `E − Σ H² = 2(K(2iy)²−1) + 12 Σ_{1≤|d|≤D} Re K(d+iy)²`, `Re K(d+iy)² = −sinh²(πy)(d²−y²)/(π²(d²+y²)²)`;
  small `y`: `≈ (8π²/3)y² − 24 y² Σ_{d≤D} d^{-2} < 0` already for `D = 2`.
  Mechanism: second-order coefficient `c₁ ∝ Σ_z y_z² Σ_{g'} H(g') M₁(x_z − g')`, `M₁(d)=∫ρσ²cos(2πdσ)`,
  negative when the off-line class sits among classes with `H ≥ 3`.
- **Survivor:** the weaker linear form (H) below — the `H ≥ 3` classes that break (H') carry slack
  `(H−1)² − 1 ≥ 3` in (H).

## Cycle H2 — horizontal Lamzouri inequality (H): `#hs(Z) ≥ 2|Z| − E`
- Equivalent forms: (i) spectral: `Σ_i (λ_i(B) − 1)² ≥ D_W − #hs` for Lamzouri's real symmetric `B`;
  (ii) slack form: Lamzouri's slack `s_L := E − 2|Z| + #real-simple ≥ #mixed classes` (mixed class = real simple
  point sharing its ordinate with an off-line pair).
- Evidence: isolated triple `{x, x±iy}`: `tr φ = 3 − 2K(2iy)² − 4K(iy)² ≤ −3`; lattice (indicator) combs of
  equal-`y` pairs are exactly Lamzouri-tight (Poisson: `E = 2|Z|`), and adding a real point on a comb class gives
  slack 4 ≥ 1; alternating/period-2 combs and many real-point surroundings all satisfy (H) with margin.
- **Proved on paper (partial):** Lamzouri's Gram–Schmidt with ranges `U₀ = ⟨f_mult, g_pairs⟩`, then good reals,
  then mixed reals, then `h`'s gives
  `#hs ≥ 2|Z| − E − Σ_{mixed c} (1 − 2t_c − t_c²)⁺`, `t_c = 2K(iy_c)²/(1+K(2iy_c))`,
  since `‖P_{U₀} f_x‖² ≥ t_c` (own `g` in `U₀`, `⟨f_x,g_z⟩ = K(iy)`) and the mixed direction has `α ≤ 1 − t_c`.
  Hence (H) holds whenever every mixed class has `t_c ≥ √2 − 1` (small displacement). Also `t ≥ 2/(2+κ)`,
  `κ = K(2iy)−1`, and the *local* slack of a mixed class is `2 + 4κ + 2κ² + 4t + 2κt − 3 > 0` for all `y`.
- **[OPEN CORE]** large-displacement mixed classes whose `h_z` lies in the span of other classes' `g`'s
  (comb-like surroundings): cross-class contributions in Gram–Schmidt can hide the local slack. Need a global
  argument (not incremental: the field `Σ_s K(x₀−s)²` at a mixed point can be ≪ 0, e.g. −22 for neighbours with
  `y=0.99`, while global slack stays huge).
- Consequence if proved: horizontally simple ≥ C₀ = 0.6725 unconditionally (Lamzouri Lemma 3.2 input), improving
  the corpus 0.5087 and making BGST's horizontal multiplicity result unconditional.

## Log
- 2026-09-26 — loop opened after a full frontier audit (frontier map, killed ledger, endpoints, STATUS tail,
  Montgomery/isolation/theta-power/PM cards, Zeta23, Sept-2026 arXiv). H1 FALSE (paper), H2 partial (paper).

## Cycle H3 — structure of the open core (paper, 2026-09-26)
- **Spectral/Toeplitz form.** `Φ := Σ_z f_z f_z̄* = M_η C_S M_η` (kernel `η(u)η(v)S(u−v)`, `S(τ)=Σ_z e^{−2πizτ}`),
  `tr Φ = |Z|`, `tr Φ² = E`, `Q := ‖Φ − Π_W‖²_HS = E − 2|Z| + D` (`D` = #distinct). Lamzouri ⟺ `Q ≥ D − #rs`;
  (H) ⟺ `Q ≥ D − #hs`.
- **Removal/doubling dichotomy.** For one mixed real `x` with field `G(x) := Σ_{s≠x} K(x−s)²`:
  `σ_L(Z) ≥ 2|G(x)|` (Lamzouri at `Z∖x` and at `Z` with `x` doubled). Gap: `|G(x)| < 1/2`. Weights on `x` do not
  close it (curvature of `Q` in the weight is exactly `K(0)² = 1`).
- **Exact transfer identity.** Replacing `x` by any real configuration `ν = Σ m_j δ_{ξ_j}` in new classes:
  `σ_H(Z) = σ_H(Z') + 2G(x) − 1 + Σ_j(2m_j − [m_j=1]) − 2Σ_j m_j G(ξ_j) − Σ_{j,k} m_j m_k K(ξ_j−ξ_k)²`.
  Induction on #mixed closes (H) whenever `G(x) ≥ 1/2`, `G(x) ≤ −1/2`, or `G(ξ) ≤ −(1−2G(x))/4` somewhere.
  It fails on the defect comb (`G ≥ 0` everywhere, `G(x)=0`) although (H) holds there with slack `≈ 2π²y²`:
  the induction discards the slack of `Z'`.
- **Idealised violator.** `Q(Z) − D + #hs ≈ 4t − 1` exactly when (i) `Z∖x` is Lamzouri-tight, (ii) the own pair is
  absorbed (`⟨Φ'ĝ,ĝ⟩ ≈ 2`), (iii) `r_x := f_x − βg` (`β = 2K(iy)/(1+K(2iy))`) is isolated (`Φ'r_x ≈ 0`).
  Exact isolation ⟺ every other point `s` satisfies `Ψ(s−x)=0`, `Ψ := (η²(1−βcosh 2πyu))^`.
- **Realisation attempt.** Pairs at `Λ = x + {zeros of (cosh(2πyu)(1−βcosh 2πyu))^}` give `U = span g`'s with
  `U^⊥ = span r_x` and `h_p ∈ U` exactly (parity), `‖Π_U f_x‖² = t` exactly — but every other `h_q` leaks
  `|⟨h_q, r̂_x⟩|² ≍ K(iy)²/4` into `U^⊥`, so the Lamzouri slack is huge. Full isolation would need all pair points
  at zeros of `Ψ`, and `Ψ` has only boundedly many non-real zeros (one sign change of `1 − βcosh`).
- **Rigidity heuristic for (H).** If all `h`'s lie in `U` and `ν := Π_{U^⊥} f_x ≠ 0`, then `(ην̄)^` (type `2πλ`) vanishes
  at every pair point. Absorbing a large-`y` pair needs pair classes of density ≥ 1 (exponential cancellation
  over `|τ|<1`), i.e. zero density 2 > 2λ·... = 1 allowed ⇒ `ν = 0`. Exact only for infinite configurations; a
  finite/quantitative version (sampling-theory) is the missing step.
- **Periodic (Bloch) formula.** Period `P`, cell multiset of `m` points: `E_cell = P^{-1} Σ_{|n|<P} ρ(n/P)|A_n|²`,
  `A_n = Σ_cell e^{2πizn/P}`. Exact cancellation of a large-`y` pair forces `P` classes per period ⇒ `m ≥ 2P + #mixed`
  ⇒ `E_cell ≥ ρ(0)m²/P ≥ 2m + 2#mixed`: (H) holds in every exactly-absorbing periodic configuration.
- **Proved (paper), sharpened partial theorem.** Gram–Schmidt order `A = span(f_mult, g)`, hs reals, mixed reals, `h`:
  `Σα_j² ≥ 2|Z| − #hs − #mix + 2T + 4Σ_p m_p‖Π_{A^⊥}h_p‖² + T²/#mix`, `T = Σ_mix ‖Π_A f_x‖²`. No independence needed.
  Horizontal simplicity can miss the Lamzouri bound only through mixed classes whose pair is almost exactly absorbed
  (`h_p ∈ A`) and far off the line (`‖Π_A f_x‖² < √2 − 1`).
- **Zeta tradeoff (paper).** With `t(y)=2K(iy)²/(1+K(2iy))`, `κ(η) := sup_y (1−2t(y))⁺/y`:
  `liminf N_hs/N ≥ C₀ − κ(η)·limsup (Σ_{T<γ≤2T}(β−½)⁺)/T`. Indicator kernel: `t(y) ≈ 2/(πy)`, `κ ≈ 0.2`.
  With the literature first-moment density (STATUS MUST-349 [P] 0.0535) this gives ≈ 0.66 horizontally simple
  (paper, external constant), versus the corpus 0.5087.
- **Verdict H3:** (H) SURVIVES; open core narrowed to a quantitative sampling-rigidity statement. Next: Lean for the
  sharpened partial theorem (abstract real inner-product form).
- **Lean (2026-09-26):** `formal/GaloisForLFunctions/HilbertMetric/HorizontalLamzouriInequality.lean` (711 lines,
  wired into `HilbertMetric`, `lake build` green, axioms = propext/choice/Quot.sound). Abstract real inner-product
  version, no independence, any ambient space: `HorizontalPacket.energy_lower_bound`, `mixedOverlap_sq_le`,
  `card_hs_ge_of_overlap`, `card_hs_ge_of_overlap_ge` (√2−1 criterion), `lamzouri_inequality` (Prop. 2.1 (2.4)),
  `mixedOverlap_ge_ownPair`. STATUS MUST-468.
- **Still open:** the kernel instantiation (`f_z = ηe^{−2πizu}`, `E = Σ K(z−s)²`) and the full (H).

## Cycle H4 — R′ killed; near-line horizontal isolation closed in Lean (2026-09-27)
- **R′ (`2T + 4Λ + T²/#M ≥ #M` always): FALSE as a route.** Double real points at all real zeros of
  `Ψ(x−·)` put `h_p ∈ A` exactly (parity) with `T = t` small and `Λ = 0`. But (H) holds there with slack
  `~2a²`: the pair is not absorbed at the level of Φ (compression eigenvalues `≈ 3 + a`, `3 − a`). So the
  trace-only range-A step is lossy, and absorption must be read from `‖Φ_A − 2I‖²`, not from `h ∈ A`.
- **Unnormalised inequality (paper + Lean).** For `m₂ ≥ 2`, `mP ≥ 1` and arbitrary norms:
  `4·mass − E − 2N + 2Σ_H(1−‖f‖²) + Σ_M(1 + 2‖P_A f‖² − 2‖f‖²) ≤ #H`. A mixed point with `‖f‖ ≤ 1` and
  `‖g_p − f‖ ≤ 1/8` costs nothing, because `2‖f‖² − 2t ≤ 8‖f‖·‖g−f‖`.
- **Theorem (Lean, unconditional).** `≥ (HD(1) − ε)N(T,2T)` zeros are simple, critical, and have no other
  zero on their horizontal line within `2/(3 log(T/2π))` of the critical line. Route: Zeta23 block data
  → `HorizontalPacket` in `ℝ^d` (kernel = normalised sampled matrix), sampling Parseval via
  `hasSum_sq_fourierCoeffOn`, cosh-shift bound, then Zeta23's seam/traces/ThmD endgame unchanged.
  Modules: `HilbertMetric/HorizontalLamzouriUnnormalized`, `RHTower/WindowTransformSamplingParseval`,
  `RHTower/HorizontalIsolationBlockPacket`, `RHTower/HorizontallyIsolatedSimpleZeros` (all built, 0
  warnings, wired). STATUS MUST-469.
- **Open core unchanged:** mixed classes whose off-line zeros are farther than `c/log T` from the line.
  The Toeplitz model says a violator needs symbol "pair comb − one real point" (negative real
  multiplicity). This is plausible evidence that (H) is true, not a proof.

## Cycle H5 — overlap criterion; radius widened to 5/(2 log(T/2π)) (2026-09-27)
- **Overlap criterion (paper + Lean).** Let `F, G` be real sequences on a countable index set with
  `Σ_t F² ≤ 1` for every finite `t`, `ΣFG = K > 0` and `ΣG² = B`. Then every finite `s` has
  `1 + 2(Σ_s FG)²/Σ_s G² − 2Σ_s F² ≥ 2K²/B − 1`. Proof: the identity
  `B(K − sq)² − (K² − s²B)(B − q²) = (Kq − sB)²` on each finite superset, then the limit.
  It is tail-robust: the truncation needs no edge analysis.
- **Zeta side.** Polarised sampling Parseval gives `Σ_k φ̂(w_k) Re ψ̂(w_k) = L∫φψ`. With `ψ = φ cosh(ε·)`,
  whose transform on the real axis is `Re φ̂(w − iε)`: `K = ∫φ²cosh/∫φ² ≥ 1`, `B = ∫φ²cosh²/∫φ² ≤ C·K`,
  `C = cosh(εL/2)`. Hence `2K²/B − 1 ≥ 2/C − 1 ≥ 0` for `C ≤ 2`, which is `δ ≤ 2 arccosh 2 / L ≈ 2.634/L`.
- **Theorem (Lean, unconditional).** The radius in MUST-469 is now `5/(2 log(T/2π))` (was `2/(3 log(T/2π))`),
  which uses `cosh(5/4) ≤ 2`. `RHTower/HorizontallyIsolatedSimpleZeros:horizontallyIsolated_simple_critical`;
  `shift_overlap_cost`, `overlap_criterion`. Axioms: propext, choice, Quot.sound.
- **Limit of this method.** For `εL → ∞` the angle between `φ` and `φ cosh(ε·)` in `L²` tends to `π/2`, since
  `φ` vanishes at the edges where `cosh` concentrates. So single-pair overlap cannot pass `O(1/L)`.
  Far pairs need multi-point absorption (the compression `‖Φ_A − 2I‖²`), not the single `g_p`.

## Cycle H6 — lens isolation in Lean; CGdL relaxation blocked; field = Berezin symbol (2026-09-27)
- **Conjecture H6a (proved, Lean).** Absorption is not only horizontal. A multiple critical zero or an
  off-line zero `z` at `(Δ, ε)` from a simple critical zero `x` costs nothing whenever
  `cosh(εL/2) ≤ 2cos²(ΔL/2)`, `|Δ|L/2 ≤ π/2` (full-grid overlap `≥ cos(ΔL/2)·J`, norm `≤ cosh(εL/2)·J`).
  Theorem: `≥ (HD(1)−ε)N(T,2T)` zeros are simple, critical, and every other zero in that lens is simple
  and critical (`RHTower/LensIsolatedSimpleZeros`, STATUS MUST-472). The lens contains the segment
  `|ε| ≤ 5/(2L)` and the rectangle `|Δ| ≤ 1/L`, `|ε| ≤ 3/(2L)`. Refactor: Zeta23's endgame is now the
  generic `thmD_count_of_seam` (any count dominating the seam); `absorbed_block_count` takes any
  multiple-point or pair absorber.
- **Conjecture H6b (killed).** Unconditional CGdL (`ĝ ≤ 0` outside the band): Fourier side fine (FE ⇒
  `|Σe^{2πiξz}|²`), physical side needs density exponent `> 2R ≥ 2` (STATUS CANNOT-473).
- **Structure (paper).** For `λ ≤ ½` (sinc model) the field `G_W(ξ) = Σ_{s∈W}K(ξ−s)²` is the Berezin
  symbol `⟨Φ_W f_ξ, f_ξ⟩` of `Φ_W` on Paley–Wiener, every comb `{f_{ξ+j}}` is an ONB, so
  `Σ_j G_W(ξ+j) = |W|` for all `ξ` (and all complex shifts). Relocation/doubling induction (base case =
  Lamzouri, induct on #mixed) closes (H) unless: `|G_{Z∖x}(x)| < ½`, and the negative mass of `G_{Z∖x}`
  and of `G_Z` along every free integer-spaced set is `< ½`. A single far pair makes an oscillating field
  `≈ ±2K(iy)² cos(2π(ξ−x))`; cancelling it to `O(1)` needs multipole/comb structures of length
  `≳ e^{πy}`. Exact combs have constant field (Poisson) and absorb a mixed point at cost 3. So violators
  of (H) need exponentially long near-combs; evidence that (H) is true, not a proof.
- **Open core unchanged:** full (H) for mixed classes outside the lens.

## Cycle H7 — full separation in Lean; trace form of the packet inequality (2026-09-27)
- **Conjecture H7 (proved, Lean).** `≥ (HD(1) − r² − ε)N(T,2T)` zeros are simple, critical and have no
  other zero within `r/log(T/2π)` (`0 < r ≤ 1`). `RHTower/SeparatedSimpleZeros:separated_simple_critical`,
  STATUS MUST-474.
- **New abstract ingredient.** Bounding the mixed Gram–Schmidt range by its trace (`4α − α² ≤ 4α`) instead
  of its dimension (`≤ 2α + 1`) gives `4·mass − E − 2N + 2Σ_H(1−‖f‖²) + Σ_M(2 + 4‖P_A f‖² − 4‖f‖²) ≤ #H +
  2Σ(2 − m₂)` for any multiplicities. A fully absorbed point earns 2 (twice the old cost), so a simple
  point may sit in the absorbing range at price 2. This is what lets near-coincident simple zeros be
  charged like a double zero, i.e. it recovers the real-configuration diagonal extraction inside the
  unconditional Hilbert-space framework.
- **Combinatorics.** Ore: a graph without isolated vertices has a dominating set of at most half the
  vertices (complement of a minimum dominating set dominates) — `exists_dominating_half`.
- **Assets.** `thmD_count_of_seam` (generic endgame), `absorbed_block_count`, `clustered_block_count`,
  `blockOverlap_ge`/`lens_overlap_cost_ge` (quantitative cost `2cos²(ΔL/2)/cosh(εL/2) − 1`).
- **Limit.** The loss `r²` is intrinsic to energy methods: a pair of simple zeros at distance `r/L` has
  energy `≈ 4 − O(r²)`, the same as a double zero. Removing it needs information beyond pair correlation.

## Cycle H8 — Fourier form with class multiplicity functions (2026-10-09, Opus loop row 595)
- **Reformulation (paper, exact).** Group `Z` by horizontal class `g = Re z`. With `c_g(σ) := Σ_{z∈C_g} e^{2π Im(z) σ}`, which is even, `≥ m_g := |C_g|` and a convex cosh-sum, `S(σ) = Σ_g c_g(σ)e^{−2πigσ}` and
  `E = ∫ρ|S|² = Σ_g ∫ρc_g² + Σ_{g≠g'} ∫ρ c_g c_{g'} cos(2π(g−g')σ)`.
  The right side of (H) is `2|Z| − #hs = Σ_g (2m_g − [m_g = 1])`.
  - For real configurations (`c_g ≡ m_g`) every cross term is `m_g m_{g'} K(g−g')² ≥ 0` and `∫ρc_g² = m_g² ≥ 2m_g − [m_g=1]`, so Lamzouri's real-multiplicity bound is plain diagonal domination.
  - Hence **(H) ⟺ the cross terms `∫ρ c_g c_{g'} cos(2π(g−g')σ)` never overspend the diagonal slack `Σ_g(∫ρc_g² − 2m_g + [m_g=1])`.**
  - Slack per class: singleton `0`; pair `2K(2iy)² − 2`; mixed `{g, g±iy}`: `4K(iy)² + 2K(2iy)² − 3`.
- **Two adjacent mixed classes at distance ½ (sinc, large `y`): no violation.** The leading terms of the cross energy cancel the own-pair energy, but only to relative order `1/y²`. The remainder is `≈ (6/π²)·sinh²(2πy)/(64y⁴) > 0`, exponentially large, so (H) holds with huge margin. This is the mechanism behind H6's "near-combs of length `e^{πy}`".
- **Comb-averaged diagonal bound.** For λ = ½ every comb `{f_{ξ+j}}` is an ONB, so `Q ≥ ∫_ℝ (G(x) − ‖Π_W f_x‖²)² dx`, with `∫G = |Z|` and `∫‖Π_W f_x‖² = D`. On the tight pair comb this gives 1 per period against the needed 2, so the averaged diagonal loses a factor 2 and cannot prove (H) alone.
- **Verdict:** (H) unresolved. The open core is exactly the sign of cross-class cosine integrals against cosh-sum multiplicities. Next: an off-diagonal ONB adapted to classes (horizontal Gram–Schmidt per comb) rather than averaged diagonals.

## Cycle H9 — spectral form; the mixed loss is pair–pair interference (2026-10-09, Opus loop row 610)
- **Theorem (Lean, MUST-855).** `HilbertMetric/HorizontalLamzouriSpectral` (wired into `HilbertMetric`; `lake build --old` green; direct `lake env lean` clean; axioms propext/choice/Quot.sound). It holds for any packet in a finite-dimensional space with `m₂ ≥ 2`, `mP ≥ 1`, simple real vectors of norm ≤ 1, and no normalisation, orthogonality or independence of the pair vectors:
  `4·mass − E − 2N + 2 Σ_{x∈M} max(G(f_x), 0) ≤ #H + #M`, with pair field `G(ψ) = Σ_p 2m_p(⟪g_p,ψ⟫² − ⟪h_p,ψ⟫²)`.
  - Corollaries: `G ≥ ½` on `M` gives `4·mass − E − 2N ≤ #H` (`four_mass_sub_energy_le_of_pairField`); in general the loss is `Σ_x (1 − 2G(f_x))⁺`.
  - The normalised forms are `spectral_energy_lower_bound` and `card_hs_ge_of_pairField`.
- **Proof (new, spectral).** Split `Φ = Φ_R + Φ_P`.
  - (i) `Φ_P ≤ Σ 2m g⊗g` has at most `P` positive eigenvalues. Cauchy–Schwarz on them with `(A − 2P)²/P ≥ 0` gives `‖Φ_P‖² − 4trΦ_P + 2N_P ≥ 4T + ‖Φ_P⁻‖²`.
  - (ii) Transport weights `p_{ki} = c_k⟪w_k,f_i⟫²/μ_i` satisfy `Σ_i p_{ki} ≤ 1`, via the test vector `Σ_i(⟪w_k,f_i⟫/μ_i)f_i`. With the tangent lines of `((2−x)⁺)² − 4` this gives `‖Φ_R‖² − 4trΦ_R + 2N_R ≥ ‖(Φ_R−2)⁺‖² − #simple`.
  - (iii) `Φ_R ≤ 2 + (Φ_R − 2)⁺` against `Φ_P⁻` costs at most `4T + ‖Φ_P⁻‖² + ‖(Φ_R−2)⁺‖²`.
  - (i)–(iii) cancel exactly, leaving `2tr(Φ_RΦ_P⁺) ≥ 2Σ_M max(G, 0)`.
- **Reading.** For an isolated mixed class, `⟪h,f⟫ = 0` by parity and `⟪g,f⟫ = K(iδ) ≥ 1`, so `G = 2K(iδ)² ≥ 2` at every displacement. H5's single-pair overlap criterion could not pass `δ ≍ 1/L`; the pair field has no such limit. The remaining open core is two-pair interference: a mixed point loses only if other off-line pairs' odd vectors overlap its vector by `Σ_{q≠p} 2m_q⟪h_q,f⟫² > 2m_p⟪g_p,f⟫² − ½`.
- **Sharpened (same day, Lean).** Keeping the norm slack `2(1 − ‖f‖²)` of every simple atom removes all norm hypotheses. The free condition becomes `G(f_x) ≥ ‖f_x‖² − ½`. An isolated mixed class with `⟪h,f⟫ = 0` and `⟪g,f⟫ ≥ ‖f‖²` satisfies it for every norm (`2t² ≥ t − ½`) and every displacement; on the full grid `⟪g,f⟫ = (L/c)∫φ²cosh(εu) ≥ ‖f‖²` and `⟪h,f⟫ = 0`. The block entry `RHTower.pairField_block_count` (module `HorizontalIsolationBlockPairField`) is wired.
- **Far-pair bonus (Lean).** The Cauchy–Schwarz step discards `(A − 2P)²/P`, where `A` is the sum of the positive pair eigenvalues and `A ≥ trΦ_P`. Keeping it adds `((trΦ_P − 2P)⁺)²/P` to the left side. In the sampled model a pair at displacement `ε` has `‖g‖² − ‖h‖² ≈ (L/c)∫φ²cosh(2εu)`, so far pairs pay into this bonus. It is the slack meant to absorb their interference `Σ_x 2m_q⟪h_q,f_x⟫²`; whether it suffices quantitatively is open.
- **Next.**
  - (a) Zeta transfer: `⟪g,f⟫ ≥ ‖f‖²` and the own odd overlap `⟪h,f⟫` on Zeta23's truncated sampling grid (`blockReVec`, `blockImVec`), analogous to `blockOverlap_near`.
  - (b) Bound the interference by the odd norms `‖h_q‖²`, which are small for near-line pairs, together with the density of far pairs per block.
