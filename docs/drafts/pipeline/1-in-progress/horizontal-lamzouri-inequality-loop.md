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

## Cycle H10 — the positive part is the sharp field; interference is an even–odd residual (2026-10-09, Opus loop row 618)
- **Rejected tool.** `HTGeometry.CauchyDifference.capacity_multiSource` (coherent log-capacity of mean-zero windows) does not apply here, for two reasons:
  - Wrong object. The packet energy `E = ‖Φ‖²` is a zero-side sampled Gram energy with kernel `K = (η²)^`, and no logarithmic difference form enters. At height `T` the archimedean symbol is flat on the window scale.
  - Wrong direction. The count needs upper bounds on `E` and lower bounds on the pair field; the capacity theorem gives lower bounds on an archimedean energy.
- **Theorem (Lean, MUST-862).** `HilbertMetric/HorizontalLamzouriPositivePart`. MUST-855's proof bounds `2tr(Φ_RΦ_P⁺)` from below by `2Σ_M max(G(f_x),0)`; this cycle keeps the positive part itself.
  - `spectral_four_mass_bound_positivePart`: `4·mass − E − 2N + 2Σ_M ⟪Φ_P⁺f_x,f_x⟫ + bonus ≤ Σ_H(2‖f‖²−1) + Σ_M(2‖f‖²−1)`, for any orthonormal diagonalisation `(e, λ)` of the pair form.
  - Free condition (`four_mass_sub_energy_le_of_positivePart`): `⟪Φ_P⁺f_x,f_x⟫ ≥ ‖f_x‖² − ½`. It contains MUST-855, because `max(G,0) ≤ ⟪Φ_P⁺·,·⟫`.
- **What changes.** `⟪Φ_P⁺f,f⟫ = G(f) + ⟪Φ_P⁻f,f⟫`. The interference `Σ_{q≠p}2m_q⟪h_q,f_x⟫²` is not a cost by itself.
  - **Decoupled pairs** (`positivePart_ge_of_decoupled`, exact). If `g_p ⊥ h_p, g_q, h_q` for all `q ≠ p`, then `⟪Φ_P⁺ψ,ψ⟫ ≥ 2m_p⟪g_p,ψ⟫²` for every `ψ`, however large `⟪h_q, ψ⟫` is. So an isolated-type mixed point stays free next to arbitrarily far pairs whose vectors are orthogonal to its own even vector.
  - **Quantitative** (`positivePartForm_ge_of_residual`). With `R_p = Φ_P g_p − λ g_p` and `0 < δ ≤ λ`: `(λ−δ)((|⟪g_p,ψ⟫| − ‖R_p‖‖ψ‖/δ)⁺)² ≤ ‖g_p‖²⟪Φ_P⁺ψ,ψ⟫`. Here `R_p = Σ_{q≠p}2m_q(⟪g_q,g_p⟫g_q − ⟪h_q,g_p⟫h_q)` when `⟪h_p,g_p⟫ = 0` (parity). Interference therefore enters only through the cross-pair overlaps `⟪g_q,g_p⟫‖g_q‖` and `⟪h_q,g_p⟫‖h_q‖` of the *own even vector*, not through the overlaps `⟪h_q,f_x⟫` of the mixed vector.
- **2×2 model (paper).** Take `Φ = αĝĝᵀ − βĥĥᵀ`, `c = ⟪ĝ,ĥ⟫`.
  - `G(ĝ) = α − βc² → −∞` as `β → ∞`, but `⟪Φ⁺ĝ,ĝ⟫ → α(1−c²)²`.
  - Numerically, with `α = 1`, `c² = ½`: `0.604` at `β = 1`, `0.289` at `β = 10`, limit `0.25`.
  - For a general `f` the limit is `α⟪ĝ − cĥ, f⟫²`. The function is not monotone in `β` when `f` is far from `ĝ`: for `f ⊥ ĝ` it is `0.104` at `β = 1`, against the limit `0.25`.
- **Verdict.**
  - (H) still unresolved.
  - The open core is now the even–odd cross-pair residual `‖R_p‖` relative to `λ_p = 2m_p‖g_p‖²`, i.e. `Σ_{q≠p}m_q|⟪h_q,ĝ_p⟫|‖h_q‖ ≪ m_p‖g_p‖` on Zeta23's grid, where `ĝ_p = g_p/‖g_p‖`. Far pairs with exponentially large `‖h_q‖` hurt only if their odd vectors are not correspondingly orthogonal to the own even vector.
  - Next: compute `⟪h_q, g_p⟫` for sampled window vectors via `hasSum_re_mul_re_paperFT_grid` (both are full-grid overlaps of `φ cosh`/`φ sinh` profiles), and decide whether the residual is `o(λ_p)` for zeta-like configurations.

## Cycle H11 — the residual question answered; the odd-angle criterion (2026-10-09, Opus loop row 619)
- **Question (H10).** Is the residual `‖R_p‖ = ‖Φ_P g_p − λg_p‖` small against `λ_p = 2m_p‖g_p‖²` for zeta windows?
- **Answer: NO (paper, rigorous).** Take two pairs `p, q`. Parity gives `⟪g_q, h_q⟫ = 0`, so
  `‖R_p‖² = 4m_q²(⟪g_q,g_p⟫²‖g_q‖² + ⟪h_q,g_p⟫²‖h_q‖²) ≥ 4m_q² c_pq² ‖g_p‖²‖h_q‖⁴`, where `c_pq` is the normalised angle `⟪ĝ_p, ĥ_q⟫`.
  - The residual floor is non-vacuous only if `‖R_p‖ < λ_p|⟪g_p, f⟫| = 2m_p‖g_p‖²J_p`.
  - With `ε_q` growing and the ordinate offset fixed, `‖h_q‖² ~ ∫φ²sinh²(ε_q u)` grows exponentially in `ε_q L`, while `c_pq` tends to a nonzero edge limit. So the floor is vacuous for every sufficiently far pair `q`, however distant its ordinate.
  - The same scaling kills MUST-855's field: `2m_q⟪h_q, f⟫² → ∞`, so `G(f) → −∞`.
  - This is why the H9 open core looked global: a single far pair anywhere in the block ruins every less-displaced mixed point.
- **Replacement (Lean, MUST-863).**
  - `positivePartForm_ge_of_oddInterference`: for `Q(v) = α⟪u,v⟫² − Σ_k b_k⟪h_k,v⟫²` with `b_k ≥ 0` of any size, `⟪Q⁺f,f⟫ ≥ α((|⟪u,f⟫| − κ‖f‖)⁺)²`, where `κ` bounds the angle of `u` to `span{h_k}`. The proof writes the positive eigenvector as `z = λ(λ + B)⁻¹u`, with `u − z ∈ span h`, `⟪u, z⟫ ≥ ‖z‖²` and `λ = α⟪u,z⟫`.
  - `four_mass_bound_singleOwner`: move all other pairs' even vectors into the real part as heavy atoms (weight `2m ≥ 2`, free in the four-trace bound).
  - `four_mass_sub_energy_le_of_oddAngle`: average the regrouped bound over the `r` owner pairs. Conclusion: `4·mass − E − 2N ≤ #H` whenever every mixed `x` satisfies `2m_p((|⟪g_p,f_x⟫| − κ_x‖f_x‖)⁺)² ≥ r(‖f_x‖² − ½)`.
  - The criterion does not involve the sizes of the odd vectors, nor the other pairs' even vectors. Even–even interference is removed by averaging, since `J_p² ≫ r`.
- **Meaning for zeta windows (paper).**
  - The criterion reads `‖P_H ĝ_p‖ ≲ √t_p ≈ J_p/‖g_p‖`. Here `H` is the span of the off-line odd vectors only: on-line zeros contribute no `h`.
  - Integrating by parts against `sin(Δu)` with a window vanishing at the edges gives `c_pq ≲ C_φ(ε_p + ε_q)L/(|Δ|L)` (higher powers for smoother `φ`). Interference is therefore *local in ordinate*: only off-line pairs within ordinate distance `≍ (ε_p + ε_q)L·t_p^{−1/2k}` of `p` (in units `1/L`) can violate the criterion.
- **Status of (H).**
  - Not proved. The open core is now the count of far off-line pairs with an off-line neighbour inside that radius, a second-order clustering event among off-line zeros.
  - Next: a rigorous truncated-grid bound for `c_pq` via `RHTower/HorizontalIsolationCrossPairOverlap` (hgt-63), then the block count `#(mixed classes failing the odd-angle criterion)`.

## Cycle H12 — the cross-pair decay on the truncated grid; the failure count (2026-10-09, Opus loop row 623)
- **Item 1: the integration-by-parts bound on `c_pq` (Lean, `RHTower/HorizontalIsolationCrossPairDecay.lean`).**
  - `abs_integral_mul_sin_le`: `|∫_a^b F sin(Δx)| ≤ ∫|F′|/|Δ|` when `F(a) = F(b) = 0`.
  - `abs_integral_cross_window_le`: for `φ ∈ C¹` vanishing at `±L/2`,
    `|Δ|·|∫φ²cosh(ε_p u)sinh(ε_q u)sin(Δu)| ≤ 2‖φ′c_p‖‖φs_q‖ + |ε_p|‖φs_p‖‖φs_q‖ + |ε_q|‖φc_p‖‖φc_q‖`,
    where `c_a = cosh(au)` and `s_a = sinh(au)`.
  - `abs_inner_blockImVec_blockReVec_sub_le`: on Zeta23's truncated grid,
    `|⟪h_q, g_p⟫ − (L/c)∫φ²cosh(ε_p u)sinh(ε_q u)sin(Δu)| ≤ √(ℓ_g ℓ_h)/c`.
    Here `ℓ_g`, `ℓ_h` are the leakages (full Poisson mass minus the `d` block samples), `ε = Re − ½` and `Δ = γ_q − γ_p`.
  - Supporting lemmas: the leakage Cauchy–Schwarz `abs_sub_sum_le_of_hasSum_le`, and `paperFT_shifted_window` (`paperFT(φe^{εu}e^{iΔu})(w) = φ̂(w + Δ − iε)`).
  - hgt-63's `RHTower/HyperbolicWindowOscillationBound.lean` proves the moment form of the same estimate.
- **Normalised angle (paper, from the Lean bounds).**
  - Use `‖φc_q‖² = ‖φ‖² + ‖φs_q‖²` and `‖φs_q‖ ≥ |ε_q|‖uφ‖`.
  - Up to the block/full-grid norm ratio and the leakage term,
    `|c_pq| ≤ (2R_φ(ε_p) + |ε_p| + |ε_q| + C_φ)/|Δ|`,
    with `R_φ(a) = ‖φ′c_a‖/‖φc_a‖` and `C_φ = ‖φ‖/‖uφ‖ ≍ 1/L`.
  - For Zeta23's `φ(u) = ϱ((L/2 − |u|)/w)`: if `ϱ ~ x^k` at `0`, Laplace gives `R_φ(a) → a√(2k/(2k−1))` for `aw ≫ 1`. Since `ϱ ∈ C³` vanishes on `x ≤ 0`, we have `k ≥ 3`, so `2R_φ ≤ 2.2|ε_p|`.
  - At `a = 0`, `R_φ(0) ≍ (wL)^{−1/2}`.
  - Hence `|c_pq| ≲ (3.2|ε_p| + |ε_q| + O((wL)^{−1/2} + 1/L))/|γ_q − γ_p|`.
  - **Correction to H11:** the gain is additive in `ε_p, ε_q`, not the product `C_φ(ε_p + ε_q)`. The higher-power refinement `t_p^{−1/2k}` is unproved.
- **Item 2: the failure count (Lean, MUST-865).**
  - **Resolvent split** (`norm_le_of_resolvent`): if `λ > 0`, `B ≥ 0` is weighted and `λd + Bd = Bu`, then for *every* `p`,
    `‖d‖ ≤ ‖p‖ + √(⟪B(u−p), u−p⟫/(4λ))`.
    - Proof: split `d = d₁ + d₂` with `(λ + B)d₁ = Bp` and `(λ + B)d₂ = B(u − p)`.
    - `‖d₁‖ ≤ ‖p‖` because `λ‖d₁‖² ≤ λ⟪d₁, p⟫`.
    - `λ‖d₂‖² = ⟪Bx, v⟫ − ⟪Bx, x⟫ ≤ ⟪Bv, v⟫/4` by Cauchy–Schwarz for `B`.
  - **Eigenvector floor** (`exists_resolvent_floor`): for a single positive eigenvalue `λ`, the defect `d = u − z` satisfies `λd + Bd = Bu`, and `α((|⟪u,f⟫| − ‖d‖‖f‖)⁺)² ≤ ⟪Q⁺f, f⟫`.
  - **Hybrid floor** (`positivePartForm_ge_of_hybridInterference`). Take `p = P_K u`, the projection on the large span, so that `‖p‖ ≤ κ`. The small family enters only through `⟪Bv₀, v₀⟫ ≤ σ²`. Then
    `⟪Q⁺f,f⟫ ≥ α((|⟪u,f⟫| − (κ + √(σ²/(4λ₀)))‖f‖)⁺)²`, with `λ₀ = α(‖u‖² − κ²) − σ²/(‖u‖² − κ²)`.
    - Large odd vectors cost only through their angle.
    - Small ones cost through their weighted overlaps, uniformly in how many there are.
  - **Weighted failure-tolerant count** (`four_mass_sub_energy_le_add_card_fail_weighted`). For owner weights `w ≥ 0` with `Σ_O w = 1`:
    `4·mass − E − 2N ≤ #H + #{x : ‖f_x‖² − ½ > w_{own x}⟪Φ_{own x}⁺f_x, f_x⟫}`.
    - **Budget form:** costs `β` with `Σβ ≤ 1` suffice. All mixed points are certified once `Σ_q max_{own x=q}(‖f_x‖² − ½)⁺/⟪Φ_q⁺f_x,f_x⟫ ≤ 1`.
    - This replaces H11's uniform factor `r`. Owners with exponentially large positive part, i.e. far pairs, cost almost nothing.
  - **Hybrid count** (`four_mass_sub_energy_le_add_hybrid_count`; block form `RHTower.oddAngle_block_hybrid_count`):
    `4 tr − ‖·‖² − 2N ≤ #(S₁ \ M) + Σ_{x∈M}(K_x/θ_x)²`, with `K_x = κ_x + √(σ²_x/(4λ₀,x))`.
    - `θ_x` is the slack of `‖f_x‖² − ½ ≤ w·2m_p((|⟪g_p,f_x⟫| − θ_x‖f_x‖)⁺)²`.
    - The count uses Chebyshev, `card_filter_lt_le_sum_sq_div`.
  - **Angle from pairwise angles** (`HilbertMetric/SpanAngleFromGramFrame.lean`). If the off-diagonal row sums of the normalised Gram matrix of `{h_q : q ∈ L}` are at most `η < 1`, then
    `κ = ‖g_p‖·√(Σ_{q∈L} c_pq²/(1 − η))` (`abs_inner_le_of_rowSum`).
- **Answer to "how many mixed classes fail" (paper synthesis).**
  - Take `L` = the off-line pairs with `Σ_{q'≠q}|⟪ĥ_q, ĥ_{q'}⟫| ≤ η` and `σ² = 0` for the rest. Write `cos_x = |⟪ĝ_p, f̂_x⟫|` and `τ_x = √((‖f_x‖² − ½)⁺/(2m_p w_p))/‖g_p‖`. Then
    `#Fail ≤ Σ_{x∈M} (Σ_{q∈L} c_{p(x)q}²/(1−η)) / (cos_x − τ_x)²`, and therefore
    `#Fail ≲ Σ_{x∈M} Σ_{q≠p(x)} (3.2ε_p + ε_q + o(1))² / ((1−η)(γ_q − γ_p)²(cos_x − τ_x)²)`.
  - The failure count is an inverse-square **pair-correlation energy of the off-line zeros, seen from the owners of mixed points**. Off-line pairs at ordinate distance `≫ (ε_p + ε_q)/(cos_x − τ_x)` from every owner cost nothing.
  - Clusters of off-line pairs with `η ≥ 1` must go into the small family (`σ²`) or use a direct frame bound `μ`.
- **Status of (H).**
  - The robustness of Zeta23's counting against off-line zeros is now reduced to two quantities:
    1. the off-line pair-correlation energy `Σ (ε_p + ε_q)²/(γ_q − γ_p)²` at owners;
    2. the owner correlations `cos_x`.
  - Neither is bounded by known zero statistics. Zero-density estimates bound the number of pairs with `ε ≥ δ`, not their ordinate clustering.
  - Caveat: for `ε_p L ≫ 1`, `g_p` concentrates at the window edges and `cos_x ≍ √(w/L)`, so `w ≍ L` is needed for `cos_x ≍ 1`.
  - Next: decide whether `cos_x − τ_x` stays bounded below for mixed points (it fails for `‖g_p‖² < 1/(4m_p w_p)`, i.e. barely off-line owners). The barely-off-line regime `ε_p L ≲ 1` is where `h_p` is tiny and the pair behaves like a double on-line zero. That regime should be routed to the `S₂` count instead of the mixed count.

## Cycle H13 — routing barely off-line pairs to the multiple points (2026-10-09, Opus loop row 625)
- **Question (H12).** Owners with `ε_p L ≲ 1` have `cos_x − τ_x` collapsing, so they cannot certify their mixed points. Can they be counted as multiple on-line points instead?
- **Exact routing identity (Lean, MUST-866, `HilbertMetric/HorizontalLamzouriRouteToMultiple.lean`).**
  - `routeToMultiple S` turns each pair `q ∈ S` into a multiple real point `(2m_q, g_q)` and drops `h_q`. The count `N` is unchanged (`route_count`).
  - With `D′` the diagonal form of the routed kernel `K′` (`four_mass_sub_energy_route_eq`):
    `4·mass − E − 2N = 4·mass′ − E′ − 2N′ − Σ_{q∈S} 2m_q(4‖h_q‖² − 2D′(h_q)) − Σ_{q,q′∈S} 4m_q m_{q′}⟪h_q,h_{q′}⟫²`.
    This is the expansion of `F(X) = 4 tr X − ‖X‖²` at `X = K′ − H` with `H = Σ_S 2m_q h_q⊗h_q`: `F(K′ − H) = F(K′) − 4 tr H + 2⟨K′, H⟩ − ‖H‖²`.
- **Routing bound** (`four_mass_sub_energy_le_route`). Routing costs at most `Σ_{q∈S} 4m_q‖h_q‖²(⟪K′ĥ_q, ĥ_q⟫ − 2)`.
  - Since `F = Σλ(4 − λ)` peaks at `λ = 2`, removing a negative atom helps exactly when the routed kernel's Rayleigh quotient in direction `ĥ_q` is below `2`.
- **Routed failure count** (`four_mass_sub_energy_le_route_add_card_fail`; block form `RHTower.oddAngle_block_route_count`):
  `4 tr − ‖·‖² − 2N ≤ #(S₁ \ M) + #{uncertified in the routed packet} + Σ_{q∈S} 4m_q(D′(h_q) − 2‖h_q‖²)`.
  - Routed pairs leave the owner set, so they no longer need certificates.
- **Size of the routing cost (paper; Lean brick B1 delegated to hgt-61).**
  - Use `|sinh x| ≤ |x|cosh x` and that the block norm is at most the full-grid norm:
    `‖h_q‖² ≤ (L/c)ε_q²∫u²φ²cosh²(ε_q u) ≤ ¼(ε_q L)²cosh²(ε_q L/2)·(L∫φ²/c)`.
  - Hence a pair with `ε_q L ≤ δ` costs at most `m_q δ² cosh²(δ/2)(L∫φ²/c)(R_q − 2)⁺`, where `R_q = ⟪K′ĥ_q, ĥ_q⟫`.
  - By parity on the full grid (`⟪g_q, h_q⟫` has `sin(0·u) = 0`), the own atom `g_q` enters `R_q` only through leakage. `R_q` sees the other zeros near `γ_q` in the derivative direction, since `ĥ_q ≈ ∂_γ f̂_γ`.
- **Status of (H).** The barely-off-line regime is closed up to `O(δ²)` per pair times the local Rayleigh excess. The remaining open core is unchanged: the pair-correlation energy of genuinely off-line pairs (`ε L ≫ 1`) at owners, against owner correlations `cos_x ≍ √(w/L)`.
- **Update (Lean).** The paper bound on `‖h_q‖²` is now proved: hgt-61's `RHTower/HorizontalIsolationOddVectorNorm` gives `hasSum_im_sq_grid`, `norm_sq_blockImVec_le`, `norm_sq_blockImVec_le_sq_mul` and `norm_sq_blockImVec_le_sq_mul_cosh`.
  - Combined count: `RHTower.routed_block_count_le_of_rayleigh` (`RHTower/HorizontalIsolationRoutedPairCost.lean`):
    `4 tr − ‖·‖² − 2N ≤ #(S₁ \ M) + #uncertified + Σ_{q∈S} 4m_q(R_q − 2)⁺ L ε_q² cosh²(ε_qL/2)∫u²φ²/c`, under `D′(h_q) ≤ R_q‖h_q‖²`.
  - Standard axioms.

## Cycle H14 — owner averaging is vacuous for many owners; the averaging-free merge (2026-10-09, Opus loop row 632)
- **Correction to H11–H13 (rigorous).** The averaged criteria (MUST-863, MUST-865 weighted/budget) certify `x` only if `‖f_x‖² − ½ ≤ β_{own x}⟪Φ_{own}⁺f_x,f_x⟫` with `Σβ ≤ 1`.
  - Zeta23's block vectors have `‖f_x‖² ≈ 1`, so the certified owners with positive part `≤ P̄` number at most `2P̄`.
  - Near owners have `⟪Φ⁺f,f⟫ = O(1)`, so only `O(1)` of them can ever be certified.
  - The criteria are therefore useful only for few owners or far owners (positive part `~e^{εL}`). With many mixed classes, almost all are charged `1`, which is worse than the corpus seam (`εL/24` each, MUST-634/636).
  - Routing (MUST-866) does not repair this: a routed pair's real point stays a mixed point with no owner.
- **Averaging-free merge (Lean, MUST-869, `HilbertMetric/HorizontalLamzouriMergeMixed.lean`).**
  - **Transfer identity** (`four_mass_sub_energy_transfer_eq`): if `P′` arises from `P` by adding signed atoms `(c_j, a_j)`, then
    `4·mass − E = 4·mass′ − E′ − 4Σc‖a‖² + 2ΣcD′(a) − ‖Σc a⊗a‖²`, and the last term is `≤ 0` (`sum_sum_mul_inner_sq_nonneg`). Routing is the special case `c = 2m`, `a = h`.
  - **Merge** (`mergeMixed`, `merge_count`, `four_mass_sub_energy_le_merge_add_card`): each class `q ∈ S` (the pair `q` and its real point `f_q`, with `mate` injective) becomes one real point of multiplicity `2m_q + 1` with vector `f_q`. The count is unchanged, and
    `4·mass − E − 2N ≤ #H + #{unmerged mixed} + Σ_{q∈S} 4m_q(2(‖g_q‖² − ‖h_q‖² − ‖f_q‖²) + D′(f_q) + D′(h_q) − D′(g_q))`.
  - No owners and no averaging are involved; each class pays only its own cost `c_q`.
- **The merge cost on Zeta23 windows (paper, full grid).** Write `Φ̂(z) = ∫φ²e^{zu}du` and `ρ_φ = φ²*φ² ≥ 0`.
  - The parity facts `‖g‖² − ‖h‖² = ‖f‖²` and `⟪f, h⟫ = 0` remove the trace term.
  - For on-line atoms `a` at ordinate offset `Δ_a`:
    `c_q = −4m_q(L/c)²[(2m_q + 1)Ψ_ε(0) + Σ_{a≠q} w_a Ψ_ε(Δ_a)]`,
    `Ψ_ε(Δ) = Re Φ̂(ε+iΔ)² − Φ̂(iΔ)² = ∫ρ_φ(s)(cosh(εs) − 1)cos(Δs)ds`.
  - **Structure of Ψ_ε:**
    - It is positive definite: its Fourier transform `ρ_φ(s)(cosh εs − 1)` is `≥ 0`.
    - `Ψ_ε(0) > 0`: an isolated class *gains* `4m(2m+1)(L/c)²Ψ_ε(0)`, where the seam charges `+εL/24`.
    - It has mean zero, `∫Ψ_ε = 2πρ_φ(0)·0 = 0`.
    - For an equally spaced environment with spacing `2π/log T`, Poisson summation gives `Σ_a Ψ_ε(Δ_a) = 0` exactly when `λ < 1`, since the support of `ρ_φ` is `|s| < L < log T`. The class then gains `2m(L/c)²Ψ_ε(0)·4m`.
    - At second order in `εL`, `Ψ_ε ∝ ε²∫s²ρ_φ cos(Δs)`. This is H1's coefficient `M₁`; its negative lobe sits at `|Δ| ≈ 3π/(2L)`, i.e. at the nearest neighbours.
  - **Merge criterion:** `2m_qΨ_ε(0) + F_q ≥ 0`, where `F_q = Σ_{all atoms a} w_aΨ_ε(γ_a − γ_q)` is the fluctuation of a mean-zero positive-definite row sum around the class.
- **Verdict.**
  - Exact, averaging-free accounting now exists. The failure of a mixed class is equivalent to a local zero-configuration fluctuation `F_q < −2m_qΨ_ε(0)`.
  - That is a statement about individual locations (wall "individual zeros"). A mean-value (large-sieve) bound for `Σ_q F_q²` gives only a constant fraction of failures, `≈ 0.05N/m²` before constants, which is worse than the corpus loss `πμ/12 ≈ 0.0175`.
  - **(H) remains open**, and the open core is now the sign of `F_q`.

## Cycle H15 — the merge criterion through the explicit formula; the quadratic mixed gain; lane verdict (2026-10-09, Opus loop row 635)
- **Merge criterion via the explicit formula (paper, full grid).**
  - The zero-side form satisfies `D(v) = Σ_ρ Re G_v(γ_ρ)` over *all* zeros, with complex `γ_ρ` for off-line ones. Hence
    `D(f_q) + D(h_q) − D(g_q) = −(L/c)² Σ_ρ Ψ_ε(γ_ρ − γ_q)`, where `Ψ_ε(Δ) = ½(Φ̂(ε+iΔ)² + Φ̂(ε−iΔ)²) − Φ̂(iΔ)²` is entire with transform `ρ_φ(s)(cosh εs − 1)`.
  - The merge cost is then exactly `c_q = 4m_q(L/c)²[−P_ε(γ_q) + 2m_qQ_ε]`, where:
    - `P_ε(t) = Σ_ρ Ψ_ε(γ_ρ − t) = −(1/π)Σ_n Λ(n)n^{−½}ρ_φ(log n)(cosh(ε log n) − 1)cos(t log n) + o(1)`; the main term vanishes because `∫Ψ_ε = 0`;
    - `Q_ε = (3Φ̂(0)² + Φ̂(2ε)²)/2 − 2Φ̂(ε)²`, which is `= ε⁴(3M₂²/2 + I₀M₄/2) + O(ε⁶) > 0` for small `ε`.
  - **The class merges for free iff the prime sum at its ordinate exceeds `2m_qQ_ε`.** The `O(ε²)` self gain of H14 cancels against the pair's own zeros at `±iε`, leaving an `O(ε⁴)` cost and an `O(ε²)` prime fluctuation.
  - The prime sum at `γ_q` is a smoothed `−ζ′/ζ` at `½ ± ε + iγ_q`, i.e. at the zeros themselves. The explicit formula only restates the configuration, so this is the individual-zeros wall in its exact form.
- **Quadratic mixed gain (Lean, MUST-870, `HilbertMetric/HorizontalLamzouriMixedRangeSharp.lean`, `RHTower/HorizontalSimplicitySharpDeficitCount.lean`).**
  - The unnormalised four-trace bound (`four_mass_sub_energy_le`) bounds the mixed range by the tangent line `4α − α² ≤ 2α + 1`.
  - Keeping the exact square (`four_mass_sub_energy_le_add_mixedRange`) and applying Cauchy–Schwarz (`d ≤ #M`, range mass `≤ S`, via `mixed_range_sum_le_unabsorbed`) gives `four_mass_sub_energy_le_sharp`: `… + (#M − S)²/#M ≤ #H`, with `S = Σ_M(‖f‖² − ‖P_A f‖²)`. This is H2's `1 − 2t − t²` in averaged form, now without normalisation; the corpus had it only for admissible packets (`sq_le_card_mul_of_sum_le`).
  - Linearised by AM–GM (`four_mass_sub_energy_le_add_sharp_deficit`, block form `absorbed_block_count_add_sharp_deficit`): for every `b ≥ 0`,
    `4 tr − ‖·‖² − 2N ≤ #(S₁ \ M) + Σ_x((1+b)d_x − b + b²)`.
    A mixed point with `d_x ≤ (b−b²)/(1+b)` (at most `3 − 2√2` at `b = √2 − 1`) is then free.
  - Effect on the corpus density (paper, flat-window estimate):
    - the per-moment slope drops from `sup ψ/x ≈ 0.031` to `sup_x min_b[(1+b)ψ − b + b²]/x ≈ 0.028`, about 10% of the loss `πμ/12`;
    - so `HD(1) − 0.0175 ≈ 0.6550` would rise to `≈ 0.6567`.
    - Propagation needs a `b`-version of `hatAz_horizontal_deficit` and the seam chain. **Not done**: the gain is too small to justify duplicating the chain.
- **Lane verdict.**
  - **(H) for ζ (zero mixed loss) is at the individual-zeros wall.** Every exact form found (residual, odd angle, routing, merge) reduces to the sign of a mean-zero local zero sum at off-line ordinates. That sum equals a prime sum evaluated at the off-line zeros themselves.
  - Averaged tools give at most constant-factor improvements of the corpus loss `πμ/12`.
  - **Status: lane saturated for RH purposes.** Positive survivors in Lean: MUST-865 cross-pair decay and failure count (few-owner regime), MUST-866 routing, MUST-869 merge identity, MUST-870 quadratic mixed gain.
