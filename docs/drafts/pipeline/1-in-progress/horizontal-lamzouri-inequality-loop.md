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
