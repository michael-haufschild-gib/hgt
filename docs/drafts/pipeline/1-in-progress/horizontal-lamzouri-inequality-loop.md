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
