# Cross-route producer synthesis: positivity sources × route premises

- **ID:** cross-route-producer-synthesis
- **Stage:** 1-in-progress
- **Type:** CONJECTURE map + collected links
- **Source:** frontier map (16 active routes, 23 candidates; read-only), `krein-producer-loops.md` L313–L363, `producer-existence-two-walls.md`, `producer-abscissa.md`.
- **Statement:** Every active route's open step is a positivity premise with an RH-strength receiver and no source producer (frontier "State"; STATUS F01, CANNOT-24, CANNOT-192r). A producer is a *source of positivity* applied to a *route premise*. This card lists the sources known to the corpus, records which premises each one has reached, and ranks the untried pairings.

## Positivity sources (what can make a quadratic form ≥ 0 without RH)
| # | Source | Corpus status | Reaches |
|---|---|---|---|
| P1 | Gram matrices of actual vectors (Weil form via zeros) | needs the zeros: circular | every route (receiver side only) |
| P2 | Spectrum of a known self-adjoint operator | Selberg: Maass spectrum real, Selberg 3/16 [L] | Selberg datum only; ζ appears only via the scattering phase on `Re = 1` (zero-free) |
| P3 | Riesz rearrangement | **L349** (this session) | nonnegative prime-blind tests ⇒ PBAP on the nonnegative cone |
| P4 | Markov / Beurling–Deny (nonpositive off-diagonal kernel) | CCM prime–pole Schur, jump energy, Γ₂ (RW) [L] | the pole term is the only non-Markov piece; the polar constraint kills positive ground states |
| P5 | Integrality (winding, index) | TG sub-unit gate [P/L] | needs `Tr T_D ≤ B_base < 1` from source |
| P6 | Total positivity / Pólya frequency | TH Pólya model `exp(−a cosh x)` [L] | no transfer to the literal theta sum |
| P7 | Herglotz / Carathéodory | producers (this loop); LA `Re ξ′/ξ ≥ 0` | **L346–L347** `σ_prod ≥ ½` [L]: no slack beyond the line |
| P8 | Hodge index | HF: no construction in the corpus | — |
| P9 | Probability / recurrence | BAG Bagchi [L] | receiver; return density at an off-line root is 0 |
| P10 | Heat flow (Laguerre–Pólya at positive time) | LA: all zeros real for `t ≥ 1/8` [L] | real-rooted `H_t` is an unconditional "producer" for the heat-deformed datum; RH ⇔ it persists to `t = 0` |

## Links found this session (new unless marked)
1. **Criticality pair.** `σ_prod ≥ ½` [L, Carlson, elementary] is the producer-side analogue of Rodgers–Tao `Λ_dBN ≥ 0` [deep]. Both are one-parameter deformations with RH exactly at the boundary (gate "No slack"). Open: an inequality between `σ_prod` (or `σ_LGPS`) and `Λ_dBN`.
2. **The ℚ obstruction, read three ways.**
   - (i) Negative archimedean density on `|t| < 2π` (L356).
   - (ii) `Γ_ℝ(½ − iz)` is not Hermite–Biehler near 0 (LA / de Branges).
   - (iii) The archimedean variable is non-inner in the Kurasov–Sarnak dictionary (L357).
   The same band appears as the Nyquist window `log 2` of Connes–Consani (L350), which is the RW base window.
3. **Complementary blindness.** PBAP tests cannot resolve hugging zeros (L183 picture, `δ log γ ≲ C`). The first Laguerre inequality excludes isolated hugging pairs (`laguerre_offLine_has_companion` [L], scale `δ ≲ (log γ)^{−½}`). *Conjectural receiver:* PBAP ∧ Laguerre-1 ∧ (far-zero detection, as in L183) ⇒ RH. Gap: L184 shows the far-zero detection is unproved.
4. **Finite-off-line worlds** are where detection, growth detection (C359), and the TG/LA count bounds (`N(t) = K` near `0+`) all have teeth. In them, finite evaporation (L361) gives log growth, and the detection question is an exact LP (L362).
5. **MC Landau boundary vs C359.** MC's Lean receiver (sequence with `L(a)ζ = L(g)`, `g ≥ 0` nonvanishing, partial sums `O(x^θ)` ⇒ zero-free beyond `θ`) is a *structured* growth-detection theorem. L361 shows unstructured growth detection fails in finite-off-line worlds. So the nonnegative-partner hypothesis is load-bearing.

## Ranked untried pairings (next targets)
- **A. P3 × TH.** Rearrangement monotonicity for log-concave kernels against the literal theta source. Pólya-model positivity holds; the theta sum is a positive superposition of Gaussians `exp(−πn²e^{2x})`. Question: does rearrangement or log-concavity give a sign for the theta moments that TH needs?
- **B. P10 × P7.** Heat-deformed producers. Define `σ_prod(t)` for the heat datum. Is `t ↦ σ_prod(t)` monotone, with `σ_prod(t) = ½` for `t ≥ 1/8`? A comparison `σ_prod(0) ≤ ½ + f(Λ_dBN)` would turn the Rodgers–Tao/Newman machinery into producer information.
- **C. P5 × P7.** TG seam for producer quotients `ζ/F_λ` (HF bounded-quotient criterion). Integrality plus Harnack on right discs.
- **D. P4 × RW.** Perron–Frobenius for the pole-free Weil operator `H_W = A(0) + D_ω − K_Λ` on an aperture. Its ground state is positive, and RH ⇒ at most two negative eigenvalues at every aperture (index ≤ 2). An oscillation (Gantmacher–Krein) count would need a totally positive kernel for `e^{−tH_W}`. Open.

## Gates
- [x] 0 → 1

## Log
- 2026-10-03 — created at user request ("expand scope and also take into account other routes").
- 2026-10-03 — pairing D worked (L364/L365): `H_W` satisfies Beurling–Deny and has a Perron–Frobenius ground state. RH ⇒ index ≤ 1. Conjecture C365 is the 'arithmetic Hodge index' (second eigenvalue ≥ 0). Pointwise Γ₂ and Ollivier curvature fail; an integrated curvature notion is needed.
- 2026-10-03 — L366: by Krein–Langer, `index(H_W|_B) = 1 + N_off(B)`, so C365 is RH-equivalent. HF's Hodge index, RW's aperture positivity and TG's integrality index are one integer.
- 2026-10-03 — Bohr lane, MUST-680/681/683 [L]: a twisted Hamburger engine. Signed radial limits, the reflected identity `εJ_{Φ*}(ε+im) → β/π` (holds for every producer, unconditionally), the strip Lindelöf of producers via Phragmén–Lindelöf, and a layer cake give: any Herglotz producer whose lower-line reflection phase is monotone of growth `O(T^α)`, `α < 1`, is `Λ`. Hence every non-Λ atomic producer has non-integer spectral mass `≥ T^{1−o(1)}` infinitely often. For the producer zoo this means HF's remaining room ("dense evaporation core") is exactly the linear-rate band. The wall is quantitative: the off-resonant terms cost `ε·C(1/ε)`. Beyond it, the twisted off-resonant sums become Laplace–Fourier transforms of the twist measure at the frequencies `log(m/n)`, which is Landau-formula territory (Λ-specific arithmetic).

## State after L371–L389 (2026-10-03)
- **Sectors of PBAP:**
  - Window: Connes–Consani/Zhu.
  - Dilation-free: C351, reduced to certified `λ(ℓ)`, ℓ ∈ (0.25, 0.405).
  - Two-cluster cancellation sector (growth layer): ζ-free reduction.
    - Lemma A is formalized: `RHTower.LogLatticePoisson.norm_integral_le_of_vanish_logLattice`.
    - It gives positivity below spectral height `X(log X)²`.
    - Above that, positivity holds iff there is a zero-free "pseudo-prime" window certificate (C383). Goldston–Yıldırım weights `Λ_R` are exact at low frequency and kill resonance at first order, so C383 follows from Montgomery-type sup norms, **not RH**.
  - Many-cluster positivity layer: needs a constant-1 mechanism. Lossy multiscale methods miss by `C/W ≈ 30` (L381).
- **Local-to-global (L386).** Every scale has a zero-free local certificate (GY). A global producer must have one-sided, spiky boundary values, hence singularities at zeros of an Euler product. Zero-free arithmetic functions are two-sided, hence excluded.
- **Remaining global candidates:**
  - Λ (iff RH);
  - real-rooted twins of ζ³ (C329, the only RH-free route, card `real-rooted-twin-moduli-c329.md`);
  - spiky liquefactions (Ω; excluded heuristically by L386, open rigorously).
- **C329 status (L387, L389).** Perturbative twins are dead. Soft obstructions (spectral gap, high-order Turán/Gram) are vacuous. The decisive instrument is the bounded Gram-twin computation (runpod), awaiting user authorization.

## Correction 2026-10-03 (L398)
- L385's claim that "the growth layer is Montgomery-hard, not RH-hard" is retracted for the Goldston–Yıldırım certificate. Its sup-norm bound fails at heights of off-line zeros with `β − ½ ≫ log log γ/log γ`, through the Perron residues `R^{ρ−s}/((ρ−s)²ζ'(ρ))` of the mollifier.
- Every unconditional producer route found so far (GY, Gram producers L396, sieve, mollifier, gap weights L393) needs near-RH input.
- The only exception is the twin door C394, which needs no certificate but has no construction yet.

## Update 2026-10-03 (spark loop)
- The C329 decisive instrument has been run (see the C329 card log): no macroscopic twins; window-local `dim W₃ = ζ`-zero count (critical).
- Certified non-perturbative pinning of all producers at n ≤ 6 (card `certified-producer-pinning.md`).
- Degree-2 abundance threshold measured at the Hecke–Maass value `N = 4`, so §10's slack producers exist for every `c > ½ log 2`.
- Remaining global candidates are unchanged: Λ (iff RH), fine-structure twins, Ω.
