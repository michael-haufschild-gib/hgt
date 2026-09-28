# Route E folder → stage 3: Lean programme ledger

Goal: formalize, unconditionally, every displayed theorem of every card in this folder; move each
card to `3-formalized/route e/` (with a `-formalized.md` companion) when all its results have
closed Lean theorems (`lake env lean` clean, `#print axioms` = propext/Classical.choice/Quot.sound,
wired into `RHTower.lean`).  Delete this file when the folder is empty.

## Cards and their open analytic cores (audit 2026-09-27)

| Card | Statement | Everything else | Open core |
|-|-|-|-|
| route-e-cofactor-amplified-e3-token-supply | (1)–(3): opposite-parity cofactor targets, `#Q_η(u) ≫ U^{1/2+η}/(log U)^{0.45}`, union `≫ U/log U` | parity balance `(7)`,`(9)`, pairing, displacement `(5)` in Lean | row supply `(6)` = quantitative Matomäki–Teräväinen Thm 1.2 at `a ∈ [1.1−10⁻⁴, 1.1]` |
| route-e-forbidden-support-e3-stability | (FS2)–(FS3): MT's `E₃` count survives deleting the prime divisors of any `A ≤ x^B` | `(FS5)`,`(FS6)`,`(FS10)`–`(FS14)`, `(FS7)` in Lean | `(FS4)` = MT Thm 1.2 (its proof, perturbed) |
| route-e-growing-reciprocal-marker-low-breadth-transport | (4): `#T_σ(X,H) ≥ cH log h/log X`; (7); low-breadth transport | marker schedule, fibres `(25)`–`(26)`, squarefree `(19)`–`(23)`, bookkeeping in Lean | `(15)` = Menon 2026 Thm 1.1 rate `(loglog L/log L)² + (loglog A)⁴/(log A)²` at `log L ≫ √(log X)(loglog X)²`; Shiu's bound `(32)` for `z^{ω(n)}`, `H ≥ √X` |

Programme cards holding the deep inputs:
- `1-in-progress/matomaki-teravainen-e3-lean-programme.md` (bricks 1–155): Prop 2.2, Lemma 3.1–3.4,
  4.1, 4.2 (Huxley strength) in Lean; open: Type-I Lemma 3.5 (Watt / Deshouillers–Iwaniec) on the
  residual small-`A` product-long range — needs Kuznetsov-strength cancellation; exponent at Huxley
  strength is `1 + 44/79 ≈ 1.557`, the cards' `1.55` needs Jutila's `σ = 49/206`.
- `1-in-progress/matomaki-radziwill-lean-programme.md`: MR for `μ` at every `h = exp((log x)^β)`;
  the gate `averagedMeanSquare_moebius_of_headSmall` reduces every window law to
  `∫_{|w| ≤ (M/h)ω} ‖∑_{n≤M} μ(n) n^{-2πiw}‖² = o(M²)`.  Milestone D (every `h → ∞`) closed 2026-09-28.

## Plan (order of attack)

1. ~~MR milestone D for `μ` (card: coprime square-root)~~ — **done 2026-09-28**, card moved to
   `3-formalized/route e/` (`Sieve/RouteECoprimeSignAllWindows`).
2. Menon rate + Shiu (growing marker card).
3. MT Type-I (both `E₃` cards): Deshouillers–Iwaniec twisted fourth moment (Kuznetsov) or a
   source-specific replacement of equal strength.

## Log
- 2026-09-27 — ledger created; route l finished (all six cards in `3-formalized/route l`).
- 2026-09-28 — MR milestone D closed (`averagedMeanSquare_moebius_of_tendsto`, every `h → ∞`,
  `h ≤ √x`); long windows `h ≥ √x` from PNT + square-divisor count (`Sieve/RouteELongWindow`);
  coprime square-root card formalized at every window law and moved to stage 3.

## Reusable assets from milestone D
- `Sieve/MoebiusMultiRangeWindow`, `…CofactorBounds`, `…LowCost`: multi-range Ramaré window with
  power thresholds and amplification; `Sieve/RamareLadderErrorSharp`;
  `Sieve/PrimeBlockPowerCofactorMeanSquare` (Lemma 13).
- `Sieve/MoebiusRangeLadder{Schedule,Costs,Window,Exceptional}`: the doubly exponential ladder
  and its `3000 M²/log ν` total cost; exceptional measure `√W|U| ≤ M exp(−T⁴⁰/(8 log T))`.
- `Sieve/HighRangeRouteTWindowTop`: Route-T high-range bound for any frequency top.
- `Sieve/MoebiusHeadWindowAllLengths`, `Sieve/MoebiusAveragedMeanSquareAllLengths`.

## Card 4 (growing reciprocal marker) — programme (2026-09-28)

**Why Menon is unavoidable.**  The card counts `n = ap`, `p ∈ (2^kN, 2^{k+1}N]` prime, `a` in the
window `(⌊X/p⌋, ⌊X/p⌋+L_k]`.  The marker primes have density `1/log X` among the starts, and a start
serves up to `4^k` markers, so the bad starts must be `o(A_k/log X)` (Cauchy–Schwarz over the
prime-weighted starts gives the same `1/log X` requirement even for a positive-proportion
conclusion).  MR's rate `(log X)^{-1/50}` cannot do this; Menon 2026 Thm 1.1 for `μ`
`(loglog L/log L)² + (loglog A)⁴/(log A)²` can (card `(15)`–`(17)`; arithmetic already in
`Sieve/GrowingReciprocalMarkerMenonRate`).  Paper text: arXiv:2607.15574 (retrieved, read).

**Menon for μ, proof skeleton (§2–§3, χ trivial, z = −1 and z = +1).**
1. `S` = integers with a prime factor in every MR range `[P_j,Q_j]`, `P₁ = (log Q₁)^{100/η}`,
   `Q₁ = min(h, exp(log X/loglog X))`, `P_j = exp(j^{4j}(log Q₁)^{j−1} log P₁)`,
   `Q_j = exp(j^{4j+2}(log Q₁)^j)`.  Prop 2.13: `#{n ≤ 3X, n ∉ S} ≪ X log P₁/log Q₁`
   (fundamental lemma, upper bound only).
2. Physical split `μ = μ1_S + μ1_{S^c}`; the `S^c` window counts are handled by the same frequency
   bound for `f ≡ 1` on `S` plus Prop 2.13 ⇒ `(log P₁/log Q₁)²`.
3. Lipschitz (Lemma 3.3) at `Y = X/(log X)^{3R}` (PNT for μ with error + sieve on `[x,x+Y]`).
4. Parseval (Prop 3.4 = MR Lemma 14) ⇒ `∫_{T₀}^{X/h}|F|² + max_T (X/(hT))∫_T^{2T}|F|²`,
   `T₀ = (log X)^R`, `F = Σ_{X≤n≤3X, n∈S} f(n)n^{-1-s}`.
5. `[T₀,T] = ∪ T_j ∪ U`, `T_j`: `j` minimal with `|Q_{j,v,H_j}(1+it)| ≤ e^{-α_j v/H_j}` ∀v.
   (3.4)–(3.5): MR Lemma 12 (Ramaré, `H`-adic) + MVT (j=1) / large values of range `j−1`
   (MR Lemma 8) + HM on `R_{j,v}` (j ≥ 2).
6. `U`: remove `n` with no prime factor in `[P,3X]`, `P = exp(log X logloglog X/(R loglog X))`
   (smooth numbers, `(log X)^{-R}`), Ramaré on `[P,3X]`; `|U| ≪ X^ε` (MR Lemma 8 at range `J`).
   Case I (`Q_v < X^{0.4}`): Route-T pointwise (Lemma 2.9) + HM on `R_v`.
   Case II: Heath–Brown (K=3) ⇒ products of ≤ 6 factors; IIa medium factor `[Q^{1/8},Q^{1/3}]`:
   μ-factor by zero-free region (Lemma 2.10), 1/log-factor by zeta-sum power saving (Lemma 2.11),
   rest by HM; IIb long factor `> Q^{1/3}` with coefficient 1/log: zeta-sum power saving
   `X^{-κ}` against `|U| ≪ X^ε`.
Analytic inputs to build/locate: fundamental lemma (upper), smooth-number bound
`Ψ(x,y) ≤ x u^{-u(1+o(1))}` (Rankin), improved MVT, discrete HM, MR Lemma 8, MR Lemma 12,
Route-T prime sums (owned), zero-free μ-sums (owned in `MoebiusTwist*`), zeta-sum power saving at
`|t| ≤ N^{7.5}` (k-th derivative test by Weyl differencing; corpus owns 2nd/3rd derivative tests,
`WeylDifferencing`), Heath–Brown identity (owned) + dyadic decomposition, PNT with error for μ.
Other card-4 pieces: combinatorial assembly `(18)`–`(30)` (Markov, fibres, Chebyshev, distinct
products), Shiu's bound `(32)` for `z^{ω(n)}` at `H ≥ √X`, low-breadth matching and Gibbs cost
`(33)`–`(36)`.
Corpus assets to audit first: `Sieve/Menon*` (184 modules, many from dead-end routes — see
`1-in-progress/route-e-four-card-stage3-working-log.md`), `Sieve/Maynard*` (Heath–Brown layer).

## Card 4 — revised route (2026-09-28, supersedes the Menon programme above)

Menon's rate is **not needed**.  The card's Markov step `(18)` asks for `o(A_k/log X)` bad starts
only because it charges every marker over a bad start at the maximal fibre multiplicity.  The
stage-3 Hall-law device (`Sieve/MarkerLossDevice`, `Sieve/MarkerHarmonicSupply`) charges the
*mean square* multiplicity instead: markers over a bad start set `S` lose harmonic mass
`≤ √(#S·(#M + 2Π))/M₀`, `Π` = shifted prime pairs within the fibre diameter (sharp 2-D sieve,
`GenericMarkerAnalytic.generic_pair_le'`).  Applied **per super-block** (a fixed number `g` of
dyadic blocks, so that `multiHarmConst (g-1) > 0`), the loss is `≤ √(ε·C_g)/log X` against mass
`≍ 1/log X`, provided the block's start scale `m` has `m² log X ≪ X` (`T1`).  So a bad-start
*density* `ε` bounded by an absolute constant suffices — i.e. MR's `o(1)` (milestone D).
Plan:
- A. `ladder*` generalisation of `Sieve/FreeScaleWindowCount` to arbitrary block windows and a
  growing number of super-blocks (union of per-super-block good markers, one final
  `card_sign_window_ge'`).
- B. per-super-block mass lemma (numeric core of `FreeScaleBudget.free_count_master`, generic
  bad set).
- C. uniform bad-outer bound: `∀ε, ∀ᶠ y, ∀ L ∈ [(log y)⁴, √y/log y], #badOuter y L ≤ …` by a
  diagonal (sequence) argument from `averagedMeanSquare_moebius_of_tendsto` +
  `eventually_fibre_step_one_growing_gen`.
- D. instantiation at `Z = ⌊X⌋`, `H₀ = ⌊√X h⌋`, windows `H₀·m_k/(4Z)`, smallest start
  `u ≍ Z(log Z)⁴/H₀`, `2^{Ig} ≍ h/(log Z)^{4.5}` ⇒ `(4)` with absolute `c`; `(5)` decoding; `(7)`.
- E. transport `(8)`–`(9)`, `(31)`–`(36)`: `Sieve/ShiuSharp` + `MobiusWoldBreadthGibbsCost`; `(34)`
  literal needs a Shiu-type bound without the `(log log)^{1-c₀}` loss of the three-term form.
- 2026-09-28 — card 4 `(4)`, `(5)`, `(7)` **closed** (Menon-free): `Sieve/BadOuterUniformWindow`
  (uniform-in-window exceptional set), `Sieve/MarkerLadder` (growing super-block ladder, decoded
  targets, per-super-block mass lemma), `Sieve/GrowingMarkerCountExplicit` (one-scale count),
  `Sieve/GrowingReciprocalMarkerCapacity` (`growing_reciprocal_marker_capacity`,
  `growing_reciprocal_marker_subpower_schedule`, `reciprocalMarker_decoding_unique`,
  `growingMarker_count_uniform` — uniform in `(log log X)² ≤ log h ≤ log X/10`).  Remaining for
  card 4: transport `(8)`–`(9)`, `(31)`–`(36)`.
- 2026-09-28 — **card 4 closed and moved** to `3-formalized/route e/` with companion.  Added
  `Sieve/ShiuAdaptiveCut` + `Sieve/ShiuOmegaTiltShortInterval` (Shiu's bound for `t^{ω(n)}` on
  `(A, A+y]`, `y ≥ √A`, sharp `(log A)^{t-1}`) and `Sieve/LowBreadthMarkerTransport` (`(34)`, cell
  matching `(8)`, shell Gibbs cost `(35)`–`(36)`).  Remaining in this folder: the two `E₃` cards
  (Matomäki–Teräväinen Thm 1.2 at exponent 1.55).

## The two `E₃` cards — what `a = 1.1` forces (2026-09-28)

Both remaining cards fix `a = 1.1` literally: card 3's `(FS1)`, card 1's `a₁ = 1.1`,
`a₀ ∈ [1.1 − 10⁻⁴, 1.1]`, `(1)` with `(log U)^{1.55}`, `(2)` with `(log U)^{-0.45}`.  So the input is
Matomäki–Teräväinen Theorem 1.2 (quantitative form, uniform in `a ∈ [1.1 − 10⁻⁴, 1.1]`) at the
paper's own exponent.  Paper re-read (`mt.txt`, §§2–7) against the corpus programme card
`1-in-progress/matomaki-teravainen-e3-lean-programme.md`:

- **Type II (§5.3) needs Jutila, not Huxley.**  With large-values exponent `σ₀`, the two Lemma-3.4
  branches close iff `a > 6/(5 + 2σ₀)`.  Jutila `σ₀ = 49/206` gives `103/94 ≈ 1.0957 < 1.1`;
  Huxley `σ₀ = 7/32` gives `96/87 ≈ 1.1034 > 1.1`.  The Type II range `θ ≤ 2/11` is tight at
  `a = 1.1` (the `ℓ = 5` branch needs `5θ ≤ 1/a`, equality at `θ = 2/11`).
- **Type I (§5.1) needs a twisted fourth moment**, but only with twist = the amplifier
  `M = P₁^k` of length `T^δ` for *some* fixed `δ > 0` (any `δ` works once `ε ≪ δ`).  Elementary
  substitutes fail by a power: Weyl pointwise + Halász on `U` gives `X^{1/a − 2/3}`; Lemma 3.4 on
  `U` keeps a diagonal term `≍ 1`; MVT loses the amplifier length.  Candidate non-spectral route:
  shifted divisor sums `∑_{am−bn=h} d(m)d(n)` by the Duke–Friedlander–Iwaniec δ-method + Weil
  (Hughes–Young range `θ < 1/11` suffices here).
- **Type I/II (§5.2) needs Watt's theorem with twist length up to `X^{1/4}`** (the prime `q₁` of
  the fourth Harman term).  Checked: (i) CS with the amplifier as the only twist needs
  `M₁M₂ ≤ X^{1/2+ε}` but Type I/II reaches `X^{5/8}`; (ii) MVT loss `X^λ`, `λ = 1 − 2μ₁ − μ₂`,
  equals the amplifier capacity, net `X^{λ/a} > 1`; (iii) moving `q₁` into Type II fails (at
  `θ = 1/4` the bad band `σ₁ ∈ [0.2987, 0.318]` survives every `ℓ`); (iv) the pure-prime reading
  of the fourth term (`E₃/E₄/E₅` with all primes `≥ X^{2/11}`) fails at equal levels
  `σ ∈ [0.2379, 0.2727]`.  So the input is spectral (Kuznetsov + Deshouillers–Iwaniec large sieve),
  as in the paper.
- **Main term (Theorem 2.1(ii) variant, programme M5c) is not started**: PNT-type counts of
  primes and of `ρ(m,q)` products in windows of relative length `X^{-1/100}`, Buchstab's `ω` on
  `[1, 7/2]`, and the paper's numerical bound `I₂(0) ≤ 0.99` (margin `≈ 0.0096` with
  `I₄ < 0.0004`).
- Pointwise `(5.6)` for the Type II variable needs a Vinogradov–Korobov-strength prime-sum bound
  (corpus Route-T envelope, `Sieve/VonMangoldtTwistPrimeEnvelope`, to be checked for the exact
  range `Q ≥ exp(log X/(log log X)³)`, `|t| ≤ X`).

Owned (programme card): Proposition 2.2 (repaired Lemma 2.3(ii)), Lemmas 3.3, 3.4, Huxley
Lemma 4.1 and Proposition 4.2 (integral form), Perron comparison bricks, Type I constructed-range
pieces.  Build order: M5c (main term) → Jutila (M4b) → §5.3 at `a = 1.1` + `(5.6)` → Lemma 3.1/§7
assembly → Type I twisted fourth moment → Watt (spectral).
- 2026-09-28 — **M5c numerics (main-term positivity)**: `Sieve/AffineEnvelopeQuadrature` (tangent of
  `log`, chords of `-log`, `1/x`, polynomial integrals, series log bounds `logLower/logUpper`),
  `Sieve/HarmanDiscardPrimeDensity` (`harmanDiscardPrimeDensity_le`: the `m`-prime discarded density
  `J₃(10⁻⁶) ≤ 0.8896`, exact inner integral, 13 cells), `Sieve/HarmanDiscardTwoPrimeDensity` +
  `...StripBounds`/`...StripBoundsUpper` (`m = p₃p₄`: section via `α₁ = 1-(2+β)α₂`, strip chords +
  wedge, 13 strips, `Σ N_s ≤ 0.0959`; tail `α₂ ≥ 1/4` gives `30κ`).  Remaining discarded pieces
  `J₅` (`m = p₃p₄p₅`) and `I₄` are crude (`≲ 2·10⁻³`).  Paper value `I₂(0) ≈ 0.9816`
  (arXiv ancillary notebook), so the margin `1 - 0.9855 - …` is ≈ 0.01.  Next: analytic side —
  short-interval PNT (exponent ≤ 0.89) up/down, uniform 1-D Mertens–Riemann sums, Harman identity
  `ρ⁻ = 1_P - D₂ - D₄`, assembly of Theorem 2.1(ii) for §7 (`ε ≤ κ/2`).
- 2026-09-28 — **M5c analytic design.**  The long window is `h₁ = x·exp(-c₁√log x)` (not `x^{99/100}`),
  `c₁ = c/4` with `c` from `Sieve.chebyshevTheta_sub_id_isBigO`, and the Perron cut `T₀ = exp((c₁/3)√log x)`;
  then every prime count in the main term (`(Z, Z(1+θ)]`, `Z ≥ X^{2/11}/2`, `θ = h₁/x`) follows from the
  classical PNT error, with no short-interval PNT.  Cost: the §5 bounds must hold for `T ≥ T₀`
  (all are powers of `T` or global over `[0, X]`; to be rechecked brick by brick).  Tools:
  (B1) uniform Mertens–Riemann `∑_{y^l<p≤y^r} g(log p/log y)/p = ∫_l^r g/α + o(1)` for Lipschitz
  families (partition + `abs_mertensS_sub_logLog_sub_const_le`); (B2) prime counts in
  `(Z, Z(1+θ)]`; (B3) Harman identity `ρ⁻ = 1_P − D₂ − D₄`; (B4) assembly with `ε ≤ κ/2 = 5·10⁻⁷`.
- 2026-09-28 — **M5c analytic side, part 1**: `Sieve/MertensRiemannUniform` (uniform Mertens–Riemann,
  partition + Mertens with `O(1/log)` error), `Sieve/PrimeCountRelativeWindow` (primes in
  `(Z, Z(1+θ)]`, `θ ≥ exp(-c√log Z)`, from the classical PNT error), `Sieve/HarmanDiscardedTails`
  (exact `ρ(n,Q) = ρ⁻ + D₂ + D₄`), `Sieve/HarmanDiscardPairTuples` / `...QuadTuples` (window sums of
  `D₂`, `D₄` ≤ prime counts over prime tuples; rough `m < q⁴` by shape), `Sieve/LipschitzBoundCalculus`,
  `Sieve/MertensRiemannEnvelopes`, `Sieve/HarmanDiscardPrimePairSum`
  (`eventually_harmanPrimePairSum_le`: the J₃ prime-pair sum ≤ 0.8896 + η).  J₃ cells now expose
  pointwise envelopes (`harmanDiscardPrimeInner_le_cellEnvelope*`).  Next: J₄ prime-triple sum,
  J₅/I₄ crude sums, PNT-window substitution, assembly of the window lower bound.
- 2026-09-28 — **M5c main term closed** (`Sieve/HarmanWindowMainTerm.exists_window_rhoMinus_ge`):
  `∃ c > 0, ∀ᶠ y, ∀ θ ∈ [exp(-(c/4)√log y), 1]`, for Harman parameters `z, Q, D, E` on the scale `y`
  (`HarmanWindowScale 10⁻⁶ y`, plus `z, D ≤ Q ≤ y < Q²/2`):
  `∑_{y<n≤y(1+θ)} ρ⁻(n) ≥ θy/(250 log y)`.  Chain: `HarmanDiscardTwoPrimeTripleSum` (J₄ prime-triple
  sum ≤ 0.0960 + η), `HarmanWindowTupleCounts` (cofactor windows, nested-region sums, log coordinates),
  `HarmanWindowPrimeCofactor` (J₃ part ≤ (1+η)(0.8896+η), unit part), `HarmanWindowTwoPrimeCofactor`
  (J₄ part + diagonal), `HarmanWindowCrudeTails` (three-prime cofactor and quadruple tail by boxes,
  `≤ 0.0097`).  Margin: `1 − 0.8896 − 0.0960 − 0.0097 − O(η) ≥ 0.0046`.  Next: the MT Theorem 1.2
  long-window sum (sum over `p₁ ∼ P₁`, `p₂ ∼ √(x/P₁)/2` with `X = √(xP₁)`, `h₁ = x·exp(−(c/8)√log x)`),
  then the analytic side (Jutila, §5.3 at `a = 1.1`, (5.6), Type I twisted fourth moment, Watt, Perron/§7).
- 2026-09-28 — **Long-window main term of Theorem 1.2** (`Sieve/MatomakiTeravainenAllIntervalLongWindow`):
  `mtAllIntervalSum z Q D E P₁ R x h = ∑_{P₁<p₁≤2P₁} ∑_{R<p₂≤2R} ∑_{x<p₁p₂n≤x+h} ρ⁻(n)`;
  `exists_mtAllIntervalSum_long_ge`: `∃ c > 0, ∀ᶠ x, ∀ a ∈ [1,2], ∀ ε ∈ (0, 10⁻⁷]`, with `P₁ = (log x)^a`,
  `R = √(x/P₁)/2`, `X = √(xP₁)` (Proposition-2.2 parameters at `X`), `h₁ = x·exp(−(c/8)√log x)`:
  `mtAllIntervalSum … x h₁ ≥ h₁/(2250 (log P₁)(log x)²)`.
- **Analytic plan for Theorem 1.2 (a = 1.1), T₀ = exp((c/32)√log x).**  Perron comparison
  (`Lemma31PerronComparison.norm_perronWindowSum_compare_sub_integral_le`, comparison kernel bounds
  `PerronCompareSharp`/`LowFreq`): low frequencies `|t| ≤ T₀` cost `exp(−(c/16)√log x)·(log x)^{O(1)}`;
  high frequencies need `(FS7)` for `P₂` (owned) and `(5.2)` for `P₁·P`.  `(5.2)` = non-`U` part
  (pointwise `|P₁| ≤ P₁^{−ε/10}` + improved MVT + z-rough pair sieve) + `U` part through Proposition 2.2
  (owned): Type II (Jutila σ₀ = 49/206 + (5.6) from Vinogradov–Korobov; `T₀` lowered is harmless since
  the prime blocks have `δ|t| ≥ exp(c'√log X)`), Type I (twisted fourth moment, twist `≤ T^{δ₀}`),
  Type I/II (Watt, twist `≤ X^{1/4}`).  Order: FS7 check → non-U part → Type II → Type I → Type I/II →
  assembly → deleted-support perturbation (card 3) and `a`-uniformity (card 1).
- **Jutila's large-values theorem (source: M. Jutila, Zero-density estimates for L-functions, Acta Arith.
  32 (1977) 55–62, read 2026-09-28).**  Notation: `f(s) = ∑_{N<n≤2N} a_n n^{-s}`, `G = ∑|a_n|²`, points
  `s_r = σ_r + it_r`, `σ_r ≥ 0`, `|t_r| ≤ T`, 1-spaced, `|f(s_r)| ≥ V`.  For `q = 1`:
  `(1.2)  R ≪ (GNV⁻² + T(G⁴N²V⁻⁸)^k + (TG²V⁻⁴)^k) T^ε`;
  `(1.4)  R ≪ (GNV⁻² + T G^{3−1/k} N^{1−1/k} V^{−6+2/k} + T(G⁴N²V⁻⁸)^k) T^ε` (= MT's display, k = 7).
  Proof of (1.2): reduce to `|t_r − t_s| ≥ h² = log⁴T`, `σ_r ≤ 1/2`, `N ≤ T`; Halász–Montgomery
  `R²V² ≪ GRN + G∑_{r≠s}|H(s_r + s̄_s)|` with smooth `H(s) = ∑ b(n)n^{-s}`,
  `b(n) = e^{−(n/2N)^h} − e^{−(n/N)^h}`, `h = log²T`.  Lemma 1 (reflection): for `h² ≤ |t| ≤ T`,
  `|H(s)| ≪ N^{1/2} ∫_{−h²}^{h²} |∑_{n≤M} n^{−1/2+i(t+τ)}| dτ + 1`, `M ≍ (|t|+h³)/N`
  (Mellin `H(s) = (1/2πi)∫ζ(s+w)Γ(1+w/h)((2N)^w−N^w)/w dw`, shift to `Re(s+w) = −1/2`, functional
  equation, split the dual series at `M`).  Hölder with exponent `2k` on the dual sum, Lemma 2
  (positivity: `∑_{r,s}|∑ a_n z_{rn} z̄_{sn}|² ≤ A²∑_{r,s}|∑ z_{rn}z̄_{sn}|²`, removes `d_k ≤ n^ε`),
  Lemma 3(i) (`∑_r |∑_{n≤N'} n^{−1/2+it_r}|² ≪ (N' + (RT)^{1/2}) log^B T`, from the fourth moment of
  `ζ` via `∑_r |ζ(1/2+it_r)|² ≤ R^{1/2}(∑|ζ|⁴)^{1/2}`) give
  `R²V² ≪ GRN + GN^{1/2}T^ε R^{2−1/k}{R((T/N)^k + (RT)^{1/2})}^{1/2k} + GR²`.
  (1.4) = (1.2) on windows `T₀ = V⁴G⁻²(GNV⁻²)^{1/k}` (Huxley subdivision).  At `k = 7`,
  `N ≥ T^{9/11}` this gives MT Lemma 4.1 up to `σ = 49/206`; `a = 1.1` needs `σ₀ > 0.2273`.

## Theorem 1.2 at a = 1.1 — work breakdown (2026-09-28)

| id | piece | status |
|-|-|-|
| A1 | window main term `exists_window_rhoMinus_ge` | **done** |
| A2 | long-window E₃ sum `exists_mtAllIntervalSum_long_ge` | **done** |
| B1 | Perron short/long comparison at `T = (x/h)L^{10}`, low frequencies `|t| ≤ T₀` | todo (corpus `Lemma31PerronComparison`, `PerronCompare*`) |
| B2 | dyadic high-frequency split + CS against `(FS7)` | todo (`DyadicPrimeMeanSquare`) |
| C1 | non-`U` part of `(5.2)`: `∫|P|² ≪ TP₁/(X log X) + (log X)⁻²` (improved MVT + z-rough pair sieve) | todo (`ImprovedMeanValue`, `RoughPairSieve*`) |
| C2 | `U` part via Proposition 2.2 (owned) | todo (assembly) |
| D1 | Jutila (1.2)/(1.4) and Lemma 4.1 up to `σ = 49/206` | todo: Halász with smooth weight, reflection Lemma 1 (Mellin/FE; corpus `SmoothAFEZeta*`), Lemma 3(i) (discrete 4th moment near ½), subdivision |
| D2 | Proposition 4.2 at Jutila strength | todo (corpus Prop 4.2 is Huxley-hardwired `7/32`) |
| D3 | (5.6) Vinogradov–Korobov pointwise bound for prime blocks `≥ z₀` on `[T₀, X]` | todo (Route-T envelope) |
| D4 | §5.3 Type II assembly at `a = 1.1` | todo |
| E1 | Type I: twisted fourth moment, twist `≤ T^{δ₀}`, `δ₀ < 1/11` (non-spectral route: DFI δ-method + Weil) | todo |
| E2 | Type I/II: Watt's theorem, twist `≤ X^{1/4}` (spectral: Kuznetsov + Deshouillers–Iwaniec) | todo |
| F1 | Theorem 1.2 weighted, uniform in `a ∈ [1.1−10⁻⁴, 1.1]` | todo |
| F2 | card 3 perturbation (deleted support), diagonal removal; card 1 row supply (6) | todo |
- 2026-09-28 — **D1 (Jutila) progress.** `RHTower/ZetaChiLeftHalfPlaneGrowth` (`χ(z−2) = χ(z)(1−z)(z−2)/4π²`,
  sharp `|χ(1/2−2j+iy)| ≤ (|y|+2j+2)^{2j}`, `|ζ| ≥ c` on `Re ≥ 3/2`, polynomial `χ` on left strips);
  `RHTower/SmoothDyadicZetaReflection.exists_norm_dyadicSmoothGram_le` (Jutila's Lemma 1 with the
  corpus Gaussian AFE: `|∑ n^{-1-iτ}(V(n/2N)−V(n/N))| ≤ N^{-1/2}∫e^{-v²}|∑_{m≤M} m^{-1/2+i(τ+v)}|dv
  + C_j(|τ|+2j+2)^{2j}M^{1/2−2j}N^{-1/2−2j} + 2e^{-τ²}/|τ|`).  Next: smooth Halász–Montgomery, Hölder
  with the positivity trick and the discrete mean value theorem (MVT replaces Jutila's fourth-moment
  Lemma 3; `k = 9`, `σ₀ = 0.23` suffices), subdivision, Lemma 4.1.
