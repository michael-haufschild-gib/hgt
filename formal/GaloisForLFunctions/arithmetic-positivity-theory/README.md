# Arithmetic Positivity Theory (APT)

Namespace `GaloisForLFunctions.ArithmeticPositivityTheory`; umbrella `ArithmeticPositivityTheory.lean`.

## 1. Motivation

RH ⇔ the Weil form `Q(g) = Re W_Λ(g,g) ≥ 0` for all admissible tests. APT asks where `Q ≥ 0` can be
proved unconditionally, channel by channel, on explicit arithmetic test families built from the
factorial (Müntz) correction tails, and how that positivity transfers to the tests that see zeros.
Three questions organise the programme:
1. Source side: on which structured families (blocks, windows, lacunary unions, translated patterns)
   is `Q` positive, and which channel pays for it?
2. Receiver side: how do these families approximate fixed-aperture tests (grid tents, smooth
   detectors, odd receivers), and what does positivity there say about zeros?
3. Selectivity: which conclusions see the exact weight `Λ` (and hence RH), and which hold for any
   comparable prime weight?

## 2. Objects

Filter and collar.
- `C(u) = {u}(1−{u})/2`; dyadic Bernoulli filter `P(u) = C(4u)/4 − 2C(2u) + 4C(u)`.
  `P(u) − 3/16 = −(2/π²) Σ_k χ(k) cos(2πku)/k²`, `χ(k) = 1, −1, 0` for `k` odd, `≡ 2 (4)`, `≡ 0 (4)`.
  `(4, −2, 1/4)` on `{1,2,4}` is the unique stencil with multiplier `4χ`.
- Collar `λ_N`: `4λ_N³ = N²(4N+1)` (irrational, algebraic); `δ_N = λ_N − N ∈ [1/15, 1/12]`;
  affine defect `e_N = N + 1/12 − λ_N`, `N e_N ∈ [1/225, 1/140]`, `N e_N → 1/144`.
- Phase profile `Φ_N(v) = P(λ_N v) − P(N v)`; pattern combination
  `B_b(v) = Σ_n b_n Φ_{n+1}(v) = −(2/π²) Σ_k w_k H_k`, `w_k = χ(k)/k²`, `Σ_{k≥2}|w_k| ≤ 3/4`.
  `H_k` = exponential sum on four signed branches `±k(n+1), ±kλ_{n+1}`, pairwise `k/15`-separated.

Sources (clock `v = e^{−x}`, `∫_{x≤0} e^x H(e^{−x}) dx = ∫_{v>1} H(v) v^{−2} dv`).
- Correction tails `T_n(x) = 1_{x≤0} a_n e^{3x/2} Φ_{n+1}(e^{−x})`, `144/(n+1) ≤ a_n² ≤ 225/(n+1)`;
  span tests `f_b = Σ (b_n/a_n) T_n`. Corrected (Müntz-smoothed) sources `H_{n,k}` = compact ramp
  `r_{n,k}` + noncompact tail `U_{n,k}`.
- Critical source `g_b(x) = 1_{x≤0} e^{x/2} B_b(e^{−x})` (endpoint jump at `x = 0`).
- Collared `g_c = σ(e^{−x} − 1) g_b` (`σ` = smooth transition, `0 ≤ σ' ≤ 4`, `|σ''| ≤ 95`).
- Doubly collared / truncated `g^V = χ(e^{−x}/V) g_c` (`criticalTruncatedTest`), compact support
  `[−log 2V, 0]`, Lipschitz; only dilations `r ≤ 2V` reach its prime channel.
- Admissible harmonic weights (`AdmissibleHarmonicWeight`): `w_1 = 1`, `|w_k| ≤ C/k²`,
  `Σ_{k≥2}|w_k| ≤ τ < 1`; covers q-adic sign-flip, q-adic drift-free, higher-order families.

Supports. Dyadic block `n+1 ∈ [M,2M]`; scale window `ScaleWindow S M L` (`n+1 ∈ [M,LM]`);
lacunary family `M_{i+1} ≥ M_i⁸`; linear window `[N, (1+δ)N]`; translated patterns `n + S`, `n → ∞`;
low window `[1, L]`.

Form and channels.
- `Q(g) = compactFullWeilEnergy g = Lévy(g) + Ω(0)·ac(0) + 2·R·E − 2·P(g)`:
  `ac` = autocorrelation, `Lévy(g) = ∫_{x>0} (ac(0) − ac(x)) ω(x) dx` with `ω = archLevySinhWeight`
  (`e^{−1/2}/x ≤ ω ≤ 3/x` on `(0,1]`, `ω ≤ 48x^{−2}` on `x ≥ 1`), polar readout `R = ∫ g e^{x/2}`,
  endpoint `E = ∫ g e^{−x/2}`, prime energy `P = Σ_r Λ(r) r^{−1/2} ∫ g(x) g(x − log r) dx`.
- Prime atom in clock form: `Λ(r)/r · ∫_{v>1} weight(v) B(v) B(rv) dv`.
- Five equal realizations on `C_c`/`C²_c`: `compactFullWeilEnergy` = `fullZeroForm` (ACT) =
  `Re weilFullFunctional Λ` (RHTower) = `Re zetaZeroConfig.W` = `SquareMass − ReflectionDefect`.
- Zero-square mass `Z(f) = Σ_ρ m_ρ |f̂(γ_ρ)|²`; `|W(f,g)| ≤ √(Z(f)Z(g))`.

Prime limit objects (translated patterns).
- Charge `A(m) = χ(m) Σ_{r|m} r Λ(r) χ(m/r)`; `A(m) < 0 ⇔ m = 2` (`A(2) = −2 log 2`), `= 0 ⇔ m = 1`
  or `4|m`, `A(p) = p log p`.
- Slow-phase defect `D(m) = ∫_{v>1} v^{−2}(1 − cos(2πmv/12))`; pattern mass
  `J_m(S,b) ∈ [Σb²/48, 4Σb²]`.
- Band weight `W(u) = u^{−2}(1 − cos(πu/6))`, Poisson `Σ_z γ(t+z) = π²/6`.
- Cell kernel `R(t)` on `[0,1]` with `P∞(S,b) = (4/π⁴) ∫_0^1 R(t) |Σ_j b_j e^{2πijt}|² dt`;
  Toeplitz coefficients `κ(k)`.

Receiver objects. Grid tent pattern `gridTentPattern G n a M` (piecewise-linear interpolant of
`G = e^{−3x/2} g` on the factorial grid, built from unit ramps), smoothed detector
`smoothGridTentDetector` (`C²_c`), period difference `f − f(· − L)`, zero configurations
(`isolatedPairConfig`, lattices, clusters), `ZetaWindowPositive R`, `HodgeIndexAtLevel`.

## 3. Language

- Channel: one summand of `Q` (Lévy/archimedean, Gamma `Ω(0)ac(0)`, polar `2RE`, prime `−2P`).
- Slope/offset/threshold: lower bounds `(s(log M − c) − K) Σb²`; threshold `M₀ = exp((c s + K)/s)`.
- Subsidy: `P ≤ −μΣb²` makes `−2P` a positive contribution.
- Critical family: sources `g_b, g_c, g^V` and their unions; carry a scale `M`.
- Receiver: fixed-aperture tests (no scale); the RH-equivalent side.
- Transfer: approximation of receivers by critical/tent families in all five forms with explicit error.
- Detection: an explicit test with `Q < 0` for a given zero configuration.
- Dominance cone: `E_low ≤ Λ E_high`.
- Tempered weight: `|w(r)| ≤ C Λ(r)` (`TemperedPrimeWeight`).

## 4. Mechanisms

M1. Archimedean log gain. Lévy symbol `∫(1 − cos tx) ω(x) dx ≥ e^{−1/2}(log|t| − 3)` for `|t| ≥ 1`.
A source with mass floor `A Σb²` whose low band `|t| ≤ ηM` carries at most half the Plancherel mass
has `Lévy ≥ e^{−1/2}(A/2)(log M − 3 − log(1/η)) Σb²` (`ofReal_le_sourceLevyEnergy`,
`sourceLevyEnergy_ge_highBand`). Low-band smallness comes from nonstationary Mellin phase: harmonic
frequencies `2πkλ ≥ 2πN` have phase derivative `≥ |ω|/2` against `|t| ≤ πM`, so
`|∫_1^∞ a(v) e^{i(ωv − t log v)}| ≤ 5/|ω|` and readouts are `≤ (15/π³) Σ|b_n|/(n+1)`.

M2. Riesz/Montgomery–Vaughan. Branch separation `k/15` gives MV interval bounds `(ℓ ∓ K/k)Σ|b|²`,
`K = 390/π`; first-harmonic dominance (`Σ_{k≥2}|w_k| ≤ 3/4`) gives window floors on length
`16K`, two-sided Riesz bounds for tails, Bohr coercivity `Σ|b|²/(8π⁴)`, linear independence of tails.

M3. ℓ²-control of the prime channel. Dilation correlations `∫φ B(v) B(rv)`: Schur test on
`11/12`-spaced branches, resonance `k ≈ lr` paid by `1/k²` weights ⇒ `r^{−1/2}` decay ⇒ majorant
`Λ(r)/r^{3/2}`. The uncollared endpoint jump has a Hilbert `1/f` tail; the collar removes it (flat
weight, two integrations by parts) or Montgomery–Vaughan on the jump kernel `sin(2πf)/(2πf)`
restores ℓ² control. On windows `[M,LM]` the decay is `min(1, √(L/r))`, cost `Θ(log L)` (Mertens,
sharp for this majorant). Cross-block coupling decays like `(mn)^{−1/16}` on `m⁸ ≤ n`.

M4. Prime subsidy in the translated limit. Rational dilation law: correlations at dilation `ρ`
keep only harmonic pairs `k = ρl` (limit vanishes at irrational `ρ`; autocorrelation limit supported
on `log ℚ_{>0}`). Regrouping gives `P∞ = (4/π⁴) Σ_m A(m) J_m/m⁴`; summation by parts + Poisson
window give `R(t) = Σ A(m)D(m)/m⁴ − ½ Σ (A(m)/m³) dev_m(t) ≤ −1/7000`. Only `A(2)` is negative,
yet `R` is negative because of the window structure.

M5. Divergence by Fatou. On translated patterns `ac(x) → 0` for a.e. `x` (irrational `e^x`) while
`ac(0)` keeps a floor; `ω ≥ e^{−1/2}/x` makes the Lévy channel diverge.

M6. Scale-free Schur complement. Low-window Lévy energy `≤ C L³ Σb²` independent of `M, V`
(interpolation `|Δ|⁴ = |Δ||Δ|³`); Young weight `γ x^{1/4}` keeps both diagonals:
`Q(low ∪ high) ≥ Q(low) + Q(high) − 2√(C_SL C_SH) √(E_low E_high)`.

M7. Transfer. Grid tents: `Σ_j ramp(u − j) = clamp(u,0,M)` (Abel), interpolation error `2Ld`,
`|Q(tent) − Q(g)| ≤ C_grid d_{n+1} ≤ C_grid/(12(n+1))` in all five forms; mollification
`|Q(smooth_k f) − Q(f)| ≤ C/(k+1)` from one L¹-Lipschitz bound on all channels; translation
invariance; parity split (even/odd channels additive, `g^V` splits mass in halves); norm-controlled
subfamily transfer: floor `−C e^{2σr}∫g²` with `∫g² ≤ α e^{2βr} ∫F²` ⇒ `zetaZeroWidth ≤ σ + β`.

M8. Detection. Period difference `f − f(· − L)` annihilates the whole on-line lattice
`½ + 2πik/L`; thin nonnegative seeds keep pair readouts in a quarter-sector, giving
`W ≤ −(e^{δL} − 1)(1 − e^{−δL}) e^{−2δR}` on an off-line pair. Reflection identity
`SquareMass − Re W = ReflectionDefect` holds for every configuration.

M9. Markov–pole split at aperture `N`: `W = M_N + cosh(g)²/2 − sinh(g)²/2` with `M_N` Markovian;
cosh kills odd `g`, sinh kills even `g`; for odd `g`, `W ≥ 0 ⇔ sinh(g)² ≤ 2M_N`.

M10. Single height. `W(S_ξ f) = A_f(ξ) − Π_f(⌊e^{2a}⌋, ξ)`; pole terms decay like
`2e^a B_f²/(1 + 2π|ξ|)⁴`; Bohr–Kronecker syndetic alignment makes prime phases return.

## 5. Pillar theorems (all unconditional)

1. Tail span coercivity: `Re W(f_b, f_b) ≥ (c log M − C) Σ|b_n|²` for complex `b` on `n+1 ≥ M`
   (`FactorialTailSpanWeilCoercivity`).
2. Compact critical positivity, uniform in `V ≥ V₀` (supports of unbounded length):
   dyadic blocks above `M₀`; windows `L ≤ M^δ` with margin `(s/4) log M Σb²`; lacunary unions of any
   depth `J` (`exists_compactFullWeilEnergy_pos_of_lacunary`,
   `exists_polynomial_window_compact_weil_and_fullZeroForm_pos`); positivity in all five forms and
   on grid tents/detectors built from these sources.
3. Prime cell kernel: `R ≤ −1/7000`, hence `P∞(S,b) ≤ −(4/(7000π⁴)) Σb²` for every finite real
   pattern; Rayleigh quotients fill exactly `[(4/π⁴) min R, (4/π⁴) max R]`; `R` has its unique
   minimum at `½` (`FactorialCriticalPrimeKernelNegativeDefinite`, `...ToeplitzSymbolRange`).
4. Linear window: `∃δ, N₀`, actual `P ≤ −(2/(7000π⁴)) Σb²` on every support in `[N,(1+δ)N]`
   (dimension `> δN`); complete energy `≥ (s(log N − c) + 4/(7000π⁴) − |Ω(0)|U − 2304/N) Σb²`
   (`exists_linearWindow_criticalPrimeEnergy_le`).
5. Negativity boundary: the dyadic pair `{M−1, 2M−1}` has `P∞ ≥ log 2/(8π⁴) > 0`; negativity fails
   on dyadic blocks, windows `L ≥ 2`, wide linear windows, polynomial windows
   (`CriticalPrimeChannelBeyondLinearWindows`).
6. Translated coercivity: for each finite `S` and each `K`, eventually `Q ≥ K Σb²` for all `b`
   (non-effective) (`FactorialCriticalCompleteFormUniformCoercivity`).
7. Schur complement and dominance cones: low window + lacunary family with `L_low⁸ ≤ M₀`; a low-mode
   certificate `Q(low) ≥ μ E_low` plus an explicit `M₀` gives `Q ≥ (μ/2)(E_low + E_high)`; every cone
   `E_low ≤ Λ E_high` is positive above `M₀(L_low, Λ)`; coupled sources `Σ b_low(n)(g_n + γ_n g_{φ(n)})`
   are positive for all nonzero `b_low` (`LowScaleCoupledPositivityAndSchurComplement`).
8. Grid-tent completeness: RH ⇔ eventual `Q(tent) ≥ 0` for all seeds; at a single radius `R`,
   tent positivity ⇒ `ZetaWindowPositive R`, `HodgeIndexAtLevel R`, ground energy `≥ 0`, and every
   zero with `2 ≤ |γ| ≤ exp(R/(10⁵ A₀ log² R)) − 306` has `|β − ½| < 1/R`
   (`zetaWindowPositive_and_hodgeIndex_of_eventually_gridTentPattern_nonneg_at_radius`,
   `zeta_excluded_depth_below_clusterHorizon_of_gridTentPattern_nonneg`).
9. Detection: every actual off-line zero of `ζ` is detected by a single-scale grid tent and smooth
   detector; quantitative lags (near-top, polylog, attained-top `O(1/g)` and `O(log 1/g)`); off-line
   lattice with spacing `2π/L` is invisible exactly up to aperture `L/2` (Nyquist).
10. Small aperture: `Q(F) ≥ (1/5000)∫F²` on `[−3/10, 3/10]`; odd `F`: `Q ≥ (1/1000)∫F²` on
    `[−181/500, 181/500]` (past the first prime `(log 2)/2`); transferred to tents and detectors.
11. Source selection: narrow pair tests `h_m + σ h_m(· − log m)` read the single coordinate
    `w(m)`; every `Λ + δ1_{n=m}` (`δ ≠ 0`) is refuted unconditionally by truncated Riemann kernels;
    `PositiveOnNonposCone U ⇔ RH ∧ Λ ≤ U`, `PositiveOnNonnegCone L ⇔ RH ∧ L ≤ Λ`; for a source
    identified with `Λ`, cone membership ⇔ RH (`SourceSelectionInTheFullWeilCone`).
12. Selectivity: every tempered weight (Liouville twist, node 4 deleted, primes only, bounded
    Beurling perturbations) has the same uniform-in-`V` window positivity as `Λ`; the shifted pair
    `ζ(s−a)ζ(s+a)` (`a ≠ 0`) has negative Weil value on wide shift pairs; at fixed `V` every weight
    passes (`WideWindowSelectivityAndBeurlingInfrastructure`).
13. Connes–Consani Sonin dichotomy: at cutoff `1`, trace domination fails on nonnegative small
    bumps, on odd mean-zero two-packets, on pole-free four-packets, with infinite negative Morse
    index and on every finite-codimension moment subspace; at every cutoff `Λ > 1`, separated
    multi-packets from profiles of width `< log Λ/(‖G_Λ‖₁ + 1)` satisfy it for all coefficients
    (`SpectralRealisationAndOperatorConstraints`).
14. Single-height laws: no lower bound `PX ≥ −(c√X + C)/π` with `c < 2` and no power saving even
    eventually in height; sharp horizon coefficient `(4 + ε)e^a`; power saving `Re Π_f ≤ c e^{θa}‖f‖²`
    gives positivity up to `X ≍ (log|ξ|)^{2/θ}`, destructive cone up to `X ≲ |ξ|⁸`; violation heights
    have window measure `O(X^{−θ} log² X)` (`SingleHeightPhaseSelectiveApertureAndPowerSaving`).
15. Rank-one readout: corrected sources satisfy `F_{H_{n,k}}(ρ) = F_{η_k}(ρ) c_n/ρ`,
    `c_n = 1/(2√(n+1))`; on the hyperplane `Σ a_n c_n = 0` combinations are invisible to zeros
    (`W(H,·) = 0`) (`RankOnePoleReadoutAndZeroNullspace`).

## 6. Tools

Developed (reusable):
- Flat-amplitude nonstationary phase: `a(1) = 0` ⇒ `|∫_{v>1} a e^{i(ωv − t log v)}| ≤ (2/|ω|)(‖a'‖₁ + ‖a/v²‖₁)`.
- Lévy symbol lower bound; abstract high-band Lévy law (mass floor + low-band smallness).
- Spaced-sum lemma, Schur test, dyadic dilation inequality, box–tail estimate for doubly weighted
  series, Montgomery–Vaughan jump-kernel bound.
- Band-limited Poisson window `γ(u) = (π²/72) sinc²(πu/12)`, window deviation `≤ (π/6)³/35`.
- Cosine-shell Gram law (disjoint frequency intervals are orthogonal, energy `π(b−a)`).
- Quantitative full-Weil smoothing (one L¹ bound controls all channels); grid-tent approximation
  constants; parity split; norm-controlled receiver transfer.
- Zero-side Cauchy–Schwarz; relative margin `δ − ε − 2√ε > 0 ⇔ ε < (√(1+δ) − 1)²` (sharp, two-mode
  extremizer); binary Schur `M² ≤ 4AD`.
- Multi-packet Toeplitz decoupling for kernels vanishing at infinity.
- Syndetic Bohr–Kronecker prime-phase alignment.
- Explicit constants: `|Ω(0)| ≤ 7`, `U ≤ 40`, `ΣΛ(r)/r^{3/2} ≤ 18`, channel constants `≤ 1.25·10⁵`;
  slopes `s ≥ 10^{−15}` (uncollared), `10^{−8}` (collared); `logLinearThreshold` closed forms.

To build:
- A positivity certificate for pure low modes (supports in `[1, L]`, no high partner).
- A mechanism for fixed-aperture receivers that does not pass through a scale `M` (odd sector,
  `sinh` capacity at aperture `N`).
- Effective translated coercivity (replace Fatou) and slopes large enough to make `M₀` usable.
- An input that separates `Λ` from tempered/Beurling weights uniformly in `V` on compact tests.

## 7. Open questions

- Low modes: is `Q(g^V) ≥ μ Σb²` on supports `[1, L]` uniformly in `V`?
- Which pattern cone carries `P∞ < 0` beyond linear windows? (Known: linear windows yes, dyadic pair
  no.)
- Can a family with `(α, 0)`-norm-controlled transfer to odd receivers carry a positivity mechanism
  other than `log M` (a subexponential odd floor is RH-equivalent)?
- What extra structure of `Λ` (multiplicativity, node criticality, exact coordinates) can enter a
  sign argument at fixed aperture? Node-deletion tests are selective; the critical family is not.
- Single height: characterise heights where power saving holds; relate the
  `O(X^{−θ} log² X)` bad-height measure to zero density.
- Sonin cutoff: does domination at `Λ > 1` extend beyond separated multi-packets?
- Effective rate for the rational dilation law / translated divergence.

## 8. Traps

- Large-scale positivity is not RH. Every `∃M₀` statement lives on tests of scale `≥ M₀`; receivers
  have no scale. With `s ~ 10^{−15}` the thresholds are `≈ exp(10^{20})`.
- Sign convention: `Q` contains `−2P`. Negative definite `P` is good.
- Uncollared sources: the endpoint jump gives `(Σ|b|)²` bounds; atom count may grow only like
  `log M`. Use the collar or Montgomery–Vaughan.
- Uniform cross-scale oscillatory gain is false: the thirteen family has gaps `→ 0` with full
  correlation mass while each Bohr mean is `0`. Baker/Bohr disjointness gives no rate.
- The subsidy does not extend past linear windows; positive cumulative charge does not fix the sign
  of `P∞`.
- Critical-family positivity is not selective: tempered weights, including Beurling systems with
  off-line zeros, pass identically. At fixed `V` any weight passes (only `r ≤ 2V` enter); the only
  separating quantifier is uniformity in `V`.
- Coupled low–high positivity does not certify pure low modes.
- Many results are RH-equivalent reformulations (tent positivity, odd subexponential floors,
  source-identified sign, pole compression, Suzuki overshoot, one-sided cones); they relocate RH.
- Cutoff-1 Connes–Consani domination is false; do not build on it.
- The archimedean–pole budget cannot be frozen at height `0`; height-eventual power saving is false.
- Pole-free corrected combinations are invisible to zeros; they carry no zero information.
- Conditional statements present in the corpus (under `RiemannHypothesis`, e.g. superexponential
  Bohr recurrence gaps) are consequences, not progress.

## 9. Place in the research

APT is the source-side engine: it builds explicit test families with certified positivity and
pushes them to receiver tests.
- Imports: `RHTower` (explicit formula, `weilFullFunctional`, CCM/Sonin, Suzuki, Beurling, zero
  density, Baker), `BiScaleUncertainty` (Lévy symbol, signed prime/polar, node-deletion price),
  `SquareRootThreshold` (off-line visibility, lag hierarchy, localized height forms, horizons),
  `ArithmeticCriticalityTheory` (`fullZeroForm`, pole-free variation), `ArithmeticCastelnuovoSeveri`
  (Hodge index at level, excluded depth), `HTGeometry` (Bohr almost periodicity, Szegő tail),
  `SelbergClass`, `Bottcher`.
- Consumers: `RHTower` Suzuki critical-family transfer and `CrossRouteReceiverBridges`;
  `ArithmeticOrientationTheory` (width functor, source dictionaries, receiver scales);
  `SquareRootThreshold` (aperture `3/10`, routes at one aperture, width-bounded floors);
  `SelectivePositivityAndThresholdLaws`; `ArithmeticCastelnuovoSeveri`; `ArithmeticPolarization`;
  `SpacingScaleHarmonicAnalysis`; `ArithmeticCriticalityTheory` (Markov windows).
- Shared dictionary: the five-form identity makes APT energies, ACT zero forms, RHTower Weil
  functionals and zero-side forms interchangeable.

## 10. Big picture

Weil positivity is cheap wherever a scale is available: the archimedean channel grows like `log M`,
every arithmetic channel is ℓ²-bounded, and on linear windows the primes even pay a positive
subsidy. So the arithmetic side is not the enemy on structured families. The difficulty of RH sits
entirely where no scale exists: fixed-aperture receivers, the odd sector, low modes. On that side
APT has a complete unconditional detection theory (every off-line zero is seen by an explicit grid
tent) and positivity only up to aperture about `0.35`.

The critical family cannot tell `ζ` from Beurling systems with off-line zeros. Any proof that runs
through scale-driven positivity plus a size bound `|w| ≤ CΛ` proves false statements. A route to RH
needs an input that is exact in `Λ` and works at bounded aperture without a scale parameter. The
astronomically large thresholds say the same thing quantitatively: the log-gain mechanism is not the
RH mechanism.
