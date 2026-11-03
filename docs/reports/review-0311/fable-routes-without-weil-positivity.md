# Proof routes that survive if Weil positivity is a dead end

Companion to `fable.md` (big picture), `rh-current-frontier-map.md` (route index),
`route-obstacles.md` (classes P1–P4, labels `A*`/`B*`), `walls-ledger.md` (Σ/Π/Γ) and
`route-unification-ledger.md` (classes C1–C20). Evidence tags: `[L]` Lean theorem read in source or
returned by the corpus search; `[D]` derived here from `[L]` statements; `[C]` proposal of this
report; `[N]` numerical. "Unexplored" means the corpus search returned no module for the mechanism
(the modules it did return are named).

---

## 0. The assumption and what it removes

**Assumption.** No argument whose core is the nonnegativity of a Hermitian form equivalent to RH
can close. By the corpus's equivalence theorems this removes, as *mechanisms*:

| Removed | Why it is Weil positivity |
|---|---|
| Windows, stages, lattices, collars (RW, F1, P1; GWZ, CSTW, CWS, WTZ, DZG) | `Q ≥ 0` on windows ⇔ RH `[L]`; lattice margins are Schur complements of `Q` `[L]` |
| Hodge index on the complete family (HF, ACS, EHT, AHD, ADT, HWV, LST, SRT, AIP, ACT, SC-index) | pencil `κQ(H) + (βJ/K)‖H‖²` at the critical curve; index of `Q` `[L]` |
| PM Krein positivity (P3, RN, W1C-Krein, PTR) | `Q(H) = 2 Re[𝓦H, 𝓦H]` exactly `[L]` |
| Prime-blind positivity (P2, PBAP, EWU, OWU) | RH ⇔ `PrimeBlindPositive`; on blind tests the functional is the zero sum `[L/D]` |
| Li, Herglotz (`Re ξ'/ξ > 0`), heat Hankel forms, Gaussian heat Hankel determinants | positivity of forms built from the zero sum `[L]` |
| Index routes as positivity (HKT, AKL, AKG, ACoT-index) | `κ` is the negative index of the same form `[L]`; they survive only in rigidity form (§2) |
| WD's integer (collision charge) | window index = Wiener–Hopf index `[L]` |
| Nyman–Beurling with Möbius coefficients | the natural approximant is the Möbius sum; it is MC (§1) |

What the assumption does **not** remove is the wall: by `walls-ledger.md`, Σ, Π and Γ are one
obstruction, and the two-site band `|c_ψ(t)| < Q(ψ)` is the smoothed prime count at sharp constant
`[L/D]`. So every surviving route meets the same obstruction as an estimate (Π), as a rigidity
statement (Γ), as a real-rootedness statement, or as a density/location statement.

---

## 1. Estimate routes (Π, class P4)

The shape: prove square-root cancellation (or boundedness) of one explicit arithmetic quantity; RH
follows by a classical equivalence. The walls proved in the corpus: Π2 (no unconditional source
at square-root precision), the parity barrier at damping `½` `[L]`, the precision class `𝒬`
(the deciding input must break parity and twist stability) `[L]`, no `ε`-uniform producer (B24),
the trivial gauge point (Γ1), and Π10 (every eventually nonempty cyclotomic band has abscissa
exactly `2Θ`, so no frequency localization lowers the target) `[L]`.

### 1.1 MC — Möbius cancellation
- Criterion: `M(x) = O(x^{1/2+ε})` ⇒ RH; Redheffer `det R_N = M(N)` `[L]`.
- Lean: half-power and Redheffer criteria; gauge exponent Haar-a.e. `½`, Baire-generic `1`;
  Chowla-type successor correlations cancel to the square root almost surely on the gauge torus
  `[L: AGT, ACG]`; Turán–Kubilius variance bounds; pretentious distance and its triangle
  inequality `[L: RHTower/Sieve, PretentiousDistance]`.
- Wall: neither measure nor category reaches the trivial gauge point; the prime source is atypical
  exactly by the pole `[L]`.
- What a proof must do: produce cancellation at `x = 0` of the gauge torus from the pole alone.
- First test: one explicit non-arithmetic gauge point with proved exponent `½` (fable.md §4.3).

### 1.2 WL / CAF — the first cyclotomic band
- Criterion: RH ⇔ the fixed first Chebyshev cyclotomic band has energy `O_ε(N^{1+ε})`; every
  eventually nonempty band has abscissa `2Θ` `[L: riemannHypothesis_iff_chebyshevFirstCyclotomicBand]`.
- Mechanism: the continuous first-mode packet is a multiplicative convolution whose Mellin transform
  factors into the Chebyshev divisor current and a nonvanishing cyclotomic multiplier; its growth
  excludes zeros in the upper sector by a first-order ODE `[L]`.
- Wall: narrowing the band does not remove off-line growth (Π10) `[L]`.
- What a proof must do: bound one explicit `L²` energy of a Chebyshev packet at `N^{1+ε}`.

### 1.3 The two-site band as a prime-sum estimate; ACoT cone coupling
- Identity: `c_ψ(t) = A(ψ)B(ψ)e^{t/2} − Σ_k μ_{−2k}ν_{−2k} e^{−(2k+½)t} − Σ_n Λ(n)n^{−1/2}(ψ⋆ψ)(t − log n)`
  `[L/D: CSTW]`; RH ⇔ `|c_ψ(t)| < Q(ψ)` `[L]`. Read as an estimate: the `ψ⋆ψ`-smoothed Chebyshev
  count on `[e^{t−2r}, e^{t+2r}]` matches `AB e^{t/2}` within a fixed constant at every scale.
- Sharper two-prime form: bounded cone coupling `C(u,v) = K(uv) − K(u) − K(v) + K(1)` on one two-prime
  lattice ⇒ RH or no deepest zero; RH outright on the finite stratum `[L: ACoT]`.
- Wall: the sharp constant is Σ; the coupling is as large as the kernel `[L]`.
- What a proof must do: an exact evaluation of the two-prime coupling, not an estimate with loss.

### 1.4 PBM — regularized prime/log-ζ abscissa
- Criterion: pole-regularized Dirichlet convergence of the prime/log-ζ series for every `σ > ½` ⇔ RH
  `[L]`; killed: `KR-RAW` (regularization alone supplies no cancellation).
- What a proof must do: actual coefficient cancellation down to the critical abscissa.

### 1.5 RB — Robin / Nicolas / Lagarias
- Criterion: Robin's inequality `σ(n) < e^γ n log log n` for `n > 5040` ⇔ RH; colossally abundant
  reduction and growing-prime-core constraints `[L: RobinColossallyAbundantReduction]`.
- Mechanism: the inequality at extremal numbers is the Mertens product
  `∏_{p≤x}(1 − 1/p)^{−1}` against `e^γ log x` at square-root precision `[D]`.
- Wall: the square-root remainder on prime-saturated extremizers; divisibility conditions do not
  exclude counterexamples `[L]`. Elementary in statement, Π in content.

### 1.6 Scheduled explicit-formula functionals (FU, CFC, RP, LI, SZ; class C6)
- Shape: an explicit-formula functional (Abel moment, first-clock sine coefficient, history floor,
  Li balance, Ward defect) bounded below or above ⇔ RH `[L]`.
- Status: exact receivers; sublinear floors impossible; each needs one joint bound paying seed,
  drift, covariance and endpoints `[L]`.
- Caveat: these are lower bounds of explicit-formula functionals, not nonnegativity of test forms;
  they survive the assumption formally, but their content is the same smoothed prime sum.

### 1.7 CHMD — causal prime wave bound
- Status: `(full prime − pole)/√Y` has operator norm `O(exp(−√log Y/9.2·10⁷))` uniformly over detail
  horizons `[L]`; the retained `√Y` scaling does not give the unnormalized error.
- What a proof must do: pay Gamma, the signed potential and infinite-orbit terms in the receiver's
  normalization.

### 1.8 WD — inner caps (flux)
- Criterion: on every Burnol unit window, at every polynomial stage, cancel the right-port flux
  through the inner caps `[½, σ_m]`, `σ_m = 1 − 1/(116 log(m+5))` `[L]`; polynomial stage ⇔ RH.
- Lean: six-way zero-free window rigidity; unconditional sub-`e^{t/2}/(t+1)` right-half-port decay
  on every Burnol window `[L]`.
- Mechanism: contour/flux identities for the logarithmic derivative; non-spectral, non-positivity.
- Wall: an independent zero-rate right-port bound through the caps (Π23).

### 1.9 Hardy–Littlewood / Riesz series
- Criterion: `H(x) = Σ_{k≥1} (−x)^k/(k! ζ(2k+1)) = O(x^{−1/4+ε})` ⇔ RH; exponent exactly `(Θ−1)/2`
  `[L: HardyLittlewoodExponentLaw]`.
- Content: Abel summation of `μ(n) n^{−1} e^{−x/n²}`; it is MC in an entire-function disguise `[D]`.

### 1.10 Nyman–Beurling / Báez-Duarte (CTF)
- Criterion: the Möbius approximation error tends to zero ⇔ RH; exact completion, optimizer and
  residual-square identities `[L]`; the terminal edge cannot be discarded `[L]`.
- Content: Hilbert-space approximation; with the natural coefficients it is MC.

### 1.11 Franel–Landau Farey discrepancy
- Criterion: with `δ_ν = f_ν − ν/L` over the Farey fractions of order `n`, RH ⇔ `Σ_ν δ_ν² = O(n^{−1+δ})`
  for every `δ > 0` `[L: FareyDiscrepancyFranelSquareLaw]`.
- Content: the Farey sawtooth is a Möbius sum (`Σ_ν e(f_ν) = M(n)`), so it is MC on `SL₂(ℤ)`-orbits;
  its value is to connect MC to the top coprime stratum (§7.5).

### 1.12 Density ladder as input (Guth–Maynard, Vinogradov–Korobov)
- Lean: Guth–Maynard Theorem 1.1 (large values `R ⪅ N²V⁻² + N^{18/5}V⁻⁴ + TN^{12/5}V⁻⁴`) with its
  corollaries (short intervals `θ > 2/15`, pointwise zero density) `[L]`; the Vinogradov–Korobov
  region `β > 1 − (log γ)^{−2/3}(log log γ)^{−5/3}/10⁷` `[L]`.
- Role: these never reach RH (density is not absence); they are inputs to §4 and §7.6.

---

## 2. Rigidity routes (Γ)

The shape: derive a contradiction from an off-line quartet by the analytic/algebraic structure of
the Euler product and the functional equation, without producing a sign. Walls: Γ15 (positive
multiplicative twins with FE, Euler product, Ramanujan bounds and zeros at any `Re s ∈ (½,1)` violate
only the strict Euler bound `θ < ½`) `[L]`; Γ16 (no selector gives positivity) `[L]`; Γ35 (FE with
positivity ⇒ counting measure of `ℕ`; FE + Euler product is the minimal input) `[L]`.

### 2.1 SEL — Selberg-class rigidity
- Lean: degree gap `(0,1)` empty; degree `< 1` is the Dirichlet unit; strong multiplicity one at the
  critical Euler abscissa for arbitrary Gamma presentations; finite-prime and finite-support
  rigidity; degree one: conductor `≥ 2m₀` or a pole at `1` `[L]`.
- What a proof must do: show a degree-one full Selberg function with an off-line zero contradicts an
  identity available only under the strict Euler bound (the twins show nothing weaker works).

### 2.2 APD / Beurling — functional-equation rigidity
- Lean: a positive measure with Riemann's functional equation is the counting measure of `ℕ`; a
  discrete Beurling system with it is the rational primes; continuous Beurling systems with
  integers more regular than `ℕ` admit zeros at any `Re s ∈ (½, 2/3)` `[L]`.
- Role: fixes the minimal input; no mechanism for the sign.

### 2.3 Pre-divisor forcing (APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF; class C10)
- Shape: a section defined before the divisor forces the zeros (Γ5); each candidate has its exact
  receiver and lacks zero-independent forcing `[L]`.

### 2.4 Band holomorphy of `Λ(s)/Λ(s+1)` (B31) and ART
- RH-equivalent analytic structure of a quotient; ART: no realization of `ζ` by dynamics except
  commutative `[L]`.

### 2.5 Krein–Langer index: the zero–one law `κ ∈ {0, ∞}` (B11)
- Lean: finite index ⇔ finitely many off-line zeros ⇔ all zeros above `T₀` on the line ⇔ bounded
  nonreal count; finite index ⇒ Lindelöf; every perturbation of `Λ` has infinite index; integer
  successor + continuous dilation ⇒ infinite index `[L]`.
- What a proof must do: show that finitely many exceptional characters of the orbit kernel are
  impossible unless there are none. Beurling shows positivity plus regular integers cannot do it;
  multiplicativity in `ℕ` must enter.
- Note: this uses the index of Weil's form as an invariant, not its positivity; it is the only
  index-theoretic survivor.

### 2.6 Hypertranscendence / differential algebra
- Lean: `ζ` and `ξ` are hypertranscendental unconditionally; the old `XiFrequencyCollapse`
  interface is a reformulation of hypertranscendence, not an independent RH input `[L]`.
- Status: no RH criterion of differential-algebraic type is known; closed as an input.

---

## 3. Real-rootedness and total positivity

Not quadratic-form positivity, so it survives the assumption as stated; it is positivity of a
different kind (Laguerre–Pólya, Pólya frequency, Lee–Yang).

### 3.1 de Bruijn–Newman / Laguerre–Pólya (Heat, LA, HCF, PA, GTA)
- Lean: RH ⇔ every local Newman constant is `0`; RH ⇔ the Laguerre inequality
  `(f')² − f f'' > 0` for `H_t` at every `t > 0`; RH ⇔ every cosine shift of `ξ` is Laguerre–Pólya;
  non-real zeros at every negative heat time (`Λ ≥ 0`); finitely many non-real zeros at positive
  time; deep off-line zeros are counted by the heat flow `[L: RHTower/Heat, DeBruijn*]`.
- Walls: B12 (approximation by RH-true objects lands in LP); `KR-CAL` (negative-time collisions do
  not refute RH; uniform control as `t ↓ 0` is needed); depth-only heat budgets fail `[L]`.
- What a proof must do: show `Λ ≤ 0`, i.e. no collision for `t > 0` as `t ↓ 0`, by the zero dynamics
  (the Rodgers–Tao mechanism runs the other way and uses RH freely inside its contradiction).

### 3.2 TH — theta Hankel sections
- Lean: signed centre-mixed Hankel sections strict through rank 8; odd fibre strictly positive beyond
  `log(6/π)` `[L: ThetaCuspSections]`; all ranks ⇔ RH.
- Wall: B12; positive tail alone does not pay the full integral `[L]`.

### 3.3 Lee–Yang / Ising (W1C, RiemannSiegelLeeYangChain, ZetaZerosLeeYangQuasicrystal)
- Lean: Riemann–Siegel sums are domain-wall expansions of a ferromagnetic chain whose partition
  function has real zeros for fields in the unit disc `[L]`; the zeros form a Lee–Yang quasicrystal
  structure `[L]`.
- What a proof must do: source-defined Ising couplings with centred slow-field convergence `[L]`.

---

## 4. Density and zero-location routes

Sub-RH by nature; they reach RH only through a zero–one law (§2.5) or an exact cap identity (§1.8).

- WD density branch: `D_win ⇔` thin Planck shadows; `D_zero ⇔ D_win +` vanishing cluster tails;
  eight-way equivalence of critical-line log-mean, mollifiers, off-line moments, 100% clustering,
  Hecke defects; almost-all Bessel–Szegő certificates at the double-log stage `[L]`.
- Backlund converses: off-line sparse ⇔ Lindelöf open ⇔ Lindelöf on the line; zeros approaching the
  line ⇒ Lindelöf `[L]`.
- Speiser counts: between unshadowed heights `ζ` and `ζ'` have equally many zeros left of the line;
  the left deficit is at most `((1 − HD1)/2 + ε)N(T)`, `HD1 = 0.6725…` `[L]`.

---

## 5. Geometric function theory

- Speiser: RH ⇔ `ζ' ≠ 0` on `0 < Re s < ½` `[L: exact counts, sign laws, local disks]`. A proof must
  exclude left zeros of `ζ'` by an argument on `Re ζ'/ζ` on rectangles; the sign law
  `2 Re ζ'/ζ = Re χ'/χ < 0` on the line is in Lean.
- XN — Newton invariant discs: line-centred Newton self-map discs covering all zeros ⇒ RH; the
  interior margin has nonnegative Laplacian; boundary sign does not pay curvature `[L]`.
- Nevanlinna / Tsuji characteristic: second-main-theorem chain and Poisson–Jensen bounds exist
  `[L: HTGeometry]`; the value `0` is totally deficient in the right half-plane under RH `[D]`; no
  criterion yet.
- Balazard–Saias–Yor / Volchkov: RH ⇔ `∫ log|ζ(½+it)| dt/(¼+t²) = 0`; the integral equals the
  positive sum `2π Σ_{right} log|ρ/(1−ρ)|` `[L]`; the critical-line log-mean `(L)` is one of CDG's
  eight forms `[L]`. A proof must evaluate a log-integral of `|ζ|` on the line exactly.

---

## 6. Recurrence and universality

- BAG — Bagchi: RH ⇔ `ζ` is strongly recurrent on every closed disc of the strip ⇔ head-target
  uniform density `[L]`. Wall: returns including possible target zeros; zero-free-target
  universality leaves exactly those targets `[L]`.

---

## 7. Alternatives not yet explored

Each was checked with the corpus search; the modules it returned are named. All are `[C]`.

### 7.1 Combinatorial topology of the divisibility nerve (discrete Morse theory)
- Fact: the nerve Euler characteristic of the divisibility–successor complex of `[1,N]` is `M(N)`
  `[L: HWV]`; `det R_N = M(N)` `[L: ADT]`.
- Mechanism: a Morse matching on the complex with few critical cells bounds `|χ| ≤ #critical`;
  RH would follow from `N^{1/2+ε}` critical cells. The complex has exponentially many faces, so the
  matching must be structural (prime towers as collapsible stars, gcd strata as the only critical
  loci).
- Corpus: no module (search returned `discreteEulerChar` of AOT and `FareyCountMertensIdentity`).
- Risk: Hodge/count mechanisms are closed as *sign* producers `[L]`; this is not a sign but a
  cancellation count, so the closure does not apply directly. Collapsibility of divisor complexes is
  known for single intervals `(1,n)` (Hall), not for the whole nerve.

### 7.2 Combinatorial evaluation of the Redheffer determinant
- Mechanism: a sign-reversing involution (Gessel–Viennot, Lindström) on the chains/matchings
  counted by `det R_N`, leaving `N^{1/2+ε}` fixed points.
- Corpus: `det_redhefferMatrix` only; no involution or path-count module.
- Wall: the fixed points are the squarefree-support defects; counting them at square-root precision
  is MC again unless the involution is scale-adapted (dyadic blocks). This is an algebraic shape for
  Π, not a new input.

### 7.3 Self-repulsion of an off-line quartet (Deuring–Heilbronn for `ζ` alone)
- Mechanism: the de la Vallée Poussin argument is repulsion of a hypothetical zero by the pole; its
  limit is `c/log t`. Replace the pole by the on-line zero sequence itself: a quartet at
  `β + iγ`, `β > ½`, must coexist with the zeros near height `γ` whose statistics are known
  unconditionally (density, Montgomery–Taylor proportion, Speiser counts `[L]`). Turán power sums
  `[L: PowerSumTuranLowerBound]` give lower bounds for `Σ_ρ (s − ρ)^{−ν}` from one exceptional term.
- Corpus: `riemannHypothesis_or_polynomial_boundary_repulsion` (ACoT cone boundary) and Diophantine
  prime repulsion only; no zero–zero repulsion module.
- Wall: known repulsion results are between different L-functions (exceptional zeros); for one
  function the quartet is consistent with every proved statistic. The survivor would be a
  quantitative "exceptional-zero repulsion" for `ζ`: an off-line zero of depth `δ` forces a zero-free
  region of width `≫ δ` around it on the line, contradicting `N(T)` locally.

### 7.4 Fourier interpolation bases with zeta nodes; exponential systems
- Mechanism: the explicit formula is one relation of an interpolation basis whose nodes are the
  zero ordinates and the points `±log n` (Bondarenko–Radchenko–Seip type). Completeness and
  uniqueness properties of the exponential system `{e^{iγ_ρ x}}` (Beurling–Malliavin, Kadec) depend
  on the nodes being real. A uniqueness theorem for functions analytic in a strip with nodes at the
  zeros, derived from the Dirichlet-series kernel, might force the nodes real.
- Corpus: `XiSchwartzSpectralMeasure`, `BlindIntegerFareyMoebius`, exponential-polynomial uniqueness
  from finite zero sets; no interpolation-basis or Beurling–Malliavin module.
- Wall: the blind cone of P2 is this uniqueness question in Weil-form clothing (tests whose
  autocorrelations vanish at `±log n`); positivity enters through weights. Without positivity the
  question is whether the interpolation kernel has a zero-free property on the strip, which is Γ.

### 7.5 Sum–product estimates for the successor–divisor coupling
- Fact: every successor pair `(n, n+1)` lies in the top coprime stratum, the open core B9 `[L: HWV]`;
  coprime pairs are the `SL₂(ℤ)`-orbit of `(1,0)`; the Farey discrepancy is `M(n)` `[L]`.
- Mechanism: estimate (not polarize) the coupling of coprime atoms at ratio `|log(m/n)| ≲ 1/c` by
  multiplicative-energy / sum–product inequalities (Elekes–Szabó type bounds for the equation
  `ab − cd = 1`, Kloosterman structure).
- Corpus: `additiveEnergy` inside Guth–Maynard only; Kloosterman modules exist (Weil bound,
  Estermann twists); no sum–product module.
- Wall: sum–product saves a power, never a constant; the critical curve needs the exact constant
  `κ₀` `[L: HWV]`. It can at most improve the exponent `1/8`.

### 7.6 Statistics of `log|ζ|` as input to the log-mean criterion
- Fact: `(L)` (critical-line log-mean `→ 0`) ⇔ 100% clustering ⇔ six other forms `[L: CDG]`;
  BSY: the weighted log-integral is exactly the right-zero sum `[L]`.
- Mechanism: Selberg's central limit theorem and its rate (unconditional) control the distribution
  of `log|ζ(½+it)|`; its mean is tied to `Σ(β − ½)` by Littlewood's lemma. A proof of `(L)` from the
  CLT with a rate would close the density branch; the BSY equality needs the mean exactly.
- Corpus: Jensen inequalities, weighted second moments, Littlewood edge budgets `[L]`; no central
  limit theorem module.

### 7.7 Symmetric Riemann–Siegel approximants with on-line zeros
- Mechanism: for `F(s) = A(s) + χ(s)A(1−s)` with `A` a Dirichlet polynomial, zeros off the line
  require `|A(s)| = |χ(s)A(1−s)|`; Spira-type results put the zeros of the symmetric approximant on
  the line. RH would follow from a lower bound `||A(s)| − |χ(s)A(1−s)|| > |R(s)|` off the line, `R`
  the Riemann–Siegel remainder.
- Corpus: `RiemannSiegelLeeYangChain` (domain-wall expansion), `RiemannSiegelThresholdLaw`,
  `ZetaNotchCriticalAFE`; no approximant-zero module.
- Wall: near the approximant's own zeros the lower bound vanishes; the mechanism is Rouché without
  a floor. Survivor: the structure of zeros of symmetric Dirichlet polynomials (a Lee–Yang
  phenomenon, §3.3).

### 7.8 Horocycle equidistribution (Zagier–Sarnak)
- Criterion: RH ⇔ long closed horocycles on `SL₂(ℤ)\H` equidistribute with error `O(y^{3/4−ε})`.
- Corpus: Maass/Deck/Whittaker modules, `MaassDyadicHorocycleReturn`, `ThetaPowerHorocycleMass`;
  the equidistribution-rate criterion is not present as a route.
- Wall: every known rate comes from the spectral expansion (Eisenstein constant term); a
  non-spectral rate (Ratner-type) has no error term. Dynamical restatement of Π.

### 7.9 Crystalline measures (Meyer, Kurasov–Sarnak)
- Fact: under RH, Guinand's distribution `Σ_ρ δ_{γ_ρ}` (with trivial terms) has Fourier transform
  supported on `±log n`: a crystalline measure. Kurasov–Sarnak classify one-dimensional Fourier
  quasicrystals by Lee–Yang varieties.
- Corpus: `ZetaZerosLeeYangQuasicrystal` (one module); `guinand` appears throughout as the explicit
  formula; no classification module.
- Mechanism: classify tempered distributions with support in a strip and spectrum in
  `±log(ℕ_{≥2}) ∪ {0}`; if the classification forces the support real, RH follows. This is Γ in the
  language of quasicrystals; the Lee–Yang input is §3.3.

### 7.10 Pretentious theory at square-root scale
- Fact: the pretentious distance, its triangle inequality and reflection law are in Lean
  `[L: PretentiousDistance, mulDistSqPair]`; Halász-type mean-square bounds exist `[L]`.
- Mechanism: Halász's theorem gives `o(x)` savings from the distance to `n^{it}`; a proof would need
  the distance calculus to reach `x^{−1/2}`. No such extension exists; the route is MC with a
  different bookkeeping.

---

## 8. Assessment

1. The survivors with exact structure in Lean are: the two-site band as a prime-sum identity and
   the ACoT cone coupling (§1.3), Selberg-class rigidity with the strict Euler bound (§2.1), the
   index zero–one law (§2.5), the heat-flow real-rootedness family (§3.1), WD's inner caps (§1.8)
   and the BSY/log-mean identities (§5).
2. Of the unexplored alternatives, three have a definable first theorem: discrete Morse theory on
   the divisibility nerve (§7.1: find a matching whose critical cells are exactly the gcd strata),
   quartet self-repulsion (§7.3: an exceptional-zero repulsion law for `ζ` alone), and interpolation
   uniqueness (§7.4: a strip-uniqueness theorem for the explicit-formula kernel). Each is a
   cancellation or rigidity statement, not a sign.
3. None of the survivors avoids the wall; each meets it as Π or Γ. The assumption reselects routes
   and changes the toolset, not the obstruction.
