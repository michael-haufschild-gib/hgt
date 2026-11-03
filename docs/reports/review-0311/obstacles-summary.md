# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route; labels `A*`, `B*`, `S*`), `walls-ledger.md` (labels
Σ/Π/Γ) and `route-unification-ledger.md` (classes C1–C20). Corpus: `8ecae707ac` with the working
tree. Evidence: `[L]` Lean, committed and in its umbrella; `[U]` committed, not in an umbrella;
`[W]` working tree or work in progress; `[D]` derived here from Lean statements; `[M]` exact model
statement; `[N]` numerical. Window tests of length `A` live on `[−A, 0]`; `c_φ(t) = W(φ(· − t), φ)`.

## 1. The big picture

### 1.1 RH is decided on two sites
For every nonzero bump `φ` and `t ≠ 0`, RH ⇔ `|c_φ(t)| < Q(φ)` ⇔ every two-site lattice window
`[[Q(φ), c_φ(t)], [c_φ(t), Q(φ)]]` is positive definite [U: GWZ `RHIsDecidedOnTwoSites`]. Off RH a
short spectrally generic bump `ψ` (support in `[−1/5, 0]`) has
`|c_ψ(s)| = Q(ψ)` at some step `s` [L: GWZ `ForbiddingLatticeZeroModesIsRH`]. One generic bump
already decides, and eventual boundedness of its orbit correlation decides; its exponential growth
rate is the zero width [L: AOG]. A first failure of Spec ℤ is a two-site window with zero mode
`(1, ∓1)`, no interior and one angle `±1`.

### 1.2 The two-site entry is the windowed prime number theorem
For ordered tests the archimedean coupling is the trivial divisor of `ζ`:
`2cosh(x/2) − ω(x) = e^{x/2} − Σ_{k≥1}e^{−(2k+½)x}` [L: CSTW]. Hence [D]
`c_ψ(t) = μ₁(ψ)ν₁(τ_tψ) − Σ_k μ_{−2k}(ψ)ν_{−2k}(τ_tψ) − Σ_n Λ(n)n^{−1/2}(ψ⋆ψ)(t − log n)`:
a pole moment growing like `e^{t/2}`, trivial-zero moments decaying like `e^{−(2k+½)t}`, and the
`ψ⋆ψ`-smoothed prime sum over the multiplicative window `[e^{t−2r}, e^{t+2r}]`. The free evolution
leaves every band [L]; each prime power is necessary [L]; only `Λ` stays positive [L]. RH is the
statement that the smoothed prime count in every short multiplicative window matches its main term
to within the Weil energy `Q(ψ)` of the bump, at square-root normalization, at every scale. The sign
wall Σ on two sites is the precision wall Π at one point.

### 1.3 The canonical system of the tower is Szegő–Levinson theory with arithmetic kicks
Weil sequences `κ(d) = c_φ(dh)` are Toeplitz data [L]. Positivity ⇔ Schur parameters in `(−1,1)`;
margins `E_n = Q(φ)∏(1 − γ_k²)`; the newest datum `κ(n+1)` enters the Schur parameter linearly with
coefficient one, the frozen prediction reads `κ(0..n)` only; changing the weight of one prime power
moves exactly one Schur parameter by `−δλ(n₀)n₀^{−1/2}k_{m+1}(log n₀)` [L]. Positive windows have outer
predictors; degenerate windows are finite curves (Carathéodory–Fejér) and a curve with `|S|`
conjugation-closed angles fails exactly at index `|S|` [L]. Under RH Spec ℤ is on every lattice the
curve with the infinitely many angles `e^{iγ_ρh}`, its spectral measure is purely atomic, `Σγ_k² = ∞`
and the margins tend to `0` (Szegő's singular case) [L]; the first margin is born at order `h²` with
coefficient `Σm_ργ_ρ²|φ̂(γ_ρ)|²` [L]; there is no unnormalized continuum limit [L].

### 1.4 The stage step lives on two collars; the kick is a collar Rosati pairing
At level `N+1` the window splits into collars and an interior; interior tests do not change the kick;
`Q ≥ 0` on `W_A` ⇔ `2wc_H(ℓ) ≤ S^N_A(H) = inf_{interior} Q_N(H + h)`; `S^N_A` is born zero at `A = ℓ`
and grows with the collar width [L]. The kick is `c_H(ℓ) = ∫_L H·(σ_AH)∘R`: a positive source exactly
on `σ_A`-even, collar-antisymmetric and on `σ_A`-odd, collar-symmetric data; frozen-negative even
(odd) tests of a nonnegative window are collar-antisymmetric (symmetric) dominant [L]. The frozen
two-collar form is explicit: the interior receives each collar only through its trivial-divisor
moments and its transports by the earlier folds; at the first stage the complement is
`Q(x_L) + Q(x_R) + Φ_ε(moments)` [L]. Window growth is a translation contraction and each stage a
Carathéodory disk [L]. The interior-gap unique-continuation principle is not structural (three-angle
curve) [L], and it is not needed (1.1).

### 1.5 The complete family: subcritical solved; at the critical curve Weil's form sits at a pole
`completeWeilMatrix tiltedUnitSpline c N ≻ 0` for every `α < 1/8`, `1 ≤ c ≤ (log N)^α` [L]. At the
critical curve every twisted direction is a positive count (Ramanujan, periodic, trigonometric,
character) [L]; the frequency counts `F(u) ∝ ζ(β+1,u) + ζ(β+1,1−u)` have a pole of order `β+1` at
`u = 0` whose finite part is the untwisted count, and Weil's form `κQ(H)` stands at the pole [L]. A
size-only, aperture-independent floor `Q ≥ −C(p)∫e^{−pu}H²` (`p > 1`) makes one small critical
multiple pay every window of every fixed family [L]; it carries no information on Weil's sign. On the
exact clock the critical boundary adds its null directions to the negative side [L]. The conductor
decomposition is uniform on a growing range, the count form ends at the resolution `m ≍ c`, and the
scaled counts remain positive quasimodes through `N^θ`, `θ < ½` [L]. The bulk is blind below the grid
`λN` [L]; at fixed overlap every bulk entry is read by `γ, γ₁` and `L'/L(1,χ)` [L].

### 1.6 Reflection: PM is the zero side; Hecke is translation; the window has no Frobenius
`Q(H) = 2Re[𝓦_AH, 𝓦_AH]` exactly, `𝓦_A` the bounded map to `ℓ²(upper Mayer resonances)` with
reflection `s ↦ ½ − s̄` (`ρ ↦ 1 − ρ̄`) [L]. `T_p − Id` is the Mellin translation `√pH(· + log p)` for
every prime, multiplier `p^{1−2s}`, Krein similitude factor `p` [L] — the translation invariance of
Weil's form. The window involution is the conjugate-linear, `e^{−A(2s−½)}`-twisted Krein reflection
[L]. Same-window similitudes are scalars [L]. Every structure PM carries is identified; PM supplies no
positivity of its own.

### 1.7 Selection and precision
Selection after positivity is automatic (Weil cone `{Λ}`; lattice selection of `Λ`) [L]. Selberg-class
rigidity: Euler-log discrepancy absolutely convergent on `σ = ½` forces equality without Gamma matching;
positive finite Euler twins with zeros at any `Re s ∈ (½,1)` violate only the strict Euler bound;
degree-zero functions are the Dirichlet unit; no degree in `(0,1)` [W] [L]. Near-line density is one
statement in eight forms; `D_win` ⇔ thin Planck shadows; `D_zero` ⇔ `D_win` + vanishing giant-cluster
tails; the double-log stage is unconditional [L]. One cyclotomic mode carries `2Θ` [L].

### 1.8 Dimension zero is classified
Weil's form is the 1-jet at `k = 0` of the Tate family; bare domination ⇔ `Q ≥ 0`; no archimedean
family dominates uniformly; positive dimension supplies no positivity [L].

### 1.9 The three walls as one statement
| Wall | Form |
|---|---|
| Σ sign | the two-site band `|c_ψ(t)| < Q(ψ)` at every step; in tower form, every prime kick lands in its prediction interval |
| Π precision | the same band read as the `ψ⋆ψ`-smoothed prime count in `[e^{t−2r}, e^{t+2r}]` at square-root precision with constant `Q(ψ)` |
| Γ selection / reflection | positivity of the reflection `ρ ↦ 1 − ρ̄` on zero coordinates; selection automatic after positivity |

All three are the Hodge index for the pair (bump, its translate by `t`): Weil's `𝔽_q` argument applied
to the diagonal and the graph of Frobenius at scale `t` [D].

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Explicit constants and horizons (eighth-root theorem, `1/9`, logarithmic profile, Beurling schedule, horizon criterion) | HF, SRT, AIP, ACS, SC | effectivization |
| A2 | General profiles past `θ = 1/1080` and the super-log-log clocks | HF, SRT, SC | tilted-spline template |
| A3 | Joint twist families; equal-parity character coupling; different moduli; moving/coalescing frequencies at fixed `K` | HF, SRT, AHD | single-family proofs are templates |
| A5 | Certified first prime stage `[0.7243, log 3)`; second-stage certificates | RW, OWU, EWU, GWZ, CWS | finite computation |
| A6 | Odd unit window: one first-moment Schur inequality for the exact logarithmic reflection operator | OWU, RW, WTZ | rank-one problem on a fixed window; all other charges paid |
| A7 | Rational Hecke graphs and Tate horizons of stages 3, 4, 5, 7, … | WTZ, CWS | finite graphs |
| A8 | Closed-form first-stage two-collar complement `Φ_ε` of the trivial-divisor moments | GWZ, CSTW, WTZ, RW | explicit archimedean Schur complement; dependence proved |
| A9 | Window index as a counting function of the length | AHD, SRT, CWS | conditional calculus |
| A10 | Function-field calibration (twisted curves, higher-genus fakes, `𝔽₃` elliptic chain) | AHD, ACS, SC, HF | the sign is known there |
| A11 | Integrate unfinished modules: CACT far reserve [U] and log-free residuals [W]; GWZ two-site module [U]; SEL degree gap [W]; LI, SZ, HKT, AKLT, ALG, AGT, ACP | HF, AIP, GWZ, ACS, LI, SZ, SC, MC | statements in place |
| A12 | Prime-side identity for the Gaussian-damped two-prime coupling | SC, ACS | heat-smoothed explicit formula |
| A13 | PM classical identifications (Selberg-zeta normalization, Lax–Phillips, Lewis–Zagier separation, `+1` Mayer eigenspace, Garland) | PM, W1C | known theories |
| A14 | Operator-native nonvanishing on `Re w = 1` | PM | Eisenstein template |
| A16 | Theta Hankel rank-8 strictness; ranks 9–10 | TH | finite computation |
| A17 | Hausdorff shifts, Jensen horizons, two-grid degrees, Toeplitz minors beyond PF₃₇ | PA, LA, HCF | effectivization |
| A18 | Nine atom-dominated collar moduli | ACT | finite case analysis |
| A19 | Mixed Schur debit; first-prime/coarse/polar costs on fixed cells | AIP, CHMD | fixed-dimensional estimates |
| A20 | Logarithmic two-point Chowla | MC | Tao's theorem |
| A21 | Björner wedge decomposition | MC, HF | classical topology |
| A22 | Depth law, star horizons, gcd-strata tables | HF, ACS | effectivization |
| A23 | Census: `S_cos(λ)`, odd stabilizer transport, `β = 2` | census, ACS | classical pair estimates |
| A24 | Voronoi summation; Zwegers' indefinite theta | ACS, HF | classical |
| A25 | Künneth primitive `h¹` at small degree; mixed jets; main-term producer | ACS, WL | calibration |
| A26 | WD composition (stopping prefix, flow threshold, density one ⇒ Lindelöf) | WD, LA, TG | composition |
| A27 | Explicit cluster-detector constant `A₀` | SRT, WD | constants |
| A28 | Finite-level Weil cones `C_A` and widths | PBAP, ACS, RW | finite convex programs, duality in place |
| A29 | Atomic-lattice bound `λ_max ≤ ½log N` with Mertens error | WTZ, HF | classical |
| A30 | Full-space positivity of the complete matrix at one small critical multiple | HF, AIP, SRT, CACT | assembly: far reserve on `(V₁)^⊥` [U], prefix cost, conductor-one block of bounded radius, Schur payment |
| A31 | Quantitative conductor range `M(N) = o(c_N)`; scaled-count quasimodes past the resolution | HF, SRT, AHD | uniform versions of proved limits |
| A32 | Infinite-packet PM identity: Krein form of every window image = renormalized mean cusp energy | PM, W1C | finite-packet identity proved [L] |
| A33 | Formal bridge: two-site entry = ordered coupling = smoothed prime-error receiver | WL, JAS, CTF, PBM, RB, GWZ | composition of proved identities |
| A34 | Two-site band on a bounded step range from zero data plus explicit tails | GWZ, WL, RW | finite verification |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on windows of every length (≡ two-site band ≡ lattice Schur parameters in `(−1,1)` ≡ translation contraction ≡ fold capacity ≡ horizon criterion ≡ Beurling schedule ≡ `ι(A) = 0` ∀A ≡ Krein positivity of zero coordinates ≡ PBAP ≡ canonical domination) | RH; fixed length sub | all sign routes |
| B42 | The two-site band `|c_ψ(t)| < Q(ψ)` for short bumps at every step (minimal form of B1) | RH | all |
| B2 | Kick admission at every prime-power stage (`2wc_H(ℓ) ≤ S^N_A(H)`; lattice `|β_n| < E_n`) | RH as induction; each stage sub | RW, GWZ, CSTW, WTZ, HF |
| B3 | Window criticality: positive ground state at every length, passing stages by collar corrections | RH; fixed length sub | GWZ, WTZ, RW, CHMD, TT, OWU, ACT, HF |
| B4 | Uniform positivity of the whole twisted sector at every critical multiple | sub | HF, SRT, AIP, AHD |
| B6 | Full-space positivity of general profiles past `log log N` | sub | HF, SRT, AIP, SC |
| B7 | Exact SOS on one two-prime lattice | RH | HF, SC, ACS |
| B8 | No zero mode at any length (HL on the positive locus) | RH | HF, TG, SC, EHT, GWZ |
| B9 | Top coprime stratum | RH | HF, ACS, ADT |
| B10 | Index ceiling uniform in resolution | ≥qRH; RH (tensor) | CHMD, SRT, WD, SC |
| B11 | Zero–one law `κ ∈ {0, ∞}` | sub | SC, HF, ACS, CWS, SRT |
| B12 | Laguerre–Pólya (all ranks / degrees) | RH | TH, LA, HCF, PA, GTA |
| B13 | Scheduled prime energies | RH | FU, CFC, RP, SZ, LI, FEL, EGC |
| B14 | Growth exponent of window negativity | ≥qRH (`< ½`); RH (`0`) | window routes, WD |
| B15 | Cross-tower gap through the archimedean channel | method | HF, AIP |
| B43 | Height–length (contact) law: RH to height `T` ⇒ windows of length `≤ c log T` positive | sub | all window routes, PM, SRT |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B16 | Inner caps `[½, σ_m]` at every polynomial stage | RH; fixed degree ≥qRH | WD, TG |
| B17 | `100%` critical-scale clustering ≡ log-mean `o(1)` ≡ Hecke `o(log U)` ≡ horizontal moment `o(T)` | sub | WD, census, MC, HEF |
| B18 | `D_win` ≡ thin Planck shadows; `D_zero` ≡ `D_win` + vanishing giant-cluster tails | sub | WD, census |
| B19 | Hecke defect pointwise / dyadic-uniform | ≥qRH / RH | WD |
| B20 | Distributional input beyond counts and moments | method | WD, HEF |
| B21 | Count-valued primitive `h¹` as an inequality; rank-2 form on spans `{ψ, τ_tψ}` | RH; fixed length sub | ACS, HF, CWS, IRK |
| B22 | Genus upper law `≤ (2+η)e^A` | indep. | ACS |
| B23 | Logarithmic Serre duality, primitive part | sub | ACS, HF |
| B24 | `ε`-uniform producer; square-root source input; Redheffer determinant | sub / RH | WL, MC, PBM, RB, JAS, CTF |
| B25 | First cyclotomic mode at square-root precision | RH (power saving ≥qRH) | MC, WL, CAF |
| B26 | Signed pair information beyond bandwidth one | sub | census, ACS |
| B27 | First Epstein real zero on the boost line | sub | ACS |
| B28 | Bounded damped cone coupling from the prime side; unattained width | RH | SC, ACS |
| B29 | Finite-sieve Hodge positivity → global | RH | SC |

### Γ — selection and reflection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B30 | Rosati positivity of the window reflection (the kick is the collar Rosati pairing) | RH | HF, ACS, CWS, GWZ, PM |
| B31 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH | HF, ACS, SC, PM |
| B32 | Selection at the trivial gauge point | RH | MC, BAG, XN |
| B33 | FE twins inside the full class with off-line zeros (none known, none excluded); unimodular gauges | sub | HF, ACS, SC, SEL |
| B34 | Krein positivity of the zero coordinates of window images (≡ finite cusp energy ⇒ zero defect) | RH; gap ≥qRH | PM, W1C |
| B35 | A statistic of resonant states selecting the decay rate | method | PM |
| B38 | Pre-divisor forcing | RH | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |
| B39 | Source-faithful realization: a tower of unbounded rank | RH | RN, PTR, W1C, PM |
| B40 | Prime-blind positivity on signed blind combinations | RH | PBAP |

### Settled questions (classified; not obstacles)
| Question | Answer | Anchor |
|---|---|---|
| Does the interior of a window carry the decisive failure? | No: RH is decided on two sites; a first failure is a two-site window with one angle `±1` | GWZ [U]/[L] |
| Is unique continuation across interior gaps structural? | No: the three-angle curve has a first critical zero mode `(1,0,0,−1)`; continuation from an end collar is structural | GWZ [L] |
| What is the two-collar recursion? | Levinson's recursion on lattices; the translation-contraction / Carathéodory-disk law in the continuum; the continuum limit is a jet system | GWZ, CSTW [L] |
| What does the archimedean place transmit across a prime-free separation? | Only the moments at the trivial divisor: the pole `s = 1` with sign `+`, the trivial zeros `s = −2k` with sign `−` | CSTW [L] |
| Is no-slack a structural accident? | No: under RH every lattice spectral measure is purely atomic (Szegő singular, `Σγ² = ∞`) | GWZ [L] |
| What does a first failure look like? | A finite curve (Carathéodory–Fejér); a curve fails at its number of angles | GWZ [L] |
| Is the complete family positive on every window at one fixed critical multiple? | Yes for every fixed family, by a size-only weighted floor; no information on Weil's sign | WTZ, AHD [L] |
| What weight does Weil's form carry at the trivial angle? | It sits at the pole of the frequency counts; the untwisted count is the finite part | AHD [L] |
| Is there an exact (not limit) PM identification of Weil energy? | Yes: `Q = 2Re[𝓦H, 𝓦H]` on `ℓ²(resonances)`; Hecke = translation; reflection = window involution | RIT [L] |
| Does positive dimension supply positivity? | No | ATD, DZG [L] |
| Does the window algebra contain a Frobenius? | No; Frobenius at scale `t` is translation by `t` | DZG, RIT [L] |
| Can the frozen form pay the new fold as a cost? | No (`Q₁ < 0 < Q` at the first prime) | WTZ [L] |
| Is the monodromy rate of a curve related to its zeros? | It equals the zero width, in both signs | AHD [L] |
| Do Euler-log discrepancies at `σ = ½` determine a full Selberg function? | Yes, without Gamma matching | SEL [L] |
| Do a positive prime measure and regular integers decide the zeros? | No: continuous Beurling systems with `N(x) − ρx − C → 0` (more regular than `ℕ`) have a zero at any `Re s ∈ (½, 2/3)` | RHTower `BeurlingOverRegularIntegersOffLineZeros`, `BeurlingRegularIntegersOffLineZeros` [L] |
| What do the functional equation and positivity determine? | `ζ`: a positive measure with Riemann's functional equation is the counting measure of `ℕ`; a discrete Beurling system with it is the rational primes | APD `PositiveMeasureHamburgerRigidity`, `BeurlingRiemannFunctionalEquationRigidity` [L] |

## 2.3 Frankenstein routes

**Verdict: no assembly closes RH.** Every route's last wall is the two-site band (1.1–1.2); assembling
routes removes route-specific blockers but not that statement. Two assemblies are strictly better than
every single route: F1 (smallest exact form) and F6 (the only one with an induction structure).

### F1. Two-site Castelnuovo–Severi (recommended form of the problem)
| Segment | Supplied by | Status |
|---|---|---|
| RH ⇔ two-site PD for short bumps at every step | GWZ, AOG | [U]/[L] |
| Explicit entry: pole moment − trivial-zero moments − smoothed prime sum | CSTW | [L]; [D] |
| Frobenius at scale `t` = translation by `t` (Hecke = Mellin translation; window has no internal Frobenius) | RIT, DZG | [L] |
| Arithmetic Riemann–Roch: Künneth `h¹ = ½Q`; pole-plane Abel completion; Weil's form a signed count | LST, ACS | [L] |
| Calibration: curves over `𝔽_q` (the 2×2 Gram of diagonal and Frobenius graph is Weil's Hasse–Weil inequality) | AHD, LST | [L] |
| Core: effectivity (a count-valued Hodge index) on every rank-2 span `{ψ, τ_tψ}` | — | B21 rank-2 (RH) |

What F1 bypasses: interiors, stages, collars, conductors, growing families, dimension zero, the PM
completion. What it keeps: square-root precision, as a Hodge-index statement for one pair of classes per
scale.

### F2. The tower assembly
Base to `181/250` (SPATL) → first stage opens positive (GWZ) → stage criterion, kick law, collar
Rosati sectors (GWZ) → frozen form in closed form (CSTW) → Levinson admission interval per kick (GWZ)
→ core: kick admission at every stage (B2). Its value is as a proof mechanism; its decisive content
is F1.

### F3. The complete-family assembly (best sub-RH theorem at the RH scale)
Subcritical PD (CACT) + critical decomposition and inheritance (AHD) + size-only weighted floor (WTZ)
+ far reserve at one small multiple (CACT [U]) → full-space positivity at one small `K₁` (A30). For RH
it lands on B1 at large multiples.

### F4. The reflection assembly (PM ⊕ window involution ⊕ collar Rosati)
PM exact completion, conjugate-linear twisted reflection, Hecke = translation, kick = collar Rosati
pairing [L]. Residual: positivity of the reflection on zero coordinates (B34), i.e. RH.

### F5. Density–index–cluster (WD ⊕ AHD ⊕ CWS ⊕ AKLT ⊕ SRT)
Off-line zeros live in density-zero window sets, are seen by smooth tests at aperture
`≍ log|γ| log log|γ| + 1/δ`, each raising the window index [L]. Residual: index ceiling and zero–one
law (B10, B11): ≥qRH.

### F6. The length–height bootstrap
| Segment | Supplied by | Status |
|---|---|---|
| Windows positive to length `A` ⇒ no zero of depth `≥ 1/a` below height `exp(a/(C log a))` (detector) | SRT | [L] |
| Contact aperture bounded by near-top zeros | SquareRootThreshold | [L] |
| Model length–height boundary sharp at window length `½log T` in both directions | SquareRootThreshold `DensityMatchedLengthHeightBoundary` | [M] |
| Zeros on the line to height `T` ⇒ windows positive to length `c log T` | — | B43 (sub) |
| A strict gain in the composite transfer `A ↦ c log D(A)` | — | open |

If zeros-to-windows and windows-to-zeros composed to a map `A ↦ A + δ`, RH would follow by induction
from the base. In the model the two transfers are exact inverses (Nyquist self-duality), so the
composite is the identity: the bootstrap is exactly critical, and the induction step is an arithmetic
super-resolution gain. The proved detector is far below Nyquist (a factor `C log a` in the exponent).

## 2.4 A wildly different route

**Verdict: none that escapes the walls.**

- The dynamical formulation (a causal evolution of the window form kicked by `Λ(n)/√n`) is developed
  (GWZ, CSTW): it is classical Szegő–Krein–Levinson theory and it ends at the two-site band.
- Dimension zero is classified (positive dimension supplies nothing); transfer from function fields
  fails at the archimedean place and at the missing internal Frobenius; the trivial angle is a pole.
- PM's realization is the zero side itself; its Hecke structure is translation invariance.
- Every route class that starts elsewhere (scheduled sums, Laguerre–Pólya, realization, pre-divisor
  sections, typicality, heat, density) has its decisive wall identified as a face of the two-site band
  (`route-unification-ledger.md`).

The most distant mechanism not developed in the corpus is **exact measure rigidity**: a classification
theorem (entropy/joinings, Ratner–Rudolph type) for positive-definite states on an arithmetic dynamical
system (adele class space, Bost–Connes system) that would force the Weil distribution to be the unique
positive state with given archimedean and Hecke data. Rigidity theorems are exact and lossless, which is
what no-slack demands. The corpus facts bearing on it point back to the walls: the Weil cone is `{Λ}`
(selection is automatic, positivity is the issue), Hecke-supported states have index `0` or `∞`, the
affine group of `ℚ` has a Mautner phenomenon, Bost–Connes states are positive only at `β > 1` [L]. A
rigidity route needs an a priori positive object whose identification with Weil's functional is exact;
that identification is where RH re-enters. No corpus result shows it escapes.

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — the prime 2 as an exact positive source
**Question.** Prove Weil positivity on every window of length `< log 3` (the whole first prime stage)
by an exact certificate in which the kick `−2w₂c_H(log 2)` is paid inside nonnegative terms: compute the
first-stage complement `Φ_ε` of the trivial-divisor moments (A8), close the odd unit window (A6) and the
even sector, and prove `S^1_A(H) ≥ 2w₂c_H(log 2)` for all `A ∈ [log 2, log 3)` using the collar Rosati
sectors.
- **Below RH.** A finite window; numerically true with margins `5.6×10⁻⁸` (even) and `1.5×10⁻⁵` (odd)
  at half-width `½log 3` [N].
- **Advance.** The first unconditional window theorem where a prime must act as a positive source:
  the frozen form is indefinite there and every cost-only payment is refuted [L]. The certificate is
  either two-collar-local — then it is the base case of every stage mechanism (ground state, Levinson
  admission, collar reflection) — or it is not, which retires stage-wise mechanisms and leaves only F1.

### 2.5.2 Route PM — PM-native short-window positivity
**Question.** Derive Krein positivity of `𝓦_A(W_A)` for some `A > 0` from the Gauss–Mayer side alone:
positivity of the Mayer transfer and Hecke-cone operators at real parameters, the three-term equation,
modular inversion and the boundary charges, without the prime side of the explicit formula.
- **Below RH.** Short windows are positive unconditionally [L]; the question is whether PM can see it.
- **Advance.** Every positivity PM carries is contractive (blind) or Krein (RH) [L]. A PM-native proof
  of any window positivity would be the first non-blind sign PM supplies, and would show which
  physical positivity (Perron–Frobenius at real `s`, cusp energy) carries the archimedean dominance.

### 2.5.3 Route WD — log-free window occupancy
**Question.** Prove `D_win`: for every `A > 0` the number of unit windows `[t, t+1] ⊂ [V, 2V]`
containing a zero of depth `≥ A/log V` is `≤ ε(A)V`, `ε(A) → 0`; equivalently, thin Planck shadows
occupy `o_A(V)` unit windows [L equivalence].
- **Below RH.** A density statement, independent of the log-mean law on generic density data [L].
- **Advance.** WD's certificate machinery is complete; this is its one analytic input at the log stage.
  Unconditionally the double-log stage holds outside `O(V/log log V)` windows, Planck-window certificates
  hold on `(1−η(c))V` windows, and mesoscopic occupancy holds [L]: one `log log` is missing, and the
  `(log V)²` per-window factor cannot be removed by moments (clustered model [M]).

### 2.5.4 Route HF — the twisted sector at every multiple
**Question.** At every critical multiple `K`, prove that the complete tilted-spline form is uniformly
positive on the whole twisted sector (all conductors through `N`, all frequencies), with vanishing
cross terms to the untwisted horizon windows, using the positive scaled counts
`E_m(c) = J(m)c^{−7}R_m(c/m)` past the resolution.
- **Below RH.** The twisted sector carries no Weil form [L]; the statement is a uniformity problem.
  Prime pairings of conductor packets contain no prime in a progression (`Λ ∗ 1 = log`) [L].
- **Advance.** HF at every `K` becomes literally Weil's form on untwisted windows of radius `½log K`
  plus positive counts: the complete family is the window tower, with no conductor, frequency or
  growing-family obstacle left.

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — the two-site band
**Question.** For one short generic bump `ψ`, prove `|c_ψ(t)| < Q(ψ)` for all `t > 0`, i.e.
`|μ₁(ψ)ν₁(τ_tψ) − Σ_kμ_{−2k}(ψ)ν_{−2k}(τ_tψ) − Σ_nΛ(n)n^{−1/2}(ψ⋆ψ)(t − log n)| < Q(ψ)`.
- **Why it opens the path.** It is RH [U/L], in its smallest form: two sites, no interior, one bump,
  one real variable, explicit entries. The trajectory is driven by the pole moment `e^{t/2}` and kicked
  down by `Λ(n)/√n` at `t = log n`; the free trajectory leaves the band [L]. It is Weil's Hasse–Weil
  inequality for the diagonal and the Frobenius graph at scale `t`, so a proof must be a Hodge index
  (F1): a count, an effectivity statement or an exact identity of rank two per scale, uniform in `t`.

### 2.6.2 Route PM — finite cusp energy forces zero defect
**Question.** Prove that every Lewis period of finite dyadic cusp energy has zero co-isometry defect,
`∫_1^∞|ψ(2a) − 2^{1−2s}ψ(a)|²da/a < ∞ ⇒ D_s(ψ) = 0`; equivalently, Krein positivity of the zero
coordinates of all window images from the physical cusp energy.
- **Why it opens the path.** Finite cusp energy ⇔ resonance and `D_s = 0` ⇔ `Re s = ¼` at a resonance
  [L], so it is RH stated between two explicit quadratic functionals of one function on `(0, ∞)`. The
  exact completion makes PM's Krein form Weil's form [L]; the physical cusp energy is a positive
  quantity whose renormalized mean is that form on finite packets [L]. The missing input is arithmetic.

### 2.6.3 Route WD — inner-cap cancellation
**Question.** On every Burnol unit window, at every polynomial stage with prefix `Θ_k(√m)`, cancel the
right-port flux through the inner caps `[½, σ_m]` by a source identity.
- **Why it opens the path.** Across all degrees it is RH; at fixed degree it is the inverse-polynomial
  corridor `|β − ½| ≤ C/|γ|^k` [L]. The exterior caps cancel to `σ_m = 1 − 1/(116log(m+5))`; bounded
  ports are local critical-line purity [L]. Everything else in WD is an equivalence.

### 2.6.4 Route HF — no weighted two-site zero mode along the multiple
**Question.** Prove that the pencil index of the complete family stays zero as the critical multiple
`K` increases: no weighted two-site zero mode `ψ ± τ_tψ` of `κQ + (βJ/K)‖·‖²_{−8}` appears at any `K`.
- **Why it opens the path.** The pencil index is monotone in `K`, zero for `K ≤ K₀` [L], and can change
  only at a jump multiple where a weighted zero mode appears; as `K → ∞` the weighted form is Weil's
  form on windows of radius `½log K`, whose first failure is two-site [U]. HF's open content is the
  two-site band seen through the complete family, with every twisted direction a positive count.

## 2.7 Does closing RH need a new field?

**Assessment: yes, and it is not the exact theory of growing windows.** That theory exists in the corpus
(GWZ, CSTW): the two-collar form, the kick law and its Rosati sectors, the trivial-divisor transmission,
the frozen form in closed form, the translation-contraction law, the lattice canonical system with
Schur parameters, Szegő–Verblunsky products, outer predictors, Carathéodory–Fejér degenerations,
zero-mode parity and the gap law. Its answers to its defining questions:

| Question | Answer |
|---|---|
| Two-collar form of a stage and its law across a kick | stage criterion; kick law; Levinson admission interval; Carathéodory disk |
| Positive ground state at every length | ⇔ outer predictors at every lattice; open (RH) |
| Unique continuation for window zero modes | structural from an end collar; not structural across interior gaps; not needed |
| Rosati form of the reflection on two-collar data | the kick is the collar Rosati pairing |
| ℤ-analogue of the trivial angle | the pole of the frequency counts; on lattices the hyperbolic pair `e^{±h/2}` |
| Soft horizons vs exact margins | Szegő's singular case: margins `κ(0)∏(1−γ²) → 0` because the spectral measure is atomic |

Its decisive output is that RH is decided on two sites: the field's own core is the Π statement of
1.2. Closing RH needs a field that produces that statement.

*What it is about.* An **arithmetic intersection theory of translates**: on the log-line of `Spec ℤ`,
classes are tests `ψ`, Frobenius at scale `t` is translation `τ_t`, the intersection pairing is Weil's
form, and the Hasse–Weil inequality `|ψ·τ_tψ| ≤ ψ·ψ` is the Hodge index of the rank-2 span
`{ψ, τ_tψ}`. Its job is to make the Hodge index on these spans a consequence of counts.

*What it would be like.* Exact and count-valued, as Weil's and Bombieri–Stepanov's proofs over `𝔽_q`:
positivity from the existence of sections (Riemann–Roch plus effectivity), not from estimates; rank two
per scale, uniform in the scale; local in the primes up to `e^{t+2r}`.

*Criteria it must meet.*
1. Reproduce Weil's proof for curves (diagonal and Frobenius graph), including the Hurwitz-weighted
   sum of squares at every resolution [L calibration].
2. Explain the trivial divisor: the archimedean contribution to `ψ·τ_tψ` is the pole moment minus the
   trivial-zero moments [L]; these must be the canonical-class terms of its Riemann–Roch.
3. Fail for fakes: flips, `ζ(s)ζ(s−ε)`, positive finite Euler twins, Epstein and golden data [L].
4. Prime-blind output: `Λ` is forced (Weil cone `{Λ}`, lattice selection) [L], not inserted.
5. Respect the walls: no finite carrier, no finite-square identity, no internal Frobenius, no slack
   (Szegő singular), positive dimension descends nothing [L].
6. Square-root precision with the explicit constant `Q(ψ)`; producers of individual slope `> 1` and the
   integer Chebyshev ceiling are excluded [L].

*Questions it must answer.*
- What is `h⁰(aψ + bτ_tψ)`, and which count has Euler characteristic `½Q(aψ + bτ_tψ)` (Künneth RR [L])?
- What plays ampleness, and what forces effectivity for classes of positive self-intersection?
- Is `c_ψ(t)` an intersection number of the graph of `τ_t` with the diagonal, with the prime sum as the
  count of "fixed points" `n ≈ e^t`?
- Which auxiliary functions (Stepanov–Bombieri over ℤ) vanish to high order on the prime points of a
  short multiplicative window with controlled size?
- How does the bound pass from one scale to all scales without loss (no slack)?

*Tools it aims to develop.* Arithmetic Riemann–Roch for indefinite lattice counts (Künneth RR, Abel
completion, Siegel majorants [L]; Zwegers' indefinite theta); a Stepanov–Bombieri method over ℤ
(finite-field Stepanov [L]; integrality producers and their ceilings [L]); Krein–Szegő theory of Weil
sequences [L]; Hurwitz/angle Plancherel theory [L]; the trivial-divisor moment calculus [L].

*Objects, language, mechanisms.*
- Objects: translate pairs `(ψ, τ_tψ)`, their 2×2 Weil Grams, Schur parameters, trivial-divisor
  moments, Künneth counts, auxiliary Dirichlet polynomials, Frobenius angles and twist frequencies.
- Mechanism A (Hodge index from counts): count-valued RR on rank-2 spans ⇒ two-site band ⇒ RH.
- Mechanism B (Stepanov over ℤ): auxiliary functions vanishing on short-window prime points ⇒
  square-root precision ⇒ RH.
- Mechanism C (kick admission): an invariant of the frozen data that keeps each Schur parameter in
  `(−1, 1)`.
- Mechanism D (length–height super-resolution): a strict arithmetic gain in the contact bootstrap (F6).

No corpus result shows that this field closes RH. Its first tests are 2.5.1 (the prime 2), A6, A8,
A33 and the rank-2 count on spans `{ψ, τ_tψ}` at one scale beyond `181/250`.


## 2.8 The one question

**On one two-site span past the first prime, is Weil's form a Hodge index? Precisely: for a short
bump `ψ` and one step `t` at which a prime acts, is the primitive Künneth `h¹` of the classes
`aψ + bτ_tψ` — which equals `½Q(aψ + bτ_tψ)` [L] — the count of an effective structure (a
count-valued Riemann–Roch on the rank-2 span, nonnegative by construction), so that
`|c_ψ(t)| ≤ Q(ψ)` at that scale follows from a Castelnuovo–Severi argument and not from the zeros?**

*Why this question locates the proof.*
- RH is decided on two sites (1.1): the whole problem is the positivity of the 2-planes
  `{ψ, τ_tψ}`. Their Gram is the Gram of the diagonal and the graph of Frobenius at scale `t` in
  Weil's proof over `𝔽_q`, with Frobenius at scale `t` acting by translation [L/D]. Over `𝔽_q` the
  count exists at every scale: Künneth effectivity of a curve window ⇔ unitarity of its Frobenius [L].
- A proof must use the functional equation and the Euler product together, and nothing more: a
  positive prime measure with integers more regular than `ℕ` is compatible with an off-line zero
  (continuous Beurling systems) [L], while Riemann's functional equation with a positive measure
  forces `ζ`, and a discrete Beurling system with that functional equation is the rational primes
  [L]. The two-site entry is exactly these two inputs set against each other: trivial-divisor
  moments (functional equation) against the smoothed prime sum (Euler product) [L/D].

*The two answers.*
- **Yes.** The proof is Weil's. The sign comes from effectivity of classes on the square of the
  log-line, Frobenius acting by translation, the trivial-divisor moments playing the canonical class;
  RH is the uniformity of the count in `t`. The rest of the corpus becomes the calibration of that
  count: curves (sums of squares at every resolution), fakes (flips, Euler twins, Epstein and golden
  data must have no such count), Weil cone `{Λ}` (the count must force `Λ`).
- **No** — no count-valued structure reproduces `½Q` on a two-site span beyond the first prime.
  Then Hodge-index proofs over ℤ fail at their smallest instance (the corpus already excludes
  bidegree counts, fixed-rank lattice counts, finite-square identities and count identities at the
  first prime [L]; a no extends this to the minimal object). The sign cannot come from geometry or from
  a positivity structure: the proof must be a square-root cancellation estimate for one smoothed
  prime sum, `c_ψ(t) = O(1)`, with the functional equation as its only global input, and every
  positivity route in the corpus is a reformulation of that estimate.

*Why it is less hard than RH or quasi-RH.* One scale and rank two: at that scale the band is a true
finite statement (proved for window length `t + r ≤ 181/250` [L], numerically beyond [N]). The question
asks for the existence of a structure, not for the location of any zero, and neither answer implies a
zero-free strip. Its first instance is a step `t` with window length `t + r ∈ (181/250, log 3)`, where
only the prime 2 acts and the frozen form is indefinite [L].
