# Route obstacles — status quo

Scope: the 33 live routes and 16 candidates of the frontier map, and the programmes that feed them
(GWZ, CSTW, ADT/AHD, CWS, WTZ, DZG, ATD, CACT, CAF, RIT/PM, PBAP, SEL, LST), read against the Lean
corpus at `8ecae707ac` with the working tree. For every route: what is established, the obstacles
that are **(A) just work** and the obstacles that are **(B) open mathematics**. Just work: known
mathematics, finite or certified computation, effectivization, assembly of proved statements,
integration of unfinished modules. Open mathematics: a statement nobody knows how to prove.

Evidence: `[L]` Lean, committed and reachable from its programme umbrella; `[U]` Lean, committed,
not yet imported by an umbrella; `[W]` Lean in the working tree or marked work in progress;
`[D]` derived here from Lean statements; `[M]` exact statement about a model configuration, not
about ζ; `[N]` numerical; `[P]` paper only.
Strength of a B item: **RH** equivalent to RH; **≥qRH** implies a zero-free half-plane and
Lindelöf; **sub** strictly weaker or of unknown strength; **indep.** not implied by RH;
**method** a missing tool; **identity** an exact identity, true or false independently of the zeros.

Windows: a window test of length `A` is a `C²` function supported in `[−A, 0]`; `Q` is Weil's form;
`c_φ(t) = W(φ(· − t), φ)` is the orbit correlation of a bump `φ`; a stage is `log(N+1) ≤ A <
log(N+2)`, `ℓ = log(N+1)`, `w = Λ(N+1)/√(N+1)`. Labels Σ/Π/Γ refer to `walls-ledger.md`; classes
C1–C20 to `route-unification-ledger.md`.

## 0. The picture

| Fact | Anchor | Consequence |
|---|---|---|
| RH ⇔ every two-site lattice window `[[Q(φ), c_φ(t)], [c_φ(t), Q(φ)]]` is positive definite ⇔ strict orbit Cauchy–Schwarz `|c_φ(t)| < Q(φ)` for every bump and `t ≠ 0`; off RH a short bump (support `⊂ [−1/5, 0]`) has `|c_ψ(s)| = Q(ψ)` at some `s` | GWZ `RHIsDecidedOnTwoSites` [U], `ForbiddingLatticeZeroModesIsRH` [L]; AOG `riemannHypothesis_iff_hasseWeil_of_generic` [L] | the first failure of Spec ℤ is two-site: no interior, single angle `±1` |
| One generic bump suffices: RH ⇔ its orbit correlation is eventually bounded; its growth rate is the zero width | AOG `riemannHypothesis_iff_eventually_bounded_of_generic`, `generic_orbitCorr_rate_iff` [L] | the decisive object is one explicit function of `t` |
| For ordered tests the archimedean coupling is the trivial divisor: `2cosh(x/2) − ω(x) = e^{x/2} − Σ_{k≥1}e^{−(2k+½)x}`; `Q(f+g) = Q(f)+Q(g)+2(μ₁(f)ν₁(g) − Σ_kμ_{−2k}(f)ν_{−2k}(g) − ΣΛ(n)n^{−1/2}c_{fg}(log n))` | CSTW `TheTrivialDivisorCouplesOrderedTests` [L] | `c_ψ(t)` = pole moment `≍ e^{t/2}` − trivial-zero moments − the `ψ⋆ψ`-smoothed prime sum on `[e^{t−2r}, e^{t+2r}]` [D] |
| Hence two-site positivity is the windowed prime number theorem at square-root precision with the explicit constant `Q(ψ)` | [D] from the two rows above | Σ on two sites is Π at one point (classes C1 and C7 coincide) |
| Lattice canonical system: Weil sequences `κ(d) = c_φ(dh)` are Toeplitz data; PD ⇔ Schur parameters in `(−1,1)`; margins `E_n = Q(φ)∏(1−γ_k²)`; the newest datum enters `β_n` linearly; a prime kick moves one Schur parameter; degenerate windows are finite curves (Carathéodory–Fejér); a curve fails exactly at its number of angles | GWZ `TheLatticeCanonicalSystem`, `TheSchurParametersOfSpecZ`, `TheLatticeReadsThePrimesCausally`, `ADegenerateWindowIsACurve`, `ACurveDegeneratesAtItsNumberOfAngles` [L] | the causal evolution of the tower is classical Szegő–Levinson theory with arithmetic kicks |
| Under RH every lattice measure is purely atomic at the angles `e^{iγ_ρh}`: `Σγ_k² = ∞`, margins `→ 0`; the first margin is born at order `h²` with coefficient `Σ m_ργ_ρ²|φ̂(γ_ρ)|²` | GWZ `TheSzegoVerblunskyLaw`, `TheLatticeHasNoSlackUnderRH`, `TheFirstMarginIsBornQuadratically` [L] | no slack is Szegő's singular case |
| Stage criterion `Q ≥ 0` on `W_A` ⇔ `2w c_H(ℓ) ≤ S^N_A(H) = inf_{interior} Q_N(H + h)`; the kick is the collar Rosati pairing `c_H(ℓ) = ∫_L H·(σ_AH)∘R`, a positive source exactly on even–antisymmetric and odd–symmetric collar data | GWZ `TheTwoCollarFormOfAStage`, `TheKickIsTheCollarReflection` [L] | the sign of each stage is a race between two collar functionals, both born zero |
| Frozen two-collar form in closed form: collars reach the interior only through trivial-divisor moments and the transports by earlier folds; window growth is a translation contraction; the stage is a Carathéodory disk | CSTW `TheFrozenFormInClosedForm`, `TheFrozenFormGluesTwoWindows`, `WindowGrowthIsATranslationContraction` [L] | the stage recursion is explicit; its sign is open |
| PM completion: `Q(H) = 2Re[𝓦H, 𝓦H]` exactly on `ℓ²(upper Mayer resonances)`, reflection `ρ ↦ 1−ρ̄`; Hecke `T_p − Id` = Mellin translation `√pH(·+log p)`, multiplier `p^{1−2s}`, similitude factor `p` | RIT `TheHeckeEquivariantCompletion`, `TheSourceHeckeOperatorsAreMellinTranslations` [L] | the completed PM space is the zero side of the explicit formula; its Hecke similitude is translation invariance |
| Aperture-independent weighted floor `Q(H) ≥ −C(p)∫e^{−pu}H²`, `p > 1`, every window length | WTZ `TheAliasingWeightPaysEveryWindow` [L] | one small critical multiple pays every window of every fixed family (size-only; no Weil information) |
| Complete tilted-spline matrix PD below `(log N)^{1/8}`; at the critical curve every twisted direction is a positive count; the untwisted count is the finite part of the frequency counts at their pole `u = 0`, where Weil's form sits | CACT [L]; AHD `TheUntwistedCountIsTheFinitePartAtZeroFrequency`, `EveryFrequencySectorInheritsThePolarization` [L] | HF = Weil's form on untwisted windows plus positive counts |
| Unconditional base: all real `C²` tests of support length `≤ 181/250` positive; first prime stage opens positive on `[log 2, 181/250]`; odd unit window `[−½, ½]` positive off one moment: `Q + (3203/320)(∫xF)² ≥ ‖F‖²/1000` | SPATL [L]; GWZ `TheFirstPrimeStageOpensPositive` [L]; WTZ `TheThirdOddMomentIsPaidByTheFirstFold` [L] | the certified tower ends inside the first prime stage |

## 1. Shared obstacle blocks

### S0. The two-site band
Routes: every sign route (C1), every precision route (C7). Classes C1, C7, C19.

Established [L]: RH ⇔ two-site PD ⇔ strict orbit Cauchy–Schwarz (GWZ); one generic bump decides,
eventual boundedness decides, growth rate = zero width (AOG); explicit ordered-coupling form of the
two-site entry (CSTW); under RH `c_φ(t) = Σ_ρ w_ρcos(γ_ρt)`, `w_ρ = m_ρ|φ̂(γ_ρ)|²` (GWZ
`SpecZIsACurveOnEveryLattice`); free evolution (no primes) fails; every prime power is needed;
only `Λ` keeps every lattice positive (GWZ `TheLatticeSelectsTheVonMangoldtWeight`).

Research status: the decisive object of the programme is one explicit function of one real variable:
the trajectory `t ↦ c_ψ(t)` of a short generic bump, driven upward by the pole moment `e^{t/2}` and
kicked by `Λ(n)/√n` at `t = log n`; RH is the statement that it never leaves the band `[−Q(ψ), Q(ψ)]`.

| | Obstacle | Strength |
|---|---|---|
| A33 | Formal bridge two-site entry ↔ ordered coupling ↔ WL/one-sided-count receivers (one module stating the band as the explicit prime-sum inequality) | — |
| A34 | Two-site band on a bounded step range from zero data plus tails (finite verification) | — |
| B42 | The band for all steps: `|c_ψ(t)| < Q(ψ)` ∀t for short bumps (= B1) | RH |

### S1. Complete Weil family at the critical overlap
Routes: HF, SRT, AIP, ACT, ACS-atomic, RW-atomic, SC, CHMD (index), FEL, MSC. Class C1.

Established:
- [L] Subcritical regime closed: `completeWeilMatrix tiltedUnitSpline c N ≻ 0` for every `α < 1/8`,
  `1 ≤ c ≤ (log N)^α`, floor `κ/(2c⁷)`.
- [L] Receivers: window criterion; horizon criterion; Beurling schedule `2L(log L)²`; unit-bump
  receiver at every positive-power rate.
- [L] Critical-curve second order: untwisted windows `κQ(H) + (βJ/K)‖H‖²_{−(β+1)}`; conductor windows
  `(7φ(m)J(m)/K)‖G‖²_{−8}`; cross pairings `→ 0`; uniform orthogonal decomposition on a growing
  conductor range `m ≤ M(N) → ∞` (nonquantitative); count ratio `c⁷E_m(c)/J(m) = R_m(c/m)` uniform
  for `m = o(c)`, `≤ ½` for `m ≥ λ₀c`; Ramanujan horizon vectors of all `m ≤ N^θ`, `θ < ½`, are
  collective quasimodes with eigenvalues `E_m(c) ≥ 0`.
- [L] Every periodic twist, every trigonometric twist with distinct frequency classes (Hurwitz weight
  `½(ζ(β+1,u)+ζ(β+1,1−u))`), every primitive character (first-order energy `−2Re L'/L(1,χ)`, second
  order `−2(φ(q)/q)Re(L'/L)'(1,χ)`, distinct characters decouple) inherits the polarization.
- [L] Frequency counts have a pole of order `β+1` at `u = 0` whose finite part is the untwisted count.
- [L] One aperture-independent `0 < K ≤ K₀` makes every independent fixed window family eventually PD
  (size-only, via the weighted floor); exact clock `c⁸ = K log N`: eventual inertia
  `(n₊(P), n₋(P)+n₀(P), 0)`.
- [L] Bulk blind below the grid: all zeros of height `≤ λN` (`2λL ≤ π`) enter a fixed packet only
  through the pole, `(c_N/log N)κy₁²Σm_ρ/(ρ(1−ρ))`.
- [L] Bulk second order at fixed overlap `0 < c < 1`: `⟨PR,R⟩ − (log N − γ)⟨R,R⟩ → 2γ₁ + γ²`, every
  conductor entry an explicit polynomial in `γ, γ₁`, divisor logarithms; center part and cross error
  explicit.
- [U] Far reserve on `(V₁)^⊥` uniformly for `1 ≤ c ≤ 2K₁(log N)^{1/8}` at one small `K₁`, with a prefix
  cost (CACT `TheTopCollarHasADyadicSeventhPowerReserve`); [W] logarithm-free low-conductor residuals.

Research status: subcritical solved; at the critical curve every direction except untwisted windows is
a positive count; one small multiple pays every fixed family by size alone. Full-space positivity at
one small multiple is an assembly problem; positivity at every multiple is Weil's sign on untwisted
windows of radius `½log K`.

| | Obstacle | Strength |
|---|---|---|
| A1 | Explicit constants and horizons (eighth-root theorem, `1/9`, logarithmic profile, Beurling schedule, horizon criterion) | — |
| A2 | General profiles past `θ = 1/1080` and the super-log-log clocks | — |
| A3 | Joint twist families (Ramanujan × character × frequency, with untwisted windows); equal-parity character coupling through `L(s,ψ̄₁ψ₂)`; characters of different moduli; moving and coalescing frequencies at fixed `K` | — |
| A4 | Solved: canonical clock inertia (AHD) | — |
| A9 | Window index as a counting function of the length | — |
| A30 | Full-space positivity at one small critical multiple: integrate the far reserve [U], pay the prefix cost, assemble the conductor-one block (at fixed `K` it synthesizes windows of bounded radius `½log K`) and the Schur payment [W] | — |
| A31 | Quantitative conductor range: prescribed `M(N) = o(c_N)`; scaled-count quasimodes past the resolution with uniform errors | — |
| B1 | Weil's sign on untwisted windows at every multiple (= windows of every length) | RH |
| B4 | Uniform positivity of the whole twisted sector (all conductors, all frequencies) at every multiple | sub |
| B5 | Solved per fixed family (size-only weighted floor) | — |
| B6 | Full-space positivity of general profiles past `log log N` | sub |
| B7 | Exact sum of squares on one two-prime lattice | RH |

### S2. The window tower and its canonical system
Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT, HF, ACS, SRT, SZ; programmes CWS, WTZ, DZG, GWZ, CSTW.
Classes C1, C4, C15, C19.

Established [L]: window datum; truncated Dirichlet λ-ring; stage transfer `Q = Q_N − 2wc_H(ℓ)`;
ground-state identity; exit charge; composite stages free; sharp floor; end profile; Barta/Picone
certificates (sign-blind); Hecke-graph reading; exact Tate horizons at stages 1–2; frozen form
indefinite at the first prime (`Q₁ < 0 < Q`); two-collar form, stage criterion, kick law,
reflection invariance, birth at zero; kick = collar Rosati pairing with explicit sign sectors; on a
nonnegative window frozen-negative even (odd) tests are collar-antisymmetric (symmetric) dominant;
chain law and stage-test identity `Q = F − 2w⟨x_L, Jx_R⟩`; frozen two-collar form in closed form
(trivial-divisor moments + earlier-fold transports); first-stage complement depends on the collars
only through `Q(x_L)`, `Q(x_R)` and their moment sequences; translation-contraction law and stage
disk; lattice canonical system (Levinson recursion, Schur parameters, causality, single-kick law,
admission interval `posDef_update_iff`); lattice union law (window ⇔ all lattices of total length
`≤ A`); refinement lowers margins; no unnormalized continuum limit (`γ₀(φ,h) → 1`, corner margin
`≤ 0`); `h²` birth law; zero modes: radical, parity, gap law, injective restriction to each end
collar; interior-gap continuation not structural (three-angle curve); RH decided on two sites [U].

Research status: the stage step is exact, local and explicit in both registers (collars;
lattices). Its sign is the only open content; two sites already decide RH, so stage mechanisms are
proof mechanisms, not new criteria.

| | Obstacle | Strength |
|---|---|---|
| A5 | Certified first prime stage `[0.7243, log 3)` (odd margin `1.5×10⁻⁵`, even `5.6×10⁻⁸` at half-width `½log 3` [N]) and second-stage certificates on the exact path graph | — |
| A6 | Odd unit window: one first-moment Schur inequality remains — for the exact logarithmic reflection operator, `K₁₁ + (63/20)K₁₃²/(1 − (63/20)K₃₃) ≤ 1/(77/20 + 39/256)`; current bound `Q + (3203/320)(∫xF)² ≥ ‖F‖²/1000` [L]; the linear chord alone cannot pay the first charge [L] | — |
| A7 | Rational Hecke graphs and Tate horizons of stages 3, 4, 5, 7, … | — |
| A8 | Closed form of the first-stage complement `Φ_ε(μ(x_L), ν(x_R))`: Schur complement of the prime-free interior form against the moment functionals `e^{(½−s)u}`, `s ∈ {1, −2, −4, …}` [structure L] | — |
| A29 | Atomic-lattice bound `λ_max ≤ ½log N` with explicit Mertens error | — |
| B2 | Exact stage step at every prime power: `2wc_H(ℓ) ≤ S^N_A(H)`; lattice form `|β_n − kick| < E_n` | RH as induction; each stage sub |
| B3 | Window criticality: a positive ground state at every length passing each stage by a collar correction | RH; fixed length sub |
| B14 | Growth exponent of window negativity (between `Θ − ½` on two-bump tests and `½`) | `< ½` ≥qRH |
| B41 | Solved: the two-collar recursion is the Levinson recursion on lattices and the Carathéodory-disk law in the continuum; the continuum limit is a jet system | identity |
| B43 | Height–length (contact) law: RH to height `T` ⇒ every window of length `≤ c log T` positive (model boundary `c = ½` sharp [M]) | sub |

### S3. Dimension zero and the Tate family
Routes: ACS, HF; programmes WTZ, DZG, ATD, AHD. Class C13.

Established [L]: Tate jet and signed-count forms of `Q`; jets generated by `M` and `ρ_A(Λ)`; the wall
`k ↦ −k` is Dirichlet inversion; bare domination ⇔ `Q ≥ 0`; no uniform Gamma–pole domination;
domination horizon `≤ C exp(−exp(A−2))` on Riemann's kernel; Euler-product pole weight forced and
refuted; Tate positivity not uniform and does not descend; completed family unimodular on the line.

Research status: classified; positive dimension supplies no positivity.

| | Obstacle | Strength |
|---|---|---|
| — | none beyond B1 | — |

### S4. Kähler package, stars and gluing
Routes: HF, ACS-Hodge, TG, SC, RW; MC through the gluing determinant. Class C12.

Established [L]: HR ∧ HL ⇔ strict HR; RH ⇔ HL on the PSD locus; stars, depth law, gcd strata;
nerve `χ̃ = −M(N)`, Redheffer `det = M(N)`; zero modes are the radical; a zero mode at a first critical
lattice length is unique, a palindrome up to sign, nonzero at both ends; first failures are two-site.

| | Obstacle | Strength |
|---|---|---|
| A21 | Björner wedge decomposition of the squarefree complex | — |
| A22 | Quantitative depth law, star horizons, gcd-strata tables | — |
| B8 | Hard Lefschetz on the positive locus = no zero mode at any length = no degenerate two-site lattice | RH |
| B9 | Payment of the top coprime stratum | RH |
| B15 | Cross-tower spectral gap through the archimedean channel | method |
| B31 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH |

### S5. Index and finite off-line support
Routes: HKT, AKLT, AID, SRT, CHMD, SC, RIT, CWS. Classes C1, C3.

Established [L]: finite index = PD minus finitely many squares; finite index ⇒ Lindelöf; RH ⇔ index
zero; window index finite, monotone, exhausting; pencil index = jump multiples; `{0, ∞}` laws; index
`≤ R + A` on `R` coarse cells; growing Euler heads unbounded.

| | Obstacle | Strength |
|---|---|---|
| B10 | Arithmetic index ceiling uniform in resolution | ≥qRH (`K_ζ`); RH (`K_ζ ⊠ K_ζ`) |
| B11 | Zero–one law `κ(K_ζ) ∈ {0, ∞}` | sub |

### S6. Window energy, near-line density and the Hecke defect
Routes: WD, LA, TG, HCF, SC-heat, TH-heat; census; HEF. Classes C3, C11.

Established [L]: window integer = Wiener–Hopf index; pair resolvent = Laplace transform of `|𝒵(t)|²`,
abscissa = twice the maximal depth; eight-way near-line density equivalence; almost-all log-stage
certificates ⇔ log-free occupancy `D_win`; `D_zero` ⇔ `D_win` + vanishing giant-cluster tails;
`(log V)²` per-window second-moment factor unimprovable under occupancy (clustered model [M]);
uniform Planck-volume bounds do not give occupancy (sparse model [M]); `D_win` ⇔ thin Planck
shadows; Planck-window log-stage Bessel–Szegő certificates on `(1−η(c))V` windows; mesoscopic
occupancy; double-log stage outside `O(V/log log V)` windows; right half-port
`O(e^{(σ_m−½)t}/(t+1))` on every Burnol window (`σ_m = 1 − 1/(116 log(m+5))`),
`O(e^{(3loglogV/logV)t}/(t+1))` outside `O(V/loglogV)` windows, exact critical-line flux identity on
`(1−O(B))V` micro-Planck windows; zero-free window ⇔ unweighted `L²` port; bounded port ⇔ local
critical-line purity; polynomial stage ⇔ RH, fixed degree `k` ⇔ `|β−½| ≤ C/|γ|^k`.

| | Obstacle | Strength |
|---|---|---|
| A26 | WD composition: computable stopping prefix, flow threshold from sub-Weyl profiles, `ΔO = o(log T)` ⇒ density one ⇒ Lindelöf | — |
| B16 | Inner caps `[½, σ_m]` at every polynomial stage | RH; fixed degree ≥qRH |
| B17 | `100%` critical-scale clustering (≡ log-mean `o(1)` ≡ Hecke `o(log U)` ≡ horizontal moment `o(T)`) | sub |
| B18 | `D_win` (≡ thin Planck shadows: vertically thin off-line projections occupy `o_A(V)` unit windows); `D_zero` (≡ `D_win` + vanishing giant-cluster tails) | sub |
| B19 | Hecke defect pointwise `O(1)` / one dyadic constant | ≥qRH / RH |
| B20 | Distributional input beyond counts and moments | method |

### S7. Counts, producers and precision
Routes: WL, MC, PBM, RB, JAS, CTF, ACS-effectivity, HF-RR, RW; census. Classes C7, C13, C19.

Established [L]: one-sided count ⇔ RH; multivariate parity producers reach `(1+ε)x + C_εlog²x`;
individual producers slope `> 1`; Redheffer `det = M(N)`; Künneth RR, window `h¹ = ½Q`;
count classification; first-prime count identity refuted; census `0.67250071`; every eventually
positive cyclotomic band has energy abscissa `2Θ`; cluster-product detector; two-site band = windowed
PNT at `√` precision [D].

| | Obstacle | Strength |
|---|---|---|
| A20 | Logarithmic two-point Chowla | — |
| A23 | Census: `S_cos(λ)`, odd stabilizer taper transport, `β = 2` | — |
| A24 | Voronoi summation; Zwegers' indefinite theta series | — |
| A25 | Künneth primitive `h¹` at small degree; mixed-jet recovery; explicit main-term producer | — |
| A27 | Explicit cluster-detector constant `A₀`; cluster horizon with the window index | — |
| B21 | Count-valued primitive `h¹` as an inequality; its rank-2 form: effectivity on every span `{ψ, τ_tψ}` | RH; fixed length sub |
| B22 | Genus upper law `g ≤ (2+η)e^A` | indep. |
| B23 | Logarithmic Serre duality, primitive part | sub |
| B24 | `ε`-uniform producer; square-root source input; half-power Redheffer determinant | sub; RH |
| B25 | First cyclotomic mode at square-root precision | RH (power saving ≥qRH) |
| B26 | Signed prime-pair information beyond bandwidth one | sub |
| B27 | First Epstein real zero on the boost line | sub |

### S8. Carriers, coupling, selection and the prime-blind cone
Routes: SC, ACS, HF; candidates; PBAP. Classes C2, C8, C16.

Established [L]: coupling calculus; bounded dense two-prime coupling ⇔ RH; Gaussian-damped cone ⇔ RH;
undamped cone ⇒ RH or unattained width; carrier classification; Weil cone `{Λ}`; lattice selection of
`Λ` (every kick necessary, every other weight degenerates some lattice); PBAP ⇔ RH, node-critical,
Farkas-dual, zero-side identity on blind tests, solved on nonnegative and separated-bump cones;
Selberg-class rigidity: Euler-log discrepancy absolutely convergent at `σ = ½` forces equality
without Gamma matching; positive finite Euler twins with zeros at any `Re s ∈ (½,1)` violate the
strict Euler bound; degree zero = Dirichlet unit [L]; no degree in `(0,1)` [W].

| | Obstacle | Strength |
|---|---|---|
| A10 | Function-field calibration (twisted horizon layer and second order for curves; higher-genus fakes; `𝔽₃` elliptic chain) | — |
| A12 | Prime-side identity for the Gaussian-damped two-prime coupling | — |
| A28 | Finite-level Weil cones `C_A` and their widths | — |
| B28 | Bounded Gaussian-damped cone coupling from the prime side; unattained width on the undamped cone | RH |
| B29 | Finite-sieve Hodge positivity → global | RH |
| B30 | Reflection positivity: Rosati positivity of the window algebra (the kick is the collar Rosati pairing) | RH |
| B32 | Zero-independent selection at the trivial gauge point | RH |
| B33 | Euler-product FE twins inside the full class; unimodular gauges | sub |
| B40 | Prime-blind positivity on signed blind combinations | RH |

### S9. Realization and scattering
Routes: PM, RN, PTR, W1C. Classes C9, C14.

Established [L]: Gauss–Mayer operator, faithful divisor; resonance ⇔ `ζ(2s) = 0`; `Z_PM` = Hardy's `Z`;
Lewis adjoint; `D_s ≤ 0`, `= 0` iff `Re s = ¼`; Krein positivity ⇔ RH; exact completion
`Q(H) = 2Re[𝓦H,𝓦H]` on `ℓ²(resonances)` with bounded window map; Hecke = Mellin translation for every
prime; Hecke cones tile the quadrant; Barnes and Eisenstein periods are Hecke eigenfunctions with
eigenvalue `1 + p^{1−2s}` for every prime; positive-determinant Hecke operators preserve the Lewis
carrier; retained boundary coordinate makes restoration invertible and corrected transport exact;
whole-Haar admission of a `T₂`-image iff `H(−log 2) = 0`; closed Cauchy reflection across the strip;
Gaussian core synthesis faithful; physical cusp energy minus explicit counterterms has mean equal to
the Krein form on finite packets.

Research status: PM's completed space is the zero side of the explicit formula; every structure it
carries (Hecke, reflection, boundary) is identified; no positivity statement is attached.

| | Obstacle | Strength |
|---|---|---|
| A13 | Classical identifications: Selberg-zeta normalization, Lax–Phillips for `PSL₂(ℤ)\ℍ`, Lewis–Zagier separation, `+1` Mayer eigenspace classification, Garland loop-group identification | — |
| A14 | Operator-native nonvanishing on `Re w = 1` | — |
| A15 | Solved: Hecke relations and Mellin bridges for every prime | — |
| A32 | Infinite-packet physical identity: Krein form of every window image = renormalized mean cusp energy with the counterterm in closed form (stub module exists [W]) | — |
| B34 | Krein positivity of the zero coordinates of window images; equivalently finite cusp energy ⇒ zero defect | RH; separated gap ≥qRH |
| B35 | A statistic of resonant states selecting the decay rate | method |
| B36 | Solved: exact Hecke-equivariant completion | identity |
| B37 | Reduced to A32 | — |
| B39 | Source-faithful realization: a tower of unbounded rank | RH |

### Route-specific items
| | Obstacle | Routes | Strength |
|---|---|---|---|
| A11 | Integration of unfinished modules: CACT far reserve [U] and log-free residuals [W]; GWZ `RHIsDecidedOnTwoSites` [U]; SEL `DegreeGap` and the ordinary Mellin chain [W]; LI Cayley ladder; SZ first-variation transfer; HKT compressions; AKLT fine towers; ALG; AGT; ACP | HF, AIP, GWZ, ACS, LI, SZ, SC, MC | — |
| A16 | Theta Hankel rank-8 strictness; ranks 9–10 | TH | — |
| A17 | Hausdorff shifts, Jensen degree horizons, two-grid degrees, Toeplitz minors beyond PF₃₇ | PA, LA, HCF | — |
| A18 | Nine atom-dominated collar moduli | ACT | — |
| A19 | Mixed Schur debit; first-prime, coarse and polar costs on fixed cells | AIP, CHMD | — |
| B12 | All-rank / all-degree signs; Laguerre–Pólya property of `ξ(½ + z)` | TH, LA, HCF, PA, GTA; ART | RH |
| B13 | Lower bounds for scheduled prime energies | FU, CFC, RP, SZ, LI, FEL, EGC | RH |
| B38 | Pre-divisor forcing | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF | RH |

## 2. Programmes

### GWZ and CSTW — the canonical system of the window tower
Thesis: the tower is a causal evolution with one arithmetic kick per prime power; positivity is the
evolution staying inside the positive cone.

Established [L]: S0 and S2 in full; RH as positivity of every lattice margin, every reflection
coefficient in `(−1,1)`, the singular law `Σγ² = ∞`, the absence of degenerate lattices, two-site
positivity [U]; degenerate windows are finite curves, curves fail at their number of angles, Spec ℤ
under RH is the curve with the infinitely many angles `e^{iγ_ρh}` on every lattice; the pole is the
hyperbolic pair of angles `e^{±h/2}` and carries one negative square; margins bounded by recurrence
`E_{m+1} ≤ Q(φ − φ(·+(m+1)h))`; trivial-divisor transmission; frozen form in closed form;
translation-contraction law.

Research status: the field's dictionary is complete and unconditional; its only positive content is
the base `181/250`. Its decisive output is that the interior of the tower never carries the first
failure that matters.

| | Obstacle | Strength |
|---|---|---|
| A5, A6, A8, A33, A34 | First prime stage; odd unit window; first-stage complement; two-site bridge; bounded-range band | — |
| B2, B3, B42, B43 | Kick admission at every stage; criticality; the two-site band; contact law | RH; RH; RH; sub |

### ADT and AHD — degenerations
Established [L]: S1 in full (critical curve, frequency grading, pole at zero frequency, aperture-
independent multiple, critical boundary, bulk below the grid, bulk second order); Frobenius-angle
dictionary; pure curves degenerate completely; monodromy rate of a curve = its zero width `log R/log q`
in both signs (Turán power sums); golden fake rate `log φ/log 5`.

| | Obstacle | Strength |
|---|---|---|
| A3, A9, A10, A31 | Joint twist families; window index vs length; `𝔽_q` twists; quantitative conductor range | — |
| B4 | Uniform twisted-sector positivity at every multiple | sub |
| B1 | Weil's sign on untwisted windows | RH |

### CWS, WTZ, DZG, ATD — window algebra and dimension zero
Established [L]: S2 (window side) and S3 in full; odd unit window off one moment; retained Gamma
comparison lossy (quintic window: retained form `< 0 < Q`); exterior Gamma reserve `1/128`.

| | Obstacle | Strength |
|---|---|---|
| A5–A8, A29 | Certified stages; odd unit window; Hecke-graph horizons; first-stage complement; atomic Mertens bound | — |
| B2, B3, B30 | Stage step; criticality; Rosati positivity | RH |

### CACT and CAF — complete forms
Established [L]: subcritical positivity; exponent ladder to `1/8`; every fixed overlap positive;
logarithmic profile; conductor frames; cyclotomic coercivity; first cyclotomic band carries `2Θ`.
[U] critical-multiple far reserve; [W] log-free residuals.

| | Obstacle | Strength |
|---|---|---|
| A1, A2, A30 | Constants; general profiles; small-multiple full-space assembly | — |
| B6, B25 | General profiles past `log log N`; first mode at `√` precision | sub; RH |

### RIT/PM — Mayer scattering
Established: S9 in full.

| | Obstacle | Strength |
|---|---|---|
| A13, A14, A32 | Classical identifications; native nonvanishing; infinite-packet physical identity | — |
| B34, B35, B39 | Krein positivity of zero coordinates; resonant statistic; unbounded-rank realization | RH; method; RH |

### PBAP — the prime-blind line (support)
Established: S8 (prime-blind part).

| | Obstacle | Strength |
|---|---|---|
| A28 | Finite-level cones and their widths | — |
| B40 | Signed blind combinations | RH |

### SEL — Selberg class (support)
Established [L]: Gamma-independent Euler rigidity at `σ = ½`; finite-prime and finite-support
rigidity; degree-zero classification; positive finite Euler twins and their exact discrepancy
boundary; [W] degree gap `(0,1)` empty.

| | Obstacle | Strength |
|---|---|---|
| A11 | Integrate the degree gap and the ordinary Mellin chain | — |
| B33 | FE twins with Euler exponent `< ½` and off-line zeros (none known; none excluded) | sub |

## 3. Live routes

Per route: path; established; A (just work); B (open). Shared items refer to Section 1.

### WL — Weil lag / prime lag
Path: prime error → square-root bound or subexponential critical energy → RH.
Established: critical-energy and one-sided `√x log²x` criteria; the first Chebyshev cyclotomic band
has abscissa `2Θ`; multivariate parity producers reach the main term; two-site band = windowed PNT at
`√` precision with constant `Q(ψ)` [D].
- A: A25, A33. B: B24, B25, B42.

### RW — restricted Weil ground energy
Path: `μ(a) ≥ 0` at every aperture → RH.
Established: attained strictly decreasing minima; floors through total length `≈ 0.7243`; exact
`{∞,2}` trace through `½log 3`; first prime stage opens positive on `[log 2, 181/250]`; window ⇔ all
fitting lattices; RH ⇔ no degenerate lattice ⇔ two-site positivity [U]; frozen negative direction at
the first fold; under RH every fixed-length lattice margin `→ 0`.
- A: A5, A6, A8. B: B1, B2, B3, B42.

### FU, CFC, RP — scheduled prime histories
Established: exact receivers; cofinal unboundedness under ¬RH; sublinear floors impossible (RP);
phase-natural transport is identity (CFC).
- A: none. B: B13.

### PA — prime–archimedean source passivity
Established: each fixed Hausdorff order positive at large shifts.
- A: A17. B: B12.

### MC — Möbius cancellation
Established: half-power and Redheffer criteria; every eventually positive cyclotomic band retains
`2Θ`; Haar-a.e. `½`, Baire-generic `1`; Redheffer `det = M(N)` = nerve Euler characteristic.
- A: A20, A21. B: B24, B25, B32.

### TT — theta seam / Wold
Established: seam, tail and Wold receivers; Φ-Doob identities; restricted current signs.
- A: none. B: B3 (odd sector), B1.

### LA — Laguerre/Jensen and local heat
Established: every fixed Jensen degree eventually real-rooted; slice floor `133/200`; right-half depth
moment `o(V)`; PF₃₇.
- A: A17, A26. B: B12; uniform tail narrowing (≥qRH).

### TG — topological sub-unit gate
Established: winding/index and cubic-transgression identities; window integer decided by the window
energy.
- A: none. B: B16, B8.

### HF — Hodge / Hecke / complete cells
Established: S1, S2, S3, S4 in full; frequency grading with Weil's form at the pole; one small
multiple pays every fixed family; Frobenius at infinity ⇔ RH; no internal window Frobenius; Hecke
on the PM side is translation.
- A: A1–A3, A9, A10, A21, A22, A25, A30, A31. B: B1, B4, B6, B7, B8, B9, B10, B21, B23, B30, B31,
  B39.

### CHMD — causal hyperbolic–modular duality
Established: RH ⇔ `R ≤ ½` on the odd sector; all-detail prime–pole cancellation
`O(exp(−√log Y/92160000))`; normalized prime matrix approaches one separable pole channel.
- A: A19. B: B10, B3; joint non-arithmetic Gamma graph + signed diagonal + poles (sub).

### TH — theta Hankel ranks
Established: rank 7 strict; rank 8 PSD; native tails = Gram-square mass minus signed local flux.
- A: A16. B: B12; rank-uniform signed flux payment (RH).

### RN — renewal
Established: compact cone-positive renewal operator with exact determinant and resonances.
- A: none. B: directed mixed prime + Gamma `≥` pole (RH); B39.

### WD — Ward / collision / window energy
Established: S6 in full.
Research status: the analytic block is one density statement in eight forms; `D_win`'s exact
equivalent is the thin-Planck-shadow statement; the double-log stage is unconditional; inner caps are
the zero-free-region problem.
- A: A26. B: B16, B17, B18, B19, B20; B10 (tower branch).

### LI — paired Li / prime–Gamma balances
Established: guarded history-zero set finite, RH ⇔ empty; Cayley–Li primitive-sign receiver [W].
- A: A11. B: B13.

### SZ — Suzuki screw / shifted-kernel limits
Established: exact lower-bound receiver; Krein–Schur block congruences; the screw function is
Weil's kernel; its lattice and continuum Schur theory is GWZ/CSTW.
- A: A11. B: B13; B2 in Krein–Schur form.

### PM — Gauss–Mayer physical realization
Established: S9 in full.
Research status: exact completion identifies PM with the zero side; Hecke operators act as
translations; the reflection is the window involution; every positivity PM has is contractive
(blind) or Krein (RH).
- A: A13, A14, A32. B: B34, B35, B39, B31.

### JAS, CTF, PBM, RB — one-sided count
Established: JAS positivity at growing logarithmic budget; CTF completion identities; PBM convergence
at every `σ > ½` ⇔ RH; RB colossally abundant reduction.
- A: A33. B: B24, B42.

### HCF, XN, BAG, EWU, GTA, OWU
- HCF: two-grid criterion; one grid aliases. A: A17. B: B12.
- XN: Newton-disc criterion; nonnegative Laplacian of the margin. B: covering with nonnegative
  margin (RH).
- BAG: disc recurrence ⇔ RH. B: B32.
- EWU: weight rigidity; attained aperture-antitone blind minima. A: A5. B: B1 (even sector).
- GTA: transverse-charge criterion. B: B12.
- OWU: odd floors; odd unit window `Q + (3203/320)(∫xF)² ≥ ‖F‖²/1000`, `Q ≥ ‖F‖²/100` off two odd
  moments, frozen odd form `Q₁ + 20M² ≥ ‖F‖²/125`; positive first-moment reflection inverse; regional
  logarithmic kernel diagonal in Legendre polynomials with eigenvalues `2H_n`. A: A5, A6. B: B1 (odd
  sector), B3.

### SRT, ACT, AIP — complete atomic matrix
- SRT: S1; horizon criterion; pencil index; cluster-product detector; bulk blind below the grid. A:
  A1, A3, A9, A27, A31. B: B1, B4, B10.
- ACT: collar thresholds pay every modulus outside nine; criticality theory. A: A18. B: B1, B3.
- AIP: complete form = jump + incidence − shell + boundary; eighth-root Schur synthesis; far reserve
  at one small multiple [U]. A: A1, A19, A30. B: B1, B4, B6.

### ACS — arithmetic Castelnuovo–Severi
Established: RH ⇔ effectivity ⇔ Hodge index ⇔ section count; primitive `h¹ = Q/2`; Abel completion;
pole-plane RR; fakes; Hecke similitudes scalar; Selberg-class rigidity at `σ = ½`; two-site
positivity is the Hodge index on the spans `{ψ, τ_tψ}` [D].
- A: A10, A23, A24, A25. B: B21 (rank-2 form), B22, B23, B26, B27, B30, B1, B7, B31.

### SC — Stokes/Witt–Krein / archimedean successor
Established: glued index `κ_ζ + 1`; carrier classification; damped cone ⇔ RH; undamped ⇒ RH or
unattained width.
- A: A10, A12. B: B1, B7, B10, B28, B29, B8.

## 4. Candidates

| Candidate | Established | A | B |
|---|---|---|---|
| APF | Fredholm index; cycle-trace reconstruction | — | zero-independent divisor exhaustion (B38) |
| BSH | framed curvature | — | pre-divisor section and mate identity coupled to Ξ zeros (B38) |
| CDC | calibrated confluence iff `Re s = ½` | — | source-defined potential forcing confluence (B38) |
| DR | cusp roots, finite monodromy | — | compatible roots on the strict-right domain (B38) |
| EGC | pole-safe contour; complete copy correction | — | outer expanding-contour sign (B13) |
| EWJ | Euler/Wold jets | — | zero-independent source admission (B38) |
| FEL | theta likelihood; BSY integral = off-line zero sum | — | predeclared source balance (B13) |
| HJ | Hurwitz residual = SEC charge | — | pre-divisor forcing (B38) |
| IRK | rotation-algebra trace / winding | — | arithmetic projective lift with integral count (B21) |
| MSC | Möbius–Sonin; strict-right divisor preservation | — | bridge to nonnegative Sonin energy (B1) |
| PCS | singular co-shift | — | source-natural wall annihilation (B38) |
| PTR | lossless stacks, unit port gap | — | prime-faithful port (B39) |
| RFHM | support grade | — | symmetry-breaking law (B38) |
| SEC | essential norm = seam jump | — | pre-divisor compactness at zeros (B38) |
| W1C | Lee–Yang receiver; PM's exact zero-coordinate Krein space, closed reflection, all-prime transport | A13, A32 | positive arithmetic Hilbert realization with self-adjoint generator (B34, B39) |
| WBF | genealogy Gram | — | any arithmetic coupling (B38) |

## 5. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ = Π on two sites: the band `|c_ψ(t)| < Q(ψ)` | every route below in the Σ and Π rows |
| Σ, window sign / stage step / criticality | RW, EWU, OWU, ACT, HF, SRT, AIP, ACS-atomic, SC, CHMD, TT, SZ; MSC, FEL; GWZ/CSTW/CWS/WTZ/DZG |
| Σ, untwisted windows at large multiples | HF, SRT, AIP, SC; CACT, AHD |
| Σ, Hodge–Lefschetz / zero modes / top coprime stratum | HF, ACS-Hodge, TG |
| Σ, rank / degree (Laguerre–Pólya) | TH, HCF, PA, GTA, LA; ART |
| Σ, scheduled prime sums | FU, CFC, RP, SZ, LI; EGC |
| Σ, realization (tower of unbounded rank) | RN, PTR, W1C |
| Π, inner caps, near-line density | WD, TG, LA (heat), SC-heat, census |
| Π, count-valued primitive `h¹` (rank-2 Castelnuovo–Severi) | ACS-effectivity, HF-RR, IRK |
| Π, one-point precision | WL, MC, PBM, RB, JAS, CTF, SC |
| Γ, reflection positivity (window Rosati form; Krein positivity of zero coordinates) | PM, HF, ACS, CWS, W1C |
| Γ, prime-blind positivity on signed blind combinations | PBAP |
| Γ, trivial gauge point / pre-divisor forcing | BAG, XN, MC; APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |
