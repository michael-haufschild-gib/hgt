# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route; labels `A*`, `B*`, `S*`, path classes P1–P4),
`walls-ledger.md` (Σ/Π/Γ) and `route-unification-ledger.md` (classes C1–C20). Corpus: `ccfb4b168e`
with the working tree. Evidence: `[L]` Lean, committed and in its umbrella; `[U]` committed, not in an
umbrella; `[W]` working tree or work in progress; `[D]` derived here from Lean statements or from the
programme's own conclusions; `[M]` model statement; `[N]` numerical. Killed mechanisms are cited by
their anchor in `rh-killed-routes.md`. Window tests of length `A` live on `[−A, 0]`;
`c_φ(t) = W(φ(· − t), φ)`.

## 1. The big picture

### 1.1 Two sites decide; this is AOG's Hasse–Weil theorem and the classical smoothed PNT
RH ⇔ `|c_φ(t)| < Q(φ)` for every nonzero bump and `t ≠ 0` ⇔ every two-site lattice window is positive
definite; off RH a short spectrally generic bump has `|c_ψ(s)| = Q(ψ)` at some step [L: GWZ
`RHIsDecidedOnTwoSites`]. The proof runs through AOG `riemannHypothesis_iff_hasseWeil_of_generic` [L]:
the statement is the lattice form of the Hasse–Weil criterion for one generic orbit, which also decides
by eventual boundedness, with growth rate the zero width [L]. For ordered tests the archimedean
coupling is the trivial divisor, `2cosh(x/2) − ω(x) = e^{x/2} − Σ_{k≥1}e^{−(2k+½)x}` [L: CSTW], so [D]

`c_ψ(t) = A(ψ)B(ψ)e^{t/2} − Σ_k μ_{−2k}(ψ)ν_{−2k}(ψ)e^{−(2k+½)t} − Σ_n Λ(n)n^{−1/2}(ψ⋆ψ)(t − log n)`,

and the two-site band is the `ψ⋆ψ`-smoothed prime count on `[e^{t−2r}, e^{t+2r}]` matching its main term
`A B e^{t/2}` within `Q(ψ)`: the classical square-root form of RH. Consequence: stages, collars and
interiors are not needed to decide RH; they are candidate proof mechanisms (P1). The decisive object
supplies no new leverage of its own.

### 1.2 The canonical system of the tower is classical Szegő–Levinson theory
Weil sequences `κ(d) = c_φ(dh)` are Toeplitz data; PD ⇔ Schur parameters in `(−1, 1)`; margins
`E_n = Q(φ)∏(1 − γ_k²)`; the newest datum enters `β_n` linearly; one prime kick moves one Schur
parameter; positive windows have outer predictors; degenerate windows are finite curves; under RH the
spectral measure is atomic (Szegő singular, margins `→ 0`); the `n`-th margin is born at order `h^{2n}`;
there is no unnormalized continuum limit [L: GWZ]. The continuum canonical system (a Hamiltonian
carrying the prime kicks) is not constructed.

### 1.3 The stage step is exact and carries no sign
Stage criterion `2wc_H(ℓ) ≤ S^N_A(H) = inf_{interior}Q_N(H + h)`; the kick is the collar Rosati pairing
`c_H(ℓ) = ∫_L H·(σ_AH)∘R`, a positive source on even–antisymmetric and odd–symmetric collar data; the
frozen two-collar form is explicit (trivial-divisor moments + earlier-fold transports); window growth is
a translation contraction and each stage a Carathéodory disk [L: GWZ, CSTW]. The frozen form is
indefinite on `[−21/20, 0]` (`#frozen-gamma-cubic`), so the kick must be a positive source at the first
prime.

### 1.4 The complete family: every layer below the sign is size-only
Subcritical PD below `(log N)^{1/8}` [L: CACT]; every twisted direction at the critical curve is a
positive count; Weil's form sits at the pole `u = 0` of the frequency counts; one small critical
multiple pays every fixed family by the aperture-independent floor `Q ≥ −C(p)∫e^{−pu}H²` [L: AHD,
WTZ]. These are blind: aliasing masks negative `Q` (`#fixed-packet-bulk`), twisted layers are
zero-blind (`#twisted-horizon-blindness`), no uniform Gram floor exists along growing overlaps
(`#growing-overlap-floor`). HF's sign content is Weil's form on untwisted windows of radius `½log K`.

### 1.5 PM is the zero side
`Q(H) = 2Re[𝓦_AH, 𝓦_AH]` exactly on `ℓ²(upper Mayer resonances)`, reflection `ρ ↦ 1 − ρ̄` [L: RIT].
`T_p − Id` is the Mellin translation `√pH(· + log p)` for every prime; its Krein similitude factor `p`
is the translation invariance of Weil's form [L/D]. Bounded Cauchy reflection exists only for
`Re s ≥ ¼` (`#cauchy-reflection-order`); the closed reflection carries no sign; the physical cusp
energy of finite packets has renormalized mean equal to the Krein square, and counterterm subtraction
does not preserve positivity [L; frontier PM row].

### 1.6 Counts, Hodge index and degeneration are closed as an RH mechanism
The archimedean domination question at the first fold has answer No: bare domination ⇔ `Q ≥ 0`; no
Gamma–pole family dominates the Tate counts; the pole weight is pinched to `1/ζ(1+k)` and refuted
(`#tate-domination`, `#tate-count-selector`; ATD, DZG [L]). The Taylor coefficients of `J_k` at `k = 0`
are Bombieri's `Λ_j`, so a count-based positivity must beat parity at first order. Every concrete count
type is excluded as an independent sign producer (`#bidegree-counts`, `#definite-counts`,
`#siegel-majorant`, `#isotropic-poisson`, automatic arithmetic RR, `#fold-count-identity`, `KR-WIP`).
Conclusion [D]: the count/Hodge/degeneration programme cannot close RH. The two-site Gram has the shape
of Weil's Hasse–Weil inequality for the diagonal and the Frobenius graph (Frobenius at scale `t` =
translation by `t`), but the 𝔽_q mechanism that proves it — Hodge index from Riemann–Roch counts — is
the closed one; no corpus result exempts rank-2 spans.

### 1.7 Selection and minimal input
Selection after positivity is automatic (Weil cone `{Λ}`; lattice selection of `Λ`) [L]. A positive
measure with Riemann's functional equation is the counting measure of `ℕ`, and a discrete Beurling
system with it is the rational primes [L: APD]; positive prime measures with integers more regular than
`ℕ` allow zeros at any `Re s ∈ (½, 2/3)` [L: RHTower Beurling]. Euler-log discrepancy absolutely
convergent at `σ = ½` determines a full Selberg function; degree in `(0,1)` is empty [L: SEL]. A proof
must use the functional equation together with the Euler product.

### 1.8 Precision and density
Near-line density is one statement in eight forms; `D_win` ⇔ thin Planck shadows; `D_zero` ⇔ `D_win` +
vanishing giant-cluster tails; double-log stage unconditional; bounded right ports ⇔ local critical-line
purity [L: CDG]. One cyclotomic mode carries `2Θ` [L: CAF]. Density statements are sub-RH and cannot
exclude density-zero exceptional sets.

### 1.9 What is ruled out
| Mechanism | Verdict | Anchor |
|---|---|---|
| Fold paid as a cost (exit charge, collar loan, transfer criterion `wE_φ ≤ Q_N`) | refuted at the first prime | `#frozen-gamma-cubic`; WTZ, DZG [L/D] |
| Sign-blind ground-state certificates (Barta, Picone on `|c_n|`) | cannot certify frozen-negative tests | WTZ [L/D] |
| Markov ground states | no cofinal Markov passage; full folded calibration fails at `a = ½log 2` | `KR-BD`, `#folded-markov` |
| Lossless local allocation; shifted ground-state combinations | refuted | `KR-LGP`; ACT [L] |
| Finite-square / finite-rank identities and realizations | refuted | `#fold-count-identity`, `#finite-window-realization`, `KR-FPR`, `#finite-virtual-realizations` |
| Slack (uniform floors, lattice slack, uniform Gram floors) | refuted | `KR-PAF`, `#lattice-positive-slack`, `#growing-overlap-floor` |
| Counts / Tate domination / Hodge index from counts | closed [D] | 1.6 |
| Size-only layers as Weil information | blind | `#fixed-packet-bulk`, `#twisted-horizon-blindness` |
| Interior-gap continuation | not structural | `#lattice-interior-gap` |
| Bounded operator symmetry for the PM reflection off `Re s = ¼` | refuted | `#cauchy-reflection-order` |
| Linear Serre–Krein isometry; Krein self-adjointness ⇒ positive projections | refuted | `#window-krein-reflection`, `#mayer-krein-sign` |
| Resonant-state selectors; contractive scattering; recentering | refuted | `#resonant-cutoff-gram`, `#scattering-schur`, `#scattering-recentering` |
| Measure-rigidity direction on the PM side | tested: rate retained, not selected; lands on B39 and the window Frobenius wall | review-0211 §2.4 |
| Selectors without positivity; regular integers | blind | Γ16; RHTower Beurling [L] |
| Producers below parity (integrality alone, fixed stencils, Adams multiplicity, sup-norm certificates) | refuted at their stated scope | rows in "Geometry, analytic tests" |
| Fixed-aperture / finite-horizon positivity as a decision | refuted | `KR-CRT`, `#finite-readings` |

### 1.10 The live paths
| Class | Statement | First test | Status |
|---|---|---|---|
| P1 signed criticality | exact signed stage payment, retaining reflected energy and the pole's negative square | odd unit window `[−½, ½]` (one first-moment direction open); first prime stage `A < log 3` | live; raw positive folded supersolutions fail for nonnegative decaying profiles [L: ACT origin law] |
| P2 prime-blind positivity | archimedean + pole part `≥ 0` on signed combinations of autocorrelations vanishing on `±log ℕ_{≥2}` | finite-level cones `C_A`, `A ≤ log 6` | live; solved on nonnegative and separated-bump cones; heuristic against finite-level slack [D] |
| P3 PM reflection | arithmetic `D_s ≥ 0` on resonances | — | reduced to the zero side; no candidate mechanism |
| P4 square-root cancellation | `c_ψ(t) = O(1)` for one smoothed short-window prime sum | — | live; classical; parity barrier for sieve-type producers |

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Explicit constants and horizons (eighth-root theorem, `1/9`, logarithmic profile, Beurling schedule, horizon criterion) | HF, SRT, AIP, ACS, SC | effectivization |
| A2 | General profiles past `θ = 1/1080` | HF, SRT, SC | tilted-spline template |
| A3 | Joint twist families; equal-parity character coupling; different moduli | HF, SRT, AHD | single-family proofs are templates |
| A5 | Certified first prime stage `[0.7243, log 3)` and second-stage certificates | RW, OWU, EWU, GWZ, CWS | finite computation (not a mechanism) |
| A6 | Odd unit window: last first-moment direction (exact target for the logarithmic reflection operator; the fixed polynomial chord cannot pay it) | OWU, RW, WTZ | rank-one problem on a fixed window; all other charges paid |
| A7 | Rational Hecke graphs and Tate horizons of stages 3, 4, 5, 7, … | WTZ, CWS | finite graphs |
| A8 | Closed-form first-stage two-collar complement `Φ_ε` | GWZ, CSTW, WTZ, RW | explicit archimedean Schur complement; dependence proved |
| A9 | Window index as a function of the length | AHD, SRT, CWS | conditional calculus |
| A10 | Function-field calibration | AHD, ACS, SC, HF | the sign is known there |
| A11 | Integration: CACT far reserve [U], log-free residuals [W]; AHD near-pair rows [U]; SEL degree-one modules [U]; LI, SZ, HKT, AKLT, ALG, AGT, ACP | HF, AIP, ACS, LI, SZ, SC, MC | statements in place |
| A12 | Gaussian-damped coupling identity | SC, ACS | explicit formula |
| A13 | PM classical identifications | PM, W1C | known theories |
| A14 | Operator-native nonvanishing on `Re w = 1` | PM | Eisenstein template (risk: reduces to the Euler product) |
| A16 | Theta Hankel rank 8 strict; ranks 9–10 | TH | finite computation |
| A17 | Hausdorff shifts, Jensen horizons, two-grid degrees, PF beyond 37 | PA, LA, HCF | effectivization |
| A18 | Nine atom-dominated collar moduli | ACT | finite case analysis |
| A19 | Mixed Schur debit; first-prime/coarse/polar costs | AIP, CHMD | fixed-dimensional estimates |
| A20 | Logarithmic two-point Chowla | MC | Tao's theorem |
| A21 | Björner wedge decomposition | MC, HF | classical topology |
| A22 | Depth law, star horizons, gcd strata | HF, ACS | effectivization |
| A23 | Census items | census, ACS | classical |
| A24 | Voronoi; Zwegers | ACS, HF | classical |
| A25 | Künneth primitive `h¹` at small degree; mixed jets | ACS, WL | calibration |
| A26 | WD composition | WD, LA, TG | composition |
| A27 | Cluster-detector constant | SRT, WD | constants |
| A28 | Finite-level Weil cones `C_A` and their widths (the P2 first test) | PBAP, ACS, RW | finite convex programs, Farkas duality in place |
| A29 | Atomic-lattice bound | WTZ, HF | classical |
| A30 | Full-space positivity at one small critical multiple (blind) | HF, AIP, SRT, CACT | assembly of [U]/[W] pieces (difficulty unverified) |
| A31 | Quantitative conductor range `M(N) = o(c_N)` | HF, SRT, AHD | uniform versions of proved limits (difficulty unverified) |
| A33 | Bridge module: two-site entry = ordered coupling = WL receiver | WL, JAS, CTF, PBM, RB, GWZ | composition of proved identities |
| A34 | Two-site band on a bounded step range from numerical zero data | GWZ, WL | computation; decides nothing |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on windows of every length (≡ two-site band ≡ lattice Schur parameters in `(−1,1)` ≡ translation contraction ≡ fold capacity ≡ horizon criterion ≡ Beurling schedule ≡ `ι(A) = 0` ∀A ≡ Krein positivity of zero coordinates ≡ PBAP) | RH; fixed length sub | all sign routes |
| B2 | Kick admission at every prime-power stage | RH as induction; each stage sub | RW, GWZ, CSTW, WTZ, HF |
| B3 | Signed criticality: an exact signed certificate at every length, including reflected and pole charges | RH; fixed length sub | P1 routes |
| B4 | Twisted-sector positivity through all conductors and frequencies at every multiple | sub | HF, SRT, AIP, AHD |
| B6 | Full-space positivity of general profiles past `log log N` | sub | HF, SRT, AIP, SC |
| B7 | Exact SOS on one two-prime lattice | RH | HF, SC, ACS |
| B8 | No zero mode at any length | RH | HF, TG, SC, EHT, GWZ |
| B9 | Top coprime stratum | RH | HF, ACS, ADT |
| B10 | Index ceiling uniform in resolution | ≥qRH; RH (tensor) | CHMD, SRT, WD, SC |
| B11 | Zero–one law `κ ∈ {0, ∞}` | sub | SC, HF, ACS, CWS, SRT |
| B12 | Laguerre–Pólya | RH | TH, LA, HCF, PA, GTA |
| B13 | Scheduled prime energies | RH | FU, CFC, RP, SZ, LI, FEL, EGC |
| B14 | Growth exponent of window negativity | ≥qRH (`< ½`) | window routes, WD |
| B15 | Cross-tower gap through the archimedean channel | method | HF, AIP |
| B41 | Continuum canonical system of the tower (lattice version solved; continuum coalesces) | identity | GWZ, CSTW, SZ |
| B43 | Contact law: RH to height `T` ⇒ windows to length `c log T` (survivor of `KR-CRT`) | sub | window routes |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B16 | Inner caps `[½, σ_m]` at every polynomial stage | RH; fixed degree ≥qRH | WD, TG |
| B17 | `100%` critical-scale clustering | sub | WD, census, MC, HEF |
| B18 | `D_win` ≡ thin Planck shadows; `D_zero` | sub | WD, census |
| B19 | Hecke defect pointwise / dyadic | ≥qRH / RH | WD |
| B20 | Distributional input beyond counts and moments | method | WD, HEF |
| B21 | Count-valued primitive `h¹` — closed as a mechanism (1.6) | RH | ACS, HF, IRK |
| B22 | Genus upper law | indep. | ACS |
| B23 | Logarithmic Serre duality, primitive part | sub | ACS, HF |
| B24 | `ε`-uniform producer; square-root source input | sub / RH | WL, MC, PBM, RB, JAS, CTF |
| B25 | First cyclotomic mode at square-root precision | RH | MC, WL, CAF |
| B26 | Signed pair information beyond bandwidth one | sub | census, ACS |
| B27 | First Epstein real zero on the boost line | sub | ACS |
| B28 | Bounded damped cone coupling; unattained width | RH | SC, ACS |
| B29 | Finite-sieve Hodge positivity → global | RH | SC |
| B42 | The two-site band (= B1 in the classical P4 form) | RH | all |

### Γ — selection and reflection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B30 | Rosati positivity of the window reflection | RH | HF, ACS, CWS, GWZ, PM |
| B31 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH | HF, ACS, SC, PM |
| B32 | Selection at the trivial gauge point | RH | MC, BAG, XN |
| B33 | FE twins inside the full class with off-line zeros | sub | HF, ACS, SC, SEL |
| B34 | Arithmetic `D_s ≥ 0` on resonances | RH | PM, W1C |
| B35 | Resonant-state statistic selecting the decay rate | method | PM |
| B37 | Gaussian-packet physical residue (height-uniform cusp bounds); counterterm does not preserve positivity | identity | PM |
| B38 | Pre-divisor forcing | RH | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |
| B39 | Source-faithful realization of unbounded rank | RH | RN, PTR, W1C, PM |
| B40 | Prime-blind positivity on signed blind combinations | RH | PBAP |

### Settled questions (classified; not obstacles)
| Question | Answer | Anchor |
|---|---|---|
| Can an archimedean family dominate the Tate counts at the first fold? | No; counts/Hodge/degeneration closed as an RH mechanism | ATD, DZG [L]; 1.6 [D] |
| Is the complete family positive on every window at one fixed critical multiple? | Yes for every fixed family, by a size-only floor; no Weil information | WTZ, AHD [L] |
| Is the untwisted window a positive Tate piece? | No: Weil's form sits at the pole of the frequency counts; the untwisted count is the finite part | AHD [L] |
| Is there a bounded operator identity for the PM reflection across the strip? | Only for `Re s ≥ ¼`; a closed densely defined reflection survives and carries no sign | RIT [L]; `#cauchy-reflection-order` |
| Is Weil energy exactly a PM Krein form? | Yes: `Q = 2Re[𝓦H, 𝓦H]` on `ℓ²(resonances)`; Hecke = translation | RIT [L] |
| Does the interior of a window carry the decisive failure? | No: two sites decide | GWZ, AOG [L] |
| What is the two-collar recursion? | Levinson's recursion on lattices; Carathéodory disk in the continuum; no unnormalized continuum limit | GWZ, CSTW [L] |
| What does the archimedean place transmit across a prime-free separation? | Only the moments at the trivial divisor | CSTW [L] |
| Is no-slack structural? | Yes: Szegő singular under RH | GWZ [L] |
| Is interior-gap continuation structural? | No (three-angle curve); not needed | GWZ [L] |
| Is the conductor decomposition uniform on a growing range? | Yes on some `M(N) → ∞` (nonquantitative); the count form ends at the resolution | AHD [L] |
| Do regular integers and positive primes decide the zeros? | No | RHTower Beurling [L] |
| What do the functional equation and positivity determine? | `ζ` | APD Hamburger [L] |
| Does the window algebra contain a Frobenius? | No; Frobenius at scale `t` is translation | DZG, RIT [L] |
| Does positive dimension supply positivity? | No | ATD, DZG [L] |

## 2.3 Frankenstein routes

**Verdict: no assembly closes RH.** Every assembly ends at the two-site band; the assemblies differ in
which mechanism they offer for it.

### F1. The tower assembly (P1; recommended)
| Segment | Supplied by | Status |
|---|---|---|
| RH ⇔ window sign; locality `n ≤ e^A`; two sites decide | CWS, GWZ, AOG | [L] |
| Window algebra; stages; Hecke-graph reading | WTZ | [L] |
| Base: all real `C²` tests positive through `181/250`; first stage opens positive to `181/250` | SPATL, GWZ | [L] |
| Stage criterion; kick = collar Rosati pairing; frozen form in closed form; Carathéodory disk; Levinson admission | GWZ, CSTW | [L] |
| Odd unit window off one first-moment direction; exact retained-Gamma identity; strip coercivity | WTZ, LST | [L] |
| Conditional odd supersolution criterion; nonnegative decaying profiles excluded by the origin jump-moment law | ACT | [L] |
| Core: exact signed stage step in every stage | — | B2, B3 (RH) |

It bypasses conductors, dimension zero, counts, density and PM. It does not bypass exactness, and every
shortcut in 1.9 (cost-only, sign-blind, Markov, finite identities, slack) is excluded at its core.
The ACT criterion is sufficient, not an existence theorem: for `ω=M/Φ`,
`(𝓛_Nω−Φcosh(x/2)ω)/Φ→−2∫M dm` at zero. A nonzero nonnegative decaying `M`
has positive jump-measure moment. This excludes that construction, not signed stage payment.

### F2. The complete-family assembly (blind)
Subcritical PD (CACT) + critical decomposition (AHD) + aperture-independent floor (WTZ) + far reserve
(CACT [U]) → full-space positivity at one small multiple (A30). It is sub-RH and carries no Weil
information (`#fixed-packet-bulk`); for RH it lands on B1 on untwisted windows at large multiples.

### F3. The reflection assembly (P3)
PM exact completion + window involution + collar Rosati pairing [L]. Residual: Krein positivity of the
zero coordinates (B34), i.e. RH, with no candidate mechanism (1.5).

### F4. Density–index–cluster (WD ⊕ AHD ⊕ CWS ⊕ AKLT ⊕ SRT)
Off-line zeros live in density-zero window sets, are seen at aperture `≍ log|γ|log log|γ| + 1/δ`, each
raising the window index [L]. Residual: index ceiling and zero–one law (B10, B11): ≥qRH.

## 2.4 A wildly different route

**Verdict: the prime-blind, existence-first route (P2) remains the one route far from the others; it
meets Σ in a form with no primes.**

- Facts [L]: every real weight with full Weil positivity is `Λ`; the Weil cone is nonempty iff the pole
  and archimedean part are nonnegative on positive combinations of autocorrelations vanishing on
  `±log ℕ_{≥2}`; RH ⇔ prime-blind positivity; node-critical (every prime power needed, composites free);
  finite-level Farkas duality; zero-side identity on blind tests; solved on nonnegative and
  separated-bump cones; at each level the Weil cone `C_A` is compact and RH ⇔ `C_A ≠ ∅` ∀A.
- Why it is far: no von Mangoldt value is estimated (no Π), selection is a theorem (no Γ); the integers
  enter only as the zero set `±log ℕ_{≥2}`.
- Walls it meets: on blind tests the archimedean–polar functional is the zero sum, so the open part
  (signed blind combinations, B40) is zero-side positivity on the blind cone (Γ8); the near-null space
  of a window has dimension of order `e^{2A}` against `≈ e^A` annihilator constraints, so finite-level
  certificates are expected to have no slack [D, heuristic]. Two-site blind tests exist only at steps
  avoiding every `log n` within `2r`, i.e. at small steps [D]: the two-site reduction does not transfer
  to the blind cone at large scales.
- First test: A28 (compute `C_A` and its width around `Λ` for `A ≤ log 6`); it decides whether finite
  levels carry freedom.

The measure-rigidity direction is tested on the PM side and lands on B39 and the window Frobenius wall
(review-0211 §2.4); no other route outside the four classes of 1.10 is identified.

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — positivity of the first prime stage by a signed certificate
**Question.** Prove Weil positivity on every window of length `< log 3` by a certificate of unbounded
rank in which the kick of `2` enters with its sign: close the odd unit window (A6), compute the
first-stage complement `Φ_ε` (A8), and prove `S^1_A(H) ≥ 2w₂c_H(log 2)` for all `A ∈ [log 2, log 3)`.
- **Below RH.** A finite window; margins `5.6×10⁻⁸` (even), `1.5×10⁻⁵` (odd) at half-width `½log 3` [N].
- **Not ruled out because.** The excluded shortcuts at this stage are cost-only payments
  (`#frozen-gamma-cubic`), finite-square identities (`#fold-count-identity`), sign-blind ground states,
  full folded calibration (`#folded-markov`) and the fixed polynomial chord (`#first-fold-linear-chord`);
  a signed certificate of unbounded rank is none of these.
- **Advance.** The first window beyond `181/250` where a prime must act as a positive source; the base
  case of every P1 mechanism.

### 2.5.2 Route PM — a zero-free region from the Lewis–Hecke carrier
**Question.** From the Lewis–Hecke structure alone — three-term equation, modular inversion, Hecke
eigenrelations `T_{p,s}ψ_s = (1 + p^{1−2s})ψ_s` for every prime, positivity of the Hecke-cone operators
at real parameters, boundary charges — prove that no Mayer resonance lies on `Re s = ½` and then a
de la Vallée Poussin-type region `Re s ≥ ½ − c/log|Im s|` for `ζ(2s)`.
- **Below RH.** A PNT-strength statement.
- **Not ruled out because.** The killed PM mechanisms are line selectors (Lewis inversion, three-term +
  inversion, resonant statistics, contractive scattering, Krein projections); none concerns a
  zero-free region. Risk: the cone counting that produces the eigenvalue `1 + p` is the Euler product
  (A14), so the argument may reduce to the classical one.
- **Advance.** It would be the first sign statement PM owns; every other PM sub-RH item is an identity
  (B37) or a blind positivity.

### 2.5.3 Route WD — log-free window occupancy
**Question.** Prove `D_win`: for every `A > 0` the number of unit windows `[t, t+1] ⊂ [V, 2V]` containing
a zero of depth `≥ A/log V` is `≤ ε(A)V`, `ε(A) → 0`; equivalently, thin Planck shadows occupy
`o_A(V)` unit windows.
- **Below RH.** A density statement.
- **Not ruled out because.** Volume and moment bounds are excluded as inputs (`#window-density-separation`,
  clustered and sparse models [M]); the statement itself is open.
- **Advance.** WD's one analytic input at the log stage; unconditionally one `log log` short.

### 2.5.4 Route HF — HF has no sub-RH question with sign content of its own
Every HF layer below the sign is blind (1.4). At a fixed multiple `K`, HF's sign content is Weil
positivity on untwisted windows of radius `½log K`: the window problem of RW at matched length.
- **Best structural question.** Full-space positivity at one small critical multiple (A30): it closes
  the eighth-root endpoint for small `K`, makes the pencil index start at zero, and leaves the
  continuation in `K` as the only HF obstacle. It is blind and carries no Weil information.
- **Not to be pursued.** Uniform floors along growing overlaps (`#growing-overlap-floor`), bare counts
  through all conductors (`#conductor-count-resolution`), collective quasimodes as lower bounds (frontier
  map), a count for the untwisted window (1.6).

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — signed window criticality
**Question.** For every window length, prove the exact signed stage payment, retaining the reflected
prime contribution and paying the pole square. Any transformed generator must come with an exact
energy identity and payment of its remaining signed terms.
- **Why it opens the path.** All-stage payment implies all-window Weil positivity and hence RH.
  `riemannHypothesis_of_foldedSupersolution` is only a sufficient criterion: its raw Neumann-folded
  generator has no nonzero nonnegative decaying profile supersolution near zero.
- **Constraints from the corpus.** Markov passage fails cofinally (`KR-BD`); full calibration fails at
  `a = ½log 2` (`#folded-markov`); every nonzero nonnegative `C¹` profile with
  `|M|,|M'|≤Ce^(−8|x|)` fails near the origin and at infinity (ACT
  `FoldedSourceOriginJumpMomentLaw`); Barta/Picone weights are sign-blind. The construction must use the signs of
  the folds, eliminate negative folded conductances (variable-hub Schur survives), and pay the pole's
  one negative square. Under RH margins collapse (Szegő singular), so `ω` is a critical, not
  subcritical, ground state.

### 2.6.2 Route PM — finite cusp energy forces zero defect
**Question.** Prove `∫_1^∞|ψ(2a) − 2^{1−2s}ψ(a)|²da/a < ∞ ⇒ D_s(ψ) = 0` for Lewis periods.
- **Why it opens the path.** Finite cusp energy ⇔ resonance and `D_s = 0` ⇔ `Re s = ¼` [L]; it is RH as an
  implication between two explicit quadratic functionals of one function. The exact completion
  identifies PM's Krein form with Weil's form [L]; the missing input is arithmetic, and no mechanism for
  it is known (1.5).

### 2.6.3 Route WD — inner-cap cancellation
**Question.** On every Burnol unit window, at every polynomial stage, cancel the right-port flux through
the inner caps `[½, σ_m]` by a source identity.
- **Why it opens the path.** Across all degrees it is RH; at fixed degree the corridor
  `|β − ½| ≤ C/|γ|^k` [L]. Everything else in WD is an equivalence.

### 2.6.4 Route HF — the pencil index stays zero
**Question.** Prove that the pencil index of the complete family is zero at every critical multiple.
- **Why it opens the path.** The index is monotone in `K`, zero for `K ≤ K₀` [L], and changes only where
  a weighted zero mode appears; its vanishing at every `K` is B1. HF supplies no mechanism of its own
  for this; its sign content is P1 on untwisted windows.

## 2.7 Does closing RH need a new field?

**Assessment: yes — a signed arithmetic criticality theory of the window tower.** Its dictionary exists
(GWZ, CSTW, WTZ, DZG, ACT): stages, collars, the kick as collar Rosati pairing, trivial-divisor
transmission, frozen forms in closed form, translation contraction, Levinson recursion, outer
predictors, Szegő singularity, zero-mode parity, the odd supersolution criterion. Its core is open, and
the corpus has fixed what the core cannot be.

*What it is about.* Positive ground states of nonlocal Schrödinger-type forms on growing intervals whose
jump part has positive archimedean rates and arithmetic jumps of length `log n`, whose potential carries
the pole's hyperbolic pair, and which are critical (zero ground energy in the limit) rather than
subcritical.

*What it would be like.* Exact and signed: positivity by identities of unbounded rank in which each
fold's sign is used; never Markov (Beurling–Deny fails cofinally), never sign-blind, never finite rank,
never with slack.

*Criteria it must meet.*
1. Reproduce the base `181/250` and the first prime stage, where the frozen form is indefinite.
2. Pay the pole's single negative square (the hyperbolic pair `e^{±h/2}` on lattices).
3. Be critical: margins tend to zero along every lattice under RH; the ground state degenerates in the
   limit.
4. Deliver the two-site band at every scale (two sites decide).
5. Force `Λ` (Weil cone `{Λ}`, lattice selection) and fail for flips, Euler twins, `ζ(s)ζ(s−ε)`,
   Epstein and golden data.
6. Use the functional equation and the Euler product together (Hamburger, Beurling).

*Questions it must answer.*
- Does the first prime stage admit a complete signed certificate (2.8)?
- How does a signed certificate pass a stage: which collar correction absorbs the kick, given that the kick is
  a positive source exactly on even–antisymmetric and odd–symmetric collar data?
- What replaces Allegretto–Piepenbrink for forms whose jump part is Markov but whose full form carries
  a rank-two indefinite pole term?
- What is the Agmon ground state of a critical (Szegő-singular) window, and how does its shape at the
  collars relate to the zero modes of a hypothetical first failure (two-site, single angle)?

*Tools.* Criticality theory for nonlocal operators (Keller–Pinchover–Pogorzelski), with signed
perturbations; variable-hub Schur elimination of negative folded conductances [L]; packed nonlocal paths
and signed supersolutions (`KR-LGP` survivor); Doob transforms; Levinson/Szegő theory of Weil
sequences [L]; the trivial-divisor moment calculus [L]; regional logarithmic Laplacian with Legendre
spectrum `2H_n` [L].

*Objects.* Folded generators, supersolutions `ω`, sinh capacity, collar classes, frozen two-collar
forms, Schur parameters, outer predictors, zero modes, the pole's hyperbolic pair.

*Explicitly outside the field.* Counts and Hodge index (1.6); Tate domination; Markov ground states;
measure rigidity on the PM side (tested); PM operator symmetry off `Re s = ¼`.

## 2.8 The one question

**Can the complete odd unit-window form be proved nonnegative by a signed certificate retaining
prime two, the Gamma remainder and the pole?** The unit window has length
`1 ∈ (181/250, log 3)`. Its frozen form is indefinite and only prime two acts.

*Why it is less hard than RH or quasi-RH.* One window, one prime, the odd sector: a finite,
explicit problem. Odd positivity on this window is within one first-moment direction of being proved
(`Q + (3203/320)(∫xF)² ≥ ‖F‖²/1000` [L]); the question asks for the mechanism, not for the numbers.

*Precise boundary.* The raw positive folded-supersolution proposal is excluded for nonnegative
decaying profiles by ACT's origin jump-moment law, including compact profiles. Removing negative
conductances changes the operator; its exact remainder still needs payment. This obstruction does
not exclude the complete Weil form. The two-moment logarithmic reflection target is refuted:
a smooth odd unit-window test has `P+E/64<0`, hence `D<0` [WTZ
`exists_odd_unit_firstFoldTwoMoment_neg`; individual Lean and standard-only axiom audit].
The stronger proved reserve is
`Q≥P+(193/10000+17/23040)E+(13/3840)(∫xF)²`.
Higher lag terms repair the same smooth direction: `P+E/64<0<Q`
[WTZ `exists_odd_unit_reservedGamma_neg_weil_pos`; individual Lean and standard-only axiom audit].
Complete odd unit-window positivity remains open.

*Why the answer tells where the proof must be.*
- A proof would advance the odd base case; the even sector and the remaining prime stages would
  still require independent payment.
- Failure of a particular lower form or supersolution does not retire P1. It identifies terms
  that the next exact signed certificate must retain.
