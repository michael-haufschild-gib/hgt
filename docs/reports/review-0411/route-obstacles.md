# Route obstacles — status quo

Scope: the 32 live routes and 17 candidates of the frontier map and the programmes that feed them,
read against the Lean corpus at `3374f0b7c6` plus the working tree. For every route: path, what is
established, the open estimate, the mechanism class, the obstacles that are **(A) just work** and the
obstacles that are **(B) open mathematics** (no known solution).

Evidence: `[L]` committed Lean; `[W]` Lean in the working tree (being formalized); `[S]` Lean module
marked unfinished in the frontier map; `[P]` paper proof on a pipeline card, not yet formalized; `[D]`
derived here from Lean statements; `[M]` exact model statement; `[N]` numerical. Strength: **RH**; **≥qRH** (zero-free half-plane or Lindelöf); **RH-adj.** (a
zero-location statement, neither RH nor sub); **sub** (strictly below quasi-RH); **indep.**;
**identity**; **method**. An A item is known mathematics, finite computation, effectivization or assembly
of proved pieces; `(difficulty unverified)` marks A items whose difficulty is not established.

Notation. Window tests live on `[−a, a]` (half-width `a`) or half-windows `[−c, 0]`; `W` is Weil's form;
`w_n = Λ(n)n^{−1/2}`. For `f` left of `m` and its mirror `f∘R`, `R(v) = 2m − v`, the **coupling** is
`𝒞_m(f) = 𝓗_m(f) − Σ_n w_n(f⋆f)(2m − log n)` with the collar Hankel form `𝓗_m`. The **band** is
`|𝒞_m(f)| ≤ W(f)`. A lag `ℓ = log n` sees a half-window test only on its **sliver** `[−c, c − ℓ]`, width
`δ = 2c − ℓ`. For a zero configuration `Z`, `WindowPositiveAt Z a` means `Re W_Z(f,f) ≥ 0` for every `C²`
test supported in `[−a, a]`; the **onset aperture** `a*(Z) ∈ [0, ⊤]` is the supremum of such `a`.
`a*(ζ) := a*(zetaZeroConfig)`. `pairEnergy(δ, a) = sinh(2δa)/(2δ) − a`. `L_T = ½log(T/2π)`.

## 0. Mechanism classes

| Class | Mechanism | Status | Anchor |
|---|---|---|---|
| P1 | **Signed criticality.** In a gauge `F = Φωu` the window form is a signed Dirichlet form plus pole charges; primes pay the prime-free archimedean–polar deficit through the sign of their sliver reflections; pole variance retained | live; every P1 statement is a lower bound for `a*(ζ)`; below `log 4` exactly a two-number convex membership; positivity-preserving (Perron/Markov) structure ends at `c = log ρ` | SWC, ACT, WTZ, GWZ, CSTW, WVL [L] |
| P2 | **Prime-blind positivity.** Archimedean + pole part `≥ 0` on signed combinations of autocorrelations vanishing on `±log ℕ_{≥2}` | live; solved on nonnegative and separated-bump cones; node-critical | RHTower PBAP [L] |
| P3 | **Reflection positivity of PM.** Krein positivity of the completed resonant space | reduced: the co-isometry defect of a resonance is `−∫2cosh(δu)·4sinh²(δu)|F(u)F(−u)|`; its sign is `δ = 0` itself | RIT [L]; [D] |
| P4 | **Square-root cancellation** of one smoothed short-window prime count: the band in prime form | live; classical; parity barrier for sieve-type producers | GWZ, SWC, CSTW, AOG [L] |
| P5 | **Reality by continuation.** Real-rootedness closed, lost only through collision; RH from a source-faithful collision-free path | live as a receiver; size information reaches heat time `½/log X` and no lower; in the pair model every depth `≤ ½` collides before `½/log X` | ZCG, RHTower DeBruijn, LA, TH, HCF [L]; [D] |
| — | Counts / Hodge index / degeneration | closed as an RH mechanism [D] | S3 |
| — | Size-only layers (subcritical regime, one critical multiple, twisted sectors, bulk, terminal windows, aperture-independent floor, simultaneous receiving) | true and blind [D] | S1 |
| — | Identification without sign (camera of the explicit formula) | complete at the square-root aperture up to near-coincidences; sign-free | S10 |
| — | Window visibility (onset laws) | classified in models; converts window sign into zero location | S11 |

Closed mechanism families (anchors in `rh-killed-routes.md` where they exist):
- **Positivity-preserving certificates:** bare and compact folded Markov supersolutions
  (`#prime-free-markov`), calibrated folded-Markov conductance (`#folded-markov`), cofinal Markov passage
  (`KR-BD`); Beurling–Deny comparison of the even band beyond `c = log ρ` at every pole strength `s ≥ 1` and
  all prime weights [L]; robust Perron margins beyond the pole-saturation gap [L].
- **Cost-only and sign-blind payment of a fold:** `#frozen-gamma-cubic`, `#retained-gamma-lower-form`,
  `#first-fold-linear-chord`, `#prime-three-sliver-potential`.
- **Ground states without the pole variance:** `#variance-dropped-theta-gauge` (`c > 273/400`),
  `#theta-gauge-cosh-defect`, `#folded-origin-charge`, `KR-LGP`.
- **Collar locality:** `#collar-positivity-induction`, `#collar-local-payment`.
- **Smooth extremals:** `#smooth-window-attainment`.
- **Finite structures:** `#fold-count-identity`, `#finite-window-realization`, `KR-FPR`,
  `#finite-virtual-realizations`.
- **Slack:** `KR-PAF`, `#lattice-positive-slack`, `#growing-overlap-floor`, `#full-conductor-diagonal`.
- **Dimension zero and counts:** `#tate-count-selector`, `#uniform-tate-positivity`, `#tate-domination`,
  `#bidegree-counts`, `#definite-counts`, `#siegel-majorant`, `#isotropic-poisson`, `KR-WIP`.
- **Critical-family shortcuts:** `#conductor-count-resolution`, `#critical-pencil-nullspace`,
  `#low-conductor-deletion`, `#prime-pole-cost`, `#charge-complement-vanishing`, `#fixed-packet-bulk`,
  `#twisted-horizon-blindness`, `#critical-pole-collar-budget`.
- **Height-local decisions:** fixed-aperture / height-local positivity (`KR-CRT`); deciding a window from the
  zeros below any height: two tempered configurations identical on `|Im z| < exp((e^{2δa} − 2)/(4δ) − a)`
  have opposite signs at `a` [L].
- **Universal density thresholds for sign:** `πD/2` for mixed on-line/off-line column families (exact onset
  `(g − ½)ℓ > πD/2`) [L]; `λ = ½` as a general sign-hiding law (single defects collapse it) [L].
- **Domination as a ζ-selector:** finite Dirichlet carriers with arbitrary real coefficients are real and
  simple above their horizon `2πe^{W_a}` [L]; twins are tilted at every height [L].
- **Size-only heat repair:** `#heat-method-floor`; Lindelöf-bounded Riemann-density pair models collide at
  every positive heat time scale (`pairModel`) [L].
- **Producers, reflection, continuation, selection without sign:** as listed in `rh-killed-routes.md`
  (`#pole-matching-half-power`, `#cauchy-reflection-order`, `#mayer-krein-sign`, `#lewis-inversion`,
  `#farey-three-term`, `#resonant-cutoff-gram`, `#scattering-schur`, `#scattering-recentering`,
  `#lattice-interior-gap`, `#positive-model-homotopy`, `#theta-fixed-cross-load`, `#finite-readings`).

## 1. The picture

| Fact | Anchor | Consequence |
|---|---|---|
| RH ⇔ every two-site lattice window PD ⇔ `|c_φ(t)| < Q(φ)` for every bump and `t ≠ 0` | GWZ [L] | the minimal decisive object is a reflection pair |
| `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; sectors of `[−a, a]` = band at the centre | SWC [L] | the band is a smoothed prime count of `f⋆f` matching the pole square within `W(f)` |
| **Onset aperture:** on tempered configurations `WindowPositiveAt Z a ⇔ a ≤ a*(Z)`; `a*(Z) = ⊤` ⇔ all zeros on the line; RH ⇔ `a*(ζ) = ⊤`; off RH `a*(ζ) = zetaContactAperture`, attained; `a*(ζ) ≥ enlargedWeilFloorAperture ∈ (0.362, ½)` | WVL `windowPositiveAt_iff_le_onsetAperture`, `onsetAperture_eq_top_iff_onLine`, `riemannHypothesis_iff_onsetAperture_zeta_eq_top` [L] | every window route measures one number |
| `AHD.windowThreshold A = ⊤ ⇔ A/2 ≤ a*(ζ)` | WVL `windowThreshold_eq_top_iff_le_onsetAperture` [L] | HF's threshold is the onset aperture |
| **Master law** in a lattice RvM background (`2π/L`): a multiplicity-`k` pair `½ ± δ + iγ₀` is window-positive at `a ≤ L/2` iff `k·pairEnergy(δ,a) ≤ L`; deep law `2δa ≍ log(4δL/k)`, shallow cubic law `a ≍ (3L/(2kδ²))^{1/3}` | WVL `windowPositiveAt_multiplicityPairConfig_iff` [L] | windows read depth and coherence, exactly |
| General RvM: positivity at `a` (`δa ≥ 2`) forces `(5/8)(Σm)a⁵e^{4δa}/(2²⁶δ⁷) ≤ Near + Far`; unshielded clusters excluded to doubly-exponential height; the shielded barrier at depth `1/a` above single-exponential height is sharp (tapered crystal) | WVL [L] | windows exclude deep unshielded zeros only |
| The ζ instance at the base aperture needs `δ ≥ 4`: vacuous; zero information starts at `a ≥ 4` and, with present constants, `a ≳ 20` | WVL `enlargedWeilFloor_excludes_zeta_coherent_cluster` [L]; [D] | short-window sign theorems carry no zero information |
| Below `log 4`: positivity ⇔ `(Λ(2)/√2, Λ(3)/√3) ∈ belowLogFourBandWeights c`, convex, compact for `c > ½log 3`, `w₂ > 0` for `c ≥ 21/40`; retained-variance certificates exact; ⇔ Hodge index of the scaling subsurface ⇔ Künneth effectivity | SWC [L] | the first stages are a two-number problem; no certificate for `c > 0.362` exists |
| Even sector Markov (Beurling–Deny) exactly for `c ≤ log ρ`, `ρ³ = ρ + 1`; beyond, every pole strength and all weights admit `E_s(f) < E_s(|f|)`; the pole is the only anti-Markov term of the even sector | SWC PerronSignLaw [L] | certificates past `c ≈ 0.281` must be signed |
| Edge law `w_n|(f⋆f)(−log n)| ≤ (Λ(n)e^c/(2n))·levyEnergy`; `{2,3}` use `< ¾`; summed bound `< 1` exactly on windows `< log 5` | SWC [L]; [D] | primes pay by sign, not size |
| Complete Weil matrix PD below `(log N)^{1/8}` and at one critical multiple; terminal source polar; simultaneous receiving charges with vanishing physical energy | CACT, AHD, CSAR [L] | HF layers below the sign are size-only |
| PM: `Q = 2Re[𝓦H, 𝓦H]` on `ℓ²(resonances)`; defect `−∫2cosh(δu)4sinh²(δu)|F(u)F(−u)|`; off-line antisymmetric combinations have Krein square `−2` | RIT [L] | PM's line condition is an identity in `δ` |
| Camera: at aperture `λ·L_T`, `λ > 1`, equal images fix RvM configurations up to near-coincidences `< δ/log T`; `λ > ½` reads every isolated zero of ζ with its multiplicity; `λ ≤ 1` fails for disjoint carriers; near-coincident moments read `w²` to `O(r³)` with loss `e^{C log²X}` | ZCG SquareRootInversion, `NearCoincidencesAreReadThroughTheirMoments` [L] | identification is complete; it carries no sign |
| Heat: real/simple above `2πe^{(6600/9991+ε)/t}`; size-only floor `½/log(X/2π)` (Gaussian saddle); `pairModel` collides below every `τ > 0`, at `t* < min(δ²/2, δ/L)` | ZCG HeatScaleRepulsion [L] | the band left to P5 is all of RH [D] |
| Every real finite Dirichlet carrier is real above `2πe^{W_a}`; twins are tilted at every height; tilts cost weight `log(t/2π)` | ZCG [L] | domination is not ζ-specific |
| Function field: camera identifies at the genus; purity closed, lost only at Frobenius collisions; integral configurations collide or repel; curve columns certified at `a > (g − ½)log q`, sharp | ZCG, WVL [L] | over `𝔽_q` integrality supplies what ζ lacks |
| FE + positivity determine `ζ`; positive primes with regular integers allow off-line zeros | APD, RHTower [L] | a proof uses FE and Euler product together |

## 2. Shared obstacle blocks

### S0. The two-site band and reflection pairs
Routes: every route of C1, C4, C7, C14, C15, C19.

Established [L]: RH ⇔ two-site PD ⇔ strict orbit Cauchy–Schwarz; one generic bump decides; orbit
correlation rate = zero width; `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; band unconditional for short pairs; parity
sectors are the band at the centre; tight band on a nonnegative window gives a reflection-pair zero mode;
strict band on smooth tests; no smooth zero mode; every statement is a lower bound for `a*(ζ)` (S11).

| | Obstacle | Strength |
|---|---|---|
| A29 | Bridge: reflection-pair coupling = smoothed prime count → WL/JAS/CTF/PBM/RB receivers | — |
| B1 | The band at every step and every test (`a*(ζ) = ⊤`) | RH |
| B10 | No zero mode at any length | RH |

### S1. Complete Weil family at the critical curve
Routes: HF, SRT, AIP, ACT (index), ACS-atomic, SC, CHMD (index). Programmes: CACT, AHD, CSAR, ACPL, ADT,
RAPT, TM, SSHA, CAF, V.

Established [L]:
- Subcritical PD for `1 ≤ c ≤ (log N)^α`, `α < 1/8`; whole-space PD at one critical multiple with every
  window corollary.
- Window threshold `R₁(A)`; antitone; `≥ R₀ > 0`; `= ⊤` up to `2·enlargedWeilFloorAperture`;
  `R₁(A) = ⊤ ⇔ A/2 ≤ a*(ζ)`; off RH `R₁(A) < ⊤ ⇔ A > 2·contact`.
- Critical-curve second order, twisted sectors positive Hurwitz counts, frequency pole of order `β+1` with
  untwisted finite part; bulk entries along growing overlap; terminal windows with polar source,
  nontrivial kernel; conductor packets; low correctors cannot improve zero-source windows; exact polar
  capacity attained by one pole coefficient; full conductor diagonal overprices terminal windows.
- Receiving charges: capacity `log log N + O(1)`; **simultaneous fixed finite receiving vectors**: modes
  `m ∣ M` carry arbitrary charges `t_m`, complete raw energy `→ (Σt_m²)(d/a − ½)`, input norm, adjunction and
  physical energy `→ 0`; at `Q = X²`, `N = X⁴⁰` exact complementary receivers read `t_l/80`, norm² `→ 1/20`;
  cutoff `= N` leaves the complement `{0}`. Literal three-range bounds, affine short rows, Mangoldt kernel
  Grams, prime-incidence moments, V-sieve inputs.

Status: every layer below the sign is size-only and classified; HF's sign content is `a*(ζ) = ⊤`. The
far-complement estimate loses `O(c)` against its `O(log N/c⁷)` reserve.

| | Obstacle | Strength |
|---|---|---|
| A1 | Explicit constants and horizons (`K₀`, eighth-root theorem, `1/9`, logarithmic profile, Beurling schedule, conductor range `M(N) = o(c_N)`) | — |
| A2 | General profiles past `θ = 1/1080` | — |
| A3 | Joint twist families; equal-parity characters through `L(s, ψ̄₁ψ₂)`; different moduli | — |
| A4 | Certified ratio interval at its size-only optimum; assembly of the receiving complement inside it (difficulty unverified) | — |
| A9 | AIP literal channel norms made critically small with growing periods, offsets and prime bands (difficulty unverified) | — |
| A10 | Window index as a counting function of the length | — |
| A37 | Simultaneous receiving with growing mode sets and growing `M` (difficulty unverified) | — |
| B6 | Twisted-sector positivity through all conductors and frequencies at every multiple | sub |
| B7 | Full-space sign at critical ratios beyond the size-only threshold (each ratio sub; all ratios RH) | sub / RH |
| B8 | General profiles past `log log N` on the full space | sub |
| B9 | Exact SOS on one two-prime lattice | RH |
| B16 | Window negativity exponent `< ½` (≡ zero width `< ½`) | ≥qRH |
| B33 | HF-native arithmetic sign: one window length `A > 2·enlargedWeilFloorAperture` with `R₁(A) = ⊤` from the complete family (≡ `a*(ζ) > 0.362…`) | sub |

### S2. The window tower, its canonical system and signed criticality
Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT, HF, ACS, SRT, SZ, MSC. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC.

Established [L]:
- Window datum, truncated Dirichlet λ-ring, stage criterion `2wc_H(ℓ) ≤ S^N_A(H)`, kick = collar Rosati
  pairing, frozen form in closed form; lattice canonical system (Levinson, Schur parameters); window ⇔ its
  lattices; lattices Szegő singular under RH; zero modes radical, parity, gap law.
- Continuum: jet Hankel limit, jet Gram PD and minors positive on nonnegative windows, jet energies
  log-convex, reflection coefficients `→ (−1)^n`, parity split `det J_n = det E·det O`.
- Sectors ⇔ Hamburger / shifted Hamburger; window ⇔ Stieltjes moment problem of jet energies.
- Gamma ladder; pole `+` square to even, `−` square to odd.
- Base: all real `C²` tests positive through length `181/250·(1 + step)`; floor `‖f‖²/8000` to
  `enlargedWeilFloorAperture`. First stage (length `21/20`): admissible `w₂` excludes `0` and `−w₂`. Odd unit
  window ⇔ `w₂ ∈ unitBandWeights`.
- Below `log 4`: sharp prime-free half-window at `c = log 2`; two-weight band ⇔ Markov–Hankel pair ⇔
  retained-variance certificates ⇔ Hodge index ⇔ Künneth effectivity; convex, compact after `½log 3`,
  cylinder in `w₃` before; soft entry `ηΩ(2c − log 3)`; weights bounded once a prime acts.
- Edge law, sliver signature, outward edge `w_ne^h/2`, collar ratio `2w_ne^h` sharp.
- Gauge calculus: pole-charged representation; theta gauges critical; dropped variance = all-pairs jump form.
- **Perron sign law:** even sector `E(f) − E(|f|) = ∬D(u,v)[ω(|u−v|) + ω(−u−v) − 4cosh(u/2)cosh(v/2)]`;
  Markov for `c ≤ log ρ`; not Markov for `log ρ < c < log 2` at every pole strength `s ≥ 1` and all weights
  (frustrated edge–centre pair); robust Perron in the pole strength costs height
  `4(s₁ − s₀) ≤ M²(E_1(g) − λ + ε)`; the arithmetic pole lies within `O(λ₀)` of the positivity threshold;
  robust kick margins force ground states to decouple reflected sliver pairs.
- Markov part negative on support `e^{−3/4}`; prime `3`: collar certificate fails for `c ≥ 287/500`, deleting it
  breaks odd positivity for `c ≥ 3/5`; variance-free certificates fail for `c > 273/400`; capacities and
  constrained ground states never smooth.

Status: the stage step, certificate format and ground-state calculus are exact. Below `log 4` the whole
problem is the membership of one explicit point in an explicit compact convex set; no certificate exists for
any `c` between `0.362` and `log 2`. These windows carry no zero information (S11); their value is the
mechanism.

| | Obstacle | Strength |
|---|---|---|
| A5 | Rigorous computer-assisted certificate of `(w₂, w₃) ∈ belowLogFourBandWeights c` for `c ∈ (0.362, log 2)`; margins `1.5×10⁻⁵` (odd), `5.6×10⁻⁸` (even) at `c = ½log 3` [N] | — |
| A6 | Rational Hecke graphs and Tate horizons of stages 3, 4, 5, 7, … | — |
| A7 | Closed form of the first-stage complement `Φ_ε` | — |
| A8 | Even-sector cosh-credit supersolutions with retained variance (difficulty unverified) | — |
| A28 | Atomic-lattice bound `λ_max ≤ ½log N` | — |
| A33 | Lévy sector margins at `c = ½log 3` in both sectors, feeding soft entry [N] | — |
| B2 | Kick admission at every stage | RH as induction; each stage sub |
| B3 | Frustration domination at every length: a signed gauge, pole variance retained, in which the sliver reflections pay the collar Hankel form, odd and even | RH; fixed length sub |
| B4 | Structural certificate of the odd unit window (`w₂ ∈ unitBandWeights`) | sub |
| B5 | Structural certificate below `log 4` (`a*(ζ) ≥ log 2`), the prime `3` paid by sign | sub |
| B17 | Global continuum canonical system of the tower (Hamiltonian with the prime kicks) | identity |
| B49 | Signed ground-state structure past `log ρ`: a nodal law or signed Doob gauge for the even band (pole frustration) and the odd band (kick frustration) | method |

### S3. Dimension zero, counts and the Hodge index
Routes: ACS, HF; programmes WTZ, DZG, ATD, AHD, LST, KPA.

Established [L]: Tate jet and signed-count forms; bare domination ⇔ `Q ≥ 0`; no uniform Gamma–pole
domination; shifted pole weight forced and refuted; Künneth `h¹ = ½Q`; bidegree, fixed-rank, definite and
Siegel counts excluded; finite-square identities refuted; below `log 4` window positivity ⇔ Künneth
effectivity ⇔ Hodge index of the scaling subsurface; degree-zero Rosati principles exact.

Status: closed as an RH mechanism [D].

| | Obstacle | Strength |
|---|---|---|
| A25 | Künneth primitive `h¹` at small degree; mixed jets | — |
| B24 | Genus upper law | indep. |
| B25 | Logarithmic Serre duality, primitive part | sub |

### S4. Kähler package, stars and gluing
Routes: HF, ACS-Hodge, TG, SC, RW; MC through the gluing determinant.

Established [L]: HR ∧ HL ⇔ strict HR; RH ⇔ HL on the PSD locus; stars, depth law, gcd strata; nerve
`χ̃ = −M(N)`, Redheffer `det = M(N)`; zero modes = radical; first failures two-site.

| | Obstacle | Strength |
|---|---|---|
| A22 | Björner wedge decomposition | — |
| A23 | Depth law, star horizons, gcd-strata tables | — |
| B10 | No zero mode at any length | RH |
| B11 | Top coprime stratum | RH |
| B35 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH |
| B45 | Cross-tower gap through the archimedean channel | method |

### S5. Index and finite off-line support
Routes: HKT, AKLT, AID, SRT, CHMD, SC, RIT, CWS.

Established [L]: finite index = PD minus finitely many squares; finite index ⇒ Lindelöf; RH ⇔ index zero;
window index finite, monotone, `sup = κ`; `{0, ∞}` laws; index `≤ R + A` on `R` coarse cells; growing Euler
heads unbounded.

| | Obstacle | Strength |
|---|---|---|
| B12 | Index ceiling uniform in resolution | ≥qRH; RH (tensor) |
| B13 | Zero–one law `κ ∈ {0, ∞}` | sub |

### S6. Window energy, near-line density and the Hecke defect
Routes: WD, LA, TG, HCF, SC-heat, TH-heat; census; HEF.

Established [L]: window integer = Wiener–Hopf index; Cauchy cap cancellation to
`σ_m = 1 − 1/(116log(m+5))`; exponent `3loglogV/logV` outside `O(V/loglogV)` windows; micro-Planck flux;
zero-free window ⇔ unweighted `L²` port; bounded port ⇔ purity; polynomial-stage TFAE ⇔ RH; eight
near-line density forms; `D_win` ⇔ thin Planck shadows; `D_zero` ⇔ `D_win` + vanishing cluster tail;
right-half squared-depth moment `o(V)`; window depth mass `≤ W` outside `o(T)` centres. Visibility: spread
shallow sets with unit-window depth² mass `W` hide from windows of half-width `a` while
`a²(2a+2π)e^{2π}e^{2σa}W ≤ m₀L`; coherent shallow clusters are seen once `δ²a³ > 3/2` [L].

Status: WD's RH content is right-port cancellation through `[½, σ_m]` (the zero-free region pushed to the
line) [D]; `D_win` is a clustering statement counts and moments cannot give.

| | Obstacle | Strength |
|---|---|---|
| A26 | WD composition; Vinogradov–Korobov cap in place of `σ_m` | — |
| A27 | Cluster-detector constant | — |
| B19 | Inner caps `[½, σ_m]` at every polynomial stage | RH; fixed degree ≥qRH |
| B20 | `100%` critical-scale clustering | sub |
| B21 | `D_win` (≡ thin Planck shadows); `D_zero` | sub |
| B22 | Hecke defect pointwise / dyadic | ≥qRH / RH |
| B23 | Distributional input beyond counts and moments | method |

### S7. Counts, producers, precision and the gauge torus
Routes: WL, MC, PBM, RB, JAS, CTF, ACS-effectivity, HF-RR, RW; census.

Established [L]: one-sided count ⇔ RH; multivariate parity producers reach `(1+ε)x + C_εlog²x`; individual
producers slope `> 1`; Redheffer `det = M(N)`; first cyclotomic band abscissa `2Θ`; pole-subtracted gauge
exponents range over `[Θ, 1]`, minimized at the trivial point; flip points exponent `max(θ, Θ)`; explicit
non-special gauge with exponent `½`; simple-critical proportion `≥ 0.67250071` (imported Zeta23 inputs).

| | Obstacle | Strength |
|---|---|---|
| A21 | Logarithmic two-point Chowla | — |
| A24 | Census items; Voronoi; Zwegers | — |
| B26 | `ε`-uniform producer; square-root source input | sub; RH |
| B27 | First cyclotomic mode at square-root precision | RH |
| B28 | Signed pair information beyond bandwidth one | sub |
| B29 | First Epstein real zero on the boost line | sub |
| B32 | Half-power law at the trivial gauge point | RH |

### S8. Carriers, coupling, selection and the prime-blind cone
Routes: SC, ACS, HF; candidates; PBAP.

Established [L]: coupling calculus; damped cone ⇔ RH; undamped ⇒ RH or unattained width; Weil cone
`⊆ {Λ}`; lattice selection; PBAP ⇔ RH, node-critical, Farkas-dual, solved on nonnegative and separated cones;
Selberg-class Euler rigidity at `σ = ½`, degree gap, degree one; Beurling and Hamburger rigidity; Legendre
`J(ρ)` real ⇔ RH.

| | Obstacle | Strength |
|---|---|---|
| A11 | Function-field calibration | — |
| A12 | Gaussian-damped coupling identity | — |
| A13 | Finite-level Weil cones `C_A` and their widths | — |
| A31 | Selberg-class degree-one classification | — |
| B30 | Bounded damped cone coupling; unattained width | RH |
| B31 | Finite-sieve Hodge positivity → global | RH |
| B34 | Rosati positivity of the window reflection | RH |
| B36 | Selection at the trivial gauge point | RH |
| B37 | FE twins inside the full class with off-line zeros | sub |
| B42 | Prime-blind positivity on signed blind combinations | RH |

### S9. Realization and scattering
Routes: PM, RN, PTR, W1C.

Established [L]: Mayer operator; resonance ⇔ `ζ(2s) = 0`; exact completion `Q = 2Re[𝓦H, 𝓦H]`; canonical
Krein–Lax–Phillips space on Lewis period cores with Krein self-adjoint generator; on-line resonances Krein
square `1`, off-line antisymmetric combinations `−2`, negative subspace of dimension `= boostPolarIndex/2`;
RH ⇔ Krein form `≥ 0` ⇔ renormalized Hodge index; defect formula; retained `T₂` channel with sign of
`¼ − Re s`, reversed at the reflected resonance; window tests lift to `+1` fixed periods; operator Mayer
`Z`-function equal to Hardy's `Z` on the line, sign changes at odd-multiplicity resonances, `> 67.25%`
disjoint sign-change intervals; physical cusp residue = Krein square.

Status: P3 reduces to `D_s(ψ_s) = 0` at resonances, which is `δ = 0` itself; a proof needs an arithmetic
second expression of the same defect with manifest sign `≥ 0` [D].

| | Obstacle | Strength |
|---|---|---|
| A14 | Classical identifications; mixed-parameter completion; full Mayer transfer compatibility; analytic completion of the corrected boundary carrier; rational Weyl identification | — |
| A15 | Operator-native nonvanishing on `Re w = 1` (risk: reduces to the Euler product) | — |
| B38 | Arithmetic expression of `D_s(ψ_s)` at resonances with manifest sign `≥ 0` | RH |
| B39 | Statistic of resonant states selecting the decay rate | method |
| B40 | Source-faithful realization of unbounded rank | RH |
| B46 | PM-native zero-free region for `ζ(2s)` from an arithmetic size bound on the defect | sub |

### S10. Zero-configuration geometry and deformation
Routes: ZCG (candidate), LA, TH, HCF, XN, SRT; programmes ZCG, RHTower DeBruijn, SquareRootThreshold.

Established [L]:
- Camera: blindness costs `πD` exactly; Paley–Wiener equivalence; sparse clusters (density `< 2a/π`) never
  cancel; shallow configurations resolved at the Ingham scale `π/(2a)` (globally and locally), optimal;
  deep columns hide only below the Ingham scale; fakes caught exactly above `½log n₀`.
- Local inversion at the square-root threshold: failure for `0 < λ ≤ 1` (disjoint-carrier half-shifted
  lattices, RvM error `≤ 1`); `λ > 1`: any two RvM configurations with equal images coincide near `T` outside
  near-collision clusters `< δ/log T`; `λ > ½` for subset carriers, `λ > (1+μ)/2` for extra density `μ`;
  ζ: one window pair of aperture `λ·L_T`, `λ > ½`, reads the exact multiplicity of every `T^{−M}`-isolated
  zero; cancelling clusters of ζ-mimics are near-coincidences within `exp(−κlog X/(1+loglog X))`.
- Near-coincidences: net multiplicity zero, centre to `O(r²)`, squared gap `w²` to `O(r³)`, with
  quasi-polynomial window loss `e^{C log²X}`; polynomial-scale precision needs isolating windows with
  polynomial floor, which worst-case RvM-blind windows do not have.
- Heat: general source-profile repulsion law; collision-free horizon `6600/9991` (sharp for the four-piece
  sub-Weyl profile); collision ⇔ `Re Q(0) = Im Q′(0) = 0`; Gaussian saddle barrier `½/log(X/2π)`;
  `pairModel` collision obstruction below every positive time scale; global: no positive-time collision ⇔
  `Λ_X = 0` ∀X ⇔ RH.
- Euler stages and every finite real carrier: phase lattices, simple, counted, repelling above
  `2πe^{W_a}`; tilts cost weight `log(t/2π) − 6/t`; twins tilted at every height.
- Function field: purity closed, lost only at Frobenius collisions; collide or repel; camera identifies at
  the genus.

Status: identification is complete at its scale and sign-free; reality at near-coincidences is the RH
content [D]. In the pair model every depth `≤ ½` collides before `½/log X`, so the part of the heat path no
size bound reaches contains every possible off-line zero [D].

| | Obstacle | Strength |
|---|---|---|
| A38 | Sub-Weyl strip profile from the best known exponent pairs (horizon toward `½`; decides nothing about zeros) | — |
| B14 | Collision exclusion along a source-faithful path: heat path on `(0, ½/log X]` with Euler-product information inside the strip (≡ `Λ_X = 0` ∀X); Laguerre–Pólya at all ranks and degrees | RH |
| B44 | Reality at near-coincidences: the sign of `w²` for every near-coincident cluster, read through the prime channel | RH |
| B48 | Second-order local inversion at polynomial scales for ζ: isolating windows whose floor is polynomial in the isolation radius on ζ's configuration (needs ζ-specific spacing input) | sub |

### S11. Window visibility
Routes: every window route (RW, EWU, OWU, ACT, TT, CHMD, SZ, MSC, HF, SRT, AIP, SC); WD, LA, ZCG through
depth and density. Programme: WindowVisibilityLaw (WVL), SquareRootThreshold, DCI.

Established [L]:
- Closed-interval law, `a* = ⊤` ⇔ on-line, ζ and AHD dictionaries (§1).
- Master law `k·pairEnergy(δ,a) ≤ L`; deep and cubic brackets for `a*`; sharp L² tilt amplification
  (`P²/‖f‖² ≍ e^{2δa}/δ`); general RvM coherent-cluster exclusion with near/far terms; outside depth `≤ σ`
  gives a pure `e^{2(δ−σ)a}/δ` law.
- Shallow: macroscopic coherent clusters cancel `log T`; DCI-admissible coherent clusters visible at
  `δ > √(3/2)a^{−3/2}`; universal non-lattice hiding when `a³W ≲ m₀L`; separated runs hide while
  `2δa·sinh(2δa) ≤ 1`.
- Barriers: biquadratic tapered crystal hides a depth-`1/a` zero for every `L ≥ 4a`; doubly-exponential
  height non-locality; contact law at `c log T` is a power-saving zero-location bound.
- Columns: split-column certification at `a > πD_on + (π/2)D_off`; pure off-line columns `a* ≤ πD/2`;
  `2g` curve columns at `a > (g − ½)log q`, sharp by a mixed configuration with `a* = (g − ½)ℓ`; one moved
  off-line pair collapses `a*` from `L/2` to `≈ (1/2δ)log(δL/ε²)`; ℓ¹ jitter `2Le^{δL}Σ|ε_k| ≤ 1` keeps
  `a* = L/2`.
- Paper, being formalized [P/W]: general aligned `k`-pair law; general RvM shallow depth-mass bound under
  positivity `Σm_qδ_q² ≲ A₀log T/a²`; tapered crystal hiding to `a ≍ log T` at peak depth `¼`; two-bump
  interferometer bound; synthesis module.

Status: classified in models; for ζ the laws are unconditional but require window positivity, known only at
`a ≤ 0.362`, where they are vacuous.

| | Obstacle | Strength |
|---|---|---|
| A35 | Sharpen the general RvM coherent-cluster constants (`2²⁶·960`) toward the model constant `4δL/k`; makes positivity at half-width `≈ 4–5` carry zero information above verified heights | — |
| A36 | Formalize the paper items of the onset-law card and the synthesis module | — |

### Route-specific items
| | Obstacle | Routes | Strength |
|---|---|---|---|
| A17 | Theta rank 9: an entry-preserving compensation varying with scale across `[8, 32]` and the compact centre gap (fixed load and quartic profile excluded; capacities exact); ranks `≥ 10` at fixed apertures (difficulty unverified) | TH | — |
| A18 | Hausdorff shifts, Jensen horizons, two-grid degrees, PF beyond 37 | PA, LA, HCF | — |
| A19 | Nine atom-dominated collar moduli | ACT | — |
| A20 | Mixed Schur debit; first-prime/coarse/polar costs | AIP, CHMD | — |
| A32 | Unfinished receivers: Cayley–Li primitive-sign receiver, SZ first-variation transfer | LI, SZ | — |
| B15 | Scheduled prime energies bounded below | FU, CFC, RP, SZ, LI, FEL, EGC | RH |
| B41 | Pre-divisor forcing | APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF | RH |

## 3. Live routes

Each entry: path; established; open; class; A; B.

### WL — Weil lag
- Path: prime error → square-root bound or subexponential critical energy → RH.
- Established: exact prime-error/energy criteria; first cyclotomic band abscissa `2Θ`, RH ⇔ energy
  `O_ε(N^{1+ε})`; gauge-torus exponents `[Θ, 1]` minimized at the trivial gauge; reflection-pair coupling =
  smoothed prime count against the collar Hankel form [L].
- Open: signed square-root precision of one band; a gauge attaining exponent `½` at the arithmetic point.
- Class P4. A: A25, A29. B: B1, B26, B27, B32.

### RW — restricted Weil ground energy
- Path: `μ(a) ≥ 0` at every radius (≡ `a*(ζ) = ⊤`) → RH.
- Established: attained radius-decreasing minima; floors through `enlargedWeilFloorAperture`; exact
  `{∞, 2}` trace through `½log 3`; window ⇔ lattices; two-site decision; sectors ⇔ moment problems; below
  `log 4` positivity ⇔ two-weight band ⇔ retained-variance certificates; positive apertures form the closed
  interval `[0, a*(ζ)]`, `a* = contact` off RH; smooth extremals excluded [L].
- Open: an all-test coupling bound paying the signed prime folds; arithmetic-point membership below `log 4`;
  outward-edge bounds control kick sizes but need a full sector margin.
- Class P1. A: A5, A7, A33, A35. B: B1, B2, B3, B4, B5, B49.

### FU — signed prime scheduling
- Path: signed prime/Möbius history → one-sided sampled Abel bound → RH.
- Established: for each fixed `m ≥ 1`, one-sided boundedness of `A(j^m)/j^m` ⇔ RH; one controlled sample per
  backward window of length `N^{1−δ}` suffices [L].
- Open: produce those samples from the complete signed history.
- Class P4. B: B15.

### CFC — first-clock lower bound
- Path: first-clock sine coefficient bounded below on an aperture tail → RH.
- Established: exact tail criterion; unbounded below under ¬RH; phase-natural transport is the identity [L].
- Open: a lower bound retaining prime, archimedean and endpoint terms.
- Class P4. B: B15.

### RP — history floor
- Path: matched-quantile prime history → eventual linear defect floor → RH.
- Established: linear-floor criterion; low-LCM and copied-diagonal payment; sublinear floor impossible [L].
- Open: high-LCM pairs, moving core and singular-domain terms in one floor.
- Class P4. B: B15.

### PA — prime–archimedean passivity
- Path: prime − archimedean trace → current sign or subexponential mismatch → RH.
- Established: exact receivers; each fixed Hausdorff order positive at large shifts [L].
- Open: all-order/all-shift sign; a signed high-frequency complement remains.
- Class P5 (order limit). A: A18. B: B14.

### MC — Möbius cancellation
- Path: Möbius/Liouville cancellation at half power → RH.
- Established: half-power and Redheffer criteria; square-root-cutoff divisor head with bounded pronic energy;
  Möbius exponent Haar-a.e. `½`, Baire-generic `1`; explicit exponent-`½` gauge off every finitely modified
  orbit; flip points `max(θ, Θ)`; sparse-prime transfer [L].
- Open: half-power cancellation at the trivial gauge; uniform signed long-modulus energy.
- Class P4. A: A21, A22. B: B26, B27, B32, B36.

### TT — theta tail / Wold
- Path: theta source → directed covariance/Wold decay or odd Weil sign → RH.
- Established: exact receivers; Φ-Doob identities retaining every reflected prime term; odd sector = band at
  the centre ⇔ shifted Hamburger moments; below `log 4` odd sector ⇔ `oddBandWeights` ⇔ retained-variance
  shifted-ground-state certificate [L].
- Open: all-test directed covariance or odd positivity; the signed reflected-prime interaction (odd
  frustration is carried by the kicks, `kick = source − conductance`).
- Class P1 (odd sector). B: B1, B3, B4, B5, B49.

### LA — Laguerre/Jensen and local heat
- Path: theta source → collision-free heat descent / uniform Jensen or heated-coefficient signs → RH.
- Established: every fixed Jensen degree eventually real-rooted; RH ⇔ every positive-time zero simple ⇔
  `Λ_X = 0` ∀X; off-line depth `d` forces `Λ_X ≥ c·d²/log X`; zeros real/simple above
  `2πexp((6600/9991+ε)/t)`, `Λ_X ≤ (6600/9991+ε)/log X`; collision ⇔ `Re Q(0) = Im Q′(0) = 0`; size-only floor
  `½/log(X/2π)`; polynomial heat preserves the mesh; reality exits only through collision [L].
- Open: arithmetic exclusion of every collision in `(0, ½/log X]` and at bounded heights; or uniform
  Jensen/heated-coefficient signs. In the pair model every depth `≤ ½` collides inside that band [D].
- Class P5. A: A18, A26, A38. B: B14.

### TG — topological sub-unit gate
- Path: Euler/Gaussian source → nonnegative residual + integer trace `< 1` → RH.
- Established: winding/index and cubic-transgression identities; central-gap receivers [L].
- Open: a matrix-complete positive residual with sub-unit integer trace on every disc, or a zero-rate
  central-gap bound.
- Class P4 (inner caps). B: B10, B19.

### HF — Hodge / Hecke / complete cells
- Path: complete arithmetic form `≥ 0` → Hodge index → RH.
- Established: S1 in full; `R₁(A) = ⊤ ⇔ A/2 ≤ a*(ζ)`; terminal source polar with nontrivial kernel; exact
  low-packet capacity; simultaneous receiving coordinates with vanishing physical energy; long-index
  cancellation on near rows and annuli [L].
- Open: `a*(ζ) = ⊤`; at each ratio beyond the size-only interval, the signed complement; far-complement
  estimate loses `O(c)` against `O(log N/c⁷)`.
- Class: sign content P1 on untwisted windows; count face closed; floor layer size-only.
  A: A1–A4, A9, A10, A11, A22, A23, A37. B: B1, B6, B7, B8, B9, B10, B11, B12, B16, B33, B34, B35, B40.

### CHMD — causal hyperbolic–modular duality
- Path: one-sided bounded prime wave or odd Doob half-threshold bound → RH.
- Established: wave/Doob receivers; Haar transport; prime-edge Gamma reserve; all-detail prime–pole
  cancellation `O(exp(−√log Y/92160000))` [L].
- Open: one-sided boundedness of the unnormalized prime wave, or the complete odd sign.
- Class P1 (odd sector). A: A20. B: B3, B12.

### TH — theta Hankel ranks
- Path: signed centre-mixed theta jets → all-rank Hankel positivity → RH.
- Established: rank 8 PD for every `0 < a < ½`; ranks `≤ N` strict near `a = ½`; native fifth even section
  PD for `q ≥ 5` with Gaussian floor; fixed cross-load PD near the endpoints and for `q ≥ 5000`, fails at
  scale 8 with capacity `½ < τ₈ < 1`; quartic flux profile `(1 − r²/2)²` preserves integrated entries,
  repairs neighbourhoods of the origin and scale 8 and a cofinal ray, fails PSD at scale 32 for the complete
  and the weighted source at every critical aperture, capacity `τ₃₂(a) ≤ 70τ₃₂/67 < 54/67`; each finite
  native shifted Hankel matrix PD past a rank-dependent radius [L].
- Open: rank-9 integrated sign `I₈(a) > 0` on `0 < a < ½` (an entry-preserving compensation that varies with
  scale across `[8, 32]` and beyond); all ranks.
- Class P5 (rank limit; a moment problem at one centre). A: A17. B: B14.

### RN — renewal
- Path: theta renewal → divisor-faithful winding/boundary-work sign → RH.
- Established: Green/BV realization; compact cone-positive renewal operator with exact
  determinant/resonances [L].
- Open: directed mixed prime + Gamma `≥` pole including cusp/seam terms.
- Class P3-type. B: B40.

### WD — Ward / collision / window energy
- Path: source current/window energy → collision charge `< 2` or all-resolution sectoriality → RH.
- Established: S6 [L].
- Open: a zero-rate right-port bound through the inner caps with prefix-limit control; density branch: thin
  Planck shadows in `≤ η(A)V` windows with a vanishing cluster tail.
- Class P4 (inner caps); density branch sub. A: A26, A27. B: B19, B20, B21, B22, B23.

### LI — paired Li and prime–Gamma balances
- Path: prime − Gamma history floor / theta-clock first-zero budget → RH.
- Established: guarded history-zero set finite; RH ⇔ empty [L]; Cayley–Li primitive-sign receiver [S].
- Open: pay the outside budget at every guarded zero, or the primitive sign.
- Class P4. A: A32. B: B15.

### SZ — Suzuki screw
- Path: complete rectangular Ward defect bounded below at one width → RH.
- Established: exact lower-bound receiver; finite light-cone Gram identities; Krein–Schur congruences [L].
- Open: uniform lower bound after negative-light, Gamma, boundary and mixed costs.
- Class P1 (Krein–Schur carrier of the canonical system). A: A32. B: B2, B15.

### PM — Gauss–Mayer physical realization
- Path: faithful scattering source → Krein/Lewis positivity or pole exclusion → RH.
- Established: S9 [L].
- Open: an arithmetic expression of the defect at resonances with manifest sign; source-forced balance of
  the retained channel; mixed-parameter completion, full Mayer transfer, rational Weyl identification.
- Class P3. A: A14, A15. B: B38, B39, B40, B46.

### JAS, CTF, PBM, RB — one-sided counts
- JAS: bounds `|Riesz(m², k)| ≤ m^{εk}` on `m < k ≤ m + m/log(m+1)` for infinitely many `m` ⇔ RH [L]; open:
  uniform arithmetic control on that window. Class P4. B: B26.
- CTF: RH ⇔ bounded real rows reach every tolerance [L]; open: construct the rows retaining the terminal
  edge. Class P4. B: B26.
- PBM: convergence/RH equivalence [L]; open: coefficient cancellation to the critical abscissa. Class P4.
  B: B26.
- RB: eventual criteria, colossally abundant reduction [L]; open: square-root remainder on prime-saturated
  extremizers. Class P4. B: B26.

### HCF, XN, BAG, EWU, GTA, OWU
- HCF: heat explicit formula, two-grid criterion, arbitrary-zero detector [L]; open: signs at every
  degree/height. Class P5. A: A18. B: B14.
- XN: coverage/self-map criterion; nonnegative Laplacian of the interior margin [L]; open: an actual
  covering. Class P5. B: B14.
- BAG: recurrence receivers; RH ⇔ high zeros approach the line at each depth and high returns on off-line
  discs [L]; open: arithmetic construction of returns. B: B36.
- EWU: weight rigidity; attained blind minima; even sign ⇔ Hamburger moments; below `log 4` even sector ⇔
  `evenBandWeights` ⇔ retained-variance even theta gauge; Markov exactly for `c ≤ log ρ`, not Markov beyond
  at every pole strength; Perron margin `≤` pole-saturation gap × height² [L]; open: all-aperture lower band
  with mixed modes and negative-kernel pairs; a signed (non-Perron) ground-state structure past `log ρ`.
  Class P1 (even sector). A: A5, A8, A33. B: B1, B3, B5, B49.
- GTA: decay criterion; positive charge and finite-prefix convergence [L]; open: rank-uniform arithmetic
  energy decay. Class P5. B: B14.
- OWU: odd criterion; odd ⇔ shifted Hamburger; odd unit window ⇔ `w₂ ∈ unitBandWeights`; retained-Gamma
  identity; capacities never attained on smooth tests; below `log 4` ⇔ `oddBandWeights` [L]; open: joint
  Gamma/prime/pole sign at every aperture. Class P1 (odd sector). A: A5, A33. B: B1, B3, B4, B5, B49.

### SRT, ACT, AIP — complete atomic matrix
- SRT: full-family/index receivers; separatedness-free depth tests; terminal correction pole-attained;
  split-column receiver `a > πD_on + πD_off/2` with sharp `(g − ½)log q`; closed-contact receiver: `R ≤ a*`
  gives depth `< 1/R` to `zetaClusterHorizonHeight` [L]. Open: complementary-window sign, high-zero tail and
  source-kernel payment at every critical ratio; column or lattice structure is not established for ζ.
  A: A1, A3, A10, A27, A35. B: B6, B7, B12.
- ACT: single-shift receiver; `Ẑ(m_au) = 2S_a − D_a + 8V_c + 8τ_cA₂`; below `log 4` retained-variance shifted
  ground states ⇔ odd positivity; `w₂ > 0` for `c ≥ 21/40`; variance-dropping fails for `c > 273/400` [L].
  Open: one shift, uniform in profile/support, paying `D_a` with retained variance; arithmetic-point
  membership. Class P1. A: A19. B: B1, B3, B5.
- AIP: allocation receiver; small-`K` floor; all-`R` low-block positivity; capacity `log log N + O(1)`;
  simultaneous receiving with vanishing energy; literal three-range, affine short rows, Mangoldt Grams,
  mixed-channel bounds [L]. Open: full-space allocation at every `K` with growing fibres, offsets and prime
  bands. A: A1, A4, A9, A20, A37. B: B6, B7, B8.

### SC — Stokes/Witt–Krein
- Path: glued affine index `≤ 1` / bounded Gaussian-damped two-prime coupling → RH.
- Established: glued index `κ_ζ + 1`; damped cone ⇔ RH; undamped ⇒ RH or unattained width; sublinear tensor
  loss ⇒ RH [L].
- Open: an arithmetic bound for the damped coupling, sublinear tensor loss, or glued index `≤ 1`.
- Class P4. A: A11, A12. B: B1, B9, B10, B12, B30, B31.

## 4. Candidates

| Candidate | Established | Promotion gap | Strength |
|---|---|---|---|
| ACS | RH ⇔ effectivity ⇔ Hodge index ⇔ section count; primitive `h¹ = Q/2`; below `log 4` Künneth effectivity ⇔ two-weight band; degree-zero Rosati principles; Legendre `J(ρ)` real ⇔ RH; Selberg degree gap and degree one [L] | a non-count source of all-aperture primitive effectivity | B34; count face closed |
| APF | Fredholm index; cycle-trace reconstruction | zero-independent divisor exhaustion | B41 |
| BSH | framed curvature | pre-divisor section and mate identity | B41 |
| CDC | calibrated confluence iff `Re s = ½` | source-defined potential forcing confluence | B41 |
| EGC | pole-safe contour; copy correction | outer expanding-contour sign | B15 |
| EWJ | Euler/Wold jets | zero-independent source admission | B41 |
| FEL | theta likelihood; BSY = off-line zero sum | predeclared source balance | B15 |
| HJ | Hurwitz residual = SEC charge | pre-divisor forcing | B41 |
| IRK | rotation-algebra trace / winding | arithmetic projective lift with integral count (count face closed) | closed |
| MSC | Möbius–Sonin; divisor preservation | bridge to nonnegative Sonin energy | B1 |
| PCS | singular co-shift | source-natural wall annihilation | B41 |
| PTR | lossless stacks, unit port gap | prime-faithful port | B40 |
| RFHM | support grade | symmetry-breaking law | B41 |
| SEC | essential norm = seam jump | pre-divisor compactness at zeros | B41 |
| W1C | Lee–Yang receiver; PM's Krein space and generator; retained-channel side law | positive arithmetic Hilbert realization | B38, B40 |
| WBF | genealogy Gram | any arithmetic coupling | B41 |
| ZCG | S10 in full | a source-side reality mechanism at near-coincidences with a proved global RH implication | B14, B44, B48 |

### ZCG — zero-configuration geometry (candidate)
- Path: prime explicit-formula image → configuration identification → reality at near-coincidences or
  collision-free deformation → RH.
- Established: S10 [L]. At the square-root aperture the explicit formula determines ζ's zeros up to
  near-coincidences of diameter `o(1/log T)`; inside them it reads the squared gap to `O(r³)` with loss
  `e^{C log²X}`.
- Why a candidate: identification decides nothing alone — an on-line competitor with the image of ζ is
  already Weil positivity — and no source-side condition with a proved RH implication fixes the sign of `w²`.
  The repulsion mechanisms proved (integrality over `𝔽_q`, archimedean phase speed above the carrier horizon,
  size-only heat bounds above `½/log X`) do not reach ζ's own scale.
- Obstacles. A: A38. B: B14, B44, B48.

## 5. Decisive wall per route

| Wall | Routes |
|---|---|
| P1 — signed criticality, `a*(ζ) = ⊤`; first instances `a*(ζ) ≥ ½` (odd), `≥ log 2` (two weights) | RW, EWU, OWU, ACT, CHMD, TT, SZ, MSC, HF (sign content), ACS (sign content); CWS, WTZ, DZG, GWZ, CSTW, SWC, WVL |
| P1 at large ratios — untwisted windows (`R₁ ≡ ⊤` ≡ `a*(ζ) = ⊤`) | HF, SRT, AIP, SC; CACT, AHD, CSAR, ACPL |
| P4 — one-point square-root precision (the band in prime form) | WL, MC, PBM, RB, JAS, CTF, SC (coupling), FU, CFC, RP, LI, EGC, FEL |
| P4 — inner caps (zero-free region to the line) | WD, TG |
| P5 — rank / degree / collision below `½/log X` | TH, HCF, PA, GTA, LA, XN; ZCG (candidate) |
| P2 — prime-blind positivity | PBAP |
| P3 — reflection positivity (zero side) | PM, W1C, RN, PTR |
| Γ — trivial gauge point / pre-divisor forcing | BAG, MC; APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF |
| closed — counts / Hodge index | ACS (count face), HF-RR, IRK |
