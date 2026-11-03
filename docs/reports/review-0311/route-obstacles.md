# Route obstacles — status quo

Scope: the 32 live routes and 17 candidates of the frontier map, and the programmes that feed them,
read against the Lean corpus at `ccfb4b168e` with the working tree. For every route: path, what is
established, the open estimate, the shortcuts already killed, the path class, the obstacles that are
**(A) just work** and the obstacles that are **(B) open mathematics**.

Evidence: `[L]` Lean, committed and in its umbrella; `[U]` committed, not in an umbrella; `[W]`
working tree or work in progress; `[D]` derived here from Lean statements or from the corpus's own
conclusions; `[M]` model statement; `[N]` numerical; `[P]` paper only. Killed shortcuts are cited by
their anchor in `rh-killed-routes.md` (`#anchor`) or by row title.
Strength: **RH**, **≥qRH** (zero-free half-plane and Lindelöf), **sub**, **indep.**, **identity**,
**method**. A (just work) means known mathematics, finite computation, effectivization or assembly;
items whose difficulty is not established are marked `(difficulty unverified)`.

Notation: window tests of length `A` on `[−A, 0]`; `Q` Weil's form; `c_φ(t) = W(φ(· − t), φ)`;
stage `log(N+1) ≤ A < log(N+2)`, `ℓ = log(N+1)`, `w = Λ(N+1)/√(N+1)`.

## 0. Path classes

Every route is a face of one statement (`route-unification-ledger.md`). What separates routes is the
mechanism they can still offer. The corpus leaves four mechanism classes and closes the rest:

| Class | Mechanism | Status | Anchor |
|---|---|---|---|
| P1 | Signed criticality: a positive supersolution / ground-state representation of the folded arithmetic jump operator in which the sign of each fold is used, stage by stage | live; first instance (first prime stage) open | ACT `riemannHypothesis_of_foldedSupersolution` [L]; killed boundaries below |
| P2 | Prime-blind positivity: archimedean + pole part `≥ 0` on signed combinations of autocorrelations vanishing on `±log ℕ_{≥2}` | live; open on signed blind combinations; heuristic: no finite-level slack [D] | RHTower PBAP modules [L] |
| P3 | Reflection positivity of PM | reduced: the completed PM space is the zero side (`Q = 2Re[𝓦H, 𝓦H]` on `ℓ²(zeros)`); no candidate mechanism | RIT `TheHeckeEquivariantCompletion` [L] |
| P4 | Square-root cancellation of one smoothed prime sum (`c_ψ(t) = O(1)`) | live; classical; parity barrier for sieve-type producers | AOG, CSTW [L]; producer no-gos [L] |
| — | Counts / Hodge index / degeneration | closed as an RH mechanism [D] | see S3 |
| — | Size-only layers (subcritical, fixed critical multiple, twisted sectors, bulk) | blind: true, carry no Weil information | `#fixed-packet-bulk`, `#twisted-horizon-blindness` |

Closed mechanism families that must not be re-proposed (anchors in `rh-killed-routes.md`):
- **Cost-only / sign-blind payments of the new fold:** exit-charge collar loan (`#frozen-gamma-cubic`),
  Barta/Picone weights on `|c_n|` (WTZ [L/D]), weighted transfer `wE_φ ≤ Q_N` (DZG [L/D]).
- **Markov ground states:** `KR-BD` (no cofinal Markov passage); fully calibrated folded-Markov
  conductance (`#folded-markov`); lossless local allocation (`KR-LGP`); nonnegative combinations of
  shifted ground states (ACT [L]).
- **Finite structures:** finite-square count identities at the first prime (`#fold-count-identity`),
  finite-dimensional window realizations (`#finite-window-realization`), finite passive realizations
  (`KR-FPR`), finite virtual graph realizations (`#finite-virtual-realizations`).
- **Slack:** uniform positive aperture floors (`KR-PAF`), positive asymptotic lattice slack
  (`#lattice-positive-slack`), uniform growing-overlap Gram floor (`#growing-overlap-floor`).
- **Dimension zero:** Tate coefficients as a selector (`#tate-count-selector`), uniform Tate positivity
  (`#uniform-tate-positivity`), Gamma/pole domination of Tate counts (`#tate-domination`).
- **Counts:** bidegree/theta counts (`#bidegree-counts`), definite counts (`#definite-counts`),
  Siegel majorant (`#siegel-majorant`), isotropic Poisson pair (`#isotropic-poisson`), automatic
  arithmetic Riemann–Roch, Witt integrality (`KR-WIP`).
- **Producers:** integrality alone, fixed factorial ratios, univariate integer sup-norm, fixed-prime
  stencils, Adams multiplicity, base-change twists (rows in "Geometry, analytic tests").
- **Reflection:** bounded Cauchy reflection off `Re s ≥ ¼` (`#cauchy-reflection-order`), literal
  Serre–Krein isometry (`#window-krein-reflection`), Krein self-adjointness ⇒ positive projections
  (`#mayer-krein-sign`), Lewis inversion, three-term + inversion, resonant-state selectors, contractive
  scattering (`#scattering-schur`).
- **Continuation:** interior-gap continuation (`#lattice-interior-gap`).
- **Selection without sign:** every selector (`Γ16` of `walls-ledger.md`); regular integers do not
  constrain zeros (RHTower Beurling modules [L]).

## 1. The picture

| Fact | Anchor | Consequence |
|---|---|---|
| RH ⇔ `|c_φ(t)| < Q(φ)` for every bump and `t ≠ 0` ⇔ every two-site lattice window PD; off RH a short spectrally generic bump has `|c_ψ(s)| = Q(ψ)` | GWZ `RHIsDecidedOnTwoSites` [L]; AOG `riemannHypothesis_iff_hasseWeil_of_generic` [L] | the lattice form of AOG's Hasse–Weil theorem: a reformulation, not new leverage |
| `c_ψ(t) = A(ψ)B(ψ)e^{t/2} − Σ_kμ_{−2k}(ψ)ν_{−2k}(ψ)e^{−(2k+½)t} − Σ_nΛ(n)n^{−1/2}(ψ⋆ψ)(t − log n)` for `t > 2r` | CSTW `TheTrivialDivisorCouplesOrderedTests` [L]; [D] | the two-site band is the smoothed prime number theorem at square-root precision with constant `Q(ψ)` — the classical form of RH |
| Lattice canonical system: Toeplitz Weil sequences, Levinson recursion, Schur parameters, outer predictors, Carathéodory–Fejér degenerations; under RH Szegő singular; `n`-th margin born at order `h^{2n}` | GWZ [L] (`TheHigherMarginsAreBornLater` [L]) | classical Szegő–Levinson theory of the Weil sequence |
| Stage criterion; kick = collar Rosati pairing with explicit sign sectors; frozen form in closed form (trivial-divisor moments + earlier-fold transports); translation-contraction law | GWZ, CSTW [L] | exact dictionary of the stage step; no sign |
| PM: `Q(H) = 2Re[𝓦H, 𝓦H]` on `ℓ²(upper Mayer resonances)`; `T_p − Id` = Mellin translation, multiplier `p^{1−2s}`, similitude `p` = translation invariance | RIT [L] | PM is the zero side; its Hecke structure is translation |
| Weighted floor `Q ≥ −C(p)∫e^{−pu}H²`, `p > 1`, every length; one small critical multiple pays every fixed family | WTZ, AHD [L] | size-only |
| Subcritical PD below `(log N)^{1/8}`; at the critical curve Weil's form sits at the pole `u = 0` of the frequency counts | CACT, AHD [L] | HF's sign content is Weil's form on untwisted windows |
| Base: all real `C²` tests positive through total length `181/250`; first prime stage opens positive to `181/250`; frozen form indefinite on `[−21/20, 0]` | SPATL, GWZ [L]; `#frozen-gamma-cubic` | the certified tower ends inside the first prime stage |
| Odd unit window `[−½, ½]`: `Q + (3203/320)(∫xF)² ≥ ‖F‖²/1000`; `Q ≥ ‖F‖²/100` off two odd moments; exact retained-Gamma identity `Q = R_ret + ∫(remainder ≥ 0) + 2·reserve‖F‖²`; strip coercivity `‖G‖²/16` with the prime-2 reflection | WTZ [L] | one first-moment direction remains |
| Dimension zero: bare domination ⇔ `Q ≥ 0`; no archimedean family dominates the Tate counts | ATD, DZG [L] | count/Hodge/degeneration closed as an RH mechanism [D] |
| FE + positivity determine `ζ` (Hamburger); positive primes with regular integers allow off-line zeros (Beurling) | APD, RHTower [L] | a proof must use the functional equation together with the Euler product |

## 2. Shared obstacle blocks

### S0. The two-site band
Routes: all of C1, C7, C14, C15. Class C19.

Established [L]: RH ⇔ two-site PD ⇔ strict orbit Cauchy–Schwarz; one generic bump decides;
eventual boundedness decides; rate = zero width (AOG); explicit entry (CSTW); under RH
`c_φ(t) = Σ_ρ w_ρcos(γ_ρt)`, `w_ρ = m_ρ|φ̂(γ_ρ)|²`; free evolution fails; only `Λ` keeps every lattice
positive.

Research status: a reformulation of the classical criterion (smoothed `ψ(x) = x + O(√x)`); it fixes
exactly what every mechanism must deliver at each scale and shows that stage/interior structure is
not needed to decide RH.

| | Obstacle | Strength |
|---|---|---|
| A33 | Bridge module: two-site entry = ordered coupling = smoothed prime-error receiver of WL | — |
| A34 | Two-site band on a bounded step range from numerical zero data and explicit tails (computational; decides nothing) | — |
| B42 | The band at every step (= B1) | RH |

### S1. Complete Weil family at the critical overlap
Routes: HF, SRT, AIP, ACT, ACS-atomic, RW-atomic, SC, CHMD (index), FEL, MSC. Class C1.

Established:
- [L] Subcritical regime closed (`α < 1/8`, floor `κ/(2c⁷)`); receivers (window, horizon, Beurling,
  unit bump).
- [L] Critical-curve second order: untwisted `κQ(H) + (βJ/K)‖H‖²_{−8}`; conductor windows
  `(7φ(m)J(m)/K)‖G‖²_{−8}`; cross pairings `→ 0`; uniform decomposition on a nonquantitative range
  `M(N) → ∞`; count ratio uniform for `m = o(c)`, `≤ ½` for `m ≥ λ₀c`; Ramanujan horizon vectors of
  `m ≤ N^θ`, `θ < ½`, collective quasimodes.
- [L] Every periodic, trigonometric (distinct frequency classes) and primitive-character twist
  inherits the polarization; frequency counts have a pole of order `β+1` at `u = 0` with finite part
  the untwisted count.
- [L] One aperture-independent `0 < K ≤ K₀` pays every fixed independent family; exact-clock inertia
  `(n₊, n₋+n₀, 0)`.
- [L] Bulk blind below the grid `λN`; bulk second order at fixed `0 < c < 1` (Stieltjes constants,
  `L'/L(1,χ)`, center part, cross error); near-pair row Riemann sums [U].
- [U] Far reserve on `(V₁)^⊥` for `1 ≤ c ≤ 2K₁(log N)^{1/8}` with prefix cost; [W] logarithm-free
  conductor residuals (the module contains an unsupported step `hdist_K : … → False` proved by
  `trivial`, flagged in the frontier map).

Killed shortcuts: `#conductor-count-resolution` (bare counts through all conductors),
`#growing-overlap-floor` (no uniform Gram floor), `#fixed-packet-bulk` (aliasing masks `Q`),
`#critical-pencil-nullspace` (equality is not a sign certificate), `#twisted-horizon-blindness`,
`#defect-capture`, `#overlap-gram-smoothing`, `#separate-shell-payment`, `#absolute-prime-correction`,
`#prime-pole-cost`, `#prime-residual-scale`, `#logarithmic-floor-budget`.

Research status: below the critical curve solved; at the critical curve every direction except
untwisted windows is a positive count; every layer below the sign is size-only. The sign content is
B1 on untwisted windows of radius `½log K` at large `K`.

| | Obstacle | Strength |
|---|---|---|
| A1 | Explicit constants and horizons | — |
| A2 | General profiles past `θ = 1/1080` | — |
| A3 | Joint twist families; equal-parity characters through `L(s,ψ̄₁ψ₂)`; different moduli | — |
| A9 | Window index as a counting function of the length | — |
| A30 | Full-space positivity at one small multiple: far reserve [U], prefix cost, conductor-one block, Schur payment [W] — blind (carries no Weil information) (difficulty unverified) | — |
| A31 | Quantitative conductor range `M(N) = o(c_N)` (difficulty unverified) | — |
| B1 | Weil's sign on untwisted windows at every multiple | RH |
| B4 | Twisted-sector positivity through all conductors and frequencies at every multiple (no uniform floor exists, `#growing-overlap-floor`) | sub |
| B6 | General profiles past `log log N` on the full space | sub |
| B7 | Exact SOS on one two-prime lattice | RH |

### S2. The window tower and its canonical system
Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT, HF, ACS, SRT, SZ; programmes CWS, WTZ, DZG, GWZ, CSTW.
Classes C1, C4, C15.

Established [L]: window datum; truncated Dirichlet λ-ring; stage transfer; ground-state identity;
exit charge; composite stages free; sharp floor; Hecke-graph reading; exact Tate horizons at stages
1–2; frozen form indefinite at the first prime; two-collar form, stage criterion, kick law, birth at
zero; kick = collar Rosati pairing; chain law; frozen form in closed form; translation contraction;
lattice canonical system (Levinson, Schur parameters, causality, single-kick law, admission
interval); window ⇔ lattices; refinement lowers margins; no unnormalized continuum limit; `h^{2n}`
birth of the `n`-th margin; zero modes (radical, parity, gap law, end-collar injectivity); odd
supersolution criterion (ACT).

Killed shortcuts: `#frozen-gamma-cubic`, `#retained-gamma-lower-form`, `#first-fold-linear-chord`,
`#fold-count-identity`, `#folded-markov`, `KR-BD`, `KR-LGP`, `KR-PAF`, `KR-CCP`,
`#lattice-positive-slack`, `#lattice-interior-gap`, semilocal positive factors, fixed finite-prime
positivity at every aperture.

Research status: the stage step is exact and explicit in both registers; its sign is the only open
content. Every certificate that treats the fold as a cost, every Markov ground state and every
finite identity is excluded; a P1 proof needs a signed certificate of unbounded rank.

| | Obstacle | Strength |
|---|---|---|
| A5 | Certified first prime stage `[0.7243, log 3)` and second-stage certificates (margins `1.5×10⁻⁵` odd, `5.6×10⁻⁸` even at half-width `½log 3` [N]) | — |
| A6 | Odd unit window: pay the last first-moment direction; exact target `K₁₁ + (63/20)K₁₃²/(1 − (63/20)K₃₃) ≤ 1/(77/20 + 39/256)` for the exact logarithmic reflection operator; the fixed polynomial chord cannot pay it (`#first-fold-linear-chord`) | — |
| A7 | Rational Hecke graphs and Tate horizons of stages 3, 4, 5, 7, … | — |
| A8 | Closed form of the first-stage complement `Φ_ε` of the trivial-divisor moments | — |
| A29 | Atomic-lattice bound `λ_max ≤ ½log N` | — |
| B2 | Kick admission at every stage | RH as induction; each stage sub |
| B3 | Signed criticality: a positive supersolution at every length, signs of the folds used | RH; fixed length sub |
| B14 | Growth exponent of window negativity | `< ½` ≥qRH |
| B41 | Continuum canonical system of the tower (Hamiltonian with the prime kicks); lattice version solved (Levinson), continuum limit coalesces | identity |
| B43 | Contact law: RH to height `T` ⇒ windows of length `c log T` positive (survivor of `KR-CRT`; model boundary `c = ½` [M]) | sub |

### S3. Dimension zero, counts and the Hodge index
Routes: ACS, HF; programmes WTZ, DZG, ATD, AHD, LST. Class C13.

Established [L]: Tate jet and signed-count forms; jets generated by `M` and `ρ_A(Λ)`; bare domination
⇔ `Q ≥ 0`; no uniform Gamma–pole domination; horizon `≤ C exp(−exp(A−2))`; Euler-product pole weight
forced and refuted; Tate positivity not uniform and does not descend; Künneth `h¹ = ½Q`; bidegree,
fixed-rank, definite and Siegel counts excluded; finite-square count identity refuted at the first
prime; Künneth effectivity of a curve window ⇔ unitarity (calibration).

Research status: closed as an RH mechanism [D]. The domination question at the first fold has answer
No; the Taylor coefficients of `J_k` at `k = 0` are Bombieri's `Λ_j`, so any count-based positivity
must beat parity at first order. Every concrete count type in the corpus is excluded as an
independent sign producer. No corpus result exempts section counts on rank-2 spans `{ψ, τ_tψ}`; the
two-site Gram has the shape of Weil's Hasse–Weil inequality, but the 𝔽_q mechanism that proves it is
the one closed here.

| | Obstacle | Strength |
|---|---|---|
| B21 | Count-valued primitive `h¹` as an independent inequality — closed as a mechanism [D] | RH |

### S4. Kähler package, stars and gluing
Routes: HF, ACS-Hodge, TG, SC, RW; MC through the gluing determinant. Class C12.

Established [L]: HR ∧ HL ⇔ strict HR; RH ⇔ HL on the PSD locus; stars, depth law, gcd strata; nerve
`χ̃ = −M(N)`, Redheffer `det = M(N)`; zero modes = radical; first failures two-site.

| | Obstacle | Strength |
|---|---|---|
| A21 | Björner wedge decomposition | — |
| A22 | Depth law, star horizons, gcd-strata tables | — |
| B8 | No zero mode at any length (= no degenerate two-site lattice) | RH |
| B9 | Top coprime stratum | RH |
| B15 | Cross-tower gap through the archimedean channel | method |
| B31 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH |

### S5. Index and finite off-line support
Routes: HKT, AKLT, AID, SRT, CHMD, SC, RIT, CWS. Classes C1, C3.

Established [L]: finite index = PD minus finitely many squares; finite index ⇒ Lindelöf; RH ⇔ index
zero; window index finite, monotone, exhausting; `{0, ∞}` laws; index `≤ R + A` on `R` coarse cells;
growing Euler heads unbounded.

Killed shortcuts: `#growing-euler-index`, fixed-complexity index as a global ceiling, positive group-
kernel repair, local tower ceilings, pointwise index conservation, `#tensor-square-inertia`.

| | Obstacle | Strength |
|---|---|---|
| B10 | Index ceiling uniform in resolution | ≥qRH; RH (tensor) |
| B11 | Zero–one law `κ ∈ {0, ∞}` | sub |

### S6. Window energy, near-line density and the Hecke defect
Routes: WD, LA, TG, HCF, SC-heat, TH-heat; census; HEF. Classes C3, C11.

Established [L]: window integer = Wiener–Hopf index; pair resolvent = Laplace transform of `|𝒵|²`;
eight-way near-line density; `D_win` ⇔ thin Planck shadows; `D_zero` ⇔ `D_win` + vanishing
giant-cluster tails; Planck certificates on `(1−η(c))V` windows; mesoscopic occupancy; double-log
stage; right half-port `O(e^{(σ_m−½)t}/(t+1))` on Burnol windows; exact critical-line flux on
micro-Planck windows; polynomial stage ⇔ RH.

Killed shortcuts: `#theta-prefix-sectoriality`, `#theta-seam-smoothing`, `#fixed-log-defect`,
`#counts-only-defect`, `#antinodal-prime`, `#unfolded-euler-mollifier`, `#theta-uniform-prefix`,
`#window-port-reflection`, `#window-port-l2`, `#holomorphic-carriers`, `#window-density-separation`,
`#holomorphic-jensen`, `KR-R3`, `KR-HUS`, `KR-LLM`.

Research status: density statements are sub-RH and cannot exclude density-zero exceptional sets; the
RH-strength content is the inner-cap (zero-free-region) problem.

| | Obstacle | Strength |
|---|---|---|
| A26 | WD composition | — |
| B16 | Inner caps `[½, σ_m]` at every polynomial stage | RH; fixed degree ≥qRH |
| B17 | `100%` critical-scale clustering | sub |
| B18 | `D_win` (≡ thin Planck shadows); `D_zero` | sub |
| B19 | Hecke defect pointwise / dyadic | ≥qRH / RH |
| B20 | Distributional input beyond counts and moments | method |

### S7. Counts, producers and precision
Routes: WL, MC, PBM, RB, JAS, CTF, ACS-effectivity, HF-RR, RW; census. Classes C7, C19.

Established [L]: one-sided count ⇔ RH; multivariate parity producers reach `(1+ε)x + C_εlog²x`;
individual producers slope `> 1`; integer-Chebyshev ceiling; Redheffer `det = M(N)`; census
`0.67250071`; every eventually positive cyclotomic band has abscissa `2Θ`; cluster-product detector.

Killed shortcuts: PNT/short intervals as square-root input, size-only Chebyshev inversion, stronger-
than-half-power target, integrality alone, fixed factorial ratios, univariate sup-norm certificate,
fixed-prime stencils, Adams multiplicity, base-change twists, gauge averages, Vaughan endpoints,
`#quasi-character`, `#single-height-saving`, `#positivity-three-quarters`, `#frullani-phase`.

| | Obstacle | Strength |
|---|---|---|
| A20 | Logarithmic two-point Chowla | — |
| A23 | Census items | — |
| A24 | Voronoi; Zwegers | — |
| A25 | Künneth `h¹` small degree; mixed jets | — |
| A27 | Cluster-detector constant | — |
| B22 | Genus upper law | indep. |
| B23 | Logarithmic Serre duality, primitive part | sub |
| B24 | `ε`-uniform producer; square-root source input | sub; RH |
| B25 | First cyclotomic mode at square-root precision | RH |
| B26 | Signed pair information beyond bandwidth one | sub |
| B27 | First Epstein real zero on the boost line | sub |

### S8. Carriers, coupling, selection and the prime-blind cone
Routes: SC, ACS, HF; candidates; PBAP. Classes C2, C8, C16, C20.

Established [L]: coupling calculus; damped cone ⇔ RH; undamped ⇒ RH or unattained width; Weil cone
`{Λ}`; lattice selection; PBAP ⇔ RH, node-critical, Farkas-dual, zero-side identity, solved on
nonnegative and separated-bump cones; Selberg-class rigidity at `σ = ½`, degree gap `(0,1)` empty,
degree-one conductor bound or pole [U]; Beurling: regular integers do not constrain zeros;
Hamburger: FE + positivity force `ζ`.

| | Obstacle | Strength |
|---|---|---|
| A10 | Function-field calibration | — |
| A12 | Gaussian-damped coupling identity | — |
| A28 | Finite-level Weil cones `C_A` and their widths (heuristic: no finite-level slack [D]) | — |
| B28 | Bounded damped cone coupling; unattained width | RH |
| B29 | Finite-sieve Hodge positivity → global | RH |
| B30 | Rosati positivity of the window reflection | RH |
| B32 | Selection at the trivial gauge point | RH |
| B33 | FE twins inside the full class with off-line zeros | sub |
| B40 | Prime-blind positivity on signed blind combinations | RH |

### S9. Realization and scattering
Routes: PM, RN, PTR, W1C. Classes C9, C14.

Established [L]: Mayer operator, faithful divisor; resonance ⇔ `ζ(2s) = 0`; `D_s ≤ 0`, `= 0` iff
`Re s = ¼`; Krein positivity ⇔ RH; exact completion; Hecke = Mellin translation for every prime;
Hecke cones tile; Barnes/Eisenstein periods Hecke eigenfunctions; corrected all-prime transport on
the retained-boundary carrier; whole-Haar admission iff `H(−log 2) = 0`; closed Cauchy reflection;
finite packets: renormalized mean cusp energy = Krein square.

Killed shortcuts: `#cauchy-reflection-order`, `#mayer-krein-sign`, `#core-hecke-boundary`,
`#lewis-inversion`, `#farey-three-term`, `#hecke-window-cusp`, `#window-krein-reflection`,
`#resonant-cutoff-gram`, `#fixed-height-hecke-residual`, `#mayer-cutoff`,
`#mayer-complex-contraction`, `#scattering-recentering`, `#scattering-schur`,
`#congruence-pole-filter`, `KR-AUT`, `KR-SEL`, local PM admission/escape.

Research status: P3 reduced to the zero side; counterterm subtraction does not preserve positivity;
no candidate sign mechanism.

| | Obstacle | Strength |
|---|---|---|
| A13 | Classical identifications (Selberg-zeta normalization, Lax–Phillips, Lewis–Zagier, `+1` eigenspace, Garland) | — |
| A14 | Operator-native nonvanishing on `Re w = 1` (risk: reduces to the Euler product) | — |
| B34 | Arithmetic `D_s ≥ 0` on resonances (finite cusp energy ⇒ zero defect) | RH |
| B35 | Statistic of resonant states selecting the decay rate | method |
| B37 | Gaussian-packet physical residue (height-uniform normalized cusp bounds); the counterterm does not preserve positivity | identity |
| B39 | Source-faithful realization of unbounded rank | RH |

### Route-specific items
| | Obstacle | Routes | Strength |
|---|---|---|---|
| A11 | Integration: CACT far reserve [U], log-free residuals [W]; AHD near-pair rows [U]; SEL degree-one modules [U]; LI, SZ, HKT, AKLT, ALG, AGT, ACP | HF, AIP, ACS, LI, SZ, SC, MC | — |
| A16 | Theta Hankel rank 8 strict; ranks 9–10 | TH | — |
| A17 | Hausdorff shifts, Jensen horizons, two-grid degrees, PF beyond 37 | PA, LA, HCF | — |
| A18 | Nine atom-dominated collar moduli | ACT | — |
| A19 | Mixed Schur debit; first-prime/coarse/polar costs | AIP, CHMD | — |
| B12 | All-rank / all-degree signs; Laguerre–Pólya | TH, LA, HCF, PA, GTA | RH |
| B13 | Scheduled prime energies | FU, CFC, RP, SZ, LI, FEL, EGC | RH |
| B38 | Pre-divisor forcing | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF | RH |

## 3. Live routes

Each entry: path; established; open estimate; killed shortcuts; class; A; B.

### WL — Weil lag
- Path: prime error → square-root bound or subexponential critical energy → RH.
- Established: exact prime-error/energy criteria; first Chebyshev cyclotomic band abscissa `2Θ`, RH ⇔
  its energy `O_ε(N^{1+ε})`; multivariate parity producers at the main term; the two-site band is the
  smoothed form of WL's criterion [D].
- Open: actual signed square-root precision of one band.
- Killed: PNT/short intervals as input, size-only inversion, producers of slope `> 1`, integrality
  alone, base-change twists.
- Class P4. A: A25, A33. B: B24, B25, B42.

### RW — restricted Weil ground energy
- Path: `μ(a) ≥ 0` at every radius → RH.
- Established: attained decreasing minima; floors through `181/500` (`1/5000`) and `a*` (`1/8000`);
  exact `{∞,2}` trace through `½log 3`; window ⇔ lattices; RH ⇔ no first degeneration ⇔ two-site PD;
  first prime stage opens positive to `181/250`; zero limiting margin under RH.
- Open: an independent all-test strict orbit bound, or an all-stage contraction/Schur sign paying the
  signed prime folds and low-moment cross terms; the frozen branch needs interior infimum attainment.
- Killed: `#lattice-positive-slack`, `#lattice-interior-gap`, `KR-PAF`, `KR-CCP`, `#fold-count-identity`,
  `#frozen-gamma-cubic`, `#folded-markov`, semilocal factors, fixed finite-prime positivity.
- Class P1. A: A5, A6, A8. B: B1, B2, B3.

### FU — signed prime scheduling
- Path: signed prime/Möbius history → completed Abel moment `A(M)/M` bounded above → RH.
- Established: exact receiver, exhaustive schedules, clock kernels.
- Open: one joint bound paying seed, drift, prior action, cross-block covariance and endpoints.
- Killed: prime scheduling/curvature, pointwise Abel-clock positivity, polynomial capture.
- Class P4. B: B13.

### CFC — first-clock lower bound
- Path: first-clock sine coefficient bounded below on an aperture tail → RH.
- Established: exact tail criterion; unboundedness below under ¬RH; phase-natural transport is the
  identity.
- Open: an actual lower bound retaining prime, archimedean and endpoint terms.
- Killed: retired label A (transport rigidity).
- Class P4. B: B13.

### RP — history floor
- Path: matched-quantile prime history → eventual linear defect floor → RH.
- Established: linear-floor criterion; low-LCM and copied-diagonal payment; sublinear floor impossible.
- Open: high-LCM pairs, moving core and singular-domain terms in one complete-history floor.
- Killed: sublinear history floor.
- Class P4. B: B13.

### PA — prime–archimedean passivity
- Path: prime − archimedean trace → current sign or subexponential mismatch → RH.
- Established: each fixed Hausdorff order positive at large shifts.
- Open: all-order/all-shift sign; order-dependent thresholds leave a signed high-frequency complement.
- Killed: `KR-FPR`, `KR-TK`, retired labels D1, C2/I.
- Class P4 (rank limit). A: A17. B: B12.

### MC — Möbius cancellation
- Path: Möbius/Liouville cancellation at half power → RH.
- Established: half-power and Redheffer criteria; near-frequency bands retain `2Θ`; gauge exponent
  Haar-a.e. `½`, Baire-generic `1`.
- Open: actual Möbius cancellation including moving-band head/leaf covariance.
- Killed: gauge averages, stronger-than-half-power target, uniform escaped decay, Vaughan endpoints,
  additive shift, `#quasi-character`, `#single-height-saving`.
- Class P4. A: A20, A21. B: B24, B25, B32.

### TT — theta seam / Wold
- Path: theta source → directed covariance/Wold decay or odd Weil sign → RH.
- Established: exact receivers; Φ-Doob identities retaining every reflected prime term; restricted
  current signs.
- Open: all-test directed covariance or odd/primitive positivity; the signed reflected-prime
  interaction remains.
- Killed: `#horizon-charge`.
- Class P1 (odd sector). B: B3, B1.

### LA — Laguerre/Jensen and local heat
- Path: theta source → all-height/all-degree Jensen or heated coefficient sign → RH.
- Established: every fixed Jensen degree eventually real-rooted; heat/depth bounds; density-one
  fixed-depth control.
- Open: uniform signs through all heights/degrees, shallow near-double pairs, exceptional windows.
- Killed: `KR-JPR`, heat/polynomial positivity, `#heat-method-floor`, finite heat support,
  `#counting-local-bound`.
- Class P4 (degree limit). A: A17, A26. B: B12.

### TG — topological sub-unit gate
- Path: Euler/Gaussian source → nonnegative residual + integer trace `< 1` → RH.
- Established: winding/index and cubic-transgression identities; central-gap receivers.
- Open: matrix-complete positive residual and sub-unit integer trace on every disc, or a zero-rate
  central-gap bound.
- Killed: `KR-R1`, `KR-DSA`, `KR-TMD`, `#positive-model-homotopy`.
- Class P4. B: B16, B8.

### HF — Hodge / Hecke / complete cells
- Path: complete arithmetic form `≥ 0` → Hodge index → RH.
- Established: S1, S2, S4; subcritical PD; one small multiple pays every fixed family; twisted sectors
  positive; Weil's form at the frequency pole; bulk second order at fixed overlap.
- Open: the full growing-family critical sign at every required multiple, or an independent all-window
  positive realization; small-`K` aliasing masks the sign; exact-clock equality turns negative.
- Killed: S1 list; `#definite-counts`; dimension-zero domination; the count face (S3).
- Class: sign content P1 (= B1); count face closed. A: A1–A3, A9, A10, A21, A22, A30, A31. B: B1, B4,
  B6, B7, B8, B9, B10, B30, B31, B39.

### CHMD — causal hyperbolic–modular duality
- Path: complete causal prime/Möbius wave bound or odd Doob half-threshold bound → RH.
- Established: wave/Doob receivers; Haar transport; prime-edge Gamma reserve; all-detail prime–pole
  cancellation `O(exp(−√log Y/92160000))`.
- Open: the complete wave/odd sign paying Gamma, the signed potential and infinite-orbit terms in the
  receiver's normalization; the `√Y` normalization gives no unnormalized error or index ceiling.
- Killed: `#growing-euler-index`, Gamma boundary reserve, Haar/modal compactness, absolute Euler
  coefficient payment.
- Class P1. A: A19. B: B10, B3.

### TH — theta Hankel ranks
- Path: signed center-mixed theta jets → all-rank Hankel positivity → RH.
- Established: rank 7 strict; rank 8 PSD; native tails = Gram-square mass minus signed local flux.
- Open: rank-8 strictness and uniform higher-rank flux payment.
- Killed: `#native-tail-boundaries`, rank-uniform native successor, `KR-HFR`.
- Class P4 (rank limit). A: A16. B: B12.

### RN — renewal
- Path: theta renewal → divisor-faithful winding/boundary-work sign → RH.
- Established: Green/BV realization; compact cone-positive renewal operator with exact determinant.
- Open: directed mixed prime + Gamma `≥` pole including cusp/seam terms.
- Killed: native carrier identification, `KR-R2`, `KR-TRC`.
- Class P3-type (realization). B: B39.

### WD — Ward / collision / window energy
- Path: source current/window energy → collision charge `< 2` or all-resolution sectoriality → RH.
- Established: S6.
- Open: an independent zero-rate right-port bound through the inner caps and finite/shallow
  exceptions; density branch: thin Planck shadows in `o_A(V)` windows with a vanishing cluster tail.
- Killed: S6 list.
- Class P4 (inner caps); density branch sub-RH. A: A26. B: B16, B17, B18, B19, B20.

### LI — paired Li
- Path: prime − Gamma history floor / theta-clock first-zero budget → RH.
- Established: guarded history-zero set finite, RH ⇔ empty; Cayley–Li receiver [W].
- Open: pay outside budget at every guarded zero, or the primitive sign.
- Killed: eventual guarded-zero budget.
- Class P4. A: A11. B: B13.

### SZ — Suzuki screw
- Path: complete rectangular Ward defect bounded below at one width → RH.
- Established: exact receiver; finite light-cone Gram identities; Krein–Schur block congruences.
- Open: a uniform lower bound after negative-light, Gamma, boundary and mixed costs.
- Killed: sharp Suzuki source in `ℓ²`, uniform causal-to-sharp recovery, positive exact unital finite
  part, `KR-BD`, `KR-NEV`.
- Class P1 (Krein–Schur carrier of the canonical system). A: A11. B: B13, B2.

### PM — Gauss–Mayer physical realization
- Path: faithful scattering source → Krein/Lewis positivity or pole exclusion → RH.
- Established: S9.
- Open: Gaussian-packet extension of the physical residue; the arithmetic sign after counterterm
  subtraction; mixed-parameter boundedness, analytic completion, full Mayer transfer, signed-form
  descent; eigenspace/Weyl identification.
- Killed: S9 list.
- Class P3 (reduced to the zero side). A: A13, A14. B: B34, B35, B37, B39.

### JAS, CTF, PBM, RB — one-sided count
- JAS: open square-root power budget or all-amplitude shell control; admission supplies no budget
  growth. Class P4. B: B24.
- CTF: open signed covariance cancellation along compatible cutoffs; the terminal edge cannot be
  discarded (killed: CTF diagonal/centering, dropping the terminal edge). Class P4. B: B24.
- PBM: open actual coefficient cancellation to the critical abscissa (killed: `KR-RAW`). Class P4.
  B: B24.
- RB: open square-root remainder on prime-saturated extremizers. Class P4. B: B24.

### HCF, XN, BAG, EWU, GTA, OWU
- HCF: open signs at every degree/height or a one-sided vertical bound; two-grid non-aliasing does not
  control coalescence (killed: one grid aliases, `KR-HFR`). Class P4. A: A17. B: B12.
- XN: open covering with nonnegative interior margin; the boundary sign does not pay curvature.
  B: covering (RH).
- BAG: open returns including possible target zeros (killed: `KR-BAG`, `KR-TOR`). B: B32.
- EWU: open nonnegative actual minima at all apertures including low/mixed modes (killed: `KR-SRP`,
  `KR-APW`). Class P1. A: A5. B: B1.
- GTA: open rank-uniform arithmetic energy decay independent of zero data. B: B12.
- OWU: open: pay the remaining first-moment debit, then all apertures (killed:
  `#first-fold-linear-chord`, `#retained-gamma-lower-form`, `#frozen-gamma-cubic`). Class P1.
  A: A5, A6. B: B1, B3.

### SRT, ACT, AIP — complete atomic matrix
- SRT: open RH-complete sign at every multiple, the high-zero tail above the grid, conductor/frequency
  uniformity (killed: tempered fixed-ratio models, `KR-CRT`, `#finite-readings`, `#uniform-margin`).
  A: A1, A3, A9, A27, A31. B: B1, B4, B10.
- ACT: open one shift uniform in profile/support including exterior primes and the signed/polar
  remainder (killed: `KR-PAF`, `#folded-markov`). Class P1. A: A18. B: B1, B3.
- AIP: open global allocation or full sign at `c = 2K(log N)^{1/8}` for every `K`; validate the
  ground-conductor `coreNearRow`; general-conductor cancellation and prefix/Schur payment; alternative:
  all-window translation contraction from the short-window seed (killed: `KR-LGP`, `KR-ADJ`,
  `#separate-shell-payment`, `#absolute-prime-correction`). A: A1, A19, A30. B: B1, B4, B6.

### SC — Stokes/Witt–Krein
- Path: glued affine index `≤ 1` / bounded Gaussian-damped two-prime coupling → RH.
- Established: glued index `κ_ζ + 1`; damped cone ⇔ RH; undamped ⇒ RH or unattained width.
- Open: a prime/archimedean bound for the damped coupling, or glued index `≤ 1`.
- Killed: `#coupling-growth`, `#pole-pair-retuning`, `#additive-reading-index`,
  `#haar-continuous-dilation`, `#separated-place-poles`, `#tensor-square-inertia`,
  `#fixed-prime-counterterm`, `#local-polar-trichotomy`, separable towers, `#padic-localization`,
  `#fixed-prime-global-index`.
- Class P4 (coupling = kernel = window error). A: A10, A12. B: B1, B7, B10, B28, B29, B8.

## 4. Candidates

| Candidate | Established | Promotion gap | Strength |
|---|---|---|---|
| ACS | RH ⇔ effectivity ⇔ Hodge index ⇔ section count; primitive `h¹ = Q/2`; pure-curve calibration; Selberg-class, Beurling and Hamburger rigidity (selection) | a non-count source of all-aperture primitive effectivity; count/Tate/Hodge sources closed (`#count-hodge-source`); Rosati heights are receivers | B21 (closed as a mechanism), B30 |
| APF | Fredholm index; cycle-trace reconstruction | zero-independent divisor exhaustion | B38 |
| BSH | framed curvature | pre-divisor section and mate identity coupled to Ξ zeros | B38 |
| CDC | calibrated confluence iff `Re s = ½` | source-defined potential forcing confluence | B38 |
| DR | cusp roots, finite monodromy | compatible roots on the strict-right domain | B38 |
| EGC | pole-safe contour; copy correction | outer expanding-contour sign | B13 |
| EWJ | Euler/Wold jets | zero-independent source admission | B38 |
| FEL | theta likelihood; BSY = off-line zero sum | predeclared source balance | B13 |
| HJ | Hurwitz residual = SEC charge | pre-divisor forcing | B38 |
| IRK | rotation-algebra trace / winding | arithmetic projective lift with integral count (count face closed [D]) | B21 |
| MSC | Möbius–Sonin; divisor preservation | bridge to nonnegative Sonin energy | B1 |
| PCS | singular co-shift | source-natural wall annihilation | B38 |
| PTR | lossless stacks, unit port gap | prime-faithful port (killed: `KR-PTR`, `KR-GAP`, `KR-COS`, `KR-POI`) | B39 |
| RFHM | support grade | symmetry-breaking law | B38 |
| SEC | essential norm = seam jump | pre-divisor compactness at zeros | B38 |
| W1C | Lee–Yang receiver; PM's exact zero-coordinate Krein space | positive arithmetic Hilbert realization (killed: `KR-ISG`) | B34, B39 |
| WBF | genealogy Gram | any arithmetic coupling | B38 |

## 5. Decisive wall per route

| Wall | Routes |
|---|---|
| P1 — signed criticality / stage step | RW, EWU, OWU, ACT, CHMD, TT, SZ, HF (sign content), ACS (sign content), MSC, FEL; GWZ/CSTW/CWS/WTZ/DZG |
| P1 at large multiples — untwisted windows | HF, SRT, AIP, SC; CACT, AHD |
| P4 — one-point square-root precision | WL, MC, PBM, RB, JAS, CTF, SC (coupling), FU, CFC, RP, LI, EGC |
| P4 — rank / degree limits (Laguerre–Pólya) | TH, HCF, PA, GTA, LA |
| P4 — inner caps (zero-free region) | WD, TG |
| P2 — prime-blind positivity | PBAP |
| P3 — reflection positivity (zero side) | PM, W1C, RN, PTR |
| Γ — trivial gauge point / pre-divisor forcing | BAG, XN, MC; APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |
| closed — counts / Hodge index | ACS (candidate), HF-RR, IRK |
