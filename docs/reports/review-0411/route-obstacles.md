# Route obstacles — status quo

Scope: the 32 live routes and 17 candidates of the frontier map and the programmes that feed them,
read against the Lean corpus. For every route: path, what is established, the open estimate, the killed
shortcuts, the mechanism class, the obstacles that are **(A) just work** and the obstacles that are
**(B) open mathematics** (no known solution).

Evidence: `[L]` committed Lean declaration; `[W]` working-tree Lean module (not committed); `[D]` derived
here from Lean statements; `[M]` exact model statement; `[N]` numerical; `[P]` paper only. Killed
shortcuts are cited by their anchor in `rh-killed-routes.md` (`#anchor`) or by row title.
Strength: **RH**; **≥qRH** (zero-free half-plane or Lindelöf); **RH-adjacent** (a zero-location statement
about the lowest off-line zeros, neither RH nor sub); **sub** (strictly below quasi-RH); **indep.**;
**identity**; **method**. A means known mathematics, finite computation, effectivization or
assembly of proved pieces; an A item whose difficulty is not established carries `(difficulty unverified)`.

Notation. Window tests live on `[−a, a]` (half-width `a`, length `2a`) or on half-windows `[−c, 0]`;
`W` is Weil's form; `w_n = Λ(n)n^{−1/2}`. For `f` supported left of `m` and its mirror `f∘R`,
`R(v) = 2m − v`, the **coupling** is `𝒞_m(f) = 𝓗_m(f) − Σ_n w_n (f⋆f)(2m − log n)` with the **collar
Hankel form** `𝓗_m(f) = e^m μ_{1/2}(f)² − Σ_k e^{2mσ_k}μ_{σ_k}(f)²`, `μ_σ(f) = ∫f e^{−σu}`,
`σ_k = −(2k + 5/2)`. The **band** is `|𝒞_m(f)| ≤ W(f)`. On a half-window `[−c, 0]` the lag `ℓ = log n`
sees `f` only on the **collar sliver** `I = [−c, c − ℓ]` of width `δ = 2c − ℓ`. The **Lévy energy** is
the jump part of the archimedean form; `Ω(δ) = ∫_δ^∞ ω` its tail.

## 0. Mechanism classes

Every route is a face of one statement (`route-unification-ledger.md`). Routes differ by the mechanism
they can offer. Five classes are live.

| Class | Mechanism | Status | Anchor |
|---|---|---|---|
| P1 | **Signed criticality.** In a gauge `F = Φωu` the window form is a signed Dirichlet form plus pole charges; the primes pay the prime-free archimedean–polar deficit through the sign of their sliver reflections; the pole variance must be retained | live; below `log 4` exactly a two-number convex membership problem; first open instances: the odd unit window (`c = ½`, one weight) and `½log 3 < c < log 2` (the prime `3` paid by sign) | SWC, ACT, WTZ, GWZ, CSTW [L] |
| P2 | **Prime-blind positivity.** Archimedean + pole part `≥ 0` on signed combinations of autocorrelations vanishing on `±log ℕ_{≥2}` | live; solved on nonnegative and separated-bump cones; deleting one prime-power node already produces a negative combination | RHTower PBAP [L] |
| P3 | **Reflection positivity of PM.** Krein positivity of the completed resonant space | reduced: `Q = 2Re[𝓦H, 𝓦H]` on `ℓ²(zeros)`; the co-isometry defect of a fixed period is `−∫2cosh(δu)·4sinh²(δu)·|F(u)F(−u)|`, `δ = 2Re s − ½`: its sign is `δ = 0` itself, not an inequality | RIT [L]; [D] |
| P4 | **Square-root cancellation** of one smoothed short-window prime count: the band in prime form | live; classical; parity barrier for sieve-type producers; below `log 4` it is a two-term prime count matching the pole square | GWZ, SWC, CSTW, AOG [L] |
| P5 | **Reality by continuation.** Real-rootedness is closed and is lost only through a collision; RH follows from a source-faithful collision-free path | live as a receiver: heat path real for `t ≥ 1/8` (corpus normalization), RH ⇔ every positive-time zero simple ⇔ local constant `Λ_X = 0` at every height; `H_t` non-real for `t < 0` | ZCG, RHTower DeBruijn, LA, TH, HCF [L] |
| — | Counts / Hodge index / degeneration | closed as an RH mechanism [D] | S3 |
| — | Size-only layers (subcritical regime, one small critical multiple, twisted sectors, bulk, terminal windows, aperture-independent floor) | true and blind [D] | S1 |
| — | Identification without sign (camera of the explicit formula) | sign-free; an on-line competitor with the image of `ζ` is already Weil positivity [D] | S10 |

Closed mechanism families (anchors in `rh-killed-routes.md`):
- **Cost-only and sign-blind payment of a fold:** nonnegative exit-charge loan (`#frozen-gamma-cubic`),
  Barta/Picone weights, weighted transfer, retained Gamma `+E/64` and two-moment form
  (`#retained-gamma-lower-form`), fixed polynomial inverse chord (`#first-fold-linear-chord`), the prime `3`
  carried by its worst-case collar mass (`#prime-three-sliver-potential`, `c ≥ 287/500` [W]).
- **Ground states without the pole variance:** bare and compact folded Markov supersolutions
  (`#prime-free-markov`), calibrated folded-Markov conductance (`#folded-markov`), zero origin correction
  (`#folded-origin-charge`), cofinal Markov passage (`KR-BD`), odd gauges discarding pole variance
  (`#variance-dropped-theta-gauge`, `c > 273/400`), nonnegative even theta-gauge cosh supersolutions
  (`#theta-gauge-cosh-defect`), lossless local allocation (`KR-LGP`).
- **Collar locality:** collar parity / automatic positive reflected coupling
  (`#collar-positivity-induction`); unit collar energy paying every kick (`#collar-local-payment`).
- **Smooth extremals:** smooth compact window eigenfunctions, constrained ground states, capacity
  maximizers (`#smooth-window-attainment`).
- **Finite structures:** finite-square count identities (`#fold-count-identity`), finite-dimensional window
  realizations (`#finite-window-realization`), finite passive realizations (`KR-FPR`), finite virtual graph
  realizations (`#finite-virtual-realizations`).
- **Slack:** uniform aperture floors (`KR-PAF`), lattice slack (`#lattice-positive-slack`), growing-overlap
  Gram floor (`#growing-overlap-floor`), full-horizon reference-energy floor (`#full-conductor-diagonal`).
- **Dimension zero and counts:** Tate selectors and domination (`#tate-count-selector`,
  `#uniform-tate-positivity`, `#tate-domination`), bidegree/definite/Siegel/isotropic counts
  (`#bidegree-counts`, `#definite-counts`, `#siegel-majorant`, `#isotropic-poisson`), Witt integrality
  (`KR-WIP`).
- **Critical-family shortcuts:** `#conductor-count-resolution`, `#critical-pencil-nullspace`,
  `#low-conductor-deletion`, `#prime-pole-cost`, `#charge-complement-vanishing`, `#fixed-packet-bulk`,
  `#twisted-horizon-blindness`, `#critical-pole-collar-budget`.
- **Producers:** integrality alone, fixed factorial ratios, univariate sup-norm, fixed-prime stencils, Adams
  multiplicity, base-change twists, `#pole-matching-half-power`.
- **Reflection:** `#cauchy-reflection-order`, `#window-krein-reflection`, `#mayer-krein-sign`,
  `#lewis-inversion`, `#farey-three-term`, `#resonant-cutoff-gram`, `#scattering-schur`,
  `#scattering-recentering`.
- **Continuation:** `#lattice-interior-gap`, `#positive-model-homotopy`, first Laguerre inequality as
  certificate, fixed cross-load for theta rank 9 (`#theta-fixed-cross-load` [W]).
- **Selection without sign:** every selector; regular integers; bounded apertures against Euler columns.

## 1. The picture

| Fact | Anchor | Consequence |
|---|---|---|
| RH ⇔ every two-site lattice window PD ⇔ `|c_φ(t)| < Q(φ)` for every bump and `t ≠ 0` | GWZ `riemannHypothesis_iff_two_site_posDef`, `riemannHypothesis_iff_abs_weilOrbitCorr_lt` [L] | the minimal decisive object is a reflection pair |
| `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; sectors of `[−a, a]` = band at the centre | SWC [L] | the band is the smoothed prime count of `f⋆f` matching the pole square within `W(f)` |
| Sharp prime-free half-window: `primeSum f = 0` for all `f` on `[−c, 0]` iff `c ≤ log 2` | SWC `primeFree_halfWindow_iff_le_log_two` [L] | below window length `log 4` the right side `W(f)` is purely archimedean–polar |
| For `0 < c < log 2`: window positive ⇔ `(Λ(2)/√2, Λ(3)/√3) ∈ belowLogFourBandWeights c` = `oddBandWeights ∩ evenBandWeights`, convex; compact for `c > ½log 3`; excludes `w₂ ≤ 0` for `c ≥ 21/40` | SWC `zetaWindowPositive_iff_mem_belowLogFourBandWeights`, `isCompact_belowLogFourBandWeights`, `not_mem_belowLogFourBandWeights_of_nonpos` [L] | the first stages are a two-number problem: two prime terms must reproduce the collar Hankel form within the archimedean energy |
| Retained-variance even theta gauges (even sector) and shifted ground states (odd sector) are exact certificates ⇔ positivity below `log 4`; variance-dropped certificates fail for `c > 273/400` | SWC `zetaWindowPositive_below_log_four_equivalences`, `exists_two_odd_tests_halfNormDual_neg_below_log_four` [L] | the certificate format is settled; only the arithmetic membership is open |
| Edge law: `(f⋆f)(−ℓ) = ∫_I(f₊² − f₋²)`; `w_n|(f⋆f)(−log n)| ≤ (Λ(n)e^c/(2n))·levyEnergy f`; `{2,3}` together `≤ (log2/2 + log3/3)·levyEnergy < ¾` | SWC `selfConv_neg_eq_sliver_signature`, `vonMangoldtAtom_mul_abs_selfConv_le`, `twoThree_kicks_le_levyEnergy` [L] | the summed bound on the reflection terms is below the Lévy energy exactly on windows shorter than `log 5` [D]; the primes pay by sign, not by size |
| Soft entry: a sector margin `η` admits any newest weight within `ηΩ(2c − log p)`, `Ω(δ) ≥ (e^{−1/2}/2)log(1/δ)` | SWC `mem_bandWeights_of_margin_log` [L] | stage induction is margin transport; margins `~10⁻⁵–10⁻⁸` [N] carry the prime `3` only on a sliver of width `≈ exp(−2.1/η)` [D] |
| Sectors are moment problems: even ⇔ Hamburger, odd ⇔ shifted Hamburger, window ⇔ Stieltjes for `s_k = W(φ^{(k)})` | SWC `even_nonneg_iff_hamburger`, `odd_nonneg_iff_shiftedHamburger`, `window_nonneg_iff_stieltjes` [L] | a nonnegative window gives every even bump a spectral measure on `[0, ∞)`; the pole sits at `x = −¼` |
| No smooth window eigenfunction, constrained ground state or capacity maximizer; nonnegative windows PD on smooth tests; strict band on smooth tests | SWC `eq_zero_of_isWindowEigen`, `not_isCapacityMax`, `weilQuad_pos_of_window_nonneg` [L] | the decisive extremals live in the energy completion, singular at the window edge |
| Lattice canonical system: margins `h^{−2n}E_n → det J_{n+1}/det J_n`, reflection coefficients `γ_n → (−1)^n`, `(1 − γ_n²)/h² → e_{n+1}/e_n`, block split by parity | SWC [L] | the canonical system freezes on the boundary of the Schur disk; local continuum limit solved |
| Complete Weil matrix PD on the whole prime-horizon space at one critical multiple; RH ⇔ window threshold `R₁(A) = ⊤` ∀A; complete terminal source polar | AHD/CACT [L] | every HF layer below the sign is size-only |
| `Q ≥ −C(p)∫e^{p|u|}H²` for `p > 1`; exponent `p` gives zero width `≤ p` | WTZ, SquareRootThreshold [L]; [D] | the size-only floor carries no zero information |
| Window positivity at `R` excludes depth `≥ 1/R` up to height `exp(R/(10⁵A₀(log R)²)) − 306`; the fall rate of the window ground energy is the zero width (two-sided for finitely many off-line zeros); deep zeros are seen at doubly exponential heights | SquareRootThreshold `zeta_abs_re_sub_half_lt_of_zetaWindowPositive`, `polarGroundEnergyRate_eq_zetaZeroWidth_of_offLineCopiesLocallyBounded`; DCI [L] | windows read depth, not height: an isolated zero of depth `δ` at height `T` is seen at half-width `≈ (1/2δ)log log T` [D] |
| PM: `Q(H) = 2Re[𝓦H, 𝓦H]` on `ℓ²(upper resonances)`; defect formula `D_s = −∫2cosh(δu)4sinh²(δu)|F(u)F(−u)|`; retained `T₂` channel has sign of `¼ − Re s` | RIT `weilQuad_eq_completedKreinForm`, `lewisCoIsometryDefect_eq_neg_log_integral`, `retainedHeckeChannel_defect_sign` [L] | PM's line condition is an identity in `δ`; arithmetic must supply a second expression |
| Camera: cancelling clusters have upper uniform density `≥ 2a/π` (sharp); blind windows exist exactly above `πD`; fakes separated exactly above `½log n₀` | ZCG `eq_of_mimic_of_count_le`, `blind_aperture_threshold`, `arithmeticImage_eq_iff` [L] | identification is a density statement; for `ζ` at height `T` the threshold `a = ¼log(T/2π)` is `λ = ½` [D] |
| Positivity at one aperture `a > πD` puts thin configurations (perturbed lattices, columns) on the line; one column pair needs `a > πD/2`, sharp | SquareRootThreshold `re_eq_half_of_re_W_nonneg_of_columns`, `offLineLattice_re_W_nonneg` [L] | sign-based visibility has the same density threshold |
| Heat path real for `t ≥ 1/8`; RH ⇔ every zero of `H_t` simple ∀t > 0; `c·d²/log X ≤ Λ_X ≤ (2/3+ε)/log X`; `H_t` non-real for `t < 0` | RHTower DeBruijn [L] | the heat path is exactly critical at `t = 0` |
| Function field: camera identifies at the genus; bounded images certify purity; purity leaves only through collision; integral configurations collide or repel | ZCG [L] | over `𝔽_q` collision exclusion comes from integrality of the image; for `ζ` the image is a `log p`-weighted sum |
| Dimension zero: bare domination ⇔ `Q ≥ 0`; no archimedean family dominates Tate counts | ATD, DZG [L] | counts closed [D] |
| FE + positivity determine `ζ`; positive primes with regular integers allow off-line zeros | APD, RHTower Beurling [L] | a proof uses the functional equation and the Euler product together |

## 2. Shared obstacle blocks

### S0. The two-site band and reflection pairs
Routes: every route of C1, C4, C7, C14, C15, C19.

Established [L]: RH ⇔ two-site PD ⇔ strict orbit Cauchy–Schwarz; one generic bump decides; eventual
boundedness of its orbit correlation decides, rate = zero width; `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; band
unconditional for short pairs (`abs_coupling_le_weilQuad_of_short`); parity sectors are the band at the
centre; a tight band on a nonnegative window gives a reflection-pair zero mode; on a nonnegative window
the band is strict on smooth tests and no smooth zero mode exists.

Status: a reformulation of the classical criterion (smoothed `ψ(x) = x + O(√x)` in a fixed multiplicative
window, constant `W(f)`).

| | Obstacle | Strength |
|---|---|---|
| A29 | Bridge: reflection-pair coupling = smoothed prime count → WL/JAS/CTF/PBM/RB receivers | — |
| A30 | Two-site band on a bounded step range from numerical zero data and explicit tails (decides nothing) | — |
| B1 | The band at every step and every test | RH |
| B10 | No zero mode at any length (≡ no degenerate two-site lattice) | RH |

### S1. Complete Weil family at the critical curve
Routes: HF, SRT, AIP, ACT (index), ACS-atomic, RW-atomic, SC, CHMD (index), FEL, MSC. Programmes:
CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF, V.

Established [L]:
- Subcritical PD for `1 ≤ c ≤ (log N)^α`, `α < 1/8`, floor `κ/(2c⁷)`.
- Whole-space PD at one critical multiple `2K₀(log N)^{1/8}` with every window corollary (horizon Grams,
  pencil index `0`, weighted sign on windows of every length, mixed families).
- Window threshold `R₁(A) = inf{7J(1)M₈(H)/(a_φ|Q(H)|) : Q(H) < 0}`; antitone; `≥ R₀ > 0`; `= ⊤` up to
  `2·enlargedWeilFloorAperture`; RH ⇔ `R₁ ≡ ⊤`; joint pole payment strictly enlarges the certified interval.
- Critical-curve second order `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²`; twisted sectors positive Hurwitz counts;
  frequency counts have a pole of order `β+1` at `u = 0` with finite part the untwisted count.
- Growing overlap: bulk entries `E_e(c)⟨R_e, R_{e'}⟩ + [e = e' = 1]κc(2 + γ − log 4π) + o(c)`.
- **Terminal windows:** every compact logarithmic window has an exact complete mixed limit at all
  positive critical ratios; the polar source keeps its boundary logarithm and a finite prime-power mean;
  every fixed nonpolar source vanishes (full centre and divisor jet cancel); a nonzero polar source exists;
  the polar source has a nontrivial kernel. Channel laws: no upward primes above half the horizon, no
  exterior primes away from it, finite prime boundary mass, prime means are finite Riemann sums.
- **Conductor packets:** terminal sources concentrate at the pole through exponent `13/32`; summable
  conductor sources; vanishing mixed mass above overlap; low correctors cannot improve zero-source
  windows; exact low-packet capacity attained by one pole coefficient; full conductor diagonal overprices
  terminal windows.
- **Receiving charges:** charges survive vanishing raw, physical and complete energy; capacity
  `log log N + O(1)`; simultaneous receiving law (factorial exclusion, cutoff `R!X²`, horizon `X⁴⁰`,
  reading factor `1/80`); complete physical energy vanishes for independently growing cutoff and horizon;
  exact neutral mixed-channel decomposition with bounded Mertens correction; receiver determinant
  `→ 6239t²/6400 > 0`. Sieve inputs (V): Brun–Titchmarsh-type progression bounds to large prime moduli,
  residue covariances, affine collision mass, proper prime-power tails `H^{−7/16}`.

Killed: `#conductor-count-resolution`, `#growing-overlap-floor`, `#fixed-packet-bulk`,
`#critical-pencil-nullspace`, `#twisted-horizon-blindness`, `#defect-capture`, `#overlap-gram-smoothing`,
`#separate-shell-payment`, `#absolute-prime-correction`, `#prime-pole-cost`, `#prime-residual-scale`,
`#logarithmic-floor-budget`, `#low-conductor-deletion`, `#charge-complement-vanishing`,
`#critical-pole-collar-budget`, `#full-conductor-diagonal`.

Status: every layer below the sign is size-only and classified. HF's sign content is `R₁ ≡ ⊤`, i.e. Weil's
form on untwisted windows at every multiple. The far-complement estimate loses `O(c)` against its
`O(log N/c⁷)` reserve (frontier map).

| | Obstacle | Strength |
|---|---|---|
| A1 | Explicit constants and horizons: `K₀`, eighth-root theorem, `1/9`, logarithmic profile, Beurling schedule, horizon criterion, conductor range `M(N) = o(c_N)` | — |
| A2 | General profiles past `θ = 1/1080` | — |
| A3 | Joint twist families; equal-parity characters through `L(s, ψ̄₁ψ₂)`; different moduli | — |
| A4 | Certified ratio interval at its size-only optimum and the assembly of the receiving-charge complement inside it (difficulty unverified) | — |
| A9 | AIP channel norms: average literal prime bands, small multipliers, offset-dividing primes, offset cardinality and periodic errors with the V-sieve bounds (difficulty unverified) | — |
| A10 | Window index as a counting function of the length | — |
| B6 | Twisted-sector positivity through all conductors and frequencies at every multiple | sub |
| B7 | Full-space sign at critical ratios beyond the size-only threshold (each ratio sub; all ratios RH) | sub / RH |
| B8 | General profiles past `log log N` on the full space | sub |
| B9 | Exact SOS on one two-prime lattice | RH |
| B16 | Window negativity exponent `< ½` in the length (≡ zero width `< ½`) | ≥qRH |
| B33 | HF-native arithmetic sign: the pencil positive at one ratio beyond the size-only interval, or the floor at exponent `p = 1`, with prime input | sub |

### S2. The window tower, its canonical system and signed criticality
Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT, HF, ACS, SRT, SZ, MSC. Programmes: CWS, WTZ, DZG, GWZ, CSTW,
SWC.

Established [L]:
- Window datum, truncated Dirichlet λ-ring, stage transfer, exit charge, sharp floor, Hecke-graph
  reading, Tate horizons at stages 1–2; stage criterion `2wc_H(ℓ) ≤ S^N_A(H)`; kick = collar Rosati
  pairing; frozen form in closed form; translation contraction.
- Lattice canonical system (Levinson, Schur parameters, outer predictors, single-kick law); window ⇔ its
  lattices; lattices Szegő singular under RH; zero modes radical, reflection parity, gap law.
- Continuum: jet Hankel limit; jet Gram PD and jet minors positive on every nonnegative window and on the
  base; jet energies strictly log-convex; reflection coefficients `→ (−1)^n`; even/odd block split
  `det J_n = det E·det O`, each block PD once its sector is nonnegative.
- Sectors ⇔ Hamburger / shifted Hamburger; window ⇔ Stieltjes moment problem of jet energies.
- Gamma ladder: `A(g)‖g'‖² ≤ A(g')‖g‖²`; Gamma floors transfer even → odd → even mean-zero; the pole adds
  its positive square to the even sector and its negative square to the odd sector.
- Base: all real `C²` tests positive through length `181/250·(1 + 6·10⁻⁷)`; floor `‖f‖²/8000` up to
  `enlargedWeilFloorAperture`.
- First stage (length `21/20`): admissible prime-two weights an interval excluding `0` and `−w₂`.
- Odd unit window `[−½, ½]`: `‖F‖²/1000 ≤ Q(F) + (3203/320)(∫xF)²`; `Q ≥ ‖F‖²/100` off two odd moments;
  exact retained-Gamma identity; higher reserve; positivity ⇔ `w₂ ∈ unitBandWeights` (convex).
- **Below `log 4`:** sharp prime-free half-window at `c = log 2`; positivity ⇔ two-weight band ⇔
  `{2,3}` Markov–Hankel form ⇔ retained-variance certificates ⇔ Hodge index of the scaling subsurface ⇔
  Künneth effectivity; admissible set convex, compact for `c > ½log 3`, excluding `w₂ ≤ 0` for
  `c ≥ 21/40`; sector sets cylinders in `w₃` for `2c ≤ log 3`; soft entry with tolerance `ηΩ(2c − log 3)`.
- **Edge law:** sliver signature `(f⋆f)(−ℓ) = ∫_I(f₊² − f₋²)`; outward jumps carry the newest prime power
  at ratio `w_ne^h/2 ≤ e^{h−1}` within `h` of entry, collar-internal jumps at `2w_ne^h` (sharp); `{2,3}`
  kicks `≤ ¾` Lévy energy.
- Gauge calculus: pole-charged representation; theta gauges critical on the line; outside charges (odd
  slack, even deficit); shifted ground states strict with slack `τ_c(a) > 0`; dropped variance is the
  all-pairs jump form `∫∫m(x)m(y)(u(x) − u(y))²`; gauge-extension invariance of the certificate sum.
- Markov part negative on a test of support `e^{−3/4}`; no Markov supersolution on longer intervals;
  kick = positive source `2w∫hh∘τu²` minus anti-diagonal conductance.
- Regularity: no smooth window eigenfunction, constrained ground state or capacity maximizer.

Killed: `#frozen-gamma-cubic`, `#retained-gamma-lower-form`, `#first-fold-linear-chord`,
`#fold-count-identity`, `#folded-markov`, `#prime-free-markov`, `#folded-origin-charge`,
`#collar-positivity-induction`, `#collar-local-payment`, `#prime-three-sliver-potential` [W],
`#variance-dropped-theta-gauge`, `#theta-gauge-cosh-defect`, `#smooth-window-attainment`, `KR-BD`, `KR-LGP`,
`KR-PAF`, `KR-CCP`, `#lattice-positive-slack`, `#lattice-interior-gap`, semilocal positive factors, fixed
finite-prime positivity.

Status: the stage step, its certificate format and its ground-state calculus are exact. Below `log 4` the
whole problem is the membership of one explicit point in an explicit compact convex set. Summed over all
acting prime powers the edge-law bound on the reflection terms stays below the Lévy energy only for windows shorter than `log 5`
(`(e^c/2)Σ_{n ≤ e^{2c}}Λ(n)/n < 1`) [D]; beyond, and already below, the primes pay by the sign of their
reflections, and summed over a reflection pair the anti-diagonals are the smoothed prime count in
`𝒞_m`: P1 meets P4.

| | Obstacle | Strength |
|---|---|---|
| A5 | Rigorous computer-assisted certificate of `(w₂, w₃) ∈ belowLogFourBandWeights c` for `c ∈ (enlargedWeilFloorAperture, log 2)`: an operator inequality on `L²[−c, 0]` with explicit kernels (Gamma symbol, pole and trivial-zero squares, two reflection kernels); margins `1.5×10⁻⁵` (odd), `5.6×10⁻⁸` (even) at `c = ½log 3` [N] | — |
| A6 | Rational Hecke graphs and Tate horizons of stages 3, 4, 5, 7, … | — |
| A7 | Closed form of the first-stage complement `Φ_ε` | — |
| A8 | Even-sector counterparts of the odd identities: cosh-credit supersolutions with retained variance (difficulty unverified) | — |
| A28 | Atomic-lattice bound `λ_max ≤ ½log N` | — |
| A33 | Lévy sector margins `η` at `c = ½log 3` in both sectors, feeding soft entry (numerical) | — |
| A34 | Tilt-amplification excluded-depth law: positivity at half-width `a` excludes every isolated zero with `2δa ≥ log(Cδ log|γ|)` (bounded local off-line count) (difficulty unverified) | — |
| B2 | Kick admission at every stage | RH as induction; each stage sub |
| B3 | Frustration domination at every length: a gauge, with retained pole variance, in which the signed sliver reflections of all acting prime powers pay the collar Hankel form, odd and even | RH; fixed length sub |
| B4 | Structural certificate of the odd unit window (`w₂ ∈ unitBandWeights`) | sub |
| B5 | Structural certificate below `log 4`: `(Λ(2)/√2, Λ(3)/√3) ∈ belowLogFourBandWeights c` for `½log 3 < c < log 2`, the prime `3` paid by the sign of its reflection | sub |
| B17 | Global continuum canonical system of the tower (Hamiltonian with the prime kicks) | identity |
| B18 | Contact law: RH to height `T` ⇒ every window of length `c log T` positive. A deep isolated lowest off-line zero just above `T` is seen at length `≈ (1/δ)log log T`, so B18 forces every lowest off-line zero to be shallow or hidden in a spread structure [D] | RH-adjacent [D] |
| B47 | Sharp visibility (onset) law: the first-failure aperture of the windows as a function of depth, height and coherence of the off-line zeros | sub |

### S3. Dimension zero, counts and the Hodge index
Routes: ACS, HF; programmes WTZ, DZG, ATD, AHD, LST, KPA.

Established [L]: Tate jet and signed-count forms; bare domination ⇔ `Q ≥ 0`; no uniform Gamma–pole
domination; Euler-product pole weight forced and refuted; Künneth `h¹ = ½Q`; bidegree, fixed-rank,
definite and Siegel counts excluded; finite-square count identities refuted; Künneth effectivity of a
curve window ⇔ unitarity; below `log 4` window positivity ⇔ Künneth effectivity ⇔ Hodge index of the
scaling subsurface. Degree-zero height principles: integral and window Rosati forms bounded above are
`≤ 0`; comparisons with sublinear error are exact (`windowRosati_eq_smul_of_degree_zero`).

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
window index finite, monotone, exhausting, `sup = κ`; `{0, ∞}` laws; index `≤ R + A` on `R` coarse cells;
growing Euler heads unbounded.

Killed: `#growing-euler-index`, fixed-complexity ceilings, positive group-kernel repair, local tower
ceilings, pointwise index conservation, `#tensor-square-inertia`.

| | Obstacle | Strength |
|---|---|---|
| B12 | Index ceiling uniform in resolution | ≥qRH; RH (tensor) |
| B13 | Zero–one law `κ ∈ {0, ∞}` | sub |

### S6. Window energy, near-line density and the Hecke defect
Routes: WD, LA, TG, HCF, SC-heat, TH-heat; census; HEF.

Established [L]: window integer = Wiener–Hopf index; pair resolvent = Laplace transform of `|𝒵|²`; Cauchy
cap cancellation down to `σ_m = 1 − 1/(116 log(m + 5))` with right half-port `O(e^{(σ_m−½)t}/(t+1))`;
exponent `3loglogV/logV` outside `O(V/loglogV)` windows; exact critical-line flux on micro-Planck windows;
zero-free window ⇔ unweighted `L²` port; bounded port ⇔ critical-line purity; polynomial-stage TFAE ⇔ RH;
fixed degree ⇔ corridor `|Re ρ − ½| ≤ C/|Im ρ|^k`; eight equivalent near-line density forms;
`D_win` ⇔ almost-all log-stage certificates ⇔ thin Planck shadows; `D_zero` ⇔ `D_win` + vanishing
cluster tail; per-window deep-order second moment with sharp `(log V)²` [M].

Killed: `#theta-prefix-sectoriality`, `#theta-seam-smoothing`, `#fixed-log-defect`, `#counts-only-defect`,
`#antinodal-prime`, `#unfolded-euler-mollifier`, `#theta-uniform-prefix`, `#window-port-reflection`,
`#window-port-l2`, `#holomorphic-carriers`, `#window-density-separation`, `#holomorphic-jensen`,
`#superharmonic-halfstrip`, `KR-R3`, `KR-HUS`, `KR-LLM`.

Status: WD's RH content is right-port cancellation through `[½, σ_m]`, the zero-free region pushed to the
line [D]. `D_zero` is a log-free near-line density (Selberg-type density counts `≍ e^{−cA}V log V` zeros
at depth `≥ A/log V`; `D_zero` asks `≤ ε(A)V`) [D].

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

Established [L]: one-sided count ⇔ RH; multivariate parity producers reach `(1+ε)x + C_εlog²x`;
individual producers slope `> 1`; integer-Chebyshev ceiling; Redheffer `det = M(N)`; every eventually
positive cyclotomic band has abscissa `2Θ`; pole-subtracted exponents over the gauge torus range exactly
over `[Θ, 1]`, minimized at the trivial point; flip points share the pole to precision `N^b` and have
Möbius exponent `max(θ, Θ)`; an explicit non-special gauge point has Möbius exponent `½`; simple-critical
proportion `≥ 0.67250071` (imported Zeta23 inputs).

Killed: PNT/short intervals, size-only inversion, stronger-than-half-power target, integrality alone, fixed
factorial ratios, sup-norm, fixed-prime stencils, Adams multiplicity, base-change twists, gauge averages,
Vaughan endpoints, `#quasi-character`, `#single-height-saving`, `#positivity-three-quarters`,
`#frullani-phase`, `#pole-matching-half-power`.

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
`⊆ {Λ}`; lattice selection; PBAP ⇔ RH, node-critical, Farkas-dual, solved on nonnegative and separated-bump
cones; Selberg-class Euler rigidity at `σ = ½`; degree gap `(0, 1)`; degree one has conductor `≥ 2` or a
pole; Beurling and Hamburger rigidity; Legendre invariant `J(ρ)` real at every zero ⇔ RH.

| | Obstacle | Strength |
|---|---|---|
| A11 | Function-field calibration | — |
| A12 | Gaussian-damped coupling identity | — |
| A13 | Finite-level Weil cones `C_A` and their widths | — |
| A31 | Selberg-class degree-one classification (coefficient periodicity, integer conductor, primitive-character identification) | — |
| B30 | Bounded damped cone coupling; unattained width | RH |
| B31 | Finite-sieve Hodge positivity → global | RH |
| B34 | Rosati positivity of the window reflection | RH |
| B36 | Selection at the trivial gauge point | RH |
| B37 | FE twins inside the full class with off-line zeros | sub |
| B42 | Prime-blind positivity on signed blind combinations | RH |

### S9. Realization and scattering
Routes: PM, RN, PTR, W1C.

Established [L]: Mayer operator, faithful divisor; resonance ⇔ `ζ(2s) = 0`; core whole-Haar admission ⇔
resonance; exact completion `Q = 2Re[𝓦H, 𝓦H]`, cores dense, window map bounded, Hecke multiplier
`p^{1−2s}`; window involution = twisted conjugate Krein reflection; `I_s` isometric iff `Re s = ¼`;
co-isometry defect `D_s(ψ_s) ≤ 0`, `< 0` iff `Re s ≠ ¼`, with the exact formula
`D_s(ψ) = −∫_0^∞(e^{δu}+e^{−δu})(e^{δu}−e^{−δu})²|F(u)F(−u)|du`; Krein self-pairing of the resonant basis
`1` on `Re s = ¼`, `0` off it; window tests lift to `+1` fixed periods whose defect dominates
`((n^δ+n^{−δ})(n^δ−n^{−δ})²/4)(foldSym − foldEnergy)`; corrected all-prime transport, eigenvalue
`1 + p^{1−2s}`; retained `T₂` channel `D_s(u_s) = |core_s(2)|²Φ(Re s)` with the sign of `¼ − Re s`,
opposite at the reflected resonance; physical cusp residue = Krein square, Gaussian residue → complete
Weil form.

Killed: `#cauchy-reflection-order`, `#mayer-krein-sign`, `#core-hecke-boundary`, `#lewis-inversion`,
`#farey-three-term`, `#hecke-window-cusp`, `#window-krein-reflection`, `#resonant-cutoff-gram`,
`#fixed-height-hecke-residual`, `#mayer-cutoff`, `#mayer-complex-contraction`, `#scattering-recentering`,
`#scattering-schur`, `#congruence-pole-filter`, `KR-AUT`, `KR-SEL`, local PM admission/escape.

Status: P3 reduces to `D_s(ψ_s) = 0` at resonances, which by the defect formula is `δ = 0` itself. The
analytic expression of the defect is manifestly `≤ 0`; a proof needs an arithmetic expression of the same
quantity at resonances with manifest sign `≥ 0`. The retained channel reads the side of a resonance [D].

| | Obstacle | Strength |
|---|---|---|
| A14 | Classical identifications (Selberg-zeta normalization, Lax–Phillips, Lewis–Zagier, `+1` eigenspace, Garland); mixed-parameter completion; full Mayer transfer compatibility; analytic completion of the corrected boundary carrier; rational Weyl identification | — |
| A15 | Operator-native nonvanishing on `Re w = 1` (risk: reduces to the Euler product) | — |
| B38 | A second, arithmetic expression of `D_s(ψ_s)` at resonances with manifest sign `≥ 0` (finite cusp energy ⇒ zero defect) | RH |
| B39 | Statistic of resonant states selecting the decay rate | method |
| B40 | Source-faithful realization of unbounded rank | RH |
| B46 | PM-native zero-free region for `ζ(2s)`: an arithmetic upper bound on `|D_s(ψ_s)|` relative to its cross mass that excludes resonances with `Re s > ½ − c/log|Im s|` (`δ = 2Re s − ½` is the depth `Re ρ − ½` of `ρ = 2s`) | sub |

### S10. Zero-configuration geometry and deformation
Routes: ZCG (candidate), LA, TH, HCF, XN, SRT; programmes ZCG, RHTower DeBruijn, SquareRootThreshold.

Established [L]:
- Camera: depth is tilt; pairs analytic in `w²`; second-order law `pairSignal = −w²M₂(f, c) + O(|w|⁴r⁴)`.
- Blindness: count bound `(D, C)` ⇒ blind windows at every aperture `> πD` (Hall matching into `D⁻¹ℤ`, no
  separation); Jensen: a nonzero window blind to lower density `D` has aperture `≥ πD`; exact threshold
  `πD` for uniform density at depth `≤ ½`; no nonzero window blind to the real zeros of `Ξ`; blind windows
  ⇔ entire functions of exponential type vanishing on the set (Paley–Wiener).
- Identification: finite modifications at every aperture; isolable clusters, simple-zero-set clusters,
  perturbed-lattice clusters plus finitely many points never cancel; cancelling clusters have upper
  uniform density `≥ 2a/π`, sharp by the on-line lattice pair; mimics contain two points of different FE
  orbits closer than any `g > π/a`; shallow configurations resolved at the Ingham scale `π/(2a)`, optimal;
  fakes (flips, Euler twins, Beurling data) separated exactly above `½log n₀`; a configuration with the
  image of data first differing from `Λ` below `e^{2r}` is not `ζ`'s.
- Local camera [W]: modulated windows; the part of a cluster at height distance `> R` from `X` contributes
  `≤ (5/4)C_fC_ge^a(1+|X|)²(1+R)^{−(2k−2)}Σ|c(z)|/(1+|γ_z|²)`, for `ζ` explicitly; perturbed-lattice
  products on the strip bounded above and, at isolated points, below.
- Positivity certifies: isolated tilts make the image negative; positivity at one aperture `a > πD` puts
  thin configurations on the line; one column pair threshold `πD/2`, sharp.
- Function field: camera identifies at the genus; pure and tilted mimics below; bounded images certify
  purity; purity closed and lost only at a Frobenius collision; integral configurations collide or repel
  at distance `≥ (4√q)^{−((g−1)²+g−2)}`.
- Euler stages `Λ_X = A_X(s) + A_X(1−s)`: phase law; above the horizon `log(t₀/2π) > 6/t₀ + W(X)` every
  line zero is simple, gaps in `[π/M, π/m]`, exact count; nothing below the horizon `≈ 2πe^{W(X)}`.
- Deformation (polynomial model): reality leaves only through collision; heat keeps centre, raises
  spread; Laguerre/heat steps never deepen nor shrink the mesh; shift averages contract squared depth.
- Heat path of `Ξ`: real for `t ≥ 1/8`; RH ⇔ every positive-time zero simple ⇔ zero collision mass ∀t > 0
  ⇔ `Λ_X = 0` ∀X; `c·d²/log X ≤ Λ_X ≤ (2/3 + ε)/log X`; global depth energy antitone; non-real for `t < 0`.

Status: identification is sign-free and is a density statement; sign visibility is a depth statement —
an isolated off-line zero of depth `δ` makes a window of half-width `≈ (1/2δ)log log T` negative, and only
spread lattice-like off-line sets hide up to `¼log T` [D]. For `ζ` the local density at height `T` is
`(1/2π)log(T/2π)`, so pair isolation requires aperture `a > ¼log(T/2π)`, the camera exponent `λ = ½`, half
the Riemann–Siegel log-length [D]. Local inversion is a quantitative race between the isolated-point lower
bound of the perturbed-lattice product (losses governed by the local count excess, `≍ log T`) and the
polynomial decay of the far tail; integer multiplicities convert approximate isolation into exact
vanishing once the tail is below the signal [D]. ZCG's RH content is reality at near-collisions, the
P5 mechanism; over `𝔽_q` it comes from integrality of the image, which `ζ` lacks.

| | Obstacle | Strength |
|---|---|---|
| A16 | Local camera at bounded height ranges: assembly of far-faintness, strip products, isolation and integer rounding with explicit constants; perturbed-lattice blind windows; function-field camera extensions (difficulty unverified) | — |
| B14 | Laguerre–Pólya at all ranks and degrees; collision exclusion along a source-faithful path (heat path on `(0, 1/8]`; `Λ_X = 0` at every height) | RH |
| B43 | Local inversion at the density scale: images agreeing at aperture `λ·½log(T/2π)`, `λ > ½`, determine the zeros near `T` outside near-collision clusters, uniformly in `T` | sub |
| B44 | Reality at near-collisions: the sign of `w²` at every cluster, read at all orders through the prime channel | RH |

### Route-specific items
| | Obstacle | Routes | Strength |
|---|---|---|---|
| A17 | Theta Hankel rank 9: a variable cross-load (or other repair) on the compact source gap; the fixed cross-load fails at scale `q = 8` [W]; native fifth even source PD for `q ≥ 5`; ranks `≥ 10` at fixed apertures (difficulty unverified) | TH | — |
| A18 | Hausdorff shifts, Jensen horizons, two-grid degrees, PF beyond 37 | PA, LA, HCF | — |
| A19 | Nine atom-dominated collar moduli | ACT | — |
| A20 | Mixed Schur debit; first-prime/coarse/polar costs | AIP, CHMD | — |
| A32 | Receivers marked unfinished in the frontier map: Cayley–Li primitive-sign receiver, SZ first-variation transfer | LI, SZ | — |
| B15 | Scheduled prime energies bounded below | FU, CFC, RP, SZ, LI, FEL, EGC | RH |
| B41 | Pre-divisor forcing | APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF | RH |

## 3. Live routes

Each entry: path; established; open estimate; killed shortcuts; class; A; B.

### WL — Weil lag
- Path: prime error → square-root bound or subexponential critical energy → RH.
- Established: exact prime-error/energy criteria; first Chebyshev cyclotomic band abscissa `2Θ`, RH ⇔ its
  energy `O_ε(N^{1+ε})`; gauge-torus exponents `[Θ, 1]`, minimized at the trivial gauge; reflection-pair
  coupling = smoothed prime count of `f⋆f` against the collar Hankel form [L].
- Open: signed square-root precision of one band; a gauge attaining exponent `½` at the arithmetic point.
- Killed: PNT/short intervals, size-only inversion, producers of slope `> 1`, integrality alone,
  base-change twists, `#pole-matching-half-power`.
- Class P4. A: A25, A29. B: B1, B26, B27, B32.

### RW — restricted Weil ground energy
- Path: `μ(a) ≥ 0` at every radius → RH.
- Established: attained radius-decreasing minima; floors through `enlargedWeilFloorAperture`; exact
  `{∞, 2}` trace through `½log 3`; window ⇔ lattices; two-site decision; odd/even sign ⇔ `C ≤ Q` / `−C ≤ Q`;
  below `log 4` positivity ⇔ two-weight band ⇔ retained-variance certificates, sharp prime-free boundary
  `c = log 2`; sectors ⇔ Hamburger/Stieltjes jet moments; smooth extremals excluded; jet minors positive
  and reflection coefficients alternating on nonnegative windows [L].
- Open: an all-test coupling bound paying the signed prime folds; actual-weight membership below `log 4`;
  outward-edge bounds control kick sizes but need a full sector margin.
- Killed: `#lattice-positive-slack`, `#lattice-interior-gap`, `KR-PAF`, `KR-CCP`, `#fold-count-identity`,
  `#frozen-gamma-cubic`, `#folded-markov`, `#collar-local-payment`, `#collar-positivity-induction`,
  `#prime-three-sliver-potential`, `#smooth-window-attainment`, semilocal factors, fixed finite-prime
  positivity.
- Class P1. A: A5, A7, A33, A34. B: B1, B2, B3, B4, B5, B47.

### FU — signed prime scheduling
- Path: signed prime/Möbius history → one-sided sampled Abel bound → RH.
- Established: for each fixed `m ≥ 1`, upper or lower boundedness of `A(j^m)/j^m` ⇔ RH; one controlled
  sample per backward window of length `N^{1−δ}` suffices [L].
- Open: produce those samples from the complete signed history (seed, drift, covariance, endpoints).
- Killed: prime scheduling/curvature, pointwise Abel-clock positivity, polynomial capture.
- Class P4. B: B15.

### CFC — first-clock lower bound
- Path: first-clock sine coefficient bounded below on an aperture tail → RH.
- Established: exact tail criterion; unboundedness below under ¬RH; phase-natural transport is the
  identity [L].
- Open: a lower bound retaining prime, archimedean and endpoint terms.
- Killed: retired label A.
- Class P4. B: B15.

### RP — history floor
- Path: matched-quantile prime history → eventual linear defect floor → RH.
- Established: linear-floor criterion; low-LCM and copied-diagonal payment; sublinear floor impossible [L].
- Open: high-LCM pairs, moving core and singular-domain terms in one complete-history floor.
- Killed: sublinear history floor.
- Class P4. B: B15.

### PA — prime–archimedean passivity
- Path: prime − archimedean trace → current sign or subexponential mismatch → RH.
- Established: exact receivers; each fixed Hausdorff order positive at large shifts [L].
- Open: all-order/all-shift sign; order-dependent thresholds leave a signed high-frequency complement.
- Killed: `KR-FPR`, `KR-TK`, retired labels D1, C2/I.
- Class P5 (order limit). A: A18. B: B14.

### MC — Möbius cancellation
- Path: Möbius/Liouville cancellation at half power → RH.
- Established: half-power and Redheffer criteria; square-root-cutoff short divisor head with bounded
  pronic energy; Möbius exponent Haar-a.e. `½`, Baire-generic `1`; an explicit gauge outside every finitely
  modified Dirichlet/vertical orbit has exponent `½`; flip points sharing the pole of `0` have exponent
  `max(θ, Θ)`; sparse-prime transfer [L].
- Open: half-power cancellation at the trivial gauge; uniform signed long-modulus energy for dampings
  cofinal at `0`.
- Killed: gauge averages, stronger-than-half-power target, uniform escaped decay, Vaughan endpoints,
  additive shift, `#quasi-character`, `#single-height-saving`, `#pole-matching-half-power`.
- Class P4. A: A21, A22. B: B26, B27, B32, B36.

### TT — theta tail / Wold
- Path: theta source → directed covariance/Wold decay or odd Weil sign → RH.
- Established: exact receivers; Φ-Doob identities retaining every reflected prime term; restricted current
  signs; odd sector = band at the centre ⇔ shifted Hamburger moments; odd theta gauges have window slack;
  below `log 4` the odd sector ⇔ `oddBandWeights` membership ⇔ retained-variance shifted-ground-state
  certificate [L].
- Open: all-test directed covariance or odd/primitive positivity; the signed reflected-prime interaction.
- Killed: `#horizon-charge`, `#variance-dropped-theta-gauge`.
- Class P1 (odd sector). B: B1, B3, B4, B5.

### LA — Laguerre/Jensen and local heat
- Path: theta source → collision-free heat descent / uniform Jensen or heated-coefficient signs → RH.
- Established: every fixed Jensen degree eventually real-rooted; RH ⇔ every positive-time zero simple ⇔
  `Λ_X = 0` at every height; `c·d²/log X ≤ Λ_X ≤ (2/3+ε)/log((X−1)/2π)`; global depth energy antitone;
  polynomial heat preserves the real mesh; reality and purity exit only through collision; heat path real
  for `t ≥ 1/8`; non-real for `t < 0` [L].
- Open: arithmetic exclusion of every positive-time collision, including bounded heights and shallow
  clusters below the heat horizon; or uniform Jensen/heated-coefficient signs.
- Killed: `KR-JPR`, heat/polynomial positivity, `#heat-method-floor`, finite heat support,
  `#counting-local-bound`, `#heat-window-charge`, `#heat-depth-budget`, `KR-CAL`.
- Class P5. A: A18, A26. B: B14.

### TG — topological sub-unit gate
- Path: Euler/Gaussian source → nonnegative residual + integer trace `< 1` → RH.
- Established: winding/index and cubic-transgression identities; central-gap receivers [L].
- Open: a matrix-complete positive residual with sub-unit integer trace on every disc, or a zero-rate
  central-gap bound.
- Killed: `KR-R1`, `KR-DSA`, `KR-TMD`, `#positive-model-homotopy`.
- Class P4 (inner caps). B: B10, B19.

### HF — Hodge / Hecke / complete cells
- Path: complete arithmetic form `≥ 0` → Hodge index → RH.
- Established: S1 in full; window threshold law and RH ⇔ `R₁ ≡ ⊤`; complete terminal source polar with a
  nontrivial kernel; exact low-packet capacity; low correctors cannot improve zero-source windows; growing
  low-block positivity at every `R`; receiving-charge calculus [L].
- Open: `R₁(A) = ⊤` at every aperture; at each ratio beyond the size-only interval, the signed complement
  (source-kernel windows, larger-conductor transport); the far-complement estimate loses `O(c)` against
  `O(log N/c⁷)`.
- Killed: S1 list; `#definite-counts`; dimension-zero domination; the count face (S3).
- Class: sign content P1 on untwisted windows; count face closed; floor layer size-only.
  A: A1–A4, A9, A10, A11, A22, A23. B: B1, B6, B7, B8, B9, B10, B11, B12, B16, B33, B34, B35, B40.

### CHMD — causal hyperbolic–modular duality
- Path: one-sided bounded prime wave or odd Doob half-threshold bound → RH.
- Established: wave/Doob receivers; Haar transport; prime-edge Gamma reserve; all-detail prime–pole
  cancellation `O(exp(−√log Y/92160000))` uniformly over every detail horizon [L].
- Open: upper or lower boundedness of the unnormalized prime wave, or the complete odd sign paying Gamma,
  potential and infinite-orbit terms.
- Killed: `#growing-euler-index`, Gamma boundary reserve, Haar/modal compactness, absolute Euler
  coefficient payment.
- Class P1 (odd sector). A: A20. B: B3, B12.

### TH — theta Hankel ranks
- Path: signed centre-mixed theta jets → all-rank Hankel positivity → RH.
- Established: rank 8 PD for every `0 < a < ½`; seventh native successor integral positive; factorial and
  logarithmic collars for every finite rank; boundary `a = ½` PD at every rank; Hankel PSD reduced to native
  (moment-)tail forms; every theta atom's fifth even matrix PD for `q ≥ 5`; native fifth even source PD on
  the scale-five ray; fixed cross-load PD near both endpoints and for `q ≥ 5000` [L]; at `q = 8` the full
  fixed cross-load has a negative direction, half load PD [W].
- Open: rank 9 integrated sign `I₈(a) > 0` at every `0 < a < ½` (a compatible variable load or another
  repair on the compact gap); all-rank positivity at fixed aperture.
- Killed: `#native-tail-boundaries`, rank-uniform native successor, `KR-HFR`, `#ninth-section-diagonal`,
  `#theta-fixed-cross-load` [W].
- Class P5 (rank limit; a moment problem at one centre). A: A17. B: B14.

### RN — renewal
- Path: theta renewal → divisor-faithful winding/boundary-work sign → RH.
- Established: Green/BV realization; compact cone-positive renewal operator with exact
  determinant/resonances [L].
- Open: directed mixed prime + Gamma `≥` pole including cusp/seam terms.
- Killed: native carrier identification, `KR-R2`, `KR-TRC`.
- Class P3-type (realization). B: B40.

### WD — Ward / collision / window energy
- Path: source current/window energy → collision charge `< 2` or all-resolution sectoriality → RH.
- Established: S6 [L].
- Open: an independent zero-rate right-port bound through the inner caps and finite/shallow exceptions
  with prefix-limit control; density branch: thin nonempty Planck shadows in `≤ η(A)V` windows with a
  vanishing cluster tail.
- Killed: S6 list.
- Class P4 (inner caps); density branch sub-RH. A: A26, A27. B: B19, B20, B21, B22, B23, B47.

### LI — paired Li and prime–Gamma balances
- Path: prime − Gamma history floor / theta-clock first-zero budget → RH.
- Established: guarded history-zero set finite; RH ⇔ it is empty; Cayley–Li primitive-sign receiver
  (unfinished) [L].
- Open: pay the outside budget at every guarded zero, or the primitive sign.
- Killed: eventual guarded-zero budget.
- Class P4. A: A32. B: B15.

### SZ — Suzuki screw
- Path: complete rectangular Ward defect bounded below at one width → RH.
- Established: exact lower-bound receiver; finite light-cone Gram identities; Krein–Schur block
  congruences [L].
- Open: a uniform lower bound after negative-light, Gamma, boundary and mixed costs.
- Killed: sharp Suzuki source in `ℓ²`, uniform causal-to-sharp recovery, positive exact unital finite
  part, `KR-BD`, `KR-NEV`.
- Class P1 (Krein–Schur carrier of the canonical system). A: A32. B: B2, B15.

### PM — Gauss–Mayer physical realization
- Path: faithful scattering source → Krein/Lewis positivity or pole exclusion → RH.
- Established: S9 [L].
- Open: an arithmetic expression of the defect at resonances with manifest sign; source-forced
  extinction or balance of the retained channel; mixed-parameter completion, full Mayer transfer,
  signed-form descent, rational Weyl identification.
- Killed: S9 list.
- Class P3. A: A14, A15. B: B38, B39, B40, B46.

### JAS, CTF, PBM, RB — one-sided counts
- JAS: for every `ε > 0`, `|Riesz(m², k)| ≤ m^{εk}` on `m < k ≤ m + m/log(m+1)` for infinitely many `m` ⇔ RH
  [L]; open: uniform arithmetic control on that window. Class P4. B: B26.
- CTF: RH ⇔ bounded real rows reach every error tolerance [L]; open: construct the rows or signed
  covariance cancellation along compatible cutoffs, retaining the terminal edge. Killed: CTF
  diagonal/centering, dropping the terminal edge. Class P4. B: B26.
- PBM: exact convergence/RH equivalence [L]; open: coefficient cancellation to the critical abscissa.
  Killed: `KR-RAW`. Class P4. B: B26.
- RB: eventual criteria, colossally abundant reduction [L]; open: square-root remainder on
  prime-saturated extremizers. Class P4. B: B26.

### HCF, XN, BAG, EWU, GTA, OWU
- HCF: heat explicit formula, two-grid criterion, arbitrary-zero detector [L]; open: signs at every
  degree/height or a one-sided vertical bound. Killed: one grid aliases, `KR-HFR`. Class P5. A: A18. B: B14.
- XN: coverage/self-map criterion; nonnegative Laplacian of the interior margin [L]; open: an actual
  covering with nonnegative interior margin. Class P5. B: B14.
- BAG: strong/local recurrence receivers; RH ⇔ all high zeros approach the line at each fixed depth and
  arbitrarily high returns on off-line-zero discs [L]; open: arithmetic construction of those returns.
  Killed: `KR-BAG`, `KR-TOR`. B: B36.
- EWU: weight rigidity; attained aperture-antitone blind minima; even positivity ⇔ `−C ≤ Q` ⇔ Hamburger
  moments of `s_k = W(φ^{(k)})`; below `log 4` even sector ⇔ `evenBandWeights` ⇔ retained-variance even
  theta-gauge certificate; cosh/mean-zero ground states singular [L]; open: an all-aperture lower-band
  bound including low/mixed modes and an actual even-sector Lévy margin. Killed: `KR-SRP`, `KR-APW`,
  `#theta-gauge-cosh-defect`. Class P1 (even sector). A: A5, A8, A33. B: B1, B3, B5.
- GTA: exact decay criterion; positive charge and strong finite-prefix convergence [L]; open: rank-uniform
  arithmetic energy decay independent of zero data. Class P5. B: B14.
- OWU: odd RH criterion; odd positivity ⇔ `C ≤ Q` ⇔ shifted Hamburger moments; odd unit window off one
  moment, retained-Gamma identity, higher reserve, one-number reduction; odd moment and sinh capacities
  never attained on smooth tests; below `log 4` odd sector ⇔ `oddBandWeights`; explicit collar payment
  per kick [L]; open: the joint Gamma/prime/pole sign at every aperture. Killed: `#first-fold-linear-chord`,
  `#retained-gamma-lower-form`, `#frozen-gamma-cubic`, `#collar-local-payment`,
  `#variance-dropped-theta-gauge`, `#prime-three-sliver-potential`. Class P1 (odd sector). A: A5, A33.
  B: B1, B3, B4, B5.

### SRT, ACT, AIP — complete atomic matrix
- SRT: full-family receivers/index exhaustion; controlled-aperture negative tests for depth `≥ δ`; growing
  low-block positivity; complete compact-terminal source polar across conductors `≤ ⌊(log N)^{13/32}⌋`;
  finite complex column unions of depth `≤ ½` certified by positivity at aperture `a > πD`; isolated tilts
  give negative images; prime pinning and depth-uniform identification [L]. Open: complementary-window
  sign at every critical ratio; high-zero tail; source-kernel windows; larger-conductor transport.
  Killed: tempered fixed-ratio models, `KR-CRT`, `#finite-readings`, `#uniform-margin`. A: A1, A3, A10,
  A27, A34. B: B6, B7, B12, B47.
- ACT: single-shift receiver; collar thresholds pay fixed finite families; `Ẑ(m_au) = 2S_a − D_a + 8V_c +
  8τ_cA₂`; below `log 4` the retained-variance shifted-ground-state certificate ⇔ odd positivity and the
  admissible set requires `w₂ > 0` for `c ≥ 21/40`; variance-dropping fails for `c > 273/400` [L]. Open: one
  shift, uniform in profile/support, paying `D_a` with same-side energy and retained variance; actual-weight
  band membership. Killed: `KR-PAF`, `#folded-markov`, `#folded-origin-charge`,
  `#variance-dropped-theta-gauge`. Class P1. A: A19. B: B1, B3, B5.
- AIP: allocation receiver; small-`K` full-space floor; all-`R` growing low-block positivity; capacity
  `log log N + O(1)`; harmonic-charge complete energy `→ 0` for independent scales; exact neutral
  mixed-channel decomposition with bounded Mertens correction; V-sieve progression, collision and tail
  bounds [L]. Open: full-space allocation at every `K`: jointly bound centre, separated-cross,
  overlap−downward and upward channels as fibres grow. Killed: `KR-LGP`, `KR-ADJ`,
  `#separate-shell-payment`, `#absolute-prime-correction`, `#prime-pole-cost`. A: A1, A4, A9, A20. B: B6,
  B7, B8.

### SC — Stokes/Witt–Krein
- Path: glued affine index `≤ 1` / bounded Gaussian-damped two-prime coupling → RH.
- Established: glued index `κ_ζ + 1`; damped cone ⇔ RH; undamped ⇒ RH or unattained width; tensor bounds
  `|c(t)|^k ≤ C_ke^{L_kt}`, `L_k/k → 0`, imply RH [L].
- Open: an arithmetic bound for the damped coupling, sublinear tensor loss, or glued index `≤ 1`.
- Killed: `#coupling-growth`, `#pole-pair-retuning`, `#additive-reading-index`, `#haar-continuous-dilation`,
  `#separated-place-poles`, `#tensor-square-inertia`, `#fixed-prime-counterterm`, `#local-polar-trichotomy`,
  separable towers, `#padic-localization`, `#fixed-prime-global-index`.
- Class P4 (coupling = window error). A: A11, A12. B: B1, B9, B10, B12, B30, B31.

## 4. Candidates

| Candidate | Established | Promotion gap | Strength |
|---|---|---|---|
| ACS | RH ⇔ effectivity ⇔ Hodge index ⇔ section count; primitive `h¹ = Q/2`; below `log 4` Künneth effectivity ⇔ two-weight band; degree-zero Rosati principles; Legendre `J(ρ)` reality ⇔ RH; cusp growth of `J∘λ`; Selberg degree gap and degree-one conductor or pole [L] | a non-count source of all-aperture primitive effectivity; Rosati heights, `j`-reality and degree-zero principles are receivers or exactness tools, not producers | B34; count face closed |
| APF | Fredholm index; cycle-trace reconstruction | zero-independent divisor exhaustion | B41 |
| BSH | framed curvature | pre-divisor section and mate identity coupled to `Ξ` zeros | B41 |
| CDC | calibrated confluence iff `Re s = ½` | source-defined potential forcing confluence | B41 |
| EGC | pole-safe contour; copy correction | outer expanding-contour sign | B15 |
| EWJ | Euler/Wold jets | zero-independent source admission | B41 |
| FEL | theta likelihood; BSY = off-line zero sum | predeclared source balance | B15 |
| HJ | Hurwitz residual = SEC charge | pre-divisor forcing | B41 |
| IRK | rotation-algebra trace / winding | arithmetic projective lift with integral count (count face closed) | closed |
| MSC | Möbius–Sonin; divisor preservation | bridge to nonnegative Sonin energy | B1 |
| PCS | singular co-shift | source-natural wall annihilation | B41 |
| PTR | lossless stacks, unit port gap | prime-faithful port (killed: `KR-PTR`, `KR-GAP`, `KR-COS`, `KR-POI`) | B40 |
| RFHM | support grade | symmetry-breaking law | B41 |
| SEC | essential norm = seam jump | pre-divisor compactness at zeros | B41 |
| W1C | Lee–Yang receiver; PM's exact zero-coordinate Krein space; retained-channel side law | positive arithmetic Hilbert realization (killed: `KR-ISG`) | B38, B40 |
| WBF | genealogy Gram | any arithmetic coupling | B41 |
| ZCG | see below | local inversion at `ζ`'s density, then a source-side reality mechanism at near-collisions with a proved global RH implication | B14, B43, B44 |

### ZCG — zero-configuration geometry (candidate)
- Path: prime explicit-formula image → configuration identification → reality at near-collisions or
  collision-free deformation → RH.
- Established: S10 in full [L]; local camera and strip products [W].
- Why a candidate: identification needs a competing configuration with the same image, and an on-line
  competitor is already Weil positivity; no source-side condition with a proved RH implication covers
  infinite, arbitrarily close clusters. The density criterion is global (uniform count bound); `ζ` has
  growing density and local count excess `≍ log T`, so the local version is a quantitative race (A16, B43).
  The repulsion mechanisms proved — integrality over `𝔽_q`, archimedean phase speed above the Euler-stage
  horizon — do not reach `ζ` at its own scale.
- Obstacles. A: A16. B: B14, B43, B44.
- Walls: Γ (identification is selection without sign) and P5 (Laguerre–Pólya at all orders); at the density
  scale the square-root threshold `λ = ½`, which is the pair-isolation aperture and the Riemann–Siegel length.

## 5. Decisive wall per route

| Wall | Routes |
|---|---|
| P1 — signed criticality / stage step / frustration domination; first instances below `log 4` | RW, EWU, OWU, ACT, CHMD, TT, SZ, HF (sign content), ACS (sign content), MSC; CWS, WTZ, DZG, GWZ, CSTW, SWC |
| P1 at large ratios — untwisted windows / threshold `R₁ ≡ ⊤` | HF, SRT, AIP, SC; CACT, AHD, CSAR, ACPL |
| P4 — one-point square-root precision (the band in prime form) | WL, MC, PBM, RB, JAS, CTF, SC (coupling), FU, CFC, RP, LI, EGC, FEL |
| P4 — inner caps (zero-free region to the line) | WD, TG |
| P5 — rank / degree / collision limits (Laguerre–Pólya) | TH, HCF, PA, GTA, LA, XN; ZCG (candidate) |
| P2 — prime-blind positivity | PBAP |
| P3 — reflection positivity (zero side) | PM, W1C, RN, PTR |
| Γ — trivial gauge point / pre-divisor forcing | BAG, MC; APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF |
| closed — counts / Hodge index | ACS (count face), HF-RR, IRK |
