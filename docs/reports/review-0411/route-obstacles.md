# Route obstacles — status quo

Scope: the 32 live routes and 17 candidates of the frontier map, and the programmes that feed them,
read against the Lean corpus. For every route: path, what is established, the open estimate, the
shortcuts that are killed, the mechanism class, the obstacles that are **(A) just work** and the
obstacles that are **(B) open mathematics** (nobody has a solution).

Evidence: `[L]` Lean declaration in the corpus; `[W]` working-tree or draft module; `[D]` derived here
from Lean statements; `[M]` exact model statement; `[N]` numerical; `[P]` paper only. Killed shortcuts
are cited by their anchor in `rh-killed-routes.md` (`#anchor`) or by row title.
Strength: **RH**; **≥qRH** (zero-free half-plane or Lindelöf); **sub** (strictly below quasi-RH);
**indep.**; **identity**; **method**. A means known mathematics, finite computation, effectivization or
assembly of proved pieces; items whose difficulty is not established carry `(difficulty unverified)`.

Notation. Window tests of length `A` live on `[−A, 0]`, or on `[−a, a]` with `a = A/2`; `Q` is Weil's
form (`W(f)` on half-window tests); `w_n = Λ(n)n^{−1/2}`; `c_φ(t) = W(φ(· − t), φ)`. For a test `f`
supported left of `m` and its mirror `f∘R`, `R(v) = 2m − v`, the **coupling** is
`𝒞_m(f) = 𝓗_m(f) − Σ_n w_n (f⋆f)(2m − log n)` with the **collar Hankel form**
`𝓗_m(f) = e^m μ_{1/2}(f)² − Σ_k e^{2mσ_k}μ_{σ_k}(f)²`, `μ_σ(f) = ∫f e^{−σu}`, `σ_k = −(2k + 5/2)`.
The **band** is `|𝒞_m(f)| ≤ W(f)`. A prime power `n` acting on `[−a, a]` with lag `ℓ = log n` has the
**collar** `[ℓ − a, a]` of half-width `h = a − ℓ/2`.

## 0. Mechanism classes

Every route is a face of one statement (`route-unification-ledger.md`). Routes differ by the mechanism
they can offer. Five classes are live; the rest are closed or blind.

| Class | Mechanism | Status | Anchor |
|---|---|---|---|
| P1 | **Signed criticality.** In a gauge `F = Φωu` the window form is a signed Dirichlet form plus pole charges; each fold is kept with its sign; the collar light cone pays a prime kick locally, the pole and the trivial-zero Hankel squares pay collectively | live; first open instances: the odd unit window (one prime-two weight in a convex interval) and the prime `3` (the first prime its own collar cannot pay) | SWC, ACT, WTZ, GWZ, CSTW [L] |
| P2 | **Prime-blind positivity.** Archimedean + pole part `≥ 0` on signed combinations of autocorrelations vanishing on `±log ℕ_{≥2}` | live; solved on nonnegative and separated-bump cones; open on signed blind combinations | RHTower PBAP modules [L] |
| P3 | **Reflection positivity of PM.** Krein positivity of the completed resonant space | reduced: the completed space is `ℓ²(zeros)`, `Q = 2Re[𝓦H, 𝓦H]`; the resonant co-isometry defect is `≤ 0` with equality exactly on the quarter line; the arithmetic reverse inequality is missing | RIT [L] |
| P4 | **Square-root cancellation** of one smoothed short-window prime count: the band in prime form | live; classical; parity barrier for sieve-type producers | GWZ, SWC, CSTW, AOG [L] |
| P5 | **Reality by continuation.** Real-rootedness is closed and is lost only through a collision; RH follows from a source-faithful path from a real configuration to `Ξ` with no collision | live as a receiver: the heat path is real for `t ≥ 1/8` (corpus normalization), RH ⇔ real at `t = 0`, and `H_t` is not real for `t < 0` (Newman); no collision-exclusion mechanism | ZCG, RHTower `DeBruijn`, LA, TH, HCF [L] |
| — | Counts / Hodge index / degeneration | closed as an RH mechanism [D] | S3 |
| — | Size-only layers: subcritical regime, one small critical multiple, twisted sectors, bulk, aperture-independent floor | true and blind; the aperture-independent floor carries no zero information [D] | S1 |
| — | Identification without sign (camera of the explicit formula) | sign-free; an on-line competitor with the image of `ζ` would already be Weil positivity, so identification decides nothing alone [D] | S10 |

Closed mechanism families (anchors in `rh-killed-routes.md`):
- **Cost-only and sign-blind payment of a fold:** nonnegative exit-charge loan (`#frozen-gamma-cubic`),
  Barta/Picone weights on `|c_n|`, weighted transfer `wE_φ ≤ Q_N`, retained Gamma `+ E/64` and the
  two-moment form (`#retained-gamma-lower-form`), fixed polynomial inverse chord
  (`#first-fold-linear-chord`).
- **Markov ground states:** cofinal Markov passage (`KR-BD`); bare and compact folded supersolutions
  (`#prime-free-markov`: the Markov part has a negative test of support `e^{−3/4}`, no Markov
  supersolution on a longer interval, the folded criterion is void on the unit odd window); fully
  calibrated folded-Markov conductance (`#folded-markov`); compact folded supersolution with zero origin
  correction (`#folded-origin-charge`); lossless local allocation (`KR-LGP`).
- **Collar locality:** collar parity / automatic positive reflected coupling
  (`#collar-positivity-induction`); unit collar energy paying every prime kick
  (`#collar-local-payment`: fails at the prime `3`).
- **Finite structures:** finite-square count identities at the first prime (`#fold-count-identity`),
  finite-dimensional window realizations (`#finite-window-realization`), finite passive realizations
  (`KR-FPR`), finite virtual graph realizations (`#finite-virtual-realizations`).
- **Slack:** uniform positive aperture floors (`KR-PAF`), positive asymptotic lattice slack
  (`#lattice-positive-slack`), uniform growing-overlap Gram floor (`#growing-overlap-floor`).
- **Dimension zero:** Tate coefficients as a selector (`#tate-count-selector`), uniform Tate positivity
  (`#uniform-tate-positivity`), Gamma/pole domination of Tate counts (`#tate-domination`).
- **Counts:** bidegree/theta counts (`#bidegree-counts`), definite counts (`#definite-counts`), Siegel
  majorant (`#siegel-majorant`), isotropic Poisson pair (`#isotropic-poisson`), automatic arithmetic RR,
  Witt integrality (`KR-WIP`).
- **Critical-family shortcuts:** bare counts through all conductors (`#conductor-count-resolution`),
  critical-pencil equality (`#critical-pencil-nullspace`), low-conductor deletion
  (`#low-conductor-deletion`), raw-cost charge control (`#prime-pole-cost`), small charge energy forcing
  vanishing complement coupling (`#charge-complement-vanishing`), fixed packets as line selectors
  (`#fixed-packet-bulk`), twisted horizons (`#twisted-horizon-blindness`).
- **Producers:** integrality alone, fixed factorial ratios, univariate sup-norm, fixed-prime stencils,
  Adams multiplicity, base-change twists; pole matching as half-power input (`#pole-matching-half-power`).
- **Reflection:** bounded Cauchy reflection off `Re s ≥ ¼` (`#cauchy-reflection-order`), literal
  Serre–Krein isometry (`#window-krein-reflection`), Krein self-adjointness ⇒ positive projections
  (`#mayer-krein-sign`), Lewis inversion (`#lewis-inversion`), three-term + inversion
  (`#farey-three-term`), resonant-state selectors (`#resonant-cutoff-gram`), contractive scattering
  (`#scattering-schur`), rational/algebraic recentering (`#scattering-recentering`).
- **Continuation:** interior-gap continuation (`#lattice-interior-gap`); crossing-free deformation as a
  free input (`#positive-model-homotopy`); first Laguerre inequality as a reality certificate
  (HTGeometry `exists_laguerre_pos_with_nonreal_zero` [L]).
- **Selection without sign:** every selector (Γ16 of `walls-ledger.md`); regular integers (Beurling)
  do not constrain zeros; no bounded aperture excludes Euler columns.

## 1. The picture

| Fact | Anchor | Consequence |
|---|---|---|
| RH ⇔ `|c_φ(t)| < Q(φ)` for every bump and `t ≠ 0` ⇔ every two-site lattice window is positive definite; off RH a short generic bump has `|c_ψ(s)| = Q(ψ)` at some step | GWZ `riemannHypothesis_iff_two_site_posDef`, `riemannHypothesis_iff_abs_weilOrbitCorr_lt` [L]; AOG [L] | the lattice form of the Hasse–Weil criterion for one orbit |
| `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; band ⇔ positivity on the pair; on a nonnegative window a tight band produces a reflection-pair zero mode with pole-charged harmonic gauge | SWC `weilQuad_add_collarReflect`, `abs_coupling_le_weilQuad_iff`, `zeroMode_of_tight_band` [L] | the two-site band is the smoothed prime count of `f⋆f` matching the pole square within `W(f)` |
| The odd and even sectors of `[−a, a]` are the band at the centre; the odd unit window reads one number: `w₂ = log 2/√2` must lie in a convex set of admissible weights | SWC `odd_nonneg_iff_centreCoupling_le`, `odd_unit_nonneg_iff_mem_unitBandWeights`, `convex_unitBandWeights` [L] | the base case of P1 is one scalar membership |
| Collar Hankel form: inertia `(1, ∞)`, negative definite on the pole hyperplane, trivial squares decay at ratio `e^{−4d}` | SWC `TheCollarHankelForm`, `exists_collarHankel_negDefinite` [L] | the archimedean place transmits one positive square across a cut |
| Markov part dies at length `e^{−3/4}`; no Markov supersolution on longer windows; folded criterion void on the unit odd window | SWC `exists_markovEnergy_neg_of_support_le`, `not_exists_markovWindowSupersolution`, `not_exists_foldedWindowSupersolution_half` [L] | the pole must be kept in every certificate |
| Pole-charged representation `Ẑ(Φωu) = J_{Φω}(u) + ∫u²ω𝒢_S(ω) + 2V_s − 2V_c`; theta gauges are critical on the line; a window reads their outside charges, slack in the odd sector, deficit in the even sector | SWC `fullZeroForm_phiDoob_mul_eq`, `fullZeroForm_thetaGauge_eq_univ`, `fullZeroForm_evenThetaGauge_le` [L] | P1 has an exact ground-state calculus |
| Collar light cone pays the kick of `n` at ratio `2w_ne^{h}`; the ratio is sharp; the prime `3` cannot be paid by its own collar | SWC `kick_add_collarLevyEnergy_nonneg`, `exists_kick_add_collarLevyEnergy_neg`, `exists_prime_three_collar_unpaid` [L] | `2w_n < 1` for `n = 2`, every proper prime power and every prime `≥ 79`; `> 1` for the primes `3 ≤ p ≤ 73` [D]: these primes are never collar-certified |
| Continuum canonical system of a bump = its jet Hankel system: `h^{−n(n−1)}det T_n → det J_n`, `h^{−2n}E_n → det J_{n+1}/det J_n` | SWC `theContinuumCanonicalSystemIsTheJetHankelSystem` [L] | the local continuum limit is solved; the global Hamiltonian is not constructed |
| Complete Weil matrix PD on the whole prime-horizon space at one critical multiple `2K₀(log N)^{1/8}`; RH ⇔ the window threshold `R₁(A) = ⊤` for every `A`; `R₁(A) ≥ R₀ > 0` for every `A` | AHD `exists_joint_critical_multiple_completeWeil_and_all_window_corollaries`, `riemannHypothesis_iff_windowThreshold_eq_top`, `apertureIndependentThreshold_le_windowThreshold` [L] | HF's size-only layer is complete; the sign is the threshold |
| Floor `Q ≥ −C(p)∫e^{p|u|}H²` for every `p > 1`; ground-energy floor `μ(A) ≥ −Ce^{2σA}` ⇔ zero width `≤ σ` | WTZ `weilQuad_ge_neg_exponentialMass`; SquareRootThreshold contact module [L] | a floor with exponent `p` gives `μ(a) ≥ −Ce^{2pa}` at half-width `a`, hence zero width `≤ p`: the proved range `p > 1` carries no zero information; `p < ½` would be quasi-RH [D] |
| PM: `Q(H) = 2Re[𝓦_AH, 𝓦_AH]` on `ℓ²(upper Mayer resonances)`; resonant co-isometry defect `< 0` iff `Re s ≠ ¼`; the retained `T₂` channel has defect of the sign of `¼ − Re s` | RIT `weilQuad_eq_completedKreinForm`, `resonantLewisPeriod_coIsometryDefect_lt_zero_iff`, `retainedHeckeChannel_defect_sign` [L] | PM is the zero side; its channel detects the side of a resonance, not the line |
| Camera of the explicit formula: finite modifications identified at every aperture; primes below `e^{2r}` pin every finite piece of the zeros of `ζ`; mimics need near-collisions or deep points; column threshold `λ = ½` | ZCG `eq_of_weil_eq_on_aperture_of_finite`, `eq_zeta_of_arithmeticImage_of_finite`, `exists_near_pair_of_mimic_of_le`, `rvmLattice_mimic_iff` [L] | identification is sign-free; reality at near-collisions is a second-order sign |
| Heat path: `H_t` real for `t ≥ 1/8`; RH ⇔ `H_0` real; `H_t` has infinitely many non-real zeros for every `t < 0` | RHTower `riemannHeat_zeros_real`, `riemannHypothesis_iff_riemannHeat_zero_real`, `riemannHeat_neg_nonreal_zeros_infinite` [L] | the heat path is exactly critical at `t = 0` |
| Dimension zero: bare domination ⇔ `Q ≥ 0`; no archimedean family dominates the Tate counts | ATD, DZG [L] | count/Hodge/degeneration closed as an RH mechanism [D] |
| FE + positivity determine `ζ`; positive primes with regular integers allow off-line zeros | APD, RHTower Beurling [L] | a proof uses the functional equation and the Euler product together |

## 2. Shared obstacle blocks

### S0. The two-site band and reflection pairs
Routes: every route of C1, C7, C14, C15, C19.

Established [L]: RH ⇔ two-site PD ⇔ strict orbit Cauchy–Schwarz; one generic bump decides; eventual
boundedness of its orbit correlation decides, rate = zero width; reflection-pair identity
`W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)` with `𝒞_m` = collar Hankel form − smoothed prime count; band
unconditional when `2(m − p) ≤ 181/250` (`abs_coupling_le_weilQuad_of_short`); parity sectors are the
band at the centre; a tight band on a nonnegative window gives a reflection-pair zero mode solving the
pole-charged source equation. [W] On a nonnegative window the band is strict on smooth tests and no
smooth test is a zero mode (`abs_centreCoupling_lt_of_window_nonneg`, `weilQuad_pos_of_window_nonneg`).

Status: a reformulation of the classical criterion (smoothed `ψ(x) = x + O(√x)` in a fixed
multiplicative window, constant `W(f)`). It fixes what every mechanism must deliver at each scale.

| | Obstacle | Strength |
|---|---|---|
| A29 | Bridge: reflection-pair coupling = smoothed prime count [L] → WL/JAS/CTF/PBM/RB receivers | — |
| A30 | Two-site band on a bounded step range from numerical zero data and explicit tails (decides nothing) | — |
| B1 | The band at every step and every test (Weil's sign on every window) | RH |
| B10 | No zero mode at any length (≡ no degenerate two-site lattice) | RH |

### S1. Complete Weil family at the critical curve
Routes: HF, SRT, AIP, ACT (index), ACS-atomic, RW-atomic, SC, CHMD (index), FEL, MSC. Programmes:
CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF.

Established [L]:
- Subcritical regime: `completeWeilMatrix tiltedUnitSpline c N ≻ 0` for `α < 1/8`, `1 ≤ c ≤ (log N)^α`,
  floor `κ/(2c⁷)`.
- **Whole-space PD at one critical multiple**: some `K₀ > 0` (`2K₀ ≤ 1`) gives, eventually in `N` and
  uniformly in `1 ≤ c ≤ 2K₀(log N)^{1/8}`, PD of the complete matrix, floor `(log N)^{−7/8}` on
  `(conductorSubspace 1 N)ᗮ`, horizon Gram `≥ 0` with index `0` for every finite family, weighted window
  sign and pencil index `0` on windows of every length for `0 < M ≤ (2K₀)^8`, and mixed
  untwisted/Ramanujan families PD (AHD/CACT). The proof splits the upper band along
  `V_{Q₁} ⊂ V_{R₀} ⊂ V_{R₁}`, `Q₁ = ⌊(log N)^{13/32}⌋`, `R₀ = ⌊exp√log N⌋`.
- **Window threshold**: for `Q(H) < 0`, `R*(H) = 7J(1)M₈(H)/(a_φ|Q(H)|)`, `M₈ = ∫e^{−8y}H²`;
  `R₁(A) = inf R*`; below `R₁(A)` the pencil `a_φQ + (7J(1)/R)M₈` is PD and horizon blocks are eventually
  positive, above it some test is eventually negative; `R₁` antitone; `R₁(A) ≥ R₀` (aperture-independent)
  and `≥ 7J(1)/(a_φS(A))` (sharp window floor); `R₁(A) = ⊤` for `A ≤ 2·enlargedWeilFloorAperture`;
  RH ⇔ `R₁ ≡ ⊤`.
- Joint pole payment strictly enlarges the certified ratio interval
  (`separatePoleCriticalRatio_lt_joint`); joint pole floor in the aliasing norm (WTZ).
- Critical-curve second order `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²`; twisted sectors are positive Hurwitz
  counts; frequency counts have a pole of order `β+1` at `u = 0` with finite part the untwisted count.
- Growing overlap (`c²log²N/N → 0`): every bulk entry is `E_e(c)⟨R_e, R_{e'}⟩ + [e = e' = 1]κc(2 + γ − log 4π) + o(c)`;
  near block, shell mass and far cross error exact; complete critical residue, upward-prime residue
  (`−(γ+1)`) and growing Gamma mean are supported at the pole.
- Terminal windows (support strictly inside `(½, 1)` of the horizon): no upward and no exterior primes;
  polar mixed limit `α[∫polarCenterProfile(F) − log(2π)∫F]`; nonpolar centre and divisor jet cancel;
  a nonzero terminal polar source exists.
- Low block: conductors `≤ ⌊(log N)^{13/32}⌋` keep `≥ ½` of their diagonal energy plus the polar part at
  every `R`; removing the block preserves the compensated window limit; the critical pole has an
  intrinsic collar cost `≥ κR²`; [W] terminal conductor sources are summable below overlap.
- Receiving charges: a coherent prime charge survives vanishing raw, physical and absolute complete
  energy; capacity `log log N + O(1)`; complementary terminal receiver pairs to `t/80`, receiver
  energy `/log N → 1/20`, source–receiver determinant `→ 6239t²/6400 > 0`; fixed packets have vanishing
  complete critical output and positive Jordan limits; the complement ramp is logarithmic.

Killed: `#conductor-count-resolution`, `#growing-overlap-floor`, `#fixed-packet-bulk`,
`#critical-pencil-nullspace`, `#twisted-horizon-blindness`, `#defect-capture`, `#overlap-gram-smoothing`,
`#separate-shell-payment`, `#absolute-prime-correction`, `#prime-pole-cost`, `#prime-residual-scale`,
`#logarithmic-floor-budget`, `#low-conductor-deletion`, `#charge-complement-vanishing`.

Status: every layer below the sign is size-only and is closed at small ratios. The aperture-independent
floor that pays the small multiple carries no zero information: its exponent `p > 1` is forced by the
Cauchy–Schwarz bound on the pole moment `∫He^{−y/2}` [L/D]. HF's sign content is `R₁ ≡ ⊤`, i.e. Weil's
form on untwisted windows of radius `½log K` at every `K`.

| | Obstacle | Strength |
|---|---|---|
| A1 | Explicit constants and horizons: `K₀`, eighth-root theorem, `1/9`, logarithmic profile, Beurling schedule, horizon criterion, quantitative conductor range `M(N) = o(c_N)` | — |
| A2 | General profiles past `θ = 1/1080` | — |
| A3 | Joint twist families; equal-parity characters through `L(s, ψ̄₁ψ₂)`; different moduli | — |
| A4 | The certified ratio interval at its size-only optimum (joint pole, higher Gamma reserves) and the assembly of the receiving-charge complement inside it (difficulty unverified) | — |
| A10 | Window index as a counting function of the length | — |
| B6 | Twisted-sector positivity through all conductors and frequencies at every multiple | sub |
| B7 | Full-space sign at critical ratios beyond the size-only threshold (each fixed ratio sub; every ratio RH) | sub / RH |
| B8 | General profiles past `log log N` on the full space | sub |
| B9 | Exact SOS on one two-prime lattice | RH |
| B16 | Window negativity exponent `< ½` in the window length (≡ zero width `< ½`); implied by an aperture-independent floor with exponent `p < ½` | ≥qRH |
| B33 | HF-native arithmetic sign: the pencil positive at one ratio beyond the size-only interval, or the floor at exponent `p = 1`, proved with prime input | sub |

### S2. The window tower, its canonical system and signed criticality
Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT, HF, ACS, SRT, SZ. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC.

Established [L]:
- Window datum, truncated Dirichlet λ-ring, stage transfer, exit charge, composite stages free, sharp
  floor, Hecke-graph reading, exact Tate horizons at stages 1–2.
- Stage criterion `2wc_H(ℓ) ≤ S^N_A(H)`; kick = collar Rosati pairing; frozen form in closed form
  (trivial-divisor moments + earlier-fold transports); translation contraction; Carathéodory disk.
- Lattice canonical system (Levinson, Schur parameters, outer predictors, causality, single-kick law,
  admission interval); window ⇔ its lattices; refinement lowers margins; lattices Szegő singular under
  RH; zero modes: radical, reflection parity, gap law, end-collar injectivity.
- Continuum limit at a bump = jet Hankel system (`W(φ^{(i)}, φ^{(j)}) = (−1)^iW(φ, φ^{(i+j)})`, odd pairings
  zero, first margin `h^{−2}E_1 → Q(φ')`).
- Base: all real `C²` tests positive through length `181/250·(1 + 6·10⁻⁷)`; first prime stage opens
  positive.
- First stage (length `21/20`): admissible prime-two weights form an interval that excludes `0` (frozen)
  and `−w₂` (flip); the sign of `Λ(2)` is forced.
- Odd unit window `[−½, ½]`: `‖F‖²/1000 ≤ Q(F) + (5123/320)(∫xF)²`, reduced to `(3203/320)`;
  `Q ≥ ‖F‖²/100` when `∫xF = ∫x³F = 0`; exact retained-Gamma identity; higher reserve
  `r(t) ≥ t³/960 + t⁴/192`; logarithmic principal energy pays the first fold on the prime-two strip;
  the odd unit window ⇔ `w₂ ∈ unitBandWeights` (convex) ⇔ the Markov–Hankel inequality
  `4S(f)² ≤ M(f) + Σ_j m_j(f)² + w₂(f⋆f)(−log 2)` on `[−½, 0]`.
- Signed criticality calculus (SWC): Markov death at `e^{−3/4}`; window Allegretto–Piepenbrink for the
  Markov part; pole-charged representation, sinh charge and cosh credit; shifted ground states strict
  pole-charged supersolutions on every window with slack `τ_c(a) = ∫_{x≥c}m_a sinh > 0`; theta gauges
  critical on the line; outside-charge identity; Rayleigh-critical gauges solve `𝒮(a) = μΦ²a`; the
  frozen odd form is Markov under `F ↦ sign(x)|F|` and the kick of `2` is anti-Markov; the kick is a
  positive source `2w∫hh∘τu²` minus the collar conductance `w∫hh∘τ(u − u∘τ)²`; odd light cone
  nonnegative for every odd gauge; collar light cone ratio `2we^h`, sharp; prime `3` unpaid by its collar.
- [W] Window eigenfunctions are not smooth; the infimum of a window is not attained on a nonzero smooth
  test; a nonnegative window is PD on smooth tests.

Killed: `#frozen-gamma-cubic`, `#retained-gamma-lower-form`, `#first-fold-linear-chord`,
`#fold-count-identity`, `#folded-markov`, `#prime-free-markov`, `#folded-origin-charge`,
`#collar-positivity-induction`, `#collar-local-payment`, `KR-BD`, `KR-LGP`, `KR-PAF`, `KR-CCP`,
`#lattice-positive-slack`, `#lattice-interior-gap`, semilocal positive factors, fixed finite-prime
positivity at every aperture.

Status: the stage step and its ground-state calculus are exact. The collar light cone certifies the
kicks with `2w_ne^h ≤ 1`; the primes `3 ≤ p ≤ 73` are outside this range from their entry (sharp failure at
thin collars), and every other prime power leaves it once `h > log(1/(2w_n))`, i.e. once
`a > log n − log(2 log n)`. Kicks outside the range need resources beyond their own collar, and summed over
a reflection pair the anti-diagonals are the smoothed prime count in `𝒞_m` [L/D]: beyond the first stages
P1 meets P4.

| | Obstacle | Strength |
|---|---|---|
| A5 | Numerical certificates: first prime stage `[0.7240, log 3)`, second stage, `w₂ ∈ unitBandWeights` (margins `1.5×10⁻⁵` odd, `5.6×10⁻⁸` even at half-width `½log 3` [N]) | — |
| A6 | Rational Hecke graphs and Tate horizons of stages 3, 4, 5, 7, … | — |
| A7 | Closed form of the first-stage complement `Φ_ε` of the trivial-divisor moments | — |
| A8 | Even-sector counterparts of the odd identities (even theta-gauge deficit, cosh-credit supersolutions) (difficulty unverified) | — |
| A9 | Edge-singularity theorems of window eigenfunctions [W] (difficulty unverified) | — |
| A28 | Atomic-lattice bound `λ_max ≤ ½log N` | — |
| B2 | Kick admission at every stage | RH as induction; each stage sub |
| B3 | Frustration domination at every length: a gauge in which the crossing prime conductances are dominated by the archimedean fold surplus plus pole slack (odd), with the cosh deficit paid (even) | RH; fixed length sub |
| B4 | Structural certificate of the odd unit window (`w₂ ∈ unitBandWeights`) | sub |
| B5 | Non-local payment of the first non-local prime: windows of length `< log 4` with the kick of `3` paid by resources outside its collar | sub |
| B17 | Global continuum canonical system of the tower (Hamiltonian with the prime kicks); local limit solved | identity |
| B18 | Contact law beyond the model boundary: RH to height `T` ⇒ windows of length `c log T` positive with `c` above the density-matched value | sub |

### S3. Dimension zero, counts and the Hodge index
Routes: ACS, HF; programmes WTZ, DZG, ATD, AHD, LST.

Established [L]: Tate jet and signed-count forms; jets generated by `M` and `ρ_A(Λ)`; bare domination ⇔
`Q ≥ 0`; no uniform Gamma–pole domination; horizon `≤ C exp(−exp(A − 2))`; Euler-product pole weight
forced (`1/ζ(1 + k)`) and refuted; Tate positivity not uniform and does not descend; Künneth `h¹ = ½Q`;
bidegree, fixed-rank, definite and Siegel counts excluded; finite-square count identity refuted at the
first prime; Künneth effectivity of a curve window ⇔ unitarity.

Status: closed as an RH mechanism [D]. The Taylor coefficients of `J_k` at `k = 0` are Bombieri's `Λ_j`,
so any count-based positivity must beat parity at first order.

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

Established [L]: finite index = PD minus finitely many squares; finite index ⇒ Lindelöf; RH ⇔ index
zero; window index finite, monotone, exhausting, `sup = κ`; `{0, ∞}` laws for escaping, mixing and
height-decaying carriers; index `≤ R + A` on `R` coarse cells; growing Euler heads unbounded.

Killed: `#growing-euler-index`, fixed-complexity index as a global ceiling, positive group-kernel
repair, local tower ceilings, pointwise index conservation, `#tensor-square-inertia`.

| | Obstacle | Strength |
|---|---|---|
| B12 | Index ceiling uniform in resolution | ≥qRH; RH (tensor) |
| B13 | Zero–one law `κ ∈ {0, ∞}` | sub |

### S6. Window energy, near-line density and the Hecke defect
Routes: WD, LA, TG, HCF, SC-heat, TH-heat; census; HEF.

Established [L]: window integer = Wiener–Hopf index; pair resolvent = Laplace transform of `|𝒵|²`;
Cauchy cap cancellation; unconditional cap at `σ_m = 1 − 1/(116 log(m + 5))` (the classical zero-free
region) with right half-port `O(e^{(σ_m−½)t}/(t+1))`; exponent `3loglogV/logV` outside
`O(V/loglogV)` windows; exact critical-line flux on `(1 − O(B))V` micro-Planck windows; zero-free window
⇔ unweighted `L²` port ⇔ `𝒵_N ≡ 0`; bounded port ⇔ critical-line purity; RH ⇔ the polynomial-stage
6-way TFAE; fixed degree `k` ⇔ corridor `|Re ρ − ½| ≤ C/|Im ρ|^k`; 8-way equivalence of the log-mean,
mollified log-means, horizontal moment `o(T)`, `100%` critical-scale clustering and dyadic Hecke
readings; `D_zero` ⇔ `D_win` + vanishing giant-cluster tails; `D_win` ⇔ thin Planck shadows; per-window
deep-order second moment `≤ C(e^{−rA}/A)V(log V)²`, the `(log V)²` sharp [M]; uniform Planck volume ⇏
occupancy [M].

Killed: `#theta-prefix-sectoriality`, `#theta-seam-smoothing`, `#fixed-log-defect`, `#counts-only-defect`,
`#antinodal-prime`, `#unfolded-euler-mollifier`, `#theta-uniform-prefix`, `#window-port-reflection`,
`#window-port-l2`, `#holomorphic-carriers`, `#window-density-separation`, `#holomorphic-jensen`, `KR-R3`,
`KR-HUS`, `KR-LLM`.

Status: the RH content of WD is right-port cancellation through `[½, σ_m]`, i.e. the zero-free region
pushed to the line; `σ_m` is the de la Vallée Poussin region [D]. Density statements are sub-RH and
cannot exclude density-zero exceptional sets.

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
positive cyclotomic band has abscissa `2Θ`; pole-subtracted prime exponents over the gauge torus range
exactly over `[Θ, 1]`, minimized at the trivial point, RH ⇔ range `[½, 1]`; flip points share the pole
of `0` to precision `N^b` and have Möbius exponent `max(θ, Θ)`; exponent invariant on sparse prime sets;
an explicit gauge point outside every finitely modified Dirichlet/vertical orbit has Möbius exponent
exactly `½`; simple-critical proportion `≥ 0.67250071` (imported Zeta23 inputs); four fifths of the zero
ordinates carry a critical zero.

Killed: PNT/short intervals as square-root input, size-only Chebyshev inversion, stronger-than-half-power
target, integrality alone, fixed factorial ratios, univariate sup-norm, fixed-prime stencils, Adams
multiplicity, base-change twists, gauge averages, Vaughan endpoints, `#quasi-character`,
`#single-height-saving`, `#positivity-three-quarters`, `#frullani-phase`, `#pole-matching-half-power`.

| | Obstacle | Strength |
|---|---|---|
| A21 | Logarithmic two-point Chowla | — |
| A24 | Census items; Voronoi; Zwegers | — |
| B26 | `ε`-uniform producer; square-root source input | sub; RH |
| B27 | First cyclotomic mode at square-root precision | RH |
| B28 | Signed pair information beyond bandwidth one | sub |
| B29 | First Epstein real zero on the boost line | sub |
| B32 | Half-power law at the trivial gauge point (proved at an explicit non-special point) | RH |

### S8. Carriers, coupling, selection and the prime-blind cone
Routes: SC, ACS, HF; candidates; PBAP.

Established [L]: coupling calculus; damped cone ⇔ RH; undamped ⇒ RH or unattained width; Weil cone
`⊆ {Λ}`; lattice selection; PBAP ⇔ RH, node-critical, Farkas-dual, zero-side identity, solved on
nonnegative and separated-bump cones; Selberg-class Euler rigidity at `σ = ½`; degree gap `(0, 1)` empty;
degree one has conductor `q ≥ 2m₀` or a genuine pole at `1`; Beurling: regular integers do not
constrain zeros; Hamburger: FE + positivity force `ζ`.

| | Obstacle | Strength |
|---|---|---|
| A11 | Function-field calibration | — |
| A12 | Gaussian-damped coupling identity | — |
| A13 | Finite-level Weil cones `C_A` and their widths (P2 first test) | — |
| A31 | Selberg-class degree-one classification (coefficient periodicity, integer conductor, primitive-character identification) | — |
| B30 | Bounded damped cone coupling; unattained width | RH |
| B31 | Finite-sieve Hodge positivity → global | RH |
| B34 | Rosati positivity of the window reflection | RH |
| B36 | Selection at the trivial gauge point | RH |
| B37 | FE twins inside the full class with off-line zeros | sub |
| B42 | Prime-blind positivity on signed blind combinations | RH |

### S9. Realization and scattering
Routes: PM, RN, PTR, W1C.

Established [L]: Mayer operator, faithful divisor; resonance ⇔ `ζ(2s) = 0`; exact completion
`Q = 2Re[𝓦H, 𝓦H]`, core space dense, window map bounded, Hecke multiplier `p^{1−2s}` (similitude
factor `p`), window involution = twisted conjugate Krein reflection; Lewis periods in
`H_LP = L²((0,∞), (a + a⁻¹)^{−6}a^{−1/2}da)`; `I_s` isometric iff `Re s = ¼`; resonant co-isometry
defect `D_s(ψ_s) ≤ 0`, `< 0` iff `Re s ≠ ¼`; Gauss–Mayer head branch bounded iff `Re s ≤ ¼`, the pair
iff `Re s = ¼`; Farey three-term operator co-expansive `μ_s > 1`; dyadic cusp energy finite iff the
forcing vanishes, for Eisenstein periods iff `s` is a resonance; nonresonant real `σ ∈ (0, ½)∖{¼}`
counterexample to naive three-term reflection positivity; corrected all-prime transport, eigenvalue
`1 + p^{1−2s}`; Hecke cones tile; Barnes/Eisenstein periods Hecke eigenfunctions; whole-Haar admission
iff `H(−log 2) = 0`; closed Cauchy reflection; physical cusp residue = Krein square, Gaussian residue →
complete Weil form, counterterm subtraction supplies no sign; retained `T₂` channel unique, with
`D_s(u_s) = |core_s(2)|²Φ(Re s)` of the sign of `¼ − Re s` and opposite sign at the reflected resonance.

Killed: `#cauchy-reflection-order`, `#mayer-krein-sign`, `#core-hecke-boundary`, `#lewis-inversion`,
`#farey-three-term`, `#hecke-window-cusp`, `#window-krein-reflection`, `#resonant-cutoff-gram`,
`#fixed-height-hecke-residual`, `#mayer-cutoff`, `#mayer-complex-contraction`, `#scattering-recentering`,
`#scattering-schur`, `#congruence-pole-filter`, `KR-AUT`, `KR-SEL`, local PM admission/escape.

Status: P3 is reduced to one inequality on resonances, `D_s(ψ_s) ≥ 0` (the reverse of the proved one).
The retained channel is an unconditional side detector: antisymmetric under reflection, it cannot
select the line [D].

| | Obstacle | Strength |
|---|---|---|
| A14 | Classical identifications (Selberg-zeta normalization, Lax–Phillips, Lewis–Zagier, `+1` eigenspace, Garland); mixed-parameter completion; full Mayer transfer compatibility; analytic completion of the corrected boundary carrier; rational Weyl identification | — |
| A15 | Operator-native nonvanishing on `Re w = 1` (risk: reduces to the Euler product) | — |
| B38 | Arithmetic `D_s(ψ_s) ≥ 0` on resonances (finite cusp energy ⇒ zero defect) | RH |
| B39 | Statistic of resonant states selecting the decay rate | method |
| B40 | Source-faithful realization of unbounded rank | RH |
| B33 | PM-native zero-free region for `ζ(2s)` | sub |

### S10. Zero-configuration geometry and deformation
Routes: ZCG (candidate), LA, TH, HCF, XN, SRT; programmes ZCG, RHTower `DeBruijn`, SquareRootThreshold.

Established [L]:
- Camera: depth is tilt, `f̂(γ − iδ) = (fe^{δu})^(γ)`; pairs analytic in `w²` (real pair, collision,
  tilted pair are the three signs of `w²`); depth signal `≤ 4sinh²(δr/2)∫|f|`; second-order law
  `pairSignal = −w²M₂(f,c) + O(|w|⁴r⁴)` with `M₂ = −(f̂)''(c)`; the height curvature of the prime channel is
  the `(log n)²`-weighted prime sum.
- Identification: finite modifications seen at every aperture; every mimic of `ζ` is infinite; explicit
  inverse by differential windows with conditioning the product of gaps; stable quantitative version
  uniform in height; primes below `e^{2r}` pin every finite piece of the zeros of `ζ`; stable pinning
  with prime discrepancy `D_r = Σ_{n≤e^{2r}}|λ(n) − λ'(n)|/√n`.
- Hiding: on-line mimics contain two points at height distance `< g` for every `g > π/(2a)`, sharp;
  tilted Ingham inequality and its block form for FE pairs; resolution uniform in depth: mimics at
  aperture `a > V/2` contain a near-collision in height at scale `90/V` (depths `≤ 1/V`) or a deep point.
- Function-field camera: aperture `> g log q/2` identifies Frobenius configurations and certifies purity,
  sharp (pure and golden data share images below).
- Euler columns: a zero of `1 + Ap^{−s} + p^{1−2s}` is on the line iff `A² ≤ 4p` (Ramanujan = reality); a
  column is an off-line lattice pair, a mimic of an on-line lattice iff aperture `≤ log p/2`; no bounded
  aperture excludes Euler columns; columns of RvM density are mimics iff the camera exponent `λ ≤ ½`.
- Deformation (polynomial model): reality leaves only through collision; heat flow keeps the centre and
  raises the spread at rate `2n²(n−1)`; backward heat exits reality in bounded time; Laguerre/heat steps
  never deepen; heat steps never shrink the mesh; shift averages contract squared depth
  (`D ↦ max(D − Σμ_j², 0)`).
- Window design: windows blind to `hℤ` and seeing a point exist iff aperture `> π/h`; blind to finite
  unions of lattices at `r > πΣ1/h_j`; blind to zero sets of exponential polynomials and transforms of
  densities; isolating windows read one lattice point; [W] blind to every bounded perturbation of a
  lattice at `r > π/h`.
- Heat path of `Ξ`: real for `t ≥ 1/8`; RH ⇔ real at `0`; infinitely many non-real zeros for every
  `t < 0`; Laguerre inequality for `Ξ` under RH; the first Laguerre inequality alone is not a reality
  certificate.

Status: identification is sign-free and solved where configurations are finite or separated. Any
on-line competitor with the image of `ζ` would itself give Weil positivity, so ZCG's RH content is a
reality mechanism at near-collisions: the sign of the second-order coefficient, read through the
`(log n)²`-weighted primes — the Laguerre–Pólya mechanism of P5 in camera form [D]. The column
threshold `λ = ½` equals the length `√(T/2π)` of the Riemann–Siegel main sum [D].

| | Obstacle | Strength |
|---|---|---|
| A16 | Height-localized identification with explicit constants; perturbed-lattice blind windows [W]; function-field camera extensions | — |
| B14 | Laguerre–Pólya at all ranks and degrees; collision exclusion along a source-faithful path (heat path on `(0, 1/8]`) | RH |
| B43 | Infinite-modification identification at the density scale: the camera at aperture `λ log T`, `λ > ½`, determines the zeros near height `T` up to near-collision clusters | sub |
| B44 | Reality at near-collisions: the sign of `w²` at every cluster, read at all orders through the prime channel | RH |

### Route-specific items
| | Obstacle | Routes | Strength |
|---|---|---|---|
| A17 | Theta Hankel rank 9: the compact source gap left by the cross-load; ranks `≥ 10` at fixed apertures | TH | — |
| A18 | Hausdorff shifts, Jensen horizons, two-grid degrees, PF beyond 37 | PA, LA, HCF | — |
| A19 | Nine atom-dominated collar moduli | ACT | — |
| A20 | Mixed Schur debit; first-prime/coarse/polar costs | AIP, CHMD | — |
| A32 | Finish the receivers marked unfinished in the frontier map: Cayley–Li primitive-sign receiver, SZ first-variation transfer | LI, SZ | — |
| B15 | Scheduled prime energies bounded below | FU, CFC, RP, SZ, LI, FEL, EGC | RH |
| B41 | Pre-divisor forcing | APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF | RH |

## 3. Live routes

Each entry: path; established; open estimate; killed shortcuts; class; A; B.

### WL — Weil lag
- Path: prime error → square-root bound or subexponential critical energy → RH.
- Established: exact prime-error/energy criteria; the first Chebyshev cyclotomic band has energy
  abscissa `2Θ`, and RH ⇔ its energy is `O_ε(N^{1+ε})`; pole-subtracted prime exponents over the gauge
  torus range exactly over `[Θ, 1]`, minimized at the trivial gauge; the reflection-pair coupling is the
  smoothed prime count of `f⋆f` against the collar Hankel form [L].
- Open: actual signed square-root precision of one band; a gauge attaining exponent `½` at the
  arithmetic point (the spectrum identity supplies none).
- Killed: PNT/short intervals as input, size-only inversion, producers of slope `> 1`, integrality
  alone, base-change twists, `#pole-matching-half-power`.
- Class P4. A: A25, A29. B: B1, B26, B27, B32.

### RW — restricted Weil ground energy
- Path: `μ(a) ≥ 0` at every radius → RH.
- Established: attained, strictly radius-decreasing minima; floors through `181/500` and the enlarged
  aperture; exact `{∞, 2}` trace through `½log 3`; window ⇔ lattices; RH ⇔ two-site PD; centre coupling
  `C` = collar Hankel − smoothed prime count with odd sign ⇔ `C ≤ Q`, even sign ⇔ `−C ≤ Q`; contact
  aperture `≥ 3/10`, `μ = 0` at it off RH; fixed-order lattice-to-jet-Hankel scaling [L]; [W] minimizers
  are non-smooth at the window edge.
- Open: an independent all-test coupling bound paying the signed prime folds and the interior energy;
  tight bands give parity zero modes only under window positivity; local collar energy fails at the
  prime `3`.
- Killed: `#lattice-positive-slack`, `#lattice-interior-gap`, `KR-PAF`, `KR-CCP`, `#fold-count-identity`,
  `#frozen-gamma-cubic`, `#folded-markov`, `#collar-local-payment`, `#collar-positivity-induction`,
  semilocal factors, fixed finite-prime positivity.
- Class P1. A: A5, A7, A9. B: B1, B2, B3, B5.

### FU — signed prime scheduling
- Path: signed prime/Möbius history → one-sided sampled Abel bound → RH.
- Established: for each fixed `m ≥ 1`, either upper or lower boundedness of `A(j^m)/j^m` ⇔ RH; one
  controlled sample in each large backward window of length `N^{1−δ}` suffices [L].
- Open: produce those samples from the complete signed history, retaining seed, drift, covariance and
  endpoints.
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
- Established: linear-floor criterion; low-LCM and copied-diagonal payment; a sublinear floor is
  impossible [L].
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
  pronic energy; Möbius exponent Haar-a.e. `½`, Baire-generic `1`; an explicit gauge point outside every
  finitely modified Dirichlet/vertical orbit has exponent exactly `½`; flip points sharing the pole of
  `0` have exponent `max(θ, Θ)`; sparse-prime transfer [L].
- Open: half-power cancellation at the trivial gauge point; uniform signed long-modulus energy for
  dampings cofinal at `0`.
- Killed: gauge averages, stronger-than-half-power target, uniform escaped decay, Vaughan endpoints,
  additive shift, `#quasi-character`, `#single-height-saving`, `#pole-matching-half-power`.
- Class P4. A: A21, A22. B: B26, B27, B32, B36.

### TT — theta tail / Wold
- Path: theta source → directed covariance/Wold decay or odd Weil sign → RH.
- Established: exact receivers; Φ-Doob identities retaining every reflected prime term; restricted
  current signs; the odd sector is the band at the centre; odd theta gauges have window slack [L].
- Open: all-test directed covariance or odd/primitive positivity; the signed reflected-prime interaction.
- Killed: `#horizon-charge`.
- Class P1 (odd sector). B: B1, B3, B4.

### LA — Laguerre/Jensen and local heat
- Path: theta source → all-height/all-degree Jensen or heated coefficient sign → RH.
- Established: every fixed Jensen degree eventually real-rooted; heat/depth bounds and density-one
  fixed-depth control; polynomial Laguerre/heat steps preserve root strips and the real mesh; shift
  averages contract squared depth; reality leaves a fixed-degree real family only through collision;
  heat path real for `t ≥ 1/8`; Newman: non-real zeros for every `t < 0` [L].
- Open: uniform signs for `Ξ` at every height/degree; a source-faithful deformation excluding collisions
  and controlling shallow exceptional windows.
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
- Established: S1 in full: subcritical PD; whole-space PD at one critical multiple with all window
  corollaries; window threshold law and RH ⇔ `R₁ ≡ ⊤`; joint pole payment; twisted sectors positive
  counts; Weil's form at the pole of the frequency counts; bulk, terminal, low-block and receiving-charge
  calculus [L].
- Open: the threshold `R₁(A) = ⊤` at every aperture (the sign on untwisted windows at every multiple);
  at each ratio beyond the size-only interval, the complementary window sign and the energy-weighted
  mixed control.
- Killed: S1 list; `#definite-counts`; dimension-zero domination; the count face (S3).
- Class: sign content P1 on untwisted windows; count face closed; floor layer size-only.
  A: A1–A4, A10, A11, A22, A23. B: B1, B6, B7, B8, B9, B10, B11, B12, B16, B33, B34, B35, B40.

### CHMD — causal hyperbolic–modular duality
- Path: one-sided bounded prime wave or odd Doob half-threshold bound → RH.
- Established: wave/Doob receivers; Haar transport; prime-edge Gamma reserve; all-detail prime–pole
  cancellation `O(exp(−√log Y/92160000))` uniformly over every detail horizon [L].
- Open: upper or lower boundedness of the unnormalized prime wave, or the complete odd sign paying Gamma,
  potential and infinite-orbit terms; `√Y`-normalized decay supplies neither.
- Killed: `#growing-euler-index`, Gamma boundary reserve, Haar/modal compactness, absolute Euler
  coefficient payment.
- Class P1 (odd sector). A: A20. B: B3, B12.

### TH — theta Hankel ranks
- Path: signed centre-mixed theta jets → all-rank Hankel positivity → RH.
- Established: rank 8 PD for every `0 < a < ½`; seventh native successor integral positive; every finite
  rank strict on a factorial collar `|a − ½| < c/(A^{N+1}((2N+1)!)^{N+2})` and on a logarithmic collar
  `|a − ½| < c/(1 + log(N+1))`; rank 9: the skipped origin minor forces a positive fifth load, constant
  diagonal pairs fail at scale seven at every critical aperture, one explicit cross-load preserves every
  mixed integral and is PD near both endpoints and on a cofinal ray [L].
- Open: rank 9 on the remaining compact source set; all-rank positivity at fixed aperture.
- Killed: `#native-tail-boundaries`, rank-uniform native successor, `KR-HFR`, `#ninth-section-diagonal`.
- Class P5 (rank limit). A: A17. B: B14.

### RN — renewal
- Path: theta renewal → divisor-faithful winding/boundary-work sign → RH.
- Established: Green/BV realization; compact cone-positive renewal operator with exact
  determinant/resonances [L].
- Open: directed mixed prime + Gamma `≥` pole including cusp/seam terms; cone positivity alone does not
  give real spectrum.
- Killed: native carrier identification, `KR-R2`, `KR-TRC`.
- Class P3-type (realization). B: B40.

### WD — Ward / collision / window energy
- Path: source current/window energy → collision charge `< 2` or all-resolution sectoriality → RH.
- Established: S6 [L].
- Open: an independent zero-rate right-port bound through the inner caps and finite/shallow exceptions;
  density branch: thin nonempty Planck shadows in `≤ η(A)V` windows with a vanishing cluster tail.
- Killed: S6 list.
- Class P4 (inner caps); density branch sub-RH. A: A26, A27. B: B19, B20, B21, B22, B23, B33.

### LI — paired Li and prime–Gamma balances
- Path: prime − Gamma history floor / theta-clock first-zero budget → RH.
- Established: the guarded history-zero set is finite; RH ⇔ it is empty; Cayley–Li primitive-sign
  receiver (unfinished) [L].
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
- Open: the arithmetic inequality `D_s(ψ_s) ≥ 0` on resonances; source-forced extinction or balance of
  the retained channel (its side is read, not forced); mixed-parameter completion, full Mayer transfer,
  signed-form descent, rational Weyl identification.
- Killed: S9 list.
- Class P3. A: A14, A15. B: B33, B38, B39, B40.

### JAS, CTF, PBM, RB — one-sided counts
- JAS: for every `ε > 0`, bounds `|Riesz(m², k)| ≤ m^{εk}` on moving windows `m < k ≤ m + m/log(m+1)` for
  infinitely many `m` ⇔ RH [L]; open: uniform arithmetic control on that window. Class P4. B: B26.
- CTF: RH ⇔ bounded real rows reach every error tolerance [L]; open: construct the rows or signed
  covariance cancellation along compatible cutoffs, retaining the terminal edge. Killed: CTF
  diagonal/centering, dropping the terminal edge. Class P4. B: B26.
- PBM: exact convergence/RH equivalence [L]; open: coefficient cancellation to the critical abscissa.
  Killed: `KR-RAW`. Class P4. B: B26.
- RB: eventual criteria, colossally abundant reduction [L]; open: square-root remainder on
  prime-saturated extremizers. Class P4. B: B26.

### HCF, XN, BAG, EWU, GTA, OWU
- HCF: heat explicit formula, two-grid criterion, arbitrary-zero detector [L]; open: signs at every
  degree/height or a one-sided vertical bound; two-grid non-aliasing does not control coalescence.
  Killed: one grid aliases, `KR-HFR`. Class P5. A: A18. B: B14.
- XN: coverage/self-map criterion; nonnegative Laplacian of the interior margin [L]; open: an actual
  covering with nonnegative interior margin. Class P5. B: B14.
- BAG: strong/local recurrence receivers; RH ⇔ all high zeros approach the line at each fixed depth and
  arbitrarily high returns on off-line-zero discs [L]; open: arithmetic construction of those returns.
  Killed: `KR-BAG`, `KR-TOR`. B: B36.
- EWU: weight rigidity; attained aperture-antitone blind minima; even positivity ⇔ `−C(f) ≤ Q(f)`;
  even theta gauges are supercritical on a window (outside cosh deficit) [L]; open: an all-aperture
  lower-band bound including low/mixed modes. Killed: `KR-SRP`, `KR-APW`. Class P1 (even sector).
  A: A5, A8. B: B1, B3.
- GTA: exact decay criterion; positive charge and strong finite-prefix convergence [L]; open:
  rank-uniform arithmetic energy decay independent of zero data. Class P5. B: B14.
- OWU: odd RH criterion; odd positivity ⇔ `C(f) ≤ Q(f)`; odd unit window off one moment, retained-Gamma
  identity, higher reserve, one-number reduction; the kick of weight `w`, lag `ℓ` is paid by
  `2we^{a−ℓ/2}` times its collar Lévy energy [L]; open: the joint Gamma/prime/pole sign at every test and
  aperture. Killed: `#first-fold-linear-chord`, `#retained-gamma-lower-form`, `#frozen-gamma-cubic`,
  `#collar-local-payment`. Class P1 (odd sector). A: A5. B: B1, B3, B4, B5.

### SRT, ACT, AIP — complete atomic matrix
- SRT: full-family receivers/index exhaustion; controlled-aperture negative tests for depth `≥ δ`;
  signed critical conductor limit, growing low-block positivity, polar mixed limit on terminal supports;
  ZCG prime pinning and depth-uniform identification [L]. Open: the complementary-window sign at every
  required critical ratio; high-zero tail; general terminal/nonpolar transport; inverse-energy mixed
  control. Killed: tempered fixed-ratio models, `KR-CRT`, `#finite-readings`, `#uniform-margin`.
  A: A1, A3, A10, A27. B: B6, B7, B12, B18.
- ACT: single-shift receiver; collar thresholds pay fixed finite families; exact shifted-gauge identity
  `Ẑ(m_au) = 2S_a − D_a + 8V_c + 8τ_cA₂` with `V_c, A₂ ≥ 0`, `τ_c > 0`; folded origin charge
  `−2Φ(0)∫M dm` must be paid exactly [L]. Open: one shift, uniform in profile/support, paying the
  reflected-prime term `D_a`. Killed: `KR-PAF`, `#folded-markov`, `#folded-origin-charge`. Class P1.
  A: A19. B: B1, B3.
- AIP: allocation receiver; whole-space floor at one small multiple; growing low-conductor positivity at
  every fixed ratio; capacity `log log N + O(1)`; uniform coefficient/overlap and small-packet bounds [L].
  Open: full-space allocation at every ratio: intermediate bands, signed complement, all-cutoff energy
  assembly. Killed: `KR-LGP`, `KR-ADJ`, `#separate-shell-payment`, `#absolute-prime-correction`.
  A: A1, A4, A20. B: B6, B7, B8.

### SC — Stokes/Witt–Krein
- Path: glued affine index `≤ 1` / bounded Gaussian-damped two-prime coupling → RH.
- Established: glued index `κ_ζ + 1`; damped cone ⇔ RH; undamped ⇒ RH or unattained width; tensor
  bounds `|c(t)|^k ≤ C_k e^{L_kt}`, `L_k/k → 0`, imply RH [L].
- Open: an arithmetic bound for the damped coupling, sublinear tensor loss, or glued index `≤ 1`.
- Killed: `#coupling-growth`, `#pole-pair-retuning`, `#additive-reading-index`,
  `#haar-continuous-dilation`, `#separated-place-poles`, `#tensor-square-inertia`,
  `#fixed-prime-counterterm`, `#local-polar-trichotomy`, separable towers, `#padic-localization`,
  `#fixed-prime-global-index`.
- Class P4 (coupling = window error). A: A11, A12. B: B1, B9, B10, B12, B30, B31.

## 4. Candidates

| Candidate | Established | Promotion gap | Strength |
|---|---|---|---|
| ACS | RH ⇔ effectivity ⇔ Hodge index ⇔ section count; primitive `h¹ = Q/2`; pure-curve calibration; Selberg Euler rigidity, degree gap, degree-one conductor or pole [L] | a non-count source of all-aperture primitive effectivity; Rosati heights are receivers | B34; count face closed |
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
| ZCG | see below | a source-side reality mechanism at near-collisions with a proved global RH implication | B14, B43, B44 |

### ZCG — zero-configuration geometry (candidate)
- Path: prime explicit-formula image → configuration identification → reality at near-collisions or
  collision-free deformation → RH.
- Established: S10 in full [L].
- Why a candidate and not a route: identification needs a competing configuration with the same image,
  and an on-line competitor is already Weil positivity; no source-side condition with a proved RH
  implication covers infinite, arbitrarily close clusters. The deformation laws are proved in the
  polynomial model; for `Ξ` the heat path is known real only for `t ≥ 1/8`, and `H_t` is non-real for
  `t < 0`, so the path is critical at `t = 0`.
- Obstacles. A: A16. B: B14 (collision exclusion on `(0, 1/8]`), B43 (identification at the density
  scale), B44 (reality at clusters: the first Laguerre inequality is not a certificate, all orders are
  needed).
- Walls: Γ (identification is selection without sign) and P5 (Laguerre–Pólya at all orders); at the
  density scale it meets the square-root threshold `λ = ½`, which is the Riemann–Siegel length.

## 5. Decisive wall per route

| Wall | Routes |
|---|---|
| P1 — signed criticality / stage step / frustration domination | RW, EWU, OWU, ACT, CHMD, TT, SZ, HF (sign content), ACS (sign content), MSC; CWS, WTZ, DZG, GWZ, CSTW, SWC |
| P1 at large ratios — untwisted windows / threshold `R₁ ≡ ⊤` | HF, SRT, AIP, SC; CACT, AHD, CSAR |
| P4 — one-point square-root precision (the band in prime form) | WL, MC, PBM, RB, JAS, CTF, SC (coupling), FU, CFC, RP, LI, EGC, FEL |
| P4 — inner caps (zero-free region to the line) | WD, TG |
| P5 — rank / degree / collision limits (Laguerre–Pólya) | TH, HCF, PA, GTA, LA, XN; ZCG (candidate) |
| P2 — prime-blind positivity | PBAP |
| P3 — reflection positivity (zero side) | PM, W1C, RN, PTR |
| Γ — trivial gauge point / pre-divisor forcing | BAG, MC; APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF |
| closed — counts / Hodge index | ACS (count face), HF-RR, IRK |
