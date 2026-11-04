# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route; labels `A*`, `B*`, `S*`, mechanism classes P1–P5),
`walls-ledger.md` (Σ/Π/Γ) and `route-unification-ledger.md` (classes C1–C21). Evidence: `[L]` Lean
declaration; `[W]` working tree or draft module; `[D]` derived here from Lean statements; `[M]` exact
model statement; `[N]` numerical; `[P]` paper. Killed mechanisms are cited by their anchor in
`rh-killed-routes.md`. Window tests of length `A` live on `[−A, 0]` or `[−a, a]`, `a = A/2`;
`w_n = Λ(n)n^{−1/2}`; for a test `f` left of `m` and its mirror `f∘R`, `R(v) = 2m − v`,
`𝒞_m(f) = 𝓗_m(f) − Σ_nw_n(f⋆f)(2m − log n)` with the collar Hankel form
`𝓗_m(f) = e^mμ_{1/2}(f)² − Σ_ke^{2mσ_k}μ_{σ_k}(f)²`.

## 1. The big picture

### 1.1 RH is the band on reflection pairs
RH ⇔ every two-site lattice window is PD ⇔ `|c_φ(t)| < Q(φ)` for every bump and `t ≠ 0` [L: GWZ]. For a
test and its mirror, `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`, so the band `|𝒞_m(f)| ≤ W(f)` is positivity on the
pair, and the odd and even sectors of a symmetric window are the band at its centre [L: SWC]. The collar
Hankel form is the main term `e^mμ_{1/2}(f)²` of the smoothed prime count of `f⋆f` minus exponentially
small trivial-zero squares; it has one positive square (the pole) and infinitely many negative ones
(`(1, ∞)` beyond the plastic distance) [L: SWC]. So the minimal decisive object is the smoothed
prime number theorem at square-root precision, with constant `W(f)`, in a fixed multiplicative window.

### 1.2 The canonical system: lattices solved, local continuum solved, global open
Lattice windows are Szegő–Levinson theory of Weil sequences: Schur parameters, outer predictors,
Carathéodory–Fejér degenerations, one kick per Schur parameter, Szegő singular under RH [L: GWZ]. The
continuum limit at a bump is the jet Hankel system `J_n = [W(φ^{(i)}, φ^{(j)})]`, with
`h^{−2n}E_n → det J_{n+1}/det J_n`, unconditionally [L: SWC]. The global canonical system — a
Hamiltonian carrying the prime kicks — is not constructed.

### 1.3 The gauge calculus of signed criticality is exact
Weil's form is `M + ½⟨c,·⟩² − ½⟨s,·⟩²` with `M` a Markov form with arithmetic jump rates. `M` has a
negative test of support `e^{−3/4}`, admits no positive supersolution on any longer interval, and ACT's
folded criterion is void on the unit odd window [L: SWC]: every certificate must keep the pole. In a
gauge `F = Φωu` the window form is a signed Dirichlet form plus pole charges,
`Ẑ(Φωu) = J_{Φω}(u) + ∫u²ω𝒢_S(ω) + 2V_s − 2V_c` [L]; theta gauges are critical on the whole line; a
window reads their outside charges with the pole's signs — slack in the odd sector, deficit in the even
sector; ACT's shifted ground states are strict pole-charged supersolutions on every window [L]. On odd
tests the frozen form is Markov and the kick is anti-Markov; the kick is a positive source minus an
anti-diagonal conductance; the odd light cone is nonnegative in every odd gauge [L].

### 1.4 Local resources certify few kicks; the rest is the prime count
The collar light cone pays the kick of `n` at ratio `2w_ne^h`, `h` the collar half-width, and the ratio is
sharp [L: SWC]. Because `2w_n < 1` exactly for `n = 2`, the proper prime powers and the primes `≥ 79`, and
`2w_p > 1` for the primes `3 ≤ p ≤ 73` [D], the prime `3` is the first prime that its own collar cannot
pay (`exists_prime_three_collar_unpaid` [L]), and the light cone certifies the kick of any other `n` only
while the window half-width is `≤ log n − log(2log n)` [D]. Kicks outside the certified range need
resources beyond their own collar, and on a reflection pair the sum of all anti-diagonals is the
smoothed prime count in `𝒞_m` [L/D]. P1 and P4 are one problem beyond the first stages. The proved
positive region, length `0.7240`, lies inside the range `≤ log 2 + 2·(−log(√2 log 2)) ≈ 0.7330` where the
light cone certifies the prime-two kick on odd tests [D]; the odd unit window (length `1`) is beyond it.

### 1.5 The complete family: size-only layers are complete; the sign is a threshold
The complete Weil matrix is PD below `(log N)^{1/8}` and on the whole prime-horizon space at one critical
multiple `2K₀(log N)^{1/8}`, with every window corollary (horizon Grams, pencil index `0`, weighted sign,
mixed families) [L: CACT/AHD]. Every window has a threshold `R₁(A)`: below it the critical pencil is PD,
above it a test is eventually negative; `R₁ ≥ R₀ > 0` for every `A`; RH ⇔ `R₁(A) = ⊤` for every `A`
[L: AHD]. The floor that pays the small multiple, `Q ≥ −C(p)∫e^{−pu}H²` for `p > 1`, carries no zero
information: `p > 1` is forced by the Cauchy–Schwarz bound on the pole moment `∫He^{−y/2}`, and by the
contact law a floor with exponent `p` gives only zero width `≤ p` [L/D]. Bulk, terminal, low-block and
receiving-charge layers are classified and polar [L].

### 1.6 PM is the zero side, with a side detector
`Q(H) = 2Re[𝓦_AH, 𝓦_AH]` exactly on `ℓ²(upper Mayer resonances)`; Hecke is translation, similitude
factor `p` [L: RIT]. The co-isometry defect of every resonant Lewis period is `≤ 0` and vanishes exactly
on `Re s = ¼` [L]; finite dyadic cusp energy characterizes resonances on the Eisenstein family [L]. The
retained `T₂` boundary channel has defect of the sign of `¼ − Re s`, opposite at the reflected resonance
[L]: it reads the side of a resonance, it does not place it [D]. The PM sign is the reverse inequality
`D_s(ψ_s) ≥ 0` on resonances.

### 1.7 The camera of the explicit formula identifies without sign
The Weil image identifies finite modifications of a zero configuration at every aperture, constructively
and stably; the primes below `e^{2r}` pin every finite piece of the zeros of `ζ`; mimics must contain a
near-collision at the camera's resolution or a deep point [L: ZCG]. Euler columns are the arithmetic
fakes: Ramanujan `A² ≤ 4p` is reality of a column, columns hide below aperture `log p/2`, columns of RvM
density hide exactly for camera exponent `λ ≤ ½` [L], and `λ = ½` is the Riemann–Siegel length [D].
Reality of a near-collision is a second-order sign, carried by the `(log n)²`-weighted primes [L]. An
on-line competitor with the image of `ζ` would already be Weil positivity [D], so identification alone
decides nothing.

### 1.8 Reality by continuation is exactly critical
`H_t` is real for `t ≥ 1/8` (corpus normalization), has finitely many non-real zeros for every `t > 0`
(Ki–Kim–Lee: confined to `(Im z)² ≤ ¼ − 2t`), and infinitely many for every `t < 0` (Newman)
[L: RHTower DeBruijn]. Reality of a fixed-degree real family is lost only through collision [L: ZCG].
With finitely many confined non-real zeros on `(0, 1/8]`, a non-real pair can be born only at a
collision, so RH ⇔ no collision of zeros of `H_t` for `t ∈ (0, 1/8]` [D]. The first Laguerre inequality is not a reality certificate [L].

### 1.9 Criticality: no slack anywhere
Weil cone `{Λ}`; lattices Szegő singular under RH; aperture floor forced to decay doubly
exponentially; theta gauges critical on the line; heat path real at `t ≥ 1/8` and non-real at every
`t < 0`; numerical margins `1.5×10⁻⁵` (odd) and `5.6×10⁻⁸` (even) at half-width `½log 3` [N]; [W] the
infimum of a window is not attained on smooth tests. Every exact reading of RH sits on a zero-slack
boundary: a proof must be an identity at the boundary, not an inequality with room [D].

### 1.10 Counts, Hodge index and degeneration are closed as an RH mechanism
Bare domination ⇔ `Q ≥ 0`; no Gamma–pole family dominates the Tate counts; the pole weight is pinched to
`1/ζ(1+k)` and refuted; every concrete count type is excluded [L: ATD, DZG, LST]. Conclusion [D]: the
count/Hodge/degeneration programme cannot close RH.

### 1.11 Selection and minimal input
Selection after positivity is automatic (Weil cone `{Λ}`; lattice selection) [L]. A positive measure with
Riemann's FE is the counting measure of `ℕ`; positive primes with regular integers allow off-line zeros;
Selberg-class Euler rigidity at `σ = ½`, degree gap `(0,1)`, degree one with conductor `≥ 2m₀` or a pole
[L: APD, RHTower, SEL]. A proof uses the functional equation and the Euler product together.

### 1.12 Precision and density
Near-line density is one statement in eight forms; `D_win` ⇔ thin Planck shadows; `D_zero` ⇔ `D_win` +
vanishing giant-cluster tails [L: CDG]. The WD cap `σ_m = 1 − 1/(116log(m+5))` is the classical
zero-free region [L]. The gauge torus has pole-subtracted exponent range exactly `[Θ, 1]`, the half-power
law holds at an explicit non-special point, and the pole does not decide it [L: AGT]. Simple-critical
proportion `≥ 0.67250071` (imported Zeta23 inputs); four fifths of the zero ordinates carry a critical
zero [L].

### 1.13 What is ruled out
| Mechanism | Verdict | Anchor |
|---|---|---|
| Fold paid as a cost (exit charge, collar loan, transfer criterion) | refuted at the first prime | `#frozen-gamma-cubic` |
| Lossless lower forms of the odd unit window (retained Gamma, `+E/64`, two-moment, polynomial chord) | refuted | `#retained-gamma-lower-form`, `#first-fold-linear-chord` |
| Markov ground states; folded supersolutions | dead beyond `e^{−3/4}`; void on the unit odd window | `#prime-free-markov`, `KR-BD`, `#folded-markov`, `#folded-origin-charge` |
| Collar-local payment of every kick; automatic positive reflected coupling | fails at the prime `3`; Hankel negative of every dimension | `#collar-local-payment`, `#collar-positivity-induction` |
| Lossless local allocation; shifted ground-state combinations | refuted | `KR-LGP`; ACT [L] |
| Finite-square / finite-rank identities and realizations | refuted | `#fold-count-identity`, `#finite-window-realization`, `KR-FPR` |
| Slack (uniform floors, lattice slack, uniform Gram floors) | refuted | `KR-PAF`, `#lattice-positive-slack`, `#growing-overlap-floor` |
| Counts / Tate domination / Hodge index from counts | closed [D] | 1.10 |
| Size-only layers as Weil information | blind | `#fixed-packet-bulk`, `#twisted-horizon-blindness` |
| Low-conductor deletion, raw-cost charge control, vanishing complement coupling | refuted | `#low-conductor-deletion`, `#prime-pole-cost`, `#charge-complement-vanishing` |
| Interior-gap continuation | not structural | `#lattice-interior-gap` |
| PM line selectors (Lewis inversion, three-term + inversion, Krein projections, resonant statistics, contractive scattering, recentering, retained channel) | refuted or side-only | `#lewis-inversion`, `#farey-three-term`, `#mayer-krein-sign`, `#resonant-cutoff-gram`, `#scattering-schur`, `#scattering-recentering`; RIT [L] |
| Bounded operator symmetry for the PM reflection off `Re s = ¼` | refuted | `#cauchy-reflection-order` |
| Selectors without positivity; regular integers; bounded apertures against Euler columns | blind | Γ16; RHTower Beurling, ZCG [L] |
| Pole matching as half-power input | refuted | `#pole-matching-half-power` |
| Producers below parity | refuted at their stated scope | rows in "Geometry, analytic tests" |
| First Laguerre inequality as a reality certificate | refuted | HTGeometry [L] |
| Fixed-aperture / finite-horizon positivity as a decision | refuted | `KR-CRT`, `#finite-readings` |

### 1.14 The live mechanism classes
| Class | Statement | First open test | Status |
|---|---|---|---|
| P1 signed criticality | exact signed payment of every kick in a gauge, the collective kicks against the pole square | odd unit window (one prime-two weight); windows of length `< log 4` (prime `3`) | live; Markov, folded, cost-only and sign-blind certificates excluded |
| P2 prime-blind positivity | archimedean + pole part `≥ 0` on signed combinations of autocorrelations vanishing on `±log ℕ_{≥2}` | finite-level cones `C_A`, `A ≤ log 6` | live; solved on nonnegative and separated-bump cones |
| P3 PM reflection | `D_s(ψ_s) ≥ 0` on resonances | — | reduced to the zero side; defect `≤ 0` proved |
| P4 square-root cancellation | the band in prime form for one smoothed count | — | live; classical; parity barrier for sieve producers |
| P5 reality by continuation | no collision along a source-faithful path | heat path on `(0, 1/8]` | live as a receiver; critical at `t = 0` |

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Explicit constants and horizons: `K₀`, eighth-root theorem, `1/9`, logarithmic profile, Beurling schedule, horizon criterion, conductor range `M(N) = o(c_N)` | HF, SRT, AIP, ACS, SC | effectivization of proved limits |
| A2 | General profiles past `θ = 1/1080` | HF, SRT, SC | tilted-spline template |
| A3 | Joint twist families; equal-parity characters through `L(s, ψ̄₁ψ₂)`; different moduli | HF, SRT, AHD | single-family proofs are templates |
| A4 | Certified ratio interval at its size-only optimum (joint pole, higher Gamma reserves) and the receiving-charge complement inside it | HF, AIP, SRT, CSAR | assembly of proved estimates (difficulty unverified) |
| A5 | Numerical certificates: first prime stage `[0.7240, log 3)`, second stage, `w₂ ∈ unitBandWeights` | RW, OWU, EWU, GWZ, CWS | finite computation; decides cases, not mechanisms; margins tiny |
| A6 | Rational Hecke graphs and Tate horizons of stages 3, 4, 5, 7, … | WTZ, CWS | finite graphs |
| A7 | Closed form of the first-stage complement `Φ_ε` | GWZ, CSTW, WTZ, RW | explicit archimedean Schur complement |
| A8 | Even-sector counterparts of the odd gauge identities | EWU, RW, SWC | mirror of proved odd identities (difficulty unverified) |
| A9 | Edge-singularity theorems of window eigenfunctions [W] | RW, SWC, GWZ | draft statements with a stated proof mechanism (difficulty unverified) |
| A10 | Window index as a function of the length | AHD, SRT, CWS | conditional calculus |
| A11 | Function-field calibration | AHD, ACS, SC, HF | the sign is known there |
| A12 | Gaussian-damped coupling identity | SC, ACS | explicit formula |
| A13 | Finite-level Weil cones `C_A` and their widths (P2 first test) | PBAP, ACS, RW | finite convex programs, Farkas duality in place |
| A14 | PM classical identifications; mixed-parameter completion; full Mayer transfer compatibility; analytic completion of the corrected boundary carrier; rational Weyl identification | PM, W1C | known theories |
| A15 | Operator-native nonvanishing on `Re w = 1` | PM | Eisenstein template (risk: reduces to the Euler product) |
| A16 | Height-localized identification with explicit constants; perturbed-lattice blind windows [W] | ZCG, SRT | quantitative versions of proved identification |
| A17 | Theta Hankel rank 9 compact source gap; ranks `≥ 10` at fixed apertures | TH | finite computation on a compact set |
| A18 | Hausdorff shifts, Jensen horizons, two-grid degrees, PF beyond 37 | PA, LA, HCF | effectivization |
| A19 | Nine atom-dominated collar moduli | ACT | finite case analysis |
| A20 | Mixed Schur debit; first-prime/coarse/polar costs | AIP, CHMD | fixed-dimensional estimates |
| A21 | Logarithmic two-point Chowla | MC | Tao's theorem |
| A22 | Björner wedge decomposition | MC, HF | classical topology |
| A23 | Depth law, star horizons, gcd strata | HF, ACS | effectivization |
| A24 | Census items; Voronoi; Zwegers | census, ACS, HF | classical |
| A25 | Künneth primitive `h¹` at small degree; mixed jets | ACS, WL | calibration |
| A26 | WD composition; Vinogradov–Korobov cap in place of `σ_m` | WD, LA, TG | classical zero-free region |
| A27 | Cluster-detector constant | SRT, WD | constants |
| A28 | Atomic-lattice bound `λ_max ≤ ½log N` | WTZ, HF | classical |
| A29 | Bridge: reflection-pair coupling = smoothed count → WL/JAS/CTF/PBM/RB receivers | WL, JAS, CTF, PBM, RB, GWZ | composition of proved identities |
| A30 | Two-site band on a bounded step range from numerical zeros | GWZ, WL | computation; decides nothing |
| A31 | Selberg-class degree-one classification | ACS, SEL | known theorem |
| A32 | Receivers marked unfinished in the frontier map: Cayley–Li primitive sign, SZ first-variation transfer | LI, SZ | statements in place |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on windows of every length (≡ band on every reflection pair ≡ lattice Schur parameters in `(−1,1)` ≡ `R₁ ≡ ⊤` ≡ `ι(A) = 0` ∀A ≡ Krein positivity of zero coordinates ≡ PBAP) | RH; fixed length sub | all sign routes |
| B2 | Kick admission at every stage | RH as induction; each stage sub | RW, GWZ, CSTW, WTZ, HF, SZ |
| B3 | Frustration domination at every length: a gauge in which the collective kicks are paid against the pole square, odd and even | RH; fixed length sub | P1 routes |
| B4 | Structural certificate of the odd unit window (`w₂ ∈ unitBandWeights`) | sub | OWU, RW, TT, SWC |
| B5 | Non-local payment of the prime `3`: windows of length `< log 4` | sub | RW, OWU, EWU, SWC |
| B6 | Twisted-sector positivity through all conductors and frequencies at every multiple | sub | HF, SRT, AIP, AHD |
| B7 | Full-space sign at critical ratios beyond the size-only threshold | sub per ratio; RH for all | HF, SRT, AIP, CSAR |
| B8 | Full-space positivity of general profiles past `log log N` | sub | HF, SRT, AIP, SC |
| B9 | Exact SOS on one two-prime lattice | RH | HF, SC, ACS |
| B10 | No zero mode at any length | RH | HF, TG, SC, EHT, GWZ |
| B11 | Top coprime stratum | RH | HF, ACS, ADT |
| B12 | Index ceiling uniform in resolution | ≥qRH; RH (tensor) | CHMD, SRT, WD, SC |
| B13 | Zero–one law `κ ∈ {0, ∞}` | sub | SC, HF, ACS, CWS, SRT |
| B14 | Laguerre–Pólya at all ranks/degrees; collision exclusion along a source-faithful path | RH | TH, LA, HCF, PA, GTA, XN, ZCG |
| B15 | Scheduled prime energies bounded below | RH | FU, CFC, RP, SZ, LI, FEL, EGC |
| B16 | Window negativity exponent `< ½` in the window length (≡ zero width `< ½`); implied by a floor with exponent `p < ½` | ≥qRH | window routes, HF, WD |
| B17 | Global continuum canonical system of the tower | identity | GWZ, CSTW, SZ, SWC |
| B18 | Contact law beyond the density-matched boundary | sub | window routes |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B19 | Inner caps `[½, σ_m]` at every polynomial stage | RH; fixed degree ≥qRH | WD, TG |
| B20 | `100%` critical-scale clustering | sub | WD, census, MC, HEF |
| B21 | `D_win` ≡ thin Planck shadows; `D_zero` | sub | WD, census |
| B22 | Hecke defect pointwise / dyadic | ≥qRH / RH | WD |
| B23 | Distributional input beyond counts and moments | method | WD, HEF |
| B24 | Genus upper law | indep. | ACS |
| B25 | Logarithmic Serre duality, primitive part | sub | ACS, HF |
| B26 | `ε`-uniform producer; square-root source input | sub / RH | WL, MC, PBM, RB, JAS, CTF |
| B27 | First cyclotomic mode at square-root precision | RH | MC, WL, CAF |
| B28 | Signed pair information beyond bandwidth one | sub | census, ACS |
| B29 | First Epstein real zero on the boost line | sub | ACS |
| B30 | Bounded damped cone coupling; unattained width | RH | SC, ACS |
| B31 | Finite-sieve Hodge positivity → global | RH | SC |
| B32 | Half-power law at the trivial gauge point | RH | MC, WL |
| B33 | Route-native arithmetic sign: HF pencil beyond the size-only interval or floor at exponent `p = 1` from primes; PM-native zero-free region for `ζ(2s)`; WD cap from the source | sub | HF, PM, WD |

### Γ — selection and reflection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B34 | Rosati positivity of the window reflection | RH | HF, ACS, CWS, GWZ, PM |
| B35 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH | HF, ACS, SC, PM |
| B36 | Selection at the trivial gauge point | RH | MC, BAG |
| B37 | FE twins inside the full class with off-line zeros | sub | HF, ACS, SC, SEL |
| B38 | Arithmetic `D_s(ψ_s) ≥ 0` on resonances | RH | PM, W1C |
| B39 | Resonant-state statistic selecting the decay rate | method | PM |
| B40 | Source-faithful realization of unbounded rank | RH | RN, PTR, W1C, PM |
| B41 | Pre-divisor forcing | RH | APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF |
| B42 | Prime-blind positivity on signed blind combinations | RH | PBAP |
| B43 | Identification at the density scale of `ζ` (local inversion up to near-collisions) | sub | ZCG, SRT |
| B44 | Reality at near-collisions, at all orders | RH | ZCG, LA |
| B45 | Cross-tower gap through the archimedean channel | method | HF, AIP |

### Settled questions (classified; not obstacles)
| Question | Answer | Anchor |
|---|---|---|
| Can a Markov supersolution certify a window longer than `e^{−3/4}`? | No; the pole must be kept | SWC [L] |
| Does the folded supersolution criterion apply on the unit odd window? | No supersolution exists there | SWC [L] |
| Can each prime kick be paid by its own collar? | Certified when `2w_ne^h ≤ 1`; fails at thin collars when `2w_n > 1`, i.e. for the primes `3 ≤ p ≤ 73` | SWC [L]; [D] |
| Is the complete family positive on the whole space at one critical multiple? | Yes, with every window corollary; size-only | CACT, AHD [L] |
| Is the untwisted window a positive Tate piece? | No: Weil's form sits at the pole of the frequency counts | AHD [L] |
| What decides HF? | `R₁(A) = ⊤` for every `A` | AHD [L] |
| What does the aperture-independent floor say about zeros? | nothing: `p > 1` is forced by the pole moment; a floor with exponent `p` gives only width `≤ p` | WTZ, SquareRootThreshold [L]; [D] |
| What is the continuum limit of a lattice at a bump? | the jet Hankel system | SWC [L] |
| Is there a bounded operator identity for the PM reflection across the strip? | Only for `Re s ≥ ¼` | RIT [L] |
| Is Weil energy exactly a PM Krein form? | Yes | RIT [L] |
| Does the retained Hecke channel select the line? | No; it reads the side | RIT [L]; [D] |
| Do the primes determine finite pieces of the zeros? | Yes, at every aperture | ZCG [L] |
| Can bounded apertures exclude Euler columns? | No | ZCG [L] |
| Does the interior of a window carry the decisive failure? | No: two sites decide; minimizers are edge-singular [W] | GWZ, SWC [L/W] |
| Is no-slack structural? | Yes | GWZ, RHTower [L] |
| Do regular integers and positive primes decide the zeros? | No | RHTower Beurling [L] |
| What do the functional equation and positivity determine? | `ζ` | APD [L] |
| Does the window algebra contain a Frobenius? | No; Frobenius at scale `t` is translation | DZG, RIT [L] |
| Does positive dimension supply positivity? | No | ATD, DZG [L] |
| Does the pole decide the half-power law? | No | AGT [L] |

## 2.3 Frankenstein routes

**Verdict: no assembly closes RH.** Every assembly ends at one named residual. Two assemblies reduce the
residual to a single precise law (F2 and F5); none circumvents it.

### F1. The gauge–tower assembly (P1)
| Segment | Supplied by | Status |
|---|---|---|
| RH ⇔ window sign ⇔ reflection pairs ⇔ parity sectors at the centre | CWS, GWZ, SWC | [L] |
| Base: all real `C²` tests positive through `0.7240`; first stage opens positive; flip rejected | SPATL, GWZ, SWC | [L] |
| Pole must be kept (Markov death; folded criterion void) | SWC | [L] |
| Exact gauge calculus: pole-charged representation, theta gauges critical on the line, outside-charge slack (odd) | SWC, ACT | [L] |
| Kick = source − anti-diagonal conductance; odd light cone `≥ 0`; collar ratio sharp | SWC | [L] |
| Stage criterion; frozen form in closed form; Levinson admission; jet Hankel limit | GWZ, CSTW, SWC | [L] |
| Odd unit window off one moment; higher Gamma reserve; one-number reduction | WTZ, SWC | [L] |
| Core: exact payment of the collective kicks against the pole square in every stage | — | B3 (RH) |

It bypasses conductors, dimension zero, counts, density and PM. It does not bypass exactness: every
shortcut of 1.13 is excluded at its core.

### F2. The multiscale assembly (P1 ⊕ P4)
Idea: in a window of half-width `a` pay the kicks inside their collar-certified range (`2w_ne^h ≤ 1`)
locally by their collars (SWC [L]), and pay the others by window positivity at a smaller scale, where
their prime sums are controlled.

| Segment | Supplied by | Status |
|---|---|---|
| Local payment of certified kicks at ratio `2w_ne^h` | SWC `kick_add_collarLevyEnergy_nonneg` | [L] |
| All kicks on a reflection pair = smoothed prime count in `𝒞_m` | SWC | [L] |
| Window positivity at length `a` bounds prime sums with autocorrelation kernels `g⋆g̃` of tests on `[−a, 0]` | CWS | [L] |
| The reflection pair at length `2a` needs prime sums with the cross-correlation kernel `(f⋆f)(2m − ·)` of `f` and its mirror | SWC | [L] |
| Bridge from autocorrelation (PD) bounds at scale `a` to cross-correlation bounds at scale `2a` | — | missing: by polarization it is positivity on `f ± f∘R`, i.e. the band at scale `2a` [D] |

Residual: the doubling step breaks exactly at polarization; the missing bridge is the band itself (B1).
The assembly also needs a lossless allocation of the archimedean light cone among all certified collars
(`KR-LGP` refutes allocation for general frustrated cycles, not for this arithmetic geometry).

### F3. The complete-family assembly (blind)
Subcritical PD (CACT) + whole space at one critical multiple (CACT/AHD) + threshold law (AHD) + joint
pole (WTZ/AHD) [L]. It is complete at small ratios and carries no Weil information there; beyond the
size-only threshold it lands on B7, and at every ratio on `R₁ ≡ ⊤` = B1.

### F4. The reflection assembly (P3)
PM exact completion + window involution + collar Rosati pairing + Lewis co-isometry calculus + retained
channel [L]. Residual: `D_s(ψ_s) ≥ 0` on resonances (B38), the reverse of the proved inequality; the
retained channel is antisymmetric under reflection and cannot supply it.

### F5. The camera–continuation assembly (Γ ⊕ P5)
| Segment | Supplied by | Status |
|---|---|---|
| Heat path real for `t ≥ 1/8`; finitely many non-real zeros for `t > 0`; non-real for `t < 0` | RHTower DeBruijn, KiKimLee | [L] |
| Reality lost only through collision; heat/Laguerre steps keep mesh and depth (model) | ZCG | [L] |
| Collisions are near-collisions of the camera; reality there = sign of the second-order coefficient, read through `(log n)²`-weighted primes | ZCG | [L] |
| Hiding needs near-collisions or deep points; finite pieces pinned by the primes | ZCG | [L] |
| Core: no collision for `t ∈ (0, 1/8]` | — | B14 (RH) |

It bypasses positivity of Weil's form and counts. Residual: collision exclusion, an all-order
Laguerre–Pólya statement localized at near-collisions (the first Laguerre inequality is not enough).

### F6. Density–index–cluster (WD ⊕ AHD ⊕ CWS ⊕ AKLT ⊕ SRT)
Off-line zeros live in density-zero window sets, are seen at aperture `≍ log|γ|log log|γ| + 1/δ`, each
raising the window index [L]. Residual: index ceiling and zero–one law (B12, B13): ≥qRH.

## 2.4 A wildly different route

**Verdict: no route that avoids all three walls is visible.** Every route reads the zeros through the
explicit formula or through a function whose divisor is that of `ζ`, and the three walls are the three
components of that formula: the sign of the zero side (Σ), the size of the prime side (Π), and the
identification/reflection between them (Γ). The corpus covers every known approach class (positivity,
precision, realization, deformation, recurrence, counts, function-field transfer, quasicrystals,
Lee–Yang).

The farthest direction not developed in the corpus, recorded as a possibility, not a route:

**Multivariate stability on the prime torus.** Lee–Yang/Borcea–Brändén stability gives zeros on the line
without positivity of a form: a stable self-reciprocal multiaffine `Q` gives a Dirichlet polynomial
`Q(n₁^{½−s}, …, n_k^{½−s})` with every zero on `Re s = ½` [L for the two-prime family
`ZetaZerosLeeYangQuasicrystal`; D from stability and self-reciprocity in general; RHTower
`StableDirichletPolynomialPutnam` is the companion theorem]. A route would extend `ξ` to a function `F` of independent variables
`z_p = p^{½−s}` on the infinite torus that is stable (nonvanishing on the open polydisc) and
self-reciprocal variable by variable; stability + self-reciprocity force the zeros onto the line by the
same contraction argument.
- What is far: no window, no sign of a quadratic form, no square-root count.
- Where it meets the walls: the functional equation of `ζ` is the simultaneous inversion `z ↦ 1/z` on
  the diagonal Kronecker line only, and the Gamma factor is not multiplicative in the primes (Γ: no
  Frobenius at the archimedean place); finite stable self-reciprocal Dirichlet polynomials have critical
  zeros that are not zeros of `ζ` [L], so `ζ` is not among them; the Herglotz function the Lee–Yang
  argument produces is a Herglotz positivity of a logarithmic derivative on `Re s > ½`; for `ξ` that
  positivity is equivalent to RH, i.e. Σ in Herglotz form [D].
- First test: the existence, for one prime, of a self-reciprocal stable extension of the Euler factor
  together with the Gamma factor — the archimedean obstruction appears already there.

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — an exact certificate of the odd unit window
**Question.** Prove `w₂ = log 2/√2 ∈ unitBandWeights` — equivalently the Markov–Hankel inequality
`4S(f)² ≤ M(f) + Σ_jm_j(f)² + w₂(f⋆f)(−log 2)` on `[−½, 0]` [L: SWC] — by an identity that writes the odd
unit-window form as a nonnegative Dirichlet form in an explicit odd gauge plus pole charges, with the
prime-two crossing conductance dominated by the archimedean fold surplus and the outside sinh slack.
- **Below RH.** One window, one prime, one sector, one scalar membership.
- **Why it is not settled by known tools.** The Markov part is dead on `(0, ½)`; the prime-two kick is
  outside its collar-certified range (`h = ½ − ½log 2 > −log(√2 log 2) ≈ 0.0199`) [D]; the frozen form is
  indefinite; every lossless lower form is refuted (retained Gamma, `+E/64`, two-moment, polynomial chord,
  folded supersolution) [L].
- **Advance.** The first window where the pole must be kept and the kick lies outside its collar's
  certified range, done exactly: it exhibits a signed payment beyond the collar at one prime.

### 2.5.2 Route PM — a zero-free region owned by the Lewis–Hecke carrier
**Question.** From the Lewis–Hecke structure alone — three-term equation, modular inversion, the Hecke
eigenrelations `T_{p,s}ψ_s = (1 + p^{1−2s})ψ_s`, the co-isometry calculus on `H_LP` and the retained
`T₂` channel sign law — prove that no Mayer resonance lies on `Re s = ½` and then a de la Vallée
Poussin-type region `Re s ≤ ½ − c/log|Im s|` for the resonances, i.e. for the zeros of `ζ(2s)`.
- **Below RH.** PNT strength.
- **Not ruled out because.** Every killed PM mechanism is a line selector; none concerns a zero-free
  region. Risk: the cone counting behind the eigenvalue `1 + p` is the Euler product (A15), so the
  argument may reduce to the classical one.
- **Advance.** The first sign statement PM owns; every other PM statement is an identity, a side
  detector or a blind positivity.

### 2.5.3 Route WD — log-free window occupancy
**Question.** Prove `D_win`: for every `A > 0` the number of unit windows `[t, t+1] ⊂ [V, 2V]` containing a
zero of depth `≥ A/log V` is `≤ ε(A)V`, `ε(A) → 0`; equivalently, thin Planck shadows occupy `o_A(V)` unit
windows [L: CDG equivalence].
- **Below RH.** A density statement.
- **Why it is not settled by known tools.** Zero-density estimates near the line carry a factor `log V`:
  the deep zeros number `≍ e^{−cA}V log V`, more than the `V` windows, so `D_win` is a statement about the
  clustering of near-line off-line zeros, which counts and moments cannot give
  (`#window-density-separation`, clustered and sparse models [M]).
- **Advance.** WD's one analytic input at the log stage; it upgrades the double-log stage to a log stage
  on almost all windows.

### 2.5.4 Route HF — beat the size-only threshold with the primes
**Question.** Prove that the critical pencil `a_φQ(H) + (7J(1)/R)M₈(H)` is positive on every window at
one explicit ratio `R > jointPoleCriticalRatio`, by an argument that uses the prime input (receiving
charges, terminal windows, conductor packets), not only Gamma/pole bounds. Floor form: an
aperture-independent floor `Q(H) ≥ −C∫e^{−pu}H²` at the edge exponent `p = 1`, which the size-only proof
cannot reach because it bounds the pole moment `∫He^{−y/2}` by Cauchy–Schwarz [L].
- **Below RH.** A fixed ratio is a finite statement; by the contact law a floor with exponent `p = 1`
  gives only zero width `≤ 1`, far below quasi-RH [L/D].
- **Why it matters.** Every HF layer proved so far is size-only [L/D]. This question tests whether the
  complete family carries arithmetic sign at all.
- **Not to be pursued.** Uniform floors along growing overlaps (`#growing-overlap-floor`), bare counts
  through all conductors (`#conductor-count-resolution`), low-block deletion (`#low-conductor-deletion`),
  a count for the untwisted window (1.10).

### 2.5.5 Route ZCG — identification at the density scale
**Question.** Prove that two tempered configurations of Riemann–von Mangoldt density whose images agree on
windows of aperture `λ log T`, `λ > ½`, modulated to height `T`, coincide near `T` outside near-collision
clusters of diameter `o(1/log T)` — a local inversion of the explicit formula at the square-root
threshold, with stable dependence on prime data.
- **Below RH.** Sign-free.
- **Not ruled out because.** Identification is proved for finite modifications, for separated
  configurations and uniformly in depth [L]; the density scale is the remaining case; the threshold
  `λ = ½` is sharp for columns [L].
- **Advance.** The explicit formula at the Riemann–Siegel length would determine the zeros up to the
  coalescent set; RH would localize to reality at near-collisions (B44).

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — exact collective payment
**Question.** On every reflection pair `f, f∘R`, write `W(f) − |𝒞_m(f)|` as a nonnegative Dirichlet form in
a gauge plus nonnegative pole charges: find a gauge family, exact on the line like the theta gauges,
whose restriction to every window pays the collective kicks against the pole square, in both parity
sectors.
- **Why it opens the path.** It is B3, hence B1 and RH; the gauge calculus is exact [L], so only the
  domination is missing.
- **Constraints.** Markov dead past `e^{−3/4}`; folded criterion void; collar locality sharp, prime `3`
  unpaid; theta gauges critical on the line with even-sector deficit; window minimizers edge-singular
  [W]; numerical margins `~10⁻⁸` near length `log 3` (criticality); the functional equation and the Euler
  product must both enter.

### 2.6.2 Route PM — finite cusp energy forces zero defect
**Question.** Prove `D_s(ψ_s) ≥ 0` for every resonant Lewis period: finite dyadic cusp energy ⇒ zero
co-isometry defect.
- **Why it opens the path.** `D_s(ψ_s) ≤ 0` with equality iff `Re s = ¼` is proved [L]; the reverse
  inequality is RH, as an inequality between two explicit quadratic functionals of one function. The
  arithmetic enters the retained channel only through `core_s(2) ≠ 0` [L]; a second arithmetic channel
  with the opposite side law would be the needed input.

### 2.6.3 Route WD — inner-cap cancellation
**Question.** On every Burnol unit window, at every polynomial stage, cancel the right-port flux through
the inner caps `[½, σ_m]` by a source identity.
- **Why it opens the path.** Across all degrees it is RH; at fixed degree it is the corridor
  `|β − ½| ≤ C/|γ|^k` [L]. The cap is the zero-free region, so the question is the zero-free region pushed
  to the line by a window identity.

### 2.6.4 Route HF — the threshold stays infinite
**Question.** Prove `R₁(A) = ⊤` for every window length `A`.
- **Why it opens the path.** It is RH [L]. The threshold is antitone, `⊤` up to
  `2·enlargedWeilFloorAperture`, and bounded below by `R₀` [L]; HF supplies no mechanism of its own for the
  sign: its content is P1 on untwisted windows of radius `½log K`, and the receiving-charge complement must
  be paid with sign at every ratio.

### 2.6.5 Route ZCG — collision exclusion on the heat path
**Question.** Prove that the zeros of `H_t` never collide for `t ∈ (0, 1/8]`.
- **Why it opens the path.** `H_{1/8}` is real; for `t > 0` the non-real zeros are finitely many and lie
  in `(Im z)² ≤ ¼ − 2t`; a non-real pair can only be born at a collision; real-rootedness passes to `t → 0`
  [L/D]. So the question is RH. ZCG supplies the local picture: a collision is a near-collision of the
  camera, and its reality is the sign of the second-order coefficient carried by the `(log n)²`-weighted
  primes [L]; the needed input is a source-side repulsion law for backward heat time.

## 2.7 Does closing RH need a new field?

**Assessment: yes — an arithmetic criticality theory: positivity, at exact criticality, of frustrated
nonlocal Dirichlet forms with arithmetic jumps.** Its dictionary exists in the corpus (SWC, ACT, GWZ,
CSTW, WTZ, DZG); its core is open; the corpus fixes what the core cannot be.

*What it is about.* Translation-invariant quadratic forms on the line whose symbol is known only through
the dual side (the primes), restricted to intervals of every length: a logarithmic-order archimedean
jump form, arithmetic jumps of length `log n` with rates `w_n`, a constant renormalized potential, a
rank-two pole term (one positive, one negative square) and the infinite-rank trivial-zero Hankel
correction. Positivity is required on every interval, at exact criticality (zero ground energy in the
limit), with frustration carried by anti-diagonal conductances.

*What it would be like.* Exact (identities at the boundary, never inequalities with slack); signed (each
kick used with its sign); multiscale (certified kicks local, the rest collective); critical (Hardy-type
optimality rather than spectral gaps); edge-singular (minimizers live at the collars); Krein-flavoured
(the pole contributes one negative square).

*Criteria it must meet.*
1. Reproduce the base `0.7240`, the first stages and their margins `~10⁻⁵–10⁻⁸`.
2. Pay the pole's negative square (the hyperbolic pair `e^{±h/2}` on lattices).
3. Be critical: margins tend to zero along every lattice; theta gauges are exact on the line.
4. Deliver the band on every reflection pair (two sites decide).
5. Pay the kicks outside the collar-certified range: the primes `3 ≤ p ≤ 73` from their entry, every
   other prime power once `h > log(1/(2w_n))`.
6. Force `Λ` and fail for flips, Euler twins, Beurling systems, `ζ(s)ζ(s−ε)`, Davenport–Heilbronn,
   Epstein and golden data.
7. Use the functional equation and the Euler product together.
8. Explain the square-root threshold (`λ = ½`, the Riemann–Siegel half) as the place where the
   functional equation supplies the other half of the data.

*Questions it must answer.*
- Is the arithmetic part of Weil's form an optimal Hardy weight for the archimedean logarithmic jump
  operator with the pole kept — nonnegative and critical — and can the Keller–Pinchover–Pogorzelski
  construction of optimal weights from pairs of positive solutions produce it?
- Which gauge family, exact on the line, restricts to every window with a nonnegative remainder in both
  sectors, and how is the even-sector cosh deficit paid?
- What is the collective law: how do the anti-diagonals outside the certified range pair with the pole square on a
  reflection pair, uniformly in the stage?
- What is the edge behaviour of critical window minimizers, and how does it constrain certificates?
- What is the global canonical system (Hamiltonian with the prime kicks), and does an exact Schur step
  propagate its positivity from one stage to the next?

*Tools.* Criticality theory and optimal Hardy weights for nonlocal operators (Keller–Pinchover–
Pogorzelski); signed-graph theory (balance, switching, frustration index, Kron reduction); Krein and
Pontryagin spaces; Krein strings, de Branges spaces and Szegő–Levinson theory; spectral theory of the
regional logarithmic Laplacian (Legendre spectrum `2H_n`); Doob transforms; the corpus's pole-charged
representation and collar light-cone calculus.

*Objects and language.* Gauges `ω`, theta gauges, charge weights `m_s, m_c`, charge variances
`V_s, V_c`, outside charges `τ`, crossing conductances, collar classes, the collar Hankel form, Schur
parameters, jet Hankel matrices, the pole's hyperbolic pair, edge-singular profiles, certified and
uncertified kicks.

*Mechanisms it aims to discover.* An exact collective identity (pole square against the smoothed prime
count) on reflection pairs; a renormalization step from scale `a` to `2a` that does not lose the
cross-correlation (the polarization obstruction of F2); a criticality-preserving gauge flow.

*Explicitly outside the field.* Counts and Hodge index; Tate domination; Markov ground states;
sign-blind and finite certificates; PM operator symmetry off `Re s = ¼`.

## 2.8 The one question

**Is there an exact signed certificate of Weil positivity on every window of length `< log 4`?**
On such windows the primes `2` and `3` act, the Markov part is dead, the frozen forms are indefinite,
both parity sectors must be paid, and the prime `3` cannot be paid by its own collar
(`2Λ(3)/√3 > 1`, `exists_prime_three_collar_unpaid` [L]); near length `log 3` the numerical margins are
`1.5×10⁻⁵` (odd) and `5.6×10⁻⁸` (even) [N].

*Why it is less hard than RH or quasi-RH.* A finite window, two primes, an explicit gauge calculus
[L: SWC]. It implies no statement about zeros at large height.

*Why it pushes the door open.* It is the smallest problem that contains every ingredient of the general
stage step: a kick that local resources provably cannot pay (Σ44), collective payment against the pole
square (Π30), both sectors (odd slack, even deficit), and margins so small that only an identity can
work (criticality). The odd unit window (2.5.1) is its one-prime, one-sector shadow. A structural answer
gives the template of the induction step (B2, B3); a proof that no certificate of the natural class
exists identifies the term that the next certificate must retain.

*Precise boundary.* Excluded: Markov supersolutions (dead past `e^{−3/4}`), folded supersolutions (void),
collar-local payment (fails at `3`), lossless lower forms (refuted), finite-square identities (refuted),
cost-only payments (refuted). Not excluded: odd theta-gauge certificates with outside-charge slack,
pole-charged supersolutions with non-compact gauges, variable-hub Schur elimination, packed nonlocal
paths, and any exact identity that uses the trivial-zero Hankel squares.
