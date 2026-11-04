# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route; labels `A*`, `B*`, `S*`, mechanism classes P1–P5),
`walls-ledger.md` (Σ/Π/Γ) and `route-unification-ledger.md` (classes C1–C25). Corpus state: `3374f0b7c6`
plus working tree. Evidence: `[L]` committed Lean; `[W]` working-tree Lean; `[P]` pipeline-card paper proof
not yet formalized; `[D]` derived here from Lean statements; `[M]` exact model statement; `[N]` numerical.
Windows `[−c, c]` or half-windows `[−c, 0]`; `w_n = Λ(n)n^{−1/2}`; for `f` left of `m` and its mirror
`f∘R`, `𝒞_m(f) = 𝓗_m(f) − Σ_nw_n(f⋆f)(2m − log n)`. `a*(Z)` is the onset aperture of a zero configuration
(supremum of half-widths at which every `C²` window test has `Re W_Z(f,f) ≥ 0`); `a*(ζ)` is that of the
zeros of `ζ`. `pairEnergy(δ, a) = sinh(2δa)/(2δ) − a`; `ρ` the plastic number, `ρ³ = ρ + 1`,
`log ρ ≈ 0.2812`.

## 1. The big picture

### 1.1 One number decides every window route
RH ⇔ `a*(ζ) = ⊤` [L: WVL]. On every tempered configuration the window-positive half-widths form the
closed interval `[0, a*(Z)]`, and `a*(Z) = ⊤` exactly when every zero is on the line [L]. HF's window
threshold is the same number: `R₁(A) = ⊤ ⇔ A/2 ≤ a*(ζ)` [L]. Off RH, `a*(ζ)` is the contact aperture and
positivity holds at it. The two-site band, the parity sectors, the jet moment problems, the lattices, the
stage step and Künneth effectivity below `log 4` are all statements `a*(ζ) ≥ a` for some `a`. Known:
`a*(ζ) ≥ enlargedWeilFloorAperture ∈ (0.362, ½)` [L]. Nothing larger is proved.

### 1.2 The first stages are two numbers
A half-window test on `[−c, 0]` meets no prime lag iff `c ≤ log 2` [L]. For `0 < c < log 2` the window is
positive iff `(Λ(2)/√2, Λ(3)/√3) ∈ belowLogFourBandWeights c`, the intersection of the odd and even sector
sets: convex, compact once `c > ½log 3`, a cylinder in `w₃` before `3` enters, excluding every `w₂ ≤ 0` for
`c ≥ 21/40` [L: SWC]. The same statement is the Hodge index of the scaling subsurface, Künneth effectivity,
a retained-variance certificate in any positive even theta gauge (even sector) and in any shifted ground
state (odd sector), and `R₁(A) = ⊤` for `A < 2log 2` [L]. The corpus holds no certificate for any
`c ∈ (0.362, log 2)`, structural or numerical.

### 1.3 The primes pay by sign, not by size
`(f⋆f)(−ℓ) = ∫_I(f₊² − f₋²)` (sliver signature); every prime power costs at most
`(Λ(n)e^c/(2n))·levyEnergy f`; `{2,3}` together `< ¾` [L]. Summed over acting prime powers the bound stays
below the Lévy energy exactly on windows shorter than `log 5` [D]. Yet the Markov part is negative beyond
support `e^{−3/4}`, `w₂ ≤ 0` and the flip are inadmissible, the prime `3` cannot be carried by its collar
size (`c ≥ 287/500`) and deleting it breaks odd positivity (`c ≥ 3/5`) [L]. The primes are small and
indispensable: they pay through the sign of their sliver reflections.

### 1.4 Positivity-preserving structure ends at the plastic threshold
In the even sector, `E(f) − E(|f|) = ∬D(u,v)[ω(|u−v|) + ω(−u−v) − 4cosh(u/2)cosh(v/2)]`, `D ≥ 0`: the pole
is the only anti-Markov term, paid by the Lévy jumps and the trivial-zero squares, and prime reflections
only help [L: SWC PerronSignLaw]. The even band is Markov exactly for `c ≤ log ρ`; for `log ρ < c < log 2`
every pole strength `s ≥ 1` and every choice of prime weights admit `E_s(f) < E_s(|f|)` (a test positive at
the edge, negative at the centre) [L]. Robust Perron in the pole strength costs height
(`4(s₁ − s₀) ≤ M²(E_1(g) − λ + ε)`); the arithmetic pole sits within `O(λ₀)` of the positivity threshold;
robust kick margins force the odd ground state to decouple reflected sliver pairs [L]. Beyond `c = log ρ`
ground states change sign: the even sector is frustrated by the pole, the odd sector by the kicks
(`kick = source − conductance`). Certificates there must be signed.

### 1.5 Certificates must keep the pole variance
Dropping the variance fails for `c > 273/400`; nonnegative even theta gauges have a negative cosh-charged
defect [L]. Retaining the variance (the all-pairs jump form `∫∫m(x)m(y)(u(x) − u(y))²`) makes the
certificates exact below `log 4` [L]. The certificate format is settled; only the arithmetic membership is
open.

### 1.6 Sectors are moment problems; extremals live at the edge
Even sector ⇔ Hamburger, odd ⇔ shifted Hamburger, window ⇔ Stieltjes for `s_k = W(φ^{(k)})` [L]. No window
eigenfunction, constrained ground state or capacity maximizer is smooth; the lattice canonical system
freezes onto the boundary of the Schur disk (`γ_n → (−1)^n`, normal velocities `e_{n+1}/e_n`), parity
split `det J_n = det E·det O` [L]. The global continuum system with the prime kicks is not constructed.

### 1.7 Local resources certify few kicks; soft entry is margin transport
Collar-internal jumps pay the kick of `n` at ratio `2w_ne^h` (sharp, never for `3 ≤ p ≤ 73`); outward jumps
carry the newest prime power at `w_ne^h/2`; a sector margin `η` admits every newest weight within
`ηΩ(2c − log p)`, `Ω(δ) ≥ (e^{−1/2}/2)log(1/δ)` [L]. Carrying `w₃` by soft entry alone needs
`η·0.303·log(1/δ) ≥ 0.634`: a margin `η = 1` covers `c ≤ 0.61` only [D].

### 1.8 The complete family is size-only below the sign
Complete Weil matrix PD below `(log N)^{1/8}` and at one critical multiple; terminal sources polar;
correctors cannot improve zero-source windows; the polar capacity is attained by one pole coefficient [L].
Simultaneous receiving charges: arbitrary charges on fixed finite modes with vanishing input, adjunction and
physical energy, read by exact complementary receivers at factor `1/80` [L]. Every proved layer is blind to
the zeros; HF's sign content is `a*(ζ) = ⊤`.

### 1.9 What a window sees: the visibility law
In a lattice Riemann–von Mangoldt background of spacing `2π/L`, a multiplicity-`k` off-line pair of depth
`δ` is window-positive at half-width `a ≤ L/2` iff `k·pairEnergy(δ, a) ≤ L` [L: WVL]: the deep law
`2δa ≍ log(4δL/k)` and the shallow cubic law `a ≍ (3L/(2kδ²))^{1/3}` are one equation. In every RvM
configuration, positivity at `a` (`δa ≥ 2`) excludes unshielded coherent clusters through an
`e^{2(δ−σ)a}/δ` law, to doubly-exponential height [L]. Shallow coherent clusters admissible under the
unconditional depth-mass bound are seen once `δ²a³ > 3/2`, far below `(loglog T)/a` [L]; spread shallow sets
hide while their unit-window depth² mass is `≲ L/a³` [L]; separated runs hide while `2δa·sinh(2δa) ≤ 1` [L].
Shielding beats windows: a tapered crystal packet hides a zero of depth `1/a` above single-exponential
height for every `L ≥ 4a`, and two configurations identical below `exp((e^{2δa} − 2)/(4δ) − a)` have opposite
window signs [L]. Columns: positivity at `a > πD_on + (π/2)D_off` certifies split column families; `πD/2` is
false for mixed ones (exact onset `(g − ½)ℓ`); one moved off-line pair collapses the onset of an off-line
lattice from `L/2` to `≈ (1/2δ)log(δL/ε²)`, while ℓ¹ jitter `2Le^{δL}Σ|ε_k| ≤ 1` keeps it [L]. So
`λ = ½` hides off-line columns only on an `e^{−δL}`-thin crystalline ridge.

For ζ the laws are unconditional but conditional on window positivity, which is proved only at
`a ≤ 0.362`, where `δa ≥ 2` is impossible: the unconditional ζ output is vacuous [D]. Zero information from
P1 starts at half-width `4` and, with the present constants (`2²⁶·960`), at `≈ 20` [D]. The contact law at
`c log T` is a power-saving zero-location bound [L].

### 1.10 The camera identifies, completely and without sign
At aperture `λ·½log(T/2π)`: for `λ > 1` two RvM configurations with the same image coincide near `T` outside
near-collision clusters of diameter `< δ/log T`; for `λ > ½` when one carrier contains the other; ζ's
isolated zeros and their exact multiplicities are read by one window pair at every `λ > ½`; for
`0 < λ ≤ 1` disjoint-carrier half-shifted lattices with RvM error `≤ 1` are mimics [L: ZCG]. Inside a
near-coincidence the image reads the net multiplicity, the centre to `O(r²)` and the squared gap `w²` to
`O(r³)`, with window loss `e^{C log²X}`; the sign of `w²` — real pair or functional-equation pair — is
read only when `|w²|` beats that loss [L]. Polynomial-scale precision needs isolating windows with
polynomial floor, which worst-case RvM-blind windows do not have [L/D]. Fakes are caught exactly at their
first prime; shallow configurations are resolved at the Ingham scale, optimally [L]. An on-line competitor
with the image of ζ is already Weil positivity: identification decides nothing alone [D].

### 1.11 Reality by continuation: size reaches exactly half the saddle
Zeros of `H_t` near height `X` are real and simple for `t ≥ (6600/9991 + ε)/log X` (sub-Weyl profile; sharp
for that profile) [L]. The general source-profile repulsion law needs a margin above `½`; the Gaussian saddle
enters `Re s > 1` exactly at `t = ½/log(X/2π)`; the Lindelöf-bounded Riemann-density pair model collides
below every positive time scale, at `t* < min(δ²/2, δ/L)` [L]. In the pair model every depth `δ ≤ ½`
collides before `½/log X`: the band no size bound reaches contains every possible off-line zero [D]. Every
finite real Dirichlet carrier is real and simple above its horizon `2πe^{W_a}`, and twins are tilted at
every height (tilts cost weight `log(t/2π)`) [L]: domination is not ζ-specific. Over `𝔽_q` integrality
supplies repulsion (collide or repel); for ζ the image is a `log p`-weighted prime sum [L].

### 1.12 PM is the zero side, and its sign is the identity `δ = 0`
`Q = 2Re[𝓦H, 𝓦H]` on `ℓ²(upper Mayer resonances)`; canonical Krein–Lax–Phillips space with Krein
self-adjoint generator; on-line resonances have Krein square `1`, off-line antisymmetric combinations `−2`;
RH ⇔ Krein form `≥ 0` ⇔ renormalized Hodge index [L]. The co-isometry defect of a resonance is
`−∫2cosh(δu)4sinh²(δu)|F(u)F(−u)|`, `δ = Re ρ − ½` [L]: its vanishing is `δ = 0`, not an inequality with
room. The retained `T₂` channel reads the side [L]. A PM proof needs an arithmetic second expression of
the defect, manifestly `≥ 0`.

### 1.13 Criticality: no slack anywhere
Weil cone `{Λ}`; lattices Szegő singular under RH; reflection coefficients freezing at `±1`; ground-energy
margins `≤ K exp((11/2)a − πe^{2(a−2)})`; theta gauges critical; extremals never smooth; Perron exactly to
`log ρ`; heat path real at `t ≥ 1/8`, non-real at `t < 0`, size horizon at the saddle; PM defect vanishing
only at `δ = 0`; numerical margins `1.5×10⁻⁵`/`5.6×10⁻⁸` at `c = ½log 3` [L/N]. A proof must be an identity
at the boundary [D]. Ground-energy margins are at most `K exp((11/2)a − πe^{2(a−2)})` (`≲ Ke^{−149}` at
`a = 4`), so numerical certification cannot reach the half-widths `a ≥ 4` where windows begin to carry zero
information [D].

### 1.14 Counts, Hodge index and degeneration are closed as an RH mechanism
Bare domination ⇔ `Q ≥ 0`; no Gamma–pole family dominates Tate counts; every concrete count type is
excluded; below `log 4` Künneth effectivity is the window sign [L]. Counts cannot close RH [D].

### 1.15 Selection and minimal input
Weil cone `{Λ}`; lattice selection; fakes caught at their first prime; Selberg-class Euler rigidity at
`σ = ½`, degree gap, degree one with conductor `≥ 2` or a pole; positive measures with Riemann's FE are the
counting measure of `ℕ`; positive primes with regular integers allow off-line zeros [L]. A proof uses the
functional equation and the Euler product together, and — by 1.11 — the Euler product inside the strip.

### 1.16 Precision and density
Near-line density is one statement in eight forms; `D_win` ⇔ thin Planck shadows; right-half squared-depth
moment `o(V)` [L]. The WD cap `σ_m` is the classical zero-free region [L]. Gauge-torus exponent range
`[Θ, 1]` [L]. Simple-critical proportion `≥ 0.67250071` [L].

### 1.17 What is ruled out
| Mechanism | Verdict | Anchor |
|---|---|---|
| Fold paid as a cost | refuted at the first prime | `#frozen-gamma-cubic` |
| Lossless lower forms of the odd unit window | refuted | `#retained-gamma-lower-form`, `#first-fold-linear-chord` |
| Markov ground states; folded supersolutions | dead beyond `e^{−3/4}` | `#prime-free-markov`, `KR-BD`, `#folded-markov`, `#folded-origin-charge` |
| Beurling–Deny / Perron for the even band past `log ρ` | refuted at every pole strength and weight | SWC PerronSignLaw [L] |
| Certificates without the pole variance | refuted for `c > 273/400` | `#variance-dropped-theta-gauge` |
| Nonnegative even theta-gauge cosh certificates | refuted | `#theta-gauge-cosh-defect` |
| The prime `3` carried by its collar size; prime `3` deleted | refuted for `c ≥ 287/500`; `c ≥ 3/5` | `#prime-three-sliver-potential` |
| Collar-local payment of every kick | fails at the prime `3` | `#collar-local-payment`, `#collar-positivity-induction` |
| Smooth extremals / smooth zero modes | none exist | `#smooth-window-attainment` |
| Finite-square / finite-rank identities and realizations | refuted | `#fold-count-identity`, `#finite-window-realization`, `KR-FPR` |
| Slack (uniform floors, lattice slack, Gram floors, full-horizon reference floors) | refuted | `KR-PAF`, `#lattice-positive-slack`, `#growing-overlap-floor`, `#full-conductor-diagonal` |
| Counts / Tate domination / Hodge index from counts | closed [D] | 1.14 |
| Size-only layers as Weil information | blind | `#fixed-packet-bulk`, `#twisted-horizon-blindness` |
| Deciding a window from zeros below a height | refuted (doubly-exponential non-locality) | WVL [L] |
| Height induction (RH to `T` ⇒ windows of length `c log T`) | the contact step is itself a zero-location statement; zeros below `T` decide windows only to half-width `≍ loglog T` | WVL [L]; [D] |
| `πD/2` as a universal column threshold; `λ = ½` as a general hiding law | refuted (mixed columns; single-defect collapse) | WVL [L] |
| Two-carrier local inversion at `λ ≤ 1` | refuted | ZCG [L] |
| Domination by finite carriers as ζ-selector | non-selective | ZCG [L] |
| Size-only heat repair below `½/log X` | refuted (`pairModel`) | ZCG [L] |
| PM line selectors | refuted or side-only | `#lewis-inversion`, `#farey-three-term`, `#mayer-krein-sign`, `#resonant-cutoff-gram`, `#scattering-schur`, `#scattering-recentering` |
| Bounded operator symmetry for the PM reflection off `Re s = ¼` | refuted | `#cauchy-reflection-order` |
| Pole matching as half-power input | refuted | `#pole-matching-half-power` |
| Fixed and quartic cross-loads for theta rank 9 | refuted at scales 8 and 32 | `#theta-fixed-cross-load` |
| Fixed-aperture / finite-horizon positivity as a decision | refuted | `KR-CRT`, `#finite-readings` |

### 1.18 The live mechanism classes
| Class | Statement | First open test | Status |
|---|---|---|---|
| P1 signed criticality | primes pay the prime-free deficit by the signs of their sliver reflections, pole variance retained, signed (non-Perron) gauge | `a*(ζ) ≥ ½` (odd unit window); `a*(ζ) ≥ log 2` (two weights) | live; format exact; Markov, Perron, variance-free, size-only, cost-only certificates excluded |
| P2 prime-blind positivity | archimedean + pole part `≥ 0` on signed blind combinations | finite-level cones `C_A`, `A ≤ log 6` | live |
| P3 PM reflection | an arithmetic expression of the defect with manifest sign | a PM-native zero-free region for `ζ(2s)` | reduced to the identity `δ = 0` |
| P4 square-root cancellation | the band in prime form for one smoothed count | — | live; classical; parity barrier |
| P5 reality by continuation | no collision along a source-faithful path below `½/log X` | the Euler product inside the strip as a repulsion input | live as a receiver; the size horizon is the saddle |

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Explicit constants and horizons: `K₀`, eighth-root theorem, `1/9`, logarithmic profile, Beurling schedule, horizon criterion, conductor range `M(N) = o(c_N)` | HF, SRT, AIP, ACS, SC | effectivization of proved limits |
| A2 | General profiles past `θ = 1/1080` | HF, SRT, SC | tilted-spline template |
| A3 | Joint twist families; equal-parity characters; different moduli | HF, SRT, AHD | single-family proofs are templates |
| A4 | Certified ratio interval at its size-only optimum; receiving complement inside it | HF, AIP, SRT, CSAR | assembly of proved estimates (difficulty unverified) |
| A5 | Rigorous computer-assisted certificate of `(w₂, w₃) ∈ belowLogFourBandWeights c` on `(0.362, log 2)`; the odd unit window as its first case | RW, OWU, EWU, ACT, GWZ, SWC, HF | operator inequality on `L²[−c, 0]` with explicit kernels; margins `~10⁻⁵–10⁻⁸` [N]; decides cases, not the mechanism, and carries no zero information |
| A6 | Rational Hecke graphs and Tate horizons of stages 3, 4, 5, 7, … | WTZ, CWS | finite graphs |
| A7 | Closed form of the first-stage complement `Φ_ε` | GWZ, CSTW, WTZ, RW | explicit Schur complement |
| A8 | Even-sector cosh-credit supersolutions with retained variance | EWU, RW, SWC | mirror of the odd identities (difficulty unverified) |
| A9 | AIP literal channel norms made critically small with growing periods, offsets and prime bands; small and offset-dividing primes | AIP | size estimates with the proved sieve bounds (difficulty unverified) |
| A10 | Window index as a function of the length | AHD, SRT, CWS | conditional calculus |
| A11 | Function-field calibration | AHD, ACS, SC, HF | the sign is known there |
| A12 | Gaussian-damped coupling identity | SC, ACS | explicit formula |
| A13 | Finite-level Weil cones `C_A` and their widths | PBAP, ACS, RW | finite convex programs, Farkas duality in place |
| A14 | PM classical identifications; mixed-parameter completion; Mayer transfer compatibility; boundary carrier; rational Weyl identification | PM, W1C | known theories |
| A15 | Operator-native nonvanishing on `Re w = 1` | PM | Eisenstein template (risk: reduces to the Euler product) |
| A17 | Theta rank 9: an entry-preserving compensation varying with scale across `[8, 32]` and the compact centre gap; ranks `≥ 10` at fixed apertures | TH | finite-dimensional sign on a compact parameter set with exact capacities (difficulty unverified; two compensation families excluded) |
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
| A31 | Selberg-class degree-one classification | ACS, SEL | known theorem |
| A32 | Unfinished receivers: Cayley–Li primitive sign, SZ first-variation transfer | LI, SZ | statements in place |
| A33 | Lévy sector margins at `c = ½log 3` in both sectors | RW, OWU, EWU, SWC | numerical; feeds soft entry |
| A35 | Sharpen the general RvM coherent-cluster law: constants `2²⁶·960` toward the model constant `4δL/k` | WVL, RW, SRT, HF, every P1 route | explicit test functions and sampling bounds already in place; makes positivity at half-width `≈ 4–5` carry zero information above verified heights |
| A36 | Formalize the onset-law card items: aligned `k`-pair law with distinct ordinates, general RvM shallow depth-mass bound under positivity, tapered crystal to `a ≍ log T`, two-bump interferometer, synthesis | WVL | paper proofs complete [P]; formalization in progress [W] |
| A37 | Simultaneous receiving with growing mode sets and growing `M` | AIP, HF, CSAR | fixed finite case proved; uniformity estimates (difficulty unverified) |
| A38 | Sub-Weyl strip profile from the best known exponent pairs, moving the heat horizon from `6600/9991` toward `½` | LA, ZCG | known subconvexity; cannot pass `½` and decides nothing about zeros |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on windows of every length (≡ `a*(ζ) = ⊤` ≡ band on every reflection pair ≡ Stieltjes moments of jet energies ≡ `R₁ ≡ ⊤` ≡ Krein positivity ≡ PBAP) | RH; fixed length sub | all sign routes |
| B2 | Kick admission at every stage (transport of `a*(ζ) ≥ a` across each prime-power entry) | RH as induction; each stage sub | RW, GWZ, CSTW, WTZ, HF, SZ |
| B3 | Frustration domination: a signed gauge with retained pole variance in which the sliver reflections of all acting prime powers pay the collar Hankel form, odd and even | RH; fixed length sub | P1 routes |
| B4 | Structural certificate of the odd unit window (`w₂ ∈ unitBandWeights`) | sub | OWU, RW, TT, SWC |
| B5 | Structural certificate below `log 4` (`a*(ζ) ≥ log 2`), the prime `3` paid by sign | sub | RW, OWU, EWU, ACT, TT, SWC, HF, ACS |
| B6 | Twisted-sector positivity through all conductors and frequencies at every multiple | sub | HF, SRT, AIP, AHD |
| B7 | Full-space sign at critical ratios beyond the size-only threshold | sub per ratio; RH for all | HF, SRT, AIP, CSAR |
| B8 | Full-space positivity of general profiles past `log log N` | sub | HF, SRT, AIP, SC |
| B9 | Exact SOS on one two-prime lattice | RH | HF, SC, ACS |
| B10 | No zero mode at any length | RH | HF, TG, SC, EHT, GWZ |
| B11 | Top coprime stratum | RH | HF, ACS, ADT |
| B12 | Index ceiling uniform in resolution | ≥qRH; RH (tensor) | CHMD, SRT, WD, SC |
| B13 | Zero–one law `κ ∈ {0, ∞}` | sub | SC, HF, ACS, CWS, SRT |
| B14 | Collision exclusion along a source-faithful path: heat path on `(0, ½/log X]` with Euler-product input inside the strip; Laguerre–Pólya at all ranks and degrees | RH | TH, LA, HCF, PA, GTA, XN, ZCG |
| B15 | Scheduled prime energies bounded below | RH | FU, CFC, RP, SZ, LI, FEL, EGC |
| B16 | Window negativity exponent `< ½` (≡ zero width `< ½`) | ≥qRH | window routes, HF, WD |
| B17 | Global continuum canonical system of the tower | identity | GWZ, CSTW, SZ, SWC |
| B33 | HF-native arithmetic sign: one `A > 2·enlargedWeilFloorAperture` with `R₁(A) = ⊤` from the complete family | sub | HF |
| B49 | Signed ground-state structure past `log ρ` (nodal law / signed Doob gauge for the pole-frustrated even band and the kick-frustrated odd band) | method | EWU, OWU, RW, ACT, SWC |

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

### Γ — selection and reflection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B34 | Rosati positivity of the window reflection | RH | HF, ACS, CWS, GWZ, PM |
| B35 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH | HF, ACS, SC, PM |
| B36 | Selection at the trivial gauge point | RH | MC, BAG |
| B37 | FE twins inside the full class with off-line zeros | sub | HF, ACS, SC, SEL |
| B38 | An arithmetic expression of `D_s(ψ_s)` at resonances with manifest sign `≥ 0` | RH | PM, W1C |
| B39 | Resonant-state statistic selecting the decay rate | method | PM |
| B40 | Source-faithful realization of unbounded rank | RH | RN, PTR, W1C, PM |
| B41 | Pre-divisor forcing | RH | APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF |
| B42 | Prime-blind positivity on signed blind combinations | RH | PBAP |
| B44 | Reality at near-coincidences: the sign of `w²` of every near-coincident cluster of ζ, read through the prime channel | RH | ZCG, LA |
| B45 | Cross-tower gap through the archimedean channel | method | HF, AIP |
| B46 | PM-native zero-free region for `ζ(2s)` | sub | PM |
| B48 | Second-order local inversion at polynomial scales for ζ (isolating windows with floor polynomial in the isolation radius on ζ's configuration) | sub | ZCG, LA |

### Settled questions (status quo answers)
| Question | Answer | Anchor |
|---|---|---|
| What decides every window route? | the onset aperture: RH ⇔ `a*(ζ) = ⊤`; `R₁(A) = ⊤ ⇔ A/2 ≤ a*(ζ)` | WVL [L] |
| Which off-line zeros can a window see? | master law `k·pairEnergy(δ,a) ≤ L` in lattice backgrounds (deep log law, shallow cubic law); unshielded coherent clusters to doubly-exponential height; shielded depth-`1/a` zeros hide above single-exponential height; spread shallow sets hide while `a³W ≲ L` | WVL [L] |
| Is the positive-aperture set closed? | yes, `[0, a*(Z)]`; seeing and hiding are exact contrapositives | WVL [L] |
| Can zeros below a height decide a window? | no: doubly-exponential non-locality | WVL [L] |
| What is the contact law? | a power-saving zero-location bound for coherent clusters | WVL [L] |
| Is `πD/2` a universal column threshold? | for pure off-line columns yes; for mixed columns no, exact onset `(g − ½)ℓ`; curve columns certified at `(g − ½)log q`, sharp | WVL [L] |
| Is `λ = ½` a sign-hiding law? | only on an `e^{−δL}`-thin ℓ¹ ridge around exact off-line lattices; one defect collapses it | WVL [L] |
| Does the unconditional base aperture locate zeros? | no: its ζ instance is vacuous (`δa ≥ 2` impossible at `a < ½`) | WVL [L]; [D] |
| Does the explicit formula determine ζ's zeros locally? | at `λ > 1` up to near-collisions `< δ/log T`; isolated zeros and multiplicities at `λ > ½`; not at `λ ≤ 1` for disjoint carriers | ZCG [L] |
| What does the camera read inside a near-coincidence? | net multiplicity, centre `O(r²)`, squared gap `O(r³)`, loss `e^{C log²X}` | ZCG [L] |
| How far does size information reach on the heat path? | to `½/log(X/2π)` (saddle); proved `6600/9991`; pair models collide below every positive scale | ZCG [L] |
| Is domination ζ-specific? | no: every real finite carrier is real above its horizon | ZCG [L] |
| How far does Perron/Markov structure reach? | even band exactly to `log ρ`; full form Markov part to support `e^{−3/4}` | SWC [L] |
| What is the sign below `log 4`? | membership of `(Λ(2)/√2, Λ(3)/√3)` in an explicit compact convex set | SWC [L] |
| Must certificates keep the pole variance? | yes; retained ones exact below `log 4` | SWC [L] |
| Can the prime `3` be paid by its size? | no; soft entry covers `δ ≤ 0.12` only | SWC [L]; [D] |
| What is a sector? | a Hamburger / shifted Hamburger problem; the window a Stieltjes problem | SWC [L] |
| Are window extremals smooth? | never | SWC [L] |
| What is the terminal source? | polar; correctors cannot improve zero-source windows | AHD, CACT [L] |
| Can finite receiving charges be paid by energy bounds? | no: arbitrary charges survive vanishing physical energy | CSAR [L] |
| What is the PM defect? | `−∫2cosh(δu)4sinh²(δu)|F(u)F(−u)|`: its sign is `δ = 0` | RIT [L] |
| What does blindness cost? | `π` times the density | ZCG [L] |
| When is a fake caught? | exactly above aperture `½log n₀` | ZCG [L] |
| How does purity survive over `𝔽_q`? | closed, lost only at Frobenius collisions; collide or repel | ZCG [L] |
| Does positive dimension supply positivity? | no | ATD, DZG [L] |

## 2.3 Frankenstein routes

**Verdict: no assembly closes RH.** Every assembly ends at one named residual; the residuals are the
three core walls in exact form, and with identification complete they reduce to two readings of one sign
(the band in prime coordinates, the reflection in zero coordinates). F5, F6 and F10 sharpen what a closing
piece must be.

### F1. The gauge–tower assembly (P1)
| Segment | Supplied by | Status |
|---|---|---|
| RH ⇔ `a*(ζ) = ⊤` ⇔ windows ⇔ reflection pairs ⇔ sectors ⇔ moment problems | WVL, CWS, GWZ, SWC | [L] |
| Base through half-width `0.362`; first stage rejects `0` and the flip | SPATL, GWZ, SWC | [L] |
| Even sector Markov to `log ρ` | SWC | [L] |
| Pole kept; variance retained; exact certificate format below `log 4` | SWC | [L] |
| Sliver signature, outward edge, soft entry, weight confinement | SWC | [L] |
| Stage criterion; Levinson admission; continuum limit at the Schur boundary | GWZ, CSTW, SWC | [L] |
| Core: signed reflections pay the collar Hankel form in every stage, past the Perron range | — | B3; first instances B4, B5; method B49 |

### F2. The multiscale assembly with margin transport (P1 ⊕ P4)
Pay kicks inside their collar-certified range locally, carry each newest prime by soft entry, pay older primes
by window positivity at a smaller scale. Residual: margins decay doubly exponentially in the length; soft
entry covers slivers `δ ≤ 0.12` at margin `1`; the doubling step needs cross-correlation kernels at scale
`2a`, which by polarization is the band at scale `2a` (B1).

### F3. The complete-family assembly = the onset aperture
Subcritical PD + one critical multiple + threshold law + terminal source polar + simultaneous receiving [L].
By `R₁(A) = ⊤ ⇔ A/2 ≤ a*(ζ)` this assembly certifies exactly the windows the base theorem certifies.
Residual: B33 (`a*(ζ) > 0.362` from the complete family), then B7, then B1.

### F4. The reflection assembly (P3)
PM Krein–Lax–Phillips space + window involution + window lift + defect formula + retained channel [L].
Residual: B38. The retained channel is antisymmetric under reflection and reads the side only.

### F5. The camera–continuation assembly (Γ ⊕ P5)
| Segment | Supplied by | Status |
|---|---|---|
| Heat path real for `t ≥ 1/8`; RH ⇔ `Λ_X = 0` ∀X | RHTower | [L] |
| Size information: no collision for `t ≥ (6600/9991 + ε)/log X`; floor `½/log X` | ZCG | [L] |
| Reality lost only through collision; collisions are near-coincidences | ZCG | [L] |
| Camera: zeros of ζ identified up to near-coincidences `o(1/log T)`; inside them `w²` to `O(r³)·e^{C log²X}` | ZCG | [L] |
| Core: the sign of `w²` at every near-coincidence ≡ no collision on `(0, ½/log X]` | — | B44 = B14 (RH) |

Residual: one quantity. In the pair model every depth `≤ ½` collides below `½/log X` [D], and the camera's
second-order precision is quasi-polynomial (B48). Neither proved repulsion mechanism (integrality over `𝔽_q`;
phase speed above the carrier horizon) reaches ζ's scale. The assembly shows that P5 and the Γ-sign are one
problem: reality of near-coincident pairs, decided by the Euler product inside the strip.

### F6. The visibility–density assembly (WVL ⊕ WD ⊕ DCI ⊕ AKLT)
| Segment | Supplied by | Status |
|---|---|---|
| Positivity at `a` excludes unshielded coherent clusters to doubly-exponential height | WVL | [L] |
| Positivity at `a` bounds shallow coherent depth mass `Σm_qδ_q² ≲ A₀log T/a²` | WVL | [P] |
| Unconditional unit-window depth-mass bound `Σ(Im z)² ≤ 40σ²log(180|T|)`; `M₂⁺(V) = o(V)` | DCI, SRT | [L] |
| Off-line zeros occupy density-zero window sets; index rises with each | WD, AHD, CWS, AKLT | [L] |
| Shielded configurations (tapered crystals) | — | hide from every fixed aperture above single-exponential height [L] |

Residual: two inputs, both open: window positivity at growing aperture (B1) and exclusion of shielded
shallow crystals, which is a log-free near-line density statement (B21, B22). The assembly shows exactly
which zero configurations a window programme cannot reach without density input: shielded ones.

### F7. Height induction (contact law)
RH to height `T` ⇒ windows of length `c log T` positive ⇒ RH somewhat higher. The second arrow is proved:
the contact law is a power-saving zero-location bound [L]. The first arrow fails: configurations identical
below `exp((e^{2δa} − 2)/(4δ) − a)` have opposite window signs, so zeros below `T` decide windows only up to
half-width `≍ loglog T` [L/D]. Residual: a contact law is itself a zero-location theorem.

### F8. The moment-problem assembly (SWC ⊕ TH ⊕ LA)
Window ⇔ Stieltjes moments of jet energies for every even bump; theta Hankel towers PD through rank 8;
fixed Jensen degrees eventually hyperbolic [L]. Residual: a representing measure built from prime data
(zero-side positivity, Γ8). The finite unconditional ranks concern the theta source at one centre and do
not transfer to window bumps.

### F9. The Hermite–Biehler assembly (ZCG ⊕ census ⊕ canonical systems)
Every symmetric half with positive phase speed gives simple line zeros as a phase lattice; every finite real
carrier is Hermite–Biehler above its horizon; twins are tilted at every height [L]. Residual: a
Hermite–Biehler factor of ζ at its own scale, which must use cancellation of the prime sum below the horizon,
not its size (B20, B14).

### F10. Structural positivity at one fixed length + sharp visibility (P1 ⊕ WVL)
| Segment | Supplied by | Status |
|---|---|---|
| Positivity at half-width `a` ⇒ no unshielded coherent cluster of depth `δ` with `e^{2(δ−σ)a} ≳ Cδa log T` | WVL | [L] (constant `C ≈ 2²⁶·960`) |
| Constant sharpened to the model value | A35 | work |
| Verified zeros to height `≈ 3·10¹²` | numerical | [P] |
| Positivity at one fixed `a ≈ 5–10` | — | B3 at fixed length (sub); numerically impossible (margins `exp(−πe^{2(a−2)})`) |

Output if the open segment were supplied: an unconditional zero-free region for unshielded deep zeros
(`Re ρ ≥ ½ + (1/2a)log(Ca log T)`) on a doubly-exponential height range — a new finite-height zero-location
theorem, not RH. Residual: structural positivity at one fixed length well past `log 4` (B3, sub), which no
numerical method reaches.

## 2.4 A wildly different route

**Verdict: one far mechanism is visible; no route that avoids all three walls is.** Every route reads the
zeros through the explicit formula or through a function with the divisor of `ζ`; the three walls are the
three components of that formula. The corpus covers positivity, precision, realization, deformation,
recurrence, counts, function-field transfer, quasicrystals, Lee–Yang, moment problems, Hermite–Biehler
phases, visibility and identification. The research tool finds no finite free convolution, mixed
characteristic polynomial or interlacing-family machinery (interlacing appears only in its classical
Laguerre and secular-equation forms).

**Real-rootedness from finite free probability (interlacing families).** Marcus–Spielman–Srivastava: the
expected characteristic polynomial of a sum of independent random rank-one PSD matrices is real-rooted (real
stability, barrier arguments); finite free convolutions preserve real-rootedness (`⊞_d` always, `⊠_d` with one
factor of nonnegative roots); `E det(x − GUE_d)` is a Hermite polynomial. The Jensen polynomials `J^{d,n}` of
`Ξ` are real-rooted for all `d, n` iff RH, each fixed degree is eventually real-rooted [L: LA], and they
tend to Hermite polynomials [P: Griffin–Ono–Rolen–Zagier]. A route would realize every `J^{d,n}` as a
finite free convolution or mixed characteristic polynomial of real-rooted pieces built from Gamma and Euler
data.
- What is far: no quadratic form sign (Σ), no square-root count (Π), no reflection or Krein positivity (PM),
  no collision exclusion by size. Real zeros come from real stability, an algebraic property preserved by
  the operations. An expectation over a family is not a single finite object, so the finite-realization
  no-gos do not apply.
- Where it meets the walls: (i) criticality — the entire-function limit of `⊞` with a semicircle is the heat
  flow, and `H_t` is non-real for every `t < 0` [L], so a factorization of `Ξ` can carry no Gaussian
  component in the limit; (ii) the size obstruction does not bind it — the pair model shows size alone
  cannot exclude collisions below `½/log X`, and an interlacing family is not a size statement, but its
  pieces must carry the Euler product inside the strip; (iii) source faithfulness — pieces from primes and
  Gamma, not zeros (Γ5); (iv) the coefficients of `J^{d,n}` are moments of `Ξ`'s Fourier kernel, so a
  `⊞`-factorization is a nonlinear identity among those moments (C22).
- First test: degree `d = 3`: real-rooted `p, q` of degree `3`, built from explicit Gamma/prime data, with
  `J^{3,n} = p ⊞_3 q` for every `n` — or a proof that no semicircle-free factorization exists, which would
  close the mechanism.

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — the global canonical system of the tower
**Question.** Construct, from the explicit formula, the continuum canonical system of Weil's
translation-invariant kernel on `[0, L]`: Krein's reflection function `A(L)` (the continuous Schur
parameters) with its singular structure at the prime-power lengths `L = log n`, such that the window of
length `L` is positive iff the system has no blow-up on `[0, L]`; equivalently `2a*(ζ)` is the first blow-up
length.
- **Below RH.** An identity: it constructs the object whose regularity is RH; it decides no sign.
- **Why it is not settled.** Lattice Levinson recursion and the local continuum limit (jet Hankel system,
  reflection coefficients freezing at `(−1)^n`, parity blocks) are proved [L]; the global system with the
  kicks is not (B17); Krein's theory needs nondegenerate truncations, available up to the first failure.
- **Advance.** One object for the lattices, the jets, the sectors (parity blocks), PM's Krein structure and
  SZ's Krein–Schur carrier; every stage step becomes a local statement about `A(L)` across `L = log n`;
  the master visibility law `k·pairEnergy(δ,a) = L` becomes the blow-up law of the system as a function of
  the zeros, and the Perron threshold `log ρ` the first length where `A(L)` leaves the positive cone.

### 2.5.2 Route PM — a zero-free region owned by the Lewis–Hecke carrier
**Question.** From the three-term equation, modular inversion, the Hecke eigenrelations
`T_pψ_s = (1 + p^{1−2s})ψ_s` and the defect formula, prove an upper bound on `|D_s(ψ_s)|` relative to its
cross mass `∫u²|F(u)F(−u)|` that excludes resonances with `Re s > ½ − c/log|Im s|` (zeros `ρ = 2s` with
`Re ρ > 1 − 2c/log|γ|`).
- **Below RH.** de la Vallée Poussin strength.
- **Not ruled out because.** Every killed PM mechanism is a line selector; none concerns the size of the
  defect, which is `≈ −8δ²·(cross mass)` [D]. Risk: the cone counting behind `1 + p` is the Euler product
  (A15).
- **Advance.** The first sign-bearing statement PM owns; it would show that the Krein structure carries
  arithmetic beyond identification.

### 2.5.3 Route WD — log-free window occupancy
**Question.** Prove `D_win`: for every `A > 0` at most `ε(A)V` unit windows of `[V, 2V]` contain a zero of
depth `≥ A/log V`, `ε(A) → 0`; equivalently thin Planck shadows occupy `o_A(V)` windows [L: CDG].
- **Below RH.** A density statement.
- **Why it is not settled.** Selberg-type density counts `≍ e^{−cA}V log V` such zeros, a logarithm more than
  the `V` windows; the unconditional squared-depth moment `o(V)` loses `(log V)²` against it; counts and
  moments cannot give it (`#window-density-separation`).
- **Advance.** WD's analytic input at the log stage on almost all windows; with F6 it is exactly the input
  that excludes shielded shallow crystals, the configurations no fixed window sees.

### 2.5.4 Route HF — the first window beyond the base, from the complete family
**Question.** Prove `R₁(A) = ⊤` for one window length `A > 2·enlargedWeilFloorAperture` (≡ `a*(ζ) > 0.362`)
with the critical-curve machinery: a pencil `a_φQ(H) + (7J(1)/R)M₈(H)` positive on every window of that
length at every ratio, using prime input in the receiving complement (growing fibres, literal prime bands).
- **Below RH.** A finite window; no zero information (vacuity).
- **Why it matters.** Every HF layer proved is size-only and reaches exactly the base aperture; the terminal
  layer is polar and correctors cannot improve zero-source windows [L], so the only place left for
  arithmetic sign is the complement. An HF proof of one window beyond the base would be the first HF
  statement carrying the sign.
- **Not to be pursued.** Uniform floors along growing overlaps, bare counts through all conductors,
  low-block deletion, terminal correctors, energy-only control of receiving charges.

### 2.5.5 Route ZCG — second-order inversion at polynomial scales
**Question.** For ζ, read the squared gap `w²` of every near-coincident cluster of diameter
`≥ T^{−M}` from equal images at aperture `(1 + ε)·½log(T/2π)`: isolating windows whose floor is polynomial in
the isolation radius on ζ's own configuration.
- **Below RH.** Sign-free; a statement about the explicit formula's resolving power.
- **Why it is not settled.** The quasi-polynomial form is proved (`|μ_j| ≤ N r^{j+1}e^{C log²X} + tail`) [L];
  worst-case RvM-blind windows have super-polynomial floors, so a proof must use structure of ζ's
  configuration (local spacing statistics), not only its counts.
- **Advance.** Every near-coincidence of ζ above polynomial scale would be read by the primes to second
  order: B44 would become the sign of an explicit prime-side second-order quantity, heat collisions would
  have a prime-side detector, and double zeros an arithmetic detector at polynomial resolution.

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — exact collective payment
**Question.** On every reflection pair, write `W(f) − |𝒞_m(f)|` as a nonnegative signed Dirichlet form in a
gauge with retained pole variance plus nonnegative pole charges: a gauge family, exact on the line like the
theta gauges, whose restriction to every window pays the collar Hankel form by the signed sliver reflections
of all acting prime powers, in both sectors.
- **Why it opens the path.** It is B3, hence B1 and `a*(ζ) = ⊤`; the gauge calculus and the certificate format
  are exact [L], so only the domination is missing.
- **Constraints.** Signed (Perron dies at `log ρ`); variance mandatory; Markov dead past `e^{−3/4}`; collar
  locality sharp; soft entry a sliver mechanism; beyond `log 5` the payment is collective (P4); extremals
  edge-singular; margins `~10⁻⁸`; FE and Euler product both enter.

### 2.6.2 Route PM — a second expression of the defect
**Question.** At every resonance, express `D_s(ψ_s)` arithmetically — through finite cusp energy, Hecke norms
or a resonance identity — as a manifestly nonnegative quantity.
- **Why it opens the path.** The analytic expression is `≤ 0` with equality only at `δ = 0` [L]; a second
  expression `≥ 0` forces `Re ρ = ½` for every zero. Arithmetic enters through `core_s(2) ≠ 0`; a channel with a
  reflection-symmetric sign law is the needed input.

### 2.6.3 Route WD — inner-cap cancellation
**Question.** On every Burnol unit window, at every polynomial stage, cancel the right-port flux through the
inner caps `[½, σ_m]` by a source identity.
- **Why it opens the path.** Across all degrees it is RH; at fixed degree the corridor
  `|β − ½| ≤ C/|γ|^k` [L]; it is the zero-free region pushed to the line.

### 2.6.4 Route HF — transport of the threshold across prime entries
**Question.** Prove that `R₁(A) = ⊤` propagates from `A` to `A + log p` across each prime-power entry: a
stage-transport law for the complete family, with the receiving complement paid at the entering conductor.
- **Why it opens the path.** `R₁` is antitone and `= ⊤` up to the base; transport across every entry is
  `R₁ ≡ ⊤ ≡ a*(ζ) = ⊤`, RH. It is B2 in HF's language, where the critical-curve decomposition separates each
  entering prime into twisted (positive) and untwisted (pole) directions [L].

### 2.6.5 Route ZCG — reality at near-coincidences
**Question.** Prove that every near-coincident cluster of ζ is a real pair (`w² ≥ 0`), by an arithmetic
second-order sign read through `(log n)²`-weighted primes; equivalently, exclude every collision of `H_t`
in `(0, ½/log X]` using the Euler product inside the strip.
- **Why it opens the path.** It is RH [L]. ZCG supplies everything sign-free: identification up to
  near-coincidences, the second-order reading of `w²`, the exact collision criterion
  `Re Q(0) = Im Q′(0) = 0`, and two repulsion templates (integrality over `𝔽_q`; phase speed above the
  carrier horizon). The missing input is a third template where the prime weight is unbounded and size is
  powerless (`pairModel`).

## 2.7 Does closing RH need a new field?

**Assessment: yes — an arithmetic criticality theory: signed positivity, at exact criticality, of
frustrated nonlocal Dirichlet forms with arithmetic jumps on intervals, decided at the boundary and sensitive
to the Euler product inside the critical strip.** Its dictionary exists in the corpus (SWC, ACT, GWZ, CSTW,
WTZ, DZG, WVL, ZCG); its core is open; the corpus fixes what the core cannot be.

*What it is about.* Translation-invariant quadratic forms on the line whose symbol is known only through
the dual side (the primes), restricted to intervals of every length: a logarithmic-order archimedean jump
form, arithmetic jumps of length `log n` with rates `w_n`, a renormalized potential, a rank-two pole term and
the infinite-rank trivial-zero Hankel correction. Positivity on every interval, at exact criticality, with
frustration carried by the pole (even sector) and by anti-diagonal conductances (odd sector), and payment
carried by reflection signatures.

*What it would be like.* Exact (identities at the boundary); signed (non-Perron past `log ρ`; ground states
with a forced sign change between edge and centre); multiscale (local kicks, soft entry, collective count);
critical (no spectral gap; margins doubly exponentially small); boundary (extremals in the energy
completion, singular at the window edge); moment-theoretic (sectors are Hamburger/Stieltjes problems);
Krein-flavoured (the pole one negative square in the odd sector; off-line resonances of Krein square `−2`);
quantitatively sharp in its output (every theorem a lower bound for `a*(ζ)`, converted to zero location by
the master law `k·pairEnergy(δ,a) = L`).

*Criteria it must meet.*
1. Reproduce the base `0.362`, the plastic threshold `log ρ`, the first stages and their margins `~10⁻⁵–10⁻⁸`.
2. Pay the pole's negative square in the odd sector and the cosh deficit in the even sector, variance retained.
3. Be critical: margins tend to zero along every lattice; reflection coefficients freeze at `±1`.
4. Deliver the band on every reflection pair (two sites decide).
5. Pay the primes `3 ≤ p ≤ 73` by sign from their entry, and every other prime power once it leaves its
   collar-certified range.
6. Cross `log 5`, where the summed edge-law bound exceeds the Lévy energy and payment becomes collective.
7. Distinguish ζ from every finite real Dirichlet carrier (real above its horizon), from Lindelöf-bounded
   Riemann-density pair models (which collide at every time scale), from Euler twins (tilted at every
   height), flips, Beurling systems, `ζ(s)ζ(s−ε)`, Davenport–Heilbronn and Epstein data: size, density,
   domination and identification are not enough.
8. Use the functional equation and the Euler product together, the Euler product inside the strip.
9. Explain the square-root threshold `λ = ½` as the aperture where the camera reads ζ's isolated zeros, and
   why sign-hiding at `λ = ½` survives only on an `e^{−δL}`-thin crystalline ridge.

*Questions it must answer.*
- Is the arithmetic part of Weil's form an optimal Hardy weight for the archimedean logarithmic jump operator
  with the pole kept?
- What replaces Perron–Frobenius past `log ρ`: which nodal structure do window ground states have, and is it
  stable across prime entries?
- Which gauge family, exact on the line, restricts to every window with a nonnegative remainder in both
  sectors?
- What is the collective law: how do the sliver signatures of all acting prime powers pair with the pole
  square on a reflection pair, uniformly in the stage?
- What is the trace theory of critical window extremals, and which boundary data does a certificate see?
- How are margins transported across prime entries, and what replaces soft entry beyond the sliver?
- What is the global canonical system, and does its positivity propagate stage by stage?
- How does the Euler product inside the strip act as a repulsion law at near-coincidences?

*Tools.* Criticality theory and optimal Hardy weights for nonlocal operators; signed-graph theory
(switching, frustration index, Kron reduction); Krein and Pontryagin spaces; Krein strings, de Branges spaces,
Szegő–Levinson theory; Hamburger/Stieltjes moment theory; Beurling–Malliavin completeness radii; Doob
transforms; exactness by homogeneity; the corpus's pole-charged representation, sliver signature,
outward-edge calculus, onset-aperture calculus and camera.

*Objects and language.* Gauges, theta gauges, charge variances, outside charges, slivers and their
signatures, outward-edge ratios, Lévy margins, sector weight sets, the collar Hankel form, Schur parameters at
the disk boundary, jet Hankel matrices and their representing measures, the onset aperture, pair energies,
shielding collars, near-coincidence moments.

*Mechanisms it aims to discover.* An exact collective identity (pole square against the signed reflections)
on reflection pairs; a renormalization from scale `a` to `2a` that keeps the cross-correlation; a
criticality-preserving signed gauge flow; a margin transport law across entries; a repulsion law at
near-coincidences driven by the Euler product in the strip.

*Explicitly outside the field.* Counts and Hodge index; Tate domination; Markov and Perron ground states past
their thresholds; variance-free, size-only, sign-blind and finite certificates; PM operator symmetry off
`Re s = ¼`; size-only floors; size-only heat repair; identification without sign.

## 2.8 The one question

**Is `a*(ζ) ≥ log 2` — the window of every length below `log 4` positive — by one exact signed mechanism in
which the prime `3` is paid by the sign of its sliver reflection and the pole variance is retained?**

Equivalently, by proved equivalences [L]: the arithmetic point `(Λ(2)/√2, Λ(3)/√3)` lies in
`belowLogFourBandWeights c` for every `c < log 2`; a retained-variance certificate exists in every positive
even theta gauge (even sector) and in every shifted ground state (odd sector); the scaling subsurface
satisfies the Hodge index; Künneth effectivity holds; `R₁(A) = ⊤` for every `A < 2log 2`.

*What the window contains.* The primes `2` and `3` and nothing else; the Markov part is dead (`e^{−3/4}`),
the even sector is not Perron (`log ρ`), variance-free certificates are dead (`273/400`), the prime `3` is not
paid by its collar (`287/500`) and is indispensable (`3/5`), soft entry covers only the first sliver (`0.61`),
`w₂ ≤ 0` and the flip are inadmissible (`21/40`); margins `1.5×10⁻⁵` (odd) and `5.6×10⁻⁸` (even) at
`c = ½log 3` [L/N].

*Why it is less hard than RH or quasi-RH.* A finite window, two numbers, an exact certificate format, a
compact convex admissible set; it implies no statement about zeros (its ζ visibility output is vacuous) and
is numerically true.

*Why it pushes the door open.* It is the smallest window where every structural feature of the stage step
is present at once — signed ground states past the Perron threshold, pole frustration in the even sector,
kick frustration in the odd sector, a prime paid by sign, retained variance — and the only window where the
whole equivalence web (HF threshold, ACS Hodge index, LST Künneth effectivity, SWC band, RW/OWU/EWU/ACT/TT
sectors) is proved in Lean. Nine routes share it as their first open instance (B5). A structural answer is
the template of B2 and B3 with the exact form every later stage must carry; it also answers B49 at its first
instance (the nodal structure past `log ρ`). A proof that no mechanism of this class exists names the term
the next certificate must retain.

*Precise boundary.* Excluded: Markov and Perron certificates, folded supersolutions, variance-free gauges,
collar-local payment, size-only payment of the prime `3`, soft entry alone, lossless lower forms,
finite-square identities, cost-only payments, smooth extremals. Not excluded: retained-variance theta gauges
and shifted ground states, pole-charged supersolutions with non-compact gauges, variable-hub Schur
elimination, packed nonlocal paths, signed Doob gauges with a fixed nodal set, and any exact identity that uses
the trivial-zero Hankel squares and the sliver signatures.

*Why this question and not another.* The global canonical system (2.5.1) is an identity and decides no sign;
the PM second formula (B38), collision exclusion (B14) and reality at near-coincidences (B44) are RH-strength;
the window visibility question is answered in models; polynomial-scale inversion (B48) serves ZCG and LA only;
finite free factorization (2.4) opens one new route. The two-weight question is sub-RH, finite, shared by
nine routes, and isolates the sign mechanism in pure form.
