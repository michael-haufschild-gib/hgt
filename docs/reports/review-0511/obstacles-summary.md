# Obstacles summary — status quo

Companion to `route-obstacles.md` (per route; labels `A*`, `B*`, `S*`, mechanism classes P1–P5),
`walls-ledger.md` (Σ/Π/Γ) and `route-unification-ledger.md` (classes C1–C30). Corpus state: `bdfa1ea5be`
plus working tree. Evidence: `[L]` committed Lean; `[W]` working-tree Lean; `[P]` pipeline-card paper proof;
`[D]` derived here from Lean statements; `[N]` numerical. Windows `[−c, c]` or half-windows `[−c, 0]`;
`w_n = Λ(n)n^{−1/2}`; `H` the archimedean–polar form (prime weights `0`), `P` the arithmetic part, `W = H − P`;
`𝒥` the Lévy energy; `𝒞_m(f) = 𝓗_m(f) − Σ_n w_n(f⋆f)(2m − log n)`; `a*(ζ)` the onset aperture;
`ℋ(c) = {t : H − tP ≥ 0 on [−c, c]}` the arithmetic Hardy interval; `L_T = ½log(T/2π)`;
`a₁ = successorWeilFloorAperture ∈ (0.362, 0.3621)`; `log ρ ≈ 0.2812` (plastic number).

## 1. The big picture

### 1.1 One sign, one number, one inequality
RH ⇔ `a*(ζ) = ⊤` ⇔ `1 ∈ ℋ(c)` for every `c` [L: WVL, FADF]. Weil positivity is a **critical Hardy
inequality**: the arithmetic part `P` must be a Hardy term for the archimedean logarithmic jump operator with
the pole kept, `H ≥ P` on every window. Two halves of "optimal Hardy term" hold unconditionally: the multiple `1`
is the only multiple admissible on every window (scaling optimality, by uniqueness of the Weil cone), and no
Hardy weight survives on odd tests (criticality) [L]. The third half — admissibility on every window — is RH.
`ℋ(c)` is a closed interval, the whole line before the first prime, bounded after it [L]. Known:
`a*(ζ) ≥ a₁`, with `a₁ − 181/500` positive and below `5×10⁻⁷` [L].

### 1.2 The certificate format is exact on every window
On every reflection pair `W(f) − |𝒞_m(f)| = ½min(W(G₊), W(G₋))`, the coupling truncating to `2 ≤ n ≤ e^{2c}`
[L: SWC]. The even sector is represented exactly by a window-adapted, line-exact signed theta gauge with zero
pole charge (`2V ≤ J_{M⁺}`), the odd sector by a shifted ground state; nonnegativity of both on every window ⇔ RH
[L]. A window-independent nonsingular even gauge cannot carry nonnegative pole charge [L]. What is open is the
inequality the format states, not the format.

### 1.3 Frustration cannot be switched away
The even kernel `ω(|u−v|) + ω(−u−v) − 4cosh(u/2)cosh(v/2)` is Markov exactly for `c ≤ log ρ`; past it the even
band fails Beurling–Deny at every pole strength and all weights, and is frustrated in every sign gauge [L: SWC,
FADF]. The odd light cone is positive, and each acting prime power adds an anti-diagonal frustrated in every sign
gauge, from `½log 2` on [L]. The logarithmic diagonal forbids cheap nodes: every node of a sign gauge creates a
negative switched conductance next to it [L]. Robust Perron in the pole strength costs height; the arithmetic
pole sits within `O(λ₀)` of the positivity threshold [L]. The trivial zeros are not part of the frustration: they
are mirror mass minus reflected (even) or antireflected (odd) energy, paid by centre killing [L]. What remains to
pay: the constant potential, the pole square (odd), the prime reflections (both).

### 1.4 Size payment is finite; beyond it only sign
The summed edge law `|P_μ(f)| ≤ E_c(μ)𝒥(f)` certifies by size until `E_c = 1`; for ζ the unique crossing is
`c* ∈ (½log 5, ½log 6]` [L]. Size dies earlier: `H` itself is negative on a window of half-width `≤ 21/40` (the
weight `w₂ = 0` is inadmissible there), and beyond a finite window one real test makes the prime part strictly
negative for the whole calibration space [L]. Each entering weight is confined two-sidedly with sharp logarithmic
constants (outer `1`, inner `η/2`), and beyond the sliver both bounds are bounded [L]. The primes pay by sign.

### 1.5 Finite matrices end before `log 6`
Positivity of any correlation form on a window is positivity of all finite rational Hecke graphs of smaller
log-spread [L: WTZ]; finite templates control spreads whose Hecke orbits are finite; at spread `6` the
×2/÷3 orbit in `[1,6)` is infinite, so no finite template exists there [L]. Exact Tate horizons are computed
through `log(81/16)`; positive Tate dimensions form `[0, κ(A)]` with `κ(A) → 0` [L]. The interval
`(log 5, log 6]` is where both the edge-law and the finite-template structure end [D].

### 1.6 The window tower is a de Branges chain until contact
Before contact every window carries a complete Weil Hilbert space realized by entire functions, a de Branges
space with an explicit Hermite–Biehler function, unitary zero-moving, antiunitary conjugation and isometric
inclusions; the Weil symbol is `1 + ½log(1 + ξ²)` minus a bounded convolution, and evaluation vectors are bounded
solutions of a logarithmic Dirichlet equation [L: CSTW]. Either RH, or at `a*` a fixed evaluation kernel
diverges monotonically while the contact window stays positive [L]. RH ⇔ the chain never reaches contact [D].
The Hamiltonian of the chain is not constructed.

### 1.7 Identification is complete; reality is the sign of a prime-side ratio
At aperture `λL_T`: `λ > 1` fixes RvM configurations up to near-collisions, `λ > ½` reads every isolated zero of
ζ with its multiplicity [L: ZCG]. Inside isolated clusters of radius `r ≤ T^{−(M'+κ_λ+1)}` the camera reads the
moments to `N r^{j+1}T^{M'+κ_λ} + e^{−K'log³T}`: centres, squared gaps, discriminants and point locations of
every polynomially small isolated cluster, from finitely many prime-side window images [L]. For a two-point
cluster `𝓗 = 4(W₁² − W₀W₂)/W₀²` equals the squared gap up to `O(r³P) + O(E)`; on-line pairs give `𝓗 ≈ Δ² ≥ 0`,
FE pairs `𝓗 ≈ −4δ² < 0` [L]. FE-pair squared gaps `≥ 0` at every zero ⇔ RH [L]. Unresolved: clusters of diameter
below `e^{−c log³T}`.

### 1.8 Continuation and finite free stability meet the same floor
`Λ_X ≤ (6600/9991 + ε)/log X`; the Gaussian saddle enters `Re s > 1` exactly at `½/log(X/2π)`; pair models with
Lindelöf size collide below every positive scale [L]. In finite free form: `e^{(t/d²)D²}J_d` is not real-rooted
for any `t > 0` (unboundedly many non-real roots, robust to Bernoulli shifts), while in the shift regime the
Jensen polynomials are asymptotically semicircular [L: FFP]. Normalized Euler factors are Hermite–Biehler stable
with forced drift `θ_S/2`; the ζ side, the Gamma side and pole pieces are unstable for every phase; the
source-faithful Γ ⊠ Θ split never certifies (Θ never real-rooted) [L]. RH ⇔ Möbius-mollified Jensen polynomials
stable at infinitely many degrees, a receiver whose converse does not use the mollifier [L/D].

### 1.9 Every route is a face of the same sign
Exact identifications [L]: the reflection-pair prime-count band ⇔ Weil-lag ⇔ JAS ⇔ CTF ⇔ PBM ⇔ eventual Robin
(SWC); Suzuki first variation = complete Weil energy (SZ); the Cayley ladder = Toeplitz ladder of paired Li
coefficients, RH ⇔ every ladder NSD on primitive vectors ⇔ entrywise `≥ 0`, Hodge index = Metzler sign (ALG
[W]); inner-cap flux = off-line generating function (WD); single-prime stage transport ⇔ RH (HF); two real
parameters `(γ, v)` decide the line (SRT); any nonnegative representation of the Mayer defect ⇔ RH (PM).

### 1.10 PM's second expression has the same sign
`−D_s(ψ_s) = |1 + p^{1−2s}|^{−2}∫_1^∞K_σ|T_{p,s}ψ_s|² = ∫_0^∞K_σ(x+1)|ψ_s(x) − (x+1)^{−2s}ψ_s(x/(x+1))|²`,
`K_σ ∝ (b^{2σ−½} − b^{−(2σ−½)})²`, `K_{1/4} ≡ 0` [L: RIT]. Infinitely many resonances lie on `Re s = ¼`, where
`D = 0` while every norm is positive: no positive multiple of a norm equals `D` [L]. PM's sign is `σ = ¼` in two
coordinate systems.

### 1.11 Visibility and the vacuity of short windows
`k·pairEnergy(δ,a) ≤ L` in lattice backgrounds, also for distinct clusters near one ordinate; unshielded clusters
excluded to doubly-exponential height; tapered crystals hide depth `1/a` above `e^{ca}`; doubly-exponential
non-locality [L: WVL]. For ζ the laws require positivity, known only to `a₁ ≈ 0.362`, where they are vacuous;
zero information starts at half-width `4` and, with present constants, `≈ 20` [D].

### 1.12 Criticality everywhere
Every exact reading sits on a zero-slack boundary: Weil cone a point; only the multiple `1` admissible; no Hardy
weight; lattices Szegő singular; reflection coefficients at `±1`; Perron exactly to `log ρ`; kernel blow-up at
contact; heat size horizon at the saddle; Gaussian finite free capacity `o(d⁻²)`; Euler drift exactly `θ_S/2`; PM
defect zero only at `σ = ¼`; numerical margins `10⁻⁴`–`10⁻⁸` [L/N]. A proof must be an identity at the boundary
[D].

### 1.13 What is ruled out
| Mechanism | Verdict | Anchor |
|---|---|---|
| Markov / Perron certificates past `e^{−3/4}` / `log ρ` | refuted at every pole strength and weight | SWC [L] |
| Balancing by sign gauges (switching) | refuted: even past `log ρ`, odd from `½log 2` | FADF [L] |
| Size-only payment of the primes | dies before `21/40` (`H < 0`); edge law at `c* ∈ (½log5, ½log6]` | FADF, SWC [L] |
| Certificates without pole variance; window-independent even gauges | refuted | SWC [L] |
| Point-value certificates | Weil's form reads no point values | FADF [L] |
| Uncoupled stage loans; twisted repair of untwisted modes | refuted at `21/20`; refuted above an explicit critical multiple | AHD [L] |
| Finite-template reduction at spread 6 | infinite Hecke orbit | WTZ [L] |
| Source-faithful finite free split; Dirichlet, ζ-side, Gamma, pole pieces | never real-rooted / unstable | FFP [L] |
| Degree-3 semicircle-free test | every real-rooted cubic passes | FFP [L] |
| Nonnegative multiple of PM norms as the defect | refuted on critical resonances | RIT [L] |
| Counts / Tate / Hodge index from counts | closed [D] | S3 |
| Height-local decision; universal density thresholds; domination as selector; size-only heat repair | refuted | WVL, ZCG [L] |
| Fixed / untruncated quartic theta cross-loads | fail at scales 8, 32 | TCS [L] |

### 1.14 The live mechanism classes
| Class | Statement | First open test | Status |
|---|---|---|---|
| P1 signed criticality | `H ≥ P` on every window in the exact two-sector format, frustration unswitchable | `a*(ζ) ≥ ½` (odd unit window, margin `≈ 2×10⁻⁴`); `a*(ζ) ≥ log 2` (two weights) | live |
| P2 calibration | the arithmetic point inside every finite-level cone `𝒜(c)` | widths of `𝒜(c)` for `c ≤ ½log 6` | live |
| P3 PM reflection | a nonnegative expression of the defect without the `(b^{2σ−½} − b^{−(2σ−½)})²` factor | a PM-native zero-free region | reduced to `σ = ¼` |
| P4 square-root cancellation | the band in prime form; Li positivity; inner caps | — | live; classical |
| P5 continuation / stability | no collision below `½/log X`; finite free stability at infinitely many degrees | an Euler-product input inside the strip | live as a receiver |

## 2.1 Obstacles that are just work

| # | Task | Routes served | Why it is work |
|---|---|---|---|
| A1 | Explicit constants and horizons (`K₀`, eighth-root theorem, `1/9`, logarithmic profile, Beurling schedule, `M(N) = o(c_N)`) | HF, SRT, AIP, ACS, SC | effectivization of proved limits |
| A2 | General profiles past `θ = 1/1080` | HF, SRT, SC | tilted-spline template |
| A3 | Joint twist families; equal-parity characters; different moduli | HF, SRT, AHD | single-family proofs are templates |
| A4 | Certified ratio interval at its size-only optimum; receiving complement inside it | HF, AIP, SRT, CSAR | assembly of proved estimates (difficulty unverified) |
| A5 | Rigorous computer-assisted certificate of the two-weight membership on `(0.3621, log 2)`, odd unit window first | RW, OWU, EWU, ACT, SWC, HF | operator inequality with explicit kernels; margins `2×10⁻⁴` (odd unit), `1.5×10⁻⁵`, `5.6×10⁻⁸` [N]; decides cases, not the mechanism; no zero information |
| A6 | Exact Tate horizons of the remaining stages below spread `6` | WTZ, CWS | finite templates exist there |
| A7 | Closed form of the first-stage complement `Φ_ε` | GWZ, CSTW, WTZ, RW | explicit Schur complement |
| A9 | Literal channel norms critically small with growing periods, offsets, prime bands | AIP | proved sieve inputs (difficulty unverified) |
| A11 | Function-field calibration of the remaining receivers (ladders, Hardy intervals, de Branges chains of curves) | AHD, ACS, SC, HF | the sign is known there |
| A13 | Widths of the finite-level cones `𝒜(c)` | PBAP, ACS, RW, FADF | convex finite programs; entry bounds proved [N] |
| A14 | PM classical identifications; mixed-parameter completion; Mayer transfer compatibility; boundary carrier; rational Weyl identification | PM, W1C | known theories |
| A15 | Operator-native nonvanishing on `Re w = 1` | PM | Eisenstein template (risk: reduces to the Euler product) |
| A17 | Theta fifth even section on `π ≤ q < 7` with an entry-preserving compensation; then rank 9 | TH | compact finite-dimensional sign with exact capacities (difficulty unverified) |
| A18 | Hausdorff shifts, Jensen horizons, two-grid degrees, PF beyond 37 | PA, LA, HCF | effectivization |
| A19 | Certificates on the nine anti-diagonals `{2,3,4,5,7,8,9,11,13}` where the pole pays nowhere | ACT | finite case analysis |
| A20 | Mixed Schur debit; first-prime/coarse/polar costs | AIP, CHMD | fixed-dimensional estimates |
| A21 | Logarithmic two-point Chowla | MC | Tao's theorem |
| A23 | Depth law, star horizons, gcd strata | HF, ACS | effectivization |
| A24 | Census items; Voronoi; Zwegers | census, ACS, HF | classical |
| A25 | Künneth primitive `h¹` at small degree; mixed jets | ACS, WL | calibration |
| A27 | Cluster-detector constant | SRT, WD | constants |
| A28 | Atomic-lattice bound `λ_max ≤ ½log N` | WTZ, HF | classical |
| A31 | Selberg-class degree-one classification | ACS, SEL | known theorem |
| A33 | Lévy sector margins at `c = ½log 3` | RW, OWU, EWU, SWC | numerical |
| A35 | Sharpen the general RvM coherent-cluster constants toward `4δL/k` | WVL, every P1 route | explicit test functions in place |
| A36 | Remaining onset-law items (general shallow depth-mass bound under positivity; tapered crystal to `a ≍ log T`; interferometer) | WVL | paper items |
| A37 | Simultaneous receiving with growing mode sets and growing `M` | AIP, HF, CSAR | fixed finite case proved (difficulty unverified) |
| A38 | Sub-Weyl strip profile from the best exponent pairs (horizon toward `½`) | LA, ZCG | known subconvexity; decides nothing about zeros |
| A39 | Krein extension for Weil's distribution on intervals (positivity at `a` ⇔ a positive measure on ℝ with the same image) and discrete mimics from de Branges sampling in the CSTW chain | RW, ZCG, WVL | classical Krein / de Branges theory on a corpus-built chain |
| A40 | Camera with real weights and Beurling–Selberg transfer of local counts to mimics | ZCG, SRT | the moment readout is linear in the weights |
| A41 | Hamiltonian of the precontact de Branges chain (de Branges ordering theorem), contact as its first singular length | RW, CSTW, SZ | classical theorem applied to a constructed chain |
| A42 | Effective `T₀` in the camera theorems | ZCG | constants |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window (≡ `1 ∈ ℋ(c)` ∀c ≡ band on reflection pairs ≡ growth steps contractions ≡ Li positivity ≡ Suzuki first variation ≡ two-parameter two-bump family) | RH; fixed length sub | all sign routes |
| B2 | Kick admission at every stage (≡ single-prime stage transport) | RH as induction; each stage sub | RW, GWZ, CSTW, WTZ, HF |
| B3 | The two-sector signed certificate inequalities on every window (`2V ≤ J_{M⁺}`; odd shifted-ground-state form) | RH; fixed length sub | P1 routes |
| B4 | Odd unit window (`w₂ ∈ unitBandWeights`) by a structural certificate | sub | OWU, RW, TT, SWC |
| B5 | Below `log 4` (`a*(ζ) ≥ log 2`), the prime `3` paid by sign | sub | RW, OWU, EWU, ACT, TT, SWC, HF, ACS |
| B6 | Twisted-sector positivity through all conductors and frequencies | sub | HF, SRT, AIP, AHD |
| B7 | Full-space sign at critical ratios beyond the size-only threshold | sub per ratio; RH all | HF, SRT, AIP, CSAR |
| B8 | General profiles past `log log N` on the full space | sub | HF, SRT, AIP, SC |
| B9 | Exact SOS on one two-prime lattice | RH | HF, SC, ACS |
| B10 | No zero mode at any length | RH | HF, TG, SC, EHT, GWZ |
| B11 | Top coprime stratum | RH | HF, ACS, ADT |
| B12 | Index ceiling uniform in resolution | ≥qRH; RH (tensor) | CHMD, SRT, WD, SC |
| B13 | Zero–one law `κ ∈ {0, ∞}` | sub | SC, HF, ACS, CWS, SRT |
| B14 | Collision exclusion below `½/log X` (≡ `Λ_X = 0` ∀X) | RH | TH, LA, HCF, PA, GTA, XN, ZCG |
| B15 | Scheduled prime energies bounded below (FU, CFC, RP, EGC, FEL) | RH | FU, CFC, RP, EGC, FEL |
| B16 | Window negativity exponent `< ½` | ≥qRH | window routes, HF, WD |
| B33 | HF-native sign: a window beyond the base certified by the complete family itself | sub | HF |
| B49 | Signed ground-state structure past `log ρ` compatible with unswitchable frustration | method | EWU, OWU, RW, ACT, SWC, FADF |
| B51 | No finite contact of the Weil de Branges chain (≡ regular Hamiltonian at every length) | RH | RW, CSTW, SZ |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B19 | Inner caps at every polynomial stage (≡ the off-line generating function is `L²(e^{−xt})` at every stage) | RH; fixed degree ≥qRH | WD, TG |
| B20 | `100%` critical-scale clustering | sub | WD, census, MC, HEF |
| B21 | `D_win` ≡ thin Planck shadows; `D_zero` | sub | WD, census |
| B22 | Hecke defect pointwise / dyadic | ≥qRH / RH | WD |
| B23 | Distributional input beyond counts and moments | method | WD, HEF |
| B24 | Genus upper law | indep. | ACS |
| B25 | Logarithmic Serre duality, primitive part | sub | ACS, HF |
| B26 | `ε`-uniform producer; square-root source input | sub / RH | WL, MC, PBM, RB, JAS, CTF |
| B27 | First cyclotomic mode at square-root precision | RH | MC, WL |
| B28 | Signed pair information beyond bandwidth one | sub | census, ACS |
| B29 | First Epstein real zero on the boost line | sub | ACS |
| B30 | Bounded damped cone coupling; unattained width | RH | SC, ACS |
| B31 | Finite-sieve Hodge positivity → global | RH | SC |
| B32 | Half-power law at the trivial gauge point | RH | MC, WL |
| B52 | Möbius-mollified Jensen stability at infinitely many degrees | RH | LA, FFP |
| B53 | A source-faithful stable finite free factorization of `J^{d,n}` other than Γ ⊠ Θ | method | FFP, TH |

### Γ — selection and reflection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B34 | Rosati positivity of the window reflection | RH | HF, ACS, CWS, GWZ, PM |
| B35 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH | HF, ACS, SC, PM |
| B36 | Selection at the trivial gauge point | RH | MC, BAG |
| B37 | FE twins inside the full class with off-line zeros | sub | HF, ACS, SC, SEL |
| B38 | A nonnegative expression of `D_s(ψ_s)` without the factor `(b^{2σ−½} − b^{−(2σ−½)})²` | RH | PM, W1C |
| B39 | Resonant-state statistic selecting the decay rate | method | PM |
| B40 | Source-faithful realization of unbounded rank | RH | RN, PTR, W1C, PM |
| B41 | Pre-divisor forcing | RH | APF, BSH, CDC, EWJ, HJ, PCS, RFHM, SEC, WBF |
| B42 | Prime-blind positivity on signed blind combinations | RH | PBAP |
| B44 | `𝓗 ≥ 0` on every isolated near-coincident cluster of ζ (the sign of an explicit prime-side ratio) | RH | ZCG, LA |
| B45 | Cross-tower gap through the archimedean channel | method | HF, AIP |
| B46 | PM-native zero-free region for `ζ(2s)` | sub | PM |
| B54 | Repulsion of distinct zeros of ζ at polynomial scale (collide or repel) | sub | ZCG, LA |

### Settled questions (status-quo answers)
| Question | Answer | Anchor |
|---|---|---|
| Is Weil positivity a Hardy inequality? | yes: `H ≥ P` on every window; only the multiple `1` admissible; critical; optimal ⇔ RH | FADF [L] |
| Can frustration be switched away? | no: even past `log ρ`, odd from `½log 2`, every gauge | FADF [L] |
| Where does size payment end? | before half-width `21/40` (`H < 0`); edge law at `c* ∈ (½log5, ½log6]` | FADF, SWC [L] |
| Is the certificate format exact on every window? | yes: neutral signed theta gauge (even), shifted ground state (odd) | SWC [L] |
| What do the trivial zeros cost? | nothing: centre killing pays them mode by mode | FADF [L] |
| What boundary data can a certificate see? | `Ω`-weighted edge masses; no point values | FADF [L] |
| Is the window tower a canonical system? | a de Branges chain before contact; kernel blow-up at contact | CSTW [L] |
| Does window positivity reduce to finite matrices? | for correlation forms yes, via rational Hecke graphs; finite templates end at spread 6 | WTZ [L] |
| Can the camera read squared gaps at polynomial scale? | yes, from three prime-side images, error `O(r³T^{M'+κ}) + e^{−c log³T}` | ZCG [L] |
| Is reality at near-coincidences RH? | yes: FE-pair squared gaps `≥ 0` ⇔ RH | ZCG [L] |
| Does finite free probability certify Jensen polynomials? | no source-faithful split certifies; Gaussian capacity `o(d⁻²)`; Euler side stable, ζ/Gamma/pole unstable | FFP [L] |
| Does PM's second expression change the sign? | no: same `(b^{2σ−½} − b^{−(2σ−½)})²` factor | RIT [L] |
| What is WD's inner cap? | the generating function of the off-line zeros | CDG [L] |
| Are SZ and LI independent of Weil positivity? | no: Suzuki first variation = Weil energy; Cayley ladder = Li coefficients | RHTower, ALG [L/W] |
| Does HF transport one prime? | single-prime transport for all `A` ⇔ RH; unconditional across `p = 2` at `A₀` | AHD [L] |

## 2.3 Frankenstein routes

**Verdict: no assembly closes RH.** Every assembly ends at the same sign, read in one of its coordinate systems
(Hardy inequality, prime count, squared gap, Krein form, Hamiltonian regularity). Two assemblies are productive
below RH: F6 converts window positivity into complete zero location at the square-root aperture, and F7 turns the
global sign into a scalar monotone quantity.

### F1. The gauge–tower assembly (P1)
| Segment | Supplied by | Status |
|---|---|---|
| RH ⇔ `1 ∈ ℋ(c)` ∀c ⇔ reflection pairs ⇔ two sectors | WVL, FADF, SWC | [L] |
| Exact two-sector format on every window | SWC | [L] |
| Base to `a₁`; floor `1/8000` on reflection pairs to `enlarged` | AIP, SWC | [L] |
| Perron to `log ρ`; trivial zeros at the centre; entry law | SWC, FADF | [L] |
| Core: `2V ≤ J_{M⁺}` and the odd ground-state inequality on every window | — | B3; first instances B4, B5 |

### F2. Hardy induction (FADF ⊕ AHD ⊕ CSTW)
`1 ∈ ℋ(c)` is antitone; composite stages carry no fold; each prime-power entry is a compact interval in the newest
weight with sharp logarithmic softness; single-prime transport for all `A` ⇔ RH [L]. Residual: a margin at every
entry. Criticality forbids uniform margins (no Hardy weight; margins doubly-exponentially small), and the
first-fold stage loan fails at `21/20` [L]: the step must be an identity at zero slack, paid by the signed fold.
B2.

### F3. The complete-family assembly = the onset aperture
Subcritical PD + one critical multiple across all entries + threshold law + terminal polar source + receiving
charges [L]; twisted sectors cannot repair untwisted modes [L]. Certifies exactly what the base certifies.
Residual: B33, B7, B1.

### F4. The reflection assembly (P3)
Krein–Lax–Phillips space + window lift + defect formula in two coordinate systems [L]. Residual: B38; both
expressions carry `(b^{2σ−½} − b^{−(2σ−½)})²`.

### F5. The camera–continuation assembly (ZCG ⊕ heat)
| Segment | Supplied by | Status |
|---|---|---|
| Heat path real for `t ≥ 1/8`; RH ⇔ `Λ_X = 0` ∀X | RHTower | [L] |
| No collision above `(6600/9991 + ε)/log X`; saddle `½/log X` | ZCG | [L] |
| Collisions are near-coincidences; identification to `e^{−c log³T}`; `𝓗` reads `w²` at polynomial scale | ZCG | [L] |
| Core: `𝓗 ≥ 0` on every near-coincidence (≡ no collision below `½/log X`) | — | B44 = B14 |

### F6. The Krein–camera assembly (CSTW ⊕ Krein ⊕ ZCG)
| Segment | Supplied by | Status |
|---|---|---|
| Window positivity at `a` gives a complete de Branges space `H(E_a)` | CSTW | [L] |
| Positivity at `a` ⇔ a positive measure on ℝ (an on-line mimic) with ζ's image on the window; discrete mimics from de Branges sampling | Krein / de Branges | A39 |
| Camera with real weights; mimic local counts by Beurling–Selberg transfer | ZCG | A40 |
| ζ vs an on-line mimic at `a = λL_T`, `λ > 1`: isolated off-line zeros excluded near `T`; an FE pair against a real pair forces `4δ² ≤ 24r³T^{M'+κ} + 4E`, so `δ ≤ e^{−c log³T}` | ZCG | [L] given A39–A40 |

Output [D]: window positivity at `a` ⇒ every off-line zero of ζ at height `T ≤ 2πe^{2a/λ}` (`T ≥ T₀`) has depth
`≤ e^{−c log³T}`; off RH, `a*(ζ) ≤ (½ + ε)log T_min` for the lowest non-super-shallow off-line zero. Shielding
does not hide from it (tapered crystals live at `λ ≤ ¼`). Residual: the sign itself — the converse (RH below `T` ⇒
positivity at `½log T`) is blocked by doubly-exponential non-locality, so height induction stays closed.

### F7. The canonical-system assembly (CSTW ⊕ GWZ ⊕ SWC)
De Branges chain before contact + lattice Levinson recursion + continuum jet limits + parity split [L] +
Hamiltonian (A41). Output: RH ⇔ the evaluation kernels `K_a(z₀, z₀) = ∫_0^a⟨H(t)Y(t,z₀), Y(t,z₀)⟩dt` stay
bounded on bounded aperture intervals at every `z₀` of one set of uniqueness [D]. Residual: B51 — a growth bound for a monotone scalar,
RH-strength.

### F8. Finite free ⊕ Euler carriers (FFP ⊕ ZCG)
Normalized Euler products HB-stable with drift `θ_S/2` ≡ the carrier horizon `2πe^{θ_S}`; curved Gamma phase
supplies drift `θ'(t)` up to degree `≈ (θ'(t) − θ_S/2)²/θ''(t)` [L]. Residual: the same domination is shared by
every finite real carrier and twins are tilted at every height [L]: no ζ selection; the mollified criterion is a
receiver (B52).

### F9. Finite Hecke graphs ⊕ numerics (WTZ ⊕ A5)
Correlation-form windows are finite matrices below spread 6 [L]; certify `a*` numerically there. Residual: Weil's
form carries the archimedean Lévy part, not a correlation form; margins `10⁻⁵`–`10⁻⁸`; windows below half-width 4
carry no zero information.

### F10. Visibility–density (WVL ⊕ WD ⊕ DCI)
Unshielded clusters excluded to doubly-exponential height; shallow depth mass bounded; inner caps = off-line
generating function [L]. Residual: B1 at growing aperture and B21 (log-free occupancy).

## 2.4 A wildly different route

**Verdict: no route that avoids all three walls is visible.** Every route reads ζ's zeros through the explicit
formula or through a function with ζ's divisor; the three walls are the three components of that formula. Finite
free probability, the farthest mechanism inside the corpus, is worked out [L: FFP]: it meets P5 exactly
(Gaussian capacity `o(d⁻²)` is de Bruijn–Newman criticality; Szegő never applies to the source split; only the
Möbius Euler side is stable). The corpus covers positivity, precision, realization, deformation, recurrence,
counts, function-field transfer, quasicrystals, Lee–Yang, moment problems, Hermite–Biehler phases, finite free
stability, visibility, identification, Bost–Connes, Deninger, Connes trace formulas and Selberg/Maass traces.

**The one source of RH never used by any route: discreteness.** Over `𝔽_q` purity is proved by an argument with no
quadratic-form sign and no square-root count: (i) a pure member of a family, (ii) continuity of the zeros along a
deformation, (iii) **integrality** forcing every near-coincidence to collide exactly or repel at distance
`≥ (4√q)^{−poly(g)}` (Γ43 [L]), so purity is lost only at a collision, and collisions of integral Frobenius
configurations keep the roots on the circle. For ζ the corpus supplies (i) the heat path is real for `t ≥ 1/8`
[L], (ii) reality is lost only through collision [L], and the camera reads every near-coincidence at polynomial
scale [L]. Missing is (iii): a discrete structure on near-coincidences.

*Route Ω (sketch).* Find a deformation family `F_t` from a pure object to ζ, each member carrying an arithmetic
lattice (integral or algebraic structure of bounded height) on the symmetric functions of its zero clusters, so
that a Liouville-type bound gives collide-or-repel uniformly along the path; then, as over `𝔽_q`, no off-line zero
can be born.
- What is far: no window sign (Σ), no prime count at square-root precision (Π), no Krein positivity (Γ). The
  producer is arithmetic discreteness.
- Where it meets the walls: the heat path is not arithmetic (Gaussian smoothing destroys integrality), and the
  camera shows ζ's own image is a `log p`-weighted prime sum with no discreteness [L/D]; the integral families
  with RH (function fields, characters) have no continuous path to ζ (centered Euler meshes recede, ART [L]).
  A first test below RH is B54: polynomial repulsion of distinct zeros of ζ itself.
- Absent from the corpus and also far: homogeneous dynamics (Zagier–Sarnak rate of closed-horocycle
  equidistribution `≍ y^{3/4−ε}` ⇔ RH; its error term has poles at `ζ(2s) = 0`, the Mayer resonances, so it meets
  Γ24); asymptotically exact towers of global fields (limit zeta functions; distributional, blind to single zeros,
  meets Σ26); the Biane–Pitman–Yor Brownian representation of `ξ` (meets P5 through the Lee–Yang/Newman class).

## 2.5 Breakthrough questions below RH and quasi-RH

### 2.5.1 Whole programme — window positivity is zero location at the square-root aperture
**Question.** Prove: if Weil's form of ζ is positive on every window of half-width `a`, then every off-line zero of
ζ at height `T ≥ T₀` with `λ·½log(T/2π) ≤ a` (`λ > 1`) has depth `≤ e^{−c log³T}`; with effective `T₀`.
- **Below RH.** An implication from a finite window to finite height; it proves nothing about `a*(ζ)`.
- **How.** F6: Krein's extension theorem turns positivity at `a` into an on-line positive mimic of ζ's image; the
  de Branges chain of CSTW supplies discrete sampling mimics; the camera with real weights and transferred counts
  identifies ζ with the mimic up to `e^{−c log³T}` clusters; the pair readout excludes FE pairs (A39, A40, A42).
- **Advance.** Every window route outputs zero location directly, with no shielding loss and no constant
  `2²⁶·960`; `a*(ζ)` becomes the visibility height of the first non-super-shallow off-line zero
  (`a* ≤ (½ + ε)log T_min`); the two programmes WVL (sign → location) and ZCG (image → configuration) become one.

### 2.5.2 Route PM — a defect size law
**Question.** At every resonance, bound `|D_s(ψ_s)|` above by an arithmetic quantity (from the three-term
equation and the Hecke relations at `p = 2, 3`) that is `o((σ − ¼)²)` times the `K`-free mass of `ψ_s` when
`|Im s|` is large, so that resonances with `|σ − ¼| ≥ c/log|Im s|` are excluded.
- **Below RH.** De la Vallée Poussin strength for `ζ(2s)`.
- **Why it is not settled.** Both expressions of `−D` are `K_σ`-weighted norms, `K_σ ≍ (σ − ¼)²` near the line
  [L]; an upper bound has to come from arithmetic, and every PM no-go concerns line selectors, not defect size.
- **Advance.** The first sign-bearing statement PM owns: the Krein structure would carry arithmetic beyond
  identification.

### 2.5.3 Route WD — log-free window occupancy
**Question.** Prove `D_win`: for every `A`, at most `ε(A)V` unit windows of `[V, 2V]` contain a zero of depth
`≥ A/log V`, `ε(A) → 0` [statement in Lean: CDG].
- **Below RH.** A density statement.
- **Why it is not settled.** Density estimates count `≍ e^{−cA}V log V` such zeros, a logarithm too many;
  counts and moments cannot give it [L].
- **Advance.** The inner-cap flux being the off-line generating function [L], `D_win` is the strongest
  statement WD can own below RH; with F10 it is the input that excludes shielded shallow crystals.

### 2.5.4 Route HF — stage 2 and the prime-3 entry from the complete family
**Question.** Prove `R₁(A) = ⊤` for every `A` up to and slightly beyond `log 3` (half-width `≈ 0.549`) from the
stage-fold identity: through stage 2 the signed fold of the prime `2` pays what the stage form cannot, and at the
entry `N + 1 = 3` the stage form plus `w₃·foldEnergy` pays the entering end mass, with the critical-curve
decomposition for the untwisted pencil.
- **Below RH.** Finitely many windows; no zero information.
- **Why it matters.** Stage 2 is where the fold, not size, must pay (the uncoupled stage loan fails at `21/20`
  [L]); the entry of `3` is the first entry of a second prime; HF's machinery has never certified a window by its
  own arithmetic (B33).
- **Not to be pursued.** Twisted correctors (refuted above an explicit multiple), uniform floors, energy-only
  receiving control.

### 2.5.5 Route ZCG — collide or repel for ζ
**Question.** Prove that distinct zeros of ζ at height `T` are at distance `≥ T^{−C}` (or `≥ e^{−o(log³T)}`).
- **Below RH.** It says nothing about the real part; off-line zeros could be well separated.
- **Why it is not settled.** Zero-spacing lower bounds are open even under RH; the camera reads clusters only down
  to `e^{−c log³T}`.
- **Advance.** Every near-coincidence of ζ becomes a polynomial-scale object whose squared gap is read by three
  prime-side images [L]; B44 becomes a sign question on a resolved configuration everywhere; it is half of the
  `𝔽_q` mechanism (2.4) for ζ itself.

## 2.6 Breakthrough questions that open the path to RH

### 2.6.1 Whole programme — a kernel bound at one point
**Question.** For every `z₀` in one fixed set of uniqueness (e.g. a non-real sequence with a finite
accumulation point), prove that the Weil reproducing kernel `K_a(z₀, z₀)` (the squared norm of the
Fourier-evaluation Riesz vector in the Weil space of half-width `a`) is bounded on every bounded interval of
apertures.
- **Why it opens the path.** It is RH [D: a bound at `z₀` up to contact passes to the contact form domain and
  forces the transform of the contact null vector to vanish at `z₀` (CSTW); vanishing on a set of uniqueness
  kills the null vector], but each condition is a single monotone scalar: `K_a(z₀,z₀) = sup|F(z₀)|²/W(F)`, increasing in `a`, with canonical-system structure
  `∫_0^a⟨H Y, Y⟩`. A growth bound is a coercivity statement `W(f) ≥ c_a|f̂(z₀)|²` that needs no test-by-test sign
  and can be attacked by ODE/comparison methods across the prime-power lengths `log n`.

### 2.6.2 Route PM — a sign-free defect identity
**Question.** Express `D_s(ψ_s)` at every resonance by an arithmetic identity whose integrand is nonnegative and
does not carry the factor `(b^{2σ−½} − b^{−(2σ−½)})²` — through the retained `T₂` channel, cusp energies of the
reflected pair, or a Hecke relation mixing `s` and `½ − s̄`.
- **Why it opens the path.** Any nonnegative representation ⇔ RH [L]; the known expressions fail only through the
  factor that vanishes at `σ = ¼`, so the question is precisely to find a channel symmetric under `s ↦ ½ − s̄`
  with a definite sign (the `T₂` channel reverses sign under it [L]).

### 2.6.3 Route WD — the off-line generating function
**Question.** At every polynomial stage, prove `Σ_{off-line ρ in the Burnol window}m_ρe^{(ρ−½)t} ∈ L²(e^{−xt}dt)`
from a source identity that does not reference the zeros.
- **Why it opens the path.** It is RH [L], and it is the only open content of WD: the inner-cap flux is this
  generating function plus bounded and `L²` terms [L]. Fixed degree gives the corridor `|β − ½| ≤ C/|γ|^k`.

### 2.6.4 Route HF — transport across one prime
**Question.** Prove `R₁(A) = ⊤ ⇒ R₁(A + log 2) = ⊤` for every `A ≥ 0`: at each entry of a power of `2`, the stage
form plus the signed fold energy pays the entering end mass.
- **Why it opens the path.** Single-prime transport for all `A` ⇔ RH [L]; it is unconditional across the first
  step [L]; the induction runs on one prime and one step length.

### 2.6.5 Route ZCG — positivity of the image Hankel ratio
**Question.** Prove `𝓗 = 4(W₁² − W₀W₂)/W₀² ≥ −B` on every polynomially isolated two-point cluster of ζ, the
`W_j` being the prime sides of three explicit windows at aperture `λL_T`.
- **Why it opens the path.** It excludes every off-line pair of depth above the readout scale [L]; with B54 (or
  the Krein–camera assembly for the remaining scales) it is RH. It is a positivity statement about three prime
  sums, the most explicit form the sign takes in the corpus.

## 2.7 Does closing RH need a new field?

**Assessment: yes, and its first chapter exists: frustrated arithmetic Dirichlet forms (FADF), the theory of
signed, critical, nonlocal Hardy inequalities with arithmetic jumps on intervals.** The field's eight founding
questions are answered in exact form in Lean [L: `TheQuestionsOfTheField`]; each answer is either an
unconditional structure theorem or an exact equivalence with RH. The core is open.

*What it is about.* Translation-invariant quadratic forms on the line known through their dual side (the primes),
restricted to every interval: a logarithmic-order archimedean jump form, arithmetic jumps of length `log n` with
rates `w_n`, a rank-two pole, the trivial-zero Hankel correction. The central object is the Hardy interval `ℋ(c)`
and the claim that the arithmetic part is an admissible Hardy term on every window.

*What it is like.* Critical (unique admissible multiple, no Hardy weight, doubly-exponentially small margins);
frustrated (unbalanced in every sign gauge past `log ρ` and `½log 2`); trace-free (no point values, only
`Ω`-weighted edge masses); canonical-system valued (a de Branges chain until contact); moment-theoretic (sectors
are Hamburger/Stieltjes problems); Krein-flavoured (the pole one negative square); finitely reducible only below
spread 6 (rational Hecke graphs); exact in output (every theorem a lower bound for `a*(ζ)`, converted into zero
location by the visibility law and the camera).

*Criteria it must meet.*
1. Reproduce `log ρ`, the base `a₁`, the stages below `log 4` and their margins `10⁻⁴`–`10⁻⁸`.
2. Pay the pole square (odd) and the cosh deficit (even) with retained variance; the trivial zeros at the centre.
3. Be critical: one admissible multiple, no Hardy weight, margins tending to zero.
4. Deliver the band on every reflection pair (two sites decide; two real parameters decide).
5. Work in a frame where frustration is not switched away: positivity of unbalanced signed forms.
6. Pay the primes by sign beyond `21/40`, and collectively beyond `c* ∈ (½log5, ½log6]`.
7. Survive the end of finite templates at spread 6 (infinite Hecke orbits).
8. Distinguish ζ from every finite real carrier, from Lindelöf-bounded pair models, from Euler twins, flips,
   Beurling systems and `ζ(s)ζ(s−ε)`; use the functional equation and the Euler product together, the Euler
   product inside the strip.
9. Explain the square-root aperture `λ = ½` as the reading aperture of the camera and the Krein–camera height law.

*Questions it must answer.*
- What replaces the Allegretto–Piepenbrink theorem (positivity ⇔ a positive supersolution) for forms that are
  frustrated in every sign gauge?
- Is there a signed ground state whose nodal set is forced (pole: edge versus centre; primes: sliver
  anti-diagonals), such that positivity reduces to a balanced (Kron-reduced) form on its nodal domains?
- How does the Hamiltonian of the Weil canonical system jump at the lengths `log n`, and what keeps it regular?
- What is the collective law of all acting sliver reflections against the pole square when finite templates no
  longer exist?
- Is there a discrete (integral) structure on near-coincidences of ζ, giving collide-or-repel?
- Which optimal Hardy weights does the archimedean logarithmic operator with the pole admit, constructively?

*Tools.* Criticality theory and optimal Hardy weights for nonlocal operators; signed-graph theory (switching,
frustration index, Kron reduction); Krein and Pontryagin spaces; Krein strings, de Branges chains, inverse spectral
theory; Szegő–Levinson theory; Hamburger/Stieltjes moment theory; finite free convolution and stability
preservers; Beurling–Malliavin completeness; rational Hecke graphs and Følner averaging; the corpus's pole-charged
representation, Hardy intervals, calibration spaces, entry laws, onset-aperture calculus and camera.

*Objects and language.* Hardy intervals, calibration spaces, stage fibres, signed theta gauges and their neutral
parameter, shifted ground states, charge variances, mirror masses, edge killing, sliver signatures, outward-edge
ratios, Lévy tails `Ω`, rational Hecke graphs and templates, de Branges chains, contact, evaluation kernels,
squared-gap Hankel ratios, onset apertures, pair energies.

*Mechanisms it aims to discover.* A ground-state theory for unbalanced critical forms; a margin transport across
entries that is an identity at zero slack; a Hamiltonian regularity law across `log n`; a collective sliver law
beyond finite templates; a discreteness law at near-coincidences.

*Outside the field.* Counts and Hodge index; Markov, Perron and switched-balance certificates past their
thresholds; size-only payment; point-value certificates; finite templates past spread 6; source-faithful finite
free splits; PM line selectors; identification without sign.

## 2.8 The one question

**Is `a*(ζ) ≥ log 2` — equivalently `1 ∈ ℋ(c)` for every `c < log 2` — provable by the exact two-sector signed
certificate, with the prime `3` paid by the sign of its sliver reflection?**

Concretely: on every window `[−c, c]`, `c < log 2`, the neutral signed theta-gauge inequality `2V ≤ J_{M⁺}`
(even sector) and the shifted-ground-state inequality (odd sector) hold for the arithmetic weights
`(Λ(2)/√2, Λ(3)/√3)` [format L: SWC]. Equivalently [L]: the arithmetic point lies in the compact convex set
`belowLogFourBandWeights c`; `R₁(2c) = ⊤`; Künneth effectivity; the Hodge index of the scaling subsurface.

*What the window contains.* The primes `2` and `3` and nothing else; even frustration by the pole past `log ρ`
in every sign gauge; odd frustration by the kick of `2` from `½log 2` in every sign gauge; size payment dead
(`H < 0` by `21/40`); the prime `3` not payable by its collar (`287/500`) and indispensable (`3/5`); the entry of
`3` at `½log 3` logarithmically soft from both sides with sharp constants; stage loans failing at `21/20`; finite
rational Hecke templates available; numerical margins `2×10⁻⁴` (odd unit window), `1.5×10⁻⁵` and `5.6×10⁻⁸`
(at `½log 3`) [L/N].

*Why it is less hard than RH or quasi-RH.* A finite window, two numbers, an exact certificate format, a compact
convex admissible set; it implies no statement about zeros.

*Why it pushes the door open.* It is the smallest window where every feature of the sign is present at once:
unswitchable frustration in both sectors, a prime paid by sign at its entry, retained variance, criticality, a
stage step at zero slack. Every structural certificate that settles it is a template for B2/B3 and answers B49 at
its first instance (the nodal structure past `log ρ`); it is shared by nine routes (B5) and by the whole
equivalence web (HF threshold, ACS Hodge index, LST effectivity, SWC band, FADF Hardy interval, RW/OWU/EWU/ACT/TT
sectors). A proof that no certificate of the exact format exists for the arithmetic weights at some `c < log 2`
would refute RH; because the format is exact, no missing term can be blamed.

*Why this and not another.* The Krein–camera theorem (2.5.1) is location, not sign; the kernel bound (2.6.1), the
image Hankel ratio (2.6.5), the defect identity (2.6.2) and single-prime transport (2.6.4) are RH-strength;
collide-or-repel (2.5.5) gives identification only; the odd unit window (B4) is the first sub-case but lacks the
prime `3` and the even sector. The two-weight window is sub-RH, finite, exact, shared by the most routes, and
isolates the mechanism in pure form.
