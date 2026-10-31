# Route unification ledger — status quo

The 33 live routes and 16 candidates are faces of three core problems, and the three core problems
are three readings of one integer on one hyperplane: the negative index `κ = κ(K_ζ)` of Weil's
correlation on the dilations of `ℚ`, read on the pole-orthogonal hyperplane `v₁^⊥`. Gluing at any
place turns it into an index-one statement, `κ(K(|a|) + |a|_v^{−s/2}ψ(b)) = κ_ζ + 1`, and the
renormalized Hodge index (RIT) is its geometric name: RH ⇔ the pairing of scaling correspondences
is positive on the hyperplane orthogonal to the pole class.

## 0. The one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ(K_ζ) = #{ρ : Re ρ > ½}`, already on two primes | HKT `TheFiniteIndexStratumOfZetaIsLindelofDeep` [L] |
| Glued state | `κ(φ_c) = κ_ζ + 1` at `∞` and at every prime; translation reading `κ = 1` for every glued state | AKG `TheGluingFormulaAtEveryPlace`, `TheTwoReadingsAdd` [L] |
| Hyperplane | boost hyperplane = `v₁^⊥` = Markov hyperplane = harmonic hyperplane; `v₁` = complete-Weil ground state | RIT `ThePoleClassIsTheGroundConductor`, `TheHodgeIndexAtGrowingOverlap` [L] |
| Hodge index | RH ⇔ `κ^{(½)}(K_ζ) = 0` ⇔ glued index `1`; `κ^{(½)}(K_ζ) = κ(K_ζ)` | RIT `TheRenormalizedHodgeIndex` [L] |
| Sign (Σ) | RH ⇔ Weil form `≥ 0` ⇔ positivity on `v₁^⊥` at RH-complete resolution | HKT, RAPT, RIT [L] |
| Count (Π) | `κ = 0` ⇔ `ψ(x) − x ≤ C√x log²x` | HKT, ACP [L] |
| Selection (Γ) | index twin-blind, glue pole-blind; glued test index `κ_ζ + 1` for `Λ`, `∞` for finite flips | AKG, RIT [L] |
| Heat | `κ(φ_c^{(t)}) − 1` = Hodge defect of `K_t` = `N(t)/2` = future collision pairs | AKG, RIT [L] |
| Quantum | collision charge = theta-prefix Fredholm index; `κ ≤ sup O`; RH ⇔ `O < 2` per window | CDG, RIT, RHTower [L] |
| Polarization | `W` Hecke-invariant (sign = RH) vs collided `D ≥ 0` (invariance = RH); `W = D` ⇔ RH | AP, CDG [L] |
| Künneth | `κ(K_ζ⊠K_ζ) ∈ {0, ∞}`, `0` ⇔ RH; `K_ζ^n` PD ⇔ RH | RIT [L] |
| Geometry | `κ` = Hodge defect of the scaling surface; RH ⇔ effectivity ⇔ section count ⇔ Castelnuovo–Severi at rational scales | ACS, ACP, RIT [L] |

The three walls are the three ways a reading of `κ` fails: the sign is not determined by estimates
across the detection edge (Σ), the count is not precise enough (Π), the reading does not distinguish
ζ from its twins (Γ).

## 1. Equivalence classes of routes

Routes in one class compute the same quantity; a theorem in one class transfers to the others by the
listed identity.

| Class | Common quantity | Routes | Identity joining them |
|---|---|---|---|
| C1 Hyperplane sign | Weil form on `v₁^⊥` at growing resolution | HF, SRT, AIP, ACS-atomic, ACT, SC (finite resolution), RIT-Hodge, CHMD-index | pole class = ground conductor; boost mass `= √(log N)⟨x, v₁⟩` [L] |
| C2 Aperture sign | ground minimum `μ(A)` of the complete form on tests of aperture `A` | RW, EWU, OWU, CFC, MSC | sinc multiple `K` at critical overlap ⇔ aperture `R` with `288e⌈1+e^{2(R+1)}⌉ < K/(4K_τ)` [L] — links C2 to C1 |
| C3 Heat / collision integer | `N(t)/2` and the horizontal collision charge | WD, SC-heat, LA (local heat), TG, HEF | heat index = future collisions; `κ ≤ sup O`; collision charge = Fredholm index [L] |
| C4 Odd / Markov sector | odd-sector Doob energy, `R ≤ ½` | CHMD, TT, AID, SAHT | Markov hyperplane = `v₁^⊥` (on atomic tests Weil form = Markov form) [L] — links C4 to C1 |
| C5 Rank / degree uniformity | all-rank Hankel or all-degree Jensen signs | TH, HCF, PA, GTA, LA-Jensen | heated Hankel inertia counts off-line pairs at matched rank [L] |
| C6 Scheduled prime sums | lower bound of a prime-scheduled energy | FU, CFC, RP, SZ, LI, FEL, EGC | each is an explicit-formula functional bounded below ⇔ RH [L/map] |
| C7 One-sided count | `ψ(x) − x` or `M(x)` at square-root precision | WL, MC, PBM, RB, JAS, CTF, ACS-effectivity | `Count(a)` iff `a − 1 ∈ 𝒬`; Farkas duality producers ↔ Möbius log-harmonic measures [L] |
| C8 Selection / typicality | the trivial gauge point among twins | MC-typicality, BAG, XN, PM | RH ⇔ trivial point typical; recurrence near every strip point [L] |
| C9 Realization | spectral reality of a constructed operator | RN, PTR, W1C, PM | Vitali: a normal real-zero approximant family forces RH [L] |
| C10 Pre-divisor | a section or potential defined before the divisor | APF, BSH, CDC, DR, EWJ, HJ, IRK, PCS, RFHM, SEC, WBF | each needs a zero-independent forcing (Γ5) |

C1, C2 and C4 are one problem (same hyperplane, linked resolutions). C3 is the heat face of the same
integer. C5 and C6 are sign problems on test families that are RH-complete only in the limit of rank
or schedule. C7 is the count face, C8–C10 the selection face.

## U-Σ — positivity on the pole-orthogonal hyperplane across the detection edge

Core problem: the complete Weil form (all primes, prime powers, poles, Gamma) is nonnegative on `v₁^⊥`
on an RH-complete test family.

Internal structure:

| Layer | Status | Anchor |
|---|---|---|
| Universal regime (no zero information) | tilted spline to `(log N)^{α<α*}`, all vectors [L] | CACT power-log |
| RH regime | tilted `α > ¼` (full), `α > ½` (`v₁^⊥`); C^∞ profiles every `α > 0` on `v₁^⊥`; sinc at `τ(c) log N ≈ 1` [L] | RAPT, RIT, TM |
| Low-conductor block | solved in the universal regime; residual-versus-floor ceiling `19 = 5 + 2·7` [L] | CACT, SSH |
| Confinement | reverse defect gap and exponential cutoff [L]; defect `≤ C c¹⁶` keeps confinement below `√N` only for `α < 1/16` | CAF, RAPT |
| Conductor averages | solved at RH-complete overlap [L] | CAF |
| Exceptional and super-`√N` conductors | open | Σ1g, Σ1h |
| Detection edge | between the regimes; unconditional positivity cannot cross it | Σ14 |

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, ACS-atomic, CAF, CACT, RAPT, SSH, SSHA | positivity at `2(log N)^{α>¼}` (tilted) or at every power of `log` on `v₁^⊥` (C^∞) |
| Archimedean / `p`-adic glued state | SC, AKG | `κ(φ_c) ≤ 1` ⇔ positivity on `v₁^⊥` |
| Renormalized Hodge index | RIT | definiteness of the renormalized pairing on the pole-orthogonal hyperplane |
| Aperture ground minimum | RW, EWU, OWU, MSC, CFC | `μ(A) ≥ 0` for every `A` |
| Haar / Doob / odd sector | CHMD, AID, SAHT, TT | `R ≤ ½` on odd vectors; uniform coarse index |
| Rank / degree | TH, LA, HCF, PA, GTA | all-rank / all-degree sign |
| Scheduled prime sums | FU, CFC, RP, SZ, LI, FEL, EGC | lower bound on a prime-scheduled energy |
| Heat flow | WD, LA, HEF, SC-heat | no index jump on `(0, 1/8]`; `Λ = 0` |
| Quantum / trace | TG, WD (collision), AID (source work) | an integer `< 2` |
| Realization | RN, PTR, W1C, PM | spectral reality of a constructed operator |
| Künneth / powers | RIT | closed: RH-equivalent at every degree, all-or-nothing |

Identities joining the faces [L]: gluing at a place `κ = κ_v + 1`; readings add; pole class = ground
conductor; on atomic tests Weil form = Markov form on `v₁^⊥`; heat index = future collisions =
Hodge defect of `K_t`; `{λ_t > 0}` null ⇔ RH and `Λ = sup Λ_X`; collision mass counts the index twice;
Künneth square squares the index.

## U-Π — square-root precision of a one-sided source count

Core problem: an unconditional one-sided count at square-root precision, or an exact geometric object
whose Riemann–Roch delivers it.

| Face | Routes / programmes | Reduction |
|---|---|---|
| One-sided prime count | WL, PBM, RB, JAS, CTF, ACP, ASRP | `ψ(x) − x ≤ C√x log²x` (Π1) |
| Integer producers | WL, AKLT, AHA | ε-uniform producer; dual precision = convergence rate of `Σ μ(b) log b/b` (Π3) |
| Möbius / Mertens cancellation | MC, BVI, THIM, BSU | moving-scale half-power cancellation; 3/4 strip via the near band (Π2, Π11) |
| Effectivity / sections | ACS, SPTL, AET | quadratic Hilbert–Samuel `h⁰` (Π11) |
| Exceptional moduli | MC, CACT, CAF | individual control beyond `(log x)^A` (Π9 = Σ1g) |
| Census / density / local counts | SRT, IGP, Zeta23, Guth–Maynard | 100% critical; pointwise local count (Π8, Π12) |
| Heat counts | WD, LA, SC-heat | `N(t)` growth (Σ5 ∩ Π) |
| Integer collision readings | WD, CDG | detection scale = collision gap (Π13) |
| Candidates | APF, EWJ, FEL, WBF, IRK | integral counts from a source lift |

Identities [L]: one-sided count ⇔ `κ = 0`; graded strip shortfall rate = zero width; prime-error budget
`≥ 2 + γ − log 4π`, equality ⇔ RH + simple; Farkas duality between producer slopes and Möbius
log-harmonic measures; theta readings recover the collided form, every depth moment and the collision
charge with explicit certificates.

## U-Γ — selection of ζ

Core problem: a zero-independent, source-defined mechanism distinguishing ζ from its twins and gauges
(Liouville twin, prime flips, Davenport–Heilbronn combinations).

| Face | Routes / programmes | Status / reduction |
|---|---|---|
| Typicality of the trivial point | MC, AGT, BAG, XN | RH ⇔ trivial point typical (Γ1) |
| Gluing of the global pole | SC, AKG, RIT | classified: only the extremal weight (archimedean pole) has one square; the glue is pole-blind (Σ11, Γ11) |
| Index selection | RIT, HKT, ACP | glued test index separates every finite flip; atomic Hodge index separates exactly submaximal margins; maximal-margin infinite twins open (Γ2, Γ12) |
| Physical / native source action | PM; PW-B retired | source-uniform extinction is a no-go; half-parameter cusp selection is RH (Γ13) |
| Pre-divisor constructions | BSH, CDC, HJ, SEC, PCS, RFHM, DR, EWJ, APF, WBF | a section / potential defined before the divisor (Γ5) |
| Polarization | AP, CDG | Hecke invariance of the collided form; Frobenius at infinity (Γ4) |
| Function-field calibration | ACS (`𝔽₃`), AKG (`𝔽_q(X)`), RIT | identical local walls; ℤ differs by density of the extremal-weight exponents (Γ10) |

Identities [L]: index twin-blind; glue absorbs exactly its own exponent pair; Haar successors with
continuous dilation have infinite index; gluing at a place is the unique finite-index carrier type with
Weil dilation and visible successor; glued index never loses a square.

## 2. Cross-family seams

| Seam | Statement | Routes on the seam |
|---|---|---|
| Σ ∩ SC: one hyperplane | SC's index-one problem, the complete-Weil sign problem and the Markov criterion are positivity on `v₁^⊥` | SC, HF, SRT, AIP, ACS-atomic, CHMD, RIT |
| Σ ∩ Π: detection edge | at the RH threshold the ground energy is `≲ 1/log N`; every error must be beaten at that scale; unconditional positivity stops at the edge | HF, SRT, AIP, SC, CACT, RAPT |
| Σ ∩ Π: confinement | defect `≤ C c¹⁶` confines negative vectors only below `exp(C c¹⁶)`; above `√N` frames and averages are missing | CACT, CAF, RAPT, HF, SC |
| Σ ∩ Π: finite index | `κ < ∞` ⇒ Lindelöf + zero-free half-plane; `κ(K_ζ⊠K_ζ) < ∞` ⇒ RH | HKT, AKLT, SRT towers, CHMD, WD, RIT |
| Σ ∩ Γ: gluing | the archimedean place supplies the square; the glue is pole-blind; selection by prime data (glued test index) | AKG, SC, RIT |
| Σ ∩ Π ∩ Γ: heat and collisions | SC-heat index − 1 = WD future collisions = Hodge defect of `K_t`; integer readings exact, detection scale = zero gap | SC, WD, LA, CDG, RIT |
| Π ∩ Γ: count precision | `Count(a)` iff `a − 1 ∈ 𝒬`; `Λ + 1/n` has Count iff RH but is never tower-positive | ACountP, SMAP, WL |
| Archimedean channel | the archimedean place is the only bridge between primes and between `+` and `×`; continuous archimedean dilation cannot coexist with height decay at finite index; its exponents are dense once two primes are present | AKG, ALG, CHMD, RIT |

## 3. Route → core problem map

| Route | Core | Class | Face |
|---|---|---|---|
| WL | Π | C7 | one-sided count, producers |
| RW, EWU, OWU | Σ (Γ) | C2 | aperture ground minimum; selectivity |
| FU, CFC, RP, SZ, LI | Σ | C6 | scheduled prime sums |
| PA, TH, LA, HCF, GTA | Σ | C5 | rank / degree sign |
| MC | Π (Γ) | C7, C8 | Möbius cancellation; typicality |
| TT | Σ | C4 | odd / directed covariance |
| TG | Σ | C3 | quantum |
| HF, SRT, AIP, ACT | Σ | C1 | complete atomic matrix |
| SC | Σ (Γ) | C1, C3 | glued state; heat homotopy |
| CHMD | Σ | C4, C1 | Haar / Doob / odd sector |
| RN | Σ | C9 | realization |
| WD | Σ (Π) | C3 | heat flow, collision index |
| PM | Γ (Σ) | C8, C9 | native source action |
| JAS, CTF, PBM, RB | Π | C7 | one-sided count |
| XN, BAG | Γ | C8 | typicality / recurrence |
| ACS | Π (Σ, Γ) | C7, C1 | effectivity; atomic; automorphic calibration |
| APF, EWJ, WBF, IRK | Γ (Π) | C10 | source lift with integral count |
| BSH, CDC, HJ, SEC, PCS, RFHM, DR | Γ | C10 | pre-divisor constructions |
| EGC, FEL, MSC | Σ | C6, C2 | contour / likelihood / Sonin |
| PTR, W1C | Σ | C9 | realization |
| PW-B (retired) | Γ | — | source-uniform extinction refuted |

## 4. What a closing argument must supply

Over `𝔽_q` one object — the Frobenius graph on `C × C` — supplies all three readings: the Hodge index
gives the sign, Riemann–Roch the count, and the graph is canonical. Over ℤ the corpus holds each
ingredient separately:

| Needed | Present over ℤ | Missing |
|---|---|---|
| Positivity by identity | local pole–successor forms = hyperbolic pair + shell squares; archimedean successor side = exact shell squares on `ℓ = 0`; matched prime form with one positive direction on every finite sieve; `D ≥ 0` | an identity for Weil's dilation form on `ℓ = 0` |
| Positivity across the detection edge | universal regime to `(log N)^{α*}`; conductor averages at RH-complete overlap | a mechanism that is not an estimate (estimates are zero-blind) |
| Count from geometry | linear theta RR; arithmetic Bézout; producers at the main term | a quadratic Riemann–Roch; ε-uniform producers |
| Canonical selector | glued test index; atomic Hodge selection; pole boundary sign | selection of maximal-margin infinite twins; a conformal correspondence over ℤ whose factor is not archimedean size |
| Integrality with homotopy invariance | collision charge as a Fredholm index; heat index as a Pontryagin homotopy | a zero-independent homotopy or detection scale along which the integer cannot jump |
