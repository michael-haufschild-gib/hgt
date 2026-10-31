# Route unification ledger — status quo

The 33 live routes, 16 candidates and PW-B are faces of three core problems. The three problems are
three readings of one integer: the negative index `κ` of Weil's correlation `K_ζ` on the dilations of
`Aff(ℚ)`. The archimedean Weil state turns that integer into an index-one statement:
`κ(ratCorr(|a|) − c|a|^{−½}|b|) = κ_ζ + 1`.

## 0. The one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ(K_ζ) = #{ρ : Re ρ > ½}`, already on two primes | HKT `TheFiniteIndexStratumOfZetaIsLindelofDeep` [L] |
| Archimedean state | `κ(φ_c) = κ^{(½)}(K_ζ) + 1 = κ_ζ + 1`; RH ⇔ `κ(φ_c) = 1` | AKG `TheArchimedeanGluingFormula`, `WeilsArchimedeanStateCountsTheZeros` [L] |
| Hyperplane | boost hyperplane `Σ w_n n^{−½} = 0` = `v_1^⊥`, `v_1` the pole conductor = complete-Weil ground state | AKG `boostMassU`, RAPT, CACT `TheCompleteWeilGroundStateIsThePole` [L] |
| Sign (Σ) | RH ⇔ `κ = 0` ⇔ Weil form `≥ 0` | HKT [L] |
| Count (Π) | `κ = 0` ⇔ `ψ(x) − x ≤ C√x log²x` | HKT `TheGlobalLawIsTheOneSidedSquareRootCount`, ACP [L] |
| Selection (Γ) | `κ` twin-blind; glued index pole-blind; pole-index window separates ζ (0) from the Liouville twin (1) | AKG, HKT [L] |
| Quantum | collision mass `= 2(κ + multiplicity excess)`; `κ ≤ sup O`; RH ⇔ `O < 2` per window | HKT, RHTower [L] |
| Polarization | `W` Hecke-invariant (sign = RH) vs collided `D` positive (invariance = RH); `W = D` ⇔ RH | AP [L] |
| Geometry | `κ` = Hodge defect of the scaling surface; RH ⇔ effectivity ⇔ section count | ACS, ACP [L] |

The three walls are the three ways a reading of `κ` fails: the sign is not determined by estimates
(Σ), the count is not precise enough (Π), the reading cannot tell ζ from its twins (Γ).

## U-Σ — the sign of the complete Weil form on the pole-orthogonal hyperplane

Core problem: the complete Weil form (all primes, prime powers, poles, Gamma) is nonnegative on an
RH-complete test family; equivalently, on `v_1^⊥` (the pole direction carries the positive ground
energy and is invisible to the glued index).

Internal structure of the core problem:

| Layer | Status | Anchor |
|---|---|---|
| Conductor averages (`m ≤ N^θ`, `θ < ½`) at RH-complete overlap | Solved [S] | CAF level of distribution, conductor-average positivity |
| Low-conductor block / ground state `v_1` | Solved at fixed `c` and diagonal schedules [L] | RAPT low spectrum, CACT ground state |
| Confinement of negative vectors (logarithmic reserve) | To `(log log N)^{<1/16}` [L]; beyond open | CACT reserve, iterated-log positivity |
| Exceptional conductors; conductors above `N^{½}` | Open | Σ1g, Σ1h |

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix at growing overlap | HF, SRT, AIP, ACT, ACS-atomic, CAF, CACT, RAPT, SSH, SSHA | positivity at `c_N = 2(log N)^{α>¼}` (Σ1) |
| Archimedean Weil state | SC, AKG | `κ(φ_c) ≤ 1` ⇔ positivity on `v_1^⊥` (same problem at overlap `→ ∞`) |
| Aperture-indexed ground minimum | RW, EWU, OWU, MSC, CCM | `μ(A) ≥ 0` for every `A`; RH ⇔ zeros approach the line ∧ `μ₀` subexponential |
| Haar / Doob / odd sector | CHMD, AID, SAHT | `R ≤ ½` on odd vectors; uniform coarse index (Σ3, Σ5) |
| Rank-indexed Hankel / Jensen | TH, LA, HCF, PA, GTA | all-rank / all-degree sign (Σ4) |
| Scheduled prime sums | FU, CFC, RP, SZ, LI, FEL, EGC | lower bound on a prime-scheduled energy |
| Heat flow | WD, LA, HEF | every `Λ_X = 0`; `E(0) = 0` (Σ5, Σ8) |
| Quantum / trace | TG, WD (collision), AID (source work) | integer `< 2` (Σ8) |
| Realization | RN, PTR, W1C, PM | spectral reality of a constructed operator (Σ6) |

Identities joining the faces [L]: archimedean gluing `κ = κ^{(½)} + 1`; complete cells capture every
finite index; zeros read atomic vectors through Möbius horizons; `{λ_t > 0}` null ⇔ RH and
`Λ = sup Λ_X`; the odd sector carries every failure; collision mass counts the index twice.

## U-Π — square-root precision of a one-sided source count

Core problem: an unconditional one-sided count at square-root precision, or an exact geometric object
whose Riemann–Roch delivers it.

| Face | Routes / programmes | Reduction |
|---|---|---|
| One-sided prime count | WL, PBM, RB, JAS, CTF, ACP, ASRP | `ψ(x) − x ≤ C√x log²x` (Π1) |
| Integer producers | WL, AKLT, AHA | ε-uniform producer; dual precision = convergence rate of `Σ μ(b) log b/b` (Π3) |
| Möbius / Mertens cancellation | MC, BVI, THIM, BSU | moving-scale half-power cancellation; 3/4 strip via near band (Π2, Π11) |
| Effectivity / sections | ACS, SPTL, AET | quadratic Hilbert–Samuel `h⁰` (Π11) |
| Exceptional moduli | MC, CACT, CAF | individual control beyond `(log x)^A` (Π9 = Σ1g) |
| Census / density / local counts | SRT, IGP, Zeta23, Guth–Maynard | 100% critical; pointwise local count (Π8, Π12) |
| Heat counts | WD, LA | `N(t)` growth (Σ5 ∩ Π) |
| Candidates | APF, EWJ, FEL, WBF, IRK | integral counts from a source lift |

Identities [L]: one-sided count ⇔ `κ = 0`; graded strip shortfall rate = zero width; five rate
currencies = zero width; prime-error budget `≥ 2 + γ − log 4π`, equality ⇔ RH + simple; Farkas
duality between producer slopes and Möbius log-harmonic measures.

## U-Γ — selection of ζ at the trivial gauge point

Core problem: a zero-independent, source-defined mechanism distinguishing ζ from its twins and gauges
(Liouville twin, prime flips, Davenport–Heilbronn combinations).

| Face | Routes / programmes | Reduction |
|---|---|---|
| Typicality of the trivial point | MC, AGT, BAG, XN | RH ⇔ trivial point typical; recurrence; Newton margin (Γ1) |
| Gluing of the global pole | SC, AKG | one-square state from coupled places (Σ11); glued index pole-blind (Γ11) |
| Physical / native source action | PM, PW-B | zero-independent selection (Γ5) |
| Pre-divisor constructions | BSH, CDC, HJ, SEC, PCS, RFHM, DR, EWJ, APF, WBF | a section / potential defined before the divisor (Γ5) |
| Polarization | AP, CDG | Hecke invariance of the collided form (Γ4) |
| Function-field calibration | ACS (F₃), AKG (`𝔽_q[T]`) | what Frobenius supplies that ℤ lacks (Γ10) |

Identities [L]: index twin-blind; pole-index window selects; Haar successors with continuous dilation
have infinite index; the archimedean successor is the unique finite-index carrier type with Weil
dilation and visible successor in the corpus.

## Cross-family seams

| Seam | Statement | Routes on the seam |
|---|---|---|
| Σ ∩ SC: one hyperplane | SC's index-one problem and the complete-Weil sign problem are positivity on `v_1^⊥` | SC, HF, SRT, AIP, ACS-atomic |
| Σ ∩ Π: averages vs individuals | conductor averages are solved; exceptional conductors are exceptional moduli | HF, SRT, AIP, MC, CAF |
| Σ ∩ Π: confinement | negative vectors must live on low conductors; detectors live on long Möbius transforms | CACT, RAPT, HF, SC |
| Σ ∩ Π: finite index | `κ < ∞` ⇒ Lindelöf + zero-free half-plane | HKT, AKLT, SRT towers, CHMD, WD |
| Σ ∩ Γ: gluing | archimedean place glues by a hyperplane; distinct places keep one square each; the global pole needs product-formula coupling | AKG, SC |
| Π ∩ Γ: count precision | `Count(a)` iff `a − 1 ∈ 𝒬`; `Λ + 1/n` has Count iff RH but is never tower-positive | ACountP, SMAP, WL |
| Σ ∩ Π ∩ Γ: archimedean channel | the archimedean place is the only bridge; continuous archimedean dilation cannot coexist with height decay at finite index | AKG, ALG, CHMD |

## Route → core problem map

| Route | Core | Face |
|---|---|---|
| WL | Π | one-sided count, producers |
| RW, EWU, OWU | Σ (Γ) | ground minimum; selectivity |
| FU, CFC, RP, SZ, LI | Σ | scheduled prime sums |
| PA, TH, LA, HCF, GTA | Σ | rank / degree sign |
| MC | Π (Γ) | Möbius cancellation; typicality |
| TT | Σ | odd / directed covariance |
| TG | Σ | quantum |
| HF, SRT, AIP, ACT | Σ | complete atomic matrix |
| SC | Σ (Γ) | archimedean Weil state; gluing |
| CHMD | Σ | Haar / Doob / odd sector |
| RN | Σ | realization |
| WD | Σ (Π) | heat flow, collision quantum |
| PM | Γ (Σ) | native source action |
| JAS, CTF, PBM, RB | Π | one-sided count |
| XN, BAG | Γ | typicality / recurrence |
| ACS | Π (Σ, Γ) | effectivity; atomic; automorphic calibration |
| APF, EWJ, WBF, IRK | Γ (Π) | source lift with integral count |
| BSH, CDC, HJ, SEC, PCS, RFHM, DR | Γ | pre-divisor constructions |
| EGC, FEL, MSC | Σ | contour / likelihood / Sonin |
| PTR, W1C | Σ | realization |
| PW-B | Γ | native source action |

## What a closing argument must supply

Over `𝔽_q` one object — the Frobenius graph on `C × C` — supplies all three readings: the Hodge index
gives the sign, Riemann–Roch gives the count, and the graph is canonical. Over ℤ the corpus holds each
ingredient separately:

| Needed | Present over ℤ | Missing |
|---|---|---|
| Positivity by identity | local shell decomposition; finite-sieve signature; collided form `D ≥ 0`; archimedean gluing by a hyperplane | an identity on `v_1^⊥` for the infinite assembly |
| Confinement | logarithmic reserve to `(log log N)^{<1/16}`; conductor averages at RH-complete overlap | polynomial confinement; exceptional and super-square-root conductors |
| Count from geometry | exact linear theta RR; arithmetic Bézout; producers at the main term | a quadratic Riemann–Roch; ε-uniform producers |
| Canonical selector | pole-index window; boundary sign | a coupling of places with one square; a conformal correspondence over ℤ whose factor is not archimedean size |
