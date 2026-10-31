# Route unification ledger — status quo

The 32 live routes, 17 candidates and PW-B are faces of three core problems. The three problems are
themselves three readings of one integer: the negative index `κ` of Weil's correlation `K_ζ` on the
dilations of `Aff(ℚ)` (the Hecke orbit kernel of the cubic spline).

## 0. The one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ(K_ζ) = #{ρ : Re ρ > ½}` (distinct, with the conjugate pair), already on two primes | HKT `TheFiniteIndexStratumOfZetaIsLindelofDeep` [L] |
| Sign (Σ) | RH ⇔ `κ = 0` ⇔ `κ ≤ 1` ⇔ Weil form `≥ 0` | same [L] |
| Count (Π) | `κ = 0` ⇔ `ψ(x) − x ≤ C√x log²x` | HKT `TheGlobalLawIsTheOneSidedSquareRootCount`, ACP [L] |
| Selection (Γ) | `κ` is twin-blind, but the pole-index window gives ζ index 0 and the Liouville twin index 1 | AKG `TheIndexIsTwinBlind`, HKT pole index [L] |
| Quantum | collision charge `O = 2(κ + multiplicity excess)`; RH ⇔ `O < 2` per window | HKT, RHTower [L] |
| Polarization | `W` (Hecke-invariant, sign = RH) vs collided `D` (positive, invariance = RH); `W = D` ⇔ RH | AP [L] |
| Geometry | `κ` = Hodge defect of the scaling surface; RH ⇔ effectivity ⇔ section count | ACS, ACP [L] |

Every route reads `κ` (or a function of it) through one of these columns; the walls are the three
ways the reading fails: the sign is not determined by the estimates (Σ), the count is not precise
enough (Π), the reading cannot tell ζ from its twins (Γ).

## U-Σ — the sign of the complete Weil form at RH-complete resolution

Core problem: show the complete Weil form (all primes, prime powers, poles, Gamma) is nonnegative on a
test family that is RH-complete.

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix at growing overlap | HF, SRT, AIP, ACT, ACS-atomic, SC (atomic), CACT, RAPT, SSH, SSHA | positivity at `c_N = (log N)^{α>¼}` (Σ1) |
| Aperture-indexed ground minimum | RW, EWU, OWU, MSC, CCM | `μ(A) ≥ 0` for every `A` |
| Haar / Doob / odd sector | CHMD, AID, SAHT, ACT | `R ≤ ½` on odd vectors; uniform coarse index (Σ3, Σ5) |
| Rank-indexed Hankel / Jensen | TH, LA, HCF, PA, GTA | all-rank / all-degree sign (Σ4) |
| Scheduled prime sums | FU, CFC, RP, SZ, LI, FEL, EGC | a lower bound on a prime-scheduled energy (Σ) |
| Heat flow | WD, LA, HEF | `λ_WD = sup λ_t = 0`; `E(0) = 0` (Σ5, Σ8) |
| Quantum / trace | TG, WD (collision), AID (source work) | integer `< 2` (Σ8) |
| Realization | RN, PTR, W1C, PM | spectral reality of a constructed operator (Σ6) |

Identities joining the faces [L]: complete cells capture every finite index (AID); fixed coarse cells
control the entire Weil index up to readouts (AID); the critical overlap law synthesizes every fixed
test from atoms (SSHA); `{λ_t > 0}` null ⇔ RH and `λ_WD = sup λ_t` (Heat); odd sector carries every
failure (CHMD). Reach is quantified by Σ1c: the faces that use estimates stop at overlap
`(log N)^{1/19}` on fixed packets.

## U-Π — square-root precision of a one-sided source count

Core problem: an unconditional one-sided count at square-root precision, or an exact geometric object
whose Riemann–Roch delivers it.

| Face | Routes / programmes | Reduction |
|---|---|---|
| One-sided prime count | WL, PBM, RB, JAS, CTF, ACP, ASRP | `ψ(x) − x ≤ C√x log²x` (Π1) |
| Möbius / Mertens cancellation | MC, BVI, THIM, BSU | moving-scale half-power cancellation; 3/4 strip via near band (Π2, Π11) |
| Producers / auxiliaries | WL, AHA, ACS (Bézout) | parity-selective integer auxiliary (Π3) |
| Effectivity / sections | ACS, SPTL, AET | quadratic Hilbert–Samuel `h⁰` on the scaling surface (Π11) |
| Census / density | SRT (towers), IGP, Zeta23, Guth–Maynard | proportion and density of critical zeros (Π8) |
| Heat counts | WD, LA | `N(t)` growth (Σ5 ∩ Π) |
| Candidates | APF, EWJ, FEL, WBF, IRK | integral counts from a source lift |

Identities [L]: one-sided count ⇔ `κ = 0` (HKT); graded strip: section shortfall rate = zero width
(SPTL); five rate currencies (lag, deficit, band, damping, Birman–Schwinger) equal the zero width
(SSIC, ACCE); prime-error budget `≥ 2 + γ − log 4π` with equality ⇔ RH + simple (ACP).

## U-Γ — selection of ζ at the trivial gauge point

Core problem: a zero-independent, source-defined mechanism that distinguishes ζ from its twins and
gauges (Liouville twin, prime flips, Davenport–Heilbronn-type combinations).

| Face | Routes / programmes | Reduction |
|---|---|---|
| Typicality of the trivial point | MC, AGT, BAG, XN | RH ⇔ trivial gauge point typical; recurrence; Newton margin (Γ1) |
| Carriers with Weil dilation | SC, AKG, APD, MPG | finite-index carrier with visible successor (Γ7, Γ9) |
| Physical / native source action | PM, PW-B | zero-independent selection (Γ5) |
| Pre-divisor constructions | BSH, CDC, HJ, SEC, PCS, RFHM, DR, EWJ, APF, WBF | a section / potential defined before the divisor (Γ5) |
| Polarization | AP, CDG | Hecke invariance of the collided form (Γ4) |
| Function-field calibration | ACS (F₃), AKG (`𝔽_q[T]`), finite-field calibrations | what Frobenius supplies that ℤ lacks (Γ10) |

Identities [L]: index twin-blind (AKG); pole-index window selects (HKT); Weil extensions classified
by index (AKG); integer counting + full-cone positivity identifies `Λ` (RHTower).

## Cross-family seams

| Seam | Statement | Routes on the seam |
|---|---|---|
| Σ ∩ Π: reach ledger | estimate-based positivity reaches overlap `(log N)^{b/(a+14)}`; the residual saving exponent `b` is a precision exponent | HF, SRT, AIP, CHMD, ACS-atomic |
| Σ ∩ Π: finite index | `κ < ∞` ⇒ Lindelöf + zero-free half-plane | HKT, AKLT, SRT towers, CHMD index, WD tower |
| Σ ∩ Γ: running counterterm | positivity needs the horizon counterterm matched exactly; the pole-index window (width `2 log 2`) is where ζ and the twin separate | AKG, HKT, RAPT, SC |
| Π ∩ Γ: count precision | `Count(a)` iff `a − 1 ∈ 𝒬`; `Λ + 1/n` has Count iff RH but is never tower-positive | ACountP, SMAP, WL |
| Σ ∩ Π ∩ Γ: archimedean channel | the archimedean place is the only bridge between primes; archimedean continuity cannot coexist with height decay at finite index | AKG, ALG, CHMD (Gamma graph) |

## Route → core problem map

| Route | Core | Face |
|---|---|---|
| WL | Π | one-sided count, producers |
| RW | Σ | ground minimum |
| FU, CFC, RP, SZ, LI | Σ | scheduled prime sums |
| PA, TH, LA, HCF, GTA | Σ | rank / degree sign |
| MC | Π (Γ) | Möbius cancellation; typicality |
| TT | Σ | odd / directed covariance |
| TG | Σ | quantum |
| HF, SRT, AIP, ACT | Σ | complete atomic matrix |
| CHMD | Σ | Haar / Doob / odd sector |
| RN | Σ | realization |
| WD | Σ (Π) | heat flow, collision quantum |
| PM | Γ (Σ) | native source action |
| JAS, CTF, PBM, RB | Π | one-sided count |
| XN, BAG | Γ | typicality / recurrence |
| EWU, OWU | Σ (Γ) | ground minimum; selectivity |
| ACS | Π (Σ, Γ) | effectivity; atomic; Rosati |
| APF, EWJ, WBF, IRK | Γ (Π) | source lift with integral count |
| BSH, CDC, HJ, SEC, PCS, RFHM, DR | Γ | pre-divisor constructions |
| EGC, FEL, MSC | Σ | contour / likelihood / Sonin |
| PTR, W1C | Σ | realization |
| SC | Γ (Σ) | carriers with Weil dilation |
| PW-B | Γ | native source action |

## What a closing argument must supply

Over `𝔽_q` one object — the Frobenius graph on `C × C` — supplies all three: the Hodge index gives the
sign, Riemann–Roch gives the count, and the graph is canonical (no twin has it). Over ℤ the corpus has
each ingredient in isolation and no object that carries two of them:

| Needed | Present over ℤ | Missing |
|---|---|---|
| Positivity by identity | local shell decomposition (AKG), finite-sieve signature (RAPT), collided form `D ≥ 0` (AP) | an identity for the infinite assembly with running counterterm |
| Count from geometry | exact linear theta RR (AET), arithmetic Bézout | a quadratic Riemann–Roch on the scaling surface |
| Canonical selector | pole-index window, boundary sign | a conformal correspondence over ℤ whose factor is not archimedean size |
