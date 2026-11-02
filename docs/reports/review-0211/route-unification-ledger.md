# Route unification ledger — status quo

The 33 live routes and 16 candidates are faces of three core problems — **U-Σ** (sign), **U-Π**
(precision and production), **U-Γ** (selection). All three read one even integer
`κ = κ(K_ζ) = #` distinct zeros right of the critical line, and all three read it on one object: the
**window tower** `A ↦ W_A`, where `W_A` is Weil's form on tests supported in `[−A, 0]` and
`κ = sup_A ι(A)`. Eight unifications organize the routes:

- **One criterion.** Every sign face — positivity at every fixed multiple of the critical overlap, the
  restricted Weil minimum at every aperture, the glued index of the archimedean successor, the
  horizon layer, the odd/Markov capacity — is Weil's form on window tests of every length [L].
- **One finite object per length.** On a window of length `A` the form is the Gamma factor (constant
  `Ω(0)` and Lévy jumps), one fold per prime power `n ≤ e^A`, and the pole; the only negative
  arithmetic terms are the symmetric fold masses; the canonical class is the half-weighted Chebyshev
  profile at the two end distances [L]. Each window has finite, Shannon-bounded index and negativity
  confined to the poles and a finite frequency band [L].
- **One decomposition.** The complete atomic family splits into Tate pieces — bulk packets
  (`#ℙ⁷(ℤ/m)`) and twisted horizon windows (zero-blind, positive; conductor two = `#ℙ⁷(𝔽₂)` count [S])
  — and one non-Tate piece, the untwisted horizon windows, which carry Weil's window form [L].
- **One axis.** Window length `A` = log of the level `⌊e^A⌋` = twice the half-width of ACS/LST/RW =
  radius `½ log K` of the tests a critical multiple `K` synthesizes = time `t` of the window energy
  `|𝒵(t)|²` = log of the Landau height `T/2π` = the exponent of the window Frobenius multiplier
  `e^{−(s−½)A}` [L/D].
- **One budget.** The negativity of a window is at most its canonical degree `≈ 4e^{A/2}` plus the pole
  capacity [S]; the budget `e^{A/2}` is the trivial strip, its exponent is `Θ − ½` [D].
- **One gluing.** One rank-one gluing at the pole creates `μ` (Redheffer `det = M(N)` = nerve Euler
  characteristic = coprimality signature) and the extra negative square of the glued state; graded
  energies are positive cone sums of top-stratum energies, top energies Möbius-signed sums [L].
- **One function for selection.** `Λ(s)/Λ(s + 1)` carries the Hodge defect as band poles, is the
  Gauss–Mayer boundary `2ζ(s)/ζ(s + 1)`, and is the scattering coefficient of `SL₂(ℤ)\ℍ` [L/D]; on a
  window the same reflection is `σ_A`, unitary exactly on the line, orienting nothing by itself [S].
- **One missing fact.** Over `𝔽_q` one object — the Frobenius graph on `C × C` — gives sign, precision
  and selection, and every window of a curve lives in one `ℂ^{2g}`. Over `ℤ` every structural axiom of
  a window cohomology holds for every weight [L/S], no finite-rank object can carry the form [L/S], and
  the counts carry all but `½Q` [S]. Missing: a tower of rank `≈ 2e^A` carrying the primitive window
  `h¹` as a count — concretely, a count for the symmetric fold masses, uniformly in `A`.

Evidence: `[L]` integrated Lean; `[S]` working tree or not wired into its umbrella; `[D]` derived
here from Lean statements.

## 0. The one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ = #{ρ : Re ρ > ½}` (distinct), even; RH ⇔ `κ < 2`; carried by one two-prime Hecke orbit | HKT, AKLT, AOG, ACS [L] |
| Window index | `ι(A)` monotone, `0` for `A ≤ 3/5`, Shannon-bounded, `sup_A ι(A) = κ`; RH ⇔ `ι(A) < 2` ∀A | CWS `TheWindowIndex` [L] |
| Window form | `Q = Ω(0)‖H‖² + J_∞ + Σ_{n≤e^A}(Λ(n)/√n)(½fold_n − sym_n) + pole`; locality in `n ≤ e^A` | CWS [L] |
| Canonical class | `k_A(u) = ψ_{1/2}(e^{−u}) + ψ_{1/2}(e^{A+u})`; `deg K_A = 2ψ_{1/2}(e^A) − Ω(0)` | CWS [L] |
| Budget | `Q ≥ −(deg K_A + 2A sinh²(A/2))‖H‖²` | CWS [S] |
| Localization | `Q(f) ≥ −2|f̂(i/2)||f̂(−i/2)| − M_a sup_{|τ|≤τ₀(a)}|f̂|²` | AHD [L] |
| Bounded kernel | RH ⇔ `‖K_ζ(u)‖ ≤ Re K_ζ(1)` (Castelnuovo–Severi at rational scales) | RIT [L] |
| Coupling | RH ⇔ bounded coupling on one dense `⟨p⟩×⟨q⟩` ⇔ bounded Gaussian-damped coupling on one natural two-prime cone | ACPL [L] |
| Horizon layer | untwisted windows → `κ_φQ(H)` past the critical curve; RH ⇔ eventual `≥ −ε` | AHD [L] |
| Second order | `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²` for every regular profile | AHD [L] |
| Pencil / phase diagram | positive for `κ·windowFloor(A) ≤ βJ/K`; window index monotone in `K`, stabilizing at Weil's index | CWS [S], AHD [L] |
| Tate pieces | bulk `J(1)#ℙ⁷(ℤ/m)` (count law over every finite ring); twisted windows zero-blind and positive; conductor-two second order `7J(2)/K` | ADT, AHD [L/S] |
| Single schedule | every finite rational Gram is a compression limit at `2L(log L)²` | TM, RIT [L] |
| Glued state | `κ(φ_c) = κ + 1` at every place | AKG [L] |
| Gluing determinant | Redheffer `det = M(N)` = nerve `χ̃` | ADT, HWV [L] |
| Strata | graded = positive cone sum of top strata; top = Möbius-signed sum | ADT, HWV [L] |
| Markov form | jumps + creation potential + pole; departing jumps pay creation; pointwise calibration fails past the plastic root | RHTower, AHD, ACT-L [L] |
| Kähler package | RH ⇔ HL on the PSD locus | HWV [L] |
| Edge | crossing with zero mode; under ¬RH the edge sits in `[(log N)^{1/9−}, 2(log N)^{1/8+}]` infinitely often | EHT [L] |
| Realizations | RH ⇔ `ℓ²(zeros)` realization of every window; none finite-dimensional; no finite-rank realization of `K_ζ` | CWS [L], RIT [S] |
| Genus | window genus main term `2e^A` = Young conjugate = theta count | CWS [S] |
| Sections and counts | Künneth: counts pay all but `½Q`; Lévy count to length `1/1000`; Stepanov over `𝔽_q` | LST [L], CWS [S] |
| Heights | windowed Tate law; generic two-prime orbit decides by an `ℕ`-count height; fakes have none | CWS [S], AE [L] |
| Frobenius at infinity | `σ(ρ) = 1 − ρ̄`; window form `e^{−(s−½)A}Ĥ(1−s)`; Hecke similitude; partner saturation | EHT, PL, RHTower [L], CWS [S] |
| Intertwining coefficient | `Λ(s)/Λ(s+1)`: band poles = Hodge defect; Mayer boundary; scattering coefficient; contractive positivity blind | RIT [L] |
| Window energy | `|𝒵(t)|²`; abscissa = 2·maximal depth; certificate depends only on it | CDG [L] |
| Hecke defect | means ↔ near-line density rates | CDG [L] |
| Heat | `κ(φ_c^{(t)}) − 1 = N(t)/2` | AKG, RIT [L] |
| Künneth | `κ(K_ζ⊠K_ζ) ∈ {0, ∞}` | RIT, EHT [L] |
| Selection | every prime-set flip separated; complete degeneration only for `Λ`; no bounded window, no density law, no contraction selects | RIT, ADT, BGG [L], CWS, ACPL [S], RIT [L] |

The three walls are the three ways a reading of the tower fails:
- **Σ**: at each length the sign is a finite question; no mechanism pays the symmetric fold masses at
  every length.
- **Π**: the negativity of windows is controlled only by the trivial budget `e^{A/2}`; the
  classical precision faces are growth statements in `A`; no count produces the primitive window `h¹`.
- **Γ**: local data, densities and contractions are blind; selection is a law in `A`, the reflection
  acting as a positivity.

## 0.1 The window axis

| Coordinate | Reading at window length `A` | Anchor |
|---|---|---|
| Window test | `H` on `[−A, 0]`; folds `T_n`, `n ≤ e^A` | CWS [L] |
| Stage | `log n ≤ A < log(n+1)`: prime-free below `log 2`; one fold `T₂` up to `log 3` | CWS [L] |
| Known sign | all tests `A ≤ 3/5`; odd `A ≤ 0.724`; `cosh`-orthogonal `A ≤ log 2 + 1/50`; Lévy count `A ≤ 1/1000` | ACS, LST [L] |
| `{∞,2}` trace | exact through `A = log 3` (half-width `½ log 3`) | SP [L] |
| Canonical degree | `2ψ_{1/2}(e^A) − Ω(0) ≈ 4e^{A/2}` | CWS [L] |
| Index | `ι(A) ≤ ⌊1 + 2A·T(A/2)/π⌋` | CWS [L] |
| Frequency band | negativity only for `|τ| ≤ τ₀(A/2)` | AHD [L] |
| Genus | `≥ (2 − η)e^A` + multiplicity excess; main term `2e^A` | ACS [L], CWS [S] |
| Landau height | `2πe^A` (Young maximizer) | CWS [S] |
| Critical multiple | a multiple `K·c*` synthesizes tests of length `≈ log K`; pencil positive while `κ·windowFloor(A) ≤ βJ/K` | TM [L], CWS [S] |
| Window energy | `t ↔ A`: off-line depth `δ` grows like `e^{δA}` | CDG [L], [D] |
| Restricted minimum | `μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})` (half-width convention) | ArithmeticCompensationTheory [L] |
| Over `𝔽_q` | windows realized in `ℂ^{2g}`; genus saturates at `2g` | CWS [S] |

Each fixed window length is a sub-RH, finite problem; all lengths together are RH.

## 0.2 The degeneration dictionary

| ADT/AHD object | Statement | Classes reading it |
|---|---|---|
| Variation over `(c, N)` | complete Weil matrices; overlap multiple = window length | C1 |
| First order | `J(m) = J(1)#ℙ⁷(ℤ/m)`; count law over every finite ring; tensor law CRT | C1, C12 |
| Monodromy | eventually idempotent; one branch per prime | C12 |
| Bulk ledger | every zero enters fixed packets through a positive pole weight | C1 |
| Twisted horizon windows | zero-blind, positive, coercive; conductor two = `#ℙ⁷(𝔽₂)` count | C1, C15 |
| Untwisted horizon windows | Weil's window form; at the critical curve plus `7J(1)/K` count | C1, C4, C15 |
| Pencil | positive at bounded `K` on bounded windows; index monotone in `K` | C1, C3 |
| One negative square | the pole gluing; Redheffer `det = M(N)` | C2, C7, C12 |
| Selection by degeneration | `F_λ = 0` only for `Λ` | C8 |

## 1. Equivalence classes of routes

Routes in one class compute the same quantity; a theorem in one class transfers through the listed
identity.

| Class | Common quantity | Routes | Identity joining them |
|---|---|---|---|
| C1 Weil's window form | `Q ≥ 0` on windows of every length; untwisted horizon layer | HF, SRT, AIP, ACT, ACS-atomic; RW, EWU, OWU, MSC, FEL; ADT/AHD | window ⇔ horizon ⇔ every `K·c*` ⇔ Beurling schedule ⇔ `ι = 0` [L] |
| C2 Glued state | `κ(φ_c) − 1` on the boost hyperplane | SC, AKG, RIT-Künneth | Grams are compressions on the Beurling schedule [L] — face of C1 |
| C3 Window integer | collision charge, heat count, window index | WD-charge, SC-heat, LA-heat, TG, HEF | index = Wiener–Hopf index = growth of `|𝒵(t)|²` [L] — face of C11 |
| C4 Odd / Markov sector | `R ≤ ½`; sinh capacity; window Markov capacity | CHMD, TT, AID, SAHT | Markov hyperplane = `v₁^⊥`; signed folds [L] — face of C1 |
| C5 Rank / degree | Laguerre–Pólya property | TH, HCF, PA, GTA, LA-Jensen; ART | inertia counts off-line pairs at matched rank [L/D] |
| C6 Scheduled prime sums | lower bound of a scheduled energy | FU, CFC, RP, SZ, LI, FEL, EGC | explicit-formula functionals bounded below ⇔ RH [L] |
| C7 One-point precision | `ψ − x`, `M(x)`, windowed prime error, coupling, Redheffer determinant | WL, MC, PBM, RB, JAS, CTF, SC-coupling | `Count(a)` iff `a − 1 ∈ 𝒬`; coupling ≡ kernel; `χ̃ = −M(N)`; canonical class = `ψ_{1/2}` profile [L] |
| C8 Selection / typicality | trivial gauge point | MC-typicality, BAG, XN | RH ⇔ trivial point typical [L] |
| C9 Realization | spectral reality of a constructed operator | RN, PTR, W1C, PM-Mayer | no finite realization; tower forced [L/S] |
| C10 Pre-divisor | a section defined before the divisor | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF | zero-independent forcing (Γ5) |
| C11 Local zero location | window power sums, Hecke defect, near-line density, census, mollified log-mean | WD-energy, WD-Hecke, census, HEF, SRT-local, IGP, TTPC | abscissa = 2·depth; density ladder; positivity cannot reach `3/4`; moments cannot fix the log-mean [L] |
| C12 Hodge–Lefschetz / gluing | HL on the positive locus; top gcd stratum | HF-Hodge, ACS-Hodge, RIT, EHT, TG | Liouville = HL; graded/top Möbius pair [L] |
| C13 Sections, correspondences, heights | count-valued primitive `h¹`; naive height | ACS-effectivity, HF-RR, RIT quadratic RR, IRK, AE | Künneth `h¹`; Rosati ⇔ naive height; windowed Tate law [L/S] |
| C14 Intertwining coefficient | poles of `Λ(s)/Λ(s+1)`; `SL₂(ℤ)` resonances | PM-scattering, HF band poles, resonant partners, PW-B survivor, W1C | band poles = Hodge defect; contraction blind [L] |
| C15 Window tower | `W_A` as a cohomology: canonical class, Serre duality, index, genus, heights, counts | CWS; meets C1, C4, C13, C14 | signed folds; Künneth form; Tate/non-Tate split [L/S] |

C1, C2, C4 are one quantity, Weil's window form. C15 is the same quantity organized as a tower with
its cohomological structure; it is where C1 (sign) and C13 (counts) meet and where C14 reappears as
the window involution. C3 is a face of C11, and C11 is the growth of window negativity in `A`. C5 and
C6 are sign problems on test families that become RH-complete only in the limit of rank, degree or
schedule. C7 and C11 are precision faces; C13 is the production face; C8–C10 and C14 are selection
faces.

## U-Σ — Weil's window form

Core problem: the window form is nonnegative at every length. Equivalent forms: every fixed
multiple of the critical overlap; horizon layer; Beurling schedule; `ι(A) = 0` ∀A; window Markov
capacity; HL on the positive locus; `μ(A) ≥ 0` ∀A [L].

| Layer | Status | Anchor |
|---|---|---|
| Receivers | window, horizon, schedule, `K·c*`, window index | CWS, AHD, RIT, TM [L] |
| Window structure | locality, folds, canonical class, stages, signed folds | CWS [L] |
| Budget and localization | canonical-degree floor; low-frequency localization; pencil | CWS [S], AHD [L] |
| Degeneration | Tate pieces + untwisted Weil piece | ADT, AHD [L/S] |
| Inherited regime, tilted spline | all vectors `α < 1/9`; three coercive pieces below `1/8`; join open | CACT, ADT [L] |
| Inherited regime, general profiles | universal-rate positivity on polynomial spans at `log log N`; super-log-log on subpolynomial spans; logarithmic profile to `ε₀·c*` | CACT, TM [L] |
| Small windows | all tests `A ≤ 3/5`; odd and `cosh`-orthogonal past `log 2`; `{∞,2}` trace through `log 3`; pointwise Markov fails at `½ log 2`, `½ log 3` | ACS, LST, SP, ACT-L [L] |
| Kähler package | HL on the PSD locus is RH | HWV [L] |
| Stars and strata | descent; graded/top Möbius pair | HWV, ADT [L] |
| Edge | crossing with zero mode | EHT [L] |

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, ACS-atomic, CACT, CAF, RAPT, SSH, SSHA, CSAR, ACPL, TM, ADT, AHD | untwisted horizon windows = window form; Tate pieces counts |
| Aperture ground minimum | RW, EWU, OWU, MSC, CFC, SP | window sign by stages; next: prime-free gap, then `sym₂` |
| Glued state | SC, AKG | Beurling-schedule sign |
| Markov / odd sector | CHMD, AID, SAHT, TT, ACT-L | nonlocal window capacity |
| Window cohomology | CWS | count for `sym_n` uniformly in `A` |
| Edge / zero modes / Kähler | EHT, HWV, RW | HL on the PSD locus |
| Stars / gluing | HWV, CSAR, ADT | top gcd stratum |
| Effectivity / RR | ACS, LST, RIT, HF, AE | count for the primitive `h¹` (U-Π production) |
| Rank / degree / approximation | TH, LA, HCF, PA, GTA, ART | Laguerre–Pólya |
| Scheduled prime sums | FU, CFC, RP, SZ, LI, FEL, EGC | scheduled energy lower bound |
| Paths | TG, SC, EHT, ACPL, HWV | source-defined HL along a flow |
| Realization | RN, PTR, W1C | tower of unbounded rank |
| Künneth / powers | RIT, EHT | closed: RH-equivalent at every degree |

## U-Π — precision and production

Core problem: an unconditional exact statement about primes or zeros at local precision, and a count
producing the window `h¹`. Six forms:
- the one-point windowed prime error (kernel, coupling, one-sided count; its damped form on the cone);
- the growth of window negativity in `A` (budget `e^{A/2}` = trivial strip);
- windowed zero power sums (window energy; window integer);
- the conjugate diagonal ↔ near-line density ladder, and the mollified log-mean;
- the signed pair information beyond bandwidth one;
- a count whose primitive `h¹` is the window form (production), carried by a tower of rank `≈ 2e^A`.

| Face | Routes / programmes | Reduction |
|---|---|---|
| One-sided prime count | WL, PBM, RB, JAS, CTF, ACP, ASRP | `ψ(x) − x ≤ C√x log²x` (Π1) |
| Windowed kernel / coupling | SC, ACPL, AKG, HKT | bounded `K_ζ` ⇔ bounded dense coupling ⇔ bounded damped cone coupling (Π4, Σ17) |
| Integer producers | WL, AKLT, AHA | `ε`-uniform producer (Π3) |
| Möbius / nerve | MC, BVI, CAF, HWV, ADT | half-power cancellation; `χ̃ = −M(N)` (Π1, Π2, Π10) |
| Window budget | CWS, all window routes | negativity growth exponent `Θ − ½` (Σ28) |
| Window energy | WD, TG, CDG | subexponential `|𝒵(t)|²` (Π17) |
| Conjugate diagonal / log-mean | WD, CDG, RBG, HEF | near-line density; moments insufficient (Π5, Π19) |
| Census | SRT, IGP, Zeta23, CDG, TTPC | signed information beyond bandwidth one; positivity insufficient (Π7) |
| Sections / heights | ACS, LST, AOG, AET, AE, RIT, SPTL, CWS | count for the primitive window `h¹`; generic two-prime `ℕ`-count (Π11h) |
| Finite realizations | RIT, CWS | no-go: tower forced (Π18) |
| Genus | ACS, RHTower, LST, CWS | main term `2e^A`; upper law open (Π16) |
| Exceptional moduli | MC, CACT, CAF | beyond `(log x)^A` (Π9) |
| Averages vs heights | WD, LA, SRT | density-zero exceptions (Π6) |
| Subconvexity / heat | LA, WD, AHA | floors `133/200`, `2/3` (Π12) |
| Candidates | APF, EWJ, FEL, WBF, IRK | integral counts from a source lift |

Identities [L]: one-sided count ⇔ `κ = 0`; coupling rate = zero width (damped cone included); window
energy abscissa = twice the maximal depth; the canonical class is the half-weighted Chebyshev profile;
dyadic Hecke means ⇔ near-line density rates; Künneth `h¹` = counts + `½Q`; Rosati positivity ⇔ naive
height; the first-order term of the degeneration is a point count over every finite ring.

## U-Γ — selection of ζ

Core problem: a source-defined mechanism that distinguishes ζ from its twins and produces positivity.
The distinguishing half is closed for every prime-set flip at every density. The producing half is
Frobenius at infinity: the reflection `ρ ↔ 1 − ρ̄` acting as a positivity, read by `Λ(s)/Λ(s+1)`, by
Rosati positivity, and on windows by `σ_A`. Selection is a law in `A`.

| Face | Routes / programmes | Status / reduction |
|---|---|---|
| Typicality of the trivial point | MC, AGT, BAG, XN | RH ⇔ trivial point typical (Γ1) |
| Gluing of the global pole | SC, AKG, RIT | classified (Σ11, Γ11) |
| Margin, index, edge, degeneration selection | RIT, ACP, HKT, EHT, ACPL, RAPT, ADT, BGG | flips separated at every density; only `Λ` degenerates completely (Γ2, Γ12, Γ18) |
| Window selection | CWS | bounded windows blind; law in `A` (Γ20) |
| Density selection | ACPL | RvM-count countermodels (Γ21) |
| Intertwining coefficient | PM, RIT, RHTower | band poles = Hodge defect; contraction blind (Σ19, Γ22) |
| Frobenius at infinity | PL, CDG, RBG, EHT, AOG, AET, CWS | defect involution; Hecke similitude; Rosati; window involution (Γ4, Γ19) |
| Physical / native source | PM; PW-B retired | source-uniform extinction no-go; recentering impossible (Γ13, Γ17) |
| Pre-divisor constructions | BSH, CDC, HJ, SEC, PCS, RFHM, DR, EWJ, APF, WBF | zero-independent forcing (Γ5) |
| FE twins | SelbergClass | off-line real zeros (Γ15) |
| Function-field calibration | ACS, AKG, RIT, EHT, ACPL, LST, HWV, AET, AHD, CWS | local walls and first-order counts identical; `ℤ` differs by infinite genus, no finite realization, disconnected links (Γ10) |
| Selection → sign | all selectors | no selector gives positivity (Γ16) |

## 2. Cross-family seams

| Seam | Statement | Routes on the seam |
|---|---|---|
| Σ: one criterion | every complete-family receiver is the window criterion | HF, SRT, AIP, ACT, RW, EWU, OWU, SC, AHD, CWS [L] |
| Σ: one object per length | window = Gamma factor + `n ≤ e^A` folds + pole; negative terms `Ω(0)`, `sym_n`, odd pole | CWS, LST, RW [L] |
| Σ: one decomposition | Tate pieces (bulk, twisted windows) + untwisted Weil piece | ADT, AHD [L/S] |
| Σ: one axis | window length = level = radius `½ log K` = active primes | AHD, TM, RW, LST, CWS [L] |
| Σ ∩ Π: one budget | canonical degree `≈ 4e^{A/2}` = trivial strip; exponent = `Θ − ½` | CWS [S], [D] |
| Σ ∩ Π: phase diagram | pencil positive at bounded `(A, K)`; RH at `A, K → ∞` | CWS [S], AHD [L] |
| Σ: one hyperplane | glued index, complete sign, Markov criterion, Hodge index on `v₁^⊥` | SC, HF, SRT, AIP, ACS, CHMD, RIT, HWV |
| Σ: inherited regime | estimates live below the critical exponent; whole-space `1/8` is a join | CACT, ADT, TM [L] |
| Σ: nonlocal payment | pointwise Markov calibration fails at the first two primes; Schur squares survive | ACT-L, RW, AIP [L] |
| Σ ∩ Π: one gluing | Redheffer, nerve `χ̃`, coprimality signature, glued index | ADT, HWV, AKG, MC [L] |
| Σ ∩ Π: strata | graded = positive cone sum of top strata | ADT, HWV [L] |
| Σ ∩ Π ∩ Γ: counts and towers | Künneth counts pay all but `½Q`; no finite realization; tower rank `2e^A`; naive height ⇔ sign | CWS, LST, AE, AET, ACS, RIT [L/S] |
| Π: window integer = window power sum | collision charge = Wiener–Hopf index = growth of `|𝒵(t)|²` | WD, TG, SC-heat [L] |
| Π: window length = window time | `e^{(s−½)A}` (window multiplier) and `e^{t(z−½)}` (window energy) | CWS, CDG [D] |
| Π: precision ladders | Hecke means ↔ density rates; census beyond bandwidth one; log-mean beyond moments | WD, CDG, TTPC, IGP [L] |
| Π: means vs heights | density statements cannot exclude density-zero clusters | WD, LA, SRT, RW, census |
| Σ ∩ Π: kernel = coupling = window error | bounded kernel, bounded dense coupling, bounded damped cone coupling, window PNT at `√` precision | SC, ACPL, EHT, WL, HKT |
| Σ ∩ Π: conductor levels | Siegel–Walfisz range; above `√N` Elliott–Halberstam type | CACT, CAF, MC |
| Σ ∩ Γ: one function | `Λ(s)/Λ(s+1)` = Hodge defect poles = Mayer boundary = modular scattering | RIT, PM, RHTower [L/D] |
| Σ ∩ Γ: Frobenius at infinity | reflection vs conjugation; Rosati; naive height; window involution | EHT, PL, CDG, HF, PM, AOG, AET, CWS |
| Γ: blind selectors | bounded windows, densities, contractions, local twists | CWS, ACPL, RIT, AKLT [L/S] |
| Σ: approximation | RH-true approximants close into Laguerre–Pólya | ART, W1C, PTR, LA, TH |
| Γ: selection without sign | every selector is a margin, index, counterterm or identity | RIT, ACP, ACPL, ALG, AES, EHT, HWV, ADT, BGG |
| Σ: paths | crossing-free deformation ⇔ positivity | TG, SC, WD, EHT, ACPL, HWV |
| Archimedean channel | Lévy jumps, `Ω(0)`, the prime-free stage, couplings of coprime atoms, the finite divisor | AKG, ALG, CHMD, RIT, ACPL, HWV, ACS, LST, ADT, CWS |

## 3. Route → core map

| Route | Core | Class | Face |
|---|---|---|---|
| WL | Π | C7 | one-sided count; canonical class as cumulative Chebyshev |
| RW, EWU, OWU | Σ (Γ) | C1, C15 | window sign by stages |
| FU, CFC, RP, SZ, LI | Σ | C6 | scheduled prime sums |
| PA, TH, LA, HCF, GTA | Σ | C5 | Laguerre–Pólya |
| MC | Π (Γ) | C7, C8 | Möbius cancellation; Redheffer; typicality |
| TT | Σ | C4 | odd / directed covariance |
| TG | Π, Σ | C3, C12 | window integer; HL along paths |
| HF | Σ (Π, Γ) | C1, C12, C13, C14, C15 | complete family = Tate pieces + window form; Kähler; correspondences; band poles |
| SRT, AIP, ACT | Σ (Π) | C1 | complete atomic matrix; window-pencil index |
| SC | Σ, Π (Γ) | C2, C7, C3 | glued state; damped cone coupling; heat |
| CHMD | Σ | C4, C1 | odd sector; window Markov capacity |
| RN | Σ | C9 | realization |
| WD | Π (Σ) | C3, C11 | window energy; Hecke defect; log-mean |
| PM | Γ (Σ) | C9, C14 | Mayer realization; scattering; reflection missing |
| JAS, CTF, PBM, RB | Π | C7 | one-sided count |
| XN, BAG | Γ | C8 | typicality / recurrence |
| ACS | Π (Σ, Γ) | C13, C1, C12, C15 | primitive `h¹` count; naive heights; genus; curve calibration |
| APF, EWJ, WBF, IRK | Γ (Π) | C10, C13 | source lift with integral count |
| BSH, CDC, HJ, SEC, PCS, RFHM, DR | Γ | C10 | pre-divisor constructions |
| EGC, FEL, MSC | Σ | C6, C1 | contour / likelihood / Sonin |
| PTR, W1C | Σ (Γ) | C9, C5, C14 | realization; faithful divisor |
| PW-B (retired) | Γ | C14 | survivor = scattering receiver |

## 4. What a closing argument must supply

| Needed | Present over `ℤ` | Missing |
|---|---|---|
| Sign of the window form | criterion; finite structure per length; signed folds; budget; low-frequency localization; positivity to `A = 3/5`, partial past `log 2` | a mechanism paying `sym_n`, `|Ω(0)|` and the odd pole at every length — a count (B42), a nonlocal capacity (B37), or an identity (B6) |
| Full-space structure | Tate pieces identified; untwisted windows = Weil; pencil | general conductors and cross-terms (B2) |
| Uniformity in `A` | each length finite and decidable; phase diagram at bounded `(A, K)` | a law in `A` (growth exponent of window negativity, B43) |
| Nondegeneracy (HL) | Kähler transport; Liouville = HL | HL on the positive locus |
| Gluing | gcd stratification; two-prime cyclic orbit carries the defect | global payment of the top stratum |
| Precision | one-sided count ⇔ RH; window energy ⇔ local zero location; producers to the main term; Hecke means to rate `< 1` | square-root windowed prime error; subexponential window energy; log-free near-line density; signed pair data beyond bandwidth one |
| Count from geometry | first order = `#ℙ⁷(ℤ/m)` over every finite ring; Künneth counts pay all but `½Q`; windowed Tate law; generic two-prime `ℕ`-count criterion | a tower of rank `≈ 2e^A` carrying the primitive window `h¹` as a count |
| Canonical selector | flips separated; complete degeneration; faithful scattering divisor; window involution with multiplier unitary on the line | the reflection acting as a positivity (Rosati, Hecke similitude, Krein structure on period functions) |
| Integrality with homotopy invariance | collision charge as Wiener–Hopf index; window index `ι(A)` | a structural bound on window negativity growth |
