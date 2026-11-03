# Route unification ledger — status quo

The 33 live routes and 16 candidates are faces of three core problems — **U-Σ** (sign), **U-Π**
(precision and production), **U-Γ** (selection and reflection). All three read one even integer
`κ = κ(K_ζ) = #` distinct zeros right of the critical line, and all three read it on one object: the
**window tower** `A ↦ W_A`, Weil's form on tests supported in `[−A, 0]`, a translation-invariant form
acted on by the Dirichlet ring truncated at `⌊e^A⌋`, with `κ = sup_A ι(A)`. The unifications:

- **One criterion.** Every sign face — every critical multiple of the complete family, the restricted
  Weil minimum, the glued index, the horizon layer, the odd/Markov capacity, the fold capacity, Mayer
  Krein positivity, prime-blind positivity, archimedean domination at dimension zero — is Weil's form on
  window tests of every length [L].
- **One algebra.** The arithmetic of a window is a finite local λ-ring: `ζ ≡ exp(Λ/log) ≡ exp Σ_aψ^a(P)/a`,
  `ρ_A(Λ) = [M, log Z]`, Hilbert function `π_k(N)`, Gorenstein only below `log 3`, no internal
  Frobenius [L].
- **One graph.** On finite configurations of `ℚ_{>0}` the window arithmetic form is the Hecke operator of
  `ℤ[ℚ^×_{>0}]`; folds count multiplicative pairs; horizons are thresholds of rational Hecke graphs [L].
- **One family, classified at its wall.** The Tate family `k ↦ ρ_A(J_k)` (counts of `𝔸^k∖0`) has Weil's
  arithmetic term as its derivative at `k = 0`. Positive dimension carries no positivity that reaches
  `k = 0`: bare domination ⇔ Weil sign; archimedean families fail; Tate positivity is not uniform; the
  completed family is unimodular on the line; the wall `k ↦ −k` is Dirichlet inversion [L].
- **One decomposition.** At the critical curve the complete family is Weil's form on untwisted windows
  plus positive counts on every twisted direction (Ramanujan, periodic, frequency, character) [L].
- **One angle dictionary.** A twist frequency `u` over `ℤ` contributes the Hurwitz form a Frobenius angle
  `u` contributes over `𝔽_q`; a pure curve's family is a sum of such squares at every resolution; the
  untwisted window is the trivial angle, where the Hurwitz form is singular and Weil's form sits [L].
- **One location.** A new fold couples only the two collars of the window; the stage step is a block
  inequality on two-collar data; frozen forms are indefinite, so the new fold is a positive source [L/D].
- **One axis.** Window length `A` = log of the level = twice the half-width of RW/LST/ACS = radius
  `½log K` of the tests a critical multiple `K` synthesizes = time of the window energy = log of the
  Landau height = exponent of the window Frobenius multiplier = logarithmic coordinate of `H_LP` [L/D].
- **One horizon.** Every soft deformation paid by the counts (Tate dimension, critical multiple, floor)
  has horizon `≍ 1/deg K_A ≍ e^{−A/2}`; the exact margin is doubly exponential [L/D].
- **One reflection.** `σ_A` is the Rosati involution of the window algebra; on Lewis periods the
  reflection is the Hilbert adjoint `I_{1/2−s̄}`; `U_LP` identifies the two up to conjugation and an
  exponential twist; no linear isometry identifies Serre duality with the Krein reflection [L].
- **One point and one cone.** The Weil cone is `{Λ}` or empty; its nonemptiness is prime-blind,
  node-critical and equal to zero-side positivity on blind tests [L].
- **One density statement and one mode.** Log-mean, mollified log-mean, horizontal moment, critical-scale
  clustering and Hecke readings are one statement [L]; one cyclotomic mode carries the zero exponent [L].
- **One gluing.** One rank-one gluing at the pole creates `μ` (Redheffer `det = M(N)` = nerve Euler
  characteristic) and the extra negative square of the glued state [L].
- **One missing fact.** Over `𝔽_q` one object — the Frobenius graph on `C × C` — gives sign, precision
  and selection; the Frobenius angles are unitary, so the complete family of a curve is a sum of squares
  at every resolution. Over `ℤ` every structural axiom of the tower holds for every Euler datum, no
  finite carrier exists, positive dimension descends nothing, the window algebra has no Frobenius, and
  Weil positivity has no slack. Missing: an exact positivity of unbounded rank on two-collar data that
  survives each prime kick — equivalently a positive ground state of the window jump process at every
  length, or a Rosati-type positivity of the window reflection.

Evidence: `[L]` Lean in the corpus; `[W]` uncommitted working tree; `[P]` paper; `[D]` derived here.

## 0. The one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ = #{ρ : Re ρ > ½}` (distinct), even; RH ⇔ `κ < 2`; carried by one two-prime Hecke orbit | HKT, AKLT, AOG, ACS [L] |
| Window index | `ι(A)` monotone, `0` for `A ≤ 3/5`, `≤ 1` on smooth windows below `log 2 + 1/50`, Shannon-bounded, `sup_A ι(A) = κ` | CWS, AHD [L] |
| Window algebra | truncated Dirichlet λ-ring; small extensions, socle, Loewy length, Hilbert function `π_k(N)`; `ρ_A(Λ) = [M, log Z]` | WTZ [L] |
| Window form | `Q = Ω(0)‖H‖² + J_∞ − 2⟨ρ_A(Λ)H,H⟩ + ½⟨c,H⟩² − ½⟨s,H⟩²` = signed folds = signed count | CWS, WTZ [L] |
| Tate jet | `Q = Ω(0)τ_H(0) − 2τ′_H(0) + J_∞ + pole`; `J_k ≡ exp(ℓ(n^k − 1))`; jets generated by `M`, `ρ_A(Λ)` | WTZ, DZG [L] |
| Dimension zero | bare domination ⇔ `Q ≥ 0`; no archimedean family dominates uniformly; horizon `≤ C exp(−exp(A−2))`; Euler-product pole weight forced | DZG, ATD [L] |
| Hecke graph | window arithmetic on `S ⊂ ℚ_{>0}` = Hecke operator of `ℤ[ℚ^×]`; Barta and Picone certificates | WTZ [L] |
| Stage transfer | `Q = Q_N − 2w c_H(log(N+1))` on the left collar; ground-state identity for every weight | WTZ, DZG [L] |
| Two collars | positivity at stage `N+1` ⇔ `S^N_ε − w(J + J*) ⪰ 0` given interior positivity | [D] |
| Frozen form | indefinite at the first prime stage; frozen odd form negative only along one cubic moment on the unit window | WTZ [L/W] |
| End profile | `Q ≥ ∫V_A H² + pole`; windows `≤ 1/7` positive by exit charge | WTZ [L] |
| Floor | `Q ≥ −(deg K_A + 2sinh(A/2) − A)‖H‖²`; window floor `−(10 + 72e^{A/2})` | WTZ, ACS [L] |
| Base | all real C² tests positive to total length `≈ 0.7243` | SP, AIP, ATD [L] |
| Exponent | negativity rate of two-bump tests = supremum of zero depths | SRT [L] |
| Bounded kernel / coupling | RH ⇔ bounded dense two-prime coupling ⇔ bounded damped cone coupling; undamped ⇒ RH or unattained width | RIT, ACPL [L] |
| Complete family | PD below `(log N)^{1/8}`; at the critical curve Weil on untwisted windows + positive counts | CACT, AHD [L] |
| Bulk | zeros below `N^θ` read only the archimedean genus `2 + γ − log 4π` at the pole | AHD [L] |
| Glued state | `κ(φ_c) = κ + 1` at every place | AKG [L] |
| Gluing determinant | Redheffer `det = M(N)` = nerve `χ̃` | ADT, HWV [L] |
| Kähler package | RH ⇔ HL on the PSD locus; zero modes = radical, touching both collars | HWV, DZG [L] |
| Realizations | no finite-dimensional window realization; no finite-rank realization of `K_ζ` | CWS, RIT [L] |
| Weil cone / PBAP | `⊆ {Λ}`; nonempty ⇔ PBAP; node-critical; Farkas at each level; zero-side identity | RHTower [L] |
| Reflection | `σ_A` Rosati; window similitudes scalar; Lewis adjoint; Krein positivity ⇔ RH; no linear Serre–Krein isometry | WTZ, DZG, RIT [L] |
| Window energy | abscissa = 2·maximal depth; port decomposition; caps to `σ_m`; polynomial stage ⇔ RH | CDG [L] |
| Near-line density | eight forms; occupancy ⇔ almost-all certificates | CDG [L] |
| One mode | first cyclotomic band energy abscissa `2Θ` | CAF [L] |
| Angles | `𝔽_q` angle ≡ `ℤ` frequency; pure curves sums of squares; golden fake exponential monodromy | AHD [L] |

The three walls are the three ways a reading of the tower fails:
- **Σ**: at each length the sign is a finite question with doubly-exponentially small margin; entrances
  are paid pointwise; the frozen form is indefinite, so each prime kick must be a positive source on
  two-collar data, exactly, uniformly in the stage.
- **Π**: the arithmetic term is the dimension-zero derivative of counts, and positive dimension descends
  nothing; precision is one Fourier mode at square-root size; nothing produces the window `h¹` by an exact
  identity of unbounded rank.
- **Γ**: the reflection exists on both sides; the window algebra has no Frobenius; positivity of the
  reflection is RH; selection after positivity is a theorem.

## 0.1 The window axis

| Coordinate | Reading at window length `A` | Anchor |
|---|---|---|
| Window test | `H` on `[−A, 0]`; folds `T_n`, `n ≤ e^A` | CWS [L] |
| Algebra | Dirichlet λ-ring mod `I_{⌊e^A⌋}`; Hilbert function `π_k`; socle `(N/2, N]` | WTZ [L] |
| Stage | `log n ≤ A < log(n+1)`; collars of width `ε = A − log n`; entrance paid by `Ω(ε) ≥ log 3` | WTZ [L] |
| Known sign | all tests `A ≤ 0.7243`; exit charge `A ≤ 1/7`; odd tests on `[−0.347, 0.347]`; odd prime-free by count | SP, AIP, WTZ, LST [L] |
| Tate horizon | `log₂(1+2√2)` (stage 1), `1.19966…` (stage 2), `≍ e^{−A/2}` | WTZ [L/N] |
| Index | `≤ 1` below `log 2 + 1/50`; `≤ ⌊1 + 2A·T(A/2)/π⌋` | CWS, AHD [L] |
| `{∞,2}` trace | exact through `A = log 3` | SP [L] |
| Canonical degree | `2ψ_{1/2}(e^A) − Ω(0) ≈ 4e^{A/2}` | CWS [L] |
| Floor | `≤ −Ω(0) + (4A+1)e^{A/2}` | WTZ [L] |
| Critical multiple | `K*(H) ≥ βJ/(κ(10 + 72e^{A/2}))`; a multiple `K` synthesizes tests of radius `½log K − O(1)` | AHD, EHT [L] |
| Frequency band | negativity only for `|τ| ≤ τ₀(A/2)` | AHD [L] |
| Genus / rank | genus `≥ (2−η)e^A`; atomic lattice rank `⌊e^A⌋` | ACS, WTZ [L] |
| Ground energy | `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})`; domination horizon on Riemann's kernel `≤ C exp(−exp(A−2))` | M, ATD [L] |
| Window energy | off-line depth `δ` grows like `e^{δA}` | CDG [L/D] |
| Mayer coordinate | `a = e^u` in `H_LP`; `I_s` ↦ window multiplier | RIT [L] |
| Hecke translation | `T_p − Id`: window `A` → window `A + log p`, similitude factor `p` | RIT [L] |
| Over `𝔽_q` | windows realized in `ℂ^{2g}`; base change exact; angle-weighted sums of squares | CWS, WTZ, AHD [L] |

Each fixed window length is a sub-RH finite problem; all lengths together are RH.

## 0.2 The degeneration and angle dictionary

| Object | Over `ℤ` | Over `𝔽_q` | Classes |
|---|---|---|---|
| Resolution axis | overlap `c`, `c⁸ ≍ K log N` | atom width `w`, overlap `w/log q` | C1 |
| First order | `J(1)#ℙ⁷(ℤ/m)` over every finite ring | narrow-width span Gram | C1, C13 |
| Twisted direction | frequency `u`: `½(ζ(β+1,u) + ζ(β+1,1−u))`, positive | angle `θ_i`: shifted lattice spectrum `S_θ`, positive | C1, C18 |
| Ramanujan / character | `J_{β+1}(m)`; count `± L(s,ψ̄²)` | — | C1 |
| Trivial direction | untwisted window: `κQ(H) + (βJ/K)‖H‖²` | real eigenvalue `β = 1`: main term `(∫φ)²/a` | C1, C18 |
| Bulk | zeros read statistically; below `N^θ` only the archimedean genus | angles read individually | C1 |
| Degeneration type | complete degeneration selects `Λ`; flips indefinite | pure: complete; golden fake: exponential monodromy | C8, C18 |
| Polarization | inherited on twisted, short, cosh-hyperplane, sub-`K₀(A)` sectors | every resolution | C1 |

## 1. Equivalence classes of routes

Routes in one class compute the same quantity; a theorem in one class transfers through the listed
identity.

| Class | Common quantity | Routes | Identity joining them |
|---|---|---|---|
| C1 Weil's window form | `Q ≥ 0` on windows of every length; untwisted horizon layer | HF, SRT, AIP, ACT, ACS-atomic; RW, EWU, OWU, MSC, FEL; ADT/AHD, CACT | window ⇔ horizon ⇔ every `K·c*` ⇔ Beurling schedule ⇔ `ι = 0` ⇔ fold capacity [L] |
| C2 Glued state | `κ(φ_c) − 1` on the boost hyperplane | SC, AKG, RIT-Künneth | Grams are compressions on the Beurling schedule [L] — face of C1 |
| C3 Window integer | collision charge, heat count, window index | WD-charge, SC-heat, LA-heat, TG, HEF | index = Wiener–Hopf index = growth of `|𝒵(t)|²` [L] — face of C11 |
| C4 Odd / Markov sector | `R ≤ ½`; sinh capacity; folded jump process | CHMD, TT, AID, SAHT, OWU, ACT | odd-sector positivity ⇔ RH; Barta/Picone ground states [L] — face of C1 |
| C5 Rank / degree | Laguerre–Pólya property | TH, HCF, PA, GTA, LA-Jensen; ART | inertia counts off-line pairs at matched rank [L/D] |
| C6 Scheduled prime sums | lower bound of a scheduled energy | FU, CFC, RP, SZ, LI, FEL, EGC | explicit-formula functionals bounded below ⇔ RH [L] |
| C7 One-point precision | `ψ − x`, `M(x)`, first cyclotomic mode, coupling, Redheffer determinant | WL, MC, PBM, RB, JAS, CTF, SC-coupling | one-sided count ⇔ RH; one mode carries `2Θ`; coupling ≡ kernel; `χ̃ = −M(N)` [L] |
| C8 Selection / typicality | trivial gauge point; degeneration type | MC-typicality, BAG, XN; ADT, AHD | RH ⇔ trivial point typical; complete degeneration selects `Λ` [L] |
| C9 Realization | spectral reality of a constructed operator | RN, PTR, W1C, PM-Mayer | no finite realization; Mayer Krein positivity ⇔ RH [L] |
| C10 Pre-divisor | a section defined before the divisor | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF | zero-independent forcing (Γ5) |
| C11 Local zero location | window energy, Hecke defect, near-line density, census, cluster detection | WD-energy, WD-Hecke, census, HEF, SRT-local, IGP, TTPC | abscissa = 2·depth; eight-form density statement; cluster-product horizon [L] |
| C12 Hodge–Lefschetz / gluing | HL on the positive locus; zero modes; top gcd stratum | HF-Hodge, ACS-Hodge, RIT, EHT, TG, DZG | Liouville = HL; zero modes = radical; graded/top Möbius pair [L] |
| C13 Sections, counts, Tate family | count-valued primitive `h¹`; naive height; Tate jet | ACS-effectivity, HF-RR, RIT quadratic RR, IRK, AE, WTZ | Künneth `h¹`; Rosati ⇔ naive height; Weil = Tate jet = signed count [L] |
| C14 Reflection | `σ_A` Rosati; Lewis co-isometry defect; Krein form; band poles | PM-scattering, HF band poles, W1C, CWS Frobenius, PW-B survivor | `U_LP` bridge; similitudes scalar; no linear Serre–Krein isometry [L] |
| C15 Window tower | `W_A` over the truncated Dirichlet λ-ring; stages; two collars | CWS, WTZ, DZG; meets C1, C4, C13, C14 | stage transfer; ground-state identity; two-collar form [L/D] |
| C16 Prime-blind cone | archimedean + pole part on the annihilator of `log ℕ_{≥2}` | PBAP (support line) | Weil cone `⊆ {Λ}`; nonempty ⇔ PBAP; zero-side identity [L] — face of C1 and Γ8 |
| C17 Dimension zero | domination of point counts by an archimedean family | ATD, DZG (classified) | bare domination ⇔ `Q ≥ 0` [L] — face of C1 with no independent content |
| C18 Angle dictionary | Hurwitz forms of angles / frequencies | AHD curve calibration; ACS, LST function-field lines | angle `u` over `𝔽_q` ≡ frequency `u` over `ℤ` [L] |

C1, C2, C4 and C17 are one quantity, Weil's window form; C15 is the same quantity organized as a tower,
where C1 (sign), C13 (counts), C14 (reflection), C4 (Markov) and C16 (blind cone) meet. C3 is a face of
C11, and C11 is the growth of window negativity in `A`. C5 and C6 are sign problems on test families
that become RH-complete only in the limit of rank, degree or schedule. C7 and C11 are precision faces;
C13 is the production face; C8–C10, C14 and C18 are selection and reflection faces.

## U-Σ — the exact two-collar stage step

Core problem: Weil's form is nonnegative on windows of every length. Each prime-power stage adds one
collar-to-collar correlation; with the interior positive, the stage is the block inequality
`S^N_ε ⪰ w_{N+1}(J + J*)` on two-collar data, where the frozen form is indefinite and the new fold must
act as a positive source — exactly, uniformly in the stage. Equivalent forms: every fixed multiple of the
critical overlap; horizon layer; Beurling schedule; `ι(A) = 0` ∀A; fold capacity; odd-sector Markov
capacity; HL on the positive locus; `μ(A) ≥ 0` ∀A; Mayer Krein positivity; prime-blind positivity;
canonical archimedean domination [L].

| Layer | Status | Anchor |
|---|---|---|
| Receivers | window, horizon, schedule, `K·c*`, window index, fold capacity, odd sector, Krein, PBAP, domination | CWS, AHD, RIT, TM, CHMD, RHTower, DZG [L] |
| Window algebra and tower control | truncated Dirichlet λ-ring; one fold per stage; no Frobenius inside | WTZ, DZG [L] |
| Entrance | every new fold paid pointwise by the collar exit charge; composite stages free | WTZ [L] |
| Stage identity | `Q = Q_N − 2wc_H(log(N+1))`; ground-state identity; two-collar block form | WTZ, DZG [L]; [D] |
| Frozen forms | indefinite at the first prime stage; one cubic-moment direction on the odd unit window | WTZ [L/W] |
| Graph structure | rational Hecke graphs; exact horizons at stages 1 and 2; Barta/Picone certificates (sign-blind) | WTZ [L] |
| Base | all tests to `≈ 0.7243`; odd window past `log 2`; odd prime-free by count | SP, AIP, LST [L] |
| Budget and localization | sharp floor; low-frequency localization; canonical-degree horizons | WTZ, AHD [L] |
| Complete family | PD below `1/8`; critical curve = Weil on untwisted windows + positive counts | CACT, AHD [L] |
| Zero modes | radical; translation stable; both collars | DZG [L] |
| No slack | Weil cone a point; doubly-exponential margins; no finite-square identity | RHTower, M, CWS [L] |
| Dimension zero | classified: no independent positivity | DZG, ATD [L] |

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, ACS-atomic, CACT, CAF, RAPT, SSH, SSHA, CSAR, ACPL, TM, ADT, AHD | subcritical solved; critical curve = Weil on untwisted windows + counts; growing conductors and one fixed multiple open |
| Aperture ground minimum | RW, EWU, OWU, MSC, CFC, SP | window sign by stages; two-collar step open |
| Glued state | SC, AKG | Beurling-schedule sign |
| Markov / odd sector | CHMD, AID, SAHT, TT, ACT, OWU | ground state of the folded jump process with sinh capacity |
| Window tower | CWS, WTZ, DZG | exact signed stage step |
| Dimension zero | ATD, DZG | equivalent to the window sign |
| Edge / zero modes / Kähler | EHT, HWV, RW, DZG | HL on the PSD locus; zero modes on both collars |
| Stars / gluing | HWV, CSAR, ADT | top gcd stratum |
| Effectivity / RR | ACS, LST, RIT, HF, AE | count-valued inequality for the primitive `h¹` (U-Π production) |
| Rank / degree / approximation | TH, LA, HCF, PA, GTA, ART | Laguerre–Pólya |
| Scheduled prime sums | FU, CFC, RP, SZ, LI, FEL, EGC | scheduled energy lower bound |
| Screw / Krein–Schur | SZ | canonical system of the Weil kernel; nearest carrier of the two-collar recursion |
| Paths | TG, SC, EHT, ACPL, HWV | source-defined HL along a flow |
| Realization | RN, PTR, W1C, PM | tower of unbounded rank; Mayer Krein positivity |
| Prime-blind | PBAP | signed blind combinations |
| Künneth / powers | RIT, EHT | RH-equivalent at every degree |

## U-Π — precision and production

Core problem: control Weil's arithmetic term at square-root precision and produce the window `h¹` by an
exact identity of unbounded rank. Forms:
- the one-point windowed prime error (kernel, coupling, one-sided count, its damped form on the cone);
- one cyclotomic mode of the Chebyshev error (energy abscissa `2Θ`);
- the growth exponent of window negativity (`≥ Θ − ½`, `≤ ½`);
- windowed zero power sums (window energy, window integer, inner caps);
- the conjugate diagonal ↔ near-line density ↔ log-mean (one statement in eight forms);
- signed pair information beyond bandwidth one;
- the first Taylor coefficient of the Tate family (parity), classified: no positivity from positive
  dimension, jets generated by `M` and `ρ_A(Λ)`;
- a count whose primitive `h¹` is the window form (production), carried by a tower of rank `≈ 2e^A`.

| Face | Routes / programmes | Reduction |
|---|---|---|
| One-sided prime count | WL, PBM, RB, JAS, CTF, ACP, ASRP | `ψ(x) − x ≤ C√x log²x` (Π1) |
| One cyclotomic mode | MC, CAF | first-band energy `O(N^{1+ε})` (Π10, B25) |
| Windowed kernel / coupling | SC, ACPL, AKG, HKT | bounded `K_ζ` ⇔ bounded dense coupling ⇔ bounded damped cone coupling (Π4, Σ17) |
| Integer producers | WL, AKLT, AHA | `ε`-uniform producer (Π3) |
| Möbius / nerve | MC, BVI, CAF, HWV, ADT | half-power cancellation; `χ̃ = −M(N)` (Π1, Π2) |
| Window budget | CWS, WTZ, SRT | exponent between `Θ − ½` and `½` (Σ28) |
| Window energy | WD, TG, CDG | inner caps (Π17, Π23) |
| Near-line density / log-mean | WD, CDG, RBG, HEF, census | eight-form statement; occupancy (Π5, Π22) |
| Census / clusters | SRT, IGP, Zeta23, CDG, TTPC | signed information beyond bandwidth one (Π7); cluster detection (Π8) |
| Tate jet / parity | WTZ, DZG, ATD, AHD | classified (Π24, Π25, Σ31) |
| Sections / heights | ACS, LST, AOG, AET, AE, RIT, SPTL, CWS | count-valued inequality for the primitive `h¹`; identities refuted (Π11h, Π20) |
| Finite realizations | RIT, CWS | no-go: tower forced (Π18) |
| Genus | ACS, RHTower, LST, CWS, WTZ | main term `2e^A`; upper law open (Π16) |
| Exceptional moduli | MC, CACT, CAF | beyond `(log x)^A` (Π9) |
| Averages vs heights | WD, LA, SRT | density-zero exceptions (Π6) |
| Subconvexity / heat | LA, WD, AHA | floors `133/200`, `2/3` (Π12) |
| Candidates | APF, EWJ, FEL, WBF, IRK | integral counts from a source lift |

Identities [L]: one-sided count ⇔ `κ = 0`; coupling rate = zero width; two-bump negativity rate = maximal
depth; window-energy abscissa = twice the maximal depth; first cyclotomic band abscissa = `2Θ`; canonical
class = half-weighted Chebyshev profile; Weil's window form = Tate jet = signed count; eight forms of
near-line density; Künneth `h¹` = counts + `½Q`; Rosati positivity ⇔ naive height; first-order
degeneration term = point count over every finite ring; bare domination ⇔ Weil sign.

## U-Γ — the positivity of the reflection

Core problem: a source-defined mechanism that makes the reflection `ρ ↔ 1 − ρ̄` act as a positivity.
The distinguishing half is closed: every prime-set flip is separated at every density, the Weil cone is a
single point, every certificate has pole weight `1` and node weights `Λ`, so selection follows from
positivity. The reflection is constructed on both sides (window Rosati involution, Lewis adjoint, Mayer
Krein space) and related by `U_LP` up to conjugation and an exponential twist; the window algebra carries
no Frobenius; positivity of the reflection is RH.

| Face | Routes / programmes | Status / reduction |
|---|---|---|
| Typicality of the trivial point | MC, AGT, BAG, XN | RH ⇔ trivial point typical; Baire-generic exponent `1` (Γ1) |
| Gluing of the global pole | SC, AKG, RIT | classified (Σ11, Γ11) |
| Margin, index, edge, degeneration selection | RIT, ACP, HKT, EHT, ACPL, RAPT, ADT, BGG | flips separated at every density; only `Λ` degenerates completely (Γ2, Γ12, Γ18) |
| Weil cone / certificates | RHTower, BSU | `⊆ {Λ}`; `β = 1`, `w = Λ`; nonempty ⇔ prime-blind (Γ23, Σ32) |
| Window selection | CWS | bounded windows blind; law in `A` (Γ20) |
| Density selection | ACPL | RvM-count countermodels (Γ21) |
| Tate counts | WTZ, DZG | soft in positive dimension; do not descend (Γ27) |
| Completed Tate family | DZG | unimodular on the line: domination = functional equation (Γ30) |
| Window Frobenius | DZG, WTZ, RIT | similitudes scalar; Frobenius changes the window (Γ28) |
| Intertwining coefficient | PM, RIT, RHTower | band poles = Hodge defect; contraction blind (Σ19, Γ22) |
| Frobenius at infinity | PL, CDG, RBG, EHT, AOG, AET, CWS, WTZ | Rosati involution; Hecke similitude; naive height (Γ4, Γ19) |
| Mayer reflection | PM, W1C | Lewis adjoint; co-isometry defect; Krein positivity ⇔ RH; no linear Serre–Krein isometry; core-packet limit (Γ24, Γ25, Γ29) |
| Resonant-state statistics | PM | cutoff Grams, Hecke gaps, height laws retain the rate (Γ26) |
| Physical / native source | PM; PW-B retired | source-uniform extinction no-go; recentering impossible (Γ13, Γ17) |
| Pre-divisor constructions | BSH, CDC, HJ, SEC, PCS, RFHM, DR, EWJ, APF, WBF | zero-independent forcing (Γ5) |
| FE twins | SelbergClass | off-line real zeros (Γ15) |
| Function-field calibration | ACS, AKG, RIT, EHT, ACPL, LST, HWV, AET, AHD, CWS, WTZ | local walls, counts, angle dictionary identical; pure curves sums of squares; fakes exponential (Γ10, Γ31) |
| Selection → sign | all selectors | no selector gives positivity (Γ16) |

## 2. Cross-family seams

| Seam | Statement | Routes on the seam |
|---|---|---|
| Σ: one criterion | every complete-family receiver is the window criterion | HF, SRT, AIP, ACT, RW, EWU, OWU, SC, AHD, CWS [L] |
| Σ ∩ Π: one algebra | window = module over the truncated Dirichlet λ-ring; arithmetic = `[M, log Z]` | WTZ, CWS [L] |
| Σ ∩ Π ∩ Γ: dimension zero | Tate pieces at positive dimension, Weil's form at `k = 0`; positive dimension classified; Euler-product pole weight forced | WTZ, DZG, ATD, AHD [L] |
| Σ: one graph | rational Hecke graphs; Perron vectors; Barta certificates | WTZ [L] |
| Σ: one decomposition | counts on every twisted direction + Weil on untwisted windows | ADT, AHD [L] |
| Σ: one location | each new fold = one collar-to-collar correlation; two-collar block inequality | WTZ, DZG [L]; [D] |
| Σ: frozen indefiniteness | the new fold is a positive source; cost-only payments refuted | WTZ [L]; PBAP node criticality [L] |
| Σ ∩ Γ: zero modes | radical vectors touch both collars, where the new fold acts | DZG [L] |
| Σ: one axis | window length = level = radius `½log K` = active primes = Mayer coordinate | AHD, TM, RW, LST, CWS, RIT, EHT [L] |
| Σ ∩ Π: one horizon | every soft horizon `≍ 1/deg K_A`; exact margin doubly exponential | WTZ, AHD, ATD, M [L]; [D] |
| Σ ∩ Π: one exponent | floor `(4A+1)e^{A/2}`; two-bump rate = maximal depth = ½ abscissa | WTZ, SRT, CDG [L] |
| Σ: subcritical regime | solved below `(log N)^{1/8}`; edge exponent `1/8` under ¬RH | CACT, EHT [L]; [D] |
| Σ: nonlocal payment | pointwise calibration fails at the first two primes; Schur squares survive; sign-blind certificates cannot use the fold sign | ACT-L, RW, AIP, CHMD, WTZ [L] |
| Σ ∩ Π: no slack | Weil cone a point; doubly-exponential margins; no finite-square identity | RHTower, M, CWS [L] |
| Σ ∩ Π: one gluing | Redheffer, nerve `χ̃`, coprimality signature, glued index | ADT, HWV, AKG, MC [L] |
| Σ ∩ Π ∩ Γ: counts and towers | Künneth counts pay all but `½Q`; signed count; no finite realization; naive height ⇔ sign | CWS, WTZ, LST, AE, AET, ACS, RIT [L] |
| Σ ∩ Γ: angle dictionary | angle over `𝔽_q` ≡ frequency over `ℤ`; trivial angle carries Weil | AHD [L] |
| Σ: screw / canonical system | translation-invariant kernel on growing intervals; Krein–Schur blocks | SZ, RHTower/Suzuki [L]; [D] |
| Π: window integer = window power sum | collision charge = Wiener–Hopf index = growth of `|𝒵(t)|²` | WD, TG, SC-heat [L] |
| Π: one density statement | log-mean = mollified log-mean = horizontal moment = clustering = Hecke readings | WD, CDG, census, MC, HEF [L] |
| Π: one mode | first cyclotomic band carries `2Θ` | MC, CAF [L] |
| Π: means vs heights | density statements cannot exclude density-zero clusters; clusters are detectable | WD, LA, SRT, RW, census [L] |
| Σ ∩ Π: kernel = coupling = window error | bounded kernel, bounded dense coupling, bounded damped cone coupling, window PNT at `√` precision | SC, ACPL, EHT, WL, HKT [L] |
| Σ ∩ Π: conductor levels | Siegel–Walfisz range; above `√N` Elliott–Halberstam type | CACT, CAF, MC [L] |
| Σ ∩ Γ: one reflection | `σ_A` Rosati ↔ Lewis adjoint via `U_LP`; Frobenius defect = co-isometry defect; window Frobenius = translation into the next window | WTZ, CWS, RIT, PM, DZG [L] |
| Σ ∩ Γ: one point, one cone | Weil cone `{Λ}`; prime-blind nonemptiness; node criticality; zero-side identity | RHTower [L] |
| Γ: blind selectors | bounded windows, densities, contractions, local twists, Tate counts, resonant-state statistics | CWS, ACPL, RIT, AKLT, WTZ [L] |
| Σ: approximation | RH-true approximants close into Laguerre–Pólya | ART, W1C, PTR, LA, TH |
| Γ: selection without sign | every selector is a margin, index, counterterm or identity | RIT, ACP, ACPL, ALG, AES, EHT, HWV, ADT, BGG |
| Σ: paths | crossing-free deformation ⇔ positivity | TG, SC, WD, EHT, ACPL, HWV |
| Archimedean channel | Lévy jumps, `Ω(0)`, exit charge, end profile, prime-free stage, archimedean Tate family, couplings of coprime atoms | AKG, ALG, CHMD, RIT, ACPL, HWV, ACS, LST, ADT, CWS, WTZ, DZG, ATD |

## 3. Route → core map

| Route | Core | Class | Face |
|---|---|---|---|
| WL | Π | C7 | one-sided count; canonical class as cumulative Chebyshev |
| RW, EWU, OWU | Σ (Γ) | C1, C4, C15 | window sign by stages; two-collar step |
| FU, CFC, RP, SZ, LI | Σ | C6 | scheduled prime sums; SZ also the screw/canonical-system carrier |
| PA, TH, LA, HCF, GTA | Σ | C5 | Laguerre–Pólya |
| MC | Π (Γ) | C7, C8 | Möbius cancellation; one cyclotomic mode; Redheffer; typicality |
| TT | Σ | C4 | odd / directed covariance |
| TG | Π, Σ | C3, C12 | window integer; HL along paths |
| HF | Σ (Π, Γ) | C1, C12, C13, C14, C15, C18 | complete family = Weil on untwisted windows + counts; Kähler; correspondences; no window Frobenius |
| SRT, AIP, ACT | Σ (Π) | C1, C4, C11 | complete atomic matrix; pencil index; cluster detection; criticality |
| SC | Σ, Π (Γ) | C2, C7, C3 | glued state; damped cone coupling; heat |
| CHMD | Σ | C4, C1 | odd sector; folded Markov capacity |
| RN | Σ | C9 | realization |
| WD | Π (Σ) | C3, C11 | window energy; inner caps; near-line density |
| PM | Γ (Σ) | C9, C14 | Mayer realization; Lewis reflection; Krein positivity; window bridge |
| JAS, CTF, PBM, RB | Π | C7 | one-sided count |
| XN, BAG | Γ | C8 | typicality / recurrence |
| ACS | Π (Σ, Γ) | C13, C1, C12, C15, C18 | count-valued primitive `h¹`; naive heights; genus; curve calibration |
| APF, EWJ, WBF, IRK | Γ (Π) | C10, C13 | source lift with integral count |
| BSH, CDC, HJ, SEC, PCS, RFHM, DR | Γ | C10 | pre-divisor constructions |
| EGC, FEL, MSC | Σ | C6, C1 | contour / likelihood / Sonin |
| PTR, W1C | Σ (Γ) | C9, C5, C14 | realization; faithful divisor; Krein form |
| PW-B (retired) | Γ | C14 | survivor = scattering receiver |
| PBAP (support) | Γ (Σ) | C16 | prime-blind positivity on signed blind combinations |

## 4. What a closing argument must supply

| Needed | Present over `ℤ` | Missing |
|---|---|---|
| Sign of the window form | criterion; λ-ring; signed folds; Hecke-graph reading; entrance free; ground-state identity; base to `0.7243` | an exact signed stage step on two-collar data in every prime-power stage (Σ30) |
| Full-space structure | PD below `1/8`; every twisted direction a positive count | growing conductors at the critical curve; one fixed multiple on windows of every length (Σ1j, Σ1k) |
| Uniformity in `A` | each length finite; stage transfer; phase diagram; canonical-degree horizons | a law in `A` beyond the `e^{−A/2}` soft horizons; subexponential window negativity |
| Positivity through dimension zero | classified: equivalent to the window sign | — (no independent input exists) |
| Nondegeneracy (HL) | Kähler transport; zero modes = radical on both collars | no zero mode at any length |
| Gluing | gcd stratification; two-prime cyclic orbit carries the defect | global payment of the top stratum |
| Precision | one-sided count ⇔ RH; one cyclotomic mode carries `2Θ`; eight-form density statement; caps to `σ_m` | square-root size of one mode; inner caps; log-free occupancy; signed pair data beyond bandwidth one |
| Count from geometry | first order = `#ℙ⁷(ℤ/m)` over every finite ring; Weil's form = signed count | an exact count-valued inequality of unbounded rank for the primitive window `h¹` |
| Canonical selector | Weil cone `{Λ}`; flips separated; Rosati involution; Lewis adjoint; Mayer Krein space; window Frobenius = translation | the reflection acting as a positivity (Rosati / Krein); finite cusp energy ⇒ zero defect |
| Integrality with homotopy invariance | collision charge as Wiener–Hopf index; window index; `{0,∞}` laws for derived objects | a zero–one law for `κ`; a structural bound on the window index |
