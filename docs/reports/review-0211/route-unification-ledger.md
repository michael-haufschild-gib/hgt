# Route unification ledger — status quo

The 33 live routes and 16 candidates are faces of three core problems — **U-Σ** (sign), **U-Π**
(precision and production), **U-Γ** (selection). All three read one even integer, `κ = κ(K_ζ)`: the
negative index of Weil's correlation on the dilations of `ℚ`, read on the pole-orthogonal hyperplane
`v₁^⊥`. Seven unifications organize them:

- **One criterion.** Every complete-family sign face — positivity at every fixed overlap multiple,
  the restricted Weil minimum at every aperture, the glued index of the archimedean successor state,
  the constant-factor wall, the second-order term of the degeneration — is Weil's form on window
  tests `H = e^{y/2}h`, `h ∈ C²[−A, 0]`. The horizon criterion, the single Beurling schedule and the
  window criterion are theorems [L].
- **One decomposition.** The complete family degenerates into a **bulk** whose rescaled limit is the
  point count `J(1)#ℙ⁷(ℤ/m)` (positive, zero-blind; zeros enter only through a positive pole weight)
  and a **horizon layer** that is Weil's window form, plus at the critical curve a prime-free coercive
  term `(7J(1)/K)∫e^{−8y}H²` [L]. The count carries no sign; the horizon carries all of it.
- **One axis.** The window length `A`, the aperture, the degree, the radius `½ log K` of the tests a
  multiple `K` synthesizes, and the set of active primes (`n ≤ e^A`, departing jumps paying their own
  creation) are one coordinate [L].
- **One gluing.** The local divisibility structure is unipotent; one rank-one gluing at the pole
  creates `μ` (Redheffer `det = M(N)` = nerve Euler characteristic = coprimality signature) and the one
  extra negative square of the glued state; graded energies are positive cone sums of top-stratum
  energies and top energies are Möbius-signed sums of graded ones [L].
- **One function for selection.** The rank-one intertwining coefficient `Λ(s)/Λ(s + 1)` carries the
  Hodge defect as band poles, is the Gauss–Mayer boundary `2ζ(s)/ζ(s + 1)`, and is the scattering
  coefficient of `SL₂(ℤ)\ℍ` [L/D]. PM, the loop-Eisenstein face and the resonant-partner face of
  Frobenius at infinity read this function.
- **One precision for the window integer.** The window index (collision charge, Wiener–Hopf index,
  sectoriality) is decided by the growth of the window energy `|Σ_{z∈W} m_z e^{t(z − ½)}|²`, whose
  Laplace abscissa is twice the maximal depth [L]. The integer route is a precision statement on
  windowed zero power sums.
- **One missing fact.** Over `𝔽_q` one object — counts of points on graphs of correspondences on
  `C × C` — gives the sign (Hodge index), the precision (Castelnuovo–Severi) and the selection (the
  Frobenius graph). Over `ℤ` the correspondence algebra, λ-ring, theorem of the square, Lefschetz trace
  and Riemann–Roch identities exist, and the first-order structure of the degeneration is already a
  point count [L]; Tate's limit law makes the missing fact exact: a naive height at bounded distance
  from the integral Rosati form [L]. U-Σ, U-Π and U-Γ are the three consequences of that absence.

Evidence: `[L]` Lean; `[S]` Lean in the working tree or not integrated; `[D]` derived here from Lean
statements.

## 0. The one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ(K_ζ) = #{ρ : Re ρ > ½}` (distinct), even; RH ⇔ `κ < 2`; carried by one two-prime lattice and the Hecke orbit of one generic test | HKT, AKLT, AOG `TheIndexExit`, ACS `TheHodgeDefectIsCyclic` [L] |
| Bounded kernel | RH ⇔ `‖K_ζ(u)‖ ≤ Re K_ζ(1)` ∀u (Castelnuovo–Severi at rational scales) | RIT `riemannHypothesis_iff_castelnuovoSeveri` [L] |
| Coupling | RH ⇔ bounded coupling on one dense `⟨p⟩×⟨q⟩`; on the natural cone: RH or polynomial repulsion from maximal width | ACPL [L] |
| Window prime error | `K_ζ(u)` = smoothed prime error in a fixed-length multiplicative window, normalized by `√u` | HKT [L]; reading [D] |
| Window test | RH ⇔ `Q(e^{y/2}h) ≥ 0` for every C² `h` on every `[−A, 0]` | AHD `riemannHypothesis_iff_halfWeight_nonneg` [L] |
| Horizon layer | horizon blocks of the complete family, divided by the overlap, tend to `κ_φQ(H)` past the critical curve; RH ⇔ eventual `≥ −ε` | AHD `TheHorizonCriterion` [L] |
| Second order | at `c^{β+1}/log N → K`: `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²`; tilted spline `κQ(H) + (7J(1)/K)∫e^{−8y}H²` | AHD `TheBulkDeterminesTheSecondOrderTerm`, `TheAliasingConstantOfTheTiltedSpline` [L] |
| Single schedule | every finite rational Gram is a limit of complete Beurling-matrix compressions at `2L(log L)²`; RH ⇔ eventual pole-hyperplane sign there | TM, RIT `TheHodgeIndexAtCriticalOverlap` [L] |
| Glued state | `κ(φ_c) = κ + 1` at `∞` and every prime; its Grams are compressions on the single schedule | AKG, TM, RIT [L] |
| Bulk | rescaled limit `J(m) = J(1)#ℙ⁷(ℤ/m)`; zero ledger `m_ρκy₁²/(ρ(1−ρ))`, `Re > 0`, for every configuration | ADT, AHD [L] |
| Gluing determinant | divisibility form unipotent; pole gluing = Redheffer `det = M(N)` = nerve `χ̃`; coprimality signature `M(N)` | ADT, HWV [L] |
| Strata | graded = positive cone sum of top strata; top = Möbius-signed sum of graded; successor and archimedean coupling in `g = 1` | ADT, HWV [L] |
| Primitive part | boost hyperplane = `v₁^⊥` = Markov = harmonic hyperplane; `v₁` = ground state = Kähler class | RIT, HWV [L] |
| Markov form | `W = V_N‖g‖² + J(g) + ½⟨c,g⟩² − ½⟨s,g⟩²`; on a window of length `A` only `n ≤ e^A` jump; RH ⇔ sinh-capacity bound | RHTower `WeilMarkovPoleCapacity`, AHD `ThePrimesOfAHorizonWindow` [L] |
| Kähler package | HR transports wherever HL holds; Liouville = HL; RH ⇔ HL on the PSD locus | HWV [L] |
| Edge | RH ⇔ no edge; a finite edge is PSD with a zero mode; under ¬RH the tilted-spline edge lies in `[(log N)^{1/9−}, 2(log N)^{1/8+}]` infinitely often | EHT [L] |
| Degree laws | ceiling; near radical `(2 − η)e^{2a}` blind below `2πe^{2a}`; genus function; finite divisor | ArithmeticCompensationTheory, RHTower, ACS [L] |
| Semilocal | exact `{∞,2}` trace through `½ log 3`; no positive semilocal or trace carrier | SP, ADT [L] |
| Scaling surface | cycles `aH + bV + f`; Castelnuovo–Severi defect = Weil's form; RH ⇔ effectivity with RR and ample axioms; cone RR ⇔ Hodge | ACS, AOG [L] |
| Sections | Künneth `h¹` = count part + `½δ`; Lévy jump count pays it on prime-free cycles to radius `1/64`; Stepanov over `𝔽_q` | LST [L] |
| Correspondences | Rosati positivity ⇔ orbit Hodge index ⇔ naive height / convex log-count on the integral Rosati form | AOG, ACP, AET [L] |
| Intertwining coefficient | `Λ(s)/Λ(s+1)`: band poles in `−½ < Re s < 0` = right zeros; = Mayer boundary `2ζ(s)/ζ(s+1)` with slope weights `(1 − 1/n)Λ(n)`; scattering coefficient of `SL₂(ℤ)\ℍ` | RIT [L]; scattering [D] |
| Window energy | `\|𝒵(t)\|² = \|Σ_{z∈W} m_z e^{t(z−½)}\|²`; abscissa = 2·maximal depth; index `0` ⇔ integrability at the stage margin; log stage ⇔ corridor; polynomial stage ⇔ RH | CDG `SzegoCollision` [L] |
| Hecke defect | means ↔ near-line density rates; `o(log U)` ⇔ critical-scale clustering; one dyadic constant ⇔ RH | CDG [L] |
| Heat | `κ(φ_c^{(t)}) − 1 = N(t)/2` | AKG, RIT [L] |
| Frobenius at infinity | `σ(ρ) = 1 − ρ̄`; RH ⇔ `σ` trivial ⇔ Hecke similitude of the collided form ⇔ partner saturation | EHT, PL, RHTower [L] |
| Mayer determinant | Euler product over periodic modular geodesics; scattering divisor = ζ's divisor | RIT [L] |
| Künneth | `κ(K_ζ⊠K_ζ) ∈ {0, ∞}`; no softening at any horizon | RIT, EHT [L] |
| Selection | every prime-set flip separated at every density; complete degeneration only for `Λ`; harmonic saturation only at the Euler gauge | RIT, ADT, BGG [L] |

The three walls are the three ways a reading of `κ` fails:
- **Σ**: Weil's window form is not decided by estimates at the edge; the family adds a zero-blind count
  and a positive prime-free term, nothing that decides the sign.
- **Π**: windowed prime errors and windowed zero power sums are not controlled at square-root (local)
  precision; the near-line density ladder stops at rate `1`; no count produces the primitive `h¹` past
  the prime-free window.
- **Γ**: every selector is a margin, index, counterterm or structural identity; the selector that would
  produce the sign is Frobenius at infinity — the placement of the poles of `Λ(s)/Λ(s+1)` — or a naive
  height on the correspondence ring.

## 0.1 The window axis

| Coordinate | Reading at window length / degree `A` | Anchor |
|---|---|---|
| Window test | `H = e^{y/2}h`, `h` on `[−A, 0]`; Weil's form with prime jumps `n ≤ e^A` | AHD [L] |
| Overlap multiple `K` | a multiple `K·c*` synthesizes tests of radius `½ log K − O(1)` on the block `[N/B, N]` | TM [L] |
| Critical multiple | at `c⁸ = K log N` a window is negative iff `K > K*(H) = 7J(1)∫e^{−8y}H²/(κ\|Q(H)\|)` | AHD [L] |
| Aperture of the restricted minimum | `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})`; positive through `181/500`; `{∞,2}` trace through `½ log 3` | ArithmeticCompensationTheory, SP [L] |
| Near radical / genus | dimension `≥ (2 − η)e^{2a}`; energy `≤ exp(−η²e^{2a}/(300a))`; blind below `2πe^{2a}` | RHTower, ACS [L] |
| Finite divisor | coercive off `D_a ∪ {i/2}` | ACS [L] |
| Visibility | isolated pairs below `2π exp(2πS_δ(a))` are seen | ACS [L] |
| Riemann–Roch | Künneth effectivity on prime-free cycles, all-profile through `181/500`, off `D_a` at every degree | LST, SP [L] |
| Over `𝔽_q` | exact radical infinite beyond the genus aperture; defect `0` or `∞` | ACS [L] |

Each fixed window length is a sub-RH, finite-dimensional problem; all lengths together are RH.

## 0.2 The degeneration dictionary

| ADT/AHD object | Statement | Classes reading it |
|---|---|---|
| Variation over the resolution `(c, N)` | complete Weil matrices; overlap multiple = aperture | C1 |
| First-order limit | `J(m) = J(1)#ℙ⁷(ℤ/m)`; tensor law = CRT; weight strings = Hensel towers | C1, C12 |
| Monodromy | dilation lowers conductors; eventually idempotent (`{0, 1}`); one branch per prime | C12, C6 |
| Scaling form | `E_m(c) = J(m)c⁻⁷R_m(c/m)`: branches through `rad m`, weights through `J` | C1 |
| Extension data | cross-conductor channels in the top coprime stratum; graded/top Möbius pair | C12, C2 |
| Bulk ledger | every zero enters fixed packets through a positive pole weight | C1 (no selection) |
| Horizon ledger | every zero enters horizon blocks through Weil's summand of the window test | C1, C4 |
| Second order | Weil's window form + `(βJ/K)∫e^{−(β+1)y}H²`; aliasing = dilation derivative of the bulk | C1 |
| One negative square | the pole gluing: glued index `κ + 1`; Redheffer `det = M(N)` | C2, C7, C12 |
| Selection by degeneration | `F_λ = 0` only for `Λ`; flips leave indefinite residues | C8 |
| Function fields | finite monodromy, detection by window `2g`, Stepanov count | calibration |

## 1. Equivalence classes of routes

Routes in one class compute the same quantity; a theorem in one class transfers to the others
through the listed identity.

| Class | Common quantity | Routes | Identity joining them |
|---|---|---|---|
| C1 Weil's window form | Weil positivity of window tests of every length; the horizon layer of the complete family | HF, SRT, AIP, ACT, ACS-atomic; RW, EWU, OWU, MSC, FEL; ADT/AHD | window criterion ⇔ horizon criterion ⇔ every fixed `K·c*` ⇔ single Beurling schedule; bulk zero-blind; second order = Weil + prime-free term [L] |
| C2 Glued state | `κ(φ_c) − 1` on the boost hyperplane | SC, AKG-gluing, RIT-Künneth | ratCorr Grams = compressions on the single Beurling schedule; RH ⇔ pole-hyperplane sign there [L] — a face of C1 |
| C3 Window integer | collision charge, heat count `N(t)/2`, window index | WD-charge, SC-heat, LA-heat, TG, HEF | index = Wiener–Hopf index = growth of the window energy; abscissa = 2·maximal depth [L] — a face of C11 |
| C4 Odd / Markov sector | odd-sector Doob energy `R ≤ ½`; sinh capacity; window Markov form | CHMD, TT, AID, SAHT | Markov hyperplane = `v₁^⊥`; Weil = Markov form + pole plane; windows see primes `n ≤ e^A` [L] — a face of C1 |
| C5 Rank / degree | all-rank Hankel, all-degree Jensen, PF signs; Laguerre–Pólya property of `ξ` | TH, HCF, PA, GTA, LA-Jensen; ART | heated Hankel inertia counts off-line pairs at matched rank; centered products close into Laguerre–Pólya [L/D] |
| C6 Scheduled prime sums | lower bound of a prime-scheduled energy | FU, CFC, RP, SZ, LI, FEL, EGC | explicit-formula functionals bounded below ⇔ RH [L] |
| C7 One-point precision | `ψ(x) − x`, `M(x)`, windowed prime error, coupling, Redheffer determinant | WL, MC, PBM, RB, JAS, CTF, SC-coupling | `Count(a)` iff `a − 1 ∈ 𝒬`; coupling ≡ kernel = window error; `χ̃ = −M(N) = −det R_N` [L] |
| C8 Selection / typicality | the trivial gauge point among twins | MC-typicality, BAG, XN | RH ⇔ trivial point typical [L] |
| C9 Realization | spectral reality of a constructed operator | RN, PTR, W1C, PM-Mayer | Vitali; Mayer determinant with faithful scattering divisor [L] |
| C10 Pre-divisor | a section or potential defined before the divisor | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF | each needs a zero-independent forcing (Γ5) |
| C11 Local zero location | window power sums, Hecke defect, near-line density, local counts, pair surplus | WD-energy, WD-Hecke, census, HEF, SRT-local count, IGP, TTPC | window energy abscissa = 2·depth; Hecke means ↔ density rates; census = signed pair surplus [L] |
| C12 Hodge–Lefschetz / gluing | HL on the positive locus; star descent; top gcd stratum | HF-Hodge, ACS-Hodge, RIT renormalized index, EHT zero modes, TG paths | Liouville = HL; transport free; graded/top Möbius pair; no semilocal carrier [L] |
| C13 Sections, correspondences, heights | a count-valued primitive `h¹`; a naive height | ACS-effectivity, HF-RR, RIT quadratic RR, IRK | universal floor law; Künneth `h¹`; Lévy count of prime-free cycles; Rosati ⇔ naive height [L] |
| C14 Intertwining coefficient | poles of `Λ(s)/Λ(s+1)` in the band; scattering resonances of `SL₂(ℤ)\ℍ` | PM-scattering, HF band poles, resonant partners (Γ4), PW-B survivor, W1C (faithful divisor) | band poles = Hodge defect; Mayer boundary = `2ζ(s)/ζ(s+1)` [L]; scattering reading [D] |

C1, C2 and C4 are one quantity: Weil's window form, read on the complete family (C1), on the glued
state at the single schedule (C2) and as a Markov capacity (C4). C12 is the deformation/gluing form of
the same sign (HL its content, the top stratum its location). C3 is a face of C11: the window
integer is the growth of a windowed zero power sum. C5 and C6 are sign problems on test families that
become RH-complete only in the limit of rank, degree or schedule. C7 and C11 are the precision faces;
C13 is the production face; C8–C10 and C14 are the selection faces, and C14 is where PM, the band poles
and Frobenius at infinity meet.

## U-Σ — Weil's window form

Core problem: Weil's form is nonnegative on window tests of every length. Equivalent forms: positivity
of the complete family at every multiple of the critical overlap; horizon-layer positivity; pole-
hyperplane positivity on the single Beurling schedule; HL on the positive locus; sinh-capacity at every
level; `μ(A) ≥ 0` for every aperture [L].

| Layer | Status | Anchor |
|---|---|---|
| Receivers | window, horizon, single-schedule, every-`K·c*` criteria | AHD, RIT, TM [L] |
| Degeneration | bulk = point-count polarization, zero-blind; horizon = Weil's window form; second order = Weil + prime-free coercive term | ADT, AHD [L] |
| Inherited regime, tilted spline | all vectors `α < 1/9`; below `1/8` packets, subthreshold block, polynomial complement, far reserve; mid-band `α < 1/4`; open: band–far cross and threshold block | CACT, ADT [L] |
| Inherited regime, smooth profiles | logarithmic profile to `ε₀·c*`, budget sharp; every compact profile on polynomial spans to `(log log N)^{1/4}`, almost-polynomial spans past `log log N` | TM, CACT [L/S] |
| Window Markov form | primes `n ≤ e^A` jump; departing jumps pay creation; RH ⇔ sinh capacity | AHD, RHTower [L] |
| Small degree | positivity through `181/500`; `{∞,2}` trace through `½ log 3`; no semilocal carrier; finite prime sets cross zero | SP [L] |
| Degree laws | ceiling; near radical; genus function; finite divisor; visibility; companions | ArithmeticCompensationTheory, RHTower, ACS [L] |
| Kähler package | transport free; HL on the PSD locus is RH | HWV [L] |
| Stars and strata | descent, depth law, Metzler on deep stars; all unpaid coupling in `g = 1`; graded/top Möbius pair | HWV, ADT [L] |
| Effectivity | RH ⇔ effectivity with RR and ample axioms; count classification | ACS, LST [L] |
| Edge | crossing with zero mode; window `[(log N)^{1/9−}, 2(log N)^{1/8+}]` under ¬RH | EHT [L] |

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, ACS-atomic, CACT, CAF, RAPT, SSH, SSHA, CSAR, ACPL, TM, ADT, AHD | Weil's window form on the horizon layer |
| Aperture ground minimum | RW, EWU, OWU, MSC, CFC, SP | `μ(A) ≥ 0` ∀A; fixed `A` finite-dimensional; next prime aperture `½ log 3` |
| Glued state | SC, AKG | pole-hyperplane sign on the single Beurling schedule |
| Markov / odd sector | CHMD, AID, SAHT, TT | window sinh capacity |
| Edge / zero modes / Kähler package | EHT, HWV, RW | HL on the PSD locus |
| Stars / gluing | HWV, CSAR, ADT | payment of the top gcd stratum |
| Effectivity / Riemann–Roch | ACS, LST, RIT, HF | a count equal to Weil's window form (U-Π production face) |
| Rank / degree / approximation | TH, LA, HCF, PA, GTA, ART | Laguerre–Pólya property |
| Scheduled prime sums | FU, CFC, RP, SZ, LI, FEL, EGC | lower bound on a prime-scheduled energy |
| Paths | TG, SC, EHT, ACPL, HWV | source-defined HL along a flow |
| Realization | RN, PTR, W1C | spectral reality of a constructed operator |
| Künneth / powers | RIT, EHT | closed: RH-equivalent at every degree and horizon |

## U-Π — precision and production

Core problem: an unconditional exact statement about primes or zeros at local (square-root) precision.
It takes five forms:
- the one-point windowed prime error (kernel, coupling, one-sided count);
- windowed zero power sums on unit height windows (window energy; the window integer);
- the conjugate-diagonal depth functional, equivalent to a near-line density ladder;
- the signed prime-pair surplus beyond bandwidth one;
- a count whose `h¹` is Weil's window form, equivalently a naive height on correspondences (production).

| Face | Routes / programmes | Reduction |
|---|---|---|
| One-sided prime count | WL, PBM, RB, JAS, CTF, ACP, ASRP | `ψ(x) − x ≤ C√x log²x` (Π1) |
| Windowed kernel / coupling | SC, ACPL, AKG, HKT | bounded `K_ζ` ⇔ bounded dense coupling ⇔ window PNT at `√` precision (Π4) |
| Integer producers | WL, AKLT, AHA | `ε`-uniform producer (Π3) |
| Möbius cancellation / nerve | MC, BVI, CAF, HWV, ADT | half-power cancellation; `χ̃(nerve) = −M(N)` (Π1, Π2, Π10) |
| Window energy | WD, TG, CDG | subexponential `\|𝒵(t)\|²` per window: log stage ⇔ corridor, polynomial stage ⇔ RH; almost all windows at log stage ⇔ log-free near-line density (Π17) |
| Conjugate diagonal | WD, CDG, RBG, HEF | near-line density rate `≥ 1`; mean `o(log U)`; fixed scale (≥qRH); dyadic one constant (RH) (Π5) |
| Census / pair surplus | SRT, IGP, Zeta23, CDG, TTPC | signed prime-pair surplus beyond bandwidth one (Π7) |
| Sections / correspondences / heights | ACS, LST, AOG, AET, RIT, SPTL | count-valued primitive `h¹` past the prime-free window; naive height (Π11h, Γ19); logarithmic duality of the split surface (Π11f) |
| Genus function | ACS, RHTower, LST | near radical `(2 + o(1))e^{2a}` ⇔ resolution of the zeros (Π16) |
| Exceptional moduli | MC, CACT, CAF | individual control beyond `(log x)^A` (Π9) |
| Averages vs heights | WD, LA, SRT | density-zero exceptions invisible to means (Π6) |
| Prefix scale | WD, CDG | solved: `Θ(√m)` unit windows, `≥ c√T` necessary (Π13) |
| Subconvexity | LA, WD, AHA | heat floors `133/200`, `2/3` (Π12) |
| Candidates | APF, EWJ, FEL, WBF, IRK | integral counts from a source lift |

Identities [L]: one-sided count ⇔ `κ = 0`; coupling rate = zero width; window-energy abscissa = twice
the maximal depth; the prime polynomial is self-absorbed by the Hecke defect at log scale; counts + linear
explicit formula cannot bound the Hecke defect; dyadic means ⇔ near-line density rates; quadratic RR ⇔
renormalized Hodge index; Künneth `h¹` = count part + `½δ`; Rosati positivity ⇔ naive height; genus law
⇒ almost all zeros simple; the first-order term of the degeneration is a point count.

## U-Γ — selection of ζ

Core problem: a source-defined mechanism that both distinguishes ζ from its twins and produces
positivity. The distinguishing half is closed for every prime-set flip at every density. The producing
half is Frobenius at infinity, read by `Λ(s)/Λ(s+1)` and, in algebraic form, by Rosati positivity of the
correspondence algebra.

| Face | Routes / programmes | Status / reduction |
|---|---|---|
| Typicality of the trivial point | MC, AGT, BAG, XN | RH ⇔ trivial point typical (Γ1) |
| Gluing of the global pole | SC, AKG, RIT | classified: only the extremal weight has one square; glue pole-blind (Σ11, Γ11) |
| Margin, index, edge and degeneration selection | RIT, ACP, HKT, EHT, ACPL, RAPT, ADT, BGG | every prime-set flip separated at every density; complete degeneration only for `Λ`; harmonic saturation only at the Euler gauge (Γ2, Γ12, Γ18) |
| Counterterm selection | HWV | self-similar star flux ⇔ generalized von Mangoldt weight (Γ18) |
| Local renormalization | AKG | counterterms make `Λ` and a twin both index `1` (Γ14) |
| Intertwining coefficient | PM, RIT loop Eisenstein, RHTower resonant partners | band poles of `Λ(s)/Λ(s+1)` = Hodge defect; Mayer boundary; scattering resonances on `Re s = 1/4` ⇔ RH (Σ19, Γ4) |
| Frobenius at infinity | PL, CDG, RBG, EHT, AOG, AET | defect involution; Hecke similitude; dyadic Hecke constant; Rosati positivity; naive height (Γ4, Γ19) |
| Physical / native source | PM; PW-B retired | source-uniform extinction no-go; algebraic recentering impossible; the modular surface selects ζ (Γ13, Γ17) |
| Pre-divisor constructions | BSH, CDC, HJ, SEC, PCS, RFHM, DR, EWJ, APF, WBF | zero-independent forcing (Γ5) |
| FE twins | SelbergClass | degree three and degree two with positive coefficients admit off-line real zeros (Γ15) |
| Function-field calibration | ACS, AKG, RIT, EHT, ACPL, LST, HWV, AET | local walls identical; `ℤ` differs by infinite genus, disconnected links, incommensurable towers and the absence of a naive height (Γ10) |
| Selection → sign | all selectors | no selector produces complete-form positivity (Γ16) |

## 2. Cross-family seams

| Seam | Statement | Routes on the seam |
|---|---|---|
| Σ: one criterion | every complete-family receiver is Weil's window criterion | HF, SRT, AIP, ACT, RW, EWU, OWU, SC, AHD [L] |
| Σ: one decomposition | bulk = zero-blind point count; horizon = Weil's window form; critical curve adds `(βJ/K)∫e^{−(β+1)y}H²` | ADT, AHD [L] |
| Σ: one axis | window length = aperture = radius `½ log K` = active primes `n ≤ e^A` | AHD, TM, RW, LST [L] |
| Σ: one hyperplane | glued index, complete-Weil sign, Markov criterion, renormalized Hodge index and HR are positivity on `v₁^⊥` | SC, HF, SRT, AIP, ACS, CHMD, RIT, HWV |
| Σ: inherited regime | estimates live below the critical exponent; whole-space `1/8` is a join of three coercive pieces | CACT, ADT, TM [L] |
| Σ ∩ Π: one gluing | Redheffer `det = M(N)`, nerve `χ̃`, coprimality signature and glued index `κ + 1` are one rank-one gluing at the pole | ADT, HWV, AKG, MC [L] |
| Σ ∩ Π: strata | graded energies are positive cone sums of top strata; the inverse is alternating | ADT, HWV [L] |
| Σ ∩ Π: degree laws | ceiling, near radical, finite divisor; each degree finite-dimensional | RW, ACS, RHTower [L] |
| Σ: Markov form | Weil = jump energy + creation potential + pole; on windows the active primes are `n ≤ e^A` | CHMD, TT, RW, LST, AHD [L] |
| Σ ∩ Π ∩ Γ: correspondences | a naive height would give sign, precision and selection at once, as over `𝔽_q`; the first-order structure of the degeneration is already a point count | ACS, LST, AOG, AET, ACP, RIT, HF, ADT [L/D] |
| Σ ∩ Π: counts at small radius | Lévy jump count on prime-free cycles to `1/64`; Stepanov over `𝔽_q` | LST [L] |
| Σ ∩ Π: unattained width | cone, tower and escape receivers leave "`Θ` not attained"; cone models with exact spline weights exist at bounded density | ACPL, AKLT, PM [L] |
| Π: window integer = window power sum | collision charge = Wiener–Hopf index = growth of `\|𝒵(t)\|²`; log stage ⇔ corridor; polynomial stage ⇔ RH | WD, TG, SC-heat [L] |
| Π: precision ladders | Hecke means ↔ near-line density rates (closed on `(0, ½)`, rate `< 1`); census ↔ pair surplus beyond bandwidth one | WD, CDG, TTPC, IGP [L] |
| Π: means vs heights | means and density statements cannot exclude density-zero clusters; finite apertures exclude isolated zeros but not clusters | WD, LA, SRT, RW, census |
| Σ ∩ Π: kernel = coupling = window error | bounded kernel, bounded dense coupling, no edge, window PNT at `√` precision are one statement | SC, ACPL, EHT, WL, HKT |
| Σ ∩ Π: conductor levels | residual control in the Siegel–Walfisz range; above `√N` Elliott–Halberstam type | CACT, CAF, MC |
| Σ ∩ Γ: one function | `Λ(s)/Λ(s+1)` carries the Hodge defect (band poles), is PM's boundary, and is the modular scattering coefficient | RIT, PM, RHTower [L/D] |
| Σ ∩ Γ: Frobenius at infinity | reflection pairing vs conjugation pairing; Rosati positivity and the naive height are the same statement | EHT, PL, CDG, HF, PM, AOG, AET |
| Σ: approximation | approximation by RH-true objects lands in the Laguerre–Pólya class | ART, W1C, PTR, LA, TH [L/D] |
| Γ: selection without sign | every selector is a margin, index, counterterm or structural identity on a partial form | RIT, ACP, ACPL, ALG, AES, EHT, HWV, ADT, BGG |
| Σ: paths | crossing-free deformation ⇔ positivity; content = HL | TG, SC, WD, EHT, ACPL, HWV |
| Archimedean channel | glues `+` and `×`; coprime atoms couple only through it; source of the finite divisor; Lévy jumps on prime-free windows; its trace carrier is indefinite | AKG, ALG, CHMD, RIT, ACPL, HWV, ACS, LST, ADT [L/D] |

## 3. Route → core map

| Route | Core | Class | Face |
|---|---|---|---|
| WL | Π | C7 | one-sided count, producers |
| RW, EWU, OWU | Σ (Γ) | C1 | Weil's window form at every aperture |
| FU, CFC, RP, SZ, LI | Σ | C6 | scheduled prime sums |
| PA, TH, LA, HCF, GTA | Σ | C5 | rank / degree sign (Laguerre–Pólya) |
| MC | Π (Γ) | C7, C8 | Möbius cancellation; Redheffer determinant; typicality |
| TT | Σ | C4 | odd / directed covariance |
| TG | Π, Σ | C3, C12 | window integer; source-defined HL along paths |
| HF | Σ (Π, Γ) | C1, C12, C13, C14 | complete family = Weil's window form; Kähler package; strata; correspondences; band poles |
| SRT, AIP, ACT | Σ (Π) | C1 | complete atomic matrix; horizon layer; zero modes |
| SC | Σ, Π (Γ) | C2, C7, C3 | glued state = single-schedule sign; coupling = window error; natural cone; heat homotopy |
| CHMD | Σ | C4, C1 | Haar / Doob / odd sector; window Markov capacity |
| RN | Σ | C9 | realization |
| WD | Π (Σ) | C3, C11 | window energy (zero power sums); Hecke defect / density ladder |
| PM | Γ (Σ) | C9, C14 | geodesic Euler product; scattering coefficient `Λ(s)/Λ(s+1)`; resonance placement |
| JAS, CTF, PBM, RB | Π | C7 | one-sided count |
| XN, BAG | Γ | C8 | typicality / recurrence |
| ACS | Π (Σ, Γ) | C13, C1, C12 | count-valued primitive `h¹`; naive heights; genus function; curve calibration |
| APF, EWJ, WBF, IRK | Γ (Π) | C10, C13 | source lift with integral count |
| BSH, CDC, HJ, SEC, PCS, RFHM, DR | Γ | C10 | pre-divisor constructions |
| EGC, FEL, MSC | Σ | C6, C1 | contour / likelihood / Sonin |
| PTR, W1C | Σ (Γ) | C9, C5, C14 | realization; approximation; faithful scattering divisor |
| PW-B (retired) | Γ | C14 | source-uniform extinction refuted; survivor is the scattering receiver |

## 4. What a closing argument must supply

Over `𝔽_q` one object, the Frobenius graph on `C × C`, supplies all three readings. Over `ℤ` the corpus
has each ingredient separately:

| Needed | Present over `ℤ` | Missing |
|---|---|---|
| Sign of Weil's window form | window, horizon, single-schedule and every-`K·c*` criteria; window Markov form; positivity through `181/500`; `{∞,2}` trace through `½ log 3` | a producer valid at every window length: a count, an identity (SOS on a two-prime lattice), or a capacity inequality for the window Markov form |
| Positivity uniform in degree | bulk point-count polarization; inherited regime below `1/8`; rough regime to `ε₀·c*`; finite divisor at every degree | a mechanism exact on the near radical (the ceiling excludes estimates there) |
| Full-space structure at the critical curve | horizon blocks and fixed packets identified exactly | the full-space second-order limit and horizon localization |
| Nondegeneracy (HL) | Kähler transport; Liouville = HL; star descent; inheritance below `1/8` | HL on the positive locus; a cross-tower gap through the archimedean channel |
| Gluing | exact gcd stratification; graded/top Möbius pair; two-prime cyclic orbit carries the defect | a global payment of the top stratum |
| Precision | one-sided count ⇔ RH; window energy ⇔ local zero location; producers to the main term; Hecke means to rate `< 1`; census certificate | square-root input for windowed prime errors; subexponential window energy; near-line density at rate `≥ 1` and log-free; the pair surplus beyond bandwidth one |
| Count from geometry | first-order Jordan limit = `#ℙ⁷(ℤ/m)`; theta `h⁰` with RR; scaling surface with RH ⇔ effectivity; Künneth `h¹`; Lévy count of prime-free cycles; correspondence algebra with Tate's limit law | a naive height on `ℤ[ℚ_{>0}^×]`; a section theory whose primitive `h¹` is a count past the first prime |
| Canonical selector | every prime-set flip separated; complete degeneration; modular surface for PM; faithful scattering divisor | Frobenius at infinity as an operator: a structure placing the poles of `Λ(s)/Λ(s+1)` (Krein, Herglotz, decay law), Rosati positivity, or a Hecke similitude of the collided form |
| Integrality with homotopy invariance | collision charge as Fredholm / Wiener–Hopf index; canonical multiplier from the window energy | a structural bound on the window energy (the index carries no information beyond it) |
