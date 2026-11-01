# Route unification ledger — status quo

The 33 live routes and 16 candidates are faces of three core problems — **U-Σ** (sign), **U-Π**
(precision and production), **U-Γ** (selection). The three are readings of one even integer,
`κ = κ(K_ζ)`: the negative index of Weil's correlation on the dilations of `ℚ`, read on the
pole-orthogonal hyperplane `v₁^⊥`. Four further unifications organize them:

- **One axis.** Every sign face lives on the degree axis: the overlap multiple `K` of the atomic
  families, the radius `½ log K` of the tests they synthesize, the aperture of the restricted Weil
  minimum and the degree of a class on the scaling surface are one coordinate `a` [L].
- **One regime.** Along that axis the complete family is a degenerating polarized family. Below the
  critical exponent it converges, after rescaling, to the Jordan-totient form and inherits its
  positivity; at the critical exponent its extension data reach the size of the limit and carry the
  zeros [L/D]. The constant-factor wall, hard Lefschetz on the positive locus and the receiver
  scale are this one regime.
- **One stratum.** Positivity is never local or semilocal: no `{∞,p}` family carries it, links of
  the dilation complex are disconnected, and every unpaid coupling lies in the top gcd stratum,
  reached only through the archimedean place [L/S].
- **One missing fact** [D]. Over `𝔽_q` a single object — the count of points on graphs of
  correspondences on `C × C` — gives the sign (Hodge index), the precision (Castelnuovo–Severi
  bound) and the selection (the Frobenius graph). Over `ℤ` the correspondence algebra, the λ-ring,
  the theorem of the square, the Lefschetz trace and the Riemann–Roch identities exist [L]; Tate's
  limit law makes the missing fact exact: a naive height (a cardinality or a log-count) at bounded
  distance from the integral Rosati form [L]. U-Σ, U-Π and U-Γ are the three consequences of that
  one absence.

Evidence: `[L]` Lean; `[S]` Lean in the working tree or unintegrated; `[D]` derived here from Lean
statements.

## 0. The one object

| Reading | Statement | Anchor |
|---|---|---|
| Index | `κ(K_ζ) = #{ρ : Re ρ > ½}` (distinct), even; RH ⇔ `κ < 2`; carried by one two-prime lattice and by the Hecke orbit of one generic test | HKT, AKLT, AOG `TheIndexExit`, ACS `TheHodgeDefectIsCyclic` [L] |
| Bounded kernel | RH ⇔ `‖K_ζ(u)‖ ≤ Re K_ζ(1)` ∀u (Castelnuovo–Severi at rational scales) | RIT `riemannHypothesis_iff_castelnuovoSeveri` [L] |
| Coupling | RH ⇔ bounded `K(uv) − K(u) − K(v) + K(1)` on one `⟨p⟩×⟨q⟩`; coupling ≡ kernel with absolute constants; local Hyers–Ulam stability | ACPL [L] |
| Window prime error | `K_ζ(u)` = smoothed prime error in a fixed-length multiplicative window at `u`, normalized by `√u` | HKT [L]; reading [D] |
| Glued state | `κ(φ_c) = κ + 1` at `∞` and every prime; two primes with bounded translations carry it | AKG [L] |
| Primitive part | boost hyperplane = `v₁^⊥` = Markov = harmonic hyperplane; `v₁` = ground state = Kähler class | RIT, HWV [L] |
| Markov form | `W = V_N‖g‖² + J(g) + ½⟨c,g⟩² − ½⟨s,g⟩²`; jump measure archimedean + prime atoms, creation potential `V_N`; RH ⇔ sinh-capacity bound | RHTower `WeilMarkovPoleCapacity` [L] |
| Kähler package | HR transports wherever HL holds; Liouville = HL; RH ⇔ HL on the PSD locus; no free Lefschetz operator | HWV [L] |
| Degeneration | rescaled limit = Jordan-totient form `J₈(m)/φ(m)` below `1/8`; extension data vanish there; inheritance radius `1/8` = receiver; dilations lower conductors; weight strings `p⁷`, `[8]_p` | ADT [L/S] |
| Edge | RH ⇔ no edge; a finite edge is PSD with a zero mode; under ¬RH the tilted-spline edge lies in `[(log N)^{1/9−}, 2(log N)^{1/8+}]` infinitely often | EHT [L] |
| Overlap = aperture = degree | at `c*` margin = synthesis error = `1/log N`; `K·c*` sees radius `½ log K − O(1)`; RH ⇔ every fixed `K` | TM `ReceiverRate` [L] |
| Constant-factor wall | relative residuals decay iff `c⁸ = o(log N)`; at the receiver scale only the exact leading term of the extension data decides | HWV `TheCrossConductorPairings`, ADT [L] |
| Degree laws | ceiling `exp((11/2)a − πe^{2(a−2)})`; near radical `(2 − η)e^{2a}` blind below `2πe^{2a}`; genus function counting distinct resolved zeros; coercive off a finite divisor `D_a` | ArithmeticCompensationTheory, RHTower, ACS [L] |
| Visibility | isolated pair seen at aperture `a` iff `S_δ(a) > (1/2π)log(ξ/2π)`; edge `≈ (cδ log γ)^{1/δ}` in the multiple; companions forced | ACS, RHTower [L] |
| Semilocal | exact `{∞,2}` trace identity through `½ log 3`; no positive semilocal carrier | SP [L/S] |
| Scaling surface | cycles `aH + bV + f`; Castelnuovo–Severi defect = Weil's form; RH ⇔ an effectivity with RR and ample axioms; cone RR ⇔ Hodge (universal floor law); orbit RR ⇔ orientation | ACS, AOG [L] |
| Sections | theta `h⁰` RR on `Spec ℤ` and the pole plane; Künneth `h¹` = count part + `½δ`; on prime-free cycles `½δ` is paid by the Lévy jump count of the Gamma factor (radius `≤ 1/64`); over curves primitive `h¹` = degree of a correspondence, paid by the Stepanov count | AOG, LST [L] |
| Correspondences | Hecke graphs, λ-ring, Rosati involution, Lefschetz trace, theorem of the square; Rosati positivity ⇔ orbit Hodge index ⇔ naive height / convex log-count on the integral Rosati form | AOG, ACP, AET [L] |
| First rung | finite Hodge defect ⇔ bounded heat counts ⇔ bounded collision charges ⇒ `Θ < 1` | AOG [L] |
| Stars and strata | star of `d` ≅ family at `(c⌊N/d⌋/N, ⌊N/d⌋)`; `W = Σ_g Cop(W at the star of g)`; successor + archimedean coupling in `g = 1`; links disconnected; nerve `χ̃ = −M(N)` | HWV [L] |
| Packet identity | Mertens polarization; complete form = jump squares + affine incidence squares + bounded diagonal − shell degree + boundary; coprime successor gap | ACPL, CSAR [L] |
| Heat | `κ(φ_c^{(t)}) − 1 = N(t)/2` = future collision pairs | AKG, RIT [L] |
| Quantum | collision charge = Fredholm index = Wiener–Hopf index; index `0` ⇔ outer Szegő factorization ⇔ disk-unit sectoriality; `κ ≤ sup O`; RH ⇔ `O < 2` per window | CDG, EHT [L] |
| Hecke defect | means ↔ near-line density rates; `o(log U)` ⇔ critical-scale clustering; fixed scale ⇔ corridor; one constant over dyadic scales ⇔ RH | CDG [L] |
| Frobenius at infinity | `σ(ρ) = 1 − ρ̄`; RH ⇔ `σ` trivial ⇔ Hecke similitude of the collided form; `κ = #` moved zeros | EHT [L] |
| Partner angle | resonant states of `ρ` and `1 − ρ̄`: `cos² = 4Reρ(1 − Reρ)`, saturated iff `Re ρ = ½` | RHTower [L] |
| Mayer determinant | `D(w,λ) = A + ζB`; real-`w` cone; signed product = exp of even-word traces; primitive coding of hyperbolic classes | RIT [L] |
| Künneth | `κ(K_ζ⊠K_ζ) ∈ {0, ∞}`; no softening at any horizon | RIT, EHT [L] |
| Finite-index constraints | `κ ≤ r` ⇔ translation-stable positive constraints of dimension `≤ r` | HKT [L] |
| Selection | every prime-set flip separated (zero-density twins below `1/4` included); self-similar flux only for generalized von Mangoldt weights | RIT, ACP, HWV [L] |

The three walls are the three ways a reading of `κ` fails:
- **Σ**: the sign of the complete form is not decided by estimates at the critical exponent. There
  the extension data of the degeneration carry the zeros, the form carries a near radical of doubly
  exponentially small energy, positivity must be glued through the archimedean channel, and only an
  exact (count), quantized or structural producer can decide.
- **Π**: the prime statistics are not precise enough (one-point window error; conjugate diagonal;
  pair surplus), and no count produces the primitive `h¹` past the prime-free window.
- **Γ**: selection of ζ does not produce positivity; every selector is a margin, index or
  counterterm identity, and the one selector that would produce positivity is a naive height on
  the correspondence ring.

## 0.1 The degree axis

| Coordinate | Reading at degree `a` | Anchor |
|---|---|---|
| Overlap multiple `K` of the atomic families | `K ≈ e^{2a}`: radius-`a` tests synthesized on the block `[N/B, N]`, `B ≈ e^{2a+2}` | TM [L] |
| Exponent of the overlap schedule | below the critical exponent the limit polarization is inherited; at it, conductor-Gram positivity is RH | ADT, HWV [L] |
| Aperture of the restricted Weil minimum | `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})`; positive through `181/500`; semilocal `{∞,2}` trace identity through `½ log 3` | ArithmeticCompensationTheory, SP [L/S] |
| Near radical / genus function | dimension `≥ (2 − η)e^{2a}` plus twice the low-zero multiplicity/clustering excess; energy `≤ exp(−η²e^{2a}/(300a))`; blind below `2πe^{2a}` | RHTower, ACS [L] |
| Finite divisor | coercive off `D_a ∪ {i/2}`; Hodge defect at degree `a` finite | ACS [L] |
| Visibility | isolated pairs below `2π exp(2πS_δ(a))` are seen; isolated-pair edge `≈ (cδ log γ)^{1/δ}` | ACS [L] |
| Riemann–Roch | Künneth effectivity on prime-free cycles (count reading to radius `1/64`, estimates to `3/10`), all-profile through `181/500`, and off `D_a` at every degree | LST, SP [L/S] |
| Rank / Jensen degree | rank and degree play the role of aperture in C5 | [D] |
| Over `𝔽_q` | exact radical infinite beyond the genus aperture; defect `0` or `∞`; fakes admit no finite divisor | ACS [L] |

Each fixed degree is a sub-RH, finite-dimensional problem; all degrees together are RH. The
complete-family routes (C1), the glued state (C2) through the ratCorr Grams, the rank/degree routes
(C5), the gluing face (C12) and the Riemann–Roch routes (C13) all read the sign along this
coordinate.

## 1. Equivalence classes of routes

Routes in one class compute the same quantity; a theorem in one class transfers to the others
through the listed identity.

| Class | Common quantity | Routes | Identity joining them |
|---|---|---|---|
| C1 Degree axis / complete family | positivity of the complete Weil family at `K·c*`, equivalently Weil positivity at radius `½ log K` | HF, SRT, AIP, ACT, ACS-atomic; RW, EWU, OWU, MSC | `W_{φ,c,N}` PSD ⇔ `N < h(atom_{c/N})`; block synthesis `K ↔ e^{2R}`; degeneration with inheritance radius = receiver; degree laws [L] |
| C2 Glued state | `κ(φ_c) − 1` on the boost hyperplane | SC, AKG-gluing, RIT-Künneth | `κ(φ_c) = 1 + κ_boost`; boost mass `= √(log N)⟨x, v₁⟩` [L]; ratCorr Grams = complete-family packet Grams at a fixed critical multiple [S] — joins C1 |
| C3 Heat / collision integer | `N(t)/2`, `O(T)`, `ΔO`, window index | WD-charge, SC-heat, LA-heat, TG, HEF | heat index = future collisions; bounded `N` ⇔ bounded `O`; `κ ≤ sup O`; window index = Wiener–Hopf index [L] — joins C1 |
| C4 Odd / Markov sector | odd-sector Doob energy `R ≤ ½`; sinh-capacity | CHMD, TT, AID, SAHT | Markov hyperplane = `v₁^⊥`; Weil form = Markov form + pole plane [L] — joins C1 |
| C5 Rank / degree uniformity | all-rank Hankel, all-degree Jensen, PF signs; Laguerre–Pólya property of `ξ` | TH, HCF, PA, GTA, LA-Jensen; ART (centered approximation) | heated Hankel inertia counts off-line pairs at matched rank [L]; centered curve products close into the Laguerre–Pólya class [L/D] |
| C6 Scheduled prime sums | lower bound of a prime-scheduled energy | FU, CFC, RP, SZ, LI, FEL, EGC | explicit-formula functionals bounded below ⇔ RH [L] |
| C7 Window precision | `ψ(x) − x`, `M(x)`, windowed prime error, inter-tower coupling, nerve Euler characteristic | WL, MC, PBM, RB, JAS, CTF, SC-coupling | `Count(a)` iff `a − 1 ∈ 𝒬`; coupling ≡ kernel = window error; `χ̃(nerve) = −M(N)` [L/D] |
| C8 Selection / typicality | the trivial gauge point among twins | MC-typicality, BAG, XN, PM-selection | RH ⇔ trivial point typical [L] |
| C9 Realization | spectral reality of a constructed operator | RN, PTR, W1C, PM-Mayer | Vitali: normal real-zero approximants force RH; Mayer determinant `D = A + ζB` with even-word trace formula [L] |
| C10 Pre-divisor | a section or potential defined before the divisor | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF | each needs a zero-independent forcing (Γ5) |
| C11 Conjugate diagonal | non-holomorphic depth functionals: Hecke defect, fibre multiplicity, same-point quantum, local counts, pair surplus | WD-Hecke, census, HEF, SRT-local count, IGP, TTPC | `H(γ) ≤` prime polynomial `+ 4E_γ(L)`; `O ∈ 2ℕ`; means ↔ near-line density; census = signed pair surplus [L] |
| C12 Hodge–Lefschetz / gluing | HL on the positive locus; star descent; top gcd stratum; inheritance past the critical exponent | HF-Hodge, ACS-Hodge, RIT renormalized index, EHT zero modes, TG paths | Liouville = HL; transport free; star isometry; gcd stratification; no semilocal carrier; limit polarization inherited exactly to `1/8` [L/S] |
| C13 Sections, correspondences and heights | a count-valued primitive `h¹`; a naive height on the integral correspondence ring | ACS-effectivity, HF-RR, RIT quadratic RR, IRK | universal floor law; Künneth `h¹`; jump-count reading of prime-free cycles; Rosati ⇔ orbit Hodge ⇔ naive height; Lefschetz trace of correctors [L] |

C1, C2, C3, C4 and C12 compute one sign on one hyperplane: C1 along the degree axis, C2 on the
glued state, C3 along the heat parameter and window by window, C4 on the odd sector and as a
capacity, C12 as the deformation form (HR is the sign, HL its content, the top gcd stratum its
location, the critical exponent its regime). C5 and C6 are sign problems on test families that
become RH-complete only in the limit of rank, degree or schedule; C5 also absorbs every
approximation-by-RH-true-objects scheme. C7 and C11 are the precision faces. C13 is the production
face: it would supply C1 and C12 with an exact producer, and its Rosati form is the Γ face. C8–C10
are the selection faces.

## U-Σ — positivity on the primitive part along the degree axis

Core problem: the complete Weil form (primes, prime powers, both poles, Gamma) is nonnegative on
`v₁^⊥` at every degree. Equivalent forms: Weil positivity at every aperture; positivity at every
multiple `K·c*`; HL on the positive locus of the overlap flow; inheritance of the limit
polarization through the critical exponent; no zero mode on `v₁^⊥` [L/D].

| Layer | Status | Anchor |
|---|---|---|
| Inherited regime, tilted spline | all vectors `α < 1/9` with logarithmic confinement and reserve `c^{−8}`; packets `α < 1/8`; mid-band packets `α < 1/4`; top self-form `O(c log c)`; binding term `c⁹` split cross payment | CACT [L] |
| Inherited regime, smooth profiles | logarithmic profile positive on `[1, ε₀·c*]`, budget sharp; every profile without real Fourier zeros has edge `→ ∞` | TM, EHT [L] |
| Degeneration | Jordan-totient limit; extension data vanish below `1/8`; dilation monodromy; weight strings | ADT [L/S] |
| Critical overlap | Denjoy–Carleman / sinc `c* ≍ L(log L)²`; tilted spline `(log N)^{1/8}`; receivers at every fixed multiple; ratCorr Grams realized at a fixed multiple | TM, SSHA, AKG [L/S] |
| Constant-factor wall | relative residuals `O(1)` at the receiver scale; only the exact leading term of the extension data decides | HWV, ADT [L] |
| Degree laws | ceiling; near radical `≈ 2e^{2a}`; genus function reading resolved zeros; finite divisor; visibility; isolated-pair edge; companions | ArithmeticCompensationTheory, RHTower, ACS [L] |
| Small degree | positivity through `181/500`; `{∞,2}` trace identity through `½ log 3`; no semilocal carrier | SP [L/S] |
| Effectivity | RH ⇔ effectivity with RR and ample axioms; cone RR ⇔ Hodge; count classification | ACS, LST [L] |
| Kähler package | transport free; HL on the PSD locus is RH; no free Lefschetz operator | HWV [L] |
| Stars and strata | descent, depth law, Metzler on deep stars; all unpaid coupling in `g = 1`; links disconnected; coprime successor gap | HWV, CSAR [L] |
| Packet arithmetic | jump and affine incidence squares, Mertens polarization, shell degree as the only growing term with explicit rows | ACPL [L] |
| High conductors | single modes coercive on `[(log N)^A, N^θ]`; finite conductor sectors; spans and `m > √N` open | CAF, ACPL [L] |
| Edge | crossing with zero mode; window `[(log N)^{1/9−}, 2(log N)^{1/8+}]` under ¬RH | EHT [L] |

| Face | Routes / programmes | Reduction |
|---|---|---|
| Complete atomic matrix | HF, SRT, AIP, ACT, ACS-atomic, CACT, CAF, RAPT, SSH, SSHA, CSAR, ACPL, TM, ADT | positivity at every `K·c*`; extension data at the critical exponent |
| Aperture ground minimum | RW, EWU, OWU, MSC, CFC, SP | `μ(A) ≥ 0` ∀A; fixed `A` finite-dimensional; next prime aperture `½ log 3` |
| Edge / zero modes / Kähler package | EHT, HWV, RW | HL on the PSD locus |
| Stars / gluing | HWV, CSAR | payment of the top gcd stratum (successor + archimedean) |
| Effectivity / Riemann–Roch | ACS, LST, RIT, HF | a count-valued primitive `h¹` (U-Π production face) |
| Glued state | SC, AKG | `κ(φ_c) < 3` ⇔ positivity on `v₁^⊥` of the ratCorr Grams = complete-family packets |
| Renormalized Hodge index | RIT | definiteness on the primitive part |
| Haar / Doob / odd sector / Markov form | CHMD, AID, SAHT, TT | `R ≤ ½` on odd vectors; sinh-capacity; uniform coarse index |
| Rank / degree / approximation | TH, LA, HCF, PA, GTA, ART | all-rank / all-degree sign = Laguerre–Pólya property |
| Scheduled prime sums | FU, CFC, RP, SZ, LI, FEL, EGC | lower bound on a prime-scheduled energy |
| Heat flow | WD, LA, HEF, SC-heat | no index jump on `(0, 1/8]` |
| Quantum / trace | TG, WD, AID | an integer `< 2`; a sectorial multiplier per window |
| Paths | TG, SC, EHT, ACPL, HWV | source-defined HL along a flow (transport itself is free) |
| Realization | RN, PTR, W1C, PM | spectral reality of a constructed operator |
| Künneth / powers | RIT, EHT | closed: RH-equivalent at every degree and horizon |

## U-Π — precision and production

Core problem: an unconditional exact statement about primes at square-root precision. It takes
four forms:
- the one-point windowed error (kernel, coupling, one-sided count);
- the conjugate-diagonal depth functional (Hecke defect), a near-line density ladder;
- the signed prime-pair surplus beyond bandwidth one;
- a count whose `h¹` is Weil's primitive form, equivalently a naive height on correspondences
  (production).

At the critical exponent Σ meets Π: margin equals residual, so only signed cancellation or an
exact count decides (Π15). The genus function sits beside Π on a separate axis: its upper law is a
statement about multiplicities and separations of zeros (Π16, indep.).

| Face | Routes / programmes | Reduction |
|---|---|---|
| One-sided prime count | WL, PBM, RB, JAS, CTF, ACP, ASRP | `ψ(x) − x ≤ C√x log²x` (Π1) |
| Windowed kernel / coupling | SC, ACPL, AKG, HKT | bounded `K_ζ` ⇔ bounded coupling ⇔ window PNT at `√` precision (Π4) |
| Integer producers | WL, AKLT, AHA | `ε`-uniform producer (Π3) |
| Möbius cancellation / nerve | MC, BVI, CAF, HWV, HTGeometry | moving-scale half-power cancellation; band localization retains `2Θ`; `χ̃(nerve) = −M(N)` (Π1, Π2, Π10) |
| Sections / correspondences / heights | ACS, LST, AOG, AET, RIT, SPTL | count-valued primitive `h¹` past the prime-free window; naive height on `ℤ[ℚ_{>0}^×]` (Π11h, Γ19); logarithmic duality of the split surface (Π11f) |
| Genus function | ACS, RHTower, LST | near radical `(2 + o(1))e^{2a}` ⇔ resolution of the zeros (Π16) |
| Exceptional moduli | MC, CACT, CAF | individual control beyond `(log x)^A` (Π9 = Σ1d) |
| Conjugate diagonal | WD, CDG, RBG, HEF | near-line density rate `≥ 1`; mean `o(log U)` (sub); fixed scale (≥qRH); dyadic one constant (RH) (Π5) |
| Census / pair surplus | SRT, IGP, Zeta23, CDG, TTPC | signed prime-pair surplus beyond bandwidth one (Π7) |
| Averages vs heights | WD, LA, SRT | density-zero exceptions invisible to means (Π6) |
| Critical-scale residual | HF, SRT, AIP, ACS, TM, ADT | signed cancellation of the extension data at `K·c*` (Π15) |
| Prefix scale | WD, CDG | stabilization at prefix `T^{O(1)}` (lower bound `c√T`) (Π13) |
| Subconvexity | LA, WD, AHA | heat floors `133/200` (slice), `2/3` (flow) (Π12) |
| Candidates | APF, EWJ, FEL, WBF, IRK | integral counts from a source lift |

Identities [L]:
- one-sided count ⇔ `κ = 0`;
- coupling rate = zero width;
- prime-error budget `≥ 2 + γ − log 4π`;
- Farkas duality between producers and Möbius log-harmonic measures;
- the prime polynomial is self-absorbed by the Hecke defect at log scale;
- counts + linear explicit formula cannot bound the Hecke defect;
- dyadic means ⇔ near-line density rates; mean `o(log U)` ⇔ critical-scale clustering;
- quadratic RR ⇔ renormalized Hodge index; cone RR ⇔ Hodge index;
- Künneth `h¹` = count part + `½δ`; on prime-free cycles `½δ` = jump count + constant + pole term;
- Rosati positivity ⇔ naive height on the integral Rosati form ⇔ midpoint-convex log-count;
- genus law ⇒ almost all zeros simple and isolated.

## U-Γ — selection of ζ

Core problem: a source-defined mechanism that both distinguishes ζ from its twins and produces
positivity. The distinguishing half is closed for prime-set flips. The producing half is Frobenius
at infinity, which has four RH-equivalent readings and a fifth form as Rosati positivity of the
correspondence algebra, i.e. a naive height on the integral Rosati form.

| Face | Routes / programmes | Status / reduction |
|---|---|---|
| Typicality of the trivial point | MC, AGT, BAG, XN | RH ⇔ trivial point typical (Γ1) |
| Gluing of the global pole | SC, AKG, RIT | classified: only the extremal weight has one square; glue pole-blind (Σ11, Γ11) |
| Margin, index and edge selection | RIT, ACP, HKT, EHT, ACPL, RAPT | every prime-set flip separated with an exact resolution threshold; zero-density twins below `1/4` by the conductor series (Γ2) |
| Counterterm selection | HWV | self-similar star flux ⇔ generalized von Mangoldt weight (Γ18) |
| Gauge fixing | ALG, AES | entrywise-nonnegative gauges only on archimedean characters (Γ12) |
| Local renormalization | AKG | counterterms make `Λ` and a twin both index `1` (Γ14) |
| Frobenius at infinity | PL, CDG, RBG, EHT, PM, AOG, AET | defect involution; Hecke similitude; dyadic Hecke constant; partner saturation; Rosati positivity; naive height (Γ4, Γ19) |
| Physical / native source | PM; PW-B retired | source-uniform extinction is a no-go; algebraic recentering impossible; the modular surface selects ζ for PM (Γ13, Γ17) |
| Pre-divisor constructions | BSH, CDC, HJ, SEC, PCS, RFHM, DR, EWJ, APF, WBF | a section / potential defined before the divisor (Γ5) |
| Function-field calibration | ACS (`𝔽₃`), AKG (`𝔽_q(X)`), RIT, EHT, ACPL, LST, HWV, AET | local walls identical; `ℤ` differs by infinite genus with finite divisors, disconnected links, incommensurable towers, and the absence of a naive height (Γ10) |
| Selection → sign | all selectors | no selector produces complete-form positivity (Γ16) |

## 2. Cross-family seams

| Seam | Statement | Routes on the seam |
|---|---|---|
| Σ: one hyperplane | glued index, complete-Weil sign, Markov criterion, renormalized Hodge index and HR of the Kähler package are positivity on `v₁^⊥` | SC, HF, SRT, AIP, ACS, CHMD, RIT, HWV |
| Σ: one axis | overlap multiple = synthesis blocks = radius = degree = aperture | HF, SRT, AIP, RW, EHT, TM, ACS, LST [L] |
| Σ: one regime | inherited regime (estimates, Jordan-totient limit) below the critical exponent; extension data of the order of the limit at it; constant-factor wall = HL = top gcd stratum there | CACT, TM, HWV, SSHA, ADT, EHT [L/D] |
| Σ ∩ Π: degree laws | ceiling, near radical blind below the Landau height, finite divisor; each degree finite-dimensional, all degrees RH | RW, ACS, RHTower, ArithmeticCompensationTheory [L]; [D] |
| Π: resolution axis | the genus function reads distinct resolved zeros; its upper law is almost-all simplicity, independent of the sign | ACS, RW [L] |
| Σ: zero modes | a finite edge is a zero mode of a PSD form; successor + dyadic rigidity confines incidence kernels to constants; Liouville = HL | EHT, CSAR, ACPL, HWV |
| Σ: gluing | stars positive locally; all successor and archimedean coupling in the top gcd stratum; links disconnected; no semilocal carrier; HL = paying `g = 1` | HWV, SP, HF, ACS [L/S] |
| Σ: Markov form | Weil form = jump energy (archimedean + prime atoms) + creation potential + pole; the pole is the only anti-Markovian term; RH = a capacity inequality | CHMD, TT, RW, LST [L] |
| Σ ∩ Π ∩ Γ: correspondences | a naive height on correspondences would give sign (Hodge index), precision (Castelnuovo–Severi) and selection (graph classes) at once, as over `𝔽_q`; the algebra, the theorem of the square and the Lefschetz trace exist over `ℤ` | ACS, LST, AOG, AET, ACP, RIT, HF, SC [L/D] |
| Σ ∩ Π: counts at small radius | on prime-free cycles the primitive `h¹` is a Lévy jump count to radius `1/64`; over `𝔽_q` the Stepanov count pays it | LST [L] |
| Σ ∩ Π: unattained width | cone, tower and escape receivers leave "`Θ` not attained"; attainment implies `Θ < 1` | ACPL, AKLT, PM [L/D] |
| Σ ∩ Π: quantization | RH = an even integer `< 2`; window index = Wiener–Hopf index, index `0` ⇔ outer Szegő factorization; readings stabilize only at prefixes `≥ c√T` | WD, TG, SC, HKT [L/S] |
| Σ ∩ Π: critical-scale residual | at `c*` margin = residual; the sign needs signed cancellation of the extension data | HF, SRT, AIP, TM, CSAR, HWV, ADT [L/D] |
| Σ ∩ Π: kernel = coupling = window error | bounded kernel, bounded coupling, no edge, window PNT at `√` precision are one statement | SC, ACPL, EHT, WL, HKT |
| Σ ∩ Π: conductor levels | residual control in the Siegel–Walfisz range; single modes to `N^θ`, `θ < ½`; above `√N` Elliott–Halberstam type | CACT, CAF, MC |
| Σ ∩ Π ∩ C11: collisions | `H(γ)` bounded by prime polynomial + Hecke defect; `ΔO ≤ 2·max H·n_off`; bounded `ΔO` ⇒ density one | WD, CDG, SRT, census |
| Π: means vs heights | means and density statements cannot exclude density-zero clusters; finite apertures exclude isolated zeros but not clusters; a fixed multiple misses shallow high zeros | WD, LA, SRT, RW, census |
| Π: precision ladders | Hecke means ↔ near-line density rates (gate closed on `(0, ½)`); census ↔ pair surplus beyond bandwidth one | WD, CDG, TTPC, IGP |
| Σ: approximation | approximation by RH-true objects (curve numerators, Lee–Yang, heat, lossless stacks) lands in the Laguerre–Pólya class | ART, W1C, PTR, LA, TH [L/D] |
| Σ ∩ Γ: gluing | the archimedean place supplies the one square; the glue is pole-blind | AKG, SC, RIT |
| Σ ∩ Γ: Frobenius at infinity | reflection pairing (Weil form) vs conjugation pairing (collided form, resonant partners); their identity is RH; Rosati positivity and the naive height are the same statement | EHT, PL, CDG, HF, PM, AOG, AET |
| Σ ∩ Γ: counterterm self-similarity | stars carry the same form for every weight; only the counterterm selects, through `Λ ∗ 1 = log` | HWV, HF, SC |
| Γ: selection without sign | every selector is a margin, index or counterterm identity on a partial form | RIT, ACP, ACPL, ALG, AES, EHT, HWV |
| Σ: paths | crossing-free deformation ⇔ positivity; Kähler transport free; content = HL | TG, SC, WD, EHT, ACPL, HWV |
| Archimedean channel | the archimedean place glues `+` and `×`; coprime atoms couple only through it (Gamma, poles, successor shells); it is the source of the finite divisor (Gamma dominance) and, on prime-free cycles, a Lévy jump count | AKG, ALG, CHMD, RIT, ACPL, HWV, ACS, LST [L/D] |

## 3. Route → core map

| Route | Core | Class | Face |
|---|---|---|---|
| WL | Π | C7 | one-sided count, producers |
| RW, EWU, OWU | Σ (Γ) | C1 | the degree axis itself; semilocal trace; selectivity |
| FU, CFC, RP, SZ, LI | Σ | C6 | scheduled prime sums |
| PA, TH, LA, HCF, GTA | Σ | C5 | rank / degree sign (Laguerre–Pólya) |
| MC | Π (Γ) | C7, C8 | Möbius cancellation; band localization; typicality |
| TT | Σ | C4 | odd / directed covariance |
| TG | Σ | C3, C12 | quantum; source-defined HL along paths |
| HF | Σ (Π, Γ) | C1, C12, C13 | complete family at the critical exponent; degeneration; Kähler package; stars and strata; correspondences and heights |
| SRT, AIP, ACT | Σ (Π) | C1 | complete atomic matrix; edge; zero modes |
| SC | Σ, Π (Γ) | C2, C7, C3 | glued state = complete-family packets at a fixed critical multiple; coupling = window error; heat homotopy |
| CHMD | Σ | C4, C1 | Haar / Doob / odd sector; Markov form |
| RN | Σ | C9 | realization |
| WD | Σ, Π | C3, C11 | window index (Wiener–Hopf); Hecke-defect / density ladder |
| PM | Γ (Σ) | C8, C9 | Mayer determinant and word traces; resonant states; partner saturation |
| JAS, CTF, PBM, RB | Π | C7 | one-sided count |
| XN, BAG | Γ | C8 | typicality / recurrence |
| ACS | Π (Σ, Γ) | C13, C1, C12 | count-valued primitive `h¹`; naive heights; genus function; atomic; curve calibration |
| APF, EWJ, WBF, IRK | Γ (Π) | C10, C13 | source lift with integral count |
| BSH, CDC, HJ, SEC, PCS, RFHM, DR | Γ | C10 | pre-divisor constructions |
| EGC, FEL, MSC | Σ | C6, C1 | contour / likelihood / Sonin |
| PTR, W1C | Σ | C9, C5 | realization; approximation by RH-true objects |
| PW-B (retired) | Γ | — | source-uniform extinction refuted |

## 4. What a closing argument must supply

Over `𝔽_q` one object, the Frobenius graph on `C × C`, supplies all three readings: the Hodge index
gives the sign, Riemann–Roch (or Stepanov's count) gives the count, the graph is canonical. A
curve's edge is `≤ 2g`: a bounded aperture decides; its towers are commensurable and its links
connected; its primitive `h¹` of a graph is the degree of a correspondence, a naive height. Over
`ℤ` the corpus has each ingredient separately:

| Needed | Present over `ℤ` | Missing |
|---|---|---|
| Positivity by identity | packet identity; Mertens polarization; local pole–successor forms; archimedean form on `ℓ = 0` = dilation form + shell squares; Markov form; matched prime form with one positive direction on every finite sieve; star isometry; gcd stratification; coprime successor gap | an identity for the shell degree jointly with the pole; an SOS identity for the dilation form on one two-prime lattice; payment of the top gcd stratum |
| Positivity uniform in degree | inherited regime with Jordan-totient limit; rough regime to `ε₀·c*`; Weil floors through radius `181/500`; receivers at every `K·c*`; coercivity off the finite divisor at every degree | the extension data at the critical exponent; a mechanism exact on the near radical (the ceiling and the near radical exclude estimates there) |
| Nondegeneracy (HL) | Kähler transport; Liouville = HL; star descent; deep stars positive; inheritance of the limit polarization below `1/8` | HL on the positive locus; inheritance through the critical exponent; a cross-tower gap through the archimedean channel |
| Gluing | exact gcd stratification; Möbius gluing of stars; two-prime cyclic orbit carries the defect | a global payment of the top stratum (no local or semilocal carrier exists) |
| Precision | one-sided count ⇔ RH; kernel = coupling = window error; producers to the main term; Hecke means `O(log U)` on `(0, ½)`; near-line density at rates `< 1`; census certificate | square-root input for one-point windows; near-line density at rate `≥ 1` and clustering; the pair surplus beyond bandwidth one |
| Count from geometry | theta `h⁰` with RR on `Spec ℤ` and the pole plane; scaling surface with RH ⇔ effectivity; Künneth `h¹`; jump-count reading of prime-free cycles; boost transform restoring the Euler product; correspondence algebra with λ-ring, theorem of the square and Lefschetz traces; Tate's limit law | a naive height on `ℤ[ℚ_{>0}^×]` at bounded distance from the Rosati form; a section theory whose primitive `h¹` is a count past the first prime, on lattices of growing rank, with a logarithmic Serre duality for the split surface |
| Genus | near radical `≥ 2e^{2a}`; genus function reading resolved zeros; finite divisor at every degree | the identification of the genus function with the `h¹` of the section theory; its upper law is almost-all simplicity (independent of RH) |
| Canonical selector | every prime-set flip separated; coupling diagonal; gauge fixing; self-similar counterterm; modular surface for PM | Frobenius at infinity as an operator: Rosati positivity / naive height, a conformal correspondence of factor `≠ 1`, a Hecke similitude of the collided form, or partner saturation |
| Integrality with homotopy invariance | collision charge as Fredholm / Wiener–Hopf index; heat index as Pontryagin homotopy; index constant on nondegenerate paths | a source-defined sectorial multiplier on every window, or a source-defined noncrossing mechanism; a separation input for prefix stabilization |
