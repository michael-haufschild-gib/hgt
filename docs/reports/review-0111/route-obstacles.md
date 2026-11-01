# Route obstacles — status quo

Scope: the 33 live routes, the 16 candidates, the retired PW-B branch and the ADT programme, read
against the Lean corpus at `b4bf677c56` with the working tree, the programme READMEs in `formal/`
and the pipeline cards. For every route: what is established, the research status of its open
obligations, the obstacles that are **(A) just work**, and the obstacles that are **(B) open
mathematics**. Just work means known mathematics, finite or kernel-certified computation,
effectivization, finishing a formalization or a paper proof in progress, or composition of proved
statements. Open mathematics means a statement nobody knows how to prove.

Evidence: `[L]` Lean; `[S]` Lean in the working tree or unintegrated; `[P]` complete paper proof,
Lean pending; `[D]` derived here from Lean statements, not formalized.

Strength of a B-item: **RH** equivalent to RH; **≥qRH** implies Lindelöf and a zero-free
half-plane; **LH** implies Lindelöf; **sub** strictly weaker or of unknown strength; **indep.** not
implied by RH and not known to imply it; **method** a missing tool, not a statement.

Wall labels Σ/Π/Γ refer to `walls-ledger.md`. Programme codes follow the frontier-map source
locator; further codes: ACPL = ArithmeticCouplingTheory, ADT = ArithmeticDegenerationTheory,
AET = ArithmeticEffectivityTheory, AOG = ArithmeticOrientationGeometry, ART =
ArithmeticResonanceTheory, BOT = Bottcher, CSAR = CriticalScaleArithmeticRigidity, EHT =
EdgeHodgeTheory, HWV = HodgeTheoryWithoutVarieties, LST = LatticeSectionTheory, RIT =
RenormalizedIntersectionTheory, SP = SelectivePositivityAndThresholdLaws.

## 0. Calibration (applies to every route)

| Fact | Anchor | Consequence |
|---|---|---|
| `κ = #` distinct right-half zeros, even; RH ⇔ `κ < 2`; finite `κ` ⇒ all high zeros critical ⇒ `Θ < 1` | AOG `TheIndexExit` [L] | every index route ends in one even integer; finite-index waypoints are ≥qRH |
| Edge logic: a statement proved without zero information holds on every datum sharing that information, so it stops below the edge of off-line members; an integer read at an RH-complete resolution is RH | EHT; ADT README [L/D] | only an identity, an inherited polarization or an integer with a structural bound can cross the edge (ADT's carriers: counts, traces, quantized readings) |
| Bounded Weil kernel ⇔ RH; coupling ≡ kernel; one lattice `⟨p⟩×⟨q⟩` decides; the Hecke orbit of one spectrally generic test under `ℤ log p + ℤ log q` carries the whole Hodge defect | RIT; ACPL; ACS `TheHodgeDefectIsCyclic` [L] | every boundedness target is RH; one rank-two orbit suffices |
| Glued state `κ(φ_c) = κ + 1` at every place; two primes with translations in `ℤ[1/qr]` carry it | AKG [L] | RH ⇔ `κ(φ_c) < 3` |
| One gluing at the pole: the divisibility form `[i∣j]` is unipotent; gluing every vertex to the pole gives Redheffer's matrix, `det = M(N)` = nerve Euler characteristic; the coprimality form has signature `M(N)` | ADT `TheMertensFunctionIsAGluingDeterminant`; HWV; RHTower [L/S] | the arithmetic of `μ` and the one negative square of the glued state are created by one rank-one coupling at the pole |
| No softening: Künneth, Hadamard and tensor powers are all-or-nothing | RIT; EHT [L] | amplification never helps |
| Kähler package: HR transports wherever HL holds; Liouville = HL; RH ⇔ HL on the PSD locus; none of the three Lefschetz candidates is free | HWV [L] | deformation costs nothing and proves nothing |
| Overlap = aperture: a multiple `K·c*` sees radius `½ log K − O(1)`; RH ⇔ positivity at every fixed `K`; every divergent rate is a receiver; finite rational Grams are complete-matrix compression limits at a family-dependent fixed multiple, and RH ⇔ eventual pole-hyperplane positivity at every fixed critical multiple | TM `ReceiverRate`; RIT `TheHodgeIndexAtCriticalOverlap` [L] | the overlap multiple is the aperture axis; the glued-state Grams are faces of the complete family |
| Degeneration: the complete family is a degenerating polarized family; below the exponent `1/(β+1)` (`1/8` for the tilted spline) the rescaled family converges to the Jordan-totient form `J(m) ∝ J_{β+1}(m)/φ(m)`, a tensor product of weight strings over the primes, exact uniformly on the subthreshold block `m ≤ c/X(ε)`; its extension data vanish and fixed packets inherit positivity; the limit is zero-blind; at every multiple of `(log N)^{1/8}` conductor-Gram positivity is RH | ADT [L/S] | the inherited regime ends exactly at the receiver; there the second-order term carries the zeros |
| Tilted spline: all vectors positive for `c ≤ (log N)^α`, `α < 1/9`, with logarithmic defect confinement and reserve `c^{−8}`; fixed and polylogarithmic packets for `α < 1/8`; collective mid-band packets for `α < 1/4`; top prime self-form `O(c(1 + log c))`; under ¬RH the edge lies in `[(log N)^{1/9−}, 2(log N)^{1/8+}]` infinitely often | CACT; SSHA; EHT [L/S] | the all-vector rough regime stops one exponent step below the receiver |
| Zero-free logarithmic profile: positive definite for `1 ≤ c ≤ ε₀·c*`, `ε₀ = 1/[103424(8π/3 + 3000)]`, optimal for the reciprocal-floor budget system; RH ⇔ positivity at every `K·c*` | TM [L] | the rough regime is closed up to a constant factor; larger multiples need a better floor or residual estimate |
| Constant-factor wall: relative cross-conductor residuals decay iff `c⁸ = o((log N)^{1−ε})`; at `c⁸ ≍ log N` what remains is a constant, not an exponent | HWV `TheCrossConductorPairings` [L] | estimates stop exactly where the receiver starts |
| Aperture ceiling `μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})` | ArithmeticCompensationTheory [L] | no positive floor along unbounded apertures |
| Near radical: dimension `≥ (2 − η)e^{2a}` plus twice the low-zero multiplicity/clustering excess, energy `≤ exp(−η²e^{2a}/(300a))`, blind below `2πe^{2a}`; the genus law forces almost all zeros simple | RHTower; ACS [L] | its exact size is a statement about multiplicities |
| Finite divisor: coercive off `i/2` and a finite grid `D_a` at every degree; Hodge defect at degree `a` finite; over `𝔽_q` it is `0` or `∞` | ACS [L] | each degree is a finite-dimensional problem |
| Visibility: an isolated pair is seen at aperture `a` iff `S_δ(a) > (1/2π)log(ξ/2π)`; its edge in the multiple is `exp(min(x/δ, L))`, between `(4δL)^{1/δ}` and `(6δL+1)^{1/δ}`; companions forced | ACS; RHTower [L] | a fixed multiple misses shallow high zeros; clusters survive |
| Markov form: `W = V_N‖g‖² + J(g) + ½⟨c,g⟩² − ½⟨s,g⟩²`; RH ⇔ sinh-capacity bound at every level | RHTower `WeilMarkovPoleCapacity` [L] | the sign is a capacity inequality with a creation potential |
| Semilocal and trace carriers: exact `{∞,2}` trace identity through `½ log 3`; zero-form operator positive on `0 < a ≤ 181/500`; no `{∞,p}` semilocal family carries positivity; the archimedean trace carrier's middle operator `1 − P − P̂` is negative on time-limited vectors | SP; RHTower CCM [L/S] | positivity is glued, never semilocal; trace identities are not positivity |
| Universal floor law; RR on an orbit ⇔ orientation | ACS; AOG [L] | no cone-type effectivity is sign-free |
| Section counts: Künneth RR `h_K(x) + h_K(−x) = ½x² + h¹_K + ½δ`; bidegree, fixed-rank, definite and Siegel counts excluded; on prime-free cycles of radius `≤ 1/64` the primitive `h¹` is paid by the Lévy–Khintchine jump count of the Gamma factor; over `𝔽_q` the Stepanov count pays it | LST [L] | the sign is a primitive `h¹`; a count pays it at small radius and over `𝔽_q` |
| Correspondence algebra: λ-ring, Rosati involution, Lefschetz trace, theorem of the square free; Rosati positivity ⇔ naive height (or midpoint-convex log-count) at bounded distance from the integral Rosati form | AOG; ACP; AET [L] | the missing input is a height nonnegative for an arithmetic reason |
| Hecke defect: dyadic means `O_c(log U)` for all `c < 1/2`; ladder ⇔ near-line density rates `r < 2c*`, `c* ≤ 2/3`; near-line density at every rate `r < 1`; `o(log U)` ⇔ critical-scale clustering; one dyadic constant ⇔ RH | CDG [L] | WD's precision ladder is a near-line density ladder |
| Quantization: window index = Wiener–Hopf index; index `0` ⇔ outer Szegő factorization ⇔ disk-unit sectoriality; prefixes `≥ c√T` are necessary; unit windows stabilize at prefix `Θ(√m)` without separation input; `Θ(√m)`-prefix Szegő positivity at logarithmic resolution ⇔ inverse-logarithmic zero-free corridor, at polynomial resolution ⇔ RH | CDG `SzegoCollision` [L/P] | RH = a sectoriality condition on polynomial-size integer data per window |
| Mayer determinant: `D(w,z)D(w,−z) = Π_c Π_{m≥0}(1 − z^{2ℓ(c)} exp(−(w/2+m)L_c))` over primitive digit-pair cycles, `L_c` the hyperbolic translation length; `Re w > 1` near `z = 0`, `\|z\| ≤ 1` for `Re w > 2` | RIT `GaussMayer*` [L] | PM has a Selberg-type product; geodesic multiplicities and the scattering link are open |
| Unattained width; selection of every prime-set flip; Frobenius at infinity with four RH-equivalent readings | ACPL, AKLT, RIT, ACP, HWV, EHT, CDG [L] | selection among flips closed; selectors are margins |
| Heat floors `133/200` (slice), `2/3 + ε` (flow); census `0.6725`; approximation by RH-true objects closes into the Laguerre–Pólya class | RHTower; IGP; TTPC; ART [L/D] | size floors; pair-surplus ladder; approximation lands in C5 |

## 1. Shared obstacle blocks

### S1. Complete Weil family across the critical overlap
Routes: HF, SRT, AIP, ACT, ACS-atomic, RW, EWU, OWU; SC through the ratCorr Grams; CHMD through
the index; TT through the odd/Markov sector.

Established:
- Tilted spline [L]: all vectors on `1 ≤ c ≤ (log N)^α`, `α < 1/9`, reserve
  `(a₀/c⁷)(poleDefect − C log(2c)‖x‖²) + (κ₀/(2c⁷))‖x‖²`, confinement `poleDefect ≤ C log(2c)‖x‖²`,
  reserve `c^{−8}`; fixed and polylogarithmic packets `α < 1/8`; collective mid-band packets
  `α < 1/4`; receiver at every `K(log N)^{1/8}`. Top prime self-form `O(c(1 + log c))` [S].
- Shell degree `0 ≤ n·d_n ≤ 2(log 4 + 4)e^{5/2}c + 2e^{3/2}c(n/N)(log n + 1)` with packet payment
  bound [L]; coprime successor gap beyond `K ≥ Q(Q−1)` [L].
- Degeneration (ADT) [L/S]: Jordan-totient limit, inheritance radius, monodromy, weight strings,
  tensor law, uniform subthreshold law.
- Logarithmic profile [L]: positive on `[1, ε₀·c*]` with the optimal budget coefficient.
- Complete-matrix compressions realize every finite rational Gram at a family-dependent fixed
  multiple; RH ⇔ eventual pole-hyperplane positivity at every fixed critical multiple [L].
- Cross-conductor channels: relative control decays exactly while `c⁸ = o(log N)`; mean square
  `o(ΣE_e²)` past `1/8` [L].
- Degree laws, visibility, isolated-pair edge, companions [L]; Weil floors through radius `181/500`
  [L]; operator positivity on `0 < a ≤ 181/500` and the `{∞,2}` trace identity through `½ log 3`
  [L/S].

Research status (1/9 → 1/8): three `c⁹` payments must drop to `c^{8+o(1)}` — prefix–terminal
reserve, band–terminal cross, inverse-energy residual. Refuted: smallness of the prefix–terminal
non-ratio block `NR_PT` on terminal-pole-orthogonal vectors. Survivor: `NR_PT ≈ σ â ⊗ p̂ + E`,
`σ ≍ c√log N`, with target `‖E‖² ≤ c(log N)^{1+δ}`, `δ = 1 − 8α`; a paper plan (global pole
orthogonality, log-smoothing at PNT precision, Mertens-level row decay) is in progress.

| | Obstacle |
|---|---|
| A1 | Tilted spline from `α < 1/9` to `α < 1/8` on all vectors along the plan T1–T4 (far reserve through the rank-one coherent part of `NR_PT` and log-smoothing; band–far cross through the `S → S` Schur bound `O(c√log c)`; inverse-energy residual split at `log X_* = (log N)^{1/8}`). Risk: if the log-smoothing step does not close, the remainder `E` is a shifted prime-pair correlation and the item becomes B-type (sub). |
| A2 | Explicit constants: horizons `N₀` for the `1/9` theorem, the logarithmic profile and the receivers; numerical constants of the complete conductor residuals; effective growing-overlap schedules. |
| A3 | Kernel-certified Weil positivity at `½ log 3` and the next prime apertures: the finite divisor and the `{∞,2}` trace identity reduce each to a finite Schur complement (near-radical dimension `≈ 2e^{2a}`, `≈ 6` at `½ log 3`); numerics must be proved in the kernel. |
| A4 | ADT tools: rescaled limits for twisted weights (prime-flip and Liouville twins); the pure block `m ≫ c` with its `log m` asymptotics; uniform limiting structure on growing blocks including the extension data; the explicit first-order correction to the Jordan limit below `1/8`. |
| A5 | Close the `[S]` status: top prime self-form, weight strings / tensor law / subthreshold law, semilocal trace and obstructions, Künneth to `181/500`. |
| A6 | The prime-successor comparison `½A_N(F) ≥ (1/64)[Σ_{Q<p≤N/16Q²} log p/p]·(nonconstant mass)` and its combination with the exact packet identity, retaining shell, pole and archimedean terms at fixed and growing overlap. |
| B1 | Positivity at every fixed multiple `K·c*` (all-aperture Weil positivity; pole-hyperplane positivity of the complete matrix at every fixed critical multiple) — **RH** over all `K`; each fixed `K` is **sub** (Σ1). |
| B2 | The second-order term of the degeneration at the critical curve `c⁸ = K log N`: the limit of the rescaled extension data on fixed packets, its dependence on the zeros and its sign; the constant of the leading `c/log N` term against `κ₀` — **RH** over all `K` (Σ1i, Π15). |
| B3 | Critical-scale identification: the fixed-`K` limit form as Weil's form at radius `½ log K` plus a coercive conductor part — **sub** (Σ1i). |
| B4 | Joint shell–pole and non-arithmetic Gamma-graph payment on growing packets (confinement exponent `≤ 8`) — **sub** (Σ1c, Σ1g). |
| B5 | Low-conductor spans below `(log N)^A`; conductors `N^{½} < m ≤ N` (Elliott–Halberstam type) — **sub** (Σ1d, Σ1e). |
| B6 | Exact sum-of-squares identity for Weil's dilation form on one two-prime lattice — **RH** (Σ18). |
| B7 | Cluster exclusion below the Landau height — **sub** (Π8). |
| B8 | One universal fixed multiple exhausting the full index (the radius-`R` argument needs `K > 1152e·sincTailConst·blockSize(R+1)`) — **method**. |

### S2. Kähler package, stars and gluing
Routes: HF, ACS-Hodge, AIP, TG, SC, RW, MC (gluing determinant).

Established [L]: Kähler package; fixed-overlap limit form degenerating to `0`; stars as lower
horizons with depth law `log d − C₀`; Metzler gauge on deep stars; gcd stratification with all
successor and archimedean coupling in `g = 1`; links disconnected; nerve `χ̃ = −M(N)` = Redheffer
determinant = coprimality signature; conductor ↔ star duality; conductor Gram PSD at every
`2K(log N)^{1/8}` ⇔ RH; no semilocal positive carrier [S]; cyclic Hodge defect on a two-prime
Hecke orbit; Margulis–Gabber–Galil affine expanders on `(ℤ/n)²` (no Weil-form link); squarefree
complex: star of `2` a cone, complementary faces = odd squarefree `m ∈ (N/2, N]` [L].

| | Obstacle |
|---|---|
| A7 | Quantitative depth law `d₀(c)`; explicit star horizons. |
| A8 | Finite-`N` tabulation of the gcd strata and of the top-stratum deficit. |
| A9 | Björner's theorem: the squarefree complex is a wedge of spheres of dimension `ω(m) − 1`, one per odd squarefree `m ∈ (N/2, N]` (topological step and integral homology). |
| B9 | HL on the positive locus of the overlap flow — **RH** (Σ2). |
| B10 | Gluing across the coprime stratum: pay the top gcd stratum (successor + archimedean coupling; a sum–product inequality on conductor packets) by the root defect, the coprime successor gap and the star depth margins — **RH** (Σ3a). |
| B11 | A cross-tower spectral gap through the archimedean channel (Garland/trickle-down unavailable; semilocal carriers excluded) — **method**; uniform version **RH** (Σ23, Σ25). |
| B12 | Loop-Eisenstein band-pole noncancellation — **RH** (Σ19). |

### S3. Index and finite off-line support
Routes: HKT, AKLT, AID, SRT towers, CHMD index, SC, RIT-Künneth.

Established [L]: finite-index kernels = PD minus `κ` unitary characters; `κ ≤ r` ⇔
translation-stable positive constraints of dimension `≤ r`; collision mass `2(κ + excess)`;
finite defect at every degree.

| | Obstacle |
|---|---|
| B13 | Arithmetic index ceiling uniform in resolution — **≥qRH** for `K_ζ`; **RH** for `K_ζ ⊠ K_ζ` (Σ4). |
| B14 | Exclude a finite nonzero Weil index (zero–one law `κ ∈ {0, ∞}`) — **sub**. |

### S4. Heat, collision charge, Szegő positivity and Hecke defect
Routes: WD, LA, TG, HCF, SC-heat, TH-heat; census; HEF.

Established:
- Heat state `κ(φ_c^{(t)}) − 1 = N(t)/2`; heat index one for every `c > 0`, `t ≥ 1/8`; bounded `N` ⇔
  bounded `O`; nonreal count `≤ C·R(t)log(2 + 3R(t))`, `R(t) ≈ 2π exp((2/3 + ε)/t)` [L].
- Window index = Wiener–Hopf index with the six-way index-zero equivalence; arithmetic reality of
  the collision loop [L]; strip zeros of theta prefixes `Θ(N² log N)`, artifact-free prefix
  `≥ c√T` [L]; separation-free stabilization at prefix `Θ(√m)` on unit windows and
  `O(T log²(T+S))` cumulatively; `Θ(√m)`-prefix Szegő positivity: logarithmic resolution ⇔
  inverse-log corridor, polynomial resolution `60m` ⇔ RH [P].
- Hecke defect [L]: half-gate `c < 1/2` closed (means and unit-window sup), density TFAE to `2/3`,
  near-line density at every rate `r < 1`, corridor `(1 + ε)loglog T/log T`, one-sided mollified
  Green–Jensen ceiling, superharmonic critical-line no-go, unit-window min/mean/sup/`C²` calculus.
- Heat slice floor `133/200`; flow floor `2/3 + ε` [L].

| | Obstacle |
|---|---|
| A10 | Formalize the separation-free polynomial-prefix stabilization and the Vinogradov–Korobov corridor bridge (Burnol selection, convex Boutroux–Cartan avoidance, Rouché basins). |
| A11 | Flow threshold `Λ_X` from the sub-Weyl profiles. |
| A12 | `ΔO = o(log T)` ⇒ density one ⇒ Lindelöf in one statement. |
| A13 | Computable stopping prefix with kernel-certified interval bounds. |
| B15 | Subcritical heat count `N(t) ≤ exp(At^{−a})`, `a < 1` — **sub**. |
| B16 | Pointwise heat horizon constant `< ½` — **≥qRH**. |
| B17 | A source-defined sectorial multiplier `F` (`Re(F·Λ) > 0` on the circle) for the `Θ(√m)`-prefix collision loop of every window: at logarithmic resolution **≥qRH**; at polynomial resolution **RH** (Σ5). |
| B18 | Cumulative charge `O(T) = o(N(T))` — **sub**. |
| B19 | Uniform increment `ΔO = o(log T)` — **LH**. |
| B20 | Hecke defect at doubly-logarithmic scale — **sub**. |
| B21 | Log-free near-line density at rate `r ≥ 1` (extends the `O(log U)` gate into `½ ≤ c < 2/3`) — **sub** (Π5). |
| B22 | Dyadic mean `o(log U)` ⇔ 100% critical-scale clustering — **sub** (Π5). |
| B23 | Pointwise `E_γ(c log T) = O(1)` — **≥qRH**. |
| B24 | One constant over dyadic scales — **RH** (Γ4, Π5). |
| B25 | An arithmetic input beyond counts and the linear explicit formula for the conjugate diagonal — **method**. |

### S5. Counts, producers and Riemann–Roch
Routes: WL, MC, PBM, RB, JAS, CTF, ACS-effectivity, HF-RR, RW; census.

Established [L]: one-sided count ⇔ RH; multivariate parity producers reach `(1 + ε)x + C_ε log²x`;
every individual producer has slope `> 1`; integer-Chebyshev ceiling `exp(−0.87n)`; Redheffer
determinant `M(N)`; theta `h⁰` with RR on `Spec ℤ` and the pole plane; universal floor law;
Künneth RR; bidegree blindness; rank law; definite fakes created by the boost (self-dual point
zero-free); Siegel majorant ⇔ Hodge; isotropic count `ζ²`; boost transform restoring the Euler
product; Hecke similitudes of primitive `h¹`; prime-free jump count paying `|Ω(0)|` to radius
`1/64`; Stepanov count paying primitive `h¹` over `𝔽_q`; Künneth effectivity to `181/500` [S];
genus function reading resolved zeros, genus law ⇒ almost all simple; census `0.6725`, cosine
certificate.

| | Obstacle |
|---|---|
| A14 | Count reading of the whole prime-free window: a Poincaré inequality for the Lévy form on an interval (interior jumps) and the pole signs (`+2A²` even, `−2A²` odd); the target `W ≥ 0` is known by estimates. |
| A15 | Calibration data: Künneth primitive `h¹` on the finite divisor at small degree. |
| A16 | Same-order mixed-jet recovery for `≥ 3` primes; explicit main-term producer `ε ↦ (support, coefficients, C_ε)`. |
| A17 | Census: `S_cos(λ)` for `λ ≤ 1`; odd-stabilizer calibration; stabilizer at `β = 2`. |
| A18 | Voronoi summation and Zwegers' indefinite theta series (classical; the tools for the logarithmic completion of the split surface). |
| B26 | A count-valued primitive `h¹` past the prime-free window — the prime comb inside the count; equivalently a naive height on the integral correspondence ring at bounded distance from the Rosati form — **RH**; at one fixed degree past the first Hecke graph **sub** (Π11h, Γ19). |
| B27 | The genus law: near radical `(2 + o(1))e^{2a}` — **indep.**; implies all but `o(T)` zeros simple and isolated (Π16). |
| B28 | Logarithmic Serre duality for the split surface (Voronoi as the duality of the cone count) — **sub** (Π11f). |
| B29 | `ε`-uniform producer: zero-free-region error **sub**; square-root error **RH** (Π3). |
| B30 | Any unconditional square-root source input; half-power growth of the Redheffer determinant — **RH** (Π1, Π2). |
| B31 | Near-band cyclotomic energy `O(N^{3/2+ε})` — **≥qRH** (Π10). |
| B32 | Signed prime-pair surplus beyond bandwidth one — **sub** (Π7). |
| B33 | Where on the boost line `0 < \|u\| ≤ 1` the first Epstein real zero enters `(½, 1)` — **sub** (calibration of the fakes). |

### S6. Carriers, gluing, coupling and selection
Routes: SC, ACS, HF; Γ-candidates.

Established [L]: coupling calculus; bounded-coupling, rate, cone and finite-stratum theorems; two-
prime alias bound; curve coupling bounded ⇔ unitary; carrier classification; every `p`-adic
neighbourhood, every two-free-prime lattice and a three-prime core carry the full affine index;
separable assemblies blind; global pole = extremal weight; prime-set flips separated with exact
resolution thresholds; divisor-identity selection; correspondence algebra with λ-ring, theorem of
the square, Tate's limit law and convexity of counts; degree-three FE twins with arbitrarily many
right-hand real zeros.

| | Obstacle |
|---|---|
| A19 | `𝔽_q(X)` calibration: local walls at higher-degree places, global Hecke product formula, archimedean Weil state of a curve; ADT rescaled limits over `𝔽_q(T)` and the limiting structure of the fakes. |
| A20 | `𝔽₃` elliptic loop chain: unfolding, Eisenstein convergence, constant term (elliptic adeles, intertwining integrals, Weyl-series convergence and loop-group cells formalized). |
| B34 | Bounded coupling on one two-prime lattice; glued index `≤ 1` — **RH** (Σ17). |
| B35 | "Bounded cone coupling ⇒ RH" as a pure implication: the double-pole argument needs an attained maximal real part; residue cancellation below an unattained supremum is uncontrolled — **sub**; excluding unattained width outright — **≥qRH**. |
| B36 | Transfer of finite-sieve Hodge positivity to the global inter-tower form — **RH**. |
| B37 | Zero-independent selection at the trivial gauge point — **RH** (Γ1). |
| B38 | Frobenius at infinity as an operator (Rosati positivity / naive height; conformal correspondence; Hecke similitude) — **RH** (Γ4, Γ19). |
| B39 | Unimodular gauges with `S_N/H_N → 1`; functional-equation twins with Euler product or positivity; zero-density twins — **sub** (Γ12, Γ15). |

### S7. Realization and scattering
Routes: PM, RN, PTR, W1C.

Established [L]: regularized Gauss–Mayer operator (nuclear of order 0, entire Fredholm
determinant, holomorphy in `w`, `D = A + ζB`, `B(w,−1) = 0`, raw finite-part classification);
real-`w` derivative cone, `B ≠ 0`, `D(w,−1) ≠ 0`; signed product = exp of even-word traces =
primitive-orbit Euler product over digit-pair cycles with factors
`1 − z^{2ℓ(c)} exp(−(w/2+m)L_c)`, `L_c = 2 log λ_c` the attained hyperbolic translation length;
`D ≠ 0` on `|z| ≤ 1` for `Re w > 2`; primitive modular coding of hyperbolic `SL₂(ℤ)` classes;
word probabilities and trace decay; Selberg constant term holomorphic on `Re s > ½`; native
self-adjoint domain rejects critical zeros as well (domain obstruction); rational and algebraic
recenterings classified; resonant states with partner angle; lossless realization needs infinitely
many resonances; Vitali receiver.

| | Obstacle |
|---|---|
| A21 | Mayer–Selberg identification: primitive pair cycles ↔ oriented/unoriented primitive closed geodesics of `PSL₂(ℤ)\ℍ` with multiplicities, so that `D(w,1)D(w,−1) = Z_Selberg(w/2)`; continuation of the scattering constant term into `Re(2s) < 1`; the normalization comparison (known mathematics). |
| A22 | Sharp unit-disk boundary: on `\|z\| = 1` the even-word logarithm converges absolutely iff `Re w > 2`; the simple spectral zero at `w = 2`, `z = 1`. |
| A23 | Lax–Phillips scattering for `PSL₂(ℤ)\ℍ` (translation representations, scattering operator, contraction semigroup). |
| B40 | Faithful equivalence between right-strip ζ zeros and scattering-sector eigenvalue events of the actual operator `ζ(w)P + remainder` (eigenvalue `z⁻¹`), surviving the domain obstruction — **method**. |
| B41 | A Hermitian (Lewis–Zagier / Krein) structure including the scattering sector, giving a classical zero-free region near `Re s = 1`; separation of cusp events from scattering events; a scattering-sector spectral gap giving a fixed zero-free strip — **sub**. |
| B42 | Off-line resonance exclusion through partner saturation — **RH** (Σ8, Γ4). |
| B43 | Escape: two-prime Euler laws from divergent receiver energy; positive gauge mass below damping `½`; exterior tightness — **sub / ≥qRH**; cofinal complete-energy bounds — **RH**. |
| B44 | Source-faithful realization (PTR port, W1C Ising limit, RN directed sign) — **RH** (Σ8). |

### Route-specific items
| | Obstacle | Routes |
|---|---|---|
| A24 | Theta Hankel rank-8 strictness; ranks 9 and 10 | TH |
| A25 | Explicit thresholds: Hausdorff shifts, Jensen degree horizons, two-grid fixed degrees; Toeplitz minors beyond PF₃₇ | PA, LA, HCF |
| A26 | The nine atom-dominated collar moduli | ACT |
| A27 | Mixed Schur debit; first-prime / coarse / polar costs on fixed cells | AIP, CHMD |
| A28 | Logarithmic two-point Chowla for distinct nonproportional affine forms (Tao's theorem) | MC |
| B45 | Odd-sector bound `R ≤ ½` — **RH** (Σ7) | CHMD, TT |
| B46 | All-rank / all-degree signs; the Laguerre–Pólya property of `ξ(½ + z)`, endpoint of every centered-approximation scheme — **RH** (Σ6, Σ26) | TH, LA, HCF, PA, GTA; ART |
| B47 | Lower bounds for scheduled prime energies — **RH** (Σ20) | FU, CFC, RP, SZ, LI, FEL, EGC |
| B48 | Pre-divisor forcing — **RH** (Γ5) | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |

## 2. Programme ADT — Arithmetic Degeneration Theory

Thesis: RH is the Hodge–Riemann relation of the degenerating family `W_{φ,c,N}` along the
resolution axis, with the dilation semigroup as monodromy (one branch per prime, glued at `∞`).
Positivity is to be obtained as in Hodge theory of degenerations: identify the rescaled limit,
prove its polarization, identify the extension data, prove or refute inheritance.

Established:
- Rescaled limit for every regular tail `x^βT(x) → A`: `c^βE_m(c) → (2A/M)ζ(β+1)J_{β+1}(m)/φ(m)`,
  Möbius and coprime forms [L]; tilted spline `β = 7` with explicit spectrum and `A_φ` [L].
- Limiting mixed structure below `1/8`; inheritance radius exactly `1/8` (`1/(β+1)`) [L].
- Monodromy: `c_m(pn) = w_p(m)c_{ℓ_p m}(n)`; commuting lowerings; pole conductor the unique fixed
  point [L]. Weight strings `[8]_p`, `p⁷`; tensor law; uniform subthreshold law [L/S].
- Gluing: Redheffer `det = M(N)` = nerve Euler characteristic; coprime inertia signature `M(N)` [L/S].
- Traps recorded as theorems or readings: the limit polarizes nothing at the edge; positive rescaled
  limits are zero-blind; lowerings transport, not create, polarization; the pole `SL₂` is blind on
  `v₁^⊥`; trace identities with middle operator `1 − P − P̂` are not positivity.

| | Obstacle |
|---|---|
| A4 | (as in S1) twisted-weight limits, pure block, growing-block structure with extension data, first-order correction below `1/8`. |
| A29 | Calibration: rescaled limits over `𝔽_q(T)`; the limiting structure of the fakes (golden datum, flips, Liouville twin). |
| A30 | Cattani–Kaplan–Schmid (limiting mixed Hodge structures, nilpotent and SL₂ orbits) as a formal model for the transplant. |
| B2 | Second-order limit at the critical curve — **RH** over all `K`; **sub** at one `K`. |
| B10 | The top stratum as the home of the extension data: a sum–product inequality on conductor packets — **RH**. |
| B26 | A count or trace equal to `½W` on a growing family, starting with the prime-free window — **RH**. |
| B49 | The threshold block `m ≍ c`: the receiver of each conductor and the coupling of the degenerating block to the pure block (the `1/9 → 1/8` gap of the whole space) — **sub**. |

## 3. Live routes

### WL — Weil lag / prime lag
Established: critical-energy, linear prime-error and one-sided `√x log²x` criteria; genus slope ⇔
RH + simple; `Count(a)` iff `a − 1 ∈ 𝒬`; Chebyshev–Stirling split; Landau-window cost
`(2 log 2 − ε)mn`; Adams threshold `2^{qr}`; `{2,3}` stencil `ψ ≤ 23x/20`; multivariate parity
producers at the main term.
- A: A16.
- B: B30; B29; joint Möbius-moment / Mertens / sawtooth payment at square-root precision (**RH**).

### RW — restricted Weil ground minimum
Established: `μ(A) ≥ 0 ∀A` ⇔ RH; floors through `181/500`; restricted form = trace of the zero-form
operator, positive on `0 < a ≤ 181/500`, exact `{∞,2}` trace identity through `½ log 3`, where
positivity ⇔ single-prime family energy `≥ 0` [L/S]; semilocal positive carriers excluded,
obstruction located in the odd polar mode [L/S]; ceiling; near radical and genus function; finite
divisor; visibility; isolated-pair edge; companions.
Research status: the `{∞,2}` semilocal question is settled (exact trace identity, no positive
carrier); the next sign test is the aperture `½ log 3`, where the prime `3` enters.
- A: A3, A5.
- B: B1; B7; depth-weighted all-window mass bound (**≥qRH**). B27 is **indep.** and not on RW's path.

### FU, CFC, RP, LI, SZ — scheduled prime sums
Established: exact receivers (completed Abel moment; first-clock tail coefficient; normalized
history floor `−B(K+2)`; guarded zero set `Z_S` finite with RH ⇔ `Z_S = ∅`; rectangular Ward
defect bounded below); cofinal unboundedness under ¬RH; transport identities; LI: Cayley ladder
reflection-positivity receiver [S]; SZ: complete first-variation transfer [S], fixed-scale,
sublinear and bounded-Gamma producers excluded.
- A: none.
- B: B47 for each (seed/drift/prior/cross-block/endpoint payment; source lower bound with prime,
  archimedean and endpoint terms; high-LCM pairs and moving core at linear scale; outside budget at
  every guarded zero; complete source assembly).

### PA — prime–archimedean source passivity
Established: each fixed Hausdorff order positive at large shifts.
- A: A25. B: B46.

### MC — Möbius cancellation
Established: half-power dictionaries; `Θ ≥ ½`, Haar-a.e. `½`; RH ⇔ trivial point typical; every
positive-power band retains `2Θ`; Redheffer `det R_N = M(N)` = nerve Euler characteristic,
RH ⇔ `det R_N = O_ε(N^{½+ε})` [S]; coprimality form signature `M(N)`; squarefree complex
(combinatorial wedge decomposition) [L]; individual finite-clock leaf squares paid.
- A: A9 (Björner topology); A28 (logarithmic Chowla).
- B: B30 (half-power cancellation / determinant bound, **RH**); B31 (**≥qRH**); head/leaf signed
  cancellation (Σ20); B37 (**RH**). The wedge has `≈ (2/π²)N` spheres of mixed dimension, so a
  discrete-Morse bound on `det R_N` needs cancellation between dimensions [D].

### TT — theta seam / Wold
Established: seam, tail and Wold receivers; `t < ½` threshold; Φ-Doob identities.
- A: none. B: B45.

### LA — Laguerre/Jensen and local heat
Established: every fixed Jensen degree eventually real-rooted; RH ⇔ every Xi Jensen polynomial
splits; slice floor `133/200`; right-half depth moment `o(V)`; PF₃₇ at the centre.
- A: A25, A11. B: B46; uniform tail narrowing (**≥qRH**); exceptional heights (**sub**).

### TG — transgression / central gap
Established: winding/index and cubic-transgression identities; finite-matrix index laws along paths;
Kähler transport free.
- A: none. B: B17 (integer trace `< 1` on every disc); B9 (source-driven noncrossing path).

### HF — Hodge / Hecke / complete cells
Established: S1 and S2 in full, with the ADT degeneration (Jordan limit, inheritance radius,
monodromy, weight strings, tensor law); complete-cell index `≤ R + A`; heat Hodge defect; loop-
Eisenstein band poles = Hodge defect; cyclic Hodge defect; packet identities, shell-degree rows,
coprime successor gap; Frobenius at infinity ⇔ RH; correspondence algebra with Tate's limit law;
the RR branch of S5.
Research status: the `1/9` exponent through edge and Hodge theory, the isolated-pair edge, the sharp
budget, the rational-Gram realization and the shell-degree bound are formalized; the `1/8` programme
(T1–T4) and the prime-successor comparison are open.
- A: A1–A9, A14, A15, A27, A30.
- B: B1–B12, B26, B28, B38, B49.

### CHMD — causal hyperbolic–modular duality
Established: RH ⇔ `R ≤ ½` on the odd sector; Markov form and sinh capacity; Haar pieces with uniform
finite index except the first-prime coarse layer; growing-packet head-pole cancellation.
- A: A27. B: B13 (**≥qRH**); B45 (**RH**); B4.

### TH — theta Hankel ranks
Established: rank 7 strict; rank 8 PSD; heated orthant signs; all-rank signed-center positivity ⇔ RH.
- A: A24. B: B46; rank-uniform signed flux payment.

### RN — renewal
Established: compact cone-positive renewal operator with exact determinant and resonances.
- A: none. B: directed mixed prime + Gamma `≥` pole; B44.

### WD — Ward / collision / heat
Established: S4 in full — Wiener–Hopf index with the six-way index-zero equivalence; arithmetic
reality; strip zeros `Θ(N² log N)` and the `c√T` prefix bound [L]; separation-free polynomial-prefix
stabilization at `Θ(√m)` and the corridor/RH equivalences of `Θ(√m)`-prefix Szegő positivity [P];
Hecke-defect hierarchy with the half-gate closed and the density equivalence to `2/3`; one-sided
Green readings; unit-window calculus.
Research status: the prefix-scale question is settled on paper; the route reduces to a sectoriality
condition on polynomial-size integer-theta data per window.
- A: A10–A13; A5.
- B: B15–B25; B13 (tower branch).

### JAS, CTF, PBM, RB — one-sided count
Established: JAS positivity at growing logarithmic budget; CTF completion identities and Euler
completion error `≤ 1/(n+1)`; PBM convergence at every `σ > ½` ⇔ RH; RB colossally abundant
reduction.
- A: none. B: B30 (square-root budget; covariance cancellation along cutoffs; coefficient
  cancellation; primorial remainder).

### HCF, XN, BAG, EWU, GTA, OWU
- HCF: two-grid criterion; one grid aliases. A: A25. B: B46.
- XN: Newton-disc criterion; nonnegative Laplacian of the margin. B: covering with nonnegative
  margin (**RH**, Γ).
- BAG: disc recurrence ⇔ RH. B: B37.
- EWU: weight rigidity; RH ⇔ nonnegative weighted minima at every aperture. A: A3. B: B1.
- GTA: transverse-charge criterion. B: B46.
- OWU: odd tests beyond `27/50` separate ζ from Liouville; odd sector carries no defect at
  `a ≤ 181/500`. A: A3. B: B1 (odd sign at every aperture).

### SRT, ACT, AIP — complete atomic matrix
- SRT: S1 in full; depth-gap visibility; local count ⇒ bounded critical multiplicity; Steklov full
  index for `β > 2`. A: A1–A6. B: B1–B8; B13.
- ACT: collar threshold pays every modulus outside nine moduli. A: A26. B: B1.
- AIP: complete form = jump + incidence − shell + boundary, explicit shell rows; allocation
  receiver. A: A1, A2, A6, A27. B: B1–B5.

### ACS — arithmetic Castelnuovo–Severi
Established: RH ⇔ effectivity ⇔ Hodge index ⇔ section count ⇔ Castelnuovo–Severi at rational
scales; universal floor law; finite divisor; reflection-sector additivity; near radical and genus
function (distinct resolved zeros; genus law ⇒ almost all simple); isolated-pair edge and
visibility above Nyquist; LST counts (jump count to `1/64`, Stepanov over `𝔽_q`, self-dual point);
correspondence algebra with naive-height criterion; degree-three FE twins.
Research status: the genus law is a simplicity statement; the isolated-pair edge is exact; the count
reading stops at radius `1/64`.
- A: A14, A15, A17–A20.
- B: B26, B28 (**sub**), B27 (**indep.**), B38, B32, B33, B1–B6, B12.

### SC — Stokes/Witt–Krein / archimedean successor
Path: `φ_c(a, b) = ratCorr(|a|) − c|a|^{−½}|b|` → `κ(φ_c) < 3` → `κ = 0` → RH.

Established: `κ(φ_c) = κ + 1` at every place; readings add; stable gluing; carrier classification;
every `p`-adic neighbourhood and every two-prime lattice carry the full affine index; coupling ≡
kernel; cone; finite stratum ⇒ RH; complete-matrix compressions realize every finite rational
Gram, and RH ⇔ eventual pole-hyperplane positivity at every fixed critical multiple (inertia +
evenness, no moment preservation needed) [L]; heat index one for `t ≥ 1/8` [L].

Research status (seven main and four heat obligations): (1) realization — done [L]; (2) cone with
unattained width — open (B35); (3) finite nonzero index — open (B14); (4) finite-sieve to global
transfer — open (B36); (5) index ceiling — open (B13); (6) square decomposition of the dilation
form — open (B6); (7) glued index `≤ 1` — open (B34, B1). Heat: upper-time calibration at `1/8`
done; subcritical count (B15), uniform count and no-jump on `(0, 1/8]` (B17) open; the
`2/3`-horizon count improves the coefficient of `1/t`, not its power.
- A: A19.
- B: B1, B6, B13–B15, B17, B34–B36, B9.

### PM — physical / complete-energy realization
Established: Mayer determinant with signed even-word trace formula and primitive-orbit Euler
product in hyperbolic-length form; real-`w` positivity; non-vanishing on the closed unit disc for
`Re w > 2`; primitive modular coding; resonant states with partner angle; escape receivers.

Research status (Mayer 1–6, Escape a–d): Mayer 1 — Euler product certified, translation lengths
identified; geodesic multiplicities and scattering normalization open (A21). Mayer 2 (faithful
zero ↔ event equivalence) open (B40). Mayer 3–5 (Hermitian structure, cusp/scattering separation,
spectral gap) open (B41). Mayer 6 (partner saturation) open (B42). Escape a–d open (B43).
- A: A21–A23.
- B: B40–B43.

## 4. Candidates and retired branch

| Candidate | Established | A (just work) | B (open) |
|---|---|---|---|
| APF | Fredholm index, cycle-trace reconstruction | — | zero-independent divisor exhaustion (B48) |
| BSH | framed curvature | — | pre-divisor section and mate identity coupled to Ξ zeros (B48) |
| CDC | calibrated confluence iff `Re s = ½` | — | source-defined potential forcing confluence (B48) |
| DR | cusp roots, finite monodromy | — | compatible roots on the strict-right domain; global monodromy (Γ) |
| EGC | pole-safe contour | — | outer expanding-contour sign (B47) |
| EWJ | Euler/Wold jets | — | zero-independent source admission (B48) |
| FEL | theta likelihood; BSY integral = off-line zero sum | — | predeclared source balance (B47) |
| HJ | Hurwitz residual = SEC charge, vanishing iff criticality | — | pre-divisor forcing (B48) |
| IRK | rotation-algebra trace / winding | — | arithmetic Poisson / projective lift with integral count (B26-type) |
| MSC | Möbius–Sonin | — | bridge to nonnegative Sonin energy (B1) |
| PCS | singular co-shift | — | source-natural wall annihilation (B48) |
| PTR | lossless stacks, unit port gap | — | prime-faithful port (B44) |
| RFHM | support grade | — | symmetry-breaking law (B48) |
| SEC | essential norm = seam jump | — | pre-divisor compactness at zeros (B48) |
| W1C | finite Lee–Yang + Ising receiver | — | couplings converging to Riemann's measure (B44) |
| WBF | genealogy Gram | — | any arithmetic coupling (B48) |
| PW-B (retired) | optical flux vanishing iff critical | — | killed as a selector (fails at `3/4 + i`); survivor: the half-parameter cusp receiver, which needs B42 (**RH**) |

Support lines (not routes): ART (centered approximation; its literal Euler branch is retired, its
survivor lands in B46); ARGON-3 approaches B (Böttcher / period rigidity: theta–Gamma differential
independence of all positive algebraic dilates) and C (two-place Krein: local conditions keep the
full index); HTGeometry `AffineExpanders`; the paused classical-formalization programme
(Lax–Phillips, Voronoi, Zwegers, CKS, Björner, logarithmic Chowla).

## 5. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ, second-order term of the degeneration (positivity at every `K·c*`) | RW, EWU, OWU, ACT, HF, SRT, AIP, ACS-atomic, SC, CHMD, TT; MSC, FEL; ADT |
| Σ, Hodge–Lefschetz / top coprime stratum | HF, ACS-Hodge, TG; ADT |
| Σ, window integer (sectorial multiplier at polynomial resolution) | WD, LA (heat), TG, SC-heat |
| Σ, rank / degree (Laguerre–Pólya) | TH, HCF, PA, GTA, LA; ART |
| Σ, scheduled prime sums | FU, CFC, RP, SZ, LI; EGC |
| Σ, realization / resonance exclusion | RN, PTR, W1C, PM |
| Π, count-valued primitive `h¹` / naive height | ACS-effectivity, HF-RR; IRK; ADT |
| Π, one-point precision (incl. the Redheffer determinant) | WL, MC, PBM, RB, JAS, CTF, SC (coupling) |
| Π, conjugate diagonal / near-line density | WD (Hecke defect), census |
| Γ, selection / Frobenius at infinity | BAG, XN, PM (partner saturation), MC (typicality), ACS (Rosati), HF (Hecke similitude); APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |

Inside Σ the complete-family routes share one coordinate, the multiple `K`. Below the critical
exponent the family degenerates to a zero-blind Euler-factor polarization and inherits it; the
estimates live there. At the critical exponent the extension data — the cross-conductor channels of
the top coprime stratum — carry the zeros, and only an exact second-order term decides. SC's glued
index is a face of the same family (pole-hyperplane positivity at every fixed multiple). WD has
become a sectoriality problem on polynomial-size integer data per window. PM has a Selberg-type
product and needs the scattering identification and a resonance-excluding structure. The
producers able to cross the edge are an identity (SOS on a two-prime lattice; the second-order
term), a count (primitive `h¹`, naive height) and an integer with a structural bound (window
index).
