# Route obstacles — status quo

Scope: the 33 live routes, the 16 candidates, the programmes ADT and AHD, and the support lines,
read against the Lean corpus at `2605d92e2b` with the working tree. For every route: what is
established, the research status of its open obligations, the obstacles that are **(A) just work**,
and the obstacles that are **(B) open mathematics**. Just work means known mathematics, finite or
kernel-certified computation, effectivization, finishing a formalization, or composition of proved
statements. Open mathematics means a statement nobody knows how to prove.

Evidence: `[L]` Lean; `[S]` Lean in the working tree or not integrated; `[P]` complete paper proof,
Lean pending; `[D]` derived here from Lean statements, not formalized.

Strength of a B-item: **RH** equivalent to RH; **≥qRH** implies Lindelöf and a zero-free
half-plane; **LH** implies Lindelöf; **sub** strictly weaker or of unknown strength; **indep.** not
implied by RH and not known to imply it; **method** a missing tool, not a statement.

Wall labels Σ/Π/Γ refer to `walls-ledger.md`. Programme codes follow the frontier-map source
locator; further codes: ACPL = ArithmeticCouplingTheory, ADT = ArithmeticDegenerationTheory,
AHD = ArithmeticHodgeTheoryOfDegenerations, AET = ArithmeticEffectivityTheory, AOG =
ArithmeticOrientationGeometry, ART = ArithmeticResonanceTheory, CSAR =
CriticalScaleArithmeticRigidity, EHT = EdgeHodgeTheory, HWV = HodgeTheoryWithoutVarieties, LST =
LatticeSectionTheory, RIT = RenormalizedIntersectionTheory, SP = SelectivePositivityAndThresholdLaws.

## 0. Calibration (applies to every route)

| Fact | Anchor | Consequence |
|---|---|---|
| `κ = #` distinct right-half zeros, even; RH ⇔ `κ < 2`; finite `κ` ⇒ all high zeros critical ⇒ `Θ < 1` | AOG `TheIndexExit` [L] | every index route ends in one even integer; finite-index waypoints are ≥qRH |
| Edge logic: a statement proved without zero information holds on every datum sharing that information and stops below the edge of off-line members | EHT; ADT [L/D] | only an identity, an inherited polarization or an integer with a structural bound crosses the edge |
| Weil's window criterion: RH ⇔ `Q(e^{y/2}h) ≥ 0` for every C² `h` on every `[−A, 0]` ⇔ horizon blocks of the tilted spline eventually `≥ −ε` past the critical curve ⇔ pole-hyperplane positivity on the single Beurling schedule `2L(log L)²` ⇔ positivity at every fixed `K·c*` | AHD `TheHorizonCriterion`; RIT `TheHodgeIndexAtCriticalOverlap`; TM `ReceiverRate` [L] | every complete-family receiver is Weil's criterion on window tests |
| Degeneration: bulk → Jordan form `J(m) = J(1)#ℙ⁷(ℤ/m)` (a point count, positive, zero-blind; a zero enters the bulk only through a pole weight of positive real part); horizon layer → `κQ(H)` past the critical curve, `κQ(H) + (7J(1)/K)∫e^{−8y}H²` at it | ADT; AHD [L] | the degeneration is a complete dictionary; it supplies no sign beyond Weil's window form |
| Window Markov form: on a window of length `A` only prime powers `n ≤ e^A` jump; departing jumps pay exactly their creation `2Λ(n)/√n‖g‖²` | AHD `ThePrimesOfAHorizonWindow` [L] | the window sign involves finitely many primes and the archimedean Lévy jumps |
| Bounded Weil kernel ⇔ RH; coupling ≡ kernel; one dense lattice `⟨p⟩×⟨q⟩` decides; the Hecke orbit of one generic test carries the whole Hodge defect | RIT; ACPL; ACS [L] | every boundedness target is RH |
| Glued state `κ(φ_c) = κ + 1` at every place | AKG [L] | RH ⇔ `κ(φ_c) < 3` |
| One gluing at the pole: divisibility form unipotent; pole gluing = Redheffer, `det = M(N)` = nerve Euler characteristic = coprimality signature | ADT; HWV [L] | the arithmetic of `μ` and the one negative square come from one rank-one gluing |
| Graded energies = positive cone sums of top-stratum energies; top = Möbius-signed sums of graded energies | ADT [L] | graded positivity never passes to the top stratum |
| No softening (Künneth, Hadamard, tensor powers all-or-nothing); Kähler transport free; RH ⇔ HL on the PSD locus | RIT; EHT; HWV [L] | amplification and deformation prove nothing |
| Tilted spline: all vectors `α < 1/9`; below `1/8` packets, the growing subthreshold block, the polynomial-conductor complement and the far reserve; mid-band `α < 1/4` | CACT; ADT [L] | the whole-space gap `1/9 → 1/8` is the join of coercive pieces |
| Logarithmic profile positive to `ε₀·c*`, budget optimal; general compact profiles positive on polynomial spans to `(log log N)^{1/4}` and on almost-polynomial spans past `log log N` | TM; CACT [L/S] | estimates reach the receiver scale only up to a constant (or `log L`) factor |
| Ceiling `μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})`; near radical `(2 − η)e^{2a}` blind below `2πe^{2a}`; finite divisor at every degree; isolated-pair visibility law; companions forced | ArithmeticCompensationTheory; RHTower; ACS [L] | each degree is finite-dimensional; estimates cannot reach the near radical |
| Semilocal and trace carriers: exact `{∞,2}` trace through `½ log 3`; no `{∞,p}` positive carrier; `1 − P − P̂` NSD on time- and band-limited vectors; no positive trace carrier for a form with a negative value; finite prime sets cross zero by `2 log(\|S\|+2) + 11` | SP; ADT [L] | positivity is glued and global |
| Counts: Künneth RR; Lévy jump count pays primitive `h¹` on prime-free cycles of radius `≤ 1/64`; Stepanov pays it over `𝔽_q`; cones, bidegree, fixed-rank, definite and Siegel counts excluded | LST [L] | a count pays the sign at small radius and over `𝔽_q` |
| Correspondence algebra: λ-ring, Rosati, Lefschetz trace, theorem of the square; Rosati positivity ⇔ naive height at bounded distance from the integral Rosati form | AOG; AET; ACP [L] | the missing input is a height nonnegative for an arithmetic reason |
| Window index = Wiener–Hopf index; index `0` ⇔ outer Szegő factorization; the exact multiplier is determined by the window energy `\|𝒵(t)\|²`, whose abscissa is twice the maximal depth; log stage ⇔ corridor, polynomial stage ⇔ RH | CDG `SzegoCollision` [L] | the window integer is decided by a zero power sum |
| Hecke-defect means ↔ near-line density rates; rate `r < 1` holds; clustering ⇔ `o(log U)` | CDG [L] | the conjugate diagonal is a near-line density ladder |
| `Λ(s)/Λ(s+1)`: band poles = Hodge defect; = Mayer boundary `2ζ(s)/ζ(s+1)`; classical zero-free region from its positive slope | RIT [L]; scattering reading [D] | PM, band poles and resonant partners read one function |
| Natural cone: bounded coupling ⇒ RH or polynomial repulsion from maximal width; unattained-width models with exact spline weights and bounded local density exist | ACPL [L] | the cone needs ζ's density or explicit formula |
| Selection: every prime-set flip separated at every density; complete degeneration and harmonic saturation select ζ; no selector gives the sign | RIT; ADT; BGG; ACP [L] | Γ reduces to Frobenius at infinity |
| Heat floors `133/200` (slice), `2/3 + ε` (flow); census `0.6725` | RHTower; IGP; TTPC [L] | size floors |

## 1. Shared obstacle blocks

### S1. Complete Weil family across the critical overlap
Routes: HF, SRT, AIP, ACT, ACS-atomic, RW, EWU, OWU, MSC, FEL; SC through the ratCorr Grams; CHMD through
the index; TT through the odd/Markov sector.

Established:
- Receivers [L]: Weil's window criterion; horizon criterion; single Beurling schedule; every fixed `K·c*`;
  conductor Gram at every `2K(log N)^{1/8}`.
- Degeneration [L]: Jordan limit `J(1)#ℙ⁷(ℤ/m)`, tensor law, weight strings (Hensel towers), scaling form
  `E_m(c) = J(m)c⁻⁷R_m(c/m)` (branches through `rad m`, weights through `J`), eventually idempotent
  monodromy, subthreshold block Jordan below `1/8`, zero ledger of the bulk positive and zero-blind.
- Second order [L]: horizon formula; two-sided horizon theorem; sharp second-order term (aliasing density =
  dilation derivative of the bulk); exact critical-curve limit `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²` for every
  regular profile, `κQ(H) + (7J(1)/K)∫e^{−8y}H²` for the tilted spline; coercivity; critical-multiple
  calculus with the exact window threshold `K*`.
- Rough regime [L]: all vectors `α < 1/9` with logarithmic confinement; below `1/8` the polynomial-conductor
  complement (floor `c_orth log N/c⁷`, nonpositive subspaces of dimension `≤ ⌊N^θ⌋`) and the far reserve;
  mid-band `α < 1/4`; near collar `130/log N·Σb_m²m/φ(m)`; terminal-support quadratic high-conductor loss
  [S].
- General profiles [L/S]: conductor floors for every compact profile (Fourier zeros allowed); polynomial
  spans at `(log log N)^β`, `β < 1/4`; polylog spans at `K log log N`; almost-polynomial spans past
  `log log N` [S].
- Logarithmic profile positive to `ε₀·c*` [L]; Weil floors through radius `181/500` and the `{∞,2}` trace
  through `½ log 3` [L].

Research status: the critical-curve question of the complete family is answered on horizon blocks — it is
Weil's window sign plus a positive prime-free term. The `1/9 → 1/8` whole-space gap has three coercive
pieces in Lean (subthreshold block, mid-band, far complement); the band–far cross and the threshold block
`e ≍ c` remain.

| | Obstacle |
|---|---|
| A1 | Join at `1/8`: pay the band–far cross (Schur bound `O(c√log c)` on `S → S`) and the threshold block `e ≍ c` jointly with the three proved coercive pieces. Risk: if the band–far cross needs the shifted prime-pair correlation `‖E‖² ≤ c(log N)^{1+δ}`, `δ = 1 − 8α`, it becomes B41. |
| A2 | Explicit horizons: `N₀` for the `1/9` theorem, the logarithmic profile, the single Beurling schedule and the horizon criterion; constants of the complete conductor residuals. |
| A3 | Kernel-certified Weil positivity at `½ log 3` and the next prime apertures: finite Schur complements on the finite divisor (near-radical dimension `≈ 2e^{2a}`). |
| A4 | Strength of one fixed critical multiple: compute which zero configurations positivity at `K` excludes (isolated pairs through the visibility law; clusters through short windows) and the effective window length; equality-case asymptotics at `K = K*`. |
| A5 | AHD calibrations: second-order term over `𝔽_q(T)`; horizon blocks of the fakes (golden datum, Liouville twin, prime flips); pure block `m ≫ c` asymptotics. |
| A6 | Close the `[S]` items: terminal-support quadratic high-conductor loss; explicit-clock almost-polynomial coercivity; finite clock products (SC); Gauss–Mayer theta ray (PM); Cayley-ladder receiver (LI); first-variation transfer (SZ); Poisson rigidity (Γ8). |
| A7 | Prime-successor comparison `½A_N(F) ≥ (1/64)[Σ_{Q<p≤N/16Q²} log p/p]·(nonconstant mass)` and its combination with the packet identity. |
| B1 | Weil's sign on window tests of every length (≡ positivity at every fixed `K·c*` ≡ horizon criterion ≡ single Beurling schedule) — **RH**; each fixed window length **sub** (Σ1). |
| B2 | Full-space second-order identification at the critical curve: the rescaled limit on all vectors (bulk ⊕ horizon ⊕ mixed) and horizon localization of negative directions — **sub** (Σ1j). |
| B3 | Positivity at one fixed critical multiple, which contains the exclusion of dense off-line clusters of depth `≳ 1/log K` at every height — **sub** (Σ1k). |
| B4 | Joint shell–pole and non-arithmetic Gamma-graph payment on growing packets (confinement exponent `≤ 8`) — **sub** (Σ1c, Σ1g). |
| B5 | Conductors `N^{½} < m ≤ N` (Elliott–Halberstam type); full-space positivity of general profiles past `log log N` — **sub** (Σ1d, Σ1e). |
| B6 | Exact sum-of-squares identity for Weil's dilation form on one two-prime lattice — **RH** (Σ18). |
| B7 | Cluster exclusion below the Landau height — **sub** (Π8). |
| B41 | Shifted prime-pair correlation bound for the prefix–terminal remainder `E` (only if A1 needs it) — **sub**. |

### S2. Kähler package, stars and gluing
Routes: HF, ACS-Hodge, AIP, TG, SC, RW; MC through the gluing determinant.

Established [L]: Kähler package; stars as lower horizons with depth law `log d − C₀`; Metzler gauge on deep
stars; gcd stratification with all successor and archimedean coupling in `g = 1`; graded/top Möbius pair
(positive forward, alternating backward); closed-form monodromy; links disconnected; nerve `χ̃ = −M(N)`;
conductor ↔ star duality; no semilocal positive carrier; cyclic Hodge defect on a two-prime Hecke orbit.

| | Obstacle |
|---|---|
| A8 | Quantitative depth law `d₀(c)`; explicit star horizons; finite-`N` tabulation of the gcd strata. |
| A9 | Björner's theorem for the squarefree complex (topological step and integral homology). |
| B8 | HL on the positive locus of the overlap flow — **RH** (Σ2). |
| B9 | Payment of the top coprime stratum (sum–product inequality on conductor packets) — **RH** (Σ3a). |
| B10 | Cross-tower spectral gap through the archimedean channel — **method**; uniform version **RH** (Σ23, Σ25). |
| B11 | Band-pole noncancellation of `Λ(s)/Λ(s+1)` — **RH** (Σ19; = B34 in scattering form). |

### S3. Index and finite off-line support
Routes: HKT, AKLT, AID, SRT towers, CHMD index, SC, RIT-Künneth.

Established [L]: finite-index kernels = PD minus `κ` unitary characters; `κ ≤ r` ⇔ translation-stable
positive constraints of dimension `≤ r`; finite defect at every degree; finite stratum ⇒ RH for bounded
cone coupling.

| | Obstacle |
|---|---|
| B12 | Arithmetic index ceiling uniform in resolution — **≥qRH** for `K_ζ`; **RH** for `K_ζ ⊠ K_ζ` (Σ4). |
| B13 | Exclude a finite nonzero index (zero–one law) — **sub**. |

### S4. Window energy, heat and the Hecke defect
Routes: WD, LA, TG, HCF, SC-heat, TH-heat; census; HEF.

Established:
- Window integer [L]: index = Wiener–Hopf index; six-way index-zero equivalence; separation-free
  stabilization at `Θ(√m)` (unit) and `O(m log²(m+S))` (cumulative); 9-way RH door-opener equivalence;
  `Θ(√m)` Hurwitz–Rouché zero capture; strip zeros `Θ(N² log N)`; artifact-free prefix `≥ c√T`.
- Window energy [L]: pair resolvent = Laplace transform of `\|𝒵(t)\|²`; abscissa = twice the maximal depth;
  energy–index law; exact multiplier and finite Bessel–Szegő certificate under a corridor margin; cepstrum
  as a positive Bessel transform of the energy, `(−1)^kS_k ≥ 0`; every certificate = exact multiplier ×
  Carathéodory factor; centered theta windows with `𝒵_N` a source contour integral; log-stage certificate
  ⇔ inverse-log corridor; `E_γ(c₀ log T) = O(1)` ⇒ corridor, zeros approach the line, Lindelöf and a
  half-plane bound.
- Hecke defect [L]: half-gate `c < 1/2` (means and unit-window sup); density TFAE to `2/3`; rate `r < 1`;
  almost-all corridor `(1+ε)loglog T/log T`; mollified Green ceiling; superharmonic no-go.
- Heat [L]: `κ(φ_c^{(t)}) − 1 = N(t)/2`; heat index one for `t ≥ 1/8`; slice floor `133/200`, flow
  floor `2/3 + ε`.

Research status: the window integer is decided by the growth of a zero power sum; the multiplier
question is closed (the canonical multiplier exists whenever any does). The open input is a bound on the
window energy, i.e. local zero location per window.

| | Obstacle |
|---|---|
| A10 | Polynomial-stage certificate: the equivalence RH ⇔ subexponential source energy on every unit window at stage `60m`; computable stopping prefix with kernel-certified intervals; flow threshold `Λ_X` from sub-Weyl profiles; `ΔO = o(log T)` ⇒ density one ⇒ Lindelöf as one statement. |
| B14 | Heat: subcritical count `N(t) ≤ exp(At^{−a})`, `a < 1` — **sub**; pointwise horizon `< ½` — **≥qRH**; `O(T) = o(N(T))` — **sub**; `ΔO = o(log T)` — **LH**. |
| B15 | Subexponential window energy on every unit window: log stage **≥qRH**, polynomial stage **RH** (Π17). |
| B16 | Log-free near-line density `#{ρ ∈ [V, 2V] : depth ≥ A/log V} ≤ ε(A)V`, `ε(A) → 0` — the log-stage certificate on almost all windows — **sub**. |
| B17 | Near-line density at rate `r ≥ 1`; 100% critical-scale clustering (dyadic means `o(log U)`) — **sub** (Π5). |
| B18 | Hecke defect: pointwise `E_γ(c log T) = O(1)` — **≥qRH**; doubly-log scale — **sub**; one constant over dyadic scales — **RH**. |
| B19 | An arithmetic input beyond counts and the linear explicit formula for the conjugate diagonal — **method**. |

### S5. Counts, producers and Riemann–Roch
Routes: WL, MC, PBM, RB, JAS, CTF, ACS-effectivity, HF-RR, RW; census.

Established [L]: one-sided count ⇔ RH; multivariate parity producers reach `(1 + ε)x + C_ε log²x`;
every individual producer has slope `> 1`; integer-Chebyshev ceiling; Redheffer `det = M(N)`, `Ω±(√N)`;
theta `h⁰` with RR on `Spec ℤ`; universal floor law; Künneth RR; count classification (bidegree, fixed
rank, definite, Siegel excluded; `m² + 64n²` and `ℤ ⊕ yℤ` fakes); isotropic count `ζ²`; boost transform;
Hecke similitudes of primitive `h¹`; Lévy jump count to radius `1/64`; Stepanov over `𝔽_q`; Künneth
effectivity to `181/500`; genus function; census `0.6725`.

| | Obstacle |
|---|---|
| A11 | Count reading of the whole prime-free window: a Poincaré inequality for the Lévy form on an interval and the pole signs (`+2A²` even, `−2A²` odd); the target `W ≥ 0` is known by estimates. |
| A12 | Künneth primitive `h¹` on the finite divisor at small degree (calibration data). |
| A13 | Same-order mixed-jet recovery for `≥ 3` primes; explicit main-term producer. |
| A14 | Census: `S_cos(λ)` for `λ ≤ 1`; odd-stabilizer calibration; stabilizer at `β = 2`. |
| A15 | Voronoi summation and Zwegers' indefinite theta series. |
| B20 | Count-valued primitive `h¹` past the prime-free window (the first prime jump `n = 2` for windows longer than `log 2`; then the prime comb) — equivalently a naive height on the integral correspondence ring — **RH**; at one fixed degree **sub** (Π11h, Γ19). |
| B21 | Genus law `g ≤ (2 + η)e^{2a}` — **indep.** (Π16). |
| B22 | Logarithmic Serre duality for the split surface — **sub** (Π11f). |
| B23 | `ε`-uniform producer: zero-free-region error **sub**; square-root error **RH** (Π3). |
| B24 | Any unconditional square-root source input; half-power growth of the Redheffer determinant — **RH** (Π1, Π2). |
| B25 | Near-band cyclotomic energy `O(N^{3/2+ε})` — **≥qRH** (Π10). |
| B26 | Signed prime-pair surplus beyond bandwidth one — **sub** (Π7). |
| B27 | First Epstein real zero on the boost line `0 < \|u\| ≤ 1` — **sub** (calibration). |

### S6. Carriers, coupling, natural cone and selection
Routes: SC, ACS, HF; Γ-candidates.

Established [L]: coupling calculus; bounded dense coupling ⇔ RH; rate = width; finite stratum ⇒ RH;
natural cone ⇒ RH or polynomial repulsion; unattained-width cone models (positive atoms; exact spline
weights with `≤ 12` atoms per unit height); carrier classification; every `p`-adic neighbourhood and every
two-free-prime lattice carry the full affine index; prime-set flips separated at every density; complete
degeneration and harmonic saturation select ζ; correspondence algebra with Tate's limit law; degree-three
and degree-two FE fakes; finite clock products with point-selecting factors [S].

| | Obstacle |
|---|---|
| A16 | `𝔽_q(X)` calibration (local walls at higher-degree places, global Hecke product formula, archimedean Weil state of a curve); `𝔽₃` elliptic loop chain. |
| A19 | Natural-cone models with Riemann–von Mangoldt local density (`≍ log T` atoms per unit height), or the obstruction that forbids them. |
| B28 | Bounded coupling on one dense two-prime lattice; glued index `≤ 1` — **RH** (Σ17). |
| B29 | Exclusion of unattained width for ζ under bounded natural-cone coupling (with density or explicit formula) — **sub**; excluding unattained width outright — **≥qRH**. |
| B30 | Transfer of finite-sieve Hodge positivity to the global inter-tower form — **RH**. |
| B31 | Zero-independent selection at the trivial gauge point — **RH** (Γ1). |
| B32 | Frobenius at infinity as an operator (Rosati positivity / naive height; Hecke similitude; partner saturation) — **RH** (Γ4, Γ19). |
| B33 | Euler-product FE twins; unimodular gauges with `S_N/H_N → 1` — **sub** (Γ12, Γ15). |

### S7. Realization and scattering
Routes: PM, RN, PTR, W1C.

Established [L]: regularized Gauss–Mayer operator (nuclear of order 0, entire Fredholm determinant,
`D = A + ζB`); determinant = Euler product over genuine periodic modular geodesics with least periods,
reversal fibres and unoriented product; scattering divisor of the constant-input inverse = ζ's divisor
with multiplicity; signed channels (negative entire, positive carrying ζ's strip multiplicities);
normalization = level-one Poincaré scattering coefficient; Epstein field split into two ζ axes and four
positive cones, Cauchy transform continued through the source half-plane, Eisenstein lift, Barnes
chamber, Lewis three-term relation continued; scattering core of finite positive energy at every nonreal
strip zero; boundary `2ζ(s)/ζ(s+1)` with slope weights `(1 − 1/n)Λ(n) ≥ 0`, 3-4-1 positivity and the
classical zero-free region `Re ρ ≤ 1 − 1/(1000 log γ)`; Cauchy multiplier envelope `2^{(1−Re w)/2}`,
contraction iff `Re w ≥ 1`, amplification at arbitrarily small `Re w > 0`; feedback zeros of `1 + 2ζ(w−1)`
after removing the constant mode; rational/algebraic recentering classified; resonant partner angle;
lossless realization needs infinitely many resonances; Vitali receiver; theta ray Mellin = completed ζ
[S].

| | Obstacle |
|---|---|
| A17 | Classical identifications: `D(w,1)D(w,−1)` against `Z_Selberg(w/2)` with normalization; continuation of the scattering constant term into `Re(2s) < 1`; Lax–Phillips scattering for `PSL₂(ℤ)\ℍ`; Lewis–Zagier separation of cusp-form events at `Re w = 1`. |
| A18 | Operator-native nonvanishing on `Re w = 1`: derive `ζ(1 + it) ≠ 0` and the classical zero-free region from the Mayer operator without ζ's Dirichlet coefficients (transfer-operator analogue of the spectral Eisenstein method). Risk: may need the Euler product, then it is not operator-native. |
| B34 | A structure (Krein-definite, Herglotz, or a decay law) placing the scattering resonances of `SL₂(ℤ)\ℍ` on `Re s = 1/4`, i.e. off-line resonance exclusion — **RH**; a separated scattering-sector gap giving a fixed zero-free strip — **≥qRH**. |
| B35 | Source-specific energy/charge control excluding off-line poles while retaining the correction `2ζ(w−1)/(w−1)`; escape (two-prime Euler laws, positive gauge mass below damping `½`, exterior tightness) — **sub / ≥qRH**; cofinal complete-energy bounds — **RH**. |
| B36 | Source-faithful realization (PTR port, W1C Ising limit, RN directed sign) — **RH** (Σ8). |

### Route-specific items
| | Obstacle | Routes |
|---|---|---|
| A20 | Theta Hankel rank-8 strictness; ranks 9 and 10 | TH |
| A21 | Explicit thresholds: Hausdorff shifts, Jensen degree horizons, two-grid degrees; Toeplitz minors beyond PF₃₇ | PA, LA, HCF |
| A22 | The nine atom-dominated collar moduli | ACT |
| A23 | Mixed Schur debit; first-prime / coarse / polar costs on fixed cells | AIP, CHMD |
| A24 | Logarithmic two-point Chowla for distinct nonproportional affine forms (Tao) | MC |
| B37 | Odd-sector bound `R ≤ ½`; sinh-capacity on every window — **RH** (Σ7) | CHMD, TT, HF |
| B38 | All-rank / all-degree signs; Laguerre–Pólya property of `ξ(½ + z)` — **RH** (Σ6, Σ26) | TH, LA, HCF, PA, GTA; ART |
| B39 | Lower bounds for scheduled prime energies — **RH** (Σ20) | FU, CFC, RP, SZ, LI, FEL, EGC |
| B40 | Pre-divisor forcing — **RH** (Γ5) | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |

## 2. Programmes ADT and AHD

Thesis: the complete Weil family `W_{φ,c,N}` is a degenerating polarized family along the resolution
axis, with the dilation semigroup as monodromy; its first-order limit, extension data and second-order
term organize every complete-family route.

Established [L]:
- First order: rescaled limit `c^βE_m(c) → (2A/M)ζ(β+1)J_{β+1}(m)/φ(m)`; for the tilted spline (`β = 7`)
  `J(m) = J(1)#ℙ⁷(ℤ/m)`, the point count of a smooth projective scheme over `ℤ/m`; weight strings are
  Hensel towers; tensor law is the Chinese remainder theorem; the exponent `β` is set by the profile
  (`c³E_m → 0` for every C² profile).
- Monodromy: closed form, valuation lowering, eventually idempotent with spectrum `{0, 1}`; scaling form
  separating branches (`rad m`) and weights (`J`).
- Gluing: Redheffer `det = M(N)`; graded = positive cone sum of top strata; top = Möbius-signed sum of
  graded pieces.
- Selection: complete degeneration (`F_λ = 0`) holds exactly for `Λ`; every prime flip leaves an
  overlap-independent indefinite residue.
- Inheritance: fixed packets and the whole growing subthreshold block below `1/8`.
- Second order (AHD): bulk zero ledger positive and zero-blind; horizon ledger = Weil summands of the
  synthesized test; horizon formula with Weil's symbol; aliasing = dilation derivative of the bulk; exact
  critical-curve limit `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²`; critical-multiple calculus; horizon criterion.
- Traps recorded as theorems: positive rescaled limits are zero-blind; lowerings transport, not create,
  polarization; the archimedean carrier `1 − P − P̂` is indefinite.

Research status: the dictionary is complete through second order on horizon blocks and on fixed packets.
It locates the sign: the bulk is a count and carries none of it; the horizon layer carries all of it as
Weil's window form. The degeneration produces no positivity at second order beyond a prime-free term.

| | Obstacle |
|---|---|
| A4, A5 | (as in S1) strength of one fixed multiple; calibrations over `𝔽_q(T)` and on the fakes; pure block. |
| B2 | Full-space second-order identification and horizon localization — **sub**. |
| B1 | Weil's window sign — **RH**. |
| B20 | A count equal to Weil's window form, starting with windows of length `≤ log 3` — **RH** over all lengths; **sub** at a fixed length. |

## 3. Live routes

### WL — Weil lag / prime lag
Established: critical-energy, linear prime-error and one-sided `√x log²x` criteria; genus slope ⇔ RH +
simple; Chebyshev–Stirling split; Landau-window cost `(2 log 2 − ε)mn`; Adams threshold `2^{qr}`; `{2,3}`
stencil `ψ ≤ 23x/20`; multivariate parity producers at the main term.
- A: A13.
- B: B24; B23; joint Möbius-moment / Mertens / sawtooth payment at square-root precision (**RH**).

### RW — restricted Weil ground minimum
Established: `μ(A) ≥ 0 ∀A` ⇔ RH; RW's object is the horizon layer of the complete family (Weil's window
form); floors through `181/500`; zero-form operator positive on `0 < a ≤ 181/500`; exact `{∞,2}` trace
through `½ log 3`; semilocal carriers excluded; finite prime sets cross zero by `2 log(\|S\|+2) + 11`;
bounded-below weighted energy forces `(1+ε)`-syndetic weight; window Markov form with primes `n ≤ e^A`;
ceiling; near radical; finite divisor; visibility.
Research status: the next sign test is the aperture `½ log 3`, where the prime `3` enters; RW and HF read
the same form.
- A: A3, A4, A11.
- B: B1; B7; B20 (as producer); depth-weighted all-window mass bound (**≥qRH**).

### FU, CFC, RP, LI, SZ — scheduled prime sums
Established: exact receivers (completed Abel moment; first-clock tail coefficient; normalized history floor
`−B(K+2)`; guarded zero set `Z_S` finite with RH ⇔ `Z_S = ∅`; rectangular Ward defect bounded below);
cofinal unboundedness under ¬RH; transport identities; LI Cayley-ladder reflection-positivity receiver
[S]; SZ complete first-variation transfer [S].
- A: A6 (LI, SZ `[S]` items).
- B: B39 for each (seed/drift/prior/cross-block/endpoint payment; prime, archimedean and endpoint terms;
  high-LCM pairs at linear scale; outside budget at every guarded zero; complete source assembly).

### PA — prime–archimedean source passivity
Established: each fixed Hausdorff order positive at large shifts.
- A: A21. B: B38.

### MC — Möbius cancellation
Established: half-power dictionaries; `Θ ≥ ½`, Haar-a.e. `½`; RH ⇔ trivial point typical; every
positive-power band retains `2Θ`; Redheffer `det R_N = M(N)` = nerve Euler characteristic, `Ω±(√N)`, RH ⇔
`O_ε(N^{½+ε})`; coprimality signature `M(N)`; squarefree complex wedge decomposition (combinatorial);
finite-clock leaf squares paid.
- A: A9, A24.
- B: B24; B25; head/leaf signed cancellation (Σ20); B31. A discrete-Morse bound on `det R_N` needs
  cancellation between dimensions [D].

### TT — theta seam / Wold
Established: seam, tail and Wold receivers; `t < ½` threshold; Φ-Doob identities.
- A: none. B: B37.

### LA — Laguerre/Jensen and local heat
Established: every fixed Jensen degree eventually real-rooted; RH ⇔ every Xi Jensen polynomial splits;
slice floor `133/200`; right-half depth moment `o(V)`; PF₃₇ at the centre.
- A: A21, A10 (flow threshold). B: B38; uniform tail narrowing (**≥qRH**); exceptional heights (**sub**).

### TG — transgression / central gap
Established: winding/index and cubic-transgression identities; finite-matrix index laws along paths;
Kähler transport free; the window integer is decided by the window energy.
- A: none. B: B15 (integer `< 2` on every disc = window energy); B8 (source-driven noncrossing path).

### HF — Hodge / Hecke / complete cells
Established: S1 and S2 in full; the ADT/AHD dictionary (first order a point count, second order on horizon
blocks = Weil's window form + prime-free coercive term, horizon criterion); complete-cell index `≤ R + A`;
heat Hodge defect; band poles = Hodge defect; cyclic Hodge defect; packet identities, shell-degree rows,
coprime successor gap; Frobenius at infinity ⇔ RH; correspondence algebra with Tate's limit law; the RR
branch of S5.
Research status: the critical-curve term is identified on horizon blocks; HF's sign problem is RW's
window form. Open structural item: the full-space second order (B2). Whole-space `1/8`: three pieces in
Lean, join open.
- A: A1–A9, A11, A12.
- B: B1–B11, B20, B22, B32, B37.

### CHMD — causal hyperbolic–modular duality
Established: RH ⇔ `R ≤ ½` on the odd sector; Markov form and sinh capacity; window Markov form; Haar pieces
with uniform finite index except the first-prime coarse layer; growing-packet head-pole cancellation.
- A: A23. B: B12 (**≥qRH**); B37 (**RH**); B4.

### TH — theta Hankel ranks
Established: rank 7 strict; rank 8 PSD; heated orthant signs; all-rank signed-center positivity ⇔ RH;
native tails = Gram-square mass minus signed local flux.
- A: A20. B: B38; rank-uniform signed flux payment (**RH**).

### RN — renewal
Established: compact cone-positive renewal operator with exact determinant and resonances.
- A: none. B: directed mixed prime + Gamma `≥` pole (**RH**); B36.

### WD — Ward / collision / window energy
Established: S4 in full — window index = Wiener–Hopf index; separation-free `Θ(√m)` stabilization and the
9-way RH door opener; window energy with Laplace abscissa = twice the maximal depth; canonical multiplier,
Bessel cepstrum and finite certificates; log-stage certificate ⇔ inverse-log corridor; `E_γ(c₀ log T) =
O(1)` ⇒ Lindelöf and a half-plane bound; Hecke-defect ladder (half-gate, density TFAE to `2/3`, rate
`r < 1`); unit-window calculus.
Research status: the multiplier question is closed; WD is decided by a bound on the window energy, i.e. by
windowed zero power sums — a local precision statement per window.
- A: A10.
- B: B15, B16, B17, B18, B14, B19; B12 (tower branch).

### JAS, CTF, PBM, RB — one-sided count
Established: JAS positivity at growing logarithmic budget; CTF completion identities and Euler completion
error `≤ 1/(n+1)`; PBM convergence at every `σ > ½` ⇔ RH; RB colossally abundant reduction.
- A: none. B: B24 (square-root budget; covariance cancellation along cutoffs; coefficient cancellation;
  primorial remainder).

### HCF, XN, BAG, EWU, GTA, OWU
- HCF: two-grid criterion; one grid aliases. A: A21. B: B38.
- XN: Newton-disc criterion; nonnegative Laplacian of the margin. B: covering with nonnegative margin
  (**RH**).
- BAG: disc recurrence ⇔ RH; weak ladders collapse. B: B31.
- EWU: weight rigidity; attained aperture-antitone blind minima; RH ⇔ nonnegative weighted minima at every
  aperture. A: A3. B: B1.
- GTA: transverse-charge criterion; positive charge and finite-prefix convergence. B: B38.
- OWU: odd floor through `181/500`; Liouville-twist separation; companion forcing and conductor horizon
  have no common aperture. A: A3. B: B1 (odd sign at every aperture).

### SRT, ACT, AIP — complete atomic matrix
- SRT: S1 in full; horizon-layer criterion (AHD) and exact aliasing constant; depth-gap visibility; local
  count ⇒ bounded critical multiplicity. A: A1–A7. B: B1–B7; B12.
- ACT: collar threshold pays every modulus outside nine moduli. A: A22. B: B1.
- AIP: complete form = jump + incidence − shell + boundary; explicit shell rows; far-reserve costs absorbed
  below `1/8`. A: A1, A2, A7, A23. B: B1–B5.

### ACS — arithmetic Castelnuovo–Severi
Established: RH ⇔ effectivity ⇔ Hodge index ⇔ section count ⇔ Castelnuovo–Severi at rational scales;
universal floor law; finite divisor; near radical and genus function; isolated-pair edge; LST counts (Lévy
jump count to `1/64`, Stepanov over `𝔽_q`, self-dual point); correspondence algebra with naive-height
criterion; degree-three and degree-two FE fakes; natural-cone models with bounded local density.
- A: A11, A12, A14–A16, A19.
- B: B20, B22, B21 (**indep.**), B32, B26, B27, B1–B6, B11.

### SC — Stokes/Witt–Krein / archimedean successor
Path: `φ_c(a, b) = ratCorr(\|a\|) − c\|a\|^{−½}\|b\|` → `κ(φ_c) < 3` → `κ = 0` → RH.

Established: `κ(φ_c) = κ + 1` at every place; readings add; carrier classification; two-prime lattices
carry the full affine index; coupling ≡ kernel; finite stratum ⇒ RH; natural cone ⇒ RH or polynomial
repulsion; unattained-width cone models with exact spline weights; every finite rational Gram is a limit
of complete-matrix compressions on the single Beurling schedule, so RH ⇔ eventual pole-hyperplane sign on
that schedule; heat index one for `t ≥ 1/8`.
Research status: (1) realization — done; (2) cone with unattained width — open (B29), models with bounded
density exist; (3) finite nonzero index — open (B13); (4) finite-sieve → global — open (B30); (5) index
ceiling — open (B12); (6) SOS — open (B6); (7) glued index `≤ 1` = pole-hyperplane sign on the Beurling
schedule = Weil's window sign (B1, B28).
- A: A16, A19, A6 (finite clock products).
- B: B1, B6, B12–B14, B28–B30, B8.

### PM — physical / complete-energy realization (Gauss–Mayer)
Established: S7 in full — geodesic Euler product with least periods and orientation fibres; scattering
divisor = ζ's divisor; signed channels; Epstein/Eisenstein identification and continuation; scattering
core of finite positive energy at every zero; boundary `2ζ(s)/ζ(s+1)` = the rank-one intertwining ratio,
with positive slope coefficients and the classical zero-free region; contraction exactly on `Re w ≥ 1`.
Research status: Mayer 1 (geodesic product, translation lengths, multiplicities) — done; faithful divisor
in the scattering channel — done; zero-free region near `Re s = 1` — done through the boundary slope
(de la Vallée Poussin on PM's own observable, using ζ's coefficients); universal contraction below
`Re w = 1` refuted; core energy nonselective. Open: a structure that places resonances.
- A: A17, A18.
- B: B34, B35.

## 4. Candidates, support lines and retired branch

| Candidate | Established | A (just work) | B (open) |
|---|---|---|---|
| APF | Fredholm index, cycle-trace reconstruction | — | zero-independent divisor exhaustion (B40) |
| BSH | framed curvature | — | pre-divisor section and mate identity coupled to Ξ zeros (B40) |
| CDC | calibrated confluence iff `Re s = ½` | — | source-defined potential forcing confluence (B40) |
| DR | cusp roots, finite monodromy | — | compatible roots on the strict-right domain; global monodromy (Γ) |
| EGC | pole-safe contour; complete copy correction | — | outer expanding-contour sign (B39) |
| EWJ | Euler/Wold jets | — | zero-independent source admission (B40) |
| FEL | theta likelihood; BSY integral = off-line zero sum | — | predeclared source balance (B39) |
| HJ | Hurwitz residual = SEC charge, vanishing iff criticality | — | pre-divisor forcing (B40) |
| IRK | rotation-algebra trace / winding | — | arithmetic Poisson / projective lift with integral count (B20-type) |
| MSC | Möbius–Sonin; strict-right divisor preservation | — | bridge to nonnegative Sonin energy (B1) |
| PCS | singular co-shift | — | source-natural wall annihilation (B40) |
| PTR | lossless stacks, unit port gap | — | prime-faithful port (B36) |
| RFHM | support grade | — | symmetry-breaking law (B40) |
| SEC | essential norm = seam jump | — | pre-divisor compactness at zeros (B40) |
| W1C | finite Lee–Yang + Ising receiver; PM supplies a faithful ζ scattering divisor | — | couplings converging to Riemann's measure, or a positive/self-adjoint realization of the faithful divisor (B36, B34) |
| WBF | genealogy Gram | — | any arithmetic coupling (B40) |
| PW-B (retired) | optical flux vanishing iff critical | — | killed as a selector (fails at `3/4 + i`); survivor: the half-parameter cusp receiver, which needs B34 (**RH**) |

Support lines (not routes): ADT and AHD (Section 2); ART (centered approximation; survivor lands in B38);
ARGON-3 approaches B (Böttcher / period rigidity: ζ and all positive algebraic dilates differentially
independent over the theta–Gamma field) and C (two-place Krein: local conditions keep the full index);
HTGeometry `AffineExpanders`; the paused classical-formalization programme (Lax–Phillips, Voronoi, Zwegers,
Björner, logarithmic Chowla).

## 5. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ, Weil's window sign (horizon layer; every `K·c*`; single Beurling schedule) | RW, EWU, OWU, ACT, HF, SRT, AIP, ACS-atomic, SC, CHMD, TT; MSC, FEL; ADT/AHD |
| Σ, Hodge–Lefschetz / top coprime stratum | HF, ACS-Hodge, TG |
| Σ, rank / degree (Laguerre–Pólya) | TH, HCF, PA, GTA, LA; ART |
| Σ, scheduled prime sums | FU, CFC, RP, SZ, LI; EGC |
| Σ, realization / resonance placement | RN, PTR, W1C, PM |
| Π, window energy and near-line density (zero power sums per window) | WD, TG, LA (heat), SC-heat, census |
| Π, count-valued primitive `h¹` / naive height | ACS-effectivity, HF-RR; IRK; ADT/AHD |
| Π, one-point precision (incl. the Redheffer determinant) | WL, MC, PBM, RB, JAS, CTF, SC (coupling) |
| Π, conjugate diagonal | WD (Hecke defect), census |
| Γ, Frobenius at infinity / `Λ(s)/Λ(s+1)` | PM (resonances), HF (band poles, Hecke similitude), ACS (Rosati), BAG, XN, MC (typicality); APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |

Inside Σ the complete-family routes are one statement: Weil's form on window tests of every length. The
degeneration shows how the family carries it — a zero-blind point-count polarization in the bulk and
Weil's window form on the horizon layer, with a positive prime-free term at the critical curve. WD's
integer is a growth bound on windowed zero power sums. PM, the band poles of the Hodge defect and the
resonant partners read one function, `Λ(s)/Λ(s+1)`. The producers that could cross the edge remain an
identity (SOS on a two-prime lattice; a full-space second-order identity), a count (primitive `h¹`,
naive height) and an integer with a structural bound (no structural bound for the window integer is in
sight: its value is analytic).
