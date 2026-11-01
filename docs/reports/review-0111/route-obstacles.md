# Route obstacles — status quo

Scope: the 33 live routes, the 16 candidates and the retired PW-B branch of the frontier map, read
against the Lean corpus at `12f15b70bf` and the working tree. For every route: what is established,
the obstacles that are **(A) just work**, and the obstacles that are **(B) open mathematics**.
Just work means known mathematics, finite or certified computation, effectivization, finishing a
formalization in progress, or composition of proved statements. Open mathematics means a statement
nobody knows how to prove.

Evidence: `[L]` Lean; `[S]` Lean in the working tree or unintegrated; `[D]` derived here from Lean
statements, not formalized.

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
| Bounded Weil kernel ⇔ RH; coupling ≡ kernel with absolute constants; one lattice `⟨p⟩×⟨q⟩` decides; the Hecke orbit of one spectrally generic test under `ℤ log p + ℤ log q` carries the whole Hodge defect | RIT; ACPL `BoundedCouplingIsTheRiemannHypothesis`; ACS `TheHodgeDefectIsCyclic` [L] | every boundedness target is RH; the coupling is not softer; one rank-two orbit suffices |
| Glued state `κ(φ_c) = κ + 1` at `∞` and every prime; two primes with translations in `ℤ[1/qr]` carry it | AKG [L] | RH ⇔ `κ(φ_c) < 3` |
| No softening: Künneth, Hadamard and tensor powers are all-or-nothing | RIT; EHT `NoSofteningAtResolution` [L] | amplification never helps |
| Kähler package: HR transports wherever HL holds; Liouville = HL; RH ⇔ HL on the PSD locus; none of the three Lefschetz candidates is free | HWV [L] | deformation costs nothing and proves nothing; the content is nondegeneracy |
| Overlap = aperture: at `c*` margin = synthesis error = `1/log N`; a multiple `K·c*` sees radius `½ log K − O(1)`; RH ⇔ positivity at every fixed `K`; every divergent rate is a receiver | TM `ReceiverRate` [L] | the overlap multiple is the aperture (degree) axis |
| Degeneration: below the exponent `1/8` the rescaled family `c⁷W_{c,N}` converges to the diagonal Jordan-totient form `J(e) = (2A_φ/M)ζ(8)J₈(e)/φ(e) > 0`, its extension data vanish and fixed packets inherit positivity; at every multiple of `(log N)^{1/8}` conductor-Gram positivity is RH; prime dilations lower the conductor (monodromy) | ADT `TheLimitingMixedStructure`, `TheDilationsLowerTheConductor` [L]; weight strings [S] | the inherited regime ends exactly at the receiver; there the extension data carry the zeros |
| Tilted spline: all vectors positive for `c ≤ (log N)^α`, `α < 1/9`, with logarithmic defect confinement and reserve `c^{−8}`; fixed and polylogarithmic packets for `α < 1/8`; collective mid-band packets for `α < 1/4`; under ¬RH the edge lies in `[(log N)^{1/9−}, 2(log N)^{1/8+}]` infinitely often | CACT; SSHA; EHT `EdgeBelowOneNinth` [L] | the all-vector rough regime stops one exponent step below the receiver |
| Zero-free logarithmic profile: positive definite for `1 ≤ c ≤ ε₀·c*`; the logarithmic budget holds exactly up to `(α/B)L(log L)²`; RH ⇔ positivity at every `K·c*` | TM [L] | for this profile the rough regime is closed up to a constant factor |
| Constant-factor wall: relative cross-conductor residuals decay iff `c⁸ = o((log N)^{1−ε})` | HWV `TheCrossConductorPairings` [L] | estimates stop exactly where the receiver starts |
| Aperture ceiling `μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})`; no positive floor along unbounded apertures | ArithmeticCompensationTheory [L] | polynomial or exponential loss never reaches all apertures |
| Near radical at level `a`: dimension `≥ (2 − η)e^{2a}`, `\|W\| ≤ exp(−η²e^{2a}/(300a))‖f‖²`, blind to every zero below `2πe^{2a}`; its dimension counts distinct resolved zeros; the matching upper bound (genus law) forces almost all zeros simple at rate `1/log T` | RHTower `SharpWeilNearRadicalCount`; ACS `TheGenusFunctionReadsTheResolvedZeros`, `TheGenusLawForcesSimpleZeros` [L] | each degree carries `≈ 2e^{2a}` near-null directions; their exact count is a statement about multiplicities |
| Finite divisor: at every degree `a`, `Re W ≥ (10 + 68e^a)(1 − 1/π)‖f‖²` off `i/2` and a finite grid `D_a`; Hodge defect at degree `a` finite; over `𝔽_q` it is `0` or `∞` | ACS [L] | at each degree the Hodge index of `ℤ` is a finite-dimensional problem |
| Visibility: an isolated pair is seen at aperture `a` iff `S_δ(a) > (1/2π)log(ξ/2π)`; its edge in the multiple is `≈ (cδ log γ)^{1/δ}`; finite-aperture positivity forces companions of deep isolated zeros | ACS `TheCriticalMultipleOfAnIsolatedPair`; RHTower `IsolatedDeepZeroWeilDetection` [L] | a fixed multiple misses shallow high zeros; finite apertures exclude isolated zeros, not clusters |
| Markov form: `W = V_N‖g‖² + J(g) + ½⟨c,g⟩² − ½⟨s,g⟩²`, `J` the archimedean + prime jump energy, `V_N = Ω(0) − 2Σ_{n≤N}Λ(n)/√n`; RH ⇔ sinh-capacity bound at every level | RHTower `WeilMarkovPoleCapacity` [L] | the sign is a capacity inequality for a jump process with a creation potential |
| Semilocal: exact `{∞,2}` trace identity through `½ log 3`; zero-form operator positive on `0 < a ≤ 181/500`; no `{∞,p}` semilocal family carries positivity | SP `SemilocalPrimeTwoTrace` [L/S] | positivity is glued, never semilocal |
| Universal floor law: an ample cone of nonnegative degree satisfies RR iff it contains the open positive cone and the Hodge index holds; RR on an orbit ⇔ orientation | ACS; AOG [L] | no cone-type effectivity is sign-free |
| Section counts: Künneth RR `h_K(x) + h_K(−x) = ½x² + h¹_K + ½δ`; bidegree, fixed-rank, definite and Siegel counts excluded; isotropic count `ζ²` with a double pole; boost average restores `ζ(s+w)ζ(s−w)`; on prime-free cycles of radius `≤ 1/64` the primitive `h¹` is paid by the Lévy–Khintchine jump count of the Gamma factor; over `𝔽_q` the Stepanov count pays it | LST [L] | the sign is the nonnegativity of a primitive `h¹`; a count pays it at small radius and over `𝔽_q` |
| Correspondence algebra: Hecke graphs, λ-ring, Rosati involution, Lefschetz trace; theorem of the square free; Rosati positivity ⇔ orbit Hodge index ⇔ a naive height (or midpoint-convex log-count) at bounded distance from the integral Rosati form | AOG; ACP `TheTheoremOfTheSquareIsFree`; AET `TatesLimitLaw`, `TheConvexityOfCounts` [L] | Weil's second-proof algebra exists over `ℤ`; the missing input is a height that is nonnegative for an arithmetic reason |
| Hecke defect: dyadic means `O_c(log U)` for all `c < 1/2`; `O_c(log U)` for `c < c*` ⇔ near-line density rate `r < 2c*`, `c* ≤ 2/3`; near-line density at every rate `r < 1`; `o(log U)` ⇔ critical-scale clustering; one constant over dyadic scales ⇔ RH | CDG `LogScaleHeckeDefect/*` [L] | WD's precision ladder is a near-line density ladder |
| Quantization: collision charge = integer-theta Fredholm index = Wiener–Hopf index; index `0` ⇔ outer Szegő factorization ⇔ disk-unit sectoriality; stopping rule sound and eventually complete; the first artifact-free prefix is `≥ c√T` | CDG `SzegoCollision/*`, `SourceIntrinsicStoppingRule` [L/S] | RH = an even integer `< 2` per window; any quantized reading needs prefixes of size `√T` |
| Unattained width: cone, tower and escape receivers leave "`Θ` not attained"; attainment ⇒ `Θ < 1` | ACPL, AKLT [L]; PM [D] | excluding it outright is ≥qRH |
| Selection: every prime-set flip separated; zero-density twins of relative density `κ ∈ (0, 1/4)` separated iff the conductor series exceeds `1/s`; self-similar star flux only for generalized von Mangoldt weights | RIT, ACP, HWV [L] | selection among flips closed; selectors are margins |
| Frobenius at infinity `σ(ρ) = 1 − ρ̄`: RH ⇔ `σ` trivial ⇔ Hecke similitude of the collided form ⇔ one dyadic Hecke constant ⇔ partner saturation | EHT; CDG; RHTower [L] | the selection wall has four RH-equivalent readings |
| Mayer determinant `D(w,λ) = A + ζ(w)B`; real-`w` cone; `D(w,z)D(w,−z) = exp(−Σ even-word traces)`, `D ≠ 0` on `\|z\| ≤ 1` for `Re w > 2`; even Gauss words code hyperbolic `SL₂(ℤ)` classes | RIT `GaussMayer*` [L] | PM has a determinant, a trace formula over words and a coding; no Selberg-zeta link, no complex-`w` positivity |
| Heat: every even heated slice coefficient positive at `λ ≥ (133/200)/log\|t\|`; flow threshold `(2/3 + ε)/log X`; `μ(½) ≤ 33/200` | RHTower `Heat/*`; AHA [L] | heat floors are size floors |
| Census: simple critical `≥ 0.67250071`; cosine certificate `(R_cos(λ) + δ_λ − ε)N − S_cos ≤ N₀ˢ` | IGP; TTPC [L] | every census gain is a signed prime-pair surplus bound |
| Approximation by RH-true objects: centered curve products are bounded by their real values; their closure is the Laguerre–Pólya class | ART [L]; reading [D] | approximation routes land in the rank/degree class (Σ6) |
| Falsification certificates: second upper periodic point of the Xi Donoghue map; repeated real root of a reversed Xi Jensen section; nonnegative Ritz velocity | BOT, LA, HM [L] | finite tests for ¬RH; no converse |

## 1. Shared obstacle blocks

### S1. Complete Weil family across the critical overlap
Routes: HF, SRT, AIP, ACT, ACS-atomic, RW, EWU, OWU; SC through the ratCorr Grams; CHMD through
the index; TT through the odd/Markov sector.

Established:
- Tilted spline [L]: all vectors positive on `1 ≤ c ≤ (log N)^α`, `α < 1/9`, with reserve
  `(a₀/c⁷)(poleDefect − C log(2c)‖x‖²) + (κ₀/(2c⁷))‖x‖²`, sublevel confinement
  `poleDefect ≤ C log(2c)‖x‖²` and all-vector defect reserve `c^{−8}`; fixed and polylogarithmic
  packets for `α < 1/8`; collective mid-band packets for `α < 1/4`; receiver at every `K(log N)^{1/8}`.
- Prime self-form of the overlapping top costs `O(c(1 + log c))` [L]; shell degree rows: upward
  `O(c)`, downward `O(c(n/N)(1 + log n))` [L].
- Degeneration [L]: rescaled limit = Jordan-totient form below `1/8`; inheritance radius `1/8`;
  dilation monodromy lowering conductors; along `p`-towers the limit coefficient is a weight string
  with steps `p⁷` and `[8]_p = 1 + p + ⋯ + p⁷` [S].
- Zero-free logarithmic profile [L]: positive definite on `[1, ε₀·c*]` with explicit
  `ε₀ = 1/(128B)`; Denjoy–Carleman receiver at every `K·c*`; a fixed `K` sees radius `½ log K − O(1)`.
- Cross-conductor channels [L]: relative residual control decays exactly while `c⁸ = o(log N)`.
- Nonpositive directions localize in a finite conductor sector at every fixed overlap and in a
  `P`-smooth sector with `log P ≍ c¹⁶/η` at growing overlap [L].
- Every finite rational correlation Gram is a limit of complete Steklov packet Grams at a
  family-dependent multiple of `c*` [L], at a fixed multiple for the smooth Steklov profile [S].
- Degree laws [L]: ceiling, near radical, genus function, finite divisor, visibility law, isolated
  pair edge, companion forcing.
- Weil floors through radius `181/500` [L]; operator positivity on `0 < a ≤ 181/500` and the
  `{∞,2}` trace identity through `½ log 3` [S].
- Exact packet identities [L]: Mertens polarization, jump energy, affine incidence squares;
  successor and dyadic rigidity with kernel the constant packet; coprime successor gap beyond
  `K ≥ Q(Q−1)`.

| | Obstacle |
|---|---|
| A1 | Tilted spline from `α < 1/9` to `α < 1/8` on all vectors: lower the split cross payment from `c⁹` to `c^{8+o(1)}`, using the collective packet coercivity to `1/4`, the logarithmic confinement and the `O(c(1 + log c))` top self-form. |
| A2 | Constants: the largest multiple `K_est` of the logarithmic profile that absolute estimates reach before residual and margin constants meet; explicit horizons `N₀` for the `1/9` theorem, the logarithmic profile and the receivers. |
| A3 | Single-`K` completeness of the Steklov/sinc schedule at `K L(log L)²` (one fixed `K` exhausting the full index). |
| A4 | Certified Weil positivity at `½ log 3` and the next prime apertures: the finite divisor and the `{∞,2}` trace identity make each one a certified finite Schur-complement computation (near-radical dimension `≈ 2e^{2a}`, i.e. `≈ 6` at `½ log 3`). |
| A5 | Close the `[S]` status of: fixed-multiple ratCorr realization (AKG `WeilGramsAtCriticalOverlap`), weight strings (ADT), operator positivity and semilocal obstructions (SP), all-profile Künneth positivity through `181/500`. |
| A6 | Leading term of the extension data in the inherited regime: the explicit first-order correction to the Jordan-totient limit as a function of `c⁸/log N`, from the cross-conductor pairings; extend the Jordan-totient limit to every profile with a regular spectral tail. |
| B1 | Positivity at every fixed multiple `K·c*` (all-aperture Weil positivity) — **RH** over all `K`; each fixed `K` is **sub** and implies Weil positivity at radius `½ log K − O(1)` (Σ1). |
| B2 | Extension data at the critical exponent: the exact leading term of the cross-conductor pairings at `c⁸ ≍ log N` (spline) and at `K·c*` (Denjoy–Carleman), where the limit polarization stops being inherited — **RH** over all `K` (Σ1i, Π15). |
| B3 | Critical-scale identification: the `N → ∞` limit of the family at fixed `K`, identified as Weil's form at radius `½ log K` plus a coercive conductor part; no converse transfer from finite apertures to fixed `K` is known — **sub** (Σ1i). |
| B4 | Joint shell–pole and non-arithmetic Gamma-graph payment on growing packets (confinement exponent `≤ 8`) — **sub** (Σ1c, Σ1g). |
| B5 | Low-conductor spans below `(log N)^A`; conductors `N^{½} < m ≤ N` (Elliott–Halberstam type) — **sub** (Σ1d, Σ1e). |
| B6 | Exact sum-of-squares identity for Weil's dilation form on one two-prime lattice — **RH** (Σ18). |
| B7 | Cluster exclusion: finite-aperture positivity forces companions of isolated deep zeros; clustered off-line zeros below the Landau height need a further input — **sub** (Π8). |

### S2. Kähler package, stars and gluing
Routes: HF, ACS-Hodge, AIP, TG, SC, RW.

Established [L]:
- Kähler package; Liouville = HL; RH ⇔ HL on the PSD locus; three Lefschetz candidates, none free.
- Fixed-overlap limit form `Σ E_m(c) y_m²` polarized by an identity, ground state the pole
  conductor, degenerating to `0` along every growing schedule.
- Stars: the star of `d` is the family at `(c⌊N/d⌋/N, ⌊N/d⌋)` for every weight; positivity descends;
  deep stars positive; depth law `log d − C₀`, sharp `log d − ε`, primitive `log d + 2log 2 − ε`.
- Metzler sign gauge on stars of depth `d ≳ c`, failing across shallow stars.
- Möbius gluing over the nerve; renormalized recursion; gcd stratification
  `W = Σ_g Cop(W at the star of g)`, each stratum off-diagonal and indefinite; every successor pair
  and the archimedean overlap of consecutive atoms lie in `g = 1`.
- Layers of a prime; Euler-product tensorization with tower gap `log p/(1 − p^{−σ})`, minimum
  `2 log 2`.
- Links of the dilation complex disconnected; over a curve with a rational point every link is
  complete. Squarefree prime complex: the augmented star at `2` is a cone.
- Nerve reduced Euler characteristic `−M(N)`; RH ⇔ `|χ̃| = O(N^{½+δ})`.
- Conductor ↔ star duality; conductor Gram graded by the lcm; conductor Gram PSD at every
  `2K(log N)^{1/8}` ⇔ RH.
- No positive semilocal carrier [S]; Hecke orbit of one generic test carries the whole defect.
- Finite affine expander: the Margulis–Gabber–Galil walk on `(ℤ/n)²` contracts zero-sum
  fluctuations by `5√2/8` uniformly in `n ≥ 3` (HTGeometry `AffineExpanders`); no link to the Weil
  form.

| | Obstacle |
|---|---|
| A7 | Quantitative depth law: explicit `d₀(c)` beyond which star margins beat shallow-star coupling; explicit horizons in `exists_star_positive_tiltedUnitSpline`. |
| A8 | Finite-`N` tabulation of the gcd strata and of the top-stratum deficit (the identities are exact). |
| B8 | HL on the positive locus of the overlap flow — **RH** (Σ2). |
| B9 | Gluing across the coprime stratum: pay the top gcd stratum (successor + archimedean coupling) by the root defect, the coprime successor gap and the star depth margins (star ascent) — **RH** (Σ3a). |
| B10 | A cross-tower spectral gap through the archimedean channel in place of connected links (Garland/trickle-down unavailable over `ℤ`; semilocal carriers excluded) — **method**; its uniform version is **RH** (Σ23, Σ25). |
| B11 | Noncancellation for the loop-Eisenstein band poles (`κ_Hodge = #` band poles of `Λ(s)/Λ(s+1)`) — **RH** (Σ19). |

### S3. Index and finite off-line support
Routes: HKT, AKLT, AID, SRT towers, CHMD index, SC, RIT-Künneth.

Established [L]: bounded finite-index kernels = PD minus `κ` unitary characters; index-one
dichotomy; `κ ≤ r` ⇔ translation-stable positive constraints of dimension `≤ r`; index =
right-zero count; collision mass `2(κ + excess)`; explicit capture stage for complete-cell
indices; finite divisor gives a finite defect at every degree.

| | Obstacle |
|---|---|
| B12 | Arithmetic index ceiling uniform in resolution — **≥qRH** for `K_ζ`; **RH** for `K_ζ ⊠ K_ζ` (Σ4). |

### S4. Heat, collision charge and Hecke defect
Routes: WD, LA, TG, HCF, SC-heat, TH-heat; census; HEF.

Established:
- Heat state `κ(φ_c^{(t)}) − 1 = N(t)/2`; heat Hodge defect `N(t)/2`; bounded `N` ⇔ bounded `O` [L].
- Moving barrier `N(t) ≤ 2O(R(0))`; unit-window increments `n_off ≤ ΔO ≤ 2n·n_off`, `ΔO ≪ log²T` [L].
- Integer-theta Fredholm collision index; per stabilized window: index `< 2` ⇔ index `0` ⇔
  Wiener–Hopf `L²` invertibility ⇔ outer Birkhoff–Zhukovsky–Szegő factorization ⇔ disk-unit
  sectoriality; arithmetic reality of the collision loop under `z ↦ 1 − z̄` [L].
- Root-free stopping certificate; seam-smooth prefixes [L]; prefix strip multiplicity
  `Θ(N² log N)`, zero-free in the strip above `C(N+2)²`, first artifact-free prefix `≥ c√T` [S].
- Hecke defect [L]: dyadic means `O_c(log U)` for all `c < 1/2` (also for the unit-window
  supremum); four-way TFAE with near-line density rates `r < 2c*`, `c* ≤ 2/3`; near-line density at
  every rate `r < 1`; almost-all corridor `(1 + ε)loglog T/log T`; `o(log U)` ⇔ critical-scale
  clustering; five-way dyadic RH equivalence for min/mean/sup/`C²`-jet; under finite off-line
  support with ¬RH fixed-`c` jets vanish while dyadic readings are unbounded.
- Heat slice floor `133/200`; flow floor `2/3 + ε` [L].

| | Obstacle |
|---|---|
| A9 | Flow threshold `Λ_X` from the sub-Weyl profiles (slice floor `133/200`, flow floor `2/3 + ε`). |
| A10 | Certified de Bruijn–Newman upper bound in corpus normalization as an index-one heat time. |
| A11 | One statement: uniform `ΔO = o(log T)` ⇒ critical density one ⇒ off-line sparsity ⇒ Lindelöf (the pieces exist). |
| A12 | Computable stopping prefix: certified interval bounds replacing compact minima. |
| B13 | Subcritical heat count `N(t) ≤ exp(At^{−a})`, `a < 1` — **sub**. |
| B14 | Pointwise heat horizon constant `< ½` — **≥qRH**. |
| B15 | Index `0` on every stabilized window: a source-defined sectorial multiplier (outer factorization) for every window collision loop; equivalently collision charge `< 2` everywhere, no heat-index jump on `(0, 1/8]` — **RH** (Σ5). |
| B16 | Cumulative charge `O(T) = o(N(T))` — **sub**. |
| B17 | Uniform increment `ΔO = o(log T)` — **LH**. |
| B18 | Polynomial-in-height stabilized prefix: a separation or boundary-modulus lower bound making the integer-theta index stabilize at prefix `T^{O(1)}` (the lower bound `c√T` holds) — **indep.** (Π13). |
| B19 | Hecke defect at doubly-logarithmic scale, multiplicity `o(log\|γ\|)` — **sub**. |
| B20 | Near-line density at exponential rate `r ≥ 1` (Hecke gate beyond `½`; rates `r < 4/3` reach `2/3`) — **sub** (Π5). |
| B21 | Dyadic mean `o(log U)` ⇔ 100% of zeros within `κ/log T` for every `κ > 0` — **sub** (Π5). |
| B22 | Fixed-scale `E_γ(c log T) = O(1)` — **≥qRH**. |
| B23 | One constant for `E_γ` over all dyadic scales — **RH** (Γ4, Π5). |
| B24 | An arithmetic input beyond counts and the linear explicit formula for the conjugate diagonal — **method**; every pointwise step is ≥qRH [D]. |

### S5. Counts, producers and Riemann–Roch
Routes: WL, MC, PBM, RB, JAS, CTF, ACS-effectivity, HF-RR, RW; census.

Established [L]:
- One-sided count ⇔ RH; prime-error budget `≥ 2 + γ − log 4π`; multivariate parity-selective
  producers reach `ψ, θ ≤ (1 + ε)x + C_ε log²x`; every individual producer has slope `> 1`;
  integer-Chebyshev ceiling `exp(−0.87n)`.
- Nerve Euler characteristic `−M(N)`.
- Riemann–Roch branch:
  - theta `h⁰` with RR on `Spec ℤ` and on the pole plane; `Λ(s)` is its Mellin generating function;
  - universal floor law; RR on an orbit ⇔ orientation;
  - Künneth RR with primitive `h¹ = ½δ`; bidegree blindness; rank law; definite fakes created by
    the boost (the self-dual point `ℤ ⊕ ℤ` has no real zero); Siegel majorant ⇔ Hodge; isotropic
    count `ζ²` needs a logarithmic completion; the boost transform restores the Euler product;
    Hecke correspondences are similitudes of primitive `h¹`;
  - prime-free cycles: `W = Ω(0)‖f‖² + J(f) + pole term` with the Lévy–Khintchine jump count `J`;
    the count alone pays `|Ω(0)|` and the pole for radius `≤ 1/64`, giving `h¹_prim ≥ ‖f‖²/40`;
  - curve calibration: primitive `h¹` = degree of the correspondence; the Stepanov count pays it on
    every Frobenius window of every odd-characteristic hyperelliptic curve;
  - Künneth effectivity on prime-free cycles and off the finite divisor at every degree, imported
    from estimates; all-profile Künneth effectivity through `181/500` [S].
- Genus function: lower bound by distinct resolved zeros; genus law ⇒ almost all zeros simple.
- Census: `0.6725`; cosine certificate; odd-stabilizer exact Poisson and transport chain.

| | Obstacle |
|---|---|
| A13 | Same-order mixed-jet recovery for `≥ 3` primes. |
| A14 | Explicit `ε ↦ (support, coefficients, C_ε)` for the main-term producer. |
| A15 | Census: bound `S_cos(λ)` for `λ ≤ 1`, where prime-pair estimates are classical, and record the bandwidth-one certificate; odd-stabilizer global calibration; stabilizer at `β = 2`. |
| A16 | Count reading of the whole prime-free window `a < ½ log 2`: count the interior jumps (gaps `< a`) and the pole term; the target `W ≥ 0` there is known by estimates. |
| A17 | Calibration data for the count problem: the Künneth primitive `h¹` on the finite divisor `D_a ∪ {i/2}` at small `a`, its dimension and sign. |
| B25 | A count-valued primitive `h¹`: a section count reading the test component, on lattices whose rank grows with the class, with a Poisson-type duality, whose primitive `h¹` is `½W(f, f)` and nonnegative by construction; equivalently a naive height on the integral correspondence ring at bounded distance from the Rosati form — **RH**; at one fixed degree past the first prime (the Hecke graph `T₂`) — **sub** (Π11h, Γ19). |
| B26 | The genus law: the near radical at degree `a` has dimension `(2 + o(1))e^{2a}` — **indep.**; it implies that all but `o(T)` zeros are simple and isolated at scale `exp(−η²T/(20 log T))` (Π16). |
| B27 | Logarithmic Serre duality for the split surface: a completion of the isotropic count (`ζ²`, double pole) matching `h⁰(D) − h⁰(D^∨) = log(D²/2)` — **sub** (Π11f). |
| B28 | `ε`-uniform producer: zero-free-region error **sub**; square-root error **RH** (Π3). |
| B29 | Any unconditional source input at square-root precision — **RH** (Π2). |
| B30 | Near-band cyclotomic energy `O(N^{3/2+ε})` on a positive-power band — **≥qRH** (Π10). |
| B31 | Signed prime-pair surplus beyond bandwidth one: `S_cos(λ)` for `λ > 1`, `S ≤ (1/18 + o(1))N` at `4/3`, `E(1/9) ≤ 4` — **sub** (Π7). |

### S6. Carriers, gluing, coupling and selection
Routes: SC, ACS, HF; Γ-candidates.

Established [L]: coupling calculus and Hyers–Ulam stability; bounded-coupling, rate, cone and
finite-stratum theorems; curve coupling bounded ⇔ unitary ⇔ Castelnuovo–Severi on the Frobenius
span; carrier classification and unique proper-subgroup split; every `p`-adic neighbourhood, every
two-free-prime lattice and a fixed three-prime core carry the full affine index; separable
assemblies blind or pointwise non-convergent, coupled matching exact but signless; global pole =
extremal weight; prime-set flip selection with exact resolution thresholds, including zero-density
twins below `1/4`; divisor-identity selection; correspondence algebra (λ-ring, Rosati, Lefschetz,
theorem of the square, `ππ′ = q`); Tate's limit law and the convexity of counts on the integral
correspondence ring.

| | Obstacle |
|---|---|
| A18 | `𝔽_q(X)` calibration: local walls at higher-degree places, global Hecke product formula, archimedean Weil state of a curve. |
| A19 | `𝔽₃` elliptic loop chain: measure-compatible unfolding, Eisenstein convergence, constant term (elliptic adeles, idele Haar, simple-root intertwining integrals, Weyl-series convergence and loop-group cells are formalized; the chain is not assembled). |
| B32 | Bounded coupling on one two-prime lattice — **RH** (Σ17). |
| B33 | "Bounded cone coupling ⇒ RH" as a pure implication — **sub**; excluding unattained width outright — **≥qRH**. |
| B34 | Zero–one law `κ ∈ {0, ∞}` (with the first rung it gives RH) — **sub**. |
| B35 | Zero-independent selection at the trivial gauge point — **RH** (Γ1). |
| B36 | Frobenius at infinity as an operator: Rosati positivity of the correspondence algebra (a naive height on the integral Rosati form), a conformal correspondence of factor `≠ 1`, or a Hecke similitude of the collided form — **RH** (Γ4, Γ19). |
| B37 | Unimodular gauges with `S_N/H_N → 1`; functional-equation twins without Euler product; prime-flip twins of density `0` or irregular density — **sub** (Γ12, Γ15). |

### S7. Realization and scattering
Routes: PM, RN, PTR, W1C.

Established [L]: regularized Gauss–Mayer operator (cutoff renormalization, nuclear of order 0,
entire Fredholm determinant, source holomorphy, word traces, `D = A + ζB`, `B(w,−1) = 0`,
convergent raw finite-branch determinants, exact finite part); real-`w` derivative cone, `B ≠ 0`
for small real `λ`, `D(w,−1) ≠ 0`, rank-one resolvent pole; signed determinant product
`D(w,z)D(w,−z) = exp(−Σ_n z^{2n+2}/(n+1) Σ even-word traces)` with absolute summability over all
even words for `Re w > 1` near `z = 0`, on `|z| ≤ 1` for `Re w > 2`, and `D(w,z) ≠ 0` there;
primitive-orbit exponent; even Gauss words ↔ digit-pair words ↔ hyperbolic `SL₂(ℤ)` classes;
resonant Eisenstein states with partner angle; algebraic recentering of the critical parabola
impossible; lossless realization needs infinitely many resonances; normal real-zero approximants
force RH (Vitali).

| | Obstacle |
|---|---|
| A20 | Mayer–Selberg identity: Euler product of `D(w,1)D(w,−1)` over primitive hyperbolic classes (the Selberg zeta of `PSL₂(ℤ)`), continuation to `½ < Re w < 1`, and the scattering-determinant link, so that ζ zeros become eigenvalue-`±1` events of the transfer operator (known mathematics, heavy formalization). |
| B38 | Off-line resonance exclusion (zero-selecting scattering rigidity) — **RH** (Σ8, Γ4). |
| B39 | A Hermitian (Lewis–Zagier / Krein) structure on eigenfunctions of the transfer operator near `Re w = 1`, scattering sector included, giving a zero-free region near `Re s = 1`; cone contraction cannot separate the cusp-form events on the line from scattering events just left of it — **sub**. |
| B40 | Source-faithful realization: prime-faithful lossless port (PTR), centred Ising limit (W1C), directed renewal sign (RN) — **RH** (Σ8). |

### Route-specific items
| | Obstacle | Routes |
|---|---|---|
| A21 | Theta Hankel rank-8 strictness; ranks 9 and 10 | TH |
| A22 | Explicit thresholds: Hausdorff shifts, Jensen degree horizons, two-grid fixed degrees | PA, LA, HCF |
| A23 | The nine atom-dominated moduli of the collar shift | ACT |
| A24 | Mixed Schur debit on fixed blocks; first-prime / coarse / polar costs on fixed cells | AIP, CHMD |
| A25 | Toeplitz minors of the Xi centre sequence beyond PF₃₇ | LA |
| B41 | Odd-sector bound `R ≤ ½` — **RH** (Σ7) | CHMD, TT |
| B42 | All-rank / all-degree theta, heat, Jensen, PF and two-grid signs; equivalently the Laguerre–Pólya property of `ξ(½ + z)`, which is also the endpoint of every centered-approximation scheme — **RH** (Σ6, Σ26) | TH, LA, HCF, PA, GTA; ART |
| B43 | Lower bounds for scheduled prime energies — **RH** (Σ20) | FU, CFC, RP, SZ, LI, FEL, EGC |
| B44 | Pre-divisor forcing: a section or potential coupled to Ξ before the divisor — **RH** (Γ5) | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |

## 2. Live routes

### WL — Weil lag / prime lag
Established: critical-energy, linear prime-error and one-sided `√x log²x` criteria; genus slope ⇔
RH + simple; `Count(a)` iff `a − 1 ∈ 𝒬`; Chebyshev–Stirling split; Landau-window cost
`(2 log 2 − ε)mn`; Adams threshold `2^{qr}`; `{2,3}` stencil `ψ ≤ 23x/20`; multivariate parity
producers at the main term.
- A: A13, A14.
- B: B29 (one-sided count, Π1); B28; joint Möbius-moment / Mertens / sawtooth payment at
  square-root precision (**RH**).

### RW — restricted Weil ground minimum
Established: `μ(A) ≥ 0 ∀A` ⇔ RH; floors through radius `181/500`; the restricted form is the trace
of the zero-form operator, positive on `0 < a ≤ 181/500`, with the exact `{∞,2}` trace identity
through `½ log 3`, where positivity ⇔ the single-prime family energy `≥ 0` [S]; no semilocal
positive carrier [S]; the floor dies doubly exponentially; near radical `≈ 2e^{2A}` at doubly
exponentially small energy; genus function counts distinct resolved zeros; finite divisor at every
aperture; visibility law; isolated-pair edge; companion forcing.
- A: A4, A5.
- B: B1 (all-aperture sign, **RH**); B7 (clusters, **sub**); the depth-weighted branch needs an
  all-window mass bound (**≥qRH**). The genus law B26 is **indep.** and not on RW's path.

### FU — Fourier/Abel prime scheduling
Established: completed Abel moment bounded above ⇒ RH; narrow-window negative prime channel.
- A: none.
- B: B43 (joint seed, drift, prior, cross-block and endpoint terms).

### CFC — first-clock sine coefficient
Established: RH ⇔ coefficient `≥ −C` on the aperture tail; unbounded below under ¬RH; phase-natural
transport is the identity.
- A: none.
- B: B43 (source lower bound retaining prime, archimedean and endpoint terms).

### RP — normalized prime history
Established: RH ⇔ history `≥ −B(K+2)` eventually; unconditionally below `−δ(K+2)` cofinally; finite
prime-clock density cancellation; low-LCM and copied-diagonal payment.
- A: none.
- B: B43 with high-LCM pairs, moving core and singular transport at linear scale.

### PA — prime–archimedean source passivity
Established: each fixed Hausdorff order positive at large shifts.
- A: A22.
- B: B42 (all-order / all-shift positivity).

### MC — Möbius cancellation
Established: half-power dictionaries; `Θ ≥ ½`, Haar-a.e. `½`; RH ⇔ trivial point typical;
cyclotomic remainder `≥ 0`; every positive-power band retains `2Θ`; prime-star nerve signed face
count `= M(N)`; Dirichlet inputs uniform for `q ≤ (log x)^A`; individual finite-clock leaf squares
paid.
- A: none beyond the Siegel–Walfisz range.
- B: B29 (moving-scale half-power cancellation, **RH**); B30 (**≥qRH**); head/leaf signed
  cancellation of finite prime clocks (Σ20); B35 (**RH**).

### TT — theta seam / Wold
Established: seam, tail and Wold receivers; `t < ½` threshold; truncated theta transform
`= −seed·B_N(ρ)` at zeros; two-horizon windowed aperture modes; Φ-Doob identities retaining every
reflected-prime term.
- A: none.
- B: B41 (all-test directed covariance or complete odd positivity).

### LA — Laguerre/Jensen and local heat
Established: every fixed Jensen degree eventually real-rooted; RH ⇔ every Xi Jensen polynomial
splits; a repeated root of a reversed section refutes RH; slice floor `133/200`;
`λ_t log t → 0` ⇔ every fixed-depth strip holds all high zeros; right-half depth moment `o(V)`;
`μ(½) ≤ 33/200`; PF₃₇ at the centre.
- A: A22, A9, A25.
- B: B42 (all degrees / all heights); uniform tail narrowing (**≥qRH**); shrinking-scale and
  exceptional-height control (**sub**).

### TG — transgression / central gap
Established: winding/index and cubic-transgression identities; finite-matrix index laws along paths;
regularized deformation of every fixed-width spline horizon ⇔ RH; Kähler transport free; no free
Lefschetz operator.
- A: none.
- B: B15 (integer trace `< 1` on every disc); B8 (a source-driven noncrossing path).

### HF — Hodge / Hecke / complete cells
Established:
- S1 and S2 in full, including the degeneration: Jordan-totient limit, inheritance radius `1/8`,
  dilation monodromy and weight strings.
- Haar/prime-edge Gamma reserve; full Weil index `≤ R + A` for `R` coarse cells.
- Heat Hodge defect `N(t)/2`; renormalized Hodge sign ⇔ quadratic RR ⇔ scaling-surface Hodge;
  loop-Eisenstein band poles = Hodge defect; cyclic Hodge defect on one Hecke orbit.
- Packet identities; coprime successor gap; shell degree row bounds.
- Frobenius at infinity ⇔ RH; correspondence algebra with λ-ring, theorem of the square, Tate's
  limit law.
- The RR branch of S5, including the jump-count reading of prime-free cycles and the Stepanov
  calibration over `𝔽_q`.
- A: A1–A8; A16; A17; A24.
- B: B1–B11; B25 (count-valued primitive `h¹`, **RH**) with B27 (**sub**); B36 (Hecke similitude /
  naive height, **RH**).

### CHMD — causal hyperbolic–modular duality
Established: RH ⇔ `R ≤ ½` on the odd sector; Markov-form and sinh-capacity criterion; prime wave
`O(e^{|u|/2})`; every Haar piece except the first-prime coarse layer has uniform finite index; the
Gamma graph pays the prime-two block; a growing Euler head alone is unbounded; the full prime window
cancels the head pole on fixed and growing packets.
- A: A24.
- B: B12 (uniform coarse-size control, **≥qRH**); B41 (**RH**); B4.

### TH — theta Hankel ranks
Established: rank 7 strict; rank 8 PSD; `I₇(a) ≥ 0` on `0 < a < ½`; heated orthant signs at all
ranks; all-rank signed-center positivity ⇔ RH; Ritz velocity identity; native tails = Gram-square
mass minus signed local flux.
- A: A21.
- B: B42; rank-uniform signed flux payment.

### RN — renewal
Established: Green/BV realization; compact cone-positive renewal operator with exact regularized
determinant and resonances.
- A: none.
- B: directed mixed prime + Gamma `≥` pole; real spectrum does not follow from cone positivity;
  native unregularized synthesis is a no-go (B40).

### WD — Ward / collision / heat
Established: S4 in full — Fredholm/Wiener–Hopf index with the six-way index-zero equivalence and
arithmetic reality; root-free stopping rule; prefix strip multiplicity `Θ(N² log N)` and the `c√T`
prefix lower bound [S]; unit-window increments and unit-window calculus; Hecke-defect hierarchy with
the half-gate closed and the density equivalence to `2/3`; zero-coordinate-free finite-theta RH
equivalence.
- A: A9–A12; A5 for the `[S]` prefix module.
- B: B13–B24; vanishing global depth energy as `t ↓ 0` (**RH**); tower-branch index ceiling (B12).

### LI — guarded history zeros
Established: `Z_S` finite; RH ⇔ `Z_S = ∅`; under ¬RH the last zero has odd order; Cayley–Li
primitive-sign receiver (RH ⇔ reflection positivity of the Cayley ladder) [S].
- A: none.
- B: B43 (pay the outside budget at every guarded zero, or establish the primitive sign).

### SZ — Suzuki / Ward defect
Established: ¬RH ⇒ cofinally unbounded below; finite packet light-Gram identity; negative
finite-cutoff pairings of the Abel clock; the Xi Donoghue map fixes `i`, and under RH `i` is its
only upper periodic point; complete first-variation transfer [S]; fixed-scale, sublinear and
bounded-Gamma producers excluded.
- A: none.
- B: B43 (uniform lower bound after complete source assembly); no converse to the Donoghue
  falsification criterion.

### PM — physical / complete-energy realization
Established:
- Gauss–Mayer operator and determinant (S7): real-`w` positivity, signed even-word trace formula,
  non-vanishing on the closed unit disc for `Re w > 2`, primitive coding.
- Resonant Eisenstein states: truncated norm `|Λ(ρ−1)|² Y^{1−Re ρ}/(1 − Re ρ)`; partner angle
  `cos² = 4Reρ(1 − Reρ)`, saturated iff critical.
- Complete-energy and gauge-mass receivers, half-damping admission, escape alternative.
- Reading [D]: with A20, ζ zeros in `½ < Re w < 1` are eigenvalue-`±1` events of the transfer
  operator; PM's selection is supplied by the modular surface, and its open core is Frobenius at
  infinity in the form of partner saturation.
- A: A20.
- B: B38 (**RH**); B39 (**sub**); cofinal complete-energy bound as `ε ↓ 0` (**RH**); exterior
  tightness and exclusion of infinite-height escape (unattained width; **≥qRH** when excluded
  outright).

### JAS — joint ancestry
Established: positivity at growing logarithmic prime budget; finite-support/phase/grade admission.
- A: none.
- B: square-root power budget (B29).

### CTF — completion transfer
Established: Euler completion error `≤ 1/(n+1)`; equal limits of full and finite-source energies;
exact completion, optimizer and residual-square identities.
- A: none.
- B: full-source energy decay by signed covariance cancellation (Π); `X^ε` receiver in the inner
  cutoff (Π).

### HCF — two-grid Hankel
Established: both `log 2`/`log 3` grids with polar cancellation ⇔ RH; one grid aliases.
- A: A22.
- B: B42 (both grid signs at every degree and height).

### XN — Newton dynamics
Established: RH ⇔ ξ-Newton source margin on discs; nonnegative Laplacian of the margin.
- A: none.
- B: cover every zero with nonnegative margin (**RH**, Γ).

### BAG — Bagchi recurrence
Established: RH ⇔ disc recurrence on every closed disc of the strip; universality; weak ladders
collapse to RH.
- A: none.
- B: B35 (returns near every right-strip point, possible zeros included).

### EWU — Euler weights
Established: RH ⇔ at every aperture some real weights make the full Weil functional nonnegative;
the obstruction dual is a blind test; weight rigidity.
- A: A4.
- B: B1 (nonnegative actual minimum at every aperture).

### GTA — transverse charge
Established: transverse-charge decay criterion; positive charge and strong finite-prefix
convergence.
- A: none.
- B: B42 (rank-uniform arithmetic transverse-energy decay).

### OWU — odd Weil selectivity
Established: every `r > 27/50` has a smooth odd test on `[−r, r]` with `W_ζ > mass/25` and
`W_Liouville < −3 mass/10`; at `a ≤ 181/500` the odd reflection sector carries no Hodge defect;
companion forcing and conductor horizon incompatible.
- A: A4 (odd tests beyond `27/50`).
- B: B1 (all-test / all-aperture odd sign).

### PBM — pole-regularized prime series
Established: convergence at every `σ > ½` ⇔ RH.
- A: none.
- B: coefficient cancellation (B29).

### RB — Robin / Nicolas
Established: large counterexamples need growing prime cores; colossally abundant reduction.
- A: none.
- B: square-root remainder on primorials (B29).

### SRT — square-root threshold / zero visibility
Established: S1 in full; depth-gap visibility; local count ⇒ bounded critical multiplicity
(density-one heights); deep zeros `o(V)`; Steklov full index for `β > 2`; unit-window increments;
companion forcing.
- A: A1–A6.
- B: B1–B7; tower-branch index ceiling (B12, **≥qRH**); unattained-depth detection (Σ4).

### ACT — collar transport
Established: explicit collar threshold pays every modulus outside nine atom-dominated moduli.
- A: A23.
- B: one fixed shift paying every profile including exterior primes (B1).

### AIP — arithmetic incidence positivity
Established: S1 in full; complete form = prime jump energy + nonnegative affine incidence energy +
signed shell/boundary terms, with explicit shell-degree rows; all-aperture allocation receiver;
full Weil index `≤ R + A`.
- A: A1, A2, A6, A24.
- B: all-aperture allocation (B1, **RH**); B2–B5.

### ACS — arithmetic Castelnuovo–Severi
Established:
- RH ⇔ effectivity ⇔ Hodge index ⇔ section count ⇔ Castelnuovo–Severi at rational scales.
- Universal floor law; RR on orbits ⇔ orientation; finite divisor and finite Hodge defect at every
  degree; reflection-sector additivity of the defect.
- Near radical, genus function (distinct resolved zeros), genus law ⇒ almost all zeros simple.
- LST count classification (S5), including the jump-count reading of prime-free cycles and the
  Stepanov count over `𝔽_q`; correspondence algebra with λ-ring and naive-height criterion.
- Visibility law; isolated-pair edge in the multiple; finite-index constraint classification;
  curve coupling bounded ⇔ unitary; quantitative complete-cell transfer at rate `N^{−1/2}`;
  `𝔽_q` elliptic adelic chain in progress.
- A: A15–A19; the S1 A-items.
- B: B25 (**RH**), B27 (**sub**); B26 (**indep.**); B36 (**RH**); census B31; B1–B6; B11.

### SC — Stokes/Witt–Krein / archimedean successor
Path: `φ_c(a, b) = ratCorr(|a|) − c|a|^{−½}|b|` → `κ(φ_c) < 3` → `κ = 0` → RH.

Established:
- `κ(φ_c) = κ + 1` at every place and for primitive Dirichlet L-functions; translation reading `1`;
  readings add; dilation form + shell squares on boost mass zero.
- Stable gluing; pole pair invisible to the boost index; carrier classification and unique
  proper-subgroup split; continuous-dilation carriers reading `1_H` exist iff `H ∈ {{0}, ℚ}`.
- Every `p`-adic neighbourhood, every two-free-prime lattice and a fixed three-prime core carry the
  full affine index.
- Coupling ≡ kernel; one lattice decides; cone; finite stratum ⇒ RH from single-lattice coupling.
- ratCorr Grams are complete-family packet Grams at a fixed multiple of the critical overlap [S]:
  the glued index is a face of S1.
- Heat-deformed state; Künneth branch all-or-nothing; coupled assemblies exact, separable blind.

Reading [D]: `K_ζ(u)` is the normalized smoothed prime error in a fixed-length multiplicative window;
bounded coupling is window PNT at square-root precision (Π4).
- A: A18; A10 (heat calibration); A5 (fixed-multiple realization).
- B: independent `κ(φ_c) < 3`, i.e. B1 on the ratCorr Grams (**RH**); B6 (**RH**); B32 (**RH**);
  B33 (**sub**); B15 on the heat branch (**RH**); B13 (**sub**); B12 for the Künneth square
  (**RH**); B8 (**RH**).

## 3. Candidates and retired branch

| Candidate | Established | A (just work) | B (open) |
|---|---|---|---|
| APF | Fredholm index, cycle-trace reconstruction | — | zero-independent divisor exhaustion (B44) |
| BSH | framed curvature | — | pre-divisor section and mate identity coupled to Ξ zeros (B44) |
| CDC | calibrated confluence iff `Re s = ½` | — | source-defined potential forcing confluence (B44) |
| DR | cusp roots, finite monodromy | — | compatible roots on the strict-right domain; global monodromy (Γ) |
| EGC | pole-safe contour | — | outer expanding-contour sign; raw decay cannot beat the Gamma floor (B43) |
| EWJ | Euler/Wold jets | — | zero-independent source admission (B44) |
| FEL | theta likelihood; BSY integral = off-line zero sum | — | predeclared source balance (B43) |
| HJ | Hurwitz residual = SEC charge, vanishing iff criticality | — | pre-divisor forcing (B44) |
| IRK | rotation-algebra trace / winding | — | arithmetic Poisson / projective lift with integral count (B25-type) |
| MSC | Möbius–Sonin | — | bridge to nonnegative Sonin energy (B1) |
| PCS | singular co-shift | — | source-natural wall annihilation; shift ≠ dilation (B44) |
| PTR | lossless stacks, unit port gap | — | prime-faithful port; infinitely many resonances needed (B40) |
| RFHM | support grade; reversible sewing inverse-covariant | — | symmetry-breaking law (B44) |
| SEC | essential norm = seam jump | — | pre-divisor compactness at zeros (B44) |
| W1C | finite Lee–Yang + Ising receiver; Vitali obstruction | — | couplings converging to Riemann's measure (B40) |
| WBF | genealogy Gram | — | any arithmetic coupling (B44) |
| PW-B (retired) | zero-independent source family at every nonreal strip point; optical flux `−16(Re s − ½)Im s·M₊M₋`, vanishing iff critical | — | killed as a selector (fails at `3/4 + i`); survivor: the half-parameter cusp `Λ(s) = 0` receiver, which needs B38 (**RH**) |

Support programmes (not routes): ADT feeds S1/S2 (degeneration); SP feeds RW/EWU/OWU (semilocal
trace); ART supplies the centered-approximation closure (B42); LST and AET feed S5/S6; HTGeometry
`AffineExpanders` supplies a finite expander family with no Weil-form link.

## 4. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ, degree axis (positivity at every `K·c*` / every aperture; extension data at the critical exponent) | RW, EWU, OWU, ACT, HF, SRT, AIP, ACS-atomic, SC (glued index), CHMD, TT; MSC, FEL |
| Σ, Hodge–Lefschetz / gluing across the coprime stratum | HF, ACS-Hodge, TG |
| Σ, heat / collision integer (window index `0`) | WD, LA (heat), TG, SC-heat |
| Σ, rank / degree (Laguerre–Pólya) | TH, HCF, PA, GTA, LA (Jensen); ART approximation |
| Σ, scheduled prime sums | FU, CFC, RP, SZ, LI; EGC |
| Σ, realization | RN, PTR, W1C, PM (Mayer resonances) |
| Π, count-valued primitive `h¹` / naive height | ACS-effectivity, HF-RR; IRK |
| Π, one-point precision | WL, MC, PBM, RB, JAS, CTF, SC (coupling = window PNT) |
| Π, conjugate diagonal / near-line density | WD (Hecke defect), census |
| Γ, selection / Frobenius at infinity | BAG, XN, PM (partner saturation), MC (typicality), ACS (Rosati), HF (Hecke similitude); APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF; PW-B (retired) |

Inside Σ the complete-family routes share one axis: the overlap multiple `K`, the radius
`½ log K` and the degree `a` are one coordinate. Below the critical exponent the family degenerates
to a positive Euler-factor polarization (the Jordan-totient form) and inherits its sign; the
estimates prove positivity there (tilted spline to `(log N)^{1/9}` on all vectors and to
`(log N)^{1/8}` on fixed packets, logarithmic profile to `ε₀·c*`). At the critical exponent the
extension data reach the size of the limit and carry the zeros; only an exact leading term
decides. At each degree the remaining problem is finite-dimensional (finite divisor), but it
carries `≈ 2e^{2a}` near-null directions whose energy is doubly exponentially small and whose
number reads the resolved zeros. Positivity is glued, never semilocal, and its unpaid part sits in
the top gcd stratum. The sign has to come from an exact producer — a count (a primitive `h¹` or a
naive height on correspondences), a quantized integer (window index), or an identity (SOS on a
two-prime lattice) — or from a structural selector. SC and WD each carry a second, Π-type target:
SC the window prime error read through the coupling, WD the conjugate-diagonal Hecke defect, a
near-line density ladder. PM's open core is Frobenius at infinity as partner saturation.
