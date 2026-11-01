# Route obstacles — status quo

Scope: the 33 live routes, the 16 candidates and the retired PW-B branch of the frontier map, read
against the Lean corpus at `91e9c8f54f` and the working tree. For every route: what is established,
the obstacles that are **(A) just work**, and the obstacles that are **(B) open mathematics**.
Just work means known mathematics, finite or certified computation, effectivization, finishing a
formalization in progress, or composition of proved statements.

Evidence: `[L]` Lean; `[S]` Lean in progress; `[D]` derived here from Lean statements, not
formalized.

Strength of a B-item: **RH** equivalent to RH; **≥qRH** implies Lindelöf and a zero-free
half-plane; **LH** implies Lindelöf; **sub** strictly weaker or of unknown strength; **indep.**
logically independent of RH; **method** a missing tool, not a statement.

Wall labels Σ/Π/Γ refer to `walls-ledger.md`. Programme codes follow the frontier-map source
locator; further codes: ACPL = ArithmeticCouplingTheory, EHT = EdgeHodgeTheory,
HWV = HodgeTheoryWithoutVarieties, LST = LatticeSectionTheory, RIT = RenormalizedIntersectionTheory,
CSAR = CriticalScaleArithmeticRigidity, AOG = ArithmeticOrientationGeometry, BOT = Bottcher.

## 0. Calibration (applies to every route)

| Fact | Anchor | Consequence |
|---|---|---|
| `κ = #` distinct right-half zeros, even; RH ⇔ `κ < 2`; finite `κ` ⇒ all high zeros critical ⇒ `Θ < 1` | AOG `TheIndexExit` [L] | every index route ends in one even integer; finite-index waypoints are ≥qRH |
| Bounded Weil kernel ⇔ RH; coupling ≡ kernel with absolute constants; one lattice `⟨p⟩×⟨q⟩` decides | RIT; ACPL `TheCouplingIsAsLargeAsTheKernel`, `BoundedCouplingIsTheRiemannHypothesis` [L] | every boundedness target is RH; the coupling is not softer |
| Glued state `κ(φ_c) = κ + 1` at `∞` and every prime | AKG [L] | RH ⇔ `κ(φ_c) < 3` |
| No softening: Künneth, Hadamard and tensor powers are all-or-nothing | RIT; EHT `NoSofteningAtResolution` [L] | amplification never helps |
| Kähler package: HR transports wherever HL holds; Liouville = HL; RH ⇔ HL on the PSD locus; none of the three Lefschetz candidates (dilation, overlap flow, coupling Laplacian) is free | HWV `TheKahlerPackage`, `TheLiouvilleProperty`, `TheLefschetzCandidates` [L] | deformation costs nothing and proves nothing; the content is nondegeneracy |
| Overlap = aperture: at the critical overlap `c*` margin = synthesis error = `1/log N`; a multiple `K·c*` synthesizes radius-`R` tests on the block `[N/B, N]`, `B ≈ e^{2R+2}`, i.e. sees radius `½ log K − O(1)`; RH ⇔ positivity at every fixed `K`; every divergent rate is a receiver | TM `ReceiverRate` [L] | the overlap multiple is the aperture (degree) axis |
| Tilted spline: all vectors positive for `c ≤ (log N)^α`, `α < 1/9`; fixed and polylogarithmic packets for `α < 1/8`; RH ⇔ positivity at every `K(log N)^{1/8}`; under ¬RH the edge lies in `[(log N)^{1/9−}, 2(log N)^{1/8+}]` infinitely often | CACT `TelescopedConductorSplitAndOneNinthWeilPositivity`, `BilinearConductorResidualsAndOneEighthPackets`; SSHA `EveryEighthRootMultipleReceivesTheTiltedSpline`; EHT `EdgeBelowOneNinth` [L] | the spline's rough regime stops one exponent step below its receiver |
| Zero-free logarithmic profile (C∞, no real Fourier zeros, Denjoy–Carleman class): positive definite for `1 ≤ c ≤ ε·c*`; RH ⇔ positivity at every `K·c*` | TM `TheLogarithmicProfileIsPositiveBelowCriticalOverlap`, `riemannHypothesis_iff_forall_critical_multiple` [L] | for this profile the rough regime is closed up to a constant factor |
| Constant-factor wall: relative cross-conductor residuals decay iff `c⁸ = o((log N)^{1−ε})`; at the receiver scale only the exact leading term decides; the Hilbert–Schmidt residual mass stays small past the RH exponent but cannot see small margins | HWV `TheCrossConductorPairings` [L] | estimates stop exactly where the receiver starts |
| Aperture floor `μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})`; no positive floor along unbounded apertures | ArithmeticCompensationTheory [L] | polynomial or exponential loss never reaches all apertures |
| Near radical: at level `a` a space of dimension `(2 − η)e^{2a}` with `|W| ≤ exp(−η²e^{2a}/(300a))‖f‖²`, built from tests blind to every zero below the Landau height `2πe^{2a}` | RHTower `SharpWeilNearRadicalCount` [L] | each degree carries `≈ 2e^{2a}` directions signed only by zeros above `2πe^{2a}` |
| Finite divisor: at every degree `a`, `Re W ≥ c_a‖f‖²`, `c_a = (10 + 68e^a)(1 − 1/π)`, on tests vanishing at `i/2` and on a finite grid `D_a`; the Hodge defect at degree `a` is finite (doubly exponential bound); over `𝔽_q` it is `0` or `∞`; the golden fake admits no finite divisor beyond `log 5/2` | ACS `SourceRiemannRochAwayFromTheLowFrequencyDivisor`, `TheHodgeDefectOfZetaIsFiniteAtEveryDegree`, `TheHodgeIndexOfZetaHoldsAwayFromLowFrequencies` [L] | at each degree the Hodge index of `ℤ` is a finite-dimensional problem |
| Visibility: an isolated pair is seen at aperture `a` iff `S_δ(a) = sinh(2δa)/(2δ) − a > (1/2π)log(ξ/2π)`; finite-aperture positivity forces an off-line companion near every deep isolated zero | ACS `ArchimedeanDominationIsBlindAtEveryDepth`; RHTower `IsolatedDeepZeroWeilDetection` [L] | finite apertures exclude isolated zeros; clusters survive |
| Universal floor law: on any polar surface an ample cone of nonnegative degree satisfies the RR axiom iff it contains the open positive cone and the Hodge index holds; RR on the orbit of a cycle ⇔ its orientation | ACS `SectionEffectivityAndTheUniversalFloorLaw`; AOG `SectionsOnTheOrbitOfACycle` [L] | no cone-type effectivity is sign-free |
| Section counts: Künneth RR `h_K(x) + h_K(−x) = ½x² + h¹_K + ½δ`; bidegree counts see no primitive class; fixed-rank counts violate RI; definite counts have off-line zeros (`ℤ ⊕ 8ℤ`); Siegel majorant `≥ 0` ⇔ Hodge index; isotropic cone count `= Γ(σ)(2π)^{−σ}ζ(σ)²` with a double pole, no Poisson pair; boost average `∫Z⁺e^{2wu}du = Kζ(s+w)ζ(s−w)`; over curves the primitive `h¹` of a graph is the degree of the correspondence (`N₁` for `1 − F`); Hecke correspondences scale primitive `h¹` | LST [L] | the sign is the nonnegativity of a primitive `h¹`; it must be a count that reads the test component |
| Correspondence algebra: Hecke graphs, Rosati involution, Lefschetz trace; Rosati positivity ⇔ orbit Hodge index; the Lefschetz trace of a corrector is primitive energy; eventual Hasse–Weil ⇒ Hasse–Weil | AOG `TheCorrespondenceAlgebra`, `CorrectorsAndTheLefschetzTrace`, `EventualHasseWeilIsHasseWeil` [L] | Weil's second-proof algebra exists over `ℤ` without its positivity |
| Hecke defect: dyadic means `O_c(log U)` for `c < 22/51` [L], `c < 1/2` [S]; `O_c(log U)` for all `c < c*` ⇔ near-line density rate `r` for all `r < 2c*`, `c* ≤ 2/3` [S]; `o(log U)` ⇔ critical-scale clustering; fixed scale ⇔ corridor (≥qRH); one constant over dyadic scales ⇔ RH; counts + linear explicit formula cannot bound it | CDG `LogScaleHeckeDefect/*` | WD's precision ladder is a near-line density ladder |
| Quantization: collision charge = integer-theta Fredholm index; root-free stopping rule sound and eventually complete; the first stabilized prefix exceeds `N₀` once a window holds more zeros than prefix `N₀` has in the whole strip | CDG `ThetaPrefixIndexTransition`, `SourceIntrinsicStoppingRule` [L] | RH = an integer `< 2` per window; height-uniform reading open |
| Unattained width: cone, tower and escape receivers leave "`Θ` not attained"; attainment ⇒ `Θ < 1` | ACPL, AKLT [L]; PM [D] | excluding it outright is ≥qRH |
| Selection: every prime-set flip separated; zero-density twins of relative density `κ ∈ (0, 1/4)` separated iff the conductor series exceeds `1/s`; self-similar star flux only for generalized von Mangoldt weights | RIT, ACP, HWV [L] | selection among flips closed; selectors are margins |
| Frobenius at infinity `σ(ρ) = 1 − ρ̄`: RH ⇔ `σ` trivial ⇔ Hecke similitude of the collided form ⇔ one dyadic Hecke constant ⇔ partner saturation | EHT `FrobeniusAtInfinity`; CDG; RHTower `EisensteinResonantPartnerAngle` [L] | the selection wall has four RH-equivalent readings |
| Mayer determinant `D(w,λ) = A + ζ(w)B`; for real `w > 0`: derivative cone with remaining mass `(3/2)^{−w}`, `B(w,λ) ≠ 0` on `0 < λ < (3/2)^w`, `D(w,−1) ≠ 0`; even Gauss words code hyperbolic `SL₂(ℤ)` classes | RIT `GaussMayer*` [L] | PM has a determinant and a coding; no trace identity, no complex-`w` positivity |
| Heat: every even heated slice coefficient positive at `λ ≥ (133/200)/log|t|` for large `|t|`; flow threshold `(2/3 + ε)/log X`; `μ(½) ≤ 33/200`, `μ(5/6) ≤ 2/53` | RHTower `Heat/SubWeylSourcesLowerTheHeatFloor`; AHA [L] | heat floors are size floors |
| Census: simple critical `≥ 0.67250071`; cosine certificate `(R_cos(λ) + δ_λ − ε)N − S_cos ≤ N₀ˢ` on `λ ∈ (0, 2]`, `R_cos(4/3) ≥ 3/4 + 79/1250`, `R_cos(2) ≥ 5/6 + 43/3750` | IGP; TTPC `CosinePrimeSurplusCriterion` [L] | every census gain is a signed prime-pair surplus bound |
| Falsification certificates: second upper periodic point of the Xi Donoghue map; repeated real root of a reversed Xi Jensen section; nonnegative Ritz velocity | BOT, LA, HM [L] | finite tests for ¬RH; no converse |

## 1. Shared obstacle blocks

### S1. Complete Weil family across the critical overlap
Routes: HF, SRT, AIP, ACT, ACS-atomic, RW, EWU, OWU; CHMD through the index; SC through the
ratCorr Grams; TT through the odd/Markov sector.

Established [L]:
- Tilted spline: rough regime to `α < 1/9` on all vectors and on every single conductor, `α < 1/8`
  on fixed and polylogarithmic conductor packets; receiver at every `K(log N)^{1/8}`.
- Zero-free logarithmic profile: positive definite on `[1, ε·c*]`; Denjoy–Carleman receiver at every
  `K·c*`.
- A fixed `K` sees radius `½ log K − O(1)`; RH is the union of the bounded rates.
- Cross-conductor channels: relative residual control decays exactly while `c⁸ = o(log N)`.
- Nonpositive directions localize in a finite conductor sector at every fixed overlap, and in a
  `P`-smooth sector with `log P ≍ c¹⁶/η` at growing overlap.
- Floor ceiling, near radical, finite divisor, visibility law, companion forcing.
- Weil floors through radius `181/500` and at an explicit `A₊ > 181/500`.
- Exact packet identities: Mertens polarization, jump energy, affine incidence squares; successor and
  dyadic rigidity with kernel the constant packet.

| | Obstacle |
|---|---|
| A1 | Tilted spline from `α < 1/9` to `α < 1/8` on all vectors: lower the split cross payment from `c⁹` to `c^{8+o(1)}`; collective packet coercivity to `α < 1/4` and logarithmic defect confinement are in progress [S]. |
| A2 | Constants: the explicit `ε` of the logarithmic profile and the largest multiple `K_est` that absolute estimates reach before the residual and margin constants meet. |
| A3 | Edge of one off-line pair in the RVM model: compose the visibility law with `K ↔ ½ log K`; expected edge `≲ C e^{2a(ρ)}·c*` [D]. |
| A4 | Propagate `1/9` into the statements that still carry the exponent `1/59` (EHT crossing, window and limit structure; HWV Liouville, stars, Lefschetz candidates). |
| A5 | Explicit horizons `N₀` for the `1/9` theorem, the logarithmic profile and the receivers (all are eventual). |
| A6 | Single-`K` completeness of the Steklov/sinc schedule at `K L(log L)²`. |
| A7 | ratCorr Grams at `K·c*` as smooth-bump packets of the complete family (synthesis + Lévy continuity); links SC to S1. |
| A8 | Size of the shell degree `d_n` at overlap `c`; comparison of CSAR rigidity with the complete energy on fixed and slowly growing packets. |
| A9 | Certified Hodge index at small degree past `½ log 3`: off the finite divisor the form is coercive, so each degree is a certified Schur-complement computation; the proved dimension bound is doubly exponential in `a`, so only small degrees are practical. |
| B1 | Positivity at every fixed multiple `K·c*` (all-aperture Weil positivity) — **RH** over all `K`; each fixed `K` is **sub** and implies Weil positivity at radius `½ log K − O(1)` (Σ1). |
| B2 | Constant-factor wall: the exact leading term of the overlap residual at `c⁸ ≍ log N` (spline) and at `K·c*` (Denjoy–Carleman), where generic bounds stop decaying — **RH** over all `K` (Σ1i, Π15). |
| B3 | Critical-scale identification: the `N → ∞` limit form at fixed `K`, identified as Weil's form at radius `½ log K` plus a coercive conductor part; the corpus has no converse transfer from finite apertures to fixed `K` — **sub** (Σ1i). |
| B4 | Joint shell–pole and non-arithmetic Gamma-graph payment on growing packets (confinement exponent `≤ 8`) — **sub** (Σ1c, Σ1g). |
| B5 | Low-conductor spans below `(log N)^A`; conductors `N^{½} < m ≤ N` (Elliott–Halberstam type) — **sub** (Σ1d, Σ1e). |
| B6 | Exact sum-of-squares identity for Weil's dilation form on one two-prime lattice — **RH** (Σ18). |
| B7 | Cluster exclusion: finite-aperture positivity forces companions of isolated deep zeros; clustered off-line zeros below the Landau height need a further input — **sub** (Π8). |

### S2. Kähler package, stars and gluing
Routes: HF, ACS-Hodge, AIP, TG, SC.

Established [L]:
- Kähler package; Liouville = HL; RH ⇔ HL on the PSD locus; three Lefschetz candidates, none free.
- Stars: the star of `d` is the family at `(c⌊N/d⌋/N, ⌊N/d⌋)` for every weight; positivity descends;
  deep stars positive; depth law `R_N ≥ (log d − C₀)|x|²`, sharp `log d − ε`, primitive
  `log d + 2 log 2 − ε`.
- The Metzler sign gauge holds on stars of depth `d ≳ c` and fails across shallow stars.
- Möbius gluing over the nerve; renormalized recursion with root defect and Mertens remainder;
  gcd stratification `W = Σ_g Cop(W at the star of g)`, each stratum off-diagonal and indefinite;
  every successor pair and the whole archimedean overlap of consecutive atoms lie in the top stratum
  `g = 1`.
- Layers of a prime (the Künneth step at the horizon); Euler-product tensorization with tower gap
  `log p/(1 − p^{−σ})`, minimum `2 log 2`.
- Links of the dilation complex are disconnected (towers of distinct primes never adjacent); over a
  curve with a rational point every link is complete.
- Nerve of the star cover = squarefree `n ≤ N`, reduced Euler characteristic `−M(N)`; RH ⇔
  `|χ̃| = O(N^{½+δ})`.
- Conductor ↔ star triangular duality; conductor Gram graded by the lcm; conductor Gram PSD at every
  `2K(log N)^{1/8}` ⇔ RH.

| | Obstacle |
|---|---|
| A10 | Quantitative depth law: explicit `d₀(c)` beyond which star margins beat shallow-star coupling; explicit horizons in `exists_star_positive_tiltedUnitSpline`. |
| A11 | Finite-`N` tabulation of the gcd strata and of the top-stratum deficit (the identities are exact). |
| B8 | HL on the positive locus of the overlap flow — **RH** (Σ2). |
| B9 | Gluing across the coprime stratum: pay the top gcd stratum (successor + archimedean coupling) by the root defect and the star depth margins (star ascent) — **RH** (Σ3a). |
| B10 | A cross-tower spectral gap in place of connected links (Garland/trickle-down unavailable over `ℤ`; coprime atoms meet only through the archimedean place) — **method**; its uniform version is **RH** (Σ23). |
| B11 | Noncancellation for the loop-Eisenstein band poles (`κ_Hodge = #` band poles of `Λ(s)/Λ(s+1)`) — **RH** (Σ19). |

### S3. Index and finite off-line support
Routes: HKT, AKLT, AID, SRT towers, CHMD index, SC, RIT-Künneth.

Established [L]: bounded finite-index kernels = PD minus `κ` unitary characters; index-one dichotomy;
`κ ≤ r` ⇔ translation-stable positive constraints of dimension `≤ r`; index = right-zero count;
collision mass `2(κ + excess)`; explicit capture stage for complete-cell indices; finite divisor
gives a finite defect at every degree.

| | Obstacle |
|---|---|
| B12 | Arithmetic index ceiling uniform in resolution — **≥qRH** for `K_ζ`; **RH** for `K_ζ ⊠ K_ζ` (Σ4). |

### S4. Heat, collision charge and Hecke defect
Routes: WD, LA, TG, HCF, SC-heat, TH-heat; census; HEF.

Established:
- Heat state `κ(φ_c^{(t)}) − 1 = N(t)/2`; heat Hodge defect `N(t)/2`; bounded `N` ⇔ bounded `O` [L].
- Moving barrier `N(t) ≤ 2O(R(0))`; unit-window increments `n_off ≤ ΔO ≤ 2n·n_off`, `ΔO ≪ log²T` [L].
- Integer-theta Fredholm collision index; root-free stopping certificate; seam-smooth prefixes [L].
- Hecke-defect hierarchy (calibration table); half-gate and density equivalence [S].
- Heat slice floor `133/200`; flow threshold `2/3 + ε` [L].

| | Obstacle |
|---|---|
| A12 | Finish the half-gate chain: means to `c < 1/2`, density equivalence to `2/3`, corridor `(1 + ε)loglog T/log T` [S]. |
| A13 | Flow threshold `Λ_X` from the sub-Weyl profiles (the slice floor is `133/200`, the flow floor `2/3 + ε`). |
| A14 | Certified de Bruijn–Newman upper bound in corpus normalization as an index-one heat time. |
| A15 | One statement: uniform `ΔO = o(log T)` ⇒ critical density one ⇒ off-line sparsity ⇒ Lindelöf (the pieces exist). |
| A16 | Computable stopping prefix: certified interval bounds replacing compact minima. |
| A17 | Growth of the strip-zero count of finite theta prefixes; it is the unconditional lower bound for the first stabilized prefix in height. |
| B13 | Subcritical heat count `N(t) ≤ exp(At^{−a})`, `a < 1` — **sub**. |
| B14 | Pointwise heat horizon constant `< ½` — **≥qRH**. |
| B15 | Collision charge `< 2` on every window; no heat-index jump on `(0, 1/8]` — **RH** (Σ5). |
| B16 | Cumulative charge `O(T) = o(N(T))` — **sub**. |
| B17 | Uniform increment `ΔO = o(log T)` — **LH**. |
| B18 | Detection scale independent of zero gaps — **sub** (Π13). |
| B19 | Hecke defect at doubly-logarithmic scale, multiplicity `o(log|γ|)` — **sub**. |
| B20 | Near-line density at exponential rate `r ≥ 1` (Hecke gate beyond `½`; rates `r < 4/3` reach `2/3`) — **sub** (Π5). |
| B21 | Dyadic mean `o(log U)` ⇔ 100% of zeros within `κ/log T` for every `κ > 0` — **sub** (Π5). |
| B22 | Fixed-scale `E_γ(c log T) = O(1)` — **≥qRH**. |
| B23 | One constant for `E_γ` over all dyadic scales — **RH** (Γ4, Π5). |
| B24 | An arithmetic input beyond counts and the linear explicit formula for the conjugate diagonal — **method**; every pointwise step is ≥qRH [D]. |
| B25 | Height-uniform quantized reading: boundary-modulus or separation lower bounds that make the integer-theta index stabilize at a prefix polynomial in height — **indep.** (Π13). |

### S5. Counts, producers and Riemann–Roch
Routes: WL, MC, PBM, RB, JAS, CTF, ACS-effectivity, HF-RR; census.

Established [L]:
- One-sided count ⇔ RH; prime-error budget `≥ 2 + γ − log 4π`; growing-alphabet producers reach
  `ψ, θ ≤ (1 + ε)x + C_ε log²x`; every individual producer has slope `> 1`.
- Nerve Euler characteristic `−M(N)`: the count wall as a bound on the topology of the star cover.
- Riemann–Roch branch:
  - theta `h⁰` with RR on `Spec ℤ` and on the pole plane; `Λ(s)` is its Mellin generating function;
  - universal floor law; RR on an orbit ⇔ orientation;
  - Künneth RR with primitive `h¹ = ½δ`; bidegree blindness; rank law; definite fakes; Siegel
    majorant ⇔ Hodge; isotropic count `ζ²` needs a logarithmic completion; the boost transform
    restores the Euler product; Hecke correspondences are similitudes of primitive `h¹`;
  - curve calibration: primitive `h¹` = degree of the correspondence;
  - Künneth effectivity on prime-free cycles and off the finite divisor at every degree — both
    imported from estimates, not produced by the count.
- Census: `0.6725`; cosine certificate; odd-stabilizer exact Poisson and transport chain.

| | Obstacle |
|---|---|
| A18 | Same-order mixed-jet recovery for `≥ 3` primes. |
| A19 | Explicit `ε ↦ (support, coefficients, C_ε)` for the main-term producer. |
| A20 | Census: bound `S_cos(λ)` for `λ ≤ 1`, where prime-pair estimates are classical, and record the bandwidth-one certificate; odd-stabilizer global calibration [S]; stabilizer at `β = 2`. |
| A21 | Calibration data for the count problem: the Künneth primitive `h¹` on the finite divisor `D_a ∪ {i/2}` at small `a`, its dimension and sign. |
| B26 | A count-valued primitive `h¹`: a section count reading the test component, on lattices whose rank grows with the class, with a Poisson-type duality, whose primitive `h¹` is `½W(f, f)` and nonnegative by construction — **RH** (Π11h). |
| B27 | The genus law: the near radical at degree `a` has dimension `(2 + o(1))e^{2a}` (upper Landau–Widom half) — **sub** (Π16). |
| B28 | Logarithmic Serre duality for the split surface: a completion of the isotropic count (`ζ²`, double pole) matching `h⁰(D) − h⁰(D^∨) = log(D²/2)` — **sub** (Π11f). |
| B29 | `ε`-uniform producer: zero-free-region error **sub**; square-root error **RH** (Π3). |
| B30 | Any unconditional source input at square-root precision — **RH** (Π2). |
| B31 | Near-band cyclotomic energy `O(N^{3/2+ε})` on a positive-power band — **≥qRH** (Π10). |
| B32 | Signed prime-pair surplus beyond bandwidth one: `S_cos(λ)` for `λ > 1`, `S ≤ (1/18 + o(1))N` at `4/3`, `E(1/9) ≤ 4` — **sub** (Π7). |

### S6. Carriers, gluing, coupling and selection
Routes: SC, ACS, HF; Γ-candidates.

Established [L]: coupling calculus and Hyers–Ulam stability; bounded-coupling, rate, cone and
finite-stratum theorems; curve coupling bounded ⇔ unitary ⇔ Castelnuovo–Severi on the Frobenius
span; carrier classification and unique proper-subgroup split; every `p`-adic neighbourhood and every
two-free-prime lattice carries the full affine index; separable assemblies blind or pointwise
non-convergent, coupled matching exact but signless; global pole = extremal weight; prime-set flip
selection including zero-density twins below `1/4`; divisor-identity selection; correspondence
algebra (Rosati, Lefschetz, `ππ′ = q`).

| | Obstacle |
|---|---|
| A22 | `𝔽_q(X)` calibration: local walls at higher-degree places, global Hecke product formula, archimedean Weil state of a curve. |
| A23 | `𝔽₃` loop chain: measure-compatible unfolding, Eisenstein convergence, constant term. |
| B33 | Bounded coupling on one two-prime lattice — **RH** (Σ17). |
| B34 | "Bounded cone coupling ⇒ RH" as a pure implication — **sub**; excluding unattained width outright — **≥qRH**. |
| B35 | Zero–one law `κ ∈ {0, ∞}` (with the first rung it gives RH) — **sub**. |
| B36 | Zero-independent selection at the trivial gauge point — **RH** (Γ1). |
| B37 | Frobenius at infinity as an operator: Rosati positivity of the correspondence algebra, a conformal correspondence of factor `≠ 1`, or a Hecke similitude of the collided form — **RH** (Γ4, Γ19). |
| B38 | Unimodular gauges with `S_N/H_N → 1`; functional-equation twins without Euler product; prime-flip twins of density `0` or irregular density — **sub** (Γ12, Γ15). |

### S7. Realization and scattering
Routes: PM, RN, PTR, W1C.

Established [L]: regularized Gauss–Mayer operator (cutoff renormalization, nuclear of order 0, entire
Fredholm determinant, source holomorphy, word traces, `D = A + ζB`, `B(w,−1) = 0`, convergent raw
finite-branch determinants, exact finite part); real-`w` derivative cone, `B ≠ 0` for small real `λ`,
`D(w,−1) ≠ 0`, rank-one resolvent pole; primitive coding of hyperbolic `SL₂(ℤ)` classes by even Gauss
words, inverse classes and roots; resonant Eisenstein states with partner angle; algebraic
recentering of the critical parabola impossible; lossless realization needs infinitely many
resonances; normal real-zero approximants force RH (Vitali).

| | Obstacle |
|---|---|
| A24 | Mayer–Selberg identity: assemble primitive-geodesic multiplicities into the trace/product identity for `D(·, ±1)` and link the scattering determinant, so that ζ zeros in `½ < Re w < 1` are eigenvalue-`±1` events of `R(w)` (known mathematics, heavy formalization). |
| B39 | Off-line resonance exclusion (zero-selecting scattering rigidity) — **RH** (Σ8, Γ4). |
| B40 | A Hermitian (Lewis–Zagier / Krein) structure on eigenfunctions of `R(w)` near `Re w = 1`, scattering sector included, giving a zero-free region near `Re s = 1`; cone contraction cannot separate the cusp-form events on the line from scattering events just left of it — **sub**. |
| B41 | Source-faithful realization: prime-faithful lossless port (PTR), centred Ising limit (W1C), directed renewal sign (RN) — **RH** (Σ8). |

### Route-specific items
| | Obstacle | Routes |
|---|---|---|
| A25 | Theta Hankel rank-8 strictness; ranks 9 and 10 | TH |
| A26 | Explicit thresholds: Hausdorff shifts, Jensen degree horizons, two-grid fixed degrees | PA, LA, HCF |
| A27 | The nine atom-dominated moduli of the collar shift | ACT |
| A28 | Mixed Schur debit on fixed blocks; first-prime / coarse / polar costs on fixed cells | AIP, CHMD |
| A29 | Toeplitz minors of the Xi centre sequence beyond PF₃₇ | LA |
| B42 | Odd-sector bound `R ≤ ½` — **RH** (Σ7) | CHMD, TT |
| B43 | All-rank / all-degree theta, heat, Jensen, PF and two-grid signs — **RH** (Σ6) | TH, LA, HCF, PA, GTA |
| B44 | Lower bounds for scheduled prime energies — **RH** (Σ20) | FU, CFC, RP, SZ, LI, FEL, EGC |
| B45 | Pre-divisor forcing: a section or potential coupled to Ξ before the divisor — **RH** (Γ5) | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |

## 2. Live routes

### WL — Weil lag / prime lag
Established: critical-energy, linear prime-error and one-sided `√x log²x` criteria; genus slope ⇔ RH +
simple; `Count(a)` iff `a − 1 ∈ 𝒬`; Chebyshev–Stirling split; Landau-window cost `(2 log 2 − ε)mn`;
Adams threshold `2^{qr}`; `{2,3}` stencil `ψ ≤ 23x/20`; growing-alphabet producers at the main term.
- A: A18, A19.
- B: B30 (one-sided count, Π1); B29; joint Möbius-moment / Mertens / sawtooth payment at
  square-root precision (**RH**).

### RW — restricted Weil ground minimum
Established: `μ(A) ≥ 0 ∀A` ⇔ RH; floors through radius `181/500` and at `A₊`; the floor dies doubly
exponentially; near radical of dimension `≈ 2e^{2A}` at doubly-exponentially small energy; finite
divisor at every aperture; visibility law; companion forcing.
- A: A9, A3.
- B: B1 (all-aperture sign, **RH**); B27 (genus law, **sub**); B7 (clusters, **sub**); the
  depth-weighted branch needs an all-window mass bound (**≥qRH**).

### FU — Fourier/Abel prime scheduling
Established: completed Abel moment bounded above ⇒ RH; narrow-window negative prime channel.
- A: none.
- B: B44 (joint seed, drift, prior, cross-block and endpoint terms).

### CFC — first-clock sine coefficient
Established: RH ⇔ coefficient `≥ −C` on the aperture tail; unbounded below under ¬RH; phase-natural
transport is the identity.
- A: none.
- B: B44 (source lower bound retaining prime, archimedean and endpoint terms).

### RP — normalized prime history
Established: RH ⇔ history `≥ −B(K+2)` eventually; unconditionally below `−δ(K+2)` cofinally; finite
prime-clock density cancellation.
- A: none.
- B: B44 with high-LCM pairs, moving core and singular transport at linear scale.

### PA — prime–archimedean source passivity
Established: each fixed Hausdorff order positive at large shifts.
- A: A26.
- B: B43 (all-order / all-shift positivity).

### MC — Möbius cancellation
Established: half-power dictionaries; `Θ ≥ ½`, Haar-a.e. `½`; RH ⇔ trivial point typical; cyclotomic
remainder `≥ 0`; every positive-power band retains `2Θ`; prime-star nerve signed face count `= M(N)`;
Dirichlet inputs uniform for `q ≤ (log x)^A`.
- A: none beyond the Siegel–Walfisz range.
- B: B30 (moving-scale half-power cancellation, **RH**); B31 (**≥qRH**); head/leaf signed
  cancellation of finite prime clocks (Σ20); B36 (**RH**).

### TT — theta seam / Wold
Established: seam, tail and Wold receivers; `t < ½` threshold; truncated theta transform
`= −seed·B_N(ρ)` at zeros; two-horizon windowed aperture modes.
- A: none.
- B: B42 (all-test directed covariance or complete odd positivity).

### LA — Laguerre/Jensen and local heat
Established: every fixed Jensen degree eventually real-rooted; RH ⇔ every Xi Jensen polynomial splits;
a repeated root of a reversed section refutes RH; slice floor `133/200`; `λ_t log t → 0` ⇔ every
fixed-depth strip holds all high zeros; right-half depth moment `o(V)`; `μ(½) ≤ 33/200`.
- A: A26, A13, A29.
- B: B43 (all degrees / all heights); uniform tail narrowing (**≥qRH**); shrinking-scale and
  exceptional-height control (**sub**).

### TG — transgression / central gap
Established: winding/index and cubic-transgression identities; finite-matrix index laws along paths;
regularized deformation of every fixed-width spline horizon ⇔ RH; Kähler transport free; no free
Lefschetz operator.
- A: none.
- B: B15 (integer trace `< 1` on every disc); B8 (a source-driven noncrossing path).

### HF — Hodge / Hecke / complete cells
Established:
- S1 and S2 in full; Haar/prime-edge Gamma reserve; full Weil index `≤ R + A` for `R` coarse cells.
- Heat Hodge defect `N(t)/2`; renormalized Hodge sign ⇔ quadratic RR ⇔ scaling-surface Hodge;
  loop-Eisenstein band poles = Hodge defect.
- Packet identities; Frobenius at infinity ⇔ RH; correspondence algebra.
- Stars, gcd strata, nerve, links, conductor duality; the RR branch of S5.
- A: A1–A11; A21; A28.
- B: B1–B11; B26 (count-valued primitive `h¹`, **RH**) with B27 and B28 (**sub**); B37 (Hecke
  similitude, **RH**).

### CHMD — causal hyperbolic–modular duality
Established: RH ⇔ `R ≤ ½` on the odd sector; prime wave `O(e^{|u|/2})`; every Haar piece except the
first-prime coarse layer has uniform finite index; the Gamma graph pays the prime-two block; a growing
Euler head alone is unbounded; the full prime window cancels the head pole on fixed and growing
packets.
- A: A28.
- B: B12 (uniform coarse-size control, **≥qRH**); B42 (**RH**); B4.

### TH — theta Hankel ranks
Established: rank 7 strict; rank 8 PSD; `I₇(a) ≥ 0` on `0 < a < ½`; heated orthant signs at all
ranks; all-rank signed-center positivity ⇔ RH; Ritz velocity identity.
- A: A25.
- B: B43; rank-uniform signed flux payment.

### RN — renewal
Established: compact cone-positive renewal operator with exact regularized determinant.
- A: none.
- B: directed mixed prime + Gamma `≥` pole; real spectrum does not follow from cone positivity; native
  unregularized synthesis is a no-go (B41).

### WD — Ward / collision / heat
Established: S4 in full; integer-theta collision readings and Fredholm index; low-window
sectoriality; root-free stopping rule; unit-window increments; Hecke-defect hierarchy, half-gate and
density equivalence [S]; zero-coordinate-free finite-theta RH equivalence.
- A: A12–A17.
- B: B13–B25; vanishing global depth energy as `t ↓ 0` (**RH**); tower-branch index ceiling (B12).

### LI — guarded history zeros
Established: `Z_S` finite; RH ⇔ `Z_S = ∅`; under ¬RH the last zero has odd order.
- A: none.
- B: B44 (pay the outside budget at every guarded zero).

### SZ — Suzuki / Ward defect
Established: ¬RH ⇒ cofinally unbounded below; finite packet light-Gram identity; negative
finite-cutoff pairings of the Abel clock; the Xi Donoghue map fixes `i`, and under RH `i` is its only
upper periodic point.
- A: none.
- B: B44 (uniform lower bound after complete source assembly); no converse to the Donoghue
  falsification criterion.

### PM — physical / complete-energy realization
Established:
- Gauss–Mayer operator and determinant (S7), including real-`w` positivity and primitive coding.
- Resonant Eisenstein states: truncated norm `|Λ(ρ−1)|² Y^{1−Re ρ}/(1 − Re ρ)`; partner angle
  `cos² = 4Reρ(1 − Reρ)`, saturated iff critical.
- Complete-energy and gauge-mass receivers, half-damping admission, escape alternative.
- Reading [D]: with A24, ζ zeros in `½ < Re w < 1` are eigenvalue-`±1` events of `R(w)`; PM's
  selection wall is Frobenius at infinity in the form of partner saturation.
- A: A24.
- B: B39 (**RH**); B40 (**sub**); cofinal complete-energy bound as `ε ↓ 0` (**RH**); exterior
  tightness and exclusion of infinite-height escape (unattained width; **≥qRH** when excluded
  outright).

### JAS — joint ancestry
Established: positivity at growing logarithmic prime budget.
- A: none.
- B: square-root power budget (B30).

### CTF — completion transfer
Established: Euler completion error `≤ 1/(n+1)`; equal limits of full and finite-source energies.
- A: none.
- B: full-source energy decay by signed covariance cancellation (Π); `B X^ε` receiver in the inner
  cutoff (Π).

### HCF — two-grid Hankel
Established: both `log 2`/`log 3` grids with polar cancellation ⇔ RH; one grid aliases.
- A: A26.
- B: B43 (both grid signs at every degree and height).

### XN — Newton dynamics
Established: RH ⇔ ξ-Newton source margin on discs; nonnegative Laplacian of the margin.
- A: none.
- B: cover every zero with nonnegative margin (**RH**, Γ).

### BAG — Bagchi recurrence
Established: RH ⇔ disc recurrence on every closed disc of the strip; universality.
- A: none.
- B: B36 (returns near every right-strip point, possible zeros included).

### EWU — Euler weights
Established: RH ⇔ at every aperture some real weights make the full Weil functional nonnegative; the
obstruction dual is a blind test.
- A: A9.
- B: B1 (nonnegative actual minimum at every aperture).

### GTA — transverse charge
Established: transverse-charge decay criterion; positive charge and strong finite-prefix
convergence.
- A: none.
- B: B43 (rank-uniform arithmetic transverse-energy decay).

### OWU — odd Weil selectivity
Established: every `r > 27/50` has a smooth odd test on `[−r, r]` with `W_ζ > mass/25` and
`W_Liouville < −3 mass/10`; companion forcing and conductor horizon incompatible.
- A: A9 (odd tests slightly beyond `27/50`).
- B: B1 (all-test / all-aperture odd sign).

### PBM — pole-regularized prime series
Established: convergence at every `σ > ½` ⇔ RH.
- A: none.
- B: coefficient cancellation (B30).

### RB — Robin / Nicolas
Established: large counterexamples need growing prime cores; colossally abundant reduction.
- A: none.
- B: square-root remainder on primorials (B30).

### SRT — square-root threshold / zero visibility
Established: S1 in full; depth-gap visibility; local count ⇒ bounded critical multiplicity
(density-one heights); deep zeros `o(V)`; Steklov full index for `β > 2`; unit-window increments;
companion forcing.
- A: A1–A9.
- B: B1–B7; tower-branch index ceiling (B12, **≥qRH**); unattained-depth detection (Σ4).

### ACT — collar transport
Established: explicit collar threshold pays every modulus outside nine atom-dominated moduli.
- A: A27.
- B: one fixed shift paying every profile including exterior primes (B1).

### AIP — arithmetic incidence positivity
Established: S1 in full; complete form = prime jump energy + nonnegative affine incidence energy +
signed shell/boundary terms; all-aperture allocation receiver; full Weil index `≤ R + A`.
- A: A1, A2, A8, A28.
- B: all-aperture allocation (B1, **RH**); B2–B5.

### ACS — arithmetic Castelnuovo–Severi
Established:
- RH ⇔ effectivity ⇔ Hodge index ⇔ section count ⇔ Castelnuovo–Severi at rational scales.
- Universal floor law; RR on orbits ⇔ orientation; finite divisor at every degree; Hodge defect finite
  at every degree; near radical finite at every level.
- LST count classification (S5); correspondence algebra.
- Visibility law; finite-index constraint classification; curve coupling bounded ⇔ unitary;
  quantitative complete-cell transfer at rate `N^{−1/2}`; `𝔽₃` elliptic adelic chain.
- A: A20–A23; the S1 A-items.
- B: B26 (**RH**), B27 and B28 (**sub**); B37 (**RH**); census B32; B1–B6; B11.

### SC — Stokes/Witt–Krein / archimedean successor
Path: `φ_c(a, b) = ratCorr(|a|) − c|a|^{−½}|b|` → `κ(φ_c) < 3` → `κ = 0` → RH.

Established:
- `κ(φ_c) = κ + 1` at every place and for primitive Dirichlet L-functions; translation reading `1`;
  readings add; dilation form + shell squares on boost mass zero.
- Stable gluing; pole pair invisible to the boost index; carrier classification and unique
  proper-subgroup split; continuous-dilation carriers reading `1_H` exist iff `H ∈ {{0}, ℚ}`.
- Every `p`-adic neighbourhood and every two-free-prime lattice carries the full affine index.
- Coupling ≡ kernel; one lattice decides; cone; finite stratum ⇒ RH from single-lattice coupling.
- Heat-deformed state; Künneth branch all-or-nothing; coupled assemblies exact, separable blind.

Reading [D]: `K_ζ(u)` is the normalized smoothed prime error in a fixed-length multiplicative window;
bounded coupling is window PNT at square-root precision (Π4); at the critical overlap smooth-bump
packets realize ratCorr Grams (A7).
- A: A22; A14 (heat calibration); A7.
- B: independent `κ(φ_c) < 3`, i.e. B1 on the ratCorr Grams (**RH**); B6 (**RH**); B33 (**RH**); B34
  (**sub**); B15 on the heat branch (**RH**); B13 (**sub**); B12 for the Künneth square (**RH**); B8
  (**RH**).

## 3. Candidates and retired branch

| Candidate | Established | A (just work) | B (open) |
|---|---|---|---|
| APF | Fredholm index, cycle-trace reconstruction | — | zero-independent divisor exhaustion (B45) |
| BSH | framed curvature | — | pre-divisor section and mate identity coupled to Ξ zeros (B45) |
| CDC | calibrated confluence iff `Re s = ½` | — | source-defined potential forcing confluence (B45) |
| DR | cusp roots, finite monodromy | — | compatible roots on the strict-right domain; global monodromy (Γ) |
| EGC | pole-safe contour | — | outer expanding-contour sign; raw decay cannot beat the Gamma floor (B44) |
| EWJ | Euler/Wold jets | — | zero-independent source admission (B45) |
| FEL | theta likelihood; BSY integral = off-line zero sum | — | predeclared source balance (B44) |
| HJ | Hurwitz residual = SEC charge, vanishing iff criticality | — | pre-divisor forcing (B45) |
| IRK | rotation-algebra trace / winding | — | arithmetic Poisson / projective lift with integral count (B26-type) |
| MSC | Möbius–Sonin | — | bridge to nonnegative Sonin energy (B1) |
| PCS | singular co-shift | — | source-natural wall annihilation; shift ≠ dilation (B45) |
| PTR | lossless stacks, unit port gap | — | prime-faithful port; infinitely many resonances needed (B41) |
| RFHM | support grade; reversible sewing inverse-covariant | — | symmetry-breaking law (B45) |
| SEC | essential norm = seam jump | — | pre-divisor compactness at zeros (B45) |
| W1C | finite Lee–Yang + Ising receiver; Vitali obstruction | — | couplings converging to Riemann's measure (B41) |
| WBF | genealogy Gram | — | any arithmetic coupling (B45) |
| PW-B (retired) | zero-independent source family at every nonreal strip point; optical flux `−16(Re s − ½)Im s·M₊M₋`, vanishing iff critical | — | killed as a selector (fails at `3/4 + i`); survivor: the half-parameter cusp `Λ(s) = 0` receiver, which needs B39 (**RH**) |

## 4. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ, degree axis (positivity at every `K·c*` / every aperture; constant-factor wall at the critical scale) | RW, EWU, OWU, ACT, HF, SRT, AIP, ACS-atomic, SC (glued index), CHMD, TT; MSC, FEL |
| Σ, Hodge–Lefschetz / gluing across the coprime stratum | HF, ACS-Hodge, TG |
| Σ, heat / collision integer | WD (charge `< 2`), LA (heat), TG, SC-heat |
| Σ, rank / degree | TH, HCF, PA, GTA, LA (Jensen) |
| Σ, scheduled prime sums | FU, CFC, RP, SZ, LI; EGC |
| Σ, realization | RN, PTR, W1C, PM (Mayer resonances) |
| Π, count-valued primitive `h¹` | ACS-effectivity, HF-RR; IRK |
| Π, one-point precision | WL, MC, PBM, RB, JAS, CTF, SC (coupling = window PNT) |
| Π, conjugate diagonal / near-line density | WD (Hecke defect), census |
| Γ, selection / Frobenius at infinity | BAG, XN, PM (partner saturation), MC (typicality), ACS (Rosati), HF (Hecke similitude); APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF; PW-B (retired) |

Inside Σ the complete-family routes share one axis: the overlap multiple `K`, the radius
`½ log K` and the degree `a` are one coordinate. Below a small multiple of the critical overlap the
sign is proved by estimates (tilted spline to `(log N)^{1/9}`, logarithmic profile to `ε·c*`). From
the critical overlap on, residual and margin are of the same order and only an exact leading term
decides. At each degree the remaining problem is finite-dimensional (finite divisor), but it carries
`≈ 2e^{2a}` directions whose energy is doubly exponentially small and is signed only by zeros above
the Landau height `2πe^{2a}`. The sign has to come from an exact producer — a count (Riemann–Roch
with a count-valued primitive `h¹`) or a quantized integer — or from a structural selector. SC and WD
each carry a second, Π-type target: SC the window prime error read through the coupling, WD the
conjugate-diagonal Hecke defect, which is a near-line density ladder. PM's open core is Frobenius at
infinity as partner saturation.
