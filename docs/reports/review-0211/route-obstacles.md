# Route obstacles — status quo

Scope: the 33 live routes, the 16 candidates, the programmes ADT, AHD and CWS, and the support
lines, read against the Lean corpus at `9ff1dbfc9a` with the working tree. For every route: what is
established, how its open obligation reads in the window picture, the obstacles that are **(A) just
work**, and the obstacles that are **(B) open mathematics**. Just work means known mathematics,
finite or kernel-certified computation, effectivization, finishing or integrating a formalization,
or composition of proved statements. Open mathematics means a statement nobody knows how to prove.

Evidence: `[L]` integrated Lean; `[S]` Lean in the working tree or not wired into its umbrella;
`[P]` complete paper proof, Lean pending; `[D]` derived here from Lean statements, not formalized.

Strength of a B-item: **RH** equivalent to RH; **≥qRH** implies a zero-free half-plane and
Lindelöf; **LH** implies Lindelöf; **sub** strictly weaker or of unknown strength; **indep.** not
implied by RH and not known to imply it; **method** a missing tool, not a statement.

Wall labels Σ/Π/Γ refer to `walls-ledger.md`. Programme codes follow the frontier-map source
locator; further codes: ACPL = ArithmeticCouplingTheory, ACT-L = ArithmeticCriticalityTheory,
ADT = ArithmeticDegenerationTheory, AHD = ArithmeticHodgeTheoryOfDegenerations, AET/AE =
ArithmeticEffectivityTheory, AOG = ArithmeticOrientationGeometry, ART = ArithmeticResonanceTheory,
CSAR = CriticalScaleArithmeticRigidity, CWS = CohomologyOfWindowsOfSpecZ, EHT = EdgeHodgeTheory,
HWV = HodgeTheoryWithoutVarieties, LST = LatticeSectionTheory, RIT =
RenormalizedIntersectionTheory, SP = SelectivePositivityAndThresholdLaws.

## 0. The window picture (applies to every route)

A **window** of length `A` is the interval `[−A, 0]` of the scaling line; a window test is a real
`C²` function `H` supported there. Lengths: CWS uses the length `A`; LST, ACS and RW use the
half-width `a = A/2`.

| Fact | Anchor | Consequence for routes |
|---|---|---|
| RH ⇔ `Q(H) ≥ 0` on every window test of every length | CWS `riemannHypothesis_iff_windowForm_nonneg` [L] | every Weil-positivity route is a statement about windows |
| Locality: on length `A`, `Q = M_{⌊e^A⌋} + ½⟨c,H⟩² − ½⟨s,H⟩²`; weights agreeing on `n ≤ e^A` give the same functional | CWS `TheWindowDatum` [L] | a window sees finitely many prime powers, the Gamma factor and the pole plane |
| Signed folds: `Q = Ω(0)‖H‖² + J_∞(H) + Σ_{n≤e^A}(Λ(n)/√n)(½fold_n − sym_n) + ½⟨c,H⟩² − ½⟨s,H⟩²`; `sym_n = ½∫_{[−A,−log n]}(H + H(·+log n))²`; pole part `= 2Ĥ(0)Ĥ(1)` [D] | CWS `weilQuad_eq_signedFolds` [L] | the only negative arithmetic terms are the symmetric fold masses; the other negative terms are `Ω(0) < 0` and the odd pole square |
| Canonical class `k_A(u) = ψ_{1/2}(e^{−u}) + ψ_{1/2}(e^{A+u})`, mass `2∫_0^A ψ_{1/2}(e^t)dt`, degree `deg K_A = 2ψ_{1/2}(e^A) − Ω(0) ≈ 4e^{A/2}` | CWS `TheCanonicalClassOfAWindow` [L] | the prime cost of a window is a half-weighted Chebyshev profile at the distances to its two ends |
| Semiboundedness `Q ≥ −(deg K_A + 2A sinh²(A/2))‖H‖²` | CWS `weilQuad_ge_neg_windowFloor` [S] | maximal window negativity is `e^{A/2}·poly(A)` (exact pole product); this is the window avatar of the trivial strip [D] |
| Window index `ι(A)`: monotone, `0` for `A ≤ 3/5`, finite, `≤ ⌊1 + 2A·T(A/2)/π⌋`; `sup_A ι(A) = #` right zeros; RH ⇔ `ι(A) < 2` ∀A | CWS `TheWindowIndex` [L] | each window is a finite problem; RH is uniformity in `A` |
| Weil's form is negative only through the two pole values and frequencies `|τ| ≤ τ₀(a) = 4exp(10 + 2e^{4a})` | AHD `exists_weilQuad_ge_of_lowFrequency` [L] | each window's sign is a low-frequency, finite-band question |
| Stages: `A < log 2` purely archimedean; `log 2 ≤ A < log 3` exactly one fold `T₂` | CWS `TheFirstPrimeFold` [L]; LST `weilPair_eq_jumpCount_add_primeTwoGraph_of_le_log_three` [L] | the first unproved windows (`3/5 < A < log 2`) involve no prime |
| Known window positivity: all tests `A ≤ 3/5`; odd tests `A ≤ 0.724`; `cosh`-orthogonal smooth tests `A ≤ log 2 + 1/50`; prime-free jump count to `A ≤ 1/1000` | ACS `zeta_hodgeDefectAt_eq_zero`; LST `SinglePrimeWindowJumpGraphAndObstructions` [L] | the first prime is passed only on hyperplanes |
| Degeneration: bulk → Jordan count `J(1)#ℙ⁷(ℤ/m)`; untwisted horizon windows → `κQ(H)` past the critical curve, `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²` at it, for every regular profile | ADT; AHD `TheBulkDeterminesTheSecondOrderTerm` [L] | complete-family routes are Weil's window criterion plus a count |
| Twisted horizon windows (mean-zero periodic twist) are zero-blind and positive, coercive at `a log N/c⁸`; the conductor-two window has second order `(7J(2)/K)∫e^{−8y}H²`, `J(2) = 255J(1)`, no Weil term | AHD `TheTwistedHorizonLayerIs{ZeroBlind,Positive}` [L]; `TheAlternatingWindowCountsTheConductorTwoPoints` [S] | every negative direction of the horizon layer is an untwisted window |
| Pencil: `κQ(H) + c∫e^{−py}H² ≥ 0` once `c ≥ κ·windowFloor(A)`; the window index of the pencil is monotone in `K`, stabilizes at Weil's index, never exceeds the right-zero count | CWS `pencil_nonneg` [S]; AHD `TheWindowIndexCountsTheRightZeros` [L] | a fixed critical multiple pays all windows of bounded length; RH sits in `K → ∞` |
| Realizations: no finite-dimensional window realization; RH ⇔ an `ℓ²(zeros)` realization; a finite-rank realization of `K_ζ` forces infinitely many right zeros | CWS `WindowRealizations` [L]; RIT `TheWeilKernelHasNoFiniteRankRealization` [S] | a geometric producer must be a tower of unbounded rank |
| Window genus main term `2e^A` = Young conjugate of the zero density = theta count of `Spec ℤ` | CWS `TheWindowGenusIsAYoungConjugate` [S] | the tower rank is `≈ 2e^A` |
| Counts: Künneth RR on a window pays everything except `½Q(H)` (`h¹_K > 0`); windowed Tate law; one spectrally generic orbit on `ℤ[p^ℤq^ℤ]` decides RH by an `ℕ`-valued count height; golden and complex fakes have none | CWS [S]; AE `MultiplicativeScaleHeightsAndWindowCounts` [L] | the missing producer is a count for the primitive window `h¹` |
| Selection: windows of bounded length cannot select ζ (prime flips beyond `e^A`) | CWS `exists_flip_twin_of_window` [S] | selection must be a law in `A` |
| Index calibration: `κ = #` right zeros, even, RH ⇔ `κ < 2`; finite `κ` ⇒ `Θ < 1`; glued state `κ + 1` | AOG; AKG [L] | finite-index waypoints are ≥qRH |
| Edge logic: a statement proved without zero information holds on every datum sharing that information | EHT; ADT [L/D] | only an identity, a count or an integer with a structural bound crosses the edge |

## 1. Shared obstacle blocks

### S1. Complete Weil family across the critical overlap
Routes: HF, SRT, AIP, ACT, ACS-atomic, RW, EWU, OWU, MSC, FEL; SC through the rational Grams; CHMD
through the index; TT through the odd/Markov sector.

Established:
- Receivers [L]: window criterion; horizon criterion; single Beurling schedule `2L(log L)²`; every
  fixed `K·c*`; conductor Gram at every `2K(log N)^{1/8}`; unit-bump pole-hyperplane receiver at
  every positive-power rate.
- Degeneration [L]: Jordan limit, count law over every finite ring (same over `ℤ` and `𝔽_q[T]`),
  Hensel weight strings, scaling form `E_m(c) = J(m)c⁻⁷R_m(c/m)`, eventually idempotent monodromy,
  growing subthreshold block Jordan below `1/8`, bulk zero ledger positive and zero-blind.
- Second order [L]: for every profile with `s^βE₁(s) → J`, the critical-curve limit
  `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²`; pencil Gram matrices are limits of the complete family's Gram
  matrices; window index monotone in `K`, stabilizing at Weil's index, exhausting the right zeros,
  Shannon-bounded.
- Twisted layer [L]: zero-blind, positive at every resolution up to `O(N⁻²)`, coercive at
  `a log N/c⁸`, second order `≥ a/K`; conductor-two second order is the count `7J(2)/K` [S].
- Rough regime [L]: all vectors `α < 1/9`; below `1/8` the subthreshold block, mid-band (`α < 1/4`),
  polynomial-conductor complement with floor `c_orth log N/c⁷` and nonpositive subspaces of dimension
  `≤ ⌊N^θ⌋`; jet–pole cancellation of the coherent pole pair; near-Gram forms cost their divisor
  mean; prime-only band `√N < p ≤ N^θ` is diagonal plus rank `≤ 2`, floor `(1−θ)/4`.
- General profiles [L]: universal-rate positivity `a e^{−Bc}` on polynomial spans `θ < 1/1080` for
  `c ≤ b log log N`; subpolynomial spans with floor `(log N)^{−η}/4` up to a super-log-log clock;
  logarithmic profile positive to `ε₀·c*` with the budget sharp.

Research status: the complete family is decomposed into counts (bulk, twisted horizon windows) and
one non-count piece, the untwisted horizon windows, which is Weil's window form. Open: the
cross-terms between these pieces on the full space, and the sign of the window form.

| | Obstacle |
|---|---|
| A1 | Join at `1/8`: pay the band–far cross (Schur `O(c√log c)`) and the threshold block `e ≍ c` against the coercive subthreshold block, mid-band and polynomial complement. Risk: if the prefix–terminal remainder needs the shifted prime-pair correlation, it becomes B41. |
| A2 | Explicit horizons `N₀` for the `1/9` theorem, the logarithmic profile, the Beurling schedule, the horizon criterion and the window-index convergence. |
| A4 | Window phase diagram: sharpen the pencil floor (use the exact pole product `2Ĥ(0)Ĥ(1)` and the weight `e^{−(β+1)y}` instead of `1`), tabulate the lower bound `K*(A) ≥ βJ/(κ·windowFloor(A))`, and settle the equality case `K = K*`. |
| A5 | Twisted windows at every conductor: compute the second order of `c_m`- and character-twisted windows (the Möbius–Poisson structure of the conductor-two proof predicts the Jordan count at `m`); prove the untwisted–twisted cross-terms vanish at fixed twist; integrate the conductor-two module. |
| A6 | Integrate the `[S]` items: conductor-two window; CWS working-tree modules; finite-rank no-go; RVM completed divisor; terminal-support quadratic loss; Cayley-ladder receiver (LI); first-variation transfer (SZ); Poisson rigidity (Γ8). |
| A7 | Prime-successor comparison `½A_N(F) ≥ (1/64)[Σ_{Q<p≤N/16Q²} log p/p]·(nonconstant mass)` with the packet identity. |
| A26 | General profiles: extend polynomial spans past `θ = 1/1080` and the super-log-log clocks (constants and cutoff exponents). |
| B1 | Weil's sign on window tests of every length — **RH**; each fixed length **sub** and decidable (Σ1). |
| B2 | Tate decomposition of the complete family at the critical curve: full-space second-order limit (bulk ⊕ twisted ⊕ untwisted ⊕ mixed), uniformity in growing twists and conductors, horizon localization of negative directions — **sub** (Σ1j). |
| B3 | Positivity at one fixed critical multiple on windows of every length; contains dense off-line clusters of depth `≳ 1/log K` at every height — **sub** (Σ1k). |
| B4 | Joint shell–pole and non-arithmetic Gamma-graph payment on growing packets (confinement exponent `≤ 8`) — **sub** (Σ1c, Σ1g). |
| B5 | Conductors `√N < m ≤ N` (Elliott–Halberstam type); full-space positivity of general profiles past `log log N` — **sub** (Σ1d, Σ1e). |
| B6 | Exact sum-of-squares identity for Weil's dilation form on one two-prime lattice — **RH** (Σ18). |
| B7 | Cluster exclusion below the Landau height — **sub** (Π8). |
| B41 | Shifted prime-pair correlation for the prefix–terminal remainder (only if A1 needs it) — **sub**. |

### S2. The window object
Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT, HF, ACS, SRT; programme CWS.

Established:
- Window datum, locality, Euler-factor locality, window involution as an isometry, window
  criterion [L]; fold identity, canonical class and its Riesz degree [L]; stages, first-prime fold,
  signed folds [L]; semiboundedness and pencil [S]; window index with Shannon bound and exhaustion [L];
  window Frobenius at infinity: `(σ_AH)^(s) = e^{−(s−½)A}Ĥ(1−s)`, multiplier unitary exactly on
  `Re s = ½`, pair products invariant [S].
- LST [L]: `{∞,2}` identity through `log 3`:
  `W = (Ω(0) − √2 log 2)‖f‖² + J_∞ + (log 2/√2)∫(f − f(·+log 2))² + 2E² − 2O²`; coercivity on all tests to
  `A = 0.6`, odd tests to `0.724`, `cosh`-orthogonal tests to `log 2 + 1/50`.
- ACT-L [L]: variable-hub Schur squares and two-vertex `T₂`-stick elimination; the fully calibrated
  folded-Markov conductance fails pointwise past the plastic root `e^{−2a} + e^{−3a} = 1`
  (corner ceilings `8(√2−1)` at `a = ½ log 2`, `3(√3−1)` at `a = ½ log 3`, both `< 4`).
- SP [L]: exact `{∞,2}` trace through `½ log 3`; no semilocal positive carrier; ceiling
  `μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})`; finite prime sets cross zero by `2 log(|S|+2) + 11`.

Research status: each window is a finite-type object; the sign question at fixed length is
decidable in principle (finite band, finitely many folds, Shannon-bounded index). Payment must be
nonlocal: pointwise Markov calibration fails at both first prime thresholds.

| | Obstacle |
|---|---|
| A3 | Certified window positivity by stage: (i) all tests on prime-free windows `3/5 < A < log 2` — a statement about the Gamma factor only; (ii) the first-fold stage `log 2 ≤ A < log 3`; (iii) the stages `log 3, log 4, log 5`. Finite band below `τ₀`, finitely many folds, interval-certified Schur complements. |
| A11 | Prime-free windows as a count: a Poincaré inequality for the Lévy jump form on an interval past length `1/1000`, with the pole signs. |
| A25 | Classical calibration of window negativity: read the classical zero-free region and the zero-density theorems as window-form bounds (high-frequency and almost-all-heights improvements of the canonical-degree floor). |
| B37 | Window Markov capacity: on every window, the Lévy jumps and antisymmetric fold counts dominate `|Ω(0)|‖H‖² + Σ(Λ(n)/√n)sym_n + ½⟨s,H⟩²` — a nonlocal Poincaré inequality — **RH**; fixed length **sub** (Σ7). |
| B42 | A count for the symmetric fold masses: an identity expressing `(log 2/√2)sym₂` (then every `sym_n`) through cardinalities, jump counts and squares — **sub** at a fixed stage; uniform in the stages it is a face of B20/B37 — **RH** (Σ27). |
| B43 | Growth law of window negativity: a bound `Q ≥ −Ce^{θA}‖H‖²` with `θ < ½` on visible windows is a zero-free strip — **≥qRH** [D]; subexponential growth — **RH** (Σ28). |

### S3. Kähler package, stars and gluing
Routes: HF, ACS-Hodge, AIP, TG, SC, RW; MC through the gluing determinant.

Established [L]: Kähler package; stars with depth law `log d − C₀`; Metzler gauge on deep stars; gcd
stratification; graded energies = positive cone sums of top strata, top = Möbius-signed sums of
graded; closed-form monodromy; disconnected links; nerve `χ̃ = −M(N)`; Redheffer `det = M(N)`;
conductor ↔ star duality; no semilocal positive carrier; cyclic Hodge defect on a two-prime orbit.

| | Obstacle |
|---|---|
| A8 | Quantitative depth law `d₀(c)`; explicit star horizons; finite-`N` tabulation of the gcd strata. |
| A9 | Björner's theorem for the squarefree complex. |
| B8 | HL on the positive locus of the overlap flow — **RH** (Σ2). |
| B9 | Payment of the top coprime stratum — **RH** (Σ3a). |
| B10 | Cross-tower spectral gap through the archimedean channel — **method**; uniform version **RH** (Σ23, Σ25). |
| B11 | Band-pole noncancellation of `Λ(s)/Λ(s+1)` — **RH** (Σ19). |

### S4. Index and finite off-line support
Routes: HKT, AKLT, AID, SRT, CHMD, SC, RIT.

Established [L]: finite-index kernels = PD minus `κ` characters; `κ ≤ r` ⇔ translation-stable
constraints of dimension `≤ r`; finite defect at every degree; window index `ι(A)` finite and
exhausting; finite off-line support ⇒ zeros approach the line ⇒ LH; positive index of `K_ζ` infinite
whenever the right zeros are finite; index `≤ R + A` for `R` coarse cells; growing Euler heads
unbounded; all-detail prime–pole cancellation `O(exp(−√log Y/92160000))` in original Haar masses.

| | Obstacle |
|---|---|
| B12 | Arithmetic index ceiling uniform in resolution — **≥qRH** for `K_ζ`; **RH** for `K_ζ ⊠ K_ζ` (Σ4). |
| B13 | Exclusion of a finite nonzero index (zero–one law) — **sub**. |

### S5. Window energy, heat and the Hecke defect
Routes: WD, LA, TG, HCF, SC-heat, TH-heat; census; HEF.

Established [L]:
- Window integer: index = Wiener–Hopf index; index `0` ⇔ outer Szegő factorization; separation-free
  stabilization at `Θ(√m)` (unit) and `O(m log²(m + S))` (cumulative); 9-way door opener.
- Window energy: pair resolvent = Laplace transform of `|𝒵(t)|²`, abscissa = twice the maximal depth;
  cepstrum `S_k = (−ρ)^k(c/2)∫e^{−t/2}(I_{k−1} − I_{k+1})(ct)|𝒵(t)|²dt`, `(−1)^kS_k ≥ 0`; every analytic
  certificate = exact multiplier × Carathéodory factor; centered theta windows with `𝒵_N` a source
  contour integral; zero transfer `A_N → ξ` at `N² ≳ m + d log(1/r)`; log stage ⇔ `A/log|γ|`
  corridor; RH ⇔ certificate at every stage with prefix `Θ(√m + √(log m log S))`.
- Mollified log-mean: holomorphic moments with the mean square cannot beat Jensen's `½ log c`;
  exponential moments at all integers do not determine the log-mean (Heyde laws).
- Hecke defect: half-gate `c < ½`; density TFAE to `2/3`; rate `r < 1`; almost-all corridor
  `(1+ε) log log T/log T`; superharmonic no-go.
- Heat: `κ(φ_c^{(t)}) − 1 = N(t)/2`; slice floor `133/200`; flow floor `2/3 + ε`.

Research status: the window integer is decided by the growth of a windowed zero power sum; the time
variable `t` of `𝒵(t)` is the window length of S2 (both read `e^{(s−½)·length}`) [D]. WD's analytic
block needs the mollified log-mean to `o(1)`, which no moment data supply.

| | Obstacle |
|---|---|
| A10 | Polynomial-stage certificate as one statement; computable stopping prefix with certified intervals; flow threshold `Λ_X` from sub-Weyl profiles; `ΔO = o(log T)` ⇒ density one ⇒ Lindelöf as one statement. |
| B14 | Heat: subcritical count (**sub**); pointwise horizon `< ½` (**≥qRH**); `O(T) = o(N(T))` (**sub**); `ΔO = o(log T)` (**LH**). |
| B15 | Subexponential window energy on every unit window: log stage **≥qRH**, polynomial stage **RH** (Π17). |
| B16 | Log-free near-line density `#{ρ ∈ [V,2V] : depth ≥ A/log V} ≤ ε(A)V` — **sub**. |
| B17 | Near-line density at rate `r ≥ 1`; critical-scale clustering — **sub** (Π5). |
| B18 | Hecke defect pointwise `O(1)` (**≥qRH**); doubly-log scale (**sub**); one dyadic constant (**RH**). |
| B19 | An arithmetic input beyond counts and the linear explicit formula — **method**. |
| B44 | Mollified log-mean `E log|ζM(½ + b/log T + it)| = o(1)`: needs distributional input (a rate in a Selberg-type limit law), not moments — **sub** (Π19). |

### S6. Counts, producers and Riemann–Roch
Routes: WL, MC, PBM, RB, JAS, CTF, ACS-effectivity, HF-RR, RW; census.

Established [L]: one-sided count ⇔ RH; multivariate parity producers reach `(1+ε)x + C_ε log²x`;
every individual producer has slope `> 1`; integer-Chebyshev ceiling; Redheffer `det = M(N)`,
`Ω±(√N)`; theta `h⁰` with RR; Künneth RR; count classification (bidegree, fixed rank, definite,
Siegel excluded; `m² + 64n²` and `ℤ ⊕ yℤ` fakes); isotropic count `ζ²`; boost transform; Hecke
similitudes of primitive `h¹`; Lévy jump count to window length `1/1000`; Stepanov over `𝔽_q`;
windowed Tate law; two-prime `ℕ`-count criterion for one generic orbit; Künneth counts on a window
pay all but `½Q` [S]; census `0.6725`; positivity-only certificates cannot reach `3/4` (best bound in
`[1/18 + 47/750, 8/27]`).

| | Obstacle |
|---|---|
| A12 | Künneth primitive `h¹` on the finite divisor at small degree. |
| A13 | Same-order mixed-jet recovery for `≥ 3` primes; explicit main-term producer. |
| A14 | Census: `S_cos(λ)` for `λ ≤ 1`; odd stabilizer; stabilizer at `β = 2`. |
| A15 | Voronoi summation; Zwegers' indefinite theta series. |
| B20 | Count-valued primitive `h¹` past the prime-free window — equivalently a naive height at bounded distance from the window Rosati form, or an `ℕ`-valued count height on one generic two-prime orbit — **RH**; at one fixed length **sub** (Π11h, Γ19). |
| B21 | Genus law `g ≤ (2 + η)e^A` — **indep.** (Π16). |
| B22 | Logarithmic Serre duality for the split surface — **sub** (Π11f). |
| B23 | `ε`-uniform producer: zero-free-region error **sub**; square-root error **RH** (Π3). |
| B24 | Unconditional square-root source input; half-power Redheffer determinant — **RH** (Π1, Π2). |
| B25 | Near-band cyclotomic energy `O(N^{3/2+ε})` — **≥qRH** (Π10). |
| B26 | Signed prime-pair information beyond bandwidth one (positivity alone is insufficient) — **sub** (Π7). |
| B27 | First Epstein real zero on the boost line `0 < |u| ≤ 1` — **sub**. |

### S7. Carriers, coupling, natural cone and selection
Routes: SC, ACS, HF; Γ-candidates.

Established [L]: coupling calculus; bounded dense coupling ⇔ RH; for every fixed Gaussian damping
`exp(τ(ρ−½)²)`, natural-cone coupling of rate `σ` ⇔ width `≤ σ`, hence bounded damped `ℕ²` coupling ⇔
RH with no attainment assumption; undamped cone: RH or polynomial repulsion from maximal width; exact
spline divisors with the full Riemann–von Mangoldt count, unattained positive width and bounded
undamped coupling [S]; carrier classification; every `p`-adic neighbourhood and every two-free-prime
lattice carry the full affine index; prime-set flips separated at every density; complete
degeneration and harmonic saturation select ζ; correspondence algebra with Tate's limit law;
degree-three and degree-two FE fakes; bounded windows cannot select [S].

| | Obstacle |
|---|---|
| A16 | `𝔽_q(X)` calibration: second order over `𝔽_q(T)`, window cohomology of curves at second order, local walls at higher-degree places, `𝔽₃` elliptic loop chain. |
| A19 | Prime-side form of the Gaussian-damped coupling (heat-smoothed explicit formula on the cone) as an identity. |
| B28 | Bounded coupling on one dense two-prime lattice; glued index `≤ 1` — **RH** (Σ17). |
| B29 | Bounded Gaussian-damped coupling on one natural two-prime cone from the prime side — **RH** (Σ17); density-only selection on the undamped cone is refuted (Γ21). |
| B30 | Finite-sieve Hodge positivity → global inter-tower form — **RH**. |
| B31 | Zero-independent selection at the trivial gauge point — **RH** (Γ1). |
| B32 | Frobenius at infinity as an operator (Rosati positivity / naive height; Hecke similitude; partner saturation; a positivity whose symmetry is the window involution) — **RH** (Γ4, Γ19). |
| B33 | Euler-product FE twins; unimodular gauges with `S_N/H_N → 1` — **sub** (Γ12, Γ15). |

### S8. Realization and scattering
Routes: PM, RN, PTR, W1C.

Established [L]: regularized Gauss–Mayer operator, entire Fredholm determinant `D = A + ζB`;
determinant = Euler product over genuine periodic modular geodesics; scattering divisor of the
constant-input inverse = ζ's divisor; signed channels; Epstein/Eisenstein identification and
continuation; scattering core of finite positive energy at every strip zero, with Mellin transform
`Γ(u/2)Γ((w−u)/2)Γ(w/2)⁻¹ζ(u)ζ(w−u)` and endpoint moments `ζ′(w)` at zeros; boundary `2ζ(s)/ζ(s+1)` with
slope weights `(1 − 1/n)Λ(n) ≥ 0` and the classical zero-free region; Cauchy averaging: norm = central
Gamma multiplier, strict contraction at all heights iff `Re w ≥ 1`, spectrum = Gamma curve ∪ {0}, no
point spectrum; signed Mayer solutions satisfy the Lewis three-term relation and continue to
`Re z > −1`; contractive scattering (Schur) positivity is blind to zero position (Blaschke pairs insert
zeros anywhere in the half-plane preserving every such inequality); rational/algebraic recentering
classified; lossless realization needs infinitely many resonances.

| | Obstacle |
|---|---|
| A17 | Classical identifications: `D(w,1)D(w,−1)` against `Z_Selberg(w/2)`; scattering constant term into `Re(2s) < 1`; Lax–Phillips for `PSL₂(ℤ)\ℍ`; Lewis–Zagier separation of cusp-form events at `Re w = 1`. |
| A18 | Operator-native nonvanishing on `Re w = 1` (risk: reduces to the Euler product). |
| B34 | A structure placing the resonances of `SL₂(ℤ)\ℍ` on `Re s = 1/4` — it must use the reflection `ρ ↔ 1 − ρ̄`, since contractive positivity is blind — **RH**; a separated scattering-sector gap — **≥qRH** (Σ19, Γ22). |
| B35 | Source-specific energy/charge control excluding off-line poles with `2ζ(w−1)/(w−1)` retained; escape — **sub / ≥qRH**; cofinal complete-energy bounds — **RH**. |
| B36 | Source-faithful realization; a finite-rank one is impossible, so a tower of unbounded rank — **RH** (Σ8). |

### Route-specific items
| | Obstacle | Routes |
|---|---|---|
| A20 | Theta Hankel rank-8 strictness; ranks 9–10 | TH |
| A21 | Hausdorff shifts, Jensen degree horizons, two-grid degrees, Toeplitz minors beyond PF₃₇ | PA, LA, HCF |
| A22 | Nine atom-dominated collar moduli | ACT |
| A23 | Mixed Schur debit; first-prime / coarse / polar costs on fixed cells | AIP, CHMD |
| A24 | Logarithmic two-point Chowla (Tao) | MC |
| B38 | All-rank / all-degree signs; Laguerre–Pólya property of `ξ(½ + z)` — **RH** (Σ6, Σ26) | TH, LA, HCF, PA, GTA; ART |
| B39 | Lower bounds for scheduled prime energies — **RH** (Σ20) | FU, CFC, RP, SZ, LI, FEL, EGC |
| B40 | Pre-divisor forcing — **RH** (Γ5) | APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |

## 2. Programmes

### ADT and AHD — degenerations
Thesis: the complete Weil family is a degenerating family along the resolution axis.

Established [L]: first order = Jordan count `#ℙ⁷(ℤ/m)` (the same law over every finite ring);
monodromy; Redheffer gluing; graded/top Möbius pair; complete degeneration selects `Λ`; second order
for every regular profile; pencil Gram limits and window index law; twisted layer zero-blind,
positive and coercive; conductor-two second order = conductor-two count [S].

Research status: the degeneration is a weight decomposition. Its Tate pieces — bulk packets and
twisted horizon windows — are point counts of projective space over residue rings and carry no zero;
its single non-Tate piece is the untwisted horizon window, which is Weil's window form. The
degeneration locates `H¹`; it does not orient it.

| | Obstacle |
|---|---|
| A4, A5 | Phase diagram; twisted windows at every conductor; cross-terms at fixed twist. |
| A16 | Second order over `𝔽_q(T)`. |
| B2 | Tate decomposition on the full space — **sub**. |
| B1 | Weil's window sign — **RH**. |

### CWS — cohomology of windows of `Spec ℤ`
Thesis: a window of length `A` is the finite object that should carry an `h¹` equal to Weil's window
form, nonnegative because it is a dimension or a count.

Established: window datum and locality [L]; canonical class `ψ_{1/2}`-profile with Riesz degree [L];
stages and signed folds [L]; semiboundedness by the canonical degree and the second-order pencil [S];
window Frobenius at infinity [S]; realizations (RH ⇔ `ℓ²(zeros)` realization; none finite-dimensional)
[L]; window index [L]; window genus `2e^A` as a Young conjugate and theta count [S]; windowed naive
heights and Tate law [S]; window cohomology of a curve (finite saturating genus; golden fake has
none) [S]; selection battery [S]; Künneth form of the window `h¹` [S].

Research status: every structural axiom of a cohomology theory holds for the window datum and for
every weight on the prime powers; the content left is a construction of the `h¹` that does not use
the zeros, at every length, by a tower of unbounded rank.

| | Obstacle |
|---|---|
| A3, A11 | Certified stages; prime-free count. |
| A6 | Integration of the working-tree modules. |
| B42 | Count for the symmetric fold masses, starting with `T₂` — **sub** at a stage. |
| B20, B37 | Count / capacity uniform in `A` — **RH**. |

## 3. Live routes

### WL — Weil lag / prime lag
Established: critical-energy, linear prime-error and one-sided `√x log²x` criteria; genus slope;
Chebyshev–Stirling split; Landau-window cost `(2 log 2 − ε)mn`; Adams threshold `2^{qr}`; `{2,3}`
stencil `ψ ≤ 23x/20`; multivariate parity producers at the main term.
Window reading: the one-sided count is the cumulative form of the canonical class
(`deg k_A = 2∫_0^A ψ_{1/2}(e^t)dt`).
- A: A13. B: B24; B23; joint Möbius-moment/Mertens/sawtooth payment at square-root precision (**RH**).

### RW — restricted Weil ground minimum
Established: `μ(A) ≥ 0 ∀A` ⇔ RH; floors through half-width `181/500`; exact `{∞,2}` trace through
`½ log 3`; window signed folds; ceiling; near radical; finite divisor; visibility; the fully
calibrated folded-Markov payment fails pointwise at `½ log 2` and `½ log 3`; Schur-square payment
survives.
Window reading: RW is the window sign by stages; its next test is the first-fold stage, where the
only negative arithmetic term is `sym₂`.
- A: A3, A11, A25. B: B1, B37, B42, B7; depth-weighted all-window mass bound (**≥qRH**).

### FU, CFC, RP, LI, SZ — scheduled prime sums
Established: exact receivers (completed Abel moment; first-clock tail; linear history floor; guarded
zero set `Z_S` finite with RH ⇔ `Z_S = ∅`; rectangular Ward defect); cofinal unboundedness under ¬RH;
LI Cayley-ladder receiver [S]; SZ first-variation transfer [S].
- A: A6. B: B39 for each.

### PA — prime–archimedean source passivity
Established: each fixed Hausdorff order positive at large shifts.
- A: A21. B: B38.

### MC — Möbius cancellation
Established: half-power dictionaries; `Θ ≥ ½`, Haar-a.e. `½`; RH ⇔ trivial point typical; every
positive-power band retains `2Θ`; Redheffer `det R_N = M(N)` = nerve Euler characteristic, `Ω±(√N)`;
coprimality signature; finite-clock leaf squares paid.
- A: A9, A24. B: B24; B25; head/leaf signed cancellation (Σ20); B31.

### TT — theta seam / Wold
Established: seam, tail and Wold receivers; Φ-Doob identities; every individual `Θ`-translate with
`|b| < ½ log 2` lies in the radical of the pole-completed CHMD pairing.
- A: none. B: B37.

### LA — Laguerre/Jensen and local heat
Established: every fixed Jensen degree eventually real-rooted; slice floor `133/200`; right-half depth
moment `o(V)`; PF₃₇ at the centre.
- A: A21, A10. B: B38; uniform tail narrowing (**≥qRH**); exceptional heights (**sub**).

### TG — transgression / central gap
Established: winding/index and cubic-transgression identities; finite-matrix index laws along paths;
Kähler transport free; window integer decided by the window energy.
- A: none. B: B15; B8.

### HF — Hodge / Hecke / complete cells
Established: S1, S2 and S3 in full; the ADT/AHD dictionary (counts plus one Weil piece); window index
law; complete-cell index `≤ R + A`; band poles = Hodge defect; cyclic Hodge defect; packet identities;
Frobenius at infinity ⇔ RH; correspondence algebra with Tate's limit law; the RR branch of S6;
no finite-rank realization of `K_ζ` [S].
Research status: HF's sign problem is the window sign; its structural question is the Tate
decomposition on the full space; whole-space positivity stands at `1/9` with three coercive pieces
below `1/8`.
- A: A1–A9, A11, A12, A25, A26. B: B1–B11, B20, B22, B32, B37, B42.

### CHMD — causal hyperbolic–modular duality
Established: RH ⇔ `R ≤ ½` on the odd sector; Markov form and sinh capacity; Haar pieces with uniform
finite index except the first-prime coarse layer; all-detail prime–pole cancellation with the
normalized prime matrix approaching one separable pole channel.
Research status: the `√Y` normalization gives no unnormalized vanishing error and no index ceiling.
- A: A23. B: B12; B37; B4.

### TH — theta Hankel ranks
Established: rank 7 strict; rank 8 PSD; all-rank signed-center positivity ⇔ RH; native tails =
Gram-square mass minus signed local flux.
- A: A20. B: B38; rank-uniform signed flux payment (**RH**).

### RN — renewal
Established: compact cone-positive renewal operator with exact determinant and resonances.
- A: none. B: directed mixed prime + Gamma `≥` pole (**RH**); B36.

### WD — Ward / collision / window energy
Established: S5 in full.
Research status: the window integer is a growth bound on `|𝒵(t)|²`; the analytic block needs the
mollified log-mean, which moment data cannot fix.
- A: A10. B: B15, B16, B17, B18, B14, B19, B44; B12 (tower branch).

### JAS, CTF, PBM, RB — one-sided count
Established: JAS positivity at growing logarithmic budget; CTF completion identities and Euler
completion error `≤ 1/(n+1)`; PBM convergence at every `σ > ½` ⇔ RH; RB colossally abundant reduction.
- A: none. B: B24.

### HCF, XN, BAG, EWU, GTA, OWU
- HCF: two-grid criterion; one grid aliases. A: A21. B: B38.
- XN: Newton-disc criterion; nonnegative Laplacian of the margin. B: covering with nonnegative margin
  (**RH**).
- BAG: disc recurrence ⇔ RH; weak ladders collapse. B: B31.
- EWU: weight rigidity; attained aperture-antitone blind minima. A: A3. B: B1.
- GTA: transverse-charge criterion; positive charge and finite-prefix convergence. B: B38.
- OWU: odd floor through half-width `181/500`; Liouville-twist separation; companion forcing and
  conductor horizon incompatible. A: A3. B: B1 (odd sector), B37.

### SRT, ACT, AIP — complete atomic matrix
- SRT: S1 in full; horizon criterion; window-pencil index exhausts the distinct right zeros;
  conductor-two second-order law [S]. A: A1–A7. B: B1–B7; B12.
- ACT: collar thresholds pay every modulus outside nine; single-shift receiver. A: A22. B: B1.
- AIP: complete form = jump + incidence − shell + boundary; prime incidence defects have an exact
  harmonic diagonal; large prime conductors have disjoint horizon spikes and a logarithmic defect gap.
  A: A1, A2, A7, A23. B: B1–B5.

### ACS — arithmetic Castelnuovo–Severi
Established: RH ⇔ effectivity ⇔ Hodge index ⇔ section count ⇔ Castelnuovo–Severi at rational
scales; finite divisor; near radical and genus function (main term `2e^A`); isolated-pair edge; LST
counts; correspondence algebra with naive-height criterion; windowed Tate law and two-prime
`ℕ`-count criterion; FE fakes; Epstein fakes; natural-cone models with RvM density.
Research status: flooring a nonnegative form assumes its sign; the producer is an independent count.
- A: A11, A12, A14–A16. B: B20, B22, B21 (**indep.**), B32, B26, B27, B42, B1–B6, B11.

### SC — Stokes/Witt–Krein / archimedean successor
Path: `φ_c(a,b) = ratCorr(|a|) − c|a|^{−½}|b|` → `κ(φ_c) < 3` → `κ = 0` → RH; or bounded
Gaussian-damped two-prime coupling → RH.
Established: `κ(φ_c) = κ + 1` at every place; carrier classification; two-prime lattices carry the full
affine index; coupling ≡ kernel; Gaussian-damped cone ⇔ RH; RvM-density countermodels for the undamped
cone [S]; every finite rational Gram is a limit of complete-matrix compressions on the Beurling
schedule.
- A: A16, A19, A6. B: B1, B6, B12–B14, B28–B30, B8.

### PM — physical / complete-energy realization (Gauss–Mayer)
Established: S8 in full.
Research status: PM has a faithful divisor and every positivity of contractive type; such positivity
localizes zeros to half-planes only. The structure it lacks is the reflection `ρ ↔ 1 − ρ̄` acting as
a positivity — the window Frobenius at infinity in scattering form.
- A: A17, A18. B: B34, B35.

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
| IRK | rotation-algebra trace / winding | — | arithmetic projective lift with integral count (B20-type) |
| MSC | Möbius–Sonin; strict-right divisor preservation | — | bridge to nonnegative Sonin energy (B1) |
| PCS | singular co-shift | — | source-natural wall annihilation (B40) |
| PTR | lossless stacks, unit port gap | — | prime-faithful port (B36) |
| RFHM | support grade | — | symmetry-breaking law (B40) |
| SEC | essential norm = seam jump | — | pre-divisor compactness at zeros (B40) |
| W1C | finite Lee–Yang + Ising receiver; PM's faithful divisor; contractive scattering blind | — | couplings converging to Riemann's measure, or a positive/self-adjoint realization of the faithful divisor (B36, B34) |
| WBF | genealogy Gram | — | any arithmetic coupling (B40) |
| PW-B (retired) | optical flux vanishing iff critical | — | survivor = half-parameter cusp receiver, which needs B34 (**RH**) |

Support lines (not routes): ADT, AHD, CWS (Section 2); ART (centered approximation; survivor lands in
B38); ARGON-3 directions B (period rigidity) and C (two-place Krein); HTGeometry `AffineExpanders`;
the paused classical-formalization programme (Lax–Phillips, Voronoi, Zwegers, Björner, logarithmic
Chowla).

## 5. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ, window sign (horizon layer; every `K·c*`; Beurling schedule; window capacity; symmetric fold masses) | RW, EWU, OWU, ACT, HF, SRT, AIP, ACS-atomic, SC, CHMD, TT; MSC, FEL; ADT/AHD/CWS |
| Σ, Hodge–Lefschetz / top coprime stratum | HF, ACS-Hodge, TG |
| Σ, rank / degree (Laguerre–Pólya) | TH, HCF, PA, GTA, LA; ART |
| Σ, scheduled prime sums | FU, CFC, RP, SZ, LI; EGC |
| Σ, realization (tower of unbounded rank) / resonance placement | RN, PTR, W1C, PM |
| Π, window energy, near-line density, mollified log-mean | WD, TG, LA (heat), SC-heat, census |
| Π, count-valued primitive `h¹` / naive height / count for `sym_n` | ACS-effectivity, HF-RR, IRK; CWS |
| Π, one-point precision (incl. the Redheffer determinant, damped coupling) | WL, MC, PBM, RB, JAS, CTF, SC |
| Π, conjugate diagonal | WD (Hecke defect), census |
| Γ, Frobenius at infinity / `Λ(s)/Λ(s+1)` / law in `A` | PM, HF, ACS, BAG, XN, MC; APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF |
