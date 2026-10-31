# Route obstacles — status quo

Scope: the 32 live routes, 17 standalone candidates and the PW-B branch of the frontier map, checked
against the Lean corpus. For every route: what is established, the obstacles that are **(A) just
work** (known mathematics, finite computation, effectivisation, bookkeeping), and the obstacles that
are **(B) open mathematics** (no known solution).

Legend. `[L]` theorem in the Lean corpus (statement read). `[map]` status from the frontier map
without a Lean statement read here. Strength of a B-item: **RH** = equivalent to RH; **≥qRH** =
implies a zero-free half-plane `Re s > ½ + α` (quasi-RH) and Lindelöf; **sub** = strictly weaker
than RH or of unknown strength. Wall labels Σ/Π/Γ refer to `walls-ledger.md`.

## 0. Hardness calibration (applies to every route)

| Fact | Anchor | Consequence for routes |
|---|---|---|
| `κ(K_ζ) = #` right zeros, already on any two-prime sublattice; RH ⇔ `κ = 0` ⇔ `κ ≤ 1` | HKT `TheFiniteIndexStratumOfZetaIsLindelofDeep` [L] | every route that ends in an index count ends in the same integer |
| `κ < ∞` ⇔ finitely many off-line zeros ⇔ bounded heat counts ⇒ Lindelöf + zero-free half-plane | same [L] | every **finite-index / finite-support waypoint is ≥qRH** |
| Fixed aperture, fixed rank, fixed overlap `c` are never RH-complete; RH-complete thresholds: tilted spline `c = (log N)^α, α > ¼`; smooth profiles `(log N)^ε`; Gevrey-2 `(log log N)^{α>2}`; Steklov/sinc `L(log L)²`, `L = log log N` | CACT, SSHA `TheCriticalExponent`, `TheGevreyProfile` [L] | fixed-resolution positivity is always **sub** |
| One-sided count `ψ(x) − x ≤ C√x log²x` ⇔ RH; section supply beating the large-sieve ceiling at rate `e^{2βr}` ⇔ zero width `≤ β` | ACP `TheStepanovCountIsTheSign`, SPTL `SerreDualScalingCohomology…` [L] | every **exponent improvement on the count side is quasi-RH** |
| The Krein index is twin-blind (`κ(k·χ) = κ(k)`) | AKG `TheIndexIsTwinBlind` [L] | index calculus alone can never select ζ; selection must use dilation data (pole, Gamma) |
| Heat: an off-line pair of depth `δ` survives to `κ = tL ≈ δ`; size-only reality horizon `≥ ½`; Weyl floor `2/3 = 4μ(½)` | Heat `AnOffLinePairSurvives…`, `KiKimLeeTwoThirdsHorizon` [L] | pointwise heat horizons below `½` are ≈ zero-width statements (**≥qRH**) |

## 1. Shared obstacle blocks

Most routes share one of five engines. Their obstacles are listed once here and referenced below.

### S1. Complete Weil matrix at growing overlap (HF, SRT, AIP, CHMD, ACS-atomic, SC, RW, EWU, OWU, ACT)

Established [L]:
- fixed `c`, all vectors: logarithmic reserve `(a/c⁷)(D_N − C log(2c)‖x‖²) ≤ W`, horizon eventual in `c` (CACT `ShiftingThePrimeEnergyGivesALogarithmicDefectReserve`);
- explicit polynomial-cost reserve at every `N ≥ cutoff(c)` (CACT `TheCompleteWeilReserveHasPolynomialOverlapCost`);
- fixed conductor packets positive for `1 ≤ c ≤ (log log N)^A` (every `A`) and for `c ≤ (log N)^A`, `A < 1/48` (CACT `FixedConductorPacketsStayPositiveAtGrowingOverlap`); `α < 1/19` on fixed packets (SSH) [map];
- complete signed residual uniform in conductor: `‖(W − E_m)v_m‖² ≤ K m⁴(c⁵/log N + c¹⁰(log N/N)² + c³/√log N)` for all `m ≤ (log N)^A` (CACT `CompleteConductorResidualsAreUniformOnLogarithmicFamilies`); downward rows `≤ C m⁴c⁵/log N` (CACT `DownwardRowsHaveUniformConductorBounds`);
- joint top-band shell–pole cancellation; growing Euler head alone has unbounded index; the full prime window cancels the `√Y` head pole on fixed packets (SSH, AID) [L].

Reach accounting (inference from the exponents above): a residual term `c^a/(log N)^b` against the
floor `E_1(c)² ≍ c⁻¹⁴` allows `c ≤ (log N)^{b/(a+14)}`. The `c⁵/log N` term gives `1/19` (the SSH
exponent), the `c³/√log N` term `1/34`. The RH-complete schedule `α > ¼` needs `b > (a+14)/4`.

| | Obstacle |
|---|---|
| A1 | Effective horizon for the fixed-`c` logarithmic reserve (any explicit `N₀(c)`) |
| A2 | All-vector positivity at iterated-log overlap: combine A1 with the uniform residual range `m ≤ (log N)^A` |
| A3 | Attribute each of the eight residual terms to its source (prime sum vs. horizon/top band); replace prime-sum errors by classical zero-free-region errors |
| A4 | Growing-packet relative remainder for the full-window head-pole cancellation, packets up to `exp(c√log Y)` (window PNT with de la Vallée Poussin error) |
| A5 | Single-`K` completeness of the Steklov/sinc schedule at the critical scale `K L(log L)²` |
| B1 | Positivity on an RH-complete schedule — **RH** (Σ1) |
| B2 | Horizon exponent `K < 4` in `N ≥ exp(c^K)` for the log reserve, or residual saving `b > (a+14)/4`; under ¬RH at least one fails — one of them carries the RH content (**open which**) |
| B3 | Conductor uniformity beyond the Siegel–Walfisz range `m ≤ (log N)^A` — **sub**, Π9 |

### S2. Index / finite off-line support (HKT, AKLT, AID, SRT towers, CHMD index branch)

Established [L]: index = right-zero count; finite stratum TFAE; converse Krein–Langer for orbit
kernels; complete cells capture every finite index; transverse energy pays each negative square;
source work `≤ 2` cofinally ⇒ RH (AID `TheSourceWorkHasAClosedQuantumThreshold`).

| | Obstacle |
|---|---|
| A6 | Effective capture stage: the complete-cell matrices capture every finite Weil index (AID `TheCompleteCellsCaptureEveryFiniteIndex`) without an explicit stage; make the stage explicit in terms of the zero packet |
| B4 | Any arithmetic index ceiling uniform in resolution — **≥qRH** (Σ5) |
| B5 | General converse Krein–Langer for kernels not presented by a zero configuration — **sub** |

### S3. Heat flow / collision charge (WD, LA, TH, TT, HCF, HEF receivers)

Established [L]: `E(t)` monotone with dissipation `E(b) + 2∫N ≤ E(a)`; energy majorization for
`8St < 1`; local threshold `λ_t ≍ depth²/local count`, `{λ_t > 0}` null ⇔ RH, `{λ_t > κ/log U}` has
measure `o(U)`, `λ_t = 0` on lower density `29/50`; heat pincer `δ²/200 ≤ λ log ≤ 67/100`; reality
horizon `2πe^{(2/3+ε)/t}` and nonreal count `≤ C₀R log R`; deep copies in `[X,2X]` `≤ C log X·N(t)` at
`t log X ≤ c`; growth ladder: `N(t) ≤ exp(At^{−a})` ⇒ `X^{o(1)}` deep counts for `a < ¼` (log⁴
persistence) [L], for `a < 1` with inverse-log persistence [map]; collision charge `O ∈ 2ℕ`, RH ⇔ `O < 2` on every window; Gauss–Hodge prime current summable
⇔ `O = 0`; theta-prefix readings converge and round to `O`.

| | Obstacle |
|---|---|
| A7 | Lower the Weyl floor `2/3 = 4μ(½)` by formalising a stronger subconvexity exponent (calibration only) |
| A8 | Effective rounding rate of theta-prefix collision readings on a fixed window (Gaussian tail errors are explicit) |
| B6 | Subcritical heat count `a < 1` — **sub**, stronger than the density hypothesis |
| B7 | Pointwise horizon constant `< ½` — ≈ zero width, **≥qRH** |
| B8 | Source-side bound `O < 2` on every window — **RH** (Σ8) |
| B9 | Uniform window rounding (rate independent of height) — **sub**, needs zero-spacing control |

### S4. Counts and producers (WL, MC, PBM, RB, JAS, CTF, ACS-effectivity)

Established [L]: one-sided count ⇔ RH (several receivers: `ψ`, `π`/li, Mertens, Turán, Riesz,
majorant); prime-error budget ⇒ purity and `S ≥ 2 + γ − log 4π`; Abel slope ⇔ RH + simple; theta `h⁰`
has exact linear Riemann–Roch but satisfies the quadratic Riemann inequality on no polar surface;
Hecke auxiliaries see only the critical lattice; `K`-monomial auxiliaries vanish to order `< K`;
coprime Möbius sawtooth sums save only `(1 + log t)^{−3}`.

| | Obstacle |
|---|---|
| A9 | Formalise the univariate integer-Chebyshev ceiling (classical) to calibrate how far single-variable integer auxiliaries can push the producer |
| A10 | Same-order mixed-jet recovery for `≥ 3` primes |
| B10 | Any unconditional source input at square-root precision — **RH** (Π2) |
| B11 | Parity-selective auxiliary of controlled height beyond the factorial Landau class (`(2 log 2 − ε)mn`) — **sub** if it does not improve exponents |
| B12 | Characteristic-0 quadratic effectivity (surface `h⁰` with Hilbert–Samuel growth) — **RH** (Π11) |

### S5. Carriers and selection (SC, AKG, APD, PW-B, Γ-candidates)

Established [L]: Hecke-supported and escaping states have `κ ∈ {0, ∞}`; pole–successor `κ = κ₀ + 1`
per place; separable assembly `Σκ₀ ≤ κ ≤ Σκ₀ + 1`; no fixed counterterm makes the prime kernel
Pontryagin; archimedean continuity against height decay ⇒ `κ = ∞`; Weil extensions: blind is
index-minimal, Hecke-supported finite index ⇒ RH, Haar successor ⇒ `κ = ∞`; shell decomposition of
the pole–successor form (renormalized hyperbolic pair + shell squares, counterterm `cR` running with
the cutoff); finite-dimensional unitary rational affine representations factor through the slope.

| | Obstacle |
|---|---|
| A11 | Remove `XiZeroCopy` from the PW-B theta instantiation where it is notational |
| B13 | Classification of finite-index states on `Aff(ℚ)` with dilation reading continuous at `1` (are they slope pull-backs?) — **sub** (Γ7) |
| B14 | Zero-independent selection of ζ at the trivial gauge point — **RH** (Γ1) |

## 2. Live routes

### WL — prime lag / Weil–Li energy (prime explicit-formula family)
Established: critical-energy, linear prime-error and one-sided `√x log²x` criteria; genus-slope ⇔ RH +
simple; budget `≥ 2 + γ − log 4π`; `Count(a)` iff `a − 1 ∈ 𝒬`; Chebyshev–Stirling split; arithmetic
Bézout and exact divisibility from approximate Frobenius vanishing; Landau window cost
`(2 log 2 − ε)mn`; Adams support `≥ 2^{qr}`; scalar jets `k < r`; Hecke auxiliaries critical-only.
- A: A9, A10.
- B: actual one-sided prime-error bound (**RH**, Π1); B11; joint Möbius-moment / Mertens / sawtooth payment at square-root precision (**RH**, Π5); auxiliaries outside a single-prime Hecke algebra whose vanishing beats the support–order law (**sub**, Π3).

### RW — restricted Weil ground minimum
Established: `μ(A) ≥ 0` for all `A` ⇔ RH; signed Gårding finite index; floors `≥ mass/5000` to `181/500`
and `≥ mass/8000` on `(181/500, A₊)`, `A₊ < ½`; `μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})` (no uniform floor).
- A: certified positivity past the two-prime aperture `½ log 3` (prime 3 enters at `2r = log 3`); fixed-`A` low-mode / collar bookkeeping.
- B: all-aperture sign (**RH**, Σ1); a uniform gap at unbounded aperture is a no-go.

### FU — Fourier/Abel prime scheduling
Established: completed Abel moment bounded above ⇒ RH (receiver).
- A: none identified.
- B: joint bound of seed, drift, prior, cross-block and endpoint terms (**RH**, Σ1).

### CFC — first-clock sine coefficient
Established: RH ⇔ coefficient `≥ −C` on the aperture tail; unbounded below under ¬RH.
- A: none.
- B: actual source lower bound (**RH**, Σ).

### RP — normalized prime history
Established: RH ⇔ history `≥ −B(K + 2)` eventually; unconditionally it drops below `−δ(K + 2)` cofinally.
- A: none.
- B: pay high-LCM pairs, the moving core and singular transport at linear scale (**RH**, Σ/Π).

### PA — Hausdorff-order positivity
Established: each fixed order positive at large shifts.
- A: explicit shift threshold per order.
- B: all-order / all-shift positivity (**RH**, Σ4).

### MC — Möbius cancellation
Established: half-power dictionaries; `Θ ≥ ½`, Haar-a.e. exponent `½`, RH iff the trivial point is
typical; Chebyshev energy = nonnegative cyclotomic remainder; far modes `≤ 288N√(N+1)`; near modes at
primitive conductor `≥ (N+1)/⌈√(N+1)⌉`; uniform Dirichlet zero-free region and Siegel for `q ≤ (log x)^A`;
reciprocal shells `≤ Cc/(log Y)^k`; `M = o(√x)` false.
- A: none beyond the Siegel–Walfisz range (done).
- B: moving-scale half-power cancellation (**RH**, Π2); near-band cyclotomic energy `O(N^{3/2+ε})` at `K = ⌈√(N+1)⌉` (closes the 3/4 strip, **≥qRH**); finite-prime clock head/leaf signed cancellation (Σ); trivial-point typicality (**RH**, Γ1).

### TT — theta seam / Wold
Established: seam, tail, Wold receivers; `t < ½` boundedness threshold; truncated theta transform `= −seed·B_N(ρ)` at zeros.
- A: none.
- B: all-test directed covariance or complete odd positivity (**RH**, Σ).

### LA — Laguerre/Jensen
Established: every fixed ξ-Jensen degree eventually real-rooted; `λ_T` facts of S3; Vitali blow-up: a real-zero entire family converging pointwise to `Ξ` on a uniqueness set and locally bounded forces RH (`XiCRealZeroVitaliBlowup`) [L].
- A: explicit horizon for each fixed degree.
- B: all-degree / all-height coefficient signs (**RH**, Σ4); Jensen hyperbolicity is nonselective — needs a Γ input.

### TG — transgression / central gap
Established: transgression and central-gap receivers.
- A: none.
- B: matrix-complete decomposition with integer trace `< 1` (**RH**, Σ8).

### HF — Hodge/Hecke/complete cells
Established: block S1; bounded-overlap complete positivity; full Weil index `≤ R + A` for `R` coarse cells (dimension of readouts); theta-prefix collision reconstruction.
- A: A1–A5.
- B: B1, B2, B3.

### CHMD — causal hyperbolic–modular duality
Established [L]: RH ⇔ `⟨Rw, w⟩ ≤ ½‖w‖²` on the odd sector ⇔ no odd eigenvector above `½`
(`CHMDOddSectorCriterion`); prime wave `O(e^{|u|/2})` unconditionally with uniformly bounded pole and
archimedean waves (`CHMDStage22…`); Haar source: every piece except the first-prime coarse layer has
uniform finite index — cubes and higher, prime-two mixed, squares + odd higher, entire square source,
full Haar prime source after a finite head, multiplier tails Gamma-small (AID); one Gamma mean graph
pays the prime-two mixed block; prime-edge Gamma keeps `1 − log 2/log 3` of divisor energy; growing
Euler head alone unbounded; full prime window cancels `√Y` on fixed packets.
- A: A4; fixed-cell first-prime / coarse / polar cost bookkeeping.
- B: uniform coarse-size control (finite index, **≥qRH**, Σ5); full wave or odd-sector sign (**RH**, Σ3); joint positivity of non-arithmetic Gamma graph + signed diagonal + prime reserve + roots + poles (Σ1).

### TH — theta Hankel ranks
Established: rank-7 center Hankel strict; rank 8 PSD; `I₇(a) ≥ 0` for `0 < a < ½`; native odd-four seam compensated at `r_c = log(5/π)`; heated orthant signs all ranks; all-rank signed-center positivity ⇔ RH.
- A: rank-8 strictness; ranks 9, 10 (finite computations).
- B: all-rank sign (**RH**, Σ4); signed local flux paid uniformly in rank (Σ4).

### RN — renewal
Established: compact cone-positive renewal operator with exact regularized determinant.
- A: none.
- B: directed mixed prime + Gamma `≥` pole (Σ); cone positivity does not give real spectrum; native unregularized synthesis is a no-go (Σ6).

### WD — Ward / collision / heat
Established: block S3.
- A: A7, A8; localized dissipation bookkeeping.
- B: B6, B7, B8, B9; vanishing global depth energy as `t ↓ 0` (**RH**); tower branch needs an arithmetic index ceiling (**≥qRH**).

### LI — guarded history zeros
Established: guarded history-zero set `Z_S` finite; RH ⇔ `Z_S = ∅`; under ¬RH the last zero has odd order.
- A: none.
- B: pay the outside budget at guarded zeros (Σ).

### SZ — Suzuki / Ward defect
Established: ¬RH ⇒ cofinally unbounded below; finite packets: reflected current + negative-light Gram = positive-light Gram; the complete Abel clock has negative finite-cutoff pairings.
- A: none.
- B: uniform lower bound after complete source assembly (Σ).

### PM — physical / complete-energy realization
Established: complete-energy and gauge-mass receivers; half-damping admission.
- A: none.
- B: cofinal complete-energy bound as `ε ↓ 0` (**RH**); exterior tightness and exclusion of infinite-height escape (Γ/Π).

### JAS — joint ancestry
Established: positivity at growing logarithmic prime budget.
- A: none.
- B: square-root power budget (**RH**, Π).

### CTF — completion transfer
Established: Euler completion error `≤ 1/(n+1)`; full and finite-source energies have the same limits.
- A: none.
- B: full-source energy decay by signed covariance cancellation (Π); the receiver needs `B X^ε` in the inner cutoff `X < M` (Π).

### HCF — two-grid Hankel
Established: positivity on both `log 2`/`log 3` grids with polar cancellation ⇔ RH; one grid alone aliases.
- A: fixed-degree checks.
- B: both grid signs at every degree and height (**RH**, Σ4).

### XN — Newton dynamics
Established: RH ⇔ ξ-Newton source margin on discs (`XiNewtonDiscSourceMargin`) [L].
- A: none.
- B: cover every zero with nonnegative margin (**RH**, Γ).

### BAG — Bagchi recurrence
Established: RH ⇔ disc recurrence on every closed disc of the strip; Voronin universality on discs, compacts and connected-complement compacts [L].
- A: none.
- B: returns near every right-strip point including potential zeros (**RH**, Γ1).

### EWU — Euler weights
Established: RH ⇔ at every aperture some real weights make the full Weil functional nonnegative; the obstruction dual is a blind test.
- A: shares RW's fixed-aperture computations.
- B: nonnegative actual minimum at every aperture (**RH**, Σ1).

### GTA — transverse charge
Established: transverse-charge decay criterion; transverse energy pays each negative square [L].
- A: none.
- B: rank-uniform arithmetic transverse-energy decay (Σ4).

### OWU — odd Weil selectivity
Established: for every `r > 27/50` a smooth odd test on `[−r, r]` has `W_ζ > mass/25` and `W_Liouville < −3 mass/10`.
- A: positivity on all odd tests slightly beyond `27/50` (shared with RW).
- B: all-test / all-aperture odd sign (**RH**, Σ1); companion-forcing certificates and the conductor horizon are incompatible (no-go).

### PBM — pole-regularized prime series
Established: convergence at every `σ > ½` ⇔ RH.
- A: none.
- B: coefficient cancellation (**RH**, Π).

### RB — Robin / Nicolas
Established: large counterexamples require growing prime(-power) cores (`RobinMovingValuationDefect`) [L]; colossally abundant reduction [L].
- A: none.
- B: square-root remainder on primorials (**RH**, Π).

### SRT — square-root threshold / zero visibility
Established: depth-gap visibility law: positivity at aperture `a` forces every depth-`δ` zero to have a companion of comparable depth within `R` (`DepthGapVisibilityLaw`) [L]; unsigned depth sampling at one aperture controls squared depths on every unit window [L]; Steklov full index for `β > 2`; tilted-spline spans `α < 1/19`.
- A: A5; explicit horizons.
- B: B1; tower branch arithmetic index ceiling (**≥qRH**).

### ACT — collar transport
Established: explicit collar-shift threshold pays every modulus outside nine atom-dominated moduli.
- A: the nine remaining moduli (finite case analysis).
- B: one fixed shift paying every profile including exterior primes (Σ1).

### AIP — arithmetic incidence positivity
Established: all-aperture allocation receiver; full Weil index `≤ R + A`; full-prime window cancellation on fixed packets.
- A: mixed Schur debit on fixed blocks.
- B: all-aperture allocation (**RH**); mixed Schur debit from tail energy uniformly (Σ1).

### ACS — arithmetic Castelnuovo–Severi
Established [L]: RH ⇔ effectivity ⇔ no abundant class ⇔ Hodge index ⇔ section count; the base theta
`h⁰` does not extend (linear RR, fails the quadratic Riemann inequality on every polar surface,
including the scaling surface regardless of RH); degree-only effectivity exists iff Hodge index;
graded strip: zero width `≤ σ` ⇔ sign-free shortfall at rate `e^{2βr}`; F₃ elliptic curve: Euler
product, quotient Haar, adele Haar, idele characters, restricted central loop group, nonzero spectral
section on it; loop Eisenstein: affine A₁ Weyl sum, finite-field Weyl poles, naturality and
continuity of unipotent streams and Borel torus coordinates.
- A: F₃ automorphic chain — unipotent quotient measure, Eisenstein series on the restricted loop group, absolute convergence, constant term (function-field mathematics); atomic branch A1–A5.
- B: characteristic-0 quadratic effectivity (**RH**, Π11); a conformal correspondence over ℤ with bounded self-intersection (Rosati) (**RH**, Γ10); census displacement — projection may erase displacement (Π8); confinement needs lower counts (Π).

## 3. Candidates

| Candidate | Established | A (just work) | B (open) |
|---|---|---|---|
| APF | Fredholm index, cycle-trace reconstruction | — | zero-independent divisor exhaustion (Γ5) |
| BSH | framed curvature | — | pre-divisor section and mate identity coupled to Ξ zeros (Γ5) |
| CDC | calibrated confluence iff `Re s = ½` | — | source-defined potential forcing confluence (Γ/Σ) |
| DR | cusp roots, finite monodromy | — | compatible roots on the strict-right domain; global monodromy (Γ) |
| EGC | pole-safe contour | — | outer expanding-contour sign; raw decay cannot beat the Gamma floor (Σ/Π4) |
| EWJ | Euler/Wold jets | — | zero-independent source admission (Γ5) |
| FEL | theta likelihood / BSY integral = off-line zero sum | — | predeclared source balance (Σ) |
| HJ | Hurwitz reflection residual = SEC charge, vanishing iff criticality | — | pre-divisor forcing (Γ5) |
| IRK | rotation-algebra trace / winding | — | arithmetic Poisson / projective lift with integral count (Γ/Π) |
| MSC | Möbius–Sonin | — | bridge to nonnegative Sonin energy (Σ) |
| PCS | singular co-shift | — | source-natural wall annihilation; shift ≠ dilation (Γ) |
| PTR | photonic lossless stack, unit port gap | — | prime-faithful port; lossless realization needs infinitely many resonances (Σ6) |
| RFHM | support grade, reversible sewing inverse-covariant | — | symmetry-breaking law (Γ) |
| SC | block S5 [L] | — | B13; source-defined nonseparable carrier with Weil dilation, visible successor and controlled index; local–global gluing with a running counterterm (Γ7, Σ10) |
| SEC | essential norm = seam jump | — | pre-divisor compactness at zeros (Γ5) |
| W1C | finite Lee–Yang + Ising receiver; Vitali blow-up obstruction [L] | — | couplings converging to Riemann's measure (Σ6) |
| WBF | genealogy Gram | — | any arithmetic coupling (Γ5) |
| PW-B | native action on source data | A11 | zero-independent selection (B14) |

## 4. Obstacle count by wall

| Wall | Routes whose decisive B-item lies there |
|---|---|
| Σ (critical sign) | RW, FU, CFC, RP, PA, TT, LA, TG, HF, CHMD, TH, RN, WD, LI, SZ, EWU, GTA, OWU, SRT, ACT, AIP, HCF; FEL, MSC, EGC, PTR, W1C |
| Π (square-root precision) | WL, MC, PBM, RB, JAS, CTF, ACS-effectivity; IRK |
| Γ (selection) | BAG, XN, PM, MC (typicality), ACS (Rosati); APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SC, SEC, WBF, PW-B |
