# Route obstacles — status quo

Scope: the 33 live routes, the 16 standalone candidates and the PW-B branch of the frontier map
(checkpoint `a5440dc8`), checked against the Lean corpus. For every route: what is established, the
obstacles that are **(A) just work** (known mathematics, finite computation, effectivisation,
bookkeeping, formal closure), and the obstacles that are **(B) open mathematics** (no known solution).

Legend. `[L]` Lean theorem (statement read). `[S]` result recorded at source/paper level in the
frontier map. `[map]` frontier-map status without a statement read here. Strength of a B-item:
**RH** = equivalent to RH; **≥qRH** = implies Lindelöf and a zero-free half-plane `Re s > ½ + α`;
**sub** = strictly weaker than RH or of unknown strength. Wall labels Σ/Π/Γ refer to
`walls-ledger.md`.

## 0. Hardness calibration (applies to every route)

| Fact | Anchor | Consequence for routes |
|---|---|---|
| `κ(K_ζ) = #` right zeros, already on any two-prime sublattice; RH ⇔ `κ = 0` ⇔ `κ ≤ 1` | HKT `TheFiniteIndexStratumOfZetaIsLindelofDeep` [L] | every route that ends in an index count ends in the same integer |
| `κ < ∞` ⇔ finitely many off-line zeros ⇔ bounded heat counts ⇒ Lindelöf + zero-free half-plane | same [L] | every **finite-index / finite-support waypoint is ≥qRH** |
| Archimedean Weil state: `κ(ratCorr(|a|) − c|a|^{−½}|b|) = κ(K_ζ) + 1` for every `c > 0` | AKG `WeilsArchimedeanStateCountsTheZeros` [L] | RH ⇔ index one for one explicit affine state ⇔ Weil Gram `≥ 0` on the boost hyperplane |
| Boost hyperplane `Σ w_n n^{−½} = 0` = orthogonal complement of the pole-conductor vector `v_1`; `v_1` is the ground state of the complete Weil matrix | AKG `boostMassU`; RAPT `ramanujanPoleProfile`; CACT `TheCompleteWeilGroundStateIsThePole` [L] | SC and the complete-Weil cluster are one sign problem: positivity on `v_1^⊥` |
| Fixed aperture, rank and overlap are never RH-complete; RH-complete overlaps: tilted spline `2(log N)^{α>¼}`, smooth `(log N)^ε`, Gevrey-2 `(log log N)^{>2}`, Steklov/sinc `K L(log L)²` | CACT, SSHA [L] | fixed-resolution positivity is always **sub** |
| One-sided count `ψ(x) − x ≤ C√x log²x` ⇔ RH; section shortfall at rate `e^{2βr}` ⇔ zero width `≤ β` | ACP, SPTL [L] | every **exponent gain on the count side is quasi-RH** |
| The Krein index is invariant under unitary twists; the glued archimedean index is invariant under the pole weight | AKG `TheIndexIsTwinBlind`, `TheGluingSquareIsSharp` [L] | index calculus cannot select ζ, and the glued state cannot use the pole to select |
| Pointwise local count bounds critical multiplicities; counting inputs give it only in density | SRT `TheLocalCountBoundsTheMultiplicity`, `CountingInputsDoNotBoundTheLocalCount` [L] | local-count hypotheses are not implied by RH; they are off the RH critical path |
| Heat: depth-`δ` pair survives to `κ = tL ≈ δ`; size-only horizon `≥ ½`; Weyl floor `2/3 = 4μ(½)` | Heat [L] | pointwise heat horizons below `½` are ≈ zero-width statements (**≥qRH**) |

## 1. Shared obstacle blocks

### S1. Complete Weil matrix at growing overlap (HF, SRT, AIP, ACS-atomic, SC, CHMD-index, RW/EWU/OWU through the ground minimum)

Established:
- all vectors, complete positivity for `1 ≤ c ≤ (log log N)^α`, `α < 1/16` [L] (CACT `TheCompleteWeilMatrixIsPositiveAtIteratedLogarithmicOverlap`); the logarithmic reserve `W ≥ ac⁻⁷(D_N − C log(2c)‖x‖²)` holds on the same range with absolute `a, C` [L] (CACT `TheCompleteWeilLogarithmicReserveSurvivesGrowingOverlap`);
- fixed packets: positive for `c ≤ (log N)^{<1/48}` [L] and `(log N)^{<1/19}` [L];
- conductor averages at RH-complete overlap: for `M = ⌊N^θ⌋`, `θ < ½`, `c²/log N → 0` (includes `2(log N)^α`, `¼ < α < ½`): `Σ_{m≤M}‖(W − E_m)v_m‖² / Σ E_m² → 0`, conductor-average energy `→ ∞`, nonpositive-conductor fraction `→ 0`, `κ(W|span{v_m : m ≤ M}) = o(M)` [S] (CAF `CompleteWeilResidualLevelOfDistribution`, `CompleteWeilConductorAveragePositivity`, `PrimeResidualLevelOfDistribution`);
- Ramanujan conductor frames for `M² ≤ N`: Riesz bounds `1 − 2θ` and `6`, Gram off-diagonal only along prime-power divisibility [S] (CAF `RamanujanConductorFrames`);
- low spectrum localized on low conductors; the unique lowest eigenvalue tends to the pole energy `E_1(c) ≍ c⁻⁷` with eigenvector near `v_1`, at every fixed `c` and along diagonal schedules [L] (RAPT, CACT);
- harmonic and prime finite parts: torsion-intersection energy plus one counterterm; full prime form `−T − D`, centered heads `+T − D`, boundary `−2T` [L] (SSH `Conductor/*`);
- conductor-uniform residual for `m ≤ (log N)^A`; joint top-band shell–pole cancellation; full prime window cancels the `√Y` head pole on fixed packets [L].

Location of the remaining sign problem (inference from the anchors): zero detectors have long Möbius
transforms (RAPT `TheZerosSeeEveryAtomicVectorThroughItsMobiusHorizons`), so under ¬RH the negative
vector at RH-complete overlap has large prime defect and violates the logarithmic reserve. Averages
and the low-conductor block are not where RH sits; the confinement of negative vectors to low
conductors is.

| | Obstacle |
|---|---|
| A1 | Lean closure of the `[S]` conductor-average results: level of distribution, conductor-average positivity, Riesz frames |
| A2 | Exceptional conductors inside the Siegel–Walfisz range: show the `o(M)` exceptional set avoids `m ≤ (log N)^A` using the individual uniform residual bound |
| A3 | Growing-packet head-pole cancellation, packets up to `exp(c√log Y)` (window PNT with classical error) |
| A4 | Growing-conductor control of the undilated hyperbolic term and moving-head packet norms (the `−2T` boundary retained) |
| A5 | Single-`K` completeness of the Steklov/sinc schedule at `K L(log L)²` |
| B1 | Positivity on an RH-complete schedule — **RH** (Σ1) |
| B2 | Confinement / logarithmic reserve beyond `(log log N)^{1/16}`: polynomial instead of exponential conductor confinement (**sub** below `¼`; **RH** on RH-complete schedules) |
| B3 | Exceptional conductors beyond `(log N)^A`: individual residual control — **sub**, Π9 |
| B4 | Square-root conductor barrier: frames and residual averages for conductors `N^{½} < m ≤ N` — **sub** (Elliott–Halberstam-type) |
| B5 | Full-complement / mixed Schur payment below the decaying floor — Σ1 |

### S2. Index / finite off-line support (HKT, AKLT, AID, SRT towers, CHMD index, SC)

Established [L]: index = right-zero count; finite stratum TFAE; converse Krein–Langer for orbit
kernels; complete cells capture every finite index; transverse energy pays each negative square;
source work `≤ 2` cofinally ⇒ RH; collision mass `= 2(κ + multiplicity excess)` on the finite
stratum; `κ ≤ sup` horizontal collision charge; archimedean state index `κ_ζ + 1`.

| | Obstacle |
|---|---|
| A6 | Explicit capture stage for complete-cell indices (AID `TheCompleteCellsCaptureEveryFiniteIndex`) |
| B6 | Any arithmetic index ceiling uniform in resolution — **≥qRH** (Σ5) |
| B7 | General converse Krein–Langer for kernels not presented by a zero configuration — **sub** |

### S3. Heat flow / collision charge (WD, LA, TH, TT, HCF; HEF receivers)

Established [L]: `E(t)` monotone with dissipation; energy majorization for `8St < 1`; slice threshold
`λ_t ≍ depth²/local count`, `{λ_t > 0}` null ⇔ RH, `λ_t = 0` on lower density `≥ 433/500`,
exponential upper tail and mean `≤ CU/log²U`; flow threshold `Λ_X` (local de Bruijn–Newman
constant): `Λ = sup_X Λ_X`, RH ⇔ every `Λ_X = 0`, `c d²/log X ≤ Λ_X ≤ (2/3+ε)/log X`; reality horizon
`2πe^{(2/3+ε)/t}`; deep copies `≤ C log X·N(t)` at `t log X ≤ c`; `N(t) ≤ exp(At^{−a})` gives `X^{o(1)}`
deep counts (`a < ¼` [L], `a < 1` [map]); collision charge `O ∈ 2ℕ`, RH ⇔ `O < 2` per window; prime
current summable ⇔ `O = 0`; theta-prefix readings round to `O`; local count for density-one heights
for ζ.

| | Obstacle |
|---|---|
| A7 | Formalise a stronger subconvexity exponent to lower the Weyl floor `2/3 = 4μ(½)` (calibration) |
| A8 | Effective rounding rate of theta-prefix collision readings on a fixed window |
| B8 | Subcritical heat count `a < 1` — **sub**, stronger than the density hypothesis |
| B9 | Pointwise horizon constant `< ½` — **≥qRH** |
| B10 | Source-side bound `O < 2` on every window — **RH** (Σ8) |
| B11 | Every `Λ_X = 0`, in particular at bounded heights — **RH** |
| B12 | Uniform rounding of collision readings (rate independent of height) — **sub**, needs zero-spacing control |

### S4. Counts and producers (WL, MC, PBM, RB, JAS, CTF, ACS-effectivity)

Established [L]: one-sided count ⇔ RH (several receivers); prime-error budget ⇒ purity,
`S ≥ 2 + γ − log 4π`; theta `h⁰` has linear RR and no quadratic Riemann inequality on any polar
surface; integer Hecke stencils: integrality ⇔ step weight `≥ 0`; every individual producer has slope
`> 1`; ceilings `2 log 2` (single prime), `1 + 1/((P+1)(P+2))` (finite alphabet), `31/30`
(parity-blind), `exp(−0.87n)` (univariate sup norm); growing-alphabet alternating parity-selective
producers reach slope `1 + ε` and `ψ, θ ≤ (1+ε)x + C_ε log²x` (AKLT
`MultivariateParityAuxiliariesReachTheMainTerm`).

| | Obstacle |
|---|---|
| A9 | Same-order mixed-jet recovery for `≥ 3` primes |
| A10 | Explicit `ε ↦ (support, coefficients, C_ε)` dependence of the main-term producer |
| B13 | ε-uniform producer: error terms of zero-free-region strength from vanishing order — **sub**; square-root precision — **RH** (Π3) |
| B14 | Any unconditional source input at square-root precision — **RH** (Π2) |
| B15 | Characteristic-0 quadratic effectivity — **RH** (Π11) |

### S5. Carriers, gluing and selection (SC, AKG, APD, PW-B, Γ-candidates)

Established [L]: Hecke-supported and escaping states have `κ ∈ {0, ∞}`; pole–successor `κ = κ₀ + 1`
per place; separable assembly `Σκ₀ ≤ κ ≤ Σκ₀ + 1`; distinct places do not glue (`k` places give
`κ = k`; real + p-adic gives 2); archimedean gluing by a hyperplane, `κ(Φ_{K,c}) = κ^{(½)}(K) + 1`;
prime towers glue at full index; the gluing square is sharp and pole-blind; every Hermitian rational
affine Haar kernel with continuous dilation has `κ = ∞`; finite-dimensional unitary rational affine
representations factor through the slope.

| | Obstacle |
|---|---|
| A11 | Remove `XiZeroCopy` from the PW-B theta instantiation where it is notational |
| B16 | One-square global state from coupled local states (product-formula coupling on principal units) — **sub** (Σ11) |
| B17 | Zero-independent selection at the trivial gauge point — **RH** (Γ1) |

## 2. Live routes

### WL — prime lag / Weil–Li energy
Established: critical-energy, linear prime-error and one-sided `√x log²x` criteria; genus slope ⇔ RH +
simple; `Count(a)` iff `a − 1 ∈ 𝒬`; Chebyshev–Stirling split; arithmetic Bézout; Landau window cost
`(2 log 2 − ε)mn`; Adams `2^{qr}`; scalar jets; block S4 producers up to the main term [L].
- A: A9, A10.
- B: actual one-sided prime-error bound (**RH**, Π1); B13; joint Möbius-moment / Mertens / sawtooth payment at square-root precision (**RH**, Π5).

### RW — restricted Weil ground minimum
Established: `μ(A) ≥ 0` for all `A` ⇔ RH; RH ⇔ zeros approach the line ∧ `μ₀` subexponentially bounded below; attained excess `Θ` forces `μ₀(B) ≤ −c'e^{2ΘB}/B³` [L]; floors `≥ mass/5000` to `181/500`, `≥ mass/8000` up to `A₊ < ½`; no uniform floor.
- A: certified positivity past the two-prime aperture `r ≥ ½ log 3`.
- B: all-aperture sign (**RH**, Σ1); a subexponential floor for `μ₀` (**≥qRH** given zeros approaching the line).

### FU — Fourier/Abel prime scheduling
Established: completed Abel moment bounded above ⇒ RH.
- A: none identified.
- B: joint bound of seed, drift, prior, cross-block and endpoint terms (**RH**, Σ).

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
Established: half-power dictionaries; `Θ ≥ ½`, Haar-a.e. `½`, RH iff the trivial point is typical; nonnegative cyclotomic remainder; far modes `≤ 288N√(N+1)`; near modes at primitive conductor `≥ (N+1)/⌈√(N+1)⌉`; uniform Dirichlet inputs and every inverse-log rate for `q ≤ (log x)^A` at one horizon; conductor-averaged large sieve for rough packets; finite prime-clock density cancellation [L].
- A: none beyond the Siegel–Walfisz range.
- B: moving-scale half-power cancellation (**RH**, Π2); near-band cyclotomic energy `O(N^{3/2+ε})` (closes the 3/4 strip, **≥qRH**); finite-prime clock head/leaf signed cancellation (Σ); trivial-point typicality (**RH**, Γ1).

### TT — theta seam / Wold
Established: seam, tail, Wold receivers; `t < ½` boundedness threshold; truncated theta transform `= −seed·B_N(ρ)` at zeros.
- A: none.
- B: all-test directed covariance or complete odd positivity (**RH**, Σ).

### LA — Laguerre/Jensen and local heat
Established: every fixed Jensen degree eventually real-rooted; block S3; Vitali blow-up (a normal real-zero approximant family of `Ξ` forces RH) [L].
- A: explicit horizon per fixed degree; A7.
- B: all-degree / all-height signs (**RH**, Σ4); density-one control leaves exceptional heights and shrinking scales (**sub**); linear detection needs microscopic local counts, which counting inputs cannot give pointwise (arithmetic input required, **sub**).

### TG — transgression / central gap
Established: receivers.
- A: none.
- B: matrix-complete decomposition with integer trace `< 1` (**RH**, Σ8).

### HF — Hodge/Hecke/complete cells
Established: block S1; full Weil index `≤ R + A` for `R` coarse cells; theta-prefix collision reconstruction; noncompact resolvent reading at `s = 4`.
- A: A1–A5.
- B: B1–B5.

### CHMD — causal hyperbolic–modular duality
Established [L]: RH ⇔ `R ≤ ½` on the odd sector ⇔ no odd eigenvector above `½`; prime wave `O(e^{|u|/2})` with bounded pole and archimedean waves; Haar source: every piece except the first-prime coarse layer has uniform finite index; Gamma mean graph pays the prime-two mixed block; prime-edge Gamma keeps `1 − log 2/log 3` of divisor energy; growing Euler head alone unbounded; full prime window cancels `√Y` on fixed packets.
- A: A3; fixed-cell first-prime / coarse / polar cost bookkeeping.
- B: uniform coarse-size control (finite index, **≥qRH**); full wave / odd-sector sign (**RH**, Σ3); joint positivity of non-arithmetic Gamma graph + signed diagonal + prime reserve + roots + poles (Σ1).

### TH — theta Hankel ranks
Established: rank 7 strict; rank 8 PSD; `I₇(a) ≥ 0` for `0 < a < ½`; heated orthant signs all ranks; all-rank signed-center positivity ⇔ RH.
- A: rank-8 strictness; ranks 9, 10.
- B: all-rank sign (**RH**, Σ4); signed local flux uniformly in rank (Σ4).

### RN — renewal
Established: compact cone-positive renewal operator with exact regularized determinant.
- A: none.
- B: directed mixed prime + Gamma `≥` pole (Σ); cone positivity does not give real spectrum; native unregularized synthesis is a no-go (Σ6).

### WD — Ward / collision / heat
Established: block S3.
- A: A7, A8; localized dissipation bookkeeping.
- B: B8–B12; vanishing global depth energy as `t ↓ 0` (**RH**); tower branch arithmetic index ceiling (**≥qRH**).

### LI — guarded history zeros
Established: `Z_S` finite; RH ⇔ `Z_S = ∅`; under ¬RH the last zero has odd order.
- A: none.
- B: pay the outside budget at guarded zeros (Σ).

### SZ — Suzuki / Ward defect
Established: ¬RH ⇒ cofinally unbounded below; finite packet identity reflected current + negative-light Gram = positive-light Gram; negative finite-cutoff pairings of the complete Abel clock.
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
Established: Euler completion error `≤ 1/(n+1)`; equal limits of full and finite-source energies.
- A: none.
- B: full-source energy decay by signed covariance cancellation (Π); `B X^ε` receiver in the inner cutoff (Π).

### HCF — two-grid Hankel
Established: both `log 2`/`log 3` grids with polar cancellation ⇔ RH; one grid aliases.
- A: fixed-degree checks.
- B: both grid signs at every degree and height (**RH**, Σ4).

### XN — Newton dynamics
Established: RH ⇔ ξ-Newton source margin on discs [L].
- A: none.
- B: cover every zero with nonnegative margin (**RH**, Γ).

### BAG — Bagchi recurrence
Established: RH ⇔ disc recurrence on every closed disc of the strip; Voronin universality on discs and compacts [L].
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
Established: for every `r > 27/50` one smooth odd test on `[−r, r]` has `W_ζ > mass/25` and `W_Liouville < −3 mass/10` [map].
- A: positivity on all odd tests slightly beyond `27/50` (shared with RW).
- B: all-test / all-aperture odd sign (**RH**, Σ1); companion-forcing certificates and the conductor horizon are incompatible (no-go).

### PBM — pole-regularized prime series
Established: convergence at every `σ > ½` ⇔ RH.
- A: none.
- B: coefficient cancellation (**RH**, Π).

### RB — Robin / Nicolas
Established: large counterexamples require growing prime(-power) cores; colossally abundant reduction [L].
- A: none.
- B: square-root remainder on primorials (**RH**, Π).

### SRT — square-root threshold / zero visibility
Established: block S1; depth-gap visibility law; unsigned depth sampling at one aperture controls squared depths; local count: pointwise ⇒ bounded critical multiplicity, not implied by counting or RH, true for density-one heights for ζ; off-line local bound ⇒ critical fraction `→ 1` [L]; Steklov full index for `β > 2`.
- A: A1, A5; explicit horizons.
- B: B1; tower branch arithmetic index ceiling (**≥qRH**); unattained-depth detection (Σ5).

### ACT — collar transport
Established: explicit collar-shift threshold pays every modulus outside nine atom-dominated moduli.
- A: the nine remaining moduli (finite case analysis).
- B: one fixed shift paying every profile including exterior primes (Σ1).

### AIP — arithmetic incidence positivity
Established: block S1; all-aperture allocation receiver; full Weil index `≤ R + A`.
- A: A1–A4; mixed Schur debit on fixed blocks.
- B: all-aperture allocation (**RH**); B2–B5.

### ACS — arithmetic Castelnuovo–Severi
Established [L]: RH ⇔ effectivity ⇔ Hodge index ⇔ section count; the base theta `h⁰` does not extend;
graded strip ⇔ zero width; atomic branch = block S1. F₃ elliptic curve: Euler product, quotient and
adele Haar, Haar periodization, degree ideles (magnitude `3^d`), finite cylinders exhausting the
finite adeles, local Haar = normalized magnitude, local spherical integrals
`(1 − q^{−s−1})/(1 − q^{−s})` on `Re s > 0`, restricted central loop group with idele rotation,
unipotent carrier = arithmetic intersection, unipotent arithmetic quotient with invariant
probability, nonzero spectral section, arithmetic Eisenstein series defined on Borel cosets and
right-arithmetic invariant; rotated series and constant-term integral [S]; polynomial cells of
degree `< 2n` [S].
- A: global Haar change of variables; spectral-section / local-kernel matching and analytic admissibility; absolute convergence; complete Bruhat unfolding; constant-term evaluation (function-field loop-group mathematics); atomic A1–A5.
- B: characteristic-0 quadratic effectivity (**RH**, Π11); a conformal correspondence over ℤ with bounded self-intersection (**RH**, Γ10); census displacement — projection may erase displacement (Π8); confinement needs lower counts (Π).

### SC — Stokes/Witt–Krein / archimedean successor
Path: `φ_c(a, b) = ratCorr(|a|) − c|a|^{−½}|b|` → `κ(φ_c) ≤ 1` → `κ_ζ = 0` → RH.
Established [L]: `κ(φ_c) = κ^{(½)}(K_ζ) + 1 = κ_ζ + 1 = #` right zeros `+ 1` for every `c > 0`; same for
tempered zero configurations and primitive Dirichlet L-functions; the gluing formula for every
Hermitian `K`; sub-boost and periodic data glue at full index; prime towers glue at `κ + 1`; the
glued index is blind to the pole weight; separated places keep one square each; every Haar
successor with continuous dilation has `κ = ∞`; zero-axis and polynomial-correction structure of
finite-index Haar kernels.
- A: instantiate the configuration theorem for the zeros of the heat-deformed `H_t` (finitely many nonreal zeros for `t > 0`): a finite-index archimedean state for every `t > 0` with index `#` nonreal right zeros of `H_t` `+ 1`.
- B: independent `κ(φ_c) ≤ 1`, equivalently Weil Gram `≥ 0` on `v_1^⊥` (**RH**, Σ1); coupled non-Haar local–global assembly with one square (B16, **sub**); growing-conductor index payment (Σ1).

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
| SEC | essential norm = seam jump | — | pre-divisor compactness at zeros (Γ5) |
| W1C | finite Lee–Yang + Ising receiver; Vitali blow-up obstruction [L] | — | couplings converging to Riemann's measure (Σ6) |
| WBF | genealogy Gram | — | any arithmetic coupling (Γ5) |
| PW-B | native action on source data | A11 | zero-independent selection (B17) |

## 4. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ (critical sign) | RW, FU, CFC, RP, PA, TT, LA, TG, HF, CHMD, TH, RN, WD, LI, SZ, EWU, GTA, OWU, SRT, ACT, AIP, HCF, SC; FEL, MSC, EGC, PTR, W1C |
| Π (square-root precision) | WL, MC, PBM, RB, JAS, CTF, ACS-effectivity; IRK |
| Γ (selection) | BAG, XN, PM, MC (typicality), ACS (Rosati), SC (gluing); APF, BSH, CDC, DR, EWJ, HJ, PCS, RFHM, SEC, WBF, PW-B |
