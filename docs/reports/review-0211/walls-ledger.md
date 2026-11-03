# Walls ledger — status quo

Three wall families block every route: **Σ** the critical sign, **Π** precision and production,
**Γ** selection of ζ. All three read one even integer, `κ = κ(K_ζ) = #` distinct zeros right of the
critical line, and all three are read on one object: the **window tower** `A ↦ W_A`, with
`κ = sup_A ι(A)`. A window of length `A` is a module over the Dirichlet ring truncated at `⌊e^A⌋`; the
tower is a chain of small extensions, one fold per integer.

- **Σ is the exact stage step.** On a window Weil's form is
  `Q = Ω(0)‖H‖² + J_∞(H) − 2⟨ρ_A(Λ)H,H⟩ + ½⟨c,H⟩² − ½⟨s,H⟩²`. A new fold `N+1` enters only as one
  collar-to-collar correlation `−2w_{N+1}∫H(u)H(u+log(N+1))du`; the collar exit charge pays it pointwise,
  composite stages are free, and the pointwise part of the bulk is paid by the end profile up to length
  `~0.18`. What is open is the exact step: the pointwise payment uses AM–GM and drops the new fold's own
  energy, and Weil positivity has no slack (the Weil cone is a single point; window margins are doubly
  exponentially small). The bulk — the accumulated canonical class against the interior jumps — has to be
  paid exactly, uniformly in the stage.
- **Π is the derivative at dimension zero.** Weil's arithmetic term is the `k`-derivative at `k = 0` of
  the Tate function `⟨ρ_A(J_k)H,H⟩`, whose values at positive integers are point counts of punctured
  affine space over `ℤ/m`; its Taylor coefficients are Bombieri's `Λ_j` [D], so the first one is the
  parity barrier on windows. Size: window negativity grows at least at rate `Θ − ½` (two-bump tests) and at most at rate `½`. Production:
  no finite-square identity, no finite-rank carrier; a producer is an exact identity of unbounded rank.
  The classical precision faces (log-mean, near-line density, Hecke defect) are one density statement in
  eight forms.
- **Γ is the positivity of the reflection.** The reflection exists on both sides — the window involution
  `σ_A` is the Rosati involution of the window algebra, and on the Mayer side the Lewis adjoint
  `I_s† = I_{1/2−s̄}` has a co-isometry defect vanishing exactly on the line, with a Krein space whose
  positivity is RH. Every selector without positivity is blind. The Weil cone is `{Λ}` or empty, and its
  nonemptiness is prime-blind.

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact
form a theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a
classification or identification theorem), **Reduced** (theorem-level equivalent of the statement
named). Strength: **RH**, **≥qRH** (zero-free half-plane and Lindelöf), **LH**, **sub**, **indep.**
Evidence: `[L]` integrated Lean; `[S]` working tree or not wired into its umbrella; `[P]` paper proof or
plan; `[N]` numerical; `[D]` derived here from Lean statements. Window lengths `A`; half-widths `a = A/2`.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign on window tests | Sharpened | RH | RH ⇔ `Q ≥ 0` on every window test of every length ⇔ fold capacity on every window ⇔ `ι(A) = 0` ∀A ⇔ horizon blocks eventually `≥ −ε` ⇔ pole-hyperplane sign on the Beurling schedule ⇔ sign at every `2K(log N)^{1/8}` ⇔ odd-sector positivity at every length ⇔ Mayer Krein positivity [L]. Window algebra = Dirichlet ring truncated at `⌊e^A⌋`; `Q` in the algebra; `ι(A)` monotone, `0` for `A ≤ 3/5`, `≤ ⌊1 + 2A·T(A/2)/π⌋`, `sup ι = #` right zeros [L]. |
| Σ1a Critical overlap and receivers | Solved | — | `c*_N ≍ L(log L)²`, margin `1/log N`; tilted-spline receiver at every `K(log N)^{1/8}`; unit-bump receiver at every positive-power rate; one Beurling profile realizes every finite rational Gram at `2L(log L)²` [L]. |
| Σ1b Rough regime, tilted spline | Partially solved | sub | All vectors `1 ≤ c ≤ (log N)^α`, `α < 1/9` [L]. Below `1/8` [L]: far reserve `(7/8)D_M + κ/(4c⁷)·log N·S − θlog N·P` on `V_1^⊥`; polynomial-conductor complement floor `c_orth log N/c⁷`, nonpositive subspaces of dimension `≤ ⌊N^θ⌋`; three-band complement keeps floors `κ₀+3`, `κ₀+2+√L/32`, `κ₀+2+3bk/(16c⁷)` after internal cross payments; band–far cross with every channel paid by a free reserve parameter; coherent jet–pole cancellation; deep-row conductor residuals; growing subthreshold block Jordan. Whole-space positivity for every `α < 1/8`: plan complete, assembly open [P]. Terminal-pole orthogonality of the prefix–terminal block refuted; survivor: rank-one coherent structure [P]. |
| Σ1c Joint shell–pole payment | Partially solved | sub | Actual prime-successor edges pay nonconstant packet mass, `½affineDirichlet ≥ [P(⌊N/16Q²⌋) − P(Q)]·mass/64` [L]; separate shell payment costs `c⁹` at `ε = c⁻⁷`; joint top-band coefficient `O_φ(G(c + log N))` [L]. Open: shell, pole, Gamma and row-potential payment coupled to the complement at the critical overlap. |
| Σ1d General profiles | Partially solved | sub | Universal rate `ae^{−Bc}` on polynomial spans `θ < 1/1080` for `c ≤ b log log N`; subpolynomial spans to a super-log-log clock [L]. Full space past `log log N` open. |
| Σ1e Square-root conductor barrier | Partially solved | sub | Frames and residual averages need `m² ≤ N`; above `√N` an Elliott–Halberstam-type input; prime conductors above `√N` have disjoint spikes [L]. |
| Σ1f Defect-only confinement | No-go | — | `Q < 2^k` witnesses [L]. |
| Σ1g Haar / Gamma graph | Partially solved | sub | All-detail prime–pole cancellation `O(exp(−√log Y/92160000))`; index `≤ R + A`; growing Euler heads unbounded [L]. Joint Gamma graph + signed diagonal + poles open. |
| Σ1h Rough regime, smooth profiles | Solved (to `ε₀·c*`) | sub | Logarithmic profile positive to `ε₀L(log L)²`, budget sharp [L]. |
| Σ1i Second order on horizon blocks | Classified | — | Every profile with `s^βE₁(s) → J`: `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²` along `c^{β+1}/log N → K`; pencil index `= #{λ_i < 0 : βJ/(−λ_i) < K}` on independent families [L]. |
| Σ1j Tate decomposition of the complete family | Partially solved | sub | Every fixed Ramanujan conductor `m ≥ 2`: complete critical-curve limit `7φ(m)J(m)‖H‖²_{−8}/K`, no Weil term; regular bulk `J_{β+1}(m)βJ‖H‖²/K`; divisor twists = sums of conductor counts; untwisted and prime-conductor windows orthogonal at second order; periodic-twist energy law; bulk packets `#ℙ⁷(ℤ/m)`; twisted windows zero-blind, positive, coercive [L]. Ramanujan-basis diagonalization [S]. Open: joint form of different conductors, character twists, growing conductors, full zero-sum exchange, bulk–horizon cross terms. |
| Σ1k Phase diagram `(A, K)` | Partially solved | sub | Sharp pencil `κQ + c∫e^{−py}H² ≥ 0` for `c ≥ κ(deg K_A + 2sinh(A/2) − A)` [L]; pencil index monotone in `K`, equal to Weil's index for large `K`, never above the right-zero count [L]. Open: one fixed `K` on windows of every length; equality case. |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | HR ∧ HL ⇔ strict HR; RH ⇔ HL on the PSD locus; the first edge is PSD with a zero mode [L]. A zero mode is a solution of the window Euler–Lagrange equation (logarithmic-Laplacian Gamma kernel, `Λ`-weighted shifts, two pole constraints) [D]. |
| Σ3 Stars and dilation monodromy | Partially solved | — / RH | Stars isometric, positivity descends, depth law; monodromy eventually idempotent; Jordan coefficient a point count; tensor law CRT [L]. |
| Σ3a Coprime stratum | Sharpened | RH | gcd stratification; graded/top Möbius pair; conductor Gram PSD at every `2K(log N)^{1/8}` ⇔ RH; Redheffer `det = M(N)` [L]. |
| Σ4 Finite index / heat count | Sharpened | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | `κ < ∞` ⇔ bounded heat counts ⇒ `Θ < 1`; no softening at any resolution; `{0, ∞}` laws for tensor squares, regular extensions, mixing and Hecke-supported carriers [L]. The zero–one law for `κ` itself is open (sub). |
| Σ5 Collision quantum / window integer | Reduced (to Π17) | RH | Index `0` ⇔ Wiener–Hopf invertibility ⇔ outer Szegő factorization [L]. |
| Σ6 Rank / degree uniformity | Partially solved | RH | Rank 7 strict, rank 8 PSD; fixed Jensen degree eventually hyperbolic; PF₃₇ [L]. |
| Σ7 Window Markov capacity | Sharpened | RH | Fold capacity criterion: RH ⇔ `|Ω(0)|‖H‖² + Σ(Λ(n)/√n)sym_n + ½s² ≤ J_∞ + Σ(Λ(n)/√n)·½fold_n + ½c²` on every window [L]. End profile `Q ≥ ∫V_A H² + pole`, `V_A = Ω_Γ + φ(−u) + φ(A+u)`; exit charge alone pays windows `≤ 1/7`; pointwise mechanism stops near `0.18` [L]. RH ⇔ `R ≤ ½` on the odd sector [L]. Pointwise folded-Markov calibration fails past the plastic root; variable-hub Schur squares and `T₂`-stick elimination survive [L]. On the odd sector: RH ⇔ an Agmon ground state of the Schur-reduced folded jump process with sinh capacity `≤ 1` [D]. |
| Σ8 Realization | Sharpened | RH | RH ⇔ every window has an `ℓ²(zeros)` realization; none finite-dimensional; a finite-rank realization of `K_ζ` forces infinitely many right zeros; under RH the level carrying slopes `1..N` has rank `≥ N` [L]. |
| Σ9 Explicit image / resolvent | Partially solved | RH in strip | Depth identity for `σ > 1`; theta–prime expression at `s = 4` [L]. |
| Σ10 Local signatures and gluing | Solved | — | `κ(φ_c) = κ + 1` at `∞` and every prime; two primes carry the full affine index [L]. |
| Σ11 Product-formula gluing of the global pole | Classified | — | Local poles add squares; extremal weight = archimedean pole on `S`-units [L]. |
| Σ12 Running counterterm / star flux | Solved | — | `log N − γ` cancels the prime diagonal; each star pays `log d` [L]. |
| Σ13 Tensor amplification | No-go | — | `K_ζ^n` PD ⇔ RH; `n₋(G⊗G) = 2n₊n₋` [L]. |
| Σ14 Deformation to a positive model | No-go as free input | — | Crossing-free path ⇔ PD [L]. |
| Σ15 Separable assemblies | Classified (no-go) | — | Blind when truncated, non-convergent when untruncated [L]. |
| Σ16 Prime–pole coherence / packet identity | Solved (identity) | — | Complete form = jump + incidence − shell + diagonal + boundary [L]. |
| Σ17 Inter-tower coupling and the natural cone | Sharpened | RH | Bounded dense coupling ⇔ RH; fixed Gaussian damping: rate `σ` ⇔ width `≤ σ`, bounded damped `ℕ²` coupling ⇔ RH; undamped: simple symmetric exact-spline divisors with the two-term RvM count, `O(log T)` remainder, bounded coupling and unattained width exist [L]. Open: the prime-side bound for the damped coupling. |
| Σ18 Exact SOS on a two-prime lattice | Open | RH | A generic Hecke orbit carries the full Hodge defect [L]. Any identity on the `{∞,2}` window is aperture-specific (that family turns negative at half-width `0.5574`); at `½log3` the odd sector has an exact Lagrange form with margin `1.5×10⁻⁵`, the even sector a secular reduction with margin `5.6×10⁻⁸` [N]. |
| Σ19 Rank-one intertwining coefficient | Sharpened | RH | `κ_Hodge = #` band poles of `Λ(s)/Λ(s+1)`; the rational level-four affine Weyl sum preserves every band zero as a pole of full multiplicity above one rotation threshold [L]; Mayer boundary `2ζ(s)/ζ(s+1)`; scattering coefficient of `SL₂(ℤ)`; contractive positivity blind [L]. |
| Σ20 Scheduled prime sums | Open | RH | Lower bounds for prime-scheduled energies (FU, CFC, RP, SZ, LI, FEL, EGC) [L receivers]. |
| Σ21 Extension / carrier | Classified | — | Escape, mixing, height decay ⇒ `κ ∈ {0, ∞}`; continuous-dilation carriers reading `1_H` iff `H ∈ {{0}, ℚ}` [L]. |
| Σ22 Lefschetz operators | Classified | — | Dilation HL trivial; overlap-flow HL on HR locus is RH [L]. |
| Σ23 Connected links | No-go | — | Links disconnected; coprime atoms couple only through the archimedean place [L]. |
| Σ24 Finite divisor | Solved | — | Coercive off `i/2` and a finite grid at every degree [L]. |
| Σ25 Semilocal and trace carriers | No-go | — | No `{∞,p}` positive carrier; exact `{∞,2}` trace through `½log3` [L]. |
| Σ26 Approximation by RH-true objects | Classified | — | Closure class Laguerre–Pólya [L/D]. |
| Σ27 Window stages | Partially solved | sub (each stage); RH (all) | Entrance solved: crossing a stage adds one fold whose end mass the collar exit charge pays (`Ω(ε) ≥ log 3 > 2/e ≥ Λ(n)/√n`); composite stages free [L]. Prime-free stage: all tests to `3/5`, exit charge to `1/7`, jump count to `1/32`, odd sector on the whole prime-free window by a count (`h¹ ≥ ‖f‖²/2000`) [L]; at most one negative direction below `log 2 + 1/50`, positivity ⇔ one cosh-capacity inequality [L]. First-fold stage: one fold `T₂`; no finite-square count identity (Π20) [L]; odd tests to `0.724`, cosh-orthogonal to `log 2 + 1/50` [L]; numerical margins `1.5×10⁻⁵` / `5.6×10⁻⁸` at `½log3` [N]. |
| Σ28 Window negativity budget | Sharpened | ≥qRH (exponent `< ½`); RH (subexponential) | Exact pole capacity `2sinh(A/2) − A`; `Q ≥ −(deg K_A + 2sinh(A/2) − A)‖H‖² ≥ −(−Ω(0) + (4A+1)e^{A/2})‖H‖²` [L]. The negativity rate of unimodular two-bump tests equals the supremum of zero depths [L]; window-energy abscissa = twice the maximal depth [L]. |
| Σ29 Low-frequency localization | Solved (localization) | — | Window negativity lives at the poles and below `τ₀(a) = 4exp(10 + 2e^{4a})` [L]. |
| Σ30 The stage step | Open | RH (exact step, as an induction); bulk room sufficient | Exact: `Q_{N+1}(H) = Q_N(H) + w_{N+1}(fold energy − end mass) = Q_N(H) − 2w_{N+1}∫_{left collar}H(u)H(u+log(N+1))du` [L/D]. Lossy: `Q ≥ Q_N − Ω(ε)∫_{collars}H²` with the reduced archimedean energy `≥ 0` [L]; its sufficient condition `Q_N − Ω(ε)∫_{collars}H² ≥ 0` (bulk room) drops the new fold's energy and over-pays its end mass, and with doubly-exponential margins it need not hold under RH. Under RH the near-null tests of the frozen form must anticipate every new prime-power fold: their end-to-end correlation at the lag `log(N+1)` is nonpositive up to the margin [D]. |
| Σ31 Positivity across the dimension-zero derivative | Sharpened | method; RH (uniform) | `Q = Ω(0)τ_H(0) − 2τ′_H(0) + J_∞ + pole`; `Q` is a signed count with the Lagrange coefficients of `log` [L]. Tate positivity at positive dimension is soft (`ζ(s)ζ(s−ε)` passes); at a prime only the sign of the weight survives `∂_k` at `0` [L]. On nonnegative tests the tangent principle bounds the arithmetic term by Tate counts in every positive dimension [S]. `J_k = Σ_j k^jΛ_j/j!` with Bombieri's `Λ_j = μ * log^j` [D]: the first coefficient is the parity barrier. |
| Σ32 Prime-blind positivity | Sharpened | RH | Every real weight with full Weil positivity is `Λ`; the Weil cone is nonempty iff the pole + archimedean part is `≥ 0` on positive combinations of autocorrelations vanishing at every `±log n` [L]; hence RH ⇔ prime-blind positivity [D]. Finite levels: the cones `C_A` of weights on `n ≤ e^A` positive on `W_A` are compact and nested, and RH ⇔ `C_A ≠ ∅` ∀A [D]. On the annihilator the archimedean part equals the zero sum `Σ_ρ ĝ(γ_ρ)` [D]. |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (equivalence) | RH | `ψ(x) − x ≤ C√x log²x` ⇔ RH ⇔ `κ = 0`; Redheffer `det R_N = M(N)`, `Ω±(√N)` [L]. The canonical class of a window is the half-weighted Chebyshev profile [L]. |
| Π2 Deciding input | Open | RH | No unconditional source input at square-root precision. |
| Π3 Producer cost | Partially solved | sub / RH | Multivariate parity producers reach `(1+ε)x + C_ε log²x`; individual producers have slope `> 1`; integer-Chebyshev ceiling [L]. |
| Π4 Window precision (kernel = coupling) | Sharpened | RH | Weil's kernel is the smoothed prime error in multiplicative windows; coupling ≡ kernel [L/D]. |
| Π5 Conjugate diagonal (Hecke defect) | Sharpened | sub → ≥qRH → RH | Means `O_c(log U)` for `c < ½`; `o(log U)` ⇔ critical-scale clustering [L], one of eight equivalent forms (Π22) [S]; one dyadic constant ⇔ RH [L]. |
| Π6 Averages versus all heights | Sharpened | — | Almost all unit windows zero-free at depth `(1+ε)log log T/log T`; right-half depth moment `o(V)` [L]; Planck windows zero-free beyond `A/log V` outside relative measure `O(e^{−rA}/A)`; all but `O_c(V/log log V)` unit windows certified at the double-log stage [S]. |
| Π7 Census / pair surplus | Partially solved | sub / LH | Simple critical `≥ 0.67250071`; positivity-only certificates cannot reach `3/4` [L]. |
| Π8 Depth visibility | Partially solved | — | Isolated pairs visible at aperture `a` iff `S_δ(a) > (1/2π)log(ξ/2π)`; clusters not excluded [L/D]. |
| Π9 Exceptional moduli | Partially solved | sub | Uniform zero-free region and Siegel for `q ≤ (log x)^A` [L]. |
| Π10 Frequency localization | Solved (localization) | ≥qRH; RH | Every band `⌈N^δ⌉` retains `2Θ` [L]. |
| Π11a–e Cone, bidegree, fixed-rank, definite, Siegel counts | No-go | — | Excluded as independent sign producers; fakes `ℤ ⊕ yℤ`, `m² + 64n²` [L]. |
| Π11f Logarithmic duality of the split surface | Partially solved | sub | Pole plane: Abel completion `A(t) > 0`, `A(1/t) = tA(t)`, logarithmic RR; boost count `B(1/t) = tB(t) + (1+t)log t + c(t−1)`; `B(t) = 4∫₀^∞C(t cosh v)dv` [L]. Primitive part open. |
| Π11g Boost transform | Solved (identity) | — | `∫Z⁺(s,u)e^{2wu}du = K(s,w)ζ(s+w)ζ(s−w)` [L]. |
| Π11h Count-valued primitive `h¹` | Sharpened | RH; fixed length sub | Window `h¹` = primitive Künneth `h¹ = ½Q`, Künneth part `h¹_K > 0` a product of counts [L]; Weil's window form is a signed count [L]; odd prime-free window paid by a count; jump count to `1/32` [L]; windowed Tate law; generic two-prime orbit `ℕ`-count criterion; golden and complex fakes have none [L]. Finite-square identities at the first prime refuted (Π20). Missing: a count-valued inequality. |
| Π12 Subconvexity / heat floor | Partially solved | sub | `μ(½) ≤ 33/200`; heat floors `133/200`, `2/3 + ε` [L]. |
| Π13 Prefix scale | Solved | — | Strip zeros `Θ(N² log N)`; stabilization `Θ(√m)`; certificate prefix `Θ(√m + √(log m log S))` [L]. |
| Π14 Amplifier rank | No-go (finite support) | — | Growing losses keep radius `Be^λ` [L]. |
| Π15 Critical-scale residual sign | Classified | — | At the critical curve the residual is the prime-free aliasing term plus Weil's form [L]. |
| Π16 Genus function | Sharpened | indep. | Window genus `≥ (2−η)e^A` plus multiplicity excess; main term `2e^A` = Young conjugate = theta count; atomic lattice of rank `⌊e^A⌋` with Arakelov degree `½log⌊e^A⌋!` [L]; upper law open. |
| Π17 Window energy | Sharpened | RH; ≥qRH (log stage) | `|𝒵(t)|²` over a reflection-closed window; abscissa = twice the maximal depth; log stage ⇔ inverse-log corridor [L]; `𝒵 = P₊ + P₋` with `P₋ ∈ L²`; the right-edge flux never cancels against its functional-equation image (`Ω(e^t/t)` on every Burnol window); polynomial stage ⇔ RH; fixed degree `k` ⇔ `|β − ½| ≤ C/|γ|^k` [S]. |
| Π18 Finite realizations | No-go | — | No finite-dimensional window realization; no finite-rank realization of `K_ζ` [L]. |
| Π19 Mollified log-mean from moments | No-go | — | Holomorphic moments attain Jensen's `½log c`; integer exponential moments do not determine the log-mean [L]. |
| Π20 Count identity at the first prime | No-go | — | For `log 2 ≤ A < 2log 2` there is no identity `Q = J_∞ + Φ + Σ_{i<k}ℓ_i²` with `Φ` vanishing on fold-free tests: fold-free, pole-free tests form an infinite-dimensional space killed by any finitely many readouts, and there `Q − J_∞ = Ω(0)‖H‖² < 0` [L]. Survivor: the obstruction is archimedean; the Lévy count must pay `Ω(0)` by an inequality. |
| Π21 Exact balance (no slack) | Classified | — | The Weil cone is `{Λ}` (under RH) or empty, for arbitrary real weights [L]; restricted ground energy `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})` [L]; near-null window tests are interpolants vanishing at the zeros below the Landau height [N/D]; the best finite-level prime-blind certificate has a margin comparable to `Λ`'s [D, heuristic]. Every lossy estimate fails on long windows. |
| Π22 Near-line density ladder | Sharpened | sub | Eight equivalent forms: critical log-mean `o(1)`, mollified log-mean `o(1)`, linear-mollifier outer law, horizontal moment `o(T)`, `100%` critical-scale clustering, `o(log U)` Hecke readings [S]. Almost-all log-stage certificates ⇔ log-free occupancy `D_win`; `D_zero ⇒ D_win ∧` log-mean law; occupancy and horizontal moment incomparable under generic density data [S]. |
| Π23 Inner caps | Open | RH (all degrees); ≥qRH (fixed degree) | Cauchy caps cancel the right-port flux down to `σ_m = 1 − 1/(116log(m+5))` [S]; the caps `[½, σ_m]` are the zero-free-region problem. |

## Γ — selection

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point | Open | RH | `Θ ≥ ½`, Haar-a.e. `½`; RH ⇔ trivial point typical [L]. |
| Γ2 Prime-set flips | Solved | — | Every nontrivial prime pattern separated at every density [L]. |
| Γ3 Twin-blindness of soft structure | No-go (complete) | — | Krein index invariant under unitary twists [L]. |
| Γ4 Frobenius at infinity | Sharpened | RH | `σ(ρ) = 1 − ρ̄`; RH ⇔ `σ` trivial ⇔ Hecke similitude ⇔ partner saturation [L]. Window: `σ_A` is the Rosati involution of the window algebra (Serre duality), multiplier `e^{−(s−½)A}` unitary exactly on `Re s = ½`, isometry on every datum [L]. Mayer: `I_s† = I_{1/2−s̄}` on `H_LP` (Γ24) [L]. Bridge: co-isometry defect of a lifted window test = window Frobenius defect, bounded by fold energies [S]. |
| Γ5 Source identification / pre-divisor | Partially solved | RH | Pre-divisor sections need zero-independent forcing [L]. |
| Γ6 Boundary sign / coherence | Solved | — | Pole boundary sign separates ζ from size-equivalent twins [L]. |
| Γ7 Affine carrier with Weil dilation | Solved | — | Gluing at a place; subgroup classification [L]. |
| Γ8 Poisson rigidity | Sharpened | RH | Zero-side positivity = RH [S]; restricted to the prime-annihilated cone it is prime-blind positivity (Σ32) [D]. |
| Γ9 Archimedean continuity vs height decay | No-go | — | ⇒ `κ = ∞` [L]. |
| Γ10 Function-field indistinguishability | Sharpened | — | Local walls identical over `𝔽_q(X)`; first-order count law identical over `ℤ` and `𝔽_q[T]`; curve windows realized in `ℂ^{2g}` [L]. Adams lifts = dilations of windows up to a Tate twist; over `𝔽_q` base change is an exact symmetry, over `ℤ` the tower is self-similar only on `e`-th powers; character twists carry Tate families [L]. |
| Γ11 Pole-blindness of the glue | No-go | — | Simple pole absorbed [L]. |
| Γ12 General gauges | Solved | sub | Harmonic saturation only at the Euler gauge [L]. |
| Γ13 Source-uniform extinction | No-go | — | Fails at `3/4 + i` [L]. |
| Γ14 Local counterterm selection | No-go | — | Flip twin glued index `1` [L]. |
| Γ15 Functional-equation twins | Partially solved | sub | Degree three and positive degree two admit off-line real zeros [L]. |
| Γ16 Selection–sign gap | Sharpened | RH | Every selector is a margin, index, counterterm or identity on a partial form; none gives the sign [L]. |
| Γ17 Scattering recentering | Classified (no-go) | — | Rational/algebraic maps real on the critical parabola are constant / horizontal [L]. |
| Γ18 Divisor-identity selection | Solved (selection) | — | Only `Λ` degenerates completely [L]. |
| Γ19 Correspondence algebra over `ℤ` | Sharpened | RH | Rosati positivity ⇔ orbit Hodge index ⇔ naive height at bounded distance [L]. |
| Γ20 Window selection | Classified | — | A window of length `A` does not see `p > e^A`; for every `A` a flip twin identical on all length-`A` tests is not Weil positive [L]. Selection is a law in `A`. |
| Γ21 Density selection on the natural cone | No-go | — | Exact spline divisors with the full RvM count, bounded undamped coupling and unattained width [L]. |
| Γ22 Contractive scattering positivity | No-go | — | Blaschke pairs keep every Schur inequality while placing zeros anywhere in `Re s > ½` [L]. |
| Γ23 Weil cone uniqueness | Solved | — | Every real weight with full Weil positivity equals `Λ` on `n ≥ 2`, with no hypothesis on the weight [L]. Selection is automatic once positivity is produced. |
| Γ24 Mayer reflection positivity | Sharpened | RH | Resonance ⇔ `ζ(2s) = 0` (five operator forms); `Z_PM` = Hardy's `Z`; `D_s(ψ_s) ≤ 0`, `= 0` iff `Re s = ¼`; Krein–Lax–Phillips space with `2κ₋ =` polar defect; Krein positivity ⇔ RH ⇔ renormalized Hodge index [L]. Finite dyadic cusp energy ⇔ resonance [S]. Open: finite cusp energy ⇒ `D_s = 0`. |
| Γ25 Two reflection centres | No-go (as operator symmetry) | — | The transfer structure reflects about `Re w = 1`, the zeta events about `Re w = ½`; the two compose to `w ↦ w + 1`; the arithmetic reflection is not an operator symmetry of `L_w` [P]. Survivor: the defect is the explicit factor `ζ(1+w)/ζ(2−w)`, analytic and nonvanishing on the strip. |
| Γ26 Resonant-state selectors | No-go | — | Fixed-`s` inversion fixes every resonant period [L]; three-term + inversion invariance holds off the line with `D_s < 0` [S]; Krein self-adjointness gives negative-norm states, not reality [L]; cutoff Gram data have a positive realization at every rate [L]; Hecke residual gaps hold at every rate including the critical one [L]; congruence level and height keep every pole [L]. The rate is retained, never selected. |
| Γ27 Tate counts as a selector | No-go | — | `ζ(s)ζ(s−ε)` has nonnegative Tate pieces in every positive dimension with zeros off the line; flip twins fail Tate positivity at their prime; at a prime only the sign of the weight survives the derivative at dimension zero [L/S]. |

## Bridges

| Bridge | Anchor |
|---|---|
| `κ(K_ζ)` = right zeros = `sup_A ι(A)` = band poles of `Λ(s)/Λ(s+1)` = upper-right Mayer resonances = `2κ₋` of the Mayer Krein space; even; RH ⇔ `κ < 2` | HKT, RIT, CWS, AOG [L] |
| Window algebra = truncated Dirichlet ring; `ρ_A(Λ)` = log-derivative of the window zeta operator; atomic lattice = regular representation | WTZ [L] |
| Weil's window form = dimension-zero jet of the Tate function = signed count; Tate pieces = degeneration counts `φ(m)#ℙ^β(ℤ/m)` | WTZ, AHD [L] |
| Tate family = exponential generating function of Bombieri's `Λ_j`; first coefficient = parity | [D] |
| Complete family at the critical curve = counts on every fixed conductor + Weil on untwisted windows | AHD [L] |
| Stage step: one collar-to-collar correlation per new fold; exit charge pays it with an AM–GM loss (Σ30) | WTZ [L]; [D] |
| Fold capacity ⇔ window sign ⇔ odd-sector Markov capacity with sinh capacity | CWS, CHMD [L]; criticality form [D] |
| Two-bump negativity rate = maximal depth = ½ window-energy abscissa; full window exponent between it and `½` | SRT, CDG [L]; WTZ floor [L] |
| Window involution = Rosati involution ↔ Lewis adjoint `I_{1/2−s̄}` via `U_LP`; Frobenius defect ↔ co-isometry defect | WTZ [L], RIT [L/S] |
| Weil cone `⊆ {Λ}`; nonempty ⇔ prime-blind positivity | RHTower [L] |
| Near-line density: eight forms; occupancy ⇔ almost-all certificates | CDG [S] |
| No finite realization ⇒ tower of rank `≥ N` for `N` slopes; genus `2e^A` | CWS, RIT [L] |
| Gaussian-damped two-prime cone coupling bounded ⇔ RH; undamped density cannot select | ACPL [L] |
| Gluing `κ(φ_c) = κ + 1`; Redheffer `det = M(N)`; graded/top Möbius pair | AKG, ADT, HWV [L] |
| Curve calibration: bounded coupling ⇔ unitary ⇔ windows realized in `ℂ^{2g}` | ACPL, LST, CWS [L] |

## Status counts

| Family | Solved | Partially solved | Sharpened | Open | No-go | Classified | Reduced |
|---|---|---|---|---|---|---|---|
| Σ (44) | 7 (Σ1a, Σ1h, Σ10, Σ12, Σ16, Σ24, Σ29) | 11 (Σ1b, Σ1c, Σ1d, Σ1e, Σ1g, Σ1j, Σ1k, Σ3, Σ6, Σ9, Σ27) | 11 (Σ1, Σ2, Σ3a, Σ4, Σ7, Σ8, Σ17, Σ19, Σ28, Σ31, Σ32) | 3 (Σ18, Σ20, Σ30) | 5 (Σ1f, Σ13, Σ14, Σ23, Σ25) | 6 (Σ1i, Σ11, Σ15, Σ21, Σ22, Σ26) | 1 (Σ5 → Π17) |
| Π (30) | 4 (Π1, Π10, Π11g, Π13) | 6 (Π3, Π7, Π8, Π9, Π11f, Π12) | 7 (Π4, Π5, Π6, Π11h, Π16, Π17, Π22) | 2 (Π2, Π23) | 9 (Π11a–e, Π14, Π18, Π19, Π20) | 2 (Π15, Π21) | — |
| Γ (27) | 6 (Γ2, Γ6, Γ7, Γ12, Γ18, Γ23) | 2 (Γ5, Γ15) | 6 (Γ4, Γ8, Γ10, Γ16, Γ19, Γ24) | 1 (Γ1) | 10 (Γ3, Γ9, Γ11, Γ13, Γ14, Γ21, Γ22, Γ25, Γ26, Γ27) | 2 (Γ17, Γ20) | — |

Strength of the open walls:
- **RH:** Σ1, Σ2, Σ3a, Σ6, Σ7, Σ8, Σ17, Σ18, Σ19, Σ20, Σ27 (all stages), Σ28 (subexponential), Σ30,
  Σ31 (uniform), Σ32, Π2, Π4, Π11h, Π17 (polynomial stage), Π23 (all degrees), Γ1, Γ4, Γ5, Γ8, Γ16, Γ19,
  Γ24.
- **≥qRH:** Σ4 (`K_ζ`), Σ28 (exponent `< ½`), Π5 (fixed scale), Π17 (log stage), Π23 (fixed
  degree).
- **sub:** Σ1b–Σ1e, Σ1g, Σ1j, Σ1k, Σ4 (zero–one law), Σ27 (each stage), Σ30 (each stage), Π3, Π5 (mean
  `o(log U)`), Π7, Π9, Π11f, Π11h (fixed length), Π12, Π22, Γ15.
- **indep.:** Π16.
- **method:** Σ31 (a positivity surviving the derivative).
