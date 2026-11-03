# Walls ledger — status quo

Three wall families block every route: **Σ** the critical sign, **Π** precision and production,
**Γ** selection of ζ. All three read one even integer, `κ = κ(K_ζ) = #` distinct zeros right of the
critical line, and all three are read on one object: the **window tower** `A ↦ W_A`, with
`κ = sup_A ι(A)`. A window of length `A` is a module over the Dirichlet ring truncated at `⌊e^A⌋` (a
finite local λ-ring); Weil's form on it is a translation-invariant form with kernel
`Ω(0)δ + (archimedean Lévy kernel) − Σ_{n≤e^A}Λ(n)n^{−1/2}(δ_{log n} + δ_{−log n}) + (pole)`.

- **Σ is the exact two-collar stage step.** At `A = log(N+1) + ε` the new fold couples only the left
  collar `[−A, −A+ε]` to the right collar `[−ε, 0]`. With the interior positive (an earlier stage),
  positivity on `W_A` is the block inequality `S^N_ε − w_{N+1}(J + J*) ⪰ 0` for the Schur complement
  `S^N_ε` of the frozen form onto the two collars [D]. The frozen form is indefinite at the first prime
  stage [L], so the new fold is a positive source: every payment that treats it as a cost is refuted, and
  Weil positivity has no slack (Weil cone a point; margins doubly exponential).
- **Π is precision at one mode; parity is classified at dimension zero.** One cyclotomic mode of the
  Chebyshev error carries the full zero exponent `2Θ` [L]. Weil's arithmetic term is the derivative at
  dimension zero of the counts of `𝔸^k∖0`; positive dimension supplies no positivity that reaches
  `k = 0` (bare domination ⇔ Weil sign; archimedean families fail; Tate positivity is not uniform)
  [L]. Production needs an exact identity of unbounded rank; finite carriers and finite-square
  identities are impossible.
- **Γ is reflection positivity.** The window algebra has no internal Frobenius (similitudes are scalars)
  [L]; the reflection `σ_A` (Rosati involution) and the Lewis adjoint exist; their positivity is RH.
  Selection is automatic after positivity (Weil cone `{Λ}`); prime-blind positivity is node-critical and
  equals zero-side positivity on blind tests [L].

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact
form a theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a
classification or identification theorem), **Reduced** (theorem-level equivalent of the wall named).
Strength: **RH**, **≥qRH** (zero-free half-plane and Lindelöf), **sub**, **indep.**, **identity**,
**method**. Evidence: `[L]` Lean in the corpus; `[W]` uncommitted working tree; `[P]` paper; `[N]`
numerical; `[D]` derived here from Lean statements. Window lengths `A`; half-widths `a = A/2`.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign on window tests | Sharpened | RH | RH ⇔ `Q ≥ 0` on every window test of every length ⇔ fold capacity ⇔ `ι(A) = 0` ∀A ⇔ horizon sign at every `2K(log N)^{1/8}` ⇔ Beurling schedule ⇔ odd-sector capacity ⇔ Mayer Krein positivity ⇔ prime-blind positivity ⇔ canonical archimedean domination on every window [L]. `ι(A)` monotone, `0` for `A ≤ 3/5`, `≤ ⌊1 + 2A·T(A/2)/π⌋`, `sup ι = #` right zeros [L]. |
| Σ1a Critical overlap and receivers | Solved | — | `c*_N ≍ L(log L)²`; tilted-spline receiver at every `K(log N)^{1/8}`; unit-bump receiver at every positive-power rate; one Beurling profile realizes every finite rational Gram at `2L(log L)²` [L]. |
| Σ1b Subcritical regime, tilted spline | Solved | sub | `completeWeilMatrix tiltedUnitSpline c N ≻ 0` for every `α < 1/8`, uniformly `1 ≤ c ≤ (log N)^α`, floor `κ/(2c⁷)`; exponent ladder `1/59, 1/16, 1/9, 1/8` [L]. Synthesized windows have vanishing length on this range. |
| Σ1c Joint shell–pole payment | Solved (subcritical) | sub | Prime-successor edges pay nonconstant packet mass; deep-row residuals `O(m(1+log m)²/log N)`; inverse-energy mass `Ψ_D ≤ 8(C_p+1)(8c⁷ + Q²(1+log Q)²)/(κ log N)`; row-split Schur synthesis [L]. |
| Σ1d General profiles | Partially solved | sub | Universal rate `ae^{−Bc}` on polynomial spans `θ < 1/1080` for `c ≤ b log log N`; subpolynomial spans to a super-log-log clock [L]. Full space past `log log N` open. |
| Σ1e Square-root conductor barrier | Partially solved | sub | Frames and residual averages need `m² ≤ N`; above `√N` an Elliott–Halberstam-type input; prime conductors above `√N` have disjoint spikes; uniform lower frames for `dp` conductors with `√N < p ≤ N^θ` [L]. |
| Σ1f Defect-only confinement | No-go | — | `Q < 2^k` witnesses [L]. |
| Σ1g Haar / Gamma graph | Partially solved | sub | All-detail prime–pole cancellation `O(exp(−√log Y/92160000))`; index `≤ R + A`; growing Euler heads unbounded [L]. Joint Gamma graph + signed diagonal + poles open. |
| Σ1h Smooth logarithmic profile | Solved (to `ε₀·c*`) | sub | Positive to `ε₀L(log L)²`; budget sharp [L]. |
| Σ1i Second order on horizon blocks | Classified | — | `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²` along `c^{β+1}/log N → K`; pencil index `= #{λ_i < 0 : βJ/(−λ_i) < K}` [L]. |
| Σ1j Critical-curve decomposition | Partially solved | sub | Every fixed finite family solved [L]: Ramanujan basis diagonal (`Σa_m²J_{β+1}(m)`), prime windows `J(1)φ(p)#ℙ⁷(𝔽_p)`, every mean-zero periodic twist (spectral Dirichlet series, coercive), real frequencies (Hurwitz forms `½(ζ(β+1,u) + ζ(β+1,1−u))`), primitive characters (count `± q^{s−1}‖L(s,ψ̄²)‖`, parity grading, `L(s,ψ̄₁ψ₂)` coupling), trigonometric twists graded by frequency [W]. Open: growing conductors, full-space cross terms, conductors above `√N`. |
| Σ1k Phase diagram `(A, K)` | Classified [W] | sub | Window floor `Q ≥ −(10 + 72e^{A/2})‖H‖²`; every critical multiple `K*(H) ≥ K₀(A) = βJ/(κ(10 + 72e^{A/2}))`; sharp pencil `κQ + c∫e^{−py}H² ≥ 0` for `c ≥ κ(deg K_A + 2sinh(A/2) − A)`; pencil index monotone in `K` [L]. Open: one fixed `K` on windows of every length; equality case. |
| Σ1l Polarization inheritance | Partially solved | sub | Eventually positive definite along the critical curve on: every twisted family, every family of windows of length `≤ 3/5`, the cosh hyperplane below `log 2 + 1/50` (at most one negative square there), every window length below `K₀(A)`; twisted directions add no negative square [L]. Untwisted long windows = Σ1. |
| Σ1m Bulk below the resolution height | Classified | — | Zeros of height `≤ N^θ` (every `θ < 1`) enter a fixed packet only through the pole, contributing `(c/log N)κy₁²(2 + γ − log 4π)`; pole-free packets blind [L]. |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | HR ∧ HL ⇔ strict HR; RH ⇔ HL on the PSD locus [L]. Zero modes of a nonnegative window are its radical, translation stable, nonvanishing on both collars at a first critical length [L]. Under ¬RH the edge exponent of the complete family is exactly `1/8` [D]. |
| Σ3 Stars and dilation monodromy | Partially solved | — / RH | Stars isometric, depth law; monodromy eventually idempotent; Jordan coefficient a point count; tensor law CRT [L]. |
| Σ3a Coprime stratum | Sharpened | RH | gcd stratification; graded/top Möbius pair; conductor Gram PSD at every `2K(log N)^{1/8}` ⇔ RH; Redheffer `det = M(N)` [L]. |
| Σ4 Finite index / heat count | Sharpened | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | `κ < ∞` ⇒ Lindelöf; RH ⇔ index `0`; `{0, ∞}` laws for tensor squares, regular extensions, mixing and Hecke-supported carriers [L]. Zero–one law for `κ` itself open (sub). |
| Σ5 Collision quantum / window integer | Reduced (to Π17) | RH | Index `0` ⇔ Wiener–Hopf invertibility ⇔ outer Szegő factorization [L]. |
| Σ6 Rank / degree uniformity | Partially solved | RH | Rank 7 strict, rank 8 PSD, strict rank-three reflected blocks; fixed Jensen degree eventually hyperbolic; PF₃₇ [L]. |
| Σ7 Window Markov capacity | Sharpened | RH | Fold capacity criterion [L]; end profile; exit charge to `1/7`; RH ⇔ `R ≤ ½` on the odd sector [L]. Barta criterion (balanced weight ⇒ Hecke-graph spectral radius `≤ 1`) and Picone ground-state transform give `Q ≥ (Ω_Γ − κ)‖H‖² + ∫VH² + pole` [L]; these certificates bound `|c_n(H)|` and are blind to the fold signs, which the first prime stage requires [L/D]. |
| Σ8 Realization | Sharpened | RH | RH ⇔ every window has an `ℓ²(zeros)` realization; none finite-dimensional; finite-rank realization of `K_ζ` forces infinitely many right zeros [L]. |
| Σ9 Explicit image / resolvent | Partially solved | RH in strip | Depth identity for `σ > 1`; theta–prime expression at `s = 4` [L]. |
| Σ10 Local signatures and gluing | Solved | — | `κ(φ_c) = κ + 1` at `∞` and every prime [L]. |
| Σ11 Product-formula gluing of the global pole | Classified | — | Local poles add squares; extremal weight = archimedean pole on `S`-units [L]. |
| Σ12 Running counterterm / star flux | Solved | — | `log N − γ` cancels the prime diagonal; each star pays `log d` [L]. |
| Σ13 Tensor amplification | No-go | — | `K_ζ^n` PD ⇔ RH; `n₋(G⊗G) = 2n₊n₋` [L]. |
| Σ14 Deformation to a positive model | No-go as free input | — | Crossing-free path ⇔ PD [L]. |
| Σ15 Separable assemblies | Classified (no-go) | — | Blind when truncated, non-convergent when untruncated [L]. |
| Σ16 Prime–pole coherence / packet identity | Solved (identity) | — | Complete form = jump + incidence − shell + diagonal + boundary [L]. |
| Σ17 Inter-tower coupling and the natural cone | Sharpened | RH | Bounded dense coupling ⇔ RH; coupling rate = zero width; damped cone ⇔ RH; undamped cone: bounded ⇒ RH or unattained width; finite stratum: bounded single-lattice coupling ⇒ RH; RvM-count exact-spline countermodels [L]. |
| Σ18 Exact SOS on a two-prime lattice | Open | RH | Generic Hecke orbit carries the full Hodge defect [L]; identities on `{∞,2}` aperture-specific [N]. |
| Σ19 Rank-one intertwining coefficient | Sharpened | RH | `κ_Hodge = #` band poles of `Λ(s)/Λ(s+1)`; rational level-four Weyl sum preserves every band zero as a pole [L]. |
| Σ20 Scheduled prime sums | Open | RH | Lower bounds for prime-scheduled energies (FU, CFC, RP, SZ, LI, FEL, EGC) [L receivers]. |
| Σ21 Extension / carrier | Classified | — | Escape, mixing, height decay ⇒ `κ ∈ {0, ∞}`; continuous-dilation carriers reading `1_H` iff `H ∈ {{0}, ℚ}` [L]. |
| Σ22 Lefschetz operators | Classified | — | Dilation HL trivial; overlap-flow HL on HR locus is RH [L]. |
| Σ23 Connected links | No-go | — | Links disconnected; coprime atoms couple only through the archimedean place [L]. |
| Σ24 Finite divisor | Solved | — | Coercive off `i/2` and a finite grid at every degree [L]. |
| Σ25 Semilocal and trace carriers | No-go | — | No `{∞,p}` positive carrier; exact `{∞,2}` trace through `½log 3` [L]. |
| Σ26 Approximation by RH-true objects | Classified | — | Closure class Laguerre–Pólya [L/D]. |
| Σ27 Window stages | Partially solved | sub (each stage); RH (all) | All real C² tests positive through total length `181/250·(1+6·10⁻⁷)`, floor `1/8000`; odd tests on `[−0.347, 0.347]` floor `1/100`; odd prime-free window by count; exit charge to `1/7` [L]. First prime stage: frozen form indefinite (C² test on `[−21/20,0]` with `Q₁ < 0 < Q`); on the unit window the frozen odd form is negative only along one cubic moment [L/W]; exact Tate horizon `log₂(1+2√2)` [L]. Second stage: fold graph = weighted path, `‖H‖² + 2αc₂ + 2βc₃ ≥ 0` ⇔ `α² + β ≤ 1` (sharp), arithmetic term `≤ 0.4505‖H‖²` [L]. No sign theorem on `[0.7243, log 3)` [N margins `1.5×10⁻⁵` odd, `5.6×10⁻⁸` even at half-width `½log 3`]. |
| Σ28 Window negativity budget | Sharpened | ≥qRH (exponent `< ½`); RH (subexponential) | Exact pole capacity `2sinh(A/2) − A`; floor `−(deg K_A + 2sinh(A/2) − A)‖H‖²`; negativity rate of two-bump tests = supremum of zero depths; window-energy abscissa = twice the maximal depth [L]. |
| Σ29 Low-frequency localization | Solved | — | Negativity only at the poles and below `τ₀(a) = 4exp(10 + 2e^{4a})` [L]. |
| Σ30 The stage step | Open | RH (as induction); each stage sub | Exact: `Q = Q_N − 2w_{N+1}c_H(log(N+1))`, the correlation on the left collar; ground-state identity `Q = Q_N − wE_φ + w∫φφ(Δ(H/φ))²` for every `φ > 0` [L]. Two-collar form: `S^N_ε ⪰ w_{N+1}(J + J*)` given interior positivity [D]. Lossy forms refuted: nonnegative collar loan and every cost-only payment fail on the first-stage frozen-negative test [L]. |
| Σ31 Positivity across the dimension-zero derivative | Classified | equivalent to Σ1 | Bare domination with the prescribed 1-jet ⇔ `Q(H) ≥ 0`, with an explicit prime-blind canonical family; no `αΓ + βpole` (nor Gamma-tilt + pole) dominates at any fixed `k > 0` across all windows; linear domination horizon on Riemann's kernel `≤ C·exp(−exp(A−2))`; shifted-pole weights pinched to `1/ζ(1+k)` and refuted for every real weight; domination holds on `[0, 0.7243]`, `0 ≤ k ≤ 1/160000` [L]. Survivors: Euler-product pole weight forced; Selberg `Λ₂` constraint on null tests; positivity lives on `Re k = 0` [L]. |
| Σ32 Prime-blind positivity | Sharpened | RH | Weil cone `{Λ}`; nonempty ⇔ PBAP; finite-level Farkas duality; node-critical (all prime powers needed, composites free); even sector: one prime plus the archimedean place on combinations blind at all other nodes; pole-free form on the primitive hyperplane; value function with gradient `(Λ, −1)`; moment region convex, above `q = −p` ⇔ RH; zero-side identity on blind tests; solved on nonnegative tests (measure `≤ log 2`, quantile transport) and on separated narrow-bump cones; pole floor `P(c) ≥ −(4mass + 6M)` [L]. |
| Σ33 Tate positivity horizon | Classified | — | `ρ_A(J_k) ⪰ 0` iff `2^k ≤ 1 + 2√2` (first prime stage), iff `((2^k−1)/(2√2))² + (3^k−1)/(2√3) ≤ 1` (second stage); `τ_H(k) ≥ (2 − exp(kN^kψ_{1/2}(N)))‖H‖²`; for every `k > 0` some window has `τ_H(k) < 0` (prime star, `Σ1/p = ∞`) [L]; numerically `k*(A) ≈ 1.66e^{−A/2}` [N]. |
| Σ34 Canonical-degree horizon | Classified | — | Every soft deformation that the counts pay unconditionally has horizon `≍ 1/deg K_A ≍ e^{−A/2}`: Tate dimension (Σ33), critical multiple (`K₀(A)`), floor (Σ28); the exact margin is doubly exponential (`μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})`; domination horizon `≤ C exp(−exp(A−2))`) [L/D]. |
| Σ35 Two-collar recursion | Open | identity | A closed causal evolution of the frozen two-collar form in the window length — the Krein/Gelfand–Levitan evolution of a translation-invariant kernel on growing intervals — with the prime powers entering as impulses `Λ(n)/√n` at `A = log n` [D]. Suzuki screw / Krein–Schur block machinery in RHTower is the nearest corpus carrier [L]. |
| Σ36 Rational Hecke-graph reading | Solved (identity) | — | Every finite `S ⊂ ℚ_{>0}` of spread `< A` is realized by bumps; the window arithmetic form on `S` is the Hecke operator of `ℤ[ℚ^×_{>0}]`; fold correlations count multiplicative pairs; negative graph form ⇒ negative window form [L]. |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (equivalence) | RH | `ψ(x) − x ≤ C√x log²x` ⇔ RH ⇔ `κ = 0`; Redheffer `det R_N = M(N)`, `Ω±(√N)` [L]. |
| Π2 Deciding input | Open | RH | No unconditional source input at square-root precision. |
| Π3 Producer cost | Partially solved | sub / RH | Multivariate parity producers reach `(1+ε)x + C_εlog²x`; individual producers slope `> 1`; integer-Chebyshev ceiling [L]. |
| Π4 Window precision (kernel = coupling) | Sharpened | RH | Weil's kernel is the smoothed prime error in multiplicative windows; coupling ≡ kernel [L/D]. |
| Π5 Conjugate diagonal (Hecke defect) | Sharpened | sub → ≥qRH → RH | Means `O_c(log U)` for `c < ½`; `o(log U)` ⇔ critical-scale clustering; one dyadic constant ⇔ RH [L]. |
| Π6 Averages versus all heights | Sharpened | — | Almost all unit windows zero-free at depth `(1+ε)log log T/log T`; right-half depth moment `o(V)`; Planck windows zero-free beyond `A/log V` outside `O(e^{−rA}/A)`; double-log stage with `O_c(V/log log V)` exceptions [L]. |
| Π7 Census / pair surplus | Partially solved | sub | Simple critical `≥ 0.67250071`; positivity-only certificates cannot reach `3/4` [L]. |
| Π8 Depth visibility | Partially solved | — | Isolated pairs visible at aperture `a` iff `S_δ(a) > (1/2π)log(ξ/2π)`; clusters detected: every zero of depth `≥ 1/a` and height `≤ exp(a/(10⁵A₀ log a)) − 306` has a smooth negative test in `[−(a+1), a+1]` (one-logarithm cluster-product horizon) [L]. |
| Π9 Exceptional moduli | Partially solved | sub | Uniform zero-free region and Siegel for `q ≤ (log x)^A` [L]. |
| Π10 Frequency localization | Solved | — | Every eventually positive cyclotomic band, the fixed first band included, has energy abscissa exactly `2Θ` [L]. |
| Π11a–e Cone, bidegree, fixed-rank, definite, Siegel counts | No-go | — | Excluded as independent sign producers; fakes `ℤ ⊕ yℤ`, `m² + 64n²` [L]. |
| Π11f Logarithmic duality of the split surface | Partially solved | sub | Pole plane: Abel completion, logarithmic RR; boost count laws [L]. Primitive part open. |
| Π11g Boost transform | Solved (identity) | — | `∫Z⁺(s,u)e^{2wu}du = K(s,w)ζ(s+w)ζ(s−w)` [L]. |
| Π11h Count-valued primitive `h¹` | Sharpened | RH; fixed length sub | Window `h¹` = primitive Künneth `h¹ = ½Q`; Weil's window form a signed count; odd prime-free window paid by a count; generic two-prime orbit `ℕ`-count criterion; fakes have none [L]. Missing: a count-valued inequality. |
| Π12 Subconvexity / heat floor | Partially solved | sub | `μ(½) ≤ 33/200`; heat floors `133/200`, `2/3 + ε` [L]. |
| Π13 Prefix scale | Solved | — | Strip zeros `Θ(N² log N)`; stabilization `Θ(√m)`; certificate prefix `Θ(√m + √(log m log S))` [L]. |
| Π14 Amplifier rank | No-go (finite support) | — | Growing losses keep radius `Be^λ` [L]. |
| Π15 Critical-scale residual sign | Classified | — | At the critical curve the residual is the prime-free aliasing term plus Weil's form [L]. |
| Π16 Genus function | Sharpened | indep. | Window genus `≥ (2−η)e^A` plus multiplicity excess; main term `2e^A`; atomic lattice of rank `⌊e^A⌋` [L]; upper law open. |
| Π17 Window energy | Sharpened | RH; ≥qRH (log stage) | `|𝒵(t)|²` over a reflection-closed window; abscissa = twice the maximal depth; right-edge flux never cancels against its functional-equation image; polynomial stage ⇔ RH; fixed degree `k` ⇔ `|β − ½| ≤ C/|γ|^k` [L]. |
| Π18 Finite realizations | No-go | — | No finite-dimensional window realization; no finite-rank realization of `K_ζ` [L]. |
| Π19 Mollified log-mean from moments | No-go | — | Holomorphic moments attain Jensen's `½log c`; integer exponential moments do not determine the log-mean [L]. |
| Π20 Count identities and cost-only payments at the first prime | No-go | — | No identity `Q = J_∞ + Φ + Σ_{i<k}ℓ_i²` with `Φ` vanishing on fold-free tests for `log 2 ≤ A < 2log 2`; nonnegative frozen collar loan refuted (`Q₁ < 0 < Q`) [L]. Survivor: the signed fold is the source of positivity. |
| Π21 Exact balance (no slack) | Classified | — | Weil cone `{Λ}` or empty; restricted ground energy `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})` [L]; near-null tests interpolate the zeros below the Landau height [N/D]. |
| Π22 Near-line density ladder | Sharpened | sub | Eight equivalent forms; almost-all log-stage certificates ⇔ log-free occupancy `D_win`; `D_zero ⇒ D_win ∧` log-mean law; occupancy and horizontal moment incomparable on generic density data [L]. |
| Π23 Inner caps | Open | RH (all degrees); ≥qRH (fixed degree) | Cauchy caps cancel the right-port flux down to `σ_m = 1 − 1/(116log(m+5))` [L]; the caps `[½, σ_m]` are the zero-free-region problem. |
| Π24 Parity at dimension zero | Classified | — | `J_k = Σ_j k^jΛ_j/j!`, `Λ_j ≥ 0` vanishing for `ω(n) > j`; jet operators generated by the position `M` and `ρ_A(Λ)` (`ρ_A(Λ_{j+1}) = [M, ρ_A(Λ_j)] + ρ_A(Λ)ρ_A(Λ_j)`); the wall `k ↦ −k` is Dirichlet inversion (`μ` on squarefree); sign `(−1)^{ω(n)}` in negative dimension; null tests carry the Selberg constraint `∂²A ≥ 2⟨ρ_A(Λ₂)H,H⟩` [L]. Sieve-accessible jets carry no arithmetic beyond `Λ`; transporting their positivity to `Λ` requires inverting `[M, ·]`, which preserves no sign. |
| Π25 Euler-product pinning | Classified | — | Any dominating shifted-pole weight equals `1/ζ(1+k) < k`; `4ξ(1+k)² < kζ(1+k)` refutes it [L]. Domination in positive dimension is forced onto an arithmetic (Euler-product) weight. |

## Γ — selection and reflection

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point | Open | RH | `Θ ≥ ½`, Haar-a.e. `½`, Baire-generic `1` with Haar-null level set; RH ⇔ trivial point typical [L]. |
| Γ2 Prime-set flips | Solved | — | Every nontrivial prime pattern separated at every density [L]. |
| Γ3 Twin-blindness of soft structure | No-go | — | Krein index invariant under unitary twists [L]. |
| Γ4 Frobenius at infinity | Sharpened | RH | `σ(ρ) = 1 − ρ̄`; RH ⇔ `σ` trivial ⇔ Hecke similitude ⇔ partner saturation [L]. `σ_A` = Rosati involution of the window algebra, multiplier `e^{−(s−½)A}` unitary exactly on `Re s = ½` [L]; Lewis adjoint `I_s† = I_{1/2−s̄}`; `U_LP` bridge, defect of a window lift = window Frobenius defect [L]. |
| Γ5 Source identification / pre-divisor | Partially solved | RH | Pre-divisor sections need zero-independent forcing [L]. |
| Γ6 Boundary sign / coherence | Solved | — | Pole boundary sign separates ζ from size-equivalent twins [L]. |
| Γ7 Affine carrier with Weil dilation | Solved | — | Gluing at a place; subgroup classification [L]. |
| Γ8 Poisson rigidity | Sharpened | RH | Zero-side positivity = RH; on prime-blind decay-class tests arch + pole = `Re Σ_ρ m_ρF̂(γ_ρ)conj F̂(γ̄_ρ)` [L]. |
| Γ9 Archimedean continuity vs height decay | No-go | — | ⇒ `κ = ∞` [L]. |
| Γ10 Function-field indistinguishability | Sharpened | — | Local walls identical over `𝔽_q(X)`; first-order count law identical over `ℤ` and `𝔽_q[T]` [L]. Pure-curve families are sums of squares at every resolution weighted by Hurwitz forms of the Frobenius angles; over `ℤ` a twist frequency `u` contributes the Hurwitz form an angle `u` contributes over `𝔽_q`; the untwisted direction is the trivial angle [L]. |
| Γ11 Pole-blindness of the glue | No-go | — | Simple pole absorbed [L]. |
| Γ12 General gauges | Solved | sub | Harmonic saturation only at the Euler gauge [L]. |
| Γ13 Source-uniform extinction | No-go | — | Fails at `3/4 + i` [L]. |
| Γ14 Local counterterm selection | No-go | — | Flip twin glued index `1` [L]. |
| Γ15 Functional-equation twins | Partially solved | sub | Degree three and positive degree two admit off-line real zeros [L]. |
| Γ16 Selection–sign gap | Sharpened | RH | Every selector is a margin, index, counterterm or identity on a partial form; none gives the sign [L]. |
| Γ17 Scattering recentering | Classified (no-go) | — | Rational/algebraic maps real on the critical parabola are constant / horizontal [L]. |
| Γ18 Divisor-identity selection | Solved | — | Only `Λ` degenerates completely [L]. |
| Γ19 Correspondence algebra over `ℤ` | Sharpened | RH | Rosati positivity ⇔ orbit Hodge index ⇔ naive height at bounded distance [L]. |
| Γ20 Window selection | Classified | — | A window of length `A` does not see `p > e^A`; a flip twin identical on all length-`A` tests is not Weil positive [L]. |
| Γ21 Density selection on the natural cone | No-go | — | Exact spline divisors with the full RvM count, bounded undamped coupling and unattained width [L]. |
| Γ22 Contractive scattering positivity | No-go | — | Blaschke pairs keep every Schur inequality while placing zeros anywhere in `Re s > ½` [L]. |
| Γ23 Weil cone uniqueness | Solved | — | Every real weight with full Weil positivity equals `Λ` on `n ≥ 2`; every certificate `(β, w)` has `β = 1`, `w = Λ` [L]. |
| Γ24 Mayer reflection positivity | Sharpened | RH | Resonance ⇔ `ζ(2s) = 0`; `Z_PM` = Hardy's `Z`; `D_s ≤ 0`, `= 0` iff `Re s = ¼`; `I_s` bounded iff `Re s = ¼`; Krein positivity ⇔ RH; finite dyadic cusp energy ⇔ resonance; `D_s < 0` off `Re s = ¼` at nonresonant Eisenstein points [L]. Open: finite cusp energy ⇒ `D_s = 0`. |
| Γ25 Two reflection centres | No-go (as operator symmetry) | — | Transfer structure reflects about `Re w = 1`, zeta events about `Re w = ½` [P]. Survivor: explicit factor `ζ(1+w)/ζ(2−w)`. |
| Γ26 Resonant-state selectors | No-go | — | Fixed-`s` inversion fixes every resonant period; three-term + inversion invariance holds off the line; Krein self-adjointness gives negative-norm states; cutoff Grams, Hecke residual gaps, height laws retain the rate [L]. |
| Γ27 Tate counts as a selector | No-go | — | `ζ(s)ζ(s−ε)` is Tate positive in every real `k ≥ 0` and its dimension-zero derivative `Λ(1 + n^ε)` is not Weil positive: Tate positivity does not descend [L]. |
| Γ28 Frobenius inside the window algebra | No-go | — | If `ρ_A(f)` is a `Q`-similitude with factor `λ`, then `λ = f(1)²` and `f(n) = 0` for `2 ≤ n < e^A`; `Q`-isometries `±1`; reflection centralizer scalar; socle principal iff `N ≤ 2` [L]. Survivor: Frobenius must change the window; `T_p − Id` realizes `√pH(· + log p)` into `A + log p` and scales complete Weil energy by `p` [L]. |
| Γ29 Linear Serre–Krein identification | No-go | — | Positive reflection-odd window tests versus the nonpositive odd Krein eigenspace: no real-linear isometry intertwines window Serre duality with the PM Krein reflection [L]. Survivor: complete Weil energy = limit of twice real Krein squares of finite core sums with conjugation and exponential twist [L]. |
| Γ30 Completed Tate family | Classified | — | `‖Λ(½+it−k/2)/Λ(½+it+k/2)‖ = 1` for all real `k, t`; archimedean and arithmetic Tate families are exact inverses in modulus on the line: domination for the completed family is the functional equation, an identity [L]. |
| Γ31 Degeneration type over `𝔽_q` | Solved (calibration) | — | Pure curves degenerate completely under dilation; the golden fake has `W ≥ cwe^{εw}` and one fixed negative square at every width [L]. Selection by monodromy type, without positivity. |

## Bridges

| Bridge | Anchor |
|---|---|
| `κ(K_ζ)` = right zeros = `sup_A ι(A)` = band poles of `Λ(s)/Λ(s+1)` = upper-right Mayer resonances = `2κ₋` of the Mayer Krein space; even; RH ⇔ `κ < 2` | HKT, RIT, CWS, AOG [L] |
| Window algebra = truncated Dirichlet λ-ring; `ρ_A(Λ) = [M, log Z]`; plethystic exponential; prime powers of `A` = primes of `A/a` | WTZ [L] |
| Weil's window form = dimension-zero jet of the Tate family = signed count; positive dimension classified | WTZ, DZG, ATD [L] |
| Window arithmetic = Hecke operator of `ℤ[ℚ^×_{>0}]` on finite configurations; horizons = graph thresholds | WTZ [L] |
| Stage step = one collar-to-collar correlation; two-collar block form | WTZ, DZG [L]; [D] |
| Fold capacity ⇔ window sign ⇔ odd-sector Markov capacity ⇔ Barta/Picone ground states | CWS, CHMD, WTZ [L] |
| Two-bump negativity rate = maximal depth = ½ window-energy abscissa; canonical degree sets every soft horizon | SRT, CDG, WTZ, AHD [L]; [D] |
| Window involution = Rosati ↔ Lewis adjoint via `U_LP`; Frobenius defect ↔ co-isometry defect; window Frobenius = translation into the next window | WTZ, RIT [L] |
| Weil cone `⊆ {Λ}`; nonempty ⇔ prime-blind positivity; node criticality; zero-side identity | RHTower [L] |
| Near-line density: eight forms; occupancy ⇔ almost-all certificates | CDG [L] |
| Complete family at the critical curve = Weil on untwisted windows + positive counts (Ramanujan, periodic, frequency, character) | AHD [L/W] |
| Frobenius angle over `𝔽_q` ≡ twist frequency over `ℤ`; untwisted window ≡ trivial angle | AHD [L] |
| One cyclotomic mode of the Chebyshev error carries `2Θ` | CAF [L] |
| Gaussian-damped two-prime cone coupling bounded ⇔ RH; undamped bounded ⇒ RH or unattained width | ACPL [L] |
| Gluing `κ(φ_c) = κ + 1`; Redheffer `det = M(N)`; graded/top Möbius pair | AKG, ADT, HWV [L] |

## Status counts

| Family | Solved | Partially solved | Sharpened | Open | No-go | Classified | Reduced |
|---|---|---|---|---|---|---|---|
| Σ (50) | 10 (Σ1a, Σ1b, Σ1c, Σ1h, Σ10, Σ12, Σ16, Σ24, Σ29, Σ36) | 9 (Σ1d, Σ1e, Σ1g, Σ1j, Σ1l, Σ3, Σ6, Σ9, Σ27) | 10 (Σ1, Σ2, Σ3a, Σ4, Σ7, Σ8, Σ17, Σ19, Σ28, Σ32) | 4 (Σ18, Σ20, Σ30, Σ35) | 5 (Σ1f, Σ13, Σ14, Σ23, Σ25) | 11 (Σ1i, Σ1k, Σ1m, Σ11, Σ15, Σ21, Σ22, Σ26, Σ31, Σ33, Σ34) | 1 (Σ5 → Π17) |
| Π (32) | 4 (Π1, Π10, Π11g, Π13) | 6 (Π3, Π7, Π8, Π9, Π11f, Π12) | 7 (Π4, Π5, Π6, Π11h, Π16, Π17, Π22) | 2 (Π2, Π23) | 9 (Π11a–e, Π14, Π18, Π19, Π20) | 4 (Π15, Π21, Π24, Π25) | — |
| Γ (31) | 7 (Γ2, Γ6, Γ7, Γ12, Γ18, Γ23, Γ31) | 2 (Γ5, Γ15) | 6 (Γ4, Γ8, Γ10, Γ16, Γ19, Γ24) | 1 (Γ1) | 12 (Γ3, Γ9, Γ11, Γ13, Γ14, Γ21, Γ22, Γ25, Γ26, Γ27, Γ28, Γ29) | 3 (Γ17, Γ20, Γ30) | — |

Strength of the open walls:
- **RH:** Σ1, Σ2, Σ3a, Σ6, Σ7, Σ8, Σ17, Σ18, Σ19, Σ20, Σ27 (all stages), Σ28 (subexponential), Σ30, Σ32,
  Π2, Π4, Π11h, Π17 (polynomial stage), Π23 (all degrees), Γ1, Γ4, Γ5, Γ8, Γ16, Γ19, Γ24.
- **≥qRH:** Σ4 (`K_ζ`), Σ28 (exponent `< ½`), Π5 (fixed scale), Π17 (log stage), Π23 (fixed degree).
- **sub:** Σ1d, Σ1e, Σ1g, Σ1j, Σ1l, Σ4 (zero–one law), Σ27 (each stage), Σ30 (each stage), Π3, Π5
  (mean `o(log U)`), Π7, Π9, Π11f, Π11h (fixed length), Π12, Π22, Γ15.
- **identity:** Σ35.
- **indep.:** Π16.
