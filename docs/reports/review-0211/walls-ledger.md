# Walls ledger — status quo

Three wall families block every route: **Σ** the critical sign, **Π** precision and production,
**Γ** selection of ζ. All three read one even integer, `κ = κ(K_ζ) = #` distinct zeros right of the
critical line, and all three are read on one object: the **window tower** `A ↦ (window of length
A)`, with `κ = sup_A ι(A)`.

- **Σ is Weil's sign on window tests, uniformly in the window length.** On a window `[−A, 0]` Weil's
  form is an explicit finite-type object: the archimedean constant `Ω(0) < 0`, the Lévy jump energy of
  the Gamma factor, one fold for each prime power `n ≤ e^A`, and the pole product `2Ĥ(0)Ĥ(1)`. In
  signed form
  `Q(H) = Ω(0)‖H‖² + J_∞(H) + Σ_{n≤e^A}(Λ(n)/√n)(½fold_n(H) − sym_n(H)) + ½⟨c,H⟩² − ½⟨s,H⟩²`:
  the symmetric fold masses `sym_n` are the only negative arithmetic terms. Every window is a finite
  problem (Shannon-bounded index, negativity confined below an archimedean frequency horizon); RH is
  the sign at every length. In the complete atomic family all directions except the untwisted
  horizon windows are point counts (Tate pieces); the untwisted horizon windows carry Weil's window
  form.
- **Π is the size and the production of the window form.** Size: the negativity of a window of
  length `A` is at most its canonical degree `deg K_A = 2ψ_{1/2}(e^A) − Ω(0)` plus the pole capacity —
  the scale `e^{A/2}` of the trivial zero-free strip; any smaller exponent is a zero-free strip, and
  subexponential growth is RH [D]. The classical faces remain: the one-point windowed prime error,
  windowed zero power sums, the conjugate diagonal, the signed pair surplus beyond bandwidth one, the
  mollified log-mean. Production: a count equal to the primitive window `h¹`; the Künneth counts pay
  all of a window except `½Q(H)`; no finite-dimensional or finite-rank object can carry it, so the
  producer is a tower of rank `≈ 2e^A`.
- **Γ is closed for every prime-set flip at every density and open as a law in `A`.** No window of
  bounded length, no zero-density law and no contractive scattering positivity selects ζ. What
  remains is Frobenius at infinity — the reflection `ρ ↔ 1 − ρ̄` acting as a positivity — read by
  `Λ(s)/Λ(s+1)`, by Rosati positivity, and on a window by the involution `σ_A`, whose multiplier
  `e^{−(s−½)A}` is unitary exactly on the critical line.

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact
form a theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a
classification or identification theorem), **Reduced** (theorem-level equivalent of the wall named).
Strength: **RH**, **≥qRH** (zero-free half-plane and Lindelöf), **LH**, **sub**, **indep.**
Evidence: `[L]` integrated Lean; `[S]` working tree or not wired into its umbrella; `[P]` paper proof;
`[D]` derived here from Lean statements. Window lengths `A`; half-widths `a = A/2`.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign on window tests | Sharpened | RH | RH ⇔ `Q ≥ 0` on every window test of every length (CWS `riemannHypothesis_iff_windowForm_nonneg`, AHD `riemannHypothesis_iff_halfWeight_nonneg`) ⇔ every window index `ι(A) = 0` ⇔ `ι(A) < 2` ∀A ⇔ horizon blocks eventually `≥ −ε` past the critical curve ⇔ pole-hyperplane positivity on the single Beurling schedule `2L(log L)²` ⇔ positivity at every fixed `K·c*` [L]. `ι(A)` monotone, `0` for `A ≤ 3/5`, finite with `ι(A) ≤ ⌊1 + 2A·T(A/2)/π⌋`, `sup_A ι(A) = #` right zeros [L]. Locality: a window of length `A` reads `Λ(n)` for `n ≤ e^A` only [L]. Ceiling `μ(A) ≤ K exp((11/2)A − πe^{2(A−2)})` for the restricted ground minimum; any `≤ r` prime towers cross zero by aperture `2 log(r+2) + 11` [L]. |
| Σ1a Critical overlap and receivers | Solved | — | Denjoy–Carleman `c*_N ≍ L(log L)²`, margin `1/log N`; tilted-spline receiver at every `K(log N)^{1/8}`; unit-bump receiver at every positive-power rate; one smooth Beurling profile realizes every finite rational Gram at `2L(log L)²` [L]. |
| Σ1b Rough regime, tilted spline | Partially solved | sub | All vectors `1 ≤ c ≤ (log N)^α`, `α < 1/9` [L]. Below `1/8` [L]: fixed and polylog packets; growing subthreshold block Jordan; polynomial-conductor complement floor `c_orth log N/c⁷`, nonpositive subspaces of dimension `≤ ⌊N^θ⌋`; far reserve; mid-band `α < 1/4`; coherent jet–pole cancellation; near-Gram forms cost their divisor mean; prime-only band `√N < p ≤ N^θ` = diagonal + rank `≤ 2`, floor `(1−θ)/4`. Open: band–far cross and threshold block `e ≍ c`. Under ¬RH the edge lies in `[(log N)^α, 2(log N)^β]` infinitely often, `α < 1/9`, `β > 1/8` [L]. |
| Σ1c Joint shell–pole payment | Open | sub | Separate shell payment costs `c⁹` at `ε = c⁻⁷`; joint top-band coefficient `O_φ(G(c + log N))`; terminal support gives linear high-conductor loss [L/S]; prime-successor comparison unproved. |
| Σ1d General profiles | Partially solved | sub | Every nonzero compact C² profile [L]: conductor floors; universal rate `a e^{−Bc}` on polynomial spans `θ < 1/1080` for `c ≤ b log log N`; subpolynomial spans with floor `(log N)^{−η}/4` up to a super-log-log clock; almost-polynomial spans past every fixed log-log multiple. Full space past `log log N` open. |
| Σ1e Square-root conductor barrier | Open | sub | Frames and residual averages need `m² ≤ N`; above `√N` an Elliott–Halberstam-type input; prime conductors above `√N` have disjoint spikes and lower frame bounds [L]. |
| Σ1f Defect-only confinement | No-go | — | `Q < 2^k` witnesses [L]. |
| Σ1g Haar / Gamma graph | Partially solved | sub | All-detail prime–pole cancellation `O(exp(−√log Y/92160000))` in original cell masses; index `≤ R + A`; growing Euler heads unbounded [L]. Joint non-arithmetic Gamma graph + signed diagonal + poles open. |
| Σ1h Rough regime, smooth profiles | Solved (to `ε₀·c*`) | sub | Logarithmic profile positive to `ε₀L(log L)²`, budget sharp [L]. |
| Σ1i Second order on horizon blocks | Classified | — | For every profile with `s^βE₁(s) → J`: `c⁻¹⟨Wx,x⟩ → κQ(H) + (βJ/K)∫e^{−(β+1)y}H²` along `c^{β+1}/log N → K`; aliasing = dilation derivative of the bulk; tilted spline `7J(1)/K` [L]. |
| Σ1j Tate decomposition of the complete family | Partially solved | sub | Tate pieces [L]: bulk packets (`#ℙ⁷(ℤ/m)`, zero-blind); windows twisted by any mean-zero periodic weight are zero-blind, positive at every resolution up to `O(N⁻²)`, coercive `a log N/c⁸`, second order `≥ a/K`; conductor-two window second order `= 7J(2)/K·∫e^{−8y}H²`, `J(2) = 255J(1)`, no Weil term [S]. Non-Tate piece: untwisted windows = Weil's form. Open: general conductors `m`, untwisted–twisted and bulk–horizon cross-terms, growing twists, horizon localization on the full space. |
| Σ1k Phase diagram `(A, K)` | Partially solved | sub | Pencil `κQ(H) + c∫e^{−py}H² ≥ 0` for `c ≥ κ·windowFloor(A)` [S]: at multiple `K` all windows with `κ·windowFloor(A) ≤ βJ/K` are positive; every negative window has `K*(H) ≥ βJ/(κ·windowFloor(A))`. Window index of the pencil monotone in `K`, equal to Weil's index for large `K`, never above the right-zero count [L]. Which configurations one fixed `K` excludes on long windows is open (dense clusters of depth `≳ 1/log K`). RH sits in `K → ∞` and `A → ∞`. |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | HR ∧ HL ⇔ strict HR; RH ⇔ HL on the PSD locus of the overlap flow; finite first edge is PSD with a zero mode [L]. |
| Σ3 Stars and dilation monodromy | Partially solved | — / RH | Stars isometric, positivity descends, depth law; monodromy `c_m(gn) = (φ(m)/φ(m/(m,g)))c_{m/(m,g)}(n)`, eventually idempotent; Jordan coefficient a point count; tensor law CRT [L]. |
| Σ3a Coprime stratum | Sharpened | RH | gcd stratification; graded/top Möbius pair; conductor Gram PSD at every `2K(log N)^{1/8}` ⇔ RH; Redheffer `det = M(N)` [L]. |
| Σ4 Finite index / heat count | Sharpened | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | `κ < ∞` ⇔ bounded heat counts ⇒ `Θ < 1`; no softening at any resolution [L]. |
| Σ5 Collision quantum / window integer | Reduced (to Π17) | RH | Index `0` ⇔ Wiener–Hopf invertibility ⇔ outer Szegő factorization; cepstrum a positive Bessel transform of `|𝒵(t)|²`; every certificate = exact multiplier × Carathéodory factor [L]. |
| Σ6 Rank / degree uniformity | Partially solved | RH | Rank 7 strict, rank 8 PSD; fixed Jensen degree eventually hyperbolic; PF₃₇ [L]. |
| Σ7 Window Markov capacity | Sharpened | RH | RH ⇔ `R ≤ ½` on odd vectors; `W = V_N‖g‖² + J(g) + ½⟨c,g⟩² − ½⟨s,g⟩²`; on a window only `n ≤ e^A` jump and departing jumps pay their creation [L]. Signed folds: negative terms are `Ω(0)`, `sym_n` and the odd pole square [L]. Pointwise calibrated folded-Markov payment fails past the plastic root (corner ceilings `8(√2−1)`, `3(√3−1) < 4`); variable-hub Schur squares and `T₂`-stick elimination survive [L]: payment is nonlocal. |
| Σ8 Realization | Sharpened | RH | RH ⇔ every window has an `ℓ²(zeros)` realization; no window realization is finite-dimensional (short windows coercive) [L]; a finite-rank realization of `K_ζ` forces infinitely many right zeros [S]; lossless realization needs infinitely many resonances [L]. A realization is a tower of unbounded rank. |
| Σ9 Explicit image / resolvent | Partially solved | RH in strip | Depth identity for `σ > 1`; theta–prime expression at `s = 4` [L]. |
| Σ10 Local signatures and gluing | Solved | — | `κ(φ_c) = κ + 1` at `∞` and every prime; two primes carry the full affine index [L]. |
| Σ11 Product-formula gluing of the global pole | Classified | — | Local poles add squares; extremal weight = archimedean pole on `S`-units [L]. |
| Σ12 Running counterterm / star flux | Solved | — | `log N − γ` cancels the prime diagonal; each star pays `log d` [L]. |
| Σ13 Tensor amplification | No-go | — | `K_ζ^n` PD ⇔ RH; `n₋(G⊗G) = 2n₊n₋` [L]. |
| Σ14 Deformation to a positive model | No-go as free input | — | Crossing-free path ⇔ PD; Kähler transport free [L]. |
| Σ15 Separable assemblies | Classified (no-go) | — | Blind when truncated, non-convergent when untruncated [L]. |
| Σ16 Prime–pole coherence / packet identity | Solved (identity) | — | Complete form = jump squares + incidence squares + diagonal − shell degree + boundary [L]. |
| Σ17 Inter-tower coupling and the natural cone | Sharpened | RH | Coupling ≡ kernel; bounded coupling on one dense `⟨p⟩×⟨q⟩` ⇔ RH [L]. Natural cone with a fixed Gaussian damping `exp(τ(ρ−½)²)`: coupling rate `σ` ⇔ width `≤ σ`; bounded damped `ℕ²` coupling ⇔ RH, no attainment assumption [L]. Undamped: RH or polynomial repulsion [L]; exact spline divisors with full RvM count, bounded undamped coupling and unattained width [S]. Open: the prime-side bound for the damped coupling. |
| Σ18 Exact SOS on a two-prime lattice | Open | RH | Hecke orbit of one generic test under `ℤ log p + ℤ log q` carries the full Hodge defect [L]; no SOS identity. |
| Σ19 Rank-one intertwining coefficient | Open | RH | `κ_Hodge = #` band poles of `Λ(s)/Λ(s+1)` in `−½ < Re s < 0` [L]; Mayer boundary `2ζ(s)/ζ(s+1)` with slope weights `(1 − 1/n)Λ(n)`, classical zero-free region [L]; scattering coefficient of `SL₂(ℤ)` [L/D]; contractive positivity blind (Γ22). |
| Σ20 Scheduled prime sums | Open | RH | Lower bounds for prime-scheduled energies (FU, CFC, RP, SZ, LI, FEL, EGC) [L receivers]. |
| Σ21 Extension / carrier | Classified | — | Escape, mixing, height decay ⇒ `κ ∈ {0, ∞}`; continuous-dilation carriers reading `1_H` iff `H ∈ {{0}, ℚ}` [L]. |
| Σ22 Lefschetz operators | Classified | — | Dilation HL trivial; overlap-flow HL on HR locus is RH; coupling Laplacian HL with base point the zero form [L]. |
| Σ23 Connected links | No-go | — | Links disconnected; coprime atoms couple only through the archimedean place [L]. |
| Σ24 Finite divisor | Solved | — | Coercive off `i/2` and a finite grid at every degree [L]. |
| Σ25 Semilocal and trace carriers | No-go | — | No `{∞,p}` positive carrier; `1 − P − P̂` indefinite; exact `{∞,2}` trace through `½ log 3` [L]. |
| Σ26 Approximation by RH-true objects | Classified | — | Closure class Laguerre–Pólya [L/D]. |
| Σ27 Window stages | Open | sub (each stage); RH (all) | Stage `n`: `log n ≤ A < log(n+1)` [L]. Prime-free stage `A < log 2`: `Q = Ω(0)‖H‖² + J_∞ + pole` (pole `= 2Ĥ(0)Ĥ(1)` [D]), a statement about the Gamma factor alone; all-test positivity proved only to `A = 3/5` [L]; the jump count pays it only to `A = 1/1000` [L]. First-fold stage: one fold `T₂`, `Q = Ω(0)‖H‖² + J_∞ + (log 2/√2)(½fold₂ − sym₂) + pole` [L]; positivity on odd tests to `0.724` and on `cosh`-orthogonal tests to `log 2 + 1/50` [L]. No count for `sym₂`. |
| Σ28 Window negativity budget | Sharpened | ≥qRH (exponent) ; RH (subexponential) | `Q ≥ −(deg K_A + 2A sinh²(A/2))‖H‖²` [S]; `deg K_A = 2ψ_{1/2}(e^A) − Ω(0) ≈ 4e^{A/2}`; exact pole term `2Ĥ(0)Ĥ(1)` with `|Ĥ(0)Ĥ(1)| ≤ Ae^{A/2}‖H‖²` [D]. An off-line pair of depth `δ` contributes at most `e^{δA}`: the budget `e^{A/2}` is the trivial strip; a smaller exponent on visible windows is a zero-free strip; subexponential growth is RH [D]. |
| Σ29 Low-frequency localization | Solved (localization) | — | On tests supported in `[−a, a]` the localized symbol `ν = μ + P_{e^{2a}}` is `≥ 0` beyond `τ₀(a) = 4exp(10 + 2e^{4a})`; `Q(f) ≥ −2|f̂(i/2)||f̂(−i/2)| − M_a·sup_{|τ|≤τ₀}|f̂|² + (positive)` [L]. Window negativity lives at the poles and in a finite frequency band. |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (equivalence) | RH | `ψ(x) − x ≤ C√x log²x` ⇔ RH ⇔ `κ = 0`; Redheffer `det R_N = M(N)` = nerve Euler characteristic, `Ω±(√N)` [L]. The canonical class of a window is the half-weighted Chebyshev profile, `deg k_A = 2∫_0^A ψ_{1/2}(e^t)dt` [L]. |
| Π2 Deciding input | Open | RH | No unconditional source input at square-root precision. |
| Π3 Producer cost | Partially solved | sub / RH | Multivariate parity producers reach `(1+ε)x + C_ε log²x`; individual producers have slope `> 1`; integer-Chebyshev ceiling `exp(−0.87n)` [L]. |
| Π4 Window precision (kernel = coupling) | Sharpened | RH | Weil's kernel is the smoothed prime error in fixed-length multiplicative windows; coupling ≡ kernel; the Gaussian-damped coupling is its heat-smoothed form [L/D]. |
| Π5 Conjugate diagonal (Hecke defect) | Sharpened | sub → ≥qRH → RH | Means `O_c(log U)` for `c < ½`; density TFAE to `2/3`; rate `r < 1`; `o(log U)` ⇔ critical-scale clustering; one dyadic constant ⇔ RH [L]. |
| Π6 Averages versus all heights | Sharpened | — | Almost all unit windows zero-free at depth `(1+ε) log log T/log T`; right-half depth moment `o(V)` [L]. |
| Π7 Census / pair surplus | Partially solved | sub / LH | Simple critical `≥ 0.67250071` [L]. Positivity-only certificates (shift inequalities, nonnegative majorants, Fejér kernels, `F = α` on `[0,1]`, `F ≥ 0`, `p ≥ 0`, lower bounds beyond `1`) cannot reach `3/4`: a GUE-plus-spike model has `I > 1/9`; best positivity bound in `[1/18 + 47/750, 8/27]` [L]. Needs signed arithmetic information beyond bandwidth one. |
| Π8 Depth visibility | Sharpened | — | Isolated pairs visible at aperture `a` iff `S_δ(a) > (1/2π)log(ξ/2π)`; clusters not excluded [L/D]. |
| Π9 Exceptional moduli | Partially solved | sub | Uniform zero-free region and Siegel for `q ≤ (log x)^A` [L]. |
| Π10 Frequency localization | Sharpened | ≥qRH; RH | Every band `K = ⌈N^δ⌉` retains `2Θ` [L]. |
| Π11a–e Cone, bidegree, fixed-rank, definite, Siegel counts | No-go | — | Excluded as independent sign producers; fakes `ℤ ⊕ yℤ`, `m² + 64n²` [L]. |
| Π11f Logarithmic duality of the split surface | Open | sub | Isotropic count `Γ(σ)(2π)^{−σ}ζ(σ)²`, no weak FE pair [L]. |
| Π11g Boost transform | Solved (identity) | — | `∫Z⁺(s,u)e^{2wu}du = K(s,w)ζ(s+w)ζ(s−w)` [L]. |
| Π11h Count-valued primitive `h¹` | Open (solved at small length) | RH | Künneth RR; Hecke similitudes; window `h¹` = primitive Künneth `h¹ = ½Q(H)`, Künneth part `h¹_K > 0` a product of counts [S]; Lévy jump count pays primitive `h¹` to window length `1/1000` [L]; windowed Tate law: naive height at bounded distance from the window Rosati form ⇔ its sign; windows `≤ 3/5` have naive heights [S]; one spectrally generic orbit: RH ⇔ `ℕ`-valued count height on `ℤ[p^ℤq^ℤ]`; golden and complex fakes have none [L]. Flooring a nonnegative form is circular. Missing: an independent count for the symmetric fold masses. |
| Π12 Subconvexity / heat floor | Partially solved | sub | `μ(½) ≤ 33/200`; heat floors `133/200`, `2/3 + ε` [L]. |
| Π13 Prefix scale of quantized readings | Solved | — | Strip zeros `Θ(N² log N)`; artifact-free prefix `≥ c√T`; stabilization `Θ(√m)`; certificate prefix `Θ(√m + √(log m log S))` [L]. |
| Π14 Amplifier rank | No-go (finite support) | — | Growing losses keep radius `Be^λ` [L]. |
| Π15 Critical-scale residual sign | Classified | — | Margin `1/log N`; literal prime residual `(log Q)²/log N`; at the critical curve the residual is the prime-free aliasing term plus Weil's form [L]. |
| Π16 Genus function | Sharpened | indep. | Window genus `≥ (2 − η)e^A` plus multiplicity excess; main term `2e^A` = Young conjugate of the zero density = theta count of `Spec ℤ` [L/S]; genus law `≤ (2 + η)e^A` open. |
| Π17 Window energy | Sharpened | RH; ≥qRH (log stage) | `|𝒵(t)|²` over a reflection-closed window; abscissa = twice the maximal depth; certificate depends only on `|𝒵(t)|²`; log stage ⇔ inverse-log corridor; polynomial stage ⇔ RH [L]. The window length `A` of CWS and the time `t` of `𝒵(t)` read the same exponential `e^{(s−½)·}` [D]. |
| Π18 Finite realizations | No-go | — | No finite-dimensional window realization for `A > 0`; finite-rank realization of `K_ζ` ⇒ infinitely many right zeros; under RH none [L/S]. Producers are towers of unbounded rank (window genus `2e^A`). |
| Π19 Mollified log-mean from moments | No-go | — | Holomorphic moments with the mean square attain Jensen's `½ log c`; integer exponential moments do not determine the log-mean [L]. WD's analytic block needs distributional input. |

## Γ — selection

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point | Open | RH | `Θ ≥ ½`, Haar-a.e. `½`; RH ⇔ trivial point typical [L]. |
| Γ2 Prime-set flips | Solved | — | Every nontrivial prime pattern separated at every density; finite flip sets have exact resolution thresholds; every flip leaves an indefinite residue while `F_Λ = 0` [L]. |
| Γ3 Twin-blindness of soft structure | No-go (complete) | — | Krein index invariant under unitary twists [L]. |
| Γ4 Frobenius at infinity | Open | RH | `σ(ρ) = 1 − ρ̄`; RH ⇔ `σ` trivial ⇔ Hecke similitude ⇔ partner saturation [L]. Window form: `(σ_AH)^(s) = e^{−(s−½)A}Ĥ(1−s)`; multiplier unitary exactly on `Re s = ½`; pair products `Ĥ(s)Ĥ(1−s)` invariant, so `σ_A` is an isometry on every datum and orients nothing by itself [S]. |
| Γ5 Source identification / pre-divisor | Partially solved | RH | Pre-divisor sections need zero-independent forcing [L]. |
| Γ6 Boundary sign / coherence | Solved | — | Pole boundary sign separates ζ from size-equivalent twins [L]. |
| Γ7 Affine carrier with Weil dilation | Solved | — | Gluing at a place; subgroup classification [L]. |
| Γ8 Poisson rigidity | Sharpened | RH | Zero-side positivity = RH [S]. |
| Γ9 Archimedean continuity vs height decay | No-go | — | ⇒ `κ = ∞` [L]. |
| Γ10 Function-field indistinguishability | Sharpened | — | Local walls identical over `𝔽_q(X)`; first-order count law identical over `ℤ` and `𝔽_q[T]` [L]; curve windows realized in one space `ℂ^{2g}`, genus saturating at `2g`; over `ℤ` genus `2e^A` and no finite realization [L/S]. |
| Γ11 Pole-blindness of the glue | No-go | — | Simple pole absorbed [L]. |
| Γ12 General gauges | Solved | sub | Harmonic saturation only at the Euler gauge [L]. |
| Γ13 Source-uniform extinction | No-go | — | Fails at `3/4 + i` [L]. |
| Γ14 Local counterterm selection | No-go | — | Flip twin glued index `1` [L]. |
| Γ15 Functional-equation twins | Partially solved | sub | Degree three and positive degree two admit off-line real zeros [L]. |
| Γ16 Selection–sign gap | Sharpened | RH | Every selector is a margin, index, counterterm or identity on a partial form; none gives the sign [L]. |
| Γ17 Scattering recentering | Classified (no-go) | — | Rational/algebraic maps real on the critical parabola are constant / horizontal [L]. |
| Γ18 Divisor-identity selection | Solved (selection) | — | Only `Λ` degenerates completely [L]. |
| Γ19 Correspondence algebra over `ℤ` | Sharpened | RH | Rosati positivity ⇔ orbit Hodge index ⇔ naive height at bounded distance; per cycle, dense pullbacks (`ℚ_{>0}^×`, `p^ℤq^ℤ`) preserve the orbit Hodge index [L]. |
| Γ20 Window selection | Classified | — | Euler-factor locality: a window of length `A` does not see `p > e^A`; for every `A` a flip with `|λ| = Λ`, identical on all length-`A` tests, is not Weil positive [S]. Selection is a law in `A`. |
| Γ21 Density selection on the natural cone | No-go | — | Exact spline divisors with the full RvM count, bounded undamped two-prime coupling and unattained width [S]. |
| Γ22 Contractive scattering positivity | No-go | — | Blaschke pairs keep the FE product, conjugation symmetry, boundary modulus and every Schur inequality while placing zeros anywhere in `Re s > ½` [L]. Placement needs the reflection, not contraction. |

## Bridges

| Bridge | Anchor |
|---|---|
| `κ(K_ζ)` = right zeros = `sup_A ι(A)` = band poles of `Λ(s)/Λ(s+1)` = zeros moved by `σ`; even; RH ⇔ `κ < 2` | HKT, RIT, CWS `TheWindowIndex`, AOG [L] |
| Window form = archimedean jumps + `n ≤ e^A` folds − canonical density + pole; signed folds; canonical class `ψ_{1/2}` profile | CWS [L] |
| Complete family = Tate pieces (bulk `#ℙ⁷(ℤ/m)`, twisted windows) + untwisted windows (Weil) | ADT, AHD [L/S] |
| Window criterion ⇔ horizon criterion ⇔ Beurling schedule ⇔ every `K·c*` ⇔ window index `0` | CWS, AHD, RIT, TM [L] |
| Phase diagram: pencil positive for `κ·windowFloor(A) ≤ βJ/K`; window index monotone in `K` | CWS [S], AHD [L] |
| Canonical degree `≈ 4e^{A/2}` = window budget = trivial strip | CWS [S]; reading [D] |
| Window length `A` ↔ window-energy time `t` ↔ multiplier exponent of `σ_A` ↔ radius `½ log K` of a critical multiple ↔ Landau height `log(T/2π)` | CWS, CDG, TM [L/S]; [D] |
| No finite realization (window or kernel) ⇒ tower of rank `≈ 2e^A` = theta count | CWS, RIT [L/S] |
| Künneth counts pay all but `½Q`; naive height ⇔ sign; generic two-prime orbit decides | CWS [S], AE, AET [L] |
| Gaussian-damped two-prime cone coupling bounded ⇔ RH; undamped density cannot select | ACPL [L/S] |
| `Λ(s)/Λ(s+1)`: band poles = Hodge defect = Mayer boundary = `SL₂(ℤ)` scattering coefficient; contractive positivity blind | RIT [L] |
| Window index = Wiener–Hopf index = growth of `|𝒵(t)|²` | CDG [L] |
| Hecke-defect means ↔ near-line density rates | CDG [L] |
| Gluing `κ(φ_c) = κ + 1`; Redheffer `det = M(N)`; graded/top Möbius pair | AKG, ADT, HWV [L] |
| Curve calibration: bounded coupling ⇔ unitary ⇔ every window realized in `ℂ^{2g}` | ACPL, LST, CWS [L/S] |

## Status counts

| Family | Solved | Partially solved | Sharpened | Open | No-go | Classified | Reduced |
|---|---|---|---|---|---|---|---|
| Σ (41) | 7 (Σ1a, Σ1h, Σ10, Σ12, Σ16, Σ24, Σ29) | 8 (Σ1b, Σ1d, Σ1g, Σ1j, Σ1k, Σ3, Σ6, Σ9) | 8 (Σ1, Σ2, Σ3a, Σ4, Σ7, Σ8, Σ17, Σ28) | 6 (Σ1c, Σ1e, Σ18, Σ19, Σ20, Σ27) | 5 (Σ1f, Σ13, Σ14, Σ23, Σ25) | 6 (Σ1i, Σ11, Σ15, Σ21, Σ22, Σ26) | 1 (Σ5 → Π17) |
| Π (26) | 3 (Π1, Π11g, Π13) | 4 (Π3, Π7, Π9, Π12) | 7 (Π4, Π5, Π6, Π8, Π10, Π16, Π17) | 3 (Π2, Π11f, Π11h) | 8 (Π11a–e, Π14, Π18, Π19) | 1 (Π15) | — |
| Γ (22) | 5 (Γ2, Γ6, Γ7, Γ12, Γ18) | 2 (Γ5, Γ15) | 4 (Γ8, Γ10, Γ16, Γ19) | 2 (Γ1, Γ4) | 7 (Γ3, Γ9, Γ11, Γ13, Γ14, Γ21, Γ22) | 2 (Γ17, Γ20) | — |

Strength of the open walls:
- **RH:** Σ1, Σ2, Σ3a, Σ6, Σ7, Σ8, Σ17, Σ18, Σ19, Σ20, Σ27 (all stages), Σ28 (subexponential), Π2,
  Π4, Π11h, Π17 (polynomial stage), Γ1, Γ4, Γ5, Γ8, Γ16, Γ19.
- **≥qRH:** Σ4 (`K_ζ`), Σ28 (exponent `< ½`), Π5 (fixed scale), Π10, Π17 (log stage on every window).
- **sub:** Σ1b–Σ1e, Σ1g, Σ1j, Σ1k, Σ27 (each stage), Π3, Π5 (mean `o(log U)`), Π7, Π9, Π11f, Π11h
  (fixed length), Π12, Γ15.
- **indep.:** Π16.
