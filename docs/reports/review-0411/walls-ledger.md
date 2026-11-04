# Walls ledger — status quo

Three wall families block every route: **Σ** the critical sign, **Π** precision and production,
**Γ** selection and reflection. All three read one even integer, `κ = κ(K_ζ) = #` distinct zeros right
of the critical line, on the window tower `A ↦ W_A` (`κ = sup_A ι(A)`), and all three are decided on
the **two-site window** `{f, f∘R}` of a test and its mirror image.

- **Σ is the sign of every window, decided on reflection pairs.** RH ⇔ `|c_ψ(t)| < Q(ψ)` for every bump
  and `t ≠ 0` [L]; `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)` and the parity sectors of a window are the band at its
  centre [L]. Every certificate must keep the pole: the Markov part dies at length `e^{−3/4}` [L]. In a
  gauge the window form is a signed Dirichlet form plus pole charges [L]; the collar light cone certifies a
  prime kick when `2Λ(n)n^{−1/2}e^{h} ≤ 1`, a range that is empty for the primes `3 ≤ p ≤ 73` [L/D].
- **Π is the same band read on the prime side.** `𝒞_m(f) = 𝓗_m(f) − Σ_nΛ(n)n^{−1/2}(f⋆f)(2m − log n)`
  [L]: the collective payment of the kicks is the smoothed prime count of `f⋆f` matching the pole square
  within `W(f)` — the square-root form of RH. Production by counts is closed [D]; the size-only floor of
  the complete family carries no zero information [L/D].
- **Γ is reflection and identification.** The completed PM space is `ℓ²(zeros)` with
  `Q = 2Re[𝓦H, 𝓦H]` [L]; the resonant co-isometry defect is `≤ 0`, zero exactly on the quarter line [L];
  the explicit formula identifies finite modifications of the zeros at every aperture without a sign [L].
  Selection is automatic after positivity [L]; positivity is the open half.

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact
form a theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a
classification or identification theorem), **Reduced** (theorem-level equivalent of the wall named).
Strength: **RH**, **≥qRH** (zero-free half-plane or Lindelöf), **sub**, **indep.**, **identity**,
**method**. Evidence: `[L]` Lean; `[W]` working tree or draft module; `[D]` derived here; `[M]` exact
model statement; `[N]` numerical; `[P]` paper. Window lengths `A`; half-widths `a = A/2`;
`c_ψ(t) = W(ψ(· − t), ψ)`; `w_n = Λ(n)n^{−1/2}`; `h = a − (log n)/2` the collar half-width of `n`.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign | Sharpened | RH | RH ⇔ `Q ≥ 0` on every window ⇔ two-site PD ⇔ strict orbit Cauchy–Schwarz ⇔ band at the centre in both parity sectors ⇔ every lattice Schur parameter in `(−1,1)` ⇔ no degenerate lattice ⇔ every growth step a translation contraction ⇔ fold capacity ⇔ `ι(A) = 0` ∀A ⇔ window threshold `R₁(A) = ⊤` ∀A ⇔ horizon sign at every `2K(log N)^{1/8}` ⇔ Beurling schedule ⇔ Krein positivity of zero coordinates ⇔ prime-blind positivity ⇔ canonical domination [L]. One generic bump decides; eventual boundedness of its orbit correlation decides [L]. |
| Σ1a Critical overlap and receivers | Solved | — | `c*_N ≍ L(log L)²`; tilted-spline receiver at every `K(log N)^{1/8}`; unit-bump receiver; one Beurling profile realizes every finite rational Gram [L]. |
| Σ1b Subcritical regime | Solved | sub | `completeWeilMatrix tiltedUnitSpline c N ≻ 0` for `α < 1/8`, `1 ≤ c ≤ (log N)^α`, floor `κ/(2c⁷)` [L]. |
| Σ1c Joint shell–pole payment | Solved | sub | Prime-successor edges pay nonconstant packet mass; row-split Schur synthesis [L]. |
| Σ1d General profiles | Partially solved | sub | Positivity on spans `θ < 1/1080` through `b_φ log log N`; every polylog span through `K log log N`; super-log-log clocks [L]. |
| Σ1e Conductor barrier | Partially solved | sub | Count form uniform for `m = o(c)`, `≤ ½` for `m ≥ λ₀c`; uniform decomposition on a nonquantitative growing range; low block `≤ ⌊(log N)^{13/32}⌋` retains half its diagonal plus the polar part at every ratio; large-prime cofactor frames [L]. |
| Σ1f Defect-only confinement | No-go | — | `Q < 2^k` witnesses [L]. |
| Σ1g Haar / Gamma graph | Partially solved | sub | All-detail prime–pole cancellation `O(exp(−√log Y/92160000))`; index `≤ R + A`; growing Euler heads unbounded [L]. |
| Σ1h Smooth logarithmic profile | Solved (to `ε₀c*`) | sub | Positive to `ε₀L(log L)²`; budget sharp [L]. |
| Σ1i Second order on horizon blocks | Classified | — | `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²`; pencil index `= #{λ_i < 0 : βJ/(−λ_i) < K}` [L]. |
| Σ1j Critical-curve decomposition | Partially solved | sub | Ramanujan, periodic, trigonometric (distinct frequency classes), primitive characters solved; frequency counts have a pole of order `β+1` at `u = 0` with finite part the untwisted count [L]. Open: the whole twisted sector uniformly at every multiple. |
| Σ1k Whole space at one critical multiple | Solved | sub (size-only) | Some `K₀` gives PD of the complete matrix on the whole prime-horizon space uniformly in `1 ≤ c ≤ 2K₀(log N)^{1/8}`, floor `(log N)^{−7/8}` off conductor one, horizon Gram index `0` for every finite family, weighted window sign on windows of every length, mixed families PD [L]. |
| Σ1l Window threshold | Sharpened | RH | `R₁(A) = inf{7J(1)M₈(H)/(a_φ|Q(H)|) : Q(H) < 0}`: pencil PD below, eventually negative test above; antitone; `R₁ ≥ R₀ > 0` and `≥ 7J(1)/(a_φS(A))`; `⊤` for `A ≤ 2·enlargedWeilFloorAperture`; RH ⇔ `R₁ ≡ ⊤` [L]. Joint pole payment strictly enlarges the certified ratio interval [L]. |
| Σ1m Polarization inheritance | Partially solved | sub | Every twisted sector with positive scalar second order, windows `≤ 3/5`, the cosh hyperplane below `log 2 + 1/50`, every window at small ratio [L]. Untwisted long windows at large ratio = Σ1. |
| Σ1n Bulk and growing overlap | Classified | — | Zeros of height `≤ λN` enter a fixed packet only through the pole; at fixed overlap bulk entries read `γ, γ₁`, divisor logarithms; along a growing overlap every bulk entry is `E_e(c)⟨R_e,R_{e'}⟩ + [e=e'=1]κc(2 + γ − log4π) + o(c)`; complete critical, upward-prime and Gamma residues supported at the pole [L]. |
| Σ1o Aperture-independent weighted floor | Solved (size-only) | — | `Q(H) ≥ −C(p)∫e^{−pu}H²` for every `p > 1` on every window [L]; joint-pole improvement [L]. The exponent `p > 1` is forced by the Cauchy–Schwarz bound on the pole moment `∫He^{−y/2}` [L]. A floor with exponent `p` gives `μ(a) ≥ −Ce^{2pa}` at half-width `a`, hence zero width `≤ p` (contact law): the proved range carries no zero information and `p < ½` would be quasi-RH [L/D]. |
| Σ1p Terminal windows | Classified | — | No upward and no exterior primes on terminal supports inside `(½, 1)`; polar mixed limit `α[∫polarCenterProfile(F) − log(2π)∫F]`; nonpolar centre and divisor jet cancel; a nonzero terminal polar source exists; low-block removal preserves the compensated window limit [L]. |
| Σ1q Receiving charges | Classified | — | Charges survive vanishing raw, physical and absolute complete energy; capacity `log log N + O(1)`, minimum energy `t²/Cap_N`; complementary receiver pairs to `t/80`, energy `/log N → 1/20`, determinant `→ 6239t²/6400 > 0`; fixed packets have zero complete output, positive Jordan limit [L]. Open: uniform assembly of the complement across regimes. |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | HR ∧ HL ⇔ strict HR; RH ⇔ HL on the PSD locus [L]. Zero modes: radical, reflection parity, gap law, end-collar injectivity; lattice first failure two-site with mode `(1, ∓1)`; a tight band on a nonnegative window yields a reflection-pair zero mode with pole-charged harmonic gauge [L]. |
| Σ2a Interior-gap continuation | No-go (as structure) | — | Three-angle curve `κ(d) = 1_{3∣d}` [L]. Not needed: two sites decide. |
| Σ2b Edge singularity | Classified [W] | — | Window eigenfunctions are not smooth; a window's infimum is not attained on a nonzero smooth test; a nonnegative window is PD on smooth tests and the band is strict on smooth tests [W]. The decisive object at a first failure lives at the window edge. |
| Σ3 Stars and dilation monodromy | Partially solved | — / RH | Stars isometric, depth law; monodromy eventually idempotent; Jordan coefficient a point count [L]. |
| Σ3a Coprime stratum | Sharpened | RH | gcd stratification; graded/top Möbius pair; Redheffer `det = M(N)` [L]. |
| Σ4 Finite index / heat count | Sharpened | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | `κ < ∞` ⇒ Lindelöf; RH ⇔ index `0`; `{0, ∞}` laws [L]. |
| Σ5 Collision quantum / window integer | Reduced (to Π17) | RH | Index `0` ⇔ Wiener–Hopf invertibility ⇔ outer Szegő factorization [L]. |
| Σ6 Rank / degree uniformity | Partially solved | RH | Rank 8 PD at every `0 < a < ½`; every finite rank strict on a factorial collar and on a logarithmic collar `|a − ½| < c/(1+log(N+1))`; rank 9 reduced to a compact source set by one cross-load; fixed Jensen degree eventually hyperbolic; PF₃₇ [L]. |
| Σ7 Window Markov capacity | Sharpened | RH | Fold capacity criterion; exit charge to `1/7`; RH ⇔ `R ≤ ½` on the odd sector [L]. |
| Σ8 Realization | Sharpened | RH | RH ⇔ every window has an `ℓ²(zeros)` realization, explicitly `Q = 2Re[𝓦H, 𝓦H]` [L]; no finite-dimensional or finite-rank realization [L]. |
| Σ9 Explicit image / resolvent | Partially solved | RH in strip | Depth identity for `σ > 1`; theta–prime expression at `s = 4` [L]. |
| Σ10 Local signatures and gluing | Solved | — | `κ(φ_c) = κ + 1` at `∞` and every prime [L]. |
| Σ11 Product-formula gluing of the pole | Classified | — | Local poles add squares; extremal weight = archimedean pole on `S`-units [L]. |
| Σ12 Running counterterm / star flux | Solved | — | `log N − γ` cancels the prime diagonal [L]. |
| Σ13 Tensor amplification | No-go | — | `K_ζ^n` PD ⇔ RH; `n₋(G⊗G) = 2n₊n₋` [L]. |
| Σ14 Deformation to a positive model | No-go as free input | — | Crossing-free path ⇔ PD [L]. |
| Σ15 Separable assemblies | Classified (no-go) | — | Blind when truncated, non-convergent when untruncated [L]. |
| Σ16 Prime–pole coherence | Solved (identity) | — | Complete form = jump + incidence − shell + diagonal + boundary [L]. |
| Σ17 Inter-tower coupling | Sharpened | RH | Bounded dense coupling ⇔ RH; damped cone ⇔ RH; undamped ⇒ RH or unattained width [L]. |
| Σ18 Exact SOS on a two-prime lattice | Open | RH | Generic Hecke orbit carries the full Hodge defect [L]. |
| Σ19 Rank-one intertwining coefficient | Sharpened | RH | `κ_Hodge = #` band poles of `Λ(s)/Λ(s+1)` [L]. |
| Σ20 Scheduled prime sums | Open | RH | FU, CFC, RP, SZ, LI, FEL, EGC receivers [L]. |
| Σ21 Extension / carrier | Classified | — | Escape, mixing, height decay ⇒ `κ ∈ {0, ∞}` [L]. |
| Σ22 Lefschetz operators | Classified | — | Dilation HL trivial; overlap-flow HL on the HR locus is RH [L]. |
| Σ23 Connected links | No-go | — | Links disconnected [L]. |
| Σ24 Finite divisor | Solved | — | Coercive off `i/2` and a finite grid [L]. |
| Σ25 Semilocal and trace carriers | No-go | — | No `{∞,p}` positive carrier; exact `{∞,2}` trace through `½log 3` [L]. |
| Σ26 Approximation by RH-true objects | Classified | — | Closure class Laguerre–Pólya [L/D]. |
| Σ27 Window stages | Partially solved | sub (each stage); RH (all) | All real `C²` tests positive through length `181/250·(1 + 6·10⁻⁷)`; first stage opens positive; at length `21/20` the admissible prime-two weights form an interval excluding `0` and `−w₂` [L]. Odd unit window: `‖F‖²/1000 ≤ Q + (3203/320)(∫xF)²`, `Q ≥ ‖F‖²/100` off two odd moments, exact retained-Gamma identity, higher reserve, logarithmic strip payment [L]. No sign theorem on `[0.7240, log 3)` [N margins `1.5×10⁻⁵` odd, `5.6×10⁻⁸` even]. |
| Σ28 Window negativity budget | Sharpened | ≥qRH (exponent `< ½` in the length); RH (subexponential) | Floor `−(deg K_A + 2sinh(A/2) − A)‖H‖²`; ground-energy floor `−Ce^{2σA}` ⇔ zero width `≤ σ`; two-bump negativity rate = maximal depth; orbit-correlation rate = zero width [L]. |
| Σ29 Low-frequency localization | Solved | — | Negativity only at the poles and below `τ₀(a)` [L]. |
| Σ30 The stage step | Sharpened | RH (as induction); each stage sub | Stage criterion `2wc_H(ℓ) ≤ S^N_A(H)`; kick = collar Rosati pairing; frozen form in closed form; Carathéodory disk; lattice admission `|β_n − kick| < E_n` [L]. |
| Σ31 Positivity across dimension zero | Classified | equivalent to Σ1 | Bare domination ⇔ `Q ≥ 0`; no uniform archimedean family; Euler-product pole weight forced and refuted [L]; count/Hodge/degeneration cannot close RH [D]. |
| Σ32 Prime-blind positivity | Sharpened | RH | Weil cone `{Λ}`; node-critical; finite-level Farkas duality; zero-side identity on blind tests; solved on nonnegative and separated-bump cones [L]. |
| Σ33 Tate positivity horizon | Classified | — | Exact horizons at stages 1–2; no `k > 0` uniform [L]. |
| Σ34 Canonical-degree horizon | Classified | — | Every soft deformation paid by counts has horizon `≍ e^{−A/2}` [L/D]. |
| Σ35 Canonical system of the tower | Partially solved | identity | Lattice: Levinson recursion, margins `κ(0)∏(1 − γ_k²)`, causality [L]. Local continuum limit at a bump = jet Hankel system, `h^{−2n}E_n → det J_{n+1}/det J_n` [L]. Global Hamiltonian carrying the prime kicks: not constructed. |
| Σ36 Rational Hecke-graph reading | Solved (identity) | — | Window arithmetic on finite `S ⊂ ℚ_{>0}` = Hecke operator of `ℤ[ℚ^×_{>0}]` [L]. |
| Σ37 Lattice canonical system | Solved (identity) | — | Window ⇔ its lattices; outer predictors; refinement lowers margins; single-kick law [L]. |
| Σ38 Two-site decision | Classified | — | RH ⇔ two-site PD; off RH `|c_ψ(s)| = Q(ψ)` for a short generic bump [L]. |
| Σ39 Trivial-divisor transmission | Solved (identity) | — | Across a cut the archimedean place and pole couple only through `μ_{1/2}ν_{1/2} − Σ_kμ_{σ_k}ν_{σ_k}`; on reflection-paired data this is the collar Hankel form, inertia `(1, ∞)`, negative definite on the pole hyperplane, trivial squares at ratio `e^{−4d}` [L]. |
| Σ40 Degenerations are curves | Classified | — | Degenerate lattice windows are finite curves; Spec ℤ under RH is the infinite-angle curve, Szegő singular [L]. |
| Σ41 Contact law | Open | sub | RH to height `T` ⇒ windows to length `c log T`? Paired-lattice boundary `X² ≤ T` [M]; contact aperture `≥ 3/10`, `μ = 0` at it off RH, bounded above by near-top zeros [L]. |
| Σ42 Markov and sign-blind ground states | No-go | — | Markov part negative on a test of support `e^{−3/4}`; no Markov supersolution on a longer interval; folded criterion void on the unit odd window; full folded calibration fails; lossless local allocation fails; Barta/Picone sign-blind [L]. |
| Σ43 Pole-charged ground-state calculus | Solved (identity) | — | `Ẑ(Φωu) = J_{Φω}(u) + ∫u²ω𝒢_S(ω) + 2V_s − 2V_c`; sinh-charged supersolution ⇒ `Ẑ ≥ J + 2A²`; cosh credit ⇒ `Ẑ ≥ J − 2V_c − 2B²`; theta gauges critical on the line; window reads outside charges: odd slack, even deficit; shifted ground states strict with slack `τ_c > 0`; Rayleigh-critical gauges and zero modes solve the pole-charged source equation [L]. |
| Σ44 Collar locality of the kick | Classified | — | `−2w∫ff(·+ℓ) + 2we^hA_C(f) ≥ 0`; failure when `λ(1 + 4h) < 2w`; prime `3` unpaid on `a ∈ (½log 3, ½log 3 + 1/40]` [L]. `2w_n < 1` for `n = 2`, proper prime powers, primes `≥ 79`; `> 1` for primes `3 ≤ p ≤ 73`; the light cone certifies the kick of `n` only while `a ≤ log n − log(2log n)` and never for `3 ≤ p ≤ 73`, where the collar provably fails at thin collars [D]. |
| Σ45 Reflection pairs and parity sectors | Solved (identity) | — | `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; band ⇔ positivity on the pair; parity sectors of `[−a, a]` = band at the centre; Markov–Hankel form of each sector [L]. |
| Σ46 Frustration of the odd sector | Classified | — | Frozen odd form Markov under `F ↦ sign(x)|F|`, kick anti-Markov; kick = source `2w∫hh∘τu²` − conductance `w∫hh∘τ(u − u∘τ)²`; odd light cone `≥ 0` for every odd gauge positive on the half-line [L]. |
| Σ47 Odd unit window | Open | sub | Positivity ⇔ `w₂ = log 2/√2 ∈ unitBandWeights` (convex) ⇔ `4S² ≤ M + Σ_jm_j² + w₂(f⋆f)(−log 2)` on `[−½, 0]` [L]. Retained Gamma, `+E/64`, two-moment, polynomial chord and folded supersolutions refuted [L]. |
| Σ48 Criticality | Classified [D] | — | Every exact reading sits on a boundary with zero slack: Weil cone a point, lattices Szegő singular, aperture floor doubly-exponentially decaying, theta gauges critical on the line, heat path real at `t ≥ 1/8` and non-real at every `t < 0` [L]. A proof is exact at the boundary. |
| Σ49 Reality by continuation | Sharpened | RH | Reality of a real family is lost only through collision; heat flow preserves mesh and depth (polynomial model); `H_t` real for `t ≥ 1/8`, RH ⇔ `H_0` real, `H_t` non-real for `t < 0`; first Laguerre inequality not a certificate [L]. Open: collision exclusion along a source-faithful path. |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (equivalence) | RH | `ψ(x) − x ≤ C√x log²x` ⇔ RH ⇔ `κ = 0`; Redheffer `det R_N = M(N)` [L]. |
| Π2 Deciding input | Open | RH | No unconditional source input at square-root precision. |
| Π3 Producer cost | Partially solved | sub / RH | Multivariate parity producers reach `(1+ε)x + C_εlog²x`; individual producers slope `> 1`; integer-Chebyshev ceiling [L]. |
| Π4 Window precision (kernel = coupling) | Sharpened | RH | `𝒞_m(f) = 𝓗_m(f) − Σ_nw_n(f⋆f)(2m − log n)`: the collar Hankel form is the main term `e^mμ_{1/2}(f)²` of the smoothed prime count of `f⋆f` plus exponentially small trivial-zero corrections; RH ⇔ the count is within `W(f)` of it for every reflection pair [L]. |
| Π5 Conjugate diagonal | Sharpened | sub → ≥qRH → RH | Means `O_c(log U)`; `o(log U)` ⇔ clustering; one dyadic constant ⇔ RH [L]. |
| Π6 Averages versus all heights | Sharpened | — | Double-log stage outside `O(V/log log V)` windows; exact critical-line flux on `(1 − O(B))V` micro-Planck windows [L]. |
| Π7 Census / pair surplus | Partially solved | sub | Simple critical `≥ 0.67250071` (imported Zeta23 inputs); four fifths of the ordinates carry a critical zero; positivity-only certificates cannot reach `3/4` [L]. |
| Π8 Depth visibility | Partially solved | — | Cluster-product horizon; off-line zeros seen at aperture `≍ log|γ|log log|γ| + 1/δ` [L]. |
| Π9 Exceptional moduli | Partially solved | sub | Uniform zero-free region and Siegel for `q ≤ (log x)^A` [L]. |
| Π10 Frequency localization | Solved | — | Every eventually positive cyclotomic band has abscissa `2Θ` [L]. |
| Π11a–e Cone, bidegree, fixed-rank, definite, Siegel counts | No-go | — | Excluded as independent sign producers [L]. |
| Π11f Logarithmic duality | Partially solved | sub | Pole plane: Abel completion, logarithmic RR [L]. |
| Π11g Boost transform | Solved (identity) | — | `∫Z⁺(s,u)e^{2wu}du = K(s,w)ζ(s+w)ζ(s−w)` [L]. |
| Π11h Count-valued primitive `h¹` | Sharpened; closed as mechanism | RH | Window `h¹ = ½Q`; Weil's form a signed count [L]; every concrete count type excluded [D]. |
| Π12 Subconvexity / heat floor | Partially solved | sub | `μ(½) ≤ 33/200`; heat floors `133/200`, `2/3 + ε` [L]. |
| Π13 Prefix scale | Solved | — | Strip zeros `Θ(N² log N)`; stabilization `Θ(√m)` [L]. |
| Π14 Amplifier rank | No-go (finite support) | — | Growing losses keep radius `Be^λ` [L]. |
| Π15 Critical-scale residual sign | Classified | — | Residual = prime-free aliasing term + Weil's form [L]. |
| Π16 Genus function | Sharpened | indep. | Genus `≥ (2 − η)e^A` + multiplicity excess; upper law open [L]. |
| Π17 Window energy | Sharpened | RH; ≥qRH (log stage) | Abscissa = twice the maximal depth; zero-free window ⇔ unweighted `L²` port; bounded port ⇔ critical-line purity; polynomial stage ⇔ RH [L]. |
| Π18 Finite realizations | No-go | — | No finite-dimensional window realization [L]. |
| Π19 Mollified log-mean from moments | No-go | — | Moments do not determine the log-mean [L]. |
| Π20 Count identities at the first prime | No-go | — | No finite-square identity for `log 2 ≤ A < 2log 2` [L]. |
| Π21 Exact balance | Classified | — | Weil cone `{Λ}`; `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})`; Szegő singular under RH [L]. |
| Π22 Near-line density ladder | Sharpened | sub | Eight equivalent forms; `D_win` ⇔ thin Planck shadows; `D_zero` ⇔ `D_win` + vanishing giant-cluster tails; `(log V)²` per-window factor sharp under occupancy [M]; uniform Planck volume ⇏ occupancy [M] [L]. |
| Π23 Inner caps | Open | RH (all degrees); ≥qRH (fixed degree) | Caps cancel to `σ_m = 1 − 1/(116log(m+5))`, the classical zero-free region [L]; the cap is the zero-free region pushed to the line [D]. |
| Π24 Parity at dimension zero | Classified | — | Jets generated by `M` and `ρ_A(Λ)`; Selberg `Λ₂` constraint [L]. |
| Π25 Euler-product pinning | Classified | — | Shifted-pole weight `= 1/ζ(1+k)`, refuted [L]. |
| Π26 Bulk second order | Solved | — | `2γ₁ + γ²` at the pole at fixed overlap; polar linear growth `κc(2 + γ − log 4π)` along growing overlap; character packets read `L'/L(1,χ)` [L]. |
| Π27 Retained Gamma comparison | No-go (as lossless) | — | `R_ret < 0 < Q` and `R_ret + E/64 < 0 < Q` on smooth odd unit tests [L]. Survivors: higher reserve `t³/960 + t⁴/192`, exterior reserve [L]. |
| Π28 Gauge-torus spectrum | Classified | RH at the trivial point | Pole-subtracted prime exponents range exactly over `[Θ, 1]`, minimized at the trivial point; RH ⇔ range `[½, 1]`; flip points share the pole and break the Möbius half-power law; an explicit non-special point has Möbius exponent `½` [L]. |
| Π29 Square-root threshold | Classified | — | Columns of RvM density are mimics of on-line lattices iff camera exponent `λ ≤ ½`, uniformly in depth and height; paired-lattice boundary `X² ≤ T` [L/M]. `λ = ½` is the length `√(T/2π)` of the Riemann–Siegel main sum [D]. |
| Π30 Collective payment of the kicks | Sharpened [D] | RH | Kicks outside the collar-certified range (Σ44) need resources beyond their own collar — provably for the primes `3 ≤ p ≤ 73` at thin collars; together the anti-diagonals of all kicks on a reflection pair are the smoothed prime count in `𝒞_m` (Π4). The P1 resource that remains for them is the pole square against that count: Σ meets Π beyond the first stages. |

## Γ — selection and reflection

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point | Open | RH | `Θ ≥ ½`; Haar-a.e. `½`; Baire-generic `1`; an explicit non-special point at `½` [L]. |
| Γ2 Prime-set flips | Solved | — | Every nontrivial prime pattern separated at every density [L]. |
| Γ3 Twin-blindness of soft structure | No-go | — | Krein index invariant under unitary twists [L]. |
| Γ4 Frobenius at infinity | Sharpened | RH | RH ⇔ `σ` trivial ⇔ Hecke similitude ⇔ partner saturation; window involution = twisted conjugate Krein reflection; kick = collar Rosati pairing [L]. |
| Γ5 Source identification / pre-divisor | Partially solved | RH | Pre-divisor sections need zero-independent forcing [L]. |
| Γ6 Boundary sign / coherence | Solved | — | Pole boundary sign separates `ζ` from size twins [L]. |
| Γ7 Affine carrier | Solved | — | Gluing at a place; subgroup classification [L]. |
| Γ8 Poisson rigidity | Sharpened | RH | Zero-side positivity = RH [L]. |
| Γ9 Archimedean continuity vs height decay | No-go | — | ⇒ `κ = ∞` [L]. |
| Γ10 Function-field indistinguishability | Sharpened | — | Pure curves: sums of squares with Hurwitz weights of the angles; twist frequency `u` ≡ angle `u`; untwisted direction = pole `u = 0`; camera of aperture `> g log q/2` identifies Frobenius configurations and certifies purity, sharp against the golden datum [L]. |
| Γ11 Pole-blindness of the glue | No-go | — | Simple pole absorbed [L]. |
| Γ12 General gauges | Solved | sub | Harmonic saturation only at the Euler gauge [L]. |
| Γ13 Source-uniform extinction | No-go | — | Fails at `3/4 + i` [L]. |
| Γ14 Local counterterm selection | No-go | — | Flip twin glued index `1` [L]. |
| Γ15 Functional-equation twins | Partially solved | sub | Degree three and positive degree two admit off-line real zeros; positive finite Euler twins have zeros at any `Re s ∈ (½,1)` and violate only `θ < ½` [L]. |
| Γ16 Selection–sign gap | Sharpened | RH | No selector gives positivity [L]. |
| Γ17 Scattering recentering | Classified (no-go) | — | Rational/algebraic recentering impossible [L]. |
| Γ18 Divisor-identity selection | Solved | — | Only `Λ` degenerates completely [L]. |
| Γ19 Correspondence algebra over ℤ | Sharpened | RH | Rosati positivity ⇔ orbit Hodge index ⇔ naive height at bounded distance [L]. |
| Γ20 Window selection | Classified | — | Bounded windows blind; flip twin identical on length-`A` tests is not Weil positive [L]. |
| Γ21 Density selection on the natural cone | No-go | — | RvM-count exact-spline countermodels [L]. |
| Γ22 Contractive scattering positivity | No-go | — | Blaschke pairs keep every Schur inequality [L]. |
| Γ23 Weil cone uniqueness | Solved | — | Full Weil positivity forces `Λ`; lattice margins all positive only for `λ = Λ` and RH [L]. |
| Γ24 Mayer reflection positivity | Sharpened | RH | Resonance ⇔ `ζ(2s) = 0`; resonant co-isometry defect `≤ 0`, `< 0` iff `Re s ≠ ¼`; `I_s` isometric iff `Re s = ¼`; head branch pair bounded iff `Re s = ¼`; dyadic cusp energy finite iff resonance (Eisenstein periods); exact completion `Q = 2Re[𝓦H,𝓦H]`; counterterm subtraction supplies no sign [L]. Open: `D_s(ψ_s) ≥ 0` on resonances. |
| Γ25 Two reflection centres | No-go (as operator symmetry) | — | Transfer reflects about `Re w = 1`, zeta events about `Re w = ½` [P]. |
| Γ26 Resonant-state selectors | No-go | — | Inversion fixes every resonant period; cutoff Grams retain the rate [L]. |
| Γ27 Tate counts as a selector | No-go | — | `ζ(s)ζ(s−ε)` Tate positive, not Weil positive [L]. |
| Γ28 Frobenius inside the window algebra | No-go | — | Same-window similitudes scalar [L]. Survivor: Frobenius at scale `t` = translation by `t` [L]. |
| Γ29 Linear Serre–Krein identification | No-go | — | No real-linear isometry [L]. |
| Γ30 Completed Tate family | Classified | — | Unimodular on the line [L]. |
| Γ31 Degeneration type over `𝔽_q` | Solved (calibration) | — | Pure curves degenerate completely; impure curves grow at exactly their zero width; golden fake rate `log φ/log 5` [L]. |
| Γ32 Hecke-equivariant completion | Solved (identity) | identity | `𝒦 = ℓ²(upper Mayer resonances)`; PM cores dense; bounded window map; Hecke multiplier `p^{1−2s}` [L]. |
| Γ33 Euler rigidity in the Selberg class | Solved | — | Euler-log discrepancy absolutely convergent at `σ = ½` ⇒ equality; degree zero = unit; no degree in `(0,1)`; degree one: conductor `≥ 2m₀` or a pole at `1` [L]. |
| Γ34 Hecke cones and periods | Solved | — | Hecke cones tile; Barnes/Eisenstein/Lewis periods Hecke eigenfunctions [L]. |
| Γ35 Beurling and Hamburger rigidity | Classified | — | Positive primes with regular integers admit zeros at any `Re s ∈ (½, 2/3)`; a positive measure with Riemann's FE is the counting measure of `ℕ` [L]. FE + Euler product are the minimal input. |
| Γ36 Identification by the explicit formula | Partially solved | sub (sign-free) | Finite modifications identified at every aperture, constructively and stably, uniformly in height; primes below `e^{2r}` pin every finite piece of the zeros of `ζ`; separated or depth-bounded infinite configurations identified; mimics contain near-collisions at scale `90/V` or deep points [L]. Open: identification at the density scale of `ζ` (B43). An on-line competitor with the image of `ζ` would already be Weil positivity [D]. |
| Γ37 Euler columns | Classified | — | A zero of `1 + Ap^{−s} + p^{1−2s}` is on the line iff `A² ≤ 4p`; columns hide below aperture `log p/2` and are seen just above; no bounded aperture excludes them [L]. |
| Γ38 Retained Hecke channel | Classified | — | The unique `T₂` boundary coefficient `core_s(2) ≠ 0`; its co-isometry defect has the sign of `¼ − Re s`, opposite at the reflected resonance [L]. It reads the side of a resonance and forces nothing [D]. |

## Bridges

| Bridge | Anchor |
|---|---|
| `κ(K_ζ)` = right zeros = `sup_A ι(A)` = band poles of `Λ(s)/Λ(s+1)` = upper-right Mayer resonances; even; RH ⇔ `κ < 2` | HKT, RIT, CWS, AOG [L] |
| Window sign ⇔ two-site sign ⇔ band at the centre in both parity sectors | GWZ, SWC [L] |
| Reflection-pair coupling = collar Hankel form − smoothed prime count (Σ on two sites = Π at one point) | SWC, CSTW [L] |
| Kick = positive source − anti-diagonal conductance; local payment ratio `2w_ne^h`; collective payment = Π4 | SWC [L]; [D] |
| Window ⇔ its lattices; local continuum limit ⇔ jet Hankel system | GWZ, SWC [L] |
| Degenerate window ⇔ finite curve; Spec ℤ under RH ⇔ infinite-angle curve, Szegő singular | GWZ [L] |
| Window algebra = truncated Dirichlet λ-ring; `ρ_A(Λ) = [M, log Z]` | WTZ [L] |
| Weil's window form = dimension-zero jet of the Tate family; positive dimension classified | WTZ, DZG, ATD [L] |
| Complete family at the critical curve = Weil at the pole of the frequency counts + positive counts; threshold `R₁(A)` | AHD [L] |
| Floor exponent of the complete family = zero width | WTZ, SquareRootThreshold [L]; [D] |
| Frobenius angle over `𝔽_q` ≡ twist frequency over ℤ; untwisted window ≡ pole at `u = 0` | AHD [L] |
| Weil energy = Krein form of zero coordinates; Hecke = translation; reflection = window involution | RIT [L] |
| Weil image ⇒ configuration (sign-free); hiding ⇔ near-collisions; reality ⇔ sign of a second-order coefficient | ZCG [L] |
| Column threshold `λ = ½` ≡ Riemann–Siegel length ≡ paired-lattice boundary `X² ≤ T` | ZCG, SquareRootThreshold [L/M]; [D] |
| Heat path critical at `t = 0`; reality leaves only through collision | RHTower DeBruijn, ZCG [L] |
| Weil cone `{Λ}`; lattice selection; prime-blind nonemptiness | RHTower, GWZ [L] |
| Near-line density: eight forms; occupancy ⇔ thin Planck shadows | CDG [L] |
| One cyclotomic mode carries `2Θ`; gauge-torus spectrum `[Θ, 1]` | CAF, AGT [L] |
| Gluing `κ(φ_c) = κ + 1`; Redheffer `det = M(N)` | AKG, ADT, HWV [L] |

## Status counts

| Family | Solved | Partially solved | Sharpened | Open | No-go | Classified | Reduced |
|---|---|---|---|---|---|---|---|
| Σ (69) | 16 (Σ1a, Σ1b, Σ1c, Σ1h, Σ1k, Σ1o, Σ10, Σ12, Σ16, Σ24, Σ29, Σ36, Σ37, Σ39, Σ43, Σ45) | 10 (Σ1d, Σ1e, Σ1g, Σ1j, Σ1m, Σ3, Σ6, Σ9, Σ27, Σ35) | 13 (Σ1, Σ1l, Σ2, Σ3a, Σ4, Σ7, Σ8, Σ17, Σ19, Σ28, Σ30, Σ32, Σ49) | 4 (Σ18, Σ20, Σ41, Σ47) | 7 (Σ1f, Σ2a, Σ13, Σ14, Σ23, Σ25, Σ42) | 18 (Σ1i, Σ1n, Σ1p, Σ1q, Σ2b, Σ11, Σ15, Σ21, Σ22, Σ26, Σ31, Σ33, Σ34, Σ38, Σ40, Σ44, Σ46, Σ48) | 1 (Σ5 → Π17) |
| Π (37) | 5 (Π1, Π10, Π11g, Π13, Π26) | 6 (Π3, Π7, Π8, Π9, Π11f, Π12) | 8 (Π4, Π5, Π6, Π11h, Π16, Π17, Π22, Π30) | 2 (Π2, Π23) | 10 (Π11a–e, Π14, Π18, Π19, Π20, Π27) | 6 (Π15, Π21, Π24, Π25, Π28, Π29) | — |
| Γ (38) | 10 (Γ2, Γ6, Γ7, Γ12, Γ18, Γ23, Γ31, Γ32, Γ33, Γ34) | 3 (Γ5, Γ15, Γ36) | 6 (Γ4, Γ8, Γ10, Γ16, Γ19, Γ24) | 1 (Γ1) | 12 (Γ3, Γ9, Γ11, Γ13, Γ14, Γ21, Γ22, Γ25, Γ26, Γ27, Γ28, Γ29) | 6 (Γ17, Γ20, Γ30, Γ35, Γ37, Γ38) | — |

Strength of the open walls:
- **RH:** Σ1 (minimal form: the band on reflection pairs), Σ1l, Σ2, Σ3a, Σ6, Σ7, Σ8, Σ17, Σ18, Σ19, Σ20,
  Σ27 (all stages), Σ28 (subexponential), Σ30, Σ32, Σ49, Π2, Π4, Π11h, Π17 (polynomial stage), Π23 (all
  degrees), Π28 (trivial point), Π30, Γ1, Γ4, Γ5, Γ8, Γ16, Γ19, Γ24.
- **identity:** Σ35 (global Hamiltonian).
- **≥qRH:** Σ4 (`K_ζ`), Σ28 (exponent `< ½`), Σ1o at exponent `p < ½`, Π5 (fixed scale), Π17 (log stage),
  Π23 (fixed degree).
- **sub:** Σ1d, Σ1e, Σ1g, Σ1j, Σ1m, Σ1q, Σ4 (zero–one law), Σ27 (each stage), Σ30 (each stage), Σ41, Σ47,
  Π3, Π5 (mean `o(log U)`), Π7, Π9, Π11f, Π11h (fixed length), Π12, Π22, Γ15, Γ36.
- **indep.:** Π16.
