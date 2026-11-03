# Walls ledger — status quo

Three wall families block every route: **Σ** the critical sign, **Π** precision and production,
**Γ** selection and reflection. All three read one even integer, `κ = κ(K_ζ) = #` distinct zeros right
of the critical line, on the window tower `A ↦ W_A` (`κ = sup_A ι(A)`), and all three are decided on the
**two-site window** `{ψ, τ_tψ}` — the lattice form of AOG's Hasse–Weil criterion [L].

- **Σ is the sign of every window, decided on two sites.** RH ⇔ `|c_ψ(t)| < Q(ψ)` for every bump and
  `t ≠ 0` [L]. In tower form every prime kick must land in the prediction interval of the frozen data
  (one Schur parameter per kick) [L]; frozen forms are indefinite, so the kick is a positive source [L].
  Cost-only, sign-blind, Markov and finite certificates are refuted; the live mechanism is signed
  criticality (P1).
- **Π is the same band read on the prime side.** The two-site entry is the trivial-divisor moment term
  minus the `ψ⋆ψ`-smoothed prime sum on `[e^{t−2r}, e^{t+2r}]` [L/D]: the classical square-root form of
  RH with constant `Q(ψ)`. Production by counts is closed: positive dimension descends nothing and no
  archimedean family dominates the Tate counts [L]; the count/Hodge/degeneration programme cannot close
  RH [D]. The live Π mechanism is square-root cancellation (P4).
- **Γ is reflection positivity.** The completed PM space is `ℓ²(zeros)` with reflection `ρ ↦ 1 − ρ̄` and
  `Q = 2Re[𝓦H, 𝓦H]` exactly; Hecke is translation; the window has no internal Frobenius [L]. Selection
  is automatic after positivity [L]; the functional equation and positivity determine `ζ` [L]. The
  prime-blind form of positivity (P2) is the one Γ-side path with no primes.

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact
form a theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a
classification or identification theorem), **Reduced** (theorem-level equivalent of the wall named).
Strength: **RH**, **≥qRH** (zero-free half-plane and Lindelöf), **sub**, **indep.**, **identity**,
**method**. Evidence: `[L]` Lean, committed and in its umbrella; `[U]` committed, not in an umbrella;
`[W]` working tree or work in progress; `[D]` derived here; `[M]` exact model statement; `[N]`
numerical. Window lengths `A`; half-widths `a = A/2`; `c_ψ(t) = W(ψ(·−t), ψ)`.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign | Sharpened | RH | RH ⇔ `Q ≥ 0` on every window ⇔ two-site PD ⇔ strict orbit Cauchy–Schwarz [U] ⇔ every lattice margin positive ⇔ every lattice Schur parameter in `(−1,1)` ⇔ positive with `Σγ² = ∞` ⇔ no degenerate lattice ⇔ every growth step a translation contraction ⇔ fold capacity ⇔ `ι(A) = 0` ∀A ⇔ horizon sign at every `2K(log N)^{1/8}` ⇔ Beurling schedule ⇔ Krein positivity of zero coordinates ⇔ prime-blind positivity ⇔ canonical domination [L]. One generic bump decides; eventual boundedness of its orbit correlation decides [L]. Minimal form: the two-site band. |
| Σ1a Critical overlap and receivers | Solved | — | `c*_N ≍ L(log L)²`; tilted-spline receiver at every `K(log N)^{1/8}`; unit-bump receiver; one Beurling profile realizes every finite rational Gram [L]. |
| Σ1b Subcritical regime | Solved | sub | `completeWeilMatrix tiltedUnitSpline c N ≻ 0` for every `α < 1/8`, `1 ≤ c ≤ (log N)^α`, floor `κ/(2c⁷)` [L]. |
| Σ1c Joint shell–pole payment | Solved (subcritical) | sub | Prime-successor edges pay nonconstant packet mass; row-split Schur synthesis [L]. |
| Σ1d General profiles | Partially solved | sub | Universal rate on spans `θ < 1/1080` for `c ≤ b log log N`; super-log-log clocks [L]. |
| Σ1e Conductor barrier | Partially solved | sub | Count form uniform for `m = o(c)`, `≤ ½` for `m ≥ λ₀c` (ends at the resolution); scaled-count quasimodes through `N^θ`, `θ < ½`; uniform decomposition on a nonquantitative growing range; conductor-packet prime pairings contain no prime in a progression (`Λ ∗ 1 = log`) at fixed overlap; large-prime cofactor frames [L]. |
| Σ1f Defect-only confinement | No-go | — | `Q < 2^k` witnesses [L]. |
| Σ1g Haar / Gamma graph | Partially solved | sub | All-detail prime–pole cancellation `O(exp(−√log Y/92160000))`; index `≤ R + A`; growing Euler heads unbounded [L]. |
| Σ1h Smooth logarithmic profile | Solved (to `ε₀c*`) | sub | Positive to `ε₀L(log L)²`; budget sharp [L]. |
| Σ1i Second order on horizon blocks | Classified | — | `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²`; pencil index `= #{λ_i < 0 : βJ/(−λ_i) < K}` [L]. |
| Σ1j Critical-curve decomposition | Partially solved | sub | Fixed finite families solved: Ramanujan, periodic, trigonometric with distinct frequency classes, primitive characters (first-order energy `−2Re L'/L(1,χ)`, second order `−2(φ(q)/q)Re(L'/L)'(1,χ)`, distinct characters decouple); frequency counts have a pole of order `β+1` at `u = 0` with finite part the untwisted count [L]. Open: the whole twisted sector uniformly at every multiple. |
| Σ1k Phase diagram `(A, K)` | Classified | sub | Aperture-independent `K₀` from the weighted floor; every fixed family PD for `K ≤ K₀`; exact clock inertia `(n₊, n₋+n₀, 0)` with the negative next aliasing coefficient [L]. |
| Σ1l Polarization inheritance | Partially solved | sub | Every twisted sector with positive scalar second order, windows `≤ 3/5`, the cosh hyperplane below `log 2 + 1/50`, every window at `K ≤ K₀` (fixed families) [L]. Untwisted long windows at large `K` = Σ1. |
| Σ1m Bulk below the grid | Classified | — | All zeros of height `≤ λN` (`2λL ≤ π`) enter a fixed packet only through the pole; at fixed overlap every bulk entry is read by `γ, γ₁` and divisor logarithms (`2γ₁ + γ²` at the pole) [L]. |
| Σ1n Aperture-independent weighted floor | Solved (size-only) | — | `Q(H) ≥ −C(p)∫e^{−pu}H²` for every `p > 1` on every window of the negative half-line, `C(p)` independent of `A` [L]. Carries no information on the sign. |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | HR ∧ HL ⇔ strict HR; RH ⇔ HL on the PSD locus [L]. Zero modes: radical, reflection-parity, gap law, injective restriction to each end collar at a first critical length; lattice zero modes unique, palindromic up to sign; a first failure is two-site with zero mode `(1, ∓1)` [L/U]. |
| Σ2a Interior-gap continuation | No-go (as structure) | — | Three-angle curve `κ(d) = 1_{3∣d}`: first critical zero mode `(1,0,0,−1)` vanishes on the interior [L]. Not needed: two sites decide. |
| Σ3 Stars and dilation monodromy | Partially solved | — / RH | Stars isometric, depth law; monodromy eventually idempotent; Jordan coefficient a point count [L]. |
| Σ3a Coprime stratum | Sharpened | RH | gcd stratification; graded/top Möbius pair; Redheffer `det = M(N)` [L]. |
| Σ4 Finite index / heat count | Sharpened | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | `κ < ∞` ⇒ Lindelöf; RH ⇔ index `0`; `{0, ∞}` laws [L]. |
| Σ5 Collision quantum / window integer | Reduced (to Π17) | RH | Index `0` ⇔ Wiener–Hopf invertibility ⇔ outer Szegő factorization [L]. |
| Σ6 Rank / degree uniformity | Partially solved | RH | Rank 8 strict; fixed Jensen degree eventually hyperbolic; PF₃₇ [L]. |
| Σ7 Window Markov capacity | Sharpened | RH | Fold capacity criterion; exit charge to `1/7`; RH ⇔ `R ≤ ½` on the odd sector; Barta/Picone certificates sign-blind [L]. |
| Σ8 Realization | Sharpened | RH | RH ⇔ every window has an `ℓ²(zeros)` realization; the realization is explicit: `Q = 2Re[𝓦H, 𝓦H]` with bounded `𝓦_A` [L]; none finite-dimensional; no finite-rank realization of `K_ζ` [L]. |
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
| Σ22 Lefschetz operators | Classified | — | Dilation HL trivial; overlap-flow HL on HR locus is RH [L]. |
| Σ23 Connected links | No-go | — | Links disconnected [L]. |
| Σ24 Finite divisor | Solved | — | Coercive off `i/2` and a finite grid [L]. |
| Σ25 Semilocal and trace carriers | No-go | — | No `{∞,p}` positive carrier; exact `{∞,2}` trace through `½log 3` [L]. |
| Σ26 Approximation by RH-true objects | Classified | — | Closure class Laguerre–Pólya [L/D]. |
| Σ27 Window stages | Partially solved | sub (each stage); RH (all) | All real `C²` tests positive through total length `181/250·(1+6·10⁻⁷)`; first prime stage opens positive on `[log 2, 181/250]` (kick ≤ two-collar form, even ≤ prime-free frozen form); odd unit window `Q + (3203/320)(∫xF)² ≥ ‖F‖²/1000`, `Q ≥ ‖F‖²/100` off two odd moments, exact retained-Gamma identity `Q = R_ret + ∫(nonnegative remainder) + 2·reserve‖F‖²`, prime-2 strip coercivity `‖G‖²/16`, frozen odd form `Q₁ + 20M² ≥ ‖F‖²/125`; second stage path `α² + β ≤ 1` [L]. One first-moment direction of the odd unit window open. No sign theorem on `[0.7243, log 3)` [N margins `1.5×10⁻⁵` odd, `5.6×10⁻⁸` even]. |
| Σ28 Window negativity budget | Sharpened | ≥qRH (exponent `< ½`); RH (subexponential) | Floor `−(deg K_A + 2sinh(A/2) − A)‖H‖²`; two-bump negativity rate = maximal depth; orbit-correlation rate = zero width [L]. |
| Σ29 Low-frequency localization | Solved | — | Negativity only at the poles and below `τ₀(a)` [L]. |
| Σ30 The stage step | Sharpened | RH (as induction); each stage sub | Stage criterion `2wc_H(ℓ) ≤ S^N_A(H)`; kick law; `S` born zero, monotone in the collar width; kick = collar Rosati pairing, positive source on even–antisymmetric and odd–symmetric data; stage test `Q = F − 2w⟨x_L, Jx_R⟩` with `F` in closed form; Carathéodory disk; lattice admission `|β_n − kick| < E_n` [L]. Lossy forms refuted at the first prime [L]. |
| Σ31 Positivity across dimension zero | Classified | equivalent to Σ1 | Bare domination ⇔ `Q ≥ 0`; no uniform archimedean family; Euler-product pole weight forced and refuted [L]. Consequence: the count/Hodge/degeneration programme cannot close RH [D]; a count-based positivity would have to beat parity at first order (Bombieri's `Λ_j`). |
| Σ32 Prime-blind positivity | Sharpened | RH | Weil cone `{Λ}`; node-critical; finite-level Farkas duality; zero-side identity on blind tests; solved on nonnegative and separated-bump cones [L]. |
| Σ33 Tate positivity horizon | Classified | — | Exact horizons at stages 1–2; no `k > 0` uniform [L]. |
| Σ34 Canonical-degree horizon | Classified | — | Every soft deformation paid by the counts has horizon `≍ e^{−A/2}`; exact margins doubly exponential [L/D]. |
| Σ35 Two-collar recursion | Partially solved | identity | Lattice: Levinson recursion, margins `κ(0)∏(1−γ_k²)`, newest datum linear in `β_n`, causality [L]. Continuum: translation contraction and Carathéodory disk [L]; no unnormalized continuum limit; the `n`-th margin is born at order `h^{2n}` (first at `h²` with coefficient `Σm_ργ_ρ²|φ̂(γ_ρ)|²`) [L]. A continuum canonical system (Hamiltonian with the prime kicks) is not constructed. |
| Σ36 Rational Hecke-graph reading | Solved (identity) | — | Window arithmetic on finite `S ⊂ ℚ_{>0}` = Hecke operator of `ℤ[ℚ^×_{>0}]` [L]. |
| Σ37 Lattice canonical system | Solved (identity) | — | Window ⇔ all lattices of total length `≤ A`; positive windows have outer predictors; refinement lowers margins; single-kick law; admission interval for a new weight [L]. |
| Σ38 Two-site decision | Classified | — | RH ⇔ two-site PD ⇔ strict orbit Cauchy–Schwarz; off RH equality `|c_ψ(s)| = Q(ψ)` for a short generic bump [L]. |
| Σ39 Trivial-divisor transmission | Solved (identity) | — | Ordered tests couple through `e^{x/2} − Σ_{k≥1}e^{−(2k+½)x}` (pole `+`, trivial zeros `−`) and the prime lags; across prime-free separations only the moments `μ_s ν_s`, `s ∈ {1, −2k}` [L]. |
| Σ40 Degenerations are curves | Classified | — | Degenerate lattice windows are finite curves (Carathéodory–Fejér); a conjugation-closed curve fails exactly at its number of angles; Spec ℤ under RH is the curve with angles `e^{iγ_ρh}` on every lattice, Szegő singular (`Σγ² = ∞`, margins `→ 0`) [L]. The pole is the hyperbolic pair `e^{±h/2}` with one negative square [L]. |
| Σ42 Markov and sign-blind ground states | No-go | — | No cofinal Markov (Beurling–Deny) passage (`KR-BD`); full folded calibration fails at `a = ½log 2` (`#folded-markov`); lossless local allocation fails (`KR-LGP`); shifted ground-state combinations fail (ACT) [L]; Barta/Picone weights are sign-blind [L/D]. Survivors: variable-hub Schur elimination; signed supersolutions; the odd supersolution criterion `riemannHypothesis_of_foldedSupersolution` [L]. |
| Σ41 Contact law | Open | sub | RH to height `T` ⇒ windows to length `c log T`? Model boundary sharp at `c = ½` in both directions [M]; contact aperture `≥ 3/10` and bounded above by near-top zeros [L]. |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (equivalence) | RH | `ψ(x) − x ≤ C√x log²x` ⇔ RH ⇔ `κ = 0`; Redheffer `det R_N = M(N)` [L]. |
| Π2 Deciding input | Open | RH | No unconditional source input at square-root precision. |
| Π3 Producer cost | Partially solved | sub / RH | Multivariate parity producers reach `(1+ε)x + C_εlog²x`; individual producers slope `> 1`; integer-Chebyshev ceiling [L]. |
| Π4 Window precision (kernel = coupling) | Sharpened | RH | Two-site entry = pole moment − trivial-zero moments − `ψ⋆ψ`-smoothed prime sum on `[e^{t−2r}, e^{t+2r}]`; RH ⇔ that smoothed count is within `Q(ψ)` of its main term at every scale [L/D]. |
| Π5 Conjugate diagonal | Sharpened | sub → ≥qRH → RH | Means `O_c(log U)`; `o(log U)` ⇔ clustering; one dyadic constant ⇔ RH [L]. |
| Π6 Averages versus all heights | Sharpened | — | Double-log stage outside `O(V/log log V)` windows; right half-port `O(e^{(3loglogV/logV)t}/(t+1))` there; exact critical-line flux on `(1−O(B))V` micro-Planck windows [L]. |
| Π7 Census / pair surplus | Partially solved | sub | Simple critical `≥ 0.67250071`; positivity-only certificates cannot reach `3/4` [L]. |
| Π8 Depth visibility | Partially solved | — | Cluster-product horizon: depth `≥ 1/a`, height `≤ exp(a/(10⁵A₀ log a)) − 306` seen in `[−(a+1), a+1]` [L]. |
| Π9 Exceptional moduli | Partially solved | sub | Uniform zero-free region and Siegel for `q ≤ (log x)^A`; Mertens constants in progressions via Newman's theorem [L]. |
| Π10 Frequency localization | Solved | — | Every eventually positive cyclotomic band has energy abscissa `2Θ` [L]. |
| Π11a–e Cone, bidegree, fixed-rank, definite, Siegel counts | No-go | — | Excluded as independent sign producers [L]. |
| Π11f Logarithmic duality | Partially solved | sub | Pole plane: Abel completion, logarithmic RR [L]. |
| Π11g Boost transform | Solved (identity) | — | `∫Z⁺(s,u)e^{2wu}du = K(s,w)ζ(s+w)ζ(s−w)` [L]. |
| Π11h Count-valued primitive `h¹` | Sharpened | RH; fixed length sub | Window `h¹ = ½Q`; Weil's form a signed count [L]. As a mechanism closed with Σ31 [D]: every concrete count type is excluded (Π11a–e, Π20) and no corpus result exempts rank-2 spans `{ψ, τ_tψ}`. |
| Π12 Subconvexity / heat floor | Partially solved | sub | `μ(½) ≤ 33/200`; heat floors `133/200`, `2/3 + ε` [L]. |
| Π13 Prefix scale | Solved | — | Strip zeros `Θ(N² log N)`; stabilization `Θ(√m)` [L]. |
| Π14 Amplifier rank | No-go (finite support) | — | Growing losses keep radius `Be^λ` [L]. |
| Π15 Critical-scale residual sign | Classified | — | Residual = prime-free aliasing term + Weil's form [L]. |
| Π16 Genus function | Sharpened | indep. | Genus `≥ (2−η)e^A` + multiplicity excess [L]; upper law open. |
| Π17 Window energy | Sharpened | RH; ≥qRH (log stage) | Abscissa = twice the maximal depth; zero-free window ⇔ unweighted `L²` port; bounded port ⇔ local critical-line purity; polynomial stage ⇔ RH [L]. |
| Π18 Finite realizations | No-go | — | No finite-dimensional window realization [L]. |
| Π19 Mollified log-mean from moments | No-go | — | Moments do not determine the log-mean [L]. |
| Π20 Count identities and cost-only payments at the first prime | No-go | — | No finite-square identity for `log 2 ≤ A < 2log 2`; `Q₁ < 0 < Q` [L]. |
| Π21 Exact balance | Classified | — | Weil cone `{Λ}`; `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})`; Szegő singular under RH [L]. |
| Π22 Near-line density ladder | Sharpened | sub | Eight equivalent forms; almost-all log-stage certificates ⇔ `D_win` ⇔ thin Planck shadows; `D_zero` ⇔ `D_win` + vanishing giant-cluster tails; `(log V)²` per-window factor unimprovable under occupancy [M]; uniform Planck volume ⇏ occupancy [M] [L]. |
| Π23 Inner caps | Open | RH (all degrees); ≥qRH (fixed degree) | Caps cancel to `σ_m = 1 − 1/(116log(m+5))` [L]. |
| Π24 Parity at dimension zero | Classified | — | Jets generated by `M` and `ρ_A(Λ)`; Selberg `Λ₂` constraint [L]. |
| Π25 Euler-product pinning | Classified | — | Shifted-pole weight `= 1/ζ(1+k)`, refuted [L]. |
| Π26 Bulk second order | Solved (fixed overlap) | — | `2γ₁ + γ²` at the pole; `D(p,p) = D(1,1) + p log²p/(p−1)²`; character packets read `L'/L(1,χ)`, `(L'/L)'(1,χ)` [L]. |
| Π27 Retained Gamma comparison | No-go (as lossless) | — | The quintic window has retained lower form `< 0 < Q` [L]. Survivor: exterior Gamma reserve `1/128`; positive first-moment reflection inverse [L]. |

## Γ — selection and reflection

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point | Open | RH | `Θ ≥ ½`, Haar-a.e. `½`, Baire-generic `1` [L]. |
| Γ2 Prime-set flips | Solved | — | Every nontrivial prime pattern separated at every density [L]. |
| Γ3 Twin-blindness of soft structure | No-go | — | Krein index invariant under unitary twists [L]. |
| Γ4 Frobenius at infinity | Sharpened | RH | RH ⇔ `σ` trivial ⇔ Hecke similitude ⇔ partner saturation; `σ_A` = Rosati involution; window involution = conjugate-linear `e^{−A(2s−½)}`-twisted Krein reflection; the kick is the collar Rosati pairing [L]. |
| Γ5 Source identification / pre-divisor | Partially solved | RH | Pre-divisor sections need zero-independent forcing [L]. |
| Γ6 Boundary sign / coherence | Solved | — | Pole boundary sign separates ζ from size twins [L]. |
| Γ7 Affine carrier | Solved | — | Gluing at a place; subgroup classification [L]. |
| Γ8 Poisson rigidity | Sharpened | RH | Zero-side positivity = RH [L]. |
| Γ9 Archimedean continuity vs height decay | No-go | — | ⇒ `κ = ∞` [L]. |
| Γ10 Function-field indistinguishability | Sharpened | — | Pure curves: sums of squares at every resolution with Hurwitz weights of the angles; a twist frequency `u` over ℤ contributes the Hurwitz form of an angle `u`; the untwisted direction is the pole `u = 0` of the frequency counts, where Weil's form sits; monodromy rate of a curve = zero width [L]. |
| Γ11 Pole-blindness of the glue | No-go | — | Simple pole absorbed [L]. |
| Γ12 General gauges | Solved | sub | Harmonic saturation only at the Euler gauge [L]. |
| Γ13 Source-uniform extinction | No-go | — | Fails at `3/4 + i` [L]. |
| Γ14 Local counterterm selection | No-go | — | Flip twin glued index `1` [L]. |
| Γ15 Functional-equation twins | Partially solved | sub | Degree three and positive degree two admit off-line real zeros; positive finite Euler twins (degree one, positive bounded multiplicative coefficients agreeing with ζ below any prefix) have zeros at any `Re s ∈ (½,1)` and violate only the strict Euler bound `θ < ½` [L]. |
| Γ16 Selection–sign gap | Sharpened | RH | No selector gives positivity [L]. |
| Γ17 Scattering recentering | Classified (no-go) | — | Rational/algebraic recentering impossible [L]. |
| Γ18 Divisor-identity selection | Solved | — | Only `Λ` degenerates completely [L]. |
| Γ19 Correspondence algebra over ℤ | Sharpened | RH | Rosati positivity ⇔ orbit Hodge index ⇔ naive height at bounded distance [L]. |
| Γ20 Window selection | Classified | — | Bounded windows blind; flip twin identical on length-`A` tests is not Weil positive [L]. |
| Γ21 Density selection on the natural cone | No-go | — | RvM-count exact-spline countermodels [L]. |
| Γ22 Contractive scattering positivity | No-go | — | Blaschke pairs keep every Schur inequality [L]. |
| Γ23 Weil cone uniqueness | Solved | — | Full Weil positivity forces `Λ`; lattice margins all positive only for `λ = Λ` and RH; every single prime power, deletion, or the free evolution degenerates some lattice [L]. |
| Γ24 Mayer reflection positivity | Sharpened | RH | Resonance ⇔ `ζ(2s) = 0`; `D_s ≤ 0`, `= 0` iff `Re s = ¼`; Krein positivity ⇔ RH; exact completion `Q = 2Re[𝓦H, 𝓦H]`; finite packets: renormalized mean cusp energy = Krein square, counterterm subtraction does not preserve positivity [L]. Bounded reflection only for `Re s ≥ ¼` [L]. Open: finite cusp energy ⇒ `D_s = 0`; no candidate mechanism. |
| Γ25 Two reflection centres | No-go (as operator symmetry) | — | Transfer reflects about `Re w = 1`, zeta events about `Re w = ½` [P]. |
| Γ26 Resonant-state selectors | No-go | — | Inversion fixes every resonant period; cutoff Grams retain the rate [L]. |
| Γ27 Tate counts as a selector | No-go | — | `ζ(s)ζ(s−ε)` Tate positive, not Weil positive [L]. |
| Γ28 Frobenius inside the window algebra | No-go | — | Same-window similitudes scalar [L]. Survivor: Frobenius at scale `t` is translation by `t`; `T_p − Id` = `√pH(·+log p)` for every prime, similitude factor `p` = translation invariance [L]. |
| Γ29 Linear Serre–Krein identification | No-go | — | No real-linear isometry [L]. Survivor: the exact conjugate-linear twisted identification [L]. |
| Γ30 Completed Tate family | Classified | — | Unimodular on the line [L]. |
| Γ31 Degeneration type over `𝔽_q` | Solved (calibration) | — | Pure curves degenerate completely; impure curves have exponential monodromy at exactly their zero width in both signs; golden fake rate `log φ/log 5` [L]. |
| Γ32 Hecke-equivariant completion | Solved (identity) | identity | `𝒦 = ℓ²(upper Mayer resonances)`, `[x,y] = Σx_s conj(y_{s♯})`; PM cores dense; bounded window map; Hecke multiplier `p^{1−2s}`; reflection twisted conjugate-linear [L]. |
| Γ33 Euler rigidity in the Selberg class | Solved | — | Euler-log discrepancy absolutely convergent at `σ = ½` ⇒ equality, no Gamma matching; finite-prime and finite-support rigidity; degree zero = Dirichlet unit; no degree in `(0,1)` [L]; degree one: conductor `≥ 2` or a pole at `1` [L]. |
| Γ34 Hecke cones and periods | Solved | — | Hecke cones of determinant `n` tile the quadrant; Barnes and Eisenstein/Lewis periods are Hecke eigenfunctions with eigenvalue `1 + p^{1−2s}` for every prime; positive-determinant Hecke operators preserve the Lewis carrier [L]. |
| Γ35 Beurling and Hamburger rigidity | Classified | — | Positive prime measures with integers more regular than `ℕ` (`N(x) − ρx − C → 0`) admit a zero at any `Re s ∈ (½, 2/3)`, any height (continuous Beurling systems) [L]; a positive measure with Riemann's functional equation is the counting measure of `ℕ`, and a discrete Beurling system with it is the rational primes [L]. The functional equation together with the Euler product is the minimal input of any proof. |

## Bridges

| Bridge | Anchor |
|---|---|
| `κ(K_ζ)` = right zeros = `sup_A ι(A)` = band poles of `Λ(s)/Λ(s+1)` = upper-right Mayer resonances; even; RH ⇔ `κ < 2` | HKT, RIT, CWS, AOG [L] |
| Window sign ⇔ two-site sign; first failure two-site | GWZ [L], AOG [L] |
| Two-site entry = trivial-divisor moments − smoothed prime sum (Σ on two sites = Π at one point) | CSTW [L]; [D] |
| Window ⇔ its lattices; Weil sequence ⇔ Toeplitz data; kick ⇔ one Schur parameter | GWZ [L] |
| Degenerate window ⇔ finite curve; Spec ℤ under RH ⇔ infinite-angle curve, Szegő singular | GWZ [L] |
| Stage step = two-collar race; kick = collar Rosati pairing; frozen form in closed form | GWZ, CSTW [L] |
| Window algebra = truncated Dirichlet λ-ring; `ρ_A(Λ) = [M, log Z]` | WTZ [L] |
| Weil's window form = dimension-zero jet of the Tate family; positive dimension classified | WTZ, DZG, ATD [L] |
| Complete family at the critical curve = Weil at the pole of the frequency counts + positive counts | AHD [L] |
| Frobenius angle over `𝔽_q` ≡ twist frequency over ℤ; untwisted window ≡ pole at `u = 0` | AHD [L] |
| Weil energy = Krein form of zero coordinates; Hecke = translation; reflection = window involution | RIT [L] |
| Weil cone `{Λ}`; lattice selection; prime-blind nonemptiness | RHTower, GWZ [L] |
| Near-line density: eight forms; occupancy ⇔ thin Planck shadows | CDG [L] |
| One cyclotomic mode carries `2Θ` | CAF [L] |
| Gluing `κ(φ_c) = κ + 1`; Redheffer `det = M(N)` | AKG, ADT, HWV [L] |

## Status counts

| Family | Solved | Partially solved | Sharpened | Open | No-go | Classified | Reduced |
|---|---|---|---|---|---|---|---|
| Σ (58) | 13 (Σ1a, Σ1b, Σ1c, Σ1h, Σ1n, Σ10, Σ12, Σ16, Σ24, Σ29, Σ36, Σ37, Σ39) | 10 (Σ1d, Σ1e, Σ1g, Σ1j, Σ1l, Σ3, Σ6, Σ9, Σ27, Σ35) | 11 (Σ1, Σ2, Σ3a, Σ4, Σ7, Σ8, Σ17, Σ19, Σ28, Σ30, Σ32) | 3 (Σ18, Σ20, Σ41) | 7 (Σ1f, Σ2a, Σ13, Σ14, Σ23, Σ25, Σ42) | 13 (Σ1i, Σ1k, Σ1m, Σ11, Σ15, Σ21, Σ22, Σ26, Σ31, Σ33, Σ34, Σ38, Σ40) | 1 (Σ5 → Π17) |
| Π (34) | 5 (Π1, Π10, Π11g, Π13, Π26) | 6 (Π3, Π7, Π8, Π9, Π11f, Π12) | 7 (Π4, Π5, Π6, Π11h, Π16, Π17, Π22) | 2 (Π2, Π23) | 10 (Π11a–e, Π14, Π18, Π19, Π20, Π27) | 4 (Π15, Π21, Π24, Π25) | — |
| Γ (35) | 10 (Γ2, Γ6, Γ7, Γ12, Γ18, Γ23, Γ31, Γ32, Γ33, Γ34) | 2 (Γ5, Γ15) | 6 (Γ4, Γ8, Γ10, Γ16, Γ19, Γ24) | 1 (Γ1) | 12 (Γ3, Γ9, Γ11, Γ13, Γ14, Γ21, Γ22, Γ25, Γ26, Γ27, Γ28, Γ29) | 4 (Γ17, Γ20, Γ30, Γ35) | — |

Strength of the open walls:
- **RH:** Σ1 (minimal form: the two-site band), Σ2, Σ3a, Σ6, Σ7, Σ8, Σ17, Σ18, Σ19, Σ20, Σ27 (all
  stages), Σ28 (subexponential), Σ30, Σ32, Π2, Π4, Π11h, Π17 (polynomial stage), Π23 (all degrees), Γ1,
  Γ4, Γ5, Γ8, Γ16, Γ19, Γ24.
- **identity:** Σ35 (continuum canonical system).
- **≥qRH:** Σ4 (`K_ζ`), Σ28 (exponent `< ½`), Π5 (fixed scale), Π17 (log stage), Π23 (fixed degree).
- **sub:** Σ1d, Σ1e, Σ1g, Σ1j, Σ1l, Σ4 (zero–one law), Σ27 (each stage), Σ30 (each stage), Σ41, Π3, Π5
  (mean `o(log U)`), Π7, Π9, Π11f, Π11h (fixed length), Π12, Π22, Γ15.
- **indep.:** Π16.
