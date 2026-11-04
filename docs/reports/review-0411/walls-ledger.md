# Walls ledger — status quo

Three wall families block every route: **Σ** the critical sign, **Π** precision and production,
**Γ** selection and reflection. All three read one even integer, `κ = κ(K_ζ) = #` distinct zeros right
of the critical line, on the window tower `A ↦ W_A` (`κ = sup_A ι(A)`), and all three are decided on the
**two-site window** `{f, f∘R}` of a test and its mirror image.

- **Σ is the sign of every window, decided on reflection pairs and paid by the primes with sign.** RH ⇔
  `|c_ψ(t)| < Q(ψ)` for every bump and `t ≠ 0` [L]; `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)` [L]. Below window
  length `log 4` the sign is the membership of `(Λ(2)/√2, Λ(3)/√3)` in an explicit compact convex set, and
  exact certificates must retain the pole variance [L]. The edge-law bound on the summed reflection terms (kicks)
  of the band stays below the Lévy energy on every window shorter than `log 5` [L/D]; the primes are needed as payers of the prime-free
  archimedean–polar deficit (Markov part negative beyond `e^{−3/4}`, `w₂ ≤ 0` inadmissible) and pay
  through the signature of their sliver reflections [L].
- **Π is the same band read on the prime side.** `𝒞_m(f) = 𝓗_m(f) − Σ_nΛ(n)n^{−1/2}(f⋆f)(2m − log n)`
  [L]: the collective payment of the kicks is the smoothed prime count of `f⋆f` matching the pole square
  within `W(f)` — the square-root form of RH; below `log 4` it is a two-term prime count. Production by
  counts is closed [D]; the size-only floor carries no zero information [L/D].
- **Γ is reflection and identification.** The completed PM space is `ℓ²(zeros)` with
  `Q = 2Re[𝓦H, 𝓦H]` [L]; the co-isometry defect of a fixed period is `−∫2cosh(δu)4sinh²(δu)|F(u)F(−u)|`,
  so the PM sign is the identity `δ = 0` [L/D]; the explicit formula identifies configurations up to a
  density threshold, sign-free; blindness costs exactly `π` times the density [L]. Selection is automatic
  after positivity [L]; positivity is the open half.

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact
form a theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a
classification or identification theorem), **Reduced** (theorem-level equivalent of the wall named).
Strength: **RH**, **≥qRH** (zero-free half-plane or Lindelöf), **sub**, **indep.**, **identity**,
**method**. Evidence: `[L]` committed Lean; `[W]` working-tree Lean; `[D]` derived here; `[M]` exact model
statement; `[N]` numerical; `[P]` paper. Window half-widths `a` or `c`; `c_ψ(t) = W(ψ(· − t), ψ)`;
`w_n = Λ(n)n^{−1/2}`; `h` the collar half-width of `n`; `δ` the sliver width `2c − log n`.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign | Sharpened | RH | RH ⇔ `Q ≥ 0` on every window ⇔ two-site PD ⇔ strict orbit Cauchy–Schwarz ⇔ band at the centre in both parity sectors ⇔ Stieltjes moment problem of jet energies for every even bump ⇔ every lattice Schur parameter in `(−1,1)` ⇔ `ι(A) = 0` ∀A ⇔ `R₁(A) = ⊤` ∀A ⇔ Krein positivity of zero coordinates ⇔ prime-blind positivity ⇔ canonical domination [L]. One generic bump decides [L]. |
| Σ1a Critical overlap and receivers | Solved | — | `c*_N ≍ L(log L)²`; tilted-spline receiver at every `K(log N)^{1/8}`; unit-bump receiver; one Beurling profile realizes every finite rational Gram [L]. |
| Σ1b Subcritical regime | Solved | sub | Complete matrix PD for `1 ≤ c ≤ (log N)^α`, `α < 1/8`, floor `κ/(2c⁷)` [L]. |
| Σ1c Joint shell–pole payment | Solved | sub | Prime-successor edges pay nonconstant packet mass; row-split Schur synthesis [L]. |
| Σ1d General profiles | Partially solved | sub | Positivity on spans `θ < 1/1080` through `b_φlog log N`; polylog spans through `Klog log N`; super-log-log clocks [L]. |
| Σ1e Conductor barrier | Partially solved | sub | Count form uniform for `m = o(c)`, `≤ ½` for `m ≥ λ₀c`; low block `≤ ⌊(log N)^{13/32}⌋` keeps half its diagonal plus the polar part at every ratio; large-prime cofactor frames [L]. |
| Σ1f Defect-only confinement | No-go | — | `Q < 2^k` witnesses [L]. |
| Σ1g Haar / Gamma graph | Partially solved | sub | All-detail prime–pole cancellation `O(exp(−√log Y/92160000))`; index `≤ R + A`; growing Euler heads unbounded [L]. |
| Σ1h Smooth logarithmic profile | Solved (to `ε₀c*`) | sub | Positive to `ε₀L(log L)²`; budget sharp [L]. |
| Σ1i Second order on horizon blocks | Classified | — | `κQ(H) + (βJ/K)∫e^{−(β+1)y}H²`; pencil index `#{λ_i < 0 : βJ/(−λ_i) < K}` [L]. |
| Σ1j Critical-curve decomposition | Partially solved | sub | Ramanujan, periodic, trigonometric, primitive characters solved; frequency counts have a pole of order `β+1` at `u = 0` with finite part the untwisted count [L]. Open: whole twisted sector at every multiple. |
| Σ1k Whole space at one critical multiple | Solved | sub (size-only) | PD of the complete matrix on the whole prime-horizon space for `1 ≤ c ≤ 2K₀(log N)^{1/8}` with every window corollary [L]. |
| Σ1l Window threshold | Sharpened | RH | `R₁(A) = inf{7J(1)M₈(H)/(a_φ|Q(H)|) : Q(H) < 0}`; antitone; `≥ R₀ > 0`; `⊤` up to `2·enlargedWeilFloorAperture`; RH ⇔ `R₁ ≡ ⊤`; joint pole payment enlarges the certified interval [L]. |
| Σ1m Polarization inheritance | Partially solved | sub | Every twisted sector with positive scalar second order, windows `≤ 3/5`, the cosh hyperplane below `log 2 + 1/50`, every window at small ratio [L]. |
| Σ1n Bulk and growing overlap | Classified | — | Bulk below the grid reads only the pole; growing-overlap entries linear and polar [L]. |
| Σ1o Aperture-independent weighted floor | Solved (size-only) | — | `Q(H) ≥ −C(p)∫e^{−pu}H²`, `p > 1`, forced by Cauchy–Schwarz on the pole moment; exponent `p` gives only zero width `≤ p` [L/D]. |
| Σ1p Terminal windows | Classified | — | Every compact logarithmic window has an exact complete mixed limit at all positive critical ratios; polar source = boundary logarithm + finite prime-power mean; nonpolar sources vanish (centre and divisor jet cancel); nonzero polar source exists; nontrivial kernel [L]. |
| Σ1q Receiving charges | Classified | — | Charges survive vanishing raw, physical and complete energy; capacity `log log N + O(1)`; simultaneous receiving law (reading factor `1/80`); complete physical energy vanishes for independent scales; exact neutral mixed channels with bounded Mertens correction; receiver determinant `→ 6239t²/6400 > 0` [L]. Open: uniform assembly of the complement. |
| Σ1r Conductor packets and correctors | Classified | — | Terminal sources concentrate at the pole through exponent `13/32`; summable sources; vanishing mixed mass above overlap; low correctors cannot improve zero-source windows; exact low-packet capacity attained by one pole coefficient; full conductor diagonal overprices terminal windows [L]. |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | HR ∧ HL ⇔ strict HR; RH ⇔ HL on the PSD locus; zero modes radical, reflection parity, gap law; first failure two-site; tight band ⇒ reflection-pair zero mode [L]. |
| Σ2a Interior-gap continuation | No-go (as structure) | — | `κ(d) = 1_{3∣d}` [L]. Two sites decide. |
| Σ2b Edge singularity | Classified | — | No smooth window eigenfunction; no smooth solution of any window equation with exponential-polynomial source (constrained ground states, capacity maximizers); nonnegative windows PD on smooth tests; strict band on smooth tests [L]. Decisive extremals live in the energy completion at the edge. |
| Σ3 Stars and dilation monodromy | Partially solved | — / RH | Stars isometric, depth law; monodromy eventually idempotent [L]. |
| Σ3a Coprime stratum | Sharpened | RH | gcd stratification; Redheffer `det = M(N)` [L]. |
| Σ4 Finite index / heat count | Sharpened | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | `κ < ∞` ⇒ Lindelöf; RH ⇔ index `0`; `{0, ∞}` laws [L]. |
| Σ5 Collision quantum / window integer | Reduced (to Π17) | RH | Index `0` ⇔ Wiener–Hopf invertibility [L]. |
| Σ6 Rank / degree uniformity | Partially solved | RH | Rank 8 PD at every `0 < a < ½`; every finite rank on factorial and logarithmic collars; theta atoms and the native fifth even source PD for `q ≥ 5`; fixed cross-load PD near endpoints and for `q ≥ 5000`; at `q = 8`, load multiples are PD iff `t < τ`, PSD iff `t ≤ τ`, with `½ < τ < 1` and singular boundary [L]; fixed Jensen degree eventually hyperbolic; PF₃₇ [L]. |
| Σ7 Window Markov capacity | Sharpened | RH | Fold capacity criterion; RH ⇔ `R ≤ ½` on the odd sector [L]. |
| Σ8 Realization | Sharpened | RH | RH ⇔ every window has an `ℓ²(zeros)` realization `Q = 2Re[𝓦H, 𝓦H]`; no finite-rank realization [L]. |
| Σ9 Explicit image / resolvent | Partially solved | RH in strip | Depth identity for `σ > 1`; theta–prime expression at `s = 4` [L]. |
| Σ10 Local signatures and gluing | Solved | — | `κ(φ_c) = κ + 1` at `∞` and every prime [L]. |
| Σ11 Product-formula gluing of the pole | Classified | — | Local poles add squares; extremal weight = archimedean pole on `S`-units [L]. |
| Σ12 Running counterterm / star flux | Solved | — | `log N − γ` cancels the prime diagonal [L]. |
| Σ13 Tensor amplification | No-go | — | `K_ζ^n` PD ⇔ RH; `n₋(G⊗G) = 2n₊n₋` [L]. |
| Σ14 Deformation to a positive model | No-go as free input | — | Crossing-free path ⇔ PD [L]. |
| Σ15 Separable assemblies | Classified (no-go) | — | Blind when truncated, non-convergent when untruncated [L]. |
| Σ16 Prime–pole coherence | Solved (identity) | — | Complete form = jump + incidence − shell + diagonal + boundary [L]. |
| Σ17 Inter-tower coupling | Sharpened | RH | Bounded dense coupling ⇔ RH; damped cone ⇔ RH [L]. |
| Σ18 Exact SOS on a two-prime lattice | Open | RH | Generic Hecke orbit carries the full Hodge defect [L]. |
| Σ19 Rank-one intertwining coefficient | Sharpened | RH | `κ_Hodge = #` band poles of `Λ(s)/Λ(s+1)` [L]. |
| Σ20 Scheduled prime sums | Open | RH | FU, CFC, RP, SZ, LI, FEL, EGC receivers [L]. |
| Σ21 Extension / carrier | Classified | — | Escape, mixing, height decay ⇒ `κ ∈ {0, ∞}` [L]. |
| Σ22 Lefschetz operators | Classified | — | Dilation HL trivial; overlap-flow HL on the HR locus is RH [L]. |
| Σ23 Connected links | No-go | — | Links disconnected [L]. |
| Σ24 Finite divisor | Solved | — | Coercive off `i/2` and a finite grid [L]. |
| Σ25 Semilocal and trace carriers | No-go | — | No `{∞,p}` positive carrier; exact `{∞,2}` trace through `½log 3` [L]. |
| Σ26 Approximation by RH-true objects | Classified | — | Closure class Laguerre–Pólya [L/D]. |
| Σ27 Window stages | Partially solved | sub (each stage); RH (all) | All real `C²` tests positive through length `181/250·(1 + 6·10⁻⁷)`; floor `‖f‖²/8000` up to `enlargedWeilFloorAperture`; first stage opens positive; at length `21/20` admissible prime-two weights exclude `0` and `−w₂`; odd unit window bounds off one moment [L]. No sign theorem on `c ∈ (enlargedWeilFloorAperture, log 2)` [N margins `1.5×10⁻⁵` odd, `5.6×10⁻⁸` even at `c = ½log 3`]. |
| Σ28 Window negativity budget | Sharpened | ≥qRH (exponent `< ½`); RH (subexponential) | Floor `−(deg K_A + 2sinh(A/2) − A)‖H‖²`; ground-energy floor `−Ce^{2σA}` ⇔ zero width `≤ σ` [L]. |
| Σ29 Low-frequency localization | Solved | — | Negativity only at the poles and below `τ₀(a)` [L]. |
| Σ30 The stage step | Sharpened | RH (as induction); each stage sub | Stage criterion; kick = collar Rosati pairing; frozen form in closed form; lattice admission [L]. Soft entry makes the step a margin transport (Σ52). |
| Σ31 Positivity across dimension zero | Classified | equivalent to Σ1 | Bare domination ⇔ `Q ≥ 0`; counts/Hodge/degeneration cannot close RH [L/D]. |
| Σ32 Prime-blind positivity | Sharpened | RH | Weil cone `{Λ}`; node-critical; Farkas duality; solved on nonnegative and separated-bump cones [L]. |
| Σ33 Tate positivity horizon | Classified | — | Exact horizons at stages 1–2; no `k > 0` uniform [L]. |
| Σ34 Canonical-degree horizon | Classified | — | Soft deformations paid by counts have horizon `≍ e^{−A/2}` [L/D]. |
| Σ35 Canonical system of the tower | Partially solved | identity | Lattice Levinson recursion; continuum margins `h^{−2n}E_n → det J_{n+1}/det J_n > 0` on every nonnegative window and the base; reflection coefficients `γ_n → (−1)^n`, `(1 − γ_n²)/h² → e_{n+1}/e_n`; parity split `det J_n = det E·det O` [L]. Global Hamiltonian with the prime kicks: not constructed. |
| Σ36 Rational Hecke-graph reading | Solved (identity) | — | Window arithmetic on finite `S ⊂ ℚ_{>0}` = Hecke operator [L]. |
| Σ37 Lattice canonical system | Solved (identity) | — | Window ⇔ its lattices; refinement lowers margins [L]. |
| Σ38 Two-site decision | Classified | — | RH ⇔ two-site PD; off RH `|c_ψ(s)| = Q(ψ)` for a short generic bump [L]. |
| Σ39 Trivial-divisor transmission | Solved (identity) | — | Collar Hankel form, inertia `(1, ∞)`, negative definite on the pole hyperplane [L]. |
| Σ40 Degenerations are curves | Classified | — | Degenerate lattice windows are finite curves; Spec ℤ under RH the infinite-angle curve [L]. |
| Σ41 Aperture–depth duality | Partially solved | sub | Fall rate of the window ground energy = zero width under bounded clustering, two-sided for finitely many off-line zeros; sustaining a larger depth-floor factor needs heights doubly exponential in the aperture (DCI); window positivity at `R` excludes depth `≥ 1/R` up to height `exp(R/(10⁵A₀(log R)²)) − 306` [L]. Tilt amplification: an isolated zero of depth `δ` at height `T` is seen at half-width `≈ (1/2δ)log log T`; spread lattice-like off-line sets hide up to `¼log T` [D]. Open: the sharp onset law (B47). A contact law at scale `c log T` forces every lowest off-line zero to be shallow or hidden: a zero-location statement [D]. |
| Σ42 Markov, sign-blind and variance-free ground states | No-go | — | Markov part negative on a test of support `e^{−3/4}`; no Markov supersolution on longer intervals; folded criterion void on the unit odd window; folded calibration fails; lossless local allocation fails; variance-dropped odd certificates fail for `c > 273/400`; nonnegative even theta-gauge cosh certificates fail; the prime `3` as a worst-case collar potential fails for `c ≥ 287/500` [L; W]. |
| Σ43 Pole-charged ground-state calculus | Solved (identity) | — | `Ẑ(Φωu) = J_{Φω}(u) + ∫u²ω𝒢_S(ω) + 2V_s − 2V_c`; theta gauges critical on the line; dropped variance = all-pairs jump form; gauge-extension invariance; below `log 4` retained-variance theta gauges (even) and shifted ground states (odd) are exact certificates ⇔ positivity [L]. |
| Σ44 Collar locality of the kick | Classified | — | Collar-internal jumps pay the kick of `n` at ratio `2w_ne^h`, sharp; prime `3` unpaid by its collar; `2w_n < 1` for `n = 2`, proper prime powers, primes `≥ 79` [L/D]. Outward jumps of the sliver carry the newest prime power at ratio `w_ne^h/2 ≤ e^{h−1}` within `h` of entry; every `n` costs `≤ (Λ(n)e^c/(2n))·levyEnergy` [L]. |
| Σ45 Reflection pairs and parity sectors | Solved (identity) | — | `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; sectors = band at the centre; Markov–Hankel form of each sector [L]. |
| Σ46 Frustration of the odd sector | Classified | — | Frozen odd form Markov, kick anti-Markov; kick = source − conductance; odd light cone `≥ 0` [L]. |
| Σ47 Odd unit window | Open | sub | Positivity ⇔ `w₂ = log 2/√2 ∈ unitBandWeights` (convex) ⇔ Markov–Hankel inequality on `[−½, 0]` [L]; odd moment capacity not attained on smooth tests [L]. |
| Σ48 Criticality | Classified [D] | — | Every exact reading sits on a zero-slack boundary: Weil cone a point, lattices Szegő singular, reflection coefficients freezing at `±1`, aperture floor doubly-exponentially small, theta gauges critical on the line, extremals not smooth, heat path real at `t ≥ 1/8` and non-real at every `t < 0`, PM defect vanishing only at `δ = 0` [L]. |
| Σ49 Reality by continuation | Sharpened | RH | Reality lost only through collision (polynomial model, function field); RH ⇔ every zero of `H_t` simple ∀t > 0 ⇔ zero collision mass ⇔ `Λ_X = 0` ∀X; `c·d²/log X ≤ Λ_X ≤ (2/3+ε)/log X`; global depth energy antitone; first Laguerre inequality not a certificate [L]. Open: collision exclusion along a source-faithful path. |
| Σ50 Below `log 4` | Sharpened | sub | For `0 < c < log 2`: positivity ⇔ `(Λ(2)/√2, Λ(3)/√3) ∈ belowLogFourBandWeights c = oddBandWeights ∩ evenBandWeights` ⇔ `{2,3}` Markov–Hankel form ⇔ Hodge index ⇔ Künneth effectivity; sharp prime-free boundary `c = log 2`; set convex, compact for `c > ½log 3`, excludes `w₂ ≤ 0` for `c ≥ 21/40` [L]. Open: membership of the arithmetic point. |
| Σ51 Sectors as moment problems | Solved (identity) | — | Even ⇔ Hamburger, odd ⇔ shifted Hamburger, window ⇔ Stieltjes for `s_k = W(φ^{(k)})`; representing measures built from the sequence alone; jet energies strictly log-convex [L]. |
| Σ52 Prime-weight confinement and soft entry | Classified | — | Sector sets cylinders in `w_p` before entry; a sector margin `η` admits `|w_p' − w_p| ≤ ηΩ(2c − log p)`, `Ω(δ) ≥ (e^{−1/2}/2)log(1/δ)`; once a prime acts, the window bounds its weight from both sides [L]. Carrying `w₃ = 0.634` needs `η·0.303·log(1/δ) ≥ 0.634`: even `η = 1` reaches only `δ ≤ 0.12` (`c ≤ 0.61`) [D]. |
| Σ53 Size versus sign of the kicks | Classified | — | `{2,3}` kicks `≤ (log2/2 + log3/3)·levyEnergy` below `log 4` [L]; the edge-law bound on all reflection terms of the band sums to `< levyEnergy` exactly on windows shorter than `log 5` [D]; yet `w₂ ≤ 0` is inadmissible for `c ≥ 21/40` and the flip is rejected at `21/20` [L]: the primes pay the prime-free deficit by the signature `(f⋆f)(−ℓ) = ∫_I(f₊² − f₋²)` of their sliver reflection [L]. |
| Σ54 Sector order of the archimedean place | Classified | — | Gamma ladder `A(g)‖g'‖² ≤ A(g')‖g‖²`; Gamma floors transfer even → odd → even mean-zero; the pole adds `+` square to even, `−` square to odd [L]. |
| Σ55 Euler-stage phase repulsion | Solved (above the horizon) | — | `Λ_X = A_X(s) + A_X(1−s)`: above `log(t₀/2π) > 6/t₀ + W(X)` every line zero simple, gaps in `[π/M, π/m]`, exact count; nothing below the horizon `≈ 2πe^{W(X)}` [L]. |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (equivalence) | RH | `ψ(x) − x ≤ C√x log²x` ⇔ RH ⇔ `κ = 0`; Redheffer `det R_N = M(N)` [L]. |
| Π2 Deciding input | Open | RH | No unconditional source input at square-root precision. |
| Π3 Producer cost | Partially solved | sub / RH | Multivariate parity producers reach `(1+ε)x + C_εlog²x`; individual producers slope `> 1` [L]. |
| Π4 Window precision (kernel = coupling) | Sharpened | RH | `𝒞_m(f) = 𝓗_m(f) − Σ_nw_n(f⋆f)(2m − log n)`; RH ⇔ the count within `W(f)` of the collar Hankel form on every reflection pair; below `log 4` a two-term count `w₂A₂(f) + w₃A₃(f)` against `𝓗₀(f)` within the archimedean–polar `W(f)` [L]. |
| Π5 Conjugate diagonal | Sharpened | sub → ≥qRH → RH | Means `O_c(log U)`; `o(log U)` ⇔ clustering; one dyadic constant ⇔ RH [L]. |
| Π6 Averages versus all heights | Sharpened | — | Double-log stage outside `O(V/log log V)` windows; exact flux on micro-Planck windows [L]. |
| Π7 Census / pair surplus | Partially solved | sub | Simple critical `≥ 0.67250071` (imported Zeta23 inputs); positivity-only certificates cannot reach `3/4` [L]. |
| Π8 Depth visibility | Partially solved | — | Cluster-product horizon; off-line zeros seen at aperture `≍ log|γ|log log|γ| + 1/δ` [L]. |
| Π9 Exceptional moduli | Partially solved | sub | Uniform zero-free region and Siegel for `q ≤ (log x)^A`; logarithmic zero-free intervals for quadratic `L` at all moduli ⇔ at large moduli [L]. |
| Π10 Frequency localization | Solved | — | Every eventually positive cyclotomic band has abscissa `2Θ` [L]. |
| Π11a–e Cone, bidegree, fixed-rank, definite, Siegel counts | No-go | — | Excluded as independent sign producers [L]. |
| Π11f Logarithmic duality | Partially solved | sub | Pole plane: Abel completion, logarithmic RR [L]. |
| Π11g Boost transform | Solved (identity) | — | `∫Z⁺(s,u)e^{2wu}du = K(s,w)ζ(s+w)ζ(s−w)` [L]. |
| Π11h Count-valued primitive `h¹` | Sharpened; closed as mechanism | RH | Window `h¹ = ½Q`; every concrete count type excluded [L/D]. |
| Π12 Subconvexity / heat floor | Partially solved | sub | `μ(½) ≤ 33/200`; heat floors `133/200`, `2/3 + ε` [L]. |
| Π13 Prefix scale | Solved | — | Strip zeros `Θ(N² log N)`; stabilization `Θ(√m)` [L]. |
| Π14 Amplifier rank | No-go (finite support) | — | Growing losses keep radius `Be^λ` [L]. |
| Π15 Critical-scale residual sign | Classified | — | Residual = prime-free aliasing term + Weil's form [L]. |
| Π16 Genus function | Sharpened | indep. | Genus `≥ (2 − η)e^A` + multiplicity excess; upper law open [L]. |
| Π17 Window energy | Sharpened | RH; ≥qRH (log stage) | Abscissa = twice the maximal depth; zero-free window ⇔ unweighted `L²` port; bounded port ⇔ purity; polynomial stage ⇔ RH [L]. |
| Π18 Finite realizations | No-go | — | No finite-dimensional window realization [L]. |
| Π19 Mollified log-mean from moments | No-go | — | Moments do not determine the log-mean [L]. |
| Π20 Count identities at the first prime | No-go | — | No finite-square identity for `log 2 ≤ A < 2log 2` [L]. |
| Π21 Exact balance | Classified | — | Weil cone `{Λ}`; `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})`; Szegő singular under RH [L]. |
| Π22 Near-line density ladder | Sharpened | sub | Eight equivalent forms; `D_win` ⇔ log-stage certificates ⇔ thin Planck shadows; `D_zero` ⇔ `D_win` + vanishing cluster tail [L]; `D_zero` is log-free (Selberg-type density counts `≍ e^{−cA}V log V`) [D]. |
| Π23 Inner caps | Open | RH (all degrees); ≥qRH (fixed degree) | Caps cancel to `σ_m = 1 − 1/(116log(m+5))` [L]; the cap is the zero-free region pushed to the line [D]. |
| Π24 Parity at dimension zero | Classified | — | Jets generated by `M` and `ρ_A(Λ)`; Selberg `Λ₂` constraint [L]. |
| Π25 Euler-product pinning | Classified | — | Shifted-pole weight `= 1/ζ(1+k)`, refuted [L]. |
| Π26 Bulk second order | Solved | — | `2γ₁ + γ²` at fixed overlap; polar growth `κc(2 + γ − log 4π)` [L]. |
| Π27 Retained Gamma comparison | No-go (as lossless) | — | `R_ret + E/64 < 0 < Q` on smooth odd unit tests; survivors: higher reserve `t³/960 + t⁴/192` [L]. |
| Π28 Gauge-torus spectrum | Classified | RH at the trivial point | Pole-subtracted exponents range exactly over `[Θ, 1]`, minimized at the trivial point; flip points break the Möbius half-power law; an explicit non-special point has exponent `½` [L]. |
| Π29 Square-root threshold | Classified | — | Columns of RvM density are mimics iff camera exponent `λ ≤ ½`; paired-lattice boundary `X² ≤ T` [L/M]; `λ = ½` is the Riemann–Siegel length and the pair-isolation aperture `2a/π = (1/2π)log(T/2π)` [D]. |
| Π30 Collective payment of the kicks | Sharpened [D] | RH | Kicks outside the collar-certified range need resources beyond their collar; the anti-diagonals of all kicks on a reflection pair are the smoothed prime count in `𝒞_m`: Σ meets Π beyond the first stages, and already below `log 4` as a two-term count. |
| Π31 Terminal prime channels | Solved | — | Terminal prime boundary mass counted by integer fibres (no short-interval prime estimate); terminal prime means are finite Riemann sums; upward-row replacement error `c⁴/N` [L]. |
| Π32 Elementary sieve inputs | Solved | — | Selberg-sieve upper bounds for primes in progressions to large prime moduli (uniform constant), residue covariances with exact period means, affine collision mass, proper prime-power tails `H^{−7/16}` [L]. |

## Γ — selection and reflection

| Wall | Status | Strength | Content |
|---|---|---|---|
| Γ1 Trivial gauge point | Open | RH | `Θ ≥ ½`; Haar-a.e. `½`; Baire-generic `1`; an explicit non-special point at `½` [L]. |
| Γ2 Prime-set flips | Solved | — | Every nontrivial prime pattern separated at every density [L]. |
| Γ3 Twin-blindness of soft structure | No-go | — | Krein index invariant under unitary twists [L]. |
| Γ4 Frobenius at infinity | Sharpened | RH | RH ⇔ `σ` trivial ⇔ Hecke similitude ⇔ partner saturation; window involution = twisted Krein reflection [L]. |
| Γ5 Source identification / pre-divisor | Partially solved | RH | Pre-divisor sections need zero-independent forcing [L]. |
| Γ6 Boundary sign / coherence | Solved | — | Pole boundary sign separates `ζ` from size twins [L]. |
| Γ7 Affine carrier | Solved | — | Gluing at a place; subgroup classification [L]. |
| Γ8 Poisson rigidity | Sharpened | RH | Zero-side positivity = RH [L]. |
| Γ9 Archimedean continuity vs height decay | No-go | — | ⇒ `κ = ∞` [L]. |
| Γ10 Function-field indistinguishability | Sharpened | — | Pure curves: Hurwitz sums of angles; camera identifies at the genus (point counts to `𝔽_{q^g}`); pure and tilted mimics below; bounded images certify purity; aperture `> g log q/2` certifies purity, sharp [L]. |
| Γ11 Pole-blindness of the glue | No-go | — | Simple pole absorbed [L]. |
| Γ12 General gauges | Solved | sub | Harmonic saturation only at the Euler gauge [L]. |
| Γ13 Source-uniform extinction | No-go | — | Fails at `3/4 + i` [L]. |
| Γ14 Local counterterm selection | No-go | — | Flip twin glued index `1` [L]. |
| Γ15 Functional-equation twins | Partially solved | sub | Degree three and positive degree two admit off-line real zeros; positive finite Euler twins violate only `θ < ½` [L]. |
| Γ16 Selection–sign gap | Sharpened | RH | No selector gives positivity [L]. |
| Γ17 Scattering recentering | Classified (no-go) | — | Rational/algebraic recentering impossible [L]. |
| Γ18 Divisor-identity selection | Solved | — | Only `Λ` degenerates completely [L]. |
| Γ19 Correspondence algebra over ℤ | Sharpened | RH | Rosati positivity ⇔ orbit Hodge index ⇔ naive height at bounded distance; integral and window Rosati forms bounded above are `≤ 0`; degree-zero comparisons are exact [L]. |
| Γ20 Window selection | Classified | — | Bounded windows blind; flip twin identical on length-`A` tests is not Weil positive [L]. |
| Γ21 Density selection on the natural cone | No-go | — | RvM-count exact-spline countermodels [L]. |
| Γ22 Contractive scattering positivity | No-go | — | Blaschke pairs keep every Schur inequality [L]. |
| Γ23 Weil cone uniqueness | Solved | — | Full Weil positivity forces `Λ` [L]. |
| Γ24 Mayer reflection positivity | Sharpened | RH | Resonance ⇔ `ζ(2s) = 0`; `D_s(ψ_s) ≤ 0`, `< 0` iff `Re s ≠ ¼`; `D_s(ψ) = −∫(e^{δu}+e^{−δu})(e^{δu}−e^{−δu})²|F(u)F(−u)|` for fixed periods; Krein self-pairing of the resonant basis `1` on `Re s = ¼`, `0` off it; exact completion `Q = 2Re[𝓦H, 𝓦H]` [L]. Open: an arithmetic expression of `D_s(ψ_s)` with manifest sign (the analytic one forces `δ = 0` only if `D_s ≥ 0` is known) [D]. |
| Γ25 Two reflection centres | No-go (as operator symmetry) | — | Transfer reflects about `Re w = 1`, zeta events about `Re w = ½` [P]. |
| Γ26 Resonant-state selectors | No-go | — | Inversion fixes every resonant period; cutoff Grams retain the rate [L]. |
| Γ27 Tate counts as a selector | No-go | — | `ζ(s)ζ(s−ε)` Tate positive, not Weil positive [L]. |
| Γ28 Frobenius inside the window algebra | No-go | — | Same-window similitudes scalar; Frobenius at scale `t` = translation by `t` [L]. |
| Γ29 Linear Serre–Krein identification | No-go | — | No real-linear isometry [L]. |
| Γ30 Completed Tate family | Classified | — | Unimodular on the line [L]. |
| Γ31 Degeneration type over `𝔽_q` | Solved (calibration) | — | Pure curves degenerate completely; impure curves grow at their zero width [L]. |
| Γ32 Hecke-equivariant completion | Solved (identity) | identity | `𝒦 = ℓ²(upper Mayer resonances)`; Hecke multiplier `p^{1−2s}` [L]. |
| Γ33 Euler rigidity in the Selberg class | Solved | — | Euler-log discrepancy convergent at `σ = ½` ⇒ equality; degree gap `(0,1)`; degree one: conductor `≥ 2` or a pole [L]. |
| Γ34 Hecke cones and periods | Solved | — | Hecke cones tile; periods Hecke eigenfunctions [L]. |
| Γ35 Beurling and Hamburger rigidity | Classified | — | Positive primes with regular integers allow zeros in `(½, 2/3)`; FE + positivity force `ℕ` [L]. |
| Γ36 Identification by the explicit formula | Partially solved | sub (sign-free) | Finite modifications identified at every aperture; isolable, simple-zero-set and perturbed-lattice clusters never cancel; cancelling clusters have upper uniform density `≥ 2a/π`, sharp; mimics contain two points of different FE orbits closer than any `g > π/a`; shallow configurations resolved at the Ingham scale `π/(2a)`, optimal [L]; far zeros faint in the local camera [W]. Open: local inversion at `ζ`'s growing density (B43). An on-line competitor with the image of `ζ` is already Weil positivity [D]. |
| Γ37 Euler columns | Classified | — | A zero of `1 + Ap^{−s} + p^{1−2s}` is on the line iff `A² ≤ 4p`; columns hide below aperture `log p/2` [L]. |
| Γ38 Retained Hecke channel | Classified | — | `D_s(u_s) = |core_s(2)|²Φ(Re s)`, sign of `¼ − Re s`, opposite at the reflected resonance [L]; reads the side, forces nothing [D]. |
| Γ39 Blindness = density aperture | Solved | — | Count bound `(D,C)` ⇒ blind windows above `πD`; Jensen: nonzero blind windows need `≥ πD`; exact threshold for uniform density at depth `≤ ½`; blind windows ⇔ entire functions of exponential type vanishing on the set; none blind to real `Ξ` zeros [L]. |
| Γ40 Positivity certifies thin configurations | Classified | — | Isolated tilts give negative images; positivity at one aperture `a > πD` puts perturbed-lattice and column configurations on the line; one column pair threshold `πD/2`, sharp; for curves positivity at `a > g log q` certifies purity [L]. Open: every column configuration above `πD/2`. |
| Γ41 Fakes at their first prime | Solved | — | Data first differing at `n₀` are separated exactly above aperture `½log n₀`; flips, Euler twins, Beurling data caught at their first prime; mimicry lives only at configuration level [L]. |
| Γ42 Legendre-invariant reality | Solved (identity) | identity | RH ⇔ `J(ρ) = 256(ρ²−ρ+1)³/(ρ²(ρ−1)²) ∈ ℝ` at every zero; `J∘λ` a coordinate on `SL(2,ℤ)\ℍ` [L]. |
| Γ43 Collide or repel over `𝔽_q` | Solved (calibration) | — | Integral trace configurations have a multiple root or distinct roots at distance `≥ (4√q)^{−((g−1)²+g−2)}`; purity closed and lost only at Frobenius collisions [L]. For `ζ` the image is a `log p`-weighted prime sum: no discreteness [D]. |

## Bridges

| Bridge | Anchor |
|---|---|
| `κ(K_ζ)` = right zeros = `sup_A ι(A)` = band poles of `Λ(s)/Λ(s+1)` = upper-right Mayer resonances; RH ⇔ `κ < 2` | HKT, RIT, CWS, AOG [L] |
| Window sign ⇔ two-site sign ⇔ band at the centre ⇔ Stieltjes moments of jet energies | GWZ, SWC [L] |
| Reflection-pair coupling = collar Hankel form − smoothed prime count | SWC, CSTW [L] |
| Below `log 4`: window sign ⇔ two-weight membership ⇔ retained-variance certificates ⇔ Hodge index ⇔ Künneth effectivity | SWC, SP, LST [L] |
| Kick = positive source − anti-diagonal conductance; reflection term = sliver signature; outward edge pays at `w_ne^h/2` | SWC [L] |
| Window ⇔ its lattices; local continuum limit ⇔ jet Hankel system; reflection coefficients freeze at `(−1)^n` | GWZ, SWC [L] |
| Sector moment problems (Hamburger/Stieltjes) ≈ theta Hankel towers at one centre ≈ Jensen/multiplier sequences | SWC, TH, LA [L]; [D] |
| Degenerate window ⇔ finite curve; Spec ℤ under RH ⇔ infinite-angle curve | GWZ [L] |
| Window algebra = truncated Dirichlet λ-ring | WTZ [L] |
| Weil's window form = dimension-zero jet of the Tate family | WTZ, DZG, ATD [L] |
| Complete family at the critical curve = Weil at the frequency pole + positive counts; threshold `R₁(A)`; terminal source polar | AHD, CACT [L] |
| Floor exponent = zero width = fall rate of the ground energy; window positivity at `R` ⇒ zero-free to height `e^{R/polylog R}`; doubly exponential reach for deep zeros | WTZ, SquareRootThreshold, DCI [L]; [D] |
| Frobenius angle over `𝔽_q` ≡ twist frequency over ℤ; untwisted window ≡ pole at `u = 0` | AHD [L] |
| Weil energy = Krein form of zero coordinates; PM defect lifts window tests and dominates fold functionals | RIT [L] |
| Weil image ⇒ configuration up to density `2a/π` (sign-free); positivity certifies up to `πD` | ZCG, SquareRootThreshold [L] |
| Column threshold `λ = ½` ≡ Riemann–Siegel length ≡ paired-lattice boundary ≡ pair-isolation aperture | ZCG, SquareRootThreshold [L/M]; [D] |
| Heat path critical at `t = 0`; reality leaves only through collision; `Λ = sup_X Λ_X` | RHTower DeBruijn, ZCG [L] |
| Euler stages `A_X(s) + A_X(1−s)`: monotone phase and simple line zeros above the horizon [L]; read as a Hermite–Biehler phase ↔ Levinson–Conrey census ↔ de Branges canonical systems [D] | ZCG, IGP, GWZ |
| Weil cone `{Λ}`; lattice selection; prime-blind nonemptiness | RHTower, GWZ [L] |
| Near-line density: eight forms; occupancy ⇔ thin Planck shadows | CDG [L] |
| One cyclotomic mode carries `2Θ`; gauge-torus spectrum `[Θ, 1]` | CAF, AGT [L] |
| Gluing `κ(φ_c) = κ + 1`; Redheffer `det = M(N)` | AKG, ADT, HWV [L] |

## Status counts

| Family | Solved | Partially solved | Sharpened | Open | No-go | Classified | Reduced |
|---|---|---|---|---|---|---|---|
| Σ (76) | 18 (Σ1a, Σ1b, Σ1c, Σ1h, Σ1k, Σ1o, Σ10, Σ12, Σ16, Σ24, Σ29, Σ36, Σ37, Σ39, Σ43, Σ45, Σ51, Σ55) | 11 (Σ1d, Σ1e, Σ1g, Σ1j, Σ1m, Σ3, Σ6, Σ9, Σ27, Σ35, Σ41) | 14 (Σ1, Σ1l, Σ2, Σ3a, Σ4, Σ7, Σ8, Σ17, Σ19, Σ28, Σ30, Σ32, Σ49, Σ50) | 3 (Σ18, Σ20, Σ47) | 7 (Σ1f, Σ2a, Σ13, Σ14, Σ23, Σ25, Σ42) | 22 (Σ1i, Σ1n, Σ1p, Σ1q, Σ1r, Σ2b, Σ11, Σ15, Σ21, Σ22, Σ26, Σ31, Σ33, Σ34, Σ38, Σ40, Σ44, Σ46, Σ48, Σ52, Σ53, Σ54) | 1 (Σ5 → Π17) |
| Π (39) | 7 (Π1, Π10, Π11g, Π13, Π26, Π31, Π32) | 6 (Π3, Π7, Π8, Π9, Π11f, Π12) | 8 (Π4, Π5, Π6, Π11h, Π16, Π17, Π22, Π30) | 2 (Π2, Π23) | 10 (Π11a–e, Π14, Π18, Π19, Π20, Π27) | 6 (Π15, Π21, Π24, Π25, Π28, Π29) | — |
| Γ (43) | 14 (Γ2, Γ6, Γ7, Γ12, Γ18, Γ23, Γ31, Γ32, Γ33, Γ34, Γ39, Γ41, Γ42, Γ43) | 3 (Γ5, Γ15, Γ36) | 6 (Γ4, Γ8, Γ10, Γ16, Γ19, Γ24) | 1 (Γ1) | 12 (Γ3, Γ9, Γ11, Γ13, Γ14, Γ21, Γ22, Γ25, Γ26, Γ27, Γ28, Γ29) | 7 (Γ17, Γ20, Γ30, Γ35, Γ37, Γ38, Γ40) | — |

Strength of the open walls:
- **RH:** Σ1 (minimal form: the band on reflection pairs), Σ1l, Σ2, Σ3a, Σ6, Σ7, Σ8, Σ17, Σ18, Σ19, Σ20,
  Σ27 (all stages), Σ28 (subexponential), Σ30, Σ32, Σ49, Π2, Π4, Π11h, Π17 (polynomial stage), Π23 (all
  degrees), Π28 (trivial point), Π30, Γ1, Γ4, Γ5, Γ8, Γ16, Γ19, Γ24.
- **identity:** Σ35 (global Hamiltonian).
- **≥qRH:** Σ4 (`K_ζ`), Σ28 (exponent `< ½`), Σ1o at exponent `p < ½`, Π5 (fixed scale), Π17 (log stage),
  Π23 (fixed degree).
- **sub:** Σ1d, Σ1e, Σ1g, Σ1j, Σ1m, Σ1q, Σ4 (zero–one law), Σ27 (each stage), Σ30 (each stage), Σ41,
  Σ47, Σ50, Π3, Π5 (mean `o(log U)`), Π7, Π9, Π11f, Π11h (fixed length), Π12, Π22, Γ15, Γ36, Γ40.
- **indep.:** Π16.
