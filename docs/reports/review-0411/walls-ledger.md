# Walls ledger — status quo

Three wall families block every route: **Σ** the critical sign, **Π** precision and production, **Γ**
selection and reflection. All three read one even integer `κ = κ(K_ζ) = #` distinct zeros right of the
critical line and one number, the onset aperture `a*(ζ)` (supremum of the half-widths at which every window
of Weil's form is positive): RH ⇔ `κ = 0` ⇔ `a*(ζ) = ⊤`. All three are decided on the two-site window
`{f, f∘R}` of a test and its mirror image.

- **Σ is the sign of every window, decided on reflection pairs and paid by the primes with sign.** RH ⇔
  `|c_ψ(t)| < Q(ψ)` for every bump and `t ≠ 0` ⇔ `a*(ζ) = ⊤` [L]; `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)` [L].
  Below window length `log 4` the sign is the membership of `(Λ(2)/√2, Λ(3)/√3)` in an explicit compact
  convex set [L]. Positivity-preserving structure ends early (Markov part at support `e^{−3/4}`, even-sector
  Perron at `c = log ρ`) [L]; beyond, the primes pay the archimedean–polar deficit by the signature of their
  sliver reflections and ground states change sign [L]. Every window theorem converts into zero location by
  the visibility law `k·pairEnergy(δ, a) ≤ L` [L], vacuously below half-width `4` [D].
- **Π is the same band read on the prime side.** `𝒞_m(f) = 𝓗_m(f) − Σ_nΛ(n)n^{−1/2}(f⋆f)(2m − log n)` [L]:
  the collective payment of the kicks is the smoothed prime count of `f⋆f` matching the pole square within
  `W(f)` — the square-root form of RH. Production by counts is closed [D]; the size-only floor carries no
  zero information [L/D]; size information on the heat path stops at the Gaussian saddle `½/log X` [L].
- **Γ is reflection and identification.** Identification is complete: at the square-root aperture the
  explicit formula fixes ζ's zeros up to near-coincidences of diameter `o(1/log T)` and reads their squared
  gaps to second order [L]. Reflection: the completed PM space is `ℓ²(zeros)` with `Q = 2Re[𝓦H, 𝓦H]`, the
  co-isometry defect of a resonance is `−∫2cosh(δu)4sinh²(δu)|F(u)F(−u)|` [L], so the PM sign is the
  identity `δ = 0`; reality at near-coincidences is the sign of `w²` [D]. Selection is automatic after
  positivity [L]; positivity is the open half.

Status: **Solved** (the face is a theorem), **Partially solved**, **Sharpened** (open, with its exact
form a theorem), **Open**, **No-go** (the mechanism is refuted), **Classified** (answered by a
classification or identification theorem), **Reduced** (theorem-level equivalent of the wall named).
Strength: **RH**, **≥qRH** (zero-free half-plane or Lindelöf), **sub**, **indep.**, **identity**,
**method**. Evidence: `[L]` committed Lean; `[W]` working-tree Lean; `[P]` pipeline-card paper proof;
`[D]` derived here; `[M]` exact model statement; `[N]` numerical. Window half-widths `a` or `c`;
`c_ψ(t) = W(ψ(· − t), ψ)`; `w_n = Λ(n)n^{−1/2}`; `h` the collar half-width of `n`; `δ` the sliver width
`2c − log n` (in zero statements, `δ` is the depth `Re ρ − ½`); `ρ³ = ρ + 1` the plastic number.

## Σ — critical sign

| Wall | Status | Strength | Content |
|---|---|---|---|
| Σ1 Weil's sign | Sharpened | RH | RH ⇔ `Q ≥ 0` on every window ⇔ `a*(ζ) = ⊤` ⇔ two-site PD ⇔ strict orbit Cauchy–Schwarz ⇔ band at the centre in both parity sectors ⇔ Stieltjes moment problem of jet energies ⇔ every lattice Schur parameter in `(−1,1)` ⇔ `ι(A) = 0` ∀A ⇔ `R₁(A) = ⊤` ∀A ⇔ Krein positivity of zero coordinates ⇔ prime-blind positivity ⇔ canonical domination [L]. One generic bump decides [L]. |
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
| Σ1l Window threshold | Reduced (to Σ56) | RH | `R₁(A) = inf{7J(1)M₈(H)/(a_φ|Q(H)|) : Q(H) < 0}`; antitone; `≥ R₀ > 0`; `⊤` up to `2·enlargedWeilFloorAperture`; `R₁(A) = ⊤ ⇔ A/2 ≤ a*(ζ)`; off RH `R₁(A) < ⊤ ⇔ A > 2·contact` [L]. |
| Σ1m Polarization inheritance | Partially solved | sub | Every twisted sector with positive scalar second order, windows `≤ 3/5`, the cosh hyperplane below `log 2 + 1/50`, every window at small ratio [L]. |
| Σ1n Bulk and growing overlap | Classified | — | Bulk below the grid reads only the pole; growing-overlap entries linear and polar [L]. |
| Σ1o Aperture-independent weighted floor | Solved (size-only) | — | `Q(H) ≥ −C(p)∫e^{−pu}H²`, `p > 1`; exponent `p` gives only zero width `≤ p` [L/D]. |
| Σ1p Terminal windows | Classified | — | Exact complete mixed limit at all positive ratios; polar source = boundary logarithm + finite prime-power mean; nonpolar sources vanish; nonzero polar source; nontrivial kernel; long-index cancellation on near rows and logarithmic annuli [L]. |
| Σ1q Receiving charges | Classified | — | Charges survive vanishing raw, physical and complete energy; capacity `log log N + O(1)`; **simultaneous fixed finite receiving vectors**: arbitrary charges on modes `m ∣ M`, raw energy `→ (Σt_m²)(d/a − ½)`, input, adjunction and physical energy `→ 0`, exact complementary receivers read `t_l/80` at `Q = X²`, `N = X⁴⁰`; mixed channels with bounded Mertens correction; receiver determinant `→ 6239t²/6400` [L]. Open: growing mode sets. |
| Σ1r Conductor packets and correctors | Classified | — | Terminal sources concentrate at the pole through `13/32`; summable sources; vanishing mixed mass above overlap; low correctors cannot improve zero-source windows; low-packet capacity attained by one pole coefficient; full conductor diagonal overprices terminal windows [L]. |
| Σ2 Edge, zero modes, hard Lefschetz | Sharpened | RH | HR ∧ HL ⇔ strict HR; RH ⇔ HL on the PSD locus; zero modes radical, reflection parity, gap law; first failure two-site; tight band ⇒ reflection-pair zero mode [L]. |
| Σ2a Interior-gap continuation | No-go (as structure) | — | `κ(d) = 1_{3∣d}` [L]. Two sites decide. |
| Σ2b Edge singularity | Classified | — | No smooth window eigenfunction, constrained ground state or capacity maximizer; nonnegative windows PD on smooth tests; strict band on smooth tests [L]. |
| Σ3 Stars and dilation monodromy | Partially solved | — / RH | Stars isometric, depth law; monodromy eventually idempotent [L]. |
| Σ3a Coprime stratum | Sharpened | RH | gcd stratification; Redheffer `det = M(N)` [L]. |
| Σ4 Finite index / heat count | Sharpened | ≥qRH (`K_ζ`); RH (`K_ζ⊠K_ζ`) | `κ < ∞` ⇒ Lindelöf; RH ⇔ index `0`; `{0, ∞}` laws [L]. |
| Σ5 Collision quantum / window integer | Reduced (to Π17) | RH | Index `0` ⇔ Wiener–Hopf invertibility [L]. |
| Σ6 Rank / degree uniformity | Partially solved | RH | Rank 8 PD at every `0 < a < ½`; every finite native shifted Hankel matrix PD past a rank-dependent radius; native fifth even section PD for `q ≥ 5`; fixed cross-load PD near endpoints and for `q ≥ 5000`, fails at scale 8 (capacity `½ < τ₈ < 1`); quartic flux profile repairs origin, scale 8 and a cofinal ray, fails at scale 32 (capacity `τ₃₂(a) ≤ 70τ₃₂/67 < 54/67`) [L]; fixed Jensen degree eventually hyperbolic; PF₃₇ [L]. Open: rank 9 integrated sign, all ranks. |
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
| Σ27 Window stages | Partially solved | sub (each stage); RH (all) | All real `C²` tests positive through half-width `enlargedWeilFloorAperture ∈ (0.362, ½)`, floor `‖f‖²/8000`; first stage opens positive; at length `21/20` admissible prime-two weights exclude `0` and `−w₂`; odd unit window bounds off one moment [L]. No sign theorem on `c ∈ (0.362, log 2)` [N margins `1.5×10⁻⁵` odd, `5.6×10⁻⁸` even at `c = ½log 3`]. Stages below half-width `4` carry no zero information [D]. |
| Σ28 Window negativity budget | Sharpened | ≥qRH (exponent `< ½`); RH (subexponential) | Floor `−(deg K_A + 2sinh(A/2) − A)‖H‖²`; ground-energy floor `−Ce^{2σA}` ⇔ zero width `≤ σ` [L]. |
| Σ29 Low-frequency localization | Solved | — | Negativity only at the poles and below `τ₀(a)` [L]. |
| Σ30 The stage step | Sharpened | RH (as induction); each stage sub | Stage criterion; kick = collar Rosati pairing; frozen form in closed form; lattice admission [L]. Soft entry makes the step a margin transport (Σ52). |
| Σ31 Positivity across dimension zero | Classified | equivalent to Σ1 | Bare domination ⇔ `Q ≥ 0`; counts/Hodge/degeneration cannot close RH [L/D]. |
| Σ32 Prime-blind positivity | Sharpened | RH | Weil cone `{Λ}`; node-critical; Farkas duality; solved on nonnegative and separated-bump cones [L]. |
| Σ33 Tate positivity horizon | Classified | — | Exact horizons at stages 1–2; no `k > 0` uniform [L]. |
| Σ34 Canonical-degree horizon | Classified | — | Soft deformations paid by counts have horizon `≍ e^{−A/2}` [L/D]. |
| Σ35 Canonical system of the tower | Partially solved | identity | Lattice Levinson recursion; continuum margins `h^{−2n}E_n → det J_{n+1}/det J_n > 0` on nonnegative windows; `γ_n → (−1)^n`; parity split `det J_n = det E·det O` [L]. Global Hamiltonian with the prime kicks: not constructed. |
| Σ36 Rational Hecke-graph reading | Solved (identity) | — | Window arithmetic on finite `S ⊂ ℚ_{>0}` = Hecke operator [L]. |
| Σ37 Lattice canonical system | Solved (identity) | — | Window ⇔ its lattices; refinement lowers margins [L]. |
| Σ38 Two-site decision | Classified | — | RH ⇔ two-site PD; off RH `|c_ψ(s)| = Q(ψ)` for a short generic bump [L]. |
| Σ39 Trivial-divisor transmission | Solved (identity) | — | Collar Hankel form, inertia `(1, ∞)`, negative definite on the pole hyperplane [L]. |
| Σ40 Degenerations are curves | Classified | — | Degenerate lattice windows are finite curves; Spec ℤ under RH the infinite-angle curve [L]. |
| Σ41 Aperture–depth duality | Classified | — | Fall rate of the window ground energy = zero width (bounded clustering; two-sided for finitely many off-line zeros); positivity at `R` excludes depth `≥ 1/R` to height `exp(R/(10⁵A₀(log R)²)) − 306` [L]. Unshielded coherent clusters excluded to doubly-exponential height by an `e^{2(δ−σ)a}/δ` law; a shielded zero of depth `1/a` hides above single-exponential height for every `L ≥ 4a` (tapered crystal, sharp); configurations identical below `exp((e^{2δa} − 2)/(4δ) − a)` have opposite signs [L]. |
| Σ42 Markov, sign-blind and variance-free ground states | No-go | — | Markov part negative on support `e^{−3/4}`; no Markov supersolution on longer intervals; folded criterion void on the unit odd window; lossless local allocation fails; variance-dropped odd certificates fail for `c > 273/400`; nonnegative even theta-gauge cosh certificates fail; the prime `3` as a worst-case collar potential fails for `c ≥ 287/500` [L]. |
| Σ43 Pole-charged ground-state calculus | Solved (identity) | — | `Ẑ(Φωu) = J_{Φω}(u) + ∫u²ω𝒢_S(ω) + 2V_s − 2V_c`; theta gauges critical on the line; dropped variance = all-pairs jump form; gauge-extension invariance; below `log 4` retained-variance certificates exact [L]. |
| Σ44 Collar locality of the kick | Classified | — | Collar-internal jumps pay the kick of `n` at ratio `2w_ne^h`, sharp; prime `3` unpaid by its collar; outward jumps carry the newest prime power at `w_ne^h/2 ≤ e^{h−1}`; every `n` costs `≤ (Λ(n)e^c/(2n))·levyEnergy` [L/D]. |
| Σ45 Reflection pairs and parity sectors | Solved (identity) | — | `W(f ± f∘R) = 2W(f) ± 2𝒞_m(f)`; sectors = band at the centre; Markov–Hankel form of each sector [L]. |
| Σ46 Frustration of the odd sector | Classified | — | Frozen odd form Markov, kick anti-Markov; kick = source − conductance; odd light cone `≥ 0` [L]. |
| Σ47 Odd unit window | Open | sub | Positivity ⇔ `w₂ = log 2/√2 ∈ unitBandWeights` (convex) ⇔ Markov–Hankel inequality on `[−½, 0]`; odd moment capacity not attained on smooth tests [L]. |
| Σ48 Criticality | Classified [D] | — | Every exact reading sits on a zero-slack boundary: Weil cone a point, lattices Szegő singular, reflection coefficients freezing at `±1`, aperture floor doubly-exponentially small, theta gauges critical, extremals not smooth, Perron exactly to `log ρ`, heat size horizon at the Gaussian saddle, PM defect vanishing only at `δ = 0` [L]. |
| Σ49 Reality by continuation | Sharpened | RH | Reality lost only through collision; RH ⇔ every zero of `H_t` simple ∀t > 0 ⇔ `Λ_X = 0` ∀X; `c·d²/log X ≤ Λ_X ≤ (6600/9991 + ε)/log X`; general source-profile repulsion law (margin `c₀ > ½`); collision ⇔ `Re Q(0) = Im Q′(0) = 0`; Gaussian saddle enters `Re s > 1` exactly at `½/log(X/2π)`; Lindelöf-bounded Riemann-density pair models collide below every positive time scale, at `t* < min(δ²/2, δ/L)` [L]. Open: collision exclusion on `(0, ½/log X]`, where every depth `≤ ½` pair of the model collides [D]: an Euler-product input inside the strip. |
| Σ50 Below `log 4` | Sharpened | sub | For `0 < c < log 2`: positivity ⇔ `(Λ(2)/√2, Λ(3)/√3) ∈ belowLogFourBandWeights c = oddBandWeights ∩ evenBandWeights` ⇔ `{2,3}` Markov–Hankel form ⇔ Hodge index ⇔ Künneth effectivity ⇔ `R₁(2c) = ⊤`; sharp prime-free boundary `c = log 2`; convex, compact for `c > ½log 3`, excludes `w₂ ≤ 0` for `c ≥ 21/40` [L]. Open: membership of the arithmetic point (no certificate exists). |
| Σ51 Sectors as moment problems | Solved (identity) | — | Even ⇔ Hamburger, odd ⇔ shifted Hamburger, window ⇔ Stieltjes for `s_k = W(φ^{(k)})` [L]. |
| Σ52 Prime-weight confinement and soft entry | Classified | — | Sector sets cylinders in `w_p` before entry; margin `η` admits `|w_p' − w_p| ≤ ηΩ(2c − log p)`; once a prime acts, its weight is bounded on both sides [L]. Carrying `w₃` by soft entry reaches `c ≤ 0.61` at `η = 1` [D]. |
| Σ53 Size versus sign of the kicks | Classified | — | `{2,3}` kicks `≤ (log2/2 + log3/3)·levyEnergy` below `log 4` [L]; summed edge-law bound `< levyEnergy` exactly on windows `< log 5` [D]; `w₂ ≤ 0` inadmissible for `c ≥ 21/40`; deleting the prime `3` breaks odd positivity for `c ≥ 3/5` [L]. |
| Σ54 Sector order of the archimedean place | Classified | — | Gamma ladder `A(g)‖g'‖² ≤ A(g')‖g‖²`; Gamma floors transfer even → odd → even mean-zero; the pole adds `+` square to even, `−` square to odd [L]. |
| Σ55 Euler-stage phase repulsion | Solved (above the horizon) | — | `Λ_X = A_X(s) + A_X(1−s)`: above `log(t₀/2π) > 6/t₀ + W(X)` every line zero simple, gaps in `[π/M, π/m]`, exact count; the same for every real finite carrier and every symmetric half [L]. |
| Σ56 Onset aperture of `ζ` | Sharpened | RH | `WindowPositiveAt Z a ⇔ a ≤ a*(Z)` on tempered configurations; `a*(Z) = ⊤` ⇔ all zeros on the line; RH ⇔ `a*(ζ) = ⊤`; off RH `a*(ζ) = zetaContactAperture`, attained; `a*(ζ) ≥ enlargedWeilFloorAperture`; `hodgeDefectAt Z a = 0 ⇔ a ≤ a*(Z)` [L]. |
| Σ57 Perron / Beurling–Deny structure | Classified (no-go past `log ρ`) | — | Even sector `E(f) − E(|f|) = ∬D[ω(|u−v|) + ω(−u−v) − 4cosh(u/2)cosh(v/2)]`; Markov iff `c ≤ log ρ` (nonnegative weights); past `log ρ` every pole strength `s ≥ 1` and all weights admit `E_s(f) < E_s(|f|)`; robust Perron costs height; arithmetic pole within `O(λ₀)` of the positivity threshold; robust kick margins decouple reflected slivers [L]. |
| Σ58 Window visibility law | Classified | — | Lattice RvM background: `WindowPositiveAt ⇔ k·pairEnergy(δ,a) ≤ L` (`a ≤ L/2`); deep and cubic brackets; sharp L² tilt `P²/‖f‖² ≍ e^{2δa}/δ`; general RvM coherent-cluster exclusion; DCI-admissible shallow coherent clusters seen at `δ²a³ > 3/2`; spread shallow sets hide while `a²(2a+2π)e^{2π}e^{2σa}W ≤ m₀L`; separated runs hide while `2δa·sinh(2δa) ≤ 1`; contact law at `c log T` a power-saving zero-location bound [L]. General shallow depth-mass bound under positivity `Σm_qδ_q² ≲ A₀log T/a²` [P]. |
| Σ59 Shielded zeros at fixed aperture | No-go | — | For every `a ≥ 2`, `L ≥ 4a`, a finite tempered RvM configuration with a zero of depth `1/a` is positive at `a` (biquadratic tapered crystal); no fixed-aperture theorem excludes shielded zeros above single-exponential height [L]. |

## Π — precision and production

| Wall | Status | Strength | Content |
|---|---|---|---|
| Π1 Global law | Solved (equivalence) | RH | `ψ(x) − x ≤ C√x log²x` ⇔ RH ⇔ `κ = 0`; Redheffer `det R_N = M(N)` [L]. |
| Π2 Deciding input | Open | RH | No unconditional source input at square-root precision. |
| Π3 Producer cost | Partially solved | sub / RH | Multivariate parity producers reach `(1+ε)x + C_εlog²x`; individual producers slope `> 1` [L]. |
| Π4 Window precision (kernel = coupling) | Sharpened | RH | `𝒞_m(f) = 𝓗_m(f) − Σ_nw_n(f⋆f)(2m − log n)`; RH ⇔ the count within `W(f)` of the collar Hankel form on every reflection pair; below `log 4` a two-term count `w₂A₂(f) + w₃A₃(f)` against `𝓗₀(f)` within the archimedean–polar `W(f)` [L]. |
| Π5 Conjugate diagonal | Sharpened | sub → ≥qRH → RH | Means `O_c(log U)`; `o(log U)` ⇔ clustering; one dyadic constant ⇔ RH [L]. |
| Π6 Averages versus all heights | Sharpened | — | Double-log stage outside `O(V/log log V)` windows; exact flux on micro-Planck windows [L]. |
| Π7 Census / pair surplus | Partially solved | sub | Simple critical `≥ 0.67250071` (imported Zeta23 inputs); operator Mayer `Z`-function with `> 67.25%` disjoint sign changes; positivity-only certificates cannot reach `3/4` [L]. |
| Π8 Depth visibility | Partially solved | — | Cluster-product horizon; off-line zeros seen at aperture `≍ log|γ|log log|γ| + 1/δ` [L]; superseded in models by Σ58. |
| Π9 Exceptional moduli | Partially solved | sub | Uniform zero-free region and Siegel for `q ≤ (log x)^A`; logarithmic zero-free intervals for quadratic `L` at all moduli ⇔ at large moduli [L]. |
| Π10 Frequency localization | Solved | — | Every eventually positive cyclotomic band has abscissa `2Θ` [L]. |
| Π11a–e Cone, bidegree, fixed-rank, definite, Siegel counts | No-go | — | Excluded as independent sign producers [L]. |
| Π11f Logarithmic duality | Partially solved | sub | Pole plane: Abel completion, logarithmic RR [L]. |
| Π11g Boost transform | Solved (identity) | — | `∫Z⁺(s,u)e^{2wu}du = K(s,w)ζ(s+w)ζ(s−w)` [L]. |
| Π11h Count-valued primitive `h¹` | Sharpened; closed as mechanism | RH | Window `h¹ = ½Q`; every concrete count type excluded [L/D]. |
| Π12 Subconvexity / heat floor | Partially solved | sub | `μ(½) ≤ 33/200`; heat floors `133/200`, `6600/9991` [L]. |
| Π13 Prefix scale | Solved | — | Strip zeros `Θ(N² log N)`; stabilization `Θ(√m)` [L]. |
| Π14 Amplifier rank | No-go (finite support) | — | Growing losses keep radius `Be^λ` [L]. |
| Π15 Critical-scale residual sign | Classified | — | Residual = prime-free aliasing term + Weil's form [L]. |
| Π16 Genus function | Sharpened | indep. | Genus `≥ (2 − η)e^A` + multiplicity excess; upper law open [L]. |
| Π17 Window energy | Sharpened | RH; ≥qRH (log stage) | Abscissa = twice the maximal depth; zero-free window ⇔ unweighted `L²` port; bounded port ⇔ purity; polynomial stage ⇔ RH [L]. |
| Π18 Finite realizations | No-go | — | No finite-dimensional window realization [L]. |
| Π19 Mollified log-mean from moments | No-go | — | Moments do not determine the log-mean [L]. |
| Π20 Count identities at the first prime | No-go | — | No finite-square identity for `log 2 ≤ A < 2log 2` [L]. |
| Π21 Exact balance | Classified | — | Weil cone `{Λ}`; `μ(a) ≤ K exp((11/2)a − πe^{2(a−2)})`; Szegő singular under RH [L]. |
| Π22 Near-line density ladder | Sharpened | sub | Eight equivalent forms; `D_win` ⇔ log-stage certificates ⇔ thin Planck shadows; `D_zero` ⇔ `D_win` + vanishing cluster tail; right-half squared-depth moment `o(V)` [L]; `D_zero` is log-free [D]. Windows of half-width `a` see coherent shallow clusters at `δ²a³ > 3/2` and miss spread ones with depth mass `≲ L/a³` [L]. |
| Π23 Inner caps | Open | RH (all degrees); ≥qRH (fixed degree) | Caps cancel to `σ_m = 1 − 1/(116log(m+5))` [L]; the cap is the zero-free region pushed to the line [D]. |
| Π24 Parity at dimension zero | Classified | — | Jets generated by `M` and `ρ_A(Λ)`; Selberg `Λ₂` constraint [L]. |
| Π25 Euler-product pinning | Classified | — | Shifted-pole weight `= 1/ζ(1+k)`, refuted [L]. |
| Π26 Bulk second order | Solved | — | `2γ₁ + γ²` at fixed overlap; polar growth `κc(2 + γ − log 4π)` [L]. |
| Π27 Retained Gamma comparison | No-go (as lossless) | — | `R_ret + E/64 < 0 < Q` on smooth odd unit tests; survivor: higher reserve `t³/960 + t⁴/192` [L]. |
| Π28 Gauge-torus spectrum | Classified | RH at the trivial point | Pole-subtracted exponents range exactly over `[Θ, 1]`, minimized at the trivial point; flip points break the Möbius half-power law; an explicit non-special point has exponent `½` [L]. |
| Π29 Square-root threshold | Classified | — | Camera: `λ = ½` is the aperture at which ζ's isolated zeros and multiplicities are read; disjoint-carrier mimics exist for all `λ ≤ 1`, none for `λ > 1` outside near-collisions [L]. Sign: off-line columns hide to `λ = ½` only on an ℓ¹ ridge `2Le^{δL}Σ|ε_k| ≤ 1`; one moved pair collapses the onset to `≈ (1/2δ)log(δL/ε²)` [L]. |
| Π30 Collective payment of the kicks | Sharpened [D] | RH | Kicks outside the collar-certified range need resources beyond their collar; the anti-diagonals of all kicks on a reflection pair are the smoothed prime count in `𝒞_m` [L/D]. |
| Π31 Terminal prime channels | Solved | — | Terminal prime boundary mass counted by integer fibres; terminal prime means finite Riemann sums; upward-row replacement error `c⁴/N` [L]. |
| Π32 Elementary sieve inputs | Solved | — | Selberg-sieve bounds for primes in progressions to large prime moduli, residue covariances with exact period means, affine collision mass, proper prime-power tails `H^{−7/16}`, periodic Gram blocks [L]. |

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
| Γ10 Function-field indistinguishability | Sharpened | — | Pure curves: Hurwitz sums of angles; camera identifies at the genus; pure and tilted mimics below; bounded images certify purity; curve columns certified by positivity at `a > (g − ½)log q`, sharp for `g ≥ 2` [L]. |
| Γ11 Pole-blindness of the glue | No-go | — | Simple pole absorbed [L]. |
| Γ12 General gauges | Solved | sub | Harmonic saturation only at the Euler gauge [L]. |
| Γ13 Source-uniform extinction | No-go | — | Fails at `3/4 + i` [L]. |
| Γ14 Local counterterm selection | No-go | — | Flip twin glued index `1` [L]. |
| Γ15 Functional-equation twins | Partially solved | sub | Degree three and positive degree two admit off-line real zeros; positive finite Euler twins violate only `θ < ½` [L]. |
| Γ16 Selection–sign gap | Sharpened | RH | No selector gives positivity [L]. |
| Γ17 Scattering recentering | Classified (no-go) | — | Rational/algebraic recentering impossible [L]. |
| Γ18 Divisor-identity selection | Solved | — | Only `Λ` degenerates completely [L]. |
| Γ19 Correspondence algebra over ℤ | Sharpened | RH | Rosati positivity ⇔ orbit Hodge index ⇔ naive height at bounded distance; degree-zero comparisons exact [L]. |
| Γ20 Window selection | Classified | — | Bounded windows blind; flip twin identical on length-`A` tests is not Weil positive [L]. |
| Γ21 Density selection on the natural cone | No-go | — | RvM-count exact-spline countermodels [L]. |
| Γ22 Contractive scattering positivity | No-go | — | Blaschke pairs keep every Schur inequality [L]. |
| Γ23 Weil cone uniqueness | Solved | — | Full Weil positivity forces `Λ` [L]. |
| Γ24 Mayer reflection positivity | Sharpened | RH | Resonance ⇔ `ζ(2s) = 0`; `D_s(ψ_s) ≤ 0`, `< 0` iff `Re s ≠ ¼`; `D_s = −∫(e^{δu}+e^{−δu})(e^{δu}−e^{−δu})²|F(u)F(−u)|`; Krein–Lax–Phillips space with Krein self-adjoint generator, on-line Krein square `1`, off-line antisymmetric `−2`, RH ⇔ Krein form `≥ 0` [L]. Open: an arithmetic expression of `D_s(ψ_s)` with manifest sign [D]. |
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
| Γ36 Identification by the explicit formula | Solved (sign-free) | sub | Finite modifications identified at every aperture; sparse clusters never cancel; shallow configurations resolved at the Ingham scale, optimal, locally and globally; deep columns hide only below it; at aperture `λ·½log(T/2π)`: `λ > 1` identifies RvM configurations outside near-collisions `< δ/log T`, `λ > ½` for subset carriers and for every isolated zero of ζ with its multiplicity, `λ ≤ 1` fails for disjoint carriers [L]. An on-line competitor with the image of `ζ` is already Weil positivity [D]. |
| Γ37 Euler columns | Classified | — | A zero of `1 + Ap^{−s} + p^{1−2s}` is on the line iff `A² ≤ 4p`; columns hide below aperture `log p/2`; twins tilted at every height `2πk/log p` [L]. |
| Γ38 Retained Hecke channel | Classified | — | `D_s(u_s) = |core_s(2)|²Φ(Re s)`, sign of `¼ − Re s`, opposite at the reflected resonance [L]; reads the side [D]. |
| Γ39 Blindness = density aperture | Solved | — | Count bound `(D,C)` ⇒ blind windows above `πD`; Jensen: nonzero blind windows need `≥ πD`; exact threshold for uniform density at depth `≤ ½`; blind windows ⇔ entire functions of exponential type vanishing on the set [L]. |
| Γ40 Positivity certifies thin configurations | Solved | — | Isolated tilts give negative images; split columns certified at `a > πD_on + (π/2)D_off`; pure off-line columns `a* ≤ πD/2`; mixed `2g`-column configurations have exact onset `(g − ½)ℓ > πD/2`; one-sided isolation makes `Re W < 0` [L]. |
| Γ41 Fakes at their first prime | Solved | — | Data first differing at `n₀` separated exactly above aperture `½log n₀` [L]. |
| Γ42 Legendre-invariant reality | Solved (identity) | identity | RH ⇔ `J(ρ) ∈ ℝ` at every zero [L]. |
| Γ43 Collide or repel over `𝔽_q` | Solved (calibration) | — | Integral trace configurations have a multiple root or distinct roots at distance `≥ (4√q)^{−((g−1)²+g−2)}`; purity lost only at Frobenius collisions [L]. For `ζ` the image is a `log p`-weighted prime sum: no discreteness [D]. |
| Γ44 Second-order coalescent precision | Partially solved | sub | Near-coincident clusters of ζ-mimics: net multiplicity `0`, centre `O(r²)`, squared gap `w²` to `O(r³)` with window loss `e^{C log²X}` (bandwidth `λ > 1/4 + πμ/2`) [L]. Polynomial-scale precision needs isolating windows with polynomial floor; worst-case RvM-blind windows do not have it [L/D]. |
| Γ45 Domination as a selector | No-go | — | Every real finite Dirichlet carrier is real and simple above its horizon `2πe^{W_a}`; a tilted carrier zero costs weight `log(t/2π) − 6/t`; twins need unbounded weight [L]. |
| Γ46 Reality at near-coincidences | Sharpened | RH | Collisions are near-coincidences of the camera; reality at one is the sign of `w²` (real pair `w² > 0`, functional-equation pair `w² = −4δ²`) [L]; the sign of `w²` at every near-coincidence ⇔ no collision of `H_t` ⇔ RH [D]. |

## Bridges

| Bridge | Anchor |
|---|---|
| `κ(K_ζ)` = right zeros = `sup_A ι(A)` = band poles of `Λ(s)/Λ(s+1)` = upper-right Mayer resonances = `boostPolarIndex/2`; RH ⇔ `κ < 2` | HKT, RIT, CWS, AOG [L] |
| RH ⇔ `a*(ζ) = ⊤`; `R₁(A) = ⊤ ⇔ A/2 ≤ a*(ζ)`; hodge defect `0` ⇔ `a ≤ a*` | WVL, AHD [L] |
| Window sign ⇔ two-site sign ⇔ band at the centre ⇔ Stieltjes moments of jet energies | GWZ, SWC [L] |
| Reflection-pair coupling = collar Hankel form − smoothed prime count | SWC, CSTW [L] |
| Below `log 4`: window sign ⇔ two-weight membership ⇔ retained-variance certificates ⇔ Hodge index ⇔ Künneth effectivity ⇔ `R₁ = ⊤` | SWC, SP, LST, AHD [L] |
| Kick = positive source − anti-diagonal conductance; reflection term = sliver signature; outward edge pays at `w_ne^h/2`; even frustration = the pole alone | SWC [L] |
| Window ⇔ its lattices; local continuum limit ⇔ jet Hankel system; reflection coefficients freeze at `(−1)^n` | GWZ, SWC [L] |
| Sector moment problems ≈ theta Hankel towers at one centre ≈ Jensen/multiplier sequences | SWC, TH, LA [L]; [D] |
| Weil's window form = dimension-zero jet of the Tate family | WTZ, DZG, ATD [L] |
| Complete family at the critical curve = Weil at the frequency pole + positive counts | AHD, CACT [L] |
| Window sign → zero location: `k·pairEnergy(δ,a) ≤ L` (models); `e^{2(δ−σ)a}/δ` (general RvM); shielding barrier at single-exponential height | WVL [L] |
| Floor exponent = zero width = fall rate of the ground energy | WTZ, SquareRootThreshold, DCI [L] |
| Frobenius angle over `𝔽_q` ≡ twist frequency over ℤ | AHD [L] |
| Weil energy = Krein form of zero coordinates; PM defect lifts window tests | RIT [L] |
| Weil image ⇒ configuration up to near-coincidences `o(1/log T)` at `λ > 1`; isolated zeros at `λ > ½` | ZCG [L] |
| Column threshold `λ = ½` ≡ camera readout aperture ≡ Riemann–Siegel length; sign-hiding there only on an `e^{−δL}` ridge | ZCG, WVL [L]; [D] |
| Heat collision ⇔ near-coincidence ⇔ sign of `w²`; size reaches `½/log X` (saddle) | RHTower, ZCG [L]; [D] |
| Euler stages, real finite carriers, symmetric halves: phase lattices above their horizon | ZCG [L] |
| Weil cone `{Λ}`; lattice selection; prime-blind nonemptiness | RHTower, GWZ [L] |
| Near-line density: eight forms; occupancy ⇔ thin Planck shadows | CDG [L] |
| One cyclotomic mode carries `2Θ`; gauge-torus spectrum `[Θ, 1]` | CAF, AGT [L] |
| Gluing `κ(φ_c) = κ + 1`; Redheffer `det = M(N)` | AKG, ADT, HWV [L] |

## Status counts

| Family | Solved | Partially solved | Sharpened | Open | No-go | Classified | Reduced |
|---|---|---|---|---|---|---|---|
| Σ (80) | 18 (Σ1a, Σ1b, Σ1c, Σ1h, Σ1k, Σ1o, Σ10, Σ12, Σ16, Σ24, Σ29, Σ36, Σ37, Σ39, Σ43, Σ45, Σ51, Σ55) | 10 (Σ1d, Σ1e, Σ1g, Σ1j, Σ1m, Σ3, Σ6, Σ9, Σ27, Σ35) | 14 (Σ1, Σ2, Σ3a, Σ4, Σ7, Σ8, Σ17, Σ19, Σ28, Σ30, Σ32, Σ49, Σ50, Σ56) | 3 (Σ18, Σ20, Σ47) | 8 (Σ1f, Σ2a, Σ13, Σ14, Σ23, Σ25, Σ42, Σ59) | 25 (Σ1i, Σ1n, Σ1p, Σ1q, Σ1r, Σ2b, Σ11, Σ15, Σ21, Σ22, Σ26, Σ31, Σ33, Σ34, Σ38, Σ40, Σ41, Σ44, Σ46, Σ48, Σ52, Σ53, Σ54, Σ57, Σ58) | 2 (Σ1l → Σ56, Σ5 → Π17) |
| Π (39) | 7 (Π1, Π10, Π11g, Π13, Π26, Π31, Π32) | 6 (Π3, Π7, Π8, Π9, Π11f, Π12) | 8 (Π4, Π5, Π6, Π11h, Π16, Π17, Π22, Π30) | 2 (Π2, Π23) | 10 (Π11a–e, Π14, Π18, Π19, Π20, Π27) | 6 (Π15, Π21, Π24, Π25, Π28, Π29) | — |
| Γ (46) | 16 (Γ2, Γ6, Γ7, Γ12, Γ18, Γ23, Γ31, Γ32, Γ33, Γ34, Γ36, Γ39, Γ40, Γ41, Γ42, Γ43) | 3 (Γ5, Γ15, Γ44) | 7 (Γ4, Γ8, Γ10, Γ16, Γ19, Γ24, Γ46) | 1 (Γ1) | 13 (Γ3, Γ9, Γ11, Γ13, Γ14, Γ21, Γ22, Γ25, Γ26, Γ27, Γ28, Γ29, Γ45) | 6 (Γ17, Γ20, Γ30, Γ35, Γ37, Γ38) | — |

Strength of the open walls:
- **RH:** Σ1 (minimal form: the band on reflection pairs), Σ2, Σ3a, Σ6, Σ7, Σ8, Σ17, Σ18, Σ19, Σ20, Σ27 (all
  stages), Σ28 (subexponential), Σ30, Σ32, Σ49, Σ56, Π2, Π4, Π11h, Π17 (polynomial stage), Π23 (all degrees),
  Π28 (trivial point), Π30, Γ1, Γ4, Γ5, Γ8, Γ16, Γ19, Γ24, Γ46.
- **identity:** Σ35 (global Hamiltonian).
- **≥qRH:** Σ4 (`K_ζ`), Σ28 (exponent `< ½`), Σ1o at exponent `p < ½`, Π5 (fixed scale), Π17 (log stage),
  Π23 (fixed degree).
- **sub:** Σ1d, Σ1e, Σ1g, Σ1j, Σ1m, Σ4 (zero–one law), Σ27 (each stage), Σ30 (each stage), Σ47, Σ50, Π3,
  Π5 (mean `o(log U)`), Π7, Π9, Π11f, Π11h (fixed length), Π12, Π22, Γ15, Γ44.
- **indep.:** Π16.
