# Route obstacles — status quo

Scope: the 38 live route formulations, the 9 route candidates and the supporting programmes. For each route: the path, what is established, the obstacles that are **(a) just work**, and the obstacles that are **(b) open mathematics nobody has a solution to**.

**Corpus checkpoint:** commit `ff6ebf7224` (2026-11-09); working-tree modules of other agents are marked `[S]`. Working log: `logs/review-0911-statusquo-facts.md`.

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means an independent source mechanism or landing is missing. Formulations are not independent mechanisms: HJ is PA, BSH is CDC, FEL's BSY criterion belongs to CTF. A criterion, a source construction, a quotient equality or a scalar grade does not discharge an arithmetic sign or vanishing.

**Evidence.** `[L]` Lean source, integrated. `[S]` Lean source unfinished or unintegrated. `[K]` Lean with transitive axiom audit. `[D]` deduction, not a Lean theorem. `[N]` numerical, uncertified. `[C]` classical literature, not formalized.

**Strength.** RH; ≥qRH (zero-free half-plane, Lindelöf or ZAL); AAL (implies the asymptotic abscissa law); sub (below quasi-RH and below AAL); method; producer; indep.

**Labels.** `A*` just-work items and `B*` open problems are listed in full in [obstacles-summary.md](obstacles-summary.md). An A item is known mathematics, finite computation, effectivization, integration or assembly of proved pieces; `(unverified)` marks A items whose difficulty is not established. Wall labels Σ, Π, Γ refer to [walls-ledger.md](walls-ledger.md).

**Notation.** Windows `[−a,a]`. `W` Weil's form, `w_n=Λ(n)n^{−1/2}`. `a*(ζ)` onset aperture; `ℋ(c)` Hardy interval; `λ*(c)` best cone margin. `L=artanh r`, `Ψ=½log H₁`, `q=Ψ′`. `N_d` non-real root count of `R_d(Ξ)`. `Θ=sup Re ρ`, `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`. **ZAL** (`Θ∞=½`): finitely many zeros beyond every positive depth. **AAL** (`Θ=Θ∞`): for every `h≥0`, finitely many zeros right of `½+h` means none. **B13 / finite stratum**: AAL at `h=0`, finitely many off-line zeros means none. **LinAt C**: `Θ−½≤C(Θ∞−½)`. `R=c⁸/log N`; `W₈(H)=∫H²e^{−8y}`; `Q₁=⌊(log N)^{13/32}⌋`; `R_c`, `R_polar`, `R_halfline`, `R_prim`, `R_high` the whole-space, polar-payment, half-line, pole-orthogonal and high-conductor critical thresholds; `W=⨅_{A≥0}windowThreshold(A)`. `E_y` Euler head, `ζM_y` Euler tail. `R(y,η)` first return of the primes `≤y` at precision `η`. A **Weil tower** at base `ℓ` is the family `e^{ℓ(ρ−½)}` of modes; its **level sums** sample the lag `Φ(νℓ)`; a set of levels is **thick** if it contains arbitrarily long runs arbitrarily far out. `primeDeviation(X)=(X−ψ(X))+X(Σ_{n≤X}Λ(n)/n−log X+γ)+O(1)`, `Φ(L)=e^{−L/2}primeDeviation(e^L)`. `Q(a)` Weil's form on integer probes. `c_B` the orbit correlation of the cubic spline `B`, `2Re S` its trace; `Γ_n` the smoothed Frobenius graph of degree `n`; `P(d)`, `A(d)` the smoothed prime count in the window of `d` and its archimedean-plus-pole prediction, `c_B(log d)=A(d)−P(d)`. A **sampling weight** `0≤w≤Λ` has a series that blows up at `1` and no other singularity on `Re s=1`. `C_∞` the archimedean compensation. `G_s(d)=e^{−(s−1)d}/(4π sinh d)` the Green function of `Δ−s(2−s)` on `ℍ³`; `G^{T_p}_s` the Green function of the Bruhat–Tits tree of `PGL₂(ℚ_p)`. A **seed** is a continuous bounded modular function decaying in the cusp; `Λ_F(s)=∫_𝒟F·E*(s−½)`. `F_n=Π_{p|n}(X²+p)`; the **orientation cover over ℤ** is the real locus of `y²=disc F_n`.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ `c_B(log p)≥−K` at every prime ⇔ `c_B(log p)≤K` at every prime ⇔ `P(p)≤A(p)+K` ⇔ `Re W(B±τ_{log p}B)≥0` at every prime; width `≤a` ⇔ the same with `Kp^a`; unconditionally `P−A=o(√p)` | [L] | Σ (Weil's sign), Π (a prime count) and the curve proof (Stepanov's bound) are one inequality at the prime degrees |
| The gap method iterates: a one-sided bound on any power-saving gap set puts every zero at depth `≤` the deepest real zero (lower side) or on the line (upper side); ζ has no real zero in the strip; Landau's theorem replaces Pringsheim's | [L] | no hypothesis on prime gaps beyond Huxley; the squares, the `n^k`, the `p^k` decide RH |
| RH ⇔ even tensor-power moments `Σ_{p≤N}log p(2Re S(log p))^{2k}≤C_kN^{1+A}` uniform in `k`; Rankin square abscissa `=2max Re ρ` | [L] | Deligne's argument runs over ℤ: positivity free, uniformity is the content |
| RH ⇔ ZAL ∧ AAL for every zero configuration; ZAL ⇒ qRH; `qRH ∨ AAL` | [L]/[D] | one half is at least quasi-RH, the other sits below it |
| Strict hierarchy `Pure ⊊ AAL ⊊ LinAt C₁ ⊊ LinAt C₂ ⊊ (∃C LinAt) ⊊ B13`; `∃C LinAt ⇔ (ZAL ⇒ Pure)`; `AAL ⇔ ∀C>1 LinAt C` | [L] | the exceptional coordinate is a dial |
| A one-sided crude bound at a sampling set of primes (a residue class, the primes off a relative-density-zero set, the degrees `p^aq^b`) gives AAL; with ZAL it is RH; attainment is free on the primes and on two-prime difference lags, not on finitely generated monoids | [L] | AAL has prime-side producers that need no periodicity of zeros |
| Positive measure (or positive dimension) of the bases with recurrent sub-top lag readings gives AAL; the residual set of such bases exists unconditionally and has dimension 0 under ¬AAL | [L] | metric, not topological, size of recurrence carries AAL |
| No property depending only on zeros above a height, or only below a fixed height, decides B13, AAL or any linear AAL | [L] | the input must couple both scales |
| FE + order one + reality admit every finite top layer; positive discrete and integer-norm Euler products with linear counting continue across `Re s=½` with exactly one off-line pair | [L] | of Euler product, integrality, linear counting, continuation and FE, only the FE excludes a finite layer |
| Integrable or square-integrable FE defects force the rational primes; a positive measure with gap `(−1,1)∖{0}` is tent-self-dual iff a Dirac comb | [L] | no nonclassical neighbour of ζ with a defective FE exists; AAL must come from exact identities of ζ |
| Any property holding for every heat deformation `H_t` and implying "finitely many non-real zeros ⇒ none" gives RH; only the undeformed kernel has a Dirichlet series | [L] | a B13 input must see the Dirichlet series |
| Under ¬AAL the raw prime current `ΣΛ(n)n^{−s}e^{−n²/t}` tends to `−ζ′/ζ` on a high strip at inverse-height damping; the FE reflects heights to themselves (`N_tζ(s+it)≈conj ζ(1−s̄+it)`) | [L] | the finite-layer world has exact identities; none transports a zero in height |
| `R_c=R_PSD=R_polar=R_halfline≤R_prim=R_high=W`; ¬RH gives a unit half-line ground state at finite `W`; finite `R_polar=W` forces it to be polar-orthogonal | [L] | the critical curve is the window plus one channel plus one orthogonality |
| RH ⇔ `Ψ` locally bounded ⇔ `a*(ζ)=⊤` ⇔ `λ*(c)→0` ⇔ two-site PD | [L] | every window route measures one number |
| Off the diagonal Weil's kernel = pole − `2πG_{1/2}` on the degree geodesic of `ℍ³` − `log p((p−1)/√p)G^{T_p}_{1/2}` on the `p`-ladders: the Green functions of all places at the critical parameter | [L] | the off-diagonal is an adelic Green pairing; the sign sits in the diagonal |
| No twisted hyperbolic carrier with convergent Poincaré series at `½` and no compact or finite-volume embedding carries the torsion; locked atomic dampings converge on the diagonal only to the discriminant diagonal and are never PSD | [L] | the archimedean fibre is `ℍ³` with one geodesic, the finite fibres are trees; the diagonal must come from a smoothing |
| RH ⇔ `Q` on integer probes is the Tate limit of an `ℕ`-count, needed on one effective ray `Γ_1+Γ_p` per prime; `Q` is not integer-valued and no integral kernel reproduces it | [L] | a count must be a genuine limit |
| One cuspidal cavity function built from Hecke eigenforms sees every resonance; RH ⇔ its energy rings down at `y^{3/4−ε}`; the dual side has no sign; RH ⇔ every reflection Krein form of the cavity is PSD | [L] | the horizon has complete and sharp receivers; every remaining physical input is a rate or a reflection sign |
| Internal modular conjugation collapses to the centre; vacuum-fixing and half-sided modular realizations cannot carry `Q` | [L] | the Hecke clock of a realization of `Q` has point spectrum; the horizon's own clock does not |
| Integrality forces exact vanishing only on the torsion of the prime torus; heights where an integer auxiliary vanishes are countable; exact order costs the degree; the minimal auxiliary at the fixed points of all `Γ_n`, `n≤N`, has log length `ψ(N)` | [L] | the exact Stepanov count over ℤ is Chebyshev's; RH is the bound `ψ(N)≤N+C√N log²N` on its degree |
| Returns of the primes: depth `t≥poly(1/δ)` (Baker, two primes suffice), Dirichlet `R≤⌈π/2δ⌉^{|P|}`; bounded-height Diophantine certificates stop at the Kronecker scale | [S] | transcendence bounds depth, not breadth |
| The orientation cover over ℤ exists: fibres `1+μ(n)`, centred count `M(N)`, weight `≥½` unconditionally, weight `½` ⇔ RH | [L] | topology carries `M(N)` as the trace of a middle cohomology that never vanishes |
| Near-unit mollifiers need length `exp(c log²T)`; conditional tail laws stop at the Kronecker scale; long mean values are collision counts of order `X²` | [L] | the near-line wall is the dark range |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | primes pay the archimedean–polar deficit by sign | format exact on every window; size payment ends before half-width `21/40` |
| M2 Calibration | window cones, blind positivity, margin | cone pinned at `e^{−c/1104}`; cone points obey PNT `5/6` on the window's range; sign open |
| M3 Canonical flow | `L,q,Ψ` of the Weil chain | exact to contact; RH ⇔ `Ψ` locally bounded |
| M4 Reflection | Krein/Lewis positivity, Hecke dispersion, ringdown, Lax–Phillips, horocycles, cavity energies, Born rules, standard forms | complete and sharp cavity receivers; reflection Krein form PSD ⇔ RH; internal and half-sided realizations excluded; rates open |
| M5 Square-root cancellation | smoothed prime counts, long moments, Farey discrepancy | receivers closed; estimates open |
| M6 Continuation | heat, cosine, Jensen | typical heights closed; small time at all heights open; finite-stratum laws on the heat family are RH; Dirichlet series selects time 0 |
| M7 Zero geometry | cameras, Blaschke factors, inner field | isolated zeros at rate 2; depth `O(T)`; clusters and `o(T)` open |
| M8 Recurrence and transport | zero transport, tail transport, partial returns, prime current in the finite-layer world | AAL ⇔ transport; passage and height reflection proved; replication open |
| M9 Production | integer stencils, integrality, Stepanov over ℤ | rate = Mertens level; exact Stepanov count = Chebyshev |
| M10 Count | nonnegative function with quadratic Tate limit | every hyperelliptic curve [L]; over ℤ one ray per prime; no count known |
| M11 Orbit at finite time | prime phases, first return, frozen polynomials, linear forms in logarithms | depth of returns bounded by Baker; breadth dark at the Kronecker scale |
| M12 Critical compactness | Gårding, Γ-liminf, threshold law, pole channel, half-line ground states | closed: `R_c=R_polar=R_halfline≤W` |
| M13 Topology of the prime complex | homotopy, persistence, fixed points, singular indices, orientation cover | `s`-independent; `Σ index=1−M(N)`; cover weight `½` ⇔ RH |
| M14 Thermal averaging | primon gas | Euler factors at real points `>1` |
| M15 Infinite-rank elimination | Weil towers, exceptional rank, thick sets, linear dial, metric recurrence | elimination proved; inputs (thick crude count, ZAL) open |
| M16 Intersection on half-products | 𝔽₁-zonotope, `ℙ¹_ℤ` torsion, `ℍ³` and tree fibres, Frobenius graphs | adelic Green formula off the diagonal; diagonal is the sign |
| M17 Prime-degree sampling | one-sided bounds at gap sets and sampling sets, Landau, tensor powers | RH at the primes from one side; AAL at sampling sets; estimate open |
| M18 FE rigidity | defective FEs, Poisson rigidity, Gaussian surgery | complete in the countable class; selects exact identities of ζ |
| Amplifiers | Diophantine repulsion, integrality, isolation, Turán, positive annihilators | amplify a certificate, produce none |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve

Routes: HF, SRT, AIP, ACS (atomic), SC, CHMD (index). Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF.

Established [L]:
- Full tilted-spline matrix PD for `1≤c≤(log N)^α`, `α<1/8`, and through `c≤2K₀(log N)^{1/8}` with complete Schur payment [K].
- Every compact C² profile: energy `≥ae^{−Bc}‖x‖²` on conductors `≤N^θ`, `θ<¼`, `c≤b log log N`.
- **Threshold identities.** `criticalPositivityThreshold = criticalNonnegativityThreshold = polarPaymentCriticalThreshold = halfLinePolarThreshold`; `poleOrthogonalCriticalThreshold = highConductorCriticalThreshold = ⨅_A windowThreshold(A) = W`; `R_polar ≤ W`. Every threshold `=⊤` ⇔ onset `=⊤` ⇔ RH. `R_c ≥ c₁e^{c₂a}` and `R_high ≥ c₀e^{6a}` for `0≤a≤a*(ζ)`.
- **Half-line ground states.** Window-level polar payment on every terminal window ⇔ strict positivity of the Gamma-truncated charged critical form on half-line profiles. Under ¬RH, `W` is finite and strong compactness of the collar bridge produces a unit half-line ground state at `W`; each ground state bounds `R_polar` by a reciprocal shift in its polar pairing; finite `R_polar=W` forces exact polar orthogonality.
- **Multipliers.** The depleted kernel `m(z)=4/(¼−z²)−12/(64−z²)` has `Re m<0`, `25|m|²<−Re m` at every ξ-zero copy and a piecewise holomorphic square root; no finite or countable square-bounded family of holomorphic multipliers dominates it on the off-line strip.
- **Charged compactness.** A nonpositive whole-space sequence yields a unit joint mass of collar profile and scalar pole coordinate with strong limits; polar matrix rows converge to their sampled profiles; fixed windows carry their physical pairings; payment at a larger ratio contradicts the limit. This closes the reduction of whole-space positivity to polar payment.
- **Conductor resolution.** Physical tearing has Schur ratio `→4/13`; conductor-adapted splitting decouples; every low-packet cross term except the literal polar collar pairing costs an arbitrarily small packet diagonal.
- **Low packet.** Payment at `R` on `[−A,0]` ⇒ `R≤windowThreshold(A)`; payment at every ratio on growing windows ⇒ RH; payment on every window for `R≤c₁e^{c₂a}`.

Structure [D]: the critical curve carries no sub-RH content beyond one inequality, `R_polar = W` at finite thresholds, and its ¬RH form is one statement about half-line ground states: whether they can be polar-orthogonal.

| | Obstacle | Strength |
|---|---|---|
| A9 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | — |
| A13 | Near-gcd charges and periods beyond `M₀(N)` (unverified) | — |
| B6 | Full-space sign eventually at every `K`; every critical threshold `=⊤` | RH |
| B8 | Head thresholds for every `d` | RH |
| B101 | Low-packet polar payment at every ratio on growing windows | RH |
| B104 | Polar payment at every `R<W`, equivalently `R_polar=W`; at finite `W`, whether a half-line ground state can be polar-orthogonal | method |
| B123 | Correlated arithmetic pairings that dominate the depleted kernel where universal holomorphic multipliers fail | method |

### S2. Window tower and canonical flow

Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT (odd), HF, ACS, SRT, SZ. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF.

Established [L]: precontact de Branges chain, canonical system with `H₁H₂=1`, flux, sampling bases; `L′=q−sinh 2L`; traces, `r`, `Ψ` absolutely continuous; `q_y→q` in `L¹`; restoring bound `|L(x)|≤artanh e^{−2(x−c)}+2osc Ψ`; RH ⇔ `L` locally bounded ⇔ `Ψ` locally bounded; off RH `L` unbounded above every base; soft prime kick; Born model; causal certificate; Szegő threshold; free reflection coordinates; forward-map tangent; cone pinning, margin ceiling, bounded extremals; cone points carry local density `1+O(e^{−a})` and PNT `5/6` on `X≤e^{2c−3}`; datum region `⊆{β≤1}`; exact null blind test; floors `(1/20000)/2^k` through `a_k<0.3621`; window naive heights exist iff positive; Tate dimension one exactly through `log 5`. Spline orbit: `|W(B,B(·−t))|≤Ke^{σt}` ⇔ width `≤σ`; RH ⇔ Hasse–Weil along the orbit.

| | Obstacle | Strength |
|---|---|---|
| A1–A3, A6 | Certified verification, numeric heights, first-window membership, cone widths | — |
| A16 | Numerical `r,m,q` [N] | — |
| B1 | Sign on every window | RH |
| B2 | Bounded oscillation of `Ψ` on every bounded aperture interval | RH |
| B3 | Variation of `r` free of `1/μ` | sub |
| B4 | Two-sector certificates; outer predictors; every actual echo in its Schur band | RH |
| B5 | Kick admission at every stage | RH |
| B16 | Decay law of `λ*(c)` | sub |
| B17 | Signed ground-state structure past `log ρ` | method |

### S3. Local onset plane

Routes: RW, ACS, SRT, ZCG, WD. Programmes: AIF, WVL, MZF, PTT, PL.

Established [L]: `Ω_ψ(a,X)` as a sum over zeros; on-line terms nonnegative; depth cost `≤(16/9)δ²a⁴‖ψ‖²`; RH ⇔ `Ω≥0`. Typical-height sign at `A=δlog T/(64M²)`; bad heights Gaussian-tailed, measure `≤T^{1−1/(64K)}` at `A=K log log T`. Weil's form is the average of its frequency packets.

Structure [D]: all-height sign stops at the size curve `a≈log log X`; typical-height statements are asymptotic and cannot decide B13.

| | Obstacle | Strength |
|---|---|---|
| B28 | Local Weil positivity at fixed `λ>0` on density-one heights | sub |
| B46 | Proportional saving at length `(log X)^{2K}`, all heights | sub |

### S4. Continuation and nodal geometry

Routes: ZCG, LA, PTR, HCF, PA, GTA, XN, WD. Programmes: NGF, FFP, ADO, AES, RHTower heat.

Established [L]: collision criterion; horizon `(6600/9991+ε)/log X`; density-one `Λ_Xlog X→0`; crystal and reality at the critical scale; sharp depth law for isolated simple zeros; `N_d` law and inner-root reality; cosine Laguerre above VK; nonrepelling values of dimension zero; maximal-angle law; one-sided Gaussian prime ceiling at every rational height ⇔ RH; high-collision counts ⇔ ZAL. **Heat family:** every `H_t` (`t>0`) has asymptotic off-axis depth `0`; a finite-stratum law valid on all `H_t` gives RH; existential linear AAL along `t→0⁺`, even with a `t`-dependent slope, is RH; `ξ_τ` has an absolutely convergent Dirichlet series on a real half-line iff `τ=0`. **Heat divisor:** with upper initial budgets `S_q=Σy(0)^{2q}` and `L_a=Σlog max(1,y(0)²/a)` (possibly `∞`): `Σ_upper(y(t)²+2t)^q≤S_q`, `N(t)(2t)^q≤2S_q`, `N(t)log(2t/a)≤2L_a`; the elapsed coefficient `2` is sharp; every positive-time confinement radius gives crowding dissipation `(card S−2)/R²`; deepest-`k` products contract; finite squared-depth mass ⇔ eventually bounded global heat energy, and then `t·N(t)→0`; power moments do not determine logarithmic majorization.

| | Obstacle | Strength |
|---|---|---|
| A19, A20 | Heat horizon toward its method floor; Jensen rung (unverified) | — |
| A50 | Finite-stratum laws on the cosine family `A_h` and the shifted Jensen family imply RH (unverified) | — |
| B24 | Collisions at arbitrarily small time, all heights | RH |
| B25 | Frequency `<1` at every collision | RH |
| B124 | Useful finite initial depth budgets for the ξ heat divisor (`S_q<∞` for some `q`, or a logarithmic budget), and extinction arbitrarily near `t=0` | sub to RH |
| B27 | Runs of `k` simple critical zeros, every `k` | sub |
| B47 | Multiplicity `o(log X)` by a non-size input | sub |
| B22, B23 | Outer roots of `R_d(Ξ)`; `N_d` bounded | RH; ≥qRH |
| B92, B93 | Rotated relation with coefficients of the size of `Q`; contradiction beyond the extremal law | RH |

### S5. Near-line geometry and long moments

Routes: WD, CTF, MC, TG; census. Programmes: CDG, APR, MZF, AIF, IWT.

Established [L]: Selberg CLT; cameras, hyperbolic density theorem, `N(ρ)=exp(−ΣG)`; box budgets and Carleson measure; eight-way log-mean equivalence, Abel form ⇔ depth density `o(T)`; Selberg's mollifier gives off-line first moment `≤(67/1000)V`, depth `O(T)`; squared off-line depth moment `o(V)`; necessary-length laws; an Euler mollifier with near-unit second moment uses every prime up to `min(1/24,1/(14K₀))log²T/log 4`; last-scale floor; Möbius zero condensation. Fejér-weighted long mean values of real Dirichlet polynomials are signed collision forms; for `Λ` on `[1,X]`, `X≥T`, the Fejér mean lies between `(2T/π²)ψ(X)²/(⌊T log X/π⌋+1)` and `(log X)²(TX/2+6X²)` and dominates the diagonal once `X≫T log³X`. Corridor `b·log log T/log T`, `b>1`: bad-window measure `O(T/log^ηT)`.

Structure [D]: past the height a long mean value is a count of prime pairs at multiplicative distance `≲1/T`; its order is unconditional, its constant is Hardy–Littlewood (binary).

| | Obstacle | Strength |
|---|---|---|
| A18, A21 | Twisted moments past `21/50` [C]; census items | — |
| B57 | Depth density `o(T)` | sub |
| B58 | `D_win` | sub |
| B59 | Cluster wall | sub |
| B60 | Exponential moments of the Green potential at deep zeros | sub |
| B61 | A detector past the last scale | sub |
| B62 | Cofinal long moment | RH |
| B66 | Near-unit holomorphic budgets; zero dilation surplus | RH |
| B82 | Inner-field decay | ≥qRH |

### S6. Production and precision

Routes: WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, LI, AIP. Programmes: ASRP, APR, AGT, AKLT, AE, AAD, RAC, MMD, SPAL, HWV.

Established [L]: band ⇔ classical criteria; integer lag; entry filters; length–precision law; gauge exponents `[Θ,1]`; twin quarter floor; Nair lattice; Stepanov over ℤ = integrality floor + Nair ceiling; producers `c=μ∗h`; floor `c/(√K(1+log K))`; uncertainty and mean-value laws give `ε≥c₁K^{−3/4}`; rate `K^{−a}` ⇒ `Re ρ≤1−a`; all `a<½` ⇒ RH; RH gives `a<¼`; Frobenius over `𝔽_q[T]` = Carlitz factorial stencil of rate 0; parity-neutral producers at every rate; cut kernel = zeros; finite-energy kernel mass annihilation ⇒ RH; exact identity pins `λ`; Farey discrepancy ⇔ RH; Möbius over `ℤ[ω]` is a cubic Gauss coefficient (composite Gauss sums cube to `μ(I)p/|p|`), with nonzero residue at `4/3` and a Fredholm spectral pencil on the cubic quotient.

| | Obstacle | Strength |
|---|---|---|
| A21, A30, A33 | Chowla [C]; best RH exponent in `[¼,½]` (unverified); cubic residue Fourier coefficients [C] | — |
| B48 | Deciding input at square-root precision | RH |
| B55 | Any polynomial stencil rate (qRH); rates `a↑½` (RH) | ≥qRH to RH |
| B15 | Mertens level past VK | sub |
| B14 | Any interior width value | ≥qRH |
| B56 | `Θ<1⇒Θ=½` | sub |
| B67 | Parity at power saving | ≥qRH |
| B91 | Finite-energy cut-kernel vectors have mass zero | RH |
| B94 | Identification of the cubic coefficients with an automorphic theta expansion; transfer to rational Möbius | past VK at least |
| B98 | Positive-generator integer-norm systems: which count distance forbids a finite top layer | method |

### S7. Reflection, carriers and the modular horizon

Routes: PM; W1C (candidate); RN and PTR in part. Programmes: RIT, ART, AOT, ACP, BHR, ASH (ModularBootstrap), AHMH, CTH, SEL/Primon.

Established [L]:
- Scattering: resonance ⇔ `ζ(2s)=0`; `Q=2Re[WH,WH]`; `D_s≤0`, zero iff `Re s=¼`; Hecke dispersion `V_p`; the Hecke algebra has a positive Poisson measure on truncated resonant states for every `Re u<0`; positive `T₂,T₃` polynomials annihilate any finite resonance set.
- Horizon: modular horizon = quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)`; ringdown in the modes of zeros; the mirror-odd sector is a cavity of cusp forms with zero horocycle means.
- Seeds: continuous bounded modular functions decaying in the cusp form a `*`-algebra containing the Maass cusp forms; `Λ_F` is holomorphic off `{0,½,1}` with `Λ_F(1−s)=Λ_F(s)`; the response Mellin transform continues to `Λ_F·2s(2s−1)/ξ(2s)`: positions are fixed by the group, a seed enters only through `Λ_F(ρ/2)`. Every seed with exponentially decaying polar transform rings down at its zero-free region: zero-free `Re z>Θ` ⇒ `y^{1−Θ/2−ε}`; a rate `y^α` forces `Λ_F(s₀)=0` at every zero of `ξ(2s)` with `Re s₀>1−α`. Every momentum channel carries every resonance with full multiplicity (`σ_{1−w}(n)/ζ(w)`).
- Cavity receivers: mirror-odd tent fields see every resonance by a phase law; pairs of Maass cusp eigenforms and pairs of Hecke eigenforms see every resonance; one cuspidal cavity function `g` of Hecke eigenforms sees every right resonance (Baire); RH ⇔ `|a_{|g|²}(y)−c|≤Cy^{¾−ε}` ∀ε; zero-free strip ⇔ a rate `y^α`, `α>½`; RH ⇔ every two-mode energy `|u+cv|²` rings down at `y^{¾−ε}`. Pair entries are Rankin–Selberg series `ρ_u(1)ρ̄_v(1)L(s,u×v)/ζ(2s)` up to Gamma factors; the diagonal of a Hecke eigenform is `ζ(s)` times Shimura's weight-½ integral, holomorphic on `Re s>0`; one eigenform is blind exactly at halving pairs `ζ(ρ)=ζ(ρ/2)=0` and at Shimura zeros; `T_p` is self-adjoint and Hecke eigenforms span every cusp space.
- Krein forms: the resonance Krein form at one resonance has infinite index of both signs at every zero; the reflection Krein form has at most one negative square, PSD on the line, exactly one negative square at each off-line zero; RH ⇔ every reflection Krein form PSD. The dual side has no sign: one-sided response bounds are as strong as two-sided ones and fail past `¾` at every seed seeing a critical resonance.
- Width axis: zero-free `Re ρ≤1−2δ` ⇔ pulse decay `e^{−(δ−ε)τ}` ⇔ horocycle rate `y^{½+δ−ε}` ⇔ smoothed Farey rate; RH ⇔ `y^{¾−ε}` ⇔ universal Lax–Phillips decay `e^{−t/4}`. Smooth profiles thermalize at `y^{½}exp(−√(−log y))`; sharp shells at log-free `O(√y)`; one sharp shell at the RH rate ⇔ RH ∧ Möbius × circle-remainder cancellation.
- Cusp channel: discrete spectrum, `N(Λ)≍Λ`; Rankin–Selberg continuation and FE; Rankin's bound; cusp-energy rate `y^{½−ε}`, `y^{¾−ε}` under RH.
- Narain AdS₃ source: literal partition, Mellin continuation retaining every arithmetic pole, central orders, boundary moment jets, remainder with exactly the VK saving; `¾` ⇒ RH; exponents `>¾` impossible.
- Graphs: black holes with flux, unitarity, Hecke; Krein flux law; Born rules; boundary algebra; genus-two graph with FE for every `q`, all-level count law iff `q≤3`.
- Standard forms: internal partner unitaries are central (Tomita collapse) and realize `Q` iff RH; external vacuum-fixing partner unitaries never have Tate limit `Q`; Borchers half-sided modular inclusions never carry `Q`.

Structure [D]: wave dynamics, unitarity, Hecke, KMS, `C*`, internal modular conjugation and half-sided inclusions leave damping open. The receivers are complete and sharp: what remains is one rate (`y^{¾}` for one cavity energy) or one reflection sign. In a GNS realization of `Q` the Hecke clock has pure point spectrum at the critical ordinates; the horizon carries the zeros as resonances. A physical carrier must connect the two.

| | Obstacle | Strength |
|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | — |
| B68 | Independent `D_s≥0`, nonnegative Krein flux, integer-probe sign, all-zero dispersion bound, or PSD of the reflection Krein forms of the cavity | RH |
| B69 | Positive physical carrier | producer |
| B70 | Lower bound for `V_p` from the carrier | sub |
| B71 | Universal decay `e^{−t/4}`; horocycle, Farey, Narain or one-cavity-energy rate `y^{¾−ε}` | RH |
| B87 | A count with Tate limit `Q` | RH |
| B113 | Möbius × quarter-disc remainder `Σ_{d≤X}μ(d)E(X/d)=O(X^{½+ε})` | beyond RH |
| B114 | A realization of the partner involution outside the central, vacuum-fixing and Borchers classes | producer |
| B117 | A confined companion of the modular horizon: a unitary system whose real normal-mode frequencies are mapped to the horizon resonances by a modular transformation | producer |
| B125 | Halving pairs: no zero `ρ` with `ζ(ρ/2)=0`, and nonvanishing of one Shimura integral at every `ρ/2` (makes one Hecke eigenform a complete receiver) | indep. |

### S8. Index and support

Routes: HKT, AKLT, SC, RIT, CWS through HF, ACS; LA; ZCG heat count. Established [L/K]: `κ(φ_c)=κ+1`; finite index ⇒ Lindelöf; `κ∈{0,∞}` under escape, mixing or decay; window index counts critical lengths; `sup_dN_d` = off-line multiplicity; `K_ζ^n` PD ⇔ RH; TFAE: `κ(K_ζ)<∞` ⇔ finite index on one two-prime lattice ⇔ finitely many off-line zeros ⇔ bounded non-real heat count ⇔ RH above some height; in the stratum RH ⇔ one non-blind prime tower PD ⇔ one Weil tower Toeplitz positive ⇔ one tower bounded on a thick set; finite off-line support ⇒ ZAL.

| | Obstacle | Strength |
|---|---|---|
| B12 | Index ceiling uniform in resolution | ≥qRH |
| B13 | Finitely many off-line zeros ⇒ none | sub |
| B23 | `N_d` bounded | ≥qRH |

### S9. Abscissa laws, transport and one-offs

Routes: BAG, JAS shell, SC undamped, WL thick runs, ACS sampling branch, ZCG one-off branch, RW polar ground energy. Programmes: AKLT, ZCG, IWT, SOSZ, EFT, AIF, APD, AAD, RAC, PTT, TAPO, SPAL, ACP.

Established [L]:
- Split, hierarchy and dial: see §0. Linear AAL is not shift-invariant: every `ξ(s+a)ξ(s−a)` satisfies the linear eventual-to-global law with `C=1+1/(2a)`; a slope uniform as `a→0` is `ZetaLinAt C`.
- Two-scale theorem; free AAL for recurrent configurations, exponential polynomials, curves, vertically periodic configurations, strip almost periodic functions, uniformly approximable Dirichlet series.
- Countermodels: `cosh` and two-scale `cosh` models; one reflection pair; harmonic-depth configurations (ZAL, infinitely many off-line zeros, no linear law); continuous Beurling systems; prime-square-corrected discrete one-offs and integer-norm one-offs with natural coefficients and linear counting, holomorphic and zero-free across the critical line with exactly one off-line pair; rational-prime one-offs; positive two-prime and Hecke annihilators of any finite zero set; the heat family; positive theta sources moved off the line by finite donor surgery with long endpoint jets and positivity after every finite prime deletion.
- FE rigidity: integrable or square-integrable FE defects force the rational primes; no nonclassical system carries a finite layer with such an FE.
- Annihilator costs: multiplicity `n` at `ρ` forces `base(σ,ρ)^n≤1+H(σ)`; reflected pairs cost a sinh ratio `>2^δ`; fixed height approaches `2^δ` iff `cos(γlog 2)=−1`; quotient inverses have mass and both signs in every late logarithmic band.
- AAL producers: not-attained top; bounded lag on a progression; lag excursions of lower Abel density zero; subexponential polar ground energy; one prime-window grid; log-dense integer lag; twisted plateau; JAS dressed, typical and shell positivity; bounded towers; one bounded cone; weak recurrence; slow aligned returns on right discs; a thick lag bound at one base; a thick prime-deviation bound `O(X^{½+a})` ∀`a>0`; a positive count of one tower; a one-sided crude bound of the spline traces at a sampling set of primes (a residue class, the primes off a set of relative density zero, the degrees `p^aq^b`); positive measure or positive Hausdorff dimension of the recurrent lag bases at every rate; uniform tensor moments at a residue class.
- Finite-layer world (¬AAL): isolated top, finite oscillation of `ψ`, syndetic lag excursions with a coefficient-density floor at every base, raw prime-current passage to `−ζ′/ζ` on a high strip at inverse-height damping and across dyadic windows, the prime current reading the top multiplicity without counterterm, head-conditioned rough variance; the FE reflects heights to themselves.
- Transport and tail: discs crossing `Re s=½` by depth `δ` force growth `T^{cδ√δ}`, flat crossing edges `T^{c₀δ}`; escaping translates bounded on a domain meeting `Re s>1` stay in `Re s>½`; partial returns transport a zero or force a deep relative small value; short-arc Euler approximation needs prime mass `≳log|τ|`; zeros of ζ are zeros of every Euler tail; near-full tail cancellation has positive density at every strip point.

Structure [D]: AAL needs a Dirichlet-series input that couples both scales, uses the Euler product and the FE together, and turns the FE (a height reflection) into transport in height. On the prime side such inputs exist as receivers: one-sided crude bounds at sampling sets. ¬AAL is a finite exceptional layer: an exclusion problem of Landau–Siegel type.

| | Obstacle | Strength |
|---|---|---|
| A37 | Resonator mean of `|ζ|²` with resonators growing below the Kronecker scale (unverified) | — |
| A47 | Explicit window constants of the tower theorems for one top quartet `Θ±iγ` at base `π/γ` (unverified) | — |
| B83 | AAL | sub |
| B89 | A bounded aligned return at each right zero on a right disc | sub |
| B96 | Conditional law of the Euler tail at the Kronecker scale | sub |
| B13 | Finite stratum | sub |
| B110 | Thick crude count: `primeDeviation(X)=O(X^{½+a})` on a thick set of geometric scales of one base, every `a>0` | AAL |
| B111 | `ZAL ⇒ RH` (existential linear AAL) | sub |
| B112 | A mechanism converting the FE into vertical transport of zeros | sub |
| B116 | Linear AAL at one fixed slope `C≥1` (⇔ thick relative crude count) | sub |
| B126 | A one-sided crude bound of the spline traces on one sampling set of primes (e.g. `p≡a (mod q)`) | AAL |
| B127 | Positive Lebesgue measure of the bases with recurrent sub-top lag readings, at every rate | AAL |
| B128 | Replication in the finite-layer world: the prime-current passage, rough variance and height reflection force a second zero at the same depth (one quartet first) | sub |
| B72 | Cutoff-uniform target mass | RH |
| B82 | Inner-field decay | ≥qRH |

### S10. Count and effectivity

Routes: ACS, HF, PM integer probes; RW through window naive heights. Programmes: AE, CWS, LST, KPA, ASH, CTH, RIT, SOSZ, RIAC, HHAC, HTG.

Established [L]: polar surface calculus; Tate principle both ways; five currencies; theta `h⁰` with exact RR; Künneth `h¹` split; source cone and all-aperture RR; Bézout ⇔ RH. Curves: integral Castelnuovo–Severi defect is the Tate limit of a count iff unitary; on a true hyperelliptic curve the defect of every integral class is a natural number. Over ℤ: `Q(a)=Σa_ma_nC(log(m/n))`; Hecke isometry of `Q`; RH ⇔ `Q` is the Tate limit of an `ℕ`-count; `Q` is not integer-valued and no integral kernel reproduces it (in particular no trace form of Hecke endomorphisms of a free abelian group); linear counts degenerate; RH ⇔ every integer plane `⟨Γ₁,Γ_n⟩` carries a binary `ℕ`-count with Tate limit `δ_n(x,y)=c_B(0)x²+2c_B(log n)xy+c_B(0)y²` ⇔ every effective prime class `Γ_1+Γ_p` carries an `ℕ`-count along its ray with Tate limit `2c_B(0)+2c_B(log p)` ⇔ the prime planes are copositive ⇔ the same at any power-saving gap set ⇔ the planes `⟨Γ_m,Γ_n⟩`, `m,n∈⟨p,q⟩`, carry binary counts. Arithmetic counts: integral trace cokernels are different quotients `R[X]/(f,f′)` with `|disc|` elements (infinite in the singular case); the integer gluing quotient is `ℤ/(1−M(N))` with oriented determinant the sum of the local singular indices; Gaussian section heights of divisor quotient classes have quadratic Tate limit (squared transverse distance), uniformly in the conductor; Hecke arithmetic sections retain every conductor charge with a unimodular squarefree multiplication matrix. Finite fields: residue rings `ℤ[X]/(P,Q)` have `|Res(P,Q)|` elements and quadratic log scaling under thickening; radial cyclotomic counts converge to the discriminant height; Frobenius-stable orbit counts of any finite permutation action are exactly `q^{|I|}`; the root-orientation cover of degree-`n` monic polynomials has `qⁿ` points (`n≥2`, odd `q`); elliptic and hyperelliptic orientation and squarefree-divisor counts have square-root discrepancy from the curve root bound, with no trace formula as input.

Structure [D]: on curves the count comes from point counts before any sign is known; over ℤ the off-diagonal is assembled from positive dampings, the sign sits in the diagonal, and no point count with Tate limit `δ_p(1,1)` is known on a single prime ray.

| | Obstacle | Strength |
|---|---|---|
| A28 | Reciprocal-quadric traces = vanishing-cycle Frobenius traces (unverified) | — |
| A41 | Count law for every curve over `𝔽_q` (Bombieri–Stepanov), first case plane quartics [C] | — |
| A48 | Hasse–Weil test of smoothed Frobenius pairs at verified scales | — |
| B87 | A count on the rays `Γ_1+Γ_p`, defined without `Q`, with Tate limit `2c_B(0)+2c_B(log p)` | RH |
| B88 | A counterterm-free damping presentation of the diagonal of Weil's form on smoothed graphs | RH |
| B65 | Genus upper law; logarithmic Serre duality; first Epstein real zero | indep. to sub |

### S11. Prime orbit at finite time

Routes: BAG, TH, SRT, RW, ZCG carriers, every route at the all-height wall. Programmes: PTT, TAPO, TTPO, SPAL, IWT, ALST.

Established [L]: windows of length `exp(10y√(log y·log log y/δ))` enter every `δ`-box; savings `8/(10⁹L⁶ℓ⁴)` at length `48L²ℓ`, `t^{−δ}` at `L^A`; first return bracketed at every precision (constant precision between `(log y)^{3/2−o(1)}` and `y/log y` in `log R`); RH bracket `exp(√(y/(48log y)))` at constant precision under RH, at precision `≍y^{−9/2}` unconditionally; proportional saving ⇔ no early heavy return; conditional Gaussian tail below the Kronecker scale; smooth × prime collision costs; returns freeze smooth Dirichlet polynomials; two distinct primes have no common exact return; Rouché copies of forced vanishing cost `J≤e²r log N+log(1/δ)`; integrality acts only on the torsion; zero estimates at sign and torsion returns uniform in the number of logarithms. Transcendence [S]: explicit linear forms in `k` logarithms with exponent `≍k²log(kW)` (necessarily `≥k−1`); depth law `t≥poly(1/δ)` for every pair of primes; return–form duality and the breadth cap at the Kronecker scale; jets survive a deep return to order `0` at constant precision and to order `1` below the Baker threshold.

| | Obstacle | Strength |
|---|---|---|
| A24, A37 | Certified scans and brackets; growing resonators (unverified) | — |
| A53 | Integrate the transcendence modules (umbrella, audit) | — |
| B46 | Proportional saving at length `(log X)^{2K}`, all heights | sub |
| B97 | Constant-precision first return: `log R(y,δ)≥y^c` for fixed `δ`, by an argument of growing height | sub |
| B100 | A saving for `t log n` on moving block families past Vinogradov's degree | sub |
| B121 | Freezing control beyond the precision cap: signed, or integral at sign returns | sub |
| B15 | Past VK | sub |
| B20 | Oscillation of the actual amplitude with the height | RH |

### S12. Topology of the prime complex

Routes: MC (nerve, Redheffer), HF and ACS through the coprime stratum. Programmes: HWV, ADT, ESG, HHAC, RIAC, HAT.

Established [L]: `det R_N=M(N)=−χ̃` of the prime-star nerve; squarefree prime complex ≃ wedge of spheres; `χ̃=Ω±(√N)`; RH ⇔ `χ̃=O(N^{½+δ})`; persistence classified and `s`-independent; finite face realizations have finite singular homology with Euler characteristic the alternating face count; a face-preserving cutoff-natural self-map homotopic to the identity fixes exactly the prime vertices; local exits are sphere bouquets; local index = Euler characteristic of block/exit relative singular homology, `Σ_p index = 1−M(N)`, indices unbounded below; the connected core is a bouquet with augmented Euler characteristic `M(N)+#primes(N/2,N]`; completed prime boundary closed iff `2Re s+δ>1`. **Orientation cover over ℤ:** the real points of `y²=disc F_n`, `F_n=Π_{p|n}(X²+p)`, number `1+μ(n)`; its integral equation is the Sylvester discriminant; the cover over `n≤N` has `N+M(N)` points; its centred count `D(N)=M(N)` exceeds `c√N` and `−c√N` infinitely often (the middle cohomology never vanishes and has weight `≥½`), and weight `½` ⇔ RH; rational fibres lose the orientation. Over `𝔽_q[T]` the factor-trace cover has exactly `qⁿ` points.

Structure [D]: Lefschetz localization of `χ` to the primes is exact; each local index is a Möbius sum over integers with least prime factor `p`; square-root cancellation must occur across primes. Homotopy, homology and persistence do not see `Im s`. The orientation cover exists over ℤ; over `𝔽_q` its middle cohomology vanishes, over ℤ it is the trace of the zeros.

| | Obstacle | Strength |
|---|---|---|
| A46 | Local singular indices beyond the cubic cutoff `N>p³` (unverified) | — |
| B10 | Top coprime stratum | RH |
| B106 | A natural self-map or action on the orientation cover over ℤ (or the prime complex) with bounded local indices whose Lefschetz number is the centred count, localizing `M(N)` to `O(N^{½+ε})` | RH (≥qRH at `θ<1`) |

### S13. Infinite-rank elimination

Routes: WL (thick runs), ZCG (tower form), ACS (thick curve counts), BAG, JAS. Programme: IWT.

Established [L]: Weil towers, level sums; the FE acts on level sums only as `S(−ν)=conj S(ν)`; exceptional-rank window theorem; price of hiding a top `≥εR^{M+1}`; rank barrier (roots-of-unity towers); infinite-rank Hasse–Weil principle; curves: unit circle ⇔ bounded traces ⇔ thick bounded traces ⇔ thick point counts within `Cq^{n/2}`; ZAL ⇔ well-foundedness; Wolff towers show well-foundedness is needed; towers of ζ with lag weights `1/(q(1−q))`; positive count of one tower ⇒ AAL; RH ⇔ ZAL ∧ (thick bounded lag / positive count of one or every tower / thick `O(X^{½})` prime deviation); linear six-way TFAE; continuous-level lag bound = zero-free half-plane. **Sampling of bases:** under ¬AAL the recurrent sub-top bases have dimension 0 and every large sampled lag exceeds every sub-top threshold at almost every base; positive dimension or positive measure at every rate ⇒ AAL; the actual lag has a dense `G_δ` of bases with recurrence at every rate unconditionally, of dimension 0 for rapid cancellation; finite oscillatory sums have uniform jets and sublevel covers.

| | Obstacle | Strength |
|---|---|---|
| A47 | Explicit rung-`k=1` window constants (unverified) | — |
| B110 | Thick crude count for ζ | AAL |
| B127 | Positive-measure recurrence of the Weil lag at every rate | AAL |
| — | ZAL | ≥qRH |

### S14. Intersection theory on half-products

Routes: ACS, HF, PM count branch. Programmes: SOSZ, HAT, AE, RIAC, HHAC, CTH.

Established [L]: zonotope defect `2Σ_k(Σ_{n>k}a_n)²` with exact count Tate limit; off-diagonal Weil = `C_∞` + Abel limit of positive twisted torsion energy; **archimedean Frobenius = Green function of `ℍ³`**: `archKernel(m,n)/√(mn)=2πG_{1/2}(d)`, `d=|log(n/m)|` the hyperbolic distance of `(0,0,m)` and `(0,0,n)`; `k=0` the cusp, `k≥1` the jets; damped kernels PSD with diagonal `n/(1−r²)`. **Finite places are trees:** on a `p`-ladder the prime kernel is `log p((p−1)/√p)G^{T_p}_{1/2}`, the tree Green function at the Ramanujan point, PD on apartments; **adelic Green formula** `W=` pole `−Σ_v` local Green kernels. **Spherical compensation:** `C_∞=(3/2)φ_{3/2}−2πG_{3/2}`; the plastic ratio is its sign change; primes never change the atomic sign; Beurling–Deny holds exactly on plastic windows. Image distances `cosh d(z_t,γz_u)=½(|a|²r+|d|²/r+|b|²/P+|c|²P)`. No twisted carrier with convergent Poincaré series at `½` carries the torsion (dilation limits are ratio kernels); no embedding into a compact quotient, or into a finite-volume quotient given a Newtonian kernel with cusp expansion, reproduces the Frobenius intersection. Locked atomic dampings have the discriminant diagonal and are never PSD; the atomic genus is `≍N log N`; the prime channel has spectral radius `≍log N`; the smooth archimedean self-energy is logarithmic with one universal counterterm. Smoothed graphs: RH ⇔ one side of Hasse–Weil at the primes ⇔ `c_B` is a counterterm-free PSD limit; neither smoothed channel alone is one.

Structure [D]: every place carries the Green function of a rank-one symmetric space at the critical parameter. The sign is the diagonal: the self-energy of the configuration in the adelic Green pairing, which atoms cannot supply (discriminant diagonal) and smoothing renormalizes.

| | Obstacle | Strength |
|---|---|---|
| A54 | Instantiate the cusp expansion with nonzero Wronskian for the `L²` resolvent of `Δ−¾` on Bianchi quotients (closes finite-volume carriers) | — |
| B87, B88 | Count; counterterm-free damping presentation of the diagonal | RH |
| B129 | The diagonal of a smoothed locked damping: does the `ℍ³`-plus-tree damping, locked so that its logarithmic divergences cancel on smoothed probes, have finite diagonal limit `c_B(0)`, and what is the defect if not (§2.8 of the summary) | method |

### S15. Functional-equation rigidity and the finite-layer world

Routes: BAG, ZCG, SC/JAS, ACS (source identification), PM. Programmes: EFT, ExactEventTheory, APD, SEL.

Established [L]: countable Beurling systems with `Σnorm^{−3/2}<∞` and theta FE up to a measurable polynomially bounded `L¹` or `L²` defect are the rational primes with zero defect; the chain is a unitary Gamma–Mellin source, a strong Hardy boundary, the tent identity, atomic recurrence, vanishing in the unit gap, origin Fejér integer support and unit multiplicities. Integrable defects forbid norm collisions and force additive saturation; asymptotic integer support is rigid; local theta data determine the defect; positive measures with gap `(−1,1)∖{0}` are tent-self-dual iff Dirac combs. Gaussian surgery: the local differential defect of `e^{x/2−πe^{2x}}` determines every causal measure; atomic Euler corrections, positive or signed, cannot repair it. Prime current: finite parts without zero-free premises; resonance at zeros; top multiplicity read without counterterm; joint height/damping finite part; under ¬AAL raw passage to `−ζ′/ζ` at inverse-height damping and across dyadic windows; head-conditioned rough variance. Normalized height reflection `O(t^{−¼})`; whole-quadrant boundedness impossible.

Structure [D]: FE + Euler product identify ζ among all systems with integrable defect; every exact identity of the finite-layer world is height-preserving. Transport is missing.

| | Obstacle | Strength |
|---|---|---|
| A55 | FE rigidity for generalized (continuous) Beurling systems with integrable defect, from Poisson rigidity and the tent machinery (unverified) | — |
| B112 | FE → vertical transport | sub |
| B128 | Replication in the finite-layer world | sub |

### S16. Lefschetz–Stepanov over ℤ

Routes: ACS (Stepanov branch), BAG, WL. Programmes: ALST, AHA, EAHT, AKLT.

Established [L]: the Adams operation is the Frobenius of integer auxiliaries — dilation on the prime orbit, Galois on the torsion, `ψ_qF=F` on the `(q−1)`-torsion; the norm amplifier at every uniform order; Siegel auxiliaries on the torsion; Stepanov's construction on the torsion with an `ℓ`-adic amplifier; exact order costs the degree; integrality cannot create zeros at returns (countable zero heights); the excess order at the common fixed point is a relation among `log p` (Gelfond–Schneider for two primes); the closed-point Stepanov count is Chebyshev's; minimal torsion auxiliaries are rigid; torsion quotient detection; the fixed-point auxiliary `A_N` has log length `ψ(N)` and RH ⇔ `ψ(N)≤N+C√N log²N`; the bound fails for the integer-norm one-off; zero estimates uniform in the number of logarithms. Triangular torsion Newton bases [S].

Structure [D]: the exact Stepanov method over ℤ reproduces Chebyshev and nothing more; the arithmetic Stepanov bound lives on the smoothed Frobenius graphs at the prime degrees (Π123), not in the degree of an auxiliary.

| | Obstacle | Strength |
|---|---|---|
| B121 | Freezing beyond the cap: integral at sign returns, or signed | sub |
| B48 | Deciding input at square-root precision | RH |

## 3. Live routes

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy, one-sided `Φ`, a one-sided crude bound at the prime degrees, or ZAL plus a thick `O(√X)` prime deviation → RH.
- **Established [L/K]:** bounded endpoint energy ⇔ RH; integer lag ⇔ RH; `Ω±(√n)`; first-band abscissa `2Θ`; gauge exponents `[Θ,1]`; subtracted lag ⇔ ZAL; lag excursions of lower Abel density zero ⇒ AAL; one-sided Gaussian prime ceiling at every rational height ⇔ RH; RH ⇔ ZAL ∧ thick `O(X^{½})`; thick `O(X^{½+a})` ∀`a` ⇒ AAL; `ZetaLinAt C` ⇔ thick `O(X^{½+C(Θ∞−½)+ε})`; continuous-level bound `O(e^{aL})` ⇔ zero-free `Re>½+a`; RH ⇔ `P(p)≤A(p)+K` at every prime (Stepanov bound as a prime count); positive-measure lag recurrence ⇒ AAL.
- **(a)** A30.
- **(b)** Bounded endpoint energy (B49); half-power at the trivial gauge (B50); deciding input (B48); the prime-window bound (B130); thick crude count (B110); `ZAL⇒RH` (B111); ZAL; past VK (B15).

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every radius → RH.
- **Established:** blocks S2, S3; RH ⇔ `Ψ` locally bounded; cone nonempty ⇔ RH; relative compactness ⇔ RH; naive height on every window ⇔ RH; RH ⇔ ZAL ∧ subexponential polar ground energy; window positivity at `a` gives depth-`¼` exclusion to height `e^{a/K}` and `R_c≥c₁e^{c₂a}` [L].
- **(a)** A1–A3, A16.
- **(b)** All-aperture sign (B1); bounded oscillation of `Ψ` (B2); variation of `r` (B3); outer predictors (B4); margin law (B16); blind positivity (B18); count on windows (B87).

### FU — Signed prime scheduling
- **Path:** signed Möbius history → one-sided sampled Abel bound → RH.
- **Established [L]:** fixed-`m` criterion; one sample per backward window; bounded blocks paid at fixed horizons.
- **(a)** None that moves the route.
- **(b)** Complete-history cross-clock bound (B42).

### CFC — First-clock lower bound
- **Path:** first-clock sine coefficient bounded below on a tail → RH.
- **Established [L]:** exact tail criterion; phase-natural transport is identity.
- **(a)** None.
- **(b)** Lower bound retaining prime, archimedean and endpoint terms (B42).

### RP — History floor
- **Path:** matched-quantile history → eventual linear floor → RH.
- **Established [L]:** exact criterion; low-LCM payment; sublinear floor impossible.
- **(a)** None.
- **(b)** High-LCM pairs, moving core, singular terms in one floor (B42).

### PA — Prime–archimedean passivity (HJ alias)
- **Path:** prime−Gamma source sign → RH.
- **Established [L]:** Hausdorff rows nonnegative for `r≥min(C₀(k+1)²,S(k))` with explicit shift; remaining entries ⇔ RH; exterior diagonal criterion at `218/25`.
- **(a)** Verified rows (A1).
- **(b)** Signs below the explicit boundary, exterior `K(z,z)≥0`, or `TV(n)/qⁿ→0` (B31).

### MC — Möbius cancellation
- **Path:** half-power Möbius or Liouville cancellation → RH.
- **Established [L/K]:** damped energy ⇔ RH; one-point form; VK Hilbert energy; Möbius zeros condense on `Re s=Θ`; gauge genericity; producer rates; parity exponent = zero abscissa; exact identity pins `λ`; twin quarter floor; Farey discrepancy ⇔ RH; `M(N)=−χ̃` of the nerve; `Σ_p` prime-vertex local indices `=1−M(N)`, indices unbounded below; persistence `s`-blind; integer gluing quotient `ℤ/(1−M(N))`; orientation cover over ℤ with centred count `M(N)`, weight `≥½` unconditionally and `=½` ⇔ RH; Möbius over `ℤ[ω]` a cubic Gauss coefficient with nonzero residue at `4/3`.
- **(a)** Chowla [C] (A21); cubic residue Fourier coefficients (A33); prime-vertex indices past the cubic cutoff (A46).
- **(b)** Trivial-gauge cancellation or zero exclusion for `M_X` (B50); deciding input (B48); past VK (B15); theta identification and rational transfer of the cubic branch (B94); a bounded-index self-map of the orientation cover (B106).

### TT — Theta tail / Wold
- **Path:** weighted endpoint energy bounded for each `0<t<½` → RH.
- **Established [L]:** Wold residual VK; `D_t+Q_t/2≥0`; boundedness ⇔ RH; uniform bound on a shrinking band.
- **(a)** None that moves the route.
- **(b)** `C_t` at every fixed `t` (B34); odd branch B4.

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted or sublinear root height → RH.
- **Established [L]:** block S4; infinitely many unshifted degrees ⇔ RH; inner roots real; `N_d≤300√(d log d)`; `sup_dN_d` = off-line multiplicity; heat-divisor budgets `N(t)(2t)^q≤2S_q`, sharp elapsed coefficient `2`.
- **(a)** A20; A1; A50.
- **(b)** Outer roots (B22); `N_d` bounded (B23) gives finite support only, RH once B13 is known; finite initial depth budgets (B124).

### ZCG — Zero-configuration geometry / heat descent
- **Path:** half-Gaussian source → no positive-time collision → RH; tower, linear, sampling and transport branches for AAL.
- **Established [L]:** blocks S4, S5, S9, S15; abscissa laws of configurations (purity = ZAL ∧ AAL, transport, free classes, curve split, two-scale theorem, linear hierarchy with explicit separating configurations, quantifier collapse, shift non-invariance, finite-rank Chebyshev exponent); heat: finite-stratum laws on `H_t` are RH, linear AAL along the heat flow is RH, only `τ=0` has a Dirichlet series; heat-divisor budgets and crowding dissipation; one-off jets; maximal-angle law; horizontal jet gain ceiling = isolation gap `<½`.
- **(a)** A19, A47, A50.
- **(b)** Small-time collisions (B24); frequency (B25); non-size frequency input (B47); runs (B27); FE-pair reality (B76); crowded zeros (B59); finite initial budgets (B124); AAL through transport, tower, sampling or rigid-world contradiction (B83, B89, B110, B112, B126, B128); `ZAL⇒RH` (B111); fixed slope (B116); rotated relation (B92, B93).

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH.
- **Established [L]:** defect trace class; multiplicity `≤` trace norm; Gaussian passage criterion.
- **(a)** None that moves the route.
- **(b)** Trace norm `<1` on every rectangle or bounded Gaussian oscillation (B38).

### HF — Hodge / Hecke / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** blocks S1, S10, S14; source-work `≤2` ⇔ RH; `R_c=R_polar=R_halfline≤R_prim=R_high=W`, every threshold `=⊤` ⇔ RH; charged compactness closed; ¬RH gives a unit half-line ground state at finite `W`, polar-orthogonal if `R_polar=W`; no universal holomorphic multiplier dominates the depleted kernel; low packet at every ratio is RH; unrestricted Gårding false [L].
- **(a)** A9, A13.
- **(b)** Full-space sign at every `K` (B6); low packet at every ratio (B101); polar payment below `W` and ground-state orthogonality (B104); correlated pairings (B123); head windows (B8); source-work ceiling (B41); top coprime stratum (B10); zero modes (B9); exact SOS (B11); Rosati and band poles (B78, B79); count and damping presentation (B87, B88); smoothed locked diagonal (B129).

### CHMD — Causal hyperbolic–modular duality
- **Path:** one-sided bounded prime wave or odd Doob half-threshold bound → RH.
- **Established [L]:** wave and Doob receivers; normalized prime−pole decay; nonfirst source keeps `1−ε` of Gamma.
- **(a)** None that moves the route.
- **(b)** Either side of the unnormalized wave bound, or the complete odd sign (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel → RH.
- **Established [L unless marked]:** rank 14 at `0<a≤½`; rank `N` from verified height `41+6(N+2)log(N+2)`; VK collar; two-atom and chain signs; `S=Π_pT_pA`; insertion cone; locking = torus positivity; columns add; current `=2|Ξ|²Re ξ′/ξ`; first-atom Gamma floor; the adaptive head `M(b)=⌈|b|/2+B⌉` pays the omitted pair sum by half that floor in every polynomial-square integral; weighted Legendre estimates preserve degree and exact norms; `ρ_q≥e^{−2q}W/8` for `q≥3`, `ρ_q/W=1+O_q(1/τ)`; fixed heads have leading term `(4/√π)|Σ_{n≤M}n^{−½+2iτ}|²`; the adaptive partial sum equals `ζ(½+ib)` up to `(9√2+√(1+2(B+1)))|b|^{−½}` and the head's leading term is `|ζ(½+ib)|²` up to `O(|ζ||b|^{−½}+|b|^{−1})`; no summable absolute pair majorant [S]; no compact core funds every Gamma direction [S].
- **Structure [D]:** positivity is automatic where `|ζ(½+ib)|` is large; the sign is decided by second-order terms near the critical zeros.
- **(a)** Rank 15+ (A4); tail-failure certificate (A5); scans and brackets (A24); verified ranks (A1); Gamma-weighted transport of the fixed-head asymptotic to `M=M(b)` (A42).
- **(b)** Exact torus law for `S*` and `{2,3}` cross-chain positivity (B19); amplitude oscillation with the height (B20); all ranks (B21); signed adaptive head near critical zeros (B102); tail law at the Kronecker scale (B96).

### RN — Theta renewal
- **Path:** two-ended renewal → no joint nodes → RH.
- **Established [L]:** `det₂` gives `D`, not Ξ; Ξ zeros = joint nodes; energy comparison ⇔ RH.
- **(a)** None.
- **(b)** Joint-node exclusion or energy comparison (B36).

### WD — Ward / collision / long moments
- **Path:** source current, window energy or long moments → RH.
- **Established [L]:** block S5; one-window form; slope rigidity; long mean values are collision counts of order `X²/log X ≲ · ≲ X²log²X`; corridor bad-window measure `O(T/log^ηT)`.
- **(a)** A18.
- **(b)** Cofinal long moment (B62); depth density (B57); `D_win` (B58); cluster wall (B59); Green moments (B60); detector past the last scale (B61); collision charge (B63).

### LI — Paired Li / Cayley ladders
- **Path:** primitive lower bound or Li sign → RH.
- **Established [L]:** guarded zero set finite, RH iff empty; ladder = Li; response floor criterion; Li `n≤314`.
- **(a)** A1.
- **(b)** Budget at every guarded zero, primitive lower bound or response floor (B43).

### SZ — Suzuki screw
- **Path:** completed Abel residual bounded → RH.
- **Established [L]:** first variation = Weil energy; `|A_N|≤C√N e^{−c·vkScale N}`.
- **(a)** None that moves the route.
- **(b)** `sup|A_N|<∞`, complete first-variation sign, or Ward lower bound (B37, B1).

### PM — Gauss–Mayer physical model
- **Path:** scattering source → Krein/Lewis positivity, integer-probe sign, dispersion bound, horocycle/Farey rate, resonant decay, Narain remainder, cavity-energy rate, reflection Krein sign or a realization of the partner involution → RH.
- **Established:** block S7; integer-probe positivity ⇔ RH; Krein flux sign ⇔ RH; horocycle rate `y^{¾−ε}` ⇔ RH; unconditional stretched-exponential thermalization; sharp shell at the RH rate ⇔ RH ∧ Möbius–circle cancellation; universal decay `e^{−t/4}` ⇔ RH; Narain `¾` ⇒ RH, remainder VK; one cuspidal cavity function of Hecke eigenforms sees every resonance and its ringdown at `y^{¾−ε}` ⇔ RH; two-mode energies ⇔ RH; reflection Krein forms PSD ⇔ RH; dual side has no sign; RH ⇔ `Q` is the Tate limit of a count ⇔ an internal standard form realizes `Q`; `Q` not integer-valued, no integral kernel; vacuum-fixing and half-sided realizations excluded [L].
- **(a)** A26.
- **(b)** `D_s≥0`, Krein flux, probe sign, dispersion bound or reflection Krein sign (B68); physical carrier (B69); `V_p` lower bound (B70); any rate past `½` or `¾` (B14, B71); count (B87); halving pairs for a single eigenform (B125); realization outside the excluded classes (B114); confined companion (B117).

### PTR — Cosine source / photonic
- **Path:** `A_h` collision-free descent → RH.
- **Established [L]:** sech handoff; strict Laguerre for `h≥½` and above VK; sign at every `0<h<½` ⇔ RH.
- **(a)** A50.
- **(b)** Strict sign below VK (B29); lossless prime-faithful stack (B69).

### JAS — Joint ancestry
- **Path:** subpower control on moving finite power windows → RH.
- **Established [L]:** RH criterion on `m<k≤m+m/log(m+1)`; finite admission; shell positivity infinitely often ⇒ AAL; typical JAS positivity ⇒ AAL; dressed PSD ⇒ AAL.
- **(a)** None.
- **(b)** Uniform control on the moving window (B51); shell signs plus ZAL.

### CTF — Chronological tail / Báez–Duarte
- **Path:** approximation, defect, BSY sign, log-dilation equality, cut-kernel mass or mollifier infimum → RH.
- **Established [L]:** rows ⇔ RH; sharp defect, sparse subpolynomial ⇒ RH; BSY `I≤0` ⇔ RH; positive-proportion form; exact infimum `exp(2I(1))`; one-`δ` dilation equality ⇔ RH; finite-energy cut-kernel mass annihilation ⇒ RH; coefficient-Hardy domain of `ζ(s+ε)` trivial for `ε≤½`.
- **(a)** None that moves the route.
- **(b)** Rows, sparse defect, BSY sign, positive proportion (B52); near-unit budgets (B66); cut-kernel mass (B91).

### HCF — Heat trace
- **Path:** both prime-log grids positive at every degree, or one Gaussian prime ceiling at every rational height → RH.
- **Established [L]:** two-grid criterion; explicit detector degree; chirp criteria; RH ⇔ `P(ε,r)` bounded above on `ε≥1` for every rational `r≥½`.
- **(a)** A1.
- **(b)** Nonnegativity at every degree, chirp bound, or the Gaussian ceiling (B30).

### XN — Newton discs
- **Path:** line-centered self-map discs covering every zero → RH.
- **Established [L]:** coverage and margin criteria; `ΔM≥0`; local damping.
- **(a)** None.
- **(b)** Cover every zero with `M≥0` (B32).

### BAG — Self-return
- **Path:** strong self-return or uniform target mass → RH; transport or tail events → AAL.
- **Established:** blocks S9, S11, S15; cutoff-uniform mass ⇔ RH; AAL ⇔ tail transport; transport on right discs; crossing discs force power growth `T^{cδ√δ}` (arcs) or `T^{c₀δ}` (flat edges); escaping translates bounded on a domain meeting `Re s>1` stay right of `½`; partial returns transport a zero or create a deep small value; short-arc Euler approximation needs prime mass `≳log|τ|`; returns at zeros tail-bad; near-full tail events positive density; forced-vanishing precision cap; integrality only on the torsion; under ¬AAL raw prime-current passage and rough variance; FE preserves height [L].
- **(a)** A37.
- **(b)** Uniform target mass (B72); exact tail events at every right zero (B83, B89); tail law at the Kronecker scale (B96); freezing beyond the precision cap (B121); replication (B128); decay (B82).

### EWU — Even sector
- **Path:** even blind minimum `≥0` → RH.
- **Established [L]:** Hamburger form; neutral gauge; Markov to `log ρ`; blind minimum `≥1/20` for `a≤(log 2+1/50)/2`.
- **(a)** A1–A3.
- **(b)** Blind minimum `≥0` at every aperture (B4, B17, B44).

### GTA — Schur charge
- **Path:** cofinally small quartic charge or compact full mode → RH.
- **Established [L]:** charge family; compactness ⇔ RH; late charge `≤HS/400`.
- **(a)** None that moves the route.
- **(b)** Charge `<ε` at arbitrarily late stages (B33).

### OWU — Odd sector
- **Path:** odd polar-hyperplane positivity → RH.
- **Established [L/K]:** shifted Hamburger; unit window reads `w₂`; frustration; prime 3 cannot be deleted past `3/5` or replaced past `287/500`.
- **(a)** A1–A3, A6.
- **(b)** Sign at every aperture on odd `F` with `∫F sinh(x/2)=0` (B4, B17, B44).

### PBM — Regularized abscissa
- **Path:** pole-regularized prime series converges for every `σ>½` → RH.
- **Established [L]:** exact equivalence.
- **(a)** None.
- **(b)** `|Σ_{n<N}(Λ(n+1)−1)/log(n+1)|≤C_εN^{½+ε}` (B53).

### RB — Robin/Nicolas
- **Path:** eventual extremal divisor inequality → RH.
- **Established [L]:** colossally abundant and lcm reductions.
- **(a)** None.
- **(b)** Eventual inequality (B54).

### SRT — Lag localization
- **Path:** complete two-bump sign or horizon-layer sign → RH.
- **Established [L/K]:** full-family receivers; depth corridors; two-lobe bound; cut crystal; sharp location; local pair cost; explicit Hausdorff shifts; critical threshold identities (S1); either prime two-bump family `B±τ_{log p}B` decides RH from one side, one test per prime.
- **(a)** A9.
- **(b)** Complementary-window sign, remaining-depth control (B6, B12, B101); the prime two-bump sign (B130); all-height column (B46).

### ACT — Single shift
- **Path:** one shift pays every even compact profile → odd positivity → RH.
- **Established [L/K]:** receiver; `{2,3,4}` band; floors through `a_k`.
- **(a)** A7.
- **(b)** One shift uniform in profile (B44, B4).

### AIP — Incidence
- **Path:** complete reflected-prime/pole allocation → subexponential cost → RH.
- **Established [L/K]:** allocation; VK cost; capacity `log log N+O(1)`; gcd-twist channel law; non-gcd periodic twists coercive to the admissible period scale; conductor resolution and threshold identities (S1).
- **(a)** A9, A13.
- **(b)** `C_σe^{2σr}` cost (B45); polar payment (B6, B101, B104).

### SC — Stokes / Witt–Krein
- **Path:** glued index `≤1`, bounded damped coupling, or undamped coupling plus ZAL → RH.
- **Established [L]:** `κ(φ_c)=κ+1`; damped bound ⇔ RH; undamped cone bound ⇒ AAL.
- **(a)** None that moves the route.
- **(b)** Arithmetic coupling bound; tensor loss (B39); B9, B11, B13.

### ACS — Castelnuovo–Severi / Stepanov at the prime degrees
- **Path:** source energy → all-aperture Bézout → RH; or one side of Hasse–Weil for the smoothed Frobenius graphs at the prime degrees → RH; or a one-sided bound at a sampling set → AAL, with ZAL → RH.
- **Established [L/K]:** blocks S10, S14, S16; source cone and RR; Bézout ⇔ RH; primitive `h¹` coercive for `a≤181/500`; Kloosterman purity; reciprocal quadric counts; Young projections at rank `≤4`; Toeplitz minors `≤200`; typical-height sign with Gaussian tails; frequency-packet average; degree-one Selberg classification; count law of every hyperelliptic curve. Frobenius graphs: RH ⇔ `c_B(log p)≥−K` at every prime ⇔ `≤K` ⇔ `P(p)≤A(p)+K` ⇔ the same on any power-saving gap set; width ⇔ growth exponent of either side; zero-free strips improve themselves at the `p^k`; RH ⇔ uniform tensor moments; Rankin square abscissa `2maxRe ρ`; RH ⇔ one-sided bounds on two-prime difference lags; one-sided bounds at sampling sets ⇒ AAL; the lower side is blind exactly to nonnegative almost periodic top layers, the upper side has no mask; count door on one ray per prime.
- **(a)** A28, A41, A48.
- **(b)** Source-energy sign (B40, B1); the prime-window bound (B130); a sampling-set bound (B126); count or Rosati producer over ℤ (B78, B87); damping presentation (B88); smoothed locked diagonal (B129); global trace (B85); mixed Young shapes (B86); B65; B28.

### SEC — Seam / Fock
- **Path:** factorial jet energy at ξ zeros → RH.
- **Established [L]:** seam admitted; Fock bound ⇔ RH.
- **(a)** None.
- **(b)** Bound at actual zeros (B73).

### CDC — Dagger (BSH alias)
- **Path:** marked-repair equality at ξ zeros → RH.
- **Established [L]:** canonical potential; `N=1,n=2` equality suffices.
- **(a)** None.
- **(b)** Equality at every zero (B74).

### PCS — Co-shift
- **Path:** reflection-odd class vanishes at ξ zeros → RH.
- **Established [L]:** quotient vanishing ⇔ `ℓ²` co-shift ⇔ RH.
- **(a)** None.
- **(b)** Vanishing at every zero; differential lift retaining the shift defect (B75).

## 4. Candidates

Each needs its independent mechanism first (B81).

| Candidate | Established [L] | (a) Just work | (b) Open mathematics |
|---|---|---|---|
| APF | prime/grade trace reconstruction on real labels | none | full-divisor exhaustion and RH landing |
| EGC | double-Gaussian zero-pair contour; count error `≤32ε²log T/T` | none | height-fibre isolation; outer landing |
| EWJ | all-depth reporter; norm exhaustion only on the blind plane | none | faithful endpoint admission |
| FEL | KL accounting; BSY criterion belongs to CTF | none | predeclared history forcing the BSY sign |
| IRK | finite idempotent traces; Meyer–Ξ free resolution | none | projective lift identifying trace with Chern charge |
| MSC | unweighted `L²` discrepancy; conormal transport | none | Sonin/Weil sign landing |
| RFHM | support source; creation; strong exhaustion | none | RH-sufficient orientation law |
| W1C | Lee–Yang receiver; one-interval convergence suffices | none | finite ferromagnetic producer converging to Ξ |
| WBF | Gram recovers magnitudes and phase class | none | arithmetic stream and Ξ landing |

## 5. Supporting programmes

| Programme | Established [L] | (a) Just work | (b) Open mathematics |
|---|---|---|---|
| SOSZ | zonotope, two half-products, point count, archimedean Frobenius as `ℍ³` Green function, damped Frobenius PSD, infinite rank, plastic sign and plastic Beurling–Deny windows, atomic genus `N log N`, prime channel `≍log N`, logarithmic archimedean self-energy, one side of Hasse–Weil at the integer, square, power, prime and prime-power degrees = RH, iterated gap method, width = growth exponent at every gap set, zero-free strips improve themselves, trace zeta at the power degrees, Stepanov bound = prime count, tensor-power trick, Rankin square abscissa, two Frobenii (difference lags RH; single degrees AAL with attainment; attainment needed for finite monoids), sampling sets ⇒ AAL, lower-side blind set, real-zero masking, Dirichlet `L` from both sides (GRH from the upper side, Siegel zeros included), count door on one ray per prime | A48 | B87, B88, B126, B129, B130 |
| HAT | image distances, twisted carriers and their dilation limits, carriers of bounded geometry, along ends of bounded self-energy, at conical limit points, with a closed degree geodesic, boundary of a group convergent at `½` (no parabolics), compact and finite-volume embeddings, spherical compensation, locked dampings give the discriminant, finite places are trees, adelic Green formula, middle cohomology of the orientation cover | A54 | B88, B106, B129 |
| ALST | Adams Frobenius on torsion and orbit, norm amplifier, Siegel and Stepanov auxiliaries on the torsion, exact vanishing costs the degree, integrality only on the torsion, excess order = relation among `log p`, closed-point Stepanov count, rigid minimal auxiliaries, Lefschetz numbers = Stepanov degrees (`ψ(N)`), separation of ζ from the one-off, zero estimates at returns; torsion Newton bases [S] | none | B121, B48 |
| AHMH | seeds, position rigidity, every-seed receiver, ringdown = zero-free region, dual side has no sign, momentum universality, odd cavity sees every resonance, pair entries = Rankin–Selberg series, Maass and Hecke pairwise visibility, Baire reduction and its converse, one cavity function a complete and sharp receiver, two-mode Zagier dichotomy, Hecke cosets, `T_p` self-adjoint, Shimura integral, halving obstruction, resonance and reflection Krein forms | A26 | B68, B71, B125 |
| EFT, ExactEventTheory | complete FE rigidity for `L¹` and `L²` defects, Gamma–Mellin source, Hardy boundary, tent identity and recurrence, integer support, norm-collision exclusion, local theta identification, Gaussian surgery and causal-measure recovery, atomic and signed Euler corrections, Gaussian prime current (finite parts, resonance at zeros, top multiplicity, uniform archimedean damping, joint height/damping, finite exceptional subtraction, passage at inverse height and across dyadic windows), head-conditioned rough variance, normalized height reflection, whole-quadrant obstruction | A55 | B112, B128 |
| TTPO [S] | explicit linear forms in `k` logarithms, return–form duality, breadth cap, depth law of returns, survival of jets at a deep return | A53 | B97, B121 |
| IWT | towers, level sums, window theorem, rank barrier, Hasse–Weil principle at infinite rank, curve TFAE, Wolff towers, towers of ζ, crude step as Toeplitz count, continuous-level lag = zero-free region, linear six-way TFAE, two-scale `cosh` models, precision cost of forced vanishing, collision size of prime mean values, sampling dimension and metric top detection, residual recurrence, arithmetic-cell curvature, finite oscillatory jets | A47 | B110, B111, B116, B127, ZAL |
| ZCG (AbscissaLaws) | split, transport, two-scale theorem, linear hierarchy with separating configurations, quantifier collapse, shift non-invariance, finite-rank Chebyshev exponent, heat-family finite-stratum law, Dirichlet-series selector of `τ=0` | A50 | B13, B83, B111 |
| AES | polynomial heat clock, finite collision times, reciprocal velocities, elapsed-depth and logarithmic-depth actions through collisions, initial divisor budgets of the ξ heat divisor, crowding dissipation, sharp coefficient `2`, deepest-product contraction, initial trace of heat depth energy | A19 | B124 |
| RIAC | completed prime boundary and exterior graph closure, prime-star and torsion compensation (`α>2`), prime-vertex dynamics, signed localization `Σ index=1−M(N)`, integer gluing counts, divisor relation geometry, integral and Gaussian section heights uniform in the conductor, Hecke arithmetic sections, prime-quadratic orientation, different and trace counts, rational fibres, finite-field root cover, Vieta correspondence, orientation determinants, elliptic and hyperelliptic orientation and squarefree counts with square-root discrepancy | A46 | B106, B88 |
| CTH | count law at every genus, every hyperelliptic curve, Born rules, boundary algebra, linear counts degenerate, Hecke conservation, second place, Farey reading, thermalization, sharp shells, modular conjugation ≠ partner involution, partner standard-form trichotomy, half-sided inclusions excluded, `Q` not integer-valued, no integral kernel | A41 | B87, B113, B114, B117 |
| APD | Hamburger rigidity, FE-defect isolation, one-offs of every positive class including discrete and integer-norm one-offs across the critical line, firewall, positive two-prime annihilators with multiplicity and their mass laws, quotient signs in bounded logarithmic bands, sparse harmonic annihilation, coefficient oscillation of annihilator inverses, relocation, Poisson rigidity of self-dual measures with a gap, additive saturation from integrable defects, finite endpoint-jet surgery of ξ and of positive theta sources, uniform real-zero division and prime-deletion bounds, Hecke state PD iff `s≥½` | A55 | B80, B98 |
| AHD / CACT | threshold identities `R_c=R_polar=R_halfline≤R_prim=R_high=W`, charged compactness, half-line ground states and orthogonality, half-line resolvent identities and multiplier no-go, aperture exchange, top-window non-escape, conductor resolution, adaptive head = `|ζ(½+ib)|²` | A9, A13 | B6, B8, B101, B104, B123 |
| AIF | inner field, Szegő infimum, rigidity, Carleson measure, dilation quotient, causal certificate, forward map, restoring bound, `Ψ`-boundedness ⇔ RH, Selberg depth `O(T)`, Bohr profiles, insertion cone, columns, local onset field | none | B2, B57, B66, B82 |
| AAD | producers, peak law, half scale, three-quarter floor, compensated producer, quarter rate under RH, parity-neutral rate, rate = Mertens scale, Frobenius = factorial stencil, transport, slow returns right of the line, crossing arcs pay three halves, flat crossing edges pay linear depth | A30 | B15, B55, B89 |
| RAC | cut identity and kernel, unique fake, carry, ledger hierarchy, twin at every degree, parity exponent, exact parity identity, exchange law, bounded count with a new zero, maximal angle, extremal-law model, rotated relations | none | B67, B91, B92, B93 |
| TAPO | first return and brackets, precision law, heavy returns, conditional moments, resonator mean, arithmetic mean values, recurrence dichotomy, tail of a return, AAL as tail transport, near-full tail events of positive density, partial returns, short-arc prime mass, Euler coordinates | A24, A37 | B89, B96, B97, B100 |
| SPAL | shifted-product rigidity, collision cells, smooth × prime collision classes, count-distance rigidity, positive near-count model | none | B98 |
| PTT | Bohr isometry, boxes, savings, rounded orbit, discrepancy, mixing time, hull with natural boundary, Ξ-current lift, certificates | A24 | B46, B100 |
| ASH | graph black holes, Krein law, Lax–Phillips rank two, one clock, KMS, count law at genus one, genus-two graph; ModularBootstrap: Narain partition, central orders, moment jets, VK remainder, `¾` ⇒ RH, ceiling `¾` | none | B68, B71, B87 |
| BHR | modular wave, metric, AdS₄ quotient, pulse regularity, ringdown = strip, horocycle Mellin formula and Zagier converse, Lax–Phillips semigroup, odd cavity, Maass cusp forms, Weyl order, Rankin–Selberg continuation and FE, Rankin bound, eigenform RS Euler product, cusp-energy rates | A26 | B71 |
| RIT | Mayer scattering, Krein square, Hecke dispersion, Hecke algebra Poisson on resonant states | none | B68, B70 |
| ACP | Mertens energy residues, positive Hecke annihilators, reflected-pair decay boundary, prime-pair source | none | B68 |
| SEL / Primon | degree-one classification, Euler rigidity; primon thermal Euler factors, Kesten–McKay densities | none | B80 |
| MMD | Möbius over `ℤ[ω]` as cubic Gauss coefficient, fixed ray phase, frozen dual phase, cubic Eisenstein series, nonzero residue, Fredholm pencil on the cubic quotient, continued Fourier modes | A33 | B94 |
| AE, KPA | polar calculus, Tate law, naive heights, five currencies, torsion intersection, Stepanov over ℤ | none | B87, B88 |
| HHAC | isolated-prime rigidity, fixed-point obstruction, core Euler characteristic, core bouquet, weighted torsion operators | none | B88, B106 |
| ESG | prime-height filtration, barcode, `s`-independence, prime-weighted homology, two-prime block quotients | none | B106 |
| HTG | integral trace cokernels, monic residue duality, discriminants as Vandermonde squares, Gaussian theta tails, weighted root-sum continuity | none | none |
| CSTW | canonical system, scalar flow, soft kick, Green corner, AC traces, `L¹` drift | A16 | B2, B3 |
| CHT | margin law, pinning, datum region, bands, local density, cone PNT `5/6`, bounded extremals | A6 | B16 |
| VHR | height 67; window, Li, Hausdorff, heat, Jensen, PF, theta rungs | A1, A2 | none; decides no all-aperture statement |
| NGF | frequency, gap laws, maximum principle, crystal and reality at critical scale | A19 | B24–B27, B47 |
| MZF | Selberg CLT, cameras, hyperbolic density, last scale, Möbius zero condensation | A18 | B57–B61 |
| FFP | `N_d` law, saddle region, stability dictionary, bulk blindness | A20 | B22, B23 |
| ADO | carrier repulsion; exceptional set of dimension zero; FE-pair flatness | none | B77 |
| APR | necessary length, Euler mollifier length `log²T`, filters, prefix amplification, collar laws | A18 | B48 |
| AKLT, ASRP | Stepanov over `𝔽_q`, Nair lattice, integrality halves, stencil ceilings; AAL producers | none | B48, B83 |
| AGT | gauge torus, pole-subtracted spectrum, twin quarter floor | none | B50 |
| PBAP, W3 | blind positivity, exact null blind test | none | B18 |
| WVL | universal threshold, two-lobe, cut crystal | none | none beyond B1 |
| CAF, TCS | two-atom, chains, Euler product, current, rank 14, first-atom reserve, adaptive pair payment, weighted Legendre kernel, Gamma floors | A4, A5, A24, A42 | B19–B21, B102 |
| HWV, ADT | nerve, sphere bouquet, `M(N)=−χ̃`, Redheffer gluing, finite face singular Euler characteristic | none | B10 |
| AK, Representation | column and rank-`≤4` Young projections, Kloosterman traces, reciprocal quadric counts | A28 | B85, B86 |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ∩Π one-sided crude bound at the prime degrees (`P(p)≤A(p)+K`; one Weil test per prime), transversal | ACS, SRT, WL, HF, RW, and every window route through Σ141 |
| Σ sign on every window (`a*(ζ)=⊤`) | RW, EWU, OWU, ACT, CHMD, SZ, RN, ACS (source branch), AIP, SRT, SC, LI, TT (odd), HF, and the critical-curve branches of HF, SRT, AIP (window + polar payment + ground-state orthogonality) |
| Σ continuation at small time and the theta head at the critical zeros | ZCG (heat branch), PTR, LA, GTA, XN, HCF, PA, TH |
| Π square-root precision and long moments | WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| Γ reflection and selection | PM (reflection Krein form, rates), BAG, SEC, CDC, PCS |
| Missing source landing | APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF |
| Missing count / diagonal of the damping presentation, transversal | ACS, HF, PM, RW through windows |
| Two-scale input for B13, `ZAL⇒RH` and AAL (sampling-set bound, transport, replication), transversal | BAG, JAS shell, SC undamped, WL thick runs, ACS sampling branch, ZCG one-off, linear and tower branches, RW polar ground energy |
| Dark range (Kronecker scale; breadth of returns), transversal | every route at all heights; BAG and ZCG one-off branches; TH certificates; WD near-unit moments |
| Width axis (horizon observables, growth exponents at the primes), transversal | PM (horocycle, Farey, Lax–Phillips, Narain, cavity energy), MC (Farey, orientation cover), ACS (growth of either side at the primes), every VK-scale saving |
