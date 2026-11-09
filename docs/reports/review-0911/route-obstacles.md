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

Routes: ZCG, LA, PTR, HCF, PA, GTA, XN. Programmes: NGF, FFP, ADO, RHTower heat.

Established [L]: collision criterion; horizon `(6600/9991+ε)/log X`; density-one `Λ_Xlog X→0`; crystal and reality at the critical scale; sharp depth law for isolated simple zeros; `N_d` law and inner-root reality; cosine Laguerre above VK; nonrepelling values of dimension zero; maximal-angle law; one-sided Gaussian prime ceiling at every rational height ⇔ RH; high-collision counts ⇔ ZAL. **Heat family:** every `H_t` (`t>0`) has asymptotic off-axis depth `0`; a finite-stratum law valid on all `H_t` gives RH; existential linear AAL along `t→0⁺`, even with a `t`-dependent slope, is RH.

| | Obstacle | Strength |
|---|---|---|
| A19, A20 | Heat horizon toward its method floor; Jensen rung (unverified) | — |
| A50 | Finite-stratum laws on the cosine family `A_h` and the shifted Jensen family imply RH (unverified) | — |
| B24 | Collisions at arbitrarily small time, all heights | RH |
| B25 | Frequency `<1` at every collision | RH |
| B26 | Arithmetic input distinguishing `Φ` among `Φe^{−τx²}` | method |
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

Routes: PM; W1C (candidate); RN and PTR in part. Programmes: RIT, ART, AOT, ACP, BHR, ASH (ModularBootstrap), CTH, SEL/Primon.

Established [L]:
- Scattering: resonance ⇔ `ζ(2s)=0`; `Q=2Re[WH,WH]`; `D_s≤0`, zero iff `Re s=¼`; Hecke dispersion `V_p`; the Hecke algebra has a positive Poisson measure on truncated resonant states for every `Re u<0`; positive `T₂,T₃` polynomials annihilate any finite resonance set.
- Horizon: modular horizon = quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)`; ringdown in the modes of zeros; the mirror-odd sector is a cavity of cusp forms and the zeros couple only to the mirror-even half.
- Width axis: zero-free `Re ρ≤1−2δ` ⇔ pulse decay `e^{−(δ−ε)τ}` ⇔ horocycle rate `y^{½+δ−ε}` ⇔ smoothed Farey rate; RH ⇔ `y^{¾−ε}` ⇔ universal Lax–Phillips decay `e^{−t/4}`. Smooth profiles thermalize at `y^{½}exp(−√(−log y))`; sharp shells at log-free `O(√y)`; one sharp shell at the RH rate ⇔ RH ∧ Möbius × circle-remainder cancellation.
- Cusp channel: Maass cusp forms, discrete spectrum, `N(Λ)≍Λ`; Rankin–Selberg continuation and FE; Rankin's bound; for a Hecke eigenform `Λ_g=½Γ_ℝ(2s)(2π)^{−s}γ_ν(s)(|ρ(1)|²+|ρ(−1)|²)Π_pQ_p^{−1}` on `Re s>2`, i.e. a Gamma factor times `L(g×ḡ,s)` (`ζ(s)L(Sym²g,s)` for real eigenvalues); cusp-energy rate `y^{½−ε}`, `y^{¾−ε}` under RH; rate `y^α` forces `Λ_g(ρ/2)=0` for `Re ρ>2−2α`.
- Narain AdS₃ source: literal partition, Mellin continuation retaining every arithmetic pole, central orders, boundary moment jets, remainder with exactly the VK saving; `¾` ⇒ RH; exponents `>¾` impossible.
- Graphs: black holes with flux, unitarity, Hecke; Krein flux law; Born rules; boundary algebra; genus-two graph with FE for every `q`, all-level count law iff `q≤3`.
- Standard forms: internal partner unitaries are central (Tomita collapse) and realize `Q` iff RH; external vacuum-fixing partner unitaries never have Tate limit `Q` (their cross-horizon correlations are multiplicative Hankel kernels, Hecke-invariant ones factor through the squarefree core, continuous log-Toeplitz and positive-energy Laplace profiles are constant); Borchers half-sided modular inclusions never carry `Q` (no non-identity eigenvalue of `U(a)`, trivial on finite-dimensional invariant subspaces and on every graph black hole, alternating Cesàro Bohr averages vanish).

Structure [D]: wave dynamics, unitarity, Hecke, KMS, `C*`, internal modular conjugation and half-sided inclusions leave damping open. In a GNS realization of `Q` the Hecke clock has pure point spectrum at the critical ordinates; the horizon carries the zeros as resonances. A physical carrier must connect the two.

| | Obstacle | Strength |
|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | — |
| A43 | Identify the continued `Λ_g` with a Gamma factor times `L(g×ḡ,s)` on ℂ (uniqueness of continuation) | — |
| B68 | Independent `D_s≥0`, nonnegative Krein flux, integer-probe sign or all-zero dispersion bound | RH |
| B69 | Positive physical carrier | producer |
| B70 | Lower bound for `V_p` from the carrier | sub |
| B71 | Universal decay `e^{−t/4}`; horocycle, Farey or Narain rate `y^{¾−ε}` | RH |
| B87 | A count with Tate limit `Q` | RH |
| B109 | Rankin–Selberg noncancellation: `Λ_g(ρ/2)≠0` at every off-line zero for some `g` | indep. |
| B113 | Möbius × quarter-disc remainder `Σ_{d≤X}μ(d)E(X/d)=O(X^{½+ε})` | beyond RH |
| B114 | A realization of the partner involution outside the central, vacuum-fixing and Borchers classes | producer |
| B117 | A confined companion of the modular horizon: a unitary system whose real normal-mode frequencies are mapped to the horizon resonances by a modular transformation | producer |

### S8. Index and support

Routes: HKT, AKLT, SC, RIT, CWS through HF, ACS; LA; ZCG heat count. Established [L/K]: `κ(φ_c)=κ+1`; finite index ⇒ Lindelöf; `κ∈{0,∞}` under escape, mixing or decay; window index counts critical lengths; `sup_dN_d` = off-line multiplicity; `K_ζ^n` PD ⇔ RH; TFAE: `κ(K_ζ)<∞` ⇔ finite index on one two-prime lattice ⇔ finitely many off-line zeros ⇔ bounded non-real heat count ⇔ RH above some height; in the stratum RH ⇔ one non-blind prime tower PD ⇔ one Weil tower Toeplitz positive ⇔ one tower bounded on a thick set; finite off-line support ⇒ ZAL.

| | Obstacle | Strength |
|---|---|---|
| B12 | Index ceiling uniform in resolution | ≥qRH |
| B13 | Finitely many off-line zeros ⇒ none | sub |
| B23 | `N_d` bounded | ≥qRH |

### S9. Abscissa laws, transport and one-offs

Routes: BAG, JAS shell, SC undamped, WL thick runs, ZCG one-off branch, RW polar ground energy. Programmes: AKLT, ZCG, IWT, AIF, APD, AAD, RAC, PTT, TAPO, SPAL, ACP.

Established [L]:
- Split, hierarchy and dial: see §0. Linear AAL is not shift-invariant: every `ξ(s+a)ξ(s−a)` satisfies the linear eventual-to-global law with `C=1+1/(2a)`; a slope uniform as `a→0` is `ZetaLinAt C`.
- Two-scale theorem; free AAL for recurrent configurations, exponential polynomials, curves, vertically periodic configurations, strip almost periodic functions, uniformly approximable Dirichlet series.
- Countermodels: `cosh` and two-scale `cosh` models; one reflection pair; harmonic-depth configurations (ZAL, infinitely many off-line zeros, no linear law); continuous Beurling systems; integer-norm and rational-prime one-offs (ZAL, violate every finite slope); positive two-prime and Hecke annihilators of any finite zero set; the heat family.
- Annihilator costs: multiplicity `n` at `ρ` forces `base(σ,ρ)^n≤1+H(σ)`; reflected pairs cost a sinh ratio `>2^δ`; fixed height approaches `2^δ` iff `cos(γlog 2)=−1`; the formal inverse of a positive annihilator with a zero `ρ` has coefficient excursions of both signs beyond `Ce^{α·frequency}` for every `0≤α<Re ρ`.
- AAL producers: not-attained top; bounded lag on a progression; lag excursions of lower Abel density zero; subexponential polar ground energy; one prime-window grid; log-dense integer lag; twisted plateau; JAS dressed, typical and shell positivity; bounded towers; one bounded cone; weak recurrence; slow aligned returns on right discs; a thick lag bound at one base; a thick prime-deviation bound `O(X^{½+a})` ∀`a>0`; a positive count of one tower.
- Transport and tail: discs crossing `Re s=½` force `|ζ|≥cτ^b`; partial returns transport a zero or force a deep relative small value; short-arc Euler approximation needs prime mass `≳log|τ|`; zeros of ζ are zeros of every Euler tail; near-full tail cancellation has positive density at every strip point.

Structure [D]: AAL needs a Dirichlet-series input that couples both scales, uses the Euler product and the FE together, and turns the FE (a height reflection) into transport in height. ¬AAL is a finite exceptional layer: an exclusion problem of Landau–Siegel type.

| | Obstacle | Strength |
|---|---|---|
| A37 | Resonator mean of `|ζ|²` with resonators growing below the Kronecker scale (unverified) | — |
| A47 | Explicit window constants of the tower theorems for one top quartet `Θ±iγ` at base `π/γ` (unverified) | — |
| B83 | AAL | sub |
| B89 | A bounded aligned return at each right zero on a right disc | sub |
| B96 | Conditional law of the Euler tail at the Kronecker scale | sub |
| B13 | Finite stratum | sub |
| B84 | Smallest FE defect of a discrete Euler product carrying a finite off-line layer | method |
| B103 | Positive discrete Euler products with linear counting, continuation across `Re s=½` and an FE: AAL? | method / sub |
| B110 | Thick crude count: `primeDeviation(X)=O(X^{½+a})` on a thick set of geometric scales of one base, every `a>0` | AAL |
| B111 | `ZAL ⇒ RH` (existential linear AAL) | sub |
| B112 | A mechanism converting the FE into vertical transport of zeros | sub |
| B116 | Linear AAL at one fixed slope `C≥1` (⇔ thick relative crude count) | sub |
| B72 | Cutoff-uniform target mass | RH |
| B82 | Inner-field decay | ≥qRH |

### S10. Count and effectivity

Routes: ACS, HF, PM integer probes; RW through window naive heights. Programmes: AE, CWS, LST, KPA, ASH, CTH, RIT, SOSZ, RIAC, HHAC.

Established [L]: polar surface calculus; Tate principle both ways; five currencies; theta `h⁰` with exact RR; Künneth `h¹` split; source cone and all-aperture RR; Bézout ⇔ RH. Curves: integral Castelnuovo–Severi defect is the Tate limit of a count iff unitary; on a true hyperelliptic curve the defect of every integral class is a natural number. Over ℤ: `Q(a)=Σa_ma_nC(log(m/n))`; Hecke isometry of `Q`; RH ⇔ `Q` is the Tate limit of an `ℕ`-count; `Q` is not integer-valued; linear counts degenerate; RH ⇔ every integer plane `⟨Γ₁,Γ_n⟩` carries a binary `ℕ`-count with Tate limit `δ_n(x,y)=c_B(0)x²+2c_B(log n)xy+c_B(0)y²`. Finite fields: residue rings `ℤ[X]/(P,Q)` have `|Res(P,Q)|` elements and quadratic log scaling under thickening; radial cyclotomic counts realize rational Abel torsion energy with exact homogeneous term and converge to the discriminant height; Frobenius-stable orbit counts of any finite permutation action are exactly `q^{|I|}`; the orientation cover of degree-`n` monic polynomials has `qⁿ+(−1)ⁿΣμ` points.

Structure [D]: on curves the count comes from point counts before any sign is known; over ℤ the off-diagonal is assembled from positive dampings, the sign sits in the diagonal, and no point count is known.

| | Obstacle | Strength |
|---|---|---|
| A28 | Reciprocal-quadric traces = vanishing-cycle Frobenius traces (unverified) | — |
| A41 | Count law for every curve over `𝔽_q` (Bombieri–Stepanov), first case plane quartics [C] | — |
| A48 | Hasse–Weil test of smoothed Frobenius pairs at verified scales | — |
| B87 | A count on integer probes, defined without `Q`, with Tate limit `Q` | RH |
| B88 | A counterterm-free damping presentation of the diagonal of Weil's form | RH |
| B95 | An abelian group with Hecke endomorphisms whose trace form is `Q` | producer |
| B65 | Genus upper law; logarithmic Serre duality; first Epstein real zero | indep. to sub |

### S11. Prime orbit at finite time

Routes: BAG, TH, SRT, RW, ZCG carriers, every route at the all-height wall. Programmes: PTT, TAPO, SPAL, IWT.

Established [L]: windows of length `exp(10y√(log y·log log y/δ))` enter every `δ`-box; savings `8/(10⁹L⁶ℓ⁴)` at length `48L²ℓ`, `t^{−δ}` at `L^A`; first return bracketed at every precision (constant precision between `(log y)^{3/2−o(1)}` and `y/log y` in `log R`); RH bracket `exp(√(y/(48log y)))` at constant precision under RH, at precision `≍y^{−9/2}` unconditionally; proportional saving ⇔ no early heavy return; conditional Gaussian tail below the Kronecker scale; smooth × prime collision costs; returns freeze smooth Dirichlet polynomials; two distinct primes have no common exact return; Rouché copies of forced vanishing cost `J≤e²r log N+log(1/δ)`.

| | Obstacle | Strength |
|---|---|---|
| A24, A37 | Certified scans and brackets; growing resonators (unverified) | — |
| B46 | Proportional saving at length `(log X)^{2K}`, all heights | sub |
| B97 | Constant-precision first return: `log R(y,δ)≥y^c` for fixed `δ` | sub |
| B100 | A saving for `t log n` on moving block families past Vinogradov's degree | sub |
| B121 | Freezing control beyond the precision cap (signed or integral) | sub |
| B15 | Past VK | sub |
| B20 | Oscillation of the actual amplitude with the height | RH |

### S12. Topology of the prime complex

Routes: MC (nerve, Redheffer), HF and ACS through the coprime stratum. Programmes: HWV, ADT, ESG, HHAC, RIAC.

Established [L]: `det R_N=M(N)=−χ̃` of the prime-star nerve; squarefree prime complex ≃ wedge of spheres; `χ̃=Ω±(√N)`; RH ⇔ `χ̃=O(N^{½+δ})`; persistence classified and `s`-independent; finite face realizations have finite singular homology with Euler characteristic the alternating face count; a face-preserving cutoff-natural self-map homotopic to the identity fixes exactly the prime vertices; local exits are sphere bouquets; local index = Euler characteristic of block/exit relative singular homology, `Σ_p index = 1−M(N)`, indices unbounded below (`1−#{q>p: pq≤N}` below the cubic cutoff); the connected core is a bouquet with augmented Euler characteristic `M(N)+#primes(N/2,N]`; completed prime boundary closed iff `2Re s+δ>1`.

Structure [D]: Lefschetz localization of `χ` to the primes is exact; each local index is a Möbius sum over integers with least prime factor `p`; square-root cancellation must occur across primes. Homotopy, homology and persistence do not see `Im s`. Over `𝔽_q[T]` the Möbius sum is the point defect of an orientation cover (Stickelberger) of exact size `qⁿ` for `n≥2`; no ℤ-analogue is constructed.

| | Obstacle | Strength |
|---|---|---|
| A46 | Local singular indices beyond the cubic cutoff `N>p³` (unverified) | — |
| B10 | Top coprime stratum | RH |
| B106 | A natural relative pair with `χ=M(N)`, or a self-map whose signed fixed-point indices localize `M(N)` to `O(N^{½+ε})` | RH (≥qRH at `θ<1`) |
| B120 | An orientation cover over the integers whose point defect is `μ` | producer |

### S13. Infinite-rank elimination

Routes: WL (thick runs), ZCG (tower form), ACS (thick curve counts), BAG, JAS. Programme: IWT.

Established [L]: Weil towers, level sums; the FE acts on level sums only as `S(−ν)=conj S(ν)`; exceptional-rank window theorem; price of hiding a top `≥εR^{M+1}`; rank barrier (roots-of-unity towers); infinite-rank Hasse–Weil principle; curves: unit circle ⇔ bounded traces ⇔ thick bounded traces ⇔ thick point counts within `Cq^{n/2}`; ZAL ⇔ well-foundedness; Wolff towers (positive weights, every mode off the circle, all nonzero levels vanish) show well-foundedness is needed; towers of ζ with lag weights `1/(q(1−q))`; positive count of one tower ⇒ AAL; RH ⇔ ZAL ∧ (thick bounded lag / positive count of one or every tower / thick `O(X^{½})` prime deviation); linear six-way TFAE; continuous-level lag bound = zero-free half-plane.

| | Obstacle | Strength |
|---|---|---|
| A47 | Explicit rung-`k=1` window constants (unverified) | — |
| A49 | Assembly: thick crude Hasse–Weil for smoothed Frobenius graphs `|c_B(νℓ)|≤C_ae^{aνℓ}` on a thick set ⇒ AAL (spline weights in the window theorem) | — |
| B110 | Thick crude count for ζ | AAL |
| — | ZAL | ≥qRH |

### S14. Intersection theory on half-products

Routes: ACS, HF, PM count branch. Programmes: SOSZ, AE, RIAC, HHAC, CTH.

Established [L]: zonotope defect `2Σ_k(Σ_{n>k}a_n)²` with exact count Tate limit; off-diagonal Weil = `C_∞` + Abel limit of positive twisted torsion energy; **archimedean Frobenius = Green function of `ℍ³`**: on coprime orders `archKernel(m,n)/√(mn)=Σ_{k≥0}e^{−(2k+½)d}=2πG_{1/2}(d)`, `d=|log(n/m)|` = hyperbolic distance of `(0,0,m)` and `(0,0,n)`; `k=0` is the cusp, `k≥1` the jets; damped kernels `√(mn)e^{−d/2}/(1−r²e^{−2d})` PSD with diagonal `n/(1−r²)`; Weil's archimedean + pole weight `=4πG_{1/2}(u)−4cosh(u/2)`; `2πG_{1/2}=2πG_{3/2}+1/(2cosh(d/2))`. Separated archimedean Cauchy blocks nonsingular, no finite-rank kernel on coprime orders; `C_∞(m,n)<0` iff `n/m` below the plastic number [S]. Atomic graphs: genus `≍N log N` on a dyadic block and on all degrees `≤N`, unconditionally; jets give the harmonic row sum `2N(1+log N)`, primes `≤2N`, pole rank two. Smoothed graphs: RH ⇔ Hasse–Weil for every pair ⇔ at every integer degree ⇔ at the squares ⇔ at prime pairs; prime planes give width `≤θ−½` from prime gaps `x^θ`, hence `≤1/12` (Huxley) [S]. No metric on `ℙ¹_ℤ`, no toric pairing and no continuous Hecke kernel carries the archimedean place.

Structure [D]: the three off-diagonal channels are a rank-two pole and two positive dampings; the jets carrier is `ℍ³`. The sign is the diagonal: the Newtonian self-energy of a point of `ℍ³` plus the torsion diagonal, renormalized; renormalization carries no sign.

| | Obstacle | Strength |
|---|---|---|
| A51 | Prime-degree width bound with prime-gap exponent `0.525` (width `≤0.025`) [C] | — |
| B87, B88 | Count; counterterm-free damping presentation of the diagonal | RH |
| B118′ | Hyperbolic carriers beyond the thin–thick obstruction (finite-volume quotients fold or diverge at cusps [S]); twisted infinite-volume Green functions | producer |
| B119 | Prime gaps `O(x^{½+ε})` (prime planes decide RH through this route iff) | sub |

## 3. Live routes

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy, one-sided `Φ`, or ZAL plus a thick `O(√X)` prime deviation → RH.
- **Established [L/K]:** bounded endpoint energy ⇔ RH; integer lag ⇔ RH; `Ω±(√n)`; first-band abscissa `2Θ`; gauge exponents `[Θ,1]`; subtracted lag ⇔ ZAL; lag excursions of lower Abel density zero ⇒ AAL; one-sided Gaussian prime ceiling at every rational height ⇔ RH; RH ⇔ ZAL ∧ thick `O(X^{½})`; thick `O(X^{½+a})` ∀`a` ⇒ AAL; `ZetaLinAt C` ⇔ thick `O(X^{½+C(Θ∞−½)+ε})`; continuous-level bound `O(e^{aL})` ⇔ zero-free `Re>½+a`.
- **(a)** A30.
- **(b)** Bounded endpoint energy (B49); half-power at the trivial gauge (B50); deciding input (B48); thick crude count (B110); `ZAL⇒RH` (B111); ZAL; past VK (B15).

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
- **Established [L/K]:** damped energy ⇔ RH; one-point form; VK Hilbert energy; Möbius zeros condense on `Re s=Θ`; gauge genericity; producer rates; parity exponent = zero abscissa; exact identity pins `λ`; twin quarter floor; Farey discrepancy ⇔ RH; `M(N)=−χ̃` of the nerve; `Σ_p` prime-vertex local indices `=1−M(N)`, indices unbounded below; persistence `s`-blind; Möbius over `ℤ[ω]` a cubic Gauss coefficient with nonzero residue at `4/3`.
- **(a)** Chowla [C] (A21); cubic residue Fourier coefficients (A33); prime-vertex indices past the cubic cutoff (A46).
- **(b)** Trivial-gauge cancellation or zero exclusion for `M_X` (B50); deciding input (B48); past VK (B15); theta identification and rational transfer of the cubic branch (B94); topological localization (B106); orientation cover over ℤ (B120).

### TT — Theta tail / Wold
- **Path:** weighted endpoint energy bounded for each `0<t<½` → RH.
- **Established [L]:** Wold residual VK; `D_t+Q_t/2≥0`; boundedness ⇔ RH; uniform bound on a shrinking band.
- **(a)** None that moves the route.
- **(b)** `C_t` at every fixed `t` (B34); odd branch B4.

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted or sublinear root height → RH.
- **Established [L]:** block S4; infinitely many unshifted degrees ⇔ RH; inner roots real; `N_d≤300√(d log d)`; `sup_dN_d` = off-line multiplicity.
- **(a)** A20; A1; A50.
- **(b)** Outer roots (B22); `N_d` bounded (B23) gives finite support only, RH once B13 is known.

### ZCG — Zero-configuration geometry / heat descent
- **Path:** half-Gaussian source → no positive-time collision → RH; tower, linear and transport branches for AAL.
- **Established [L]:** blocks S4, S5, S9; abscissa laws of configurations (purity = ZAL ∧ AAL, transport, free classes, curve split, two-scale theorem, linear hierarchy with explicit separating configurations, quantifier collapse, shift non-invariance, finite-rank Chebyshev exponent); heat: finite-stratum laws on `H_t` are RH, linear AAL along the heat flow is RH; one-off jets; maximal-angle law; horizontal jet gain ceiling = isolation gap `<½`.
- **(a)** A19, A47, A50.
- **(b)** Small-time collisions (B24); frequency (B25); time-0 selector (B26); non-size frequency input (B47); runs (B27); FE-pair reality (B76); crowded zeros (B59); AAL through transport, tower or rigid-world contradiction (B83, B89, B110, B112); `ZAL⇒RH` (B111); fixed slope (B116); rotated relation (B92, B93).

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH.
- **Established [L]:** defect trace class; multiplicity `≤` trace norm; Gaussian passage criterion.
- **(a)** None that moves the route.
- **(b)** Trace norm `<1` on every rectangle or bounded Gaussian oscillation (B38).

### HF — Hodge / Hecke / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** blocks S1, S10, S14; source-work `≤2` ⇔ RH; `R_c=R_polar≤R_prim=R_high=W`, every threshold `=⊤` ⇔ RH; charged compactness closed; low packet at every ratio is RH; unrestricted Gårding false [L].
- **(a)** A9, A13.
- **(b)** Full-space sign at every `K` (B6); low packet at every ratio (B101); polar payment below `W` (B104); head windows (B8); source-work ceiling (B41); top coprime stratum (B10); zero modes (B9); exact SOS (B11); Rosati and band poles (B78, B79); count and damping presentation (B87, B88).

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
- **Path:** scattering source → Krein/Lewis positivity, integer-probe sign, dispersion bound, horocycle/Farey rate, resonant decay, Narain remainder, cusp-energy rate or a realization of the partner involution → RH.
- **Established:** block S7; integer-probe positivity ⇔ RH; Krein flux sign ⇔ RH; horocycle rate `y^{¾−ε}` ⇔ RH; unconditional stretched-exponential thermalization; sharp shell at the RH rate ⇔ RH ∧ Möbius–circle cancellation; universal decay `e^{−t/4}` ⇔ RH; Narain `¾` ⇒ RH, remainder VK; cusp-energy rate reads `Λ_g(ρ/2)`; RS Euler product of eigenforms; RH ⇔ `Q` is the Tate limit of a count ⇔ an internal standard form realizes `Q`; `Q` not integer-valued; vacuum-fixing and half-sided realizations excluded [L].
- **(a)** A26, A43.
- **(b)** `D_s≥0`, Krein flux, probe sign or dispersion bound (B68); physical carrier (B69); `V_p` lower bound (B70); any rate past `½` or `¾` (B14, B71); count (B87); Rankin–Selberg noncancellation (B109); realization outside the excluded classes (B114); confined companion (B117).

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
- **Established:** blocks S9, S11; cutoff-uniform mass ⇔ RH; AAL ⇔ tail transport; transport on right discs; crossing discs force power growth; partial returns transport a zero or create a deep small value; short-arc Euler approximation needs prime mass `≳log|τ|`; returns at zeros tail-bad; near-full tail events positive density; forced-vanishing precision cap [L].
- **(a)** A37.
- **(b)** Uniform target mass (B72); exact tail events at every right zero (B83, B89); tail law at the Kronecker scale (B96); freezing beyond the precision cap (B121); decay (B82).

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
- **Established [L/K]:** full-family receivers; depth corridors; two-lobe bound; cut crystal; sharp location; local pair cost; explicit Hausdorff shifts; critical threshold identities (S1).
- **(a)** A9.
- **(b)** Complementary-window sign, remaining-depth control (B6, B12, B101); all-height column (B46).

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

### ACS — Castelnuovo–Severi
- **Path:** source energy → all-aperture Bézout → RH; or Hasse–Weil for smoothed Frobenius graphs → RH.
- **Established [L/K]:** blocks S10, S14; source cone and RR; Bézout ⇔ RH; primitive `h¹` coercive for `a≤181/500`; Kloosterman purity; reciprocal quadric counts; Young projections at rank `≤4`; Toeplitz minors `≤200`; typical-height sign with Gaussian tails; frequency-packet average; degree-one Selberg classification; count law of every hyperelliptic curve; RH ⇔ bounded `c_B(log n)` with any constant ⇔ Hasse–Weil at the squares ⇔ at prime pairs ⇔ binary plane counts; crude bound `Kn^σ` at the integers ⇔ width `≤σ`; prime planes give width `≤1/12` [S].
- **(a)** A28, A41, A48, A49, A51.
- **(b)** Source-energy sign (B40, B1); count or Rosati producer over ℤ (B78, B87); damping presentation (B88); global trace (B85); mixed Young shapes (B86); prime gaps at the critical exponent (B119); B65; B28.

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
| IWT | towers, level sums, window theorem, rank barrier, Hasse–Weil principle at infinite rank, curve TFAE, Wolff towers, towers of ζ, crude step as Toeplitz count, continuous-level lag = zero-free region, linear six-way TFAE, two-scale `cosh` models, precision cost of forced vanishing, collision size of prime mean values | A47, A49 | B110, B111, B116, ZAL, B97, B121 |
| ZCG (AbscissaLaws) | split, transport, two-scale theorem, linear hierarchy with separating configurations, quantifier collapse, shift non-invariance, finite-rank Chebyshev exponent, heat-family finite-stratum law | A50 | B13, B83, B111 |
| SOSZ | zonotope, two half-products, point count, archimedean Frobenius as `ℍ³` Green function, damped Frobenius PSD, infinite rank and plastic sign [S], atomic genus `N log N` on blocks and on all degrees, integer/square/prime-pair Hasse–Weil = RH, crude bound = width, plane counts, prime planes width `≤1/12` [S] | A48, A49, A51 | B87, B88, B118′, B119 |
| RIAC | completed prime boundary, prime-star and torsion compensation, prime-vertex dynamics, exits as bouquets, signed localization `Σ index=1−M(N)`, resultant counts, thickened intersections, rational Abel counts and discriminant height, Frobenius orbit counts `q^{|I|}`, finite-field orientation cover | A46 | B106, B88, B120 |
| CTH | count law at every genus, every hyperelliptic curve, Born rules, boundary algebra, linear counts degenerate, Hecke conservation, second place, Farey reading, thermalization, sharp shells, modular conjugation ≠ partner involution, partner standard-form trichotomy, half-sided inclusions excluded, `Q` not integer-valued | A41 | B87, B95, B113, B114, B117 |
| APD | Hamburger rigidity, FE-defect isolation, one-offs of every positive class, firewall, positive two-prime annihilators with multiplicity, harmonic-packet, left-growth, Chebyshev, hyperbolic, fixed-height and divisor costs, coefficient oscillation of annihilator inverses, relocation, Hecke state PD iff `s≥½` | none | B80, B84, B103 |
| AHD / CACT | threshold identities `R_c=R_polar≤R_prim=R_high=W`, charged compactness, aperture exchange, top-window non-escape, conductor resolution, adaptive head = `|ζ(½+ib)|²` | A9, A13 | B6, B8, B101, B104 |
| AIF | inner field, Szegő infimum, rigidity, Carleson measure, dilation quotient, causal certificate, forward map, restoring bound, `Ψ`-boundedness ⇔ RH, Selberg depth `O(T)`, Bohr profiles, insertion cone, columns, local onset field | none | B2, B57, B66, B82 |
| AAD | producers, peak law, half scale, three-quarter floor, compensated producer, quarter rate under RH, parity-neutral rate, rate = Mertens scale, Frobenius = factorial stencil, transport, slow returns right of the line | A30 | B15, B55, B89 |
| RAC | cut identity and kernel, unique fake, carry, ledger hierarchy, twin at every degree, parity exponent, exact parity identity, exchange law, bounded count with a new zero, maximal angle, extremal-law model, rotated relations | none | B67, B91, B92, B93 |
| TAPO | first return and brackets, precision law, heavy returns, conditional moments, resonator mean, arithmetic mean values, recurrence dichotomy, tail of a return, AAL as tail transport, near-full tail events of positive density, partial returns, short-arc prime mass, Euler coordinates | A24, A37 | B89, B96, B97, B100 |
| SPAL | shifted-product rigidity, collision cells, smooth × prime collision classes, count-distance rigidity, positive near-count model | none | B98, B103 |
| PTT | Bohr isometry, boxes, savings, rounded orbit, discrepancy, mixing time, hull with natural boundary, Ξ-current lift, certificates | A24 | B46, B100 |
| ASH | graph black holes, Krein law, Lax–Phillips rank two, one clock, KMS, count law at genus one, genus-two graph; ModularBootstrap: Narain partition, central orders, moment jets, VK remainder, `¾` ⇒ RH, ceiling `¾` | none | B68, B71, B87 |
| BHR | modular wave, metric, AdS₄ quotient, pulse regularity, ringdown = strip, horocycle Mellin formula and Zagier converse, Lax–Phillips semigroup, odd cavity, Maass cusp forms, Weyl order, Rankin–Selberg continuation and FE, Rankin bound, eigenform RS Euler product, cusp-energy rates | A26, A43 | B71, B109 |
| RIT | Mayer scattering, Krein square, Hecke dispersion, Hecke algebra Poisson on resonant states | none | B68, B70 |
| ACP | Mertens energy residues, positive Hecke annihilators, reflected-pair decay boundary, prime-pair source | none | B68 |
| SEL / Primon | degree-one classification, Euler rigidity; primon thermal Euler factors, Kesten–McKay densities | none | B80 |
| MMD | Möbius over `ℤ[ω]` as cubic Gauss coefficient, fixed ray phase, frozen dual phase, cubic Eisenstein series, nonzero residue, Fredholm pencil on the cubic quotient, continued Fourier modes | A33 | B94 |
| AE, KPA | polar calculus, Tate law, naive heights, five currencies, torsion intersection, Stepanov over ℤ | none | B87, B88 |
| HHAC | isolated-prime rigidity, fixed-point obstruction, core Euler characteristic, core bouquet, weighted torsion operators | none | B88, B106 |
| ESG | prime-height filtration, barcode, `s`-independence, prime-weighted homology, two-prime block quotients | none | B106 |
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
| Σ sign on every window (`a*(ζ)=⊤`) | RW, EWU, OWU, ACT, CHMD, SZ, RN, ACS (source branch), AIP, SRT, SC, LI, TT (odd), HF, and the critical-curve branches of HF, SRT, AIP (window + polar payment) |
| Σ continuation at small time and the theta head at the critical zeros | ZCG (heat branch), PTR, LA, GTA, XN, HCF, PA, TH |
| Π square-root precision and long moments | WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| Π crude bound at every integer degree (Frobenius graphs) | ACS (graph branch) |
| Γ reflection and selection | PM, BAG, SEC, CDC, PCS |
| Missing source landing | APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF |
| Missing count / diagonal of the damping presentation, transversal | ACS, HF, PM, RW through windows |
| Two-scale Euler-product-and-FE input for B13, `ZAL⇒RH` and AAL, transversal | BAG, JAS shell, SC undamped, WL thick runs, ZCG one-off, linear and tower branches, RW polar ground energy |
| Dark range (Kronecker scale), transversal | every route at all heights; BAG and ZCG one-off branches; TH certificates; WD near-unit moments |
| Width axis (horizon observables), transversal | PM (horocycle, Farey, Lax–Phillips, Narain, cusp energy), MC (Farey), ACS (prime planes), every VK-scale saving |
