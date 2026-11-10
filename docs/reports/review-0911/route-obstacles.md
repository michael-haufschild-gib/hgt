# Route obstacles — status quo

Scope: the 38 live route formulations, the 9 route candidates and the supporting programmes. For each route: the path, what is established, the obstacles that are **(a) just work**, and the obstacles that are **(b) open mathematics nobody has a solution to**.

**Corpus checkpoint:** commit `43e39a9cec` (2026-11-09). Working log: `logs/review-0911-statusquo-research-3.md`. Companions: [obstacles-summary.md](obstacles-summary.md) (A/B lists, ideation), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ), [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem).

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means an independent source mechanism or landing is missing. Formulations are not independent mechanisms: HJ is PA, BSH is CDC, FEL's BSY criterion belongs to CTF. A criterion, a source construction, a quotient equality or a scalar grade does not discharge an arithmetic sign or vanishing.

**Evidence.** `[L]` Lean source, integrated. `[S]` Lean source unfinished or unintegrated. `[K]` Lean with transitive axiom audit. `[D]` deduction, not a Lean theorem. `[N]` numerical, uncertified. `[C]` classical literature, not formalized.

**Strength.** RH; ≥qRH (zero-free half-plane, Lindelöf or ZAL); AAL (implies the asymptotic abscissa law); sub (below quasi-RH and below AAL); method; producer; indep.

**Labels.** `A*` just-work items and `B*` open problems are listed in full in [obstacles-summary.md](obstacles-summary.md). An A item is known mathematics, finite computation, effectivization, integration or assembly of proved pieces; `(unverified)` marks A items whose difficulty is not established. Wall labels Σ, Π, Γ refer to [walls-ledger.md](walls-ledger.md).

**Notation.** Windows `[−a,a]`. `W` Weil's form, `w_n=Λ(n)n^{−1/2}`. `a*(ζ)` onset aperture; `ℋ(c)` Hardy interval; `λ*(c)` best cone margin. `L=artanh r`, `Ψ=½log H₁`, `q=Ψ′`. `N_d` non-real root count of `R_d(Ξ)`. `Θ=sup Re ρ`, `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`. **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **Landing** ZAL ⇒ finitely many off-line zeros; **DH** ¬AAL ⇒ ZAL; **LinAt C** `Θ−½≤C(Θ∞−½)`. `R=c⁸/log N`; `R_c`, `R_polar`, `R_halfline`, `R_prim`, `R_high` the whole-space, polar-payment, half-line, pole-orthogonal and high-conductor critical thresholds; `W=⨅_A windowThreshold(A)`. `E_y` Euler head, `ζM_y` Euler tail. `R(y,η)` first return of the primes `≤y` at precision `η`. A **Weil tower** at base `ℓ` samples the lag `Φ(νℓ)`; a set of levels is **thick** if it contains arbitrarily long runs arbitrarily far out. `primeDeviation(X)=(X−ψ(X))+X(Σ_{n≤X}Λ(n)/n−log X+γ)+O(1)`, `Φ(L)=e^{−L/2}primeDeviation(e^L)`. `Q(a)` Weil's form on integer probes. `c_B` the orbit correlation of the cubic spline `B`, `Re S=c_B`, `Re W(B±τ_vB)=2c_B(0)±2c_B(v)`; `Γ_n` the smoothed Frobenius graph of degree `n`; `P(d)`, `A(d)` the smoothed prime count in the window of `d` and its archimedean-plus-pole prediction, `c_B(log d)=A(d)−P(d)`. A **`√T` window** at the primes is `{p: |log p−T|≤r√T}`. `G_s(d)=e^{−(s−1)d}/(4π sinh d)` the Green function of `Δ−s(2−s)` on `ℍ³`; `G^{T_p}_s` the Green function of the Bruhat–Tits tree of `PGL₂(ℚ_p)`. A **seed** is a continuous bounded modular function decaying in the cusp; `Λ_F(s)=∫_𝒟F·E*(s−½)`. `F_n=Π_{p|n}(X²+p)`; the **orientation cover over ℤ** is the real locus of `y²=disc F_n`. `χ_x` a unimodular multiplicative twist (point of the gauge torus), `T_x(u)` its window trace. `Δ_g` the Gram-coupled locking defect.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ `c_B(log p)≥−K` at every prime ⇔ `c_B(log p)≤K` ⇔ `P(p)≤A(p)+K` ⇔ `Re W(B±τ_{log p}B)` bounded below at every prime; width `≤a` ⇔ the same with `Kp^a` | [L] | Σ (Weil's sign), Π (a prime count) and the curve proof (Stepanov's bound) are one inequality at the prime degrees: the smoothed PNT error sampled at the primes |
| RH ⇔ `\|c_B(log p)\|≤K` at every prime, by absolute convergence, continuation and the Laplace rate theorem | [L] | the decision step needs no sign |
| For every `r>0`: RH ⇔ the one-sided bound holds at the primes of arbitrarily late windows `\|log p−T\|≤r√T` | [L] | the minimal face is local in scale: a configuration-free decisive sample of density zero along any sparse sequence of scales |
| Positive deletion: three-point probability averages annihilate reflected quartets with additive Gaussian cost; a late tail keeps one chosen mode; a finite spectrum oscillates with bounded gaps | [L] | decisiveness needs no attainment and no Dirichlet series; the window radius is set by the deletion cost (`√T` in general, `log²T` leakage for ζ) |
| Unconditionally `\|P(n)−A(n)\|≤C√n·exp(−(log n)^{3/5}/(10⁸log log n))` | [L] | the face sits between the VK saving and a constant |
| RH ⇔ ZAL ∧ B13 ∧ Landing; AAL ⇔ B13 ∧ Landing ∧ DH; no two atoms fail together | [L] | the exceptional coordinate has three atoms; a hypothetical failure of AAL lies in exactly one sector |
| Landing ⇔ eventual Hadamard positivity uniform up to the line ⇔ ZAL forces finite Krein–Langer index ⇔ ZAL forces bounded heat counts (eleven forms) | [L] | landing is the gate between the ZAL receivers and the finite-stratum receivers |
| FE models of exponential type and positive integer-norm Euler products realize ZAL with infinitely many off-line zeros | [L] | landing needs the FE and the Euler product together |
| Classical Deuring–Heilbronn holds for real zeros of quadratic `L(s,χ)`; ζ has no Siegel regime; graded repulsion fails on integer-norm Euler products | [L] | DH for ζ is AAL on `¬ZAL` worlds and needs the FE |
| Under ¬AAL damping filters read the exceptional divisor at rate `a(β−σ)/2−π/4−dκ`; the Euler series bounds them only above abscissa `1` | [L] | the exceptional-current route needs an inequality that the explicit formula does not supply |
| RH ⇔ even tensor-power moments uniform in `k` ⇔ `A_k=o(k)`; every constituent of `M^{⊗m}` is a Tate twist | [L] | Deligne's argument runs over ℤ; the uniformity is the content |
| Gauge family: big monodromy, pure Gaussian generic fibre, ζ's vertical family equidistributed; ζ is the jump fibre; trace constants do not specialize to it; exact monodromy transfers only the trivial bound; near-ζ deformations keep the zeros | [L] | Deligne's family step does not run through twists; a family with a jump at ζ equal to the pole alone is missing |
| Haar-a.e. Euler products are zero-free right of the line; off-line zeros of ζ sit on density-zero sets of heights | [L]/[D] | in-law statements are blind to every atom of RH |
| Off the diagonal Weil's kernel = pole − `2πG_{1/2}` on the degree geodesic − `log p((p−1)/√p)G^{T_p}_{1/2}` on the `p`-ladders | [L] | the off-diagonal is an adelic Green pairing at every place's tempered edge; the sign sits in the diagonal |
| Ordered Gram coupling gives finite locked limits `Weil(f)+Δ_g` on every packet; a discrete adelic quotient by the rational split torus carries the degree points; the prime unit cannot carry scalar descent | [L] | the diagonal is the sign of `Weil(f)` against a transformed prime mismatch and discriminant; a Green/Robin realization on the quotient is open |
| RH ⇔ `Q` on integer probes is the Tate limit of an `ℕ`-count, needed on one ray `Γ_1+Γ_p` per prime; `Q` is not integer-valued | [L] | a count must be a genuine limit |
| One cuspidal cavity function of Hecke eigenforms sees every resonance; RH ⇔ its energy rings down at `y^{¾−ε}`; RH ⇔ every reflection Krein form PSD | [L] | the horizon has complete and sharp receivers; physics leaves one rate or one reflection sign |
| Integrality is exact only on the torsion; the exact Stepanov count over ℤ is Chebyshev's; the only exact symmetries of the prime orbit are integer dilations; no finitely generated ℤ-lattice of zero modes is stable under three prime Frobenii | [L] | exact methods over ℤ reach Chebyshev; any integral cohomology of the zeros has infinite rank |
| Returns of the primes: depth `t≥poly(1/δ)`; heavy subsets silent to `log t=(log y)^{3/2−ε}`; collective return counts proved beyond a depth floor that grows with the number of primes | [L] | breadth past VK is a depth floor uniform in `π(y)` |
| Near-unit mollifiers need length `exp(c log²T)`; long mean values are collision counts of order `X²` | [L] | the near-line wall is the dark range |
| The orientation cover over ℤ has centred count `M(N)`, weight `≥½`, weight `½` ⇔ RH | [L] | topology carries the Mertens level |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | primes pay the archimedean–polar deficit by sign | format exact on every window; size payment ends before half-width `21/40` |
| M2 Calibration | window cones, blind positivity, margin | cone pinned at `e^{−c/1104}`; cone points obey PNT `5/6` on the window's range; sign open |
| M3 Canonical flow | `L,q,Ψ` of the Weil chain | exact to contact; RH ⇔ `Ψ` locally bounded |
| M4 Reflection | Krein/Lewis positivity, Hecke dispersion, ringdown, Lax–Phillips, horocycles, cavity energies, Born rules, standard forms | complete and sharp cavity receivers; reflection Krein form PSD ⇔ RH; internal and half-sided realizations excluded; rates open |
| M5 Square-root cancellation | smoothed prime counts, long moments, Farey discrepancy | receivers closed; estimates open |
| M6 Continuation | heat, cosine, Jensen | typical heights closed; small time at all heights open; heat finiteness (Ki–Kim–Lee) does not pass to `t=0` |
| M7 Zero geometry | cameras, Blaschke factors, inner field | isolated zeros at rate 2; depth `O(T)`; clusters and `o(T)` open |
| M8 Recurrence and transport | zero transport, tail transport, partial returns, prime current in the finite-layer world, damping filters | AAL ⇔ transport; filters read the exceptional divisor; Euler bounds only above abscissa 1; transport open |
| M9 Production | integer stencils, integrality, Stepanov over ℤ | rate = Mertens level; exact Stepanov count = Chebyshev |
| M10 Count | nonnegative function with quadratic Tate limit | every hyperelliptic curve [L]; over ℤ one ray per prime; no count known |
| M11 Orbit at finite time | prime phases, first return, collective counts, linear forms in logarithms | depth bounded by Baker; breadth to VK; counts beyond the depth floor |
| M12 Critical compactness | Gårding, Γ-liminf, threshold law, pole channel, half-line ground states | closed: `R_c=R_polar=R_halfline≤W` |
| M13 Topology of the prime complex | homotopy, persistence, fixed points, singular indices, orientation cover | `s`-independent; `Σ index=1−M(N)`; cover weight `½` ⇔ RH |
| M14 Thermal averaging | primon gas | Euler factors at real points `>1` |
| M15 Infinite-rank elimination | Weil towers, exceptional rank, thick sets, linear dial, metric recurrence, infinite Turán | elimination proved; inputs (thick crude count, ZAL) open |
| M16 Intersection on half-products | 𝔽₁-zonotope, `ℙ¹_ℤ` torsion, `ℍ³` and tree fibres, Frobenius graphs, Gram coupling, adelic quotient | adelic Green formula off the diagonal; finite coupled limits; diagonal is the sign |
| M17 Prime-degree sampling | one- and two-sided bounds at gap sets, Bohr-dense sets, `√T` windows; Landau; tensor powers | RH at sparse local windows from one side or, sign-free, from both; AAL at sampling sets; estimate open |
| M18 FE rigidity | defective FEs, Poisson rigidity, Gaussian surgery | complete in the countable class; selects exact identities of ζ |
| M19 Exceptional-coordinate atoms | ZAL, B13, Landing, DH; Hadamard threshold; Krein index; classical Deuring–Heilbronn | RH = ZAL ∧ B13 ∧ Landing; each atom calibrated; all open for ζ |
| M20 Families and monodromy | gauge torus, vertical family, Künneth, isozeric deformations | generic purity free; ζ is the jump fibre; specialization missing |
| Amplifiers | Diophantine repulsion, integrality, isolation, Turán, positive annihilators | amplify a certificate, produce none |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve

Routes: HF, SRT, AIP, ACS (atomic), SC, CHMD (index). Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF.

Established [L]:
- Full tilted-spline matrix PD for `1≤c≤(log N)^α`, `α<1/8`, and through `c≤2K₀(log N)^{1/8}` with complete Schur payment [K]; every compact C² profile: energy `≥ae^{−Bc}‖x‖²` on conductors `≤N^θ`, `θ<¼`, `c≤b log log N`; logarithmic profile positive to `ε₀L(log L)²`; the fixed Beurling profile at `c_N=2L(log L)²`, `L=log log N`, has sign ⇔ RH.
- **Threshold identities.** `R_c=R_PSD=R_polar=R_halfline≤R_prim=R_high=W`; every threshold `=⊤` ⇔ onset `=⊤` ⇔ RH; `R_c≥c₁e^{c₂a}`, `R_high≥c₀e^{6a}` for `0≤a≤a*(ζ)`.
- **Half-line ground states.** Window-level polar payment ⇔ strict positivity of the Gamma-truncated charged critical form on half-line profiles; under ¬RH strong compactness produces a unit half-line ground state at finite `W`; each ground state bounds `R_polar` by a reciprocal shift in its polar pairing; finite `R_polar=W` forces polar orthogonality.
- **Multipliers.** The depleted kernel `m(z)=4/(¼−z²)−12/(64−z²)` admits no finite or countable square-bounded dominating family of holomorphic multipliers on the off-line strip.
- **Charged compactness and conductor resolution** closed: physical tearing Schur ratio `→4/13`; conductor-adapted splitting decouples; every low-packet cross term except the polar collar pairing costs an arbitrarily small packet diagonal.

Structure [D]: the critical curve carries no sub-RH content beyond one inequality, `R_polar=W` at finite thresholds, and one statement about half-line ground states.

| | Obstacle | Strength |
|---|---|---|
| A9 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | — |
| A13 | Near-gcd charges and periods beyond `M₀(N)` (unverified) | — |
| B6 | Full-space sign eventually at every `K`; every critical threshold `=⊤` | RH |
| B8 | Head thresholds for every `d` | RH |
| B101 | Low-packet polar payment at every ratio on growing windows | RH |
| B104 | Polar payment at every `R<W`; at finite `W`, whether a half-line ground state can be polar-orthogonal | method |
| B123 | Correlated arithmetic pairings that dominate the depleted kernel | method |

### S2. Window tower and canonical flow

Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT (odd), HF, ACS, SRT, SZ. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF.

Established [L]: precontact de Branges chain, canonical system with `H₁H₂=1`; `L′=q−sinh 2L`; traces, `r`, `Ψ` absolutely continuous; `q_y→q` in `L¹`; restoring bound `|L(x)|≤artanh e^{−2(x−c)}+2osc Ψ`; RH ⇔ `Ψ` locally bounded; soft prime kick; Born model; causal certificate; Szegő threshold; forward-map tangent; cone pinning, margin ceiling, bounded extremals; cone points carry local density `1+O(e^{−a})` and PNT `5/6` on `X≤e^{2c−3}`; datum region `⊆{β≤1}`; exact null blind test; floors `(1/20000)/2^k` through `a_k<0.3621`; Tate dimension one positive exactly through `log 5`; finite templates exactly below spread `27/5`.

| | Obstacle | Strength |
|---|---|---|
| A1–A3, A6 | Certified verification, numeric heights, first-window membership, cone widths | — |
| A16 | Numerical `r,m,q` [N] | — |
| B1 | Sign on every window | RH |
| B2 | Bounded oscillation of `Ψ` on every bounded aperture interval | RH |
| B3 | Variation of `r` free of `1/μ` | sub |
| B4 | Two-sector certificates; outer predictors; every echo in its Schur band | RH |
| B5 | Kick admission at every stage | RH |
| B16 | Decay law of `λ*(c)` | sub |
| B17 | Signed ground-state structure past `log ρ` | method |

### S3. Local onset plane

Routes: RW, ACS, SRT, ZCG, WD. Programmes: AIF, WVL, MZF, PTT, PL.

Established [L]: `Ω_ψ(a,X)` as a sum over zeros; on-line terms nonnegative; depth cost `≤(16/9)δ²a⁴‖ψ‖²`; RH ⇔ `Ω≥0`; typical-height sign at `A=δlog T/(64M²)` with Gaussian-tailed bad heights; Weil's form is the average of its frequency packets.

| | Obstacle | Strength |
|---|---|---|
| B28 | Local Weil positivity at fixed `λ>0` on density-one heights | sub |
| B46 | Proportional saving at length `(log X)^{2K}`, all heights | sub |

### S4. Continuation and nodal geometry

Routes: ZCG, LA, PTR, HCF, PA, GTA, XN, WD. Programmes: NGF, FFP, ADO, AES, RHTower heat.

Established [L]: collision criterion; horizon `(6600/9991+ε)/log X`; density-one `Λ_Xlog X→0`; crystal and reality at the critical scale; sharp depth law for isolated simple zeros; `N_d` law, inner-root reality, `N_d≤300√(d log d)`; cosine Laguerre above VK; nonrepelling values of dimension zero. **Heat family:** each `H_t`, `t>0`, has finitely many non-real zeros (Ki–Kim–Lee in Lean) and asymptotic off-axis depth `0`; off-line zeros of ζ make the collision mass diverge as `t→0⁺`; a finite-stratum law valid on all `H_t` gives RH; linear AAL along the heat flow is RH; only `τ=0` has a Dirichlet series. **Heat divisor:** `N(t)(2t)^q≤2S_q`, `N(t)log(2t/a)≤2L_a`, sharp elapsed coefficient `2`, crowding dissipation, finite squared-depth mass ⇔ bounded heat energy, then `t·N(t)→0`.

| | Obstacle | Strength |
|---|---|---|
| A19, A20 | Heat horizon toward its method floor; Jensen rung (unverified) | — |
| A50 | Finite-stratum laws on the cosine family and the shifted Jensen family imply RH (unverified) | — |
| B24 | Collisions at arbitrarily small time, all heights | RH |
| B25 | Frequency `<1` at every collision | RH |
| B124 | Useful finite initial depth budgets and extinction near `t=0` | sub to RH |
| B27 | Runs of `k` simple critical zeros, every `k` | sub |
| B47 | Multiplicity `o(log X)` by a non-size input | sub |
| B22, B23 | Outer roots of `R_d(Ξ)`; `N_d` bounded | RH; ≥qRH |
| B92, B93 | Rotated relation with coefficients of the size of `Q`; contradiction beyond the extremal law | RH |

### S5. Near-line geometry and long moments

Routes: WD, CTF, MC, TG; census. Programmes: CDG, APR, MZF, AIF, IWT.

Established [L]: Selberg CLT; cameras, hyperbolic density theorem, `N(ρ)=exp(−ΣG)`; eight-way log-mean equivalence, Abel form ⇔ depth density `o(T)`; off-line first moment `≤(67/1000)V`, depth `O(T)`; necessary-length laws; an Euler mollifier with near-unit second moment uses every prime up to `≍log²T`; last-scale floor; Möbius zero condensation; Fejér long mean values are signed collision forms of exact order `X²`; corridor bad-window measure `O(T/log^ηT)`.

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

Routes: WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, LI, AIP. Programmes: ASRP, APR, AGT, AKLT, AE, AAD, RAC, MMD, SPAL, HWV, ArithmeticDefectRigidity.

Established [L]: band ⇔ classical criteria; integer lag; entry filters; length–precision law; gauge exponents `[Θ,1]`; twin quarter floor; Nair lattice; Stepanov over ℤ = integrality floor + Nair ceiling; producers `c=μ∗h`; rate `K^{−a}` ⇒ `Re ρ≤1−a`; all `a<½` ⇒ RH; RH gives `a<¼`; Frobenius over `𝔽_q[T]` = factorial stencil of rate 0; parity-neutral producers at every rate; cut kernel = zeros; finite-energy kernel mass annihilation ⇒ RH; exact parity identity pins `λ`; Farey discrepancy ⇔ RH; Möbius over `ℤ[ω]` a cubic Gauss coefficient with nonzero residue at `4/3`; residue energies of the damped Möbius form are bounded or equidistributed (`|E_qr−E/q|≤8√E+4`).

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
- Scattering: resonance ⇔ `ζ(2s)=0`; `Q=2Re[WH,WH]`; `D_s≤0`, zero iff `Re s=¼`; Hecke dispersion; Poisson-positive Hecke algebra on truncated resonant states for every `Re u<0`; positive `T₂,T₃` polynomials annihilate any finite resonance set.
- Horizon: modular horizon = quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)`; ringdown in the modes of zeros; the mirror-odd sector is a cavity of cusp forms.
- Seeds: a `*`-algebra containing the Maass cusp forms; response Mellin transform `Λ_F·2s(2s−1)/ξ(2s)` (positions fixed by the group); every seed rings down at its zero-free region; a rate `y^α` forces `Λ_F(s₀)=0` at every zero of `ξ(2s)` with `Re s₀>1−α`.
- Cavity receivers: pairs of Maass or Hecke eigenforms see every resonance; one cuspidal cavity function `g` of Hecke eigenforms sees every right resonance; RH ⇔ `|a_{|g|²}(y)−c|≤Cy^{¾−ε}`; RH ⇔ every two-mode energy rings down at `y^{¾−ε}`; one eigenform is blind exactly at halving pairs `ζ(ρ)=ζ(ρ/2)=0` and at Shimura zeros.
- Krein forms: the resonance Krein form has infinite index of both signs; the reflection Krein form is PSD on the line and has exactly one negative square at each off-line zero; RH ⇔ every reflection Krein form PSD; the dual side has no sign.
- Width axis: zero-free `Re ρ≤1−2δ` ⇔ pulse decay `e^{−(δ−ε)τ}` ⇔ horocycle rate `y^{½+δ−ε}` ⇔ smoothed Farey rate; RH ⇔ `y^{¾−ε}` ⇔ universal decay `e^{−t/4}`; sharp shells log-free `O(√y)`; one sharp shell at the RH rate ⇔ RH ∧ Möbius × circle-remainder cancellation.
- Cusp channel, Narain AdS₃ partition (remainder with exactly the VK saving; `¾` ⇒ RH; `>¾` impossible), graph black holes, Born rules, genus-two graph (FE for every `q`, all-level count law iff `q≤3`).
- Standard forms: internal partner unitaries are central and realize `Q` iff RH; vacuum-fixing partners and Borchers half-sided inclusions never carry `Q`.
- Archimedean place: `2πG_{1/2}=2πG_{3/2}+½φ_{1/2}` (Euclidean AdS₃ scalar of `m²=−¾`, quantizations `Δ=½` and `Δ=3/2`); the pole is `(3/2)φ_{3/2}+½φ_{1/2}`.

Structure [D]: wave dynamics, unitarity, Hecke, KMS, `C*`, internal modular conjugation and half-sided inclusions leave damping open. The receivers are complete and sharp; what remains is one rate or one reflection sign. A physical carrier must connect the horizon's resonances with the point spectrum of a GNS realization of `Q`.

| | Obstacle | Strength |
|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | — |
| B68 | Independent `D_s≥0`, nonnegative Krein flux, integer-probe sign, all-zero dispersion bound, or PSD of the reflection Krein forms | RH |
| B69 | Positive physical carrier | producer |
| B70 | Lower bound for `V_p` from the carrier | sub |
| B71 | Universal decay `e^{−t/4}`; horocycle, Farey, Narain or one-cavity-energy rate `y^{¾−ε}` | RH |
| B87 | A count with Tate limit `Q` | RH |
| B113 | Möbius × quarter-disc remainder `Σ_{d≤X}μ(d)E(X/d)=O(X^{½+ε})` | beyond RH |
| B114 | A realization of the partner involution outside the central, vacuum-fixing and Borchers classes | producer |
| B117 | A confined companion of the modular horizon | producer |
| B125 | Halving pairs: no zero `ρ` with `ζ(ρ/2)=0`, and nonvanishing of one Shimura integral at every `ρ/2` | indep. |

### S8. Index, support and the finite stratum

Routes: HKT, AKLT, SC, RIT, CWS through HF, ACS; LA; ZCG heat count. Established [L/K]: `κ(φ_c)=κ+1`; finite index ⇒ Lindelöf; `κ∈{0,∞}` under escape, mixing or decay; window index counts critical lengths; `sup_dN_d` = off-line multiplicity; `K_ζ^n` PD ⇔ RH; TFAE: `κ(K_ζ)<∞` ⇔ finite index on one two-prime lattice ⇔ finitely many off-line zeros ⇔ bounded non-real heat count ⇔ RH above some height ⇔ eventual slice positivity ⇔ central-gap budget ⇔ finite-dimensional odd bound states; in the stratum RH ⇔ one non-blind prime tower PD ⇔ one Weil tower Toeplitz positive ⇔ one tower bounded on a thick set. ZAL forcing any of these is the landing law (S9).

**Positive sign calibration [L].** For `Y≥1`, the completed Eisenstein constant term
`Λ(2s)Y^s+Λ(2s−1)Y^{1−s}` has no non-real zero off `Re s=½`.
`InfiniteRankPurityTheory.lineLaw` proves this without truncation: the pole-cleared
function has a Schur quotient and an index-one defect; conjugation forces every
exceptional zero to be real. `constantTerm_zero_subsingleton` permits at most one
zero right of the line. A proposed sign mechanism must recover this line law;
the calibration does not assert absence of real exceptional zeros.

| | Obstacle | Strength |
|---|---|---|
| B12 | Index ceiling uniform in resolution | ≥qRH |
| B13 | Finitely many off-line zeros ⇒ none | sub |
| B23 | `N_d` bounded | ≥qRH |

### S9. Exceptional coordinate: atoms, landing, Deuring–Heilbronn, transport, one-offs

Routes: BAG, JAS shell, SC undamped, WL thick runs, ACS sampling branch, ZCG one-off, linear and landing branches, RW polar ground energy, LA (finite support). Programmes: ZCG (AbscissaLaws), ELT, EFT, IWT, SOSZ, AKLT, AIF, APD, AAD, RAC, PTT, TAPO, SPAL, ACP.

Established [L]:
- **Atoms.** Purity ⇔ ZAL ∧ AAL; strict dial `Pure ⊊ AAL ⊊ LinAt C₁ ⊊ LinAt C₂ ⊊ (∃C LinAt) ⊊ B13`; `∃C LinAt ⇔ B13 ∧ Landing`; `AAL ⇔ B13 ∧ Landing ∧ DH`; `Pure ⇔ ZAL ∧ B13 ∧ Landing`; the atoms never fail in pairs; for ζ, RH ⇔ ZAL ∧ B13 ∧ Landing.
- **Landing.** Tail law, undecided below every height; eleven equivalent forms for ζ (bounded Hadamard threshold as `σ↓½`, finite Krein–Langer index under eventual Hadamard positivity, finite `{2,3}`-lattice index, the line above a height, bounded heat counts, slice positivity, central-gap budget, finite odd bound states under ZAL). A zero of depth `δ` is invisible to the exponential current at speeds `a<π/(2δ)`; under ZAL with infinitely many off-line zeros every speed loses infinitely many.
- **Calibrations.** FE models of exponential type with approaching off-line quartets violate landing; a positive integer-norm Euler product with linear counting and remainder depths `θ_n↓½` satisfies ZAL, B13 and DH and violates landing; cosh and two-scale cosh models; one reflection pair; harmonic-depth configurations; continuous Beurling systems; prime-square-corrected discrete and integer-norm one-offs continued across `Re s=½`; rational-prime one-offs; positive two-prime and Hecke annihilators; the heat family; positive theta sources after finite donor surgery.
- **Deuring–Heilbronn.** Extreme DH ⇔ (AAL ⇔ B13); integer-norm one-off: extreme DH without linear AAL; two-scale integer-norm product: linear AAL without asymptotic DH; graded repulsion refuted on positive integer-norm Euler products; classical Deuring–Heilbronn for real zeros of quadratic `L(s,χ)`, constant uniform in conductor, height and zeros; infinite power sums detect a maximal term; ζ has no Siegel regime (`(1−Re ρ₁)log(|Im ρ₁||Im ρ₂|)≥1/58`); AAL(ζ) ⇔ DH(`L_a`).
- **Free AAL and the two-scale law.** Recurrent configurations, exponential polynomials, curves, vertically periodic configurations, strip almost periodic functions and uniformly approximable Dirichlet series obey AAL; no property of the zeros above a height or below a fixed height decides B13, any linear law or AAL; landing is a tail law, decided by no property of the zeros below a fixed height.
- **AAL producers.** Not-attained top; bounded lag on a progression; Abel-density-zero lag excursions; subexponential polar ground energy; prime-window grid; log-dense integer lag; JAS dressed, typical and shell positivity; bounded towers; one bounded cone; weak recurrence; slow aligned returns on right discs; thick lag or thick prime deviation `O(X^{½+a})` ∀`a>0`; positive count of one tower; one-sided bound on a sampling set or a Bohr-dense set; positive-measure lag recurrence; uniform tensor moments at a residue class.
- **Finite-layer world (¬AAL).** Isolated top, finite oscillation of `ψ`, syndetic lag excursions, raw prime current → `−ζ′/ζ` on a high strip, head-conditioned rough variance, joint prime-phase returns; corrected Gaussian current at exponential damping = top mode × finite wave with sharp recurrent envelope; one positive top ordinate ⇒ divergence; local height filters and prime-only damping filters read each top mode with the infinite remainder retained; at exponentially narrow damping the selected top mode grows when `dκ<a(β−σ)/2−π/4`; the Euler-region bound gives decay only when `dκ>a(1−σ)/2`.
- **Transport and tail.** AAL ⇔ zero transport ⇔ tail transport; discs crossing `Re s=½` force power growth; escaping translates bounded on a domain meeting `Re s>1` stay right of `½`; partial returns transport a zero or force a deep small value; zeros of ζ are zeros of every Euler tail; near-full tail cancellation has positive density at every strip point; heavy returns are rare (collective counts).

Structure [D]: the exceptional coordinate has three atoms on the RH path (ZAL, B13, Landing) and one off it (DH). Each atom needs the FE and the Euler product jointly (calibrations; ZAL also the coefficient size); B13 and DH couple both scales (two-scale law) while landing is a tail law; every atom is invisible in law (random Euler products are zero-free right of `½`). The exact identities of the finite-layer world are consistent: the filtered current is the filtered zero sum, so a contradiction needs an inequality not implied by the explicit formula.

| | Obstacle | Strength |
|---|---|---|
| A37 | Resonator mean of `\|ζ\|²` with resonators growing below the Kronecker scale (unverified) | — |
| A47 | Explicit window constants of the tower theorems for one top quartet (unverified) | — |
| A67 | Dominant-ordinate divergence: the corrected current diverges for every top layer whose largest Gamma weight exceeds the sum of the others (Kronecker) [D] | — |
| A68 | A landing calibration with ζ's Gamma factor and Riemann–von Mangoldt counting (unverified) | — |
| B13 | Finite stratum | sub |
| B83 | AAL | sub |
| B89 | A bounded aligned return at each right zero on a right disc | sub |
| B96 | Conditional law of the Euler tail at the Kronecker scale | sub |
| B110 | Thick crude count | AAL |
| B111 | `ZAL⇒RH` = B13 ∧ Landing | sub |
| B112 | A mechanism converting the FE into vertical transport | sub |
| B116 | Linear AAL at one fixed slope | sub |
| B126 | A one-sided crude bound on one sampling set of primes | AAL |
| B127 | Positive-measure lag recurrence at every rate | AAL |
| B128 | Replication in the finite-layer world | sub |
| B134 | An upper bound for the corrected exceptional current at one supercritical speed that is not a consequence of the explicit formula | sub |
| B138 | Landing law for ζ | sub |
| B141 | Deuring–Heilbronn for ζ: `¬ZAL ⇒ AAL` | sub |
| B72 | Cutoff-uniform target mass | RH |
| B82 | Inner-field decay | ≥qRH |

### S10. Count and effectivity

Routes: ACS, HF, PM integer probes; RW through window naive heights. Programmes: AE, CWS, LST, KPA, ASH, CTH, RIT, SOSZ, RIAC, HHAC, HTG.

Established [L]: polar surface calculus; Tate principle both ways; theta `h⁰` with exact RR; Künneth `h¹` split; source cone and all-aperture RR; Bézout ⇔ RH. Curves: integral Castelnuovo–Severi defect is the Tate limit of a count iff unitary; every hyperelliptic curve has the count law. Over ℤ: RH ⇔ `Q` is the Tate limit of an `ℕ`-count; `Q` is not integer-valued and no integral kernel reproduces it; linear counts degenerate; RH ⇔ every effective prime class `Γ_1+Γ_p` carries an `ℕ`-count along its ray with Tate limit `2c_B(0)+2c_B(log p)` ⇔ the prime planes are copositive ⇔ the same on any power-saving gap set ⇔ ZAL ∧ the same on runs of integers. Arithmetic counts defined before the form exist (different quotients, gluing quotient `ℤ/(1−M(N))`, Gaussian section heights, resultant rings, radial cyclotomic counts); none has Tate limit `δ_p(1,1)`. λ-ring effectivity: one Hecke or Adams correspondence replaces the ample axiom, and every stable Riemann–Roch cone forces the zero defect floor.

| | Obstacle | Strength |
|---|---|---|
| A28 | Reciprocal-quadric traces = vanishing-cycle Frobenius traces (unverified) | — |
| A41 | Count law for every curve over `𝔽_q` (Bombieri–Stepanov), first case plane quartics [C] | — |
| A48 | Hasse–Weil test of smoothed Frobenius pairs at verified scales | — |
| B87 | A count on the rays `Γ_1+Γ_p`, defined without `Q`, with Tate limit `2c_B(0)+2c_B(log p)` | RH |
| B88 | A counterterm-free presentation of the diagonal; the sign of the Gram defect | RH |
| B65 | Genus upper law; logarithmic Serre duality; first Epstein real zero | indep. to sub |

### S11. Prime orbit at finite time

Routes: BAG, TH, SRT, RW, ZCG carriers, every route at the all-height wall. Programmes: PTT, TAPO, TTPO, CDGeo, SPAL, IWT, ALST.

Established [L]: windows of length `exp(10y√(log y·log log y/δ))` enter every `δ`-box; savings `t^{−δ}` at length `L^A`; first return bracketed at every precision; proportional saving ⇔ no early heavy return; conditional Gaussian tail below the Kronecker scale; returns freeze smooth Dirichlet polynomials; Rouché copies cost `J≤e²r log N+log(1/δ)`; explicit linear forms in `k` logarithms; depth law `t≥poly(1/δ)`; return–form duality and the breadth cap at the Kronecker scale (rounded systems are function fields); reciprocity of returns with the zeros near the height; return bounds are label statements shared by `ζ(s−h)`; heavy subsets silent while `log t≤(log y)^{3/2−ε}`; a strip of depth `h` gives `log t≥c·y^{1/2−h}`; absolute large values force heavy returns at dilated heights; collective rank depth; **collective counts**: returns of `k` prime logarithms at precision `1/(2N)` have measure `≤(5π/2)4^k max(T/2,Δ^{−1})/N^{k−r+1}`, weighted heavy returns `≤(5π/2)max(T/2,δ^{−1})e^{−W/(8M)}` with hereditary rank floors and Hall-matched coordinates.

| | Obstacle | Strength |
|---|---|---|
| A24, A37 | Certified scans and brackets; growing resonators (unverified) | — |
| B46 | Proportional saving at length `(log X)^{2K}`, all heights | sub |
| B97 | Constant-precision first return of heavy subsets past the VK rung (top rung: Littlewood-type bound for `ζ(1+it)`) | sub |
| B137 | A collective depth floor uniform in `π(y)`: return counts valid from heights `≤exp(y^c)` | sub |
| B100 | A saving for `t log n` on moving block families past Vinogradov's degree | sub |
| B121 | Freezing control beyond the precision cap | sub |
| B15 | Past VK | sub |
| B20 | Oscillation of the actual amplitude with the height | RH |

### S12. Topology of the prime complex

Routes: MC (nerve, Redheffer), HF and ACS through the coprime stratum. Programmes: HWV, ADT, ESG, HHAC, RIAC, HAT.

Established [L]: `det R_N=M(N)=−χ̃` of the prime-star nerve; squarefree prime complex ≃ wedge of spheres; RH ⇔ `χ̃=O(N^{½+δ})`; persistence classified and `s`-independent; prime-vertex local indices sum to `1−M(N)` and are unbounded below; the connected core is a bouquet with augmented Euler characteristic `M(N)+#primes(N/2,N]`. **Orientation cover over ℤ:** real points of `y²=disc F_n` number `1+μ(n)`; centred count `M(N)=Ω±(√N)`; weight `≥½`, weight `½` ⇔ RH. Over `𝔽_q[T]` the factor-trace cover has exactly `qⁿ` points.

| | Obstacle | Strength |
|---|---|---|
| A46 | Local singular indices beyond the cubic cutoff (unverified) | — |
| B10 | Top coprime stratum | RH |
| B106 | A natural self-map or correspondence on the orientation cover with bounded local indices whose Lefschetz numbers are the centred counts | RH (≥qRH at `θ<1`) |

### S13. Infinite-rank elimination

Routes: WL (thick runs), ZCG (tower form), ACS (thick curve counts), BAG, JAS. Programme: IWT.

Established [L]: Weil towers and level sums; exceptional-rank window theorem; rank barrier; infinite-rank Hasse–Weil principle; ZAL ⇔ well-foundedness; Wolff towers show well-foundedness is needed; positive count of one tower ⇒ AAL; RH ⇔ ZAL ∧ (thick bounded lag / positive count of a tower / thick `O(X^{½})` prime deviation); linear six-way TFAE; continuous-level lag bound = zero-free half-plane; metric recurrence of bases (positive measure or dimension ⇒ AAL; actual residual recurrence has dimension 0); infinite power sums detect a maximal term.

| | Obstacle | Strength |
|---|---|---|
| A47 | Explicit rung-`k=1` window constants (unverified) | — |
| B110 | Thick crude count for ζ | AAL |
| B127 | Positive-measure recurrence of the Weil lag at every rate | AAL |
| — | ZAL | ≥qRH |

### S14. Intersection theory on half-products and the adelic carrier

Routes: ACS, HF, PM count branch. Programmes: SOSZ, HAT, AE, RIAC, HHAC, CTH.

Established [L]: zonotope defect with exact count Tate limit; off-diagonal Weil = `C_∞` + Abel limit of positive twisted torsion energy; **archimedean Frobenius = Green function of `ℍ³`**, `archKernel(m,n)/√(mn)=2πG_{1/2}(d)`; **finite places are trees**, `log p((p−1)/√p)G^{T_p}_{1/2}` on `p`-ladders at the Ramanujan point; **adelic Green formula**; spherical compensation `C_∞=(3/2)φ_{3/2}−2πG_{3/2}` with sign change at the plastic ratio; no twisted carrier with convergent Poincaré series at `½`, no compact or (given a cusp expansion) finite-volume embedding carries the torsion; locked atomic dampings converge on the diagonal only to the discriminant; scalar locking on smoothed packets converges iff discrete mass = `L²` mass; **ordered Gram coupling** gives finite locked limits `Weil(f)+Δ_g` on every compact C² packet, overlaps included; the **prime unit** identifies `p^k` with `p^{k+2}` and admits no invariant scalar or unitary Frobenius kernel; two positive parity fibres over unitary characters recover every tree Green entry; the **discrete adelic quotient** by the rational split torus in `SL₂(ℂ)×Π'_pSL₂(ℚ_p)` carries the square degrees, and after Weyl conjugation the original degree points, as distinct points. Smoothed graphs: RH ⇔ one side of Hasse–Weil at the primes ⇔ `c_B` is a counterterm-free PSD limit; neither smoothed channel alone is one.

Structure [D]: every place carries the Green function of a rank-one symmetric space (real or `p`-adic) at its tempered edge. Local Robin data give the discriminant (atoms) or the Gram defect (packets): the diagonal is not local. The quotient constructed is the split-torus (adele-class) quotient; a Green/Robin realization on it would place Weil's form in an adelic potential theory, and its sign would remain the open input.

| | Obstacle | Strength |
|---|---|---|
| A54 | Instantiate the cusp expansion with nonzero Wronskian for Bianchi resolvents (closes finite-volume carriers) | — |
| A69 | Full-degree adelic configuration (non-square degrees) on the discrete quotient (unverified) | — |
| A70 | Torus-periodized local Green functions at the degree points of the quotient compared with the adelic Green formula (unverified) | — |
| B87, B88 | Count; sign of the Gram defect / counterterm-free diagonal | RH |
| B133 | Green/Robin realization of Weil's full kernel, diagonal included, on the adelic quotient | producer |

### S15. Functional-equation rigidity

Routes: BAG, ZCG, SC/JAS, ACS (source identification), PM. Programmes: EFT, ExactEventTheory, APD, SEL.

Established [L]: countable Beurling systems with theta FE up to a measurable polynomially bounded `L¹` or `L²` defect are the rational primes with zero defect; positive measures with gap `(−1,1)∖{0}` are tent-self-dual iff Dirac combs; local Gaussian defects determine causal measures; atomic Euler corrections cannot repair Gaussian surgery; normalized height reflection `O(t^{−¼})`; whole-quadrant boundedness impossible.

| | Obstacle | Strength |
|---|---|---|
| A55 | FE rigidity for continuous Beurling systems with integrable defect (unverified) | — |
| B112 | FE → vertical transport | sub |

### S16. Lefschetz–Stepanov over ℤ

Routes: ACS (Stepanov branch), BAG, WL. Programmes: ALST, AHA, EAHT, AKLT.

Established [L]: the Adams operation is the Frobenius of integer auxiliaries (dilation on the orbit, Galois on the torsion); norm amplifier; exact order costs the degree; integrality cannot create zeros at returns; the closed-point Stepanov count is Chebyshev's; the fixed-point auxiliary `A_N` has log length `ψ(N)` and RH ⇔ `ψ(N)≤N+C√N log²N` (violated by the integer-norm one-off); polynomial Stepanov syzygies of order `<r` have image `J_q^r` and sharp cost `p_min^{qr}`; polynomial, integral, rational and real rational maps preserving a finite or the full prime orbit are Laurent Adams maps; scalar endomorphisms of a finite prime-log lattice are ℤ.

| | Obstacle | Strength |
|---|---|---|
| B121 | Freezing beyond the cap | sub |
| B48 | Deciding input at square-root precision | RH |

### S17. Prime-degree sampling and scale locality

Routes: ACS, SRT, WL, HF (one test per prime), ZCG (sampling), PM count door. Programmes: SOSZ, CDGeo.

Established [L]: one-sided or two-sided bounds at every power-saving gap set decide (gap method, Landau or the Laplace rate theorem); attainment is free on the primes, on power-saving gap sets, off power-thin or short-window-sparse exceptions, on two-prime difference lags, and on `√T` windows; decisive samples with arbitrarily large gaps and of zero convergence exponent exist; Bohr-dense sets decide attained tops (lower side) and attained tops with real zeros (upper side); sampling weights are Bohr-dense; density-zero exceptions, very smooth degrees and finitely many Frobenii admit unattained tops; one Frobenius aliases; δ-separated configurations are decided by windows of length `80/δ`; for ζ the deletion leakage at radius `C·log²T` is exponentially small; RH ⇔ uniform tensor moments; VK saving of the Stepanov bound.

| | Obstacle | Strength |
|---|---|---|
| A56 | Explicit rung for the prime two-bump tests (unverified) | — |
| A58 | Effective gap iteration constants (unverified) | — |
| A59 | Short-interval primes in a fixed residue class; the residue-class Stepanov bound becomes an RH criterion [C] | — |
| A64 | RH criterion on `log²T` prime windows for ζ from the log-square leakage and the prime-gap transfer (unverified) | — |
| A65 | Two-prime local criterion: lower bounds on two-prime difference lags in `√T` windows ⇔ RH [D] | — |
| B130 | The arithmetic Stepanov bound at the primes (one-sided or two-sided), on any decisive sample | RH |
| B140 | Bounded windows: is a lower bound on windows `[x_k,Cx_k]` along a sparse sequence of scales decisive for configurations with ζ's zero counting? | method |

### S18. Families and monodromy

Routes: ACS (tensor branch), HF, SC. Programmes: AWT, AK, SOSZ.

Established [L]: gauge torus of twists with big monodromy, uniform generic weights, Gaussian generic Frobenius; ζ's vertical family Haar-equidistributed at every fixed degree, with generic moments below the square-root scale; the trivial fibre carries the pole and is the jump; trace constants are closed and Haar-generic, yet blow up at ζ; Baire-generic exponent `½` against Haar-generic `0`; edge divisor of every fibre via pretentious distances, jump at ζ one simple pole; exact monodromy transfers only the trivial bound; summable Euler deformations keep the zeros; Künneth: every constituent of `M^{⊗m}` is a Tate twist; abscissa of the `2k`-th tensor series exactly `1+2kb`; RH ⇔ `A_k=o(k)`; invariant tensor weights and abstract monodromy are refuted as purity inputs (golden datum).

| | Obstacle | Strength |
|---|---|---|
| B85 | Arithmetic global trace on a family containing ζ | RH |
| B86 | Mixed Young projections at unbounded rank | RH |
| B142 | A family in which the jump at ζ is the pole alone and pole-subtracted trace constants specialize to ζ | producer |

## 3. Live routes

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy, one-sided `Φ`, a one-sided crude bound at the prime degrees (or at the primes of late `√T` windows), or ZAL plus a thick `O(√X)` prime deviation → RH.
- **Established [L/K]:** bounded endpoint energy ⇔ RH; integer lag ⇔ RH; `Ω±(√n)`; first-band abscissa `2Θ`; gauge exponents `[Θ,1]`; subtracted lag ⇔ ZAL; lag excursions of lower Abel density zero ⇒ AAL; one-sided Gaussian prime ceiling at every rational height ⇔ RH; RH ⇔ ZAL ∧ thick `O(X^{½})`; thick `O(X^{½+a})` ∀`a` ⇒ AAL; `ZetaLinAt C` ⇔ thick `O(X^{½+C(Θ∞−½)+ε})`; continuous-level bound `O(e^{aL})` ⇔ zero-free `Re>½+a`; RH ⇔ `P(p)≤A(p)+K` at every prime ⇔ the same at the primes of late `√T` windows; positive-measure lag recurrence ⇒ AAL; VK saving of `P−A`.
- **(a)** A30, A64, A65.
- **(b)** Bounded endpoint energy (B49); half-power at the trivial gauge (B50); deciding input (B48); the prime-window bound (B130); thick crude count (B110); `ZAL⇒RH` = B13 ∧ Landing (B111, B138); ZAL; past VK (B15).

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
- **Established [L/K]:** damped energy ⇔ RH; residue energies bounded or equidistributed; VK Hilbert energy; Möbius zeros condense on `Re s=Θ`; producer rates; parity exponent = zero abscissa; exact identity pins `λ`; twin quarter floor; Farey discrepancy ⇔ RH; `M(N)=−χ̃` of the nerve; `Σ_p` prime-vertex indices `=1−M(N)`; gluing quotient `ℤ/(1−M(N))`; orientation cover with centred count `M(N)`, weight `≥½`, `=½` ⇔ RH; Möbius over `ℤ[ω]` a cubic Gauss coefficient with nonzero residue at `4/3`.
- **(a)** Chowla [C] (A21); cubic residue Fourier coefficients (A33); prime-vertex indices past the cubic cutoff (A46).
- **(b)** Trivial-gauge cancellation or zero exclusion for `M_X` (B50); deciding input (B48); past VK (B15); theta identification and rational transfer of the cubic branch (B94); a bounded-index correspondence on the orientation cover (B106).

### TT — Theta tail / Wold
- **Path:** weighted endpoint energy bounded for each `0<t<½` → RH.
- **Established [L]:** Wold residual VK; `D_t+Q_t/2≥0`; boundedness ⇔ RH; uniform bound on a shrinking band.
- **(a)** None that moves the route.
- **(b)** `C_t` at every fixed `t` (B34); odd branch B4.

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted or sublinear root height → RH.
- **Established [L]:** block S4; infinitely many unshifted degrees ⇔ RH; inner roots real; `N_d≤300√(d log d)`; `sup_dN_d` = off-line multiplicity; heat-divisor budgets.
- **(a)** A20; A1; A50.
- **(b)** Outer roots (B22); `N_d` bounded (B23) gives finite support only: RH needs B13; under ZAL it needs landing (B138); finite initial depth budgets (B124).

### ZCG — Zero-configuration geometry / heat descent / abscissa laws
- **Path:** half-Gaussian source → no positive-time collision → RH; or ZAL ∧ B13 ∧ Landing → RH; tower, linear, sampling and transport branches for AAL.
- **Established [L]:** blocks S4, S5, S8, S9, S15, S17; abscissa laws of configurations (split, atoms, landing TFAE, transport, free classes, two-scale theorem, linear hierarchy with separating configurations, quantifier collapse, shift non-invariance, finite-rank Chebyshev exponent); heat: finite-stratum laws on `H_t` are RH, Ki–Kim–Lee finiteness does not land, only `τ=0` has a Dirichlet series; heat-divisor budgets; compact coordinates of tempered configurations and continuity of spline traces on compact charts; exceptional current, damping filters and contracting prime filters (ELT).
- **(a)** A19, A47, A50, A67, A68.
- **(b)** Small-time collisions (B24); frequency (B25); non-size frequency input (B47); runs (B27); FE-pair reality (B76); crowded zeros (B59); finite initial budgets (B124); AAL through transport, tower, sampling or rigid-world contradiction (B83, B89, B110, B112, B126, B128); independent current bound (B134); landing (B138); DH for ζ (B141); B13; fixed slope (B116); rotated relation (B92, B93).

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH.
- **Established [L]:** defect trace class; multiplicity `≤` trace norm; Gaussian passage criterion.
- **(a)** None that moves the route.
- **(b)** Trace norm `<1` on every rectangle or bounded Gaussian oscillation (B38).

### HF — Hodge / Hecke / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** blocks S1, S10, S14; source-work `≤2` ⇔ RH; `R_c=R_polar=R_halfline≤R_prim=R_high=W`, every threshold `=⊤` ⇔ RH; charged compactness closed; ¬RH gives a unit half-line ground state at finite `W`, polar-orthogonal if `R_polar=W`; no universal holomorphic multiplier dominates the depleted kernel; low packet at every ratio is RH; Gram-coupled finite limits on every packet; discrete adelic quotient carrying the degree points; λ-ring effectivity reduces to the defect floor [L].
- **(a)** A9, A13, A69, A70.
- **(b)** Full-space sign at every `K` (B6); low packet at every ratio (B101); polar payment below `W` and ground-state orthogonality (B104); correlated pairings (B123); head windows (B8); source-work ceiling (B41); top coprime stratum (B10); zero modes (B9); exact SOS (B11); Rosati and band poles (B78, B79); count and diagonal (B87, B88); Green/Robin realization (B133).

### CHMD — Causal hyperbolic–modular duality
- **Path:** one-sided bounded prime wave or odd Doob half-threshold bound → RH.
- **Established [L]:** wave and Doob receivers; normalized prime−pole decay; nonfirst source keeps `1−ε` of Gamma.
- **(a)** None that moves the route.
- **(b)** Either side of the unnormalized wave bound, or the complete odd sign (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel → RH.
- **Established [L unless marked]:** rank 14 at `0<a≤½`; rank `N` from verified height `41+6(N+2)log(N+2)`; VK collar; two-atom and chain signs; `S=Π_pT_pA`; locking = torus positivity; columns add; current `=2|Ξ|²Re ξ′/ξ`; adaptive head `M(b)=⌈|b|/2+B⌉` pays the omitted pair sum by half the first-atom floor; the adaptive partial sum is `ζ(½+ib)` up to `O(|b|^{−½})`, the head's leading term `|ζ(½+ib)|²`; no summable absolute pair majorant [S]; no compact core funds every Gamma direction [S].
- **(a)** Rank 15+ (A4); tail-failure certificate (A5); scans and brackets (A24); verified ranks (A1); Gamma-weighted transport to `M=M(b)` (A42).
- **(b)** Exact torus law for `S*` and `{2,3}` cross-chain positivity (B19); amplitude oscillation with the height (B20); all ranks (B21); signed adaptive head near critical zeros (B102); tail law at the Kronecker scale (B96).

### RN — Theta renewal
- **Path:** two-ended renewal → no joint nodes → RH.
- **Established [L]:** `det₂` gives `D`, not Ξ; Ξ zeros = joint nodes; energy comparison ⇔ RH.
- **(a)** None.
- **(b)** Joint-node exclusion or energy comparison (B36).

### WD — Ward / collision / long moments
- **Path:** source current, window energy or long moments → RH.
- **Established [L]:** block S5; one-window form; slope rigidity; long mean values are collision counts of order `X²/log X≲·≲X²log²X`; corridor bad-window measure `O(T/log^ηT)`.
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
- **Established:** block S7; integer-probe positivity ⇔ RH; Krein flux sign ⇔ RH; horocycle rate `y^{¾−ε}` ⇔ RH; unconditional stretched-exponential thermalization; universal decay `e^{−t/4}` ⇔ RH; Narain `¾` ⇒ RH, remainder VK; one cavity function of Hecke eigenforms is a complete and sharp receiver; reflection Krein forms PSD ⇔ RH; dual side has no sign; RH ⇔ `Q` is the Tate limit of a count ⇔ an internal standard form realizes `Q`; `Q` not integer-valued; vacuum-fixing and half-sided realizations excluded; Gram-coupled limits, positive parity fibres and the discrete adelic quotient [L].
- **(a)** A26, A69, A70.
- **(b)** `D_s≥0`, Krein flux, probe sign, dispersion bound or reflection Krein sign (B68); physical carrier (B69); `V_p` lower bound (B70); any rate past `½` or `¾` (B14, B71); count (B87); halving pairs for a single eigenform (B125); realization outside the excluded classes (B114); confined companion (B117); Green/Robin realization (B133).

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
- **Established:** blocks S9, S11, S15; cutoff-uniform mass ⇔ RH; AAL ⇔ tail transport; transport on right discs; crossing discs force power growth; escaping translates stay right of `½`; partial returns transport a zero or create a deep small value; returns at zeros tail-bad; near-full tail events positive density; forced-vanishing precision cap; integrality only on the torsion; rational orbit maps are Laurent Adams; weighted heavy-return measures `≤C max(T/2,δ^{−1})e^{−W/(8M)}`; coordinate separation retains half of any nonnegative prime weight; heavy subsets silent to the VK height [L].
- **(a)** A37, A47.
- **(b)** Uniform target mass (B72); exact tail events at every right zero (B83, B89); tail law at the Kronecker scale (B96); freezing beyond the cap (B121); replication (B128); independent current bound (B134); breadth past VK (B97, B137); decay (B82); DH for ζ (B141).

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
- **Path:** complete two-bump sign, horizon-layer sign, or a late-lag lower bound on a decisive sample → RH.
- **Established [L/K]:** full-family receivers; depth corridors; two-lobe bound; cut crystal; sharp location; critical threshold identities (S1); either prime two-bump family `B±τ_{log p}B` decides RH from one side; two-prime difference lags decide without attainment; gappy primes, prime powers of zero convergence exponent and the primes of late `√T` windows are universal decisive samples; positive infinite tail deletion removes the attained-top requirement; δ-separated configurations are decided on windows of length `80/δ`.
- **(a)** A9, A56, A64, A65.
- **(b)** Complementary-window sign, remaining-depth control (B6, B12, B101); the prime two-bump sign on a decisive sample (B130); all-height column (B46); bounded windows (B140).

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
- **Established [L]:** `κ(φ_c)=κ+1`; damped bound ⇔ RH; undamped cone bound ⇒ AAL; with ZAL ⇔ RH.
- **(a)** None that moves the route.
- **(b)** Arithmetic coupling bound; tensor loss (B39); B9, B11, B13; ZAL.

### ACS — Castelnuovo–Severi / Stepanov at the prime degrees
- **Path:** source energy → all-aperture Bézout → RH; or one side of Hasse–Weil for the smoothed Frobenius graphs on a decisive sample of prime degrees → RH; or a one-sided bound at a sampling or Bohr-dense set → AAL, with ZAL → RH; or uniform tensor moments → RH.
- **Established [L/K]:** blocks S10, S14, S16, S17, S18; source cone and RR; Bézout ⇔ RH; primitive `h¹` coercive for `a≤181/500`; Kloosterman purity; reciprocal quadric counts; Young projections at rank `≤4`; typical-height sign with Gaussian tails; count law of every hyperelliptic curve; RH ⇔ `c_B(log p)≥−K` at every prime ⇔ `≤K` ⇔ two-sided sign-free ⇔ the same on the primes of late `√T` windows; width ⇔ growth exponent; RH ⇔ `A_k=o(k)`; Rankin square abscissa `2maxRe ρ`; lower side blind exactly to nonnegative almost periodic top layers; VK saving of `P−A`; gauge family (S18).
- **(a)** A28, A41, A48, A56, A59, A64, A65.
- **(b)** Source-energy sign (B40, B1); the prime-window bound (B130); a sampling-set bound (B126); bounded windows (B140); count or Rosati producer over ℤ (B78, B87); diagonal (B88); global trace (B85); mixed Young shapes (B86); family specialization (B142); B65; B28.

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
| SOSZ | zonotope, half-products, point count, archimedean Frobenius as `ℍ³` Green function, damped Frobenius PSD, plastic sign, atomic genus `N log N`, logarithmic archimedean self-energy, one side of Hasse–Weil at every gap set = RH, iterated gap method, width = growth exponent, trace zeta at the power degrees, Stepanov bound = prime count, tensor-power trick, Rankin square, two Frobenii, sampling and Bohr-dense sets, lower-side blind set, Dirichlet `L` from both sides, count door, classical and VK saving, decisive samples (gaps, zero convergence exponent), almost-all-prime boundary, very smooth degrees, **scale locality** (`√T` windows, positive deletion, finite-spectrum oscillation, separated ordinates, ζ log-square leakage) | A48, A56, A58, A59, A64, A65 | B87, B88, B126, B130, B140 |
| HAT | twisted carriers and their dilation limits; carriers of bounded geometry, along ends, at conical limit points, with closed degree geodesics; boundary of groups convergent at `½`; compact and finite-volume embeddings; spherical compensation; locked dampings give the discriminant; finite places are trees; adelic Green formula; orientation-cover cohomology; smooth Green damping; mass obstruction; Gram coupling; prime-unit collapse; twisted Green fibres; discrete adelic degree configuration | A54, A69, A70 | B88, B106, B133 |
| ELT | Gaussian observation boundary, pole-dominated raw current, exponential passage, escaping layer profile, sharp recurrent envelope, single-quartet divergence, landing law for ζ (eleven forms), Deuring–Heilbronn question for ζ, classical Deuring–Heilbronn for quadratic `L(s,χ)`, complete Dirichlet divisor, positive Dirichlet moment kernel, infinite power sums, no Siegel regime, co-moving remainder masking, local and damping filters, contracting prime filters, Euler-region filter bounds | A47, A67, A68 | B128, B134, B138, B141 |
| ZCG (AbscissaLaws) | split, atoms, landing law, transport, two-scale theorem, linear hierarchy, quantifier collapse, shift non-invariance, finite-rank Chebyshev exponent, heat-family finite-stratum law, Dirichlet-series selector, compact coordinates of tempered configurations | A50 | B13, B83, B111, B138 |
| AWT | gauge family with big monodromy and uniform generic weights, Gaussian Frobenius, vertical equidistribution, generic moments on the archimedean line, trivial fibre as jump, Baire against Haar genericity, edge divisors, isozeric Euler deformations, exact-monodromy pricing, Künneth for tensor powers, exact tensor weights, `A_k=o(k)` ⇔ RH | none | B142 |
| CDGeo | two-sided gap iteration, absolute large values force heavy returns, fixed-height prime mass, collective rank depth, reciprocal-rank bounds, collective auxiliary, extrapolation and logarithm bounds, bounded elimination, hereditary rank, weighted coordinate separation, finite-time and weighted return counts | none | B97, B137 |
| ALST | Adams Frobenius on torsion and orbit, norm amplifier, Stepanov auxiliaries on the torsion, exact vanishing costs the degree, integrality only on the torsion, closed-point Stepanov count, rigid minimal auxiliaries, Lefschetz numbers = Stepanov degrees, polynomial Stepanov syzygies, polynomial, integral, rational and real rational orbit preservers are (Laurent) Adams maps, integer clock multipliers | none | B121, B48 |
| AHMH | seeds, position rigidity, every-seed receiver, ringdown = zero-free region, dual side has no sign, momentum universality, odd cavity, Maass and Hecke pairs, one cavity function a complete and sharp receiver, two-mode Zagier dichotomy, `T_p` self-adjoint, Shimura integral, halving obstruction, resonance and reflection Krein forms | A26 | B68, B71, B125 |
| EFT, ExactEventTheory | complete FE rigidity for `L¹` and `L²` defects, Gamma–Mellin source, tent identity, integer support, Gaussian surgery, Gaussian prime current, head-conditioned rough variance, joint prime-phase returns, normalized height reflection | A55 | B112, B128 |
| RHTower/Deninger | big and rational Witt rings with Frobenius and Galois descent, Deninger's additive-defect filtration, Witt Frobenius transgression, distributional Lefschetz formula = explicit formula, Meyer flow trace, no finitely generated Frobenius-stable lattice | none | B142 (as a carrier question) |
| TTPO | explicit linear forms, return–form duality, breadth cap, depth law, survival of jets, reciprocity of returns, function-field case, label statements, Turán on thick sets, VK breadth of heavy subsets, strip ⇒ breadth | none | B97, B121, B137 |
| IWT | towers, window theorem, rank barrier, Hasse–Weil principle at infinite rank, Wolff towers, towers of ζ, continuous-level lag = zero-free region, linear six-way TFAE, FE admits every finite layer and approaching remainders, sampling dimension, residual recurrence | A47 | B110, B111, B116, B127, ZAL |
| AES | heat clock, elapsed-depth and logarithmic-depth actions, initial divisor budgets, crowding dissipation, sharp coefficient `2`, deepest-product contraction | A19 | B124 |
| RIAC | completed prime boundary, prime-star and torsion compensation, prime-vertex dynamics, signed localization, gluing and section counts, prime-quadratic orientation, different and trace counts, finite-field root cover, orientation and squarefree counts over `𝔽_q` | A46 | B106, B88 |
| CTH | count law at every genus and every hyperelliptic curve, Born rules, boundary algebra, linear counts degenerate, Hecke conservation, second place, Farey reading, thermalization, sharp shells, partner standard-form trichotomy, half-sided inclusions excluded, `Q` not integer-valued | A41 | B87, B113, B114, B117 |
| APD | Hamburger rigidity, FE-defect isolation, one-offs of every positive class, integer-norm one-off across the line, two-scale and approaching integer-norm Euler products, firewall, positive annihilators and their phase geometry, Poisson rigidity, additive saturation, finite endpoint-jet surgery, Hecke state PD iff `s≥½` | A55 | B80, B98 |
| AHD / CACT | threshold identities, charged compactness, half-line ground states and orthogonality, multiplier no-go, aperture exchange, top-window non-escape, conductor resolution, adaptive head = `\|ζ(½+ib)\|²` | A9, A13 | B6, B8, B101, B104, B123 |
| AIF | inner field, Szegő infimum, Carleson measure, dilation quotient, causal certificate, forward map, restoring bound, `Ψ`-boundedness ⇔ RH, Selberg depth `O(T)`, Bohr profiles, local onset field | none | B2, B57, B66, B82 |
| AAD | producers, peak law, half scale, three-quarter floor, compensated producer, quarter rate under RH, rate = Mertens scale, Frobenius = factorial stencil, transport, slow returns right of the line | A30 | B15, B55, B89 |
| RAC | cut identity and kernel, ledger hierarchy, parity exponent, exact parity identity, exchange law, bounded count with a new zero, maximal angle, rotated relations | none | B67, B91, B92, B93 |
| TAPO | first return and brackets, precision law, heavy returns, conditional moments, resonator mean, recurrence dichotomy, AAL as tail transport, near-full tail events, partial returns, short-arc prime mass | A24, A37 | B89, B96, B97, B100 |
| PTT | Bohr isometry, boxes, savings, rounded orbit, mixing time, hull with natural boundary, Ξ-current lift | A24 | B46, B100 |
| ASH | graph black holes, Krein law, Lax–Phillips rank two, KMS, count law at genus one, genus-two graph; ModularBootstrap: Narain partition, VK remainder, `¾` ⇒ RH, ceiling `¾` | none | B68, B71, B87 |
| BHR | modular wave, metric, AdS₄ quotient, ringdown = strip, horocycle Mellin formula, Lax–Phillips semigroup, Maass cusp forms, Weyl order, Rankin–Selberg continuation and FE, Rankin bound, cusp-energy rates | A26 | B71 |
| RIT | Mayer scattering, Krein square, Hecke dispersion, Hecke Poisson measure | none | B68, B70 |
| ACP | Mertens energy residues, positive Hecke annihilators, reflected-pair decay boundary | none | B68 |
| SEL / Primon | degree-one classification, Euler rigidity, primon thermal Euler factors | none | B80 |
| MMD | Möbius over `ℤ[ω]` as cubic Gauss coefficient, nonzero residue, Fredholm pencil | A33 | B94 |
| AE, KPA, HHAC, ESG | polar calculus, Tate law, five currencies, torsion intersection, isolated-prime rigidity, core bouquet, barcodes | none | B87, B88, B106 |
| CSTW, CHT, VHR, NGF, MZF, FFP, ADO, APR, AKLT, ASRP, AGT, PBAP, WVL, CAF, TCS, HWV, ADT, AK | as in blocks S1–S6, S8, S11 | A1, A2, A4, A5, A6, A16, A18, A19, A20, A24, A28, A42 | B2, B3, B10, B16, B18, B19–B27, B47, B48, B50, B55, B57–B61, B77, B83, B85, B86, B102 |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| The minimal face: a crude bound on the smoothed prime count at a decisive sample of primes (one-sided `P(p)≤A(p)+K`, one Weil test per prime; or sign-free two-sided), local in scale (`√T` windows) | ACS, SRT, WL, HF, RW, and every window route through Σ141 |
| Σ sign on every window (`a*(ζ)=⊤`) | RW, EWU, OWU, ACT, CHMD, SZ, RN, ACS (source branch), AIP, SRT, SC, LI, TT (odd), HF, and the critical-curve branches of HF, SRT, AIP |
| Σ continuation at small time and the theta head at the critical zeros | ZCG (heat branch), PTR, LA, GTA, XN, HCF, PA, TH |
| Π square-root precision and long moments | WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| Γ reflection and selection | PM (reflection Krein form, rates), BAG, SEC, CDC, PCS |
| Missing source landing | APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF |
| The diagonal: count and Gram-defect sign; Green/Robin realization on the adelic quotient | ACS, HF, PM, RW through windows |
| The exceptional atoms: ZAL, B13, Landing (RH path), DH (AAL only) | BAG, JAS shell, SC undamped, WL thick runs, ACS sampling branch, ZCG one-off, linear and landing branches, LA finite support, RW polar ground energy |
| Dark range (Kronecker scale; collective depth floor) | every route at all heights; BAG and ZCG one-off branches; TH certificates; WD near-unit moments |
| Width axis (horizon observables, growth exponents at the primes) | PM, MC, ACS, every VK-scale saving |
| Families: specialization at the jump fibre | ACS tensor branch, HF, SC |
