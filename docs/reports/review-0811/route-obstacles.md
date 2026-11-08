# Route obstacles — status quo

Scope: 38 live route formulations, 9 candidates and their supporting programmes. For each route: path, what is established, obstacles that are **(a) just work**, obstacles that are **(b) open mathematics nobody has a solution to**.

**Corpus checkpoint:** commit `48ce5506c8` plus the working tree of 2026-11-08.

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means an independent source mechanism or landing is missing. Formulations are not independent mechanisms: HJ is PA, BSH is CDC, FEL's BSY criterion belongs to CTF. A criterion, a source construction, a quotient equality or a scalar grade does not discharge an arithmetic sign or vanishing.

**Evidence.** `[L]` Lean source. `[S]` Lean source unfinished, unintegrated or uncommitted. `[K]` Lean with transitive axiom audit. `[D]` deduction, not a Lean theorem. `[N]` numerical, uncertified. `[C]` classical literature, not formalized.

**Strength.** RH; ≥qRH (zero-free half-plane or Lindelöf); sub (strictly below quasi-RH); method; indep.

**Labels.** `A*` just-work items and `B*` open problems are listed in full in [obstacles-summary.md](obstacles-summary.md). An A item is known mathematics, finite computation, effectivization, integration or assembly of proved pieces; `(unverified)` marks A items whose difficulty is not established. Wall labels Σ, Π, Γ refer to [walls-ledger.md](walls-ledger.md).

**Notation.** Windows `[−a,a]`. `W` Weil's form, `w_n=Λ(n)n^{−1/2}`, `H` the archimedean–polar form, `P` the arithmetic part. `a*(ζ)` onset aperture; `ℋ(c)` Hardy interval; `λ*(c)` best cone margin. `r=τ_R(i)/τ_L(i)`, `L=artanh r`, `Ψ=½log H₁`, `q=Ψ′`. `N_d` non-real root count of `R_d(Ξ)`. `Θ=½+zeroWidth`, `Θ∞` asymptotic abscissa. ZAL: finitely many zeros beyond every positive depth. AAL: a right abscissa bound valid beyond some height holds for all zeros (equivalently: finitely many zeros right of `½+h` forces none). `E(s)=(s−1)ζ(s)/s`, `I(w)` inner field. `R=c⁸/log N`, `W₈(H)=∫H²e^{−8y}`, `Q₁=⌊(log N)^{13/32}⌋`, `R_c`, `R_polar`, `R_high` whole-space, polar-payment and high-conductor critical thresholds. `A(K)` best stencil slope on alphabet `≤K`. `R(y,η)` first return of the primes `≤y` at precision `η`. `E_y` Euler head, `ζM_y` Euler tail. `L=log|t|`, `ℓ=log L` in orbit statements. `A_φ(y)` horocycle mean of a pseudo-Eisenstein series at height `y`; `m_g(y)` cusp energy on that horocycle; `Λ_g` completed Rankin–Selberg function of a cusp form `g`. `A_YZ(y)` Narain double target-horocycle heat average. `Q(a)` the Weil form on integer probes `a∈ℤ^N`; `𝒬_t` Krein square of a black hole `(q,t)`.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ ZAL ∧ AAL; ZAL ⇒ qRH; ¬AAL ⇒ `Θ<1`; `qRH ∨ AAL` | [L]/[D] | one half is at least quasi-RH, the other sits below it |
| AAL ⇔ every right abscissa bound valid beyond some height holds for all zeros; symmetric shifts `ξ(s+a)ξ(s−a)` preserve AAL | [L] | AAL is a configuration statement (finiteness of the top layer), not a statement about the line `½` |
| Finite stratum: `κ(K_ζ)<∞` ⇔ index finite on one two-prime lattice ⇔ finitely many off-line zeros ⇔ bounded heat count ⇔ every zero above some height on the line; under it RH ⇔ one non-blind prime tower is PD | [L]/[K] | AAL at the abscissa `½` is "finite stratum ⇒ RH" (B13): the milestone toward AAL |
| Under AAL: RH ⇔ ZAL ⇔ finite off-line support ⇔ `κ(K_ζ)<∞` ⇔ bounded heat count ⇔ finite critical energy ⇔ eventual Hadamard ⇔ eventual central-gap budget | [L] | every large-height receiver reads RH once one-offs are gone |
| ¬AAL ⇔ finite top layer ⇔ `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})`, `T` a unique trigonometric polynomial ⇔ two-prime dilation annihilation | [L] | failure of AAL is one rigid object |
| Positive Euler products with integer norms (holomorphic on `Re s>½`) or rational-prime labels (holomorphic on `Re s>17/30`) carry a finite top layer with linear counting; none continues to `Re s=½`; positive two-prime and positive Hecke polynomials annihilate every finite zero set | [L] | an AAL proof must use the critical line (FE, critical regularity), not positivity, Euler products or counting |
| A positive annihilator of a zero that is `ε`-accurate right of the zero has mass `≥ε^{−(Re ρ−σ_lo)/(σ_hi−Re ρ)}` left of it | [L] | positivity can remove finitely many zeros only at a quantified cost on the critical side |
| Rational relocation of ζ's own critical zeros, normalized at `0` and `1`, has a signed density, negative on `(1,1+ε)` under every finite Dirichlet filter | [L] | a top layer of ζ cannot be produced by surgery on ζ while keeping positive coefficients |
| RH ⇔ `a*(ζ)=⊤` ⇔ `λ*(c)→0` ⇔ two-site PD ⇔ `Ψ` locally bounded | [L] | every window route measures one number |
| `0<R_c≤R_polar≤R_high=⨅_A windowThreshold(A)`; each stage `=⊤` ⇔ RH; at each fixed ratio every conductor channel except the pole is paid; the pole at every ratio is RH | [L] | the critical curve carries no sub-RH content; it is the window |
| Window positivity at aperture `a` excludes depth-`¼` zeros to height `e^{a/K}`, sharpens the pole self-energy and gives `R_polar≥c₁e^{c₂a}` | [L] | the form bootstraps by exchanging aperture for ratio; `a*(ζ)` is not raised |
| The adaptive theta head has leading term `(4/√π)\|Σ_{n≤\|b\|/2}n^{−½+ib}\|²`, a critical-line partial sum of ζ | [L]/[C]/[D] | the theta sign is decided near the critical zeros of ζ |
| Zeros of ζ are zeros of the Euler tail `ζM_y` at every cut; returns at right zeros are tail-bad at every cut; nonvanishing targets return at positive density | [L] | AAL in tail form needs an atypical tail event |
| Conditional tail laws stop at the Kronecker scale; first return bracketed at every precision; proportional saving ⇔ no early heavy return | [L] | the dark range is the Kronecker scale |
| Every unconditional saving carries the VK saving; stencil rate = Mertens level; the Narain AdS₃ remainder carries exactly the VK saving | [L] | production and holography have no content independent of the Mertens level |
| Farey discrepancy, `M(N)`, the nerve Euler characteristic and the core Euler characteristic minus `#primes(N/2,N]` are one number; persistence of the prime complex is classified and independent of `s`; maps homotopic to the identity have `≥N/(4log N)` fixed points | [L] | topology of the prime complex carries `M(N)` only as a signed count of a fixed barcode |
| Pulse ringdown, horocycle mean, Farey count, Lax–Phillips mode and cusp energy: a gain `δ` past the trivial rate ⇔ a strip of width `2δ`; the RH rates are `y^{¾}` and `e^{−t/4}`; sharp sources need cancellation beyond RH | [L] | every horizon observable is a receiver on the width axis |
| A count law has a quadratic half (Born rule = FE) and a count half (positivity = damping); it holds on every hyperelliptic curve, produced by Stepanov from a crude bound at every level; over ℤ the quadratic half holds (Hecke isometry of `Q`) and RH ⇔ `Q` is the Tate limit of a count | [L] | the separating property is a count; over ℤ only its count half is missing |
| Over ℤ a constant-factor bound `\|ψ(x)−x\|≤C√x` is false and any exponent `½+ε` is RH; tensor index is `0` or `∞` | [L]/[D] | there is no crude regime over ℤ: the count door has no sub-RH rung |
| ζ is isolated: FE defect `≤1/6400`, count distance `o(log n)`, exact parity identity | [L] | any stable argument in these metrics is about ζ alone |
| Necessary mollifier length `exp(c log²T)` = length of an Euler mollifier over primes `≤c log²T`, where absolute non-alignment starts | [L]/[D] | the near-line wall and the dark range are one wall |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | Primes pay the archimedean–polar deficit by sign | format exact on every window; size payment ends before half-width `21/40` |
| M2 Calibration | Window cones, blind positivity, margin | cone pinned at `e^{−c/1104}`; cone points obey PNT `5/6` on the window's range; ceiling doubly exponential; sign open |
| M3 Canonical flow | `L,q,Ψ` of the Weil chain | exact to contact; RH ⇔ `Ψ` locally bounded; `Ψ` oscillation is the sole control |
| M4 Reflection | Krein/Lewis positivity, Hecke dispersion, ringdown, Lax–Phillips decay, horocycle and Farey rates, Born rules | coefficient completion closed; Hecke algebra Poisson-positive off the line; FE = nondegenerate Born rule; positivity of the Born rule = damping; flux sign open |
| M5 Square-root cancellation | One smoothed prime count, long moments, Farey discrepancy | receivers closed; estimates open |
| M6 Continuation | Heat, cosine, Jensen | typical heights closed; small time at all heights open |
| M7 Zero geometry | Cameras, Blaschke factors, inner field | isolated zeros at rate 2; depth `O(T)`; clusters and `o(T)` open |
| M8 Recurrence | Transport of zeros by returns | transport closed on right discs; returns at zeros tail-bad; existence open |
| M9 Production | Integer stencils, integrality, Stepanov over ℤ | exact; rate = Mertens level; Stepanov over ℤ reaches Chebyshev; zeros are the kernel |
| M10 Count | A nonnegative function with quadratic Tate limit | every hyperelliptic curve [L]; over ℤ RH-strength, local data only |
| M11 Orbit at finite time | Prime phases at one height; first return; conditional tail; collision arithmetic | absolute savings; brackets at every precision; dark at the Kronecker scale |
| M12 Critical compactness | Gårding, Γ-liminf, non-escape, threshold law, conductor resolution | assembled [L]: the critical curve is the window; only the pole channel is unpaid at a fixed ratio |
| M13 Topology of the prime complex | Homotopy type, persistence, fixed points, torsion forms | classified, `s`-independent; literal fixed-point localization refuted; renormalized torsion forms converge only on `ℓ²(n^δ)`, `δ>0` |
| M14 Thermal averaging | Primon gas, Kesten–McKay densities, Green covariances | exact Euler factors at real points `>1`; never enters the strip |
| Amplifiers | Diophantine repulsion, integrality, isolation, Turán power sums | amplify a certificate, produce none |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve

Routes: HF, SRT, AIP, ACS (atomic), SC, CHMD (index). Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF.

Established:
- Full tilted-spline matrix PD for `1≤c≤(log N)^α`, `α<1/8` [L], and through `c≤2K₀(log N)^{1/8}` with complete Schur payment [K].
- Every compact C² profile: energy `≥ae^{−Bc}‖x‖²` on conductors `≤N^θ`, `θ<¼`, `c≤b log log N` [L].
- Every fixed ratio: critical pencil `κQ+(7J/R)W₈`; low packet `m≤Q₁` keeps its diagonal and polar part [K]; polar capacity `S_A²/(J₁/R+κg)` [K].
- Γ-liminf with weight `α_R>0`; strong `L²` limits; precompactness from physical and Fourier tails [L]. Unrestricted Gårding false; top-collar Gårding at every `R` [L].
- **Threshold chain [L].** `0<R_c≤R_c^{PSD}≤R_polar≤R_high=R_high^{PSD}=⨅_{A≥0}windowThreshold(A)≥c₀e^{6a*(ζ)}`; each stage `=⊤` ⇔ `a*(ζ)=⊤` ⇔ RH. `R_polar≥c₁e^{c₂a}` for every `a≤a*(ζ)`. `windowThreshold A₀=⊤` ⇒ `windowThreshold A≥ce^{3A₀}` for every `A`.
- **Conductor resolution at a fixed ratio [L].** Physical tearing has Schur ratio `→4/13`; conductor-adapted far complement decouples; for every `ε` a finite prefix `m₀(R,ε)` of conductors leaves residual low-packet coupling `≤ε`; eventual PSD gives polar payment on every window. Fixed nonpolar conductors have vanishing top-window rows uniformly on critical bands; deep conductor residuals vanish at every ratio; whole-space collar Gårding loses only the conductor-one coefficient square `b₁²`; primitive nonpositive directions have compact collar profiles with bounded weighted mass and Lévy energy [L].
- **Aperture exchange [L].** Window positivity at `a` excludes depth-`¼` zeros up to height `e^{a/K}`; sharp pole self-energy and compressed pole cross pairing for `K(2s+2)≤a*`; Mertens lag `Cx^{−1/4}`; reciprocal-Mangoldt error `Ce^{−t/8}`.
- **Low packet [L].** Payment at `R` on `[−A,0]` ⇒ `R≤windowThreshold A`; payment at every ratio on windows of length `→∞` ⇒ RH.

Structure [D]: at each ratio the critical form is paid on every channel except the pole `m=1`, its retained diagonal and the collar `L²` debit; the pole against growing windows is RH. No sub-RH content remains at the critical curve beyond the architectural question `R_c=R_high`.

| | Obstacle | Strength |
|---|---|---|
| A9 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | — |
| A13 | Near-gcd charges and periods beyond `M₀(N)` (unverified) | — |
| B6 | Full-space sign eventually at every `K`; equivalently every critical threshold `=⊤` | RH |
| B8 | Head thresholds for every `d` | RH |
| B101 | Low-packet polar payment at every ratio on growing windows (the pole channel) | RH |
| B104 | `R_c(ζ)=R_high` | method |

### S2. Window tower and canonical flow

Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT (odd), HF, ACS, SRT, SZ, MSC. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF.

Established [L]: precontact de Branges chain, canonical system with `H₁H₂=1`, flux, sampling bases; `L′=q−sinh 2L`; traces, `r`, `Ψ` absolutely continuous; `q_y→q` in `L¹`; restoring bound `|L(x)|≤artanh e^{−2(x−c)}+2osc Ψ`; RH ⇔ `L` locally bounded on precontact intervals ⇔ `Ψ` locally bounded; off RH `L` is unbounded above every base; soft prime kick; Born model; causal certificate; Szegő threshold; free reflection coordinates; forward-map tangent; cone pinning, margin ceiling, bounded extremals; cone points carry local density `1+O(e^{−a})`, positive support density and PNT `5/6` on `X≤e^{2c−3}`; datum region `⊆{β≤1}`; exact null blind test; floors `(1/20000)/2^k` through `a_k<0.3621`; window naive heights exist iff positive, and on length `≤3/5`; Tate dimension one exactly through `log 5`.

Structure [D]: the whole window tower is one local boundedness statement for one real function. The margin ceiling forces `m≳e^{2a}`, above the Born bound: the potential is a nonlinear collective response.

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

Established [L]: `Ω_ψ(a,X)` as a sum over zeros; on-line terms nonnegative; depth cost `≤(16/9)δ²a⁴‖ψ‖²`; RH ⇔ `Ω≥0`. Typical-height sign at `A=δlog T/(64M²)` for every shaped test; bad heights Gaussian-tailed `≤209(4kδ²)^kT`, measure `≤T^{1−1/(64K)}` at `A=K log log T`. Weil's form is the average of its frequency packets. Visibility, cut crystal, sharp location at `λ>1`; isolated-zero entry on the column.

Structure [D]: all-height sign stops at the size curve `a≈log log X`; past it the input is the short-sum barrier (S11).

| | Obstacle | Strength |
|---|---|---|
| — | none that moves the route | — |
| B28 | Local Weil positivity at fixed `λ>0` on density-one heights | sub |
| B46 | Proportional saving = no early heavy return at length `(log X)^{2K}`, all heights | sub |

### S4. Continuation and nodal geometry

Routes: ZCG, LA, PTR, HCF, PA, GTA, XN. Programmes: NGF, FFP, ADO, RHTower heat.

Established [L]: collision criterion; horizon `(6600/9991+ε)/log X`; density-one `Λ_Xlog X→0` with cubic exceptional exponent; crystal and reality at the critical scale; sharp depth law for isolated simple zeros; `N_d` law and inner-root reality; cosine Laguerre above VK; nonrepelling values of dimension zero; maximal-angle law and Stieltjes sign; one-sided Gaussian prime ceiling at every rational height ⇔ RH. The extremal inequality alone has a polynomial model with off-axis zeros.

| | Obstacle | Strength |
|---|---|---|
| A19, A20 | Heat horizon toward its method floor; Jensen rung and constants (unverified) | — |
| B24 | Collisions at arbitrarily small time, all heights | RH |
| B25 | Frequency `<1` at every collision | RH |
| B26 | Arithmetic input distinguishing `Φ` among `Φe^{−τx²}` | method |
| B27 | Runs of `k` simple critical zeros, every `k` | sub |
| B47 | Multiplicity `o(log X)` by a non-size input | sub |
| B22, B23 | Outer roots of `R_d(Ξ)`; `N_d` bounded | RH; ≥qRH |
| B92, B93 | Rotated relation with coefficients of the size of `Q`; a contradiction using growth, log-concavity or arithmetic of `Q` beyond the extremal law | RH |

### S5. Near-line geometry and long moments

Routes: WD, CTF, MC, TG; census. Programmes: CDG, APR, MZF, AIF.

Established [L]: Selberg CLT and prime field; cameras, hyperbolic density theorem, `N(ρ)=exp(−ΣG)`; box budgets and Carleson measure; eight-way log-mean equivalence, Abel form ⇔ depth density `o(T)`; Selberg's mollifier gives off-line first moment `≤(67/1000)V`, depth `O(T)` uniformly in windows and a bounded inner field at infinity; necessary-length laws; last-scale floor; long-moment slope, one-window and positive-proportion forms; Möbius zero condensation; dilation identity: RH ⇔ zero surplus ⇔ Szegő budget ratio equality, Euler prefixes invariant.

Structure [D]: an Euler mollifier over primes `≤y` has length `e^{θ(y)}`, so the necessary length is that of an Euler mollifier over primes up to `≈c log²T`, the scale where prime phases become absolutely non-aligned (S11). The near-line wall is the dark range. Bounded inner field is not vanishing inner field.

| | Obstacle | Strength |
|---|---|---|
| A18, A21 | Twisted moments past `21/50` [C]; census items | — |
| B57 | Depth density `o(T)`, equivalently log-mean `→0` | sub |
| B58 | `D_win` | sub |
| B59 | Cluster wall | sub |
| B60 | Exponential moments of the Green potential at deep zeros | sub |
| B61 | A detector past the last scale | sub |
| B62 | Cofinal long moment | RH |
| B66 | Near-unit holomorphic budgets; zero dilation surplus | RH |
| B82 | Inner-field decay | ≥qRH |

### S6. Production and precision

Routes: WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, LI, AIP. Programmes: ASRP, APR, AGT, AKLT, AE, AAD, RAC, MMD, SPAL, HWV.

Established [L]: band ⇔ classical criteria; integer lag; entry filters; length–precision law; gauge exponents `[Θ,1]`; twin quarter floor; Nair lattice; Stepanov over ℤ = integrality floor + Nair ceiling, comparable log-torsion and degree; producers `c=μ∗h`, mollifiers on `Re s=1`; floor `c/(√K(1+log K))`; rate `K^{−a}` ⇒ `Re ρ≤1−a`; all `a<½` ⇒ RH; RH gives `a<¼`; the Frobenius over `𝔽_q[T]` is Carlitz's factorial stencil of rate 0; compensated producer; parity-neutral producers at every rate; extremal fakes with `≤K` atoms; cut kernel = zeros; finite-energy kernel mass annihilation ⇒ RH; exact identity pins `λ`; exchange law; count-distance rigidity; bounded count with a new zero (signed generators); Farey discrepancy ⇔ RH; square-root Farey law ⇔ RH; `M(N)=−χ̃` of the nerve; cubic Gauss conversion with nonzero residue at `4/3` and continued Fourier modes.

| | Obstacle | Strength |
|---|---|---|
| A21, A30, A33 | Chowla [C]; best RH exponent in `[¼,½]` (unverified); cubic residue Fourier coefficients [C] | — |
| B48 | A deciding input at square-root precision; equivalently a crude zero-localized prime count at every level (Stepanov over ℤ) | RH |
| B55 | Any polynomial stencil rate (qRH); rates `a↑½` (RH) | ≥qRH to RH |
| B15 | Mertens level past VK | sub |
| B14 | Any interior width value | ≥qRH |
| B56 | `Θ<1⇒Θ=½` | sub |
| B67 | Parity at power saving | ≥qRH |
| B91 | Finite-energy cut-kernel vectors have mass zero | RH |
| B94 | Transfer of the cubic conversion to rational-integer Möbius | past VK at least |
| B98 | Positive-generator integer-norm systems: which count distance forbids a finite top layer | method |

### S7. Reflection, carriers and the modular horizon

Routes: PM; W1C (candidate); RN and PTR in part. Programmes: RIT, ART, AOT, ACP, BHR, ASH (ModularBootstrap), CTH, SEL/Primon.

Established [L unless marked]:
- Scattering: resonance ⇔ `ζ(2s)=0`; `Q=2Re[WH,WH]`; `D_s≤0`, zero iff `Re s=¼`; Hecke dispersion `V_p`; every Hecke operator diagonal on Eisenstein; the Hecke algebra has a positive Poisson measure on truncated resonant states for every `Re u<0`; positive `T₂,T₃` polynomials annihilate any finite resonance set; scattering Blaschke product.
- Horizon: exact modular horizon, quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)`; ringdown in the modes of zeros; metric of general `L²` data; pulse metrics regular across the horizon.
- Width-axis dictionary: for `0<δ≤¼`, zero-free `Re ρ≤1−2δ` ⇔ every compact pulse rings down at `e^{−(δ−ε)τ}` ⇔ every horocycle mean converges at `y^{½+δ−ε}` ⇔ every smoothed Farey count converges at that rate; RH ⇔ `y^{¾−ε}` ⇔ square-root Farey law ⇔ every resonant mode decays at `e^{−t/4}` (Lax–Phillips semigroup of the modular surface).
- Cusp channel: Maass cusp forms exist (mirror-odd sector is cuspidal); spectrum discrete, `N(Λ)≍Λ`; joint eigenspaces of dimension `≤2`; Rankin–Selberg continuation with FE and `e^{−π|t|}` decay; mean-square law; smoothed Rankin–Selberg sums with power saving `X^{3/4}`; cusp energy rate `y^{½−ε}` unconditionally, `y^{¾−ε}` under RH; rate `y^α` forces `Λ_g(ρ/2)=0` for `Re ρ>2−2α`.
- Narain AdS₃ source [L]: literal partition, modular invariance in all three moduli, mirror symmetry, Mellin continuation retaining every arithmetic pole; source clock holomorphic in a fixed complex strip; double average with exact main terms and Schwartz boundary; remainder with the VK saving at a target-independent exponent `1/128`; `¾` ⇒ RH; every exponent `>¾` impossible.
- Graphs: black holes with flux, unitarity, Hecke at every degree and class; Krein flux law; Born rules (nondegenerate ⇔ FE, positive ⇔ damping); boundary algebra with partner involution (positive state ⇔ damped; `C*` blind); count law ⇔ `t²≤4q`; genus-two graph: FE for every `q`, first-level count law iff `q≤19`, all levels iff `q≤3`.
- Sharp sources: sharp shells thermalize at `y^{½}log(1/y)`; their `¾` rate needs Möbius × circle-problem cancellation not controlled by RH.
- Primon: arithmetic thermal means are Euler factors of `ζ(2e^β+1)`; Kesten–McKay densities, Gaussian Green processes, likelihood span = even semicircle `L²`.

Structure [D]: wave dynamics, unitarity, Hecke, KMS, `C*`-positivity, the functional equation at genus two and the first-level count leave damping open on graphs; the separating law is a count of full rank. Every modular-horizon observable reads the poles `ρ/2` of one Eisenstein series, in space or in time, on the width axis.

| | Obstacle | Strength |
|---|---|---|
| A26 | Weyl asymptotic with its constant (`N(Λ)∼Λ/12`) [C]; order `N(Λ)≍Λ` is proved | — |
| A43 | Identify `Λ_g` with the completed `L(g×g,s)=ζ(s)L(Sym²g,s)` for Hecke eigenforms [C] | — |
| B68 | Independent `D_s≥0`, nonnegative Krein flux, integer-probe sign or all-zero dispersion bound | RH |
| B69 | Positive physical carrier | producer |
| B70 | Lower bound for `V_p` from the carrier | sub |
| B71 | Universal decay `e^{−t/4}` / horocycle rate `y^{¾−ε}` / Narain remainder `y^{¾−ε}` | RH |
| B87 | A count for `Q` over ℤ | RH |
| B109 | Rankin–Selberg noncancellation: some cusp form `g` with `Λ_g(ρ/2)≠0` at every off-line zero `ρ` | indep. (completes a receiver) |

### S8. Index and support

Routes: HKT, AKLT, SC, RIT, CWS through HF, ACS; LA; ZCG heat count. Established [L/K]: `κ(φ_c)=κ+1`; finite index ⇒ Lindelöf; `κ∈{0,∞}` under escape, mixing or decay; window index counts critical lengths; `sup_dN_d` off-line multiplicity; `K_ζ^n` PD ⇔ RH; TFAE: `κ(K_ζ)<∞` ⇔ index finite on one two-prime lattice ⇔ finitely many off-line zeros ⇔ bounded non-real heat count for `t>0` ⇔ every zero above some height on the line; under finite support, RH ⇔ the kernel on one non-blind prime tower is PD ⇔ infinitely many prime towers are PD.

Structure [D]: the finite stratum is one object read five ways, and AAL at the single abscissa `σ=½` is exactly "finite stratum ⇒ RH" (B13). Every receiver in the TFAE list becomes an RH receiver once B13 is known.

| | Obstacle | Strength |
|---|---|---|
| B12 | Index ceiling uniform in resolution | ≥qRH |
| B13 | Exclude finite nonzero off-line support; equivalently `κ(K_ζ)∈{0,∞}`; equivalently eventual RH ⇒ RH | sub |
| B23 | `N_d` bounded | ≥qRH |

### S9. Abscissa split, recurrence, one-offs

Routes: BAG, JAS shell, SC undamped, WL sparse samples, ZCG one-off branch, RW polar ground energy. Programmes: AKLT, ZCG, AIF, APD, AAD, RAC, PTT, TAPO, SPAL, ACP.

Established [L unless marked]:
- Split RH ⇔ ZAL ∧ AAL ⇔ ZAL ∧ zero-disc weak recurrence ⇔ ZAL ∧ subexponential polar ground energy. AAL ⇔ eventual-to-global abscissa bounds; symmetric shifts preserve AAL.
- AAL producers: not-attained top; bounded lag on a progression; lag `≤Me^{aL}` off a set of lower Abel density zero; subexponential polar ground energy; one generic prime-window grid; log-dense integer lag; twisted plateau; JAS dressed PSD, typical positivity, shell positivity (Turán's second main theorem with a finite head); bounded towers; one bounded cone; weak recurrence; infinitely many zeros near each right zero; slow aligned returns on right discs.
- ¬AAL: finite oscillation of `ψ(x)−x`, unique `T`, quantized coefficients, remainder ceiling, sign changes, two-prime dilation annihilation, rightmost-zero jets with long-shift correlation `m²`.
- Transport: discs crossing `Re s=½` force `|ζ|≥cτ^b`; right discs carry the AAL receiver. Head returns `N<1024(log τ)⁴(log log τ)²`.
- Tail: zeros of ζ = zeros of `ζM_y` at every cut; returns at right zeros tail-bad and of density zero; nonvanishing targets return at positive density; head frozen below `1/log y`.
- Hull: Haar-a.e., fair-coin-a.e. and order-two fibres extend zero-free to `Re s>½` with natural boundary `½`; the Liouville point extends iff RH.
- Countermodels: continuous one-offs; discrete and integer-norm one-offs with linear counting; rational-prime one-offs with multiplicative linear counting on `Re s>17/30`; positive two-prime annihilators; positive Hecke annihilators. Every one-off fails to continue to `Re s=½`; FE defect `≤1/6400` forces the rational primes.
- Annihilator cost [L]: a positive two-prime annihilator that is `ε`-accurate on a line right of its zero has mass `≥ε^{−(Re ρ−σ_lo)/(σ_hi−Re ρ)}` on every line left of it; at unit mass its zero is simple with `Re` derivative `≥log 2`.
- Relocation [L]: rational relocation of two critical pairs of ζ to `¼,¾`, normalized at `0` and `1`, has signed zero-mass density, negative on `(1,1+ε)` under every finite Dirichlet filter.

Structure [D]: the random Euler model does not reach targets with zeros, so a bounded return at a zero is an arithmetic event at the Kronecker scale. The one input no countermodel carries is the functional equation at the critical line. ¬AAL is a finite exceptional layer inside the strip, an exclusion problem of Landau–Siegel type. Since AAL is the eventual-to-global step and is shift-invariant, it is the ℤ-analogue of the self-improvement step of the curve proof (power-sum elimination plus FE), not of the crude count.

| | Obstacle | Strength |
|---|---|---|
| A37 | Resonator mean of `\|ζ\|²` with resonators growing below the Kronecker scale (unverified) | — |
| B83 | AAL | sub |
| B89 | A bounded aligned return at each right zero on a right disc, i.e. a tail event cancelling the head at every cut | sub |
| B96 | Conditional law of the Euler tail at the Kronecker scale | sub |
| B13 | Finite nonzero off-line support | sub |
| B84 | Smallest FE defect carrying a one-off | method |
| B103 | Does continuation to the critical line (or small FE defect) force AAL for positive Euler products with linear counting | method / sub |
| B72 | Cutoff-uniform target mass | RH |
| B82 | Inner-field decay | ≥qRH |

### S10. Count and effectivity

Routes: ACS, HF, PM integer probes; RW through window naive heights. Programmes: AE, CWS, LST, KPA, ASH, CTH, RIT.

Established [L]: polar surface calculus; Tate law (degree-two form `≥0` iff a function bounded below lies at bounded distance); five currencies; theta `h⁰` with exact RR; Künneth `h¹` split; Λ as an intersection number of torsion orbits, with an indefinite renormalized torsion limit; source cone and all-aperture RR; Bézout ⇔ RH; Young projections at rank `≤4`; reciprocal tangent quadrics with exact projective counts. On curves: count law at level `n` = genus form = half the Castelnuovo–Severi defect; tower count law ⇔ crude bound at every level ⇔ unitary; RH, Hasse–Weil and the count law for every hyperelliptic curve (any degree, odd characteristic); bielliptic genus-two count = sum of two Manin counts; Rosati form = Born rule, and naive height ⇔ nonnegativity ⇔ count law at every level ⇔ unitary. Over ℤ: `Q(a)=Σa_ma_nC(log(m/n))`; Hecke isometry of `Q`; RH ⇔ `Q` is the Tate limit of an `ℕ`-valued count; linear counts degenerate; Hecke gives conservation only; non-arithmetic Hecke triangle groups fail at a second place.

Structure [D]: over curves the count comes from a crude producer at every level plus finite-rank self-improvement; over ℤ there is no crude regime (Π111), and the count must be produced exactly at square-root size by an object other than `Q`.

| | Obstacle | Strength |
|---|---|---|
| A28 | Identify reciprocal-quadric traces with vanishing-cycle Frobenius traces (unverified) | — |
| A41 | Count law for every curve over `𝔽_q` (Bombieri–Stepanov), first case plane quartics [C] | — |
| B87 | A function on integer probes, nonnegative for an arithmetic reason, with quadratic Tate limit `Q` | RH |
| B88 | Sign of the renormalized torsion form and its comparison with Gamma/pole at the critical weight `δ=0` | RH |
| B95 | An abelian group with Hecke endomorphisms `T_n`, `T_n′T_n=n`, whose trace form is `Q` | producer |
| B65 | Genus upper law; logarithmic Serre duality; first Epstein real zero | indep. to sub |

### S11. Prime orbit at finite time

Routes: BAG, TH, SRT, RW, ZCG carriers, every route at the all-height wall. Programmes: PTT, TAPO, SPAL.

Established [L]:
- Boxes: every window of length `exp(10y√(log y·log log y/δ))` enters every `δ`-box on primes `≤y`; dyadic sign codes give missed boxes.
- Savings: `8/(10⁹L⁶ℓ⁴)` at length `48L²ℓ`; `t^{−δ}` at `L^A`; no cancellation below `c log T` at some height; square-root cancellation at all dyadic lengths `Y..T/log T` off measure `≪TY^{−2ε}`.
- First return: brackets at every precision; bounded harmonic defect `R≥exp(c(log N)^{3/2}/log log N)`; RH bracket at precision `≍y^{−9/2}`; weak returns = extreme values of `ζ(1+it)`.
- Heavy returns: proportional saving ⇔ no early heavy return.
- Conditional tail: Gaussian conditional moments below the Kronecker scale; smooth × prime mean squares with collision costs.
- Ceilings: rounded orbit; word costs; binomial blocks; moving jet; comb.
- Certificates: Euler coordinates stop at `Re s=1`; head–tail certificate ⇔ tail-good.

Structure [D]: between `log t` and `exp((log t)^{2/3})` the Taylor degree of `t log(n+h)` exceeds `(log length)²`. The required saving at the size curve is `≈εL/ℓ`, the proved one `≈L⁻⁶`.

| | Obstacle | Strength |
|---|---|---|
| A24, A37 | Certified scans and brackets; growing resonators (unverified) | — |
| B46 | Proportional saving at length `(log X)^{2K}`, all heights | sub |
| B97 | Constant-precision first return: `log R(y,δ)≥y^c` for fixed `δ`, every heavy subset | sub |
| B100 | A saving for `t log n` on moving families of blocks past Vinogradov's degree | sub |
| B15 | Past VK | sub |
| B20 | Oscillation of the actual amplitude with the height | RH |

### S12. Topology of the prime complex

Routes: MC (nerve, Redheffer), HF and ACS through the coprime stratum. Programmes: HWV, ADT, ESG, HHAC.

Established [L unless marked]: `det R_N=M(N)=−χ̃` of the prime-star nerve; squarefree prime complex ≃ wedge of spheres over odd squarefree `N/2<m≤N`; `χ̃=Ω±(√N)`; RH ⇔ `χ̃=O(N^{½+δ})`. Persistence: bar `[m,2m)` for every odd squarefree `m`, degree `ω(m)`, over every ring; Dirichlet weighting `n^{−s}` gives an isomorphic persistence functor for every `s`; prime-valued boundaries add `ℤ/2` classes on `[2m,3m)` for squarefree labels coprime to 6, torsion exponent 2, nonsplit extension; two-prime block quotients compute the core over every ring [L]. Fixed points: upper-half primes isolated; every map homotopic to the identity has `≥N/(4log N)` fixed points; the core ≃ bouquet of odd-squarefree composite spheres with augmented Euler characteristic `M(N)+#primes(N/2,N]`. Torsion forms: raw positive, renormalized convergent in operator norm on `ℓ²(n^δ)`, `δ>0`, at rate `O(ε^α)`, represented by a compact self-adjoint operator; unweighted mixed row unbounded; the limit kernel is indefinite (negative on equal-coefficient vectors on `{p,2p}`, positive on single primes).

Structure [D]: homotopy type, homology, persistence and fixed-point sets are computed exactly and carry `M(N)` only as the signed count `Σμ(m)` of a fixed barcode; nothing in them depends on `s`. Matchings and filtrations cannot go below the Betti number `≍N`; literal fixed points cannot go below `N/(4log N)`; the core's own Euler characteristic is not of square-root size. Cancellation at `√N` must come from structure outside the homotopy type.

| | Obstacle | Strength |
|---|---|---|
| B10 | Top coprime stratum | RH |
| B106 | A natural relative pair `(X,A)` with `χ(X,A)=M(N)`, or a natural self-map or group action whose signed fixed-point indices localize to `O(N^{½+ε})` | RH (≥qRH at exponent `θ<1`) |
| B88 | Sign of the renormalized torsion form at the critical weight | RH |

## 3. Live routes

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy or one-sided `Φ` → RH.
- **Established [L/K]:** bounded endpoint energy ⇔ RH; integer lag ⇔ RH; `Ω±(√n)`; first-band abscissa `2Θ`; gauge exponents `[Θ,1]`; subtracted lag ⇔ ZAL; lag excursions of lower Abel density zero ⇒ AAL; log-dense integer lag bounded above ⇒ AAL; one-sided Gaussian prime ceiling at every rational height ⇔ RH. Production support: stencil exponent `[¼,½]` under RH; cut kernel; exact parity identity; twin quarter floor.
- **(a)** A30.
- **(b)** Bounded endpoint energy and first-band square-root bound (B49); half-power at the trivial gauge (B50); deciding input (B48); past VK (B15).

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every radius → RH.
- **Established:** blocks S2, S3; RH ⇔ `Ψ` locally bounded; cone nonempty ⇔ RH; relative compactness ⇔ RH; naive height on every window ⇔ RH; RH ⇔ ZAL ∧ subexponential polar ground energy; cone points obey local density and PNT `5/6` on the window's range [L]; window positivity at `a` gives depth-`¼` exclusion to height `e^{a/K}` and `R_polar≥c₁e^{c₂a}` [L].
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
- **Established [L]:** Hausdorff rows nonnegative for `r≥min(C₀(k+1)²,S(k))` with the explicit shift from the sharp zero mass; remaining entries ⇔ RH; exterior diagonal criterion at `218/25`.
- **(a)** Verified rows (A1).
- **(b)** Signs below the explicit boundary, exterior `K(z,z)≥0`, or `TV(n)/qⁿ→0` (B31).

### MC — Möbius cancellation
- **Path:** half-power Möbius or Liouville cancellation → RH.
- **Established [L/K]:** damped energy ⇔ RH; one-point form; VK Hilbert energy; Möbius zeros condense on `Re s=Θ`; gauge genericity; producer rates; parity exponent = zero abscissa; exact identity pins `λ`; twin quarter floor; Farey discrepancy ⇔ RH; square-root Farey law ⇔ RH; `M(N)=−χ̃` of the nerve and `M(N)` = core Euler characteristic minus `#primes(N/2,N]`; persistence of the prime complex classified and `s`-blind; cubic branch: ideal Möbius = cubic Gauss coefficient, nonzero residue at `4/3`, continued Fourier modes.
- **(a)** Chowla [C] (A21); Fourier coefficients of the cubic residue (A33).
- **(b)** Trivial-gauge cancellation or zero exclusion for `M_X` (B50); deciding input (B48); past VK (B15); rational transfer (B94); topological localization (B106).

### TT — Theta tail / Wold
- **Path:** weighted endpoint energy bounded for each `0<t<½` → RH.
- **Established [L]:** Wold residual VK; `D_t+Q_t/2≥0`; boundedness ⇔ RH; uniform bound on a shrinking band.
- **(a)** None that moves the route.
- **(b)** `C_t` at every fixed `t` (B34); odd branch B4.

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted or sublinear root height → RH.
- **Established [L]:** block S4; infinitely many unshifted degrees ⇔ RH; inner roots real; `N_d≤300√(d log d)`.
- **(a)** A20; A1.
- **(b)** Outer roots (B22); `N_d` bounded gives finite support only (B23), which is RH once B13 is known.

### ZCG — Zero-configuration geometry / heat descent
- **Path:** half-Gaussian source → no positive-time collision → RH.
- **Established [L]:** blocks S4, S5, S9; cameras; sharp location; one-off structure and jets; maximal-angle law; the extremal law alone admits a polynomial model; AAL ⇔ eventual-to-global abscissa bounds, preserved by symmetric shifts; prime-pair source retains the prime-power field.
- **(a)** A19.
- **(b)** Small-time collisions (B24); frequency (B25); time-0 selector (B26); non-size frequency input (B47); runs (B27); FE-pair reality (B76); crowded zeros (B59); long-shift `Λ` correlation or a bounded return in the one-off world (B83, B89); rotated relation or a contradiction using growth or arithmetic (B92, B93).

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH.
- **Established [L]:** defect trace class; multiplicity `≤` trace norm; Gaussian passage criterion.
- **(a)** None that moves the route.
- **(b)** Trace norm `<1` on every rectangle or bounded Gaussian oscillation (B38).

### HF — Hodge / Hecke / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** blocks S1, S10; source-work `≤2` ⇔ RH; threshold chain `R_c≤R_polar≤R_high=⨅windowThreshold` [L]; at a fixed ratio only the pole channel is unpaid [L]; `R_polar≥c₁e^{c₂a}` below the onset [L]; low packet at every ratio is RH [L]; unrestricted Gårding false [L].
- **(a)** A9, A13.
- **(b)** Full-space sign at every `K` (B6); low packet at every ratio (B101); head windows (B8); source-work ceiling (B41); top coprime stratum (B10); zero modes (B9); exact SOS (B11); Rosati and band poles (B78, B79); count (B87).

### CHMD — Causal hyperbolic–modular duality
- **Path:** one-sided bounded prime wave or odd Doob half-threshold bound → RH.
- **Established [L]:** wave and Doob receivers; normalized prime−pole decay; nonfirst source keeps `1−ε` of Gamma.
- **(a)** None that moves the route.
- **(b)** Either side of the unnormalized wave bound, or the complete odd sign (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel → RH.
- **Established [L unless marked]:** rank 14 at `0<a≤½`; rank `N` from verified height; VK collar; two-atom and chain signs; `S=Π_pT_pA`; insertion cone; locking = torus positivity; columns add; current `=2|Ξ|²Re ξ′/ξ`; frozen certificate exactly above the size curve; first-atom Gamma floor `aC_Γ/cosh(πb/2)`, positive Bessel tails at every cutoff with complete Gamma mass and exponential transport; the adaptive head `M(b)=⌈|b|/2+B⌉` pays the omitted pair sum by half that floor in every polynomial-square integral; fixed heads have leading term `(4/√π)|Σ_{n≤M}n^{−½+2iτ}|²`; no summable absolute pair majorant; no compact core funds every Gamma direction; weighted Legendre kernels preserve degree.
- **Structure [D]:** the adaptive head is a partial sum of ζ on the critical line of length half the height; positivity is automatic where `|ζ(½+ib)|` is large and is decided by second-order terms near the critical zeros. A proof through `S` must use oscillation of the amplitude with the height.
- **Numerics:** positive at actual phases `b≤775`; torus-uniform positivity fails once primes `≲19–47` are free [N].
- **(a)** Rank 15 and beyond (A4); tail-failure certificate (A5); scans and brackets (A24); verified ranks (A1); uniform fixed-head asymptotic at `M=M(b)` (A42, unverified).
- **(b)** Exact torus law for `S*` and `{2,3}` cross-chain positivity (B19); amplitude oscillation with the height (B20); all ranks (B21); signed adaptive head at every degree, decided near critical zeros (B102); tail law at the Kronecker scale (B96).

### RN — Theta renewal
- **Path:** two-ended renewal → no joint nodes → RH.
- **Established [L]:** `det₂` gives `D`, not Ξ; Ξ zeros = joint nodes; energy comparison ⇔ RH.
- **(a)** None.
- **(b)** Joint-node exclusion or energy comparison (B36).

### WD — Ward / collision / long moments
- **Path:** source current, window energy or long moments → RH.
- **Established [L]:** block S5; one-window form; slope rigidity.
- **(a)** A18.
- **(b)** Cofinal long moment (B62); log-mean (B57); `D_win` (B58); cluster wall (B59); Green moments (B60); detector past the last scale (B61); collision charge (B63).

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
- **Path:** scattering source → Krein/Lewis positivity, integer-probe sign, dispersion bound, horocycle/Farey rate, resonant decay, Narain remainder or cusp-energy rate → RH.
- **Established:** block S7; integer-probe positivity ⇔ RH; Krein flux sign ⇔ RH; horocycle rate `y^{¾−ε}` ⇔ square-root Farey law ⇔ RH; universal resonant decay `e^{−t/4}` ⇔ RH; Narain `¾` ⇒ RH, Narain remainder has the VK saving; cusp-energy rate reads `Λ_g(ρ/2)`; RH ⇔ `Q` is the Tate limit of a count; Born rules and the boundary algebra separate FE (quadratic half) from damping (count half); linear horizon counts degenerate [L].
- **(a)** A26, A43.
- **(b)** `D_s≥0`, Krein flux, probe sign or dispersion bound (B68); physical carrier (B69); `V_p` lower bound (B70); any rate past `½` or `¾` (B14, B71); count (B87); Rankin–Selberg noncancellation (B109).

### PTR — Cosine source / photonic
- **Path:** `A_h` collision-free descent → RH.
- **Established [L]:** sech handoff; strict Laguerre for `h≥½` and above VK; sign at every `0<h<½` ⇔ RH.
- **(a)** None.
- **(b)** Strict sign below VK (B29); lossless prime-faithful stack (B69).

### JAS — Joint ancestry
- **Path:** subpower control on moving finite power windows → RH.
- **Established [L]:** RH criterion on `m<k≤m+m/log(m+1)`; finite admission; shell positivity infinitely often ⇒ AAL (Turán power sums with a finite head over all ξ zeros); typical JAS positivity ⇒ AAL; dressed PSD ⇒ AAL.
- **(a)** None.
- **(b)** Uniform control on the moving window (B51); shell signs plus ZAL.

### CTF — Chronological tail / Báez–Duarte
- **Path:** approximation, defect, BSY sign, log-dilation equality, cut-kernel mass or mollifier infimum → RH.
- **Established [L]:** rows ⇔ RH; sharp defect, sparse subpolynomial ⇒ RH; BSY `I≤0` ⇔ RH; positive-proportion form; exact infimum `exp(2I(1))`; rigidity; one-`δ` dilation equality ⇔ Szegő ratio equality ⇔ RH; Euler prefixes invariant; finite-energy cut-kernel mass annihilation ⇒ RH; the coefficient-Hardy domain of `ζ(s+ε)` is trivial for `ε≤½`, dense for `ε>½`.
- **(a)** None that moves the route.
- **(b)** Rows, sparse defect, BSY sign, positive proportion (B52); near-unit budgets, zero surplus (B66); cut-kernel mass (B91).

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
- **Path:** strong self-return or head-target mass, or decay plus zero-disc recurrence → RH; slow aligned returns on right discs → AAL.
- **Established:** blocks S9, S11; cutoff-uniform mass ⇔ RH; transport on right discs with explicit exponent; crossing discs force power growth; returns at zeros tail-bad; recurrence dichotomy; arbitrary finite smooth-head moments with explicit arithmetic cost [L].
- **(a)** A37.
- **(b)** Uniform target mass (B72); returns at off-line zeros (B83, B89); tail law at the Kronecker scale (B96); decay (B82).

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
- **Established [L/K]:** full-family receivers; depth corridors; two-lobe bound; cut crystal; sharp location; local pair cost; isolated-zero entry; explicit Hausdorff shifts; critical threshold chain and conductor resolution (S1).
- **(a)** A9.
- **(b)** Complementary-window sign, remaining-depth control (B6, B12, B101); all-height column (B46).

### ACT — Single shift
- **Path:** one shift pays every even compact profile → odd positivity → RH.
- **Established [L/K]:** receiver; `{2,3,4}` band; floors through `a_k`.
- **(a)** A7.
- **(b)** One shift uniform in profile (B44, B4).

### AIP — Incidence
- **Path:** complete reflected-prime/pole allocation → subexponential cost → RH.
- **Established [L/K]:** allocation; VK cost; capacity; channel law on gcd twists; non-gcd periodic twists coercive to the admissible period scale; conductor resolution at a fixed ratio (S1).
- **(a)** A9, A13.
- **(b)** `C_σe^{2σr}` cost (B45); the pole channel at every ratio (B6, B101).

### SC — Stokes / Witt–Krein
- **Path:** glued index `≤1`, bounded damped coupling, or undamped coupling plus ZAL → RH.
- **Established [L]:** `κ(φ_c)=κ+1`; damped bound ⇔ RH; undamped cone bound ⇒ AAL.
- **(a)** None that moves the route.
- **(b)** Arithmetic coupling bound; tensor loss (B39); B9, B11, B13.

### ACS — Castelnuovo–Severi
- **Path:** source energy → all-aperture Bézout → RH.
- **Established [L/K]:** block S10; source cone and RR; Bézout ⇔ RH; primitive `h¹` coercive for `a≤181/500`; Kloosterman purity; reciprocal quadric counts; column projections and Young projections at rank `≤4`; Toeplitz minors `≤200`; typical-height sign with Gaussian tails; frequency-packet average; degree-one Selberg classification; count laws of every hyperelliptic curve; Rosati height = Born rule.
- **(a)** A28, A41.
- **(b)** Source-energy sign (B40, B1); count or Rosati producer over ℤ (B78, B87); global trace (B85); mixed Young shapes at unbounded rank (B86); B65; B28.

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
| AIF | inner field, Szegő infimum, rigidity, Carleson measure, dilation quotient, causal certificate, forward map, restoring bound, `Ψ`-boundedness ⇔ RH, Selberg depth `O(T)`, Bohr profiles, insertion cone, columns, local onset field, Dirichlet–Hardy domain of `ζ(s+ε)` | none | B2, B57, B66, B82 |
| AAD | producers, peak law, half scale, compensated producer, quarter rate under RH, parity-neutral rate, rate = Mertens scale, extremal fakes sparse, Frobenius = factorial stencil, transport, slow returns right of the line | A30 | B15, B55, B89 |
| RAC | cut identity and kernel, unique fake, carry, ledger hierarchy, twin at every degree, parity exponent, exact parity identity, exchange law, bounded count with a new zero, maximal angle, extremal-law model, rotated relations | none | B67, B91, B92, B93 |
| TAPO | first return and brackets, precision law, heavy returns, tail–head decoupling, conditional moments, resonator mean, arithmetic mean values, recurrence dichotomy, tail of a return, head resolution, moving jet, Euler coordinates, comb | A24, A37 | B89, B96, B97, B100 |
| SPAL | shifted-product rigidity, collision cells, smooth × prime collision classes, count-distance rigidity, positive near-count model | none | B98, B103 |
| APD | Hamburger rigidity, FE-defect isolation, continuous/discrete/integer-norm/rational-prime one-offs, positive two-prime annihilators, zero relocation (mean spectra, Bohr, vertical trace, signed zero-mass density, first-gap negativity) | none | B80, B84, B103 |
| PTT | Bohr isometry, boxes, savings, rounded orbit, discrepancy, mixing time, hull with natural boundary, Ξ-current lift, certificates | A24 | B46, B100 |
| ASH | graph black holes, Krein law, Lax–Phillips rank two, one clock, KMS, rank barrier, bulk log-mean, count law at genus one, integer probes, Manin heights, throats, genus-two graph; ModularBootstrap: Narain partition, modularity, Mellin continuation, pole coverage, double-average main terms, Schwartz boundary, VK remainder, `¾` ⇒ RH, ceiling `¾` | none | B68, B71, B87 |
| CTH | count law at every genus (genus form, tower ⇔ crude bound), every hyperelliptic curve (RH in even degree), bielliptic Jacobian count, Born rules, boundary algebra, linear counts degenerate, Hecke conservation, second place of Hecke triangle groups, Farey reading and square-root Farey law, thermalization = strip, sharp shells, Rosati = Born rule, Tate limit over ℤ | A41 | B87, B95 |
| BHR | modular wave, metric, AdS₄ quotient, pulse regularity, echo train, ringdown = strip, two rates one exponent, horocycle Mellin formula and Zagier converse, Lax–Phillips semigroup, Maass cusp forms, discreteness, Weyl order, Rankin–Selberg continuation and decay, mean-square law, cusp-energy rates, Hecke multiplicity `≤2` | A26, A43 | B71, B109 |
| RIT | Mayer scattering, Krein square, Hecke dispersion, Hecke algebra Poisson on resonant states | none | B68, B70 |
| ACP | Mertens energy residues, positive Hecke annihilators and constant-mode cost, reflected-pair decay boundary, prime-pair source | none | B68 |
| SEL / Primon | degree-one classification, Euler rigidity; primon thermal Euler factors, Kesten–McKay densities, Green/Gaussian covariances, likelihood Hilbert space, principal series | none | B80 |
| MMD | cubic Gauss conversion, cubic Eisenstein series, nonzero residue, continued Fourier modes | A33 | B94 |
| AE, KPA | polar calculus, Tate law, naive heights, five currencies, torsion intersection, Stepanov over ℤ | none | B87, B88 |
| HHAC | isolated-prime rigidity, fixed-point obstruction, core Euler characteristic, core bouquet, torsion chord energies, weighted torsion operators, sharp weight of the prime row | none | B88, B106 |
| ESG | prime-height filtration, arithmetic barcode, `s`-independence of persistence, prime-weighted homology with `ℤ/2` torsion, two-prime block quotients | none | B106 |
| CSTW | canonical system, scalar flow, soft kick, Green corner, AC traces, `L¹` drift, sampling | A16 | B2, B3 |
| CHT | margin law, pinning, datum region, bands, local density, support density, cone PNT `5/6`, bounded extremals, edge law | A6 | B16 |
| VHR | height 67; window, Li, Hausdorff, heat, Jensen, PF, theta rungs | A1, A2 | none; decides no all-aperture statement |
| NGF | frequency, blow-up, gap laws, maximum principle, crystal and reality at critical scale | A19 | B24–B27, B47 |
| MZF | Selberg CLT, cameras, hyperbolic density, derivative law, rigidity, last scale, Möbius zero condensation | A18 | B57–B61 |
| FFP | `N_d` law, saddle region, stability dictionary, bulk blindness | A20 | B22, B23 |
| ADO | carrier repulsion; exceptional set of dimension zero; FE-pair flatness | none | B77 |
| APR | necessary length, filters, prefix amplification, collar laws | A18 | B48 |
| AKLT, ASRP | Stepanov over `𝔽_q` order, Nair lattice, integrality halves, stencil ceilings; AAL producers | none | B48, B83 |
| AGT | gauge torus, pole-subtracted spectrum, twin quarter floor | none | B50 |
| PBAP, W3 | blind positivity, exact null blind test | none | B18 |
| WVL | universal threshold, two-lobe, cut crystal | none | none beyond B1 |
| AHD / CACT | aliasing limits, Γ-liminf, polar capacity, far margin, collar Gårding, threshold chain with `R_polar`, continuum threshold growth, aperture exchange, top-window non-escape, splitting order, conductor resolution | A9, A13 | B6, B8, B101, B104 |
| CAF, TCS | two-atom, chains, Euler product, current, rank 14, first-atom Bessel/Gamma reserve, adaptive pair payment, fixed-head asymptotic, compact-core boundary, weighted Legendre kernels | A4, A5, A24, A42 | B19–B21, B102 |
| HWV, ADT | nerve of the star cover, sphere bouquet, `M(N)=−χ̃`, Redheffer gluing, effective depth laws | none | B10 |
| AK, Representation | column and rank-`≤4` Young projections, curve characters, Kloosterman traces, reciprocal quadric counts | A28 | B85, B86 |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ sign or budget on every window (`a*(ζ)=⊤`) | RW, EWU, OWU, ACT, CHMD, SZ, RN, ACS, AIP, SRT, SC, LI, TT (odd), HF, and the critical-curve branches of HF, SRT, AIP (reduced to the pole channel) |
| Σ continuation at small time and the theta head | ZCG, PTR, LA, GTA, XN, HCF, PA, TH |
| Π square-root precision and long moments | WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| Γ reflection and selection | PM, BAG, SEC, CDC, PCS |
| Missing source landing | APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF |
| Missing count, transversal | ACS, HF, PM, RW through windows |
| Critical-line input for the AAL half, transversal | BAG, JAS shell, SC undamped, WL sparse, ZCG one-off branch, RW polar ground energy |
| Dark range (Kronecker scale), transversal | every route at all heights; BAG and ZCG one-off branches; TH certificates; WD near-unit moments |
| Width axis (horizon observables), transversal | PM (horocycle, Farey, Lax–Phillips, Narain, cusp energy), MC (Farey), every VK-scale saving |
