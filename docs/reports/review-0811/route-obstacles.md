# Route obstacles — status quo

Scope: the 38 live route formulations, the 9 route candidates and the supporting programmes. For each route: the path, what is established, the obstacles that are **(a) just work**, and the obstacles that are **(b) open mathematics nobody has a solution to**.

**Corpus checkpoint:** commit `906b3c709c` plus the working tree of 2026-11-08. Working log: `logs/review-0811-status-research.md`.

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means an independent source mechanism or landing is missing. Formulations are not independent mechanisms: HJ is PA, BSH is CDC, FEL's BSY criterion belongs to CTF. A criterion, a source construction, a quotient equality or a scalar grade does not discharge an arithmetic sign or vanishing.

**Evidence.** `[L]` Lean source, integrated. `[S]` Lean source unfinished, unintegrated or uncommitted. `[K]` Lean with transitive axiom audit. `[D]` deduction, not a Lean theorem. `[N]` numerical, uncertified. `[C]` classical literature, not formalized.

**Strength.** RH; ≥qRH (zero-free half-plane, Lindelöf or ZAL); AAL (implies the asymptotic abscissa law); sub (strictly below quasi-RH and below AAL); method; indep.

**Labels.** `A*` just-work items and `B*` open problems are listed in full in [obstacles-summary.md](obstacles-summary.md). An A item is known mathematics, finite computation, effectivization, integration or assembly of proved pieces; `(unverified)` marks A items whose difficulty is not established. Wall labels Σ, Π, Γ refer to [walls-ledger.md](walls-ledger.md).

**Notation.** Windows `[−a,a]`. `W` Weil's form, `w_n=Λ(n)n^{−1/2}`. `a*(ζ)` onset aperture; `ℋ(c)` Hardy interval; `λ*(c)` best cone margin. `L=artanh r`, `Ψ=½log H₁`, `q=Ψ′`. `N_d` non-real root count of `R_d(Ξ)`. `Θ=½+zeroWidth`. **ZAL**: finitely many zeros beyond every positive depth. **AAL**: for every `h≥0`, finitely many zeros right of `½+h` means none. **B13 / finite stratum**: AAL at `h=0`, i.e. finitely many off-line zeros means none. `R=c⁸/log N`; `W₈(H)=∫H²e^{−8y}`; `Q₁=⌊(log N)^{13/32}⌋`; `R_c`, `R_pole`, `R_polar`, `R_high` the whole-space, primitive-hyperplane, polar-payment and high-conductor critical thresholds; `W=⨅_{A≥0}windowThreshold(A)`. `E_y` Euler head, `ζM_y` Euler tail. `R(y,η)` first return of the primes `≤y` at precision `η`. A **Weil tower** at base `ℓ` is the family `e^{ℓ(ρ−½)}` of modes; its **level sums** sample the Weil lag `Φ(νℓ)`; a set of levels is **thick** if it contains arbitrarily long runs arbitrarily far out. `primeDeviation(X)=(X−ψ(X))+X(Σ_{n≤X}Λ(n)/n−log X+γ)+O(1)`, so `Φ(L)=e^{−L/2}primeDeviation(e^L)`. `Q(a)` the Weil form on integer probes. `C_∞` the archimedean compensation (pole plane minus archimedean Lévy density). `𝒬_t` the Krein square of a graph black hole `(q,t)`.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ ZAL ∧ AAL for every zero configuration; ZAL ⇒ qRH; `qRH ∨ AAL` | [L]/[D] | one half is at least quasi-RH, the other sits below it |
| AAL ⇔ zero transport: every right zero `ρ` has, for every `ε` and height `T`, a zero with `Re>Re ρ−ε`, `\|Im\|>T` | [L] | AAL is vertical transport of zeros, the zero-level trace of recurrence |
| AAL ⇔ tail transport: at such points every Euler tail `ζM_y` vanishes and `\|ζ−E_y\|=\|E_y\|≥Π_{p≤y}(1+p^{−σ})^{−1}`; events produced by returns have density zero | [L] | AAL is the existence of rare events; density statements only bound them from above |
| ¬AAL ⇔ an isolated top: a finite nonempty layer on `Re=Θ>½`, every other zero left of some `Θ₂<Θ`; the FE reflects it to a bottom layer at the same heights | [L] | the failure of AAL is a finite-rank Weil datum riding on an infinite-rank remainder |
| No property depending only on zeros above a height, and no property depending only on zeros below a fixed height, decides the finite stratum | [L] | densities, pair statistics, gaps, counts and finite verification cannot touch B13 or AAL; the input must couple both scales |
| FE + order one + reality admit every finite top layer (`cosh(s−½)·Π quartets`) | [L] | an argument excluding a finite layer must use the Dirichlet series |
| Positivity, integer-norm or rational-prime Euler products, linear counting, continuation across `Re s=½` (continuous Beurling systems) and the reflection symmetry of the zero set each carry a finite top layer; AAL is invariant under `ξ(s+a)ξ(s−a)` | [L] | an AAL input cannot use the position `½` of the line and must turn the FE into transport in height |
| Curves: AAL holds for free (zeros periodic in height); a crude count at every level, ZAL, purity and unitarity are equivalent | [L] | both steps of the curve proof (Stepanov, power sums) sit inside ZAL; AAL is the periodicity of the Frobenius, which ζ lacks |
| Towers: an isolated top forces syndetic excursions of the level sums with gap the exceptional rank; no thick set of levels carries a bound below the top; density `1−1/k` sets do not self-improve (rank barrier) | [L] | elimination works at infinite rank on thick sets |
| For ζ: a prime deviation `O(X^{½+a})` along a thick set of geometric scales of one base, for every `a>0`, gives AAL; RH ⇔ ZAL ∧ thick `O(X^{½})` | [L] | the curve proof's elimination step exists over ℤ; its inputs are a thick crude count and ZAL |
| Finite stratum: finite index of `K_ζ` ⇔ finite index on one two-prime lattice ⇔ finitely many off-line zeros ⇔ bounded heat count ⇔ RH above some height; under it one non-blind prime tower decides | [L]/[K] | B13 turns every finite-stratum receiver into an RH receiver |
| RH ⇔ `a*(ζ)=⊤` ⇔ `λ*(c)→0` ⇔ two-site PD ⇔ `Ψ` locally bounded | [L] | every window route measures one number |
| `0<R_c≤R_pole=R_high=W`, `W=⊤` ⇔ RH; positivity on `ℝ^N` = primitive hyperplane + pole channel; below `W` the pole channel decides; `R_c=W` ⇔ the pole channel pays at every `R<W` | [L]/[S] | the critical curve is the window plus one channel |
| The adaptive theta head has leading term `\|ζ(½+ib)\|²` up to `O(\|ζ(½+ib)\|\|b\|^{−½}+\|b\|^{−1})` | [L] | the theta sign is decided near the critical zeros of ζ |
| Off the diagonal, Weil's form = archimedean compensation `C_∞` + Abel limit of positive torsion energy of `ℙ¹_ℤ`; `C_∞` changes sign; the diagonal must be renormalized; renormalization carries no sign; damping is lossless | [L] | a count at the critical weight must be a damping of a positive object, not a renormalization |
| RH ⇔ `Q` on integer probes is the Tate limit of an `ℕ`-count; on curves the defect is itself a count of points; over ℤ nothing plays that role | [L] | the count wall is the absence of a point count |
| RH ⇔ a standard-form von Neumann algebra with rational dilations, `JU(r)J=U(r^{−1})`, natural-cone form `Q`; internal realizations collapse to the centre (Tomita) | [L] | the partner involution is not internal modular conjugation |
| Every horizon observable reads the zero-free strip on the width axis; smooth horocycles thermalize at `y^{½}exp(−√(−log y))` unconditionally; one sharp shell at the RH rate ⇔ RH ∧ Möbius × circle-remainder cancellation | [L] | horizon receivers carry the VK saving and no more |
| Necessary near-unit mollifier length `exp(c log²T)` = Euler mollifier over primes `≤c log²T`; conditional tail laws stop at the Kronecker scale; long mean values are collision counts | [L] | the near-line wall is the dark range |
| Farey discrepancy, `M(N)`, nerve and core Euler characteristics are one number; prime-vertex self-maps homotopic to the identity have exactly the primes as fixed points, with local indices unbounded below | [L] | topology carries `M(N)` only as a signed count |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | primes pay the archimedean–polar deficit by sign | format exact on every window; size payment ends before half-width `21/40` |
| M2 Calibration | window cones, blind positivity, margin | cone pinned at `e^{−c/1104}`; cone points obey PNT `5/6` on the window's range; sign open |
| M3 Canonical flow | `L,q,Ψ` of the Weil chain | exact to contact; RH ⇔ `Ψ` locally bounded |
| M4 Reflection | Krein/Lewis positivity, Hecke dispersion, ringdown, Lax–Phillips, horocycles, Born rules, standard forms | FE = nondegenerate Born rule; positivity of the Born rule = damping; internal modular conjugation collapses; flux sign open |
| M5 Square-root cancellation | smoothed prime counts, long moments, Farey discrepancy | receivers closed; estimates open |
| M6 Continuation | heat, cosine, Jensen | typical heights closed; small time at all heights open |
| M7 Zero geometry | cameras, Blaschke factors, inner field | isolated zeros at rate 2; depth `O(T)`; clusters and `o(T)` open |
| M8 Recurrence and transport | zero transport, tail transport, almost periodicity, partial returns | AAL ⇔ transport; uniform almost periodicity gives AAL; ζ lacks it in the strip; existence of rare events open |
| M9 Production | integer stencils, integrality, Stepanov over ℤ | rate = Mertens level; Stepanov over ℤ reaches Chebyshev |
| M10 Count | nonnegative function with quadratic Tate limit | every hyperelliptic curve (a point count) [L]; over ℤ no point count |
| M11 Orbit at finite time | prime phases at one height; first return; returns freeze smooth polynomials | absolute savings; dark at the Kronecker scale; prime orbit has one fixed point |
| M12 Critical compactness | Gårding, Γ-liminf, threshold law, pole channel | critical curve = window + pole channel |
| M13 Topology of the prime complex | homotopy, persistence, fixed points, singular indices | classified, `s`-independent; localization to the primes with unbounded indices |
| M14 Thermal averaging | primon gas | Euler factors at real points `>1` |
| M15 Infinite-rank elimination | Weil towers, exceptional rank, thick sets, well-foundedness | window theorem, rank barrier, Hasse–Weil principle at infinite rank [L]; inputs (thick crude count, ZAL) open |
| M16 Intersection on half-products | 𝔽₁-zonotope surface, `ℙ¹_ℤ` torsion orbits, Frobenius graphs | off-diagonal assembled [L]; diagonal is the sign |
| Amplifiers | Diophantine repulsion, integrality, isolation, Turán | amplify a certificate, produce none |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve

Routes: HF, SRT, AIP, ACS (atomic), SC, CHMD (index). Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF.

Established:
- Full tilted-spline matrix PD for `1≤c≤(log N)^α`, `α<1/8` [L], and through `c≤2K₀(log N)^{1/8}` with complete Schur payment [K].
- Every compact C² profile: energy `≥ae^{−Bc}‖x‖²` on conductors `≤N^θ`, `θ<¼`, `c≤b log log N` [L].
- **Threshold chain [L].** `0<R_c≤R_c^{PSD}`, `R_c≤R_pole≤R_high=R_high^{PSD}=W≥c₀e^{6a*(ζ)}`; all thresholds `=⊤` ⇔ `a*(ζ)=⊤` ⇔ RH. `R_polar≥c₁e^{c₂a}` for `a≤a*(ζ)`. Below `c₀e^{6a*}` every nonzero nonpositive vector charges both the low packet `V_{Q₁}` and a top window of length `≤⅛log(R+1)+C₀`.
- **Primitive hyperplane [S].** `R_pole=W`: a nonpositive primitive sequence has a nonzero compact collar profile, contradicting the continuum pencil below `W`.
- **Pole channel [L].** Positivity on `ℝ^N` is positivity on the primitive hyperplane plus positivity on `x+w`, `0≠x` in the polar line, `w` primitive. Below `W` the complete matrix is PD iff its pole channel is; `R_c=W` iff the pole channel pays at every `R<W`.
- **Charged profiles [S].** Bounded Weil energy, eighth mass and joint normalization with the pole coordinate give strong subsequential limits of unit joint mass; the polar matrix row converges to an explicit sampled profile on each fixed terminal fraction; the polar source is continuous in the exponential norm; payment at a larger ratio leaves explicit `W₈` and pole reserves at every smaller ratio; polar payment at every window of a strictly larger ratio excludes nonzero charged limit profiles.
- **Conductor resolution [L/S].** Physical tearing has Schur ratio `→4/13`; conductor-adapted splitting decouples; a fixed Schur multiplier is absorbed by deep, intermediate and prefix reserves; every low-packet cross term except the literal polar collar pairing costs an arbitrarily small packet diagonal; the low packet retains its exact scalar pole energy; whole-space collar Gårding and the far-energy bridge share one decomposition and lose only a multiple of the scalar polar coordinate square.
- **Low packet [L].** Payment at `R` on `[−A,0]` ⇒ `R≤windowThreshold(A)`; payment at every ratio on windows of length `→∞` ⇒ RH.

Structure [D]: at a fixed ratio everything except the pole channel is paid or reduced to the window; the pole at every ratio is RH. No sub-RH content remains at the critical curve; `R_c=W` is architectural.

| | Obstacle | Strength |
|---|---|---|
| A9 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | — |
| A13 | Near-gcd charges and periods beyond `M₀(N)` (unverified) | — |
| A44 | Charged Γ-liminf for actual nonpositive whole-space sequences: from fixed-fraction polar-row convergence to the full physical pairing; integration of the `[S]` polar-row chain (unverified) | — |
| B6 | Full-space sign eventually at every `K`; every critical threshold `=⊤` | RH |
| B8 | Head thresholds for every `d` | RH |
| B101 | Low-packet polar payment at every ratio on growing windows | RH |
| B104 | Pole-channel payment at every `R<W`, equivalently `R_c=W` | method |

### S2. Window tower and canonical flow

Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT (odd), HF, ACS, SRT, SZ. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF.

Established [L]: precontact de Branges chain, canonical system with `H₁H₂=1`, flux, sampling bases; `L′=q−sinh 2L`; traces, `r`, `Ψ` absolutely continuous; `q_y→q` in `L¹`; restoring bound `|L(x)|≤artanh e^{−2(x−c)}+2osc Ψ`; RH ⇔ `L` locally bounded on precontact intervals ⇔ `Ψ` locally bounded; off RH `L` is unbounded above every base; soft prime kick; Born model; causal certificate; Szegő threshold; free reflection coordinates; forward-map tangent; cone pinning, margin ceiling, bounded extremals; cone points carry local density `1+O(e^{−a})`, positive support density and PNT `5/6` on `X≤e^{2c−3}`; datum region `⊆{β≤1}`; exact null blind test; floors `(1/20000)/2^k` through `a_k<0.3621`; window naive heights exist iff positive; Tate dimension one exactly through `log 5`. Spline orbit: `|W(B,B(·−t))|≤Ke^{σt}` ⇔ width `≤σ`; RH ⇔ Hasse–Weil along the orbit of the cubic spline.

Structure [D]: the window tower is one local boundedness statement for one real function; the margin ceiling forces `m≳e^{2a}`, above the Born bound.

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

Established [L]: `Ω_ψ(a,X)` as a sum over zeros; on-line terms nonnegative; depth cost `≤(16/9)δ²a⁴‖ψ‖²`; RH ⇔ `Ω≥0`. Typical-height sign at `A=δlog T/(64M²)` for every shaped test; bad heights Gaussian-tailed, measure `≤T^{1−1/(64K)}` at `A=K log log T`. Weil's form is the average of its frequency packets. Visibility, cut crystal, sharp location at `λ>1`.

Structure [D]: all-height sign stops at the size curve `a≈log log X`; past it the input is the short-sum barrier (S11). Typical-height statements are asymptotic in the sense of S9 and cannot decide B13.

| | Obstacle | Strength |
|---|---|---|
| — | none that moves the route | — |
| B28 | Local Weil positivity at fixed `λ>0` on density-one heights | sub |
| B46 | Proportional saving at length `(log X)^{2K}`, all heights | sub |

### S4. Continuation and nodal geometry

Routes: ZCG, LA, PTR, HCF, PA, GTA, XN. Programmes: NGF, FFP, ADO, RHTower heat.

Established [L]: collision criterion; horizon `(6600/9991+ε)/log X`; density-one `Λ_Xlog X→0`; crystal and reality at the critical scale; sharp depth law for isolated simple zeros; `N_d` law and inner-root reality; cosine Laguerre above VK; nonrepelling values of dimension zero; maximal-angle law; one-sided Gaussian prime ceiling at every rational height ⇔ RH; ZAL ⇔ LH ∧ every cosine-shift level of ξ has finitely many non-real zeros; high-collision counts ⇔ ZAL. The extremal inequality alone has a polynomial model.

| | Obstacle | Strength |
|---|---|---|
| A19, A20 | Heat horizon toward its method floor; Jensen rung (unverified) | — |
| B24 | Collisions at arbitrarily small time, all heights | RH |
| B25 | Frequency `<1` at every collision | RH |
| B26 | Arithmetic input distinguishing `Φ` among `Φe^{−τx²}` | method |
| B27 | Runs of `k` simple critical zeros, every `k` | sub |
| B47 | Multiplicity `o(log X)` by a non-size input | sub |
| B22, B23 | Outer roots of `R_d(Ξ)`; `N_d` bounded | RH; ≥qRH |
| B92, B93 | Rotated relation with coefficients of the size of `Q`; contradiction beyond the extremal law | RH |

### S5. Near-line geometry and long moments

Routes: WD, CTF, MC, TG; census. Programmes: CDG, APR, MZF, AIF, IWT.

Established [L]: Selberg CLT and prime field; cameras, hyperbolic density theorem, `N(ρ)=exp(−ΣG)`; box budgets and Carleson measure; eight-way log-mean equivalence, Abel form ⇔ depth density `o(T)`; Selberg's mollifier gives off-line first moment `≤(67/1000)V`, depth `O(T)`, bounded inner field at infinity; squared off-line depth moment `o(V)`; necessary-length laws; an Euler mollifier with a near-unit second moment uses every prime up to `min(1/24,1/(14K₀))log²T/log 4`; last-scale floor; one-window and positive-proportion forms; Möbius zero condensation; dilation identity; Fejér-weighted long mean values of Dirichlet polynomials of any length are collision forms, of exact order `N²` past the height.

Structure [D]: the necessary length is that of an Euler mollifier over primes up to `≈c log²T`, where prime phases become absolutely non-aligned; the near-line wall is the dark range. Past the height a long mean value has no diagonal main term; its main term is a binary prime statement in short multiplicative ranges.

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

Established [L]: band ⇔ classical criteria; integer lag; entry filters; length–precision law; gauge exponents `[Θ,1]`; twin quarter floor; Nair lattice; Stepanov over ℤ = integrality floor + Nair ceiling; producers `c=μ∗h`; floor `c/(√K(1+log K))`; rate `K^{−a}` ⇒ `Re ρ≤1−a`; all `a<½` ⇒ RH; RH gives `a<¼`; Frobenius over `𝔽_q[T]` = Carlitz factorial stencil of rate 0; parity-neutral producers at every rate; extremal fakes with `≤K` atoms; cut kernel = zeros; finite-energy kernel mass annihilation ⇒ RH; exact identity pins `λ`; exchange law; count-distance rigidity; bounded count with a new zero; Farey discrepancy ⇔ RH; `M(N)=−χ̃` of the nerve; cubic Gauss conversion with nonzero residue at `4/3`.

| | Obstacle | Strength |
|---|---|---|
| A21, A30, A33 | Chowla [C]; best RH exponent in `[¼,½]` (unverified); cubic residue Fourier coefficients [C] | — |
| B48 | Deciding input at square-root precision; a crude zero-localized prime count at every level | RH |
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
- Scattering: resonance ⇔ `ζ(2s)=0`; `Q=2Re[WH,WH]`; `D_s≤0`, zero iff `Re s=¼`; Hecke dispersion `V_p`; Hecke operators diagonal on Eisenstein; the Hecke algebra has a positive Poisson measure on truncated resonant states for every `Re u<0`; positive `T₂,T₃` polynomials annihilate any finite resonance set.
- Horizon: modular horizon = quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)`; ringdown in the modes of zeros; pulse metrics regular across the horizon.
- Width axis: for `0<δ≤¼`, zero-free `Re ρ≤1−2δ` ⇔ pulse decay `e^{−(δ−ε)τ}` ⇔ horocycle rate `y^{½+δ−ε}` ⇔ smoothed Farey count rate; RH ⇔ `y^{¾−ε}` ⇔ universal Lax–Phillips decay `e^{−t/4}`. Smooth profiles thermalize unconditionally at `y^{½}exp(−√(−log y))`, hence `o(y^{½})` and every logarithmic power past `y^{½}`; ceiling `y^{¾}` (Hardy). Sharp shells thermalize at a log-free `O(√y)`; one shell at `y^α` forces `Re ρ≤2−2α`; one shell at the RH rate ⇔ RH ∧ `Σ_{d≤X}μ(d)E(X/d)=O(X^{½+ε})`.
- Cusp channel: Maass cusp forms exist, discrete spectrum, `N(Λ)≍Λ`; Rankin–Selberg continuation with FE and `e^{−π|t|}` decay; Rankin's bound `|ρ(n)|≪n^{½−δ}`; Rankin–Selberg Euler product of normalized Hecke sequences, diagonal = `ζ(s)L(Sym²g,s)/ζ(2s)` [L]; for a Hecke eigenform, `Σ|ρ(n)|²|n|^{−s}` and `∫|g|²E(s−½)` as that Euler product on `Re s>2` [S]; cusp-energy rate `y^{½−ε}`, `y^{¾−ε}` under RH, rate `y^α` forces `Λ_g(ρ/2)=0` for `Re ρ>2−2α`.
- Narain AdS₃ source: literal partition, modular invariance, Mellin continuation retaining every arithmetic pole; exact main terms; central orders classified (one exceptional height `Y*=exp(2−4Re ξ′(1))`); boundary moment jets; remainder with exactly the VK saving at a target-independent exponent; `¾` ⇒ RH; every exponent `>¾` impossible.
- Graphs: black holes with flux, unitarity, Hecke; Krein flux law; Born rules (nondegenerate ⇔ FE, positive ⇔ damping); boundary algebra (positive state ⇔ damped; `C*` blind); genus-two graph with FE for every `q`, all-level count law iff `q≤3`.
- Standard forms: right wedge strictly spacelike from every `SL₂(ℤ)`-image of the left wedge; the boost-commuting wedge exchange fixes cusp height; geometric KMS period `2π` against arithmetic strip period `1`; `GL₂(ℤ)` symmetries fix pseudo-Eisenstein series; Tomita central collapse; graph standard-form partner representation iff `t²≤4q`; RH ⇔ a standard form with `JU(r)J=U(r^{−1})` and natural-cone form `Q` (or Tate limit `Q`).
- Primon: thermal means are Euler factors of `ζ(2e^β+1)`.

Structure [D]: wave dynamics, unitarity, Hecke, KMS, `C*`, internal modular conjugation, FE at genus two and first-level counts leave damping open; the separating law is a positive count of full rank. Every modular-horizon observable reads the poles `ρ/2` of one Eisenstein series on the width axis.

| | Obstacle | Strength |
|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | — |
| A43 | Integrate the eigenform Rankin–Selberg series and transport the identification `Λ_g=` completed `ζ(s)L(Sym²g,s)/ζ(2s)` from `Re s>2` to `ℂ` | — |
| B68 | Independent `D_s≥0`, nonnegative Krein flux, integer-probe sign or all-zero dispersion bound | RH |
| B69 | Positive physical carrier | producer |
| B70 | Lower bound for `V_p` from the carrier | sub |
| B71 | Universal decay `e^{−t/4}` / horocycle, Farey or Narain rate `y^{¾−ε}` | RH |
| B87 | A count for `Q` over ℤ | RH |
| B109 | Rankin–Selberg noncancellation: `Λ_g(ρ/2)≠0` at every off-line zero for some `g` | indep. |
| B113 | Möbius × quarter-disc remainder `Σ_{d≤X}μ(d)E(X/d)=O(X^{½+ε})` (sharp shells) | beyond RH |
| B114 | A positive-energy (half-sided) realization of the partner involution | producer |

### S8. Index and support

Routes: HKT, AKLT, SC, RIT, CWS through HF, ACS; LA; ZCG heat count. Established [L/K]: `κ(φ_c)=κ+1`; finite index ⇒ Lindelöf; `κ∈{0,∞}` under escape, mixing or decay; window index counts critical lengths; `sup_dN_d` = off-line multiplicity; `K_ζ^n` PD ⇔ RH; TFAE: `κ(K_ζ)<∞` ⇔ finite index on one two-prime lattice ⇔ finitely many off-line zeros ⇔ bounded non-real heat count ⇔ RH above some height; under finite support, RH ⇔ one non-blind prime tower PD; eventual slice positivity ⇔ finite off-line support; finite off-line support ⇒ ZAL.

Structure [D]: the finite stratum is one object read many ways. No asymptotic property and no finite verification decides it [L].

| | Obstacle | Strength |
|---|---|---|
| B12 | Index ceiling uniform in resolution | ≥qRH |
| B13 | Finitely many off-line zeros ⇒ none | sub |
| B23 | `N_d` bounded | ≥qRH |

### S9. Abscissa laws, transport and one-offs

Routes: BAG, JAS shell, SC undamped, WL thick runs, ZCG one-off branch, RW polar ground energy. Programmes: AKLT, ZCG, IWT, AIF, APD, AAD, RAC, PTT, TAPO, SPAL, ACP.

Established [L unless marked]:
- Split: RH ⇔ ZAL ∧ AAL for every configuration; AAL ⇔ eventual-to-global abscissa bounds ⇔ zero transport ⇔ tail transport; ¬AAL ⇔ isolated top; symmetric shifts preserve AAL.
- Two-scale theorem: every property depending only on zeros above a height, or only below a fixed height, that holds on a pure configuration holds on one with ZAL and ¬AAL at `h=0`.
- Free AAL: vertically recurrent configurations, zero sets of exponential polynomials, curves, configurations with a vertical period; zeros of strip almost periodic functions recur with bounded gaps (Bohr); Dirichlet series uniformly approximated by partial sums on closed strips obey AAL there.
- Countermodels: `cosh` models (FE, order one, reality, any finite layer); one reflection pair; continuous Beurling systems continuing across `Re s=½`; integer-norm and rational-prime one-offs with linear counting; positive two-prime and Hecke annihilators of any finite zero set, of arbitrary multiplicity at nonconstant mass arbitrarily close to 1, harmonic packets of `m` points forcing mass `≥m`.
- AAL producers: not-attained top; bounded lag on a progression; lag excursions of lower Abel density zero; subexponential polar ground energy; one prime-window grid; log-dense integer lag; twisted plateau; JAS dressed, typical and shell positivity; bounded towers; one bounded cone; weak recurrence; infinitely many zeros near each right zero; slow aligned returns on right discs; a thick lag bound at one base; a thick prime-deviation bound `O(X^{½+a})` ∀`a>0`.
- Tower form of ¬AAL: syndetic lag excursions at every base with gap the exceptional rank; a single top pair `Θ±iγ` makes the lag large at every level at base `π/γ`.
- Transport: discs crossing `Re s=½` force `|ζ|≥cτ^b`; right discs carry the AAL receiver; a partial return transports a zero or forces an exponentially deep relative small value on the omitted arc; an Euler head approximating a central zero on all but an angle `δ` needs prime mass `≳1/δ`.
- Tail: zeros of ζ are zeros of `ζM_y` at every cut; returns at right zeros are tail-bad, density zero; nonvanishing targets return at positive density.

Structure [D]: AAL needs a Dirichlet-series input that couples both scales and turns the FE (a height reflection, which keeps heights in the zero set) into transport in height. ¬AAL is a finite exceptional layer inside the strip, an exclusion problem of Landau–Siegel type.

| | Obstacle | Strength |
|---|---|---|
| A37 | Resonator mean of `\|ζ\|²` with resonators growing below the Kronecker scale (unverified) | — |
| A47 | Explicit window constants of the IWT tower theorems for one top quartet (rung `k=1` bookkeeping) (unverified) | — |
| B83 | AAL | sub |
| B89 | A bounded aligned return at each right zero on a right disc | sub |
| B96 | Conditional law of the Euler tail at the Kronecker scale | sub |
| B13 | Finite stratum | sub |
| B84 | Smallest FE defect carrying a one-off | method |
| B103 | Positive discrete Euler products with linear counting, continuation across `Re s=½` and an FE: AAL? | method / sub |
| B110 | Thick crude count: `primeDeviation(X)=O(X^{½+a})` on a thick set of geometric scales of one base, every `a>0` | AAL |
| B111 | Linear AAL: `Θ−½≤C(Θ∞−½)`, i.e. finitely many zeros right of `½+h` ⇒ none right of `½+Ch` | sub |
| B112 | A mechanism turning the FE into vertical transport of zeros | sub |
| B72 | Cutoff-uniform target mass | RH |
| B82 | Inner-field decay | ≥qRH |

### S10. Count and effectivity

Routes: ACS, HF, PM integer probes; RW through window naive heights. Programmes: AE, CWS, LST, KPA, ASH, CTH, RIT, SOSZ, RIAC, HHAC.

Established [L]: polar surface calculus; Tate law and Tate principle in both directions (a degree-two homogeneous function is the Tate limit of an `ℕ`-count iff it is `≥0`); five currencies; theta `h⁰` with exact RR; Künneth `h¹` split; source cone and all-aperture RR; Bézout ⇔ RH. Curves: integral Castelnuovo–Severi defect is the Tate limit of a count iff unitary; on a true hyperelliptic curve the defect of every integral class is itself a natural number, an integer polynomial in `q` and the point counts. Over ℤ: `Q(a)=Σa_ma_nC(log(m/n))`; Hecke isometry of `Q`; RH ⇔ `Q` is the Tate limit of an `ℕ`-count; linear counts degenerate; Hecke gives conservation only. Surface of Spec ℤ: Frobenius graphs on the 𝔽₁-zonotope surface meet in `m+n`; the zonotope defect is `2Σ_k(Σ_{n>k}a_n)²` (Hodge index by counting); Weil's off-diagonal = one 𝔽₁-cusp with its jet tower plus gcd-twisted torsion intersections on `ℙ¹_ℤ`; point count `Λ(n)+1+1/(n²−1)` fails Hasse–Weil for every finite genus; smoothed Frobenius graph pairs pass Hasse–Weil ⇔ RH [S]; no metric on `ℙ¹_ℤ` carries the jets; the archimedean place is not toric; the primes are jumps of the Hecke kernel; off-diagonal Weil = `C_∞` + Abel limit of positive torsion energy. Torsion forms: raw positive; renormalized limit compact self-adjoint on `ℓ²(n^δ)`, indefinite with definite subspaces of every dimension of both signs surviving any finite constraint or finite-rank correction; Hilbert–Schmidt iff `δ>½`. Critical weight: damping lossless; renormalization carries no sign.

Structure [D]: on curves the count comes from point counts before any sign is known; over ℤ the off-diagonal is assembled from existing half-products, and the sign sits in the diagonal, which no half-product supplies and which can only be renormalized. A count at the critical weight must be a damping of something positive.

| | Obstacle | Strength |
|---|---|---|
| A28 | Reciprocal-quadric traces = vanishing-cycle Frobenius traces (unverified) | — |
| A41 | Count law for every curve over `𝔽_q` (Bombieri–Stepanov), first case plane quartics [C] | — |
| A48 | Hasse–Weil test of smoothed Frobenius pairs at verified scales (window rungs) | — |
| B87 | A nonnegative count on integer probes, defined without `Q`, with Tate limit `Q` | RH |
| B88 | A counterterm-free damping presentation of Weil's form: positive kernels whose limit is Weil's kernel on and off the diagonal (off-diagonal: `C_∞` + torsion energy) | RH |
| B95 | An abelian group with Hecke endomorphisms whose trace form is `Q` | producer |
| B65 | Genus upper law; logarithmic Serre duality; first Epstein real zero | indep. to sub |

### S11. Prime orbit at finite time

Routes: BAG, TH, SRT, RW, ZCG carriers, every route at the all-height wall. Programmes: PTT, TAPO, SPAL, IWT.

Established [L]: every window of length `exp(10y√(log y·log log y/δ))` enters every `δ`-box on primes `≤y`; savings `8/(10⁹L⁶ℓ⁴)` at length `48L²ℓ`, `t^{−δ}` at `L^A`; no cancellation below `c log T` at some height; first return bracketed at every precision; bounded-harmonic-defect return `≥exp(c(log N)^{3/2}/log log N)`; RH bracket at precision `≍y^{−9/2}`; proportional saving ⇔ no early heavy return; conditional Gaussian tail below the Kronecker scale; smooth × prime collision costs; at a `δ`-return of `P` every `P`-smooth `n` has `|n^{−it}−1|≤Ω(n)δ`, so Dirichlet polynomials on `P`-smooth integers freeze, and `J` moment conditions force approximate vanishing to order `J` at every return; two distinct primes have no common exact return (one fixed point).

Structure [D]: between `log t` and `exp((log t)^{2/3})` the Taylor degree of `t log(n+h)` exceeds `(log length)²`; required saving at the size curve `≈εL/ℓ`, proved `≈L⁻⁶`. The archimedean Frobenius substitute exists only approximately.

| | Obstacle | Strength |
|---|---|---|
| A24, A37 | Certified scans and brackets; growing resonators (unverified) | — |
| B46 | Proportional saving at length `(log X)^{2K}`, all heights | sub |
| B97 | Constant-precision first return: `log R(y,δ)≥y^c` for fixed `δ`, every heavy subset | sub |
| B100 | A saving for `t log n` on moving block families past Vinogradov's degree | sub |
| B15 | Past VK | sub |
| B20 | Oscillation of the actual amplitude with the height | RH |

### S12. Topology of the prime complex

Routes: MC (nerve, Redheffer), HF and ACS through the coprime stratum. Programmes: HWV, ADT, ESG, HHAC, RIAC.

Established [L unless marked]: `det R_N=M(N)=−χ̃` of the prime-star nerve; squarefree prime complex ≃ wedge of spheres; `χ̃=Ω±(√N)`; RH ⇔ `χ̃=O(N^{½+δ})`; persistence: bar `[m,2m)` for every odd squarefree `m`, isomorphic for every `s∈ℂ`; prime-weighted homology with `ℤ/2` classes, two-prime block quotients compute the core over every ring; finite face realizations have finite singular homology with Euler characteristic the alternating face count [S]. Prime-vertex dynamics: a face-preserving, cutoff-natural self-map homotopic to the identity has fixed points exactly at the prime vertices; each prime vertex has a compact isolating block with exit ≃ upper link; for `p≤N≤p³` the relative singular index is `1−#{q>p prime: pq≤N}`, unbounded below. The connected core is a bouquet of odd-squarefree composite spheres with augmented Euler characteristic `M(N)+#primes(N/2,N]`. Completed prime boundary: bounded and closed extension of `Σp^{−s}a_p` on `Σp^δ|a_p|²` iff `2Re s+δ>1`; imaginary Dirichlet gauges are unitary in every exterior degree, so the completed boundary relation depends only on `Re s`.

Structure [D]: Lefschetz localization of `χ` to the primes is exact, and each local index is a Möbius sum over integers with least prime factor `p` (a Buchstab decomposition of `M(N)`); square-root cancellation must occur across primes among indices of size `≍N/(p log N)`. Homotopy, homology, persistence and the completed boundary graph do not see `Im s`.

| | Obstacle | Strength |
|---|---|---|
| A46 | Local singular indices of prime vertices beyond the cubic cutoff `N>p³` (unverified) | — |
| B10 | Top coprime stratum | RH |
| B106 | A natural relative pair `(X,A)` with `χ(X,A)=M(N)`, or a natural self-map or action whose signed fixed-point indices localize to `O(N^{½+ε})` | RH (≥qRH at `θ<1`) |
| B88 | Damping presentation of the torsion and archimedean parts at the critical weight | RH |

### S13. Infinite-rank elimination

Routes: WL (thick runs), ZCG (tower form), ACS (thick curve counts), BAG, JAS. Programme: IWT.

Established [L]: Weil towers and level sums; the FE acts on level sums only through `S(−ν)=conj S(ν)`; exceptional-rank window theorem; thick sets self-improve; price of hiding a top `≥εR^{M+1}` in trace norm; rank barrier (roots-of-unity towers, density `1−1/k`); infinite-rank Hasse–Weil principle (well-founded outer part + thick crude bound ⇒ only the critical layer visible); curves self-improve on thick sets; ZAL ⇔ well-foundedness of the tower; isolated top ⇒ window data; towers of ζ with lag weights `1/(q(1−q))`, every point visible; thick lag bound ⇒ AAL; RH ⇔ ZAL ∧ bounded lag on a thick set ⇔ ZAL ∧ thick `O(X^{½})` prime deviation; calibration battery: golden fake fails the crude count on every thick set, the integer-norm one-off satisfies ZAL and violates AAL. Without well-foundedness the principle fails (Wolff configurations vanish on progressions at one and two bases).

| | Obstacle | Strength |
|---|---|---|
| A47 | Explicit rung-`k=1` window constants (unverified) | — |
| B110 | Thick crude count for ζ | AAL |
| — | ZAL (finitely many zeros beyond each depth) | ≥qRH |

### S14. Intersection theory on half-products

Routes: ACS, HF, PM count branch. Programmes: SOSZ, AE, RIAC, HHAC, CTH.

Established: see S10 (surface of Spec ℤ) [L/S].

| | Obstacle | Strength |
|---|---|---|
| B87, B88 | Count; counterterm-free damping presentation of the diagonal | RH |
| B115 | A carrier for the jets of the trivial zeros (rank `≥3` on coprime orders; neither toric nor Arakelov on `ℙ¹_ℤ`) | producer |

## 3. Live routes

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy, one-sided `Φ`, or ZAL plus a thick `O(√X)` prime deviation → RH.
- **Established [L/K]:** bounded endpoint energy ⇔ RH; integer lag ⇔ RH; `Ω±(√n)`; first-band abscissa `2Θ`; gauge exponents `[Θ,1]`; subtracted lag ⇔ ZAL; lag excursions of lower Abel density zero ⇒ AAL; log-dense integer lag bounded above ⇒ AAL; one-sided Gaussian prime ceiling at every rational height ⇔ RH; RH ⇔ ZAL ∧ `primeDeviation=O(X^{½})` on arbitrarily long late geometric runs; thick `O(X^{½+a})` ∀`a` ⇒ AAL.
- **(a)** A30.
- **(b)** Bounded endpoint energy (B49); half-power at the trivial gauge (B50); deciding input (B48); thick crude count (B110); ZAL; past VK (B15).

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every radius → RH.
- **Established:** blocks S2, S3; RH ⇔ `Ψ` locally bounded; cone nonempty ⇔ RH; relative compactness ⇔ RH; naive height on every window ⇔ RH; RH ⇔ ZAL ∧ subexponential polar ground energy; cone points obey local density and PNT `5/6` on the window's range; window positivity at `a` gives depth-`¼` exclusion to height `e^{a/K}` and `R_polar≥c₁e^{c₂a}` [L].
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
- **Established [L/K]:** damped energy ⇔ RH; one-point form; VK Hilbert energy; Möbius zeros condense on `Re s=Θ`; gauge genericity; producer rates; parity exponent = zero abscissa; exact identity pins `λ`; twin quarter floor; Farey discrepancy ⇔ RH; `M(N)=−χ̃` of the nerve and the core Euler characteristic minus `#primes(N/2,N]`; localization of `χ` to prime vertices with indices unbounded below; persistence `s`-blind; cubic branch with nonzero residue at `4/3`.
- **(a)** Chowla [C] (A21); cubic residue Fourier coefficients (A33); prime-vertex indices past the cubic cutoff (A46).
- **(b)** Trivial-gauge cancellation or zero exclusion for `M_X` (B50); deciding input (B48); past VK (B15); rational transfer (B94); topological localization (B106).

### TT — Theta tail / Wold
- **Path:** weighted endpoint energy bounded for each `0<t<½` → RH.
- **Established [L]:** Wold residual VK; `D_t+Q_t/2≥0`; boundedness ⇔ RH; uniform bound on a shrinking band.
- **(a)** None that moves the route.
- **(b)** `C_t` at every fixed `t` (B34); odd branch B4.

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted or sublinear root height → RH.
- **Established [L]:** block S4; infinitely many unshifted degrees ⇔ RH; inner roots real; `N_d≤300√(d log d)`; `sup_dN_d` = off-line multiplicity.
- **(a)** A20; A1.
- **(b)** Outer roots (B22); `N_d` bounded (B23) gives finite support only, RH once B13 is known.

### ZCG — Zero-configuration geometry / heat descent
- **Path:** half-Gaussian source → no positive-time collision → RH; tower and transport branches for AAL.
- **Established [L]:** blocks S4, S5, S9; abscissa laws of configurations (purity = ZAL ∧ AAL, AAL = zero transport, curves and exponential polynomials satisfy AAL, curve template split, one pair violates AAL at `h=0`, ¬AAL ⇔ finite layer, two-scale theorem, almost periodic zeros recur); one-off jets; maximal-angle law; horizontal jet gain ceiling = isolation gap `<½`; prime-pair source retains the prime-power field.
- **(a)** A19.
- **(b)** Small-time collisions (B24); frequency (B25); time-0 selector (B26); non-size frequency input (B47); runs (B27); FE-pair reality (B76); crowded zeros (B59); AAL through transport, tower or rigid-world contradiction (B83, B89, B110, B112); rotated relation (B92, B93).

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH.
- **Established [L]:** defect trace class; multiplicity `≤` trace norm; Gaussian passage criterion.
- **(a)** None that moves the route.
- **(b)** Trace norm `<1` on every rectangle or bounded Gaussian oscillation (B38).

### HF — Hodge / Hecke / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** blocks S1, S10, S14; source-work `≤2` ⇔ RH; `R_pole=R_high=W`, `W=⊤` ⇔ RH [S/L]; the complete matrix below `W` is decided by the pole channel [L]; charged profiles and polar-row profiles [S]; low packet at every ratio is RH [L]; unrestricted Gårding false [L].
- **(a)** A9, A13, A44.
- **(b)** Full-space sign at every `K` (B6); low packet at every ratio (B101); pole channel below `W` (B104); head windows (B8); source-work ceiling (B41); top coprime stratum (B10); zero modes (B9); exact SOS (B11); Rosati and band poles (B78, B79); count and damping presentation (B87, B88).

### CHMD — Causal hyperbolic–modular duality
- **Path:** one-sided bounded prime wave or odd Doob half-threshold bound → RH.
- **Established [L]:** wave and Doob receivers; normalized prime−pole decay; nonfirst source keeps `1−ε` of Gamma.
- **(a)** None that moves the route.
- **(b)** Either side of the unnormalized wave bound, or the complete odd sign (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel → RH.
- **Established [L unless marked]:** rank 14 at `0<a≤½`; rank `N` from verified height; VK collar; two-atom and chain signs; `S=Π_pT_pA`; insertion cone; locking = torus positivity; columns add; current `=2|Ξ|²Re ξ′/ξ`; first-atom Gamma floor `aC_Γ/cosh(πb/2)`; the adaptive head `M(b)=⌈|b|/2+B⌉` pays the omitted pair sum by half that floor in every polynomial-square integral; fixed heads have leading term `(4/√π)|Σ_{n≤M}n^{−½+2iτ}|²`; the adaptive partial sum equals `ζ(½+ib)` up to `(9√2+√(1+2(B+1)))|b|^{−½}` and the head's leading term is `|ζ(½+ib)|²` up to `O(|ζ||b|^{−½}+|b|^{−1})`; no summable absolute pair majorant [S]; no compact core funds every Gamma direction [S]; the theta cusp reflected squared product has no finite positive or signed Laplace representation.
- **Structure [D]:** positivity is automatic where `|ζ(½+ib)|` is large; the sign is decided by second-order terms near the critical zeros.
- **Numerics:** positive at actual phases `b≤775`; torus-uniform positivity fails once primes `≲19–47` are free [N].
- **(a)** Rank 15+ (A4); tail-failure certificate (A5); scans and brackets (A24); verified ranks (A1); uniform Gamma-weighted transport of the fixed-head asymptotic to `M=M(b)` (A42).
- **(b)** Exact torus law for `S*` and `{2,3}` cross-chain positivity (B19); amplitude oscillation with the height (B20); all ranks (B21); signed adaptive head near critical zeros (B102); tail law at the Kronecker scale (B96).

### RN — Theta renewal
- **Path:** two-ended renewal → no joint nodes → RH.
- **Established [L]:** `det₂` gives `D`, not Ξ; Ξ zeros = joint nodes; energy comparison ⇔ RH.
- **(a)** None.
- **(b)** Joint-node exclusion or energy comparison (B36).

### WD — Ward / collision / long moments
- **Path:** source current, window energy or long moments → RH.
- **Established [L]:** block S5; one-window form; slope rigidity; long mean values are collision counts.
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
- **Path:** scattering source → Krein/Lewis positivity, integer-probe sign, dispersion bound, horocycle/Farey rate, resonant decay, Narain remainder, cusp-energy rate or a standard form → RH.
- **Established:** block S7; integer-probe positivity ⇔ RH; Krein flux sign ⇔ RH; horocycle rate `y^{¾−ε}` ⇔ RH; unconditional stretched-exponential thermalization; one sharp shell at the RH rate ⇔ RH ∧ Möbius–circle cancellation; universal resonant decay `e^{−t/4}` ⇔ RH; Narain `¾` ⇒ RH, remainder VK; cusp-energy rate reads `Λ_g(ρ/2)`; RS Euler product; RH ⇔ `Q` is the Tate limit of a count ⇔ a standard form with partner modular conjugation; internal realizations collapse [L].
- **(a)** A26, A43.
- **(b)** `D_s≥0`, Krein flux, probe sign or dispersion bound (B68); physical carrier (B69); `V_p` lower bound (B70); any rate past `½` or `¾` (B14, B71); count (B87); Rankin–Selberg noncancellation (B109); positive-energy realization (B114).

### PTR — Cosine source / photonic
- **Path:** `A_h` collision-free descent → RH.
- **Established [L]:** sech handoff; strict Laguerre for `h≥½` and above VK; sign at every `0<h<½` ⇔ RH.
- **(a)** None.
- **(b)** Strict sign below VK (B29); lossless prime-faithful stack (B69).

### JAS — Joint ancestry
- **Path:** subpower control on moving finite power windows → RH.
- **Established [L]:** RH criterion on `m<k≤m+m/log(m+1)`; finite admission; shell positivity infinitely often ⇒ AAL (Turán with a finite head); typical JAS positivity ⇒ AAL; dressed PSD ⇒ AAL.
- **(a)** None.
- **(b)** Uniform control on the moving window (B51); shell signs plus ZAL.

### CTF — Chronological tail / Báez–Duarte
- **Path:** approximation, defect, BSY sign, log-dilation equality, cut-kernel mass or mollifier infimum → RH.
- **Established [L]:** rows ⇔ RH; sharp defect, sparse subpolynomial ⇒ RH; BSY `I≤0` ⇔ RH; positive-proportion form; exact infimum `exp(2I(1))`; one-`δ` dilation equality ⇔ RH; Euler prefixes invariant; finite-energy cut-kernel mass annihilation ⇒ RH; coefficient-Hardy domain of `ζ(s+ε)` trivial for `ε≤½`.
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
- **Established:** blocks S9, S11; cutoff-uniform mass ⇔ RH; AAL ⇔ tail transport; transport on right discs with explicit exponent; crossing discs force power growth; partial returns transport a zero or create a deep small value; short-arc Euler approximation needs prime mass `≳log|τ|`; returns at zeros tail-bad; recurrence dichotomy; smooth-head moments with explicit arithmetic cost [L].
- **(a)** A37.
- **(b)** Uniform target mass (B72); rare tail events at every right zero (B83, B89); tail law at the Kronecker scale (B96); decay (B82).

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
- **Established [L/K]:** full-family receivers; depth corridors; two-lobe bound; cut crystal; sharp location; local pair cost; explicit Hausdorff shifts; critical threshold chain, pole channel and conductor resolution (S1).
- **(a)** A9.
- **(b)** Complementary-window sign, remaining-depth control (B6, B12, B101); all-height column (B46).

### ACT — Single shift
- **Path:** one shift pays every even compact profile → odd positivity → RH.
- **Established [L/K]:** receiver; `{2,3,4}` band; floors through `a_k`.
- **(a)** A7.
- **(b)** One shift uniform in profile (B44, B4).

### AIP — Incidence
- **Path:** complete reflected-prime/pole allocation → subexponential cost → RH.
- **Established [L/K]:** allocation; VK cost; capacity `log log N+O(1)`; gcd-twist channel law; non-gcd periodic twists coercive to the admissible period scale; conductor resolution at a fixed ratio (S1).
- **(a)** A9, A13.
- **(b)** `C_σe^{2σr}` cost (B45); the pole channel (B6, B101, B104).

### SC — Stokes / Witt–Krein
- **Path:** glued index `≤1`, bounded damped coupling, or undamped coupling plus ZAL → RH.
- **Established [L]:** `κ(φ_c)=κ+1`; damped bound ⇔ RH; undamped cone bound ⇒ AAL.
- **(a)** None that moves the route.
- **(b)** Arithmetic coupling bound; tensor loss (B39); B9, B11, B13.

### ACS — Castelnuovo–Severi
- **Path:** source energy → all-aperture Bézout → RH.
- **Established [L/K]:** blocks S10, S14; source cone and RR; Bézout ⇔ RH; primitive `h¹` coercive for `a≤181/500`; Kloosterman purity; reciprocal quadric counts; Young projections at rank `≤4`; Toeplitz minors `≤200`; typical-height sign with Gaussian tails; frequency-packet average; degree-one Selberg classification; count law of every hyperelliptic curve; Rosati height = Born rule; square-root curve counts on thick sets of levels force purity; integral defect of a true curve is a count.
- **(a)** A28, A41, A48.
- **(b)** Source-energy sign (B40, B1); count or Rosati producer over ℤ (B78, B87); damping presentation (B88); global trace (B85); mixed Young shapes (B86); B65; B28.

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
| IWT | Weil towers, level sums, exceptional-rank window theorem, rank barrier, infinite-rank Hasse–Weil principle, exceptional coordinate, `cosh` models, towers of ζ, thick crude count ⇒ AAL, RH ⇔ ZAL ∧ thick `√X`, returns freeze smooth polynomials, critical weight, long mean values = collision counts, calibration battery | A47 | B110, ZAL, B97 |
| SOSZ | 𝔽₁-zonotope surface, two half-products, point count of Spec ℤ, infinite genus of atomic graphs, smoothed pairs Hasse–Weil ⇔ RH [S], no metric on `ℙ¹_ℤ` for the jets, archimedean place not toric, primes are jumps, torsion energy against the jets | A48 | B87, B88; a jets carrier |
| RIAC | completed prime boundary half-plane `2Re s+δ>1`, unitary vertical gauges, prime-star and torsion compensation at log exponent `>2`, prime-vertex dynamics, local flow, singular indices unbounded below | A46 | B106, B88 |
| AIF | inner field, Szegő infimum, rigidity, Carleson measure, dilation quotient, causal certificate, forward map, restoring bound, `Ψ`-boundedness ⇔ RH, Selberg depth `O(T)`, Bohr profiles, insertion cone, columns, local onset field | none | B2, B57, B66, B82 |
| AAD | producers, peak law, half scale, compensated producer, quarter rate under RH, parity-neutral rate, rate = Mertens scale, Frobenius = factorial stencil, transport, slow returns right of the line | A30 | B15, B55, B89 |
| RAC | cut identity and kernel, unique fake, carry, ledger hierarchy, twin at every degree, parity exponent, exact parity identity, exchange law, bounded count with a new zero, maximal angle, extremal-law model, rotated relations | none | B67, B91, B92, B93 |
| TAPO | first return and brackets, precision law, heavy returns, conditional moments, resonator mean, arithmetic mean values, recurrence dichotomy, tail of a return, AAL as tail transport, partial returns, short-arc prime mass, Euler coordinates | A24, A37 | B89, B96, B97, B100 |
| SPAL | shifted-product rigidity, collision cells, smooth × prime collision classes, count-distance rigidity, positive near-count model | none | B98, B103 |
| APD | Hamburger rigidity, FE-defect isolation, one-offs of every positive class, critical-line firewall, positive two-prime annihilators (arbitrary multiplicity, harmonic packets, left growth), zero relocation and first-gap negativity, Hecke state PD iff `s≥½` | none | B80, B84, B103 |
| PTT | Bohr isometry, boxes, savings, rounded orbit, discrepancy, mixing time, hull with natural boundary, Ξ-current lift, certificates | A24 | B46, B100 |
| ASH | graph black holes, Krein law, Lax–Phillips rank two, one clock, KMS, count law at genus one, genus-two graph; ModularBootstrap: Narain partition and its central orders, moment jets, VK remainder, `¾` ⇒ RH, ceiling `¾` | none | B68, B71, B87 |
| CTH | count law at every genus, every hyperelliptic curve, Born rules, boundary algebra, linear counts degenerate, Hecke conservation, second place, Farey reading, stretched-exponential thermalization, sharp shells ⇔ RH ∧ Möbius–circle, modular conjugation is not the partner involution, Tomita collapse, standard-form criterion ⇔ RH, count door of a curve and of ℤ | A41 | B87, B95, B113, B114 |
| BHR | modular wave, metric, AdS₄ quotient, pulse regularity, ringdown = strip, horocycle Mellin formula and Zagier converse, Lax–Phillips semigroup, Maass cusp forms, Weyl order, Rankin–Selberg continuation, Rankin bound, RS Euler product, eigenform series [S], cusp-energy rates | A26, A43 | B71, B109 |
| RIT | Mayer scattering, Krein square, Hecke dispersion, Hecke algebra Poisson on resonant states | none | B68, B70 |
| ACP | Mertens energy residues, positive Hecke annihilators, reflected-pair decay boundary, prime-pair source | none | B68 |
| SEL / Primon | degree-one classification, Euler rigidity; primon thermal Euler factors, Kesten–McKay densities | none | B80 |
| MMD | cubic Gauss conversion, cubic Eisenstein series, nonzero residue, continued Fourier modes | A33 | B94 |
| AE, KPA | polar calculus, Tate law, naive heights, five currencies, torsion intersection, Stepanov over ℤ | none | B87, B88 |
| HHAC | isolated-prime rigidity, fixed-point obstruction, core Euler characteristic, core bouquet, weighted torsion operators (indefinite under finite constraints, Hilbert–Schmidt iff `δ>½`) | none | B88, B106 |
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
| AHD / CACT | threshold chain, `R_pole=W` [S], pole channel decides, charged profiles [S], aperture exchange, top-window non-escape, conductor resolution | A9, A13, A44 | B6, B8, B101, B104 |
| CAF, TCS | two-atom, chains, Euler product, current, rank 14, first-atom reserve, adaptive pair payment, head = `\|ζ(½+ib)\|²` | A4, A5, A24, A42 | B19–B21, B102 |
| HWV, ADT | nerve, sphere bouquet, `M(N)=−χ̃`, Redheffer gluing, finite face singular Euler characteristic [S] | none | B10 |
| AK, Representation | column and rank-`≤4` Young projections, Kloosterman traces, reciprocal quadric counts | A28 | B85, B86 |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ sign on every window (`a*(ζ)=⊤`) | RW, EWU, OWU, ACT, CHMD, SZ, RN, ACS, AIP, SRT, SC, LI, TT (odd), HF, and the critical-curve branches of HF, SRT, AIP (window + pole channel) |
| Σ continuation at small time and the theta head at the critical zeros | ZCG, PTR, LA, GTA, XN, HCF, PA, TH |
| Π square-root precision and long moments | WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| Γ reflection and selection | PM, BAG, SEC, CDC, PCS |
| Missing source landing | APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF |
| Missing count / damping presentation of the diagonal, transversal | ACS, HF, PM, RW through windows |
| Two-scale Dirichlet-series input for AAL, transversal | BAG, JAS shell, SC undamped, WL thick runs, ZCG one-off and tower branches, RW polar ground energy |
| Dark range (Kronecker scale), transversal | every route at all heights; BAG and ZCG one-off branches; TH certificates; WD near-unit moments |
| Width axis (horizon observables), transversal | PM (horocycle, Farey, Lax–Phillips, Narain, cusp energy), MC (Farey), every VK-scale saving |
