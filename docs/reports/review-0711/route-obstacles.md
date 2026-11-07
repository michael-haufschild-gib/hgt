# Route obstacles — status quo

Scope: 38 live route formulations, 9 candidates and their supporting programmes. For each route: path, what is established, obstacles that are **(a) just work**, obstacles that are **(b) open mathematics nobody has a solution to**.

Corpus checkpoint: commit `bf10668155` plus the working tree of 2026-11-07.

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means an independent source mechanism or landing is missing. Formulations are not independent mechanisms: HJ is PA, BSH is CDC, FEL's BSY criterion belongs to CTF. A criterion, a source construction, a quotient equality or a scalar grade does not discharge an arithmetic sign or vanishing.

**Evidence.** `[L]` Lean source. `[S]` Lean source unfinished, unintegrated or uncommitted. `[K]` Lean with transitive axiom audit. `[D]` deduction, not a Lean theorem. `[N]` numerical, uncertified. `[C]` classical literature, not formalized.

**Strength.** RH; ≥qRH (zero-free half-plane or Lindelöf); sub (strictly below quasi-RH); method; indep.

**Labels.** `A*` just-work items and `B*` open problems are listed in full in [obstacles-summary.md](obstacles-summary.md). An A item is known mathematics, finite computation, effectivization, integration or assembly of proved pieces; `(unverified)` marks A items whose difficulty is not established. Wall labels Σ, Π, Γ refer to [walls-ledger.md](walls-ledger.md).

**Notation.** Windows `[−a,a]`. `W` Weil's form, `w_n=Λ(n)n^{−1/2}`, `H` the archimedean–polar form, `P` the arithmetic part. `a*(ζ)` onset aperture; `ℋ(c)` Hardy interval; `λ*(c)` best cone margin. `r=τ_R(i)/τ_L(i)`, `L=artanh r`, `Ψ=½log H₁`, `q=Ψ′`. `N_d` non-real root count of `R_d(Ξ)`. `Θ=½+zeroWidth`, `Θ∞` asymptotic abscissa. ZAL: finitely many zeros beyond every positive depth. AAL: finitely many zeros right of `½+h` forces none. `E(s)=(s−1)ζ(s)/s`, `I(w)` inner field. `R=c⁸/log N`, `W₈(H)=∫H²e^{−8y}`, `Q₁=⌊(log N)^{13/32}⌋`, `R_c` whole-space and `R_high` high-conductor critical thresholds. `A(K)` best stencil slope on alphabet `≤K`. `R(y,η)` first return of the primes `≤y` at precision `η`. `E_y` Euler head, `ζM_y` Euler tail. `L=log|t|`, `ℓ=log L` in orbit statements. `A_φ(y)` horocycle mean of a pseudo-Eisenstein series at height `y`.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ ZAL ∧ AAL; ZAL ⇒ qRH; ¬AAL ⇒ `Θ<1`; `qRH ∨ AAL` | [L]/[D] | one half is at least quasi-RH, the other sits below it |
| Under AAL: RH ⇔ ZAL ⇔ finite off-line support ⇔ `κ(K_ζ)<∞` ⇔ bounded heat count ⇔ finite critical energy ⇔ eventual Hadamard ⇔ eventual central-gap budget | [L] | every large-height receiver reads RH once one-offs are gone |
| ¬AAL ⇔ attained top excess ⇔ `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})`, `T` a unique nonzero trigonometric polynomial ⇔ two-prime dilation annihilation | [L] | failure of AAL is one rigid object |
| Positive Euler products with integer norms, or with rational-prime labels and multiplicative linear counting, carry a finite top layer; none continues to `Re s=½` | [L]/[S]/[D] | an AAL proof must use the critical line (FE, critical regularity), not positivity or counting |
| RH ⇔ `a*(ζ)=⊤` ⇔ `λ*(c)→0` ⇔ two-site PD ⇔ `Q(a)≥0` on every integer probe ⇔ `Ψ` locally bounded | [L] | every window route measures one number |
| At the critical curve `R_high=⨅_A windowThreshold(A)≥c₀e^{6a*(ζ)}`; all critical thresholds `=⊤` ⇔ RH | [S] | the complete matrix at ratio `R` is a window rung |
| Low-packet polar payment at every ratio on windows of length `→∞` ⇒ RH | [L] | the low packet is not a finite task |
| Zeros of ζ are zeros of the Euler tail `ζM_y` at every cut; a return at a right zero is tail-bad at every cut and has density zero; nonvanishing targets return at positive density | [L] | AAL needs an atypical tail event |
| Conditional on head alignment the tail is Gaussian below the Kronecker scale; arithmetic mean values pay off-diagonals by collision counts; nothing distributional is known at the scale | [L] | the dark range is the Kronecker scale |
| First return: `exp(c(log N)^{3/2}/log log N)≤R` at bounded harmonic defect, `R(y,η)≤exp(C_ηy/log y)`; at precision `≍y^{−9/2}`, `R>exp(√(y/(48log y)))` | [L] | the RH bracket holds at polynomial precision; constant precision is open |
| Proportional saving ⇔ no early heavy return | [L] | B46 is a first-return statement for heavy subsets |
| Every certificate past `Re s=1` is a tail-good condition | [L] | certificate routes reduce to the tail law |
| Every unconditional saving carries the VK saving; stencil rate is the Mertens level; under RH the stencil exponent lies in `[¼,½]` | [L] | production has no content independent of the Mertens level |
| Farey discrepancy, `M(N)` and the nerve Euler characteristic are one number; long closed horocycles of the modular horizon equidistribute at `y^{1/2}`, and at `y^{3/4}` iff RH | [L]/[S] | geometry, dynamics and the Mertens level read one quantity |
| Zeros are the power-law kernel of the cut system; finite-energy kernel mass annihilation ⇒ RH | [L] | the Nyman–Beurling criterion read from the dual side |
| ζ is isolated: FE defect `≤1/6400`, count distance `o(log n)`, exact parity identity | [L] | any stable argument in these metrics is about ζ alone |
| Universal damping is not forced by waves, flux, unitarity, Hecke, or the functional equation at genus two; the count law forces it at genus one | [L] | the separating property is a count |
| Necessary mollifier length `exp(c log²T)` = length of an Euler mollifier over primes `≤c log²T`, where absolute non-alignment starts | [L]/[D] | the near-line wall and the dark range are one wall |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | Primes pay the archimedean–polar deficit by sign | format exact on every window; size payment ends before half-width `21/40` |
| M2 Calibration | Window cones, blind positivity, margin | cone pinned at `e^{−c/1104}`; cone points obey PNT with exponent `5/6` on the window's range; ceiling doubly exponential; sign open |
| M3 Canonical flow | `L,q,Ψ` of the Weil chain | exact to contact; RH ⇔ `Ψ` locally bounded [L]; `Ψ` oscillation is the sole control |
| M4 Reflection | Krein/Lewis positivity, Hecke dispersion, ringdown, Lax–Phillips decay, horocycle rate | coefficient completion closed; Hecke algebra positive Poisson on resonant states; flux sign open; FE does not force damping |
| M5 Square-root cancellation | One smoothed prime count, long moments, Farey discrepancy | receivers closed; estimates open |
| M6 Continuation | Heat, cosine, Jensen | typical heights closed; small time at all heights open |
| M7 Zero geometry | Cameras, Blaschke factors, inner field | isolated zeros at rate 2; depth `O(T)`; clusters and `o(T)` open |
| M8 Recurrence | Transport of zeros by returns | transport closed on right discs; returns at zeros are tail-bad; existence open |
| M9 Production | Integer stencils | exact; rate = Mertens level; zeros are the kernel |
| M10 Count | A nonnegative function at bounded distance from the form | Manin at genus one [L]; over ℤ local data only |
| M11 Orbit at finite time | Prime phases at one height; first return; conditional tail; collision arithmetic | absolute savings; brackets at every precision; dark at the Kronecker scale |
| M12 Critical compactness | Gårding, Γ-liminf, non-escape, threshold law | assembled [S]: the critical curve is the window; low packet at every ratio is RH |
| Amplifiers | Diophantine repulsion, integrality, isolation | amplify a certificate, produce none |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve

Routes: HF, SRT, AIP, ACS (atomic), SC, CHMD (index). Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF.

Established:
- Full tilted-spline matrix PD for `1≤c≤(log N)^α`, `α<1/8` [L], and through `c≤2K₀(log N)^{1/8}` with complete Schur payment [K].
- Every compact C² profile: energy `≥ae^{−Bc}‖x‖²` on conductors `≤N^θ`, `θ<¼`, `c≤b log log N` [L].
- Every fixed ratio: critical pencil `κQ+(7J/R)W₈`; low packet `m≤Q₁` keeps its diagonal and polar part [K]; polar capacity `S_A²/(J₁/R+κg)` [K].
- Γ-liminf with weight `α_R>0`; strong `L²` limits from bounded form; physical and Fourier tails give precompactness [L]. Unrestricted Gårding false on `(V₁)ᗮ`; top-collar Gårding at every `R` [L].
- Far margin coercive for `0<R<R*`; joint complement coercive for `0<R≤min(1,5R*/6)` [L].
- Non-gauge periodic charges coercive up to the admissible period scale `M₀(N)→∞` [L].
- **Threshold law [S].** `0<R_c≤R_pole≤R_high=R_high^{PSD}=⨅_{A≥0}windowThreshold(A)≥c₀e^{6a*(ζ)}`; the inequality `R_high≥⨅wT` is the compactness assembly (one-sided spline mollification, Kolmogorov–Riesz, Γ-liminf, window mollification). Every nonzero nonpositive whole-space vector below `c₀e^{6a*}` charges `V_{Q₁}` and the top window of length `(1/8)log(R+1)+C₀`. All thresholds `=⊤` ⇔ RH.
- **Low packet [L].** Eventual PSD along a critical sequence ⇒ polar payment on every window; payment at `R` on `[−A,0]` ⇒ `R≤windowThreshold A`; payment at every ratio on windows of length `→∞` ⇒ RH; payment on every window for `R≤(2K)⁸`.
- **Splitting order [S].** Physical tearing of the prime quasimode has Schur ratio `→4/13`; conductor-adapted splitting decouples the far band.

Structure [D]: the critical-curve problem is the window problem in another parametrization: at each ratio, positivity on the high-conductor complement holds exactly below the window threshold, and the low packet against growing windows is RH. No sub-RH content remains at the critical curve beyond the architectural question `R_c=R_high`.

| | Obstacle | Strength |
|---|---|---|
| A9 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | — |
| A11 | Integrate the critical-curve modules: threshold law, continuum threshold growth, top-window non-escape, `4/13` obstruction, far decoupling, signed-PNT bridge | — |
| A13 | Near-gcd charges and periods beyond `M₀(N)` (unverified) | — |
| B6 | Full-space sign eventually at every `K`; equivalently every critical threshold `=⊤` | RH |
| B8 | Head thresholds for every `d` | RH |
| B101 | Low-packet polar payment at every ratio on growing windows | RH |
| B104 | `R_c(ζ)=R_high`: does the low packet lower the whole-space threshold | method |

### S2. Window tower and canonical flow

Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT (odd), HF, ACS, SRT, SZ, MSC. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF.

Established [L]: precontact de Branges chain, canonical system with `H₁H₂=1`, flux, sampling bases; `L′=q−sinh 2L`, contact criterion and scaling; traces, `r`, `Ψ` absolutely continuous; `q_y→q` in `L¹`; restoring bound `|L(x)|≤artanh e^{−2(x−c)}+2osc Ψ`; RH ⇔ `L` locally bounded on precontact intervals ⇔ `Ψ` locally bounded, and off RH `L` is unbounded above every base; soft prime kick; Born model; causal certificate, Szegő threshold, free reflection coordinates, forward-map tangent; cone pinning, margin ceiling, bounded extremals for every weight; cone points carry local density `1+O(e^{−a})`, positive support density and PNT with exponent `5/6` on `X≤e^{2c−3}` (the last [S]); datum region `⊆{β≤1}`; exact null blind test; floors `(1/20000)/2^k` through `a_k<0.3621`; window naive heights exist iff positive, and on length `≤3/5`; Tate dimension one exactly through `log 5`.

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

Established [L]: `Ω_ψ(a,X)` as a sum over zeros; on-line terms nonnegative; depth cost `≤(16/9)δ²a⁴‖ψ‖²`; RH ⇔ `Ω≥0`. Typical-height sign at `A=δlog T/(64M²)` for every shaped test; the bad heights have Gaussian tails `≤209(4kδ²)^kT`, exponential rarity, and measure `≤T^{1−1/(64K)}` at `A=K log log T`. Weil's form is the average of its frequency packets; negative tests have negative packets on positive measure. Visibility, cut crystal, sharp location at `λ>1`; isolated-zero entry on the column.

Structure [D]: all-height sign stops at the size curve `a≈log log X`; past it the input is the short-sum barrier (S11).

| | Obstacle | Strength |
|---|---|---|
| — | none that moves the route | — |
| B28 | Local Weil positivity at fixed `λ>0` on density-one heights | sub |
| B46 | Proportional saving = no early heavy return at length `(log X)^{2K}`, all heights | sub |

### S4. Continuation and nodal geometry

Routes: ZCG, LA, PTR, HCF, PA, GTA, XN. Programmes: NGF, FFP, ADO, RHTower heat.

Established [L]: collision criterion; horizon `(6600/9991+ε)/log X`; density-one `Λ_Xlog X→0` with cubic exceptional exponent; crystal and reality at the critical scale; sharp depth law for isolated simple zeros; `N_d` law and inner-root reality; cosine Laguerre above VK; nonrepelling values of dimension zero; maximal-angle law and Stieltjes sign; ZAL ⇔ uniform high-collision counts. The extremal inequality alone has a polynomial model with off-axis zeros.

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

Established [L unless marked]: band ⇔ classical criteria; integer lag; entry filters; length–precision law; gauge exponents `[Θ,1]`; twin pairs carry a quarter floor (`Θ≤2max(θ_μ(x),θ_μ(y))`); Nair lattice; producers `c=μ∗h`, mollifiers on `Re s=1`; floor `c/(√K(1+log K))`; rate `K^{−a}` ⇒ `Re ρ≤1−a`; all `a<½` ⇒ RH; RH gives `a<¼`; compensated producer with smooth letters; parity-neutral producers at every rate; extremal fakes with `≤K` atoms; cut kernel = zeros; finite-energy kernel mass annihilation ⇒ RH; exact identity pins `λ`; exchange law; count-distance rigidity at `o(log)`; bounded count with a new zero (signed generators); Farey discrepancy ⇔ RH, `|M(n)|≤2π·`Farey discrepancy, `M(N)=−χ̃` of the nerve; Carlitz stencil; torsion energy; cubic Gauss conversion, cubic Eisenstein series, constant term supported on cubes, residue at `4/3` nonzero with cubic character, continuation of the Fourier modes.

| | Obstacle | Strength |
|---|---|---|
| A21, A30, A33 | Chowla [C]; best RH exponent in `[¼,½]` (unverified); cubic residue Fourier coefficients = cubic theta / Gauss sums [C] | — |
| B48 | A deciding input at square-root precision | RH |
| B55 | Any polynomial stencil rate (qRH); rates `a↑½` (RH) | ≥qRH to RH |
| B15 | Mertens level past VK | sub |
| B14 | Any interior width value | ≥qRH |
| B56 | `Θ<1⇒Θ=½` | sub |
| B67 | Parity at power saving (a strip up to twist-absorbed zeros) | ≥qRH |
| B91 | Finite-energy cut-kernel vectors have mass zero | RH |
| B94 | Transfer of the cubic conversion to rational-integer Möbius | past VK at least |
| B98 | Positive-generator integer-norm systems: which count distance, between `o(log n)` and linear, forbids a finite top layer | method |

### S7. Reflection and carriers

Routes: PM; W1C (candidate); RN and PTR in part. Programmes: RIT, ART, AOT, ACP, BHR, ASH.

Established [L unless marked]: resonance ⇔ `ζ(2s)=0`; `Q=2Re[WH,WH]`; `D_s≤0`, zero iff `Re s=¼`; Hecke dispersion `V_p`; every Hecke operator diagonal on Eisenstein, the whole Hecke algebra has a positive Poisson measure on truncated resonant states for every `Re u<0`; scattering Blaschke product; exact modular horizon, a quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)`; ringdown in the modes of zeros; pulse metrics regular across the horizon; quarter-line bound ⇔ RH; horocycle rate `y^α` ⇒ `Re ρ≤2−2α`, unconditional rate `y^{1/2−ε}`, RH ⇔ rate `y^{3/4−ε}` [S for the forward direction]; Lax–Phillips semigroup of the modular surface with RH ⇔ universal resonant decay `e^{−t/4}` [S]; graph black holes with flux, unitarity, Hecke at every degree and class; Krein flux law; count law ⇔ `t²≤4q`; Manin's Hasse; trivial-zero law; throats have FE only at genus `≤1`; genus-two graph with FE and a slow resonance for `q≥4`.

Structure [D]: the wave system does not know the partner law; at genus two the functional equation is supplied by branching and still does not force damping. The separating law is the count. Horocycle rate and resonant decay are the same scattering poles read in space and in time.

| | Obstacle | Strength |
|---|---|---|
| A26 | Weyl law [C]; metric of `L²` data; scalar sector | — |
| A32 | Manin at higher genus through Jacobians; first test the genus-two graph [C] (unverified in corpus) | — |
| A35 | Integrate the horizon modules: horocycle forward rate, modular Lax–Phillips semigroup | — |
| B68 | Independent `D_s≥0`, nonnegative Krein flux, integer-probe sign or all-zero dispersion bound | RH |
| B69 | Positive physical carrier | producer |
| B70 | Lower bound for `V_p` from the carrier | sub |
| B71 | Sharp decay of the smoothed resonant sum; equivalently horocycle rate `y^{3/4−ε}` | RH |
| B87 | A count for `Q` over ℤ | RH |

### S8. Index and support

Routes: HKT, AKLT, SC, RIT, CWS through HF, ACS; LA. Established [L]: `κ(φ_c)=κ+1`; finite index ⇒ Lindelöf; `κ∈{0,∞}` under escape, mixing or decay; window index counts critical lengths; `sup_dN_d` off-line multiplicity; `K_ζ^n` PD ⇔ RH; finite support makes almost every prime tower decide.

| | Obstacle | Strength |
|---|---|---|
| B12 | Index ceiling uniform in resolution | ≥qRH |
| B13 | Exclude finite nonzero off-line support | sub |
| B23 | `N_d` bounded | ≥qRH |

### S9. Abscissa split, recurrence, one-offs

Routes: BAG, JAS shell, SC undamped, WL sparse samples, ZCG one-off branch, RW polar ground energy. Programmes: AKLT, ZCG, AIF, APD, AAD, RAC, PTT, TAPO, SPAL.

Established [L unless marked]:
- Split RH ⇔ ZAL ∧ AAL ⇔ ZAL ∧ zero-disc weak recurrence; RH ⇔ ZAL ∧ subexponential polar ground energy.
- AAL producers: not-attained top; bounded lag on a progression; lag `≤Me^{aL}` off a set of lower Abel density zero; subexponential polar ground energy; one generic prime-window grid; log-dense integer lag; twisted plateau; JAS dressed PSD; typical JAS positivity; bounded towers; one bounded cone; shell positivity; weak recurrence; infinitely many zeros near each right zero; slow aligned returns on right discs.
- ¬AAL: finite oscillation of `ψ(x)−x`, unique `T`, quantized coefficients, remainder ceiling, sign changes, two-prime dilation annihilation, rightmost-zero jets with long-shift correlation `m²`.
- Transport: discs crossing `Re s=½` force `|ζ|≥cτ^b`; right discs carry the AAL receiver with explicit exponent. Head returns have `N<1024(log τ)⁴(log log τ)²`.
- Tail: zeros of ζ are zeros of `ζM_y` at every cut; returns at right zeros are tail-bad at every cut and have density zero; nonvanishing targets return at positive density; the head is frozen below resolution `1/log y`; fixed-resonator mean squares split as smooth part times rough part.
- Hull: Haar-a.e., fair-coin-a.e. and Liouville-antipodal order-two fibres extend zero-free to `Re s>½` with natural boundary `½`; the Liouville point extends iff RH.
- Countermodels: continuous one-offs with regular integer count; discrete and integer-norm one-offs with linear counting; rational-prime one-offs with multiplicative linear counting [S]; nonnegative two-prime annihilators of any finite zero set. Every one-off fails to continue to `Re s=½`; FE defect `≤1/6400` forces the rational primes.

Structure [D]: the random Euler model does not reach targets with zeros, so a bounded return at a zero is an arithmetic event at the Kronecker scale. The one input no countermodel carries is the functional equation at the critical line. ¬AAL is a finite exceptional layer inside the strip, an exclusion problem of Landau–Siegel type.

| | Obstacle | Strength |
|---|---|---|
| A36 | Integrate the rational-prime one-off modules | — |
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

Routes: ACS, HF, PM integer probes; RW through window naive heights. Programmes: AE, CWS, LST, KPA, ASH, RIT.

Established [L]: polar surface calculus; Tate law (degree-two form `≥0` iff a function bounded below lies at bounded distance); five currencies; curve Rosati has a naive height ⇔ unitary; Manin's height on twisted elliptic curves with Hasse from the count law; theta `h⁰` with exact RR; Künneth `h¹` split; Λ as an intersection number of torsion orbits; sign lost in `log(1/(1−r))Σx²`; source cone and all-aperture RR; Bézout ⇔ RH; every Young projection of the arithmetic character at rank `≤4` nonnegative.

| | Obstacle | Strength |
|---|---|---|
| A28, A32 | Reciprocal quadric traces (unverified); Manin at higher genus | — |
| B87 | A function on correspondences, nonnegative for an arithmetic reason, at bounded distance from `Q` | RH |
| B88 | Torsion self-energy paid by the archimedean reserve at finite `r` | RH |
| B95 | An abelian group with Hecke endomorphisms `T_n`, `T_n′T_n=n`, whose trace form is `Q` | producer |
| B65 | Genus upper law; logarithmic Serre duality; first Epstein real zero | indep. to sub |

### S11. Prime orbit at finite time

Routes: BAG, TH, SRT, RW, ZCG carriers, every route at the all-height wall. Programmes: PTT, TAPO, SPAL.

Established [L]:
- Boxes: every window of length `exp(10y√(log y·log log y/δ))` enters every `δ`-box on primes `≤y`; dyadic sign codes give a box of radius `ρ` missed below `log T≈π(y)log(π/(4ρ))`.
- Savings: `8/(10⁹L⁶ℓ⁴)` at length `48L²ℓ` from low-energy squared words; `t^{−δ}` at `L^A`; no cancellation below `c log T` at some height; square-root cancellation at all dyadic lengths `Y..T/log T` off measure `≪TY^{−2ε}`.
- First return: brackets at every precision; at bounded harmonic defect `R≥exp(c(log N)^{3/2}/log log N)` (VK on the `1`-line); RH bracket at precision `≍y^{−9/2}`; weak returns = extreme values of `ζ(1+it)`.
- Heavy returns: proportional saving ⇔ no early heavy return.
- Conditional tail: decoupling by unique factorization, Gaussian conditional moments, large deviations, all below the Kronecker scale; smooth×prime mean squares with off-diagonal cost `8X²|A|²`, rectangular cost `4Z(X+Z)(Σ|r|)²K²`, arbitrary smooth heads through the reduced-ratio height.
- Ceilings: rounded orbit; one word `≤1/(2(k+2))`; binomial phase `2/(k+1)` per block; the jet of `t log` moves; comb inequality; logarithmic half-turns of `log 3/log 4` return polynomially in the precision.
- Archimedean place: `h↦t log(1+h/x)` additive only up to `|t|hh′/x²`; the depth aspect is exact.
- Certificates: Euler coordinates stop at `Re s=1`; head–tail certificate ⇔ tail-good.

Structure [D]: between `log t` and `exp((log t)^{2/3})` the Taylor degree of `t log(n+h)` exceeds `(log length)²`. The required saving at the size curve is `≈εL/ℓ`, the proved one `≈L⁻⁶`. Arithmetic mean values control the rarity of large tails; a bounded return at a zero needs the opposite, the existence of a tail event.

| | Obstacle | Strength |
|---|---|---|
| A24, A37 | Certified scans and brackets; growing resonators (unverified) | — |
| B46 | Proportional saving at length `(log X)^{2K}`, all heights | sub |
| B97 | Constant-precision first return: `log R(y,δ)≥y^c` for fixed `δ`, for every heavy subset | sub |
| B100 | A saving for `t log n` on moving families of blocks past Vinogradov's degree | sub |
| B15 | Past VK | sub |
| B20 | Oscillation of the actual amplitude with the height | RH |

## 3. Live routes

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy or one-sided `Φ` → RH.
- **Established [L/K]:** bounded endpoint energy ⇔ RH; integer lag ⇔ RH; `Ω±(√n)`; first-band abscissa `2Θ`; gauge exponents `[Θ,1]`; subtracted lag ⇔ ZAL; lag excursions of lower Abel density zero ⇒ AAL; log-dense integer lag bounded above ⇒ AAL. Production support: stencil exponent `[¼,½]` under RH; cut kernel; exact parity identity; twin quarter floor.
- **(a)** A30.
- **(b)** Bounded endpoint energy and first-band square-root bound (B49); half-power at the trivial gauge (B50); deciding input (B48); past VK (B15).

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every radius → RH.
- **Established:** blocks S2, S3; RH ⇔ `Ψ` locally bounded [L]; cone nonempty ⇔ RH; relative compactness ⇔ RH; naive height on every window ⇔ RH; RH ⇔ ZAL ∧ subexponential polar ground energy [L]; cone points obey local density and PNT with exponent `5/6` on the window's range [L/S].
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
- **Established [L]:** Hausdorff rows nonnegative for `r≥min(C₀(k+1)²,S(k))` with the explicit shift `S(k)` from the sharp zero mass; remaining entries ⇔ RH; exterior diagonal criterion at `218/25`.
- **(a)** Verified rows (A1).
- **(b)** Signs below the explicit boundary, exterior `K(z,z)≥0`, or `TV(n)/qⁿ→0` (B31).

### MC — Möbius cancellation
- **Path:** half-power Möbius or Liouville cancellation → RH.
- **Established [L/K]:** damped energy ⇔ RH; one-point form; VK Hilbert energy; Möbius zeros condense on `Re s=Θ`; gauge genericity; producer rates; parity exponent = zero abscissa; exact identity pins `λ`; order-two twins have Möbius exponent `≥¼`, constant-source twins `≥½`; Farey discrepancy ⇔ RH and `M(N)=−χ̃` of the nerve; cubic branch: ideal Möbius = cubic Gauss coefficient, cubic Eisenstein series, constant term supported on cubes, nonzero residue at `4/3` with `ΔR=(8/9)R` and cubic character, continued Fourier modes.
- **(a)** Chowla [C] (A21); Fourier coefficients of the cubic residue (A33).
- **(b)** Trivial-gauge cancellation or zero exclusion for `M_X` (B50); deciding input (B48); past VK (B15); rational transfer (B94).

### TT — Theta tail / Wold
- **Path:** weighted endpoint energy bounded for each `0<t<½` → RH.
- **Established [L]:** Wold residual VK; `D_t+Q_t/2≥0`; boundedness ⇔ RH; uniform bound on a shrinking band.
- **(a)** None that moves the route.
- **(b)** `C_t` at every fixed `t` (B34); odd branch B4.

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted or sublinear root height → RH.
- **Established [L]:** block S4; infinitely many unshifted degrees ⇔ RH; inner roots real; `N_d≤300√(d log d)`.
- **(a)** A20; A1.
- **(b)** Outer roots (B22); `N_d` bounded gives finite support only (B23, B13).

### ZCG — Zero-configuration geometry / heat descent
- **Path:** half-Gaussian source → no positive-time collision → RH.
- **Established [L]:** blocks S4, S5, S9; cameras; sharp location; one-off structure and jets; maximal-angle law; the extremal law alone admits a polynomial model; one-offs over positive Euler products exist and stop at the critical line.
- **(a)** A19.
- **(b)** Small-time collisions (B24); frequency (B25); time-0 selector (B26); non-size frequency input (B47); runs (B27); FE-pair reality (B76); crowded zeros (B59); long-shift `Λ` correlation or a bounded return in the one-off world (B83, B89); rotated relation or a contradiction using growth or arithmetic (B92, B93).

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH.
- **Established [L]:** defect trace class; multiplicity `≤` trace norm; Gaussian passage criterion.
- **(a)** None that moves the route.
- **(b)** Trace norm `<1` on every rectangle or bounded Gaussian oscillation (B38).

### HF — Hodge / Hecke / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** blocks S1, S10; source-work `≤2` ⇔ RH; the critical curve is the window (`R_high=⨅windowThreshold`) [S]; low packet at every ratio is RH [L]; unrestricted Gårding false [L].
- **(a)** A9, A11, A13.
- **(b)** Full-space sign at every `K` (B6); low packet at every ratio (B101); head windows (B8); source-work ceiling (B41); top coprime stratum (B10); zero modes (B9); exact SOS (B11); Rosati and band poles (B78, B79); count (B87).

### CHMD — Causal hyperbolic–modular duality
- **Path:** one-sided bounded prime wave or odd Doob half-threshold bound → RH.
- **Established [L]:** wave and Doob receivers; normalized prime−pole decay; nonfirst source keeps `1−ε` of Gamma.
- **(a)** None that moves the route.
- **(b)** Either side of the unnormalized wave bound, or the complete odd sign (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel → RH.
- **Established [L unless marked]:** rank 14 at `0<a≤½`, payment `∫p²·current≥aE/250` for `deg p≤13` from a radius-12 power core, height 67 and the coupled current tail; rank `N` from verified height; VK collar; two-atom and chain signs; `S=Π_pT_pA`; insertion cone with exact threshold `½`; theta amplitude not all-base torus-positive; locking = torus positivity; columns add; `current=2|Ξ|²Re ξ′/ξ` with sharp tail `≤3.6·10⁷|a|e^{−(7/5)|b|}`; frozen certificate exactly above the size curve; first-atom Gamma reserve uniform in frequency and degree, and the infinite remainder beyond a frequency-adaptive cutoff `≍|b|/2` costs at most half of it [S].
- **Structure [D]:** a proof through `S` must use oscillation of the amplitude with the height; all ranks reduce to the frequency-adaptive finite head of signed unequal pairs.
- **Numerics:** positive at actual phases `b≤775`; torus-uniform positivity fails once primes `≲19–47` are free [N].
- **(a)** Rank 15 and beyond, each rank finite (A4); tail-failure certificate (A5); scans and brackets (A24); verified ranks (A1); integrate the Gamma-reserve modules (A36).
- **(b)** Exact torus law for `S*` and `{2,3}` cross-chain positivity (B19); amplitude oscillation with the height (B20); all ranks (B21); finite-head unequal pairs at every frequency (B102); tail law at the Kronecker scale (B96).

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
- **Path:** scattering source → Krein/Lewis positivity, integer-probe sign, dispersion bound, horocycle rate or resonant decay → RH.
- **Established:** block S7; integer-probe positivity ⇔ RH; Krein flux sign ⇔ RH; horocycle rate `y^{3/4−ε}` ⇔ RH (Zagier) [L/S]; universal resonant decay `e^{−t/4}` ⇔ RH [S]; count law gives damping at genus one; FE at genus two does not.
- **(a)** A26, A32, A35.
- **(b)** `D_s≥0`, Krein flux, probe sign or dispersion bound (B68); physical carrier (B69); `V_p` lower bound (B70); resonant decay or horocycle rate past `y^{1/2}` (B71, B14); count (B87).

### PTR — Cosine source / photonic
- **Path:** `A_h` collision-free descent → RH.
- **Established [L]:** sech handoff; strict Laguerre for `h≥½` and above VK; sign at every `0<h<½` ⇔ RH.
- **(a)** None.
- **(b)** Strict sign below VK (B29); lossless prime-faithful stack (B69).

### JAS — Joint ancestry
- **Path:** subpower control on moving finite power windows → RH.
- **Established [L]:** RH criterion on `m<k≤m+m/log(m+1)`; finite admission; shell positivity infinitely often ⇒ AAL; typical JAS positivity ⇒ AAL; dressed PSD ⇒ AAL.
- **(a)** None.
- **(b)** Uniform control on the moving window (B51); shell signs plus ZAL.

### CTF — Chronological tail / Báez–Duarte
- **Path:** approximation, defect, BSY sign, log-dilation equality, cut-kernel mass or mollifier infimum → RH.
- **Established [L]:** rows ⇔ RH; sharp defect, sparse subpolynomial ⇒ RH; BSY `I≤0` ⇔ RH; positive-proportion form; exact infimum `exp(2I(1))`; rigidity; one-`δ` dilation equality ⇔ Szegő ratio equality ⇔ RH; Euler prefixes invariant; finite-energy cut-kernel mass annihilation ⇒ RH; Vasyunin cotangent sums obey an approximate reciprocity law.
- **(a)** None that moves the route.
- **(b)** Rows, sparse defect, BSY sign, positive proportion (B52); near-unit budgets, zero surplus (B66); cut-kernel mass (B91).

### HCF — Heat trace
- **Path:** both prime-log grids positive at every degree → RH.
- **Established [L]:** two-grid criterion; explicit detector degree; chirp criteria.
- **(a)** A1.
- **(b)** Nonnegativity at every degree, or chirp bound (B30).

### XN — Newton discs
- **Path:** line-centered self-map discs covering every zero → RH.
- **Established [L]:** coverage and margin criteria; `ΔM≥0`; local damping.
- **(a)** None.
- **(b)** Cover every zero with `M≥0` (B32).

### BAG — Self-return
- **Path:** strong self-return or head-target mass, or decay plus zero-disc recurrence → RH; slow aligned returns on right discs → AAL.
- **Established:** blocks S9, S11; cutoff-uniform mass ⇔ RH; transport on right discs with explicit exponent; crossing discs force power growth; returns at zeros tail-bad at every cut; recurrence dichotomy on universal discs; arbitrary finite smooth-head moments with explicit arithmetic cost [L].
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
- **Established [L/K/S]:** full-family receivers; depth corridors; two-lobe bound; cut crystal; sharp location; local pair cost; isolated-zero entry; explicit Hausdorff shifts; critical-curve threshold law [S].
- **(a)** A9, A11.
- **(b)** Complementary-window sign, remaining-depth control (B6, B12, B101); all-height column (B46).

### ACT — Single shift
- **Path:** one shift pays every even compact profile → odd positivity → RH.
- **Established [L/K]:** receiver; `{2,3,4}` band; floors through `a_k`.
- **(a)** A7.
- **(b)** One shift uniform in profile (B44, B4).

### AIP — Incidence
- **Path:** complete reflected-prime/pole allocation → subexponential cost → RH.
- **Established [L/K]:** allocation; VK cost; capacity; channel law on gcd twists; non-gcd periodic twists coercive to the admissible period scale.
- **(a)** A9, A11, A13.
- **(b)** `C_σe^{2σr}` cost (B45); packet complement (B6, B101).

### SC — Stokes / Witt–Krein
- **Path:** glued index `≤1`, bounded damped coupling, or undamped coupling plus ZAL → RH.
- **Established [L]:** `κ(φ_c)=κ+1`; damped bound ⇔ RH; undamped cone bound ⇒ AAL.
- **(a)** None that moves the route.
- **(b)** Arithmetic coupling bound; tensor loss (B39); B9, B11, B13.

### ACS — Castelnuovo–Severi
- **Path:** source energy → all-aperture Bézout → RH.
- **Established [L/K]:** block S10; source cone and RR; Bézout ⇔ RH; primitive `h¹` coercive for `a≤181/500`; Kloosterman purity; column projections and all Young projections at rank `≤4`; Toeplitz minors `≤200`; typical-height sign with Gaussian tails; frequency-packet average; degree-one Selberg classification.
- **(a)** A28, A32.
- **(b)** Source-energy sign (B40, B1); count or Rosati producer (B78, B87); global trace (B85); mixed Young shapes at unbounded rank (B86); B65; B28.

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
| AIF | inner field, Szegő infimum, rigidity, Carleson measure, dilation quotient, Laguerre factorization, causal certificate, forward map, restoring bound, `Ψ`-boundedness ⇔ RH, Selberg depth `O(T)` and bounded inner field at infinity, Bohr profiles, insertion cone, columns, local onset field | none | B2, B57, B66, B82 |
| AAD | producers, uncertainty, peak law, half scale, compensated producer, quarter rate under RH, parity-neutral rate, rate = Mertens scale, extremal fakes sparse, returns are prime returns, transport, slow returns right of the line | A30 | B15, B55, B89 |
| RAC | cut identity and kernel, unique fake, carry, ledger hierarchy, twin at every degree, parity exponent, exact parity identity, exchange law, bounded count with a new zero, maximal angle, extremal-law model, rotated relations | none | B67, B91, B92, B93 |
| TAPO | first return and brackets incl. the `3/2` bracket, VK on the `1`-line, precision law, heavy returns, tail–head decoupling, conditional moments, resonator mean of ζ, arithmetic mean values, recurrence dichotomy, tail of a return, head resolution, moving jet, depth aspect, Euler coordinates, comb, six questions answered | A24, A37 | B89, B96, B97, B100 |
| SPAL | shifted-product rigidity, collision cells, smooth×prime collision classes, rectangular collisions, logarithmic half-turns with polynomial returns, count-distance rigidity, positive near-count model with power rate | none | B98, B103 |
| APD | Hamburger rigidity, FE-defect isolation, continuous/discrete/integer-norm one-offs [L], rational-prime one-offs with multiplicative counting [S], positive two-prime annihilators | A36 | B80, B84, B103 |
| PTT | Bohr isometry, boxes, savings from low-energy words, rounded orbit, discrepancy, mixing time from below, hull with natural boundary over Haar, order-two and Liouville-antipodal points, Ξ-current lift, certificates | A24 | B46, B100 |
| ASH | graph black holes, Krein law, Lax–Phillips rank two, one clock, KMS, rank barrier, bulk log-mean, count law, integer probes, Manin heights, trivial zeros of a cusp, throats, genus-two graph | A32 | B68, B87 |
| BHR | modular wave, metric, AdS₄ quotient, pulse regularity across the horizon, echo train, causal symbol, ringdown, cusp channel, horocycle Mellin formula and Zagier converse [L], horocycle forward rate and Lax–Phillips decay [S] | A26, A35 | B71 |
| RIT | Mayer scattering, Krein square, Hecke dispersion, every Hecke operator diagonal on Eisenstein, Poisson spectral measure of the Hecke algebra on resonant states | none | B68, B70 |
| MMD | cubic Gauss conversion, cubic quotient, Eisenstein series, constant term on cubes, nonzero residue with cubic character, continued Fourier modes, compact pullbacks | A33 | B94 |
| AE, KPA | polar calculus, Tate law, naive heights, five currencies, torsion intersection and energy, height principles | none | B87, B88 |
| CSTW | canonical system, scalar flow, soft kick, Green corner, AC traces, `L¹` drift, sampling | A16 | B2, B3 |
| CHT | margin law, pinning, datum region, bands, local density, support density, cone PNT `5/6` [S], bounded extremals, edge law | A6 | B16 |
| VHR | height 67; window, Li, Hausdorff, heat, Jensen, PF, theta rungs | A1, A2 | none; decides no all-aperture statement |
| NGF | frequency, blow-up, gap laws, maximum principle, crystal and reality at critical scale | A19 | B24–B27, B47 |
| MZF | Selberg CLT, cameras, hyperbolic density, derivative law, rigidity, last scale, Möbius zero condensation | A18 | B57–B61 |
| FFP | `N_d` law, saddle region, stability dictionary, bulk blindness | A20 | B22, B23 |
| ADO | carrier repulsion; exceptional set of dimension zero; FE-pair flatness | none | B77 |
| APR | necessary length, filters, prefix amplification, collar laws | A18 | B48 |
| AKLT, ASRP | Stepanov over ℤ, Nair lattice, integrality halves, stencil ceilings; AAL producers | none | B48, B83 |
| AGT | gauge torus, pole-subtracted spectrum, twin quarter floor | none | B50 |
| SEL | degree-one classification, Euler rigidity | none | B80 |
| PBAP, W3 | blind positivity, exact null blind test | none | B18 |
| WVL | universal threshold, two-lobe, cut crystal | none | none beyond B1 |
| AHD/CACT | aliasing limits, Γ-liminf, polar capacity, far margin, collar Gårding, low packet at every ratio = RH [L]; threshold law, continuum threshold growth, top-window non-escape, splitting order [S] | A9, A11, A13 | B6, B8, B101, B104 |
| CAF, TCS | two-atom, chains, Euler product, current, rank 14, first-atom Gamma reserve and pair-remainder payment [S] | A4, A5, A24, A36 | B19–B21, B102 |
| HWV, ADT | nerve of the star cover, sphere bouquet, `M(N)=−χ̃`, Redheffer gluing, effective depth laws | none | B10 |
| AK, Representation | column and rank-`≤4` Young projections, curve characters, endpoint character, Kloosterman traces | A28 | B85, B86 |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ sign or budget on every window (`a*(ζ)=⊤`) | RW, EWU, OWU, ACT, CHMD, SZ, RN, ACS, AIP, SRT, SC, LI, TT (odd), HF, and the critical-curve branches of HF, SRT, AIP |
| Σ continuation at small time | ZCG, PTR, LA, GTA, XN, HCF, PA, TH |
| Π square-root precision and long moments | WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| Γ reflection and selection | PM, BAG, SEC, CDC, PCS |
| Missing source landing | APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF |
| Missing count, transversal | ACS, HF, PM, RW through windows |
| Critical-line input for the AAL half, transversal | BAG, JAS shell, SC undamped, WL sparse, ZCG one-off branch, RW polar ground energy |
| Dark range (Kronecker scale), transversal | every route at all heights; BAG and ZCG one-off branches; TH certificates; WD near-unit moments |
