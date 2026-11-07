# Route obstacles — status quo

Scope: 38 live route formulations, 9 candidates and their supporting programmes. For each route: path, what is established, obstacles that are **(a) just work**, obstacles that are **(b) open mathematics nobody has a solution to**.

Corpus checkpoint: commit `1500534c93` plus the working tree of 2026-11-07.

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means an independent source mechanism or landing is missing. Formulations are not independent mechanisms: HJ is PA, BSH is CDC, FEL's BSY criterion belongs to CTF. A criterion, a source construction, a quotient equality or a scalar grade does not discharge an arithmetic sign or vanishing.

**Evidence.** `[L]` Lean source. `[S]` Lean source unfinished, unintegrated or uncommitted. `[K]` Lean with transitive axiom audit. `[D]` deduction, not a Lean theorem. `[N]` numerical, uncertified. `[C]` classical literature, not formalized.

**Strength.** RH; ≥qRH (zero-free half-plane or Lindelöf); sub (strictly below quasi-RH); method; indep.

**Labels.** `A*` just-work items and `B*` open problems are listed in full in [obstacles-summary.md](obstacles-summary.md). An A item is known mathematics, finite computation, effectivization or assembly of proved pieces; `(unverified)` marks A items whose difficulty is not established. Wall labels Σ, Π, Γ refer to [walls-ledger.md](walls-ledger.md).

**Notation.** Windows `[−a,a]`. `W` Weil's form, `w_n=Λ(n)n^{−1/2}`, `H` the archimedean–polar form, `P` the arithmetic part. `a*(ζ)` onset aperture; `ℋ(c)` Hardy interval; `λ*(c)` best cone margin. `r=τ_R(i)/τ_L(i)`, `L=artanh r`, `Ψ=½log H₁`, `q=Ψ′`. `N_d` non-real root count of `R_d(Ξ)`. `Θ=½+zeroWidth`, `Θ∞` asymptotic abscissa. ZAL: finitely many zeros beyond every positive depth. AAL: finitely many zeros right of `½+h` forces none. `E(s)=(s−1)ζ(s)/s`, `I(w)` inner field. `R=c⁸/log N`, `W₈(H)=∫H²e^{−8y}`, `Q₁=⌊(log N)^{13/32}⌋`, `S_R` the top-window ratio with `log S_R≤(1/8)log(R+1)+C₀`. `A(K)` best stencil slope on alphabet `≤K`. `R(y,η)` first return of the primes `≤y` at precision `η`. `E_y` Euler head, `ζM_y` Euler tail. `L=log|t|`, `ℓ=log L` in orbit statements.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ ZAL ∧ AAL; ZAL ⇒ qRH; ¬AAL ⇒ `Θ<1`; `qRH ∨ AAL` | [L]/[D] | one half is at least quasi-RH, the other sits below it |
| Under AAL: RH ⇔ ZAL ⇔ finite off-line support ⇔ `κ(K_ζ)<∞` ⇔ bounded heat count ⇔ finite critical energy ⇔ eventual Hadamard ⇔ eventual central-gap budget | [L] | every large-height receiver reads RH once one-offs are gone |
| ¬AAL ⇔ `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})`, `T` a unique nonzero trigonometric polynomial ⇔ two-prime dilation annihilation | [L] | failure of AAL is one rigid object |
| RH ⇔ `a*(ζ)=⊤` ⇔ `λ*(c)→0` ⇔ two-site PD ⇔ `Q(a)≥0` on every integer probe ⇔ `Ψ` locally bounded | [L]/[D] | every window route measures one number |
| At a fixed critical ratio every vector vanishing on the top logarithmic window `Ioc(N/S_R,N)` has the floor `(κ₀/(2c⁷))‖x‖²`; nonpositive directions meet that window | [S] | the complete matrix at ratio `R` is one finite window plus its coupling to the low packet |
| Physical tearing at the collar boundary fails at Schur ratio `4/13` on prime quasimodes; keeping conductors `≤N^θ` whole decouples the far band | [S] | split by conductor first, by position second |
| Zeros of ζ are zeros of the Euler tail `ζM_y` at every cut; a return at a right zero is tail-bad at every cut and has density zero | [L] | AAL needs an atypical tail event |
| Conditional on head alignment the tail is Gaussian below the Kronecker scale; nothing is known at it | [L] | the dark range is the Kronecker scale |
| First return: `exp(c(log y)^{1−η})≤R(y,η)≤exp(C_ηy/log y)`; at precision `≍y^{−9/2}`, `R>exp(√(y/(48log y)))` | [L] | the RH bracket holds at polynomial precision; constant precision is open |
| Proportional saving ⇔ no early heavy return | [L] | B46 is a first-return statement for heavy subsets |
| Every certificate past `Re s=1` is a tail-good condition; the frozen Ξ-current certificate exists exactly above the size curve | [L] | certificate routes reduce to the tail law |
| Every unconditional saving carries the VK saving; stencil rate is the Mertens level; under RH the stencil exponent lies in `[¼,½]` | [L] | production has no content independent of the Mertens level |
| Zeros are the power-law kernel of the cut system; finite-energy kernel mass annihilation ⇒ RH | [L] | the Nyman–Beurling criterion read from the dual side |
| ζ is isolated: FE defect `≤1/6400`, count distance `o(log n)`, exact parity identity | [L] | any stable argument in these metrics is about ζ alone |
| Universal damping is not forced by waves, flux, unitarity, Hecke, or the functional equation at genus two; the count law forces it at genus one | [L] | the separating property is a count |
| Necessary mollifier length `exp(c log²T)` = length of an Euler mollifier over primes `≤c log²T`, where absolute non-alignment starts | [L]/[D] | the near-line wall and the dark range are one wall |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | Primes pay the archimedean–polar deficit by sign | format exact on every window; size payment ends before half-width `21/40` |
| M2 Calibration | Window cones, blind positivity, margin | cone pinned at `e^{−c/1104}`; ceiling doubly exponential; sign open |
| M3 Canonical flow | `L,q,Ψ` of the Weil chain | exact to contact; `Ψ` oscillation is the sole control |
| M4 Reflection | Krein/Lewis positivity, Hecke dispersion, ringdown | coefficient completion closed; flux sign open; FE does not force damping |
| M5 Square-root cancellation | One smoothed prime count, long moments | receivers closed; estimates open |
| M6 Continuation | Heat, cosine, Jensen | typical heights closed; small time at all heights open |
| M7 Zero geometry | Cameras, Blaschke factors, inner field | isolated zeros at rate 2; clusters and log-mean open |
| M8 Recurrence | Transport of zeros by returns | transport closed on right discs; returns at zeros are tail-bad; existence open |
| M9 Production | Integer stencils | exact; rate = Mertens level; zeros are the kernel |
| M10 Count | A nonnegative function at bounded distance from the form | Manin at genus one [L]; over ℤ local data only |
| M11 Orbit at finite time | Prime phases at one height; first return; conditional tail | absolute savings; brackets at every precision; dark at the Kronecker scale |
| M12 Critical compactness | Gårding, Γ-liminf, non-escape | collar and complement Gårding; top-window non-escape; low packet open |
| Amplifiers | Diophantine repulsion, integrality, isolation | amplify a certificate, produce none |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve

Routes: HF, SRT, AIP, ACT, ACS (atomic), SC, CHMD (index). Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF.

Established:
- Full tilted-spline matrix PD for `1≤c≤(log N)^α`, `α<1/8` [L], and through `c≤2K₀(log N)^{1/8}` with complete Schur payment [K].
- Every compact C² profile: energy `≥ae^{−Bc}‖x‖²` on conductors `≤N^θ`, `θ<¼`, `c≤b log log N` [L].
- Every fixed ratio: critical pencil `κQ+(7J/R)W₈`; low packet `m≤Q₁` keeps its diagonal and polar part [K]; polar capacity `S_A²/(J₁/R+κg)` [K].
- Γ-liminf with weight `α_R>0` at every `R`; bounded form gives strong `L²` limits; physical and Fourier tails give precompactness [L].
- Unrestricted Gårding false on `(V₁)ᗮ` (deep difference, `W₈≍N⁸`); top-collar Gårding at every `R` [L].
- Far margin coercive for `0<R<R*`; joint complement coercive for `0<R≤min(1,5R*/6)` [L].
- **Top-window non-escape [S].** `log S_R≤(1/8)log(R+1)+C₀`; vectors vanishing on `Ioc(N/S_R,N)` have the unconditional floor; every nonpositive direction meets the window. Mechanism: rescale to horizon `N/S_R`, below the unconditional critical multiple.
- **All-ratio Gårding [S].** Window-localized collar Gårding (nonpositive collars keep half their `L²` mass in `(−A_R,1]`); far Gårding on `(V₁)ᗮ`; complement Gårding on `(V_{Q₁})ᗮ` retaining `(κ₀+2)‖z‖²`, prefix mass, seventh mass, `W₈`, Lévy energy at cost `cB_far∫U_w²`.
- **Splitting order [S, statements only].** Physical tearing of the prime quasimode `v_q−proj v_q`, `q∈(Q₁,2Q₁]`, has Schur ratio `→4/13`; conductor-adapted splitting with conductors `≤N^θ` kept whole decouples the far band.

Structure [D]: at fixed `R` the complete matrix is PD iff the Schur complement of the top window is PD. A negative complement sequence has bounded `W₈` and a strong limit with nonpositive limit pencil, which is a window of half-width `O(log R)`. What is not paid is the low packet against the window: its positivity is polar, and the pole line is spread over all atoms.

| | Obstacle | Strength |
|---|---|---|
| A9 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | — |
| A10 | Compactness assembly: negative complement sequence ⇒ strong limit ⇒ finite window rung | — |
| A11 | Finish and integrate the CACT critical-ratio modules: `4/13` obstruction, far decoupling, signed PNT pole bridge | — |
| A12 | Low-packet signed polar Schur payment against the top window at every ratio (unverified) | — |
| A13 | Growing-period charges beyond gcd profiles (unverified) | — |
| B6 | Full-space sign eventually at every `K` | RH |
| B7 | Positivity on conductors `Q₁..N^θ` above `R*`, as opposed to Gårding | sub |
| B8 | Head thresholds for every `d` | RH |

### S2. Window tower and canonical flow

Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT (odd), HF, ACS, SRT, SZ, MSC. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF.

Established [L]: precontact de Branges chain, canonical system with `H₁H₂=1`, flux, sampling bases; `L′=q−sinh 2L`, contact criterion and scaling; traces, `r`, `Ψ` absolutely continuous; `q_y→q` in `L¹`; restoring bound `|L(x)|≤artanh e^{−2(x−c)}+2osc Ψ`; soft prime kick; Born model; causal certificate, Szegő threshold, free reflection coordinates, forward-map tangent; cone pinning, margin ceiling, bounded extremals for every weight; exact null blind test; floors `(1/20000)/2^k` through `a_k<0.3621`; window naive heights exist iff positive, and on length `≤3/5`.

Structure [D]: RH ⇔ `Ψ` locally bounded on `[0,∞)`. The margin ceiling forces `m≳e^{2a}`, above the Born bound: the potential is a nonlinear collective response.

| | Obstacle | Strength |
|---|---|---|
| A1–A3, A6–A8 | Certified verification, numeric heights, first-window membership, cone widths, anti-diagonals, Tate dimension one | — |
| A15, A16 | Lean statement RH ⇔ `Ψ` locally bounded; numerical `r,m,q` | — |
| B1 | Sign on every window | RH |
| B2 | Bounded oscillation of `Ψ` on every bounded aperture interval | RH |
| B3 | Variation of `r` free of `1/μ` | sub |
| B4 | Two-sector certificates; outer predictors; every actual echo in its Schur band | RH |
| B5 | Kick admission at every stage | RH |
| B16 | Decay law of `λ*(c)` | sub |
| B17 | Signed ground-state structure past `log ρ` | method |

### S3. Local onset plane

Routes: RW, ACS, SRT, ZCG, WD. Programmes: AIF, WVL, MZF, PTT.

Established [L]: `Ω_ψ(a,X)` as a sum over zeros; on-line terms nonnegative; depth cost `≤(16/9)δ²a⁴‖ψ‖²`; RH ⇔ `Ω≥0`. Typical-height sign at `A=δlog T/(64M²)` for every shaped test, no zero information. Visibility, cut crystal, sharp location at `λ>1`; isolated-zero entry on the column.

Structure [D]: all-height sign stops at the size curve `a≈log log X`; past it the input is the short-sum barrier (S11).

| | Obstacle | Strength |
|---|---|---|
| A14 | Frequency-integral identity; Gaussian moments in the typical-height sign | — |
| B28 | Local Weil positivity at fixed `λ>0` on density-one heights | sub |
| B46 | Proportional saving = no early heavy return at length `(log X)^{2K}`, all heights | sub |

### S4. Continuation and nodal geometry

Routes: ZCG, LA, PTR, HCF, PA, GTA, XN. Programmes: NGF, FFP, ADO, RHTower heat.

Established [L]: collision criterion; horizon `(6600/9991+ε)/log X`; density-one `Λ_Xlog X→0` with cubic exceptional exponent; crystal and reality at the critical scale; sharp depth law for isolated simple zeros; `N_d` law and inner-root reality; cosine Laguerre above VK; nonrepelling values of dimension zero; maximal-angle law and Stieltjes sign. The extremal inequality alone has a polynomial model with off-axis zeros (Γ120).

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

Established [L]: Selberg CLT and prime field; cameras, hyperbolic density theorem, `N(ρ)=exp(−ΣG)`; box budgets and Carleson measure; eight-way log-mean equivalence, Abel form ⇔ depth density `o(T)`; necessary-length laws (near-unit moments need `log N≥log²T/(6K₀)`); last-scale floor; long-moment slope, one-window and positive-proportion forms; Möbius zero condensation; dilation identity: RH ⇔ zero surplus ⇔ Szegő budget ratio equality, Euler prefixes invariant, Dirichlet Gram = Abel squares = Laguerre energy.

Structure [D]: an Euler mollifier over primes `≤y` has length `e^{θ(y)}`, so the necessary length is that of an Euler mollifier over primes up to `≈c log²T`, the same scale where prime phases become absolutely non-aligned (S11). The near-line wall is the dark range.

| | Obstacle | Strength |
|---|---|---|
| A17, A18, A21 | Selberg `O(T)` depth density; twisted moments past `21/50` [C]; census items | — |
| B57 | Depth density `o(T)`, equivalently log-mean `→0` | sub |
| B58 | `D_win` | sub |
| B59 | Cluster wall | sub |
| B60 | Exponential moments of the Green potential at deep zeros | sub |
| B61 | A detector past the last scale | sub |
| B62 | Cofinal long moment | RH |
| B66 | Near-unit holomorphic budgets; zero dilation surplus | RH |
| B82 | Inner-field decay | ≥qRH |

### S6. Production and precision

Routes: WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, LI, AIP. Programmes: ASRP, APR, AGT, AKLT, AE, AAD, RAC, MMD, SPAL.

Established [L unless marked]: band ⇔ classical criteria; integer lag; entry filters; length–precision law; gauge exponents `[Θ,1]`; Nair lattice; producers `c=μ∗h`, mollifiers on `Re s=1`; floor `c/(√K(1+log K))`; rate `K^{−a}` ⇒ `Re ρ≤1−a`; all `a<½` ⇒ RH; RH gives `a<¼`, so the RH exponent lies in `[¼,½]`; compensated producer with smooth letters; parity-neutral producers at every rate; extremal fakes with `≤K` atoms [L/S]; cut kernel = zeros; strip superpositions classified; finite-energy kernel mass annihilation ⇒ RH; exact identity pins `λ`; exchange law; count-distance rigidity at `o(log)`; bounded count with a new zero (signed generators); Carlitz stencil; torsion energy; cubic Gauss conversion, cubic Eisenstein series, resolvent and residue at `4/3` [L], constant term supported on cubes [S].

| | Obstacle | Strength |
|---|---|---|
| A21, A30, A31, A33 | Chowla [C]; best RH exponent in `[¼,½]` (unverified); discrete Beurling one-off [C]; cubic residue `R≠0` and Gauss-sum coefficients [C] | — |
| B48 | A deciding input at square-root precision | RH |
| B55 | Any polynomial stencil rate (qRH); rates `a↑½` (RH) | ≥qRH to RH |
| B15 | Mertens level past VK | sub |
| B14 | Any interior width value | ≥qRH |
| B56 | `Θ<1⇒Θ=½` | sub |
| B67 | Parity at power saving (a strip up to twist-absorbed zeros) | ≥qRH |
| B91 | Finite-energy cut-kernel vectors have mass zero | RH |
| B94 | Transfer of the cubic conversion to rational-integer Möbius | past VK at least |
| B98 | Positive-generator integer-norm system with a new zero: does count distance `O(x^θ)` forbid new zeros right of `θ`? | method |

### S7. Reflection and carriers

Routes: PM; W1C (candidate); RN and PTR in part. Programmes: RIT, ART, AOT, ACP, BHR, ASH.

Established [L]: resonance ⇔ `ζ(2s)=0`; `Q=2Re[WH,WH]`; `D_s≤0`, zero iff `Re s=¼`; Hecke dispersion `V_p`; scattering Blaschke product; exact modular horizon, ringdown in the modes of zeros, quarter-line bound ⇔ RH, general `L²` data; graph black holes with flux, unitarity, Hecke at every degree and class; Krein flux law on every system; count law ⇔ `t²≤4q`; Manin's Hasse from heights on a true curve; trivial-zero law `g≤m+1`; throats have FE only at genus `≤1`; genus-two graph with FE and a slow resonance for `q≥4`.

Structure [D]: the wave system does not know the partner law; at genus two the functional equation is supplied by branching and still does not force damping. The separating law is the count.

| | Obstacle | Strength |
|---|---|---|
| A25–A27 | All-`n` physical moments (unverified); Weyl law, metric of `L²` data, regularity, scalar sector; modular dictionary | — |
| A32 | Manin at higher genus through Jacobians; first test the genus-two graph of Γ118 [C] (unverified in corpus) | — |
| B68 | Independent `D_s≥0`, nonnegative Krein flux, integer-probe sign or all-zero dispersion bound | RH |
| B69 | Positive physical carrier | producer |
| B70 | Lower bound for `V_p` from the carrier | sub |
| B71 | Sharp decay of the smoothed resonant sum | RH |
| B87 | A count for `Q` over ℤ | RH |

### S8. Index and support

Routes: HKT, AKLT, SC, RIT, CWS through HF, ACS; LA. Established [L]: `κ(φ_c)=κ+1`; finite index ⇒ Lindelöf; `κ∈{0,∞}` under escape, mixing or decay; window index counts critical lengths; `sup_dN_d` off-line multiplicity; `K_ζ^n` PD ⇔ RH; finite support makes almost every prime tower decide.

| | Obstacle | Strength |
|---|---|---|
| B12 | Index ceiling uniform in resolution | ≥qRH |
| B13 | Exclude finite nonzero off-line support | sub |
| B23 | `N_d` bounded | ≥qRH |

### S9. Abscissa split, recurrence, one-offs

Routes: BAG, JAS shell, SC undamped, WL sparse samples, ZCG one-off branch. Programmes: AKLT, ZCG, AIF, APD, AAD, RAC, PTT, TAPO, SPAL.

Established [L]:
- Split RH ⇔ ZAL ∧ AAL ⇔ ZAL ∧ zero-disc weak recurrence; AAL producers (bounded lags, twisted plateaux, JAS, towers, cone, shell positivity, typical JAS positivity, finite-measure lag excursions, bounded return at each right zero, slow aligned returns on right discs).
- ¬AAL: finite oscillation of `ψ(x)−x`, unique `T`, quantized coefficients, remainder ceiling, sign changes, two-prime dilation annihilation, rightmost-zero jets with long-shift correlation `m²`.
- Transport: discs crossing `Re s=½` force `|ζ|≥cτ^b`, so the polynomial slow-return premise there is RH; right discs carry the AAL receiver with explicit `transportExponent`. Head returns have `N<1024(log τ)⁴(log log τ)²`; the first nontrivial return of the primes `≤N` is above `N`.
- Tail: zeros of ζ are zeros of `ζM_y` at every cut; returns at right zeros are tail-bad at every cut and have density zero; the head is frozen below resolution `1/log y`; the tail is conditionally Gaussian below the Kronecker scale.
- Hull: Haar-a.e. and fair-coin-a.e. `±1` fibres extend zero-free to `Re s>½` with natural boundary `½`; the Liouville point extends iff RH.
- Isolation: FE defect `≤1/6400`; count distance `o(log n)`; continuous one-offs exist; bounded counts with a new zero exist with signed generators.

Structure [D]: the random Euler model does not reach targets with zeros, so a bounded return at a zero is an arithmetic event at the Kronecker scale, not a typical one.

| | Obstacle | Strength |
|---|---|---|
| A23 | Resonator mean of `\|ζ(s+iτ)\|²` on Bohr sets below the Kronecker scale | — |
| A31 | Discrete Beurling one-off and its FE defect [C] | — |
| B83 | AAL | sub |
| B89 | A bounded aligned return at each right zero on a right disc, i.e. a tail event cancelling the head at every cut | sub |
| B96 | Conditional law of the Euler tail at the Kronecker scale | sub |
| B13 | Finite nonzero off-line support | sub |
| B84 | Smallest FE defect carrying a one-off | method |
| B72 | Cutoff-uniform target mass | RH |
| B82 | Inner-field decay | ≥qRH |

### S10. Count and effectivity

Routes: ACS, HF, PM integer probes; RW through window naive heights. Programmes: AE, CWS, LST, KPA, ASH, RIT.

Established [L]: polar surface calculus; Tate law (degree-two form `≥0` iff a function bounded below lies at bounded distance); five currencies; curve Rosati has a naive height ⇔ unitary; Manin's height on twisted elliptic curves with Hasse from the count law; theta `h⁰` with exact RR; Künneth `h¹` split; Λ as an intersection number of torsion orbits; sign lost in `log(1/(1−r))Σx²`; source cone and all-aperture RR; Bézout ⇔ RH.

| | Obstacle | Strength |
|---|---|---|
| A32 | Manin at higher genus | — |
| B87 | A function on correspondences, nonnegative for an arithmetic reason, at bounded distance from `Q` | RH |
| B88 | Torsion self-energy paid by the archimedean reserve at finite `r` | RH |
| B95 | An abelian group with Hecke endomorphisms `T_n`, `T_n′T_n=n`, whose trace form is `Q` | producer |
| B65 | Genus upper law; logarithmic Serre duality; first Epstein real zero | indep. to sub |

### S11. Prime orbit at finite time

Routes: BAG, TH, SRT, RW, ZCG carriers, every route at the all-height wall. Programmes: PTT, TAPO, SPAL.

Established [L]:
- Boxes: every window of length `exp(10y√(log y·log log y/δ))` enters every `δ`-box on primes `≤y`; some box of radius `ρ` is missed below `log T≈π(y)log(π/(4ρ))` [S].
- Savings: `8/(10⁹L⁶ℓ⁴)` at length `48L²ℓ` from low-energy squared words; `t^{−δ}` at `L^A`; no cancellation below `c log T` at some height; square-root cancellation at all dyadic lengths `Y..T/log T` off measure `≪TY^{−2ε}`.
- First return: brackets at every precision; RH bracket at precision `≍y^{−9/2}`; weak returns = extreme values of `ζ(1+it)`; fade length `exp(O(|ζ(1+iτ)|))`.
- Heavy returns: proportional saving ⇔ no early heavy return.
- Conditional tail: decoupling by unique factorization, Gaussian conditional moments, large deviations, all below the Kronecker scale.
- Ceilings: rounded orbit; one word `≤1/(2(k+2))`; binomial phase `2/(k+1)` per block; the jet of `t log` moves, so exotic blocks are `O(ηH+1)`; comb inequality reaches first returns polynomial in the length.
- Archimedean place: `h↦t log(1+h/x)` is additive only up to `|t|hh′/x²`; the depth aspect is exact.
- Certificates: Euler coordinates stop at `Re s=1`; head–tail certificate ⇔ tail-good; Ξ-current certificate exactly above the size curve.

Structure [D]: between `log t` and `exp((log t)^{2/3})` the Taylor degree of `t log(n+h)` exceeds `(log length)²`. The required saving at the size curve is `≈εL/ℓ`, the proved one `≈L⁻⁶`.

| | Obstacle | Strength |
|---|---|---|
| A14, A24 | Moment upgrade; certified scans and brackets | — |
| A22 | VK bound `\|ζ(1+it)\|≪(log t)^{2/3+ε}` in the first-return lower bracket [C] | — |
| A34 | Integrate the [S] modules (mixing time from below, questions of the field) | — |
| B46 | Proportional saving at length `(log X)^{2K}`, all heights | sub |
| B97 | Constant-precision first return: `log R(y,δ)≥y^c` for fixed `δ`, for every heavy subset | sub |
| B100 | A saving for `t log n` on moving families of blocks past Vinogradov's degree | sub |
| B15 | Past VK | sub |
| B20 | Oscillation of the actual amplitude with the height | RH |

## 3. Live routes

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy or one-sided `Φ` → RH.
- **Established [L/K]:** bounded endpoint energy ⇔ RH; integer lag ⇔ RH; `Ω±(√n)`; first-band abscissa `2Θ`; gauge exponents `[Θ,1]`; subtracted lag ⇔ ZAL; finite-measure excursions ⇒ AAL. Production support: under RH stencil exponent `[¼,½]`; cut kernel; exact parity identity.
- **(a)** A30.
- **(b)** Bounded endpoint energy and first-band square-root bound (B49); half-power at the trivial gauge (B50); deciding input (B48); past VK (B15).

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every radius → RH.
- **Established:** blocks S2, S3; cone nonempty ⇔ RH; relative compactness ⇔ RH; naive height on every window ⇔ RH.
- **(a)** A1–A3, A15, A16.
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
- **Established [L]:** Hausdorff rows nonnegative for `r≥C₀(k+1)²`; remaining entries ⇔ RH; exterior diagonal criterion at `218/25`.
- **(a)** Verified rows (A1).
- **(b)** Signs below the quadratic boundary, exterior `K(z,z)≥0`, or `TV(n)/qⁿ→0` (B31).

### MC — Möbius cancellation
- **Path:** half-power Möbius or Liouville cancellation → RH.
- **Established [L/K]:** damped energy ⇔ RH; one-point form; VK Hilbert energy; Möbius zeros condense on `Re s=Θ`; gauge genericity; producer rates; parity exponent = zero abscissa; exact identity pins `λ`; cubic branch: ideal Möbius = cubic Gauss coefficient, actual cubic Eisenstein series with Kubota character, Fourier unfolding, Fredholm pencil, meromorphic resolvent, residue at `4/3` finite-dimensional [L], constant term on cubes [S].
- **(a)** Chowla [C] (A21); cubic residue nonvanishing and Gauss-sum coefficients (A33).
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
- **Established [L]:** blocks S4, S5, S9; cameras; sharp location; one-off structure and jets; maximal-angle law; the extremal law alone admits a polynomial model.
- **(a)** A19.
- **(b)** Small-time collisions (B24); frequency (B25); time-0 selector (B26); non-size frequency input (B47); runs (B27); FE-pair reality (B76); crowded zeros (B59); long-shift `Λ` correlation or a bounded return in the one-off world (B83, B89); rotated relation or a contradiction using growth or arithmetic (B92, B93).

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH.
- **Established [L]:** defect trace class; multiplicity `≤` trace norm; Gaussian passage criterion.
- **(a)** None that moves the route.
- **(b)** Trace norm `<1` on every rectangle or bounded Gaussian oscillation (B38).

### HF — Hodge / Hecke / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** blocks S1, S10; source-work `≤2` ⇔ RH; top-window non-escape and complement Gårding at every ratio [S]; unrestricted Gårding false [L].
- **(a)** A9–A13.
- **(b)** Full-space sign at every `K` (B6); middle band (B7); head windows (B8); source-work ceiling (B41); top coprime stratum (B10); zero modes (B9); exact SOS (B11); Rosati and band poles (B78, B79); count (B87).

### CHMD — Causal hyperbolic–modular duality
- **Path:** one-sided bounded prime wave or odd Doob half-threshold bound → RH.
- **Established [L]:** wave and Doob receivers; normalized prime−pole decay; nonfirst source keeps `1−ε` of Gamma.
- **(a)** None that moves the route.
- **(b)** Either side of the unnormalized wave bound, or the complete odd sign (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel → RH.
- **Established [L]:** rank ten at `0<a≤½`; rank `N` from verified height; VK collar; two-atom and chain signs; `S=Π_pT_pA`; insertion cone with exact threshold `½`; theta amplitude not all-base torus-positive; locking = torus positivity, convergence essential; columns add; `current=2|Ξ|²Re ξ′/ξ`; the Ξ-current lifts to the torus with the pole as worst point, so a frozen certificate exists exactly above the size curve; Euler coordinates stop at `Re s=1`.
- **Structure [D]:** a proof through `S` must use oscillation of the amplitude with the height, and below the size curve the certificate is a tail-good condition.
- **Numerics:** positive at actual phases `b≤775`; torus-uniform positivity fails once primes `≲19–47` are free [N].
- **(a)** Rank 11 (A4); tail-failure certificate (A5); scans and brackets (A24); verified ranks (A1).
- **(b)** Exact torus law for `S*` and `{2,3}` cross-chain positivity (B19); amplitude oscillation with the height (B20); all ranks (B21); tail law at the Kronecker scale (B96).

### RN — Theta renewal
- **Path:** two-ended renewal → no joint nodes → RH.
- **Established [L]:** `det₂` gives `D`, not Ξ; Ξ zeros = joint nodes; energy comparison ⇔ RH.
- **(a)** None.
- **(b)** Joint-node exclusion or energy comparison (B36).

### WD — Ward / collision / long moments
- **Path:** source current, window energy or long moments → RH.
- **Established [L]:** block S5; one-window form; slope rigidity.
- **(a)** A17, A18.
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
- **Path:** scattering source → Krein/Lewis positivity, integer-probe sign, or dispersion bound → RH.
- **Established:** block S7; integer-probe positivity ⇔ RH; Krein flux sign ⇔ RH; count law gives damping at genus one; FE at genus two does not.
- **(a)** A25–A27, A32.
- **(b)** `D_s≥0`, Krein flux, probe sign or dispersion bound (B68); physical carrier (B69); `V_p` lower bound (B70); resonant decay (B71); count (B87).

### PTR — Cosine source / photonic
- **Path:** `A_h` collision-free descent → RH.
- **Established [L]:** sech handoff; strict Laguerre for `h≥½` and above VK; sign at every `0<h<½` ⇔ RH.
- **(a)** None.
- **(b)** Strict sign below VK (B29); lossless prime-faithful stack (B69).

### JAS — Joint ancestry
- **Path:** subpower control on moving finite power windows → RH.
- **Established [L]:** RH criterion on `m<k≤m+m/log(m+1)`; finite admission; shell positivity infinitely often ⇒ AAL; typical JAS positivity ⇒ AAL.
- **(a)** None.
- **(b)** Uniform control on the moving window (B51); shell signs plus ZAL.

### CTF — Chronological tail / Báez–Duarte
- **Path:** approximation, defect, BSY sign, log-dilation equality, cut-kernel mass or mollifier infimum → RH.
- **Established [L]:** rows ⇔ RH; sharp defect, sparse subpolynomial ⇒ RH; BSY `I≤0` ⇔ RH; positive-proportion form; exact infimum `exp(2I(1))`; rigidity; one-`δ` dilation equality ⇔ Szegő ratio equality ⇔ RH; Euler prefixes invariant; finite-energy cut-kernel mass annihilation ⇒ RH.
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
- **Established:** blocks S9, S11; cutoff-uniform mass ⇔ RH; transport on right discs with explicit exponent; crossing discs force power growth; returns at zeros tail-bad at every cut; first return above the length [L].
- **(a)** A23, A22.
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
- **Established [L/K/S]:** full-family receivers; depth corridors; two-lobe bound; cut crystal; sharp location; local pair cost; isolated-zero entry; critical-ratio non-escape [S].
- **(a)** A9–A12, A14.
- **(b)** Complementary-window sign, remaining-depth control (B6, B7, B12); all-height column (B46).

### ACT — Single shift
- **Path:** one shift pays every even compact profile → odd positivity → RH.
- **Established [L/K]:** receiver; `{2,3,4}` band; floors through `a_k`.
- **(a)** A7.
- **(b)** One shift uniform in profile (B44, B4).

### AIP — Incidence
- **Path:** complete reflected-prime/pole allocation → subexponential cost → RH.
- **Established [L/K]:** allocation; VK cost; capacity; channel law on gcd twists.
- **(a)** A9–A13.
- **(b)** `C_σe^{2σr}` cost (B45); packet complement (B6, B7).

### SC — Stokes / Witt–Krein
- **Path:** glued index `≤1`, bounded damped coupling, or undamped coupling plus ZAL → RH.
- **Established [L]:** `κ(φ_c)=κ+1`; damped bound ⇔ RH; undamped cone bound ⇒ AAL.
- **(a)** None that moves the route.
- **(b)** Arithmetic coupling bound; tensor loss (B39); B9, B11, B13.

### ACS — Castelnuovo–Severi
- **Path:** source energy → all-aperture Bézout → RH.
- **Established [L/K]:** block S10; source cone and RR; Bézout ⇔ RH; primitive `h¹` coercive for `a≤181/500`; Kloosterman purity; column projections; Toeplitz minors `≤200`; typical-height sign; degree-one Selberg classification.
- **(a)** A28, A29, A32.
- **(b)** Source-energy sign (B40, B1); count or Rosati producer (B78, B87); global trace (B85); mixed Young shapes (B86); B65; B28.

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
| AIF | inner field, Szegő infimum, rigidity, Carleson measure, dilation quotient with Szegő ratio, conformal Dirichlet Gram and Laguerre factorization, causal certificate, forward map, restoring bound, Bohr profiles, insertion cone and critical-strip Bernstein, columns, local onset field | A17 | B2, B57, B66, B82 |
| AAD | producers, uncertainty, peak law, half scale, Möbius producer, compensated producer with smooth letters, quarter rate under RH, parity-neutral rate, rate = Mertens scale, extremal fakes sparse, returns are prime returns, transport count, missing input, slow returns right of the line | A30 | B15, B55, B89 |
| RAC | cut identity and kernel beyond power laws, unique fake, finite-level radius, carry, ledger hierarchy, twin at every degree, parity exponent, exact parity identity, exchange law, bounded count with a new zero, first return above the length, cancellation at almost every height, maximal angle, extremal-law model, rotated relations | none | B67, B91, B92, B93 |
| TAPO | first return and its brackets, extreme-value dictionary, precision law, heavy returns, fade, tail–head decoupling, conditional moments, head resolution, tail of a return, jet of the logarithm, depth aspect, Euler coordinates, comb | A22, A34 | B89, B96, B97, B100 |
| SPAL | shifted-product rigidity, tuple reconstruction, resolution sharpness, collision cells, winding occupancy, finite alignment returns, norm-collision amplification, count-distance rigidity, logarithmic floor, positive near-count model | A31 | B98 |
| PTT | Bohr isometry, boxes at square-root cost, savings from low-energy words, rounded orbit, discrepancy, hull with natural boundary over Haar and order-two points, lacunary prime characters, Ξ-current lift, certificates | A14, A24, A34 | B46, B100 |
| ASH | graph black holes, Krein law, one clock, KMS, rank barrier, bulk log-mean, count law, integer probes, Manin heights, trivial zeros of a cusp, throats, genus-two graph | A27, A32 | B68, B87 |
| BHR | modular wave, metric, echo train, causal symbol, ringdown, pulses, general data, cusp channel | A26 | B71 |
| MMD | cubic Gauss conversion, cubic quotient, Eisenstein series, Fourier unfolding, Fredholm pencil, resolvent, residue [L]; constant term on cubes [S] | A33 | B94 |
| AE, KPA | polar calculus, Tate law, naive heights, five currencies, torsion intersection and energy, height principles | none | B87, B88 |
| CSTW | canonical system, scalar flow, soft kick, Green corner, AC traces, `L¹` drift, sampling | A15, A16 | B2, B3 |
| CHT | margin law, pinning, datum, bands, bounded extremals, edge law | A6 | B16 |
| VHR | height 67; window, Li, Hausdorff, heat, Jensen, PF, theta rungs | A1, A2 | none; decides no all-aperture statement |
| NGF | frequency, blow-up, gap laws, maximum principle, crystal and reality at critical scale | A19 | B24–B27, B47 |
| MZF | Selberg CLT, cameras, hyperbolic density, derivative law, rigidity, last scale, Möbius zero condensation | A18 | B57–B61 |
| FFP | `N_d` law, saddle region, stability dictionary, bulk blindness | A20 | B22, B23 |
| ADO | carrier repulsion; exceptional set of dimension zero; FE-pair flatness | none | B77 |
| APR | necessary length, filters, prefix amplification, collar laws | A18 | B48 |
| AKLT, ASRP | Stepanov over ℤ, Nair lattice, integrality halves, stencil ceilings; AAL producers | none | B48, B83 |
| APD, SEL | Hamburger rigidity, defect `1/6400` isolation, one-off models, degree-one classification | A31 | B80, B84 |
| PBAP, W3 | blind positivity, exact null blind test | none | B18 |
| WVL | universal threshold, two-lobe, cut crystal | none | none beyond B1 |
| AHD/CACT | aliasing limits, Γ-liminf, polar capacity, far margin, collar Gårding [L]; top-window non-escape and complement Gårding [S] | A9–A13 | B6–B8 |
| CAF, TCS | two-atom, chains, Euler product, current, rank ten | A4, A5, A24 | B19–B21 |
| AK, Representation | column Young projections, curve characters, endpoint character, Kloosterman traces | A28, A29 | B85, B86 |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ sign or budget | RW, EWU, OWU, ACT, CHMD, SZ, RN, ACS, AIP, SRT, SC, LI, TT (odd) |
| Σ critical ratio: top window plus low packet (Σ126, Σ127) | HF, SRT, AIP packet branches |
| Σ continuation at small time | ZCG, PTR, LA, GTA, XN, HCF, PA, TH |
| Π square-root precision and long moments | WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| Γ reflection and selection | PM, BAG, SEC, CDC, PCS |
| Missing source landing | APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF |
| Missing count, transversal | ACS, HF, PM, RW through windows |
| Dark range (Kronecker scale), transversal | every route at all heights; BAG and ZCG one-off branches; TH certificates; WD near-unit moments |
