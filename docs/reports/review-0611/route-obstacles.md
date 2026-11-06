# Route obstacles — status quo

Scope: 38 live route formulations, 9 candidates and their supporting programmes. For each: path, what is established, obstacles that are **(a) just work**, obstacles that are **(b) open mathematics nobody has a solution to**.

Corpus checkpoint: commit `c7d60e30c6` plus the working tree of 2026-11-06.

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means an independent source mechanism or landing is missing. Formulations are not independent mechanisms: HJ is PA, BSH is CDC, FEL's BSY criterion belongs to CTF. A criterion, a source construction, a quotient equality or a scalar grade does not discharge an arithmetic sign or vanishing.

**Evidence.** `[L]` Lean source. `[S]` Lean source marked unfinished or unintegrated in the frontier map. `[K]` Lean with transitive axiom audit. `[D]` mathematical deduction, not a Lean theorem. `[N]` numerical, uncertified. `[C]` classical literature, not formalized.

**Strength.** RH; ≥qRH (zero-free half-plane or Lindelöf); sub (strictly below quasi-RH); method; indep. (independent of RH).

**Labels.** `A*` just-work items and `B*` open problems are listed in full in [obstacles-summary.md](obstacles-summary.md). An A item is known mathematics, finite computation, effectivization or assembly of proved pieces; `(unverified)` marks A items whose difficulty is not established.

**Notation.** Windows `[−a,a]`. `W` Weil's form, `w_n=Λ(n)n^{−1/2}`, `H` the archimedean–polar form, `P` the arithmetic part, `W=H−P`. `μ(a)` ground energy. `a*(ζ)` onset aperture. `ℋ(c)` Hardy interval, `𝒜(c)` window cone, `λ*(c)` its best margin. `K_a(z,z)` Weil reproducing kernel. `τ_L,τ_R` endpoint traces. `r=τ_R(i)/τ_L(i)`, `L=artanh r`, `m=cosh 2L=(1+r²)/(1−r²)`. `Ψ=½log H₁`, `q=Ψ′`. `H_t` the de Bruijn–Newman flow, `Λ_X` its local constant, `τ=t log²X`. `N_d` non-real root count of `R_d(Ξ)`. `w=zetaZeroWidth`, `Θ=½+w`, `Θ∞` asymptotic abscissa. ZAL: finitely many zeros beyond every positive depth (`Θ∞=½`). AAL: finitely many zeros right of `½+h` forces none (`Θ∞=Θ`). `E(s)=(s−1)ζ(s)/s`, `I(w)` inner field. `M_X` truncated Möbius polynomial, `E_X=ζM_X−1`. `ϱ` pseudo-hyperbolic ratio on `Re s>½`, `N(ρ)` normalized derivative at a right zero. `Φ(u)=Re Σ_ρ e^{u(ρ−½)}/(ρ(1−ρ))` lag function. `vkScale(T)=(log T)^{3/5}(log log T)^{−5/3}`. `L_T=log T` in near-line statements.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ ZAL ∧ AAL; ZAL ⇒ qRH | [L] | one half is at least quasi-RH, the other sits below it |
| Under AAL: RH ⇔ ZAL ⇔ finite off-line support ⇔ `κ(K_ζ)<∞` ⇔ bounded nonreal heat count ⇔ finite critical source energy ⇔ eventual Hadamard positivity ⇔ eventual central-gap budget | [L] | every large-height receiver reads RH once one-offs are gone |
| ¬AAL ⇔ finite top and bottom layers at `Re s=β*,1−β*` plus zero-free vertical strips across all heights | [L] | failure of AAL is a rigid world with a zero-free strip |
| RH ⇔ `a*(ζ)=⊤` ⇔ `1∈ℋ(c)` ∀c ⇔ `λ*(c)→0` ⇔ two-site PD ⇔ no finite contact | [L] | every window route measures one number |
| `L′=q−sinh 2L`, `(log K)′=2 cosh 2L`, `H₁H₂=1`; contact is `∫dx/(1−r²)=∞`; `q∈L¹` up to contact gives RH | [L] | the tower is one scalar flow |
| `\|κ(x)\|≤artanh e^{−2(x−c)}+∫_c^x\|q\|` with no dependence on `κ(c)`; kicked form with `Σ\|k_j\|` | [S] | contact is local; verified initial data is forgotten at rate 2 |
| Prime kick: `(Ψ(x)−Ψ(a))log(1/(x−a))→w(a)` from the right, none from the left | [L] | prime thresholds carry an integrable soft singularity |
| Window PD ⇔ predictor with positive margin and no zero of `A` in the closed disc, any sign pattern | [S] | frustration blocks positive gauges, not certificates; RH is existence of outer predictors |
| Every sequence in `(−1,1)` is the reflection data of exactly one passive even sequence; an echo train is passive iff each echo lies in its Schur band `(π_n−E_n,π_n+E_n)`; `Λ(n₀)` is explicit in the first reflector at step `log n₀` | [S] | reflection data are free coordinates and read the primes causally; the wall is the forward map |
| `c_φ(t)↛0` for every nonzero test, so far-translate energy never decouples; under RH far dipoles of unit mass have arbitrarily small energy | [S] | Lions' dichotomy fails; the space at infinity is the Bohr compactification of translations |
| On a Kronecker family the infimum of a sum of columns is the sum of the infima; `1−2Σc_icos(bℓ_i)≥0` iff `2Σ\|c_i\|≤1`; commensurable reflectors allow the Fejér train with `2Σ\|c_k\|=N` | [S] | positivity lives inside one prime at a time; across primes only size is available, paid by the base |
| Lattice at slack `s`: `s>0` Szegő, `s<0` finite negative witness, RH places every lattice at `s=0` with `Σγ²=∞` | [S] | zero slack is singularity of the spectral measure |
| `I(w)=Σm_ρG(w,ρ)≥0`; `inf_Q ∫‖ζ exp Q(φ_w)‖²P_w=exp(2∫log‖ζ‖P_w)`; RH ⇔ budgets at `w=1` reach 1 | [S] | the inner mass has a second expression; what is missing is a near-extremal construction |
| Over `𝔽_q`: inner mass `Σlog⁺‖β‖`, budgets reach 1 ⇔ unitary ⇔ Castelnuovo on the Frobenius span ⇔ reflectors in `(−1,1)` | [S] | the opposite sign is an intersection inequality there |
| RH through height 67 with no zero located; PF₂₀₀, slices `\|t\|≤133/2`, Li `n≤314`, rank ten | [L] | finite rungs are theorems; they decide nothing |
| Every route with a saving carries the same Vinogradov–Korobov saving | [L] | one width axis; interior values are zero-free strips |
| Exceptional heights `{X:Λ_Xlog X>κ}` have measure `≤T^{θ(κ)}`; zeros real and gaps crystalline at `τ≳κ(δ)` outside `δT` heights; isolated simple zero: `d−7η≤Λ_Xlog(X/2π)≤d+17η` | [L] | the typical-height layer is closed down to bounded `τ` |
| `Φe^{−τx²}` has the same parabolic laws and non-real zeros below `τ`; central inequality stronger than RH | [L] | parabolic structure cannot select time 0 |
| `T⁻¹∫_T^{2T}log‖ζ(½+it)‖dt→0` ⇔ `100%` critical-scale clustering ⇔ six further forms | [L] | the near-line layer is one number |
| Isolated zeros obey rate 2 without separation; `N(ρ)=Πϱ^{m}` over all other right zeros | [L/S] | negative moments of `ζ′` at zeros are the remaining input |
| Last-scale floor; necessary length; length–precision law; slope `2wθ`; RH in one bounded window | [L] | polynomial detectors stop at depth `≍log log V/θ` |
| `S(a,b)=Σ_Nτ_b(N)A(log N)`, `S=Π_pT_pA`; torus-positive amplitudes with left growth `κ<½` are the exponentially convex ones; `A` is log-concave | [L/S] | TH needs height dependence of the amplitude, not phase locking at a fixed amplitude |
| `current=2‖Ξ‖²Re ξ′/ξ(½+a+ib)` | [L] | TH reads Gamma speed against Euler speed, the inequality of the ZCG carriers [D] |
| `V_p(ρ,Y)=2(1−p^{Reρ−1})`; all-`n` Hecke moments are a Poisson mixture positive for every `Re u<0` | [L] | Hecke dispersion reads depth directly; `C*`-positivity is blind |
| `φ(s)=Λ(2s−1)/Λ(2s)` has zeros at `(1+ρ)/2`; Schur positivity blind to their position; `c_Y` zeros on the line for `Y>1`; `‖ζ(1+it)‖≥c/(t³log²t)` from the carrier | [L] | PM reaches the edge by unitarity; `φ(s)(s−1)/s` is a Blaschke product whose zeros have depth `¼` under RH [D] |
| `ψ(n+1)=max log(1/∫₀¹P)` over integer `P`; integrality exponent is `Θ`; balanced stencils reach slope `1+ε`, `C_ε` non-explicit; integer sup-norm ceiling `e^{−0.87n}` | [L] | Stepanov over `ℤ` loses nothing at integrality; the rate of production is a width axis [D] |
| Pair recurrence at typical base heights; returns at a zero `≤T^θ`; continuous Beurling models have one-off zeros and no recurrence; exact FE forces rational primes, mismatch at `N` costs defect `>1/(400N²)` | [L] | one-offs are excluded only by inputs special to the rational primes |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | Primes pay the archimedean–polar deficit by sign in a frustrated critical form | format exact on every window; causal certificate exact; size payment ends before half-width `21/40` |
| M2 Calibration | Window cones, blind positivity, margin | cone pinned at rate `e^{−c/1104}`; exact null blind test; ceiling doubly exponential; sign open |
| M3 Canonical flow | `L,q` of the Weil chain | exact to contact; contact local; contact-uniform control open |
| M4 Reflection | Krein/Lewis positivity, Eisenstein carrier, Hecke dispersion | coefficient completion closed; depth read exactly; `D_s≥0` open |
| M5 Square-root cancellation | One smoothed prime count, long moments, auxiliaries | receivers closed; integrality exact; arithmetic estimates open |
| M6 Continuation | Heat, cosine, Jensen | high-time and typical-height regions closed; small time at all heights open |
| M7 Zero geometry | Cameras, Blaschke factors, inner field | isolated zeros at rate 2; clusters open; log-mean open |
| M8 Recurrence | Transport of zeros by vertical returns | transport closed; pair returns at typical base; returns at a zero open |
| Amplifiers | Diophantine repulsion, integrality as amplification | amplify a certificate, produce none |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve

Routes: HF, SRT, AIP, ACT, ACS (atomic), SC, CHMD (index). Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF.

Established:
- Full tilted-spline matrix PD for `1≤c≤(log N)^α`, `α<1/8` [L], through one small multiple `c≤2K₀(log N)^{1/8}` [K].
- Every compact C² profile: energy `≥a e^{−Bc}‖x‖²` on conductors `≤N^θ`, every `θ<¼`, `c≤b log log N` [L].
- Every fixed ratio `R=c⁸/log N`: critical pencil `κQ+(7J/R)∫e^{−8y}H²`, aliasing limit, fixed-family inertia, positive low packet through `⌊(log N)^{13/32}⌋` [K], polar capacity `S_A²/(J₁/R+κg)` [K].
- Weighted floor `Q(H)≥−F(p)∫e^{−pu}H²`, `p>1`, independent of aperture [L].
- Atomic synthesis: mixed mass, below-grid recovery, sharp weighted high-aliasing floor along strong `L¹` limits; prime shifts infinitesimal in `e^{−8y}`; bounded weighted collar mass; exponential control of `L¹` and polar tails; physical plus Fourier tails give `L²` precompactness; prefix mass `²≤C_φP/c` [L].
- Far reserve: for `c⁸≤R log N`, the complete energy dominates `(1/8)(D/c⁷)log N·M₇−(C_S+C′R)c·M₇` plus a quarter of the top archimedean energy, with `M₇` the seventh-weighted collar mass [L].
- Prefix Schur cost is the prefix residual, `A⁻¹≤20`; fixed conductor blocks have a positive Schur floor [L].
- Receiving modes with bounded charge and vanishing physical energy, capacity `log log N+O(1)` [L/K]. Literal coherent channel `≤KBVW|t|(1/√log Q+ω_Q(M)/log Q)` [L].
- Dirichlet-shift companions reduce long windows to heads; `d=2` unconditional; all `d` ⇔ RH [L].
- Far bubbles do not decouple: `Q(φ−φ(·+t))=2Q(φ)−2c_φ(t)` and `c_φ(t)↛0`; subsequential decoupling is not excluded [S].

Structure [D]:
- At `c⁸=R log N` the far-reserve balance is `c·[D/(8R)−C_S−C′R]·M₇`, positive iff `R<R₀`, `R₀` the positive root of `C′R²+C_SR−D/8=0`. So `R₀` is the size-only optimum.
- The limit pencil at a fixed ratio is a finite rung: far windows are paid by `e^{−8y}`, so sign on smooth families at ratio `R` follows from `a*(ζ)≥(1/8)log R+O(1)`. What is left at a fixed ratio is compactness of bounded-energy sequences.

| | Obstacle | Strength |
|---|---|---|
| A9–A13 | Constants, explicit `R₀`, channel norms, Schur debit, Γ-limit assembly | — |
| B6 | Profile decomposition at one ratio above `R₀`, with the Bohr compactification as the space at infinity | sub |
| B7 | Full-space sign eventually at every `K` | RH |
| B8 | Growing families, coalescing frequencies, conductors beyond `(log N)^{13/32}` | sub |
| B9 | Head thresholds for every `d` | RH |

### S2. Window tower and canonical flow

Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT (odd), HF, ACS, SRT, SZ, MSC. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF.

Established:
- Precontact de Branges chain, canonical system, `H₁H₂=1`, flux, sampling bases, positive on-line mimic at every precontact aperture, Gram AC with no atom [L].
- `L′=q−sinh 2L` in integrated form; `Ψ=L+θ`, `θ′=sinh 2L`; `K` at `z` grows `≤K(i,i)^{2|z|+1}`; contact criterion `lt_onsetAperture_iff_integral_reflection_bounded`; contact scaling `|q|≈(1+1/γ)m` at order `γ` [L].
- Spectral drift `q_y=τ_Lτ_R/K(x,iy)`, `Ψ(b)−Ψ(a)=lim_{y→∞}∫q_y`, `r_y→0` [L]. Abel limit only.
- Soft prime kick; `r` continuous before contact; traces and sources bounded on compact precontact intervals with constants retaining `1/μ` [L].
- Coming down from infinity, energy identity `∫q²=∫(L′²+sinh²2L)+[cosh 2L]`, Darboux pair `p″=(1+q²+q′)p`, `K=pw/2` [S].
- Born model: reflectors at `½log n`, kicks `|k_n|≤A log n/√n`, any phases and initial state: `|κ_n|≤¼log n+½log(2log n)+5A`, `1−r_n²≥e^{−10A}/(2√n log n)`. Contact by size is impossible; a collapse needs coherence over `≳√n` reflectors [S].
- Lattice flow `artanh r_{n+1}=artanh(s r_n)−artanh γ_n` [L]. Curve flow: `r_0=1`, inside `(−1,1)`, boundary at the number of angles with `r_R=B(0)`; Schur parameter = polar term − `N_{n+1}q^{−(n+1)/2}` − frozen prediction [L].
- Causal certificate, Szegő threshold, reflector `γ₁=(κ₀κ₂−κ₁²)/(κ₀²−κ₁²)`; free reflection coordinates, Schur band, prime dictionary, injective forward map [S].
- Cone: pinning, ceiling, bands, datum classification; exact two-sector format; `{2,3,4}` band below `log 5` [L].
- Exact null blind test `Φ=Ξg`, sharp tail exponent one [L].
- Aperture flow strictly decreasing, no non-radiating ground state [L]. Floors `(1/20000)/2^k` through `a_k<0.3621` [L].

Structure [D]: The margin ceiling [L] forces `log K≳e^{2a}`, so `m≳e^{2a}` on average on precontact intervals, above the Born bound `m≲ae^{a}`. The potential is therefore not the Born medium of the echo train: it is a nonlinear collective response.

| | Obstacle | Strength |
|---|---|---|
| A1–A3, A6–A8 | Certified verification, numeric heights, first-window membership, cone widths, anti-diagonals, Tate dimension one | — |
| A15–A18 | `Ψ∈AC_loc` before contact with `μ`-dependent constants, numerical `r,m,q`, weight-specific window bounds, integration of [S] modules | — |
| B1 | Sign on every window | RH |
| B2 | Contact exclusion: `q∈L¹` up to every contact | RH |
| B3 | Bounded variation of `r` on bounded intervals, free of `1/μ` | sub |
| B4 | Two-sector certificate inequalities; outer predictors at every window; every actual echo in its Schur band | RH |
| B5 | Kick admission at every stage | RH |
| B17 | Decay law of `λ*(c)` | sub (rate) |
| B18 | Signed ground-state structure past `log ρ` | method |

### S3. Continuation and nodal geometry

Routes: ZCG, LA, PTR, HCF, PA, GTA, XN. Programmes: NGF, FFP, ADO, RHTower heat.

Established [L]:
- Collision criterion; horizon `(6600/9991+ε)/log X` from the profile margin `(c−w)²−4cE(w)≥m` with `c>½`; `c d²/log X≤Λ_X`; a heat coefficient below a fixed `κ₀` at all large `X` gives a zero-free half-plane.
- Fock identity, monotone frequency, order law, Hermite blow-up, Sturm drop, gap law, maximum principle, uniform mesh, cluster spread, crystal symbol, depth moments, finite-speed lateral energy, compression bound.
- Multiplicity `≤(3300/9991+ε)log X`.
- Density-one: `Λ_Xlog X→0`. Power-saving exceptional set `T^{θ(κ)}`. Critical scale: all zeros real, central gaps, crystal law `|(x′−x)·½log(x/2π)−π|≤ε` outside `δT` heights.
- Complex saddle at `u=y+2τℓ`; line model at power level; quotient by an isolated zero; sharp depth law for isolated simple zeros.
- `N_d` nondecreasing, supremum is off-line multiplicity, `N_d≤300√(d log d)`, inner roots real, Cauchy bulk blind.
- Cosine strict Laguerre `(Im ξ′)²+Re ξ Re ξ″>0` on `½<Re s<1` ⇔ RH; holds for `h≥½` and above VK.
- Fejér-budget verification through height 67.

| | Obstacle | Strength |
|---|---|---|
| A19, A20, A26 | Horizon toward its method floor, explicit `θ(κ)`, Jensen rung | — |
| B26 | Exclude collisions at arbitrarily small time, all heights | RH |
| B27 | Frequency `<1` at every putative collision | RH |
| B28 | An arithmetic input distinguishing `Φ` among `Φe^{−τx²}` | method |
| B29 | Runs of `k` simple critical zeros, every `k` | sub |
| B83 | An all-height frequency input not reducible to size: multiplicity `o(log X)` | sub |
| B24 | Outer-root control of `R_d(Ξ)` | RH |
| B25 | `N_d` bounded | ≥qRH |

### S4. Near-line geometry and long moments

Routes: WD, CTF, MC, TG; census. Programmes: CDG, APR, MZF, AIF.

Established:
- Selberg CLT; off-line `log|ζ|` is the prime field up to bounded error; barrier law; Lorentz mass exponential tail [L].
- Prime camera rate 2 for dominant zeros; Turán camera for bounded clusters; hyperbolic density theorem without separation; `N(ρ)≤Π_Dϱ` [L]. `N(ρ)=exp(−Σ_{a≠ρ}m_aG(ρ,a))` [S].
- Box budget `(2θ/5)Σm≤½log∫|ζM|²P_w−log|E(w)M(w)|`, arithmetic embedding, crowd, shadows [S].
- 8-way log-mean equivalence; Littlewood edge budget at all heights; Euler-mollifier log-mean `≤Σ_{p∈S}(3+6/log p)`; exponential tail moment [L].
- Jensen extremizer: moments do not determine the log-mean [L]. Necessary-length laws, last-scale floor, short weights blind, occupied windows lose one log, corridor exceptions [L].
- Long-moment slope `2wθ`, quantifier collapse, one-window and positive-proportion RH forms, exponent rigidity, Möbius zeros condense on `Re s=Θ`, collar factorization, zero-damping head `1−1/(D+1)` [L].

Structure [D]: Isolated means Carleson uniformly separated in `H²(Re s>½)`. Jensen with a second moment loses exactly the variance of `log|ζM|`, a positive constant at polynomial length, so `log-mean→0` cannot come from any second-moment bound with polynomial mollifiers.

| | Obstacle | Strength |
|---|---|---|
| A18, A22, A24 | Integration, moments past `21/50`, census items | — |
| B57 | `T⁻¹∫log‖ζ‖→0` (`100%` critical-scale clustering) | sub |
| B58 | `D_win` | sub |
| B59 | Cluster wall: Density Hypothesis rate for all near-line zeros | sub |
| B60 | Exponential moments of the Green potential at deep zeros | sub |
| B61 | A detector past the last scale | sub |
| B62 | Cofinal long moment bound | RH |
| B80 | Explicit near-extremal mollifiers: budgets near 1 | RH |
| B79 | Inner-field decay `I(½+h+it)→0` | ≥qRH |

### S5. Production and precision

Routes: WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, LI, AIP. Programmes: ASRP, APR, AGT, AKLT, AE.

Established [L]: band ⇔ every classical one-sided criterion; integer form `E(n)≤(2+γ−log 4π)√n` ⇔ RH; `Ω±(√n)` unconditional; entry filters; necessary length; length–precision law; gauge torus exponents `[Θ,1]`; Nair lattice exact; Siegel and Liouville halves each RH at square-root scale; integrality exponent `Θ`; univariate ceiling `e^{−0.87n}`; single-prime, finite-alphabet and non-alternating stencil ceilings; balanced multivariate stencils reach slope `1+ε` by Farkas duality.

Structure [D]: With `(c*1)=(Σλ_d)²` a stencil is a Selberg sieve weight and the slope ceiling is the parity factor. Passing it needs signed `f≥0`. A balanced stencil of alphabet `K` and slope `1+ε(K)`, with constants polynomial in `K`, gives a one-sided error `ε(x^η)x`, so `ε(K)` carries the same exponents as the prime number theorem error: `exp(−(log K)^α)`, `α=3/5` is VK; `K^{−c}` is quasi-RH.

| | Obstacle | Strength |
|---|---|---|
| A23, A25, A32 | Chowla, Selberg degree-one, explicit stencil families | — |
| B48 | A deciding input at square-root precision | RH |
| B55 | Explicit parity-selective producer with a rate past VK; polynomial rate gives a strip | sub to ≥qRH |
| B56 | `Θ<1⇒Θ=½` | sub |
| B16 | Past Vinogradov–Korobov | sub |

### S6. Reflection and carriers

Routes: PM; W1C (candidate); RN and PTR in part. Programmes: RIT, ART, AOT, ACP.

Established:
- Resonance ⇔ `ζ(2s)=0`; `Q=2Re[WH,WH]`; `D_s≤0`, zero iff `Re s=¼`; lifted Hecke and Lewis carriers; closed Cauchy reflection [L/K].
- Line law for `c_Y`, `Y>1`; boundary norm; `|ζ(1+it)|≥1/(6250t³log²t)`, `t≥2·10⁷`; full determinant has no reflection; Schur positivity blind to zero position [L].
- Height law `ν_Y`; rescaled height limit; uniform Hecke residual `≥(−2a)mass/1024`; mixed-prime one-step isometry; cutoff Gram kernel [L].
- `V_p(ρ,Y)=2(1−p^{Reρ−1})`, one-sided bound at one `p,Y` ⇔ RH, `≤2(1−p^{−½−β})` ⇔ half-plane bound; Poisson mixture positive for every `Re u<0`; bilateral Cauchy–Szegő Gram law [L].

Structure [D]:
- `S(s)=φ(s)(s−1)/s` has modulus 1 on `Re s=½`, is holomorphic on `Re s>½`, and decays only polynomially on the real axis, so it is a Blaschke product over `(1+ρ)/2`. Resonant states are its model-space kernels: the Gram law is the Szegő kernel. Hecke `T_p` acts on them by the Toeplitz symbol `p^{u}+p^{−u}`, and `V_p=2(1−|θ_p|²)` is the kernel norm of `θ_p=p^{u}`, `Re u<0`.
- The `c_Y` line law is unitarity of the same system; with FFP's drift law and PTR at `h=½` it sits on one Hermite–Biehler shift axis.

| | Obstacle | Strength |
|---|---|---|
| A28 | Physical mixed Hecke moments; Lean dictionary for `S` (unverified) | — |
| B66 | Independent `D_s≥0` or full Krein positivity | RH |
| B67 | Positive physical carrier | method |
| B68 | Zero-free curve inside the strip from the carrier: lower bound for `V_p` | sub |

### S7. Index and support

Routes: HKT, AKLT, SC, RIT, CWS through HF, ACS; LA. Established [L/S]: `κ(φ_c)=κ+1`; finite index ⇒ Lindelöf; `κ∈{0,∞}` under escape, mixing or height decay; `sup_dN_d` off-line multiplicity; `K_ζ^n` PD ⇔ RH; finite off-line support makes all but `(κ choose 2)` prime towers decide.

| | Obstacle | Strength |
|---|---|---|
| B13 | Index ceiling uniform in resolution | ≥qRH |
| B14 | Exclude finite nonzero off-line support | sub |
| B25 | `N_d` bounded | ≥qRH |

### S8. Abscissa split and recurrence

Routes: BAG, JAS shell branch, SC undamped branch, WL sparse samples. Programmes: AKLT, ZCG, AIF, APD.

Established:
- Split RH ⇔ ZAL ∧ AAL and RH ⇔ ZAL ∧ zero-disc weak recurrence [L]; RH ⇔ inner-field decay ∧ recurrence [S].
- Producers of AAL [L]: bounded lags on one progression or a log-dense set; nonnegative twisted plateau energies; JAS at level one; off-line chain; infinitely many bounded prime towers; one bounded two-prime cone; shell positivity infinitely often. All retain their source bound.
- Attained top: `Φ(mℓ)` unbounded on every progression; `K_ζ` bounded on finitely many towers; `|E_X|≥X^κ` off a vanishing set; top annihilators; twisted FE after Blaschke division [L].
- Transport of zeros by returns; returns at a zero `≤T^θ`, threshold `≍|g|r^m`; pair recurrence at typical base with relatively dense shifts; head-zero discs [L].
- Countermodels: continuous Beurling systems with exactly one off-line pair, `N(x)−ρx−C→0`, no recurrence; zero `L¹` FE defect forces rational primes; mismatch at `N` costs `>1/(400N²)` [L].
- Euler columns: `|c|>√p` gives `I_F(w)=log(|c|/√p)+log|G(w)|−log|F(w)|`, periodic right zeros, `I_F→log⁺(|c|/√p)` as `σ→∞`; `E=s−ρ` has `I_E=G(·,ρ)`, so a finite nontrivial inner factor exists as soon as no arithmetic is required [S].

Structure [D]: ¬AAL ⇔ `ψ(x)−x=x^{β}T(log x)+O(x^{β−η})` for some `β>½`, `η>0` and nonzero finite trigonometric polynomial `T`.

| | Obstacle | Strength |
|---|---|---|
| A31 | Lean form of the prime-side statement | — |
| B81 | AAL | sub |
| B82 | Upper side of the FE-defect trade-off | method |
| B69 | Cutoff-uniform target mass | RH |
| B79 | Inner-field decay | ≥qRH |

## 3. Live routes

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy or one-sided `Φ` → RH.
- **Established [L/K]:** bounded endpoint energy ⇔ RH; `E(n)≤(2+γ−log 4π)√n` ⇔ RH; `Ω±(√n)`; first-band abscissa `2Θ`; gauge exponents `[Θ,1]`; subtracted lag `Φ_S≤Me^{au}` ⇔ ZAL; density-zero excursions force top weight `≤0`.
- **(a)** Künneth and mixed jet calibration (A14).
- **(b)** `E(n)` upper bound at the ceiling; first-band square-root bound (B49); half-power at the trivial gauge (B50); parity-breaking producer (B48, B55).

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every radius → RH.
- **Established:** block S2.
- **(a)** A1–A3, A15–A18.
- **(b)** All-aperture sign or subexponential floor (B1, B15); `q∈L¹` up to contact (B2); bounded variation of `r` free of `1/μ` (B3); outer predictors at every window (B4); margin law (B17); blind positivity on nonnegative mixtures (B19).

### FU — Signed prime scheduling
- **Path:** signed Möbius history → one-sided sampled Abel bound → RH.
- **Established [L]:** one-sided criterion at fixed `m`; one controlled sample per backward window `N^{1−δ}`; exhaustive bounded-block payment at fixed horizons.
- **(a)** None that moves the route.
- **(b)** Complete-history cross-clock bound retaining seed, drift, covariance, endpoints (B44).

### CFC — First-clock lower bound
- **Path:** first-clock sine coefficient bounded below on a tail → RH.
- **Established [L]:** exact tail criterion; phase-natural transport is identity.
- **(a)** None.
- **(b)** Lower bound retaining prime, archimedean and endpoint terms (B44).

### RP — History floor
- **Path:** matched-quantile history → eventual linear floor → RH.
- **Established [L]:** exact linear-floor criterion; low-LCM payment; sublinear floor impossible.
- **(a)** None.
- **(b)** High-LCM pairs, moving core, singular-domain terms in one floor (B44).

### PA — Prime–archimedean passivity (HJ alias)
- **Path:** prime−Gamma source sign → RH.
- **Established [L]:** calibrated Hausdorff rows nonnegative for `r≥C₀(k+1)²`, explicit `C₀`, explicit core and tail constants; remaining entries ⇔ RH; exterior diagonal criterion at `218/25`; row `k+1≤(3/2)(T−1)`, `r≤RT³` from verified height.
- **(a)** Verified rows (A1).
- **(b)** Signs below the quadratic boundary uniformly in `k`, or `K(z,z)≥0` on the exterior sector, or `TV(n)/qⁿ→0` for every `q>1` (B33).

### MC — Möbius cancellation
- **Path:** half-power Möbius or Liouville cancellation → RH.
- **Established [L/K]:** bounded damped `E_ε` ⇔ RH; fixed `t₀`: `M_N(½+it₀)≪N^ε` ⇔ RH; undamped Hilbert energy `≤CTe^{−c·vkScale(T)}`; Möbius zeros condense on `Re s=Θ`, eventual zero-freeness on compacts of `Re s>½` avoiding 1 ⇔ RH; Haar-a.e. exponent `½`, Baire-generic `1`; flip exponent `max(θ,Θ)`.
- **(a)** Logarithmic two-point Chowla (A23).
- **(b)** Trivial-gauge cancellation or independent zero exclusion for `M_X` (B50); signed long-modulus tail (B50); parity-breaking producer (B48).

### TT — Theta tail / Wold
- **Path:** weighted endpoint energy bounded for each `0<t<½` → RH.
- **Established [L]:** Wold residual `O(e^{−c·vkScale(N)})`; `D_t+Q_t/2≥0`; boundedness ⇔ RH; uniform bound on a shrinking band.
- **(a)** None that moves the route.
- **(b)** `C_t` for every fixed `0<t<½`; endpoint `t=½` fails (B36). Odd branch: B4.

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted or sublinear root height → RH.
- **Established [L]:** block S3. RH ⇔ infinitely many unshifted degrees real; RH ⇔ sublinear upper-root height for mollified, shifted families; inner roots real; `N_d≤300√(d log d)`.
- **(a)** A26; A1.
- **(b)** Outer-root control (B24); bounded `N_d` gives finite support only (B25, B14).

### ZCG — Zero-configuration geometry / heat descent
- **Path:** half-Gaussian source → no positive-time collision → RH.
- **Established [L]:** blocks S3, S4; cameras, sharp location `e^{−c log³T}` under positivity at `λ·½log(T/2π)`, `λ>1`, with closed-form height.
- **(a)** A19, A20.
- **(b)** Collisions at small time, all heights (B26); frequency `<1` (B27); arithmetic time-0 selector (B28); all-height non-size frequency input (B83); runs (B29); FE-pair reality with coverage (B73); crowded and multiple zeros in the sharp depth law (B59).

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH.
- **Established [L]:** defect constructed, trace class; multiplicity `≤` trace norm; Gaussian passage alternative.
- **(a)** None that moves the route.
- **(b)** Trace norm `<1` on every rectangle, or bounded centered Gaussian oscillation (B40).

### HF — Hodge / Hecke / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** block S1; cofinal source-work `≤2` ⇔ RH; sharp Schur bound `½log N` [L].
- **(a)** A9–A14.
- **(b)** Compactness at one ratio above `R₀` (B6); full-space sign at every `K` (B7); growing twists and conductors (B8); head windows (B9); source-work ceiling (B43); top coprime stratum (B11); zero modes (B10); exact SOS on a two-prime lattice (B12); Rosati and band poles (B75, B76).

### CHMD — Causal hyperbolic–modular duality
- **Path:** one-sided bounded prime wave or odd Doob half-threshold bound → RH.
- **Established [L]:** wave and Doob receivers; normalized prime−pole decay `O(e^{−√log Y/92160000})`; nonfirst source retains fraction `1−ε` of Gamma energy.
- **(a)** Mixed Schur debit (A12).
- **(b)** Either side of the unnormalized wave bound, or complete odd sign paying first-prime, potential and polar terms (B37, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel → RH.
- **Established:** full-source rank ten at `0<a≤½` from height 67; rank `N` from height `41+6(N+2)log(N+2)`; all ranks in a VK collar; two-atom and `q^n`-chain all-rank sign; Euler product `S=Π_pT_pA`; `A` not a positive Laplace mixture; `current=2|Ξ|²Re ξ′/ξ` [L]. Insertion cone = exponentially convex amplitudes for left growth `κ<½`; fixed-amplitude locking = torus positivity; Hecke–Bessel, log-concavity and size-floor walls; columns add on Kronecker families [S].
- **Structure [D]:** `A` grows at the critical rate `e^{|x|/2}`, the density of the primes. Since `current/|Ξ|²=log(b/2π)+2Re ζ′/ζ+O(1/b)` and columns add, a prime set is torus-safe while the sum of its column minima stays above the Gamma base `log(b/2π)`. Locking is therefore carried by the growth of the Gamma term with `b`.
- **Numerics:** positive at actual phases, `b≤775`; torus-uniform positivity fails once primes `≲19–47` are free [N].
- **(a)** Rank 11 (A4); tail-failure certificate (A5); certified scans and `S*` brackets (A27); verified ranks (A1).
- **(b)** Torus law for `S*(a,b)` and cross-chain positivity on small `S` (B21); height-dependent invariant above `S*` (B22); all ranks at every `a` (B23).

### RN — Theta renewal
- **Path:** two-ended renewal → no joint nodes → RH.
- **Established [L]:** `det₂` gives `D`, not Ξ; `Ξ=0` ⇔ joint node for `|x|<¼,y>0`; energy comparison ⇔ RH; `D` has nonreal zeros.
- **(a)** None.
- **(b)** Joint-node exclusion or the energy comparison (B38).

### WD — Ward / collision / long moments
- **Path:** source current, window energy or long moments → RH.
- **Established [L]:** block S4; attained extrema and collision receivers; one-window form; slope rigidity.
- **(a)** A18, A22.
- **(b)** Cofinal long moment (B62); log-mean (B57); `D_win` (B58); cluster wall (B59); Green-potential moments (B60); detector past the last scale (B61); collision charge (B63).

### LI — Paired Li / Cayley ladders
- **Path:** primitive lower bound or Li sign → RH.
- **Established [L]:** guarded zero set finite, RH iff empty; ladder = Li coefficients; Li form `=−2` window form on primitive vectors over `𝔽_q`; subexponential response criterion; Li `n≤314` proved, `n≤4.7T` from verified height.
- **(a)** Verified entries (A1).
- **(b)** Budget at every guarded zero, primitive lower bound or response floor (B45).

### SZ — Suzuki screw
- **Path:** completed Abel residual bounded → RH.
- **Established [L]:** first variation = Weil energy; `|A_N|≤C√N e^{−c·vkScale(N)}`; bounded ⇔ RH.
- **(a)** None that moves the route.
- **(b)** `sup|A_N|<∞`, complete first-variation sign, or rectangular Ward lower bound (B39, B1).

### PM — Gauss–Mayer physical model
- **Path:** scattering source → Krein/Lewis positivity or one-prime dispersion bound → RH.
- **Established:** block S6.
- **(a)** A28.
- **(b)** Independent `D_s≥0`, renormalized Krein positivity or the all-zero dispersion bound (B66); positive physical carrier (B67); interior zero-free curve (B68).

### PTR — Cosine source / photonic
- **Path:** `A_h` collision-free descent → RH.
- **Established [L]:** sech handoff; strict Laguerre for `h≥½` and above VK; sign at every `0<h<½` ⇔ RH; lossless stack on one real window ⇔ RH.
- **(a)** None.
- **(b)** Strict sign below the VK boundary (B31); independent lossless prime-faithful stack (B67).

### JAS — Joint ancestry
- **Path:** subpower control on moving finite power windows → RH.
- **Established:** `RH⇔∀ε, frequently, |Riesz(m²,k)|≤m^{εk}` on `m<k≤m+m/log(m+1)`; finite admission; shell positivity infinitely often ⇒ AAL [L].
- **(a)** None.
- **(b)** Uniform arithmetic control on that window (B51); shell signs plus ZAL.

### CTF — Chronological tail / Báez–Duarte
- **Path:** approximation, defect, BSY sign or mollifier infimum → RH.
- **Established:** real unit-bounded rows ⇔ RH; sharp defect `D_y≥c_ρy^{2Re ρ−1}`, sparse subpolynomial ⇒ RH; BSY `I≤0⇔RH`; positive-proportion form ⇔ RH [L]. Exact infimum `exp(2I(1))` [S].
- **(a)** None that moves the route.
- **(b)** Vanishing-error rows, sparse defect, BSY sign, uniform positive proportion (B52); near-unit budgets (B80).

### HCF — Heat trace
- **Path:** both prime-log grids positive at every degree → RH.
- **Established [L]:** two-grid criterion at fixed offsets; explicit detector degree; bounded prime chirp ⇔ RH; chirp mean `→0` ⇔ RH; degree `+1≤T/4800` from verified height.
- **(a)** Verified degrees (A1).
- **(b)** Nonnegativity at every degree, or chirp bound or mean (B32).

### XN — Newton discs
- **Path:** line-centered self-map discs covering every zero → RH.
- **Established [L]:** coverage and closed-margin criteria; `ΔM≥0`; local damping preserves first jets.
- **(a)** None.
- **(b)** Cover every zero with `M≥0` throughout (B34).

### BAG — Self-return
- **Path:** strong self-return or head-target mass, or decay plus zero-disc recurrence → RH.
- **Established:** block S8; transfer closed; cutoff-uniform mass ⇔ RH [L].
- **(a)** A18.
- **(b)** Uniform positive mass (B69); returns on off-line-zero discs (B81); decay (B79).

### EWU — Even sector
- **Path:** even blind minimum `≥0` → RH.
- **Established [L]:** Hamburger form; neutral gauge; Markov to `log ρ`; blind minimum `≥1/20` for `a≤(log 2+1/50)/2`.
- **(a)** Verified windows (A1–A3).
- **(b)** Blind minimum `≥0` at every aperture; variance payment by signed jumps (B4, B18, B46).

### GTA — Schur charge
- **Path:** cofinally small quartic charge or compact full mode → RH.
- **Established [L]:** charge family; compactness ⇔ RH; late charge `≤HS/400`; small-spectrum suppression; skew energy has a positive limit.
- **(a)** None that moves the route.
- **(b)** Charge `<ε` at arbitrarily late stages; large spectral nodes uncontrolled (B35).

### OWU — Odd sector
- **Path:** odd polar-hyperplane positivity → RH.
- **Established [L/K]:** shifted Hamburger; unit window reads `w₂`; frustration; prime 3 cannot be deleted past `3/5` or replaced past `287/500`; variance retention necessary above `273/400`.
- **(a)** A1–A3, A6.
- **(b)** Sign at every aperture on compact C² odd `F` with `∫F sinh(x/2)=0`; retained-variance payment (B4, B18, B46).

### PBM — Regularized abscissa
- **Path:** pole-regularized prime series converges for every `σ>½` → RH.
- **Established [L]:** exact equivalence.
- **(a)** None.
- **(b)** `|Σ_{n<N}(Λ(n+1)−1)/log(n+1)|≤C_εN^{½+ε}` (B53).

### RB — Robin/Nicolas
- **Path:** eventual extremal divisor inequality → RH.
- **Established [L]:** colossally abundant and lcm reductions without `Θ<1`.
- **(a)** None.
- **(b)** Eventual inequality on colossally abundant `n`, or lcm defect bound (B54).

### SRT — Lag localization
- **Path:** complete two-bump sign or horizon-layer sign → RH.
- **Established [L/K]:** full-family receivers; depth `<10⁶exp(−a/(1200log(|γ|+3)))` under sign, `|γ|≥110`; universal threshold `k·pairEnergy(δ,a)≤(K/2)ℓe^{2(2π/ℓ+σ)a}`; two-lobe bound with absolute constants; cut crystal hides fixed depth from aperture `(log T)/36`; split-column receiver; closed-form sharp-location height.
- **(a)** A9.
- **(b)** Complementary-window sign, remaining-depth control, source kernel at every ratio (B7, B8, B13).

### ACT — Single shift
- **Path:** one shift pays every even compact profile → odd positivity → RH.
- **Established [L/K]:** single-shift receiver; `{2,3,4}` band with kicks `<0.991` of Lévy energy; floors through `a_k`.
- **(a)** Anti-diagonals (A7).
- **(b)** One shift uniform in profile paying `D_a` (B46, B4).

### AIP — Incidence
- **Path:** complete reflected-prime/pole allocation → subexponential cost → RH.
- **Established [L/K]:** allocation; `|cost|≤Ke^{r−c(2r)^{3/5}(log 2r)^{−5/3}}·Sobolev`; capacity; channel law.
- **(a)** A9–A12.
- **(b)** `C_σe^{2σr}` cost bound for every `σ>0` (B47); packet-branch complement (B6–B8).

### SC — Stokes / Witt–Krein
- **Path:** glued index `≤1`, bounded damped two-prime coupling, or undamped coupling plus ZAL → RH.
- **Established:** `κ(φ_c)=κ+1`; damped bound ⇔ RH; heat-average source; undamped cone bound ⇒ AAL [L].
- **(a)** A14.
- **(b)** Arithmetic coupling bound; sublinear tensor loss (B41); B10, B12, B14.

### ACS — Castelnuovo–Severi
- **Path:** source energy → all-aperture Bézout → RH.
- **Established [L/K]:** source cone; RR at every aperture; Bézout ⇔ RH; primitive `h¹` coercive for `a≤181/500`; tensor-uniform growth ⇔ purity on curves; Kloosterman curves pure by Stepanov; compactified moments with signed Tate correction; torus critical points and transverse quadrics counted; every column Young projection nonnegative; endpoint Toeplitz minors of order `≤200` nonnegative; character positivity ⇔ RH.
- **(a)** A14, A25, A29, A30.
- **(b)** Source-energy sign (B42, B1); independent count or Rosati producer (B75); arithmetic global trace (B84); mixed Young shapes (B85); genus, Serre duality, Epstein (B65).

### SEC — Seam / Fock
- **Path:** factorial jet energy at ξ zeros → RH.
- **Established [L]:** seam admitted; `F_ρ` identified; Fock bound ⇔ RH.
- **(a)** None.
- **(b)** Bound at actual zero parameters (B70).

### CDC — Dagger (BSH alias)
- **Path:** marked-repair equality at ξ zeros → RH.
- **Established [L]:** canonical potential, Euler-face metric, calibration; `N=1,n=2` equality suffices.
- **(a)** None.
- **(b)** Proof-erasure equality at every zero (B71).

### PCS — Co-shift
- **Path:** reflection-odd class vanishes at ξ zeros → RH.
- **Established [L]:** quotient vanishing ⇔ `n^{−ρ}−n^{−(1−ρ̄)}∈ℓ²` ⇔ RH; cutoffs converge strongly with a persistent gap.
- **(a)** None.
- **(b)** Vanishing at every zero; independent differential lift retaining the shift defect (B72).

## 4. Candidates

Each needs its independent mechanism first (B78).

| Candidate | Established [L] | (a) Just work | (b) Open mathematics |
|---|---|---|---|
| APF | prime/grade trace reconstruction on real labels | none | full-divisor exhaustion and RH landing |
| EGC | double-Gaussian zero-pair contour; count error `≤32ε²log T/T`; raw baseline persists | none | height-fibre isolation; outer landing |
| EWJ | all-depth reporter; norm exhaustion only on blind plane | none | faithful endpoint admission |
| FEL | KL accounting; BSY criterion belongs to CTF | none | calibrated predeclared history forcing BSY sign |
| IRK | finite idempotent traces; Meyer–Ξ free resolution | none | projective lift identifying trace with Chern charge |
| MSC | unweighted `L²` discrepancy; conormal transport | none | Sonin/Weil sign landing |
| RFHM | support source; creation; strong exhaustion | none | RH-sufficient orientation law |
| W1C | Lee–Yang receiver; one-interval convergence suffices | none | finite ferromagnetic producer converging to Ξ |
| WBF | Gram recovers magnitudes and phase class | none | arithmetic stream and Ξ landing |

## 5. Supporting programmes

| Programme | Established [L/S] | (a) Just work | (b) Open mathematics |
|---|---|---|---|
| AIF | inner field, Poisson–Jensen, Szegő infimum, box budgets, crowd, curve chain, causal certificate, Szegő threshold, inverse scattering with prime data, anchor flow, far bubbles, recurrence zero–one law, insertion cone, arithmetic Bernstein, torus walls, echo columns, Euler columns | A18 | B2, B57, B79, B80, B81 |
| CSTW | canonical system, scalar flow, soft kick, Green corner, charts, sampling, mimics | A15, A16 | B2, B3 |
| CHT | margin law, pinning, datum, bands, edge law | A6, A17 | B17 |
| VHR | height 67 by Fejér budget; rungs: window, Li, Hausdorff, heat, Jensen, PF, theta | A1, A2 | none; decides no all-aperture statement |
| NGF | frequency, blow-up, gap laws, maximum principle, crystal and reality at critical scale, order bound | A19, A20 | B26–B29, B83 |
| MZF | Selberg CLT, cameras, hyperbolic density without separation, derivative law, rigidity, last scale, Möbius zero condensation | A18, A22 | B57–B61 |
| FFP | `N_d` law, saddle region, stability dictionary, bulk blindness | A26 | B24, B25 |
| ADO | carrier repulsion; a.e. value; exceptional set dimension `≤1`; FE-pair flatness | none | B74 |
| APR | necessary length, filters, prefix amplification, collar laws | A22 | B48 |
| AKLT, ASRP, AE | Stepanov over `ℤ`, Nair lattice, Siegel and Liouville halves, stencil ceilings, slope `1+ε`; AAL producers, tower detection | A32 | B48, B55, B81 |
| PBAP, W3 | blind positivity, blind ζ dictionary, Carlson threshold, exact null blind test, sharp correlation tail | none | B19 |
| WVL | universal threshold, two-lobe, cut crystal, sampling at a free window | none | none beyond B1 |
| AHD/CACT | aliasing limits, dual floors, head reduction, polar capacity, far reserve, tails, compactness | A9–A13 | B6–B9 |
| CAF, TCS | two-atom, geometric chains, Euler product, explicit current core and tail, rank ten, section heights | A4, A5, A27 | B21–B23 |
| AK, Representation (W2, W4) | column Young projections, curve phase characters, positive endpoint character, canonical compression, Kloosterman receivers and traces, torus critical points | A29, A30 | B84, B85 |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ sign or budget | RW, EWU, OWU, ACT, CHMD, SZ, RN, ACS, AIP, SRT, SC, LI, TT (odd) |
| Σ full-space compactness, then sign | HF, SRT and AIP packet branches |
| Σ continuation at small time | ZCG, PTR, LA, GTA, XN, HCF, PA, TH |
| Π square-root precision and long moments | WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| Γ reflection and selection | PM, BAG, SEC, CDC, PCS |
| Missing source landing | APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF |
