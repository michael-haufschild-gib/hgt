# Route obstacles — status quo

Scope: 38 live route formulations, 9 candidates and their supporting programmes. For each: path, what is established, obstacles that are **(a) just work**, obstacles that are **(b) open mathematics nobody has a solution to**.

Corpus checkpoint: commit `a079423f8d` plus the working tree of 2026-11-07.

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means an independent source mechanism or landing is missing. Formulations are not independent mechanisms: HJ is PA, BSH is CDC, FEL's BSY criterion belongs to CTF. A criterion, a source construction, a quotient equality or a scalar grade does not discharge an arithmetic sign or vanishing.

**Evidence.** `[L]` Lean source. `[S]` Lean source unfinished, unintegrated or uncommitted. `[K]` Lean with transitive axiom audit. `[D]` deduction, not a Lean theorem. `[N]` numerical, uncertified. `[C]` classical literature, not formalized.

**Strength.** RH; ≥qRH (zero-free half-plane or Lindelöf); sub (strictly below quasi-RH); method; indep. (independent of RH).

**Labels.** `A*` just-work items and `B*` open problems are listed in full in [obstacles-summary.md](obstacles-summary.md). An A item is known mathematics, finite computation, effectivization or assembly of proved pieces; `(unverified)` marks A items whose difficulty is not established.

**Notation.** Windows `[−a,a]`. `W` Weil's form, `w_n=Λ(n)n^{−1/2}`, `H` the archimedean–polar form, `P` the arithmetic part, `W=H−P`. `μ(a)` ground energy. `a*(ζ)` onset aperture. `ℋ(c)` Hardy interval, `𝒜(c)` window cone, `λ*(c)` its best margin. `τ_L,τ_R` endpoint traces. `r=τ_R(i)/τ_L(i)`, `L=artanh r`, `Ψ=½log H₁`, `q=Ψ′`. `H_t` the de Bruijn–Newman flow, `Λ_X` its local constant, `τ=t log²X`. `N_d` non-real root count of `R_d(Ξ)`. `w=zetaZeroWidth`, `Θ=½+w`, `Θ∞` asymptotic abscissa. ZAL: finitely many zeros beyond every positive depth (`Θ∞=½`). AAL: finitely many zeros right of `½+h` forces none (`Θ∞=Θ`). `E(s)=(s−1)ζ(s)/s`, `I(w)` inner field. `M_X` truncated Möbius polynomial, `E_X=ζM_X−1`. `N(ρ)` normalized derivative at a right zero. `Φ(u)=Re Σ_ρ e^{u(ρ−½)}/(ρ(1−ρ))` lag function. `vkScale(T)=(log T)^{3/5}(log log T)^{−5/3}`. `R=c⁸/log N`, `W₈(H)=∫H²e^{−8y}`, `R*` the far-margin root. `A(K)` best slope of an integer producer on alphabet `≤K`.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ ZAL ∧ AAL; ZAL ⇒ qRH; ¬AAL ⇒ `Θ<1` | [L] | one half is at least quasi-RH, the other sits below it; `qRH ∨ AAL` is a theorem [D] |
| Under AAL: RH ⇔ ZAL ⇔ finite off-line support ⇔ `κ(K_ζ)<∞` ⇔ bounded nonreal heat count ⇔ finite critical source energy ⇔ eventual Hadamard positivity ⇔ eventual central-gap budget | [L] | every large-height receiver reads RH once one-offs are gone |
| ¬AAL ⇔ `ψ(x)−x=x^{β}T(log x)+O(x^{β−η})`, `T≠0` a finite trigonometric polynomial, `β>½` ⇔ two-prime dilation annihilation of `ψ`; `β=Θ`, `T` unique, coefficients `−ord/(Θ+iμ)`, `η≤Θ−Θ₂` sharp | [L] | failure of AAL is one rigid object, with sign changes at bounded log gap |
| RH ⇔ `a*(ζ)=⊤` ⇔ `1∈ℋ(c)` ∀c ⇔ `λ*(c)→0` ⇔ every window cone nonempty ⇔ two-site PD ⇔ no finite contact | [L] | every window route measures one number; existence of any admissible weight on each window is enough |
| `L′=q−sinh 2L`, `(log K)′=2 cosh 2L`, `H₁H₂=1`; `|L(x)|≤artanh e^{−2(x−c)}+2 osc_{[c,x]}Ψ`, no initial value and no `1/μ`; `Ψ` absolutely continuous on compact precontact intervals, `q_y→q` in `L¹` | [L] | RH ⇔ `Ψ` locally bounded on `[0,∞)` [D]: the Hamiltonian stays finite and positive |
| Lattice PD ⇔ positive-margin outer predictor; reflection data free; passive iff each echo in its Schur band; first reflector reads `Λ(n₀)`; `∂E_n/∂λ(n₀)=−(2/√n₀)A_n(log n₀)`, `E_n` concave in the weights; Born defect `≤K(Π(1+|γ_k|)−1)` | [L] | the forward map from primes to reflectors has an exact tangent at every stage; its size is not controlled |
| Certified aperture `2a₀`: outer predictors, circle zeros, every echo in its band, with `Λ(2)` in the data | [L] | the causal certificate is a theorem on windows past `log 2` |
| Local onset field `Ω_ψ(a,X)`: on-line zeros `≥0`; pair at depth `δ` costs `≤(16/9)δ²a⁴‖ψ‖²`; RH ⇔ `Ω≥0` everywhere; `Q(f)=∫|f̂|²W_N` on `PW_a` | [L]/[D] | sign is a function on the plane `(a,log X)` |
| All-height sign up to `a≈log log X−log 4`; density `1−δ` sign for all shape-bounded tests up to `a=δ log T/(64M²)` | [D]/[L] | two proved curves on that plane; both size only |
| `c_φ(t)↛0` for every nonzero test; profile decomposition holds in `ℓ²(zeros)`; RH ⇔ every orbit correlation is relatively compact ⇔ moving-bubble energies have nonnegative subsequential limits | [L] | Bohr compactness is an RH-level target, not a source bound |
| At fixed critical ratio: Γ-liminf `liminf Q(U_N)≥Q_T(F)+α_R∫_{y<0}F²e^{−8y}`; bounded form and masses make `L¹` limits strong; `|P|≤εW₈+B_ε‖H‖²`; coercivity on the far complement for `R<R*` | [L] | HF at one ratio reduces to a uniform `W₈` Gårding bound and a finite window [D] |
| RH through height 67 with no zero located; PF₂₀₀, slices `|t|≤133/2`, Li `n≤314`, rank ten | [L] | finite rungs are theorems; they decide nothing |
| Every route with a saving carries the same Vinogradov–Korobov saving, stencils included: `A(K)−1≤exp(−(log K)^α)`, `α<3/5` | [L] | one width axis; interior values are zero-free strips |
| Polynomial stencil rate ⇔ fixed zero-free strip; rate `K^{−a}` ⇒ `Re ρ≤1−2a/3`; floor `cK^{−3/4}` | [L] | production has no content independent of the Mertens level at exponent scale |
| Complete ledger of a zero mode vanishes for every balanced stencil; ledgers against `Λ` and `−λΛ` differ `≤2wψ(√n)`; positive Hecke combinations never improve the rate | [L] | linear floor identities are blind to zeros and to parity at square-root scale |
| `T⁻¹∫_T^{2T}log‖ζ(½+it)‖dt→0` ⇔ `100%` critical-scale clustering ⇔ six further forms ⇔ `I(½+x+it)→0` ⇔ depth density `o(T)` | [L] | the near-line layer is one number |
| Moment data bound `I` at width `x` by `log log x` | [L] | a mollifier is required for `O(T)`, and no moment suffices for `o(T)` |
| Near-extremal mollifiers: `|EM_Q−1|²≤(B−1)|s−1|²/(2Re s−1)`; limit forced to `1/E`; every budget `≥|ρ|²/|ρ−1|²`. Over a curve purity gives holomorphic Euler-log convergence and `|P(v)/P(ρv)|²≤4^{rank}` | [L] | actual holomorphic budget control is missing; boundary quotient means tend to 1 even for nonunitary data [K] |
| Zero `L¹` FE defect, and any defect `≤1/6400`, forces the rational primes; pole residue `½` or `2β≥√2`; rational quartet surgery preserves FE and destroys Bohr almost periodicity | [L] | ζ is an isolated point of Beurling systems in FE defect |
| Modular horizon: exact conformally coupled solutions, smooth across the horizon, one damped mode per zero, rate `D+(1−β)/2`, plus branch silent; reflected signal = pulse ∗ echo train; universal damping ⇔ RH | [L] | ringdown is an exact physical reading; it adds no estimate |
| Returns on a disc in the upper quadrant force `n^{−iτ_j}→1` for every `n` and a spike near `1+iτ_j` | [L] | phases never obstruct recurrence; the tail does, at almost every Bohr time |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | Primes pay the archimedean–polar deficit by sign in a frustrated critical form | format exact on every window; causal certificate exact; size payment ends before half-width `21/40` |
| M2 Calibration | Window cones, blind positivity, margin | cone pinned at rate `e^{−c/1104}`; exact null blind test; ceiling doubly exponential; sign open |
| M3 Canonical flow | `L,q` of the Weil chain | exact to contact; `Ψ` oscillation is the sole control; contact-uniform bound open |
| M4 Reflection | Krein/Lewis positivity, Eisenstein carrier, Hecke dispersion, ringdown | coefficient completion closed; depth read exactly; `D_s≥0` open |
| M5 Square-root cancellation | One smoothed prime count, long moments | receivers closed; arithmetic estimates open |
| M6 Continuation | Heat, cosine, Jensen | high-time and typical-height regions closed; small time at all heights open |
| M7 Zero geometry | Cameras, Blaschke factors, inner field, Carleson measure | isolated zeros at rate 2; clusters open; log-mean open |
| M8 Recurrence | Transport of zeros by vertical returns | transport closed; pair returns at typical base; returns at a zero open |
| M9 Production | Integer stencils | exact; rate is the Mertens level; no independent mechanism |
| Amplifiers | Diophantine repulsion, integrality as amplification | amplify a certificate, produce none |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve

Routes: HF, SRT, AIP, ACT, ACS (atomic), SC, CHMD (index). Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF.

Established:
- Full tilted-spline matrix PD for `1≤c≤(log N)^α`, `α<1/8` [L], through one small multiple `c≤2K₀(log N)^{1/8}` [K].
- Every compact C² profile: energy `≥a e^{−Bc}‖x‖²` on conductors `≤N^θ`, `θ<¼`, `c≤b log log N` [L].
- Every fixed ratio `R`: critical pencil `κQ+(7J/R)W₈`, aliasing limit, fixed-family inertia, positive low packet through `⌊(log N)^{13/32}⌋` [K], polar capacity `S_A²/(J₁/R+κg)` [K].
- Weighted floor `Q(H)≥−F(p)∫e^{−pu}H²`, `p>1` [L]. Prime form `|P(H)|≤εW₈(H)+B_ε‖H‖²`, aperture uniform, for `H` supported in `y≤0` [L].
- Atomic synthesis: mixed mass, below-grid recovery, sharp aliasing floor; Γ-liminf with weight `α_R=7(∫φ²)J(1)/((∫φ)²R)` at every `R` [L]. Bounded form, `L²` and `W₈` give uniform Fourier tails and strong `L²` limits; prime sum and pole moments pass to the limit [L]. Physical plus Fourier tails give precompactness [L].
- Far band: explicit `farMargin R=3D/(8R)−C−C′R`; coercive with floor `min(1,farMargin R)` on the complement of conductors `≤N^θ` for `0<R<R*`; joint complement of the low packet coercive for `0<R≤min(1,5R*/6)`, `c≥(log N)^{1/16}` [L]. `C′` is the pole window cost, paid by Young against the reserve; `C` carries the archimedean localization commutator, the Gamma offset, the top prime constant and the prefix leak [L].
- Plateau Schur floor `(a/2)e^{−Bc}‖z‖²` on conductor blocks `Q≤(log N)^{1/32}`, `c≤b log log N`, `log M≤√log N`; a full-space floor passes to the Schur complement of every tail [L].
- Periodic charges: `J_N=O(log N)` iff gcd profile; four literal channels; on orthogonal pairs the mixed error vanishes on the window `2α<β`, `β+2α<½`, nonempty exactly for `α<1/8` [L].
- Receiving modes with bounded charge and vanishing physical energy, capacity `log log N+O(1)` [L/K].
- Dirichlet-shift companions reduce long windows to heads; `d=2` unconditional; all `d` ⇔ RH [L].
- Far bubbles do not decouple; `Q(φ−φ(·+t))=2Q(φ)−2c_φ(t)` [L].

Structure [D]:
- `Q(U)≈Energy/c` in physical normalization, so the far balance reads `(3D/8R−C−C′R)M₇`. Below `R*` size gives coercivity. Above `R*` the natural statement is a Gårding bound `Q(U)+B_R‖U‖²≥a_RW₈(U)`, not coercivity.
- A Gårding bound bounds `W₈` along negative sequences. Then a negative sequence has a strong limit `F≠0` with `Q_T(F)+α_R∫_{y<0}F²e^{−8y}≤0`. The limit pencil is a finite rung: far windows are paid by `e^{−8y}`. So HF at one ratio is a window of half-width of order `log R`.
- `C′R` is a Young trade on a rank-one prefix–collar pole cross term, and the prime term is infinitesimal in `W₈`. The localization commutator in `C` is the one piece with no proved replacement.

| | Obstacle | Strength |
|---|---|---|
| A9 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | — |
| A10, A11 | Uniform `W₈` Gårding above `R*` (unverified); fixed-ratio compactness assembly | — |
| A12, A13 | Low-packet/complement Schur payment on the certified interval; growing-period charges (unverified) | — |
| B6 | Full-space sign eventually at every `K`: `a*=⊤` through A10–A11 | RH |
| B7 | Growing families, coalescing frequencies, conductors beyond `(log N)^{13/32}`, where not reached by A10 | sub |
| B8 | Head thresholds for every `d` | RH |

### S2. Window tower and canonical flow

Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT (odd), HF, ACS, SRT, SZ, MSC. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF.

Established:
- Precontact de Branges chain, canonical system, `H₁H₂=1`, flux, sampling bases, positive on-line mimic at every precontact aperture, Gram AC with no atom [L].
- `L′=q−sinh 2L`; `Ψ=L+θ`; contact criterion; contact scaling `|q|≈(1+1/γ)m` at order `γ`; contact forces kernel blow-up [L].
- Traces, `r`, `Ψ` absolutely continuous on compact precontact intervals; `q=Ψ′` a function; `q_y→q` in `L¹` by a Kato contraction; `Ψ′=(r′+2r)+(r′+2r)r²/(1−r²)` a.e.; Riesz increments Lipschitz in `L¹` [L]. Constants retain the ground energy at the top of the interval [L].
- Restoring bound `|L(x)|≤artanh e^{−2(x−c)}+2ω`, `ω=osc_{[c,x]}Ψ`, for the actual chain [L].
- Soft prime kick, `(Ψ(x)−Ψ(a))log(1/(x−a))→w(a)` from the right [L].
- Born model: kicks `|k_n|≤A log n/√n`, `1−r_n²≥e^{−10A}/(2√n log n)` [L]. Lattice kick `q_n=−artanh γ_n`, tangent carries `1/(1−γ_n²)`, Born defect by accumulated reflection [L].
- Lattice flow `artanh r_{n+1}=artanh(s r_n)−artanh γ_n` [L]. Curve flow with boundary at the number of angles [L].
- Causal certificate, Szegő threshold, free reflection coordinates, Schur band, prime dictionary, injective forward map, exact tangent, concave margins [L]. Certified windows carry the full causal chain with `Λ(2)` [L]. At a ratio below a window's threshold, the non-Toeplitz pencil has a triangular causal certificate [L].
- Cone: pinning, ceiling, bands, datum classification; every real weight has an attained ground state, bounded, with exact edge law; explicit sup bound `‖u‖∞≤2(C₀+2L/a+KL/ρ)` [L].
- Exact null blind test `Φ=Ξg`, sharp tail exponent one [L].
- Floors `(1/20000)/2^k` through `a_k<0.3621` [L].

Structure [D]: Contact gives `limsup|r|=1`. The restoring bound then forces `osc Ψ=∞`, and no contact gives `Ψ` AC on compacts. So RH ⇔ `Ψ` locally bounded. The margin ceiling forces `m≳e^{2a}` on average, above the Born bound `m≲ae^{a}`, so the potential is a nonlinear collective response.

| | Obstacle | Strength |
|---|---|---|
| A1–A3, A6–A8 | Certified verification, numeric heights, first-window membership, cone widths, anti-diagonals, Tate dimension one | — |
| A15, A16 | Lean statement RH ⇔ `Ψ` locally bounded; numerical `r,m,q` | — |
| B1 | Sign on every window | RH |
| B2 | Bounded oscillation of `Ψ` on every bounded aperture interval | RH |
| B3 | Variation of `r` on bounded intervals free of `1/μ` | sub |
| B4 | Two-sector certificates; outer predictor at every window; every actual echo in its Schur band | RH |
| B5 | Kick admission at every stage | RH |
| B16 | Decay law of `λ*(c)` | sub |
| B17 | Signed ground-state structure past `log ρ` | method |

### S3. Local onset plane

Routes: RW, ACS, SRT, ZCG, WD. Programmes: AIF, WVL, MZF.

Established:
- `Ω_ψ(a,X)` as a sum over zeros at scale `1/a`; on-line terms nonnegative; depth cost; RH ⇔ `Ω≥0`; bounded apertures positive at every height [L].
- `Q_γ(F₀)=Q(F₀cos γ·)+Q(F₀sin γ·)`: prime part `(1/π)∫Φ D_N(γ+t)dt`, arch part `≥(½log(2+|γ|)−C)∫F₀²`, no shape condition, no zero information [L].
- `A=δ log T/(64M²)`: outside a test-independent set of measure `δT`, `Q_γ(F₀)>0` for every `F₀∈C²_c[−A,A]` of shape `≤M` [L].
- Visibility: `k·pairEnergy(δ,a)≤(K/2)ℓe^{2(2π/ℓ+σ)a}`; cut crystal hides fixed depth to aperture `(log T)/36`; positivity at `λ·½log T`, `λ>1`, gives depth `<e^{−c log³T}` [L].

Structure [D]:
- On `PW_a`, `Q` is diagonal in frequency, `Q(f)=∫|f̂|²W_N`, so `‖χ‖²Q(f)=∫Q(f∗χ̌_X)dX`: global sign at `a` follows from local sign at `a+b`, all heights.
- `2e^{a}≈½log X` gives all-height sign to `a≈log log X−log 4`. Gaussian moments of `D_N` hold to `k≈log T/(2A)`, so bad-height measure is `≤T exp(−(log T/2A)log(log T/2A))`, which at `A=K log log T` is `T^{1−1/(2K)}`. Moments reach all heights only for `K<½`, below the size bound.
- Base versus `D_N`: zero at depth `d`, height `γ`, forces a large value of a prime polynomial of length `(log γ)^{1/d}`. No nontrivial sup bound exists between length `log t` and `exp((log t)^{2/3})`. All-height sign, the zero-free region and the width axis are this one barrier.

| | Obstacle | Strength |
|---|---|---|
| A14 | Frequency-integral identity in Lean; moment upgrade of the exceptional proportion | — |
| B28 | Local Weil positivity at fixed `λ>0` on density-one heights | sub |
| B46 | All-height one-sided bound for prime polynomials of length `(log X)^{2K}`, `K>1` | sub |

### S4. Continuation and nodal geometry

Routes: ZCG, LA, PTR, HCF, PA, GTA, XN. Programmes: NGF, FFP, ADO, RHTower heat.

Established [L]:
- Collision criterion; horizon `(6600/9991+ε)/log X` from the profile margin; `c d²/log X≤Λ_X`; a heat coefficient below a fixed `κ₀` at all large `X` gives a zero-free half-plane.
- Fock identity, monotone frequency, order law, Hermite blow-up, gap law, maximum principle, uniform mesh, cluster spread, crystal symbol, depth moments, finite-speed lateral energy.
- Multiplicity `≤(3300/9991+ε)log X`.
- Density-one: `Λ_Xlog X→0`. Exceptional set explicit: `θ(κ)=1−κ³/41943040000`, `0<κ≤8`; cubic because of the level. Critical scale: all zeros real, central gaps, crystal law outside `δT` heights.
- Complex saddle; line model at power level; quotient by an isolated zero; sharp depth law for isolated simple zeros.
- `N_d` nondecreasing, supremum is off-line multiplicity, `N_d≤300√(d log d)`, inner roots real, Cauchy bulk blind.
- Cosine strict Laguerre ⇔ RH; holds for `h≥½` and above VK.
- Nonrepelling ζ-values have Hausdorff dimension zero, contain a dense residual set; `0∉E` undecided.

| | Obstacle | Strength |
|---|---|---|
| A19, A20 | Horizon toward its method floor; Jensen rung and constants | — |
| B24 | Exclude collisions at arbitrarily small time, all heights | RH |
| B25 | Frequency `<1` at every putative collision | RH |
| B26 | An arithmetic input distinguishing `Φ` among `Φe^{−τx²}` | method |
| B27 | Runs of `k` simple critical zeros, every `k` | sub |
| B64 | Signed pair information beyond bandwidth one | sub |
| B47 | Multiplicity `o(log X)` by an all-height input not reducible to size | sub |
| B22 | Outer-root control of `R_d(Ξ)` | RH |
| B23 | `N_d` bounded | ≥qRH |

### S5. Near-line geometry and long moments

Routes: WD, CTF, MC, TG; census. Programmes: CDG, APR, MZF, AIF.

Established:
- Selberg CLT; off-line `log|ζ|` is the prime field up to bounded error; barrier law; Lorentz mass exponential tail [L].
- Prime camera rate 2; Turán camera for bounded clusters; hyperbolic density theorem without separation; `N(ρ)≤Π_Dϱ`; `N(ρ)=exp(−Σ_{a≠ρ}m_aG(ρ,a))` [L]. Crowds exponentially rare [L].
- Box budget, arithmetic embedding, Carleson measure `μ(box)≤(5/2)xI`, embedding at scale `x` with constant `I/(2πx)` [L].
- 8-way log-mean equivalence; Abel log-mean ⇔ `I(½+x+it)→0` ⇔ depth density `o(T)`, independent of `t`; `I` bounded ⇔ `O(T)`; `I≤log(1+log 5x)+C` and depth mass `≤(5/2)T(log(1+log 5T)+C)` from the empty mollifier [L].
- Jensen extremizer: moments do not determine the log-mean [L]. Necessary-length laws, last-scale floor, short weights blind, occupied windows lose one log, corridor exceptions [L].
- Long-moment slope `2wθ`, quantifier collapse, one-window and positive-proportion RH forms, exponent rigidity, Möbius zeros condense on `Re s=Θ`, collar factorization [L].
- Twisted second moment to length `U^{21/50}` [L].

Structure [D]: Isolated means Carleson uniformly separated in `H²(Re s>½)`. Jensen with a second moment loses the variance of `log|ζM|`, a positive constant at polynomial length. The log-mean is the Bode sensitivity integral of the causal symbol, and Littlewood's lemma is that identity.

| | Obstacle | Strength |
|---|---|---|
| A17, A18, A21 | Selberg `O(T)` depth density in the inner-field form; moments past `21/50`; census items | — |
| B57 | `T⁻¹∫log‖ζ‖→0`, equivalently depth density `o(T)` | sub |
| B58 | `D_win` | sub |
| B59 | Cluster wall: Density Hypothesis rate for all near-line zeros | sub |
| B60 | Exponential moments of the Green potential at deep zeros | sub |
| B61 | A detector past the last scale | sub |
| B62 | Cofinal long moment bound | RH |
| B66 | Near-unit holomorphic mollifier budgets; quotient limits alone are insufficient | RH |
| B82 | Inner-field decay `I(½+h+it)→0` | ≥qRH |

### S6. Production and precision

Routes: WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, LI, AIP. Programmes: ASRP, APR, AGT, AKLT, AE, AAD.

Established [L unless marked]:
- Band ⇔ every classical one-sided criterion; `E(n)≤(2+γ−log 4π)√n` ⇔ RH; `Ω±(√n)`; entry filters; necessary length; length–precision law; gauge torus exponents `[Θ,1]`; Nair lattice exact; Siegel and Liouville halves RH at square-root scale; integrality exponent `Θ`; univariate ceiling `e^{−0.87n}`; slope ceilings.
- Producer: balanced stencil, `g≥0`, `g≥m` on a window. `c=μ∗h`; constant window ⇒ `c=mμ` there. `D_cζ=Σg(r)(r^{−s}−(r+1)^{−s})`: a producer is a mollifier on `Re s=1`. `ψ(x)≤(1+ε)x+2K(5+log K)(1+log K+(K+1)ε)(1+log x)(1+log x/log 2)`.
- Uncertainty `m|1−B^{−ρ}|≤|ρ|(4+1/β)w^{1−β}T^β`; mean-value law `w²≤144TE`; floor `A(K)−1≥cK^{−3/4}`; rate `K^{−a}` ⇒ `Re ρ≤1−2a/3`.
- Explicit polynomial-alphabet Möbius producer from a Mertens level; `hasRate_vk`: rate `exp(−(log K)^α)`, `α<3/5`; polynomial rate ⇔ zero-free strip.
- Ledger of a zero mode vanishes, truncation `≤w/β`. Sieve and producer cones disjoint; parity ledger `2c(1)#{K<p≤x}≤g(x)−Σc(k)λ(k)L(⌊x/k⌋)`.
- Carlitz stencil over `𝔽_q[T]`: `T^{q^n}−T=D_n/D_{n−1}^q`, rate 0, exact ledger from size and multiplicity alone.
- Dual: fake prime measures `Σu(r)(r mod k)=log k` bound the slope; the rate is not a capacity; positive Hecke combinations multiply the normalized slope by `1+a/j`; `Λ` and `−λΛ` ledgers differ `≤2wψ(√n)` [L].

Structure [D]: Under RH the Möbius producer reaches only a small exponent `a` (`σ/16` in Lean, `≈1/7` optimized), while the sharp reading needs `a↑3/4` for RH. So the scale `a∈(0,3/4]` is not known to be reached under RH: a stencil route to RH needs a better object than Möbius, which constant-window rigidity forbids on the window.

| | Obstacle | Strength |
|---|---|---|
| A21, A29, A30 | Chowla, exponent optimization, discrete Beurling one-off | — |
| B48 | A deciding input at square-root precision | RH |
| B55 | Any polynomial stencil rate (is qRH); rates `a↑3/4` | ≥qRH to ≥RH |
| B15 | Mertens level past VK, equivalently stencil rate `α>3/5` | sub |
| B14 | Window negativity exponent `<½`; any interior width value | ≥qRH |
| B56 | `Θ<1⇒Θ=½` | sub |
| B67 | Parity input in a ledger: bound on `Σc(k)λ(k)L(⌊x/k⌋)` | method |

### S7. Reflection and carriers

Routes: PM; W1C (candidate); RN and PTR in part. Programmes: RIT, ART, AOT, ACP, BHR.

Established:
- Resonance ⇔ `ζ(2s)=0`; `Q=2Re[WH,WH]`; `D_s≤0`, zero iff `Re s=¼`; lifted Hecke and Lewis carriers; closed Cauchy reflection [L/K].
- Line law for `c_Y`, `Y>1`; boundary norm; `|ζ(1+it)|≥1/(6250t³log²t)`, `t≥2·10⁷`; Schur positivity blind to zero position [L].
- Height law `ν_Y`; uniform Hecke residual; mixed-prime one-step isometry; cutoff Gram kernel [L].
- `V_p(ρ,Y)=2(1−p^{Re ρ−1})`, one-sided bound at one `p,Y` ⇔ RH; Poisson mixture positive for every `Re u<0`; prime-word moments identified with the Poisson spectral measure [L].
- `S(s)=φ(s)(s−1)/s` is a Blaschke product over `(1+ρ)/2`, with Green potential and resonant Szegő Gram [L].
- Horizon: echo train `K(τ)=Σ_{2log c<τ}(ϕ(c)/c)(1−e^{−(τ−2log c)})^{−1/2}`, transform `Λ(2w)/Λ(2w+1)`; causal symbol; exact lift; `R=−12`, coupling `+2`; `SL₂(ℤ)` invariance; smoothness across the horizon; ringdown uniform on `τ≥0` at a fixed point, remainder `O(e^{−Aτ})` all `A`; multiplicity `m` gives degree `≤m−1`; every zero excited; raw echo has no pointwise exponential bound, independent of RH; Gaussian probes keep every pole [L]. Whittaker tail and jets `O((1+|Im u|)^Me^{−π|Im u|/2})`; `E(iξ;x,Y)` polynomially bounded; jets polynomially bounded on the lines and edges contour arguments use [L]. Any modular wave lifts, with no spectral assumption [S].
- No `ℓ²`-perturbed arithmetic progression of zeros; `Σ|ζ(½+i(a+dn))|/|½+i(a+dn)|=∞` [L].

Structure [D]:
- The massless topological black hole is locally AdS₄, in a Rindler wedge with horizon quotient by `Γ`. Echo delays `2log c` are cusp-to-cusp lengths of `Γ`, and the echo train is the cusp channel of a method-of-images sum.
- The radial problem is exact Pöschl–Teller; zeros enter only through Eisenstein poles on the horizon. So ringdown is the Lax–Phillips problem of `Γ\ℍ` lifted to a black hole.
- KMS, Osterwalder–Schrader and Tomita positivity are positivity of the real spectral density `1/|ξ(1+2iν)|²`: blind in the sense already proved for `C*`-Hecke moments.

| | Obstacle | Strength |
|---|---|---|
| A24–A26 | All-`n` physical moments; packets with rapidly decreasing amplitude, spin two; Lean dictionary for images, Lax–Phillips, Zagier | — |
| A31 | Graph model of the horizon over a curve | — |
| B68 | Independent `D_s≥0` or full Krein positivity | RH |
| B69 | Positive physical carrier | producer |
| B70 | Zero-free curve inside the strip from the carrier: lower bound for `V_p` | sub |
| B71 | Sharp decay of the smoothed resonant sum (any uniform gap ≥qRH) | RH |

### S8. Index and support

Routes: HKT, AKLT, SC, RIT, CWS through HF, ACS; LA. Established [L]: `κ(φ_c)=κ+1`; finite index ⇒ Lindelöf; `κ∈{0,∞}` under escape, mixing or height decay; window index counts critical lengths; `sup_dN_d` off-line multiplicity; `K_ζ^n` PD ⇔ RH; finite off-line support makes all but `(κ choose 2)` prime towers decide.

| | Obstacle | Strength |
|---|---|---|
| B12 | Index ceiling uniform in resolution | ≥qRH |
| B13 | Exclude finite nonzero off-line support | sub |
| B23 | `N_d` bounded | ≥qRH |

### S9. Abscissa split, recurrence, one-offs

Routes: BAG, JAS shell branch, SC undamped branch, WL sparse samples. Programmes: AKLT, ZCG, AIF, APD, AAD.

Established:
- Split RH ⇔ ZAL ∧ AAL ⇔ ZAL ∧ zero-disc weak recurrence ⇔ inner-field decay ∧ recurrence [L].
- Producers of AAL: bounded lags on one progression or a log-dense set; nonnegative twisted plateau energies; JAS at level one; off-line chain; infinitely many bounded prime towers; one bounded two-prime cone; shell positivity infinitely often. All retain their source bound [L].
- ¬AAL: bilateral spectral gap, finite top and bottom layers [L]; finite oscillation of `ψ(x)−x`, uniqueness, quantization, remainder ceiling `η≤Θ−Θ₂` with sharp converse, remainder floor `½`, bounded-log-gap sign changes, alternating-`Λ` transfer [L]; two-prime dilation annihilation, single-base periodic pinning [L]; `Φ(mℓ)` unbounded on every progression; `K_ζ` bounded on finitely many towers; `|E_X|≥X^κ` off a vanishing set; annihilators nonvanishing on `Re s≤½`; twisted FE after Blaschke division [L].
- Rightmost-zero jets: `Λ`-moments/`k!` at `ρ+1→−m`; coefficient-square diagonal `→0`; off-diagonal `→m²`; shifts `≤r^k`, `r<R²`, contribute `o(1)`; horizontal gain `<gap<½` [L].
- Returns: transport of zeros; returns at a zero `≤T^θ`; threshold `≍|g|r^m`; pair recurrence at typical base with relatively dense shifts; returns on a disc force `n^{−iτ_j}→1` and a spike near `1+iτ_j`; limits of translates embed in the gauge torus, a return being the fibre over the identity; dual `le_of_phase_return` from a producer [L].
- Countermodels: continuous Beurling systems with exactly one off-line pair, `N(x)−ρx−C→0`, no recurrence [L]. Rational quartet surgery: FE exact, not Bohr almost periodic, no Dirichlet series [L]. Golden `L`-function: periodic returns, zero right of the line, fails the count [L].
- Rigidity: integrable defect at unit density forces integers; residue gap `½` or `2β≥√2`; defect `≤1/6400` forces the rational primes; mismatch at `N` costs `>1/(400N²)` [L].

Structure [D]: Exact integrality `N(x)=⌊x⌋` and exact FE specify one function. So AAL has no deformation class: any argument stable below defect `1/6400` concerns ζ alone, and fakes begin at finite defect. Discrete Beurling primes can approximate a continuous prime measure with error `O(√x)` and keep its zeros right of `½` [C], so discreteness of primes alone does not give AAL; integrality of norms or FE must enter.

| | Obstacle | Strength |
|---|---|---|
| A22 | Hurwitz limit map onto the gauge torus and its fibres | — |
| A30 | Discrete Beurling one-off and its FE defect | — |
| B83 | AAL | sub |
| B13 | Finite nonzero off-line support, the smallest instance | sub |
| B84 | Smallest FE defect carrying a one-off | method |
| B72 | Cutoff-uniform target mass | RH |
| B82 | Inner-field decay | ≥qRH |

## 3. Live routes

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy or one-sided `Φ` → RH.
- **Established [L/K]:** bounded endpoint energy ⇔ RH; `E(n)≤(2+γ−log 4π)√n` ⇔ RH; `Ω±(√n)`; first-band abscissa `2Θ`; gauge exponents `[Θ,1]`; subtracted lag `Φ_S≤Me^{au}` ⇔ ZAL; density-zero excursions force top weight `≤0`. Producer bounds through AAD.
- **(a)** None that moves the route.
- **(b)** `E(n)` upper bound at the ceiling; first-band square-root bound (B49); half-power at the trivial gauge (B50); deciding input (B48); Mertens level past VK (B15).

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every radius → RH.
- **Established:** block S2; local sign S3; every window cone nonempty ⇔ RH; RH ⇔ relative compactness of orbit correlations.
- **(a)** A1–A3, A15, A16.
- **(b)** All-aperture sign (B1); bounded oscillation of `Ψ` (B2); variation of `r` free of `1/μ` (B3); outer predictors at every window (B4); margin law (B16); blind positivity on nonnegative mixtures (B18).

### FU — Signed prime scheduling
- **Path:** signed Möbius history → one-sided sampled Abel bound → RH.
- **Established [L]:** one-sided criterion at fixed `m`; one controlled sample per backward window `N^{1−δ}`; exhaustive bounded-block payment at fixed horizons.
- **(a)** None that moves the route.
- **(b)** Complete-history cross-clock bound retaining seed, drift, covariance, endpoints (B42).

### CFC — First-clock lower bound
- **Path:** first-clock sine coefficient bounded below on a tail → RH.
- **Established [L]:** exact tail criterion; phase-natural transport is identity.
- **(a)** None.
- **(b)** Lower bound retaining prime, archimedean and endpoint terms (B42).

### RP — History floor
- **Path:** matched-quantile history → eventual linear floor → RH.
- **Established [L]:** exact linear-floor criterion; low-LCM payment; sublinear floor impossible.
- **(a)** None.
- **(b)** High-LCM pairs, moving core, singular-domain terms in one floor (B42).

### PA — Prime–archimedean passivity (HJ alias)
- **Path:** prime−Gamma source sign → RH.
- **Established [L]:** calibrated Hausdorff rows nonnegative for `r≥C₀(k+1)²`; remaining entries ⇔ RH; exterior diagonal criterion at `218/25`; verified-height rows.
- **(a)** Verified rows (A1).
- **(b)** Signs below the quadratic boundary, or `K(z,z)≥0` on the exterior sector, or `TV(n)/qⁿ→0` for every `q>1` (B31).

### MC — Möbius cancellation
- **Path:** half-power Möbius or Liouville cancellation → RH.
- **Established [L/K]:** bounded damped `E_ε` ⇔ RH; fixed `t₀`: `M_N(½+it₀)≪N^ε` ⇔ RH; undamped Hilbert energy `≤CTe^{−c·vkScale(T)}`; Möbius zeros condense on `Re s=Θ`; Haar-a.e. exponent `½`, Baire-generic `1`; flip exponent `max(θ,Θ)`; VK-scale integer producers.
- **(a)** Logarithmic two-point Chowla (A21).
- **(b)** Trivial-gauge cancellation or independent zero exclusion for `M_X`; signed long-modulus tail (B50); deciding input (B48); past VK (B15).

### TT — Theta tail / Wold
- **Path:** weighted endpoint energy bounded for each `0<t<½` → RH.
- **Established [L]:** Wold residual `O(e^{−c·vkScale(N)})`; `D_t+Q_t/2≥0`; boundedness ⇔ RH; uniform bound on a shrinking band.
- **(a)** None that moves the route.
- **(b)** `C_t` for every fixed `0<t<½`; endpoint `t=½` fails (B34). Odd branch: B4.

### LA — Jensen line anchor
- **Path:** Jensen polynomials real-rooted or sublinear root height → RH.
- **Established [L]:** block S4. RH ⇔ infinitely many unshifted degrees real; RH ⇔ sublinear upper-root height for mollified, shifted families; inner roots real; `N_d≤300√(d log d)`.
- **(a)** A20; A1.
- **(b)** Outer-root control (B22); bounded `N_d` gives finite support only (B23, B13).

### ZCG — Zero-configuration geometry / heat descent
- **Path:** half-Gaussian source → no positive-time collision → RH.
- **Established [L]:** blocks S4, S5, S9; cameras, sharp location with closed-form height; explicit exceptional exponent; one-off structure and rightmost-zero jets.
- **(a)** A19.
- **(b)** Collisions at small time, all heights (B24); frequency `<1` (B25); time-0 selector (B26); non-size frequency input (B47); runs (B27); FE-pair reality with coverage (B76); crowded and multiple zeros in the depth law (B59); long-shift `Λ` correlation in the one-off world (B83).

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH.
- **Established [L]:** defect constructed, trace class; multiplicity `≤` trace norm; Gaussian passage alternative; explicit central-gap inequality `P(y)−C(y)≤−1/10+32√y`, `0<y≤1`, ⇔ RH.
- **(a)** None that moves the route.
- **(b)** Trace norm `<1` on every rectangle, or bounded centered Gaussian oscillation (B38).

### HF — Hodge / Hecke / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** block S1; cofinal source-work `≤2` ⇔ RH; sharp Schur bound `½log N`.
- **(a)** A9–A13.
- **(b)** Full-space sign at every `K` (B6), which is RW through A10–A11 [D]; growing twists and conductors (B7); head windows (B8); source-work ceiling (B41); top coprime stratum (B10); zero modes (B9); exact SOS on a two-prime lattice (B11); Rosati and band poles (B78, B79).

### CHMD — Causal hyperbolic–modular duality
- **Path:** one-sided bounded prime wave or odd Doob half-threshold bound → RH.
- **Established [L]:** wave and Doob receivers; normalized prime−pole decay `O(e^{−√log Y/92160000})`; nonfirst source retains fraction `1−ε` of Gamma energy.
- **(a)** None that moves the route.
- **(b)** Either side of the unnormalized wave bound, or complete odd sign paying first-prime, potential and polar terms (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel → RH.
- **Established [L]:** full-source rank ten at `0<a≤½`; rank `N` from height `41+6(N+2)log(N+2)`; all ranks in a VK collar; two-atom and `q^n`-chain all-rank sign; `S=Π_pT_pA`; `A` not a positive Laplace mixture; `current=2|Ξ|²Re ξ′/ξ`; insertion cone = exponentially convex for left growth `κ<½`; locking = torus positivity for fixed amplitudes; columns add; products of columns rigid; Sato–Tate pairing; base pays by size when `Σlog p/(p^{½+a}−1)<½log(b/2π)`, primes `≤P` at `log(b/2π)>14√P log P`; alignment has a height in `[B,BQ^{|S|}]`; `{2,3}` cone strictly larger (`e^{−x²}` at `x≥3/2`); limiting amplitudes inherit torus obstructions, oscillating ones can escape.
- **Structure [D]:** `A` grows at the critical rate `e^{|x|/2}`. A proof through `S` must exhibit oscillation of `A` with the height to the end.
- **Numerics:** positive at actual phases, `b≤775`; torus-uniform positivity fails once primes `≲19–47` are free [N].
- **(a)** Rank 11 (A4); tail-failure certificate (A5); certified scans and `S*` brackets (A23); verified ranks (A1).
- **(b)** Exact torus law for `S*(a,b)` and cross-chain positivity on small `S` (B19); height-dependent amplitude oscillation (B20); all ranks at every `a` (B21).

### RN — Theta renewal
- **Path:** two-ended renewal → no joint nodes → RH.
- **Established [L]:** `det₂` gives `D`, not Ξ; `Ξ=0` ⇔ joint node; energy comparison ⇔ RH; `D` has nonreal zeros.
- **(a)** None.
- **(b)** Joint-node exclusion or the energy comparison (B36).

### WD — Ward / collision / long moments
- **Path:** source current, window energy or long moments → RH.
- **Established [L]:** block S5; attained extrema and collision receivers; one-window form; slope rigidity.
- **(a)** A17, A18.
- **(b)** Cofinal long moment (B62); log-mean (B57); `D_win` (B58); cluster wall (B59); Green-potential moments (B60); detector past the last scale (B61); collision charge (B63).

### LI — Paired Li / Cayley ladders
- **Path:** primitive lower bound or Li sign → RH.
- **Established [L]:** guarded zero set finite, RH iff empty; ladder = Li coefficients; Li form `=−2` window form on primitive vectors over `𝔽_q`; subexponential response criterion; Li `n≤314`.
- **(a)** Verified entries (A1).
- **(b)** Budget at every guarded zero, primitive lower bound or response floor (B43).

### SZ — Suzuki screw
- **Path:** completed Abel residual bounded → RH.
- **Established [L]:** first variation = Weil energy; `|A_N|≤C√N e^{−c·vkScale(N)}`; bounded ⇔ RH.
- **(a)** None that moves the route.
- **(b)** `sup|A_N|<∞`, complete first-variation sign, or rectangular Ward lower bound (B37, B1).

### PM — Gauss–Mayer physical model
- **Path:** scattering source → Krein/Lewis positivity or one-prime dispersion bound → RH.
- **Established:** block S7.
- **(a)** A24–A26, A31.
- **(b)** Independent `D_s≥0`, renormalized Krein positivity or the all-zero dispersion bound (B68); positive physical carrier (B69); interior zero-free curve (B70); sharp decay of the resonant sum (B71).

### PTR — Cosine source / photonic
- **Path:** `A_h` collision-free descent → RH.
- **Established [L]:** sech handoff; strict Laguerre for `h≥½` and above VK; sign at every `0<h<½` ⇔ RH; lossless stack on one real window ⇔ RH.
- **(a)** None.
- **(b)** Strict sign below the VK boundary (B29); independent lossless prime-faithful stack (B69).

### JAS — Joint ancestry
- **Path:** subpower control on moving finite power windows → RH.
- **Established [L]:** `RH⇔∀ε, frequently, |Riesz(m²,k)|≤m^{εk}` on `m<k≤m+m/log(m+1)`; finite admission; shell positivity infinitely often ⇒ AAL.
- **(a)** None.
- **(b)** Uniform arithmetic control on that window (B51); shell signs plus ZAL.

### CTF — Chronological tail / Báez–Duarte
- **Path:** approximation, defect, BSY sign or mollifier infimum → RH.
- **Established [L]:** real unit-bounded rows ⇔ RH; sharp defect `D_y≥c_ρy^{2Re ρ−1}`, sparse subpolynomial ⇒ RH; BSY `I≤0⇔RH`; positive-proportion form ⇔ RH; exact infimum `exp(2I(1))`; rigidity of near-extremal families.
- **(a)** None that moves the route.
- **(b)** Vanishing-error rows, sparse defect, BSY sign, uniform positive proportion (B52); near-unit budgets (B66).

### HCF — Heat trace
- **Path:** both prime-log grids positive at every degree → RH.
- **Established [L]:** two-grid criterion at fixed offsets; explicit detector degree; bounded prime chirp ⇔ RH; chirp mean `→0` ⇔ RH.
- **(a)** Verified degrees (A1).
- **(b)** Nonnegativity at every degree, or chirp bound or mean (B30).

### XN — Newton discs
- **Path:** line-centered self-map discs covering every zero → RH.
- **Established [L]:** coverage and closed-margin criteria; `ΔM≥0`; local damping preserves first jets.
- **(a)** None.
- **(b)** Cover every zero with `M≥0` throughout (B32).

### BAG — Self-return
- **Path:** strong self-return or head-target mass, or decay plus zero-disc recurrence → RH.
- **Established:** block S9; transfer closed; cutoff-uniform mass ⇔ RH [L].
- **(a)** None that moves the route.
- **(b)** Uniform positive mass (B72); returns on off-line-zero discs (B83); decay (B82).

### EWU — Even sector
- **Path:** even blind minimum `≥0` → RH.
- **Established [L]:** Hamburger form; neutral gauge; Markov to `log ρ`; blind minimum `≥1/20` for `a≤(log 2+1/50)/2`.
- **(a)** Verified windows (A1–A3).
- **(b)** Blind minimum `≥0` at every aperture; variance payment by signed jumps (B4, B17, B44).

### GTA — Schur charge
- **Path:** cofinally small quartic charge or compact full mode → RH.
- **Established [L]:** charge family; compactness ⇔ RH; late charge `≤HS/400`; small-spectrum suppression; skew energy has a positive limit.
- **(a)** None that moves the route.
- **(b)** Charge `<ε` at arbitrarily late stages; large spectral nodes uncontrolled (B33).

### OWU — Odd sector
- **Path:** odd polar-hyperplane positivity → RH.
- **Established [L/K]:** shifted Hamburger; unit window reads `w₂`; frustration; prime 3 cannot be deleted past `3/5` or replaced past `287/500`; variance retention necessary above `273/400`.
- **(a)** A1–A3, A6.
- **(b)** Sign at every aperture on compact C² odd `F` with `∫F sinh(x/2)=0`; retained-variance payment (B4, B17, B44).

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
- **Established [L/K]:** full-family receivers; depth `<10⁶exp(−a/(1200log(|γ|+3)))` under sign, `|γ|≥110`; universal threshold; two-lobe bound; cut crystal; split-column receiver; local pair cost `≥−(16/9)δ²a⁴‖ψ‖²`; closed-form sharp-location height.
- **(a)** A9, A14.
- **(b)** Complementary-window sign, remaining-depth control (B6, B7, B12).

### ACT — Single shift
- **Path:** one shift pays every even compact profile → odd positivity → RH.
- **Established [L/K]:** single-shift receiver; `{2,3,4}` band with kicks `<0.991` of Lévy energy; floors through `a_k`.
- **(a)** Anti-diagonals (A7).
- **(b)** One shift uniform in profile paying `D_a` (B44, B4).

### AIP — Incidence
- **Path:** complete reflected-prime/pole allocation → subexponential cost → RH.
- **Established [L/K]:** allocation; `|cost|≤Ke^{r−c(2r)^{3/5}(log 2r)^{−5/3}}·Sobolev`; capacity; channel law on gcd twists below the eighth root.
- **(a)** A9–A13.
- **(b)** `C_σe^{2σr}` cost bound for every `σ>0` (B45); packet-branch complement (B6, B7).

### SC — Stokes / Witt–Krein
- **Path:** glued index `≤1`, bounded damped two-prime coupling, or undamped coupling plus ZAL → RH.
- **Established [L]:** `κ(φ_c)=κ+1`; damped bound ⇔ RH; heat-average source; undamped cone bound ⇒ AAL.
- **(a)** None that moves the route.
- **(b)** Arithmetic coupling bound; sublinear tensor loss (B39); B9, B11, B13.

### ACS — Castelnuovo–Severi
- **Path:** source energy → all-aperture Bézout → RH.
- **Established [L/K]:** source cone; RR at every aperture; Bézout ⇔ RH; primitive `h¹` coercive for `a≤181/500`; tensor-uniform growth ⇔ purity on curves; Kloosterman curves pure by Stepanov; compactified moments with signed Tate correction; reciprocal tangent quadrics counted over every finite extension; every column Young projection nonnegative; endpoint Toeplitz minors of order `≤200` nonnegative; character positivity ⇔ RH; typical-height local sign at `A=δ log T/(64M²)`; each right zero is a Lefschetz ratio, two primes determine it. Degree-one Selberg classification [L].
- **(a)** A27, A28.
- **(b)** Source-energy sign (B40, B1); independent count or Rosati producer (B78); arithmetic global trace (B85); mixed Young shapes (B86); genus, Serre duality, Epstein (B65); exceptional-height and unbounded-shape control in the modulated branch (B28).

### SEC — Seam / Fock
- **Path:** factorial jet energy at ξ zeros → RH.
- **Established [L]:** seam admitted; `F_ρ` identified; Fock bound ⇔ RH.
- **(a)** None.
- **(b)** Bound at actual zero parameters (B73).

### CDC — Dagger (BSH alias)
- **Path:** marked-repair equality at ξ zeros → RH.
- **Established [L]:** canonical potential, Euler-face metric, calibration; `N=1,n=2` equality suffices.
- **(a)** None.
- **(b)** Proof-erasure equality at every zero (B74).

### PCS — Co-shift
- **Path:** reflection-odd class vanishes at ξ zeros → RH.
- **Established [L]:** quotient vanishing ⇔ `n^{−ρ}−n^{−(1−ρ̄)}∈ℓ²` ⇔ RH; cutoffs converge strongly with a persistent gap.
- **(a)** None.
- **(b)** Vanishing at every zero; independent differential lift retaining the shift defect (B75).

## 4. Candidates

Each needs its independent mechanism first (B81).

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

| Programme | Established [L] | (a) Just work | (b) Open mathematics |
|---|---|---|---|
| AIF | inner field, Poisson–Jensen, Szegő infimum, Hardy class of a disc datum, near-extremal rigidity, Carleson measure, log-mean at infinity, large-width bound, box budgets, crowd, curve chain, Abel mollifier of a curve, causal certificate, Szegő threshold, inverse scattering, forward map, potential past Born, restoring bound, Bohr profile decomposition, recurrence zero–one law, insertion cone, arithmetic Bernstein, torus walls, echo columns, column calculus, correlated amplitudes, local onset field, certified passivity, the questions of the field | A17 | B2, B57, B66, B82, B83 |
| AAD | producers, Mellin transform, uncertainty, mean value, three-quarters floor, Möbius producer, VK rate, polynomial rate ⇔ strip, first-return bound, returns are prime returns, ledger blindness, parity ledger, Frobenius as stencil, fake prime measures, Hecke action, battery | A29 | B15, B55, B67 |
| CSTW | canonical system, scalar flow, soft kick, Green corner, charts, AC traces, `L¹` drift, Lipschitz increments, sampling, mimics | A15, A16 | B2, B3 |
| CHT | margin law, pinning, datum, bands, bounded extremals for every weight, explicit sup bound, edge law | A6 | B16 |
| VHR | height 67 by Fejér budget; rungs: window, Li, Hausdorff, heat, Jensen, PF, theta | A1, A2 | none; decides no all-aperture statement |
| NGF | frequency, blow-up, gap laws, maximum principle, crystal and reality at critical scale, order bound | A19 | B24–B27, B47 |
| MZF | Selberg CLT, cameras, hyperbolic density, derivative law, rigidity, last scale, Möbius zero condensation | A18 | B57–B61 |
| FFP | `N_d` law, saddle region, stability dictionary, bulk blindness | A20 | B22, B23 |
| ADO | carrier repulsion; a.e. value; exceptional set dimension zero; FE-pair flatness | none | B77 |
| APR | necessary length, filters, prefix amplification, collar laws | A18 | B48 |
| AKLT, ASRP, AE | Stepanov over `ℤ`, Nair lattice, Siegel and Liouville halves, stencil ceilings, Farkas producer at doubly exponential cost; AAL producers, tower detection | none | B48, B83 |
| APD, SEL | Hamburger rigidity, unit-density rigidity, residue gap, defect `1/6400` isolation, one-off models, Bohr obstruction, Selberg rigidity, degree-one classification | A30 | B80, B84 |
| PBAP, W3 | blind positivity, blind ζ dictionary, Carlson threshold, exact null blind test, sharp correlation tail | none | B18 |
| WVL | universal threshold, two-lobe, cut crystal, sampling at a free window | none | none beyond B1 |
| AHD/CACT | aliasing limits, Γ-liminf, dual floors, head reduction, polar capacity, far margin, certified ratio interval, tails, compactness | A9–A13 | B6–B8 |
| CAF, TCS | two-atom, geometric chains, Euler product, explicit current core and tail, rank ten, section heights, growing-block Schur floor | A4, A5, A23 | B19–B21 |
| BHR | modular wave, metric, smoothness, echo train, causal symbol, ringdown, modes, sharp analytic boundary, near-arithmetic ladder exclusion, sharp Bessel and Eisenstein bounds, lift of any modular wave [S] | A25, A26 | B71 |
| AK, Representation | column Young projections, curve phase characters, positive endpoint character, canonical compression, Kloosterman receivers and traces, torus critical points, reciprocal quadric trace | A27, A28 | B85, B86 |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ sign or budget | RW, EWU, OWU, ACT, CHMD, SZ, RN, ACS, AIP, SRT, SC, LI, TT (odd) |
| Σ full-space, which is window sign through Gårding and compactness | HF, SRT and AIP packet branches |
| Σ continuation at small time | ZCG, PTR, LA, GTA, XN, HCF, PA, TH |
| Π square-root precision and long moments | WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| Γ reflection and selection | PM, BAG, SEC, CDC, PCS |
| Missing source landing | APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF |
