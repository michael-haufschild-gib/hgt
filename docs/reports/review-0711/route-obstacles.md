# Route obstacles — status quo

Scope: 38 live route formulations, 9 candidates and their supporting programmes. For each: path, what is established, obstacles that are **(a) just work**, obstacles that are **(b) open mathematics nobody has a solution to**.

Corpus checkpoint: commit `b33ed59737` plus the working tree of 2026-11-07.

**Live** means source observable, proved RH-sufficient receiver and explicit open estimate. **Candidate** means an independent source mechanism or landing is missing. Formulations are not independent mechanisms: HJ is PA, BSH is CDC, FEL's BSY criterion belongs to CTF. A criterion, a source construction, a quotient equality or a scalar grade does not discharge an arithmetic sign or vanishing.

**Evidence.** `[L]` Lean source. `[S]` Lean source unfinished, unintegrated or uncommitted. `[K]` Lean with transitive axiom audit. `[D]` deduction, not a Lean theorem. `[N]` numerical, uncertified. `[C]` classical literature, not formalized.

**Strength.** RH; ≥qRH (zero-free half-plane or Lindelöf); sub (strictly below quasi-RH); method; indep. (independent of RH).

**Labels.** `A*` just-work items and `B*` open problems are listed in full in [obstacles-summary.md](obstacles-summary.md). An A item is known mathematics, finite computation, effectivization or assembly of proved pieces; `(unverified)` marks A items whose difficulty is not established. Wall labels Σ, Π, Γ refer to [walls-ledger.md](walls-ledger.md).

**Notation.** Windows `[−a,a]`. `W` Weil's form, `w_n=Λ(n)n^{−1/2}`, `H` the archimedean–polar form, `P` the arithmetic part, `W=H−P`. `μ(a)` ground energy. `a*(ζ)` onset aperture. `ℋ(c)` Hardy interval, `𝒜(c)` window cone, `λ*(c)` its best margin. `τ_L,τ_R` endpoint traces. `r=τ_R(i)/τ_L(i)`, `L=artanh r`, `Ψ=½log H₁`, `q=Ψ′`. `H_t` the de Bruijn–Newman flow, `Λ_X` its local constant, `τ=t log²X`. `N_d` non-real root count of `R_d(Ξ)`. `w=zetaZeroWidth`, `Θ=½+w`, `Θ∞` asymptotic abscissa. ZAL: finitely many zeros beyond every positive depth (`Θ∞=½`). AAL: finitely many zeros right of `½+h` forces none (`Θ∞=Θ`). `E(s)=(s−1)ζ(s)/s`, `I(w)` inner field. `M_X` truncated Möbius polynomial, `E_X=ζM_X−1`. `N(ρ)` normalized derivative at a right zero. `Φ(u)=Re Σ_ρ e^{u(ρ−½)}/(ρ(1−ρ))` lag function. `vkScale(T)=(log T)^{3/5}(log log T)^{−5/3}`. `R=c⁸/log N`, `W₈(H)=∫H²e^{−8y}`, `R*` the far-margin root. `A(K)` best slope of an integer producer on alphabet `≤K`, `ε=A−1` its rate. `L=log|t|`, `ℓ=log L` in orbit statements. `Q(a)=W(f_a,f_a)`, `f_a=Σa_iB(·−log(i+1))`, `a∈ℤ^N`, the integer probes.

## 0. The picture

| Fact | Evidence | Consequence |
|---|---|---|
| RH ⇔ ZAL ∧ AAL; ZAL ⇒ qRH; ¬AAL ⇒ `Θ<1` | [L] | one half is at least quasi-RH, the other sits below it; `qRH ∨ AAL` is a theorem [D] |
| Under AAL: RH ⇔ ZAL ⇔ finite off-line support ⇔ `κ(K_ζ)<∞` ⇔ bounded nonreal heat count ⇔ finite critical source energy ⇔ eventual Hadamard positivity ⇔ eventual central-gap budget | [L] | every large-height receiver reads RH once one-offs are gone |
| ¬AAL ⇔ `ψ(x)−x=x^{β}T(log x)+O(x^{β−η})`, `T≠0` a finite trigonometric polynomial, `β>½` ⇔ two-prime dilation annihilation of `ψ`; `β=Θ`, `T` unique, coefficients `−ord/(Θ+iμ)`, `η≤Θ−Θ₂` sharp | [L] | failure of AAL is one rigid object, with sign changes at bounded log gap |
| RH ⇔ `a*(ζ)=⊤` ⇔ `1∈ℋ(c)` ∀c ⇔ `λ*(c)→0` ⇔ every window cone nonempty ⇔ two-site PD ⇔ no finite contact ⇔ `Q(a)≥0` on every integer probe | [L] | every window route measures one number; existence of any admissible weight on each window is enough |
| A form homogeneous of degree two is `≥0` iff a function bounded below lies at bounded distance; RH ⇔ every window correspondence form has one; over a curve kernel orders do not supply it, heights do | [L] | what a sign proof needs is a function, nonnegative for an arithmetic reason, at bounded distance from the form |
| Black hole `(q,G,D)` of any channel data: flux, unitarity, edge theorem, positive commuting Hecke at every degree and class; `t²>4q` has resonances off the universal circle | [L] | universal damping is not a law of wave dynamics |
| Parallelogram law for the count at every probe ⇔ `t²≤4q`; over a true curve `K(x,y)=ht(yP₀−xP₁)`, Hasse from it with neither Stepanov nor character sums | [L/S] | the separating property on the graph is a count that is quadratic. Fake: count, not quadratic. ℤ: quadratic, not known count. Curve: both |
| `L′=q−sinh 2L`, `(log K)′=2 cosh 2L`, `H₁H₂=1`; `|L(x)|≤artanh e^{−2(x−c)}+2 osc_{[c,x]}Ψ`, no initial value and no `1/μ`; `Ψ` absolutely continuous on compact precontact intervals, `q_y→q` in `L¹` | [L] | RH ⇔ `Ψ` locally bounded on `[0,∞)` [D]: the Hamiltonian stays finite and positive |
| Lattice PD ⇔ positive-margin outer predictor; reflection data free; passive iff each echo in its Schur band; first reflector reads `Λ(n₀)`; `∂E_n/∂λ(n₀)=−(2/√n₀)A_n(log n₀)`, `E_n` concave in the weights; Born defect `≤K(Π(1+|γ_k|)−1)` | [L] | the forward map from primes to reflectors has an exact tangent at every stage; its size is not controlled |
| Local onset field `Ω_ψ(a,X)`: on-line zeros `≥0`; pair at depth `δ` costs `≤(16/9)δ²a⁴‖ψ‖²`; RH ⇔ `Ω≥0` everywhere | [L] | sign is a function on the plane `(a,log X)` |
| All-height sign up to `a≈log log X−log 4`; density `1−δ` sign for all shape-bounded tests up to `a=δ log T/(64M²)` | [D]/[L] | two proved curves on that plane; both size only |
| At fixed critical ratio: Γ-liminf with weight `α_R>0`; bounded form and masses make `L¹` limits strong; Gårding `Q+B_R‖U‖²≥κ_R·seventhMass+a_RW₈` on the top collar at every `R`; false for unrestricted atoms, `W₈≍N⁸` at `y≈−log N` | [L] | on the collar HF at one ratio is a finite window [D]; prefix coupling is the remaining channel |
| Every route with a saving carries the same Vinogradov–Korobov saving, stencils included: `A(K)−1≤exp(−(log K)^α)`, `α<3/5` | [L] | one width axis; interior values are zero-free strips |
| Polynomial stencil rate ⇔ fixed zero-free strip; rate `K^{−a}` ⇒ `Re ρ≤1−a`; floor `ε≥c/(√K(1+log K))`; all `a<½` ⇒ RH; RH gives `a<1/5` | [L] | production has no content independent of the Mertens level |
| Zeros are exactly the power-law kernel vectors of the cut system; a kernel vector bounded below by the pronic measure vanishes, which reaches exactly `Re s≥1` | [L] | no stencil identity excludes a zero; positivity of the cut system is the edge |
| Complete ledger of a zero mode vanishes for every balanced stencil; degree `k` ledgers have order `m−k` at multiplicity `m`; exact ledgers holomorphic off `s=1`; twin and `Λ` share every leading pole at right zeros | [L/S] | polynomial ledgers read zeros without constraining them and read parity only at `s=1,2` |
| `L(x)≪x^{a}` ∀`a>Θ` ⇔ zero-free `Re s>Θ`; parity-neutral producers at every rate | [L] | a parity source at power saving is a zero-free strip |
| Prime phases: no cancellation below length `c log T` at some height; absolute saving `4·10⁻¹⁰/(L⁸ℓ⁴)` at length `48L²ℓ`; `t^{−δ}` at `L^A`; required at the size curve `≈εL/ℓ` [D] | [L] | the short-sum barrier has a proved left end; between `log t` and `exp((log t)^{2/3})` only absolute savings exist |
| Rounded orbit: same diagonal moments, same early orbit, exact return at `T`; one word certifies precision `≤1/(2(k+2))`; transfer to rare heights stops at Kronecker scale | [L] | diagonal data, group closure and polynomial-phase treatment have proved ceilings |
| `T⁻¹∫_T^{2T}log‖ζ(½+it)‖dt→0` ⇔ `100%` critical-scale clustering ⇔ six further forms ⇔ `I(½+x+it)→0` ⇔ depth density `o(T)` ⇔ density-zero damping deficit | [L] | the near-line layer is one number |
| Near-extremal mollifiers: limit forced to `1/E`; one fixed-`δ` log-dilation equality ⇔ RH; first jet `−(1+γ)` ⇔ RH; over a curve purity gives `|P(v)/P(ρv)|²≤4^{rank}` | [L] | actual holomorphic budget control is missing; boundary quotient means tend to 1 even for nonunitary data [K] |
| Zero `L¹` FE defect, and any defect `≤1/6400`, forces the rational primes; exact count forces them with no analysis; stencil systems have infinite FE defect | [L] | ζ is an isolated point of Beurling systems in FE defect |
| Returns on a disc force `n^{−iτ_j}→1` and a spike near `1+iτ_j`; at a zero a positive proportion of prime returns are not returns of ζ; under a finite layer every phase return is unbounded on every domain joining the zero to `Re s>1`; a bounded return at each zero gives AAL | [L] | phases never obstruct recurrence; the tail does |
| Hull: Haar-a.e. fibre extends zero-free; Liouville fibre extends ⇔ RH; RH ⇔ every nonzero limit of translates zero-free; limits on `Re s>1` fill the torus, twin included | [L] | arguments stable under limits of translates on `Re s>1` cannot separate ζ from its twin |

## 1. Mechanism classes

| Class | Mechanism | Status |
|---|---|---|
| M1 Signed criticality | Primes pay the archimedean–polar deficit by sign in a frustrated critical form | format exact on every window; causal certificate exact; size payment ends before half-width `21/40` |
| M2 Calibration | Window cones, blind positivity, margin | cone pinned at rate `e^{−c/1104}`; exact null blind test; ceiling doubly exponential; sign open |
| M3 Canonical flow | `L,q` of the Weil chain | exact to contact; `Ψ` oscillation is the sole control; contact-uniform bound open |
| M4 Reflection | Krein/Lewis positivity, Eisenstein carrier, Hecke dispersion, ringdown | coefficient completion closed; depth read exactly; Krein law on every system; flux sign open |
| M5 Square-root cancellation | One smoothed prime count, long moments | receivers closed; arithmetic estimates open |
| M6 Continuation | Heat, cosine, Jensen | high-time and typical-height regions closed; small time at all heights open |
| M7 Zero geometry | Cameras, Blaschke factors, inner field, Carleson measure | isolated zeros at rate 2; clusters open; log-mean open |
| M8 Recurrence | Transport of zeros by vertical returns | transport closed; pair returns at typical base; tail fails at a zero; returns at a zero open |
| M9 Production | Integer stencils | exact; rate is the Mertens level on the half scale; zeros are the kernel; no independent mechanism |
| M10 Count | A nonnegative function at bounded distance from the form | exact Tate law; Manin over curves; over ℤ local data only |
| M11 Orbit at finite time | Prime phases at one height | absolute non-alignment; proved ceilings for words, moments and transfer; proportional saving open |
| Amplifiers | Diophantine repulsion, integrality as amplification | amplify a certificate, produce none |

## 2. Shared obstacle blocks

### S1. Complete Weil family at the critical curve

Routes: HF, SRT, AIP, ACT, ACS (atomic), SC, CHMD (index). Programmes: CACT, AHD, CSAR, ACPL, ADT, RAPT, TM, SSHA, CAF.

Established:
- Full tilted-spline matrix PD for `1≤c≤(log N)^α`, `α<1/8` [L], through one small multiple `c≤2K₀(log N)^{1/8}` [K].
- Every compact C² profile: energy `≥a e^{−Bc}‖x‖²` on conductors `≤N^θ`, `θ<¼`, `c≤b log log N` [L].
- Every fixed ratio `R`: critical pencil `κQ+(7J/R)W₈`, aliasing limit, fixed-family inertia, positive low packet through `⌊(log N)^{13/32}⌋` [K], polar capacity `S_A²/(J₁/R+κg)` [K].
- Weighted floor `Q(H)≥−F(p)∫e^{−pu}H²`, `p>1` [L]. Prime form `|P(H)|≤εW₈(H)+B_ε‖H‖²` for `H` supported in `y≤0` [L].
- Atomic synthesis: mixed mass, below-grid recovery, sharp aliasing floor; Γ-liminf with weight `α_R=7(∫φ²)J(1)/((∫φ)²R)` at every `R` [L]. Bounded form, `L²` and `W₈` give uniform Fourier tails and strong `L²` limits; prime sum and pole moments pass to the limit [L]. Physical plus Fourier tails give precompactness [L].
- **Gårding verdict [L].** At `c⁸/log N→R>0`: `Q(U)+B‖U‖²≥aW₈(U)`, `a>0`, is false on `(conductorSubspace 1 N)ᗮ` for every `B`: the deep difference `z_N=(e₁−√2e₂)/√3` has energy `O(log N)` in unit `L²` and `W₈≍N⁸`. On the top collar `Ioc(N/linearDefectCutoff c,N)`, uniformly for `c⁸≤R log N`, every `R>0`: `Q(U_y)+B_R‖U_y‖²≥κ_R·seventhMass(y)+a_RW₈(U_y)`. Lévy interpolation takes the shell commutator from `O(cGS)` to `O((c²/N)GS)`.
- Far band: `farMargin R=3D/(8R)−C−C′R`; coercive with floor `min(1,farMargin R)` on the complement of conductors `≤N^θ` for `0<R<R*`; joint complement of the low packet coercive for `0<R≤min(1,5R*/6)`, `c≥(log N)^{1/16}` [L].
- Prefix: `(∫|prefix|)²≤C_φP/(4c)`, `P` prefix coefficient square mass; on small multiples a reserve `θ log N/(8C)` on prefix mass of conductors `>N^θ` [L].
- Plateau Schur floor `(a/2)e^{−Bc}‖z‖²` on conductor blocks `Q≤(log N)^{1/32}`, `c≤b log log N`, `log M≤√log N`; a full-space floor passes to the Schur complement of every tail [L].
- Periodic charges: `J_N=O(log N)` iff gcd profile; four literal channels; on orthogonal pairs the mixed error vanishes on the window `2α<β`, `β+2α<½` [L].
- Receiving modes with bounded charge and vanishing physical energy, capacity `log log N+O(1)` [L/K].
- Dirichlet-shift companions reduce long windows to heads; `d=2` unconditional; all `d` ⇔ RH [L].
- Far bubbles do not decouple; `Q(φ−φ(·+t))=2Q(φ)−2c_φ(t)` [L].

Structure [D]:
- A negative sequence supported on the top collar has `W₈` bounded by `B_R/a_R`, then a strong limit `F≠0` with `Q_T(F)+α_R∫_{y<0}F²e^{−8y}≤0`. The limit pencil is a finite rung. So on the collar HF at one ratio is a window of half-width of order `log R`.
- Deep atoms carry a positive reserve of order `θ log N` per unit prefix coefficient mass on far conductors (proved on small multiples), so the question at fixed `R` is a Schur complement of the prefix against the collar. A cross operator between prefix and collar is sparse, with weights `(n/m)^{½}Λ(m/n)`; its norm decides whether the prefix decouples.
- Low-conductor vectors (the pole line first) are spread over the prefix, so the low packet enters this Schur complement.

| | Obstacle | Strength |
|---|---|---|
| A9 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | — |
| A10 | Collar compactness assembly: collar sign at `R` from one window | — |
| A11, A12, A13 | Prefix–collar coupling at fixed `R` (unverified); low-packet/complement Schur on the certified interval (unverified); growing-period charges (unverified) | — |
| B6 | Full-space sign eventually at every `K` | RH |
| B7 | Growing families, coalescing frequencies, conductors between `(log N)^{13/32}` and `N^θ` above `R*` | sub |
| B8 | Head thresholds for every `d` | RH |

### S2. Window tower and canonical flow

Routes: RW, EWU, OWU, ACT, AIP, CHMD, TT (odd), HF, ACS, SRT, SZ, MSC. Programmes: CWS, WTZ, DZG, GWZ, CSTW, SWC, FADF, CHT, AIF.

Established:
- Precontact de Branges chain, canonical system, `H₁H₂=1`, flux, sampling bases, positive on-line mimic at every precontact aperture, Gram AC with no atom [L].
- `L′=q−sinh 2L`; `Ψ=L+θ`; contact criterion; contact scaling `|q|≈(1+1/γ)m` at order `γ`; contact forces kernel blow-up [L].
- Traces, `r`, `Ψ` absolutely continuous on compact precontact intervals; `q=Ψ′` a function; `q_y→q` in `L¹` by a Kato contraction; constants retain the ground energy at the top of the interval [L].
- Restoring bound for the actual chain; soft prime kick `(Ψ(x)−Ψ(a))log(1/(x−a))→w(a)` [L].
- Born model: `1−r_n²≥e^{−10A}/(2√n log n)` [L]. Lattice flow `artanh r_{n+1}=artanh(s r_n)−artanh γ_n`; curve flow with boundary at the number of angles [L].
- Causal certificate, Szegő threshold, free reflection coordinates, Schur band, prime dictionary, injective forward map, exact tangent, concave margins [L]. Certified windows `≤2a₀` carry the full causal chain with `Λ(2)` [L].
- Cone: pinning, ceiling, bands, datum classification; every real weight has an attained ground state, bounded, with exact edge law [L].
- Exact null blind test `Φ=Ξg`, sharp tail exponent one [L].
- Floors `(1/20000)/2^k` through `a_k<0.3621` [L].
- Window correspondences: Rosati form has a naive height ⇔ positive; length `≤3/5` has one; RH ⇔ all windows [L]. Atoms form the Arakelov bundle `⊕_{m≤N}𝒪(½log m)` with exact RR [L].

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

Routes: RW, ACS, SRT, ZCG, WD. Programmes: AIF, WVL, MZF, PTT.

Established:
- `Ω_ψ(a,X)` as a sum over zeros at scale `1/a`; on-line terms nonnegative; depth cost; RH ⇔ `Ω≥0`; bounded apertures positive at every height [L].
- `Q_γ(F₀)=Q(F₀cos γ·)+Q(F₀sin γ·)`: prime part `(1/π)∫Φ D_N(γ+t)dt`, arch part `≥(½log(2+|γ|)−C)∫F₀²`, no shape condition, no zero information [L].
- `A=δ log T/(64M²)`: outside a test-independent set of measure `δT`, `Q_γ(F₀)>0` for every `F₀∈C²_c[−A,A]` of shape `≤M` [L].
- Visibility: `k·pairEnergy(δ,a)≤(K/2)ℓe^{2(2π/ℓ+σ)a}`; cut crystal hides fixed depth to aperture `(log T)/36`; positivity at `λ·½log T`, `λ>1`, gives depth `<e^{−c log³T}` [L].
- An isolated zero of depth `δ` with no companion in radius `R` forces the column above `ce^{θa}` of its norm once `sinh(δa)⁴≫log γ·poly(a)(1+e^a/(1+R))` [L].

Structure [D]:
- On `PW_a`, `Q` is diagonal in frequency, so global sign at `a` follows from local sign at `a+b`, all heights.
- `2e^{a}≈½log X` gives all-height sign to `a≈log log X−log 4`. Gaussian moments of `D_N` hold to `k≈log T/(2A)`; they reach all heights only for `K<½` in `A=K log log T`, below the size bound.
- All-height sign, the zero-free region and the width axis are the short-sum barrier: block S11.

| | Obstacle | Strength |
|---|---|---|
| A14 | Frequency-integral identity in Lean; moment upgrade of the exceptional proportion | — |
| B28 | Local Weil positivity at fixed `λ>0` on density-one heights | sub |
| B46 | Proportional saving against size for prime polynomials of length `(log X)^{2K}`, `K≥1`, all heights | sub |

### S4. Continuation and nodal geometry

Routes: ZCG, LA, PTR, HCF, PA, GTA, XN. Programmes: NGF, FFP, ADO, RHTower heat.

Established [L]:
- Collision criterion; horizon `(6600/9991+ε)/log X`; `c d²/log X≤Λ_X`; a heat coefficient below a fixed `κ₀` at all large `X` gives a zero-free half-plane.
- Fock identity, monotone frequency, order law, Hermite blow-up, gap law, maximum principle, uniform mesh, cluster spread, crystal symbol, depth moments, finite-speed lateral energy.
- Multiplicity `≤(3300/9991+ε)log X`.
- Density-one: `Λ_Xlog X→0`. Exceptional set `θ(κ)=1−κ³/41943040000`, `0<κ≤8`. Critical scale: all zeros real, central gaps, crystal law outside `δT` heights.
- Complex saddle; line model at power level; quotient by an isolated zero; sharp depth law for isolated simple zeros.
- `N_d` nondecreasing, supremum is off-line multiplicity, `N_d≤300√(d log d)`, inner roots real, Cauchy bulk blind.
- Cosine strict Laguerre ⇔ RH; holds for `h≥½` and above VK.
- Nonrepelling ζ-values have Hausdorff dimension zero, contain a dense residual set; `0∉E` undecided.
- Maximal-angle zero: Hermite–Biehler law, RH ⇔ modulus equality at zeros; Stieltjes sign at the extremal zero.

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
| B92, B93 | Rotated relation with coefficients of the size of `Q`; a contradiction from the extremal Stieltjes sign | RH |

### S5. Near-line geometry and long moments

Routes: WD, CTF, MC, TG; census. Programmes: CDG, APR, MZF, AIF.

Established:
- Selberg CLT; off-line `log|ζ|` is the prime field up to bounded error; barrier law; Lorentz mass exponential tail [L].
- Prime camera rate 2; Turán camera for bounded clusters; hyperbolic density theorem without separation; `N(ρ)≤Π_Dϱ`; `N(ρ)=exp(−Σ_{a≠ρ}m_aG(ρ,a))` [L]. Crowds exponentially rare [L].
- Box budget, arithmetic embedding, Carleson measure `μ(box)≤(5/2)xI`, embedding at scale `x` with constant `I/(2πx)` [L].
- 8-way log-mean equivalence; Abel log-mean ⇔ `I(½+x+it)→0` ⇔ depth density `o(T)`; `I` bounded ⇔ `O(T)`; `I≤log(1+log 5x)+C` and depth mass `≤(5/2)T(log(1+log 5T)+C)` from the empty mollifier [L].
- Jensen extremizer: moments do not determine the log-mean [L]. Necessary-length laws, last-scale floor, short weights blind, occupied windows lose one log, corridor exceptions [L].
- Long-moment slope `2wθ`, quantifier collapse, one-window and positive-proportion RH forms, exponent rigidity, Möbius zeros condense on `Re s=Θ`, collar factorization [L].
- Twisted second moment to length `U^{21/50}` [L].
- Dilation: `I(1)−I_δ(1)≥0`, one-`δ` equality ⇔ RH, jet `−(1+γ)` ⇔ RH; single factor model-part limit `1−‖β‖⁻²` [L]. Surplus as a ratio of Szegő budget infima; Euler prefixes pass through the identity [S].

Structure [D]: Isolated means Carleson uniformly separated in `H²(Re s>½)`. Jensen with a second moment loses the variance of `log|ζM|`. The log-mean is the Bode integral of the causal symbol at universal damping [L].

| | Obstacle | Strength |
|---|---|---|
| A17, A18, A21 | Selberg `O(T)` depth density in the inner-field form; moments past `21/50`; census items | — |
| B57 | `T⁻¹∫log‖ζ‖→0`, equivalently depth density `o(T)` | sub |
| B58 | `D_win` | sub |
| B59 | Cluster wall: Density Hypothesis rate for all near-line zeros | sub |
| B60 | Exponential moments of the Green potential at deep zeros | sub |
| B61 | A detector past the last scale | sub |
| B62 | Cofinal long moment bound | RH |
| B66 | Near-unit holomorphic mollifier budgets; zero dilation surplus | RH |
| B82 | Inner-field decay `I(½+h+it)→0` | ≥qRH |

### S6. Production and precision

Routes: WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, LI, AIP. Programmes: ASRP, APR, AGT, AKLT, AE, AAD, RAC, MMD.

Established [L unless marked]:
- Band ⇔ every classical one-sided criterion; `E(n)≤(2+γ−log 4π)√n` ⇔ RH; `Ω±(√n)`; entry filters; necessary length; length–precision law; gauge torus exponents `[Θ,1]`; Nair lattice exact; Siegel and Liouville halves RH at square-root scale; integrality exponent `Θ`; univariate ceiling `e^{−0.87n}`; slope ceilings.
- Producer: balanced stencil, `g≥0`, `g≥m` on a window. `c=μ∗h`; constant window ⇒ `c=mμ` there. `D_cζ=Σg(r)(r^{−s}−(r+1)^{−s})`: a producer is a mollifier on `Re s=1`. `|M(n)|≤εn+12(w/m)√n+K`, with no zero of ζ.
- Uncertainty `m|1−B^{−ρ}|≤|ρ|(4+1/β)w^{1−β}T^β`; peak law `w≤100(1+log K)²(KT+m)`; floor `ε≥c/(√K(1+log K))`; rate `K^{−a}` ⇒ `Re ρ≤1−a`; all `a<½` ⇒ RH.
- Explicit polynomial-alphabet Möbius producer from a Mertens level; weighted entanglement gives `a<σ/(2+σ)` from `M(y)≪y^{1−σ}`, so RH gives `a<1/5`; `hasRate_vk`: rate `exp(−(log K)^α)`, `α<3/5`; polynomial rate ⇔ zero-free strip.
- Parity: parity-neutral producers `≤4000δ(1+log T)²` on `[1,T⁵]`. Power-saving parity bound = strip. Sieve and producer cones disjoint.
- Cut system: zeros are the kernel; unique fake at infinite level; strong duality; profinite rigidity; no uniform measure; carry law; every integer a cut; self-similar count quantized; exchange law; stencil systems infinite FE defect.
- Ledgers: order `m−k`; twin at every degree [S]; Selberg reading passes filters and reads `s=2`; gain `√(N/y)` [S].
- Carlitz stencil over `𝔽_q[T]`: exact ledger from size and multiplicity alone. Curve stencil stops at `|a|≤q+1`.
- Torsion: Λ is a log-resultant; prime form is a renormalized positive energy; `ν̂_N(1)=M(N)`.
- Descent: over `ℤ[ω]`, `μ(I)conj(G₁)=c(I)G₂`; ray phase fixed; Kubota multiplier, finite-volume quotient, variational Laplacian, cusp barrier with potential `≥1` off a compact [L/S].

| | Obstacle | Strength |
|---|---|---|
| A21, A30, A31, A33 | Chowla; optimal producer exponent; discrete Beurling one-off; cubic continuation, residue, Fourier identification | — |
| B48 | A deciding input at square-root precision | RH |
| B55 | Any polynomial stencil rate (is qRH); rates `a↑½` (imply RH) | ≥qRH to RH |
| B15 | Mertens level past VK, equivalently stencil rate `α>3/5` | sub |
| B14 | Window negativity exponent `<½`; any interior width value | ≥qRH |
| B56 | `Θ<1⇒Θ=½` | sub |
| B67 | Parity at power saving, which is a strip up to twist-absorbed zeros | ≥qRH |
| B91 | Classification of kernel vectors of the cut system | method |
| B94 | Transfer of cubic Gauss conversion to rational-integer Möbius | past VK at least |

### S7. Reflection and carriers

Routes: PM; W1C (candidate); RN and PTR in part. Programmes: RIT, ART, AOT, ACP, BHR, ASH.

Established:
- Resonance ⇔ `ζ(2s)=0`; `Q=2Re[WH,WH]`; `D_s≤0`, zero iff `Re s=¼`; lifted Hecke and Lewis carriers; closed Cauchy reflection [L/K].
- Line law for `c_Y`, `Y>1`; boundary norm; `|ζ(1+it)|≥1/(6250t³log²t)`, `t≥2·10⁷`; Schur positivity blind to zero position [L].
- `V_p(ρ,Y)=2(1−p^{Re ρ−1})`, one-sided bound at one `p,Y` ⇔ RH; Poisson mixture positive for every `Re u<0` [L].
- `S(s)=φ(s)(s−1)/s` is a Blaschke product over `(1+ρ)/2` [L].
- Horizon: exact lift of any modular wave; `R=−12`, coupling `+2`; echo train `K(τ)`, transform `Λ(2w)/Λ(2w+1)`; causal symbol; compact pulses, image field, uniform ringdown; multiplicity `m` gives degree `≤m−1`; every zero excited; raw echo has no pointwise exponential bound; one-sided quarter-line bound ⇔ RH; `L²` data split into three channels; contractive cosine families; Maass forms vanish at the cusp, `λ≥¼`; exact metric of a pulse in vector and scalar sectors, ringing in the modes of zeros [L].
- Graph: black hole `(q,G,D)`; Jost function; exact ringdown with no remainder; plus branch purely incoming; flux and mass law; Hasse window; fakes; Hecke at every degree and class, positive and commuting; Hecke rigidity `X^d+Y^d`; cuspidal sector; base-change tower with tensor trick; Krein flux; Lax–Phillips matrix; Kramers–Kronig; throat, with FE only at genus `≤1` on a path quotient [L/S].
- Krein law at every genus and on the modular horizon; one clock; KMS strip; rank barrier; bulk log-mean; horocycle = wave on the graph [L].
- Count law, integer probes, heights on the twisted curve, Hasse from the count law [L/S].
- No `ℓ²`-perturbed arithmetic progression of zeros [L].

Structure [D]: The massless topological black hole is locally AdS₄. Echo delays `2log c` are cusp-to-cusp lengths of `Γ`, and the echo train is the cusp channel of the image sum [L for the images]. The radial problem is exact Pöschl–Teller; zeros enter only through Eisenstein poles on the horizon. `𝒬` is the determinant of the probe on the two-dimensional state space: universal damping says the state map is elliptic.

| | Obstacle | Strength |
|---|---|---|
| A25–A27 | All-`n` physical moments; Weyl law, metric of `L²` data, regularity at `r=1`, scalar `s=u−½`; modular dictionary | — |
| A32 | Manin at higher genus through a constant Jacobian (unverified in corpus) | — |
| B68 | Independent `D_s≥0`, nonnegative Krein flux, or all-zero dispersion bound | RH |
| B69 | Positive physical carrier | producer |
| B70 | Zero-free curve inside the strip from the carrier: lower bound for `V_p` | sub |
| B71 | Sharp decay of the smoothed resonant sum (any uniform gap ≥qRH) | RH |
| B87 | A count for `Q` over ℤ | RH |

### S8. Index and support

Routes: HKT, AKLT, SC, RIT, CWS through HF, ACS; LA. Established [L]: `κ(φ_c)=κ+1`; finite index ⇒ Lindelöf; `κ∈{0,∞}` under escape, mixing or height decay; window index counts critical lengths; `sup_dN_d` off-line multiplicity; `K_ζ^n` PD ⇔ RH; finite off-line support makes all but `(κ choose 2)` prime towers decide.

| | Obstacle | Strength |
|---|---|---|
| B12 | Index ceiling uniform in resolution | ≥qRH |
| B13 | Exclude finite nonzero off-line support | sub |
| B23 | `N_d` bounded | ≥qRH |

### S9. Abscissa split, recurrence, one-offs

Routes: BAG, JAS shell branch, SC undamped branch, WL sparse samples, ZCG one-off branch. Programmes: AKLT, ZCG, AIF, APD, AAD, RAC, PTT.

Established:
- Split RH ⇔ ZAL ∧ AAL ⇔ ZAL ∧ zero-disc weak recurrence ⇔ inner-field decay ∧ recurrence [L].
- Producers of AAL: bounded lags on one progression or a log-dense set; nonnegative twisted plateau energies; JAS at level one; off-line chain; infinitely many bounded prime towers; one bounded two-prime cone; shell positivity infinitely often; a bounded phase return at each right zero. All retain their source bound [L].
- ¬AAL: bilateral spectral gap, finite top and bottom layers [L]; finite oscillation of `ψ(x)−x`, uniqueness, quantization, remainder ceiling `η≤Θ−Θ₂`, remainder floor `½`, bounded-log-gap sign changes, alternating-`Λ` transfer [L]; two-prime dilation annihilation, single-base periodic pinning [L]; `Φ(mℓ)` unbounded on every progression; `K_ζ` bounded on finitely many towers; `|E_X|≥X^κ` off a vanishing set; annihilators nonvanishing on `Re s≤½`; twisted FE after Blaschke division [L]; every phase return unbounded on every domain joining a top zero to `Re s>1` [L].
- Rightmost-zero jets: `Λ`-moments/`k!` at `ρ+1→−m`; coefficient-square diagonal `→0`; off-diagonal `→m²`; shifts `≤r^k`, `r<R²`, contribute `o(1)`; horizontal gain `<gap<½` [L].
- Returns: transport of zeros; return exponent `≤` density exponent, jump at tolerance `≍r^D`; pair recurrence at typical base; returns on a disc force `n^{−iτ_j}→1` and a spike near `1+iτ_j`; limits embed onto the torus; tail fails at a zero; Dirichlet polynomial zeros recur effectively [L].
- Effective transport: stated disc reaches `Re s=−1/10`; scope in Γ107.
- Countermodels: continuous Beurling systems with exactly one off-line pair, no recurrence [L]. Rational quartet surgery: FE exact, not Bohr almost periodic [L]. Golden `L`-function: periodic returns, zero right of the line, fails the count [L].
- Rigidity: integrable defect at unit density forces integers; residue gap; defect `≤1/6400` forces the rational primes; exact count forces them; adding generators adds no zeros; zeros right of `σ` invariant under exchange of exponent `<σ` [L].

Structure [D]: Alignment up to `y` resolves ζ at scale `1/log y`, and prescribable `y` is `≈log t`. The resonator mean of `|ζ(s+iτ)|²` on the Bohr set is `|Π_{p≤y}(1−ω_pp^{−s})^{−1}|²Π_{p>y}(1−p^{−2σ})^{−1}`, for `σ>½` and resonator length `≤T^{½−ε}`. Its Euler part never vanishes and carries `y^{ρ−s}` left of a right zero. So typical aligned shifts are large left of a right zero in every world, and a bounded return is an atypical member of the Bohr set. Harmonic-measure reasoning gives that transport at precision `ε` needs a two-sided bound `|log|ζ(s+iτ)||≲log(1/ε)`, compatible with the zero term only at left depth `≍1/log y`. Exact integrality and exact FE specify one function, so AAL has no deformation class.

| | Obstacle | Strength |
|---|---|---|
| A22, A23 | Repair of the effective transport disc; Bohr-set second moment | — |
| A31 | Discrete Beurling one-off and its FE defect | — |
| B83 | AAL | sub |
| B89 | Bounded or polylogarithmic aligned return at each right zero, on a domain right of the line | sub |
| B13 | Finite nonzero off-line support, the smallest instance | sub |
| B84 | Smallest FE defect carrying a one-off | method |
| B72 | Cutoff-uniform target mass | RH |
| B82 | Inner-field decay | ≥qRH |

### S10. Count and effectivity

Routes: ACS, HF, PM integer probes; RW through window naive heights. Programmes: AE, CWS, LST, KPA, ASH, RIT.

Established:
- Polar surface calculus: Riemann inequality and subquadratic growth force Hodge index; effectivity function exists under Hodge index; abundance rate; five currencies of effectivity [L].
- Tate law: `q` homogeneous degree two is `≥0` iff naive height exists; approximate parallelogram gives exact; midpoint-convex at bounded distance also suffices; Northcott at torsion [L].
- Curve: Rosati has a naive height ⇔ unitary; kernel orders do not supply it; actual hyperelliptic curves have naive heights through Stepanov and Gauss sums [L]. Elliptic: height on `h(T)Y²=h(X)`, exact parallelogram, Hasse from the count law [S].
- Base: theta `h⁰` with exact RR; Künneth count on a polar surface with `h¹` split into positive Künneth and primitive `½δ`; base `h⁰` does not extend to a quadratic Riemann inequality; free polarization `log ϑ(J,t)=πJ²/t+O_t(1)`, soft [L].
- Prime data: Λ is an intersection number of torsion orbits; `T_r` PSD; sign lost in `log(1/(1−r))Σx²` [L]. Log-torsion `ψ(N)`: RH ⇔ `N+O(√N log²N)` [L].
- Source cone and all-aperture RR constructed; Bézout ⇔ RH; primitive `h¹` coercive for `a≤181/500`; bidegree counts see no primitive class; fixed-rank lattice counts violate surface RI [L].
- Height principles: Rosati form bounded above is `≤0`; degree zero forces proportionality, on curves, scaling data and windows [L].

Structure [D]: Literal `K:ℕ` equal to `Q(a)` is not the usable form: `Q` contains Gamma integrals and local degrees `log p`. The usable form is a real function at bounded distance, a sum over places with local degrees. Actual modular surfaces see only the cuspidal part: Hecke curves on `X(1)×X(1)` are bidegree classes, and the primitive part of `X₀(N)×X₀(N)` is `End J₀(N)`; resonances live on the Eisenstein sector [L for the sector split].

| | Obstacle | Strength |
|---|---|---|
| A32 | Manin at higher genus | — |
| B87 | Function on correspondences, nonnegative for an arithmetic reason, at bounded distance from the form | RH |
| B88 | Torsion self-energy paid by the archimedean reserve at finite `r` | RH (all windows) |
| B95 | Abelian group with Hecke endomorphisms `T_n`, `T_n′T_n=n`, whose trace form is `Q` | producer |
| B65 | Genus upper law; logarithmic Serre duality; first Epstein real zero | indep. to sub |

### S11. Prime orbit at finite time

Routes: BAG, TH, SRT, RW, ZCG carriers, and every route at the all-height wall. Programme: PTT.

Established [L]:
- Finite-time Bohr isometry: `2(Y+1)τD<ηL` gives entry to every half-space at level `m/(m+1)`; every window `exp((20/δ)y log y)` enters every box on primes `≤y`.
- Effective Kronecker; left endpoint of the short-sum barrier.
- `le_of_aligned`, Tarry–Escott words, squared words with logarithmic Hankel form, misalignment band, mass of misaligned primes, escape from low-rank progressions, avoidance of torsion points.
- Savings: `T^{−2/(A−1)−δ}` at `(log T)^A`; on any set of `(log T)^{A′}` primes, top of the column included; `exp(−L^β)` at `7L^A`; `4·10⁻¹⁰/(L⁸ℓ⁴)` at `48L²ℓ`; modulus below size by `10⁻²⁵L⁻¹⁹ℓ⁻¹⁴`; `√P`-gain away from small primes; `‖Σ_{n<N}n^{it}‖≤N(1−1/(10⁹L⁸ℓ⁴))`; `|ζ(σ+it)|≤ζ(σ)exp(−(log|t|)^{−C})`.
- Energy: clocked moment exact; diagonal range; last-moment count `H^{1/A+o(1)}`; past-diagonal bound with gap the density of smooth numbers.
- Ceilings: rounded orbit; one word `≤1/(2(k+2))`; polynomial phase saves `≤2/(k+1)` without excluding binomial denominators; squared word free of small primes is an almost-prime tuple in a sumset; transfer to rare heights stops at Kronecker; `|ι|log G≲log T`.
- Corners: long-time means and absolute moments blind to the twin; Fejér mean at the start of the orbit sees the sign.
- Certificates: pointwise tautological; frozen costs size; prime-by-prime above size; Agler wall for finite primes and for all primes on `Re s>σ₀≥½`; rank one free; coordinates that see the height telescope on `Re s>2`.
- Hull classified; critical coupling of the base; pole's price `Σ_{p≤z}cos(u log p)/p≤log(8log|u|+39)+C`; large-value heights form approximate groups.

Structure [D]: On the range between `log t` and `exp((log t)^{2/3})` the Taylor degree of `t log(n+h)` exceeds `(log length)²`, where Vinogradov's saving `exp(−c log³y/L²)` is trivial. General high-degree Weyl sums can have no saving; `t log n` has the multiplicative structure `log(ab)=log a+log b`. The required saving at the size curve is `≈εL/ℓ` and the proved one is `≈L⁻⁸`. Pigeonhole on products reaches precision `T^{−1/(A−1)}` at `y=L^A`, not a constant.

| | Obstacle | Strength |
|---|---|---|
| A14, A24 | Moment upgrade; certified scans and brackets | — |
| B46 | Proportional saving at length `(log X)^{2K}`, all heights | sub (up to crystal shielding) |
| B15 | Past VK | sub |
| B90 | Certificate past the abscissa in coordinates that see the height | method |
| B20 | Oscillation of the actual amplitude with the height | RH (all primes) |

## 3. Live routes

### WL — Weil lag
- **Path:** bounded prime-deficit critical energy or one-sided `Φ` → RH.
- **Established [L/K]:** bounded endpoint energy ⇔ RH; `E(n)≤(2+γ−log 4π)√n` ⇔ RH; `Ω±(√n)`; first-band abscissa `2Θ`; gauge exponents `[Θ,1]`; subtracted lag `Φ_S≤Me^{au}` ⇔ ZAL; density-zero excursions force top weight `≤0`. Half-scale producer bounds and cut kernel through AAD, RAC.
- **(a)** A30 (no movement of the route).
- **(b)** `E(n)` upper bound at the ceiling; first-band square-root bound (B49); half-power at the trivial gauge (B50); deciding input (B48); Mertens level past VK (B15).

### RW — Restricted Weil ground energy
- **Path:** `μ(a)≥0` at every radius → RH.
- **Established:** block S2; local sign S3; every window cone nonempty ⇔ RH; RH ⇔ relative compactness of orbit correlations; RH ⇔ naive height on every window.
- **(a)** A1–A3, A15, A16.
- **(b)** All-aperture sign (B1); bounded oscillation of `Ψ` (B2); variation of `r` free of `1/μ` (B3); outer predictors at every window (B4); margin law (B16); blind positivity on nonnegative mixtures (B18); count on windows (B87).

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
- **Established [L/K]:** bounded damped `E_ε` ⇔ RH; fixed `t₀`: `M_N(½+it₀)≪N^ε` ⇔ RH; undamped Hilbert energy `≤CTe^{−c·vkScale(T)}`; Möbius zeros condense on `Re s=Θ`; Haar-a.e. exponent `½`, Baire-generic `1`; flip exponent `max(θ,Θ)`; producer rates force `Re ρ≤1−a`; parity-neutral VK rates; Liouville exponent ⇔ zero-free strip; cubic Gauss conversion over `ℤ[ω]` with fixed ray phase, Kubota multiplier, finite-volume quotient, variational Laplacian.
- **(a)** Logarithmic two-point Chowla (A21); cubic spectral theory and theta residue (A33).
- **(b)** Trivial-gauge cancellation or independent zero exclusion for `M_X`; signed long-modulus tail (B50); deciding input (B48); past VK (B15); transfer from the cubic conversion to rational-integer Möbius (B94).

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
- **Established [L]:** blocks S4, S5, S9; cameras, sharp location with closed-form height; explicit exceptional exponent; one-off structure and rightmost-zero jets; maximal-angle law.
- **(a)** A19; A22.
- **(b)** Collisions at small time, all heights (B24); frequency `<1` (B25); time-0 selector (B26); non-size frequency input (B47); runs (B27); FE-pair reality with coverage (B76); crowded and multiple zeros in the depth law (B59); long-shift `Λ` correlation or a bounded return in the one-off world (B83, B89); rotated relation or extremal contradiction (B92, B93).

### TG — Topological sub-unit gate
- **Path:** cubic defect trace norm `<1` → integer zero count vanishes → RH.
- **Established [L]:** defect constructed, trace class; multiplicity `≤` trace norm; Gaussian passage alternative; explicit central-gap inequality `P(y)−C(y)≤−1/10+32√y`, `0<y≤1`, ⇔ RH.
- **(a)** None that moves the route.
- **(b)** Trace norm `<1` on every rectangle, or bounded centered Gaussian oscillation (B38).

### HF — Hodge / Hecke / complete cells
- **Path:** complete arithmetic form `≥0` → Hodge index → RH.
- **Established:** blocks S1, S10; cofinal source-work `≤2` ⇔ RH; sharp Schur bound `½log N`; collar Gårding at every `R`; unrestricted Gårding false.
- **(a)** A9–A13.
- **(b)** Full-space sign at every `K` (B6); growing twists and conductors (B7); head windows (B8); source-work ceiling (B41); top coprime stratum (B10); zero modes (B9); exact SOS on a two-prime lattice (B11); Rosati and band poles (B78, B79); count (B87).

### CHMD — Causal hyperbolic–modular duality
- **Path:** one-sided bounded prime wave or odd Doob half-threshold bound → RH.
- **Established [L]:** wave and Doob receivers; normalized prime−pole decay `O(e^{−√log Y/92160000})`; nonfirst source retains fraction `1−ε` of Gamma energy.
- **(a)** None that moves the route.
- **(b)** Either side of the unnormalized wave bound, or complete odd sign paying first-prime, potential and polar terms (B35, B4).

### TH — Theta moment positivity
- **Path:** signed center-mixed jets → all-rank Hankel → RH.
- **Established [L]:** full-source rank ten at `0<a≤½`; rank `N` from height `41+6(N+2)log(N+2)`; all ranks in a VK collar; two-atom and `q^n`-chain all-rank sign; `S=Π_pT_pA`; `A` not a positive Laplace mixture; `current=2|Ξ|²Re ξ′/ξ`; insertion cone = exponentially convex for left growth `κ<½`; `κ=½` exact threshold of the `L²` prime-pair cone; any all-base torus-positive amplitude with `κ<min(1,κ₀)` vanishes, so the theta amplitude is not all-base torus-positive; locking = torus positivity for fixed amplitudes; columns add; products of columns rigid; Sato–Tate pairing; base pays by size when `Σlog p/(p^{½+a}−1)<½log(b/2π)`; alignment has a height in `[B,BQ^{|S|}]`; `thetaAmp(x)e^{x/2}→½`.
- **Structure [D]:** `A` grows at the critical rate `e^{|x|/2}`. A proof through `S` must exhibit oscillation of `A` with the height to the end.
- **Numerics:** positive at actual phases, `b≤775`; torus-uniform positivity fails once primes `≲19–47` are free [N].
- **(a)** Rank 11 (A4); tail-failure certificate (A5); certified scans and `S*` brackets (A24); verified ranks (A1).
- **(b)** Exact torus law for `S*(a,b)` and cross-chain positivity on small `S` (B19); height-dependent amplitude oscillation (B20); all ranks at every `a` (B21); certificates in coordinates that see the height (B90).

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
- **Path:** scattering source → Krein/Lewis positivity, integer-probe sign, or one-prime dispersion bound → RH.
- **Established:** block S7; integer spline-probe positivity ⇔ RH; Krein square decays at the universal rate unconditionally; flux sign ⇔ RH.
- **(a)** A25–A27.
- **(b)** Independent `D_s≥0`, nonnegative Krein flux, integer-probe sign or all-zero dispersion bound (B68); positive physical carrier (B69); interior zero-free curve (B70); sharp decay of the resonant sum (B71); count for `Q` (B87).

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
- **Path:** approximation, defect, BSY sign, log-dilation equality or mollifier infimum → RH.
- **Established [L]:** real unit-bounded rows ⇔ RH; sharp defect `D_y≥c_ρy^{2Re ρ−1}`, sparse subpolynomial ⇒ RH; BSY `I≤0⇔RH`; positive-proportion form ⇔ RH; exact infimum `exp(2I(1))`; rigidity of near-extremal families; one-`δ` dilation equality ⇔ RH; first jet ⇔ RH.
- **(a)** None that moves the route.
- **(b)** Vanishing-error rows, sparse defect, BSY sign, uniform positive proportion (B52); near-unit budgets, zero dilation surplus (B66).

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
- **Established:** blocks S9, S11; transfer closed; cutoff-uniform mass ⇔ RH; phase returns exist; a bounded phase return at each right zero gives AAL; tail fails at a zero; hull classified [L].
- **(a)** A22, A23.
- **(b)** Uniform positive mass (B72); returns on off-line-zero discs (B83, B89); decay (B82).

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
- **Established [L/K]:** full-family receivers; depth `<10⁶exp(−a/(1200log(|γ|+3)))` under sign, `|γ|≥110`; universal threshold; two-lobe bound; cut crystal; split-column receiver; local pair cost `≥−(16/9)δ²a⁴‖ψ‖²`; closed-form sharp-location height; isolated-zero entry on the column.
- **(a)** A9, A10, A14.
- **(b)** Complementary-window sign, remaining-depth control (B6, B7, B12); all-height column (B46).

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
- **Established [L/K]:** block S10; source cone; RR at every aperture; Bézout ⇔ RH; primitive `h¹` coercive for `a≤181/500`; tensor-uniform growth ⇔ purity on curves; Kloosterman curves pure by Stepanov; compactified moments with signed Tate correction; reciprocal tangent quadrics counted over every finite extension; every column Young projection nonnegative; endpoint Toeplitz minors of order `≤200` nonnegative; character positivity ⇔ RH; typical-height local sign at `A=δ log T/(64M²)`; each right zero is a Lefschetz ratio. Degree-one Selberg classification.
- **(a)** A28, A29, A32.
- **(b)** Source-energy sign (B40, B1); count or Rosati producer (B78, B87); arithmetic global trace (B85); mixed Young shapes (B86); genus, Serre duality, Epstein (B65); exceptional-height and unbounded-shape control in the modulated branch (B28).

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
| AIF | inner field, Poisson–Jensen, Szegő infimum, near-extremal rigidity, Carleson measure, log-mean at infinity, large-width bound, box budgets, crowd, curve chain, Abel mollifier of a curve, boundary quotient, dilation quotient, causal certificate, Szegő threshold, inverse scattering, forward map, potential past Born, restoring bound, Bohr profile decomposition, recurrence zero–one law, insertion cone, arithmetic Bernstein, critical-strip Bernstein, torus walls, echo columns, column calculus, correlated amplitudes, local onset field, certified passivity, questions of the field | A17 | B2, B57, B66, B82, B83 |
| AAD | producers, Mellin transform, uncertainty, peak law, half scale, Möbius producer, one-fifth rate under RH, parity-neutral rate, rate = Mertens scale, first-return bound, returns are prime returns, transport count, missing input, ledger blindness and ladder, parity ledger, Frobenius as stencil, curve stencil, extremal fake, profinite rigidity, Hecke action | A22, A30 | B15, B55, B89 |
| RAC | cut identity and kernel, unique fake, no uniform measure, carry, ledger hierarchy, Selberg reading, twin at every degree [S], every level seen [S], parity exponent, exchange law, generators, exact count, stencil FE defect, effective Kronecker, tail at a zero, limit map onto torus, maximal angle, Stieltjes sign, rotated relation classes [L/S] | none | B67, B91, B92, B93 |
| PTT | block S11 | A14 | B46, B90 |
| ASH | block S7 graph, Krein law, one clock, KMS, rank barrier, bulk log-mean, count law, integer probes, heights [L/S] | A27, A32 | B68, B87 |
| BHR | modular wave, metric, smoothness, echo train, causal symbol, ringdown, pulses, general data, cusp channel, metric of a pulse, sharp analytic boundary, near-arithmetic ladder exclusion | A26 | B71 |
| MMD | block S6 descent; quotient analysis to Green identity, coordinate expression, cusp barrier [L/S] | A33 | B94 |
| AE, KPA | polar calculus, Tate law, naive heights, convexity of counts, five currencies, torsion intersection, torsion energy, horizon torsion, Stepanov over ℤ, hyperelliptic calibration, height principles | none | B87, B88 |
| CSTW | canonical system, scalar flow, soft kick, Green corner, charts, AC traces, `L¹` drift, Lipschitz increments, sampling, mimics | A15, A16 | B2, B3 |
| CHT | margin law, pinning, datum, bands, bounded extremals for every weight, explicit sup bound, edge law | A6 | B16 |
| VHR | height 67 by Fejér budget; rungs: window, Li, Hausdorff, heat, Jensen, PF, theta | A1, A2 | none; decides no all-aperture statement |
| NGF | frequency, blow-up, gap laws, maximum principle, crystal and reality at critical scale, order bound | A19 | B24–B27, B47 |
| MZF | Selberg CLT, cameras, hyperbolic density, derivative law, rigidity, last scale, Möbius zero condensation | A18 | B57–B61 |
| FFP | `N_d` law, saddle region, stability dictionary, bulk blindness | A20 | B22, B23 |
| ADO | carrier repulsion; a.e. value; exceptional set dimension zero; FE-pair flatness | none | B77 |
| APR | necessary length, filters, prefix amplification, collar laws | A18 | B48 |
| AKLT, ASRP | Stepanov over `ℤ`, Nair lattice, Siegel and Liouville halves, stencil ceilings, Farkas producer at doubly exponential cost; AAL producers, tower detection | none | B48, B83 |
| APD, SEL | Hamburger rigidity, unit-density rigidity, residue gap, defect `1/6400` isolation, one-off models, Bohr obstruction, Selberg rigidity, degree-one classification | A31 | B80, B84 |
| PBAP, W3 | blind positivity, blind ζ dictionary, Carlson threshold, exact null blind test, sharp correlation tail | none | B18 |
| WVL | universal threshold, two-lobe, cut crystal, sampling at a free window | none | none beyond B1 |
| AHD/CACT | aliasing limits, Γ-liminf, dual floors, head reduction, polar capacity, far margin, certified ratio interval, tails, compactness, collar Gårding | A9–A13 | B6–B8 |
| CAF, TCS | two-atom, geometric chains, Euler product, explicit current core and tail, rank ten, section heights, growing-block Schur floor | A4, A5, A24 | B19–B21 |
| AK, Representation | column Young projections, curve phase characters, positive endpoint character, canonical compression, Kloosterman receivers and traces, torus critical points, reciprocal quadric trace | A28, A29 | B85, B86 |

## 6. Decisive wall per route

| Wall | Routes |
|---|---|
| Σ sign or budget | RW, EWU, OWU, ACT, CHMD, SZ, RN, ACS, AIP, SRT, SC, LI, TT (odd) |
| Σ full-space: collar is window sign through Gårding and compactness; prefix coupling | HF, SRT and AIP packet branches |
| Σ continuation at small time | ZCG, PTR, LA, GTA, XN, HCF, PA, TH |
| Π square-root precision and long moments | WL, MC, PBM, RB, JAS, CTF, FU, CFC, RP, TT (endpoint), WD, TG |
| Γ reflection and selection | PM, BAG, SEC, CDC, PCS |
| Missing source landing | APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF |
| Missing count, transversal to the above | ACS, HF, PM, RW through windows |
| Short-sum barrier, transversal to the above | every route at all heights |
