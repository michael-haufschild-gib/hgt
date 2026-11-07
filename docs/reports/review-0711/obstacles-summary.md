# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `1500534c93` plus the working tree of 2026-11-07.

Evidence: `[L]` Lean source; `[S]` Lean source unfinished, unintegrated or uncommitted; `[K]` Lean with transitive axiom audit; `[D]` deduction, not a Lean theorem; `[N]` numerical, uncertified; `[C]` classical, not formalized.

**38 live formulations; 9 candidates.** HJ→PA; BSH→CDC; FEL's BSY criterion→CTF. Candidates: APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF.

## 1. Big picture

### 1.1 RH has two halves
RH ⇔ ZAL ∧ AAL [L]. ZAL (finitely many zeros beyond each positive depth) implies quasi-RH [L]. AAL (finitely many zeros right of `½+h` forces none) is implied by RH and does not imply any zero-free region; `qRH ∨ AAL` is a theorem [D]. Under AAL, RH ⇔ ZAL ⇔ finite off-line support ⇔ `κ(K_ζ)<∞` ⇔ bounded non-real heat count ⇔ finite critical source energy ⇔ eventual Hadamard positivity ⇔ eventual central-gap budget [L]. Failure of AAL is one rigid object: `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})`, `T` a unique trigonometric polynomial with coefficients `−ord/(Θ+iμ)`, zero constant mode, sharp remainder ceiling, sign changes at bounded log gap, two-prime dilation annihilation of `ψ` [L].

### 1.2 The sign plane
On `PW_a`, Weil's form is diagonal in frequency [D]. Sign is a function on `(a,log X)` [L]: all heights to `a≈log log X−log 4` by size [L/D]; every shaped test on density-one heights to `a=δlog T/(64M²)`, with no zero information [L]; isolated zeros visible at `a≈(1/2d)log(4d log X)`, fixed depth hidden by a cut crystal to `(log T)/36`, sharp location at `λ>1` [L]; RH ⇔ `Ω≥0` everywhere [L]. Statements strictly below quasi-RH are averages over heights or tests, near-line densities, one-off exclusions and reductions [D].

### 1.3 The window sign is one scalar flow
The tower is a canonical system to contact with `H₁H₂=1` [L]. `L′=q−sinh 2L`; the actual chain obeys `|L(x)|≤artanh e^{−2(x−c)}+2osc_{[c,x]}Ψ` with no initial value and no `1/μ` [L]. So **RH ⇔ `Ψ=½log H₁` is locally bounded on `[0,∞)`** [D]. The margin ceiling forces `m≳e^{2a}`, above the Born bound: the potential is a nonlinear collective response [D].

### 1.4 The certificate is causal
A window is PD iff it has a positive-margin outer predictor [L]. RH is existence of outer predictors for every window [L]. Reflection data are free coordinates; the forward map from primes has an exact tangent; margins are concave in the weights [L].

### 1.5 At a fixed critical ratio the complete matrix is one window plus one low packet
At `R=c⁸/log N` fixed: Γ-liminf with weight `α_R>0` [L]; bounded form makes `L¹` limits strong [L]; collar Gårding at every `R` [L]; unrestricted Gårding false on deep atoms [L]. Every vector vanishing on the top logarithmic window `Ioc(N/S_R,N)`, `log S_R≤(1/8)log(R+1)+C₀`, has the floor `(κ₀/(2c⁷))‖x‖²`, because it lives at a lower ratio where the unconditional critical multiple applies; every nonpositive direction meets the window [S]. Gårding with an `L²` defect holds on the complement of the low packet at every ratio [S]. Physical tearing of prime quasimodes at the collar boundary fails with Schur ratio `4/13`; keeping conductors `≤N^θ` whole decouples the far band [S, statements only]. What remains at a ratio: the low packet's signed polar part against the top window, and the compactness assembly [D].

### 1.6 The inner mass has a second expression, and the dilation decides
On `Re s>½`, `E` has inner factor the Blaschke product of right zeros [L]. `exp(2I(1))=inf_Q∫|ζ exp Q|²dP₁` [L]. For one fixed `0<δ<½`, RH ⇔ zero dilation surplus `I(1)−I_δ(1)` ⇔ the critical-to-shifted Szegő budget ratio equals its outer value `((1−δ)/(δ|ζ(1+δ)|))²`; finite Euler prefixes are outer on `Re s≥½` and leave the surplus invariant [L]. Mollifiers are outer: they move the outer term and leave the inner mass, so the log-mean is invisible to mollification except through Jensen, which loses the variance [L/D].

### 1.7 The near-line wall is the dark range
Near-unit mollified moments need `log N≥log²T/(6K₀)` [L]: the length of an Euler mollifier over primes up to `≈c log²T` [D]. Prime phases become absolutely non-aligned exactly there: `Σ_{p<N}(1−cos t log p)/√p≥8/(10⁹L⁶ℓ⁴)` at `N≥48L²ℓ` [L]. Conditional tail laws stop at the Kronecker scale `y≈log T` (TAPO, 1.9). So the near-line wall (log-mean, clusters), the short-sum barrier (all-height sign, width axis) and the AAL input (1.10) sit on one range of primes, from `log T` to `exp((log T)^{2/3})`, where every conditioning resonator is longer than the height [D].

### 1.8 Production is the Mertens level on the half scale
A producer of rate `ε` gives `|M(n)|≤εn+12(w/m)√n+K`; floor `ε≥c/(√K(1+log K))`; rate `K^{−a}` ⇒ `Re ρ≤1−a`; all `a<½` ⇒ RH; none past `½` [L]. `|M(n)|≤Cn^{1−σ}` gives every `a<2σ/(3+2σ)`; RH gives `a<¼`; under RH the exponent lies in `[¼,½]` [L]. Compensated producers have smooth letters at cost `1/y` [L]. Zeros are the power-law kernel of the cut system; strip superpositions in the kernel are spanned by zeros; finite-energy kernel mass annihilation ⇒ RH [L]. The exact identity `Σ_{k≤x}F(⌊x/k⌋)=⌊√x⌋` pins `λ`; a power-saving Liouville bound is a zero-free strip [L]. Parity is a size statement.

### 1.9 The prime orbit at one height
Every window `exp(10y√(log y·log log y/δ))` enters every `δ`-box on primes `≤y` [L]; some box of radius `ρ` is missed below `log T≈π(y)log(π/(4ρ))` [S]. The first return `R(y,η)` lies between `exp(c(log y)^{1−η})` and `exp(C_ηy/log y)`; a weak return is a spike `|ζ(1+1/log N+it)|≍log N` [L]. Savings exclude returns: `R(y,η)>exp(√(y/(48log y)))` once `η≲y^{−9/2}`, the RH bracket at polynomial precision [L]. Proportional saving is the absence of early heavy returns [L]. Ceilings: rounded orbit; one word `≤1/(2(k+2))`; one binomial block `2/(k+1)`; transfer stops at Kronecker; the comb reaches first returns polynomial in the length [L]. The jet of `t log` moves along one curve, so the binomial ceiling binds one block and not a moving family [L/S]. The archimedean place is an approximate homomorphism with defect `|t|hh′/x²`; the depth aspect is exact [L].

### 1.10 Zeros are tail events
`ζ=E_y·ζM_y`; the head never vanishes on `Re s>0`, so the zeros of ζ are the zeros of the tail at every cut [L]. The head is frozen below resolution `1/log y` [L]. Along a bounded phase return the head returns and the tail carries the zero; every return at a right zero is tail-bad at every cut, with a tolerance independent of the cut, and such returns have density zero [L]. Conditional on head alignment, unique factorization makes the tail Gaussian through order `k` while `log max A+k log Z≪log T` [L]; past the Kronecker scale nothing is known. The random Euler model does not approximate functions with zeros [D], so a bounded return at a zero is an arithmetic event, not a typical one.

### 1.11 Certificates past the abscissa are tail-good conditions
In returning prime coordinates the archimedean coordinate dominates (Agler wall) [L]. Euler coordinates have `Σ_p|1−E_p(s)|<∞` iff `Re s>1`, and no summable perturbation crosses [L]. The head–tail certificate exists exactly where the tail is at most the head [L]. For `σ>1` the Ξ-current lifts to the torus with the pole as worst fibre point: a frozen certificate exists exactly above the size curve `−ζ′/ζ(σ)≤B(σ+it)` [L].

### 1.12 ζ is isolated
FE `L¹` defect `≤1/6400` forces the rational primes [L]. A positive integer-norm system with count error `o(log n)` is the rational primes; odd primes plus labels of norms `3,4` have count error `O(log²x)` and only ζ's zeros [L]. Exchanges of exponent `<σ` keep the zeros right of `σ` [L]. A bounded count error admits a new zero right of `½` with signed generators [L]; with nonnegative generators the question is open. Continuous Beurling one-offs exist [L].

### 1.13 Physics: exact and blind, separated by a count
The modular horizon is an exact solution with general `L²` data and one mode per zero; universal damping ⇔ RH [L]. On graphs every channel datum is a black hole with flux, unitarity, edge theorem and positive commuting Hecke families [L]. Integrality of the mode polynomial bounds the genus by the number of trivial zeros plus one [L]. A path throat has the functional equation only at genus `≤1`; an explicit branched graph has the genus-two functional equation for every `q` and a slow resonance for `q≥4` [L]. **Neither wave dynamics nor the functional equation forces universal damping.** The count law does: Manin's height on the twisted curve gives `K(1,1)=#E(𝔽_q)` and Hasse [L].

### 1.14 The count
A form homogeneous of degree two is nonnegative iff a function bounded below lies at bounded distance (Tate) [L]. RH ⇔ naive height on every window [L]. Fake: count, not quadratic. ℤ: `Q` on integer probes quadratic, not known to be a count. Curve: both [L]. Local data over ℤ: Λ is an intersection number of torsion orbits; the theta `h⁰` with exact RR; the sign is lost in the torsion self-energy `log(1/(1−r))Σx²` [L].

### 1.15 Hull
Haar-a.e. fibres and fair-coin-a.e. `±1` fibres extend zero-free to `Re s>½` with natural boundary `½` [L]. The Liouville point, where every coin is `−1`, extends iff RH [L]. RH ⇔ every nonzero limit of vertical translates is zero-free [L].

### 1.16 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| Markov, Perron, sign-gauge balance past `e^{−3/4}`, `log ρ` | refuted | [L] |
| Size-only payment of primes | ends before half-width `21/40` | [L] |
| Floor tower as aperture producer | stays below `0.3621` | [L] |
| Weighted Gårding on the whole horizon | false on deep atoms | [L] |
| Physical tearing at the collar boundary | Schur ratio `4/13` | [S] |
| Fixed theta heads; pointwise prime payment | no margin | [L] |
| Positive Laplace mixtures; all-base torus positivity of the theta amplitude | excluded | [L] |
| Fixed or limiting amplitude locking; divergent torus sums | adds nothing | [L] |
| Product certificates in Euler coordinates past `Re s=1` | cannot cross | [L] |
| Kernel payment in returning prime coordinates | dominated by Gamma | [L] |
| Lions dichotomy for far translates | fails on every bubble | [L] |
| Parabolic structure as selector of `t=0` | blind | [L] |
| Barriers, short detectors and weights | blind to purity | [L] |
| Moment data for the log-mean; outer mollifiers for the inner mass | blind | [L] |
| Diagonal moments, group closure, early orbit against a return | blind | [L] |
| Transfer of typical bounds past Kronecker | empty | [L] |
| Slow-return bounds on discs crossing `Re s=½` | the premise is RH | [L] |
| Schur, `C*`, KMS, reflection positivity as zero locators | blind | [L] |
| Wave dynamics, flux, unitarity, Hecke, functional equation at genus two as universal damping | fakes carry all | [L] |
| Integer stencils as a mechanism independent of Möbius | rate is the Mertens level | [L] |
| Polynomial ledgers as parity input at zeros | twin shares every leading pole | [L] |
| An independent parity source at power saving | is a strip | [L] |
| Bounded count error as a selector | new zero with signed generators | [L] |
| Extremal-angle position alone | has a polynomial model | [L] |
| Rotated relations with coefficients of growth `exp(C√\|w\|)` | trivial | [L] |
| Raw echo decay; near-arithmetic ladders; rational zero relocation | excluded | [L] |

## 2.1 Tasks that are just work

Difficulty is established only where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### Finite verification
| # | Task | Routes | Basis |
|---|---|---|---|
| A1 | Lean-certified `RHVerifiedThrough T` past 67 with zero location (Turing count), first `T≈10²–10³` | all rungs | `hardySEM` sign chains; Fejér budget is a bounded-height method |
| A2 | Numeric values of `windowHeight`, `xiMassHeight`, `heatGridHeight`, theta `D` | window routes, TH, LA, HCF | explicit definitions |
| A3 | Two-weight membership past `a₀`: odd unit window, `log 2`, `½log 5` | RW, OWU, EWU, ACT, SWC, HF | A1–A2 or rigorous Galerkin |
| A4 | Full-source theta rank 11 at every `0<a≤½` (unverified) | TH | core on `[1,5]`, Legendre kernel, height 67 |
| A5 | Lean certificate of the center-tail failure | TH | finite computation |
| A6 | Cone widths `𝒜(c)` past `c=0.66`; Lévy margins at `½log 3` | PBAP, ACS, RW, CHT | convex programs |
| A7 | Certificates on the nine anti-diagonals `{2,3,4,5,7,8,9,11,13}` | ACT | finite case analysis |
| A8 | Tate dimension-one sign from `log(9/2)` to `log(27/5)` | WTZ, CWS | one finite template decides |

### Critical curve
| # | Task | Routes | Basis |
|---|---|---|---|
| A9 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | HF, SRT, AIP, ACS, SC | proved limits |
| A10 | Compactness assembly: a negative complement sequence at ratio `R` has a strong nonzero limit with nonpositive limit pencil, a window of half-width `O(log R)` | HF, SRT, AIP, ACS | Σ115, Σ116, Σ126, Σ87 |
| A11 | Finish and integrate the CACT critical-ratio modules: `4/13` obstruction, conductor-adapted far decoupling, signed PNT pole bridge, window-localized and complement Gårding | HF, SRT, AIP, ACS | statements and partial proofs in source |
| A12 | Low-packet signed polar Schur payment against the top window at every ratio (unverified) | HF, AIP | polar capacity, low-packet diagonal, conductor-adapted split |
| A13 | Growing-period charges beyond gcd profiles (unverified) | AIP, HF | four channels below the eighth root |
| A14 | Frequency-integral identity; Gaussian moments in the typical-height sign | RW, ACS, SRT | moments of `D_N` |

### Flow, near-line, continuation, orbit
| # | Task | Routes | Basis |
|---|---|---|---|
| A15 | Lean statement RH ⇔ `Ψ` locally bounded | RW, SZ | restoring bound, contact criterion |
| A16 | Numerical `r,m,q` for `a≤1` [N] | RW | Galerkin |
| A17 | Selberg `O(T)` depth density in inner-field form | WD, CTF, RW, ZCG | second moment, twisted moment to `21/50` |
| A18 | Twisted second moments past `21/50`: to `½`, Conrey `4/7` [C] | WD, census | raises rate `2θ` |
| A19 | Heat horizon toward its method floor | ZCG | profile margin |
| A20 | Jensen rung toward the saddle scale (unverified) | LA, FFP | saddle identity |
| A21 | Census items; logarithmic two-point Chowla [C]; runs past five | MC, ACS, census | classical |
| A22 | VK bound `\|ζ(1+it)\|≪(log t)^{2/3+ε}` into the first-return lower bracket: `R≥exp(c(log y)^{3/2−o(1)})` at bounded harmonic defect [C] | BAG, PTT, TAPO | extreme-value dictionary |
| A23 | Resonator mean of `\|ζ(s+iτ)\|²` itself on Bohr sets below the Kronecker scale | BAG, ZCG, PTT | TAPO decoupling for Dirichlet tails |
| A24 | Certified scans of `S_S`; brackets for `S*(a,b)` | TH | column calculus |
| A34 | Integrate the [S] modules: mixing time from below, TAPO questions, extremal-fake atoms, cubic constant term on cubes | PTT, TAPO, AAD, MMD | source present |

### Theta, reflection, weights, production, descent
| # | Task | Routes | Basis |
|---|---|---|---|
| A25 | PM physical all-`n` Hecke moments beyond squarefree words (unverified) | PM, W1C | prime-word moments |
| A26 | Weyl law [C]; metric of `L²` horizon data; regularity at `r=1`; scalar sector | PM, BHR | cusp channel, metric of a pulse |
| A27 | Lean dictionary: local AdS₄ isometry, modular Lax–Phillips, Zagier–Sarnak [C], Kramers–Kronig | PM | graph versions in ASH |
| A28 | Reciprocal quadric traces = vanishing-cycle Frobenius traces (unverified) | ACS | quadric counts |
| A29 | Mixed Young projections at small rank (unverified) | ACS | column projections, PF₂₀₀ |
| A30 | Best stencil exponent under RH in `[¼,½]` (unverified) | WL, MC | quarter rate, half scale |
| A31 | Discrete Beurling one-off and its FE defect [C] | BAG, ACS | exchange law, near-count model |
| A32 | Manin at higher genus through Jacobians [C] (unverified in corpus); first case the genus-two graph of Γ118 | ACS, PM, AE | parallelogram law of heights, count law |
| A33 | Cubic quotient: residue `R≠0` at `4/3`, residue = cubic theta, Fourier coefficients = Gauss sums [C] | MC, MMD | resolvent, residue, constant term on cubes |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window | RH; fixed length sub | all sign routes |
| B2 | Bounded oscillation of `Ψ` on every bounded aperture interval | RH | RW, SZ, CHT |
| B3 | Variation of `r` free of `1/μ` | sub | RW |
| B4 | Two-sector certificates; outer predictor at every window; every actual echo in its Schur band | RH | sign routes |
| B5 | Kick admission at every stage | RH (induction) | RW, GWZ, WTZ, HF |
| B6 | Full-space sign eventually at every `K` | RH | HF, SRT, AIP |
| B7 | Positivity, not just Gårding, on conductors `Q₁..N^θ` above `R*` | sub | HF, AHD |
| B8 | Head thresholds for every `d` | RH | HF, AHD |
| B9 | No zero mode at any length | RH | HF, TG, SC, EHT |
| B10 | Top coprime stratum | RH | HF, ACS, ADT |
| B11 | Exact SOS on a two-prime lattice | RH | HF, SC, ACS |
| B12 | Index ceiling uniform in resolution | ≥qRH | CHMD, SRT, SC |
| B13 | Exclude finite nonzero off-line support | sub | whole programme |
| B14 | Window negativity exponent `<½`; any interior width value | ≥qRH | width axis |
| B15 | Past Vinogradov–Korobov | sub | every route |
| B16 | Decay law of `λ*(c)` | sub | CHT, RW |
| B17 | Signed ground-state structure past `log ρ` | method | EWU, OWU, RW, ACT |
| B18 | Prime-blind positivity on nonnegative blind mixtures | RH | RW, PBAP |
| B19 | Exact torus law for `S*(a,b)`; `{2,3}` cross-chain positivity | model | TH |
| B20 | Oscillation of the actual amplitude with the height | RH (all primes) | TH |
| B21 | All theta ranks at every `a` | RH | TH |
| B22 | Outer-root control of `R_d(Ξ)` | RH | LA |
| B23 | `N_d` bounded | ≥qRH | LA, FFP |
| B24 | Collision exclusion at small time, every height | RH | ZCG |
| B25 | Frequency `<1` at every collision | RH | ZCG |
| B26 | Arithmetic input distinguishing `Φ` among `Φe^{−τx²}` | method | ZCG, TH |
| B27 | Runs of `k` simple critical zeros, every `k` | sub | ZCG, census |
| B28 | Local Weil positivity at fixed `λ>0` on density-one heights | sub | RW, ZCG, WD, ACS |
| B29 | Cosine Laguerre sign below VK | RH | PTR |
| B30 | Heat grids at every degree | RH | HCF |
| B31 | Hausdorff signs below the quadratic boundary | RH | PA |
| B32 | Self-map discs covering every zero | RH | XN |
| B33 | Cofinally small quartic charge | RH | GTA |
| B34 | `C_t` at every fixed `0<t<½` | RH | TT |
| B35 | Unnormalized prime wave bound; complete odd sign | RH | CHMD |
| B36 | Joint-node exclusion | RH | RN |
| B37 | Bounded `A_N` | RH | SZ |
| B38 | Cubic trace norm `<1` | RH | TG |
| B39 | Damped coupling bound; sublinear tensor loss | RH | SC |
| B40 | Source-energy sign | RH | ACS |
| B41 | Source-work ceiling `≤2` | RH | HF |
| B42 | Complete-history floors | RH | FU, CFC, RP |
| B43 | Li budget or response floor | RH | LI |
| B44 | Retained-variance payment; one shift uniform in profile | RH | ACT, OWU, EWU |
| B45 | `C_σe^{2σr}` signed cost bound | RH | AIP |
| B46 | Proportional saving at length `(log X)^{2K}`, all heights; equivalently no early heavy return | sub (up to shielding) | RW, all rungs, PTT |
| B47 | Multiplicity `o(log X)` by an input not reducible to size | sub | ZCG |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B48 | Deciding input at square-root precision | RH | WL, MC, PBM, RB, JAS, CTF |
| B49 | Bounded endpoint energy; integer lag ceiling | RH | WL |
| B50 | Trivial-gauge half power; zero exclusion for `M_X` | RH | MC, WL |
| B51 | Moving power window control | RH | JAS |
| B52 | Vanishing rows, sparse defect, BSY sign, positive proportion | RH | CTF |
| B53 | Regularized partial-sum bound | RH | PBM |
| B54 | Eventual extremal inequality | RH | RB |
| B55 | Any polynomial stencil rate (qRH); rates `a↑½` (RH) | ≥qRH to RH | WL, MC |
| B56 | `Θ<1⇒Θ=½` | sub | whole programme |
| B57 | Depth density `o(T)`, equivalently log-mean of ζ on the line `→0` | sub | WD, census, MC, RW, ZCG, CTF, PM |
| B58 | `D_win` | sub | WD |
| B59 | Cluster wall | sub | WD, ZCG |
| B60 | Exponential moments of the Green potential at deep zeros | sub | WD, MC, ADO |
| B61 | A detector past the last scale | sub | WD |
| B62 | Cofinal long moment | RH | WD, CTF |
| B63 | Collision-charge bound | RH | WD |
| B64 | Signed pair information beyond bandwidth one | sub | census, ACS |
| B65 | Genus upper law; logarithmic Serre duality; first Epstein real zero | indep. to sub | ACS |
| B66 | Near-unit holomorphic budgets; zero dilation surplus | RH | CTF, WD, AIF |
| B67 | Parity at power saving | ≥qRH | WL, MC |
| B91 | Finite-energy cut-kernel vectors have mass zero | RH | RAC, CTF |
| B94 | Transfer of the cubic conversion to rational-integer Möbius | past VK at least | MC, MMD |
| B96 | Conditional law of the Euler tail at the Kronecker scale (head resonator as long as the height) | sub | BAG, TH, WD, TAPO |
| B97 | Constant-precision first return of every heavy subset: `log R(y,δ)≥y^c` for fixed `δ` | sub | PTT, TAPO, BAG |
| B98 | Positive-generator integer-norm systems: does count distance `O(x^θ)` forbid new zeros right of `θ`? | method | RAC, SPAL |
| B100 | A saving for `t log n` on moving families of blocks past Vinogradov's degree | sub | PTT, TAPO |

### Γ — selection and reflection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B68 | Independent `D_s≥0`, nonnegative Krein flux, integer-probe sign or all-zero dispersion bound | RH | PM |
| B69 | Positive physical or graph carrier | producer | PM, W1C, PTR |
| B70 | Lower bound for `V_p` from the carrier | sub | PM |
| B71 | Sharp decay of the smoothed resonant sum | RH | PM |
| B72 | Cutoff-uniform target mass | RH | BAG |
| B73 | Factorial-Fock bound at actual zeros | RH | SEC |
| B74 | Proof-erasure equality at actual zeros | RH | CDC |
| B75 | Reflection-odd class vanishes at actual zeros | RH | PCS |
| B76 | FE-pair reality with coverage | RH | ZCG, ADO |
| B77 | `0∉E` | indep. | ADO |
| B78 | Rosati positivity of the window reflection | RH | HF, ACS, CWS, PM |
| B79 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH | HF, ACS, SC, PM |
| B80 | FE twins with off-line zeros in the full class | sub | SEL |
| B81 | Candidate landings | producer | candidates |
| B82 | Inner-field decay `I(½+h+it)→0` | ≥qRH | BAG, AIF |
| B83 | AAL | sub | BAG, JAS, SC, whole programme |
| B84 | Smallest FE defect carrying a one-off | method | BAG, ACS |
| B85 | Arithmetic global trace on a family containing ζ | RH | ACS |
| B86 | Mixed Young projections; positive arithmetic representation | RH | ACS |
| B87 | Function on correspondences, nonnegative for an arithmetic reason, at bounded distance from `Q` | RH | ACS, HF, PM, RW, AE |
| B88 | Torsion self-energy paid by the archimedean reserve at finite `r` | RH | AE, HF |
| B89 | A bounded aligned return at each right zero on a right disc: a tail event cancelling the head at every cut | sub | BAG, ZCG |
| B92 | Arithmetic source of a rotated relation with coefficients of the size of `Q` | RH | ZCG, RAC |
| B93 | A contradiction using growth, log-concavity or arithmetic of `Q` beyond the extremal law | RH | ZCG, RAC |
| B95 | Abelian group with Hecke endomorphisms whose trace form is `Q` | producer | ACS, AE |

## 2.3 Frankenstein routes

**No assembly closes RH.** Each assembly below has at least one open input; the only one whose output is RH (F1) needs two. The others collapse independent problems into one.

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F1 | **Split skeleton.** Any AAL producer (bounded lags on a progression, twisted plateau sign, JAS level one or typical positivity, bounded towers, one bounded cone, shell positivity, finite-measure lag excursions, a bounded return at each right zero, slow aligned returns on right discs) with any ZAL receiver (inner-field decay, subtracted lag, heat coefficient `→0`, eventual Hadamard) | RH [L] | one AAL input (B83) and one ZAL input (≥qRH) | The only assembly whose output is RH |
| F2 | **Critical-ratio collapse.** CACT top-window non-escape and complement Gårding [S], collar Gårding, Γ-liminf, strong limits and tails [L], VHR window rung [L] | Complete matrix at ratio `R` from one verified window of length `(1/8)log R+O(1)`, up to the low packet [D] | A10, A11, A12 | HF, SRT, AIP packet branches stop being independent problems at every fixed ratio |
| F3 | CSTW traces and flow, AIF restoring bound | RH ⇔ `Ψ` locally bounded [D] | B2 | The tower is one local boundedness statement |
| F4 | ACS typical sign, AIF onset field, WVL visibility, ZCG sharp location, PTT isolated-zero entry | Negativity at aperture `a` is carried by exceptional heights [L/D] | B28, B46 | First sign past bounded aperture on typical heights |
| F5 | Eight-way log-mean equivalence, Selberg tail, Carleson measure, bulk log-mean, necessary length | Typical-height layer = depth density `o(T)`; any mollifier reaching it has at least the Euler length of the primes `≤c log²T` [L/D] | B57 | One target for RW, ZCG, WD, CTF, PM |
| F6 | `N(ρ)=exp(−ΣG)`, hyperbolic count, box budgets, long-mollifier residues | Deep zeros obey rate 2 or carry a large Green potential [L] | B60 | Density Hypothesis exponent near `½` |
| F7 | **One edge.** Pronic domination, flux, FFP drift, Euler coordinates, PM scattering, PTR at `h=½` | One theorem `Re s≥1` with many proofs [L/D] | B68, B70 | Marks what positivity reaches |
| F8 | TH column calculus, ZCG carrier horizon, FFP drift, PTT Ξ-current lift | Euler column minima against the Gamma base; a frozen certificate exactly above the size curve, with the pole as worst point [L] | B19, B20, B96 | Merges TH's wall with ZCG's |
| F9 | AAD rate law, Möbius and compensated producers, quarter rate, RAC kernel and parity identity | Stencils, parity and zero-free regions are one axis [L] | B15 | Closes production and parity as independent routes |
| F10 | One verified height, all rungs | All finite rungs [L] | nothing finite | Decides no all-rank statement |
| F11 | VK savings of all routes | One width axis [L] | B15 | They share one input |
| F12 | ¬AAL consequences: finite oscillation, dilation annihilation, jets with long-shift `m²`, unbounded returns at the top zero, returns tail-bad at every cut, `\|E_X\|≥X^κ` off a vanishing set, twisted FE, zero-free strip, qRH | A contradiction search on one rigid world [L/D] | any contradiction | Decides B83 if it succeeds |
| F13 | **Isolation.** APD defect `1/6400`, SPAL count distance, RAC parity identity and exchange law, SEL degree one | ζ is a singleton in three metrics [L] | B84, B98 | Every stable argument in these metrics is about ζ alone |
| F14 | Curve chain, Abel mollifier, near-extremal rigidity, Carleson measure, Szegő-ratio dilation | Over a curve: Castelnuovo ⇔ dilation bound ⇔ budgets reach 1. Over ℤ: every piece except the bound [L] | B66 | States what a Castelnuovo over ℤ must assert |
| F15 | **Count skeleton.** Integer probes, Tate law, Λ as log-resultant of torsion cycles, torsion energy, theta `h⁰`, Manin's height over `𝔽_q(T)` | Every ingredient of Manin's proof except one function at bounded distance from `Q` [L] | B87, B88 | States the missing object; output would be RH |
| F16 | Horizon, fakes, Hecke rigidity, Krein law, KMS strip, throat, trivial-zero law, genus-two graph | Physics reduced to one law, a count of channels; waves and the functional equation do not supply it [L] | B68, B87 | Closes wave dynamics, Hecke, KMS and reflection as sources of the sign |
| F17 | **Dark range.** PTT savings, TAPO precision law, heavy-return dictionary, RAC almost-every-height cancellation and first return above the length | The short-sum barrier is one first-return statement; the RH bracket is proved at polynomial precision [L] | B97 | The gap is precision `y^{−9/2}` against constant precision |
| F18 | **AAL tail form.** Transport on right discs, tail of a return, head resolution, conditional tail moments | AAL ⇐ at each right zero an arithmetic tail event cancelling the head at every cut, necessarily at the Kronecker scale [L/D] | B89, B96 | Replaces recurrence wording by one tail statement |
| F19 | **Certificate skeleton.** Agler wall, Euler coordinates, head–tail certificate, Ξ-current lift, Euler tail law | Arithmetic certificates exist exactly at tail-good heights, which have density one; returns to zeros sit at the others [L/D] | B96 at all heights | One tail law for TH certificates, PTT and BAG |

**Closest to the open core: F1, then F18 and F15.** F1 says what a two-route proof looks like. F18 says what the AAL half needs. F15 says what one object would close the sign side. F2, F9, F16, F17, F19 are collapses and sharpenings.

### The hard half: what a contradiction search on ¬AAL may assume (F12)

| In the world ¬AAL | Evidence |
|---|---|
| Zero-free strip `(β₁,Θ)` at all heights; `Θ<1`; finite top layer | [L] |
| `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})`, `T` unique, coefficients `−ord/(Θ+iμ)`, `η≤Θ−Θ₂` | [L] |
| Sign changes of `ψ(e^u)−e^u` at bounded log gap, amplitude `≥δe^{Θu}` | [L] |
| Two-prime dilation annihilation of `ψ` | [L] |
| `Φ(mℓ)` unbounded on every progression; `K_ζ` bounded on finitely many towers | [L] |
| `Λ`-moments at `ρ+1→−m`; diagonal `→0`; short shifts `→0`; long-shift correlation `→m²` | [L] |
| Every phase return unbounded on every domain joining a top zero to `Re s>1`; every return at a top zero tail-bad at every cut | [L] |
| Head returns of length `N` satisfy `N<1024(log τ)⁴(log log τ)²`; first nontrivial return of the primes `≤N` above `N` | [L] |
| Every right zero is a Lefschetz ratio; two primes determine it | [L] |

No contradiction comes from exact identities: every exact ledger is holomorphic off `s=1` [L]. Typical aligned shifts are tail-good in every world, so size on aligned shifts cannot provide one [L/D].

Which inputs carry a one-off:

| Input class | Status | Evidence |
|---|---|---|
| Positive continuous prime measure, `N(x)−ρx−C→0` | one off-line pair | [L] |
| Discrete primes approximating a continuous measure | zeros right of `½` kept | [C] |
| Integer norms, signed generators, bounded count error | new zeros on a vertical progression | [L] |
| Integer norms, positive generators, count error `O(log²x)` | exists, only ζ's zeros | [L] |
| Integer norms, positive generators, count error `o(log n)` | only the rational primes | [L] |
| Exchange of exponent `<σ` | zeros right of `σ` unchanged | [L] |
| Exact Euler product and exact FE; FE defect `≤1/6400` | only ζ | [L] |
| Euler product and FE with larger defect | open | B84 |

## 2.4 Wildly different routes

Each mechanism below avoids Σ payment, Π precision and Γ selection as stated. All are speculative, and none is promising on the corpus evidence. W6, W7, W9, W10 and W11 have no decisive Lean content.

### W5. Extremal angle
- **Idea.** Under ¬RH a zero of maximal angle of `Q(z²)=Ξ(z)` exists and `‖Q(t̄w₀)‖<‖Q(tw₀)‖` for `Im t>0`; RH ⇔ equality at zeros [L].
- **Status.** The inequality alone has a polynomial model with off-axis zeros [L]. Relations with coefficients of growth `exp(C√|w|)` are trivial [L].
- **Survivor.** The extremal law plus growth of `Q`, log-concavity of its coefficients or arithmetic (B93), or a rotated relation with coefficients of the size of `Q` (B92).
- **Risk.** Rotation in `−(s−½)²` has no arithmetic meaning.

### W6. Equivariant localization of the prime complex
- **Idea.** `M(N)` is minus the reduced Euler characteristic of the nerve of the star cover; the star of 2 is contractible, which is the matching `n↔2n`, and the complex is a wedge of spheres over odd squarefree `m∈(N/2,N]` [L]. Cancellation is between dimensions. Euler characteristics localize to fixed sets of torus actions.
- **Target.** A space homotopy equivalent to the nerve with an action whose fixed set has `O(N^{½+ε})` cells, or a filtration whose spectral sequence pairs classes of opposite parity down to that size. Either gives RH [L for RH ⇔ `|χ̃|=O(N^{½+δ})`].
- **First test.** Reproduce the cancellation of `M_C(n)` for a curve over `𝔽_q[T]` by a fixed-point formula on its prime complex.
- **Risk.** Dilations are semigroup maps that leave `[1,N]`; their boundary is where square-root cancellation is decided. `|χ̃|≥c√N` infinitely often [L], so the fixed set must have exactly square-root size.

### W7. Interlacing families
- **Idea.** Mixed characteristic polynomials of PSD matrices are real-rooted by real stability [C].
- **Target.** Exhibit `R_d(Ξ)` as an expected characteristic polynomial of an interlacing family built from first atoms, PD at every rank [L].
- **First test.** Degrees `3,4`.
- **Risk.** A Hilbert–Pólya realization in finite-dimensional dress.

### W9. Values of the form on integer probes
- **Idea.** `Q` on `ℤ^N` is a real quadratic form; under ¬RH it is indefinite for large `N`. Indefinite irrational forms in `≥3` variables have values dense near 0 (Margulis, Dani–Margulis) with effective rates (Lindenstrauss–Margulis–Mohammadi–Shah) [C].
- **Target.** A lower bound `|Q(a)|≥‖a‖^{−κ′}` on primitive probes of one irrational restriction per `N`, `κ′` below the effective exponent. No sign is asked for.
- **Risk.** Generic forms have large Diophantine exponent; a lower bound must use the arithmetic of the coefficients, whose only known source is positivity.

### W10. Heights on actual arithmetic varieties
- **Idea.** Arithmetic Hodge index is a theorem on arithmetic surfaces (Faltings–Hriljac) [C]. Gross–Zagier heights of Hecke translates of a Heegner point are a positive quadratic form with local terms `log p·(incidence)` and an archimedean Green term [C].
- **Target.** A limit of Arakelov forms on `X₀(N)` converging to `Q` on integer probes.
- **Risk.** Hecke curves on `X(1)×X(1)` are bidegree classes and the primitive part of `X₀(N)×X₀(N)` is cuspidal; resonances live on the Eisenstein sector, which does not meet it [L].

### W11. AdS₃ modular bootstrap
- **Idea.** In the spectral decomposition of 2d CFT torus partition functions over `SL₂(ℤ)\ℍ`, the Eisenstein overlap has poles at zeros of `ζ(2s)`; boundary unitarity and modular invariance constrain the spectral density [C, from memory, not in the corpus].
- **Target.** A family of unitary partition functions whose Eisenstein overlaps force cancellations at off-line zeros.
- **Risk.** Unitarity is a positivity of the spectral density; Narain-type averages realize Eisenstein series exactly, so the zeros enter as poles of coefficients, not as constraints. The corpus shows KMS, reflection and `C*` positivity are blind on every black hole [L].

### Formalized lines with walls of their own

| Line | Established [L] | Boundary [L] | Open core |
|---|---|---|---|
| W2 Representation | coherent central class functions ⇔ RH; column Young projections nonnegative; Toeplitz minors `≤200` | sorted occupancy and finite stabilizers fail | positive arithmetic representation (B86) |
| W3 Exact extremal | `Φ=Ξg` blind at every `log n` | `kb≤2` for full `Ξ^k` divisor | blind positivity (B18) |
| W4 Weight on a family | tensor growth ⇔ purity; Kloosterman purity by Stepanov | Golden has correct weights | arithmetic global trace (B85) |

### Tested and rejected forms

| Form | Reason | Evidence |
|---|---|---|
| Horocycle renormalization | horosphere indicators solve the wave equation | [L] |
| Lee–Yang lift on the prime torus | needs Gamma speed above total Euler speed | [D]/[L] |
| Stable Dirichlet polynomial with critical zeros | Herglotz carrier rigidity | [L] |
| Arithmetic capacity for the stencil rate | dual constraints are sawteeth | [L] |
| Agler decomposition in prime or Euler coordinates | Gamma coordinate dominates; Euler coordinates stop at `Re s=1` | [L] |
| Functional equation as damping law | genus-two graph has FE and a slow resonance | [L] |
| Extremal-angle inequality alone | polynomial model | [L] |
| Newton polygon separation of zeros | Taylor ratios `→1` | [D] |
| Comb or crystalline rigidity of the zero divisor | needs zero-side positivity | [D] |

## 2.5 Breakthrough question below RH and quasi-RH

| Test | Requirement |
|---|---|
| T1 | Implied by RH and not implying quasi-RH |
| T2 | Answered by proving or refuting a stated inequality |
| T3 | A named consequence can be written down |
| T4 | Not decided by a finite rung |
| T5 | False on a corpus fake |
| T6 | Names an input not refuted in Lean |
| T7 | Not a shape already answered without moving a wall |

### Primary: is the depth density `o(T)`? (B57)

**Question.** Does `Σ_{T<γ≤2T,β>½}m_ρ(β−½)=o(T)`? Equivalently `T⁻¹∫_T^{2T}log|ζ(½+it)|dt→0`, `I(½+x+it)→0`, density-zero damping deficits on the horizon, and for each fixed `u>0` the proportion of zeros of depth `>u/log T` tends to zero [L/D].

- **Why it matters.** It is `100%` critical-scale clustering, the Euler-mollified log-mean, the outer law, the dyadic depth, the Hecke and theta readings, the Abel inner mass at infinity and the Bode integral at universal damping [L]. It closes the typical-height layer for RW, ZCG, WD, CTF and PM at once, and gives local Weil positivity at fixed `λ` on density-one heights (B28) [D].
- **Where it stands.** Empty mollifier: `O(T log log T)` [L]. Selberg: `O(T)` [C]. Critical-line proportion `→1` implies it [L]. Under RH: `0`.
- **The tool gap.** Mollifiers are outer: on `Re s≥½` an Euler prefix changes only the outer term and leaves the inner mass and the dilation surplus invariant [L]. So mollification reaches the log-mean only through Jensen, which loses the variance of `log|ζM|`, and moment data do not determine the log-mean [L]. A near-unit moment needs length `exp(c log²T)` [L], the Euler length of the primes up to `c log²T`, where prime phases first become absolutely non-aligned [L/D]. The needed input is therefore a control of the zeros within `u/log T` of the line that is not a second moment: for instance a variance bound `T⁻¹∫(log|ζM|−mean)²→0` for some non-Euler `M`, or a fixed-scale density estimate.
- **Tests.** T1–T4, T7 pass. T5: false on `ζ(s)(1−cp₀^{−s})`, `c>√p₀`, where the mean tends to `log(c/√p₀)>0` [L]. T6: prime field, long-mollifier ceiling, tail moment, Carleson embedding, dilation identity.
- **Limit.** Sparse off-line zeros survive; rare heights untouched.

### Alternatives

| Question | Why it matters | Tests | Limit |
|---|---|---|---|
| Can ζ have exactly finitely many off-line zeros? (B13) | Every finite-support receiver (`N_d` bounded, `κ<∞`, bounded heat count, finite critical energy) becomes an RH receiver [L] | all pass; T5 continuous one-offs | subsumed by AAL (section 3) |
| Conditional law of the Euler tail at the Kronecker scale (B96) | Lights the dark range for BAG, TH certificates, WD; its off-diagonal is a count of shifted smooth × prime products [D] | T1 fails in the letter: the off-diagonal is a Hardy–Littlewood problem not implied by RH [D]; T2–T7 pass | parity: as hard as pair correlation past `α=1` [C] |
| Constant-precision first return of heavy subsets (B97) | Implies B46 and the all-height sign past size | T1: RH gives it [D]; strength qRH up to shielding [D] | see 2.6 |
| Signed pair surplus beyond bandwidth one (B64) | Census to `3/4` at `4/3`; same off-diagonal as B96 [D] | T1 fails in the letter | parity |
| Positive-generator integer systems: count distance `O(x^θ)` forbids new zeros right of `θ`? (B98) | Makes integrality a quantitative selector; between the proved `o(log)` rigidity and the `O(log²)` fake | T1 vacuous; T5 the signed bounded-count model | says nothing about ζ's own zeros |
| Low packet against the top window at every ratio (A12) | Completes F2: the complete matrix at every ratio is one window rung | T5 fails by design | architectural |
| Multiplicity `o(log X)` by a non-size input (B47) | First all-height input not reducible to size | T1: RH gives `≪log X/log log X` [C] | bounds collisions only |

## 2.6 If positivity, Weil positivity and spectral methods are excluded

"Spectral" is read as spectral theory of operators: eigenvalue problems, spectral decompositions, Hilbert–Pólya realizations, Kuznetsov and trace formulas. Fourier analysis and exponential sums are kept.

**What survives** [L]:

| Class | Receivers | Sign-free input proved |
|---|---|---|
| Production | integrality halves, stencils, one-sided counts as `ψ(x)` bounds, `\|M(n)\|≤εn+12(w/m)√n+K` | exact integrality; VK-scale rate; compensated producers; Stepanov over `𝔽_q` |
| Orbit | column bounds, isolated-zero entry, first return | absolute non-alignment `L⁻⁶`; boxes at square-root cost; precision law; heavy-return dictionary; moving jet; comb |
| Transport | recurrence, target mass, AAL | transport on right discs; returns are prime returns; tail of a return |
| Cancellation | `M(x)`, one-point and one-window forms, long moments, Báez–Duarte, cut kernel | VK; length and last-scale laws; almost-every-height square-root cancellation |
| Rigidity | exact FE, exact count, count distance, parity identity | three isolation metrics; exchange law |
| Dominance | finite carriers real above a horizon; Gamma speed on rotations | Gamma speed beats finite Euler speed |
| Identification | cameras, sharp location | sign-free readout under isolation |

All of Σ falls, with PM's Krein branch, TH certificates, W2, W3, the index routes and the count door.

**The natural doors under this exclusion.** Stepanov over ℤ is a stencil, whose rate is the Mertens level [L]. Every exact ledger is holomorphic off `s=1` [L]. Parity at power saving is a strip, and the exact identity already pins `λ` [L]. Rotated identities below the size of `Q` are trivial [L]. What remains sign-free and unclosed is the orbit of the prime phases at one height, past the Kronecker scale.

**The question.** *Does every heavy subset of the primes up to `y` need a height `exp(y^c)` to return at fixed precision?* Precisely: is there `c>0` such that for every `δ∈(0,1)` and every small `κ>0`, for large `y` no set `H` of primes `≤y` missing at most a fraction `κ` of the weight `Σp^{−½}` satisfies `1−cos(t log p)≤δ` for all `p∈H` at a height `1≤t≤exp(y^c)`?

**Why it opens the path.**
- Pure Diophantine statement about `(t log p)_{p≤y}`: no form, no sign, no operator.
- By the heavy-return dictionary it is the proportional saving B46 at length `y=(log t)^{1/c}` [L], hence the all-height sign past the size curve, the width axis up to crystal shielding and the exclusion of isolated zeros of depth `>c/2` through the column bound [L/D].
- Its precision-weak form is a theorem: at precision `≍y^{−9/2}` the first return already exceeds `exp(√(y/(48log y)))`, the RH bracket [L]. The question is the passage from polynomial to constant precision.
- Its ceilings are known: words certify precision `≤1/(2(k+2))`, one binomial block saves `≤2/(k+1)`, transfer stops at Kronecker [L]. The unused structure is identified: the jet of `t log` moves along one curve and exotic blocks are rare [L/S]; returns lay smooth integers on a multiplicative approximate group [L]; the archimedean place is an approximate homomorphism with quadratic defect [L].

**Tests.** T1: RH implies proportional saving for `K>1` [D]. T2–T4, T7 pass. T5: false on impure columns [L]. T6: precision law, comb, moving jet. Strength: quasi-RH up to shielding [D].

**Limit.** Speaks about large heights only; a one-off at a fixed height is invisible to it. The first theorem past absolute savings is strip-strength up to shielding.

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved.** The modular horizon is an exact locally AdS₄ solution with general `L²` data, a covariant metric and one ringdown mode per zero; universal damping ⇔ RH [L]. On graphs universal damping is not a law of wave dynamics: fakes have flux, unitarity, causality and positive commuting Hecke families [L]. Reflection is supplied, not derived: a path throat has the functional equation only at genus `≤1`, and a branched graph with the genus-two functional equation still has a slow resonance for `q≥4` [L]. Integrality of the mode polynomial bounds the genus by the trivial zeros plus one [L]. Hecke on the Eisenstein sector is modular time [L]; KMS gives `¼` its meaning and no force [L]. What separates true curves from fakes is the count law: on a true elliptic curve the count is Manin's height and Hasse follows [L].

**The law, read physically [D].** `K(φ+ψ)+K(φ−ψ)=2K(φ)+2K(ψ)` for the number of open channels of a probe is a Born rule. A fake's channel count `|𝒬|` is a real count that fails it because some probes reverse orientation. Over ℤ, `Q` obeys the rule and has no count. The genus-two graph shows that the count cannot be local: the functional equation needs branching at the cusp, and the parallelogram law must come from a global group law, as Manin's comes from the addition law of the curve.

**The question.** *Is there a bulk-defined count of open channels for integer sources on the modular horizon, obeying the parallelogram law and at bounded distance from `Q(a)`?* Candidates: degrees of line bundles on a compactified cusp quotient attached to the source; numbers of echoes above threshold weighted by the integers `ϕ(c)`; nodal counts of the response on the horizon.

**Why it opens the path.**
- It is the physics form of the Tate statement: any such observable gives RH [L].
- It names the law as a Born rule for channels, not as a dynamical law, which is what the fakes force.
- It has a finite first rung: on the genus-two graph, decide whether a parallelogram channel count exists exactly for `q≤3`, where the modes are damped, and fails for `q≥4` (Γ118). That is a computation on an explicit 11-vertex graph.
- A refutation in the natural candidates ends the physical reading of the sign, leaving the horizon as a language.

**Tests.** A structure question, RH-strength in full. T2 on one window of length `≤3/5`, where a naive height is known to exist [L]. T5: fakes fail [L]. T6: count law, heights, Tate law, trivial-zero law.

**Second physical question.** A flux law `d/dτ Q=−𝓕` with `𝓕` a manifest boundary square. On every black hole `𝓕=(1−1/q)𝒬`, a boundary square exactly under universal damping [L]; completing the square uses the mode frequency `√(q−t²/4)`, so the question is why every mode oscillates [D].

**Limit.** The geometry is locally pure AdS, so gravity imposes nothing; function-field models have finite rank; a compact probe excites infinitely many modes over ℤ [L].

## 2.8a If RH is a problem of topology or geometry: question

**What is proved.** RR at every aperture on the source cone; Bézout ⇔ RH; primitive `h¹` coercive for `a≤181/500`; bidegree counts see no primitive class [L]. Tate law and five currencies [L]. Manin's height on the twisted curve gives Hasse [L]. Λ is an intersection number of torsion orbits [L]. `M(N)` is minus the reduced Euler characteristic of the nerve of the prime stars; RH ⇔ `|χ̃|=O(N^{½+δ})` [L].

**Geometric question.** *Is there a height machine over ℤ: an abelian group `G` with commuting Hecke endomorphisms `T_n`, `T_n′T_n=n`, and a function `h=Σ_vλ_v` on `ℤ[T_n]`, each `λ_v` a local size at `v` and `h` bounded below by a product formula, at bounded distance from `Q`?*
- It is the exact specification of the missing object (B87, B95); it gives RH by the Tate law [L].
- It explains why sign is not payment: nonnegativity comes from the product formula, so local terms of either sign are expected [D].
- Rungs: Manin at genus two through a Jacobian (A32), tested on the genus-two graph; then one window of length `≤3/5` built from torsion energy and theta count without using `Q≥0`.
- T5: Golden has no naive height, the complex fake has kernel counts and no height [L].

**Topological question.** *Does the Mertens Euler characteristic localize: is there a space homotopy equivalent to the nerve of the prime stars with a group action whose fixed set has `O(N^{½+ε})` cells?*
- The first cancellation is already topological: the star of 2 is contractible, which is the matching `n↔2n`, and leaves a wedge of spheres over odd squarefree `m∈(N/2,N]` [L]. The question asks for the remaining cancellation by a fixed-point formula.
- `|χ̃|≥c√N` infinitely often [L], so the fixed set must have exactly square-root size: the action has to see the boundary of `[1,N]` under dilation.
- First rung: the prime complex of `𝔽_q[T]`, where the Euler characteristic is computable and the fixed-point formula must reproduce it.

**Limit.** Natural Frobenius candidates are refuted in their classes [L]. Heights over number fields give central-value signs, not off-line zeros [D]. Dilations are not actions on `[1,N]`.

## 2.8b Does closing RH need a new field?

No theorem says so. The evidence is structural: every available tool stops for a proved reason.

| Tool | Why it stops |
|---|---|
| Size estimates | before half-width `21/40`; exact across independent reflectors; all heights only to `a≈log log X` |
| Markov, Perron | frustration past `log ρ` |
| Type I/II sieve data | parity-blind |
| Linear floor identities | blind to every zero; rate is the Mertens level |
| Polynomial ledgers | exact ones holomorphic off `s=1` |
| Barriers, short detectors | blind to purity; last-scale floor |
| Mollifiers | outer: cannot touch the inner mass; near-unit moments need length `exp(c log²T)` |
| Words and polynomial phases | one block only |
| Diagonal moments, group closure | rounded orbit returns |
| Conditional laws on Bohr sets | stop at the Kronecker scale |
| Transfer to rare heights | stops at Kronecker |
| Certificates in prime or Euler coordinates | Gamma dominates; Euler coordinates stop at `Re s=1`; past it, tail-good only |
| Concentration-compactness | Gårding fails on deep atoms; physical tearing fails at `4/13` |
| Finite computation | finite rungs decide nothing |
| Tensor amplification, integrality | carry RH unchanged; amplify, produce nothing |
| Parabolic monotonicity | blind to `t=0` |
| Unitarity, Schur, `C*`, KMS, flux, Hecke, the functional equation | reach only the edge; hold on fakes; FE does not force damping at genus two |

**What is built, and where it stops.**

| Field | Object | Stops at |
|---|---|---|
| Arithmetic inner functions | half-plane, causal order, inner mass | one-dimensional; no sign |
| Prime torus theory | `(t,ω_t)` at finite time; hull | absolute savings; ceilings |
| Tail arithmetic of the prime orbit | first return, Euler tail, conditional law | the Kronecker scale |
| Sum-product arithmetic of the logarithm | products of translates, collision cells, count distance | rigidity only; no saving |
| Rigid arithmetic of cuts | cut system, ledgers, kernel, exchange | parity is the strip |
| Arithmetic scattering holography | waves on quotients with trees | wave dynamics and FE not the law; count missing over ℤ |
| Effective geometry (AE, ACS, LST) | polar surfaces, naive heights | producer of a count |

**The proposal: arithmetic of the Kronecker scale.** Every sub-RH wall sits on one range: the near-line mollifier needs Euler length of the primes up to `c log²T`; prime phases become non-aligned there; the conditional law of the Euler tail is known only while the head resonator is shorter than the height; a bounded return at a zero is an atypical tail event there [L/D]. At that scale conditioning needs Dirichlet polynomials longer than the height, whose mean values carry off-diagonal main terms: counts of shifted products `mn−m′n′=h` with `m` smooth and `n` prime [D]. This is the setting of Montgomery's `F(α)` for `α>1` and of the trans-threshold census [C/L].

| Aspect | Content |
|---|---|
| Objects | Dirichlet polynomials of length `≥` height; head–tail decompositions `ζ=E_y·ζM_y`; resonators on smooth integers; conditional measures on Bohr sets at the first-return scale; shifted smooth × prime product sets; long mollifiers; first returns of heavy subsets |
| Language | Kronecker scale, dark range, conditional tail, tail-good height, heavy return, near-collision, off-diagonal main term, resolution `1/log y` |
| Mechanisms | unique-factorization decoupling below the scale; shifted convolution beyond it; Hardy–Littlewood main terms; large deviations conditional on the head; outer versus inner factor |
| Tools to build | mean-value theorem for smooth × rough polynomials of length `T^{1+κ}`; the off-diagonal main term as a singular series; lower bounds for conditional large deviations; twisted moments with resonators longer than the height; constant-precision first return |
| Calibration | rank-one flows (no dark range); function fields, where the head is periodic; conditional Gaussianity below the scale [L]; Montgomery's theorem for `α<1` [C]; continuous Beurling systems |

**Criteria it must meet.** Reduce to periodic flow at rank one. Recover the proved conditional laws below the scale. Read parity through binary main terms, since Type I/II data are blind [L]. Fail on Beurling one-offs through the integer structure of shifted products. Treat ζ and its twin alike where the primes are the same.

**Questions it must answer.** What is the off-diagonal of `∫|R|²|B|²` at length `≍T`, and does it carry a main term? Does that main term see zeros, as `F(α)` does? Is a bounded return at a right zero a conditional large deviation, and of what probability? What is `R(y,δ)` at constant precision? Does any mollifier of length `exp(c log²T)` reach near-unit moments?

**Limits.** Binary problems at the Kronecker scale are parity problems: a theorem there is at least as hard as pair correlation past `α=1` [C]. Exceptional zeros are the one known parity-breaking input (Heath-Brown's Siegel-zero twin-prime argument [C]); an off-line zero at fixed `Θ<1` changes prime densities only by `x^{Θ−1}`, too little for that mechanism [D].

## 2.9 If positivity, Weil positivity and spectral methods are excluded: which field?

Inner-function theory, holography's flux and the count door lose their core. Under the exclusion the Kronecker-scale field of 2.8b loses its spectral tools (Kuznetsov, shifted-convolution spectral theory) and must count near-collisions combinatorially.

**What it would be about.** *Fine-scale multiplicative energy:* how many quadruples of structured integers satisfy `|log(mn)−log(m′n′)|<1/T`, for `m` smooth and `n` rough or prime, at the Kronecker scale, and how the two structures of `n↦t log n` (smooth in `n`, additive under multiplication) are incompatible at one height. It extends sum-product arithmetic of the logarithm from rigidity to counting.

| Aspect | Content |
|---|---|
| Objects | product sets of smooth and rough integers; near-collisions at relative scale `1/T`; level sets `L(t,δ)` as multiplicative approximate groups; moving jets of `t log`; carries `⌊kx⌋−k⌊x⌋`; integer-norm Beurling systems with count distance |
| Language | near-collision, fine multiplicative energy, comb, moving jet, carry, count distance, isolation |
| Mechanisms | sum-product growth; incidence bounds for hyperbolas `xy=c`; integer gap `\|log(a/b)\|≥1/max(a,b)`; products of translates recovering tuples; carries as averages of translations; Stepanov's polynomial method |
| Tools to build | incidence bounds for near-collisions of smooth × prime products at scale `1/T`; a polynomial method at the archimedean place; savings for moving block families past Vinogradov's degree; a contradiction engine on the finite oscillation of ¬AAL using carries |
| Test cases | Weil for curves through Stepanov [L for split hyperelliptic]; depth aspect, where `q`-differencing is exact [L]; continuous Beurling systems, which have no carries [L]; the odd-primes-plus-{3,4} system at count distance `log²` [L] |

**Criteria it must meet.** No quadratic form with a sign, no operator spectrum. Proves Hasse–Weil over `𝔽_q` in the same language. Separates rational primes from continuous and discrete Beurling systems, through count-distance rigidity at `o(log)` [L]. Any parity output at power saving is a zero-free strip [L]. Not blind to zero modes: avoids functionals linear in `ψ` read through floors [L].

**Questions it must answer.** What replaces Frobenius, given that over ℤ a dilation of the count is an average of translations [L]? Is the fine multiplicative energy of smooth × prime products at scale `1/T` at its random value? Do moving block families of `t log n` save past Vinogradov's degree? Is the minimal count distance of a positive-generator system with a new zero at least `x^θ`?

**Limits.** Nothing in the corpus shows the exclusion is forced: over `𝔽_q` Hodge index, Stepanov and Manin all prove the theorem. No source produces parity at power saving other than a strip [L]. No named mechanism above VK.

## 2.10 If RH is a physical phenomenon in AdS with a modular horizon: which field?

Arithmetic scattering holography exists. Its positive results are the graph black hole, the Krein law, the one clock, the bulk log-mean, Manin's count on true curves and the trivial-zero law. Its negative results are that wave dynamics, unitarity, Hecke, KMS and the functional equation do not carry universal damping. What it leaves is a count.

**What it would be about.** *Counting holography:* quantum numbers of boundary sources on arithmetic quotients of AdS. A probe is a source. Its count is a boundary degeneracy: an integer on the graph, a sum of local degrees over ℤ. The count is global, built from a group law on the quotient, and each place contributes a nonnegative number of open channels after a product formula.

| Aspect | Content |
|---|---|
| Objects | modular horizon and graph black holes; probes `y−xπ` and integer vectors `a`; channels; echo integers `ϕ(c)`; Krein square; state map; twisted curve and its Jacobian; trivial modes; radial Pöschl–Teller tower; general `L²` data and metric |
| Language | probe, channel, Born rule for counts, orientation of a probe, elliptic state map, flux, damping deficit, partner law, trivial mode, silent branch, modular clock |
| Mechanisms | exact d'Alembert and contour expansion; flux balance; Hecke as time shift; Krein translation invariance; parallelogram from an addition law; integrality of mode polynomials; poles of a height as channels above a place |
| Tools to build | a bulk construction of `K` on integer probes; a dictionary between heights on Jacobians and solutions on branched graphs; a boundary operator algebra whose GNS form on sources is Krein; Lyapunov functionals from counts |
| Calibration | true curves, where Manin gives the count [L]; fakes, where the count is not quadratic [L]; throats, where FE fails past genus one [L]; the genus-two graph, damped exactly for `q≤3` [L]; non-congruence groups [C] |

**Criteria it must meet.** Recover Hasse from channels at all probes [L] and Hasse–Weil at every genus (A32). Fail on fakes through the count, not through dynamics [L]. Supply the partner law globally, since local wave systems do not know it [L]. Fail for non-arithmetic groups. Explain the blindness of KMS, Schur and `C*` positivity [L]. Be consistent with raw echo spikes and GUE statistics [L; C].

**Questions it must answer.** What is `K` on an integer source of the modular horizon? What is the physical origin of the parallelogram law on a branched graph? Does integrality of the mode data, which bounds genus by trivial modes, force a count when trivial modes are infinite in number, as over ℤ? Why is the form a boundary square exactly when modes oscillate? Does Hecke at a second place constrain a count, given that it does not constrain flux?

**Limits.** Every proved physical statement is a restatement, an edge theorem or a statement that a physical law is absent. The geometry is locally pure AdS. The programme has produced no estimate outside the Eisenstein calculus. It is a language until a count exists.

## 2.11 If RH is a problem of topology or geometry: which field?

**What it would be about.** *Height and homotopy theory of arithmetic counts.* Counts are Euler characteristics (the nerve of the prime stars has `χ̃=−M(N)`), signs are signatures (Hodge index on polar surfaces), and nonnegativity comes from heights with a product formula. The field asks for the three structures over ℤ that a variety supplies over `𝔽_q`: a group law (for the parallelogram), a fixed-point formula (for cancellation in Euler characteristics), and a polarization (for the sign).

| Aspect | Content |
|---|---|
| Objects | integer probes and window correspondences; `Q`; local heights `λ_v` with `deg p=log p`; torsion cycles and resultants; Arakelov bundles `⊕𝒪(½log m)`; theta `h⁰`; the prime complex and the nerve of prime stars; polar surfaces; Hecke similitudes |
| Language | height, local height, naive height, Tate limit, product formula, self-energy, Euler characteristic, localization, signature, primitive class |
| Mechanisms | product formula as nonnegativity; Tate limit from an approximate parallelogram; height principles; discrete Morse matchings (the contractible star of 2); fixed-point localization; Hecke equivariance |
| Tools to build | a function on correspondences with arithmetic nonnegativity; regularization of torsion self-energy at finite `r`; an approximate parallelogram for a log-count; a fixed-point formula for dilation semigroups on `[1,N]` with boundary; the signature of a quadratic refinement of the nerve |
| Test cases | elliptic curves by Manin [L]; hyperelliptic curves through Stepanov [L]; Golden, no height [L]; complex fake [L]; genus-two graph [L]; prime complex of `𝔽_q[T]` |

**Criteria it must meet.** Recover Hasse–Weil for curves from heights with no form as input. Be false on Golden and on shifted data with nonnegative Tate coefficients [L]. Read the test beyond its two degrees [L]. Be infinite-rank in the limit, with no finite-dimensional realization on a window [L]. Not define its height through `Q`. See torsion through `ℤ⊂ℝ`, which no Beurling system carries [L]. Reproduce `|χ̃|≥c√N` infinitely often [L].

**Questions it must answer.** What is the group, or what replaces it? What is the addition law behind a quasi-parallelogram over ℤ? Where does the torsion self-energy go? Which action localizes the Euler characteristic of the nerve to a fixed set of square-root size? Why does the prime complex have Betti numbers `≈cN` and Euler characteristic of expected size `√N`? Do Hecke correspondences generate the ample cone?

**Limits.** Finite-rank carriers, separable assemblies, connected links and natural Frobenius candidates are refuted in their classes [L]. Actual modular surfaces see only the cuspidal part [D]. Over `𝔽_q` these structures are consequences of having a variety; over ℤ none of them is known to exist.

## 3. The one question

**Can ζ have a finite top layer?** Equivalently: is the asymptotic abscissa law true, so that finitely many zeros right of `½+h` forces none? Equivalently [L]: can `ψ(x)−x` be one finite oscillation `x^ΘT(log x)+O(x^{Θ−η})` with `Θ>½`?

The expected answer is no finite top layer: AAL holds. Then RH ⇔ ZAL, and every receiver that delivers finite off-line support delivers RH.

### Why this one

Prefix decoupling at a fixed critical ratio is answered in two directions: physical tearing fails at Schur ratio `4/13`, conductor-adapted splitting decouples, and nonpositive directions cannot escape the top logarithmic window [S]. What remains of it is the low packet against one window (A12) and assembly (A10, A11): work, not a wall. Of the walls left, AAL is the only one that is strictly below quasi-RH, decides RH together with a quasi-RH half, is false on a corpus fake, and has a rigid negative world.

| Kind | Best form | Why it ranks lower | Evidence |
|---|---|---|---|
| Critical ratio | low packet against the top window (A12) | architectural; moves no sign wall | [S]; [D] |
| 100% near the line | depth density `o(T)` (B57) | mollifiers are outer; near-unit moments need length `exp(c log²T)` | [L]; [D] |
| Rate near `½` | cluster wall (B59) | Ingham's slope | [D]; [C] |
| All-height sign | constant-precision first return (B97), proportional saving (B46) | quasi-RH up to shielding | [L]; [D] |
| Kronecker-scale law | conditional tail (B96), pair surplus past bandwidth one (B64) | binary prime problems; not implied by RH | [D]; [C] |
| Production, parity | stencil rate (B55), parity (B67) | rate is the Mertens level; parity at power saving is a strip | [L] |
| Count | function at bounded distance from `Q` (B87) | RH-strength | [L] |
| **One-offs** | **AAL (B83)** | **sub-qRH, decisive with ZAL, false on fakes, rigid negative world** | **[L]** |

### What an answer does

| Answer | Effect |
|---|---|
| **AAL proved** | RH ⇔ ZAL [L]. Finite off-line support, `κ(K_ζ)<∞`, bounded non-real heat count, finite critical source energy, eventual Hadamard positivity and the eventual central-gap budget each become RH [L]. |
| **AAL proved** | The obstacle "finite or shallow exceptions remain" loses its finite half in LA (`N_d` bounded ⇒ RH), HF, AKLT and CWS (finite index ⇒ RH), ZCG (bounded heat count ⇒ RH), FFP, WD and RW large-height receivers. |
| **AAL proved** | F1 becomes the architecture: one ZAL producer closes RH. The one-off countermodels of APD, RAC and the continuous Beurling systems stop being models of ζ. |
| **AAL proved** | B13 is answered: ζ has no finitely many off-line zeros. |
| **A proof that bounded returns at right zeros never exist, in any world** | BAG, AAD and TAPO stop being AAL producers; AAL moves to the lag side or the integer side below. |

### What is proved around it

| Channel | Status | Module |
|---|---|---|
| Split and collapse | RH ⇔ ZAL ∧ AAL; eight statements coincide under AAL | `ZetaWeakRecurrenceLadderCollapse`, `AsymptoticAbscissaLawProducers` [L] |
| Rigid negative world | finite oscillation, unique `T`, quantized coefficients, sign changes, two-prime dilation annihilation, rightmost-zero jets with long-shift `m²` | `TheOneOffsAreFiniteOscillationsOfThePrimeError`, `PrimeErrorFiniteOscillationRigidityAndSignChanges`, `MultiplicativeDilationAnnihilationOfPrimeError`, `FiniteExceptionalLayersForcePersistentLowJets` [L] |
| Lag producer | `∀a>0`: `Φ(L)≤Me^{aL}` off a set of finite measure ⇒ AAL | `WeilLagFunctionFiniteMeasureExcursion` [L] |
| Typical JAS producer | typical positivity of JAS phase aggregates at every level ⇒ AAL | `JointAncestryTypicalAsymptoticAbscissa` [L] |
| Transport | bounded translates on a domain joining ρ to `Re s>1` copy the zero; slow aligned returns on right discs ⇒ AAL; crossing discs force `\|ζ\|≥cτ^b` | `TheMissingInputOfTransport`, `TheSlowReturnBoundLivesRightOfTheLine` [L] |
| Tail | zeros of ζ = zeros of `ζM_y`; returns at right zeros tail-bad at every cut, density zero; head frozen below `1/log y` | `TheTailOfAReturnCarriesTheZero`, `TheHeadIsFrozenAtItsResolution` [L] |
| Conditional law | Gaussian tail moments and large deviations below the Kronecker scale | `TheTailDecouplesFromTheHead`, `TheConditionalMomentsOfTheTail` [L] |
| Head length | head returns `N<1024(log τ)⁴(log log τ)²`; first nontrivial return above `N` | `TheSlowReturnBoundLivesRightOfTheLine`, `TheFirstReturnIsAboveTheLength` [L] |
| Fakes | continuous Beurling one-offs; bounded count with a new zero (signed generators) | `BeurlingOverRegularIntegersOffLineZeros`, `ABoundedCountWithANewZero` [L] |
| Isolation | FE defect, count distance, exact parity identity | `SmallIntegrableDefectsForceTheRationalPrimes`, `CountDistanceRigidity`, `TheExactIdentityDeterminesTheParity` [L] |

### The three forms of the missing input

1. **Tail form (B89, B96).** At each right zero, a sequence of aligned heights at which the Euler tail cancels the head on a disc about the zero, at every cut. Such heights are tail-bad and have density zero [L]; the random Euler model never approximates a function with a zero [D]. So the input is an arithmetic event at the Kronecker scale, where conditioning needs a resonator as long as the height and the off-diagonal is a count of shifted smooth × prime products [D].
2. **Lag form (Γ69).** For every `a>0`, a one-sided bound `Φ(L)≤M_ae^{aL}` for all `L` outside a set of finite measure. In prime terms, `ψ(x)−x` bounded below by `−M_ax^{½+a}` off a set of `x` of finite logarithmic measure [L/D]. Under ¬AAL the trigonometric polynomial `T` is negative on a set of positive density, so the bound fails on a set of infinite measure [D].
3. **Integer form (Γ81).** Under ¬AAL a two-prime dilation polynomial annihilates `ψ=log lcm(1,…,⌊x⌋)` to `κx+O(x^{Θ−η})`. A contradiction would have to come from integrality and carries of `lcm` at the dilated points; exact ledgers are blind [L], so only inexact integer information can serve.

### First steps

1. Write the off-diagonal of `∫_T^{2T}|R|²|ζM_y|²` at resonator length `≍T` as a sum over shifted smooth × prime products, identify its main term, and compute what the finite oscillation of ¬AAL contributes to it.
2. Decide whether the lag form is weaker than a zero-free strip: does a zero at `β` force `Φ(L)>e^{(β−½−ε)L}` on a set of infinite measure only for attained tops, as the Landau argument gives, or for every `β`?
3. Test the integer form on the rigid object: compute the dilation-annihilated `ψ` for an explicit top layer and compare with the carries of `lcm(1,…,⌊x/p^aq^b⌋)`.
4. Run the typical JAS producer at one level `σ` on explicit prime sets and resolutions, as a finite test of how typical positivity fails under a finite top.

### Validation

| Test | Verdict |
|---|---|
| T1 | Pass. RH implies AAL; AAL implies no zero-free region [D]. |
| T2 | Pass. A stated existence or inequality in each form. |
| T3 | Pass. The effects table. |
| T4 | Pass. Not decided by any finite rung: it concerns all heights. |
| T5 | Pass. False on continuous Beurling one-offs [L]. |
| T6 | Pass. Each form names an unrefuted input: an arithmetic tail event, a one-sided lag bound off finite measure, an integer contradiction. |
| T7 | Pass. Moves Γ68, Γ69, Γ106, Γ115, B13. |

### Limits

- AAL leaves ZAL, which is at least quasi-RH; the closing argument still needs it.
- The tail form sits at the Kronecker scale, the same dark range as B46 and B57; no tool there is known.
- The lag form may be as hard as a strip; that is step 2.
- Exact identities cannot help [L]; the integer form must use inexact information.
