# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `c7d60e30c6` plus the working tree of 2026-11-06.

Evidence: `[L]` Lean source; `[S]` Lean source marked unfinished or unintegrated in the frontier map, or uncommitted; `[K]` Lean with transitive axiom audit; `[D]` deduction, not a Lean theorem; `[N]` numerical, uncertified; `[C]` classical, not formalized.

**38 live formulations; 9 candidates.** HJ→PA; BSH→CDC; FEL's BSY criterion→CTF. Candidates: APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF.

## 1. Big picture

### 1.1 RH has two halves
RH ⇔ ZAL ∧ AAL [L]. ZAL says finitely many zeros lie beyond each positive depth and implies quasi-RH [L]. AAL says finitely many zeros right of `½+h` forces none. Under AAL, RH ⇔ ZAL ⇔ finite off-line support ⇔ `κ(K_ζ)<∞` ⇔ bounded nonreal heat count ⇔ finite critical source energy ⇔ eventual Hadamard positivity ⇔ eventual central-gap budget [L]. Failure of AAL is a rigid world: finite top and bottom layers at `Re s=β*,1−β*`, zero-free vertical strips across all heights, all other zeros in `[1−β₁,β₁]` [L]. Height-local receivers read ZAL. Sparse arithmetic samples and twisted energies read AAL, through the exclusion of an attained top [L].

### 1.2 Window sign is one scalar flow, and contact is local
The tower is a canonical system to contact with `H₁H₂=1`, no singular part and no atom at aperture 0 [L]. With `L=artanh r`, `q=Ψ′`: `L′=q−sinh 2L`, `(log K)′=2 cosh 2L` [L]. Contact is `∫dx/(1−r²)=∞`, and `q∈L¹` up to contact gives RH [L]. The restoring force forgets the past: `|L(x)|≤artanh e^{−2(x−c)}+∫_c^x|q|`, independent of `L(c)` [S]. So contact is decided locally, and verified initial data does not help past a bounded distance [D]. Prime thresholds are soft: `(Ψ(x)−Ψ(a))log(1/(x−a))→Λ(n)/√n` from the right at `2a=log n`, no left kick [L]. A kick of this modulus is integrable, so no single prime aperture produces contact. In the Born model, with reflectors at `½log n`, kicks `|k_n|≤A log n/√n`, any phases and any initial state, `1−r_n²≥e^{−10A}/(2√n log n)`: kicks of arithmetic size cannot cause contact by size, and a collapse needs coherence over `≳√n` reflectors [S]. The proved margin ceiling forces `m≳e^{2a}` on average [L], above the Born bound `m≲ae^{a}`, so the actual `q` is a nonlinear response and not the Born medium [D].

### 1.3 The certificate is causal, and reflection data are free coordinates
A window is PD iff it has a predictor with positive margin whose polynomial has no zero in the closed disc, for any sign pattern [S]. Sign changes of the predictor are free, so frustration blocks positive gauges and not certificates. Doob gauges die on a triangle [S]. Outer predictors make `A∓zA*` vanish only on the circle: functional equation plus passivity gives reality in every window [S]. RH is existence of outer predictors for every window, lattice and nonzero test [S]. Every sequence in `(−1,1)` is the reflection data of exactly one passive even sequence; an echo train is passive iff each echo lies in its Schur band; the first reflector of a short bump reads `Λ(n₀)` explicitly, and the forward map from prime data is causal and injective [S]. So passivity puts no constraint beyond the size of each coordinate. The wall is the forward map from primes to reflectors.

### 1.4 Why the datum is critical, and what compactness can mean
Slack `s` adds an absolutely continuous density to the spectral measure. `s>0` is Szegő's regime with square-summable reflectors; `s<0` has a finite negative witness once margins tend to 0; RH places every lattice at `s=0` with `Σγ²=∞` [S]. Zero slack is singularity of the measure. Under RH each lattice of Spec ℤ is a purely deterministic stationary process in Kolmogorov's sense [D]. For every nonzero test `c_φ(t)↛0`, so far-translate energy never decouples; under RH far dipoles of unit mass have arbitrarily small energy [S]. The bottom of the form is reached at translation infinity by bubbles that interfere and never separate. Any compactness theorem has the Bohr compactification as its space at infinity.

### 1.5 The inner mass has a second expression
On `Re s>½`, `E=(s−1)ζ/s` has inner factor exactly the Blaschke product of right zeros, with no singular part [S]. `I(w)=Σm_ρG(w,ρ)≥0`, and `RH⇔I(w)=0` at one point [S]. Second expression: `exp(2I(1))=inf_Q∫|ζ exp Q(φ₁)|²dP₁`, each budget an upper bound, the infimum exact [S]. Over `𝔽_q`, inner mass is `Σlog⁺|β_i|`, and budgets reach 1 ⇔ unitarity ⇔ Castelnuovo ⇔ reflectors in `(−1,1)` [S]. So the second expression exists. What is missing over ℤ is a construction of near-extremal mollifiers, the role Castelnuovo plays over a curve.

### 1.6 Finite rungs are theorems; they decide nothing
RH through height 67 is proved with no zero located, by a Fejér budget on `Re s=1` [L]. It gives PF₂₀₀ at the centre, PF₂₀₀ of the endpoint exterior sequence, slices `|t|≤133/2`, Li `n≤314` and rank ten [L]. Window, Hausdorff, heat, Jensen and theta rungs have explicit heights [L]. The budget's left side is below a fixed constant while `½log(γ/2π)` grows, so it is a bounded-height method [D]. The floor tower stays below `0.3621` [L].

### 1.7 One Vinogradov–Korobov layer
AIP cost, SZ source, TT band, MC Hilbert form, WL energy, PTR depth and TH collar carry one VK saving and stop there [L]. Interior values of any width parameter are zero-free strips. No route has a mechanism past VK.

### 1.8 The typical-height layer
Heights with `Λ_Xlog X>κ` have measure `≤T^{θ(κ)}` [L]. At critical scale, all zeros are real and the crystal law holds outside `δT` heights for `τ≳κ(δ)` [L]. Isolated simple zero: `d−7η≤Λ_Xlog(X/2π)≤d+17η` [L]. Complex saddles replace size bounds at power level [L]. A central inequality at all heights is stronger than RH; heating the kernel preserves all parabolic laws [L].

### 1.9 The near-line layer is one number
`T⁻¹∫_T^{2T}log|ζ(½+it)|dt→0` is equivalent to the Euler-mollified log-mean, the linear-mollifier outer law, the dyadic horizontal moment, `100%` critical-scale clustering and three defect readings [L]. Selberg's tail moment disposes of large depth, so only small `κ` matters [L]. Moments do not determine the log-mean, and Jensen is sharp for moment data [L]. With polynomial mollifiers, Jensen loses the variance of `log|ζM|`, a positive constant [D]. Isolated zeros obey rate 2 without separation [L]. At simple right zeros `N(ρ)=exp(−Σ_{a≠ρ}m_aG(ρ,a))` [S], so negative moments of `ζ′` are exponential moments of the Green potential.

### 1.10 Long moments are rigid
Slope is exactly `2wθ`. Cofinal bound at any fixed `K` self-improves to `K=6`. RH reads at one point, in one bounded window, or as a positive proportion of every length-2 window with `|E_X|≤X^ε` [L]. Möbius polynomial zeros accumulate at every point of `Re s=Θ`, and eventual zero-freeness right of `½` is RH [L].

### 1.11 Positivity lives inside one prime at a time
`S(a,b)=Σ_Nτ_b(N)A(log N)=Π_pT_pA` with Eisenstein coefficients [L]. `A` is not a positive Laplace mixture [L]. Torus-positive amplitudes with left growth `κ<½` are exactly the exponentially convex ones; the critical exponent `½` is the density of the primes, and `A` grows at that exact rate [S]. Phase locking at a fixed amplitude equals torus positivity [S]. On a Kronecker family the infimum of a sum of columns is the sum of the infima, and an echo train `1−2Σc_icos(bℓ_i)` is passive iff `2Σ|c_i|≤1`; on commensurable reflectors the Fejér train is passive with `2Σ|c_k|=N` [S]. So over `𝔽_q` all reflectors share one column with unbounded room, and over ℤ each prime is its own column and only size crosses columns. `current=2|Ξ|²Re ξ′/ξ(½+a+ib)` [L], and `Re ξ′/ξ=½log(b/2π)+Re ζ′/ζ+O(1/b)`. So the base that pays the columns is the Gamma term, which grows with `b` [D]. Torus failure at `P≈19–47` [N] is the same inequality as the ZCG carrier horizon [D].

### 1.12 PM reaches the edge by unitarity and reads depth by Hecke
Boundary norm gives `|ζ(1+it)|≥1/(6250t³log²t)`, `t≥2·10⁷`, with no Euler-product inequality [L]. `V_p(ρ,Y)=2(1−p^{Reρ−1})`, ordinate-free, and one-sided bound at one `p,Y` ⇔ RH [L]. All-`n` Hecke moments are a Poisson mixture positive at every `Re u<0`, on-line or off-line, so `C*`-positivity is blind [L]. Schur positivity is blind to zero position [L]. `S(s)=φ(s)(s−1)/s` is a Blaschke product over `(1+ρ)/2`, resonant states are its model-space kernels, and Hecke acts on them by the Toeplitz symbol `p^{u}+p^{−u}` [D]. RH is `Re s=¾` for its zeros [L].

### 1.13 Production is exact at integrality and has no rate
`ψ(n+1)=max log(1/∫₀¹P)` over integer `P` of degree `≤n`; Stepanov over ℤ loses nothing at the integrality step [L]. Siegel and Liouville halves are each RH at square-root scale; the integrality exponent is `Θ` [L]. Sup-norm control is capped at `e^{−0.87n}` [L]. Balanced multivariate stencils reach slope `1+ε`, giving `ψ≤(1+ε)x+C_εlog²x`, by finite Farkas duality with non-explicit `C_ε` [L]. The rate `ε(K)` carries the prime number theorem exponents [D]. Over `𝔽_q` the chain producer → count → unitarity is complete for split hyperelliptic curves and Kloosterman data [L].

### 1.14 Recurrence is closed at typical base, open at a zero
Returns transport zeros [L]. Pair recurrence holds at density-`(1−δ)` base heights with relatively dense shifts [L]. At a zero, returns are `≤T^θ` [L]. Continuous Beurling systems with positive prime and integer densities have exactly one off-line pair and no recurrence [L]. Exact FE forces rational primes, and a prime-count mismatch at `N` costs FE defect `>1/(400N²)` [L]. Dirichlet polynomials and periodic data recur, so their inner degree is `0` or `∞` [S]. A finite nontrivial inner factor exists as soon as no arithmetic is required [S].

### 1.15 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| Markov, Perron, sign-gauge balance past `e^{−3/4}`, `log ρ` | refuted | [L] |
| Size-only payment of primes | ends before half-width `21/40` | [L] |
| Floor tower as aperture producer | stays below `0.3621` | [L] |
| Fixed theta heads; pointwise prime payment | no margin; fails at `log 6` | [L] |
| Positive Laplace mixtures for the theta amplitude | excluded | [L] |
| Fixed-amplitude locking; torus-uniform theta positivity | locking adds nothing [S]; fails at `P≈19–47` [N] | [S]/[N] |
| Cancellation across independent reflectors at a fixed base | none: size is exact | [S] |
| Lions dichotomy for far translates | fails on every bubble | [S] |
| Parabolic structure as selector of `t=0` | blind | [L] |
| Central inequality as an RH-level target | stronger than RH | [L] |
| Barriers on prime sums; short detectors and weights | blind to purity; stop at the last scale | [L] |
| Moment data for the log-mean; coefficient norms for long moments | blind | [L] |
| Schur, `C*`-Hecke and raw-norm positivity as zero locators | blind | [L] |
| Full-determinant arithmetic reflection | none | [L] |
| Positive primes plus smooth integer count as AAL | false for continuous models | [L] |
| Invariant tensor weights; principal-branch endpoint signs; pure compression | false for Golden or RH-level | [L] |
| Finite-template, separable, finite-realization, tensor, integrality shortcuts | stated classes refuted | [L] |

## 2.1 Tasks that are just work

Difficulty is established only where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### Finite verification
| # | Task | Routes | Basis |
|---|---|---|---|
| A1 | Lean-certified `RHVerifiedThrough T` past 67 with actual zero location, first `T≈10²–10³` | all rungs | `hardySEM` sign chains exist; Turing count missing; Fejér budget is a bounded-height method |
| A2 | Numeric values of `windowHeight`, `xiMassHeight`, `heatGridHeight`, theta `D`; reduce them toward `log(T₀/2π)≳2Σ_{n≤e^{2a+s}}Λ(n)/√n` | window routes, TH, LA, HCF | explicit definitions in Lean |
| A3 | Two-weight membership past `a₀`: odd unit window, `log 2`, `½log 5` | RW, OWU, EWU, ACT, SWC, HF | A1–A2, or rigorous Galerkin |
| A4 | Full-source theta rank 11 at every `0<a≤½` (unverified) | TH | core on `[1,5]`, Legendre kernel, height 67; or A1 through `41+6(N+2)log(N+2)` |
| A5 | Lean certificate of the center-tail failure | TH | finite computation |
| A6 | Cone widths `𝒜(c)` past `c=0.66`; Lévy sector margins at `½log 3` | PBAP, ACS, RW, CHT | convex programs |
| A7 | Certificates on the nine anti-diagonals `{2,3,4,5,7,8,9,11,13}` | ACT | finite case analysis |
| A8 | Tate dimension-one sign from `log(9/2)` to `log(27/5)` | WTZ, CWS | one finite template decides every `A<log(27/5)` |

### Effectivization and assembly
| # | Task | Routes | Basis |
|---|---|---|---|
| A9 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | HF, SRT, AIP, ACS, SC | proved limits |
| A10 | Explicit `R₀` from the far reserve; certified ratio interval; receiving complement inside it (unverified) | HF, AIP, SRT | `exists_fixed_ratio_far_reserve_retaining_archForm` |
| A11 | Literal channel norms with growing periods and offsets (unverified) | AIP | `LiteralChannelScaleDomination` |
| A12 | Mixed Schur debit; first-prime, coarse, polar costs | AIP, CHMD | prefix residual identity |
| A13 | One Γ-limit lower bound along `L¹`-convergent atomic sequences | HF, AIP | mixed mass, physical dual floor, prime-shift infinitesimality, exponential tails |
| A14 | Star horizons, gcd strata, Künneth mixed jets | HF, ACS, WL, SC | effectivization |

### Canonical flow and integration
| # | Task | Routes | Basis |
|---|---|---|---|
| A15 | `Ψ∈AC_loc` before contact and `L¹` convergence `q_y→q` on compact precontact intervals, constants allowed to depend on `μ` (unverified) | RW, SZ | Green corner, soft kick, uniform charts |
| A16 | Numerical `r,m,q` for `a≤1` [N] | RW | Galerkin |
| A17 | Weight-specific specialization of the bounded window solutions | CHT, RW | edge law |
| A18 | Integrate modules marked [S]: AIF, AKLT index modules, HKT index modules | RW, TH, WD, CTF, BAG, SC | sources exist |

### Continuation, near-line, production
| # | Task | Routes | Basis |
|---|---|---|---|
| A19 | Heat horizon from `6600/9991` toward its method floor | ZCG | profile margin `(c−w)²−4cE(w)≥m`, best exponent pair |
| A20 | Explicit `θ(κ)` in the power-saving exceptional set | ZCG | level `E≍η³` |
| A21 | Local Weil positivity at small `λ` on positive-density heights (unverified) | RW, ZCG, WD | zero keeping, Lorentz tail, visibility law; `exists_shortWindow_positiveProportion_heights_weilPositive` is the envelope case |
| A22 | Twisted second moments past `21/50`: to `½`, Conrey `4/7` [C] | WD, census | raises rate `2θ` |
| A23 | Logarithmic two-point Chowla [C] | MC | Tao |
| A24 | Census items; Voronoi; Zwegers [C] | census, ACS | classical |
| A25 | Selberg-class degree-one classification [C] | ACS, SEL | degree gap and conductor pole in Lean |
| A26 | Jensen rung toward saddle scale; constants in `300√(d log d)` (unverified) | LA, FFP | saddle identity |
| A27 | Certified scans of `S_S`; brackets for `S*(a,b)` from the size floor, the log-concavity wall and columns add | TH | torus walls |
| A28 | PM physical mixed Hecke moments (unverified); Lean dictionary for the Blaschke product `S` | PM, W1C | one-step isometry; Maass–Selberg |
| A29 | Reciprocal transverse specialization, extension trace, exceptional-divisor identification (unverified) | ACS, W4 | transverse form and quadric counts in Lean |
| A30 | Mixed Young projections at small rank (unverified) | ACS, W2 | column projections and PF₂₀₀ in Lean |
| A31 | Lean form of `¬AAL ⇔` finite oscillation of `ψ(x)−x` | BAG, WL | spectral gap, truncated explicit formula |
| A32 | Constructive form of the balanced stencils with explicit `C_ε` at the VK rate (unverified) | WL, MC | Farkas proof, Möbius residue test |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window | RH; fixed length sub | all sign routes |
| B2 | `q∈L¹` up to every finite contact | RH | RW, SZ, CHT |
| B3 | Bounded variation of `r` on bounded intervals, free of `1/μ` | sub | RW |
| B4 | Two-sector certificates; outer predictor at every window; every actual echo in its Schur band | RH | sign routes |
| B5 | Kick admission at every stage | RH as induction | RW, GWZ, WTZ, HF |
| B6 | Profile decomposition at one critical ratio above `R₀`, with the Bohr compactification as the space at infinity | sub | HF, SRT, AIP, ACS |
| B7 | Full-space sign eventually at every `K` | RH | HF, SRT, AIP |
| B8 | Growing families, moving frequencies, conductors past `(log N)^{13/32}` | sub | HF, AHD |
| B9 | Head thresholds for every `d` | RH | HF, AHD |
| B10 | No zero mode at any length | RH | HF, TG, SC, EHT |
| B11 | Top coprime stratum | RH | HF, ACS, ADT |
| B12 | Exact SOS on a two-prime lattice | RH | HF, SC, ACS |
| B13 | Index ceiling uniform in resolution | ≥qRH | CHMD, SRT, SC |
| B14 | Exclude finite nonzero off-line support | sub | whole programme |
| B15 | Window negativity exponent `<½`; any interior width value | ≥qRH | width axis |
| B16 | Past Vinogradov–Korobov: floor `α>3/5` | sub | every route |
| B17 | Decay law of `λ*(c)` | sub | CHT, RW |
| B18 | Signed ground-state structure past `log ρ` | method | EWU, OWU, RW, ACT |
| B19 | Prime-blind positivity on nonnegative blind mixtures | RH | RW, PBAP |
| B21 | Torus law for `S*(a,b)`; cross-chain positivity on small prime sets, first `{2,3}` | model | TH |
| B22 | A height-dependent prime-insertion invariant containing the actual amplitude | RH (all primes) | TH |
| B23 | All ranks at every `a` | RH | TH |
| B24 | Outer-root control of `R_d(Ξ)` | RH | LA |
| B25 | `N_d` bounded | ≥qRH | LA, FFP |
| B26 | Collision exclusion at small time, every height | RH | ZCG |
| B27 | Frequency `<1` at every putative collision | RH | ZCG |
| B28 | Arithmetic input distinguishing `Φ` among `Φe^{−τx²}` | method | ZCG, TH |
| B29 | Runs of `k` simple critical zeros, every `k` | sub | ZCG, census |
| B30 | Local Weil positivity at fixed `λ>0` on density-one heights | sub | RW, ZCG, WD |
| B31 | Cosine Laguerre sign below the VK boundary | RH | PTR |
| B32 | Heat grids at every degree; chirp bound or mean | RH | HCF |
| B33 | Hausdorff signs below the quadratic boundary; exterior diagonal; `TV(n)/qⁿ→0` | RH | PA |
| B34 | Covering every zero by a self-map disc | RH | XN |
| B35 | Cofinally small quartic charge | RH | GTA |
| B36 | `C_t` at every fixed `0<t<½` | RH | TT |
| B37 | Bound on the unnormalized prime wave; complete odd sign | RH | CHMD |
| B38 | Joint-node exclusion | RH | RN |
| B39 | Bounded `A_N`; rectangular Ward lower bound | RH | SZ |
| B40 | Cubic trace norm `<1`; bounded Gaussian oscillation | RH | TG |
| B41 | Damped coupling bound; sublinear tensor loss | RH | SC |
| B42 | Source-energy sign at every radius | RH | ACS |
| B43 | Source-work ceiling `≤2` | RH | HF |
| B44 | Complete-history floors | RH | FU, CFC, RP |
| B45 | Li budget or response floor | RH | LI |
| B46 | Retained-variance payment; one shift uniform in profile | RH | ACT, OWU, EWU |
| B47 | `C_σe^{2σr}` signed cost bound | RH | AIP |
| B83 | All-height frequency input not reducible to size: multiplicity `o(log X)` | sub | ZCG |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B48 | Deciding input at square-root precision: parity-breaking, pure, unbounded aperture and length | RH | WL, MC, PBM, RB, JAS, CTF |
| B49 | Bounded endpoint energy; integer lag ceiling; first cyclotomic mode | RH | WL |
| B50 | Trivial-gauge half power; long-modulus tail; zero exclusion for `M_X` | RH | MC, WL |
| B51 | Moving power window control | RH | JAS |
| B52 | Vanishing rows, sparse defect, BSY sign, positive proportion | RH | CTF |
| B53 | Regularized partial-sum bound | RH | PBM |
| B54 | Eventual extremal inequality | RH | RB |
| B55 | Explicit parity-selective producer with rate past VK; polynomial rate gives a one-sided strip [D] | sub to ≥qRH | WL, MC |
| B56 | `Θ<1⇒Θ=½` | sub | whole programme |
| B57 | Log-mean of ζ on the line `→0`, equivalently `100%` critical-scale clustering | sub | WD, census, MC, RW, ZCG |
| B58 | `D_win` | sub | WD |
| B59 | Cluster wall: Density Hypothesis rate for every near-line zero | sub | WD, ZCG |
| B60 | Exponential moments of the Green potential at deep zeros | sub | WD, MC, ADO |
| B61 | A detector past the last scale | sub | WD |
| B62 | Cofinal long moment; one-window bound; pronic tail | RH | WD, CTF |
| B63 | Collision-charge bound | RH | WD |
| B64 | Signed pair information beyond bandwidth one | sub | census, ACS |
| B65 | Genus upper law; logarithmic Serre duality; first Epstein real zero | indep. to sub | ACS |
| B80 | Explicit near-extremal mollifiers | RH | CTF, WD, AIF |

### Γ — selection and reflection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B66 | Independent `D_s≥0`, Krein positivity or all-zero dispersion bound | RH | PM |
| B67 | Independent positive physical or graph carrier | producer | PM, W1C, PTR |
| B68 | Zero-free curve inside the strip from the carrier; lower bound for `V_p` | sub | PM |
| B69 | Cutoff-uniform target mass | RH | BAG |
| B70 | Factorial-Fock bound at actual zeros | RH | SEC |
| B71 | Proof-erasure equality at actual zeros | RH | CDC |
| B72 | Reflection-odd class vanishes at actual zeros | RH | PCS |
| B73 | FE-pair reality with coverage | RH | ZCG, ADO |
| B74 | `0∉E` | indep. | ADO |
| B75 | Rosati positivity of the window reflection | RH | HF, ACS, CWS, PM |
| B76 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH | HF, ACS, SC, PM |
| B77 | FE twins with off-line zeros in the full class | sub | SEL |
| B78 | Candidate landings: APF full divisor, EGC height fibre, EWJ endpoint, FEL history, IRK projective lift, MSC Sonin sign, RFHM orientation, W1C producer, WBF arithmetic stream | producer | candidates |
| B79 | Inner-field decay `I(½+h+it)→0` | ≥qRH | BAG, AIF |
| B81 | AAL | sub | BAG, JAS, SC, whole programme |
| B82 | Upper side of the FE-defect trade-off for one-off zeros | method | BAG, ACS |
| B84 | Arithmetic global trace dominating local tensor moments; weight bound on a family containing ζ | RH | ACS, W4 |
| B85 | Mixed Young projections; positive arithmetic representation | RH | ACS, W2 |

## 2.3 Frankenstein routes

**No assembly closes RH.** Any assembly of proved parts whose remaining input follows from a theorem would make that input RH-equivalent. One structural Frankenstein exists: the split of RH lets two routes each do what the other cannot.

| # | Parts | What the assembly gives | Missing input | Strength of the gain |
|---|---|---|---|---|
| F1 | **Split skeleton.** Any AAL producer (one bounded two-prime cone, infinitely many bounded prime towers, shell positivity infinitely often, bounded lags on one progression, twisted plateau sign) with any ZAL receiver (inner-field decay, `Φ_S≤Me^{au}`, heat coefficient `→0`, eventual Hadamard) | RH [L]. A sparse route blind to a non-attained top and a height-local route blind to finite exceptions cover each other's blind spot | One independent AAL input (B81) and one ZAL input (at least qRH) | The only assembly whose output is RH |
| F2 | AHD aliasing limit, CACT dual floors and tails, WTZ weighted floor, VHR window rung | Full-space sign at ratio `R` from a verified height [D] | Bohr profile decomposition above `R₀` (B6) | Removes HF's complement at that ratio; sign is handed to verified windows |
| F3 | Anchor flow, soft kick, contact criterion | A local bound on `∫\|q\|` on each interval excludes contact; verified data is unnecessary [S/D] | B2, B3 | Reduces the tower to one local estimate |
| F4 | NGF zero keeping, MZF Lorentz tail and hyperbolic camera, WVL thresholds, sampling atoms | Local Weil positivity at aperture `λ(δ)·½log T` outside `δT` [D] | Assembly (A21); fixed `λ` is B30 and B57 | First sign at unbounded aperture for all tests |
| F5 | 8-way equivalence, Selberg tail moment, Euler-mollifier log-mean bound, prime field | Typical-height layer reduces to one number, `E log‖ζM_S‖=o(1)` [L] | B57 | One target for RW, ZCG, WD |
| F6 | `N(ρ)=exp(−ΣG)`, hyperbolic count, box budgets, long-mollifier residue bound | Deep zeros obey rate 2 or carry a large Green potential [L/S] | B60 | Density Hypothesis exponent near `½` |
| F7 | TH Euler product, PM scattering, FFP drift law, PTR at `h=½`, Lagarias–Suzuki line law | One edge theorem with several proofs on one Hermite–Biehler shift axis [D] | Interior: B66, B68 | One carrier; no interior gain |
| F8 | TH torus walls, columns add, ZCG carrier horizon, FFP forced drift | One inequality: sum of Euler column minima against Gamma base [D] | B21 | Merges TH's wall with ZCG's |
| F9 | Stepanov over ℤ, recurrence transport | The order of Weil's theorem in Stepanov's form: count, then purity, then one-offs [D] | B55, B81 | Sign-free skeleton (see 2.6) |
| F10 | One verified height, all rungs | All finite rungs [L] | Nothing finite | Decides no all-rank statement |
| F11 | VK savings of all routes | One width axis [L] | B16 | They share one input |
| F12 | Attained-top consequences: unbounded lags on every progression, unbounded towers, `\|E_X\|≥X^κ` off a vanishing set, top annihilators, twisted FE, zero-free strip, quasi-RH, finite-frequency prime error | A contradiction search on one rigid world [L/D] | Any contradiction | Decides B81 if it succeeds |

**Closest to the open core: F1, then F12.** F1 says what a two-route proof looks like. F12 is the only place where a proof may assume a zero-free strip.

## 2.4 Wildly different routes

Each mechanism below avoids Σ payment, Π precision and Γ selection as stated. All are speculative. **W5–W7 have no Lean content.** I see no route that I would call promising; these are the ones with a concrete mechanism and a first test.

### W5. Extremal modulus (Bethe / T-Q mechanism)
- **Idea.** Spectral determinants of PT-symmetric oscillators have real zeros with no self-adjoint operator and no positive form [C]. An exact relation `T(E)D(E)=a(E)D(qE)+b(E)D(q⁻¹E)` with entire `T` gives Bethe equations at the zeros. At the zero of extremal argument, every Hadamard factor has modulus on one side of 1, so the product cannot have the required modulus unless the zero is on the axis.
- **Target.** A second-order functional relation for ξ or a transform. At a top zero, `|ξ(ρ+h)|>|ξ(ρ−h)|` holds by Hadamard for real `h>0` [D]. An identity forcing `|ξ(ρ+h)|=|ξ(ρ−h)|` at zeros would end the argument, with no sign used beyond the extremal position.
- **Why the walls differ.** No payment, no window, no precision. It uses the same extremal position that gives the corpus its AAL producers.
- **First test.** A relation with explicit modulus on `L`-polynomials of curves. Hecke gives one in `z` at fixed `s`, not in `s`.
- **Risk.** ζ and its algebraic dilates are differentially independent over the Gamma–theta field [L], which excludes such a relation with coefficients in that field. It must therefore be infinite-term or have transcendental coefficients.

### W6. Arithmetic capacity for integer auxiliaries
- **Idea.** Fekete–Szegő–Rumely–Cantor theory gives exact existence criteria for integer auxiliaries with prescribed local conditions, via capacity of an adelic set [C]. The Nair lattice is exact [L] and the stencil slope has infimum 1 [L].
- **Target.** Express the optimal slope `A(K)` of stencils of alphabet `K` as an adelic capacity, with a perturbation formula for `A(K)−1`.
- **Why the walls differ.** It does not estimate primes. It computes an extremal constant, as sphere packing computes a bound by an extremal function.
- **First test.** Reproduce the integer Chebyshev ceiling `e^{−0.87n}` [L] and the parity ceiling `31/30` [L] from capacity.
- **Risk.** Capacity is continuous data and parity is not. The rate may be blind to `Θ`.

### W7. Interlacing families (mixed characteristic polynomials)
- **Idea.** Mixed characteristic polynomials of PSD matrices are real-rooted by real stability, with no eigenvalue estimate [C].
- **Target.** Exhibit `R_d(Ξ)` or its Hankel as such a polynomial, built from first atoms, PD at every rank [L].
- **Why the walls differ.** No inequality is paid. The unstable pieces in the finite free calculus [L] are factorwise splits, not mixed forms.
- **First test.** Degree `d=3,4`: are the Taylor coefficients mixed discriminants of explicit PSD matrices?
- **Risk.** A Hilbert–Pólya realization in finite-dimensional dress. No corpus module addresses it.

### Formalized lines with walls of their own

| Line | Established [L] | Boundary [L] | Open core |
|---|---|---|---|
| W2 Representation | Coherent central class functions with Gram positivity ⇔ RH; positive real-part character with transposition defect `Σ(Im α_ρ)²/p₁²`; every column Young projection nonnegative; endpoint Toeplitz minors of order `≤200` nonnegative | Sorted occupancy and finite partition stabilizers fail; generic common-pivot tests pass non-characters | Positive arithmetic representation with prescribed cycles (B85) |
| W3 Exact extremal | Real exponentially decaying `Φ=Ξg`, blind at every `log n`, zero pole–archimedean energy; tail exponent 1 attained | `kb≤2` for full `Ξ^k` divisor; no strict energy on blind tests | Positivity of the whole blind program (B19) |
| W4 Weight on a family | Tensor-uniform growth ⇔ purity; nonnegative global trace bounds negative spectrum; Kloosterman fibres pure by Stepanov; explicit moment counts and Tate corrections | Golden has correct invariant weights and full `SL₂` image; pure compression preserves even subspace iff RH | Arithmetic family and global trace (B84) |

### Tested and rejected form
**Lee–Yang lift on the prime torus.** A stable lift on the product torus requires Gamma speed above the total Euler speed, which diverges [D]. It agrees with forced Euler drift `θ_S/2` [L] and with columns add [S].

## 2.5 Breakthrough questions below RH and quasi-RH

| Test | Requirement |
|---|---|
| T1 | Implied by RH and not implying quasi-RH |
| T2 | Answered by proving or refuting a stated inequality |
| T3 | A named consequence can be written down |
| T4 | Not decided by a finite rung |
| T5 | False on a corpus fake |
| T6 | Names an input not refuted in Lean |
| T7 | Not a shape already answered without moving a wall |

### 2.5.1 Whole programme — the log-mean of ζ (B57)
**Question.** Does `T⁻¹∫_T^{2T}log|ζ(½+it)|dt→0`?
- **Why it matters.** By the 8-way equivalence it is `100%` critical-scale clustering, the Euler-mollified log-mean, the outer law, and the dyadic depth, Hecke and theta readings [L]. By the depth law it is reality at every `τ>0` on density-one windows outside crowds [D]. It gives local Weil positivity at fixed `λ` on density-one heights (B30) [D]. It closes the typical-height layer for RW, ZCG and WD together.
- **Where it stands.** Selberg gives `O(1)` for this mean. Under RH it is `O(log T/T)`, while `log|ζ|` has variance `½log log T`. Selberg's tail moment removes large depth [L], and `|∫log|M_S||≤Σ_{p∈S}(3+6/log p)` [L].
- **The tool gap.** Jensen plus a second moment cannot reach `o(1)` with polynomial mollifiers: the moment stays above `1+1/(8+6θ)` [L], and moments do not determine the log-mean [L]. The target is a sharp log-mean, not a sharper moment. The natural input is the prime field `log|ζ|=Re P+` bounded error [L], with the mean of the error reduced from bounded to `o(1)`.
- **Tests.** T1–T4, T7 pass. T5: false on `ζ(s)(1−cp₀^{−s})`, `c>√p₀`, where the mean tends to `log(c/√p₀)>0` [S]. T6: prime field, Euler-mollifier bound, tail moment.
- **Limit.** Sparse off-line zeros survive; rare large heights untouched.

### 2.5.2 Route PM — a lower bound for Hecke dispersion (B68)
**Question.** Is there an explicit `η(γ)>0`, derived from the Hecke action on truncated resonant states with no Euler-product inequality, such that `V_p(ρ,Y)≥η(γ)` at every resonance?
- **Why it matters.** `V_p=2(1−p^{β−1})` [L], so this is the zero-free curve `β≤1−η(γ)/(2log p)` from the carrier: the first interior information without an Euler-product inequality. The boundary proof already gives `|ζ(1+it)|≥c/(t³log²t)` that way [L].
- **Tests.** All pass. T5: Blaschke insertion preserves every Schur form [L], so the proof must use actual Whittaker and Hecke data. T6: uniform Hecke residual, height law, boundary norm [L].
- **Limit.** A curve of classical shape at best. It does not touch `D_s≥0`.

### 2.5.3 Route WD — the cluster wall (B59, B60)
**Question.** Is the mean of `exp(2Σ_{a≠ρ}m_aG(ρ,a))` over zeros of depth `≈α/L` bounded by `e^{εα}`? That gives `N(½+α/L,T)≪_εTLe^{−(2−ε)α}`, `1≤α≤cL`, for every near-line zero.
- **Why it matters.** Isolated zeros obey it without separation [L]. `N(ρ)=exp(−ΣG)` [S] reduces negative moments of `ζ′` to exponential moments of one potential: no further analytic input stands between them. The Density Hypothesis near `σ=½` is open [C].
- **Tests.** All pass. T5: false on the impure column, fraction `≈1/A` of zeros at depth `A/L` [L]. T6: hyperbolic count, box budgets, Lorentz tail, A22.
- **Limit.** The one-log loss remains, so no `D_win`; sparse zeros survive.

### 2.5.4 Route HF — a Bohr profile decomposition above `R₀` (B6)
**Question.** Fix `R>R₀`, where `R₀` is the positive root of `C′R²+C_SR−D/8=0` from the far reserve [D from L]. Does every sequence of atomic tests with bounded complete energy split as a strong physical `L¹` limit plus profiles over the Bohr compactification of translations, with nonnegative asymptotic energy?
- **Why it matters.** At fixed `R` the limit pencil is a finite rung [D]. All remaining content is compactness: far band, conductors past `(log N)^{13/32}`, receiving-charge bubbles. Lions' additive splitting is not available: `c_φ(t)↛0` for every nonzero test, and only subsequential decoupling survives [S]. The theorem has to be stated on the Bohr space, which no profile decomposition in the corpus does.
- **Tests.** T1–T3, T7 pass. T5: the Liouville twin fails at fixed overlap [K]. T6: aliasing limit, sharp dual floor, tails, `L²` precompactness criterion, receiving modes with exact limits [L], recurrence of nonnegative cosine series [S].
- **Gives.** The first full-space sign past size, and the first compactness theorem for an arithmetic form.
- **Limit.** Each ratio is separate. Sign is handed to verified windows.

### 2.5.5 Route TH — the torus law (B21)
**Question.** Is the largest torus-positive prime set `S*(a,b)` exactly the set where the sum of Euler column minima stays above the Gamma base, up to a constant: `Σ_{p∈S}log p/(p^{½+a}−1)≲½log(b/2π)`? First case: is the complete `{2,3}`-smooth spectrum positive at every `0<a<½`, every `b`, every pair of phases?
- **Why it matters.** It would turn the numerical wall at `P≈19–47` [N] into a law, explain locking by the growth of the Gamma term, and identify TH's wall with ZCG's carrier horizon [D]. Columns add on Kronecker families [S] gives the shape of the law at a fixed base. It is the first cross-chain theorem. Pointwise payment fails at `log 6` [L], so the proof must integrate over centers.
- **Tests.** T2, T3, T7 pass. T1 and T5 do not apply: this is a model source, and prime flips inside `S` are points of the same torus. T6: columns add, Hecke–Bessel, log-concavity and size-floor walls [S].
- **Limit.** A law for `S*` says nothing above `S*`, where actual cancellation in the prime sum is needed.

### 2.5.6 Route RW — bounded variation of the reflection (B3)
**Question.** Is `r` of bounded variation on bounded aperture intervals, with a constant free of `1/μ`? Equivalently, is `∫|q|(1−r²)≤C(b−a)+C′` on precontact intervals?
- **Why it matters.** Every proved chart estimate retains `1/μ`, which is doubly exponentially small; expected `|q|(1−r²)≈2` is bounded [D]. It would make every contact of finite order, with the exact scaling law `|q|≈(1+1/γ)m` [L], and give a step `a*≥a+c(1−r²)/C`.
- **Tests.** T2, T3, T7 pass. T1: implied by RH on each interval. T5 fails: as a structural bound it should hold for fakes, so arithmetic enters only through the data. T6: restoring flow, soft kick, energy identity, Green corner [L/S].
- **Limit.** Permits contact and produces no sign. Its value is the removal of `1/μ`.

### 2.5.7 Route ZCG — an all-height input that is not a size bound (B83)
**Question.** Is every zero's multiplicity `o(log X)` unconditionally? The route reaches it through a Fock frequency bound `o(log X)` at small `t`, since order is at most twice the frequency.
- **Why it matters.** ZCG's only all-height inputs are size bounds. Its frequency law gives `≤(3300/9991+ε)log X`, a size bound in disguise [L]. Lindelöf would give `o(log X)` [D]; an unconditional proof must use more than size. It is the first step toward frequency `<1` at collisions (B27) and bounds every collision order.
- **Tests.** T1: RH gives `≪log X/log log X` [C]; it does not imply quasi-RH. T2, T3, T4, T7 pass. T5: false on FE twins with prescribed high-order zeros [L]. T6: frequency monotonicity, order law, FE-pair flatness, near-coincidence dictionary [L].
- **Limit.** Bounds collisions, does not exclude them.

## 2.6 If positivity, Weil positivity and spectral methods are excluded

**What survives** [L]:

| Class | Receivers | Sign-free input proved |
|---|---|---|
| Production | Siegel and Liouville halves, stencils, one-sided counts as `ψ(x)` bounds | exact integrality; slope `1+ε`; Stepanov chain over `𝔽_q` |
| Transport | Strong and weak recurrence, target mass, AAL | pair returns at typical base; zero-disc transport |
| Cancellation | `M(x)`, one-point and one-window forms, long moments, Báez-Duarte | VK; last-scale and length laws |
| Dominance | Finite carriers real above horizon; heat horizon | Gamma speed beats finite Euler speed |
| Identification | Cameras, sharp location, FE-pair flatness | sign-free readout conditional on isolation |
| Rigidity | Exact FE forces primes; Selberg-class discrepancy; Hamburger uniqueness | zero defect ⇒ rational primes |

All of Σ falls, with PM's Krein branch, TH, W2, W3 and the index routes. Over `𝔽_q` a proof with this profile exists: Stepanov's. A producer gives a count, the count gives purity, and no Hodge index or operator appears [L]. So the template is not hypothetical.

**The question.** Is there an explicit parity-selective integer auxiliary over ℤ whose forced vanishing at primes beats its size at a rate past Vinogradov–Korobov?

Precisely: let `A(K)` be the least slope of a balanced integer stencil of alphabet `≤K` with `Σc(k)⌊r/k⌋≥0` and `≥1` on `[1,B)`. Corpus: `inf A=1`, unattained [L]. Does an explicit family, with constants polynomial in `K`, satisfy `A(K)−1≤exp(−(log K)^α)` with `α>3/5`, produced with no zeros and no Fourier analysis? Its Siegel-half counterpart on the lower side: integer `P` of degree `≤n` with `0<∫₀¹P≤exp(−n+n·e^{−(log n)^α})`.

**Why it opens the path.**
- It reads the exponents [D]: `α=3/5` is VK; `K^{−c}` is quasi-RH; square-root scale in either the Siegel or the Liouville half is RH [L]. So one construction parameter runs from a historic advance to the theorem.
- No zero, no sign of a form, no operator. The only arithmetic fact is that a nonzero integer has size at least 1.
- All Π filters are constraints on it and none refutes it. Squares give the Selberg sieve and the parity factor [D], and non-alternating stencils stop at `31/30` [L], so the construction must be signed.
- With transport for one-offs (B81) it is the full Stepanov order over ℤ (F9).

**Tests.** T1: RH gives the prime count; whether RH gives such stencils is unproved, though truncated Möbius weights suggest it [D]. T2, T3, T4, T6, T7 pass. T5: the statement concerns rational integers only, and it must fail for Beurling data by construction, since the stencil uses `⌊r/k⌋`.

**Limit.** Best elementary PNT errors are far below VK [C]. Farkas duality uses a Möbius test [L], so the known stencils are not independent of prime information. An independent construction is exactly what is missing.

**Second door.** AAL (2.9) is also sign-free in its prime-side form.

## 2.7 Does closing RH need a new field?

No theorem says so. The evidence is structural: every available tool stops for a proved reason.

| Tool | Why it stops |
|---|---|
| Size estimates | die before half-width `21/40`; exact across independent reflectors |
| Positivity-preserving (Markov, Perron) | frustration past `log ρ` |
| Type I/II sieve data | parity blind |
| Barriers, distribution of prime sums | blind to purity |
| Short mollifiers and weights | last-scale floor |
| Second moments for the log-mean | Jensen is sharp for moment data |
| Concentration-compactness | far bubbles do not decouple |
| Finite computation | finite rungs decide nothing |
| Tensor amplification | carries RH unchanged |
| Integrality | amplifies; no rate |
| Parabolic monotonicity | blind to `t=0` |
| Unitarity, Schur and `C*` positivity | reach only the edge; blind to zero position |
| Fixed-amplitude Euler positivity | Laplace cone; columns add |

**What the field would be about.** *Arithmetic inner-function theory:* why a function with an Euler product and a functional equation has trivial inner factor right of its symmetry line, and why its critical causal system stays passive at zero slack. It already exists as a Lean programme, in part.

| Aspect | Built | To build |
|---|---|---|
| Objects | inner field, box and crowd, anchor flow, reflectors as free coordinates, outer predictors, insertion operators, echo columns, Euler columns, scattering Blaschke product [S/D] | local onset field; arithmetic Carleson measure; forward map from primes to reflectors at large `n` |
| Language | budget, second expression, depth, shadow, crowd, causal in place of positive, slack threshold, Schur band [S] | a calculus of signed echo trains across columns |
| Mechanisms | Poisson–Jensen, Szegő infimum, restoring flow, Schur recursion, prime dictionary at the first reflector [S] | near-extremal mollifiers; passivity certified from arithmetic data |
| Tools | a priori estimates free of `1/μ` for smooth `q` and finite kicks [S]; box budgets [S]; recurrence of nonnegative cosine series [S] | a priori estimates for the actual chain; profile decomposition over Bohr space; Carleson embedding at critical scale with arithmetic coefficients |

**Criteria it must meet.**
- False on every corpus fake: impure columns, Golden, FE twins, shifted products, heated kernels, continuous Beurling systems.
- Parity-breaking and locally pure.
- Unbounded aperture.
- Recovers Weil's proof over `𝔽_q`, including Castelnuovo, as its curve chain [S].
- Sees incommensurability of `log p`: commensurable steps have strictly weaker locking and unbounded room in one column [S]; independent columns allow only size [S]; periodic data admits finite impurity [L].

**Questions it must answer.**
- When is a frustrated form nonnegative at zero slack? The causal certificate and the Schur band give the form of the answer [S], not the producer.
- How does `q` depend on the data past the Born regime? How do reflectors depend on primes past the first echo?
- What plays the role of Castelnuovo: what constructs a near-extremal mollifier over ℤ?
- Why is `(β,s)=(1,0)` critical? Answered in form: singular spectrum [S].
- Can an arithmetic inner factor be finite and nontrivial? Non-arithmetic data can [S].
- How does the Gamma base's growth with height pay the columns above `S*`?

**Limits.** The closest existing pieces are de Branges theory, Krein systems, Hardy space theory and critical Hardy inequalities. What is new is the arithmetic forcing. The production side is not obviously part of the same field, and the corpus proves no bridge beyond shared RH endpoints.

## 2.8 If positivity, Weil positivity and spectral methods are excluded: which field?

If the exclusion holds, inner-function theory loses its core, since a Blaschke mass is a positive quantity and a passive medium is a positive form. The field must be a different one.

**What it would be about.** *Arithmetic auxiliary dynamics:* how the rational integers force zeros of `ζ` by two operations with no sign: **construction** (an integer object forced to vanish beyond its size) and **transport** (a vertical return moving a zero to new heights). The model is Stepanov's proof, plus the almost-periodicity that a curve has automatically.

| Aspect | Content |
|---|---|
| Objects | Nair lattices and horizons; stencils and factorial towers; Hecke dilation operators on them; gauge torus with Adams operators; return sets; Hurwitz limit set of vertical translates; extremal top layers |
| Language | size against multiplicity; Siegel half and Liouville half; integrality exponent; slope; return exponent; transport; extremal position in place of sign |
| Mechanisms | Forced vanishing contradicting size; zero transport by minimum modulus; extremal-factor modulus at a top zero; exact FE rigidity as a uniqueness theorem; Gamma speed as dominance |
| Tools to build | Siegel's lemma with parity constraints; zero and multiplicity estimates over ℤ on the gauge torus; size bounds for signed stencils past sup-norm; quantitative universality at prescribed base points; effective Kronecker at arithmetic scale |
| Test cases | Weil for curves through Stepanov; Kloosterman data; the `{2,3}` stencils; the Golden fake, which must obey transport and fail construction |

**Criteria it must meet.**
- Uses no quadratic form with a sign, no self-adjoint operator, no Hadamard positivity.
- Proves Hasse–Weil over `𝔽_q` in the same language [L for split hyperelliptic curves].
- Distinguishes rational primes from continuous Beurling systems, which have one-offs and no recurrence [L], and from discrete near-fakes.
- Breaks parity: passes the Liouville twin and the filters on Type I and II data [L].
- Reaches past the last-scale floor, which binds polynomial detectors [L].

**Questions it must answer.**
- What replaces Frobenius? Over `𝔽_q`, `(x^q)′=0` is what makes multiplicity cheap. Over ℤ, what makes multiplicity at primes cheap? Adams operators have a sharp support bound `2^{qr}` for full multiplicity [L].
- What is the exact rate `A(K)−1`? Is it computable by a capacity?
- Where does the factor 2 of sieve parity go in a signed construction?
- Why do primes recur at a zero, if they do?
- Is a single off-line zero a contradiction with integer-valued integers `N(x)=⌊x⌋`?

**Limits.**
- Nothing in the corpus shows the exclusion is forced. Over `𝔽_q` both Hodge index and Stepanov prove the theorem.
- The Π filters constrain this field heavily, and no source produces parity-breaking at any power saving.
- Transport may be false in spirit (see 2.9).

## 2.9 The one question

**Can the error in the prime number theorem be a single finite oscillation?** Formally: are there `β>½`, `η>0` and a nonzero finite trigonometric polynomial `T` with

`ψ(x)−x=x^{β}T(log x)+O(x^{β−η})`?

This is the failure of the asymptotic abscissa law [D from L]: AAL fails exactly when finitely many zeros at `Re s=β` stand above a zero-free strip across all heights, and the truncated explicit formula converts that into this expansion and back. The answer expected is **no**.

### Why this question

**It is the exact split of RH [L].** `RH ⇔ ZAL ∧ AAL`, and `RH ⇔ ZAL ∧ zero-disc weak recurrence`. Failure of AAL implies quasi-RH, so AAL holds automatically if `Θ=1`.

**It is logically below quasi-RH.** AAL alone gives no strip. It is implied by RH.

**It is the only half of RH where a proof may assume strong hypotheses.** A proof by contradiction may use all of the following at once:

| In the world ¬AAL | Evidence |
|---|---|
| Zero-free strip `(β₁,β*)` at all heights; quasi-RH; finite top layer | [L] |
| `ψ(x)−x` and `M(x)` are finite oscillations at leading order | [D] |
| `Φ(mℓ)` unbounded above on every progression | [L] |
| `K_ζ` bounded on only finitely many prime towers | [L] |
| `\|E_X\|≥X^κ` off a vanishing set in every bounded window, `κ<w` | [L] |
| Finite annihilators nonvanishing on `Re s≤½`; twisted FE with phase `B²` | [L] |
| No returns at the top zero beyond a finite height | [L] |

No other open statement on any route has this property: it asks for a contradiction in a world with far more structure than any other open statement allows.

**Everything else lands on it.** The most repeated limit in this document is "sparse off-line zeros survive".

### What an answer does

**If AAL is proved:**

| Effect | Routes | Evidence |
|---|---|---|
| RH ⇔ ZAL ⇔ finite off-line support ⇔ finite Weil index ⇔ bounded heat count ⇔ finite critical energy ⇔ eventual Hadamard positivity ⇔ eventual central-gap budget | LA, HF index, SC, CHMD, AIP, SRT, ZCG | [L] |
| Any finite bound on off-line multiplicity gives RH: a count replaces a sign | all index and count routes | [L] |
| Large-height receivers read the global abscissa | ZCG, SRT, LA, LI | [L] under weak recurrence |
| Density and typical-height theorems gain an RH-level target | WD, MZF, NGF, census | [D] |
| Bounded heights leave the proof; finite rungs stop being needed | RW, VHR, every rung | [D] |
| TG's norm `<1` relaxes to a ceiling uniform in the rectangle | TG | [D] |

**If a barrier is proved instead:** a refutation for ζ would refute RH. The realistic negative outcome is a near-fake in a named input class, which kills every argument using only that class.

| Input class | Status | Evidence |
|---|---|---|
| Positive continuous prime measure, `N(x)−ρx−C→0` | one off-line pair, no recurrence | [L] |
| Euler product with positive generalized primes, small reciprocal mass | one-off pair exists | [L] |
| FE with a finite coefficient prefix | zeros placed at will | [L] |
| No arithmetic: `E=s−ρ` | finite inner factor `G(·,ρ)` | [S] |
| Exact Euler product and exact Riemann FE | only ζ | [L] |
| Euler product and FE with `L¹` defect `M` | primes fixed up to `≍M^{−1/2}`; mismatch at `N` costs `>1/(400N²)`; upper side open | [L] |

### The route it opens

- **Path.** Assume the finite oscillation. Derive a contradiction from exact integrality of `N(x)=⌊x⌋` and exact FE.
- **Established.** Transport by returns, pair returns at typical base, returns at a zero `≤T^θ`, threshold `≍|g|r^m` [L]; all AAL producers [L]; the structure of ¬AAL [L].
- **Missing.** Any lower bound on returns at a zero; any contradiction in ¬AAL.
- **Recurrence as the shadow of Frobenius [D].** Over `𝔽_q`, zeros are periodic in `Im s`, so AAL is automatic and Weil's content is ZAL. Golden obeys AAL and fails ZAL. Dirichlet polynomials and periodic data recur, so their zeros are absent or infinite [S]. Over ℤ the flow has no period, and AAL asks how much of periodicity survives.
- **Ladder [D].** Let `e(ρ)` be the growth exponent of the return set at a zero. Density forces `e≤1−cd`. Any unbounded return set gives AAL for that zero. A return exponent above the density bound gives RH.

### Where the proof must be

| Layer | Content | Status |
|---|---|---|
| Typical heights | crystal, real zeros at critical scale, rate 2 for isolated zeros | closed to bounded `τ`; `τ→0` is B57 |
| Rare large heights | ZAL | open, at least quasi-RH |
| One-offs | AAL | open, no estimate |

### First tests

1. **FE-defect trade-off (B82).** How small can the `L¹` defect be for a Beurling system with a one-off off-line zero? The lower bound is proved. A matching family would bar every defect-stable argument.
2. **Discretize the countermodel.** Does a discrete Beurling system with integer-valued integer norms and a one-off pair exist? The exact theorem says no at zero defect [L]. The intermediate range is unknown.
3. **Contradiction search in ¬AAL (F12).** Combine the table above with Selberg's symmetry identity, exact sawtooth of `N(x)`, and top annihilators.
4. **Return lower bound in a model.** Prove returns for an off-line zero of an almost-periodic family with Gamma phase, then find where the Euler tail breaks the argument.

### Validation

T1 passes: implied by RH; it does not imply quasi-RH. T2 passes: a stated expansion to prove or refute. T3 passes: the collapse table. T4 passes: no finite rung decides it. T5 passes: the expansion holds on continuous Beurling systems, so a proof must exclude them. T6 passes: transport, rigidity, spectral gap and top annihilators. T7 passes: no theorem answers it.

### Limits

- The evidence leans against an independent proof. The random Euler model has no zeros, and Deuring–Heilbronn repulsion points the other way [C]: an exceptional zero in a non-RH world may well be a one-off. Test 1 is the check.
- No estimate of any kind exists on this side. The question is less hard only in the sense that a proof may assume strong hypotheses.
- ZAL remains at least quasi-RH. Answering this question does not finish RH.
- Any statement that with known theorems implies RH is RH-equivalent. No below-RH question can close RH logically.

### Why the others rank lower

- **Log-mean (2.5.1):** a classical advance that closes the typical layer, with no effect on rare heights or one-offs.
- **Stepanov over ℤ (2.6):** the deepest in method, but the first rung beats VK by elementary means, and known constructions are not independent of primes.
- **Bohr profile decomposition (2.5.4):** the most reachable, and it simplifies one large block, but it produces no sign and reaches no zero.
- **Cluster wall (2.5.3):** confined to typical heights.
- **Near-extremal mollifier (B80), `D_s≥0` (B66), `q∈L¹` (B2):** RH-strength; answering them is the proof.
