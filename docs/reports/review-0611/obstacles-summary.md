# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `8c88f0f9a6` plus the working tree of 2026-11-06.

Evidence: `[L]` Lean source; `[S]` Lean source unfinished or uncommitted; `[D]` deduction, not a Lean theorem; `[N]` numerical, uncertified; `[C]` classical, not formalized.

**38 live formulations; 9 candidates.** HJ→PA; BSH→CDC; FEL's BSY criterion→CTF. Candidates: APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF.

## 1. Big picture

### 1.1 One sign, one number
RH ⇔ `a*(ζ)=⊤` ⇔ `1∈ℋ(c)` ∀c ⇔ `λ*(c)→0` ⇔ no finite contact [L]. Weil positivity is a critical Hardy inequality `H≥P` on every window; the multiple `1` is the only possible all-window multiplier and no Hardy weight survives on odd tests [L].

### 1.2 The tower is one scalar flow up to contact
The window tower is a literal canonical system with diagonal Hamiltonian, `H₁H₂=1`, no singular part and no atom at aperture 0 [L]. At the anchor `z=i` the traces are real, `τ_L²−τ_R²=2K`, and `K′=τ_L²+τ_R²` [L]. So with `r=τ_R/τ_L∈(−1,1)` [D]:

`(log K(i,i))′ = 2(1+r²)/(1−r²)`, `r′ = (1−r²)q − 2r`, `(log(1−r²))′ ≥ −2|q|`, where `q=Ψ′`, `H₁=e^{2Ψ}`.

Contact is `∫dx/(1−r²)=∞`, and `q∈L¹` on an interval excludes it there. Near aperture 0, `m≈1/(2a)`. At finite-order contact, `m≈γ/(2(a*−a))` and `|q|≈2m`. Under RH, `log K≳πe^{2(a−2)}` [L upper bound on `μ`], so `1−r²≍e^{−2a}` is expected [D]. The only proved global upper control divides by `μ` [L]. RH is therefore a statement about one real function `q`: the potential of a layered medium whose reflectors sit at `½log n`. The prime echo train must be the impulse response of a passive medium.

### 1.3 Finite rungs are theorems; they decide nothing
Lean has the window rung with an explicit height, plus Li, Hausdorff, heat-grid, Jensen, PF, slice and theta rungs [L]. Lean's certified verified height is `H²<431/2` [L]; the rung heights are explicit but not yet evaluated. External `T₀=3×10¹²` gives `a*(ζ)≥≈1.9` [D]. The floor tower stays below `0.3621` [L]. The limit critical pencil at a fixed ratio `R` is also a rung: `a*(ζ)≥(1/8)log R+O(1)` suffices, because the weight `e^{−8y}` pays far windows and the localization cost [D].

### 1.4 One Vinogradov–Korobov layer
AIP cost, SZ source, TT band, MC Hilbert form, WL energy, PTR depth and TH collar all carry the same VK saving and stop there [L]. Interior values of any route's width parameter are zero-free strips. No route has a mechanism past VK.

### 1.5 The crystal on almost all heights
On one density-one set, `Λ_X log X→0` and central gaps hold at every fixed `κ≤t log(x/2π)≤1`, with constant independent of `κ` [L]. For every `δ` there is `κ`: outside `δT`, gaps satisfy `g²≥c·min(t,log⁻²)` for `τ≳κ` on windows of `≍κ` zeros [L], and all zeros there are real [S]. The input is a Poisson-sum slope comparison, with no size bound for ζ below the saddle [L]. The central inequality at all heights implies RH and bounded multiplicity, so it is stronger than RH [L]. Heating the kernel preserves every parabolic law and creates non-real zeros, so parabolic structure cannot select `t=0` [L].

### 1.6 Near-line zeros: isolated at rate 2, clusters at rate 2θ
Hyperbolically isolated zeros obey the Density Hypothesis rate: `≪(α+1)TLe^{−2x}/B₀²` for `x=(1−3c)α≤(3/2)cL`, unconditionally [L], with separation removable [S]. `N(ρ)≤Πϱ`, where `N(ρ)` is the normalized derivative [S]. Isolation is Carleson's uniform separation in `H²(Re s>½)` [D]. Non-isolated zeros are bounded only through the mollifier defect, rate `2θ`, `22/25` at length `T^{21/50}` [L/D]. Barrier data cannot decide occupancy [L]; polynomial detectors stop at depth `≍log log V/θ` [L]; occupied windows lose one log [L].

### 1.7 Long moments are rigid
Slope is exactly `2wθ`. A cofinal bound at any fixed `K` self-improves to `K=6`. RH reads in one bounded window, `∫₀¹|ζM_X|²≪X^{2ε}`, or as a positive proportion of every length-2 window with `|E_X|≤X^ε` [L]. Prefix cancellation, coefficient norms and local inverses do not control the collar [L]. At `r=2`, `ε=0`, the head is exactly `1−1/(D+1)`; all growth sits in the pronic tail [L].

### 1.8 TH is Eisenstein-coefficient positivity
Pair spectrum is `cos(b log(n/m))·A(nm;a,b)`, `A>0` [L]. Summing [D]: `S(a,b)=Σ_Nτ_b(N)A(N;a,b)`, `τ_b(p^k)=U_k(cos(b log p))`, `Σ τ_b(N)N^{−s}=ζ(s+ib)ζ(s−ib)`. These are the Fourier coefficients of `E*(iy,½+ib)`. As operators, `S=Π_pT_pA|_{x=0}`, where `T_p=(1−2cos(b log p)σ_p+σ_p²)^{−1}` and `σ_p` is the shift by `log p` in `x=log N`. Laplace mixtures in `x` are invariant with multiplier `|1−p^{−s+ib}|^{−2}>0`; `A` has a log-concave tail outside this cone. As `a→0`, `current/a→Ξ′²−ΞΞ″`, the Laguerre form that PTR, ZCG and LA also read [D]. Actual phases give `S>0` at all tested `b≤775`; with prime phases free up to `P`, the torus minimum turns negative at `P≈19–47` [N]. A proof must use actual phase locking.

### 1.9 PM reaches the edge by unitarity
The Mayer carrier proves `ζ(2s)≠0` on `Re 2s=1` by Maass–Selberg and a nonzero Whittaker mode [L]. Resonant `D_s≤0`, zero iff `Re s=¼` [L]. No arithmetic reflection holds for the full determinant [L]. Norm positivity lives on the unitary axis; interior information has no norm to use [D].

### 1.10 One inner factor
On `Re s>½`, `(s−1)ζ(s)/s` has inner factor the Blaschke product of right zeros; RH ⇔ trivial. BSY reads its mass at 1; `N(ρ)≤Πϱ` reads it at a zero; the Krein–Langer index reads its degree; Schur parameters and `r(a)` peel it [D]. Equivalences identify truth values, not mechanisms.

### 1.11 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| Markov, Perron, sign-gauge balance past `e^{−3/4}`, `log ρ` | refuted | [L] |
| Size-only payment of primes | ends before half-width `21/40` | [L] |
| Floor tower as aperture producer | stays below `0.3621` | [L] |
| Fixed finite heads for all theta ranks | no Gaussian margin | [L] |
| Pointwise iteration of prime payment | fails at `log 6` | [L] |
| Torus-uniform theta positivity | fails at `P≈19–47` | [N] |
| Parabolic structure as selector of `t=0` | blind | [L] |
| Central inequality as an RH-level target | stronger than RH | [L] |
| Barriers on prime sums as occupancy input | blind to purity | [L] |
| Short detectors and short weights | stop at the last scale | [L] |
| Coefficient norms and local inverses for long moments | blind | [L] |
| Full-determinant arithmetic reflection | none | [L] |
| Finite-template, separable, finite-realization, tensor, integrality shortcuts | stated classes refuted | [L] |

## 2.1 Tasks that are just work

Difficulty is established only where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### Finite verification
| # | Task | Routes | Basis |
|---|---|---|---|
| A1 | Lean-certified `RHVerifiedThrough T` past `14.68`, first `T≈10²–10³` | all rungs | `hardySEM` certified sign chains exist; Turing count missing |
| A2 | Numeric values of `windowHeight`, `xiMassHeight`, `heatGridHeight`, theta `D`; reduce them toward `log(T₀/2π)≳2Σ_{n≤e^{2a+s}}Λ(n)/√n` | window routes, TH, LA, HCF | explicit definitions in Lean; the rungs are vacuous without values |
| A3 | Two-weight membership past `a₀`: odd unit window, `log 2`, `½log 5` | RW, OWU, EWU, ACT, SWC, HF | A1–A2, or rigorous Galerkin |
| A4 | Full-theta rank 10 at every `0<a<½` | TH | gamma reserve, or A1 through `D(N+1)³+1` |
| A5 | Centre PF beyond 54; slice band beyond `709/50` | PA, LA | low-height Gamma |
| A6 | Lean certificate of the center-tail failure | TH | finite computation |
| A7 | Cone widths `𝒜(c)` past `c=0.66`; Lévy sector margins at `½log 3` | PBAP, ACS, RW, CHT | convex programs; numerics |
| A8 | Exact Tate horizons below spread 6 | WTZ, CWS | finite templates exist |
| A9 | Certificates on the nine anti-diagonals `{2,3,4,5,7,8,9,11,13}` | ACT | finite case analysis |

### Effectivization
| # | Task | Routes | Basis |
|---|---|---|---|
| A10 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | HF, SRT, AIP, ACS, SC | proved limits |
| A11 | General profiles past `θ=1/1080` | HF, SRT, SC | tilted-spline template |
| A12 | Certified ratio interval at the size-only optimum; receiving complement inside it (unverified) | HF, AIP, SRT | assembly |
| A13 | Literal channel norms with growing periods, offsets, prime bands (unverified) | AIP | sieve inputs |
| A14 | Mixed Schur debit; first-prime, coarse, polar costs | AIP, CHMD | fixed-dimensional estimates |
| A15 | Sharp-location constants | ZCG, SRT | explicit cameras |
| A16 | Window-visibility constants toward `4δL/k`; tapered crystal to `a≍log T`; two-bump interferometer | WVL, P1 routes | explicit tests |
| A17 | Star horizons, gcd strata, Künneth mixed jets | HF, ACS, WL | effectivization |
| A18 | Hausdorff row saddle estimates and horizons | PA | `HausdorffSaddle` |

### Canonical flow
| # | Task | Routes | Basis |
|---|---|---|---|
| A19 | Lean form of `(log K)′=2(1+r²)/(1−r²)`, `r′=(1−r²)q−2r`, limit-circle transfer, contact scaling | RW, SZ | canonical system, anchor identity |
| A20 | Gelfand–Levitan formula for `q`; singular terms at `2a=log n` | RW, HF | Green operator, edge law |
| A21 | Numerical `r,m,q` for `a≤1` [N] | RW | Galerkin |
| A22 | Function-field chain: `r,q`, ladders, purity certificates of a curve | RW, HF, ACS, SC | `TheWindowReceiversOfACurve`; sign known there |

### Continuation and near-line
| # | Task | Routes | Basis |
|---|---|---|---|
| A23 | Horizon toward `4μ(½)≈0.619` | ZCG | best exponent pair |
| A24 | Power-saving exceptional set `|{X:Λ_Xlog X>κ}|≪_κT^{1−c(κ)}`, every `κ>0` (unverified) | ZCG | zero density, large values at `σ=½+η` |
| A25 | Lower side and sharp constant of the linear depth law outside crowds (unverified) | ZCG | `exists_zero_near_of_normal_density` |
| A26 | Integrate NGF and MZF `[S]` modules | ZCG, WD | sources exist |
| A27 | Local Weil positivity at small `λ` on positive-density heights (unverified) | RW, ZCG, WD | zero keeping, Lorentz tail, visibility law, short-window lower count |
| A28 | Twisted second moments past `21/50`: to `½`, Conrey `4/7` [C] | WD, census | raises rate `2θ` |
| A29 | Logarithmic two-point Chowla [C] | MC | Tao |
| A30 | Census items; Voronoi; Zwegers [C] | census, ACS | classical |
| A31 | Selberg-class degree-one classification [C] | ACS, SEL | known theorem |
| A32 | PM physical mixed-parameter carrier identifications (unverified) | PM, W1C | completion closed |
| A33 | Effective boundary lower bound `|ζ(1+it)|≫t^{−C}` from the Mayer carrier | PM | Maass–Selberg, Whittaker |
| A34 | Jensen rung toward saddle scale; constants in `300√(d log d)` (unverified) | LA, FFP | saddle identity, height law |
| A35 | One Γ-limit lower bound along `L¹`-convergent atomic sequences | HF, AIP | aliasing limit, dual floors, prime-shift infinitesimality, exponential tail control |
| A36 | `S=Π_pT_pA` and Eisenstein identification in Lean; certified scans of `S_S` | TH | pair spectrum factorization |
| A37 | EGC contour constants | EGC | contour in place |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window | RH; fixed length sub | all sign routes |
| B2 | Contact exclusion: `q∈L¹_loc` on every bounded aperture interval | RH | RW, SZ, CHT |
| B3 | Scale-invariant flow bound: `r` of uniformly bounded variation, free of `1/μ` | sub | RW |
| B4 | Two-sector certificate inequalities on every window | RH | P1 routes |
| B5 | Kick admission at every stage | RH as induction | RW, GWZ, WTZ, HF |
| B6 | Concentration-compactness at one critical ratio above the size-only optimum | sub | HF, SRT, AIP, ACS |
| B7 | Full-space sign eventually at every `K` | RH | HF, SRT, AIP |
| B8 | Growing families, moving frequencies, conductors past `(log N)^{13/32}` | sub | HF, AHD |
| B9 | Head thresholds for every `d` | RH | HF, AHD |
| B10 | No zero mode at any length | RH | HF, TG, SC, EHT |
| B11 | Top coprime stratum | RH | HF, ACS, ADT |
| B12 | Exact SOS on a two-prime lattice | RH | HF, SC, ACS |
| B13 | Index ceiling uniform in resolution | ≥qRH | CHMD, SRT, SC |
| B14 | Zero–one law: exclude finite nonzero off-line support | sub | whole programme |
| B15 | Window negativity exponent `<½`; any interior width value | ≥qRH | width axis |
| B16 | Past Vinogradov–Korobov: floor `α>3/5` | sub | every route |
| B17 | Decay law of `λ*(c)` | sub | CHT, RW |
| B18 | Signed ground-state structure past `log ρ` | method | EWU, OWU, RW, ACT |
| B19 | Prime-blind positivity on signed blind combinations | RH | PBAP |
| B21 | `S`-smooth spectra on small prime sets, first `{2,3}` | model | TH |
| B22 | A prime-insertion invariant containing the actual amplitude | RH (all primes) | TH |
| B23 | Full-source rank `≥10`, all ranks at every `a` | RH (all ranks) | TH |
| B24 | Outer-root control of `R_d(Ξ)` | RH | LA |
| B25 | `N_d` bounded | ≥qRH | LA, FFP |
| B26 | Collision exclusion at small time, every height | RH | ZCG |
| B27 | Frequency `<1` at every putative collision | RH | ZCG |
| B28 | Arithmetic input distinguishing `Φ` among `Φe^{−τx²}` | method | ZCG, TH |
| B29 | Runs of `k` simple critical zeros, every `k` | sub | ZCG, census |
| B30 | Local Weil positivity at fixed `λ>0` on density-one heights | sub | RW, ZCG, WD |
| B31 | Cosine Laguerre sign below the VK boundary | RH | PTR |
| B32 | Heat grids at every degree; chirp bound or mean | RH | HCF |
| B33 | Hausdorff initial segments uniformly in `k`; exterior diagonal; `TV(n)/qⁿ→0` | RH | PA |
| B34 | Covering every zero by a self-map disc | RH | XN |
| B35 | Cofinally small quartic charge | RH | GTA |
| B36 | `C_t` at every fixed `0<t<½` | RH | TT |
| B37 | Bound on the unnormalized prime wave; complete odd sign | RH | CHMD |
| B38 | Joint-node exclusion | RH | RN |
| B39 | `sup|A_N|<∞`; rectangular Ward lower bound | RH | SZ |
| B40 | Cubic trace norm `<1`; bounded Gaussian oscillation | RH | TG |
| B41 | Damped coupling bound; sublinear tensor loss | RH | SC |
| B42 | Source-energy sign at every radius | RH | ACS |
| B43 | Source-work ceiling `≤2` | RH | HF |
| B44 | Complete-history floors | RH | FU, CFC, RP |
| B45 | Li budget or response floor | RH | LI |
| B46 | Retained-variance payment; one shift uniform in profile | RH | ACT, OWU, EWU |
| B47 | `C_σe^{2σr}` signed cost bound | RH | AIP |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B48 | Deciding input at square-root precision: parity-breaking, pure, unbounded aperture and length | RH | WL, MC, PBM, RB, JAS, CTF |
| B49 | Bounded endpoint energy; first cyclotomic mode | RH | WL |
| B50 | Trivial-gauge half power; long-modulus tail | RH | MC, WL |
| B51 | Moving power window control | RH | JAS |
| B52 | Vanishing rows, sparse defect, BSY sign, positive proportion | RH | CTF |
| B53 | Regularized partial-sum bound | RH | PBM |
| B54 | Eventual extremal inequality | RH | RB |
| B55 | `ε`-uniform producer: `C_ε` quasi-polynomial beats VK, polynomial gives a one-sided strip [D] | sub to ≥qRH | WL, MC |
| B56 | `Θ<1⇒Θ=½` | sub | whole programme |
| B57 | `100%` critical-scale clustering | sub | WD, census, MC |
| B58 | `D_win` | sub | WD |
| B59 | Cluster wall: Density Hypothesis rate for every near-line zero | sub | WD, ZCG |
| B60 | Negative moments of `N(ρ)` at deep zeros | sub | WD, MC, ADO |
| B61 | A detector past the last scale | sub | WD |
| B62 | Cofinal long moment; one-window bound; pronic tail | RH | WD, CTF |
| B63 | Collision-charge bound | RH | WD |
| B64 | Signed pair information beyond bandwidth one | sub | census, ACS |
| B65 | Genus upper law; logarithmic Serre duality; first Epstein real zero | indep. to sub | ACS |

### Γ — selection and reflection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B66 | Independent `D_s≥0` or Krein positivity | RH | PM |
| B67 | Independent positive physical or graph carrier | producer | PM, W1C, PTR |
| B68 | PM-native zero-free curve inside the strip | sub | PM |
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

## 2.3 Frankenstein routes

**No assembly closes RH.** Any assembly of proved parts whose remaining input follows from a theorem would make that input RH-equivalent. Each row names what the parts jointly give and the one input still missing.

| # | Parts | What the assembly gives | Missing input | Strength of the gain |
|---|---|---|---|---|
| F1 | AHD aliasing limit, CACT dual floors, WTZ weighted floor, prime-shift infinitesimality, VHR window rung | Full-space sign at critical ratio `R` from a verified height. With external `T₀`: ratios up to order `e^{15}`, far past the size-only optimum; constants not computed [D] | Compactness of bounded-energy sequences (B6) | Removes HF's complement obstacles at that ratio |
| F2 | CSTW canonical system, CHT edge law, WVL corridors, VHR | Scalar flow `r,q` with verified initial data. A variation bound gives step `a*≥a+c(1−r(a)²)/C(a)`: an aperture flow that does not freeze [D] | B3 | Structural sign past `a₀`; no RH |
| F3 | NGF zero keeping, MZF Lorentz tail and hyperbolic camera, WVL `pairEnergy`, sampling atoms | Local Weil positivity at aperture `λ(δ)L` outside `δT`: first sign at unbounded aperture [D] | Assembly (A27); fixed `λ` is B30 | Contact, if any, is a sparse-height event |
| F4 | Census proportion, NGF maximum principle, finite speed, high-time horizon | Cylinders reaching `t=0` on a positive proportion of windows [D] | `k`-runs (B29); lateral layers | First exact reality in a window at `t=0` |
| F5 | MZF `N(ρ)≤Πϱ`, ADO FE-pair flatness, MC negative-moment bound | Deep zeros either obey rate 2 or sit where `ζ′` is abnormally small | `J` bound (B60) | Density Hypothesis exponent near `½` |
| F6 | TH Euler operators, PM Eisenstein carrier, Maass–Selberg | TH is a truncated Hecke period; PM is its scattering. Edge positivity is shared [D] | Positivity off the unitary axis (B66) | One carrier for two routes |
| F7 | TH finite ranks, PTR VK window, LA verified degrees, PF rungs | All Laguerre-type finite rungs from one verified height [L] | Nothing finite | Decides no all-rank statement |
| F8 | VK savings of AIP, SZ, TT, MC, PTR, TH | One width axis [L] | B16 | No combination improves VK; they share one input |
| F9 | Hyperbolic density, `N_d` height law, finite support consequences | Finite off-line support makes every deep zero isolated, so the camera sees it at rate 2, and `N_d` counts it from `d≳γ²log γ` [D] | B14 | Clean test bed for the zero–one law |

**Closest to the open core: F1 and F2.** F1 replaces HF's complement by compactness and hands the sign to verified windows. F2 replaces the `1/μ` factor by a scale-invariant bound. Together they would reduce the atomic and tower routes to one all-aperture statement, B1. Neither supplies B1.

## 2.4 Wildly different routes

Each mechanism below avoids Σ payment, Π precision and Γ selection as stated. All are speculative. They share only the endpoint RH.

### W1. Interlacing families (mixed characteristic polynomials)
- **Idea.** Marcus–Spielman–Srivastava obtain real-rootedness without any eigenvalue estimate: the mixed characteristic polynomial `Π(1−∂_{z_i})det(xI+Σz_iA_i)|_{z=0}` of PSD matrices is real-rooted by real stability [C].
- **Target.** Exhibit `R_d(Ξ)`, or its Hankel, as a mixed characteristic polynomial of PSD matrices built from first atoms, which are PD at every rank [L].
- **Why the walls differ.** No inequality is paid. The finite free calculus already holds [L], and the unstable pieces it rules out are factorwise splits, not mixed forms.
- **First test.** Degree `d=3,4`: are the actual Taylor coefficients mixed discriminants of explicit PSD matrices?
- **Risk.** It is a Hilbert–Pólya realization in finite-dimensional dress. Lorentzian necessary conditions may fail on Ξ.

### W2. Representation-theoretic construction (Thoma, Schur–Weyl)
- **Formal receiver [L].** With `α_ρ=1/(ρ(1−ρ))`, completed arithmetic response jets define the normalized central class functions `σ↦Π_{cycles}p_k(α)/p₁^k`, coherently under restriction. Their complex Gram positivity is equivalent to RH: common-pivot cycles recover every endpoint Hankel test, without invoking Thoma classification. See [exact construction and open source obligation](../../drafts/pipeline/1-in-progress/w2-representation-construction.md).
- **Why the walls differ.** A representation has positivity built in. The [endpoint exterior coefficient sequence is PF₂₀₀](../../drafts/pipeline/3-formalized/not_new_scientific_knowledge/w2-endpoint-sector-positivity.md) [L], by sector preservation and locally uniform products. This finite-order result does not establish full character positivity.
- **Positive model [L].** Summable independent-color alphabets give positive coherent characters with exact cycle power sums. Normalized endpoint real parts give such a character, but its transposition discrepancy is exactly `Σ(Im α_ρ)²/p₁²`, zero iff RH. [Fixed-mean mixing adds precisely total color variance](../../drafts/pipeline/3-formalized/not_new_scientific_knowledge/w2-mean-preserving-endpoint-mixture-minimum.md); its unique supported minimizer is the deterministic real-part alphabet. Disjoint-cycle factorization separately acquires a covariance defect.
- **Partition boundary [L].** [Sorted occupancy fails Young branching](../../drafts/pipeline/5-failed/w2-sorted-occupancy-young-law.md). [Finite unmarked partition stabilizers fail restriction](../../drafts/pipeline/5-failed/w2-unmarked-finite-partition-stabilizers.md); blockwise stabilization is coherent. Infinite occupied blocks force finitely supported partition stabilizers to be blockwise.
- **Curve calibration [L].** A [positive phase character exists for every nonempty curve datum](../../drafts/pipeline/3-formalized/not_new_scientific_knowledge/w2-curve-phase-character-purity-boundary.md), including the golden fake. Exact identification with the periodic endpoint alphabet is equivalent to Frobenius purity. The fake passes every principal-branch endpoint test and fails the first-period test.
- **Alternating projections [L].** [Every arithmetic sign projection is nonnegative](../../drafts/pipeline/3-formalized/not_new_scientific_knowledge/w2-endpoint-exterior-series.md): its exact value is the corresponding derivative of `G(1/4+z/M)²/G(1/4)²`. This retains the actual complex divisor weights and proves all column projections; mixed Young shapes remain open.
- **Open core.** Construct a positive arithmetic representation with the prescribed cycle values independently of zeros. The formal equivalence and positive substitute do not supply this input.

### W3. Exact extremal function (sphere-packing method)
- **Idea.** Construct the exact null ray of the blind program, as Viazovska's functions do for a zero-slack LP [C].
- **Result [L].** A nonzero test with `Φ=Ξ·g`, `|Φ|²` blind at every `log n`, `n≥2`, and exactly zero pole–archimedean energy is [constructed in Lean](../../drafts/pipeline/3-formalized/w3-single-exact-blind-test.md). The annihilating arc multiplier has positive real part on `|Im z|≤501/1000`; its principal square root supplies `g` without extra zeros in that strip.
- **Why the walls differ.** No primes and no margin appear.
- **Constraints [L].** The Carlson obstruction assumes wider Mellin-strip decay and logarithmic-room integrability (`ExactNullCertificateOrderTransfer`). Full containment of the `Ξ^k` divisor forces `kb≤2` for a nonzero source with tail `exp(−a exp(b|x|))`.
- **Sharp boundary [L].** The constructed blind correlation [attains exponent one](../../drafts/pipeline/3-formalized/w3-exact-blind-correlation-boundary.md); every exponent `b>1` is excluded by its full `Ξ²` divisor.
- **Remaining boundary.** Exact existence does not supply positivity of the entire blind program. Prime-blind positivity remains the RH-level question.

### W4. Purity by a weight argument on a non-fibred base
- **Idea.** Deligne's Weil II gets purity from a family with big monodromy and the Rankin trick on tensor powers, with positivity from Euler-product coefficients, not a Hodge index [C]. Direct tensor powers of `K_ζ` carry RH unchanged [L]; the missing piece is a base with monodromy.
- **Target.** A family containing ζ over an analytic base, built with condensed or analytic-stack methods [C], whose monodromy-invariant part is pure.
- **Why the walls differ.** Sign comes from a weight filtration on a family, not from a window.
- **First test.** Reproduce the function-field window receivers from such a family.
- **Risk.** No such base is known; the Golden fake shows Euler data plus FE alone are not enough [L].
- **Formal boundary.** Golden Frobenius also has every `SL₂`-invariant tensor weight and nonnegative even-tensor Euler coefficients, but its optimal degree-`m` growth rate is `φ^m` ([obstruction and positive survivor](../../drafts/pipeline/5-failed/w4-invariant-weights-alone.md)) [L]. A common rate across all even degrees is equivalent to curve purity and the spectrum-window receiver [L]. Canonical divisor compression is pure, but Frobenius preserves its invariant subspace iff RH ([exact decomposition](../../drafts/pipeline/3-formalized/w4-canonical-monodromy-compression.md)) [L]. The arithmetic family and global trace bound remain open.
- **Constructive calibration.** A [nonnegative global trace](../../drafts/pipeline/3-formalized/w4-positive-global-trace.md) bounds its negative spectrum from its positive spectrum alone [L]. Actual [Kloosterman fibres recover all window forms](../../drafts/pipeline/3-formalized/w4-kloosterman-window-receiver.md) using the independent Stepanov estimate [L]. Their global moments are [explicit projective torus point-count differences](../../drafts/pipeline/3-formalized/w4-kloosterman-moments-are-point-counts.md), with an unconditional even-degree incidence inequality [L]. The new cohomological weight argument remains open.
- **Local geometry.** The [hyperplane term is an explicit Tate trace](../../drafts/pipeline/3-formalized/w4-hyperplane-trace-is-explicit.md) [L]. The reciprocal locus has [normalized sign critical points and a nondegenerate transverse Hessian when `2≠0`](../../drafts/pipeline/3-formalized/w4-reciprocal-torus-singularities.md) [L]. Its [coordinate boundary is critical exactly where at least three coordinates vanish](../../drafts/pipeline/3-formalized/w4-reciprocal-projective-boundary.md) [L]. The global trace formula and weight bound remain open.
- **Boundary and compactified trace.** The [complete projective coordinate boundary](../../drafts/pipeline/3-formalized/w4-coordinate-boundary-tate-trace.md) has count `D_n=Σ_{j=0}^{n−2}q^j−B_{n−1}−nB_{n−2}` and a finite signed Tate trace over every finite extension, with eigenvalues bounded by `q^(n−4)` [L]. The [compactified moment identity](../../drafts/pipeline/3-formalized/w4-compactified-moment-trace.md) separates the actual projective count from explicit Tate corrections; its even-degree remainder is unconditionally nonnegative [L]. The remaining finite spectrum and its positive weight bound are not yet constructed.
- **Critical-point trace.** Every normalized torus critical point [descends through field embeddings](../../drafts/pipeline/3-formalized/w4-critical-point-tate-trace.md). Its trace is constant, with exact binomial counts outside characteristic two and an exact zero-or-one formula in characteristic two [L]. The [actual transverse quadratic determinant](../../drafts/pipeline/3-formalized/w4-transverse-quadratic-determinant.md) is `−Πx_i` [L]. Exact [affine discriminant distributions](../../drafts/pipeline/3-formalized/w4-quadratic-fibres-from-discriminants.md) and [actual projective quotient counts](../../drafts/pipeline/3-formalized/w4-projective-quadric-counts.md) hold for every nondegenerate quadratic form over an odd finite field [L]. Reciprocal transverse specialization, extension trace, and exceptional-divisor identification remain to be constructed.

### Tested and rejected form
**Lee–Yang lift on the prime torus.** `Ξ=A+A^#` lifts to `w²Π_p(z_p−a_p)/(z_p(1−a_pz_p))=−1` with `a_p=p^{−½}` and `w` the Gamma phase. Each Euler factor has winding 0, so all drift comes from `w`. A stable lift on the product torus requires Gamma speed above the total Euler speed, which diverges [D]. This agrees with the forced Euler drift `θ_S/2` [L]. A lift must correlate torus position with height; a product-torus Lee–Yang route does not exist in this form.

## 2.5 Breakthrough questions below RH and quasi-RH

| Test | Requirement |
|---|---|
| T1 | Implied by RH and not implying quasi-RH |
| T2 | Answered by proving or refuting a stated inequality |
| T3 | A named consequence can be written down |
| T4 | Not decided by a finite rung (applies to claims of reaching RH) |
| T5 | False on a corpus fake |
| T6 | Names an input not refuted in Lean |
| T7 | Not a shape already answered without moving a wall |

### 2.5.1 Whole programme — the local onset field (B30)
**Question.** Let `f` be supported in `[−λL_T, λL_T]`, `L_T=½log(T/2π)`, with transform concentrated in a unit window at height `X`. Is there one `λ>0` such that `Re W(f,f)` is nonnegative up to tail terms for all but `o(T)` heights `X∈[T,2T]`?
- **Why it matters.** Lean has sign at aperture `≈0.362`; verification reaches `≈1.9`. This would be sign at unbounded aperture, selected by arithmetic. It defines a field `a*(X)` in place of the single number `a*(ζ)`.
- **Structure [D].** `pairEnergy(δ,a)≈(2/3)δ²a³`, so depth `A/L` is invisible to `λ≈A^{−2/3}`. `λ>1` forces depth `<e^{−c log³T}`: a phase transition at the camera threshold.
- **Reach.** At fixed density `1−δ`, `λ(δ)>0` follows from zero keeping by assembly (A27). Fixed `λ` at density one requires that zeros deeper than a fixed `A/L` have density zero.
- **Tests.** T1, T2, T3, T7 pass. T5: false on `ζ(s)(1−cp₀^{−s})` once `A≳λ^{−2/3}`. T6: weak for fixed `λ`; the named inputs reach only `λ(δ)`.
- **Gives.** Sign and location in one statement; RW, ZCG and WD share one exceptional set.
- **Limit.** Sparse off-line zeros survive.

### 2.5.2 Route PM — an interior zero-free curve (B68)
**Question.** Can the Mayer carrier alone, by a quantitative Maass–Selberg argument, exclude resonances on `Re 2s≥1−η(|Im s|)` for an explicit `η>0`?
- **Tests.** All pass. T5: Blaschke insertion preserves boundary modulus and every native contractivity [L], so a proof must use the actual Whittaker data. T6: the boundary proof's ingredients [L] and A33.
- **Gives.** The first interior information from a carrier without the Euler-product inequality.
- **Limit.** A curve of classical shape at best. It does not touch `D_s≥0`.

### 2.5.3 Route WD — the cluster wall (B59, B60)
**Question.** Does every near-line zero obey the Density Hypothesis rate: `N(½+α/L,T)≪_εTLe^{−(2−ε)α}`, `1≤α≤cL`? Equivalently, is the mean of `N(ρ)^{−2}` over zeros of depth `≈α/L` bounded by `e^{εα}`?
- **Why it matters.** Isolated zeros already obey it [L]. The remaining case is a local fraction `≳1/8` of comparably deep zeros [D]. The Density Hypothesis near `σ=½` is open [C].
- **Tests.** All pass. T5: false on the impure column, with fraction `≈1/A` of zeros at depth `A/L` [L]. T6: hyperbolic camera, `N(ρ)≤Πϱ`, Lorentz tail, A28.
- **Gives.** Rate 2 for every near-line zero; corridor constants at `b>½`.
- **Limit.** The one-log loss remains, so no `D_win`; sparse zeros survive. A mollifier at length `T` is the classical route to the same rate.

### 2.5.4 Route HF — concentration-compactness at a critical ratio (B6)
**Question.** Fix one ratio `R` above the size-only optimum. Does every sequence of atomic tests with bounded complete energy split as a strong physical `L¹` limit plus bubbles of nonnegative asymptotic energy?
- **Why it matters.** At fixed `R`, the limit pencil is a finite rung [D]. All remaining content is compactness: far band, conductors past `(log N)^{13/32}`, receiving-charge bubbles.
- **Tests.** T1–T3, T7 pass. T5: the Liouville twin fails at fixed overlap [L]. T6: aliasing limit [L], sharp dual floor [S], tightness from bounded weighted collar mass [S], receiving modes with exact limits [L].
- **Gives.** The first full-space sign past size, up to ratios fixed by the verified height (F1).
- **Limit.** Each ratio is separate. Sign is not produced; it is handed to verified windows.

### 2.5.5 Route TH — the first cross-chain theorem (B21)
**Question.** Is the complete `{2,3}`-smooth aperture spectrum positive at every `0<a<½`, every frequency, every pair of prime phases? What is the largest prime set `S*(a,b)` with torus-uniform positivity?
- **Evidence.** `{2,3}` torus minimum `≈+0.30·A(1)`; `S*` contains primes through 13 at tested `(a,b)` and fails by primes through `19–47` [N]. Pointwise payment fails at `log 6` [L], so the proof must integrate over centers.
- **Tests.** T2, T3, T7 pass. T1 and T5 do not apply: this is a model source, and prime flips inside `S` are points of the same torus.
- **Gives.** The first cross-chain positivity; the correct split between Euler-positive small primes and phase-locked larger primes.
- **Limit.** A theorem on small `S` says nothing above `S*`.

### 2.5.6 Route RW — a scale-invariant flow bound (B3)
**Question.** Is the anchor reflection `r(a)` of uniformly bounded variation on bounded aperture intervals, with a constant free of `1/μ`? Equivalently, is `∫|q|(1−r²)` bounded by an explicit `C(b)`?
- **Why it matters.** Every proved chain bound divides by `μ`, which is doubly exponentially small; `m` is only exponential [D]. A bound in `m` replaces `1/μ` by something exponentially smaller, while still allowing contact.
- **Tests.** T2, T3, T7 pass. T1: implied by RH on each interval; the explicit constant is the content. T5 fails: as a structural bound it should hold for fakes, so arithmetic enters through initial data only. T6: edge law, flux identity, Green operator [L].
- **Gives.** Step `a*≥a+c(1−r(a)²)/C(a)`: an aperture flow that does not freeze.
- **Limit.** Finite step at each stage; no RH. Its value is the removal of the `1/μ` factor.

### 2.5.7 Route ZCG — runs on the critical line (B29)
**Question.** For every `k`, do a positive proportion of zeros start a run of `k` consecutive simple zeros on the critical line?
- **Why it matters.** All ZCG reality stops at bounded `τ`. Runs give windows that are exactly real at `t=0`. With the maximum principle they would give the first cylinders down to `t=0`.
- **Tests.** T1–T3, T7 pass. T5: false on `ζ(s)(1−cp₀^{−s})` for `k>A`. T6: Selberg sign changes, simple-critical `≥0.67250071` by union bound for `k≤3` [D].
- **Limit.** Positive proportion only; lateral layers remain.

## 2.6 Questions that would open the path to RH

Every statement below is RH-strength or stronger; **none is a reachable factor**. Each entry gives the form that most changes what must be proved.

| Route | Question | Why it would open the path | Verdict |
|---|---|---|---|
| 2.6.1 Whole | A second exact formula for the inner-factor mass with the opposite manifest sign | Inner mass `I=Σ_off log|ρ/(1−ρ)|≥0` is unconditional; `I≤0⇔RH` [L]. Over `𝔽_q` that second formula is Castelnuovo's inequality [C] | RH. It says what kind of identity is missing: not an estimate, a second expression |
| 2.6.2 PM | An independent expression forcing `D_s≥0` | `D_s≤0` always; equality iff `Re s=¼` [L] | RH; needs a positive physical carrier (B67). It is 2.6.1 on the Mayer side |
| 2.6.3 WD | Sparse subpolynomial bound on the pronic tail at `r=2,ε=0` | Head is exactly `1−1/(D+1)`; tail gives `K=3`, which gives RH [L] | RH; attractive because only a tail of a compact parity energy remains |
| 2.6.4 HF | Compactness at every ratio with constants polynomial in `R` | HF becomes RW: full-space sign ⇔ `a*(ζ)=⊤` with `R(a)≈e^{8a}` [D] | Reduces to RH, not implied by it alone; removes every complement obstacle |
| 2.6.5 TH | A prime-insertion invariant: `S_{≤p}≥c_pS_{<p}` at actual phases, `Πc_p>0` | Limit gives current `≥0`, hence all ranks, hence RH | RH. Torus-uniform form is false [N]; the invariant must see phase locking |
| 2.6.6 RW | `∫₀^a|q|<∞` at every `a`, by an arithmetic formula for `q` | Contact excluded; prime echo train certified passive [D] | RH; a closed formula for `q` valid past any aperture would be the proof |
| 2.6.7 ZCG | Automorphy of `Φ` gives Gaussian frequency `<1` at every putative collision | Only an input failing for `Φe^{−τx²}` can select `t=0` [L]; modularity fails after heating [D]; frequency `<1` is weaker than the central inequality [L] | RH |

Common shape: **each route has a one-sided sign already proved, and the opposite sign is RH**: BSY `I≥0`, PM `D_s≤0`, TT `D+Q/2≥0`, Li response. What is missing across the programme is a second expression, not a sharper estimate of the first.

## 2.7 Does closing RH need a new field?

No theorem says so. The evidence is structural: every available tool stops for a proved reason.

| Tool | Why it stops |
|---|---|
| Size estimates | die before half-width `21/40` |
| Positivity-preserving (Markov, Perron) | frustration past `log ρ` |
| Type I/II sieve data | parity blind |
| Barriers, distribution of prime sums | blind to purity |
| Short mollifiers and weights | last-scale floor |
| Finite computation | finite rungs decide nothing |
| Tensor amplification | carries RH unchanged |
| Integrality | amplifies, produces nothing |
| Parabolic monotonicity | blind to `t=0` |
| Unitarity (Maass–Selberg) | reaches only the edge |
| Torus-uniform Euler positivity | fails above small prime sets |

**What the field would be about.** *Arithmetic inner-function theory:* why a function with an Euler product and a functional equation has trivial inner factor on the half-plane right of its symmetry line, while its critical passive system stays passive at zero slack.

| Aspect | Content |
|---|---|
| Objects | Inner factors of arithmetic functions; passive layered media with reflectors on `½log n`; window cones over `log ℕ`; canonical flows `r,q`; prime-insertion operators `T_p`; Carleson measures of near-line zeros; local onset fields |
| Language | Budget instead of exact sign; hyperbolic geometry of zeros; depth, crowd, Carleson box; width axis; a duality between prime weights and blind states; Laguerre form as the common observable |
| Mechanisms | A second expression with opposite sign; phase locking of `(p^{ib})` as a source of positivity, not just cancellation; passivity certified from arithmetic initial data |
| Criteria it must meet | False on every corpus fake (columns, Golden, twins, shifted products, heated kernels); parity-breaking; locally pure; unbounded aperture; recovers Weil's proof over `𝔽_q`, including Castelnuovo; sees incommensurability of `log p`, since periodic data admits finite impurity |
| Questions | When is a frustrated form nonnegative at zero slack? What replaces Allegretto–Piepenbrink? Which cones of amplitudes are invariant under prime insertion with locked phases? When is an echo train passive? Why is `(β,s)=(1,0)` critical? Can an arithmetic inner factor be finite and nontrivial? |
| Tools to build | Exact certificates for frustrated forms; a priori estimates for Krein systems with soft atomic kicks, free of `1/μ`; concentration-compactness for arithmetic quadratic forms; Carleson embedding at the critical scale with arithmetic coefficients; inverse scattering with prime data |
| Test cases | Function-field chain, where sign is known and `r,q` compute; then `{2,3}` spectra; then one critical ratio |

**Limits.** The closest existing pieces are de Branges theory, Krein systems, Hardy space theory and critical Hardy inequalities. These are not new; what is new is the arithmetic forcing. The production side, square-root precision, is not obviously part of the same field, and the corpus proves no bridge beyond shared RH endpoints.

## 2.8 The one question

**The zero–one law (B14).** Can ζ have a finite, nonzero number of off-line zeros? Equivalently: does an off-line zero force infinitely many others?

**Why this question.**
1. **Below RH.** RH implies it vacuously. It does not imply quasi-RH: infinitely many off-line zeros approaching the line stay allowed.
2. **It replaces a sign by a count.** With it, RH ⇔ `κ<∞` ⇔ `sup_dN_d<∞` ⇔ finite Weil index ⇔ uniformly bounded heat count [L receivers plus B14]. TG's norm `<1` relaxes to any ceiling uniform in the rectangle [D]. `N_d≤300√(d log d)` [L] is already a count in that family.
3. **Selective.** False on `ξ·R` with rational `R`, on the tempered lattice with one pair [L], on the Golden curve datum with own-tower index 1 [L]. So a proof must use degree one over ℤ, and in particular the incommensurability of `log p`, since periodic data admits finite impurity.
4. **Named inputs.** Finite support gives Lindelöf and a zero-free half-plane [L], makes all but `(κ choose 2)` prime towers decide [K], isolates every deep zero so the camera sees it at rate 2 (F9), and fixes `H_t`'s non-real count [L]. BAG's weaker criterion is RH ⇔ (zeros approach the line at each fixed depth) ∧ (high returns on off-line-zero discs) [L]; the returns half is a direct way to prove it.
5. **Not a shape already answered.** Zero–one laws exist for escape, mixing and height-decay carriers [L]; the actual ζ pullback does not escape, and the question is open there.

**Consequence.** A count instead of a sign: the first time RH follows from a bound with no exact constant.

**Ladder.** Let `e(ρ)` be the return exponent of a disc around an off-line zero. Density bounds force `e≤1−cd` [D]. Arbitrarily high returns give the zero–one law; `e` above the density bound gives RH [D]. This is a width axis for recurrence.

**Limits.**
- Risk that it is false in spirit: Deuring–Heilbronn repulsion points the other way, and the random Euler model has no zeros, so nothing suggests that an anomaly recurs [D].
- `κ<∞` remains ≥qRH. The question moves the door; it does not walk through it.
- Any statement that with known theorems implies RH is RH-equivalent. No below-RH question can close RH logically.

**Next strongest.**
- **HF compactness (2.5.4):** the most reachable, and it passes every test, but it hands sign to verified windows and produces no sign.
- **Cluster wall (2.5.3):** a real classical advance, but sparse zeros survive.
- **Local onset field (2.5.1):** the broadest reading, but its fixed-`λ` form has only the input B57 has.

**Not doors:**
- first windows, which are finite verification;
- the limit critical pencil at a fixed ratio, also a finite rung;
- `D_win` by barriers, refuted as a sole input;
- the central inequality, which is stronger than RH;
- torus-uniform theta positivity, which fails numerically.

## 2.9 The question with the largest impact
**Can an off-line zero be a one-off?** Formally, the asymptotic abscissa law (AAL): for every `h≥0`, if only finitely many zeros lie right of `½+h`, then none does. Equivalently, `limsup(Re ρ−½)` along growing heights equals `sup(Re ρ−½)`. The zero–one law of 2.8 is the case `h=0`.

A sufficient form is weak recurrence around off-line zeros: for every zero `ρ₀` with `½<Re ρ₀<1`, every disc around it and every `ε>0`, there are arbitrarily high `τ` with `sup|ζ(s+iτ)−ζ(s)|<ε` on the disc. A return moves the zero to a new height at nearly the same depth [L].

### Why this question

**It is the exact split of RH [L].**
- `RH ⇔ ZAL ∧ AAL` (`riemannHypothesis_iff_zerosApproachLine_and_asymptoticAbscissaLaw`), where ZAL says that for each `h>0` only finitely many zeros lie right of `½+h`.
- `RH ⇔ ZAL ∧ ZetaZeroDiscWeaklyRecurrent` (`riemannHypothesis_iff_zerosApproachLine_and_zeroDiscWeaklyRecurrent`). The recurrence condition is vacuous under RH.

**The corpus sits almost entirely on one side of that split.** Density, clustering, typical-height and large-height theorems all read ZAL-type information. On the AAL side, Lean has receivers and one upper bound: return shifts around an off-line zero have density zero (`exists_zetaSelfReturn_density_zero`). No lower bound on returns is known. Only BAG names the condition, and it has no estimate for it.

**It is the reason for the most repeated limit in this document,** "sparse off-line zeros survive".

### What an answer does

**If AAL is proved:**

| Effect | Routes | Evidence |
|---|---|---|
| The sparse-zero objection ends: density and typical-height theorems gain an RH-level target | WD, MZF, NGF, census | [D] |
| Large-height receivers read the global abscissa | ZCG, SRT, LA, LI | [L] under weak recurrence: `eventualHadamardPositivityRight_iff_forall_re_le_of_weaklyRecurrent`, `eventualFilteredCentralGapRate_iff_filteredCentralGapRate_of_weaklyRecurrent`, `riemannHypothesis_iff_eventualFilteredCentralGapBudget_of_weaklyRecurrent` |
| A count replaces a sign: any finite bound on off-line multiplicity gives RH, through `N_d`, Weil index or heat count | LA, HF index, SC, CHMD, AIP, SRT | [L] receivers, [D] assembly |
| TG's norm `<1` relaxes to a ceiling uniform in the rectangle | TG | [D] |
| Bounded heights leave the proof, so finite rungs stop being needed for RH | RW, VHR, every rung | [D] |
| What remains is ZAL alone | all | [L] |

**If a barrier is proved instead:** for ζ itself, a refutation of AAL would refute RH. The realistic negative outcome is a fake in a named input class, which kills every argument using only that class.

| Input class | Status | Evidence |
|---|---|---|
| Euler product with positive generalized primes, small reciprocal mass | one-off off-line pair exists: `ζ(s)((s−β)²+γ²)/(s−β)²` | [L] `exists_small_reciprocalMass_zero_off_line` |
| Positive prime density with regular integers | zero at `β+iγ` | [L] `regular_integers_do_not_constrain_zeros`, continuous-density models |
| FE with a finite coefficient prefix | zeros placed at will | [L] FE twins |
| Exact Euler product and exact Riemann FE | only ζ: no fake exists | [L] `beurlingSystem_rigidity_of_theta_relation` |
| Euler product and FE with defect `M` | open: primes fixed up to height `≍M^{−1/2}` | [L] `beurling_primes_of_critical_line_defect` |

So the only open barrier is a near-fake. Primes up to `M^{−1/2}` fix isolated zeros up to height `T≈M^{−1}`, using the camera at `λ>½` [D]. A family with a one-off off-line zero just above that height would kill every defect-stable argument for AAL. Size and perturbative tools would be out, and the proof would have to use the exact FE at all heights.

### The route it opens

**Recurrence as the shadow of Frobenius [D].** Over `𝔽_q`, zeros are periodic in `Im s` with period `2π/log q`, so AAL is automatic and all of Weil's content is ZAL. The impure Golden datum obeys AAL and fails ZAL [L datum, D reading]. Finite Euler carriers and Dirichlet polynomials are almost periodic, so their zeros recur [C]. Over ℤ, the flow `s↦s+iτ` has no period, and AAL asks how much of that periodicity survives.

- **Path:** off-line zero → returns → infinitely many zeros at the same depth → contradiction with ZAL or with zero density.
- **Established [L]:** transport of zeros along returns (`exists_zeta_zero_far_of_weaklyRecurrent`); flow/head-target transfer; density zero of returns.
- **Missing:** any lower bound on returns.
- **Ladder [D].** Let `e(ρ)` be the growth exponent of the return set. Zero density forces `e≤1−cd` at depth `d`. Any unbounded return set gives AAL for that zero. A return exponent above the density bound gives RH.

### Where the proof must be

| Layer | Content | Status |
|---|---|---|
| Typical heights | crystal, real zeros at critical scale, rate 2 for isolated zeros, local sign | closed, or assembly |
| Rare large heights | ZAL; `Λ_X log X→0` at every height forces it (`exists_depth_tendsto_zero_of_heatCoefficient`) | open, at least Lindelöf strength |
| One-offs | AAL | open, no estimate |

More typical-height theorems do not reach either open layer. On the ZAL layer the tool question is the bandwidth wall:
- Depth `b` is visible to second moments only at length `T^{1/(2b)}` (length–precision law [L]).
- Moments below bandwidth one stop at exceptional sets of size `T^{1−2b}`, the Density Hypothesis rate [D]. The hyperbolic theorem has reached that rate for isolated zeros [L].
- Excluding a single height needs bandwidth `1/(2b)` [D].

### First tests

1. **Near-fake trade-off.** How small can the FE defect be for a Beurling system with a one-off off-line zero? The two-sided bound decides whether AAL has a robust proof.
2. **Return lower bound in a model.** Prove returns for an off-line zero of an almost-periodic family with Gamma phase, then find where the tail of the Euler product breaks the argument.
3. **One quartet.** Assume exactly one off-line quartet. Then `ξ=ξ₀R` with `ξ₀` in the Laguerre–Pólya class, Lindelöf holds, and all but `(κ choose 2)` prime towers decide [K]. Look for a contradiction with the Dirichlet series, using incommensurability of `log p`.

### Validation

T1 passes: implied by RH, and it does not imply quasi-RH, since `limsup=sup>0` stays allowed. T2 and T3 pass. T5 passes: false on the Beurling fake and on `ξ·R` with rational `R`. T6 passes: transport, head-target transfer, rigidity and the finite-support consequences are the named inputs. T7 passes: no theorem answers it.

### Limits

- The evidence leans against an independent proof. The random Euler model has no zeros, and Deuring–Heilbronn repulsion points the other way [C]. A zero in a non-RH world may well be a one-off, so AAL may have no proof independent of RH. Test 1 is the check on this.
- ZAL remains at least Lindelöf strength. Answering this question does not finish RH.
- A near-fake does not refute AAL. It only bars robust proofs.

### Why the others rank lower

- **Past bandwidth one:** the tool question for ZAL, with no effect on the one-off layer.
- **A second expression with opposite sign (2.6.1):** RH-strength, so answering it is the proof.
- **HF compactness (2.5.4):** the most reachable, and it simplifies one large block, but it produces no sign and reaches no zero.
- **Cluster wall (2.5.3):** a classical advance, confined to typical heights.
