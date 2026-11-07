# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `a079423f8d` plus the working tree of 2026-11-07.

Evidence: `[L]` Lean source; `[S]` Lean source unfinished, unintegrated or uncommitted; `[K]` Lean with transitive axiom audit; `[D]` deduction, not a Lean theorem; `[N]` numerical, uncertified; `[C]` classical, not formalized.

**38 live formulations; 9 candidates.** HJ→PA; BSH→CDC; FEL's BSY criterion→CTF. Candidates: APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF.

## 1. Big picture

### 1.1 RH has two halves
RH ⇔ ZAL ∧ AAL [L]. ZAL says finitely many zeros lie beyond each positive depth and implies quasi-RH [L]. AAL says finitely many zeros right of `½+h` forces none. Failure of AAL implies `Θ<1`, so `qRH ∨ AAL` is a theorem [D]. Under AAL, RH ⇔ ZAL ⇔ finite off-line support ⇔ `κ(K_ζ)<∞` ⇔ bounded nonreal heat count ⇔ finite critical source energy ⇔ eventual Hadamard positivity ⇔ eventual central-gap budget [L]. Failure of AAL is exactly one rigid object: `ψ(x)−x=x^{Θ}T(log x)+O(x^{Θ−η})` with `T` a unique trigonometric polynomial, coefficients `−ord/(Θ+iμ)`, zero constant mode, `η≤Θ−Θ₂` sharp, and sign changes at bounded log gap [L]. It is also two-prime dilation annihilation of `ψ` [L].

### 1.2 The sign plane
On `PW_a`, Weil's form is diagonal in frequency: `Q(f)=∫|f̂|²W_N`, `W_N=Ω−2D_N`, `N=e^{2a}` [D], and `‖χ‖²Q(f)=∫Q(f∗χ̌_X)dX`. So sign is a function on the plane `(a,log X)`, the local onset field [L]. The corpus knows four curves on it:

| Curve | Statement | Evidence |
|---|---|---|
| All heights | Gamma base beats size: `a≈log log X−log 4` | [L] single-height form, [D] constant |
| Density `1−δ` | Every shape-bounded test positive up to `a=δ log T/(64M²)`, one exceptional set, no zero information | [L] |
| Visibility | Isolated depth `d` negative at `a≈(1/2d)log(4d log X)`; a cut crystal hides fixed depth to `(log T)/36`; `λ>1` gives sharp location | [L] |
| RH | `Ω≥0` everywhere | [L] |

Moments of `D_N` are Gaussian to order `k≈log T/(2A)`. That gives exceptional measure `T exp(−(log T/2A)log(log T/2A))`, which at `A=K log log T` is `T^{1−1/(2K)}`, and it reaches all heights only for `K<½`, below the size bound [D]. A zero of depth `d` at height `γ` forces a large value of a prime polynomial of length `(log γ)^{1/d}` [D]. No nontrivial sup bound exists between length `log t` and `exp((log t)^{2/3})` [D]. So all-height sign, zero-free regions and the width axis are one barrier, the **short-sum barrier**.

### 1.3 Window sign is one scalar flow, and contact is `Ψ` blowing up
The tower is a canonical system to contact with `H₁H₂=1`, no singular part and no atom at aperture 0 [L]. `L′=q−sinh 2L`, `(log K)′=2 cosh 2L` [L]. `r`, the traces and `Ψ` are absolutely continuous on compact precontact intervals, `q=Ψ′` is a function, and `q_y→q` in `L¹` [L]. For the actual chain, `|L(x)|≤artanh e^{−2(x−c)}+2 osc_{[c,x]}Ψ`, with no initial value, no `1/μ` and no derivative of `Ψ` [L]. Contact gives `limsup|r|=1` [L]. So **RH ⇔ `Ψ=½log H₁` is locally bounded on `[0,∞)`** [D]. All proved chart constants keep the ground energy of the top of the interval [L]. Prime thresholds are soft: `(Ψ(x)−Ψ(a))log(1/(x−a))→Λ(n)/√n` from the right [L]. A kick of this modulus cannot cause contact by size; in the Born model a collapse needs coherence over `≳√n` reflectors [L]. The proved margin ceiling forces `m≳e^{2a}`, above the Born bound `m≲ae^{a}`, so the actual `q` is a nonlinear response [D].

### 1.4 The certificate is causal, and the forward map has an exact tangent
A window is PD iff it has a predictor with positive margin whose polynomial has no zero in the closed disc, any sign pattern [L]. RH is existence of outer predictors for every window, lattice and nonzero test [L]. So RH is vanishing of an integer winding number on every lattice [D]. Reflection data are free coordinates; an echo train is passive iff each echo lies in its Schur band [L]. The forward map from primes is causal and injective, with exact tangent `∂E_n/∂λ(n₀)=−(2/√n₀)A_n(log n₀)`, `A_n` the autocorrelation of the predictor test [L]. Margins are concave in the weights [L]. The tangent of the potential carries `1/(1−γ_n²)`, and the Born defect is bounded by accumulated reflection `Π(1+|γ_k|)−1` [L]. On certified windows past `log 2` the whole chain is a theorem, with `Λ(2)` in the data [L]. So the size of the forward map at large `n` is what is unknown, and nothing else.

### 1.5 Why the datum is critical, and what compactness means
Slack `s>0` is Szegő's regime with square-summable reflectors; `s<0` has a finite negative witness; RH places every lattice at `s=0` with `Σγ²=∞` [L]. For every nonzero test `c_φ(t)↛0` [L]. In `ℓ²(zeros)` a profile decomposition is a theorem: bubbles interact through Bohr characters [L]. For ζ, RH ⇔ every orbit correlation is relatively compact ⇔ moving-bubble energies have nonnegative subsequential limits [L]. So Bohr compactness is an RH-level target, and the spectral side of compactness has no open content. RH is also existence of **any** real weight making each window nonnegative: the cone forces `Λ` afterwards [L]. So the sign can be stated with no primes in it, as a statement about Gamma, the pole and the set `log ℕ` [L].

### 1.6 One full-space problem reduces to one window
At fixed `R=c⁸/log N`: Γ-liminf with weight `α_R>0` at every `R` [L]; bounded form and masses make `L¹` limits strong [L]; prime form `≤εW₈+B_ε‖H‖²` [L]; coercive far complement for `R<R*` [L]. What stops the assembly above `R*` is a `W₈` Gårding bound. The term `C′R` is a Young trade on a rank-one pole cross term [L], and the prime term is infinitesimal in `W₈` [L]. The localization commutator is the one piece with no replacement. With that bound, a negative sequence has a strong nonzero limit on which the limit pencil is negative, and the limit pencil is a finite window of half-width of order `log R` [D]. So HF at each ratio is a rung of RW, and HF's all-ratio statement is `a*=⊤`.

### 1.7 The inner mass has a second expression, and its minimizer is forced
On `Re s>½`, `E` has inner factor exactly the Blaschke product of right zeros [L]. `exp(2I(1))=inf_Q∫|ζ exp Q(φ₁)|²dP₁` [L]. Near-extremal families have no freedom: `|EM_Q−1|²≤(B−1)|s−1|²/(2Re s−1)`, limit `1/E`, first coefficient `|q₁−(1−γ)|²≤B−1`, Bessel on all Taylor coefficients, every budget `≥|ρ|²/|ρ−1|²`, flatten law `∫||ζM|²/B−1|P₁≤2√(log B−2I(1))` [L]. Over a curve the extremal family is the damped Euler logarithm, and Castelnuovo is exactly the uniform bound `|P(v)/P(ρv)|²≤4^{rank}` on the dilation quotient; the golden curve has floor `φ²` [L]. So the mollifier is not what is missing. The missing input over ℤ is domination of `E(s)/E(s_ρ)`.

### 1.8 Finite rungs are theorems; they decide nothing
RH through height 67 is proved with no zero located [L]. It gives PF₂₀₀, PF₂₀₀ of the endpoint sequence, slices `|t|≤133/2`, Li `n≤314` and rank ten [L]. Window, Hausdorff, heat, Jensen and theta rungs have explicit heights [L]. The budget's left side is below a fixed constant while `½log(γ/2π)` grows, so it is a bounded-height method [D]. The floor tower stays below `0.3621` [L].

### 1.9 One Vinogradov–Korobov layer, and production is on it
AIP cost, SZ source, TT band, MC Hilbert form, WL energy, PTR depth, TH collar and integer stencils carry one VK saving and stop there [L]. `A(K)−1≤exp(−(log K)^α)` for every `α<3/5` at polynomial alphabet, read back as the VK zero-free region through the rate law [L]. Polynomial rate ⇔ fixed zero-free strip [L]. A constant window forces `c=mμ` there [L].

### 1.10 Linear exact identities are blind
A producer is a mollifier on `Re s=1` [L]. Exact integrality loses nothing, and the Chebyshev bound has a constant polynomial in the alphabet [L]. Yet the complete ledger of a zero mode vanishes for every balanced stencil, truncation `≤w/β` [L]. Ledgers against `Λ` and `−λΛ` differ by at most `2wψ(√n)` [L]. Positive Hecke combinations multiply the normalized slope by `1+a/j` [L]. The dual variables are fake prime measures, and the rate is not a capacity [L]. Sieve and producer cones are disjoint, and the factor 2 is the stencil read against Liouville sums [L]. Over `𝔽_q[T]` the Carlitz stencil of `1−qX` has rate 0 because norms are quantized; over ℤ every integer is a cut, and the rate is `≥cK^{−3/4}` [L]. Under RH the Möbius producer reaches a small exponent, while RH needs `a↑3/4` [D].

### 1.11 The near-line layer is one number
`T⁻¹∫_T^{2T}log|ζ(½+it)|dt→0` is equivalent to the Euler-mollified log-mean, the outer law, the dyadic moment, `100%` critical-scale clustering and three defect readings [L], and in Abel form to `I(½+x+it)→0` and to depth density `o(T)` [L]. Moment data alone give `I≤log(1+log 5x)+C` [L]. Selberg's mollifier gives `O(T)` [C]. Moments do not determine the log-mean, Jensen is sharp for moment data [L], and with polynomial mollifiers Jensen loses a positive constant [D]. Isolated zeros obey rate 2 without separation [L]. At simple right zeros `N(ρ)=exp(−Σ_{a≠ρ}m_aG(ρ,a))` [L]. The Carleson measure of ζ is controlled by `I` at every scale, with an embedding for coefficients of `A` [L]. The critical-scale crystal, reality and depth laws hold outside `δT` heights [L], with explicit exponent `1−κ³/41943040000` [L].

### 1.12 Long moments are rigid
Slope is exactly `2wθ`. A cofinal bound at any fixed `K` self-improves to `K=6`. RH reads at one point, in one bounded window, or as a positive proportion of every length-2 window [L]. Möbius polynomial zeros accumulate at every point of `Re s=Θ` [L].

### 1.13 Positivity lives inside one prime at a time
`S(a,b)=Π_pT_pA` with Eisenstein coefficients [L]. `A` is not a positive Laplace mixture [L]. Torus-positive amplitudes with left growth `κ<½` are exactly the exponentially convex ones [L]; `{2,3}` alone is strictly larger [L]. Signed columns add, products of columns are rigid, and the cone lies in its own dual [L]. An amplitude with a limit at height infinity gains nothing from locking; only amplitudes oscillating with the height to the end can gain [L]. `current=2|Ξ|²Re ξ′/ξ` [L]. The Gamma base pays by size when `Σlog p/(p^{½+a}−1)<½log(b/2π)`, and alignment below the base fails the current within `[B,BQ^{|S|}]` [L].

### 1.14 PM reaches the edge by unitarity and rings at every zero
Boundary norm gives `|ζ(1+it)|≥1/(6250t³log²t)` with no Euler-product inequality [L]. `V_p(ρ,Y)=2(1−p^{Re ρ−1})`, one-sided bound at one `p,Y` ⇔ RH [L]. `C*`-Hecke positivity and Schur positivity are blind to zero position [L]. `S(s)=φ(s)(s−1)/s` is a Blaschke product over `(1+ρ)/2` [L]. On the massless topological black hole with horizon `PSL₂(ℤ)\ℍ`, Eisenstein packets lift to exact solutions smooth across the horizon. Each zero gives one damped mode at rate `D+(1−β)/2`, the plus branch is silent, the reflected signal is pulse ∗ echo train, and universal damping ⇔ RH [L]. The geometry is locally AdS₄ in a Rindler wedge, the echo train is a cusp-channel image sum, and zeros enter only through the Eisenstein poles of the horizon [D]. Natural positivity of the Hartle–Hawking state is positivity of the density `1/|ξ(1+2iν)|²` on real `ν`, which is blind [D]. Any solution of the modular wave equation lifts to the black hole with no spectral assumption [S], and `E` and its jets grow polynomially on the lines and edges contour arguments use [L].

### 1.15 Recurrence and one-offs
Returns transport zeros [L]. A return on a disc in the upper quadrant is a simultaneous Kronecker return of all primes, paid by a spike of ζ near `1+iτ_j` [L]. A limit of translates on the upper quadrant fixes a point `ω` of the gauge torus, unitary and completely multiplicative, with `G=Σω(n)n^{−s}` on `Re s>1`: the limit set embeds in the torus and a return is the fibre over the identity [L]. Pair recurrence holds at density-`(1−δ)` base heights [L]. At a zero, returns are `≤T^θ` [L]. Truncated Euler products cannot return to a zero (Hurwitz), so a return at an off-line zero lives in the gap between ζ and every truncated product, on a density-zero set of times [D]. Golden has exact periodic returns, a right zero and fails the count: transport alone proves nothing [L].

### 1.16 ζ is isolated
A Beurling system whose FE has `L¹` defect `≤1/6400`, with the stated analytic hypotheses, has exact rational primes [L]. Residue is `½` with integers, or `2β≥√2` [L]. So near ζ, in this metric, there are no fakes. Rational quartet surgery keeps FE exact and line reality, and it destroys vertical Bohr almost periodicity on `Re s>1` and every absolutely convergent Dirichlet representation [L]. Continuous positive Beurling systems with one off-line pair exist at finite defect [L]. Degree-one Selberg class is `L(s+iθ,χ)` [L].

### 1.17 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| Markov, Perron, sign-gauge balance past `e^{−3/4}`, `log ρ` | refuted | [L] |
| Size-only payment of primes | ends before half-width `21/40` | [L] |
| Floor tower as aperture producer | stays below `0.3621` | [L] |
| Fixed theta heads; pointwise prime payment | no margin; fails at `log 6` | [L] |
| Positive Laplace mixtures for the theta amplitude | excluded | [L] |
| Fixed or limiting amplitude locking | adds nothing | [L] |
| Cancellation across independent reflectors at a fixed base | none: size is exact | [L] |
| Lions dichotomy for far translates | fails on every bubble | [L] |
| Parabolic structure as selector of `t=0` | blind | [L] |
| Central inequality as an RH-level target | stronger than RH | [L] |
| Barriers on prime sums; short detectors and weights | blind to purity; stop at the last scale | [L] |
| Moment data for the log-mean; coefficient norms for long moments | blind | [L] |
| Schur, `C*`-Hecke and raw-norm positivity as zero locators | blind | [L] |
| Full-determinant arithmetic reflection | none | [L] |
| Positive primes plus smooth integer count as AAL | false for continuous models | [L] |
| Invariant tensor weights; principal-branch endpoint signs; pure compression | false for Golden or RH-level | [L] |
| Finite-template, separable, finite-realization, tensor, integrality shortcuts | stated classes refuted | [L] |
| Integer stencils as a mechanism independent of Möbius | rate is the Mertens level; ledgers blind | [L] |
| Positive Hecke amplification of stencils | multiplies the slope by `1+a/j` | [L] |
| Capacity reading of the stencil rate | dual constraints are sawteeth | [L] |
| Raw echo decay | spikes defeat every pointwise exponential bound, independent of RH | [L] |
| Near-arithmetic ladders of zeros | excluded, `ℓ²` perturbation allowed | [L] |
| Rational relocation of zeros in the Dirichlet class | excluded | [L] |

## 2.1 Tasks that are just work

Difficulty is established only where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### Finite verification
| # | Task | Routes | Basis |
|---|---|---|---|
| A1 | Lean-certified `RHVerifiedThrough T` past 67 with actual zero location, first `T≈10²–10³` | all rungs | `hardySEM` sign chains exist; Turing count missing; Fejér budget is a bounded-height method |
| A2 | Numeric values of `windowHeight`, `xiMassHeight`, `heatGridHeight`, theta `D`; reduce toward `log(T₀/2π)≳2Σ_{n≤e^{2a+s}}Λ(n)/√n` | window routes, TH, LA, HCF | explicit definitions in Lean |
| A3 | Two-weight membership past `a₀`: odd unit window, `log 2`, `½log 5` | RW, OWU, EWU, ACT, SWC, HF | A1–A2, or rigorous Galerkin |
| A4 | Full-source theta rank 11 at every `0<a≤½` (unverified) | TH | core on `[1,5]`, Legendre kernel, height 67 |
| A5 | Lean certificate of the center-tail failure | TH | finite computation |
| A6 | Cone widths `𝒜(c)` past `c=0.66`; Lévy sector margins at `½log 3` | PBAP, ACS, RW, CHT | convex programs |
| A7 | Certificates on the nine anti-diagonals `{2,3,4,5,7,8,9,11,13}` | ACT | finite case analysis |
| A8 | Tate dimension-one sign from `log(9/2)` to `log(27/5)` | WTZ, CWS | one finite template decides every `A<log(27/5)` |

### Critical curve
| # | Task | Routes | Basis |
|---|---|---|---|
| A9 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | HF, SRT, AIP, ACS, SC | proved limits |
| A10 | Uniform Gårding at each fixed `R`: `Q(U)+B_R‖U‖²≥a_RW₈(U)` on normalized atomic sources (unverified; the one question of section 3) | HF, SRT, AIP, ACS | prime form infinitesimal in `W₈`; pole cross term rank one; Γ-liminf has `α_R>0`; commutator is the unverified piece |
| A11 | Compactness assembly: a negative sequence at ratio `R` has a strong nonzero limit with negative limit pencil, so sign at `R` follows from one window (given A10) | HF, SRT, AIP | Γ-liminf, strong-limit, tail, precompactness theorems |
| A12 | Low-packet/complement Schur payment on `0<R≤min(1,5R*/6)` (unverified) | HF, AIP | certified complement, low packet, polar capacity |
| A13 | Growing-period charges beyond gcd profiles; four-channel law at the critical scale (unverified) | AIP, HF | four channels close below the eighth root |
| A14 | Frequency-integral identity `‖χ‖²Q(f)=∫Q(f∗χ̌_X)dX` in Lean; replace Markov by Gaussian moments in the typical-height sign | RW, ACS, SRT | `MostHeightsAreWeilPositiveAtSmallAperture`, moments of `D_N` |

### Flow, near-line, continuation
| # | Task | Routes | Basis |
|---|---|---|---|
| A15 | Lean statement RH ⇔ `Ψ` locally bounded | RW, SZ | restoring bound, contact criterion, AC of `Ψ` |
| A16 | Numerical `r,m,q` for `a≤1` [N] | RW | Galerkin; not run |
| A17 | Selberg `O(T)` depth density in inner-field form, removing `log log` | WD, CTF, RW, ZCG | `exists_logIntegral_le_of_secondMoment`, twisted second moment to `21/50` |
| A18 | Twisted second moments past `21/50`: to `½`, Conrey `4/7` [C] | WD, census | raises rate `2θ` |
| A19 | Heat horizon from `6600/9991` toward its method floor | ZCG | profile margin, best exponent pair |
| A20 | Jensen rung toward saddle scale; constants in `300√(d log d)` (unverified) | LA, FFP | saddle identity |
| A21 | Census items; logarithmic two-point Chowla [C]; Voronoi; Zwegers [C]; runs past five | MC, ACS, census | classical |
| A22 | Hurwitz limit map: onto the torus on `Re s>1` by Kronecker [C]; uniqueness of the limit over a torus point on connected domains by the identity theorem | BAG, AAD | `exists_gauge_point` |

### Theta, reflection, weights, production
| # | Task | Routes | Basis |
|---|---|---|---|
| A23 | Certified scans of `S_S`; brackets for `S*(a,b)` from the mass bound, the alignment height and column minima | TH | column calculus |
| A24 | PM physical all-`n` Hecke moments beyond squarefree words (unverified) | PM, W1C | one-step isometry, prime-word moments |
| A25 | Ringdown for rapidly decreasing amplitudes, from polynomial jets on the contour lines at good heights; spin two (unverified) | PM | lift of any modular wave, polynomial growth of the Eisenstein function, sharp Bessel bounds |
| A26 | Lean dictionary: local AdS₄ isometry, cusp image sum for `K`, Lax–Phillips semigroup, Zagier–Sarnak horocycle criterion [C] | PM | echo train, causal symbol |
| A27 | Reciprocal quadric traces identified with vanishing-cycle Frobenius traces (unverified) | ACS, W4 | transverse form and quadric counts |
| A28 | Mixed Young projections at small rank (unverified) | ACS, W2 | column projections and PF₂₀₀ |
| A29 | Optimal `a(σ)` in `hasRate_of_power`; best exponent reached under RH (unverified) | WL, MC | `exists_moebius_producer_of_level` |
| A30 | Discrete Beurling system with a one-off pair, and its FE defect [C for the discretization] | BAG, ACS | `overRegularZeta`, random approximation |
| A31 | Graph model: `Γ\T_∞` for a curve over `𝔽_q`, scattering and ringdown, resonances at zeros of `ζ_C` [C] (unverified) | PM, CWS | see 2.7 |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window | RH; fixed length sub | all sign routes |
| B2 | Bounded oscillation of `Ψ` on every bounded aperture interval | RH | RW, SZ, CHT |
| B3 | Variation of `r` on bounded intervals, free of `1/μ` | sub | RW |
| B4 | Two-sector certificates; outer predictor at every window; every actual echo in its Schur band | RH | sign routes |
| B5 | Kick admission at every stage | RH as induction | RW, GWZ, WTZ, HF |
| B6 | Full-space sign eventually at every `K` | RH | HF, SRT, AIP |
| B7 | Growing families, moving frequencies, conductors past `(log N)^{13/32}`, outside the reach of A10 | sub | HF, AHD |
| B8 | Head thresholds for every `d` | RH | HF, AHD |
| B9 | No zero mode at any length | RH | HF, TG, SC, EHT |
| B10 | Top coprime stratum | RH | HF, ACS, ADT |
| B11 | Exact SOS on a two-prime lattice | RH | HF, SC, ACS |
| B12 | Index ceiling uniform in resolution | ≥qRH | CHMD, SRT, SC |
| B13 | Exclude finite nonzero off-line support | sub | whole programme |
| B14 | Window negativity exponent `<½`; any interior width value | ≥qRH | width axis |
| B15 | Past Vinogradov–Korobov: Mertens level, equivalently stencil rate, `α>3/5` | sub | every route |
| B16 | Decay law of `λ*(c)` | sub | CHT, RW |
| B17 | Signed ground-state structure past `log ρ` | method | EWU, OWU, RW, ACT |
| B18 | Prime-blind positivity on nonnegative blind mixtures | RH | RW, PBAP |
| B19 | Exact torus law for `S*(a,b)`; cross-chain positivity on small prime sets, first `{2,3}` | model | TH |
| B20 | Oscillation of the actual amplitude with the height, to the end | RH (all primes) | TH |
| B21 | All ranks at every `a` | RH | TH |
| B22 | Outer-root control of `R_d(Ξ)` | RH | LA |
| B23 | `N_d` bounded | ≥qRH | LA, FFP |
| B24 | Collision exclusion at small time, every height | RH | ZCG |
| B25 | Frequency `<1` at every putative collision | RH | ZCG |
| B26 | Arithmetic input distinguishing `Φ` among `Φe^{−τx²}` | method | ZCG, TH |
| B27 | Runs of `k` simple critical zeros, every `k` | sub | ZCG, census |
| B28 | Local Weil positivity at fixed `λ>0` on density-one heights | sub | RW, ZCG, WD, ACS |
| B29 | Cosine Laguerre sign below the VK boundary | RH | PTR |
| B30 | Heat grids at every degree; chirp bound or mean | RH | HCF |
| B31 | Hausdorff signs below the quadratic boundary; exterior diagonal; `TV(n)/qⁿ→0` | RH | PA |
| B32 | Covering every zero by a self-map disc | RH | XN |
| B33 | Cofinally small quartic charge | RH | GTA |
| B34 | `C_t` at every fixed `0<t<½` | RH | TT |
| B35 | Bound on the unnormalized prime wave; complete odd sign | RH | CHMD |
| B36 | Joint-node exclusion | RH | RN |
| B37 | Bounded `A_N`; rectangular Ward lower bound | RH | SZ |
| B38 | Cubic trace norm `<1`; bounded Gaussian oscillation | RH | TG |
| B39 | Damped coupling bound; sublinear tensor loss | RH | SC |
| B40 | Source-energy sign at every radius | RH | ACS |
| B41 | Source-work ceiling `≤2` | RH | HF |
| B42 | Complete-history floors | RH | FU, CFC, RP |
| B43 | Li budget or response floor | RH | LI |
| B44 | Retained-variance payment; one shift uniform in profile | RH | ACT, OWU, EWU |
| B45 | `C_σe^{2σr}` signed cost bound | RH | AIP |
| B46 | All-height one-sided bound for prime polynomials of length `(log X)^{2K}`, `K>1`: sign past the size curve | sub | RW, all rungs |
| B47 | All-height frequency input not reducible to size: multiplicity `o(log X)` | sub | ZCG |

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
| B55 | Any polynomial stencil rate (is qRH); rates `a↑3/4` (imply RH, not known implied by it) | ≥qRH to ≥RH | WL, MC |
| B56 | `Θ<1⇒Θ=½` | sub | whole programme |
| B57 | Log-mean of ζ on the line `→0`, equivalently depth density `o(T)` | sub | WD, census, MC, RW, ZCG, CTF |
| B58 | `D_win` | sub | WD |
| B59 | Cluster wall: Density Hypothesis rate for every near-line zero | sub | WD, ZCG |
| B60 | Exponential moments of the Green potential at deep zeros | sub | WD, MC, ADO |
| B61 | A detector past the last scale | sub | WD |
| B62 | Cofinal long moment; one-window bound; pronic tail | RH | WD, CTF |
| B63 | Collision-charge bound | RH | WD |
| B64 | Signed pair information beyond bandwidth one | sub | census, ACS |
| B65 | Genus upper law; logarithmic Serre duality; first Epstein real zero | indep. to sub | ACS |
| B66 | Near-unit budgets: dilation-quotient domination for `E` | RH | CTF, WD, AIF |
| B67 | Parity input in a ledger: a bound on `Σc(k)λ(k)L(⌊x/k⌋)` not reducible to Mertens | method | WL, MC |

### Γ — selection and reflection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B68 | Independent `D_s≥0`, Krein positivity or all-zero dispersion bound | RH | PM |
| B69 | Independent positive physical or graph carrier | producer | PM, W1C, PTR |
| B70 | Zero-free curve inside the strip from the carrier; lower bound for `V_p` | sub | PM |
| B71 | Sharp decay of the smoothed resonant sum; any uniform gap is ≥qRH | RH | PM |
| B72 | Cutoff-uniform target mass | RH | BAG |
| B73 | Factorial-Fock bound at actual zeros | RH | SEC |
| B74 | Proof-erasure equality at actual zeros | RH | CDC |
| B75 | Reflection-odd class vanishes at actual zeros | RH | PCS |
| B76 | FE-pair reality with coverage | RH | ZCG, ADO |
| B77 | `0∉E` | indep. | ADO |
| B78 | Rosati positivity of the window reflection | RH | HF, ACS, CWS, PM |
| B79 | Band holomorphy of `Λ(s)/Λ(s+1)` | RH | HF, ACS, SC, PM |
| B80 | FE twins with off-line zeros in the full class | sub | SEL |
| B81 | Candidate landings: APF full divisor, EGC height fibre, EWJ endpoint, FEL history, IRK projective lift, MSC Sonin sign, RFHM orientation, W1C producer, WBF arithmetic stream | producer | candidates |
| B82 | Inner-field decay `I(½+h+it)→0` | ≥qRH | BAG, AIF |
| B83 | AAL | sub | BAG, JAS, SC, whole programme |
| B84 | Smallest FE defect carrying a one-off, above the gap `1/6400` | method | BAG, ACS |
| B85 | Arithmetic global trace dominating local tensor moments; weight bound on a family containing ζ | RH | ACS, W4 |
| B86 | Mixed Young projections; positive arithmetic representation | RH | ACS, W2 |

## 2.3 Frankenstein routes

**No assembly closes RH.** Any assembly of proved parts whose remaining input follows from a theorem would make that input RH-equivalent. One assembly has RH as its output, and several collapse whole blocks.

| # | Parts | What the assembly gives | Missing input | Strength of the gain |
|---|---|---|---|---|
| F1 | **Split skeleton.** Any AAL producer (bounded two-prime cone, bounded prime towers, shell positivity infinitely often, bounded lags on one progression, twisted plateau sign) with any ZAL receiver (inner-field decay, `Φ_S≤Me^{au}`, heat coefficient `→0`, eventual Hadamard) | RH [L]. A sparse route blind to a non-attained top and a height-local route blind to finite exceptions cover each other's blind spot | One AAL input (B83) and one ZAL input (at least qRH) | The only assembly whose output is RH |
| F2 | AHD Γ-liminf and aliasing limit, CACT strong limits and tails, prime shifts infinitesimal, WTZ weighted floor, VHR window rung | HF at ratio `R` from one verified window [D] | A10 | Removes HF as an independent problem at every fixed ratio; HF all-ratio is `a*=⊤` |
| F3 | CSTW AC traces, anchor flow, contact criterion, AIF restoring bound | RH ⇔ `Ψ` locally bounded [D] | B2 | The whole tower is one local boundedness statement |
| F4 | ACS typical sign, AIF onset field, WVL visibility, ZCG sharp location, frequency integral | Global negativity at aperture `a` must be spectrally carried by exceptional heights; sign at unbounded aperture for all shaped tests [L/D] | B28, B46 | First sign past bounded aperture, on typical heights, for all tests at once |
| F5 | 8-way equivalence, Selberg tail moment, Euler-mollifier log-mean bound, prime field, Carleson measure, large-width inner field | Typical-height layer reduces to depth density `o(T)` [L] | B57 | One target for RW, ZCG, WD, CTF |
| F6 | `N(ρ)=exp(−ΣG)`, hyperbolic count, box budgets, long-mollifier residue bound, crowds rare | Deep zeros obey rate 2 or carry a large Green potential [L] | B60 | Density Hypothesis exponent near `½` |
| F7 | TH Euler product, PM scattering, FFP drift law, PTR at `h=½`, Lagarias–Suzuki line law | One edge theorem with several proofs on one Hermite–Biehler shift axis [D] | B68, B70 | One carrier; no interior gain |
| F8 | TH column calculus, ZCG carrier horizon, FFP forced drift | One inequality, sum of Euler column minima against the Gamma base, with both sides proved as brackets [L/D] | B19, B20 | Merges TH's wall with ZCG's |
| F9 | AAD rate law, Möbius producer, VK Mertens level | Stencils and zero-free regions are the same axis in both directions at exponent scale [L] | B15 | Closes production as an independent route |
| F10 | One verified height, all rungs | All finite rungs [L] | Nothing finite | Decides no all-rank statement |
| F11 | VK savings of all routes | One width axis [L] | B15 | They share one input |
| F12 | Attained-top consequences: finite oscillation, dilation annihilation, unbounded lags on every progression, unbounded towers, `|E_X|≥X^κ` off a vanishing set, top annihilators, twisted FE, zero-free strip, qRH | A contradiction search on one rigid world [L/D] | Any contradiction | Decides B83 if it succeeds |
| F13 | APD isolation, Hamburger rigidity, Bohr obstruction, Selberg degree-one classification | Every class of Euler product plus small-defect FE is a singleton [L] | B84 | Any stable argument in that metric is about ζ alone |
| F14 | Curve chain, Abel mollifier, near-extremal rigidity, Carleson measure | Over a curve: Castelnuovo ⇔ dilation bound ⇔ budgets reach 1 ⇔ unitary. Over ℤ: every piece except the dilation bound [L] | B66 | States exactly what a Castelnuovo over ℤ must assert |

**Closest to the open core: F1, then F12.** F1 says what a two-route proof looks like. F12 is the only place where a proof may assume a zero-free strip. F2 and F9 are collapses: they remove independent problems and do not advance the core.

### The hard half: what a contradiction search on ¬AAL may assume (F12, F13)

AAL is the exact split of RH, it is below qRH, and it has no estimate. It is the one place where a proof may assume all of this at once:

| In the world ¬AAL | Evidence |
|---|---|
| Zero-free strip `(β₁,Θ)` at all heights; `Θ<1`; finite top layer | [L] |
| `ψ(x)−x=x^{Θ}T(log x)+O(x^{Θ−η})`, `T` unique, coefficients `−ord/(Θ+iμ)`, zero constant mode, `η≤Θ−Θ₂` | [L] |
| `ψ(e^u)−e^u` changes sign at bounded log gap, amplitude `≥δe^{Θu}` | [L] |
| Dilation operators at two primes reduce `ψ` to `κx+O(x^{β−η})` | [L] |
| `Φ(mℓ)` unbounded above on every progression; `K_ζ` bounded on only finitely many prime towers | [L] |
| `|E_X|≥X^κ` off a vanishing set in every bounded window, `κ<w` | [L] |
| Finite annihilators nonvanishing on `Re s≤½`; twisted FE with phase `B²` | [L] |
| No returns at the top zero beyond a finite height | [L] |
| `Λ`-moments/`k!` at `ρ+1→−m`, diagonal `→0`, short shifts `→0`, long-shift correlation `→m²` | [L] |
| Every right zero is a Lefschetz ratio, and two primes determine it | [L] |

Exact form of the missing input [D]: suppose that at a zero `ρ` right of `½+h` one sequence `τ_j→∞` with `n^{−iτ_j}→1` for all `n` has translates bounded on a connected domain joining `ρ` to `Re s>1`. Then Montel, the identity theorem and Hurwitz copy `ρ` to unbounded heights, contradicting a finite layer. Kronecker supplies the phases, and boundedness along such a density-zero set of times is what is open.

Which inputs carry a one-off:

| Input class | Status | Evidence |
|---|---|---|
| Positive continuous prime measure, `N(x)−ρx−C→0` | one off-line pair, no recurrence | [L] |
| Euler product with positive generalized primes, small reciprocal mass | one-off pair exists | [L] |
| Discrete primes approximating a continuous measure; integer norms by rounding a smooth density | zeros right of `½` kept | [C]; [D] |
| FE with a finite coefficient prefix | zeros placed at will | [L] |
| Exact FE times a rational relocation | no Dirichlet series, not Bohr almost periodic | [L] |
| Exact Euler product and exact Riemann FE | only ζ | [L] |
| Euler product and FE with `L¹` defect `≤1/6400` | only ζ | [L] |
| Euler product and FE with larger `L¹` defect | open | B84 |

## 2.4 Wildly different routes

Each mechanism below avoids Σ payment, Π precision and Γ selection as stated. All are speculative. **W5, W6, W8 have no Lean content; W7 has only the Hermite–Biehler dictionary.** I see no route I would call promising; these are the ones with a concrete mechanism and a first test.

### W5. Extremal angle (Bethe / T-Q mechanism)
- **Idea.** Spectral determinants of PT-symmetric oscillators have real zeros with no self-adjoint operator and no positive form [C]. A second-order functional relation gives Bethe equations at the zeros, and Hadamard's product turns them into a contradiction at the extremal zero.
- **Exact form [D].** Put `z=(s−½)²`, `F(z)=Ξ(√z)`, of order `½`. Under ¬RH, `arg z` attains a maximum, since `arg z≈2d/t→0`. This top exists even when the horizontal top is not attained. For `|q|=1`, `q≠±1`, every Hadamard factor at that zero satisfies `|1−qz_k/z_n|≥|1−q̄z_k/z_n|`, strict for infinitely many `n`. So `|F(qz_k)|>|F(q̄z_k)|` there, while under RH equality holds at every zero. RH follows from one identity forcing equality at zeros.
- **Why the walls differ.** No payment, no window, no precision, no form. The input is an identity, not an estimate.
- **First test.** The constant-coefficient relation `ωF(qz)+F(q̄z)=TF(z)` fails on any polynomial with two nonzero coefficients unless `ωq^k+q^{−k}` is constant on the support [D]. So the relation must have nonconstant coefficients of equal modulus on a sector. Find such a relation for `L`-polynomials of curves. Hecke gives one in `z` at fixed `s`, not in `s`.
- **Risk.** ζ and its positive algebraic dilates are differentially independent over the Gamma–theta field [L]; complex rotations are outside that theorem. Every entire `F` satisfies a relation with interpolated `a`, so all content is in `|a|=|b|`.

### W6. Weighted homology of the prime complex
- **Idea.** `M(N)` is the reduced Euler characteristic of a wedge of spheres indexed by odd squarefree `m∈(N/2,N]` [L]. Betti numbers are `≈cN` and the Euler characteristic is conjecturally `√N`, so all cancellation is between dimensions. Over `𝔽_q`, Möbius sums are traces of Frobenius on sign-twisted cohomology of configuration spaces, with few classes of large weight [C].
- **Target.** A filtration of the prime complex by log height, whose spectral sequence pairs classes of opposite parity, with a weight on each surviving class.
- **Why the walls differ.** Cancellation becomes exactness of a differential, not an estimate on primes.
- **First test.** Reproduce `M_C(n)` for a genus-`g` curve from a filtered complex over `𝔽_q[T]`, then compute the first page over ℤ at small `N`.
- **Risk.** Parity swaps must preserve size: prime splitting `p↦qr`, `qr≈p`. Counts of primes and semiprimes differ, so pairing needs the full Koszul structure. Betti numbers are forced large in the simplicial model, so a different complex is needed. No Frobenius exists to supply the weights.

### W7. Interlacing families (mixed characteristic polynomials)
- **Idea.** Mixed characteristic polynomials of PSD matrices are real-rooted by real stability, with no eigenvalue estimate [C].
- **Target.** Exhibit `R_d(Ξ)` or its Hankel as such a polynomial, built from first atoms, PD at every rank [L].
- **Why the walls differ.** No inequality is paid. The unstable pieces in the finite free calculus [L] are factorwise splits, not mixed forms.
- **First test.** Degree `d=3,4`: are the Taylor coefficients mixed discriminants of explicit PSD matrices?
- **Risk.** A Hilbert–Pólya realization in finite-dimensional dress.

### W8. Renormalization of the horocycle flow
- **Idea.** RH is the sharp rate `y^{3/4−ε}` of equidistribution of long closed horocycles on `PSL₂(ℤ)\ℍ` [C], a statement absent from the corpus. The geodesic flow renormalizes the horocycle flow, and deviation exponents are Lyapunov exponents of a cocycle on a Sobolev bundle [C for compact and flat cases].
- **Target.** A cusp-channel renormalization cocycle whose Lyapunov exponent on the Eisenstein part is pinned to `¼`, and a sum formula of Eskin–Kontsevich–Zorich type playing the role of the log-mean.
- **Why the walls differ.** Dynamics of a parabolic flow, not a form, a window or a moment. Lyapunov sums are computed by geometry.
- **First test.** The tree quotient over a curve (A31), where the exponent is known by Weil.
- **Risk.** Generic Fuchsian groups have resonances off any line [C], so Hecke must enter. It may reduce to cusp scattering (PM).

### Formalized lines with walls of their own

| Line | Established [L] | Boundary [L] | Open core |
|---|---|---|---|
| W2 Representation | Coherent central class functions with Gram positivity ⇔ RH; positive real-part character with transposition defect `Σ(Im α_ρ)²/p₁²`; column Young projections nonnegative; endpoint Toeplitz minors of order `≤200` nonnegative | Sorted occupancy and finite partition stabilizers fail; generic common-pivot tests pass non-characters | Positive arithmetic representation with prescribed cycles (B86) |
| W3 Exact extremal | Real exponentially decaying `Φ=Ξg`, blind at every `log n`, zero pole–archimedean energy; tail exponent 1 attained | `kb≤2` for full `Ξ^k` divisor; no strict energy on blind tests | Positivity of the whole blind program (B18): a Cohn–Elkies-type linear program with an exact extremizer and no dual certificate |
| W4 Weight on a family | Tensor-uniform growth ⇔ purity; nonnegative global trace bounds negative spectrum; Kloosterman fibres pure by Stepanov; explicit moment counts and Tate corrections | Golden has correct invariant weights and full `SL₂` image; pure compression preserves even subspace iff RH | Arithmetic family and global trace (B85) |

### Tested and rejected forms
| Form | Reason | Evidence |
|---|---|---|
| Lee–Yang lift on the prime torus | requires Gamma speed above the total Euler speed, which diverges; agrees with forced drift `θ_S/2` and columns add | [D]/[L] |
| Stable Dirichlet polynomial with critical zeros among ζ zeros | Herglotz carrier rigidity forbids it | [L] |
| Arithmetic capacity for the stencil rate | dual constraints are sawteeth; the capacity ceiling `e^{−0.87n}` is passed by stencils | [L] |
| Newton polygon or tropical separation of zeros, as for Goss zeta [C] | Taylor ratio `a_k²/(a_{k−1}a_{k+1})→1`, while separation needs `4`; arithmetic spacing has no geometric gap | [D] |
| Kac–Murdock–Szegő count of negative directions | symbol bandwidth equals test bandwidth, and `W_N<0` on a large set coexists with sign | [D] |
| Comb or crystalline rigidity of the zero divisor | needs zero-side positivity, which is RH | [D] |

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

### Primary: is the depth density `o(T)`? (B57)
**Question.** Does `Σ_{0<γ≤T,β>½}m_ρ(β−½)=o(T)`? Equivalently `T⁻¹∫_T^{2T}log|ζ(½+it)|dt→0`, equivalently `I(½+x+it)→0`.

- **Why it matters.** It is `100%` critical-scale clustering, the Euler-mollified log-mean, the outer law, the dyadic depth, Hecke and theta readings, and the Abel inner mass at infinity [L]. By the depth law it is reality at every `τ>0` on density-one windows outside crowds [D]. It gives local Weil positivity at fixed `λ` on density-one heights (B28) [D]. It closes the typical-height layer for RW, ZCG, WD and CTF together, and it is the mean damping law of the ringdown: the frequency average of `|κ−¼|` is `o(1/log T)` [D].
- **Where it stands.** Empty mollifier: `O(T log log T)` [L]. Selberg's mollifier: `O(T)` [C]. Under RH: `O(log T)`, while `log|ζ|` has variance `½log log T`.
- **The tool gap.** A second moment cannot reach it: a polynomial mollifier leaves the moment above `1+1/(8+6θ)` [L], and moments do not determine the log-mean [L]. Moment `→1` needs superpolynomial length, `log N≥log²T/(6K₀)` [L], while `log N=o(T)` suffices [L]. The target is a second moment beyond every known off-diagonal range for a structured mollifier, or a sharp log-mean by another route. The natural input is `log|ζ|=Re P+` bounded error [L], with the mean of the error reduced from bounded to `o(1)`.
- **Tests.** T1–T4, T7 pass. T5: false on `ζ(s)(1−cp₀^{−s})`, `c>√p₀`, where the mean tends to `log(c/√p₀)>0` [L]. T6: prime field, long-mollifier ceiling, tail moment, Carleson embedding.
- **Limit.** Sparse off-line zeros survive; rare large heights untouched.

### Alternatives, by route
| Route | Question | Why it matters | Tests | Limit |
|---|---|---|---|---|
| WD | Cluster wall: mean of `exp(2Σ_{a≠ρ}m_aG(ρ,a))` over zeros of depth `≈α/L` is `≤e^{εα}`, giving `N(½+α/L,T)≪_εTLe^{−(2−ε)α}` (B59, B60) | No further analytic input stands between it and the Density Hypothesis near `½` [L] | All pass. T5: impure column has fraction `≈1/A` at depth `A/L` | One-log loss; no `D_win`; sparse zeros survive |
| PM | Explicit `η(γ)>0` with `V_p(ρ,Y)≥η(γ)` at every resonance, from the Hecke action with no Euler-product inequality (B70) | Zero-free curve `β≤1−η/(2log p)` from the carrier: the first interior information of its kind | All pass. T5: Blaschke insertion preserves Schur forms, so actual Whittaker data must enter | A curve of classical shape at best |
| RW | Variation of `r` free of `1/μ` (B3) | Every contact of finite order, step `a*≥a+c(1−r²)/C` | T2, T3, T7 pass. T5 fails: a structural bound holds for fakes | Permits contact; produces no sign |
| TH | Exact law for `S*(a,b)`; complete `{2,3}`-smooth spectrum positive at every `0<a<½` (B19) | First cross-chain theorem; merges TH with ZCG's carrier horizon | T2, T3, T7 pass. Model source | Says nothing above `S*` |
| ZCG | Multiplicity `o(log X)` by a non-size input (B47) | First all-height input not reducible to size | T1: RH gives `≪log X/log log X` [C]; T2–T4, T7 pass. T5: FE twins | Bounds collisions, does not exclude them |
| RW, all rungs | One-sided bound for prime polynomials of length `(log X)^{2K}`, `K>1`, at all heights (B46) | First all-height sign past size; `windowHeight(a)≈exp(e^{a/K})`, so `a*≥K log log T₀`, all rungs amplified [D] | T1: not known to imply qRH: cut crystal blocks the deduction [L]. T2–T4 pass. T5: columns of depth `>1/(2K)` violate it. T6: short-sum barrier | Finite rungs amplified, still rungs |

## 2.6 If positivity, Weil positivity and spectral methods are excluded

**What survives** [L]:

| Class | Receivers | Sign-free input proved |
|---|---|---|
| Production | Siegel and Liouville halves, stencils, one-sided counts as `ψ(x)` bounds | exact integrality; VK-scale rate; Stepanov chain over `𝔽_q` |
| Transport | Strong and weak recurrence, target mass, AAL | pair returns at typical base; zero-disc transport; returns are prime returns |
| Cancellation | `M(x)`, one-point and one-window forms, long moments, Báez-Duarte | VK; last-scale and length laws |
| Dominance | Finite carriers real above horizon; heat horizon | Gamma speed beats finite Euler speed |
| Identification | Cameras, sharp location, FE-pair flatness | sign-free readout conditional on isolation |
| Rigidity | Exact FE forces primes; `1/6400` gap; Selberg-class discrepancy; Hamburger uniqueness | zero defect ⇒ rational primes |

All of Σ falls, with PM's Krein branch, TH, W2, W3 and the index routes.

**The natural door under this exclusion is closed.** Over `𝔽_q` a proof with this profile exists: Stepanov's, producer → count → purity. Over ℤ the Stepanov object is a stencil, and its rate is the Mertens level in both directions at exponent scale [L]; a constant window is Möbius [L]; floor-sum ledgers are blind to every zero [L] and to the Liouville twin below `w√n` [L]; positive Hecke action never improves it [L]. So the Stepanov template yields a restatement of cancellation, unless something other than a linear floor identity enters. The one thing Frobenius gives over `𝔽_q`, quantized norms with no sawtooth, has no analogue here [L].

**The question.** *Is there an identity at the zeros of ξ that relates two rotated values with equal modulus?* Precisely: with `w=−(s−½)²`, `Q(α²)=XiC α`, are there `q` on the unit circle with `Im q>0`, and arithmetically defined entire `a,b,T` with `|a|=|b|` on a sector containing the zeros and `a(w)≠0` at those zeros, such that `TQ(w)=a(w)Q(qw)+b(w)Q(q̄w)`?

**Necessary correction [K].** Without coefficient nonvanishing, every entire `F` satisfies the relation with `a=b=F`, `T=F(q·)+F(q̄·)`. Even `F(0)=a(0)=b(0)=1` permits an off-axis zero with unequal rotated moduli. The exact local alternative and quantitative residual bound are formalized in `RAC:RotatedRelationsNeedNonvanishingCoefficients`; see [the scoped refutation](../../drafts/pipeline/5-failed/rotated-relations-with-unrestricted-balanced-coefficients.md).

**Why it opens the path.**
- At a zero of maximal positive angle, Hadamard factors compare weakly in the same direction, with a strict factor, giving `|Q(qw_k)|>|Q(q̄w_k)|` [D]. Balanced nonzero coefficients would force equality. The factor identity is oriented: its squared-modulus difference is `4 Im(q) Im(w_k/w_n)` [K].
- No form, no sign of an energy, no spectrum, no estimate on primes. It uses Hadamard's product and an identity. It is the only proof shape for real zeros without a positive form, besides Stepanov [C].
- A refutation in a named coefficient class excludes only that class of rotated identities.

**Tests.** The repaired relation is RH-sufficient by the extremal-product argument [D]; the unrestricted relation is not. Construct or refute it in a specified coefficient class, including nonvanishing. `AlgebraicDilationThetaGammaIndependence` [L] constrains some classes. Bare modulus equality at zeros is RH itself, so the content must be an arithmetic construction of the coefficients and proof of their nonvanishing.

**Limit.** Hecke relations act in `z∈ℍ` at fixed `s`. Rotation in `−(s−½)²` has no known arithmetic meaning. Exclusions for a particular coefficient class do not exclude arbitrary arithmetic identities.

**Second door.** AAL (B83) is sign-free in its prime-side form. It covers the half that a count cannot reach.

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved.** The setting is an exact solution: metric, conformal coupling, Neumann and Dirichlet lifts, smoothness across the horizon, echo train, causal symbol, one mode per zero, universal damping ⇔ RH [L]. The radial problem is exact Pöschl–Teller, and zeros enter as resonances of the wave equation on the horizon `Γ\ℍ` [D]. The geometry is locally AdS₄; the delays `2log c` are cusp-to-cusp lengths of `Γ` [D].

**What physics does not give.** Causality puts poles in the lower half-plane. Unitarity gives the edge `Re s=1` [L]. KMS, reflection and Tomita positivity are positivity of a real spectral density, and they are blind, in the same way `C*`-Hecke positivity is proved blind [L/D]. Lyapunov exponents and energy decay are lower-rate statements; a generic Fuchsian horizon has resonances off the line [C], so the phenomenon depends on Hecke.

**The question.** *On the function-field black hole, can universal damping be derived from the wave dynamics, without Weil's theorem?* Take a curve `C` over `𝔽_q` and `Γ=GL₂(𝔽_q[C−∞])`, acting on the Bruhat–Tits tree `T_∞`. `Γ\T_∞` is a graph with cusps [C]. The wave equation on it is an exact discrete system with a causal scattering matrix whose resonances are the zeros of `ζ_C` [C]. Universal damping there is a theorem, by Weil. Is there a proof of it from energy flux at the cusps, Hecke correspondences at other places acting as exact symmetries, and unitarity alone?

**Why it opens the path.**
- It is decidable and honest: RH is known there, so a derivation exposes the physical law and a refutation shows that the physical reading is a reformulation, ending that branch.
- It names the law to look for. Castelnuovo is the dilation bound `|P(v)/P(ρv)|²≤4^{rank}` [L]. On the horizon, `P(ρv)` is the response with extra damping. So the candidate law is **damping domination**: adding uniform damping never amplifies a mode's response by more than a fixed factor, with a mean tending to 1. A physical proof of that on the graph is a proof of Castelnuovo.
- It transports. The modular horizon has the same scattering form, the same Hecke action by the Toeplitz symbol `p^u+p^{−u}`, the same model-space picture [L/D]. The only obstruction to transport is rank, since the dilation product has infinitely many factors, which is B66 stated physically.

**Tests.** T1: not RH; it is a theorem about curves with an open method. T2: a stated derivation or a stated obstruction. T3: yes in both directions. T4: all curves, all genus. T5: Golden has no tree lattice, and an argument must use the lattice. T6: curve chain, Abel mollifier, `V_p`, one-step isometry [L]. T7: passes.

**Second physical question.** Off-line resonances carry strictly negative Krein value `D_s<0` [L]. A negative-energy mode in a system with non-negative dissipation cannot decay (Thomson–Tait–Chetaev) [C]. Is there a flux law `d/dτ Q=−𝓕` for the physical Krein square, with `𝓕` a manifest boundary square? If yes, RH. If no, the Krein form is not a dissipated energy, and PM's Krein branch has no physical reading. The physical energy is positive and gives no constraint; the question is about the Krein form alone.

**Limit.** Function-field scattering is finite-dimensional per cusp. The infinite rank over ℤ may be the entire difficulty.

## 2.8a If RH is a problem of topology or geometry: question

**What is proved.** RR holds at every aperture on the source cone [L]. Bézout ⇔ RH [L]. Primitive `h¹` is coercive for `a≤181/500` [L]. Bidegree counts see no primitive class, and fixed-rank lattice counts violate surface RI [L]. Curve windows: Künneth effectivity ⇔ unitarity [L]. `M(N)` is an Euler characteristic [L]. RH is vanishing of a winding number on every lattice [L/D], and the index counts critical lengths, so right zeros are walls in a connected family [L].

**Where geometry enters Weil's proof.** Riemann–Roch gives `h⁰>0`. A section has an actual divisor. An actual divisor meets an ample curve in a nonnegative number of points. The last step is a count, not an inequality. Over ℤ the first step exists, and the second and third do not.

**The question.** *Does Bézout have a zero-count proof: is there a section space `H⁰(x)` on the scaling surface, of dimension given by the proved RR and reading the primitive component of `x`, such that the restriction of a nonzero section to the ample class has a nonnegative zero count equal to `x·A`?*

**Why it opens the path.**
- Bézout is RH [L]. A zero count needs no sign. It would replace every signed estimate of the Σ family by one structural fact.
- It is a precise specification: an infinite-rank count, since fixed rank is excluded [L]; reading the test beyond its two degrees [L]; exact RR; Hecke similitude `h¹_prim→b h¹_prim` [L].
- Natural candidates exist with real zeros already: self-reciprocal companions of outer predictors have all zeros on the circle [L], and at contact the zero mode has only real zeros [D]. So the zero count is available for the window sections, and what is missing is its identification with the intersection number.

**Tests.** T1: implies RH, not an RH restatement: existence of a section theory is a stronger structure. T2: construct, or prove no such space with these properties exists. T3: RH. T4: passes. T5: Golden has correct invariant weights and fails purity [L], so the theory must fail there. T6: source cone, RR, curve calibration `deg(m−nF)=N₁` at genus one [L]. T7: passes.

**Limit.** An effective cone exists abstractly and Bézout remains RH-level [L]. So everything is in the words "actual zero count". If the count is only defined through `Q`, the statement is empty.

## 2.8b Does closing RH need a new field?

No theorem says so. The evidence is structural: every available tool stops for a proved reason.

| Tool | Why it stops |
|---|---|
| Size estimates | die before half-width `21/40`; exact across independent reflectors; all-height sign stops at `a≈log log X` |
| Positivity-preserving (Markov, Perron) | frustration past `log ρ` |
| Type I/II sieve data | parity blind |
| Linear floor identities | blind to every zero; rate is the Mertens level |
| Barriers, distribution of prime sums | blind to purity |
| Short mollifiers and weights | last-scale floor |
| Second moments for the log-mean | Jensen is sharp for moment data |
| Concentration-compactness | far bubbles do not decouple; spectral profile decomposition is RH-free and decides nothing |
| Finite computation | finite rungs decide nothing |
| Tensor amplification | carries RH unchanged |
| Integrality | amplifies; no rate |
| Parabolic monotonicity | blind to `t=0` |
| Unitarity, Schur, `C*` and KMS positivity | reach only the edge; blind to zero position |
| Fixed-amplitude Euler positivity | Laplace cone; columns add |

**What is already built does not reach the remainder.** Arithmetic inner-function theory exists as a programme, and it is one-dimensional: one half-plane, one causal order by `log n`, one reflector per step. So are the canonical chain, lattice Schur theory, critical Hardy theory and the curve chain. The walls that remain concern many independent primes at finite height, and those theories cannot state them.

**The proposal: prime torus theory.** Over `𝔽_q` the phases are one coordinate: `q^{−s}` is periodic, there is one column, and Schur parameters, Castelnuovo and the Carlitz stencil all close [L]. Over ℤ the coordinates `p^{−s}` are independent. The height `t` moves one point `ω_t=(p^{−it})_p` along a dense one-parameter subgroup of the infinite torus `𝕋^∞`, and the Gamma base sees only `t`. The field studies the pair `(t,ω_t)` **at finite time**. No programme has this as its object. The gauge torus spectrum, the Wiener monoid with its Bohr points, the torus scans of TH and multiplicative Bochner theory have no time coordinate. Recurrence and the first-return bound of auxiliary dynamics have one, for returns to the identity only.

**The walls as statements about the orbit.**

| Wall | Statement on the orbit | Evidence |
|---|---|---|
| Fixed-amplitude locking; columns add | For a fixed function the infimum over the orbit is the infimum over the torus. This is Bohr's isometry for bounded Dirichlet series. | [L]; [C] |
| Arithmetic Bernstein | Torus-positive amplitudes are the exponentially convex ones below growth `κ=½`; `κ=½` is the density of the primes and `A` sits exactly there | [L] |
| Base against columns | A race: the base `½log t` against the time the orbit needs to align. Above the horizon the base wins on the whole torus. | [L] |
| Short-sum barrier | How long until the orbit enters `{Σ_{p≤y}p^{−½}Re ω_p≥V}`? Diagonal moments see nothing once `π(y)` passes `log T`. | [D] |
| Parity | The Liouville twin is the orbit translated by the point `−1`, so an argument invariant under torus translation cannot separate the two. The asymmetry is the start of the orbit: `ω_0=1`, the pole. | [D]; flips [L] |
| Mertens, zero-free regions | Halász: `M(x)` is small while the orbit stays far from `−1` in a weighted distance. `3+4cos+cos2` is doubling `ω↦ω²`, available because the orbit is a group. | [C] |
| Returns, AAL | Limits of translates embed in the torus; a return is the fibre over the identity, paid by a spike near the pole | [L] |
| Zeros in the hull | Haar-typical points carry no zero (Bohr–Jessen), so zeros sit over a Haar-null set | [C]; [D] |
| Strip off the domain | Point evaluations of the Bohr lift exist on `𝔻^∞∩ℓ²`, which on the orbit is `Re s>1`. The strip exists by continuation only, and truncated products never vanish. | [C]; [D] |
| Coupling frequencies | Several primes, heights or harmonics in one positive certificate never beat the single-frequency ratio: `a(γ)≤2a(0)` | [L] |
| Castelnuovo | The dilation bound is `4^{rank}`, and the rank over ℤ is infinite | [L] |

| Aspect | Content |
|---|---|
| Objects | `X=[1,∞)×𝕋^∞` with the orbit; truncated orbit `O_T(y)` on primes `≤y`; alignment time `τ_y(R)`; return Bohr sets; near-diagonal energy `E_k(y,T)`, the pairs of `k`-fold products of primes `≤y` with `|log(a/b)|≤1/T`; exceptional heights as approximate groups; the hull over the torus; amplitudes depending on `t` |
| Language | alignment, race, corners `+1` and `−1`, fibre, time to reach, mixing time `e^{π(y)}`, below-mixing regime, height coupling |
| Mechanisms | group closure (`ω_{t+t′}=ω_tω_{t′}`, so differences of large-value heights are partly aligned, as in Halász–Montgomery and Guth–Maynard [C]); the cost of a return [L]; off-diagonal energy past the diagonal range, which is `y`-smooth numbers in short intervals [C in part]; positivity with coefficients depending on `t` |
| Tools to build | a non-alignment theorem below the mixing time; a bound on `E_k(y,T)` for `k≫log T/log y`; discrepancy of the orbit against Haar measure at time `T` for `y>log T`; a transfer from typical to rare heights; sum-of-squares certificates on `X` with kernel-valued prime conductances |
| Test cases | curves (rank one, periodic flow); Golden (rank one, wrong weights); commensurable steps, which have unbounded room in one column [L]; continuous Beurling systems, which have no torus since `ζ_B→1` vertically [L]; integer-norm systems, which share the torus and differ in amplitude [D] |

The last tool has a concrete first form [D, untested]. Frustration is a theorem about scalar conductances [L]. On the half-plane, `(1−p^{−x})/x` with `x=s+s̄′−1` is the Laplace transform of a delay line of length `log p`, and an Agler-type decomposition [C on the polydisc] would write the scattering kernel `(1−S(s)conj S(s′))/x` as `Σ_p((1−p^{−x})/x)K_p(s,s′)` plus an archimedean term, with `K_p` positive semidefinite. That is energy paid prime by prime, with kernel-valued weights where sign gauges fail. First test: two primes against a Gamma-like factor.

**Criteria it must meet.**
- Reduces to Schur, Castelnuovo and periodic flow at rank one.
- Not invariant under torus translation: it must see the start of the orbit.
- Pays past the Kronecker scale, at unbounded aperture and length.
- Sees incommensurability: commensurable steps behave differently [L].
- False on impure columns, Golden and heated kernels. Against integer-norm systems it must fail through the amplitude, since the torus is the same.

**Questions it must answer.**
- How long does the orbit need to enter a half-space at length `y=(log T)^{2K}`, `K>½`? Is there any saving against size?
- What is the near-diagonal energy past `k=log T/log y`?
- Why does the Gamma coupling sit at exactly the critical growth `κ=½` of the Bernstein theorem?
- Which functions on `X` restrict to the Ξ-current and have a sum-of-squares form with `t`-dependent coefficients?
- Over which torus points does the hull extend into the strip, and which of those carry zeros?
- Does a large-value set of heights have additive structure, and does its structure force returns that the pole must pay for?

**Limits.**
- For a Dirichlet series the supremum on the orbit equals the supremum on the torus, so every gain must come from finite time or from the Gamma coupling [C].
- Sz.-Nagy already dilates the one-parameter flow. Ando–Varopoulos failures for three commuting contractions apply only to decoupled primes, not to the actual chain [C; D].
- A non-alignment theorem speaks about large heights only. A one-off at fixed height is invisible to it, and a discrete system with integer norms built by rounding a smooth density shares the torus and can carry a one-off [D]. So this field does not reach AAL without an input from the amplitude or the functional equation.
- Non-alignment gives the sign past size, which is a zero-free strip up to crystal shielding [D]. The field's first theorem would be qRH-strength; nothing below that is a test of it, apart from curves and models.
- No mechanism past diagonal moments is known. Baker's bounds are exponentially too weak for the transference [D].

## 2.9 If positivity, Weil positivity and spectral methods are excluded: which field?

If the exclusion holds, inner-function theory and the positivity half of prime torus theory lose their core, since a Blaschke mass is a positive quantity and a passive medium is a positive form. Stepanov over ℤ, as a linear stencil theory, has closed. The field must be nonlinear in the primes.

**What it would be about.** *Rigid arithmetic of cuts:* how an exact statement about one object, `N(x)=⌊x⌋`, forces its zeros, by operations that have no sign and are not linear floor identities. All multiplicity of a stencil lives in fractional parts [L]. Every integer is a cut. The object is single: within FE defect `1/6400` there is nothing else [L]. So this field has no deformation theory near its object, and its theorems concern one function.

| Aspect | Content |
|---|---|
| Objects | sawteeth `r mod k`; fake prime measures; ledgers; finite oscillations; dilation operators on `ψ`; return sets as Bohr sets; gauge torus with Adams operators; the Beurling space with the FE-defect metric; the zero of maximal angle |
| Language | cut; multiplicity against size; ledger; blindness; parity ledger; oscillation; annihilator; transport; isolation; extremal position in place of sign |
| Mechanisms | exact identities; extremal-factor modulus at the maximal-angle zero; rigidity as uniqueness; transport by minimum modulus; Gamma speed as dominance; nonlinear ledgers mixing additive and multiplicative structure |
| Tools to build | ledgers that are not blind: quantities nonlinear in `Λ`, since every linear floor functional annihilates zero modes [L]; a parity input in the term `Σc(k)λ(k)L(⌊x/k⌋)`; effective Kronecker at arithmetic scale; pointwise bounds below the VK length; a metric geometry of Beurling systems above the gap |
| Test cases | Weil for curves through Stepanov and the Carlitz stencil [L]; Kloosterman data; continuous Beurling systems, which must fail construction [L]; Golden, which obeys transport and fails construction [L] |

**Criteria it must meet.**
- Uses no quadratic form with a sign, no self-adjoint operator.
- Proves Hasse–Weil over `𝔽_q` in the same language [L for split hyperelliptic curves].
- Distinguishes rational primes from continuous and discrete Beurling systems.
- Breaks parity: passes the Liouville twin and the filters on Type I and II data [L].
- Is not blind to zero modes, which excludes every functional linear in `ψ` read through floors [L].

**Questions it must answer.**
- What replaces Frobenius? Over `𝔽_q[T]`, quantized norms mean a stencil is cut only at a degree boundary and the rate is 0 [L]. Over ℤ what removes the sawtooth?
- What nonlinear functional of `Λ` sees a zero mode, and survives the Liouville twin? Selberg's `Λ∗Λ` sees it through a pole, consistent with any meromorphic world [D].
- Why do primes recur at a zero, if they do? They must, on any bounded return [L]; the tail is what fails.
- Is a single off-line zero a contradiction with `N(x)=⌊x⌋`? Analytic identities are consistent with one [D], so the contradiction, if any, needs arithmetic information not implied by meromorphy.
- What is the fake prime measure closest to the true one, for each `K`?

**Limits.**
- Nothing in the corpus shows the exclusion is forced. Over `𝔽_q` both Hodge index and Stepanov prove the theorem.
- No source produces parity-breaking at any power saving.
- The field has no named mechanism above VK.

## 2.10 If RH is a physical phenomenon in AdS with a modular horizon: which field?

**What it would be about.** *Arithmetic scattering holography:* wave dynamics on quotients of AdS by arithmetic groups, with Hecke correspondences as exact non-local symmetries, and with the finite places included as trees. The bulk is adelic: `Γ\(ℍ×Π_pT_p)` with radial AdS direction [D]. Hecke `T_p` is translation on the tree at `p`. Zeros are resonances of the horizon, and RH is one universal relaxation rate.

| Aspect | Content |
|---|---|
| Objects | modular horizon; radial Pöschl–Teller tower; causal symbol; echo train as image sum; resonant states as model-space kernels; Hecke dispersion `V_p`; Krein square; tree quotients over curves |
| Language | ringdown, overtone, excitation factor, silent branch, flux, relaxation rate, damping domination, modular time, Bode integral (log-mean), passive and inner transfer function |
| Mechanisms | contour expansion; Maass–Selberg as flux; Hecke isometries; Lax–Phillips semigroup and functional model; Kramers–Kronig and Bode for `log|S|`; Chetaev-type energy balance if the Krein form has one |
| Tools to build | energy estimates that see Hecke symmetry; a Lyapunov functional for the Eisenstein sector; sharp decay for smoothed resonant sums; causal, compactly supported probes; horocycle renormalization |
| Calibration | function-field graph model, where Weil supplies the answer; non-congruence `Γ` and deformations, where resonances leave the line [C] |

**Criteria it must meet.**
- Recovers the edge theorem from flux [L], and the sharp rate over curves from physics.
- Fails for non-arithmetic `Γ`: geometry alone cannot be the source.
- Explains why KMS, Schur and `C*` positivity are blind [L/D].
- Is consistent with raw echo spikes, which defeat every pointwise exponential bound independent of RH [L].
- Gives no prediction contradicting GUE statistics, whose ramp and plateau read pair correlation (B64) [C].

**Questions it must answer.**
- What quantity decays at exactly the universal rate, and what is the proof in the graph model?
- What is the physical meaning of `¼`? On the Lewis side it is the fixed line of inversion; FE partners have damping rates with fixed sum `½` [L]; is it the midpoint of a KMS-type strip in the Mellin variable [D]?
- Why is the plus branch silent [L], and what does it say about reflection?
- Does Hecke at a second place act as a constraint on flux through the first?
- What is the bulk reading of the log-mean?

**Limits.** Every proved physical statement here is a restatement or an edge theorem. The physical energy is positive and imposes nothing on mode positions. The geometry is locally pure AdS, so no gravitational dynamics is involved: this is scattering on a quotient. The programme has not produced one estimate that is not already in the Eisenstein calculus. It is a language until the graph test returns.

## 2.11 If RH is a problem of topology or geometry: which field?

**What it would be about.** *Effective geometry of the scaling surface:* an intersection theory on `Spec ℤ×Spec ℤ` with windows as open pieces, Hecke correspondences as curves, and sections with actual zero sets.

| Aspect | Content |
|---|---|
| Objects | windows and their lattices; source cone; canonical class; primitive `h¹`; Hecke correspondences; Lefschetz sequences `c_m=W(T_{mℓ}g,g)`, whose ratios are off-line zeros [L]; predictor polynomials and their winding; the prime complex; star covers |
| Language | degree, primitive class, effective, ample, Bézout, Castelnuovo, wall, critical length, gluing, nerve |
| Mechanisms | RR with an actual section; effective ⇒ count ⇒ nonnegativity; wall-crossing of an integer on a connected family of windows; Bochner-type identity with a curvature term; Künneth; Hecke similitude |
| Tools to build | a section space reading primitive classes; a vanishing theorem (`h⁰=0` for negative degree); a curvature whose sign is arithmetic, knowing that cutoff `Γ₂` is unbounded below [L]; a filtration of the prime complex with weights; an index formula for the winding |
| Test cases | genus-one curves, where the primitive correction is `N₁` [L]; finite curve windows, Künneth ⇔ unitarity [L]; Golden, with correct weights and no purity [L]; Kloosterman fibres [L] |

**Criteria it must meet.**
- Recovers Weil's proof for curves as a special case, step by step.
- Is false on Golden and on shifted data whose Tate coefficients are nonnegative [L].
- Reads the test beyond its two degrees [L].
- Has infinite-rank counts [L], with no finite-dimensional norm realization on a window [L].
- Does not define its zero count through `Q`.

**Questions it must answer.**
- What is a section, and what is its divisor?
- What is an irreducible curve on the scaling surface, and why do distinct ones meet nonnegatively?
- Is there a homotopy invariant equal to the window index, computed without the form?
- Why does the prime complex have Betti numbers `≈cN` and Euler characteristic of expected size `√N`; what differential explains it?
- Do Hecke correspondences generate the ample cone?

**Limits.** Finite-rank carriers, separable assemblies, connected links and natural Frobenius candidates are refuted in their stated classes [L]. The corpus has every statement of this geometry except a mechanism: RR is exact and Bézout is RH. Over `𝔽_q` the same statements are consequences of having a variety.

## 3. The one question

**Can a negative direction of the complete Weil matrix at a fixed critical ratio escape every window of length of order `log R`?** Let `R=c⁸/log N` be fixed and let `R_c(ζ)` be the largest ratio below which the matrix is eventually positive definite. Is `log R_c(ζ)≳a*(ζ)`? The inequality that decides it is a Gårding bound at each fixed `R` (A10):

`Q(U)+B_R‖U‖²≥a_RW₈(U)` on normalized atomic sources, with `a_R>0`.

The expected answer is yes. Then HF, SRT, the packet branch of AIP and the atomic branch of ACS stop being separate problems at every fixed ratio.

### Why this one

**This is a structural question, because no analytic estimate below quasi-RH is both reachable and consequential.** A statement below qRH must leave sparse deep zeros alive, and that leaves these kinds:

| Kind | Best form | Why it is out of reach | Evidence |
|---|---|---|---|
| One-offs | AAL (B83) | no estimate of any kind; means are blind since the oscillation has zero constant mode | [L]; [D] |
| 100% near the line | depth density `o(T)` (B57) | moment `→1` needs `log N≥log²T/(6K₀)`: a superpolynomial mollifier with no off-diagonal theory | [L]; [D] |
| Rate near `½` | cluster wall (B59) | isolated rate `2−2γ` against fourth-moment rarity `4γ` balances at `4/3`, Ingham's slope at `σ=½`; passing it is a classical barrier | [D]; [C] |
| All-height sign | past size (B46) | depth `d` at height `X` is visible at `a≈(1/2d)log(4d log X)`, so sign at `a=K log log X`, `K>1`, is a zero-free strip up to crystal shielding | [L]; [D] |
| Production | stencil rate (B55) | rate is the Mertens level | [L] |
| **Reduction** | **this question** | **one named inequality, with its neighbours proved** | **[L]** |

### What is proved around it

A negative sequence can only escape through one of these channels.

| Channel | Status | Module |
|---|---|---|
| Far tail `y→−∞` | Γ-liminf keeps `α_R∫_{y<0}F²e^{−8y}`, `α_R>0` at every `R`, on sequences with bounded `W₈` | `TheCriticalFormHasAGammaLiminf` |
| High frequency | a bounded form keeps high frequencies small; `L¹` limits become strong | `BoundedWeilEnergyUpgradesL1LimitsToStrongLimits` |
| Prime shifts | `|P|≤εW₈+B_ε‖H‖²` | `PrimeShiftsAreInfinitesimalInTheExponentialWeight` |
| Precompactness | physical and Fourier tails; bounded collar mass | `PhysicalAndFourierTailsGiveCompactness`, `ThePhysicalCollarHasBoundedExponentialMass` |
| Far conductors | coercive for `R<R*` | `TheFarComplementHasAnExplicitRatioInterval` |
| Periodic charges | four channels below the eighth root; `J_N=O(log N)` iff gcd profile | `TheFourChannelsOfAPeriodicCharge`, `TheJumpEnergyDetectsTheGcdProfiles` |
| Pole cross term | rank one | [D] |
| Growing-period charges | open (A13) | — |
| Localization commutator | inside `C` in `farMargin`; no replacement | — |

Coercivity at `R*` is not what is needed. `farMargin R=3D/(8R)−C−C′R` asks the reserve to beat `C` and `C′R` outright, while a Gårding bound lets them be paid by `εW₈+B_R‖U‖²`.

### What makes it mathematics and not bookkeeping

A Schur complement against the window margin fails. `λ*(c)` decays doubly exponentially [L] and the reserve `e^{8L}` only exponentially, so that route stops at bounded `R` [D]. The argument must use the `W₈` reserve on the near-kernel vectors of the window. The estimate is then an effective margin of about `(log R)^{O(1)}/R` and a tail paid from length `(2/7)log R`, so half-width `(1/7)log R` suffices [D, an estimate and not a proof].

### What an answer does

| Answer | Effect |
|---|---|
| **Yes** | At each ratio HF, SRT, AIP packets and ACS atoms become a rung of RW; the all-ratio statement is `a*=⊤`. B6 becomes B1. |
| **Yes** | A theorem on the critical curve: the complete matrix at exponent `1/8` is positive definite at every ratio with `log R≲a`, from one verified window, far past the proved multiple `2K₀`. |
| **Yes** | The critical-curve content of CACT (228 modules), AHD, CAF, ACPL, RAPT, TM and ADT is finished, and A9, A12, A13 stop being route tasks. Effort moves to B2 and the zero-side walls. |
| **Yes** | A template: Γ-liminf, Gårding and compactness turn a critical family into a window. |
| **No** | A sequence with bounded form and `W₈→∞`, in Lean. That channel is then exactly the independent content of HF, and HF keeps a wall of its own. It is not a negative direction, so it does not touch RH. |

`R_c<∞⇔a*<∞` either way: the limit pencil is negative once a negative window is available and `R` is large [D].

### First steps

1. Audit `farLinearConstant` term by term (collar, `dyadicArchConstant/4`, leak) and bound each by `εW₈+B‖U‖²`.
2. Replace the Young trade on the pole window by the rank-one structure, using the signed polar part of the low packet.
3. Bound `W₈` on near-kernel vectors of the window from below.
4. Close the growing-period channel (A13).
5. Assemble the compactness (A11) and state `log R_c≳a*`.

### Validation

| Test | Verdict |
|---|---|
| T1 | Pass. Under RH no negative sequence exists, and the reduction says nothing about zeros. |
| T2 | Pass. A stated inequality to prove or refute. |
| T3 | Pass. The table above. |
| T4 | Pass. Each window is a rung; the reduction is uniform in `R`. |
| T5 | **Fails, by design.** It is a reduction, expected to hold on any Chebyshev-bounded datum, so it does not separate ζ from a fake. |
| T6 | Pass. Every neighbouring channel is proved, and no input is refuted. |
| T7 | Pass. It moves Σ1s, Σ87, Σ88 and Σ116. |

**By the tests this is not a door to RH. I found no question below quasi-RH that passes all seven and also has a working tool.** The questions passing all seven, such as B57 and B59, are in the table of kinds above.

### Limits

- No sign wall moves. B1, B2 and every RH-level item stay as they are.
- ZAL and AAL are untouched, and typical heights gain nothing.
- The constant between `a*` and `log R` is only estimated, and A13 may hide a real channel.
- The gain is architectural: fewer independent problems, one theorem on the critical curve, and one scalar left on the sign side.

### Why the others rank lower

- **AAL (B83):** the exact split of RH with a rigid negative world, and no estimate to start from. Its table is in 2.3.
- **Log-mean (B57), cluster wall (B59):** real advances on typical heights, blocked at the mollifier length and at Ingham's slope.
- **All-height sign (B46), past VK (B15):** effectively qRH in the first case and a historic barrier in the second.
- **Hecke dispersion floor (B70):** `V_p≥η` already follows from the formula for `V_p` and VK; the question asks only for a new proof.
- **`{2,3}` torus positivity (B19):** a compact check at fixed primes, and the torus turns negative by `P=19` in scans [N].
- **Smallest FE defect (B84):** a barrier for defect-stable arguments, with no gain on ζ.
- **Near-extremal mollifier (B66), `D_s≥0` (B68), bounded `Ψ` (B2):** RH-strength.
