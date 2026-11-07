# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `b33ed59737` plus the working tree of 2026-11-07.

Evidence: `[L]` Lean source; `[S]` Lean source unfinished, unintegrated or uncommitted; `[K]` Lean with transitive axiom audit; `[D]` deduction, not a Lean theorem; `[N]` numerical, uncertified; `[C]` classical, not formalized.

**38 live formulations; 9 candidates.** HJ→PA; BSH→CDC; FEL's BSY criterion→CTF. Candidates: APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF.

## 1. Big picture

### 1.1 RH has two halves
RH ⇔ ZAL ∧ AAL [L]. ZAL says finitely many zeros lie beyond each positive depth and implies quasi-RH [L]. AAL says finitely many zeros right of `½+h` forces none. Failure of AAL implies `Θ<1`, so `qRH ∨ AAL` is a theorem [D]. Under AAL, RH ⇔ ZAL ⇔ finite off-line support ⇔ `κ(K_ζ)<∞` ⇔ bounded nonreal heat count ⇔ finite critical source energy ⇔ eventual Hadamard positivity ⇔ eventual central-gap budget [L]. Failure of AAL is exactly one rigid object: `ψ(x)−x=x^{Θ}T(log x)+O(x^{Θ−η})` with `T` a unique trigonometric polynomial, coefficients `−ord/(Θ+iμ)`, zero constant mode, `η≤Θ−Θ₂` sharp, and sign changes at bounded log gap [L]. It is also two-prime dilation annihilation of `ψ` [L].

### 1.2 The sign plane
On `PW_a`, Weil's form is diagonal in frequency: `Q(f)=∫|f̂|²W_N`, `W_N=Ω−2D_N`, `N=e^{2a}` [D]. Sign is a function on the plane `(a,log X)`, the local onset field [L].

| Curve | Statement | Evidence |
|---|---|---|
| All heights | Gamma base beats size: `a≈log log X−log 4` | [L] single-height form, [D] constant |
| Density `1−δ` | Every shape-bounded test positive up to `a=δ log T/(64M²)`, one exceptional set, no zero information | [L] |
| Visibility | Isolated depth `d` negative at `a≈(1/2d)log(4d log X)`; a cut crystal hides fixed depth to `(log T)/36`; `λ>1` gives sharp location | [L] |
| RH | `Ω≥0` everywhere | [L] |

Every sign statement sits in one of two places [D]. On bounded aperture it is a finite rung, decided by verified height. On a family unbounded along a progression it reads every off-line zero the test does not annihilate, through the growth `e^{δt}` of `c_φ(t)`, and is RH-level. Statements strictly below quasi-RH are therefore averages over heights or tests, near-line densities, one-off exclusions and reductions.

### 1.3 Window sign is one scalar flow, and contact is `Ψ` blowing up
The tower is a canonical system to contact with `H₁H₂=1`, no singular part and no atom at aperture 0 [L]. `L′=q−sinh 2L`, `(log K)′=2 cosh 2L` [L]. `r`, the traces and `Ψ` are absolutely continuous on compact precontact intervals, `q=Ψ′` is a function, and `q_y→q` in `L¹` [L]. For the actual chain, `|L(x)|≤artanh e^{−2(x−c)}+2 osc_{[c,x]}Ψ`, with no initial value, no `1/μ` and no derivative of `Ψ` [L]. Contact gives `limsup|r|=1` [L]. So **RH ⇔ `Ψ=½log H₁` is locally bounded on `[0,∞)`** [D]. Prime thresholds are soft: `(Ψ(x)−Ψ(a))log(1/(x−a))→Λ(n)/√n` [L]. In the Born model a collapse needs coherence over `≳√n` reflectors [L]. The proved margin ceiling forces `m≳e^{2a}`, above the Born bound `m≲ae^{a}`, so the actual `q` is a nonlinear response [D].

### 1.4 The certificate is causal, and the forward map has an exact tangent
A window is PD iff it has a predictor with positive margin whose polynomial has no zero in the closed disc, any sign pattern [L]. RH is existence of outer predictors for every window, lattice and nonzero test [L]. Reflection data are free coordinates; an echo train is passive iff each echo lies in its Schur band [L]. The forward map from primes is causal and injective, with exact tangent `∂E_n/∂λ(n₀)=−(2/√n₀)A_n(log n₀)` [L]. Margins are concave in the weights [L]. The tangent of the potential carries `1/(1−γ_n²)`, and the Born defect is bounded by `Π(1+|γ_k|)−1` [L]. On certified windows past `log 2` the whole chain is a theorem, with `Λ(2)` in the data [L].

### 1.5 Why the datum is critical, and what compactness means
Slack `s>0` is Szegő's regime with square-summable reflectors; `s<0` has a finite negative witness; RH places every lattice at `s=0` with `Σγ²=∞` [L]. For every nonzero test `c_φ(t)↛0` [L]. In `ℓ²(zeros)` a profile decomposition is a theorem [L]. For ζ, RH ⇔ every orbit correlation is relatively compact ⇔ moving-bubble energies have nonnegative subsequential limits [L]. RH is also existence of **any** real weight making each window nonnegative: the cone forces `Λ` afterwards [L].

### 1.6 The critical family: Gårding holds on the collar and fails on deep atoms
At fixed `R=c⁸/log N`: Γ-liminf with weight `α_R>0` at every `R` [L]; bounded form and masses make `L¹` limits strong [L]; prime form `≤εW₈+B_ε‖H‖²` [L]; coercive far complement for `R<R*` [L]. The weighted Gårding bound `Q+B‖U‖²≥aW₈` is false on the whole horizon: `(e₁−√2e₂)/√3` at `y≈−log N` has energy `O(log N)` in unit `L²` and `W₈≍N⁸` [L]. It holds on the top collar at every `R`, uniformly for `c⁸≤R log N`, with seventh-mass control as well [L]. So a negative sequence supported on the collar has a strong nonzero limit with negative limit pencil, and the limit pencil is a finite window of half-width of order `log R` [D]. What remains of the full-space problem at a ratio is the coupling of prefix and low packet to the collar.

### 1.7 The inner mass has a second expression, and its minimizer is forced
On `Re s>½`, `E` has inner factor exactly the Blaschke product of right zeros [L]. `exp(2I(1))=inf_Q∫|ζ exp Q(φ₁)|²dP₁` [L]. Near-extremal families have no freedom: limit `1/E`, first coefficient `|q₁−(1−γ)|²≤B−1`, every budget `≥|ρ|²/|ρ−1|²` [L]. For one fixed `0<δ<½`, the Poisson mean of `log|ζ(½+iτ)/ζ(½+δ+iτ)|` equals `log((1−δ)/(δ|ζ(1+δ)|))` plus a surplus `I(1)−I_δ(1)≥0`; RH ⇔ zero surplus; the first jet is `−(1+γ)+Σm_ρRe(ρ⁻¹+(1−ρ)⁻¹)` [L]; `exp(2(I(1)−I_δ(1)))` is the ratio of critical to shifted Szegő budget infima [S]. Boundary quotient means tend to 1 for every finite curve datum [K]; for a single factor the model-space projection reads the inner mass as `1−‖β‖⁻²` [L]. Over a curve the extremal family is the damped Euler logarithm and Castelnuovo is the uniform bound `|P(v)/P(ρv)|²≤4^{rank}` [L].

### 1.8 Finite rungs are theorems; they decide nothing
RH through height 67 is proved with no zero located [L]. It gives PF₂₀₀, slices `|t|≤133/2`, Li `n≤314` and rank ten [L]. Window, Hausdorff, heat, Jensen and theta rungs have explicit heights [L]. The floor tower stays below `0.3621` [L].

### 1.9 One Vinogradov–Korobov layer, and production is on it, on the half scale
AIP cost, SZ source, TT band, MC Hilbert form, WL energy, PTR depth, TH collar and integer stencils carry one VK saving and stop there [L]. A producer of rate `ε` gives `|M(n)|≤εn+12(w/m)√n+K`, with no zero of ζ and no analysis, and a Mertens level gives producers of comparable rate on a polynomial alphabet [L]: the two scales coincide. Peak law `w≤100(1+log K)²(KT+m)`, floor `ε≥c/(√K(1+log K))`, rate `K^{−a}` ⇒ `Re ρ≤1−a`, rates for all `a<½` ⇒ RH, no rate past `½`. RH gives `a<1/5`, a strip at `Θ` gives `a<(1−Θ)/(3−Θ)` [L]. Certifying `ζ(s)≠0` needs `|s|≲√K(1+log K)` [L].

### 1.10 Zeros are a kernel; ledgers see them and do not constrain them; parity is the strip
`U_s(r)=r^{−s}−(r+1)^{−s}` satisfies `ΣU_s(r)(r mod k)=(1−k^{1−s})ζ(s)`: the zeros are exactly the power-law kernel vectors of the Chebyshev moment system [L]. A summable kernel vector vanishes; a kernel vector bounded below by the pronic measure vanishes; so positivity of the system reaches exactly `Re s≥1` [L]. At infinite level the pronic measure is the only fake prime measure; at bounded level translation by `lcm` empties any window [L]. Linear ledgers annihilate every zero mode [L]. Degree `k` ledgers have order `m−k` at multiplicity `m`, and every exact ledger is holomorphic off `s=1`: seeing a zero costs the exact value [L]. The twin symbol is `A−2A(2s)`: at a zero it shares every leading pole with `A^k`, at the pole the gap reads `−ζ′/ζ(2)` [S]. Selberg's reading passes the twin, Type I and Type II filters and reads a value at `s=2` [L]. Parity-neutral producers exist at every rate [L]. `L(x)≪x^{a}` for all `a>Θ` ⇔ zero-free `Re s>Θ`, so a parity source at power saving is a zero-free strip up to zeros a twist absorbs [L]. Over ℤ a dilation of the count is an average over translations: a self-similar count is quantized, and every integer is a cut [L]. Over a curve the kernel has dimension `deg P` and obeys one recurrence [L]. Linear curve stencils stop at `|a|≤q+1`; purity is an upper bound for curve and twist [L].

### 1.11 The near-line layer is one number
`T⁻¹∫_T^{2T}log|ζ(½+it)|dt→0` is equivalent to the Euler-mollified log-mean, the outer law, the dyadic moment, `100%` critical-scale clustering and three defect readings [L], in Abel form to `I(½+x+it)→0` and to depth density `o(T)` [L], and on the horizon to density-zero damping deficit [L]. Moment data alone give `I≤log(1+log 5x)+C` [L]. Selberg's mollifier gives `O(T)` [C]. Moments do not determine the log-mean [L]. Isolated zeros obey rate 2 without separation [L]. At simple right zeros `N(ρ)=exp(−Σ_{a≠ρ}m_aG(ρ,a))` [L]. The critical-scale crystal, reality and depth laws hold outside `δT` heights [L].

### 1.12 Long moments are rigid
Slope is exactly `2wθ`. A cofinal bound at any fixed `K` self-improves to `K=6`. RH reads at one point, in one bounded window, or as a positive proportion of every length-2 window [L]. Möbius polynomial zeros accumulate at every point of `Re s=Θ` [L].

### 1.13 Positivity lives inside one prime at a time
`S(a,b)=Π_pT_pA` with Eisenstein coefficients [L]. `A` is not a positive Laplace mixture [L]. Below left growth `½` the level-1 Hecke cone, the torus cone and exponential convexity coincide; `½` is the exact threshold of the `L²` prime-pair cone; an all-base torus-positive amplitude with left growth `κ<min(1,κ₀)` and right decay `κ₀` vanishes, so the theta amplitude is not all-base torus-positive [L]. Signed columns add, products of columns are rigid [L]. An amplitude with a limit at height infinity gains nothing from locking; only amplitudes oscillating with the height can gain [L]. The base pays by size when `Σlog p/(p^{½+a}−1)<½log(b/2π)` [L]. `thetaAmp(x)e^{x/2}→½`: integer tests balance exactly, primes lose one logarithm, and both `½`s are the pole [L]. Kernel-valued prime payment in returning coordinates satisfies `|S|≤|G|` for an archimedean coordinate `G` vanishing vertically, on `Re s>0` for finite primes and on `Re s>σ₀≥½` for all primes [L]; coordinates that do not return escape this and telescope on `Re s>2` [L].

### 1.14 The prime orbit at one height
Phases are prescribable up to length `≈log T`: every window `exp((20/δ)y log y)` enters every box on primes `≤y`, and below `c log T` no sup bound is possible [L]. Past that, absolute savings: `t^{−δ}` at `L^A`, `exp(−L^β)` at `7L^A`, `4·10⁻¹⁰/(L⁸ℓ⁴)` at `48L²ℓ`, on any large set of primes including the top of the column at power-of-`T` loss [L]. Proved ceilings: the rounded orbit shares diagonal moments and early orbit and returns at `T`; one word certifies precision `≤1/(2(k+2))`; a polynomial phase saves `≤2/(k+1)` without excluding binomial denominators; a squared word free of small primes is an almost-prime tuple in a sumset; transfer to rare heights stops at the Kronecker scale; large values at last diagonal scale number `H^{1/A+o(1)}` and are not excluded [L]. Required at the size curve is `≈εL/ℓ` [D]. A one-sided column bound at height `γ` excludes an isolated zero of depth `δ` at length `(log γ)^{O(1/δ)}` [L].

The first-return time of the orbit brackets this [D]: with `R(y,δ)` the least `t≥1` aligning all primes `≤y` to precision `δ`, Vinogradov gives `R≥exp(c(log y)^{3/2})`, Kronecker gives `R≤exp(C_δy/log y)`, RH gives `R≥exp(c√y/log y)`. On the range between, the Taylor degree of `t log(n+h)` at length `y` is `≈log t/log y`, above `(log y)²`: Weyl sums past Vinogradov's degree. This range is the **dark range**.

### 1.15 Physics: exact and blind, with one survivor
The modular horizon is an exact solution with general `L²` data, metric of a pulse and one mode per zero; universal damping ⇔ RH; one-sided quarter-line bound ⇔ RH [L]. On the graph every channel datum `(q,G,D)` is a tree quotient with flux, unitarity, edge theorem and positive commuting Hecke at every degree and class; fakes with `t²>4q` have resonances off the universal circle [L]. **Universal damping is not a law of wave dynamics.** Hecke acts on every resonance by the dispersion relation `X^d+Y^d` [L]. Its independent content lives on a cuspidal sector with no resonances [L]. On the modular horizon Hecke at `p` is modular time translation by `log p` [L]. Schur, KMS, reflection and `C*` positivity hold on every system [L]. The throat has flux and unitarity with any partner product, and a path quotient has FE only at genus `≤1`: reflection is supplied, not derived [L/S]. A compact probe excites infinitely many modes [L]. Survivor: the Krein law. The form multiplies by exactly `q` per double tick on every system, unconditionally, and decays at the universal rate on the modular horizon; its flux is nonnegative exactly under universal damping [L].

### 1.16 The count
A form homogeneous of degree two is nonnegative iff a function bounded below lies at bounded distance from it (Tate), and any function at bounded distance recovers the form by `h(mξ)/m²` [L]. RH ⇔ naive height on every window [L]. Over a curve the Rosati form has one iff unitary; kernel orders do not supply it [L]. On the graph the parallelogram law for the count at all probes ⇔ `t²≤4q`, with first instance the conservation of channels [L]; over a true curve the count is the height on `h(T)Y²=h(X)`, with an exact parallelogram law, and Hasse follows with neither Stepanov nor character sums [S]. Fake: count, not quadratic. ℤ: `Q` on integer probes quadratic, not known to be a count. Curve: both [L].

Local data over ℤ exist. Λ is an intersection number of torsion orbits, the log of a cyclotomic resultant, Hecke equivariant [L]. The base has the theta `h⁰` with exact Riemann–Roch, and the window atoms form an Arakelov bundle [L]. The prime form plus a log-discriminant diagonal is minus the renormalized limit of a positive torsion energy, and the sign is lost exactly in `log(1/(1−r))Σx²` [L]. The base `h⁰` does not extend to a quadratic Riemann inequality [L].

### 1.17 Recurrence, tail and hull
Returns transport zeros [L]. A return on a disc is a simultaneous Kronecker return of all primes, paid by a spike of ζ near `1+iτ_j` [L]. Limits on `Re s>1` fill the gauge torus, the Liouville twin among them, so an argument stable under such limits cannot separate ζ from its twin [L]. Prime returns have positive density; at a zero `½<Re ρ<1`, a positive proportion of prime returns are not returns of ζ, whatever the prime set [L]. Under a finite layer every phase return is unbounded on every connected domain joining a top zero to `Re s>1`; a bounded return at each right zero gives AAL [L]. Return exponent is at most density exponent and jumps at tolerance `≍r^D` [L]. Haar-a.e. fibres extend zero-free; the Liouville fibre extends iff RH; RH ⇔ every nonzero limit of translates is zero-free [L].

Resonator mean on a Bohr set [D]: for `σ>½` and resonator length `≤T^{½−ε}`, `E_R|ζ(s+iτ)|²≈|Π_{p≤y}(1−ω_pp^{−s})^{−1}|²Π_{p>y}(1−p^{−2σ})^{−1}`. The Euler part never vanishes and carries `y^{ρ−s}` left of a right zero. So typical aligned shifts are large left of a right zero, in every world, and a zero is a tail event at resolution `1/log y`. A bounded return is an atypical member of the Bohr set.

**Scope of the effective form.** The stated disc in `TheTransportOfAZeroIsEffective` is `closedBall(3+iγ,31/10)`, which contains `−1/10+iγ`. There `|ζ(−1/10+i(γ+τ))|≥cτ^{3/5}` by the functional equation, while a head return has `τ≥N` [D]. So `|ζ(s+iτ)|≤N^A` for all `A>0` fails unconditionally at large `τ`; `hslow` holds iff no right zero exists; the stated receiver reads RH⇒AAL. The form with `TranslatesBoundedOn` is unaffected. Repair is A22.

### 1.18 ζ is isolated
A Beurling system whose FE has `L¹` defect `≤1/6400`, with the stated analytic hypotheses, has exact rational primes [L]. Integer norms with `N(x)−⌊x⌋→0` force them with no analysis [L]. Residue is `½` with integers, or `2β≥√2` [L]. Stencil systems `ζG` have infinite FE defect [L]; zeros right of `σ` are invariants of the primes modulo exchange of exponent `<σ`, and adding generators adds no zeros [L]. Rational quartet surgery keeps FE exact and destroys Bohr almost periodicity [L]. Continuous positive Beurling systems with one off-line pair exist at finite defect [L]. Degree-one Selberg class is `L(s+iθ,χ)` [L].

### 1.19 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| Markov, Perron, sign-gauge balance past `e^{−3/4}`, `log ρ` | refuted | [L] |
| Size-only payment of primes | ends before half-width `21/40` | [L] |
| Floor tower as aperture producer | stays below `0.3621` | [L] |
| Weighted Gårding on the whole horizon | false on deep atoms; true on the top collar | [L] |
| Fixed theta heads; pointwise prime payment | no margin; fails at `log 6` | [L] |
| Positive Laplace mixtures; all-base torus positivity of the theta amplitude | excluded | [L] |
| Fixed or limiting amplitude locking | adds nothing | [L] |
| Cancellation across independent reflectors at a fixed base | none: size is exact | [L] |
| Kernel-valued payment in returning prime coordinates beyond the Gamma coordinate | excluded | [L] |
| Lions dichotomy for far translates | fails on every bubble | [L] |
| Parabolic structure as selector of `t=0` | blind | [L] |
| Barriers on prime sums; short detectors and weights | blind to purity; stop at the last scale | [L] |
| Moment data for the log-mean; coefficient norms for long moments | blind | [L] |
| Diagonal moments, group closure, early orbit against a return | blind | [L] |
| Transfer of typical bounds to rare heights past Kronecker | empty | [L] |
| Schur, `C*`, KMS, reflection and raw-norm positivity as zero locators | blind | [L] |
| Wave dynamics, flux, unitarity, positive Hecke at all degrees and classes as a law of universal damping | fakes carry all of them | [L] |
| Full-determinant arithmetic reflection | none | [L] |
| Positive primes plus smooth integer count as AAL | false for continuous models | [L] |
| Invariant tensor weights; principal-branch endpoint signs; pure compression | false for Golden or RH-level | [L] |
| Finite-template, separable, finite-realization, tensor, integrality shortcuts | stated classes refuted | [L] |
| Integer stencils as a mechanism independent of Möbius | rate is the Mertens level; ledgers blind | [L] |
| Positive Hecke amplification of stencils; capacity reading of the rate | excluded | [L] |
| Polynomial ledgers as a parity input at zeros | twin shares every leading pole | [S] |
| An independent parity source at power saving | is a strip | [L] |
| Rotated relations with coefficients of growth `exp(C√|w|)` | trivial | [L/S] |
| Raw echo decay; near-arithmetic ladders; rational zero relocation | excluded | [L] |

## 2.1 Tasks that are just work

Difficulty is established only where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### Finite verification
| # | Task | Routes | Basis |
|---|---|---|---|
| A1 | Lean-certified `RHVerifiedThrough T` past 67 with actual zero location, first `T≈10²–10³` | all rungs | `hardySEM` sign chains exist; Turing count missing; Fejér budget is a bounded-height method |
| A2 | Numeric values of `windowHeight`, `xiMassHeight`, `heatGridHeight`, theta `D` | window routes, TH, LA, HCF | explicit definitions in Lean |
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
| A10 | Collar compactness assembly: a negative collar sequence at ratio `R` has a strong nonzero limit with negative limit pencil, so collar sign at `R` follows from one window | HF, SRT, AIP, ACS | collar Gårding, Γ-liminf, strong limits, tails, precompactness |
| A11 | Prefix–collar coupling at fixed `R`: bound the cross operator against the prefix reserve (unverified; the one question of section 3) | HF, SRT, AIP, ACS | sparse cross weights `(n/m)^{½}Λ(m/n)`; prefix reserve `θ log N`; prefix `L¹` mass small |
| A12 | Low-packet/complement Schur payment on `0<R≤min(1,5R*/6)` (unverified) | HF, AIP | certified complement, low packet, polar capacity |
| A13 | Growing-period charges beyond gcd profiles; four-channel law at the critical scale (unverified) | AIP, HF | four channels close below the eighth root |
| A14 | Frequency-integral identity in Lean; replace Markov by Gaussian moments in the typical-height sign | RW, ACS, SRT | `MostHeightsAreWeilPositiveAtSmallAperture`, moments of `D_N` |

### Flow, near-line, continuation, returns
| # | Task | Routes | Basis |
|---|---|---|---|
| A15 | Lean statement RH ⇔ `Ψ` locally bounded | RW, SZ | restoring bound, contact criterion, AC of `Ψ` |
| A16 | Numerical `r,m,q` for `a≤1` [N] | RW | Galerkin |
| A17 | Selberg `O(T)` depth density in inner-field form, removing `log log` | WD, CTF, RW, ZCG | `exists_logIntegral_le_of_secondMoment`, twisted second moment to `21/50` |
| A18 | Twisted second moments past `21/50`: to `½`, Conrey `4/7` [C] | WD, census | raises rate `2θ` |
| A19 | Heat horizon from `6600/9991` toward its method floor | ZCG | profile margin, best exponent pair |
| A20 | Jensen rung toward saddle scale; constants in `300√(d log d)` (unverified) | LA, FFP | saddle identity |
| A21 | Census items; logarithmic two-point Chowla [C]; Voronoi; Zwegers [C]; runs past five | MC, ACS, census | classical |
| A22 | Effective transport on a disc with left edge right of `½`: restate `exists_exponent_transport` and its corollaries | BAG, ZCG | three circles, `exists_isHeadReturn_le` |
| A23 | Bohr-set second moment: resonator mean of `|ζ(s+iτ)|²` on `σ>½`, length `≤T^{½−ε}`, with its explicit-formula reading | BAG, ZCG, PTT | `TheBoxesOfTheTorus`, `ZetaLineResonatorLargeValues` |

### Theta, reflection, weights, production, descent
| # | Task | Routes | Basis |
|---|---|---|---|
| A24 | Certified scans of `S_S`; brackets for `S*(a,b)` | TH | column calculus |
| A25 | PM physical all-`n` Hecke moments beyond squarefree words (unverified) | PM, W1C | one-step isometry, prime-word moments |
| A26 | Weyl law for level one [C]; metric of `L²` horizon data; regularity at `r=1`; scalar sector `s=u−½` | PM, BHR | `TheCuspChannel`, `TheMetricOfAPulse` |
| A27 | Lean dictionary: local AdS₄ isometry, modular Lax–Phillips semigroup, modular Zagier–Sarnak criterion [C], modular Kramers–Kronig | PM | graph versions in ASH |
| A28 | Reciprocal quadric traces identified with vanishing-cycle Frobenius traces (unverified) | ACS | transverse form and quadric counts |
| A29 | Mixed Young projections at small rank (unverified) | ACS | column projections and PF₂₀₀ |
| A30 | Best producer exponent under RH, in `[1/5,½]` (unverified) | WL, MC | `TheOneFifthRateUnderTheRiemannHypothesis`, `TheHalfScaleOfTheRate` |
| A31 | Discrete Beurling system with a one-off pair, and its FE defect [C for the discretization] | BAG, ACS | `overRegularZeta`, exchange law, random approximation |
| A32 | Manin at higher genus: heights on a constant Jacobian over a function field, with `Tr(P(F)P(F)′)` as Tate limit [C] (unverified in corpus) | ACS, PM, AE | `TheParallelogramLawOfHeights`, `TheCountLawOfATrueCurve` |
| A33 | Cubic quotient: cusp and exterior coercivity, spectral expansion, continuation of the Eisenstein series past `Re s>2`, residue = cubic theta, Fourier coefficients = Gauss sums [C] | MC, MMD | `TheCubicVariationalLaplacian`, `TheCubicCuspBarrier`, `TheCubicEisensteinSeries` |

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
| B7 | Growing families, moving frequencies, conductors between `(log N)^{13/32}` and `N^θ` above `R*` | sub | HF, AHD |
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
| B46 | Proportional saving against size for prime polynomials of length `(log X)^{2K}`, `K≥1`, at all heights; it implies the first-return bound `R(y,δ)≥exp(y^{c})` | sub (up to crystal shielding) | RW, all rungs, PTT |
| B47 | All-height frequency input not reducible to size: multiplicity `o(log X)` | sub | ZCG |
| B90 | Certificate past the abscissa in coordinates that see the height | method | TH, RW, PTT |

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
| B55 | Any polynomial stencil rate (is qRH); rates `a↑½` (imply RH) | ≥qRH to RH | WL, MC |
| B56 | `Θ<1⇒Θ=½` | sub | whole programme |
| B57 | Log-mean of ζ on the line `→0`, equivalently depth density `o(T)` | sub | WD, census, MC, RW, ZCG, CTF, PM |
| B58 | `D_win` | sub | WD |
| B59 | Cluster wall: Density Hypothesis rate for every near-line zero | sub | WD, ZCG |
| B60 | Exponential moments of the Green potential at deep zeros | sub | WD, MC, ADO |
| B61 | A detector past the last scale | sub | WD |
| B62 | Cofinal long moment; one-window bound; pronic tail | RH | WD, CTF |
| B63 | Collision-charge bound | RH | WD |
| B64 | Signed pair information beyond bandwidth one | sub | census, ACS |
| B65 | Genus upper law; logarithmic Serre duality; first Epstein real zero | indep. to sub | ACS |
| B66 | Near-unit budgets; zero dilation surplus; dilation-quotient domination for `E` | RH | CTF, WD, AIF |
| B67 | Parity at power saving, which is a strip up to twist-absorbed zeros | ≥qRH | WL, MC |
| B91 | Classification of kernel vectors of the cut system: are all of moderate growth superpositions of zero modes | method | RAC, WL |
| B94 | Transfer of `μ(I)conj(G₁)=c(I)G₂` and Kubota–Patterson theory to rational-integer Möbius cancellation | past VK at least | MC, MMD |

### Γ — selection and reflection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B68 | Independent `D_s≥0`, nonnegative Krein flux, integer-probe sign or all-zero dispersion bound | RH | PM |
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
| B87 | Function on correspondences, nonnegative for an arithmetic reason, at bounded distance from the form | RH | ACS, HF, PM, RW, AE |
| B88 | Torsion self-energy `log(1/(1−r))Σx²` paid by the archimedean reserve at finite `r` | RH (all windows) | AE, HF |
| B89 | Bounded or polylogarithmic aligned return at each right zero, on a domain right of the line | sub | BAG, ZCG |
| B92 | Arithmetic source of a rotated relation with coefficients of the size of `Q`, nonzero at zeros | RH | ZCG, RAC |
| B93 | A contradiction from the extremal Stieltjes sign `Im(w₀Q″/Q′)≤0` | RH | ZCG, RAC |
| B95 | Abelian group with Hecke endomorphisms `T_n`, `T_n′T_n=n`, whose trace form is `Q` | producer | ACS, AE |

## 2.3 Frankenstein routes

**No assembly closes RH.** Any assembly of proved parts whose remaining input follows from a theorem would make that input RH-equivalent. One assembly has RH as its output, and several collapse whole blocks.

| # | Parts | What the assembly gives | Missing input | Strength of the gain |
|---|---|---|---|---|
| F1 | **Split skeleton.** Any AAL producer (bounded two-prime cone, bounded prime towers, shell positivity infinitely often, bounded lags on one progression, twisted plateau sign, bounded phase return at each right zero) with any ZAL receiver (inner-field decay, `Φ_S≤Me^{au}`, heat coefficient `→0`, eventual Hadamard) | RH [L]. A sparse route blind to a non-attained top and a height-local route blind to finite exceptions cover each other's blind spot | One AAL input (B83) and one ZAL input (at least qRH) | The only assembly whose output is RH |
| F2 | **Collar assembly.** AHD Γ-liminf and aliasing limit, CACT collar Gårding, strong limits and tails, prime shifts infinitesimal, WTZ weighted floor, VHR window rung | Collar sign at ratio `R` from one verified window [D] | A10; for the full matrix A11, A12 | Removes HF as an independent problem at every fixed ratio on the collar |
| F3 | CSTW AC traces, anchor flow, contact criterion, AIF restoring bound | RH ⇔ `Ψ` locally bounded [D] | B2 | The whole tower is one local boundedness statement |
| F4 | ACS typical sign, AIF onset field, WVL visibility, ZCG sharp location, PTT isolated-zero entry, frequency integral | Global negativity at aperture `a` must be spectrally carried by exceptional heights; sign at unbounded aperture for all shaped tests [L/D] | B28, B46 | First sign past bounded aperture, on typical heights, for all tests at once |
| F5 | 8-way equivalence, Selberg tail moment, Euler-mollifier log-mean bound, prime field, Carleson measure, large-width inner field, bulk log-mean | Typical-height layer reduces to depth density `o(T)` [L] | B57 | One target for RW, ZCG, WD, CTF, PM |
| F6 | `N(ρ)=exp(−ΣG)`, hyperbolic count, box budgets, long-mollifier residue bound, crowds rare | Deep zeros obey rate 2 or carry a large Green potential [L] | B60 | Density Hypothesis exponent near `½` |
| F7 | **One edge.** RAC pronic domination, ASH flux, FFP drift, TH Euler product, PM scattering, PTR at `h=½`, Lagarias–Suzuki line law | One edge theorem `Re s≥1` with several proofs, all positivity, on one Hermite–Biehler shift axis [L/D] | B68, B70 | Marks exactly what positivity reaches; no interior gain |
| F8 | TH column calculus, ZCG carrier horizon, FFP forced drift, PTT critical coupling | One inequality, sum of Euler column minima against the Gamma base, with both sides proved as brackets [L/D] | B19, B20 | Merges TH's wall with ZCG's |
| F9 | AAD rate law, Möbius producer, VK Mertens level, RAC kernel and parity exponent | Stencils, parity and zero-free regions are one axis in both directions [L] | B15 | Closes production and parity as independent routes |
| F10 | One verified height, all rungs | All finite rungs [L] | Nothing finite | Decides no all-rank statement |
| F11 | VK savings of all routes | One width axis [L] | B15 | They share one input |
| F12 | Attained-top consequences: finite oscillation, dilation annihilation, unbounded lags on every progression, unbounded towers, `|E_X|≥X^κ` off a vanishing set, top annihilators, twisted FE, zero-free strip, qRH, unbounded phase returns | A contradiction search on one rigid world [L/D] | Any contradiction | Decides B83 if it succeeds |
| F13 | APD isolation, Hamburger rigidity, Bohr obstruction, exact count, stencil FE defect, exchange law, Selberg degree-one classification | Every class of Euler product plus small-defect FE is a singleton [L] | B84 | Any stable argument in that metric is about ζ alone |
| F14 | Curve chain, Abel mollifier, near-extremal rigidity, Carleson measure, dilation quotient | Over a curve: Castelnuovo ⇔ dilation bound ⇔ budgets reach 1 ⇔ unitary. Over ℤ: every piece except the dilation bound [L] | B66 | States exactly what a Castelnuovo over ℤ must assert |
| F15 | **Count skeleton.** Quadratic form on integer probes, Tate law, Λ as log-resultant of torsion cycles, positive torsion energy, theta `h⁰` and Arakelov bundle, Manin's height over curves | Every ingredient of Manin's proof except one: a function on probes, nonnegative for an arithmetic reason, at bounded distance from `Q` [L/S] | B87, B88 | States the missing object exactly. Output would be RH |
| F16 | Horizon exact solution, fakes, Hecke rigidity, Krein law, KMS strip, throat, rank barrier | Physics reduced to one law: nonnegative Krein flux, plus the partner law supplied by FE [L] | B68 | Closes wave dynamics, Hecke and KMS as sources of the sign |
| F17 | PTT non-alignment, RAC Kronecker left endpoint, first-return bound, isolated-zero entry, TheTransferToRareHeights | Short-sum barrier as one statement on first-return time [L/D] | B46 | Sharp bracket for the dark range |
| F18 | Transport theorem, tail at a zero, resonator mean, missing input, hull | AAL's exact form: one bounded return at each right zero, necessarily atypical on its Bohr set [L/D] | B89 | Replaces recurrence wording by one existence statement |

**Closest to the open core: F1, then F15.** F1 says what a two-route proof looks like. F15 says what one object would close the sign side. F2, F9, F16 and F17 are collapses and sharpenings: they remove independent problems and do not advance the core.

### The hard half: what a contradiction search on ¬AAL may assume (F12, F13)

| In the world ¬AAL | Evidence |
|---|---|
| Zero-free strip `(β₁,Θ)` at all heights; `Θ<1`; finite top layer | [L] |
| `ψ(x)−x=x^{Θ}T(log x)+O(x^{Θ−η})`, `T` unique, coefficients `−ord/(Θ+iμ)`, zero constant mode, `η≤Θ−Θ₂` | [L] |
| `ψ(e^u)−e^u` changes sign at bounded log gap, amplitude `≥δe^{Θu}` | [L] |
| Dilation operators at two primes reduce `ψ` to `κx+O(x^{β−η})` | [L] |
| `Φ(mℓ)` unbounded above on every progression; `K_ζ` bounded on only finitely many prime towers | [L] |
| `|E_X|≥X^κ` off a vanishing set in every bounded window, `κ<w` | [L] |
| Finite annihilators nonvanishing on `Re s≤½`; twisted FE with phase `B²` | [L] |
| No returns at the top zero beyond a finite height; every phase return unbounded on every domain joining it to `Re s>1` | [L] |
| `Λ`-moments/`k!` at `ρ+1→−m`, diagonal `→0`, short shifts `→0`, long-shift correlation `→m²` | [L] |
| Every right zero is a Lefschetz ratio, and two primes determine it | [L] |

No contradiction is available from exact identities: every exact ledger is holomorphic off `s=1` [L]. Size arguments on aligned shifts cannot provide one either: typical aligned shifts are large left of a right zero in every world [D].

Which inputs carry a one-off:

| Input class | Status | Evidence |
|---|---|---|
| Positive continuous prime measure, `N(x)−ρx−C→0` | one off-line pair, no recurrence | [L] |
| Euler product with positive generalized primes, small reciprocal mass | one-off pair exists | [L] |
| Discrete primes approximating a continuous measure; integer norms by rounding a smooth density | zeros right of `½` kept | [C]; [D] |
| FE with a finite coefficient prefix | zeros placed at will | [L] |
| Exact FE times a rational relocation | no Dirichlet series, not Bohr almost periodic | [L] |
| Integer norms with exchange of exponent `<σ` | zeros right of `σ` unchanged | [L] |
| Exact Euler product and exact Riemann FE; exact count | only ζ | [L] |
| Euler product and FE with `L¹` defect `≤1/6400` | only ζ | [L] |
| Euler product and FE with larger `L¹` defect | open | B84 |

## 2.4 Wildly different routes

Each mechanism below avoids Σ payment, Π precision and Γ selection as stated. All are speculative. **W6, W7, W9, W10 have no decisive Lean content.** I see no route I would call promising; these are the ones with a concrete mechanism and a first test.

### W5. Extremal angle
- **Idea.** Hadamard's product turns a zero of maximal angle into a strict inequality between rotated moduli: `‖Q(t̄w₀)‖<‖Q(tw₀)‖`, `Im t>0`, and RH ⇔ equality at zeros [L]. No form, no estimate. An identity at the zeros would close it.
- **Status.** Relations `TQ=AQ(ϑ·)+BQ(ϑ̄·)` with coefficients of growth `exp(C√|w|)` are trivial, by Gamma speed on the negative axis [L/S]. The vacuous `A=Q(ϑ̄·)`, `B=−Q(ϑ·)` has the growth of `Q`. Coefficients must be nonzero at the zeros [L]. Necessary law: `Im(w₀Q″/Q′)≤0`, the angular Stieltjes force of the other zeros [L].
- **What survives.** Coefficients of the exact size of `Q` with an arithmetic source (B92), or a contradiction from the force law (B93).
- **Risk.** Rotation in `−(s−½)²` has no known arithmetic meaning. Rotating the Mellin line multiplies by `e^{−iαs}` and does not rotate `s` [D].

### W6. Weighted homology of the prime complex
- **Idea.** `M(N)` is the reduced Euler characteristic of a wedge of spheres indexed by odd squarefree `m∈(N/2,N]` [L]. Betti numbers are `≈cN`, the Euler characteristic conjecturally `√N`, so all cancellation is between dimensions. `ν̂_N(1)=M(N)` on the torsion measure [L].
- **Target.** A filtration of the prime complex by log height, whose spectral sequence pairs classes of opposite parity, with a weight on each surviving class.
- **First test.** Reproduce `M_C(n)` for a genus-`g` curve from a filtered complex over `𝔽_q[T]`, then compute the first page over ℤ at small `N`.
- **Risk.** Parity swaps must preserve size. Betti numbers are forced large in the simplicial model. No Frobenius supplies the weights.

### W7. Interlacing families (mixed characteristic polynomials)
- **Idea.** Mixed characteristic polynomials of PSD matrices are real-rooted by real stability, with no eigenvalue estimate [C].
- **Target.** Exhibit `R_d(Ξ)` or its Hankel as such a polynomial, built from first atoms, PD at every rank [L].
- **First test.** Degree `d=3,4`: are the Taylor coefficients mixed discriminants of explicit PSD matrices?
- **Risk.** A Hilbert–Pólya realization in finite-dimensional dress.

### W9. Values of the form on integer probes
- **Idea.** `Q` on `ℤ^N` is a real quadratic form. Under ¬RH it is indefinite for large `N`. By Margulis (Oppenheim conjecture) [C], an indefinite nondegenerate real form in at least three variables, not proportional to a rational one, has `inf|Q(ℤ^N∖0)|=0`, with values dense (Dani–Margulis) [C]; effectively, `|Q(v)|<‖v‖^{−κ}` at polynomial size for Diophantine forms (Lindenstrauss–Margulis–Mohammadi–Shah) [C]. Rational indefinite forms in at least five variables are isotropic (Meyer) [C].
- **Target.** A lower bound `|Q(a)|≥‖a‖^{−κ′}` on primitive probes, `κ′` below the effective exponent, on one irrational nondegenerate restriction per `N`. No sign is asked for: only a size lower bound of an absolute value, which definiteness then follows from.
- **Why the walls differ.** Homogeneous dynamics and Diophantine approximation on the coefficients `W_{ij}`, with no payment, no precision on primes and no selection.
- **First test.** Over curve data the form is rational, so the discriminator is anisotropy: is a fake's isotropy at rank `≥5` visible by a mod-`p` argument on `ℤ[F]`?
- **Risk.** Lower bounds for `|Q(a)|` with a tiny exponent are as hard as the sign, since a positive-definite lower bound is the only known source. Generic forms have large Diophantine exponent, so the bound must use arithmetic of `W_{ij}`.

### W10. Heights on actual arithmetic varieties
- **Idea.** Arithmetic Hodge index is a theorem on actual arithmetic surfaces (Faltings–Hriljac: Néron–Tate height is minus the arithmetic self-intersection), with positivity by a count [C]. Gross–Zagier heights of Hecke translates of a Heegner point, `⟨T_my,T_ny⟩`, are a positive quadratic form on a Hecke lattice with local terms `log p·(incidence)` and an archimedean Green term [C]. This is the shape of Weil's form with its sign supplied.
- **Target.** A limit, in `N` or in a family, of genuine Arakelov forms on `X₀(N)` converging to `Q` on integer probes. Positive forms have a positive limit (Σ26).
- **Why the walls differ.** The sign is a theorem on the approximants. The obstruction is identification.
- **First test.** Spectral expansion of the height form: which automorphic data carry its weights?
- **Risk.** It expands over cusp forms and central derivatives `L′(f,K,1)`, and the Hecke part of `X₀(N)×X₀(N)` is `End J₀(N)`, cuspidal. Hecke curves on `X(1)×X(1)` are bidegree classes. On the horizon the resonances live on the Eisenstein sector, and the two sectors do not meet [L]. So the known forms do not see zeros of ζ. Central-value signs do not reach off-line points [D].

### Formalized lines with walls of their own

| Line | Established [L] | Boundary [L] | Open core |
|---|---|---|---|
| W2 Representation | Coherent central class functions with Gram positivity ⇔ RH; positive real-part character with transposition defect `Σ(Im α_ρ)²/p₁²`; column Young projections nonnegative; endpoint Toeplitz minors of order `≤200` nonnegative | Sorted occupancy and finite partition stabilizers fail; generic common-pivot tests pass non-characters | Positive arithmetic representation with prescribed cycles (B86) |
| W3 Exact extremal | Real exponentially decaying `Φ=Ξg`, blind at every `log n`, zero pole–archimedean energy; tail exponent 1 attained | `kb≤2` for full `Ξ^k` divisor; no strict energy on blind tests | Positivity of the whole blind program (B18) |
| W4 Weight on a family | Tensor-uniform growth ⇔ purity; nonnegative global trace bounds negative spectrum; Kloosterman fibres pure by Stepanov; explicit moment counts and Tate corrections | Golden has correct invariant weights and full `SL₂` image; pure compression preserves even subspace iff RH | Arithmetic family and global trace (B85) |

### Tested and rejected forms
| Form | Reason | Evidence |
|---|---|---|
| Horocycle renormalization as an independent dynamics | horosphere indicators solve the discrete wave equation; equidistribution at `y^{3/4}` is universal damping | [L] |
| Lee–Yang lift on the prime torus | requires Gamma speed above the total Euler speed, which diverges | [D]/[L] |
| Stable Dirichlet polynomial with critical zeros among ζ zeros | Herglotz carrier rigidity forbids it | [L] |
| Arithmetic capacity for the stencil rate | dual constraints are sawteeth | [L] |
| Agler decomposition in prime coordinates | Gamma coordinate carries all of `S` | [L] |
| Newton polygon or tropical separation of zeros | Taylor ratio `a_k²/(a_{k−1}a_{k+1})→1`, while separation needs `4` | [D] |
| Kac–Murdock–Szegő count of negative directions | symbol bandwidth equals test bandwidth | [D] |
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
**Question.** Does `Σ_{0<γ≤T,β>½}m_ρ(β−½)=o(T)`? Equivalently `T⁻¹∫_T^{2T}log|ζ(½+it)|dt→0`, equivalently `I(½+x+it)→0`, equivalently the damping deficits of the horizon have density zero.

- **Why it matters.** It is `100%` critical-scale clustering, the Euler-mollified log-mean, the outer law, the dyadic depth, Hecke and theta readings, the Abel inner mass at infinity, and the Bode integral at universal damping [L]. By the depth law it is reality at every `τ>0` on density-one windows outside crowds [D]. It gives local Weil positivity at fixed `λ` on density-one heights (B28) [D]. It closes the typical-height layer for RW, ZCG, WD and CTF together.
- **Where it stands.** Empty mollifier: `O(T log log T)` [L]. Selberg's mollifier: `O(T)` [C]. Critical-line proportion `→1` implies it [L]. Under RH: `O(log T)`.
- **The tool gap.** A second moment cannot reach it: a polynomial mollifier leaves the moment above `1+1/(8+6θ)` [L], and moments do not determine the log-mean [L]. Moment `→1` needs `log N≥log²T/(6K₀)` [L], while `log N=o(T)` suffices [L]. The natural input is `log|ζ|=Re P+` bounded error [L], with the mean of the error reduced from bounded to `o(1)`.
- **Tests.** T1–T4, T7 pass. T5: false on `ζ(s)(1−cp₀^{−s})`, `c>√p₀`, where the mean tends to `log(c/√p₀)>0` [L]. T6: prime field, long-mollifier ceiling, tail moment, Carleson embedding, dilation quotient.
- **Limit.** Sparse off-line zeros survive; rare large heights untouched.

### Alternatives, by route
| Route | Question | Why it matters | Tests | Limit |
|---|---|---|---|---|
| Whole programme | Can ζ have exactly finitely many off-line zeros? (B13) | Every finite-support receiver (`N_d` bounded, `κ<∞`, bounded heat count, finite critical energy) becomes an RH receiver [L] | All pass. T5: continuous Beurling one-offs. T6: rigid ¬AAL world | No mechanism: exact ledgers blind, aligned size blind |
| BAG, ZCG | One bounded or polylogarithmic aligned return at each right zero, on a domain right of the line (B89) | AAL [L] | All pass. T5: Beurling one-offs. T6: `TheMissingInputOfTransport` | Returns are atypical on their Bohr set [D]; needs tail control past Kronecker |
| WD | Cluster wall: mean of `exp(2Σ_{a≠ρ}m_aG(ρ,a))` over zeros of depth `≈α/L` is `≤e^{εα}` (B59, B60) | No further analytic input stands between it and the Density Hypothesis near `½` [L] | All pass. T5: impure column | One-log loss; no `D_win`; sparse zeros survive |
| PTT, RW, all rungs | First proportional saving: a loss of `c` of size at length `(log X)^{2K}`, `K>1`, all heights (B46), which implies `R(y,δ)≥exp(y^{c′})` | First all-height sign past size; `a*≥K log log T₀`, all rungs amplified [D] | T1: not known to imply qRH: cut crystal blocks the deduction [L]. T2–T4 pass. T5: columns of depth `>1/(2K)`. T6: non-alignment. RH gives it for `K>1` [D] | Effectively qRH up to shielding |
| PM | Explicit `η(γ)>0` with `V_p(ρ,Y)≥η(γ)` from the Hecke action with no Euler-product inequality (B70) | Zero-free curve from the carrier | All pass. T5: Blaschke insertion | A curve of classical shape at best; VK already gives the bound |
| TH | Exact law for `S*(a,b)`; complete `{2,3}`-smooth spectrum positive at every `0<a<½` (B19) | First cross-chain theorem; merges TH with ZCG's carrier horizon | T2, T3, T7 pass. Model source | Says nothing above `S*` |
| ZCG | Multiplicity `o(log X)` by a non-size input (B47) | First all-height input not reducible to size | T1: RH gives `≪log X/log log X` [C]; T2–T4, T7 pass. T5: FE twins | Bounds collisions, does not exclude them |
| RW | Variation of `r` free of `1/μ` (B3) | Every contact of finite order, step `a*≥a+c(1−r²)/C` | T2, T3, T7 pass. T5 fails | Permits contact; produces no sign |

## 2.6 If positivity, Weil positivity and spectral methods are excluded

**What survives** [L]:

| Class | Receivers | Sign-free input proved |
|---|---|---|
| Production | Siegel and Liouville halves, stencils, one-sided counts as `ψ(x)` bounds, `|M(n)|≤εn+12(w/m)√n+K` | exact integrality; VK-scale rate; Stepanov chain over `𝔽_q` |
| Orbit | column bounds, isolated-zero entry | absolute non-alignment; unique factorization; words; Kronecker with explicit scale |
| Transport | Strong and weak recurrence, target mass, AAL | pair returns at typical base; zero-disc transport; returns are prime returns |
| Cancellation | `M(x)`, one-point and one-window forms, long moments, Báez-Duarte | VK; last-scale and length laws |
| Dominance | Finite carriers real above horizon; heat horizon; Gamma speed on rotations | Gamma speed beats finite Euler speed |
| Identification | Cameras, sharp location, FE-pair flatness | sign-free readout conditional on isolation |
| Rigidity | Exact FE or exact count forces primes; `1/6400` gap; exchange law; Selberg-class discrepancy | zero defect ⇒ rational primes |

All of Σ falls, with PM's Krein branch, TH, W2, W3, the index routes, and the count door, whose output is positivity of a form.

**The natural doors under this exclusion are closed or narrowed.**
- Stepanov over ℤ: its object is a stencil, whose rate is the Mertens level; floor ledgers are blind [L]; linear curve stencils stop at `|a|≤q+1` even over `𝔽_q` [L].
- Nonlinear ledgers: every exact ledger is holomorphic off `s=1`; polynomial ledgers read the twin at `s=2` only [L/S].
- Parity: at power saving it is a zero-free strip [L].
- Rotated identities: coefficients of growth below `Q` are excluded [L/S].

**The question.** *At every large height, does the prime column lose a fixed proportion of its size at some polylogarithmic length?* Precisely: is there `K>1` and `c>0` with `Σ_{p≤y}p^{−½}(1−cos(t log p))≥c·Σ_{p≤y}p^{−½}` at `y=(log t)^{2K}`, all large `t`? It implies that the first-return time of the prime orbit at constant precision is at least `exp(y^{c′})`.

**Why it opens the path.**
- Pure exponential-sum statement: no form, no sign, no spectrum.
- It is the shared barrier: all-height sign past `log log X`, the width axis, the zero-free region up to crystal shielding, and through `AnIsolatedZeroForcesAnEntry` isolated zeros of depth `>1/(2K)` [L/D].
- The proved saving is `≈L⁻⁸` at the size curve; the target is `≈L/ℓ` [L/D]. Its ceilings are known: words `≤1/(2(k+2))`, polynomial phases `≤2/(k+1)`, transfer stops at Kronecker [L]. So any proof uses something else, and the corpus states what that something must be: the multiplicative structure of `log` against additive shifts.

**Tests.** T1: RH implies it for `K>1` [D], and it is not known to imply qRH because of crystal shielding [L]. T2–T4 pass. T5: false on columns of depth `>1/(2K)` [L]. T6: non-alignment, last-moment count. T7: moves Π80, Π87, Σ118.

**Limit.** Honest strength is qRH up to shielding. It does not touch AAL: a one-off at fixed height is invisible to it.

**Second door.** AAL (B83) in prime-side form, and its exact input B89.

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved.** The setting is an exact solution with general `L²` data and a covariant metric [L]. Zeros are resonances of the wave equation on `Γ\ℍ` [L]. On the graph, universal damping is not a law of wave dynamics: fakes have flux, unitarity, causality, positive commuting Hecke at every degree and class [L]. Horocycle renormalization is the wave equation [L]. Hecke on the Eisenstein sector is modular time [L]. KMS gives `¼` its meaning and no force [L]. Reflection is supplied, since the throat has flux with any partner product [L]. The Krein law holds on every system, and a positive flux is the content of RH [L]. What separates true curves from fakes is the count law, whose first instance is the conservation of channels [L].

**The law, read physically [D].** `K(φ+ψ)+K(φ−ψ)=2K(φ)+2K(ψ)` for the number of open channels of a probe is a Born rule: channel counts are squared norms on the probe lattice (Jordan–von Neumann). A fake's channel count is `|𝒬|`, a real count that fails the rule because some probes reverse orientation: `𝒬` is the determinant of the probe on the two-dimensional state space, and universal damping says the state map is elliptic. Over ℤ, `Q` obeys the rule and has no count.

**The question.** *Is there a boundary counting observable on the modular horizon: a nonnegative quantity attached to each integer source `a`, defined by the bulk solution without reference to Weil's form, at bounded distance from `Q(a)`?* Candidates to test: nodal count of the response on the horizon; number of echoes above threshold, whose weights are the integers `ϕ(c)`; degeneracy of a boundary operator sourced by `f_a`.

**Why it opens the path.**
- On the graph the answer is yes on true curves, with `K=ht`, whose poles sit at points of the curve above each place of the base: an exact channel count place by place [S].
- It names the law: a Born rule for channels, not a dynamical law.
- It is the physics form of the Tate statement, so any such observable gives RH [L]. The form `Q` is the exact target, by `h(mξ)/m²→q_x(ξ)` [L].
- A refutation in the natural candidates ends the physical reading of the sign, leaving the horizon as a language.

**Tests.** The full statement implies RH, so it is a structure question and not a door below RH. T2: test each candidate against the bounded-distance condition on one window. T3: RH. T5: fakes fail it [L]. T6: count law, heights, Tate law. T7: passes. A lower rung exists: exhibit the observable on one window of length `≤3/5`, where a naive height is known to exist [L].

**Second physical question.** Is there a flux law `d/dτ Q=−𝓕` with `𝓕` a manifest boundary square at the modular horizon? On every black hole `𝓕=(1−1/q)𝒬`, a boundary square exactly under universal damping [L]. Completing the square uses the frequency of the mode, `√(q−t²/4)`, so the question is why every mode oscillates [D].

**Limit.** Function-field scattering has rank two per elliptic curve and finite rank per curve; every compact probe excites infinitely many modes over ℤ [L]. The geometry is locally pure AdS, so no gravitational dynamics is involved. Physical energy is positive and imposes nothing on mode positions.

## 2.8a If RH is a problem of topology or geometry: question

**What is proved.** RR holds at every aperture on the source cone [L]. Bézout ⇔ RH [L]. Primitive `h¹` is coercive for `a≤181/500` [L]. Bidegree counts see no primitive class, and fixed-rank lattice counts violate surface RI [L]. The effectivity calculus, five currencies and Tate law are theorems [L]. Manin's proof of Hasse is formal for elliptic curves [S]. Λ is an intersection number of torsion orbits on `ℝ/ℤ` [L]. `M(N)` is an Euler characteristic [L]. RH is vanishing of a winding number on every lattice [L/D].

**Where geometry enters Manin's proof.** A constant curve over `F(T)` has a group of points. The height of a point is the degree of a rational function, a sum over places of nonnegative pole orders. Its parallelogram law comes from the addition law. Frobenius is a point. The Tate limit is the degree form. The last line needs no form. Over ℤ the lattice of probes exists and is quadratic. The local terms exist as log-resultants and a Gaussian count. The sum over places has the right shape, with `deg p=log p`. A group whose addition law explains the parallelogram does not exist.

**The question.** *Is there a height machine over ℤ: an abelian group `G` with commuting Hecke endomorphisms `T_n`, `T_n′T_n=n`, and a local-height function `h=Σ_vλ_v` on `ℤ[T_n]`, each `λ_v` defined by a size at the place `v` and `h` bounded below by a product formula, at bounded distance from `Q`?*

**Why it opens the path.**
- It is a precise specification (B95, B87): the object would give RH by the Tate law [L].
- It explains why sign is not payment: nonnegativity comes from `Σ_vlog‖x_i‖_v=0`, which gives `Σ_vlog max_i‖x_i‖_v≥0`. The Weil form's mixed signs at `p` are expected, since local heights need not be positive [D].
- It reduces the geometric problem to one structural unknown.

**Tests.** Stronger than RH: a structure question. T5: Golden has no naive height [L], complex fake has kernel counts and no height [L], so `G` must fail to exist for them. T2: test named `G`: torsion `ℤ[ℚ/ℤ]` with `σ_n,ρ_n`, big Witt vectors `W(ℤ)` with `F_pV_p=p`, gauge torus with Adams operators, idele class group. Each has a decision: does the Rosati trace, if any, equal `Q`? T6: all inputs named. T7: passes.

**First rungs.** A32 at higher genus, so the group is a Jacobian and the form is Rosati. Then one window: a function at bounded distance on length `≤3/5`, built from torsion energy and theta count without using `Q≥0`.

**Limit.** An effective cone exists abstractly and Bézout remains RH-level [L]. Natural Frobenius candidates are refuted in their stated classes [L]. Self-energy is exactly where the sign is lost [L]. If `h` is only defined through `Q`, the statement is empty.

## 2.8b Does closing RH need a new field?

No theorem says so. The evidence is structural: every available tool stops for a proved reason.

| Tool | Why it stops |
|---|---|
| Size estimates | die before half-width `21/40`; exact across independent reflectors; all-height sign stops at `a≈log log X` |
| Positivity-preserving (Markov, Perron) | frustration past `log ρ` |
| Type I/II sieve data | parity blind |
| Linear floor identities | blind to every zero; rate is the Mertens level |
| Polynomial ledgers | exact ones holomorphic off `s=1`; read the twin at `s=2` |
| Barriers, distribution of prime sums | blind to purity |
| Short mollifiers and weights | last-scale floor |
| Second moments for the log-mean | Jensen is sharp for moment data |
| Words and polynomial phases on one block | `1/(2(k+2))`; `2/(k+1)` |
| Diagonal moments, group closure | rounded orbit returns |
| Transfer to rare heights | stops at Kronecker |
| Concentration-compactness | far bubbles do not decouple; Gårding fails on deep atoms |
| Finite computation | finite rungs decide nothing |
| Tensor amplification | carries RH unchanged |
| Integrality | amplifies; no rate |
| Parabolic monotonicity | blind to `t=0` |
| Unitarity, Schur, `C*`, KMS, flux | reach only the edge; hold on fakes |
| Hecke at any place | dispersion relation on resonances |
| Fixed-amplitude Euler positivity; returning coordinates | Laplace cone; columns add; Agler wall |

**What is already built, and where it stops.**

| Field | Object | Stops at |
|---|---|---|
| Arithmetic inner functions | half-plane, causal order by `log n`, one reflector per step | one-dimensional; no sign |
| Prime torus theory | pair `(t,ω_t)` at finite time | absolute savings; proved ceilings |
| Rigid arithmetic of cuts | cut system, ledgers, Beurling metric | parity is the strip; ledgers read `s=2` |
| Arithmetic scattering holography | waves on arithmetic quotients with trees | wave dynamics not the law; count missing over ℤ |
| Effective geometry (AE, ACS, LST) | polar surfaces, effectivity, naive heights | producer of a count |

**The proposal: tail arithmetic of the prime orbit.** All remaining walls point at one range of primes at one height: those past the Kronecker scale, whose phases cannot be prescribed, and below the Vinogradov length, where no saving is known. Zeros at their true scale are events of this range: alignment up to `y` resolves ζ only at `1/log y` [D]. The field studies the law of the phases `t log p` on this range, at a single height, including conditionally on alignment below it.

| Aspect | Content |
|---|---|
| Objects | dark range `log t<p<exp((log t)^{2/3})`; first-return function `R(y,δ)`; Bohr sets with their conditional tails; resonator means; fade profiles `p^{−iτ}≈w(log p/log N)`; Taylor polynomials of `t log(n+h)` of degree above `(log length)²`; almost-prime patterns in sumsets; large-value sets as approximate groups; non-returning coordinate systems |
| Language | dark range, tail event, resolution scale, first return, fade, atypical return, degree past Vinogradov, top of the column, height coupling |
| Mechanisms | additive–multiplicative incompatibility of `t log n`: additive Taylor structure in `n`, multiplicative `log(ab)=log a+log b`; integer gap `|log(a/b)|≥1/max(a,b)`; exclusion of binomial denominators; density of smooth numbers past the diagonal; group closure on heights; certificates in coordinates vanishing vertically |
| Tools to build | proportional non-alignment past Kronecker; a moment past the last diagonal scale that sees smooth-number density; conditional mean values on Bohr sets; a lower bound for atypical members of a Bohr set; a sum-product theorem for the height orbit; Agler-type certificates past the abscissa |
| Test cases | curves (rank one, periodic flow, no dark range); Golden; commensurable steps; continuous Beurling systems (no torus); characters of smooth modulus, where `q`-differencing gives zero-free regions past VK [C]; depth aspect `p^m`, where `p`-adic logarithm gives the same degree structure [C] |

**Criteria it must meet.**
- Reduces to periodic flow at rank one.
- Sees the start of the orbit: not invariant under torus translation, since twin and `ζ` share every absolute moment [L].
- Uses integrality: transfer alone is empty past Kronecker [L].
- Passes its ceilings: not diagonal moments, not one word, not one polynomial phase [L].
- False on impure columns, Golden and heated kernels. Against integer-norm systems it must fail through the amplitude.

**Questions it must answer.**
- What is `R(y,δ)`? Bracket: `exp(c(log y)^{3/2})` to `exp(C_δy/log y)` [D].
- What does a tail look like conditionally on alignment below it, at resolution finer than `1/log y`?
- Why is `t log n` not a generic phase past Vinogradov's degree, given that binomial phases have no saving [L]?
- What replaces `q`-factorization at the archimedean place, where a height has no prime factors?
- Is an atypical bounded return possible at a right zero, and what does its tail look like?
- Which certificates in non-returning coordinates survive past `Re s=1`?

**Limits.**
- Non-alignment speaks about large heights only; a one-off at fixed height is invisible except through the return question.
- First theorem past absolute savings is strip-strength up to shielding [D].
- No mechanism past diagonal moments is known. Baker's bounds are exponentially too weak for the transference [D].
- Since `n^{it}` is completely multiplicative, bilinear sums factor, so Type II amplification is empty in the height aspect [D].

## 2.9 If positivity, Weil positivity and spectral methods are excluded: which field?

Inner-function theory, the certificate half of tail arithmetic, holography's flux and the count door all lose their core. Rigid arithmetic of cuts is the sign-free programme, and its theorems are closures: linear and polynomial ledgers, parity at power saving, rotated relations below `Q`. What remains sign-free and unclosed is exponential-sum arithmetic of one phase.

**What it would be about.** *Sum-product arithmetic of the logarithm:* how the two structures of `n↦t log n`, smooth in `n` and additive under multiplication, are incompatible at a single height. It would stand to ζ as Bourgain's sum-product exponential sums stand to sums over small multiplicative subgroups, where polynomial methods have nothing [C].

| Aspect | Content |
|---|---|
| Objects | phase `φ_t(n)=t log n`; sets with additive structure and phases near a subgroup; words and their moments; sawteeth `r mod k`; carries; the first-return function; dilation operators on `ψ`; finite oscillations; the Beurling space with the FE-defect metric |
| Language | incompatibility, energy between shifts and products, alignment, cut, carry, ledger, oscillation, annihilator, isolation |
| Mechanisms | sum-product growth; integer gap; carry as an average of translations; exact rigidity; Gamma speed as dominance; extremal position at the zero of maximal angle |
| Tools to build | additive energy of phase level sets past the diagonal; exponential-sum bounds for `t log n` at degree past `(log length)²`; a contradiction engine on finite oscillations using carries; effective Kronecker in both directions; a metric geometry of Beurling systems above the gap |
| Test cases | Weil for curves through Stepanov; depth aspect and smooth moduli [C]; Burgess [L in AE]; continuous Beurling systems, which have no carries [L]; Golden, which obeys transport and fails construction [L] |

**Criteria it must meet.**
- Uses no quadratic form with a sign, no self-adjoint operator.
- Proves Hasse–Weil over `𝔽_q` in the same language [L for split hyperelliptic curves through Stepanov].
- Distinguishes rational primes from continuous and discrete Beurling systems.
- Breaks parity only through a mechanism that is at power saving a zero-free strip [L], so its output must include one.
- Is not blind to zero modes: excludes every functional linear in `ψ` read through floors and every exact ledger [L].

**Questions it must answer.**
- What replaces Frobenius? Over `𝔽_q[T]` a self-similar count is quantized and has rate 0; over ℤ a dilation is an average of translations [L]. What does the average give?
- Does a set of integers in an interval have phases `t log n` in a small arc only for `t` below a power of the first return?
- Is a single off-line zero a contradiction with `N(x)=⌊x⌋`? Exact identities cannot say [L]; carries are the unused part of the exact count.
- What is the smallest count distance carrying a one-off among integer-norm systems? Exchange law: a new zero at `β` needs deletion of exponent at least `β` [L].

**Limits.**
- Nothing in the corpus shows the exclusion is forced. Over `𝔽_q` Hodge index, Stepanov and Manin all prove the theorem.
- No source produces parity at any power saving other than a strip [L].
- The field has no named mechanism above VK.

## 2.10 If RH is a physical phenomenon in AdS with a modular horizon: which field?

Arithmetic scattering holography exists. Its positive results are the graph black hole, the Krein law, the one clock, the bulk reading of the log-mean. Its negative results are that wave dynamics, unitarity, Hecke and KMS do not carry universal damping. What it leaves is a count.

**What it would be about.** *Counting holography:* quantum numbers of boundary sources on arithmetic quotients of AdS. A probe is a source. Its count is a boundary degeneracy, an integer on the graph and a sum of local degrees over ℤ. Trees at finite places are local channels, and each place contributes a nonnegative number of open channels after a boundary identity, which is the product formula.

| Aspect | Content |
|---|---|
| Objects | modular horizon and graph black holes; probes as ring elements `y−xπ` and integer vectors `a`; channels; echo integers `ϕ(c)`; Krein square; state map; twisted curve over the base; heights; torsion orbits; radial Pöschl–Teller tower; general `L²` data and metric |
| Language | probe, channel, Born rule for counts, orientation of a probe, elliptic state map, flux, damping deficit, partner law, silent branch, modular clock |
| Mechanisms | exact d'Alembert and contour expansion; flux and energy balance; Hecke as time shift; Krein translation invariance; parallelogram from an addition law; poles of a height as channels above a place; nodal counting |
| Tools to build | a bulk construction of `K` on integer probes; a dictionary between heights on twisted curves and solutions on the graph; a boundary operator algebra whose GNS form on sources is Krein; Lyapunov functionals from counts; modular form of the rank barrier |
| Calibration | true curves, where Manin gives the count [S]; fakes, where the count is not quadratic [L]; throats with `b≠2`, where the partner law fails [L]; non-congruence `Γ` and deformations, where resonances leave the line [C]; harmonic analysis of 2d CFT partition functions, whose scalar sector has sum rules at ξ zeros [C, from memory, not in corpus] |

**Criteria it must meet.**
- Recovers Hasse from channels at all probes [S], and Hasse–Weil at every genus (A32).
- Fails on fakes through the count, not through dynamics [L].
- Supplies the partner law from reflection, since wave systems do not know it [L].
- Fails for non-arithmetic `Γ`.
- Explains blindness of KMS, Schur and `C*` positivity [L].
- Consistent with raw echo spikes and with GUE statistics [L; C].

**Questions it must answer.**
- What is `K` on an integer source of the modular horizon?
- What is the physical origin of the parallelogram law over a true curve, in terms of the graph alone?
- Why is the form a boundary square exactly when modes oscillate, and what oscillation does the modular horizon guarantee?
- What does a compact probe's infinite excitation become in the count: a convergent sum over places?
- Does Hecke at a second place constrain a count, given that it does not constrain flux on the Eisenstein sector [L]?
- What is the bulk meaning of torsion self-energy?

**Limits.** Every proved physical statement is a restatement, an edge theorem, or a statement that a physical law is absent. The geometry is locally pure AdS. Function-field models have finite rank. The programme has not produced one estimate that is not already in the Eisenstein calculus. It is a language until a count exists.

## 2.11 If RH is a problem of topology or geometry: which field?

**What it would be about.** *Height theory of `Spec ℤ`:* heights, not sections, as the primitive notion on the scaling surface. Effective geometry on polar surfaces has every statement of Weil's proof, and Bézout is RH. Manin's route uses fewer inputs: a group, an addition law, a local size. So this field asks for those over ℤ.

| Aspect | Content |
|---|---|
| Objects | integer probes and window correspondences; quadratic form `Q`; local heights `λ_v` with `deg p=log p`; torsion cycles and resultants; torsion energy `T_r`; Arakelov bundles `⊕𝒪(½log m)`; theta `h⁰`; log-counts; polar surfaces; Hecke similitudes; prime complex |
| Language | height, local height, naive height, Tate limit, degree zero, Northcott, product formula, self-energy, moving, abundant class, primitive class |
| Mechanisms | product formula as nonnegativity; Tate limit from an approximate parallelogram; midpoint convexity of log-counts; height principles (bounded above, degree zero); Hecke equivariance; moving a divisor by a Poisson identity |
| Tools to build | a function on correspondences with arithmetic nonnegativity; regularization of torsion self-energy at finite `r`; approximate parallelogram for a log-count with cross terms; moving lemma by Poisson; identification of Rosati trace on a candidate `G`; index formula for the winding |
| Test cases | elliptic curves by Manin [S]; hyperelliptic curves, naive height through Stepanov [L]; Golden, no height [L]; complex fake, kernel counts without height [L]; Frey and quintic data [L]; genus-one primitive correction `deg(m−nF)` [L] |

**Criteria it must meet.**
- Recovers Hasse–Weil for curves from heights, with no form as input.
- False on Golden and on shifted data whose Tate coefficients are nonnegative [L].
- Reads the test beyond its two degrees [L].
- Infinite-rank in the limit [L], with no finite-dimensional norm realization on a window [L].
- Does not define its height through `Q`.
- Sees torsion: uses `ℤ⊂ℝ`, which no Beurling system carries [L].

**Questions it must answer.**
- What is the group, or what replaces it?
- What is the addition law behind a quasi-parallelogram over ℤ?
- Where does `log(1/(1−r))Σx²` go: which archimedean term pays it, and at what `r`?
- Can a theta count with cross terms be defined from local data? Free polarizations are soft [L].
- Why does the prime complex have Betti numbers `≈cN` and Euler characteristic of expected size `√N`?
- Do Hecke correspondences generate the ample cone?

**Limits.** Finite-rank carriers, separable assemblies, connected links and natural Frobenius candidates are refuted in their stated classes [L]. Actual modular surfaces see only the cuspidal part [D]. Heights over number fields give central-value signs, not off-line zeros [D]. Over `𝔽_q` the same statements are consequences of having a variety.

## 3. The one question

**Does the prefix decouple from the top collar at a fixed critical ratio?** Let `R=c⁸/log N` be fixed, `y` the top-collar part of `U` and `p` the prefix. Is the Schur cost of the prefix and low packet against the collar negligible:

`|B(U_y,U_p)|²≤o(1)·Q(U_p)·(Q(U_y)+B_R‖U_y‖²)`, on the complement of a low packet whose signed polar part is retained?

The expected answer is yes. Then a negative direction at ratio `R` is a collar direction, collar Gårding and Γ-liminf give a strong limit, and `log R_c(ζ)≳a*(ζ)`, with `R_c` the largest ratio below which the matrix is eventually positive definite. HF, SRT, the packet branch of AIP and the atomic branch of ACS stop being separate problems at every fixed ratio.

### Why this one

**This is a structural question, because no analytic estimate below quasi-RH is both reachable and consequential.** By 1.2 a statement below qRH leaves sparse deep zeros alive, and that leaves these kinds:

| Kind | Best form | Why it is out of reach | Evidence |
|---|---|---|---|
| One-offs | AAL (B83), finite support (B13), aligned return (B89) | no estimate of any kind; exact ledgers blind; typical aligned shifts large in every world | [L]; [D] |
| 100% near the line | depth density `o(T)` (B57) | moment `→1` needs `log N≥log²T/(6K₀)`: a superpolynomial mollifier with no off-diagonal theory | [L]; [D] |
| Rate near `½` | cluster wall (B59) | isolated rate `2−2γ` against fourth-moment rarity `4γ` balances at `4/3`, Ingham's slope; passing it is a classical barrier | [D]; [C] |
| All-height sign | proportional saving (B46) | sign at `a=K log log X`, `K>1`, is a zero-free strip up to crystal shielding; proved `L⁻⁸` against required `L/ℓ`; ceilings proved | [L]; [D] |
| Production, parity | stencil rate (B55), parity (B67) | rate is the Mertens level; parity at power saving is a strip | [L] |
| **Reduction** | **this question** | **one named inequality, with its neighbours proved** | **[L]** |

### What is proved around it

| Channel | Status | Module |
|---|---|---|
| Top collar | Gårding at every `R`, with seventh mass and `W₈` | `UnrestrictedAtomicGardingFailsAndCollarGardingHolds` |
| Far tail `y→−∞` | Γ-liminf keeps `α_R∫_{y<0}F²e^{−8y}`, `α_R>0` at every `R`, on sequences with bounded `W₈` | `TheCriticalFormHasAGammaLiminf` |
| Deep atoms | positive; `W₈` unbounded; no Gårding | `UnrestrictedAtomicGardingFailsAndCollarGardingHolds` |
| Prefix mass | `(∫|prefix|)²≤C_φP/(4c)`; reserve `θ log N/(8C)` on far conductors at small multiples | `ThePhysicalPrefixHasSmallL1Mass`, `TheCriticalFarComplementRetainsTheCollarWeight` |
| High frequency | a bounded form keeps high frequencies small; `L¹` limits become strong | `BoundedWeilEnergyUpgradesL1LimitsToStrongLimits` |
| Prime shifts | `|P|≤εW₈+B_ε‖H‖²` | `PrimeShiftsAreInfinitesimalInTheExponentialWeight` |
| Precompactness | physical and Fourier tails; bounded collar mass | `PhysicalAndFourierTailsGiveCompactness`, `ThePhysicalCollarHasBoundedExponentialMass` |
| Far conductors | coercive for `R<R*` | `TheFarComplementHasAnExplicitRatioInterval` |
| Low packet | positive with polar part through `⌊(log N)^{13/32}⌋` at every `R` | `TheCriticalLowPacketRetainsItsSignedPolarPart` |
| Periodic charges | four channels below the eighth root; `J_N=O(log N)` iff gcd profile | `TheFourChannelsOfAPeriodicCharge`, `TheJumpEnergyDetectsTheGcdProfiles` |
| Prefix–collar cross operator | sparse, weights `(n/m)^{½}Λ(m/n)` [D]; unbounded by no theorem | — |
| Conductors `(log N)^{13/32}` to `N^θ` above `R*` | open (B7) | — |

### What makes it mathematics and not bookkeeping

The cross operator couples atoms of very different scale, so size may suffice on far prefix conductors; on the low packet it cannot, since the pole line is spread over the prefix and the low packet's positivity is polar. A Schur complement against the window margin fails: `λ*(c)` decays doubly exponentially [L] and the reserve `e^{8L}` only exponentially [D]. The estimate is an effective margin of about `(log R)^{O(1)}/R` and a tail paid from length `(2/7)log R`, so half-width `(1/7)log R` suffices [D, an estimate and not a proof].

### What an answer does

| Answer | Effect |
|---|---|
| **Yes** | At each ratio HF, SRT, AIP packets and ACS atoms become a rung of RW; the all-ratio statement is `a*=⊤`. B6 becomes B1. |
| **Yes** | A theorem on the critical curve: the complete matrix at exponent `1/8` is positive definite at every ratio with `log R≲a`, from one verified window, far past the proved multiple `2K₀`. |
| **Yes** | The critical-curve content of CACT (253 modules), AHD (148), CAF, ACPL, RAPT, TM and ADT is finished, and A9, A12, A13 stop being route tasks. Effort moves to B2, the count and the dark range. |
| **Yes** | A template: Gårding on a collar, Γ-liminf and compactness turn a critical family into a window. |
| **No** | A sequence on which prefix–collar coupling stays comparable to the reserves, in Lean. That channel is then exactly the independent content of HF, and HF keeps a wall of its own. It is not a negative direction, so it does not touch RH. |

`R_c<∞⇔a*<∞` either way on collar-supported sources: the limit pencil is negative once a negative window is available and `R` is large [D].

### First steps

1. Assemble A10 for collar-supported sources and state `log R_c^{collar}≳a*`.
2. Bound the prime cross operator between far prefix and collar in operator norm, against `θ log N`.
3. Pay the Gamma and pole cross terms with the rank-one polar structure.
4. Treat low packet against collar with the signed polar part (A12), through `⌊(log N)^{13/32}⌋`.
5. Close conductors above `(log N)^{13/32}` on the collar (A13).

### Validation

| Test | Verdict |
|---|---|
| T1 | Pass. Under RH no negative sequence exists, and the reduction says nothing about zeros. |
| T2 | Pass. A stated inequality to prove or refute. |
| T3 | Pass. The table above. |
| T4 | Pass. Each window is a rung; the reduction is uniform in `R`. |
| T5 | **Fails, by design.** It is a reduction, expected to hold on any Chebyshev-bounded datum, so it does not separate ζ from a fake. |
| T6 | Pass. Every neighbouring channel is proved. |
| T7 | Pass. It moves Σ1s, Σ87, Σ88, Σ122. |

**By the tests this is not a door to RH. I found no question below quasi-RH that passes all seven and also has a working tool.** Those passing all seven, B57, B59, B13 and B89, are in the table of kinds above.

### Limits

- No sign wall moves. B1, B2 and every RH-level item stay as they are.
- ZAL and AAL are untouched, and typical heights gain nothing.
- The constant between `a*` and `log R` is only estimated, and A13 may hide a real channel.
- The gain is architectural: fewer independent problems, one theorem on the critical curve, and one scalar left on the sign side.

### Why the others rank lower

- **AAL (B83), finite support (B13), aligned return (B89):** decisive, the exact split of RH, with a rigid negative world and no estimate to start from. Typical aligned shifts are large in every world [D], so the input is about atypical tails.
- **Log-mean (B57), cluster wall (B59):** real advances on typical heights, blocked at the mollifier length and at Ingham's slope.
- **Proportional saving (B46), past VK (B15):** effectively a strip up to shielding in the first case and a historic barrier in the second.
- **Count (B87):** closes the sign, and it is RH-strength. Its rungs are structural and lack a stated inequality until a candidate is named: first A32, then a named candidate on one window.
- **Hecke dispersion floor (B70):** `V_p≥η` already follows from the formula for `V_p` and VK; the question asks only for a different proof.
- **`{2,3}` torus positivity (B19):** a compact check at fixed primes, and the torus turns negative by `P=19` in scans [N].
- **Smallest FE defect (B84):** a barrier for defect-stable arguments, with no gain on ζ.
- **Near-extremal mollifier (B66), `D_s≥0` (B68), bounded `Ψ` (B2):** RH-strength.
