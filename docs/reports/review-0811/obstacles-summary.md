# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `2f84c625ef` plus the working tree of 2026-11-08.

Evidence: `[L]` Lean source; `[S]` Lean source unfinished, unintegrated or uncommitted; `[K]` Lean with transitive axiom audit; `[D]` deduction, not a Lean theorem; `[N]` numerical, uncertified; `[C]` classical, not formalized.

**38 live formulations; 9 candidates.** HJ→PA; BSH→CDC; FEL's BSY criterion→CTF. Candidates: APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF.

## 1. Big picture

### 1.1 RH has two halves, and the second half is a self-improvement
RH ⇔ ZAL ∧ AAL ⇔ ZAL ∧ zero-disc weak recurrence ⇔ ZAL ∧ a subexponential lower bound for the polar ground energy [L]. ZAL (finitely many zeros beyond each positive depth) implies quasi-RH [L]. AAL is exactly the implication "a right abscissa bound valid for all zeros above some height holds for all zeros" (`asymptoticAbscissaLaw_iff_xi_eventualToGlobal`) [L], and it is invariant under the symmetric shifts `ξ(s+a)ξ(s−a)`, which keep the functional equation and move every abscissa by `a` [L]. So AAL is not a statement about the line `½`: it is the step that turns finitely many exceptions into none. `qRH ∨ AAL` [D]. Under AAL, RH ⇔ ZAL ⇔ finite off-line support ⇔ `κ(K_ζ)<∞` ⇔ bounded non-real heat count ⇔ finite critical source energy ⇔ eventual Hadamard positivity ⇔ eventual central-gap budget [L]. Failure of AAL is one rigid object: a finite top layer with attained top excess, `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})` with `T` a unique trigonometric polynomial, sign changes at bounded log gap, and two-prime dilation annihilation of `ψ` [L].

### 1.2 Why there are three walls, and what the curve proof does that ℤ cannot
No test is compactly supported on both sides of the explicit formula [D]. A compact prime side (windows, Σ) leaves infinitely many zero modes, and only an exact sign decides. A localized zero side (Gaussian or band-limited weights, Π) makes a crude bound sufficient — RH ⇔ for every rational `r≥½`, the Gaussian prime sum `P(ε,r)` is bounded above on `ε≥1` [L] — but leaves an infinite prime sum at square-root precision. Γ is the involution `ρ↦1−ρ` and the selection of ζ.

The corpus proves RH for every hyperelliptic curve over a finite field of odd characteristic by three steps [L]: a crude count at every level of the base-change tower (Stepanov's auxiliary polynomial), self-improvement of any constant-factor bound to the sharp one by power sums (finite rank), and the functional equation pinning every mode to the circle. Over ℤ the crude statement is ZAL, the self-improvement is AAL, the functional equation is that of ξ [D]. Two of the three steps have no ℤ-counterpart in the corpus: there is no Frobenius substitute that makes a crude producer cheap (Stepanov over ℤ is integrality plus Nair and stops at Chebyshev [L]; the Frobenius over `𝔽_q[T]` is a factorial stencil of rate 0, over ℤ the rate is the Mertens level [L]), and there is no crude regime to self-improve from: `|ψ(x)−x|≤C√x` is false, any exponent `½+ε` is RH, and tensor indices are `0` or `∞` (Π111) [L/D]. Infinitely many modes (the rank barrier, Γ100) is what removes the crude regime.

### 1.3 The sign plane
Weil's form is the average of its frequency packets [L]. Sign is a function on `(a,log X)`: all heights to `a≈log log X−log 4` by size [L/D]; every shaped test on density-one heights to `a=δlog T/(64M²)`, with bad heights of Gaussian tail and measure `≤T^{1−1/(64K)}` at `a=K log log T` [L]; isolated zeros visible at `a≈(1/2d)log(4d log X)`, fixed depth hidden by a cut crystal to `(log T)/36`, sharp location at `λ>1` [L]; RH ⇔ `Ω≥0` everywhere [L].

### 1.4 The window sign is one scalar flow
The tower is a canonical system to contact with `H₁H₂=1` [L]. `L′=q−sinh 2L`; `|L(x)|≤artanh e^{−2(x−c)}+2osc_{[c,x]}Ψ` [L]. **RH ⇔ `Ψ=½log H₁` is locally bounded**, and off RH `L` is unbounded above every base [L]. The margin ceiling forces `m≳e^{2a}`, above the Born bound: the potential is a nonlinear collective response [D].

### 1.5 The certificate is causal
A window is PD iff it has a positive-margin outer predictor [L]. Reflection data are free coordinates; the forward map from primes has an exact tangent; margins are concave in the weights [L]. Every point of the window cone carries local density `1+O(e^{−a})`, positive support density and `|ψ_λ(X)−X|≤CX^{5/6}log X` for `X≤e^{2c−3}` [L]: window positivity is a prime count with power saving on the window's range.

### 1.6 The critical curve is the window, and only the pole is left
At critical overlap `R=c⁸/log N` the thresholds form one chain `0<R_c≤R_c^{PSD}≤R_polar≤R_high=⨅_{A≥0}windowThreshold(A)≥c₀e^{6a*(ζ)}`, each `=⊤` iff RH [L]. At each fixed ratio, physical tearing fails at Schur ratio `4/13`, conductor-adapted splitting decouples the far complement, a finite conductor prefix leaves the low packet arbitrarily small, every fixed nonpolar conductor has vanishing top-window row uniformly on critical bands, and eventual PSD gives polar payment on every window [L/S]. What is unpaid is the pole channel `m=1`, its retained diagonal and the collar `L²` debit; the pole against growing windows at every ratio is RH [L]. The critical-curve programme carries no sub-RH content.

### 1.7 Below the onset the form exchanges aperture for ratio
Window positivity at half-width `a` excludes every zero of depth `≥¼` up to height `e^{a/K}`; this makes the lag `|Φ(L)|≤Ce^{L/4}` for `K(L+2)≤a`, the Mertens lag `O(x^{−1/4})`, the pole self-energy sharp (`|e^{−s}D(s)−κ₀|≤Ce^{−s/2}`), the pole cross pairing compressed, and the polar payment possible for `R≤c₁e^{c₂a}` [L]; conversely `windowThreshold A₀=⊤` gives `windowThreshold A≥ce^{3A₀}` [L]. The explicit formula squeezes `|ψ(x)−x|≤Cx^{7/8}` from `β≤¾` to height `√x` [L]. Every exchange is single-exponential and none raises `a*(ζ)`.

### 1.8 The theta wall is ζ on the critical line
The theta all-rank problem reduces to the frequency-adaptive head `M(b)=⌈|b|/2+B⌉`; the omitted pair sum costs at most half the first-atom floor `aC_Γ/cosh(πb/2)` in every polynomial-square integral [L]. For fixed `M` the head at frequency `2τ` over the natural Gamma weight is `(4/√π)|Σ_{n≤M}n^{−½+2iτ}|²+o(1)` [L]; fixed heads, summable absolute majorants and compact cores fail [L]. With `M≈|b|/2` the head is a partial sum of length half the height, which approximates `ζ(½+ib)` to `O(|b|^{−½})` [C]; uniformity of the fixed-`M` asymptotic at `M=M(b)` is open. So the sign is automatic where `|ζ(½+ib)|` is large and is decided by second-order terms where the head is small, near the zeros of ζ on and next to the line [D].

### 1.9 The inner mass has a second expression, and the dilation decides
On `Re s>½`, `E` has inner factor the Blaschke product of right zeros [L]. `exp(2I(1))=inf_Q∫|ζ exp Q|²dP₁` [L]. For one fixed `0<δ<½`, RH ⇔ zero dilation surplus ⇔ the critical-to-shifted Szegő budget ratio equals its outer value; Euler prefixes leave it invariant [L]. Selberg's mollifier gives off-line first moment `≤(67/1000)V`, depth `O(T)`, bounded inner field at infinity [L]. Mollifiers are outer: they reach the inner mass in size, not in its vanishing [L/D].

### 1.10 The near-line wall is the dark range
Near-unit mollified moments need `log N≥log²T/(6K₀)` [L], the length of an Euler mollifier over primes up to `≈c log²T` [D]; prime phases become absolutely non-aligned exactly there [L]; conditional tail laws stop at the Kronecker scale `y≈log T` [L]. The log-mean, the cluster wall, the short-sum barrier and the AAL tail input sit on one range of primes, from `log T` to `exp((log T)^{2/3})` [D].

### 1.11 Production, Farey, the nerve, the core and the barcode are the Mertens level
A producer of rate `ε` gives `|M(n)|≤εn+12(w/m)√n+K`; floor `ε≥c/(√K(1+log K))`; rate `K^{−a}` ⇒ `Re ρ≤1−a`; all `a<½` ⇒ RH; none past `½`; RH places the exponent in `[¼,½]` [L]. Twin pairs carry a quarter floor [L]. Zeros are the kernel of the cut system [L]. The exact identity `Σ_{k≤x}F(⌊x/k⌋)=⌊√x⌋` pins `λ`; a power-saving Liouville bound is a zero-free strip [L]. RH ⇔ Farey `L²` discrepancy `≤Cn^{−1+δ}` ⇔ every smoothed totient-weighted Farey count of order `C` is `mC²+O(C^{½+ε})` [L]; `M(N)=−χ̃` of the prime-star nerve; the connected prime core has augmented Euler characteristic `M(N)+#primes(N/2,N]`; the persistence barcode is the odd squarefree `m` with bars `[m,2m)` [L]. One number in five languages.

### 1.12 The prime orbit at one height
Every window `exp(10y√(log y·log log y/δ))` enters every `δ`-box on primes `≤y` [L]. A weak return is a spike `|ζ(1+1/log N+it)|≍log N`; at bounded harmonic defect `R≥exp(c(log N)^{3/2}/log log N)` [L]; at precision `≍y^{−9/2}` the RH bracket `R>exp(√(y/(48log y)))` holds [L]. Proportional saving is the absence of early heavy returns [L]. Ceilings: rounded orbit; one word `≤1/(2(k+2))`; one binomial block `2/(k+1)`; transfer stops at Kronecker; the jet of `t log` moves along one curve [L].

### 1.13 Zeros are tail events; certificates past the abscissa are tail-good
`ζ=E_y·ζM_y`; the head never vanishes on `Re s>0`, so the zeros of ζ are the zeros of the tail at every cut [L]. Returns at right zeros are tail-bad at every cut, density zero; nonvanishing targets return at positive density [L]. Conditional on head alignment the tail is Gaussian while the resonator is shorter than the height; arithmetic mean values bound smooth × prime moments by collision counts [L]. These are upper bounds: a bounded return at a zero needs the existence of a tail event, and past the Kronecker scale nothing distributional is known [D]. Euler coordinates stop at `Re s=1`; head–tail certificates exist exactly at tail-good heights [L].

### 1.14 ζ is isolated, positivity is blind to finite layers, and surgery on ζ is detected
FE `L¹` defect `≤1/6400` forces the rational primes; count error `o(log n)` forces them among positive integer-norm systems; the exact parity identity pins `λ` [L]. Finite top layers exist in every positive Euler-product class tested: continuous systems; discrete and integer-norm systems with linear counting (holomorphic on `Re s>½`); rational-prime labels with multiplicative natural coefficients and linear counting, holomorphic on `Re s>17/30` with exactly `3/5±iγ` there [L]. Nonnegative two-prime Dirichlet polynomials and nonnegative polynomials in the Hecke operators `T₂,T₃` annihilate any finite set of zeros with constant coefficient 1 [L]. Every one-off fails at the critical line [L/D]. In the opposite direction, relocating two actual critical pairs of ζ to the lines `¼,¾` by a rational multiplier normalized at `0` and `1` produces a signed, integrable, zero-mass Dirichlet density that is negative on `(1,1+ε)` under every finite Dirichlet filter [L/S]: a top layer cannot be put into ζ by surgery that keeps positive coefficients. **What separates ζ from every countermodel is the functional equation on `Re s=½`, and a top layer of ζ would have to be intrinsic** [D].

### 1.15 Physics: every horizon observable is the width axis
The modular horizon is the quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)` [L]. For `0<δ≤¼`: every zero has `Re ρ≤1−2δ` ⇔ every compact pulse rings down at `e^{−(δ−ε)τ}` ⇔ every horocycle mean converges at `y^{½+δ−ε}` ⇔ every smoothed Farey count does [L]; RH ⇔ `y^{¾−ε}` ⇔ every resonant mode of the Lax–Phillips semigroup decays at `e^{−t/4}` [L]. The horocycle mean is the totient-weighted Farey count of order `y^{−½}` [L]. Sharp sources (shells) thermalize at `y^{½}log(1/y)` unconditionally, and their `¾` rate needs Möbius × circle-problem cancellation that RH does not control [L]. The Narain AdS₃ partition — modular invariant, its scalar Mellin transform continued with every arithmetic pole — has a double-average remainder with exactly the VK saving at a universal exponent; `¾` ⇒ RH and every exponent `>¾` is impossible [L/S]. The cusp channel is the full classical Maass theory: existence, discreteness, `N(Λ)≍Λ`, Rankin–Selberg continuation, mean-square law; its horocycle energy converges at `y^{½−ε}` and at `y^{¾−ε}` under RH, and a rate `y^α` forces `Λ_g(ρ/2)=0` for `Re ρ>2−2α` [L/S]. The primon gas (Hartnoll–Yang) gives thermal means that are Euler factors of `ζ(2e^β+1)` [L], at real points right of 1.

### 1.16 The count: a quadratic half and a count half
A count law on a black hole `(q,t)` has two halves [L]. Its quadratic half is a nondegenerate Born rule `MᵀSM=qS` for the delay, which exists iff modes come in partners `α↦q/α` — the functional equation. Its count half is positivity, which puts every mode on `|α|²=q` — universal damping. The boundary algebra `R[π]/(π²−tπ+q)` with the partner involution `π*=q/π` has the Krein square as the GNS form of every state and a positive state iff damped; with the Hilbert involution it is a `C*`-algebra on every black hole, fakes included. Linear counts (shells, Farey points, echoes) never obey the law; Hecke supplies only the conservation `K(1+πⁿ)+K(1−πⁿ)=2K(1)+2K(πⁿ)`, which fakes keep; non-arithmetic Hecke triangle groups fail the count at their second place [L]. On curves the count law holds for every hyperelliptic curve over every finite extension, produced from a crude bound at every level [L]; the Rosati form is the equal-weight Born rule, and naive height ⇔ nonnegativity ⇔ count law at every level ⇔ unitarity [L]. Over ℤ the quadratic half holds unconditionally (Hecke at `p` is an exact isometry of `Q`) and **RH ⇔ `Q` is the Tate limit of an `ℕ`-valued count**; no parallelogram law is needed [L]. The content is a count defined without `Q`.

### 1.17 Topology of the prime complex is classified and blind
The prime-product complex is a bouquet of spheres; its persistence is the interval module of odd squarefree `m` with bars `[m,2m)`, over every ring, and Dirichlet weighting gives an isomorphic persistence functor for every `s∈ℂ` [L]. With prime-valued boundaries, homology acquires `ℤ/2` classes on `[2m,3m)` for squarefree labels coprime to 6, a nonsplit extension and torsion exponent 2 [L/S]. Upper-half primes are isolated points, so every map homotopic to the identity has `≥N/(4log N)` fixed points; the connected core is a bouquet of odd-squarefree composite spheres with Euler characteristic `M(N)+#primes(N/2,N]` [L]. Renormalized torsion forms converge in operator norm only on `ℓ²(n^δ)`, `δ>0`; on unweighted `ℓ²` the mixed prime row is unbounded [L]. `M(N)` appears as the signed count of a fixed barcode; nothing in the homotopy type or the persistence module sees `s`.

### 1.18 Hull
Haar-a.e., fair-coin-a.e. and order-two fibres extend zero-free to `Re s>½` with natural boundary `½`; the product of a fibre and its antipode is `ζ(2s)`; the Liouville point extends iff RH [L].

### 1.19 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| Markov, Perron, sign-gauge balance past `e^{−3/4}`, `log ρ` | refuted | [L] |
| Size-only payment of primes | ends before half-width `21/40` | [L] |
| Floor tower as aperture producer | stays below `0.3621` | [L] |
| Weighted Gårding on the whole horizon | false on deep atoms | [L] |
| Physical tearing at the collar boundary | Schur ratio `4/13` | [L] |
| The critical ratio as an independent sub-RH problem | thresholds end at the window threshold; only the pole channel remains | [L/S] |
| Uniform logarithmic Gamma reserve in coefficient norm | resonant two-copy profiles | [L] |
| Fixed theta heads; summable absolute pair majorants; compact cores | no margin; harmonic diagonal; geometric growth | [L] |
| Positive Laplace mixtures; all-base torus positivity of the theta amplitude | excluded | [L] |
| Fixed or limiting amplitude locking | adds nothing | [L] |
| Product certificates in Euler coordinates past `Re s=1` | cannot cross | [L] |
| Parabolic structure as selector of `t=0` | blind | [L] |
| Barriers, short detectors and weights | blind to purity | [L] |
| Moment data for the log-mean; outer mollifiers for the inner mass | blind | [L] |
| Diagonal moments, group closure, early orbit against a return | blind | [L] |
| Slow-return bounds on discs crossing `Re s=½` | the premise is RH | [L] |
| Schur, `C*`, KMS, reflection positivity as zero locators | blind | [L] |
| Positive Poisson measure of the Hecke algebra; positive Hecke polynomials | hold off the line; annihilate finite resonance sets | [L] |
| Wave dynamics, flux, unitarity, Hecke, FE at genus two, first-level counts, integrality as universal damping | fakes carry all | [L] |
| Linear counts as count laws | degenerate | [L] |
| Hecke at a second place as a count law | conservation only | [L] |
| Narain remainder past `¾` | impossible | [L] |
| Sharp horizon sources at the RH rate | need cancellation beyond RH | [L] |
| Integer stencils as a mechanism independent of Möbius | rate is the Mertens level | [L] |
| Polynomial ledgers as parity input at zeros | twin shares every leading pole | [L] |
| An independent parity source at power saving | is a strip | [L] |
| Bounded count error as a selector | new zero with signed generators | [L] |
| Positive Euler product, integer or rational-prime norms, linear counting as AAL | finite top layers exist | [L] |
| Nonnegative Dirichlet coefficients plus proximity to `1` on `Re s≥1` as zero exclusion | two-prime annihilators | [L] |
| Mean spectra as detectors of zero relocation | relocation invisible | [L] |
| Discrete Morse matchings of the prime complex | Betti number `≍N` | [D] |
| Fixed-point localization with `O(√N)` fixed points | `≥N/(4log N)` fixed points | [L] |
| Persistence of the prime complex as a zero detector | isomorphic for every `s` | [L] |
| Torsion forms on unweighted `ℓ²` | mixed row unbounded | [L] |
| Thermal averaging (primon gas) as a strip input | Euler factors at real points `>1` | [L] |
| Extremal-angle position alone | has a polynomial model | [L] |
| Rotated relations with coefficients of growth `exp(C√\|w\|)` | trivial | [L] |
| Raw echo decay; near-arithmetic ladders | excluded | [L] |

## 2.1 Tasks that are just work

Difficulty is established only where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### Finite verification
| # | Task | Routes | Basis |
|---|---|---|---|
| A1 | Lean-certified `RHVerifiedThrough T` past 67 with zero location (Turing count), first `T≈10²–10³` | all rungs | `hardySEM` sign chains; Fejér budget is a bounded-height method |
| A2 | Numeric values of `windowHeight`, `xiMassHeight`, `heatGridHeight`, theta `D` | window routes, TH, LA, HCF | explicit definitions |
| A3 | Two-weight membership past `a₀`: odd unit window, `log 2`, `½log 5` | RW, OWU, EWU, ACT, SWC, HF | A1–A2 or rigorous Galerkin |
| A4 | Theta rank 15 and beyond at every `0<a≤½`, one rank at a time (unverified past 14) | TH | radius-12 power core, height 67, coupled current tail |
| A5 | Lean certificate of the center-tail failure | TH | finite computation |
| A6 | Cone widths `𝒜(c)` past `c=0.66`; Lévy margins at `½log 3` | PBAP, ACS, RW, CHT | convex programs |
| A7 | Certificates on the nine anti-diagonals `{2,3,4,5,7,8,9,11,13}` (unverified; task statement unsettled) | ACT | finite case analysis |

### Critical curve
| # | Task | Routes | Basis |
|---|---|---|---|
| A9 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | HF, SRT, AIP, ACS, SC | proved limits |
| A13 | Near-gcd charges and periods beyond the admissible scale `M₀(N)` (unverified) | AIP, HF | gcd-defect coercivity through `M₀(N)` |
| A38 | Integrate the conductor-resolution modules: top-window conductor row cancellation, all-ratio deep conductor pairings, nonpolar collar residuals | HF, SRT, AIP | complete source |

### Flow, near-line, continuation, orbit
| # | Task | Routes | Basis |
|---|---|---|---|
| A16 | Numerical `r,m,q` for `a≤1` [N] | RW | Galerkin |
| A18 | Twisted second moments past `21/50`: to `½`, Conrey `4/7` [C] | WD, census | raises rate `2θ` |
| A19 | Heat horizon toward its method floor | ZCG | profile margin |
| A20 | Jensen rung toward the saddle scale (unverified) | LA, FFP | saddle identity |
| A21 | Census items; logarithmic two-point Chowla [C]; runs past five | MC, ACS, census | classical |
| A24 | Certified scans of `S_S`; brackets for `S*(a,b)` | TH | column calculus |
| A37 | Resonator mean of `\|ζ\|²` with resonators growing below the Kronecker scale, length `T^θ`, `θ<1` (unverified) | BAG, ZCG, PTT | fixed-resonator limit, mean-value theorem, arithmetic mean values |

### Theta, horizon, counts, production, descent, integration
| # | Task | Routes | Basis |
|---|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` with its constant [C] | PM, BHR | order `N(Λ)≍Λ` proved; heat trace finite |
| A28 | Reciprocal quadric traces = vanishing-cycle Frobenius traces (unverified) | ACS | exact projective quadric counts over every extension |
| A30 | Best stencil exponent under RH in `[¼,½]` (unverified) | WL, MC | quarter rate, half scale |
| A33 | Fourier coefficients of the cubic residue = cubic theta coefficients and Gauss sums [C] | MC, MMD | nonzero residue, continued Fourier modes |
| A39 | Integrate the untracked horizon modules: universal VK rate of the Narain average, complex Mellin shift, Rankin–Selberg growth | PM, BHR, ASH | complete source |
| A40 | Integrate the untracked relocation, persistence and torsion modules: first-gap relocation obstruction, two-prime arithmetic cores, integral persistence, weighted integral coefficients, compact probe inclusions | BAG, ZCG, MC | complete source |
| A41 | Count law for every curve over `𝔽_q` (Bombieri–Stepanov), first case plane quartics [C] | ACS, PM, CTH | crude-bound self-improvement [L]; hyperelliptic Stepanov [L] |
| A42 | Uniform fixed-head theta asymptotic at `M=M(b)≈\|b\|/2` with an effective error (unverified) | TH | fixed-`M` asymptotic [L]; Bessel–Gamma transport [L] |
| A43 | Identify `Λ_g` with the completed `L(g×g,s)=ζ(s)L(Sym²g,s)` for Hecke eigenforms [C] | PM, BHR | Rankin–Selberg unfolding [L]; Hecke eigenforms [L] |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window | RH; fixed length sub | all sign routes |
| B2 | Bounded oscillation of `Ψ` on every bounded aperture interval | RH | RW, SZ, CHT |
| B3 | Variation of `r` free of `1/μ` | sub | RW |
| B4 | Two-sector certificates; outer predictor at every window; every actual echo in its Schur band | RH | sign routes |
| B5 | Kick admission at every stage | RH | RW, GWZ, WTZ, HF |
| B6 | Full-space sign eventually at every `K`; equivalently every critical threshold `=⊤` | RH | HF, SRT, AIP |
| B8 | Head thresholds for every `d` | RH | HF, AHD |
| B9 | No zero mode at any length | RH | HF, TG, SC, EHT |
| B10 | Top coprime stratum | RH | HF, ACS, ADT |
| B11 | Exact SOS on a two-prime lattice | RH | HF, SC, ACS |
| B12 | Index ceiling uniform in resolution | ≥qRH | CHMD, SRT, SC |
| B13 | Exclude finite nonzero off-line support | sub | whole programme |
| B14 | Window negativity exponent `<½`; any interior width value, incl. a horocycle, Farey, pulse or Narain exponent past `½` | ≥qRH | width axis |
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
| B30 | Heat grids at every degree; Gaussian prime ceiling at every rational height | RH | HCF |
| B31 | Hausdorff signs below the explicit shift | RH | PA |
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
| B101 | Polar payment of the pole channel at every ratio on windows of length `→∞` | RH | HF, AIP, SRT |
| B102 | Sign of the frequency-adaptive theta head at every degree; its leading term is `\|Σ_{n≤\|b\|/2}n^{−½+ib}\|²`, so the sign is decided where that partial sum of ζ is small | RH (all ranks) | TH |
| B104 | `R_c(ζ)=R_high` | method | HF, SRT |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B48 | Deciding input at square-root precision; equivalently a crude zero-localized prime count at every level (a Stepanov method over ℤ with a Frobenius substitute) | RH | WL, MC, PBM, RB, JAS, CTF, HCF |
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
| B96 | Conditional law of the Euler tail at the Kronecker scale; in particular lower bounds for tail events | sub | BAG, TH, WD, TAPO |
| B97 | Constant-precision first return of every heavy subset: `log R(y,δ)≥y^c` for fixed `δ` | sub | PTT, TAPO, BAG |
| B98 | Positive-generator integer-norm systems: which count distance forbids a finite top layer | method | RAC, SPAL, APD |
| B100 | A saving for `t log n` on moving families of blocks past Vinogradov's degree | sub | PTT, TAPO |
| B106 | A natural relative pair with Euler characteristic `M(N)`, or a natural self-map or group action whose signed fixed-point indices localize to `O(N^{½+ε})` | RH (≥qRH at exponent `θ<1`) | MC, HF, ESG, HHAC |

### Γ — selection and reflection
| # | Problem | Strength | Routes |
|---|---|---|---|
| B68 | Independent `D_s≥0`, nonnegative Krein flux, integer-probe sign or all-zero dispersion bound | RH | PM |
| B69 | Positive physical or graph carrier | producer | PM, W1C, PTR |
| B70 | Lower bound for `V_p` from the carrier | sub | PM |
| B71 | Universal decay `e^{−t/4}` of every resonant mode; equivalently horocycle, Farey or Narain rate `y^{¾−ε}` | RH | PM, BHR, CTH |
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
| B83 | AAL: eventual abscissa bounds are global | sub | BAG, JAS, SC, whole programme |
| B84 | Smallest FE defect carrying a one-off | method | BAG, ACS, APD |
| B85 | Arithmetic global trace on a family containing ζ | RH | ACS |
| B86 | Mixed Young projections at unbounded rank; positive arithmetic representation | RH | ACS |
| B87 | A nonnegative count on integer probes, defined without `Q`, with quadratic Tate limit `Q` | RH | ACS, HF, PM, RW, AE, CTH |
| B88 | Sign of the renormalized torsion form, and its comparison with the Gamma/pole reserve at the critical weight `δ=0` | RH | AE, HHAC, HF |
| B89 | A bounded aligned return at each right zero on a right disc: a tail event cancelling the head at every cut | sub | BAG, ZCG |
| B92 | Arithmetic source of a rotated relation with coefficients of the size of `Q` | RH | ZCG, RAC |
| B93 | A contradiction using growth, log-concavity or arithmetic of `Q` beyond the extremal law | RH | ZCG, RAC |
| B95 | Abelian group with Hecke endomorphisms whose trace form is `Q` | producer | ACS, AE |
| B103 | Does a positive Euler product with linear counting that continues across `Re s=½` with a functional equation satisfy AAL | method / sub | BAG, APD, ZCG |
| B109 | Rankin–Selberg noncancellation: some cusp form `g` with `Λ_g(ρ/2)≠0` at every off-line zero `ρ` | indep. (completes a receiver) | PM, BHR |

## 2.3 Frankenstein routes

**No assembly closes RH.** Each assembly below has at least one open input; the assemblies whose output is RH (F1, F22, F15) need inputs of RH or AAL strength. The others collapse independent problems into one or fix what a missing input must contain.

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F1 | **Split skeleton.** Any AAL producer (not-attained top, bounded lag on a progression, Abel-density-zero lag excursions, subexponential polar ground energy, one prime-window grid, log-dense integer lag, twisted plateau, JAS dressed/typical/shell, bounded towers, one bounded cone, weak recurrence, slow aligned returns on right discs) with any ZAL receiver (inner-field decay, subtracted lag, heat coefficient `→0`, eventual Hadamard, uniform high-collision counts) | RH [L] | one AAL input (B83), which must use the critical line (F21), and one ZAL input (≥qRH) | the only two-input assembly whose output is RH |
| F2 | **Critical curve = window.** Threshold chain with `R_polar` [L], conductor resolution at a fixed ratio [L/S], low packet at every ratio [L], collar Gårding, Γ-liminf, strong limits [L], VHR window rung [L] | the complete matrix at ratio `R` is decided by one channel, the pole; at every ratio it is RH | none for the collapse; B104 architectural | HF, SRT, AIP critical branches are the window problem of RW |
| F3 | CSTW traces and flow, AIF restoring bound | RH ⇔ `Ψ` locally bounded [L] | B2 | the tower is one local boundedness statement |
| F4 | ACS typical sign with Gaussian tails, AIF onset field, frequency packets, WVL visibility, ZCG sharp location, PTT isolated-zero entry | negativity at aperture `K log log T` lives on heights of measure `≤T^{1−1/(64K)}` [L] | B28, B46 | first sign past bounded aperture on typical heights |
| F5 | Eight-way log-mean equivalence, Selberg `O(T)` depth and bounded inner field, Carleson measure, bulk log-mean, necessary length | typical-height layer = depth density `o(T)`; any mollifier reaching it has Euler length of the primes `≤c log²T` [L/D] | B57 | one target for RW, ZCG, WD, CTF, PM |
| F6 | `N(ρ)=exp(−ΣG)`, hyperbolic count, box budgets, long-mollifier residues | deep zeros obey rate 2 or carry a large Green potential [L] | B60 | Density Hypothesis exponent near `½` |
| F7 | **One edge.** Pronic domination, flux, FFP drift, Euler coordinates, PM scattering, PTR at `h=½`, Hecke-algebra Poisson measure, positive Hecke annihilators, primon thermal means | one theorem `Re s≥1` with many proofs [L/D] | B68, B70 | marks what positivity reaches |
| F8 | **Theta wall.** TH column calculus, ZCG carrier horizon, FFP drift, PTT Ξ-current lift, CAF adaptive head and Gamma reserve, fixed-head asymptotic | all ranks reduce to the adaptive head, whose leading term is a critical partial-sum square of ζ [L/C/D] | B19, B20, B102, A42 | merges TH's wall with the size of ζ on the line |
| F9 | AAD rate law, Möbius and compensated producers, quarter rate, twin quarter floor, RAC kernel and parity identity, Frobenius as factorial stencil | stencils, parity, twin pairs and zero-free regions are one axis; the missing Frobenius is the missing rate [L] | B15 | closes production and parity as independent routes |
| F10 | One verified height, all rungs, cone PNT on the window's range | all finite rungs [L] | nothing finite | decides no all-rank statement |
| F11 | VK savings of all routes, including the Narain remainder | one width axis [L/S] | B15 | they share one input |
| F12 | ¬AAL consequences: finite oscillation, dilation annihilation, jets with long-shift `m²`, unbounded returns at the top zero, returns tail-bad at every cut, zero-free strip, qRH, the FE pairing top and bottom layers, Turán lower bounds for power sums of the finite head on every window of exponents | a contradiction search on one rigid world [L/D] | any contradiction, necessarily using the FE (F21) | decides B83 if it succeeds |
| F13 | **Isolation.** APD defect `1/6400` and quantitative defect bounds, SPAL count distance, RAC parity identity and exchange law, SEL degree one, relocation first-gap obstruction | ζ is a singleton in three metrics and cannot be reached by rational surgery with positive coefficients [L/S] | B84, B98 | every stable argument in these metrics is about ζ alone |
| F14 | Curve chain, Abel mollifier, near-extremal rigidity, Carleson measure, Szegő-ratio dilation | over a curve: Castelnuovo ⇔ dilation bound ⇔ budgets reach 1; over ℤ: every piece except the bound [L] | B66 | states what a Castelnuovo over ℤ must assert |
| F15 | **Count skeleton.** Hecke isometry of `Q` (quadratic half), Tate principle (a count needs no law), Λ as torsion intersection and renormalized torsion forms on `ℓ²(n^δ)`, theta `h⁰`, Manin and Stepanov counts on curves, Born rules, boundary algebra | every ingredient of the curve count proof except a count over ℤ [L] | B87, B88 | states the missing object; output RH |
| F16 | **Horizon.** AdS₄ quotient, fakes, Hecke rigidity, Hecke Poisson, Krein law, KMS, throat, trivial-zero law, genus-two graph, Born rules, boundary algebra, linear counts, second place, Farey reading, horocycle / Farey / Lax–Phillips / Narain / cusp-energy receivers | physics reduced to one law, a positive count of full rank; waves, Hecke, KMS, `C*` and the FE do not supply it; every observable is on the width axis [L/S] | B68, B71, B87 | closes wave dynamics, Hecke, KMS, reflection and linear counts as sources of the sign |
| F17 | **Dark range.** PTT savings, TAPO precision law and `3/2` bracket, heavy-return dictionary, RAC almost-every-height cancellation | the short-sum barrier is one first-return statement; the RH bracket is proved at polynomial precision [L] | B97 | the gap is precision `y^{−9/2}` against constant precision |
| F18 | **AAL tail form.** Transport on right discs, tail of a return, recurrence dichotomy, head resolution, conditional tail moments, arithmetic mean values | AAL ⇐ at each right zero an arithmetic tail event cancelling the head at every cut, at the Kronecker scale; the proved mean values bound such events from above only [L/D] | B89, B96 (lower bounds) | one tail statement |
| F19 | **Certificate skeleton.** Agler wall, Euler coordinates, head–tail certificate, Ξ-current lift, Euler tail law | arithmetic certificates exist exactly at tail-good heights [L/D] | B96 at all heights | one tail law for TH certificates, PTT and BAG |
| F20 | **Mertens in five geometries.** Franel–Landau, square-root Farey law, nerve, core Euler characteristic, persistence barcode, Zagier horocycle law | one exponent read by stencils, Farey fractions, simplices, persistence and horocycles [L] | B14, B15, B50, B106 | lets topological and dynamical tools act on the Mertens level; each lands on Π |
| F21 | **Critical-line firewall.** Continuous, discrete, integer-norm and rational-prime one-offs; positive two-prime and Hecke annihilators; FE-defect rigidity; relocation first-gap obstruction; rigid ¬AAL world; shift invariance of AAL | every input to AAL that uses only positivity, Euler products over rational primes, integer norms, linear counting or rational surgery is refuted; the input must use the FE and cannot use the position of the line [L/S/D] | a mechanism by which the FE excludes a finite top layer (B83, B103) | removes most of the AAL search space and names the one ingredient left |
| F22 | **Curve-proof template over ℤ.** Crude half: a ZAL producer (inner-field decay, `Λ_Xlog X→0`, bounded heat count, the Gaussian ceiling at each rational height). Self-improvement: AAL through Turán's second main theorem on the finite head (JAS shell criterion) with the FE-reflected bottom layer and the finite-oscillation rigidity. FE: ξ. Count: Tate limit | RH, with each step matched to its curve counterpart (Stepanov ↔ ZAL, power sums ↔ AAL, FE ↔ FE, count ↔ Tate limit) [L/D] | a crude producer over ℤ (no Frobenius; ≥qRH) and B83 | shows that over ℤ the crude step is the hard one and the self-improvement is the sub-qRH one; aims the work at AAL |
| F23 | **Theta at the zeros.** CAF adaptive head and fixed-head asymptotic, the critical partial sum `≈ζ(½+ib)` [C], ZCG FE-pair flatness (`\|ζ(½+iγ)\|≪\|γ\|^{33/200+ε}δ²` for a pair of depth `δ`), MZF negative moments `N(ρ)` | the theta sign is decided where `\|ζ(½+ib)\|` is small; there its size is set by `ζ′` at the critical zeros and by FE-pair flatness at off-line pairs [L/D] | A42; B102; lower bounds for `\|ζ′(½+iγ)\|` relative to the head remainder (negative moments, Π54) | joins TH (Σ) to the negative-moment wall (Π) at one place |
| F24 | **Topology meets the horizon.** Core Euler characteristic `M(N)+#primes(N/2,N]`, square-root Farey law ⇔ RH, `SL₂(ℤ)` acting on Farey fractions on closed horocycles | the only arithmetic group action in the corpus that carries `M(N)` as a deviation acts on the Farey model [L/D] | B106: a cell model of the core on which `SL₂(ℤ)` acts with fixed points of bounded index | turns B106 into one concrete construction |
| F25 | **Count through torsion.** Renormalized torsion operators on `ℓ²(n^δ)` (raw forms positive, counterterm `log(2ε)⟨x,y⟩`, operator-norm limit), Tate principle, Hecke isometry | a positive torsion count exists at every `δ>0`; the critical form lives at `δ=0`, where the mixed row is unbounded [L] | B88: survival of positivity as `δ→0` after renormalization | locates the count wall at the critical weight |

**Closest to the open core: F22, F21, F18 and F15.** F22 says which step of the curve proof each open problem is. F21 says what the AAL step must contain. F18 says where the tail form of that step lives. F15 says what one object would close the sign side.

### The hard half: what a contradiction search on ¬AAL may assume (F12)

| In the world ¬AAL | Evidence |
|---|---|
| Zero-free strip `(β₁,Θ)` at all heights; `Θ<1`; finite top layer; attained top excess | [L] |
| `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})`, `T` unique, coefficients `−ord/(Θ+iμ)`, `η≤Θ−Θ₂` | [L] |
| Sign changes of `ψ(e^u)−e^u` at bounded log gap, amplitude `≥δe^{Θu}` | [L] |
| Two-prime dilation annihilation of `ψ` | [L] |
| `Φ(mℓ)` unbounded on every progression; lag excursions of positive lower Abel density; polar ground energy `≤−c′e^{2(Θ−½)B}/B³` | [L] |
| Turán: on every window of `\|G\|` consecutive exponents, the power sum over the top layer is `≥c·Z^ν` with an explicit `c` | [L] |
| `Λ`-moments at `ρ+1→−m`; diagonal `→0`; short shifts `→0`; long-shift correlation `→m²` | [L] |
| Every phase return unbounded on every domain joining a top zero to `Re s>1`; every return at a top zero tail-bad at every cut | [L] |
| Head returns of length `N` satisfy `N<1024(log τ)⁴(log log τ)²` | [L] |
| The FE maps the top layer `Θ+iγ_j` to a bottom layer `1−Θ+iγ_j`; symmetric shifts move both layers by `±a` and keep the world ¬AAL | [L/D] |
| The top layer is not a rational relocation of critical zeros of ζ with positive coefficients | [L/S] |

No contradiction comes from exact identities: every exact ledger is holomorphic off `s=1` [L]. Typical aligned shifts are tail-good in every world [L/D]. No contradiction comes from positivity, Euler products, counting or positive Hecke combinations alone: the countermodels and annihilators satisfy all of them [L].

Which inputs carry a one-off:

| Input class | Status | Evidence |
|---|---|---|
| Positive continuous prime measure, `N(x)−ρx−C→0` | one off-line pair | [L] |
| Discrete primes following a continuous measure, linear counting | one off-line pair on `Re s>½`; blow-up at `s=½` | [L] |
| Integer norms, nonnegative integer coefficients, linear counting | one off-line pair, holomorphic on `Re s>½` | [L] |
| Rational-prime labels (repeated), multiplicative natural coefficients, linear counting | one off-line pair, holomorphic on `Re s>17/30` | [L] |
| Integer norms, signed generators, bounded count error | new zeros on a vertical progression | [L] |
| Integer norms, positive generators, count error `O(log²x)` | exists, only ζ's zeros | [L] |
| Integer norms, positive generators, count error `o(log n)` | only the rational primes | [L] |
| Rational relocation of ζ's critical zeros, endpoint-normalized | signed density, negative at the first integer gap | [L/S] |
| Exact Euler product and exact FE; FE defect `≤1/6400` | only ζ | [L] |
| Euler product, linear counting and continuation across `Re s=½` without FE | open | B103 |
| Euler product and FE with larger defect | open | B84 |

## 2.4 Wildly different routes

**Verdict.** No route in the corpus or among the proposals avoids Σ payment, Π precision and Γ selection by a proved mechanism. Every RH-equivalent statement in the corpus transports by an exact identity to one of the three cores, so a wildly different route must produce a new invariant, not a new reading. Two proposed lines are walled: fixed-point localization of the Mertens Euler characteristic (W6) and the AdS₃ modular bootstrap (W11). Five lines have no wall identified in the corpus: W7, W9, W10, W14, W15. The strongest case for "possibly wildly different" is W14, then W7.

### Walled lines
| Line | Wall |
|---|---|
| W6 Fixed-point localization of `M(N)` | Maps homotopic to the identity have `≥N/(4log N)` fixed points (isolated upper primes); the connected core has Euler characteristic `M(N)+#primes(N/2,N]`, not of square-root size; persistence is classified and `s`-independent; matchings cannot go below Betti `≍N` [L/D]. Survivor: B106, a natural relative pair with `χ=M(N)` or a signed-index localization; F24 names its one concrete candidate. |
| W11 AdS₃ modular bootstrap | The Narain double average carries exactly the VK saving at a universal exponent; `¾` ⇒ RH; every exponent `>¾` impossible; the source reads ξ only through `ξ(1+2u)` in a denominator [L/S]. It is the width axis. |
| W12 Horocycle renormalization | Horocycle mean = Farey count; its rate is the Mertens level [L]. |
| W13 Function-field limit | Centered curve Euler products with shrinking mesh lose their half-plane [L]. |
| W5 Extremal angle | The inequality alone has a polynomial model [L]; with arithmetic it is Σ [D]. |

### Lines with no identified wall

#### W14. An integer-valued Riemann–Roch on `Spec ℤ` as the count
- **Idea.** RH ⇔ `Q` on integer probes is the Tate limit of an `ℕ`-valued count [L]. Over a curve the count is `χ` of a divisor on `C×C` (quadratic by Riemann–Roch, nonnegative after Hodge index). Absolute algebra with coefficients in the sphere spectrum gives a Riemann–Roch formula for Arakelov divisors on `Spec ℤ̄` with integer-valued dimensions of `H⁰,H¹` [C; outside the corpus, details unverified here].
- **Target.** An integer-valued `χ` on Hecke correspondences of a surface surrogate for `Spec ℤ×Spec ℤ`, quadratic up to `O(m)` under scaling, whose quadratic part on integer probes is `Q`.
- **Why it might avoid the walls.** It produces a count by a dimension, not by a sign or a precision estimate; the Tate principle then gives the sign for free [L]. It is the one construction type that the count wall names and that has not been tried.
- **First test.** Reproduce the corpus theta `h⁰` with exact RR [L] as an integer-valued dimension; then test the Born-rule conditions of CTH on two-term probes `y−x·T_p`.
- **Risk.** The surface `Spec ℤ×_{𝔽₁}Spec ℤ` is not constructed; an integer-valued `h⁰` on `Spec ℤ̄` is linear in the divisor, and Γ128 forbids linear counts: the quadratic count must come from a product structure that does not exist yet.

#### W7. Interlacing families
- **Idea.** Expected characteristic polynomials of interlacing families of Hermitian matrices are real-rooted by real stability [C].
- **Target.** Realize the Jensen polynomials `R_d(Ξ)`, infinitely many `d`, as expected characteristic polynomials of interlacing families built from first atoms, PD at every rank [L].
- **Status.** The canonical finite-free split `J=Γ⊠Θ` fails factorwise (`Θ` never real-rooted) [L]: the decomposition must be non-canonical.
- **Risk.** A Hilbert–Pólya realization in finite-dimensional dress.

#### W9. Values of the form on integer probes
- **Idea.** `Q` on `ℤ^N` is a real quadratic form; under ¬RH it is indefinite for large `N`. Indefinite irrational forms in `≥3` variables take values dense near 0 with effective rates [C].
- **Target.** A lower bound `|Q(a)|≥‖a‖^{−κ′}` on primitive probes of one irrational restriction per `N`, `κ′` below the effective exponent. No sign is asked for.
- **Risk.** Generic forms have large Diophantine exponent; a lower bound must use arithmetic of the coefficients, whose only known source is positivity.

#### W10. Heights on actual arithmetic varieties
- **Idea.** Arithmetic Hodge index holds on arithmetic surfaces; Gross–Zagier heights of Hecke translates of Heegner points form a positive quadratic form with local terms `log p·(incidence)` and an archimedean Green term [C].
- **Target.** A limit of Arakelov forms on `X₀(N)` converging to `Q` on integer probes.
- **Risk.** The primitive part of `X₀(N)×X₀(N)` is cuspidal; resonances live on the Eisenstein sector, which couples only to the mirror-even half [L].

#### W15. An Iwasawa-theoretic realization
- **Idea.** Iwasawa main conjectures identify `p`-adic `L`-functions with characteristic ideals of class-group modules — sign-free, algebraic counts [C].
- **Target.** An inverse system of class groups or Selmer modules whose characteristic power series has zeros in bijection with the complex zeros of ζ.
- **Risk.** `p`-adic `L`-functions interpolate special values, not complex zeros; no transfer between the two zero sets is known.

### Tested and rejected forms
| Form | Reason | Evidence |
|---|---|---|
| Horocycle renormalization as a sign | horosphere indicators solve the wave equation; the rate is the Mertens level | [L] |
| Lee–Yang lift on the prime torus | needs Gamma speed above total Euler speed | [D]/[L] |
| Stable Dirichlet polynomial with critical zeros | Herglotz carrier rigidity | [L] |
| Arithmetic capacity for the stencil rate | dual constraints are sawteeth | [L] |
| Agler decomposition in prime or Euler coordinates | Gamma coordinate dominates; Euler coordinates stop at `Re s=1` | [L] |
| Functional equation as damping law | genus-two graph has FE and a slow resonance | [L] |
| Linear counts from the horizon | degenerate | [L] |
| Discrete Morse matching of the prime complex | Betti number `≍N` | [D] |
| Fixed-point localization in literal cardinality | `≥N/(4log N)` fixed points | [L] |
| Persistence of the prime complex | `s`-independent | [L] |
| Newton polygon separation of zeros | Taylor ratios `→1` | [D] |
| Comb or crystalline rigidity of the zero divisor | needs zero-side positivity | [D] |
| AdS₃ bootstrap past VK | remainder is the VK saving; `>¾` impossible | [L] |

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

**Question.** Does `Σ_{T<γ≤2T,β>½}m_ρ(β−½)=o(T)`? Equivalently `T⁻¹∫_T^{2T}log|ζ(½+it)|dt→0`, `I(½+x+it)→0`, density-zero damping deficits on the horizon, and for each fixed `u>0` the proportion of zeros of depth `>u/log T` tends to zero [L].

- **Why it matters.** It is `100%` critical-scale clustering, the Euler-mollified log-mean, the dyadic depth, the Abel inner mass at infinity and the Bode integral of universal damping [L]. It closes the typical-height layer for RW, ZCG, WD, CTF and PM at once and gives local Weil positivity at fixed `λ` on density-one heights (B28) [D]. In the curve-proof template (F22) it is the density-one form of the crude step: ZAL asks for finitely many zeros beyond each depth, B57 for a vanishing proportion beyond each scaled depth.
- **Where it stands.** Selberg's mollifier: off-line first moment `≤(67/1000)V`, depth `O(T)` uniformly in windows, inner field bounded at infinity, Abel log-mean `≤11/2` [L]. Selberg's density theorem gives a proportion `≪e^{−cu}` beyond depth `u/log T` [C], decaying in `u` but not vanishing at fixed `u`. Critical-line proportion `→1` implies it [L].
- **The tool gap.** Mollifiers are outer: Euler prefixes change the outer term and leave the inner mass and the dilation surplus invariant [L]. A near-unit moment needs length `exp(c log²T)` [L], the Euler length of the primes up to `c log²T`, where prime phases first become absolutely non-aligned [L/D]. Vanishing needs a control of the zeros within `u/log T` of the line that is not a second moment: a variance bound `T⁻¹∫(log|ζM|−mean)²→0` for some non-Euler `M`, or a fixed-scale density estimate.
- **Tests.** T1–T4, T7 pass. T5: false on `ζ(s)(1−cp₀^{−s})`, `c>√p₀` [L]. T6: prime field, long-mollifier ceiling, tail moment, Carleson embedding, dilation identity.
- **Limit.** Sparse off-line zeros survive; rare heights untouched.

### Alternatives

| Question | Why it matters | Tests | Limit |
|---|---|---|---|
| AAL (B83) | decides RH together with ZAL; the self-improvement step of the curve proof | all pass | §3 |
| Finitely many off-line zeros? (B13) | every finite-support receiver becomes an RH receiver [L] | all pass; T5 one-offs | subsumed by AAL |
| Lower bounds for tail events at the Kronecker scale (B96) | the existence side of the dark range [L/D] | T1 fails in the letter (Hardy–Littlewood off-diagonal) [D] | as hard as pair correlation past `α=1` [C] |
| Constant-precision first return of heavy subsets (B97) | implies B46 and the all-height sign past size | T1: RH gives it [D]; qRH up to shielding | see 2.6 |
| Continuation across `Re s=½` as an AAL selector (B103) | tests whether critical regularity already excludes finite top layers | T1 vacuous for ζ; T5 one-offs | an answer about fakes |
| Multiplicity `o(log X)` by a non-size input (B47) | first all-height input not reducible to size | T1: RH gives `≪log X/log log X` [C] | bounds collisions only |
| Rankin–Selberg noncancellation (B109) | turns the cusp-energy rate into a full RH receiver | T1 vacuous under RH | adds a receiver, not a producer |

## 2.6 If positivity, Weil positivity and spectral methods are excluded

"Spectral" is read as spectral theory of operators in every form: eigenvalue problems, spectral decompositions, Hilbert–Pólya realizations, Kuznetsov and trace formulas, spectral gaps of flows, Lax–Phillips semigroups. Fourier analysis, mean-value theorems, exponential sums, power sums and reciprocity are kept.

**The exclusion is not fatal over function fields.** The corpus proof of RH for every hyperelliptic curve uses Stepanov's auxiliary polynomial, power-sum elimination and the functional equation — no positivity, no Weil positivity, no operator [L]. Its three steps have sign-free counterparts over ℤ: a crude producer, an infinite-rank self-improvement, and reciprocity as the functional equation.

**What survives** [L]:

| Class | Receivers | Sign-free input proved |
|---|---|---|
| Production | integrality halves, stencils, one-sided counts | exact integrality; Stepanov over ℤ to Chebyshev; VK-scale rate; compensated producers; Carlitz factorial stencil over `𝔽_q[T]` |
| Power sums | JAS shell criterion, ¬AAL world | Turán's second main theorem, separation-free, with a finite head over all ξ-zeros |
| Farey and topology | Franel–Landau, square-root Farey law, nerve and core Euler characteristics, barcode | `\|M(n)\|≤2π·`discrepancy; `χ̃=−M(N)`; sphere bouquet; persistence classification |
| Orbit | column bounds, isolated-zero entry, first return | absolute non-alignment `L⁻⁶`; boxes; `3/2` bracket; precision law; heavy-return dictionary; moving jet; comb |
| Collision arithmetic | smooth × prime mean values | gcd-class collision counts; rectangular costs; logarithmic half-turns |
| Transport | recurrence, target mass, AAL | transport on right discs; returns are prime returns; tail of a return |
| Cancellation | `M(x)`, long moments, Báez–Duarte, cut kernel | VK; length and last-scale laws; almost-every-height square-root cancellation |
| Rigidity | exact FE, exact count, count distance, parity identity, relocation | three isolation metrics; exchange law; first-gap relocation obstruction; Vasyunin reciprocity |
| Identification | cameras, sharp location | sign-free readout under isolation |

All of Σ falls, with PM's Krein, Lax–Phillips and cusp-energy branches, the horocycle rate as proved by Eisenstein series, TH certificates, the index routes and the count door through Hodge index.

**The question.** *Does every heavy subset of the primes up to `y` need a height `exp(y^c)` to return at fixed precision?* Precisely: is there `c>0` such that for every `δ∈(0,1)` and every small `κ>0`, for large `y` no set `H` of primes `≤y` missing at most a fraction `κ` of the weight `Σp^{−½}` satisfies `1−cos(t log p)≤δ` for all `p∈H` at a height `1≤t≤exp(y^c)`?

**Why it opens the path.**
- It is the sign-free crude step. By the heavy-return dictionary it is the proportional saving B46 at length `y=(log t)^{1/c}` [L], hence the all-height sign past the size curve, the width axis up to crystal shielding and the exclusion of isolated zeros of depth `>c/2` through the column bound [L/D]: a ZAL-type statement with no sign in it.
- Its precision-weak form is a theorem: at precision `≍y^{−9/2}` the first return exceeds `exp(√(y/(48log y)))`, the RH bracket [L]; at bounded harmonic defect the lower bracket is `exp(c(log y)^{3/2}/log log y)`, the VK exponent [L]. The question is the passage from polynomial to constant precision.
- Its ceilings are known (words, binomial blocks, transfer at Kronecker) and its unused structure is identified: the moving jet, multiplicative approximate groups of returns, gcd classes of collisions, the quadratic defect of the archimedean place [L].
- It pairs with a sign-free self-improvement already in the corpus: Turán's theorem on the finite head of a top layer, the finite oscillation of `ψ`, and the FE as Poisson summation — the AAL step of §3 without any positivity.

**Tests.** T1: RH implies proportional saving for `K>1` [D]. T2–T4, T7 pass. T5: false on impure columns [L]. T6: precision law, comb, moving jet, collision classes. Strength: quasi-RH up to shielding [D].

**Limit.** It speaks about large heights; a one-off at a fixed height is invisible to it. Under the exclusion the AAL half needs the functional equation as a reciprocity law (Poisson, Farey, Dedekind and cotangent sums), and the crude step needs a Frobenius substitute (2.9).

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved.** The modular black hole is the quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)`; pulses are regular across the horizon; general `L²` data have a covariant metric and one ringdown mode per zero [L]. In time, every compact pulse rings down at the rate `δ` exactly when the zero-free strip has width `2δ`, and the Lax–Phillips semigroup has the resonant states as eigenvectors with RH ⇔ universal decay `e^{−t/4}` [L]. In space, long closed horocycles count Farey points; they thermalize at `y^{½}` unconditionally and at `y^{¾}` iff RH, and any gain past `½` is a strip [L]. The cusp channel is the full Maass theory; its energy thermalizes at `y^{½}`, at `y^{¾}` under RH, and its rate reads `Λ_g(ρ/2)` [L]. The Narain AdS₃ partition carries the VK saving and no more [L/S]. On graphs a count law is a Born rule: its quadratic half is the functional equation, its count half is universal damping; the boundary algebra with the partner involution has a positive state exactly under damping, while with the Hilbert involution it is `C*` on every black hole [L]. Linear counts are degenerate; Hecke supplies conservation only; non-arithmetic Hecke triangle groups fail the count at a second place [L]. Over ℤ the Weil form on integer sources is exactly Hecke-isometric, and RH ⇔ it is the Tate limit of a count [L].

**The law, read physically [D].** Two involutions act on a horizon. The Hilbert involution (adjoint) gives `C*`, KMS and reflection positivity, which every black hole has and which therefore select nothing. The partner involution `α↦q/α` (the functional equation) gives the Krein square as the GNS form of every state; a positive state for it exists exactly when every mode is damped. Universal damping is the statement that the two involutions agree on the modes. On a Jacobian the agreement is forced by a polarization: the Rosati involution is positive, and the Rosati trace is the equal-weight Born rule [L].

**The question.** *Is the functional equation of ξ the modular conjugation of the arithmetic horizon?* Precisely: is there a von Neumann algebra of `SL₂(ℤ)`-invariant observables of the AdS₄ wedge, in standard form with a cyclic separating vector, whose Tomita–Takesaki conjugation `J` acts on integer sources as the partner involution of the Eisenstein channel, so that the natural positive cone gives a positive Born rule with quadratic growth `Q`?

**Why it opens the path.**
- A positive Born rule over ℤ is RH by the Tate principle [L]; Tomita positivity is the one physical positivity that is tied to a specific involution.
- It explains every blindness in the corpus: KMS, `C*` and reflection positivity are positivity for the Hilbert involution, which every fake also has [L]; the question asks for positivity of the other involution.
- It has a theorem-level rung on graphs: a positive state for the partner involution exists iff the black hole is damped [L]; the genus-two graph has positive Born rules exactly for `q≤3` [L].
- It explains why arithmeticity matters: for non-arithmetic Hecke groups the count fails at a second place [L], so the modular conjugation of a non-arithmetic quotient cannot be the partner involution at every place.
- A negative answer in the natural algebras (the Bisognano–Wichmann wedge algebra restricted to invariant observables) ends the physical reading of the sign, leaving the horizon as a language.

**Tests.** RH-strength in full. T2 on finite windows where positivity is known [L]. T5: graph fakes have the partner involution and no positive state [L]. T6: Born rule, boundary algebra, Tate limit, second-place law.

**Second physical question.** *Does a long closed horocycle thermalize faster than `y^{½}` by any power?* A rate `y^{½+δ}` for every smooth profile is exactly a zero-free strip of width `2δ` [L]; for sharp shells the RH rate needs Möbius × circle-problem cancellation beyond RH [L], so the physical observable must be smooth.

**Limit.** The geometry is locally pure AdS, so gravity imposes nothing; every physical statement proved is a restatement, an edge theorem, a width-axis receiver or the absence of a law [L]. The primon gas (a modular billiard at a cosmological singularity) gives the same arithmetic only as Euler factors at real temperatures right of 1 [L].

## 2.8a If RH is a problem of topology or geometry: question

**What is proved.** RR at every aperture on the source cone; Bézout ⇔ RH; primitive `h¹` coercive for `a≤181/500`; bidegree counts see no primitive class [L]. Tate law and five currencies [L]. Count laws on every hyperelliptic curve; Rosati height = Born rule [L]. Λ is an intersection number of torsion orbits; renormalized torsion forms converge on `ℓ²(n^δ)`, `δ>0`, and fail on `ℓ²` [L]. `M(N)` is minus the reduced Euler characteristic of the prime-star nerve, the signed count of the persistence barcode, and the core Euler characteristic minus `#primes(N/2,N]`; persistence is `s`-independent; maps homotopic to the identity have `≥N/(4log N)` fixed points [L]. The same number is the Farey discrepancy and the horocycle deviation [L].

**Geometric question.** *Is there a Riemann–Roch count on correspondences of `Spec ℤ`: an integer-valued `χ` on Hecke correspondences of a surface surrogate for `Spec ℤ×Spec ℤ`, with `χ(mD)=m²(D·D)/2+O(m)`, whose intersection form on integer probes is `Q`?*
- By the Tate principle it gives RH with no further input [L]; nonnegativity of `Q` would be the Hodge index of the surrogate, read through a count.
- It is the precise form of the missing object (B87, B95) in the language of surfaces: on curves `C×C` supplies exactly this count [C], and the corpus proves the count law it implies for every hyperelliptic curve [L].
- The corpus constrains it: a linear count (an `h⁰` on `Spec ℤ̄` alone) is degenerate [L]; the count must be quadratic of full rank, so a product structure is required.
- Rungs: one window of length `≤3/5`, where a naive height is known to exist [L]; the torsion forms at `δ>0`, where a positive count exists, and the passage `δ→0` (B88).

**Topological question.** *Is there a natural relative pair or group action on a model of the prime core whose signed fixed-point indices localize `M(N)` to `O(N^{½+ε})`?*
- Literal fixed-point localization is refuted (`≥N/(4log N)` isolated upper primes), the core's own Euler characteristic is `M(N)+#primes(N/2,N]`, matchings stop at Betti `≍N`, and persistence is `s`-blind [L/D]. What survives is signed cancellation among fixed points of both signs, or a relative pair `(X,A)` with `A` absorbing the upper primes.
- `|χ̃|≥c√N` infinitely often [L], so the localized set has exactly square-root size and must see the boundary of `[1,N]` under dilation.
- The one arithmetic action in the corpus that carries `M(N)` as a deviation is `SL₂(ℤ)` on Farey fractions along closed horocycles [L] (F24): a cell model of the core on which this action has bounded-index fixed points would answer the question.
- First rung: the prime complex of `𝔽_q[T]`, where the Möbius sums vanish past degree one.

**Limit.** Natural Frobenius candidates are refuted in their classes [L]. Heights over number fields give central-value signs, not off-line zeros [D]. Dilations are not actions on `[1,N]`. A homotopy model with any required action exists abstractly; only a natural one carries content.

## 2.8b Does closing RH need a new field?

No theorem says so. The evidence is structural: every available tool stops for a proved reason, and the curve proof decomposes into three steps of which ℤ lacks two.

| Tool | Why it stops |
|---|---|
| Size estimates | before half-width `21/40`; all heights only to `a≈log log X` |
| Markov, Perron | frustration past `log ρ` |
| Type I/II sieve data | parity-blind |
| Linear floor identities, polynomial ledgers | blind to every zero; exact ledgers holomorphic off `s=1` |
| Barriers, short detectors | blind to purity; last-scale floor |
| Mollifiers | outer; near-unit moments need length `exp(c log²T)` |
| Words and polynomial phases | one block only |
| Conditional laws, arithmetic mean values | stop at the Kronecker scale; upper bounds only past it |
| Certificates in prime or Euler coordinates | Gamma dominates; Euler coordinates stop at `Re s=1` |
| Concentration-compactness at the critical curve | assembles at every ratio; returns the window threshold; leaves the pole channel |
| Finite computation | finite rungs decide nothing |
| Tensor amplification, integrality | carry RH unchanged; no crude regime over ℤ |
| Parabolic monotonicity | blind to `t=0` |
| Positivity, Euler products, integer norms, linear counting, positive Hecke combinations | carry or annihilate finite top layers |
| Discrete Morse theory, homotopy type, persistence of the prime complex | Betti `≍N`; fixed points `≥N/(4log N)`; `s`-independent |
| Unitarity, Schur, `C*`, KMS, flux, Hecke, FE on graphs | wrong involution; hold on fakes |
| Horizon observables | width axis; VK saving; `¾` is RH |
| Thermal averaging | Euler factors at real points `>1` |

**What is built, and where it stops.**

| Field | Object | Stops at |
|---|---|---|
| Arithmetic inner functions | half-plane, causal order, inner mass | size, not vanishing |
| Prime torus theory, tail arithmetic of the prime orbit | `(t,ω_t)` at finite time; first return; Euler tail | the Kronecker scale; upper bounds past it |
| Sum-product arithmetic of the logarithm | collision classes, count distance | no lower bound for a tail event |
| Rigid arithmetic of cuts | cut system, ledgers, kernel | parity is the strip |
| Arithmetic scattering holography, black-hole ringdown, counting holography | waves on quotients, Lax–Phillips, horocycles, Born rules, count laws | the count over ℤ |
| Effective geometry (AE, ACS, LST), height homotopy, effective scaling geometry | polar surfaces, naive heights, torsion forms, persistence | producer of a count; sign at `δ=0`; `s`-blind topology |
| Arithmetic positive duality | Beurling systems, FE-defect rigidity, one-offs, relocation | the critical line |

**The proposal: infinite-rank Weil theory over `Spec ℤ`.** On curves the proof has three steps: a crude count at every level, cheap because the Frobenius makes high-order vanishing cheap; a self-improvement, which is algebra because the rank is finite; and the functional equation. Over ℤ the crude step is ZAL (≥qRH), the self-improvement is AAL (sub), the functional equation is that of ξ, and the count half is the Tate limit. A field that proves RH has to build the infinite-rank analogue of each step, and the corpus fixes where each must act: the crude step at the dark range (every sub-RH precision question sits between `log T` and `exp((log T)^{2/3})`), the self-improvement at the critical line (every one-off fails there), the count at the critical weight `δ=0` (torsion forms converge only for `δ>0`).

| Aspect | Content |
|---|---|
| Objects | zeta-like objects with infinitely many modes and a functional equation; finite top layers and their reflected bottom layers; power sums of zeros on windows of exponents; scales `x=e^n` as levels; Euler heads and tails; heavy subsets of prime phases; Hecke correspondences on integer probes; renormalized torsion forms on `ℓ²(n^δ)`; positive Euler products with a finite top layer as calibration |
| Language | level, crude bound, self-improvement, rank barrier, top layer, eventual-to-global law, partner involution, Born rule, Tate limit, Kronecker scale, tail-good height, heavy return, critical weight |
| Mechanisms | Turán power sums with tail control in place of finite power-sum elimination; the FE as the step that converts an exceptional-set bound into a global bound; integrality and carries in place of the Frobenius; collision counting past the Kronecker scale; renormalization at `δ→0` |
| Tools to build | an infinite-rank Turán theorem whose tail is controlled by the FE-reflected bottom layer; a Frobenius substitute for auxiliary functions at the archimedean place; mean-value theorems for Dirichlet polynomials longer than the height with main terms; a count on correspondences at the critical weight |
| Calibration | curves of every genus (finite rank, complete proof [L]); graph black holes (FE without damping [L]); Beurling one-offs (no FE [L]); shifted products `ξ(s+a)ξ(s−a)` (FE, AAL ⇔ AAL(ξ) [L]); function fields, where the head is periodic |

**Criteria it must meet.** Reduce to the Lean curve proof at finite rank. Fail on every one-off through the functional equation and on rational relocation through positivity. Be invariant under symmetric shifts. Respect the rank barrier: no constant-factor crude regime. Treat ζ and its Liouville twin alike where the primes are the same. Read parity through binary main terms, since Type I/II data are blind.

**Questions it must answer.** What replaces "finitely many power sums" when the modes are infinite and grow like `T log T`? Which exceptional-set bound (finitely many zeros beyond each depth, a density-zero set, a heavy-return bound) self-improves under the FE? What is the infinite-rank analogue of `|α|≤√q` from `Σαⁿ=O(q^{n/2})`, given that `|ψ(x)−x|≤C√x` is false? Is a finite top layer compatible with the FE once the bottom layer is reflected into the power sums? Which auxiliary function has forced vanishing at the returns of the prime orbit with controlled size? What survives of a positive count at `δ>0` as `δ→0`?

**Limits.** Binary problems at the Kronecker scale are parity problems: a theorem there is at least as hard as pair correlation past `α=1` [C]. Excluding a finite top layer is an exceptional-zero problem of Landau–Siegel type inside the strip [D]. The crude step over ℤ is already quasi-RH.

## 2.9 If positivity, Weil positivity and spectral methods are excluded: which field?

Inner-function theory, holography's flux and Lax–Phillips, the horocycle and cusp-energy receivers, Hodge index and the count door through polarization lose their core. What remains is exactly the toolkit of the curve proof in the corpus: an auxiliary-function count, power sums and the functional equation as an identity [L]. The field that survives is **sign-free Weil theory over ℤ**: Stepanov's method at the archimedean place, infinite-rank power sums, and reciprocity.

**What it would be about.** A Frobenius substitute: over `𝔽_q` the map `x↦x^q` fixes the points and lets an auxiliary polynomial vanish to high order at all of them at low degree; over ℤ the "points" at height `t` are the phases `t log p`, and the substitute must make an auxiliary Dirichlet polynomial vanish to high order at the returns of the prime orbit with controlled length. The corpus marks what does not work: completely multiplicative maps with bounded additive defect are trivial [L]; a constant-carry Frobenius for integer floors does not exist [L]; the integer Frobenius stencil has rate the Mertens level [L]; Stepanov over ℤ by integrality stops at Chebyshev [L]. What it would add: the arithmetic of near-collisions `|log(mn)−log(m′n′)|<1/T` for smooth `m` and prime `n` at the Kronecker scale, power sums of the zeros on windows of exponents (Turán), and reciprocity laws — Poisson summation for theta, Farey symmetry, Dedekind and cotangent reciprocity — as the functional equation.

| Aspect | Content |
|---|---|
| Objects | auxiliary Dirichlet polynomials at one height; level sets `L(t,δ)` of `t log n` as multiplicative approximate groups; returns of heavy prime subsets; product sets of smooth and prime integers and their gcd classes; lcm and factorial ratios with their carries; power sums of zeros of a finite head; Farey fractions and the Stern–Brocot tree; cotangent and Vasyunin sums |
| Language | Frobenius substitute, forced vanishing, return, heavy subset, near-collision, collision class, comb, moving jet, carry, reciprocity, power-sum window, top layer |
| Mechanisms | Stepanov's degree-versus-vanishing count; Turán's separation-free lower bound for power sums; integrality `\|n\|≥1`; sum-product growth and incidence bounds for hyperbolas `xy=c`; carries as averages of translations; reciprocity along the Euclidean algorithm |
| Tools to build | an auxiliary-function method bounding the number of heavy returns at fixed precision (B97); an infinite-rank Turán theorem whose tail is paid by the reciprocity-reflected bottom layer; incidence bounds with a prime-density saving for smooth × prime near-collisions; exact reciprocity for the Nyman–Beurling Gram along Farey paths; a contradiction engine for the finite oscillation of `ψ=log lcm` at dilated points |
| Test cases | every hyperelliptic curve through Stepanov [L]; the depth aspect, where `q`-differencing is exact [L]; continuous, discrete and rational-prime one-offs, which have no reciprocity at the critical line [L]; the odd-primes-plus-`{3,4}` system at count distance `log²` [L]; rational relocations, which fail at the first integer gap [L/S] |

**Criteria it must meet.** No quadratic form with a sign, no operator spectrum. Proves Hasse–Weil over `𝔽_q` in the same language, as the corpus does for hyperelliptic curves [L]. Separates rational primes from every Beurling one-off through count distance or reciprocity [L]. Any parity output at power saving is a zero-free strip [L]. Not blind to zero modes: avoids functionals linear in `ψ` read through floors [L]. Respects the rank barrier.

**Questions it must answer.** What replaces the Frobenius, given that over ℤ a dilation of the count is an average of translations [L]? Is the fine multiplicative energy of smooth × prime products at scale `1/T` at its random value? Do moving block families of `t log n` save past Vinogradov's degree? Does Turán's lower bound on the top layer, combined with reciprocity, contradict the finite oscillation of `ψ`? Does reciprocity, iterated along the Euclidean algorithm, evaluate the Nyman–Beurling distance?

**Limits.** Nothing in the corpus shows the exclusion is forced. No source produces parity at power saving other than a strip [L]. No named mechanism above VK.

## 2.10 If RH is a physical phenomenon in AdS with a modular horizon: which field?

Arithmetic scattering holography, black-hole ringdown and counting holography exist and are formalized. Their positive results: the horizon as an AdS₄ quotient; regularity across the horizon; the graph black hole; the Krein law; the one clock; Lax–Phillips on graphs and on the modular surface; the width-axis dictionary in time and space; the Farey reading of the horocycle; the full Maass theory of the cusp channel; the Narain AdS₃ partition with its exact main terms; Born rules; the boundary algebra; the count law on every hyperelliptic curve; the Tate limit over ℤ. Their negative results: wave dynamics, unitarity, Hecke, KMS, `C*`, the functional equation, integrality, linear counts and Hecke at a second place do not carry universal damping. What they leave is one positivity, for one involution.

**What it would be about.** *Arithmetic polarization of horizons:* the positivity of the partner involution. On a Jacobian the Rosati involution is positive and the Rosati trace is a count; on a graph black hole the partner involution has a positive state exactly when the hole is damped; over ℤ the Weil form on integer sources is Hecke-isometric and is a count exactly under RH [L]. The field asks which physical structure makes the partner involution positive: a polarization of the horizon, a Tomita–Takesaki structure in which the functional equation is the modular conjugation, or a global group law (a "Jacobian of the horizon") whose counts are Born rules.

| Aspect | Content |
|---|---|
| Objects | `SL₂(ℤ)\`(Rindler wedge of AdS₄); graph black holes `(q,t)` and oscillator banks; integer sources and probes; boundary algebras `R[π]/(π²−tπ+q)` and the Hecke algebra on integer sources; partner and Hilbert involutions; Born rules; the Eisenstein channel and its resonant states; the cusp channel and Rankin–Selberg functions; Farey points on closed horocycles; the Narain partition; Jacobians and Rosati forms as calibration |
| Language | probe, source, channel, Born rule, partner involution, positive state, modular conjugation, polarization, damping, width, thermalization, ringdown, place, second place |
| Mechanisms | Born covariance `MᵀSM=qS`; GNS construction; Tomita–Takesaki and Bisognano–Wichmann; Rosati positivity; Tate limits of counts; Hecke as time shift; horocycle = Farey count; Mellin contour shifts on the width axis |
| Tools to build | a standard-form von Neumann algebra of invariant wedge observables on which the functional equation acts; a Hecke-covariant count of full rank on integer sources; a dictionary between Jacobians of curves and polarized horizons; a second-place test for arithmetic quotients over ℤ; a physical noncancellation principle for `Λ_g(ρ/2)` |
| Calibration | true curves (Rosati, Manin, Stepanov) [L]; graph fakes (partner involution, no positive state) [L]; the genus-two graph (positive Born rules iff `q≤3`) [L]; non-arithmetic Hecke triangle groups (negative counts at a second place) [L]; the Narain source (VK and no more) [L/S]; sharp shells (beyond RH) [L] |

**Criteria it must meet.** Recover Hasse–Weil from Born rules at every genus [L]. Fail on fakes through positivity of the partner involution, not through dynamics [L]. Supply the partner law globally, since local wave systems do not know it [L]. Fail for non-arithmetic groups at a second place [L]. Explain the blindness of KMS, Schur, `C*` and Hecke-algebra positivity as positivity of the wrong involution [L]. Explain the two RH rates `e^{−t/4}` and `y^{¾}` as one exponent [L]. Use only smooth sources, since sharp ones need more than RH [L].

**Questions it must answer.** Is the functional equation the modular conjugation of an arithmetic algebra of the horizon? What is the "Jacobian of the horizon" whose Rosati involution is the partner involution? Why does arithmeticity (no second place) make the partner involution positive? What is the full-rank count on integer sources, given that every linear count is degenerate? Is `Λ_g(ρ/2)≠0` for some cusp mode at every zero, as a physical coupling statement? Does the Narain bootstrap, completed with its cusp channel, carry anything past VK?

**Limits.** Every proved physical statement is a restatement, an edge theorem, a width-axis receiver or the absence of a law. The geometry is locally pure AdS. The programme has produced no estimate outside the Eisenstein calculus.

## 2.11 If RH is a problem of topology or geometry: which field?

**What it would be about.** *Renormalized intersection theory of arithmetic counts.* Counts are Euler characteristics and Riemann–Roch numbers; signs are signatures (Hodge index on a surface); nonnegativity comes from heights with a product formula or from Tate limits of counts; the zeros enter through an `s`-dependent completion. The corpus has computed the homotopy type, the homology and the persistence of the prime complex completely, and they do not see `s` [L]; it has built the torsion intersection form and renormalized it on `ℓ²(n^δ)`, `δ>0` [L]. The field must therefore work with completed, weighted or equivariant invariants that change with `s`, and must reach the critical weight `δ=0`.

| Aspect | Content |
|---|---|
| Objects | integer probes and Hecke correspondences; a surface surrogate for `Spec ℤ×Spec ℤ` (polar and scaling surfaces); local heights `λ_v` with `deg p=log p`; torsion cycles, resultants and renormalized torsion forms; theta `h⁰`; the prime-product complex, its nerve, its connected core and its persistence module; Farey fractions on closed horocycles; relative pairs and group actions on models of the core |
| Language | height, local height, naive height, Tate limit, product formula, Riemann–Roch count, self-energy, renormalization, critical weight, Euler characteristic, barcode, Lefschetz localization, fixed-point index, relative pair, signature, primitive class |
| Mechanisms | product formula as nonnegativity; Tate limit from a quadratic count; Riemann–Roch on surfaces; Hodge index; Lefschetz fixed-point formulas with signed indices; equivariant localization; renormalization of torsion self-energy as `δ→0`; Hecke equivariance |
| Tools to build | an integer-valued Riemann–Roch count on correspondences, quadratic under scaling; a renormalized torsion form at `δ=0` with its sign; an `s`-dependent completion of the prime chain complex whose homology sees the zeros; a natural relative pair `(core, A)` with `χ=M(N)`; a cell model of the core with an `SL₂(ℤ)`-action through Farey fractions |
| Test cases | elliptic and hyperelliptic curves (Manin, Stepanov, Rosati) [L]; Golden (no height) [L]; the complex fake [L]; the genus-two graph [L]; the prime complex of `𝔽_q[T]`; Farey and horocycle laws [L]; the persistence classification and fixed-point obstruction [L] |

**Criteria it must meet.** Recover Hasse–Weil for curves from heights or counts with no form as input. Be false on Golden and on shifted data with nonnegative Tate coefficients [L]. Read the test beyond its two degrees [L]. Be infinite-rank, with no finite-dimensional realization on a window [L]. Not define its height or count through `Q`. Depend on `s`, unlike homotopy and persistence [L]. Reproduce Betti `≍N`, fixed points `≥N/(4log N)` and `|χ̃|≥c√N` infinitely often [L]. Reach the critical weight `δ=0`, where the mixed torsion row is unbounded [L].

**Questions it must answer.** What is the surface surrogate on which Hecke correspondences have a quadratic Riemann–Roch count? Where does the torsion self-energy go as `δ→0`, and does positivity survive the renormalization? Which completion of the prime complex makes its homology depend on `s`? Which relative pair or action localizes `M(N)` with signed indices? Is the nerve realized inside the cusp geometry of the modular surface, with `SL₂(ℤ)` acting on its cells as on Farey fractions?

**Limits.** Finite-rank carriers, separable assemblies, connected links, natural Frobenius candidates, literal fixed-point localization and persistence are refuted in their classes [L]. Actual modular surfaces see only the cuspidal part [D]. Over `𝔽_q` these structures come from having a variety; over ℤ none of them is known to exist.

## 3. The one big question

**Is the asymptotic abscissa law true — does the functional equation turn eventual abscissa bounds into global ones, so that ζ has no finite top layer?** Equivalently [L]: for every `σ`, if all zeros above some height satisfy `Re ρ≤σ`, then all zeros do. Equivalently [L]: finitely many zeros right of `½+h` forces none. Equivalently [L]: `ψ(x)−x` is never one finite oscillation `x^ΘT(log x)+O(x^{Θ−η})` with `Θ>½`. Equivalently [L/D]: **the self-improvement step of the curve proof holds for ζ at infinite rank.**

The expected answer is that AAL holds. Then RH ⇔ ZAL, and every receiver that delivers finite off-line support delivers RH.

### Why this one

The corpus shows that every open RH-strength wall is one of the three cores, and that the curve proof — the only complete proof of an RH in the corpus — consists of a crude count, a self-improvement and the functional equation [L]. Over ℤ the crude count is ZAL, which is already quasi-RH; the count half is RH-strength; the critical curve and the horizon reduce to the window and the width axis. The self-improvement is the one step that is strictly below quasi-RH, decides RH together with the crude step, has a rigid negative world, has its forced ingredient identified, and has had every non-FE mechanism removed.

| Kind | Best form | Why it ranks lower | Evidence |
|---|---|---|---|
| Critical ratio | pole channel at every ratio (B101) | RH-strength; at one ratio a window rung | [L] |
| 100% near the line | depth density `o(T)` (B57) | Selberg gives size `O(T)`; vanishing needs a non-outer input | [L]; [D] |
| Rate near `½` | cluster wall (B59) | Ingham's slope | [D]; [C] |
| All-height sign | constant-precision first return (B97), proportional saving (B46) | quasi-RH up to shielding | [L]; [D] |
| Kronecker-scale law | lower bounds for tail events (B96) | binary prime problems; not implied by RH | [D]; [C] |
| Production, parity, Farey, nerve, core, barcode | stencil rate (B55), parity (B67), relative localization (B106) | rate is the Mertens level; parity at power saving is a strip; topology is `s`-blind | [L]; [D] |
| Horizon | any exponent past `½`, universal decay (B71) | interior exponent is a strip; `¾` is RH | [L] |
| Count | Tate limit of a count over ℤ (B87) | RH-strength; no crude regime over ℤ | [L] |
| Theta | adaptive head near critical zeros (B102) | RH-strength | [L/D] |
| **Self-improvement** | **AAL (B83)** | **sub-qRH; decisive with ZAL; false on fakes; rigid negative world; forced ingredient the FE; positivity, surgery and the location of the line excluded as inputs** | **[L/D]** |

### What an answer does

| Answer | Effect |
|---|---|
| **AAL proved** | RH ⇔ ZAL [L]. Finite off-line support, `κ(K_ζ)<∞`, bounded non-real heat count, finite critical source energy, eventual Hadamard positivity and the eventual central-gap budget each become RH [L]. |
| **AAL proved** | The obstacle "finite or shallow exceptions remain" loses its finite half in LA (`N_d` bounded ⇒ RH), HF, AKLT and CWS (finite index ⇒ RH), ZCG (bounded heat count ⇒ RH), FFP, WD and RW large-height receivers. |
| **AAL proved** | F1 and F22 become the architecture: one crude (ZAL) producer closes RH. The one-off countermodels stop being models of ζ, and the proof names the FE invariant that separates them. B13 is answered. |
| **AAL proved** | The infinite-rank self-improvement exists for ζ; the same argument, being shift-invariant, holds for `ξ(s+a)ξ(s−a)` and is a template for the Selberg class. |
| **AAL refuted** | RH is false, with a finite top layer, a zero-free strip and a rigid finite oscillation of `ψ(x)−x`; the layer is intrinsic, not a rational relocation [L/S]. |
| **A proof that bounded returns at right zeros never exist in any world** | BAG, AAD and TAPO stop being AAL producers; AAL moves to the FE, power-sum, lag or integer forms below. |

### What is proved around it

| Channel | Status | Module |
|---|---|---|
| Split and collapse | RH ⇔ ZAL ∧ AAL ⇔ ZAL ∧ weak recurrence ⇔ ZAL ∧ subexponential polar ground energy; eight statements coincide under AAL | `ZetaWeakRecurrenceLadderCollapse`, `PolarGroundEnergySubexponentialZerosApproachLine`, `AsymptoticAbscissaLawProducers` [L] |
| Form of the law | AAL ⇔ eventual-to-global abscissa bounds; preserved by symmetric shifts | `SymmetricShiftsPreserveTheAsymptoticAbscissaLaw` [L] |
| Rigid negative world | attained top, finite oscillation, unique `T`, quantized coefficients, sign changes, two-prime dilation annihilation, rightmost-zero jets | `TheOneOffsAreFiniteOscillationsOfThePrimeError`, `PrimeErrorFiniteOscillationRigidityAndSignChanges`, `MultiplicativeDilationAnnihilationOfPrimeError`, `FiniteExceptionalLayersForcePersistentLowJets` [L] |
| Power sums | Turán's second main theorem, separation-free; applied to all ξ-zeros with a finite head and tail bounds | `HTGeometry/PowerSumTuranLowerBound`, `JointAncestryShellPowerSumCriterion` [L] |
| Lag producers | `Φ(L)≤Me^{aL}` off a set of lower Abel density zero ⇒ AAL; one bounded progression ⇒ AAL | `WeilLagFunctionDensityZeroExcursion`, `WeilLagProgressionZerosApproachLine` [L] |
| Transport | bounded translates copy the zero; slow aligned returns on right discs ⇒ AAL; crossing discs force `\|ζ\|≥cτ^b` | `TheMissingInputOfTransport`, `TheSlowReturnBoundLivesRightOfTheLine` [L] |
| Tail | zeros of ζ = zeros of `ζM_y`; returns at right zeros tail-bad at every cut, density zero; recurrence dichotomy | `TheTailOfAReturnCarriesTheZero`, `TheRecurrenceDichotomyOfTheTail` [L] |
| Fakes | continuous, discrete, integer-norm and rational-prime one-offs; bounded count with a new zero; positive two-prime and Hecke annihilators | `BeurlingOverRegularIntegersOffLineZeros`, `ADiscreteBeurlingOneOff`, `TheIntegerNormOneOffHasLinearCounting`, `TheRationalPrimeOneOffHasMultiplicativeCounting`, `ABoundedCountWithANewZero`, `PositiveTwoPrimeAnnihilators`, `PositiveHeckeAnnihilatorsOfFiniteResonances` [L] |
| Isolation and surgery | FE defect, count distance, exact parity identity; relocation signed density, zero mass, first-gap negativity | `SmallIntegrableDefectsForceTheRationalPrimes`, `CountDistanceRigidity`, `TheExactIdentityDeterminesTheParity`, `TheNormalizedRelocationDensityHasZeroMass` [L]; `TheFirstIntegerGapDetectsRelocation` [S] |
| Curve template | tower count law ⇔ crude bound at every level; FE pins the modes; every hyperelliptic curve | `TheCountLawOfATrueCurveAtEveryGenus`, `TheCountLawOfEveryHyperellipticCurve` [L] |

### The five forms of the missing input

1. **Critical-line form (B83, B103, B84).** A statement in which the functional equation of ζ acts on a finite top layer and its mirror bottom layer and meets a constraint that a finite oscillation cannot satisfy. Every countermodel lacks the FE, positivity annihilates finite layers, and the law is shift-invariant; so the constraint must come from the FE as an involution, not from positivity or the position of the line [L/D]. Candidate quantities: theta-type transforms whose two asymptotic ends are exchanged by the FE; a quantitative FE-defect bound turning a finite top layer into a positive defect; the reflected Nyman–Beurling Gram, whose cotangent sums obey reciprocity.
2. **Power-sum form (F12, F22).** Turán's theorem gives, on every window of `|G|` consecutive exponents, a power sum of the top layer of size `≥cZ^ν` [L]; the explicit formula turns it into a large value of `ψ(x^ν)−x^ν` on every geometric window. A contradiction needs an upper bound for `ψ` on a positive proportion of such windows — the lag producers on progressions are exactly such bounds [L] — and the FE must supply it by reflecting the bottom layer into the same power sums.
3. **Tail form (B89, B96).** At each right zero, aligned heights at which the Euler tail cancels the head on a disc about the zero, at every cut. Such heights are tail-bad and of density zero [L]; arithmetic mean values bound such events from above [L]; the input is a lower bound for an arithmetic tail event at the Kronecker scale [D].
4. **Lag form (Γ69).** For every `a>0`, `Φ(L)≤M_ae^{aL}` outside a set of lower Abel density zero; in prime terms `ψ(x)−x≥−M_ax^{½+a}` off a sparse set [L/D]. Under ¬AAL the polynomial `T` is negative on a set of positive density, so the bound fails on a set of positive lower Abel density [D].
5. **Integer form (Γ81).** Under ¬AAL a two-prime dilation polynomial annihilates `ψ=log lcm(1,…,⌊x⌋)` to `κx+O(x^{Θ−η})`. A contradiction must come from integrality and carries of `lcm` at the dilated points; exact ledgers are blind [L], so only inexact integer information can serve.

### First steps

1. Write the FE-reflected power sums of the rigid ¬AAL world: the Turán windows of the top layer together with the bottom layer `1−Θ+iγ_j` in one theta-type transform; determine whether the reflected terms can be made to dominate on a positive proportion of geometric windows.
2. Decide B103 on the countermodel side: continue a discrete or rational-prime one-off across `Re s=½` (adjusting the prime-square sum that forces the blow-up at `s=½`), or prove that critical continuation with linear counting forbids a finite top layer.
3. Decide whether the lag form is weaker than a zero-free strip: does a zero at `β` force `Φ(L)>e^{(β−½−ε)L}` on a set of positive lower Abel density only for attained tops, or for every `β`?
4. Extend the relocation obstruction from rational multipliers to entire multipliers of finite order normalized at `0` and `1`: does every finite surgery on ζ's zeros fail positivity at the first integer gap?
5. Test the integer form on the rigid object: compute the dilation-annihilated `ψ` for an explicit top layer and compare with the carries of `lcm(1,…,⌊x/p^aq^b⌋)`.

### Validation

| Test | Verdict |
|---|---|
| T1 | Pass. RH implies AAL; AAL implies no zero-free region [D]. |
| T2 | Pass. A stated implication or inequality in each form. |
| T3 | Pass. The effects table. |
| T4 | Pass. Not decided by any finite rung: it concerns all heights. |
| T5 | Pass. False on continuous, discrete, integer-norm and rational-prime one-offs [L]. |
| T6 | Pass. Each form names an unrefuted input: an FE constraint on a top layer, an FE-reflected power-sum bound, a lower bound for a tail event, a one-sided lag bound off a sparse set, an integer contradiction. |
| T7 | Pass. Moves Γ68, Γ69, Γ106, Γ115, Γ124, Γ136, B13. |

### Limits

- AAL leaves ZAL, which is at least quasi-RH; the closing argument still needs it, and over ℤ the crude step is the harder one.
- Excluding a finite top layer is an exceptional-zero problem of Landau–Siegel type inside the strip; classical exceptional-zero repulsion is consistent with ¬AAL worlds and gives no contradiction [D].
- The tail form sits at the Kronecker scale, the same dark range as B46 and B57; its existence side is a parity problem.
- The lag form may be as hard as a strip; that is step 3.
- Exact identities cannot help [L]; positivity, Euler products, integer norms, counting, positive Hecke combinations and rational surgery cannot help [L/S]; the location of the line cannot help (shift invariance) [L]. The integer form must use inexact information and the critical-line form must use the FE as an involution.
