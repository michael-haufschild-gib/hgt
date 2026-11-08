# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `906b3c709c` plus the working tree of 2026-11-08. Working log: `logs/review-0811-status-research.md`.

Evidence: `[L]` Lean source; `[S]` Lean source unfinished, unintegrated or uncommitted; `[K]` Lean with transitive axiom audit; `[D]` deduction, not a Lean theorem; `[N]` numerical, uncertified; `[C]` classical, not formalized. Sections 2.3–2.13 and 3 are interpretation and ideation; every statement there that is not tagged is a proposal, not a result.

**38 live formulations; 9 candidates.** HJ→PA; BSH→CDC; FEL's BSY criterion→CTF. Candidates: APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF.

## 1. Big picture

### 1.1 RH is ZAL plus AAL, and AAL is transport
For every zero configuration (reflection-symmetric, locally finite in height), purity ⇔ ZAL ∧ AAL [L]. ZAL — finitely many zeros beyond each positive depth — implies quasi-RH. AAL — finitely many zeros right of `½+h` means none — is equivalent to **zero transport**: every right zero has zeros of real part `>Re ρ−ε` at arbitrarily large height [L]. For ζ it is equivalent to **tail transport**: every right zero transports to arbitrarily high points at which every Euler tail `ζM_y` vanishes and cancels the head with full amplitude `|E_y|≥Π_{p≤y}(1+p^{−σ})^{−1}`; such heights are tail-bad at every cut, and the events produced by returns have density zero [L]. AAL is the existence of rare events; every density statement bounds them from above. The failure of AAL is one rigid object: an **isolated top**, a finite nonempty layer on `Re=Θ>½` over an infinite remainder left of some `Θ₂<Θ`, reflected by the FE to a bottom layer at the same heights, with every higher zero inside `|Re z−½|≤Θ−½` [L]. In primes it is a finite oscillation `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})`; in towers it forces syndetic lag excursions `|Φ(νℓ)|>Ce^{aνℓ}` at every base, with exceptional rank 1 at the resonant base `π/γ` of a single top pair [L].

### 1.2 What decides AAL, and what cannot
Three proved boundaries fix the shape of any AAL input.
- **Two scales.** A property depending only on zeros above some height (densities, pair statistics, gaps, growth of counts), or only on zeros below a fixed height (finite verification), that holds on a pure configuration holds on a configuration with ZAL and a finite off-line layer [L]. An input for the finite stratum or for AAL must couple low and high zeros.
- **Analytic shape.** The FE, order one and reality admit every finite top layer: `cosh(s−½)·Π_{q∈Q}(s−q)(s−q̄)(s−1+q)(s−1+q̄)` [L]. On tower level sums the FE acts only as `S(−ν)=conj S(ν)` [L]. An argument excluding a finite layer must use the Dirichlet series.
- **Firewall.** Continuous Beurling systems (whose zeta is rational and continues across `Re s=½`), integer-norm and rational-prime Euler products with linear counting, and one reflection pair each carry a finite top layer; positive two-prime and Hecke polynomials annihilate every finite zero set at every multiplicity; AAL is invariant under `ξ(s+a)ξ(s−a)` [L]. The reflection `ρ↦1−ρ̄` keeps heights while AAL is vertical transport: an FE-based input must turn the FE into transport in height.

What gives AAL for free [L]: vertical recurrence; zero sets of exponential polynomials, including finite Dirichlet polynomials; curves; vertically periodic configurations; strip almost periodic functions (Bohr: zeros recur with bounded gaps); Dirichlet series uniformly approximated by their partial sums on closed strips. Almost periodicity at large height alone is not enough: the rational one-off tends to 1 vertically and violates AAL.

### 1.3 The curve proof, read in the coordinate of ζ
For every curve datum in the strip, AAL holds because the zeros are periodic in height, and a crude count `|N_n−qⁿ−1|≤Cq^{n/2}` at every level, ZAL, purity and unitarity are equivalent [L]. Both steps of the curve proof — Stepanov's crude count and the power-sum self-improvement — sit inside ZAL; AAL is the periodicity of the Frobenius. In the tower coordinate the picture is the mirror image: finite rank makes the outer part well-founded (ZAL is automatic) and elimination algebraic. ζ has neither freebie [L/D].

Elimination exists at infinite rank [L]. The exceptional rank — the number of distinct visible top points — decides Turán windows: above an isolated top of modulus `R`, every window of `k` consecutive levels has `|S(ν)|≥εRᵛ−(Σ|b|)rᵛ`; no **thick** set of levels (arbitrarily long runs arbitrarily far out; every density-one set is thick) carries a bound below `R`; hiding a top costs trace norm `≥εR^{M+1}`. The rank barrier is sharp: roots-of-unity towers vanish off `kℤ`, so sets of density `1−1/k` do not self-improve. With a well-founded outer part, a crude bound on a thick set leaves only the critical layer visible (the infinite-rank Hasse–Weil principle); Wolff configurations show well-foundedness is needed. For ζ: a prime deviation `O(X^{½+a})` along a thick set of geometric scales of one base, for every `a>0`, gives AAL; **RH ⇔ ZAL ∧ thick `O(X^{½})`** [L].

### 1.4 The finite stratum
Finite negative index of `K_ζ` ⇔ finite index on one two-prime lattice ⇔ finitely many off-line zeros ⇔ bounded heat count ⇔ RH above some height ⇔ eventual slice positivity; in the stratum Lindelöf holds and one non-blind prime tower decides RH [L/K]. The finite stratum is AAL at `h=0` (B13). No asymptotic property and no finite verification decides it [L].

### 1.5 The window sign is one scalar flow
The tower is a canonical system to contact with `H₁H₂=1`; `L′=q−sinh 2L`; `|L(x)|≤artanh e^{−2(x−c)}+2osc_{[c,x]}Ψ` [L]. **RH ⇔ `Ψ=½log H₁` is locally bounded**; off RH `L` is unbounded above every base [L]. RH ⇔ Hasse–Weil along the cubic-spline orbit; the orbit correlation grows at the zero width [L].

### 1.6 The critical curve is the window plus one channel
At critical overlap `R=c⁸/log N`: `0<R_c≤R_c^{PSD}`, `R_c≤R_pole≤R_high=W=⨅_A windowThreshold(A)≥c₀e^{6a*(ζ)}`, every threshold `=⊤` ⇔ RH [L]; `R_pole=W` [S]. Positivity on `ℝ^N` splits into the primitive hyperplane plus the pole channel; below `W` the complete matrix is PD iff its pole channel is, and `R_c=W` iff the pole channel pays at every ratio below `W` [L]. Charged profiles have strong limits, the polar row has its explicit profile, and polar payment at a larger ratio excludes charged limit profiles [S]. Conductor-adapted splitting absorbs every low-packet cross term except the literal polar collar pairing [S]. The critical-curve programme carries no sub-RH content.

### 1.7 Below the onset the form exchanges aperture for ratio
Window positivity at `a` excludes zeros of depth `≥¼` up to height `e^{a/K}`, gives the Mertens lag `O(x^{−1/4})`, a sharp pole self-energy, and `R_polar≥c₁e^{c₂a}` [L]. Every exchange is single-exponential; none raises `a*(ζ)`.

### 1.8 The theta wall is ζ on the critical line
All ranks reduce to the adaptive head `M(b)=⌈|b|/2+B⌉`, whose omitted pair sum costs at most half the first-atom floor [L]. Below the grid the critical partial sum is `ζ(½+ib)` up to `9M^{−½}+M^{½}/|b|`; at `M=M(b)` the error is `O(|b|^{−½})`, and the head's leading term is `|ζ(½+ib)|²+O(|ζ(½+ib)||b|^{−½}+|b|^{−1})` [L]. The sign is automatic where `|ζ(½+ib)|` is large and is decided by second-order terms near the critical zeros.

### 1.9 The near-line wall is the dark range
Near-unit mollified moments need `log N≥log²T/(6K₀)`; an Euler mollifier reaching them uses every prime up to `min(1/24,1/(14K₀))log²T/log 4` [L]; prime phases become absolutely non-aligned at length `≈L²`; conditional tail laws stop at the Kronecker scale `y≈log T` [L]. Past the height a long mean value of a Dirichlet polynomial has no diagonal main term: the Fejér mean is a collision form of exact order `N²`, and for prime polynomials a count of prime pairs in short multiplicative ranges [L]. The log-mean, the cluster wall, the short-sum barrier and the AAL tail input sit on one range of primes, from `log T` to `exp((log T)^{2/3})` [D].

### 1.10 The archimedean Frobenius exists only approximately
At a `δ`-return of a set `P` of primes, every `P`-smooth `n` has `|n^{−it}−1|≤Ω(n)δ`; Dirichlet polynomials on `P`-smooth integers freeze, and `J` moment conditions force approximate vanishing to order `J` at every return [L]. Two distinct primes have no common exact return: the prime orbit has one fixed point [L]. The Stepanov analogue over ℤ has its auxiliary polynomials; it lacks exact vanishing.

### 1.11 Production, Farey, the nerve, the core and the prime vertices are the Mertens level
Producer rates equal the Mertens level; Farey discrepancy ⇔ RH; `M(N)=−χ̃` of the prime-star nerve; the connected core has Euler characteristic `M(N)+#primes(N/2,N]`; the barcode is `[m,2m)` over odd squarefree `m`, independent of `s` [L]. A face-preserving, cutoff-natural self-map homotopic to the identity has exactly the prime vertices as fixed points; their relative singular indices are `1−#{q>p: pq≤N}` below the cubic cutoff, unbounded below [L]. Localized at the primes, `χ` becomes a sum of Möbius sums over integers of fixed least prime factor; square-root cancellation must happen across primes [D].

### 1.12 The count: quadratic half, count half, and where the count is missing
A count law has a quadratic half (a nondegenerate Born rule, i.e. the FE) and a count half (positivity, i.e. damping) [L]. Tate principle both ways: a degree-two homogeneous function is the Tate limit of an `ℕ`-count iff it is `≥0` [L]. On a true hyperelliptic curve the Castelnuovo–Severi defect of every integral class is itself a natural number, an integer polynomial in `q` and the point counts: the count exists before any sign is known [L]. Over ℤ the quadratic half holds (Hecke at `p` is an exact isometry of `Q`), and RH ⇔ `Q` is the Tate limit of an `ℕ`-count [L]; nothing plays the role of the point counts.

### 1.13 The surface of Spec ℤ: the off-diagonal is assembled, the diagonal is the sign
On the 𝔽₁-zonotope surface, power-map graphs meet in `m+n` points and the defect is `2Σ_k(Σ_{n>k}a_n)²` — Hodge index by counting — realizing the pole plane and the first archimedean channel [L]. Weil's off-diagonal between atoms at `log m`, `log n` is one 𝔽₁-cusp with its tower of even jets (the trivial zeros) plus the gcd-twisted torsion intersection on `ℙ¹_ℤ` (the primes), with every local index `≥0` [L]. Atomic Frobenius graphs have infinite genus (`Λ(n)+1+1/(n²−1)` points where `ℙ¹` has `n+1`) [L]; smoothed by the cubic spline, Hasse–Weil for every pair of integer degrees ⇔ RH [S]. No metric on `ℙ¹_ℤ`, no toric Green function and no continuous Hecke kernel carries the archimedean place: the jets have rank `≥3` on coprime orders, toric pairings depend on `mn` while Weil's depend on `m/n`, and the primes are jump discontinuities at `log pᵏ` [L]. Off the diagonal, `W=C_∞+lim_{r→1}T̃_r` with `T̃_r` positive torsion energies and `C_∞` the archimedean compensation, which changes sign [L]. What no half-product supplies is the diagonal `Γ_n²`, which must be renormalized; and **renormalization carries no sign** — for every symmetric form `Q`, `Q+c(δ)I` is eventually PSD and renormalizes to `Q` — while **damping is lossless** [L]. A count at the critical weight has to be a damping of something positive.

### 1.14 Physics: every horizon observable is the width axis; internal modular conjugation collapses
The modular horizon is the quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)` [L]. For `0<δ≤¼`, a zero-free strip of width `2δ` ⇔ pulse ringdown at `e^{−(δ−ε)τ}` ⇔ horocycle and smoothed Farey rates `y^{½+δ−ε}`; RH ⇔ `y^{¾−ε}` ⇔ universal Lax–Phillips decay `e^{−t/4}` [L]. Smooth profiles thermalize unconditionally at `y^{½}exp(−√(−log y))`; sharp shells at a log-free `O(√y)`; one sharp shell at the RH rate ⇔ RH ∧ `Σ_{d≤X}μ(d)E(X/d)=O(X^{½+ε})` [L]. The Narain AdS₃ remainder carries exactly the VK saving; `¾` ⇒ RH; exponents `>¾` impossible [L]. The cusp channel is the full Maass theory with Rankin's bound and the Rankin–Selberg Euler product `ζ(s)L(Sym²g,s)/ζ(2s)` [L/S]. The right Rindler wedge is strictly spacelike from every `SL₂(ℤ)`-image of the left wedge; the unique boost-commuting wedge exchange fixes cusp height; the geometric KMS period is `2π`, the arithmetic strip period `1`; `GL₂(ℤ)` symmetries fix every pseudo-Eisenstein series; and in any standard form, an operator `Z` with `Z,JZJ∈M` is central with `JZJ=Z*` and natural-cone pairing `‖ZΩ‖²` [L]. Internal modular conjugation is Hilbert-adjoint positivity, which every fake has. **RH ⇔ there is a standard-form von Neumann algebra with rational dilations, `JU(r)J=U(r^{−1})`, whose natural-cone form on integer sources is `Q` (or has Tate limit `Q`)** [L].

### 1.15 Hull
Haar-a.e., fair-coin-a.e. and order-two fibres extend zero-free to `Re s>½` with natural boundary `½`; the Liouville point extends iff RH [L].

### 1.16 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| Markov, Perron, sign-gauge balance past `e^{−3/4}`, `log ρ` | refuted | [L] |
| Size-only payment of primes | ends before half-width `21/40` | [L] |
| Floor tower as aperture producer | stays below `0.3621` | [L] |
| Weighted Gårding on the whole horizon | false on deep atoms | [L] |
| Physical tearing at the collar boundary | Schur ratio `4/13` | [L] |
| The critical ratio as an independent sub-RH problem | window threshold plus the pole channel | [L/S] |
| Uniform logarithmic Gamma reserve in coefficient norm | resonant two-copy profiles | [L] |
| Fixed theta heads; summable absolute pair majorants; compact cores | no margin; harmonic diagonal; geometric growth | [L/S] |
| Positive Laplace representations of the theta amplitude or its reflected square | excluded | [L] |
| Fixed or limiting amplitude locking | adds nothing | [L] |
| Product certificates in Euler coordinates past `Re s=1` | cannot cross | [L] |
| Parabolic structure as selector of `t=0` | blind | [L] |
| Barriers, short detectors and weights | blind to purity | [L] |
| Moment data for the log-mean; outer mollifiers for the inner mass | blind | [L] |
| Asymptotic or local-below zero statistics as inputs to the finite stratum or AAL | cannot decide | [L] |
| FE, order one and reality as exclusion of a finite layer | `cosh` models | [L] |
| Positivity, Euler products, integer norms, linear counting, continuation across `Re s=½`, reflection symmetry, positive Hecke combinations as AAL | finite layers exist | [L] |
| Density statements on levels of a tower | rank barrier | [L] |
| Elimination without well-foundedness | Wolff configurations | [L] |
| Exact returns as a Frobenius | one fixed point | [L] |
| Diagonal moments, group closure, early orbit against a return | blind | [L] |
| Slow-return bounds on discs crossing `Re s=½` | the premise is RH | [L] |
| Schur, `C*`, KMS, reflection positivity, internal modular conjugation as zero locators | blind; central collapse | [L] |
| Positive Poisson measure of the Hecke algebra; positive Hecke polynomials | hold off the line; annihilate finite resonance sets | [L] |
| Wave dynamics, flux, unitarity, Hecke, FE at genus two, first-level counts, integrality as universal damping | fakes carry all | [L] |
| Linear counts as count laws; Hecke at a second place | degenerate; conservation only | [L] |
| Narain remainder past `¾`; sharp sources at the RH rate | impossible; need Möbius × circle cancellation | [L] |
| Integer stencils as a mechanism independent of Möbius | rate is the Mertens level | [L] |
| Polynomial ledgers as parity input at zeros | twin shares every leading pole | [L] |
| Bounded count error as a selector | new zero with signed generators | [L] |
| Mean spectra as detectors of zero relocation | relocation invisible | [L] |
| Discrete Morse matchings; fixed-point localization in cardinality; persistence of the prime complex | Betti `≍N`; prime vertices fixed; `s`-independent | [L/D] |
| Torsion forms on unweighted `ℓ²`; finite constraints or finite-rank repair of the renormalized torsion limit | mixed row unbounded; both signs survive | [L] |
| Renormalization as a source of sign | any form arises | [L] |
| Metrics on `ℙ¹_ℤ`, toric Green functions, continuous Hecke kernels as carriers of the archimedean place | excluded | [L] |
| Finite-genus atomic Frobenius graphs | fail Hasse–Weil | [L] |
| Thermal averaging (primon gas) as a strip input | Euler factors at real points `>1` | [L] |
| Extremal-angle position alone; rotated relations of small growth | polynomial model; trivial | [L] |

## 2.1 Tasks that are just work

Difficulty is established only where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### Finite verification
| # | Task | Routes | Basis |
|---|---|---|---|
| A1 | Lean-certified `RHVerifiedThrough T` past 67 with zero location (Turing count), first `T≈10²–10³` | all rungs | `hardySEM` sign chains; Fejér budget |
| A2 | Numeric values of `windowHeight`, `xiMassHeight`, `heatGridHeight`, theta `D` | window routes, TH, LA, HCF | explicit definitions |
| A3 | Two-weight membership past `a₀`: odd unit window, `log 2`, `½log 5` | RW, OWU, EWU, ACT, SWC, HF | A1–A2 or rigorous Galerkin |
| A4 | Theta rank 15 and beyond at every `0<a≤½`, one rank at a time (unverified past 14) | TH | radius-12 power core, height 67, coupled current tail |
| A5 | Lean certificate of the center-tail failure | TH | finite computation |
| A6 | Cone widths `𝒜(c)` past `c=0.66`; Lévy margins at `½log 3` | PBAP, ACS, RW, CHT | convex programs |
| A7 | Certificates on the nine anti-diagonals `{2,3,4,5,7,8,9,11,13}` (unverified; statement unsettled) | ACT | finite case analysis |
| A48 | Hasse–Weil test of smoothed Frobenius pairs at verified scales | SOSZ, HF, ACS | window rungs (A1) |

### Critical curve
| # | Task | Routes | Basis |
|---|---|---|---|
| A9 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | HF, SRT, AIP, ACS, SC | proved limits |
| A13 | Near-gcd charges and periods beyond `M₀(N)` (unverified) | AIP, HF | gcd-defect coercivity through `M₀(N)` |
| A44 | Charged Γ-liminf for actual nonpositive whole-space sequences: pass from fixed-fraction polar-row convergence to the full physical pairing; integrate the polar-row, charged-limit and adaptive-packet modules (unverified) | HF, SRT, AIP | strong charged limits, polar row profiles, interior margin, physical-coordinate payment [S]; high-conductor analogue [L] |

### Flow, near-line, continuation, orbit
| # | Task | Routes | Basis |
|---|---|---|---|
| A16 | Numerical `r,m,q` for `a≤1` [N] | RW | Galerkin |
| A18 | Twisted second moments past `21/50`: to `½`, Conrey `4/7` [C] | WD, census | raises rate `2θ` |
| A19 | Heat horizon toward its method floor | ZCG | profile margin |
| A20 | Jensen rung toward the saddle scale (unverified) | LA, FFP | saddle identity |
| A21 | Census items; logarithmic two-point Chowla [C]; runs past five | MC, ACS, census | classical |
| A24 | Certified scans of `S_S`; brackets for `S*(a,b)` | TH | column calculus |
| A37 | Resonator mean of `\|ζ\|²` with resonators growing below the Kronecker scale (unverified) | BAG, ZCG, PTT | fixed-resonator limit, arithmetic mean values |
| A47 | Explicit window constants of the tower theorems for one top quartet `Θ±iγ` at base `π/γ`: the size of `ε`, the onset level, dependence on `γ` and `Θ−½` (unverified) | ZCG, WL, IWT | `exists_syndetic_lag_excursions_of_not_asymptoticAbscissaLaw`, `eventually_lag_large_of_single_top_pair` [L] |

### Theta, horizon, counts, production, descent, topology
| # | Task | Routes | Basis |
|---|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | PM, BHR | order `N(Λ)≍Λ` proved |
| A28 | Reciprocal quadric traces = vanishing-cycle Frobenius traces (unverified) | ACS | exact projective quadric counts |
| A30 | Best stencil exponent under RH in `[¼,½]` (unverified) | WL, MC | quarter rate, half scale |
| A33 | Fourier coefficients of the cubic residue [C] | MC, MMD | nonzero residue, continued Fourier modes |
| A41 | Count law for every curve over `𝔽_q` (Bombieri–Stepanov), first case plane quartics [C] | ACS, PM, CTH | crude-bound self-improvement on thick sets [L] |
| A42 | Uniform Gamma-weighted transport of the fixed-head theta asymptotic to `M=M(b)≈\|b\|/2` with effective error (unverified) | TH | fixed-`M` asymptotic [L]; adaptive partial sum `=ζ(½+ib)+O(\|b\|^{−½})` [L] |
| A43 | Integrate the eigenform Rankin–Selberg series and transport `Λ_g=` completed `ζ(s)L(Sym²g,s)/ζ(2s)` from `Re s>2` to `ℂ` | PM, BHR | RS Euler product [L]; eigenform series [S]; continuation [L] |
| A46 | Local singular indices of prime vertices beyond the cubic cutoff `N>p³` (unverified) | MC, RIAC | discrete-exit computation [L]; finite face Euler characteristic [S] |

## 2.2 Open mathematical obstacles

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window | RH; fixed length sub | all sign routes |
| B2 | Bounded oscillation of `Ψ` on every bounded aperture interval | RH | RW, SZ, CHT |
| B3 | Variation of `r` free of `1/μ` | sub | RW |
| B4 | Two-sector certificates; outer predictor at every window; every echo in its Schur band | RH | sign routes |
| B5 | Kick admission at every stage | RH | RW, GWZ, WTZ, HF |
| B6 | Full-space sign eventually at every `K`; every critical threshold `=⊤` | RH | HF, SRT, AIP |
| B8 | Head thresholds for every `d` | RH | HF, AHD |
| B9 | No zero mode at any length | RH | HF, TG, SC, EHT |
| B10 | Top coprime stratum | RH | HF, ACS, ADT |
| B11 | Exact SOS on a two-prime lattice | RH | HF, SC, ACS |
| B12 | Index ceiling uniform in resolution | ≥qRH | CHMD, SRT, SC |
| B13 | Finitely many off-line zeros ⇒ none (the finite stratum; AAL at `h=0`) | sub | whole programme (§3) |
| B14 | Any interior width value: window negativity exponent `<½`, a horocycle, Farey, pulse, Narain or spline-orbit exponent past the trivial one | ≥qRH | width axis |
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
| B46 | Proportional saving at length `(log X)^{2K}`, all heights; no early heavy return | sub (up to shielding) | RW, all rungs, PTT |
| B47 | Multiplicity `o(log X)` by an input not reducible to size | sub | ZCG |
| B101 | Polar payment of the pole channel at every ratio on growing windows | RH | HF, AIP, SRT |
| B102 | Sign of the adaptive theta head at every degree; leading term `\|ζ(½+ib)\|²`, decided near the critical zeros | RH (all ranks) | TH |
| B104 | Pole-channel payment at every ratio below `W`, equivalently `R_c=W` | method | HF, SRT, AIP |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B48 | Deciding input at square-root precision; a crude zero-localized prime count at every level | RH | WL, MC, PBM, RB, JAS, CTF, HCF |
| B49 | Bounded endpoint energy; integer lag ceiling | RH | WL |
| B50 | Trivial-gauge half power; zero exclusion for `M_X` | RH | MC, WL |
| B51 | Moving power window control | RH | JAS |
| B52 | Vanishing rows, sparse defect, BSY sign, positive proportion | RH | CTF |
| B53 | Regularized partial-sum bound | RH | PBM |
| B54 | Eventual extremal inequality | RH | RB |
| B55 | Any polynomial stencil rate (qRH); rates `a↑½` (RH) | ≥qRH to RH | WL, MC |
| B56 | `Θ<1⇒Θ=½` | sub | whole programme |
| B57 | Depth density `o(T)`, equivalently log-mean `→0` | sub | WD, census, MC, RW, ZCG, CTF, PM |
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
| B96 | Conditional law of the Euler tail at the Kronecker scale; lower bounds for tail events | sub | BAG, TH, WD, TAPO |
| B97 | Constant-precision first return of every heavy subset: `log R(y,δ)≥y^c` for fixed `δ` | sub | PTT, TAPO, BAG |
| B98 | Positive-generator integer-norm systems: which count distance forbids a finite top layer | method | RAC, SPAL, APD |
| B100 | A saving for `t log n` on moving families of blocks past Vinogradov's degree | sub | PTT, TAPO |
| B106 | A natural relative pair with `χ=M(N)`, or a natural self-map or action whose signed fixed-point indices localize `M(N)` to `O(N^{½+ε})` | RH (≥qRH at `θ<1`) | MC, HF, ESG, HHAC, RIAC |
| B110 | **Thick crude count**: `primeDeviation(X)=O_a(X^{½+a})` along a thick set of geometric scales `X=e^{νℓ}` of one base, for every `a>0` | AAL (with ZAL at `a=0`: RH) | WL, ZCG, ACS, IWT |
| B113 | Möbius × quarter-disc remainder `Σ_{d≤X}μ(d)E(X/d)=O(X^{½+ε})` | beyond RH | PM (sharp shells) |

### Γ — selection, reflection and transport
| # | Problem | Strength | Routes |
|---|---|---|---|
| B68 | Independent `D_s≥0`, nonnegative Krein flux, integer-probe sign or all-zero dispersion bound | RH | PM |
| B69 | Positive physical or graph carrier | producer | PM, W1C, PTR |
| B70 | Lower bound for `V_p` from the carrier | sub | PM |
| B71 | Universal decay `e^{−t/4}`; horocycle, Farey or Narain rate `y^{¾−ε}` | RH | PM, BHR, CTH |
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
| B83 | AAL | sub | BAG, JAS, SC, ZCG, WL, IWT |
| B84 | Smallest FE defect carrying a one-off | method | BAG, ACS, APD |
| B85 | Arithmetic global trace on a family containing ζ | RH | ACS |
| B86 | Mixed Young projections at unbounded rank | RH | ACS |
| B87 | A nonnegative count on integer probes, defined without `Q`, with Tate limit `Q` | RH | ACS, HF, PM, RW, AE, CTH |
| B88 | A counterterm-free damping presentation of Weil's form: natural positive kernels `K_r` whose limit is Weil's kernel on and off the diagonal (off the diagonal `C_∞+T̃_r` is known) | RH | AE, HHAC, SOSZ, RIAC, HF |
| B89 | A bounded aligned return at each right zero on a right disc | sub | BAG, ZCG |
| B92 | Arithmetic source of a rotated relation with coefficients of the size of `Q` | RH | ZCG, RAC |
| B93 | A contradiction using growth or arithmetic of `Q` beyond the extremal law | RH | ZCG, RAC |
| B95 | Abelian group with Hecke endomorphisms whose trace form is `Q` | producer | ACS, AE |
| B103 | Positive discrete Euler products with linear counting, continuation across `Re s=½` and an FE: AAL? (continuation alone fails for continuous systems) | method / sub | BAG, APD, ZCG |
| B109 | Rankin–Selberg noncancellation: some cusp form `g` with `Λ_g(ρ/2)≠0` at every off-line zero | indep. | PM, BHR |
| B111 | **Linear AAL**: `Θ−½≤C(Θ∞−½)` for one constant `C`, i.e. finitely many zeros right of `½+h` ⇒ none right of `½+Ch` | sub | BAG, ZCG, IWT |
| B112 | A mechanism converting the FE (a height reflection) into vertical transport of zeros, using the Dirichlet series and coupling both scales | sub | BAG, ZCG, APD |
| B114 | A positive-energy (half-sided) carrier of the partner involution | producer | PM, CTH |
| B115 | A carrier of the jets of the trivial zeros (rank `≥3` on coprime orders; not Arakelov on `ℙ¹_ℤ`, not toric) | producer | SOSZ, ACS, HF |
| — | ZAL | ≥qRH | whole programme |

## 2.3 Frankenstein routes

**No assembly closes RH.** Every assembly below has at least one open input. The assemblies whose output is RH (F1, F22, F15) need inputs of RH, AAL or ≥qRH strength. The others collapse independent problems into one or fix what a missing input must contain.

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F1 | **Split skeleton.** Any AAL producer (Γ69, incl. thick lag and thick prime deviation) with any ZAL receiver (inner-field decay, subtracted lag, `Λ_Xlog X→0`, eventual Hadamard, LH with every cosine-shift level eventually real, high-collision counts) | RH [L] | one AAL input (B83) and one ZAL input (≥qRH) | the only two-input assembly with output RH |
| F2 | **Critical curve = window + pole channel.** Threshold chain, `R_pole=W` [S], pole-channel decision [L], conductor resolution, charged profiles [S], low packet at every ratio [L] | the complete matrix is decided by the pole channel; at every ratio it is RH | none for the collapse; B104 architectural | HF, SRT, AIP critical branches are the window problem of RW |
| F3 | CSTW traces and flow, AIF restoring bound | RH ⇔ `Ψ` locally bounded [L] | B2 | the tower is one local boundedness statement |
| F4 | ACS typical sign, AIF onset field, frequency packets, WVL visibility, ZCG sharp location | negativity at aperture `K log log T` on heights of measure `≤T^{1−1/(64K)}` [L] | B28, B46 | first sign past bounded aperture on typical heights; asymptotic, cannot reach AAL |
| F5 | Log-mean equivalences, Selberg `O(T)` depth, Carleson measure, Euler mollifier length `log²T` | typical-height layer = depth density `o(T)`; any Euler mollifier reaching it uses the primes `≤c log²T` [L] | B57 | one target for RW, ZCG, WD, CTF, PM |
| F6 | `N(ρ)=exp(−ΣG)`, hyperbolic count, box budgets | deep zeros obey rate 2 or carry a large Green potential [L] | B60 | density exponent near `½` |
| F7 | **One edge.** Pronic domination, flux, FFP drift, Euler coordinates, Hecke Poisson measure, positive Hecke annihilators, primon means, Hecke state on `Aff(ℚ)` | positivity reaches `Re s=1`, and `Re s=½` only as a threshold [L/D] | B68, B70 | marks what positivity reaches |
| F8 | **Theta wall.** Column calculus, carrier horizon, Ξ-current lift, adaptive head, Gamma reserve, partial sum `=ζ(½+ib)` | all ranks reduce to `\|ζ(½+ib)\|²` plus second-order terms near the zeros [L] | A42, B102 | merges TH with the size of ζ on the line |
| F9 | Rate law, producers, quarter rate, twin floor, cut kernel, parity identity, Frobenius = factorial stencil | stencils, parity, twin pairs and strips are one axis [L] | B15 | closes production and parity as independent routes |
| F10 | One verified height, all rungs, cone PNT | all finite rungs [L] | nothing finite | decides no all-rank statement and no finite-stratum statement |
| F11 | VK savings of all routes incl. Narain and horocycle | one width axis [L] | B15 | they share one input |
| F12 | **Rigid ¬AAL world.** Finite oscillation, dilation annihilation, jets with long-shift `m²`, tower excursions at every base, single top pair seen at every level of its resonant tower, tail-bad returns, qRH, FE pairing top and bottom layers | a contradiction search on one rigid world [L] | any contradiction; it must use the Dirichlet series and couple scales | decides B83 if it succeeds |
| F13 | **Isolation.** FE-defect rigidity `1/6400`, count distance, parity identity, Selberg degree one, relocation first-gap obstruction | ζ is a singleton in three metrics; rational surgery with positive coefficients fails [L] | B84, B98 | every stable argument in these metrics is about ζ alone |
| F14 | Curve chain, Abel mollifier, near-extremal rigidity, Szegő-ratio dilation | over a curve: Castelnuovo ⇔ budgets reach 1; over ℤ every piece except the bound [L] | B66 | states what a Castelnuovo over ℤ must assert |
| F15 | **Count skeleton.** Hecke isometry of `Q`, Tate principle both ways, point-count defect on curves, half-products, positive torsion energy, `C_∞`, critical weight | every ingredient of the curve count proof except a count over ℤ; the off-diagonal assembled; the diagonal the missing positive damping [L] | B87, B88 | output RH; names the missing object exactly |
| F16 | **Horizon.** AdS₄ quotient, fakes, Hecke rigidity, Krein law, KMS, throats, genus-two graph, Born rules, boundary algebra, standard forms and Tomita collapse, all horizon receivers | physics reduced to one positivity for one involution; internal realizations excluded [L] | B68, B71, B87, B114 | closes waves, Hecke, KMS, reflection, internal modular conjugation and linear counts as sources |
| F17 | **Dark range.** Savings, precision law, heavy-return dictionary, almost-every-height cancellation, collision counts past the height | the short-sum barrier is one first-return statement [L] | B97 | gap: precision `y^{−9/2}` against constant precision |
| F18 | **AAL tail form.** Tail transport, partial returns, short-arc prime mass, recurrence dichotomy, conditional moments | AAL ⇔ rare tail events at every right zero; proved results bound them from above [L] | B89, B96 lower bounds | one tail statement |
| F19 | Agler wall, Euler coordinates, head–tail certificate, Ξ-current lift | certificates exist exactly at tail-good heights [L/D] | B96 | one tail law for TH, PTT and BAG |
| F20 | **Mertens in six geometries.** Franel–Landau, Farey law, nerve, core, barcode, prime-vertex indices, Zagier horocycle law | one exponent [L] | B14, B15, B50, B106 | topological and dynamical tools act on the Mertens level |
| F21 | **Critical-line firewall + two-scale law + `cosh` models** | every AAL input using only positivity, Euler products, linear counting, continuation, reflection symmetry, FE with analytic shape, or scale-separated zero statistics is refuted [L] | B112 | removes most of the AAL search space; names the ingredient left: a two-scale Dirichlet-series statement with the FE as transport |
| F22 | **Curve template over ℤ.** Elimination at infinite rank (window theorem, thick sets), towers of ζ, thick crude count ⇒ AAL, ZAL = well-foundedness, FE = Born rule, count = Tate limit | RH = ZAL + thick `√X` count; AAL = thick crude count at every `a>0` [L] | B110 and ZAL | the elimination step exists over ℤ; the two missing inputs are a thick crude count and well-foundedness |
| F23 | **Theta at the zeros.** Adaptive head `=\|ζ(½+ib)\|²`, FE-pair flatness, negative moments | the theta sign is decided where `\|ζ(½+ib)\|` is small; there its size is set by `ζ′` at the critical zeros [L/D] | A42, B102, Π54 | joins TH (Σ) to the negative-moment wall (Π) |
| F24 | **Topology meets the horizon.** Core Euler characteristic, prime-vertex indices, square-root Farey law, `SL₂(ℤ)` on Farey fractions | the only arithmetic action carrying `M(N)` as a deviation acts on the Farey model [L/D] | B106 | turns B106 into one construction |
| F25 | **Count through torsion and the archimedean place.** Positive torsion energies `T̃_r`, `C_∞`, half-products, critical weight, compensation exponent 2 | `W=C_∞+lim T̃_r` off the diagonal; the torsion part is a positive damping; the archimedean part changes sign; the diagonal is a renormalization [L] | B88; a jets carrier | the count must include the archimedean place as a positive damping |
| F26 | **Two-scale tower input.** Towers of ζ at every base, exceptional rank, thick sets, Fejér collision counts, Euler mollifier length, partial returns | a thick crude count is a statement about the prime deviation on long runs of geometric scales, i.e. about long mean values past the height, which are binary collision counts [L/D] | B110 | joins the IWT door to the dark range: B110 and B96/B97 sit on the same primes |
| F27 | **Standard-form physics.** Tomita collapse, graph standard forms iff damped, RH ⇔ standard form with partner conjugation, Lax–Phillips outgoing subspaces | a realization must keep the dilations outside `M ∩ JMJ`; the half-sided (outgoing) structure is the one known structure doing this [L/D] | B114 | turns the physical sign into a positive-energy question |

**Closest to the open core: F22, F21, F26, F15.** F22 names the two missing inputs of the curve template over ℤ. F21 fixes what the AAL input must contain. F26 locates the thick crude count on the dark range. F15 names the one object that closes the sign side.

### The rigid ¬AAL world: what a contradiction search may assume (F12)
| In the world ¬AAL | Evidence |
|---|---|
| Isolated top `Θ`, rest left of `Θ₂<Θ`, bottom layer reflected at the same heights, higher zeros in `\|Re z−½\|≤Θ−½` | [L] |
| `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})`, `T` unique, sign changes at bounded log gap | [L] |
| Two-prime dilation annihilation of `ψ` | [L] |
| At every base, syndetic lag excursions `\|Φ(νℓ)\|>Ce^{aνℓ}` with gap the exceptional rank; single top pair: every level at base `π/γ` | [L] |
| Polar ground energy `≤−c′e^{2(Θ−½)B}/B³`; lag excursions of positive lower Abel density | [L] |
| `Λ`-moments: diagonal `→0`, long-shift correlation `→m²` | [L] |
| Every return at a top zero tail-bad; transport events rare | [L] |
| Zero-free strip `(Θ₂,Θ)` above the layer's heights; qRH | [L] |
| The layer is not a rational relocation of critical zeros of ζ with positive coefficients | [L] |

No contradiction comes from exact identities, from positivity, Euler products, counting or positive Hecke combinations alone, from the FE with order one and reality, or from statistics at one scale [L].

## 2.4 Breakthrough question below RH and quasi-RH: the thick crude count

| Test | Requirement |
|---|---|
| T1 | Implied by RH and not implying quasi-RH |
| T2 | Answered by proving or refuting a stated inequality |
| T3 | A named consequence can be written down |
| T4 | Not decided by a finite rung |
| T5 | False on a corpus fake |
| T6 | Names an input not refuted in Lean |
| T7 | Not a shape already answered without moving a wall |

**Question.** *Is the prime deviation square-root small along arbitrarily long runs of geometric scales?* Precisely (B110): is there a base `ℓ>0` such that for every `a>0`

  `|(X−ψ(X))+X(Σ_{n≤X}Λ(n)/n−log X+γ)| ≤ C_a X^{½+a}`

for `X=e^{νℓ}` with `ν` in a thick set — a set of levels containing arbitrarily long runs arbitrarily far out, for example any set of density one?

**What it gives [L].** AAL outright (`asymptoticAbscissaLaw_of_thick_primeDeviation_bound`). With ZAL at `a=0`, RH (`riemannHypothesis_iff_zerosApproachLine_and_thick_primeDeviation`). At one fixed `a` it excludes every isolated top above `½+a`.

**Why this question.**
- **It is the crude count of the curve template over ℤ.** The elimination step is proved at infinite rank; what is missing is exactly a crude bound on a thick set of levels. On curves Stepanov supplies it; over ℤ it is B110.
- **It has the shape the two-scale law demands.** A bound on the prime side at scale `X` sees every zero, low and high, through the explicit formula; it is neither an asymptotic nor a local-below property of the zeros, so it is not excluded by Γ140.
- **It sits exactly at a proved boundary.** Density `1−1/k` sets of levels do not self-improve (rank barrier); thick sets do. The question asks for the cheapest set that works.
- **It is false on every fake that matters.** Beurling one-offs: the deviation is `≍X^{3/5}` at every level of the resonant tower. The golden fake: unbounded on every thick set. `cosh` models: no Dirichlet series.
- **It is precision on long runs, not everywhere.** It asks for square-root size on long stretches of scales, which is weaker than RH and does not imply a zero-free strip.
- **It lies on the dark range.** On a run `[Y,Ye^{kℓ}]` the deviation is governed by Dirichlet polynomials whose length passes the height, where mean values are collision counts of primes in short multiplicative ranges (F26). Inputs: Fejér collision identities, smooth × prime collision arithmetic, Euler mollifiers of length `log²T`.

**Tests.** T1: RH gives `O(X^{½}log²X)` everywhere; B110 implies AAL, which does not imply quasi-RH. T2: a stated inequality. T3: AAL, and RH with ZAL [L]. T4: a finite rung cannot produce arbitrarily long runs arbitrarily far out. T5: fails on Beurling one-offs and the golden fake [L]. T6: inputs are prime-side counts on thick sets; none is refuted. T7: moves Γ68, Γ69, Π114, B83.

**Limits.** It does not give ZAL. It is at least AAL-hard. A world with AAL and infinitely many off-line zeros accumulating to some `Θ>½` is not excluded by it.

### Alternatives
| Question | Why it matters | Tests | Limit |
|---|---|---|---|
| Depth density `o(T)` (B57) | closes the typical-height layer for RW, ZCG, WD, CTF, PM | T1–T7 pass | asymptotic: cannot touch AAL (Γ140) |
| Finite stratum (B13) | §3 | all pass | §3 |
| Linear AAL (B111) | §2.5 | all pass | §2.5 |
| Constant-precision first return (B97) | sign-free crude step on the dark range | T1 [D] | quasi-RH up to shielding |
| Lower bounds for tail events at the Kronecker scale (B96) | existence side of the dark range | T1 fails in the letter [D] | as hard as pair correlation past `α=1` [C] |
| Rankin–Selberg noncancellation (B109) | turns the cusp-energy rate into a full receiver | T1 vacuous | adds a receiver |

## 2.5 Breakthrough question below AAL, RH and quasi-RH: linear AAL

**Question.** *Can the deepest zero sit arbitrarily far above the asymptotic abscissa?* Let `Θ=sup Re ρ` and `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`. AAL is `Θ=Θ∞`; the finite stratum B13 is `Θ∞=½ ⇒ Θ=½`. **Linear AAL** (B111): is there a constant `C` with

  `Θ−½ ≤ C(Θ∞−½)`,

equivalently: finitely many zeros right of `½+h` ⇒ no zero right of `½+Ch`, for every `h≥0`?

**Structure [D].** Linear AAL with any `C` contains B13 (take `h=0`). As `C↓1` it becomes AAL. The constant is a dial between the finite stratum and the full law. In the ¬AAL world, linear AAL with constant `C` excludes every isolated top whose depth exceeds `C` times the depth of the remainder.

**Why this question.**
- **It is the quantitative core of AAL that the corpus can attack.** Under an isolated top `Θ` over a remainder of depth `Θ₂−½` with `Θ−½>C(Θ₂−½)`, the tower theorems give syndetic lag excursions `≍X^{Θ}` against a remainder of trace norm `≍X^{Θ₂}`: an exponent gap `≥(1−1/C)(Θ−½)` [L]. A crude count of the prime deviation at an exponent between `Θ₂` and `Θ`, on a thick set of scales and **relative to the asymptotic abscissa** — `O(X^{½+C(Θ∞−½)+ε})` — excludes the top. The question is B110 with a relative exponent.
- **It isolates the finite-rank part of ¬AAL.** A top far above everything else is a finite-rank Weil datum riding on a remainder that is small at the relevant exponent: the regime where elimination is cleanest and the price of hiding a top is largest.
- **It is a two-scale statement by construction.** `Θ` sees low zeros, `Θ∞` sees high zeros. Γ140 excludes scale-separated inputs and not this one.
- **Its failure world is the best-equipped world after the finite stratum.** Exact oscillation of `ψ(x)−x` at leading order, a zero-free strip of width `≥(1−1/C)(Θ−½)` above the layer, Lindelöf-type control in that strip, the FE-reflected bottom layer and the exceptional rank all apply [L].

**What an answer needs [L/D].** The Dirichlet series (FE models admit every layer), both scales (Γ140), and the FE converted into vertical transport (firewall). The natural form: an inequality that bounds the prime deviation at scale `X` by the zeros of depth `≥Θ∞−½` only up to a loss `X^{ε}`, on long runs of scales — a relative thick crude count.

**Tests.** T1: implied by AAL, hence by RH; does not imply quasi-RH. T2: an inequality between `Θ` and `Θ∞`. T3: B13, and with `C=1` AAL. T4: no finite rung decides it (Γ140). T5: false on `cosh` models, one-reflection-pair configurations and Beurling one-offs, all of which have `Θ∞=½<Θ` [L]. T6: relative thick crude count; FE-to-transport. T7: moves Γ68, Γ136, Γ146.

**Limit.** It leaves AAL at the top of the dial: a layer only slightly deeper than the remainder is not excluded for `C>1`.

## 2.6 If positivity, Weil positivity and spectral methods are excluded

"Spectral" is read as spectral theory of operators in every form: eigenvalues, spectral decompositions, Hilbert–Pólya realizations, trace formulas, spectral gaps, Lax–Phillips semigroups, standard forms. Kept: counting, Fourier analysis, mean values, exponential sums, power sums, Vandermonde and Turán, Dirichlet polynomials, integrality, reciprocity, recurrence, almost periodicity, Jensen and Rouché.

**The exclusion is not fatal.** The corpus proves RH for every hyperelliptic curve by Stepanov's auxiliary polynomial, power-sum elimination and the FE — no positivity, no operator [L]. Its infinite-rank analogues are sign-free and proved where they exist: the exceptional-rank window theorem (Vandermonde), the rank barrier, elimination on thick sets, RH ⇔ ZAL ∧ thick `O(√X)`, tail transport, partial returns (Jensen), zero recurrence for almost periodic functions (Bohr), long mean values as collision counts, returns freezing smooth polynomials [L]. What falls: all of Σ, the PM Krein, Lax–Phillips, cusp-energy and standard-form branches, the index routes, the count door through Hodge index.

**The question.** *Does Stepanov's method work at the returns of the prime orbit?* Precisely: for the primes `P≤y`, a precision `δ∈(0,1)` and `T≥1`, is the number of `1`-separated `δ`-returns of `P` in `[T,2T]` at most `T·exp(−cy^c)`, uniformly in `T≤exp(y^c)`, by an auxiliary-polynomial argument — an auxiliary Dirichlet polynomial `A` on `P`-smooth integers with `J` vanishing logarithmic moments, approximately vanishing to order `J` at every return (Π115), whose approximate zeros of total order `J·#returns` are bounded by a Jensen count of zeros of an exponential polynomial of length `log N` on `[T,2T]`?

**Why it opens the path.**
- **It is the curve proof's first step over ℤ.** Over `𝔽_q`, `x^q−x` vanishes at every point, an auxiliary polynomial vanishes to high order at all points at low degree, and degree bounds the number of points. Over ℤ the points at height `t` are the phases `n^{−it}`, the auxiliary polynomials exist and freeze at returns [L]; the missing step is the degree-versus-vanishing count, which here is Jensen's count of zeros of an exponential polynomial — sign-free.
- **Its output is the dark-range input.** No early return at constant precision is B97; by the heavy-return dictionary it is proportional saving B46, hence the all-height sign past the size curve and the exclusion of isolated zeros of depth beyond `c/2` [L/D].
- **It names its own obstacle precisely.** Exact returns do not exist (one fixed point) [L]; a Rouché copy needs the freezing error `δ·Σ|c_n n^{−s}|Ω(n)` below the `J`-th exponential tail on a circle [L]. The question is whether `J`, the length and `δ` can be balanced.
- **It pairs with a proved sign-free elimination.** A crude count on a thick set of scales plus elimination gives AAL (B110 ⇒ AAL); Stepanov at returns is the natural producer of crude counts in a sign-free world.

**Tests.** T1: RH gives proportional saving for `K>1` [D]. T2–T4, T7 pass. T5: fails for impure columns [L]. T6: approximate forced vanishing, Jensen counts, collision classes. Strength: quasi-RH up to shielding [D].

**Limit.** It speaks about large heights; a finite layer at a fixed height is invisible to it. The AAL half then needs the FE as a reciprocity law (Poisson, Farey, Dedekind and cotangent sums) acting as transport.

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved.** See 1.14. In particular: every horizon observable sits on the width axis; the count law is a Born rule plus damping; the partner involution has a positive state exactly when the hole is damped; **internal modular conjugation collapses to the Hilbert adjoint** (Tomita), the geometric wedge exchange fixes cusp height, and the geometric KMS period `2π` differs from the arithmetic period `1`; RH ⇔ a standard form with rational dilations and `JU(r)J=U(r^{−1})` whose natural-cone form on integer sources is `Q` [L].

**The law, read physically [D].** A realization of the partner involution as modular conjugation cannot keep the dilations inside `M∩JMJ`: they would be central and unitary. In algebraic quantum field theory the one structure in which modular conjugation inverts a one-parameter group that is not in `M` is a **half-sided modular inclusion** (Borchers, Wiesbrock) [C]: a unitary group `U(a)` with positive generator, `U(a)Ω=Ω`, and `U(a)MU(a)*⊂M` for `a≥0`; then Borchers' theorem forces `JU(a)J=U(−a)` and `Δ^{it}U(a)Δ^{−it}=U(e^{−2πt}a)`.

**The question.** *Is the functional equation of ξ the Borchers inversion of a half-sided modular inclusion of horizon algebras?* Precisely: is there a von Neumann algebra `M` of `SL₂(ℤ)`-invariant observables of the AdS₄ Rindler wedge, in standard form with vacuum `Ω`, and a positive-energy unitary group `U(a)` — the Hecke clock, `a=log` of the Hecke degree (Hecke at `p` is time translation by `log p`, Γ101) — with `U(a)MU(a)*⊂M` for `a≥0`, such that the vacuum form on integer sources has Tate limit `Q`?

**Why it opens the path.**
- **By the corpus criterion it is RH** (Γ148): any standard form with partner modular conjugation and natural-cone form `Q` is equivalent to RH. The question asks for the one structure that escapes the central collapse.
- **It explains the factor `2π` [D].** Borchers' relation rescales the translation parameter by `e^{−2πt}` along the modular flow. The arithmetic strip period `1` against the geometric KMS period `2π` is the normalization in this relation, not a mismatch.
- **It turns the count half into a physical axiom.** Positive energy is the spectrum condition. Under it, vacuum correlations of half-sided translates in Euclidean Hecke time are Laplace transforms of positive measures on `[0,∞)` (Bernstein–Widder) [C], which for the zero gas is a zero-side positivity, RH-strength (Γ8). The producer would be a positive Hamiltonian for the Hecke clock on the Eisenstein channel.
- **It has rungs.** On graph black holes partner standard forms exist iff the hole is damped [L]: test whether they are half-sided with a positive Hecke generator. On the modular surface, the Lax–Phillips outgoing subspace `D₊` with `U(t)D₊⊂D₊` for `t≥0` is the one-particle shadow of half-sided invariance [L/D]; its second quantization is the natural candidate algebra.
- **A negative answer is informative.** If no half-sided inclusion of invariant wedge algebras carries the Hecke clock with positive energy, the partner involution cannot be modular, and the physical reading reduces to a language.

**Calibration and risks.** The theta reflected squared product has no finite positive or signed Laplace representation [L]: the Euclidean positivity cannot live on the theta carrier. The zero ordinates `±γ` give a two-sided spectrum, so positive energy needs a Hermite–Biehler half of Ξ (zeros in one half-plane), whose existence for Ξ is RH; positive energy is itself the sign in physical dress.

**Second physical question.** *Does any smooth closed-horocycle observable thermalize faster than `y^{½}` by a power?* A rate `y^{½+δ}` is a zero-free strip of width `2δ` [L]; the unconditional saving is `exp(−√(−log y))` [L]; sharp shells at the RH rate need cancellation beyond RH [L].

## 2.8 If RH is a problem of topology or geometry

**What is proved.** See 1.11–1.13. The off-diagonal of Weil's form is assembled from the two half-products that exist; the zonotope surface has Hodge index by counting; atomic Frobenius graphs have infinite genus and smoothed pairs pass Hasse–Weil ⇔ RH; the archimedean place is carried by no metric, no toric Green function and no continuous kernel; off the diagonal `W=C_∞+lim T̃_r` with positive torsion energies; the diagonal must be renormalized, renormalization carries no sign, damping is lossless [L]. In topology, localization of `χ` to the prime vertices is exact with indices unbounded below; persistence is `s`-blind [L].

**Geometric question.** *Is Weil's form the Abel limit of intersection pairings of effective cycles on an honest arithmetic surface, with no counterterm?* Precisely: is there a family of arithmetic surfaces (or one surface with a degenerating metric) whose effective cycles `D_n^{(r)}`, `r↑1`, have intersection matrices `K_r(m,n)=D_m^{(r)}·D_n^{(r)}/√(mn)` that are positive kernels for `r<1` and converge pointwise — **diagonal included** — to Weil's kernel? Off the diagonal the limit must be `C_∞+lim T̃_r`; the torsion part already is such a limit on `ℙ¹_ℤ`; what is missing is a positive damping of `C_∞` and the diagonal, i.e. an archimedean fibre carrying the cusp and the jets of the trivial zeros as a damping of a positive object.

**Why it opens the path.**
- **Limits of positive kernels are positive**, so a positive answer is RH; and by the critical weight [L], a damping is the only kind of limit that carries a sign.
- **It is exactly where the corpus stops.** The off-diagonal prime part is a positive damping; the archimedean part is explicit and sign-changing; no half-product supplies the diagonal [L].
- **It names the carrier.** The jets are the even-sector Lefschetz trace of the dilation `x↦nx` of `ℝ` at its fixed point [L], of rank `≥3` on coprime orders, depending on ratios, not products [L]. The carrier is a geometry of the dilation action of `ℝ₊^*` on `ℝ` with an orientation-reversing involution — the archimedean analogue of the Frobenius action at a fixed point.
- **Its rungs are explicit.** The zonotope surface (pole plane + first channel, a count) [L]; the cubic-spline smoothing (genus `c_B(0)/2` under RH) [S]; single pairs of degrees (two-site tests, window rungs).

**Topological question.** *Is there a natural self-map of a model of the prime complex, not homotopic to the identity, whose Lefschetz number is `M(N)` and whose local fixed-point indices are bounded?* Maps homotopic to the identity fix exactly the primes with indices unbounded below [L]; matchings stop at Betti `≍N`; persistence is `s`-blind [L]. A map of Lefschetz number `M(N)` with `O(N^{½+ε})` fixed points of bounded index would give the half-power law; `|χ̃|≥c√N` infinitely often [L] forces exactly square-root many. Candidates: dilation-type maps on a completed complex, the `SL₂(ℤ)` action on Farey fractions (F24), the power-map Frobenius of the zonotope surface. First rung: the prime complex of `𝔽_q[T]`, where Möbius sums vanish past degree one.

**Limit.** Over `𝔽_q` these structures come from a variety; over ℤ none is constructed. Heights over number fields give central-value signs, not off-line zeros [D].

## 2.9 Does closing RH need a new field?

No theorem says so. The evidence is structural: every available tool stops for a proved reason, and the curve proof's freebies — finite rank and periodicity — are both absent over ℤ.

| Tool | Why it stops |
|---|---|
| Size estimates | before half-width `21/40`; all heights only to `a≈log log X` |
| Markov, Perron | frustration past `log ρ` |
| Type I/II sieve data | parity-blind |
| Linear floor identities, ledgers | blind to every zero |
| Barriers, short detectors | blind to purity; last-scale floor |
| Mollifiers | outer; near-unit moments need the primes up to `log²T` |
| Conditional laws, mean values | stop at the Kronecker scale; past the height collision counts |
| Euler and prime coordinates | stop at `Re s=1` |
| Concentration-compactness at the critical curve | returns the window threshold plus the pole channel |
| Finite computation | decides no rung of the finite stratum |
| Zero statistics at one scale | cannot decide the finite stratum or AAL |
| FE with analytic shape | admits every finite layer |
| Positivity, Euler products, counting, continuation | carry finite layers |
| Density statements on tower levels | rank barrier |
| Exact Frobenius | no exact returns |
| Renormalization | carries no sign |
| Metrics, toric and continuous kernels | cannot carry the archimedean place |
| Unitarity, Schur, `C*`, KMS, internal modular conjugation | wrong involution; central collapse |
| Horizon observables | width axis; VK saving |
| Homotopy, persistence, identity-homotopic fixed points | `s`-blind; primes fixed with unbounded indices |

**What is built, and where it stops.**
| Field | Object | Stops at |
|---|---|---|
| Infinite-rank Weil theory | towers, exceptional rank, thick sets, elimination, critical weight, Frobenius substitute | the thick crude count for ζ; ZAL |
| Zero-configuration geometry | abscissa laws, transport, two-scale law, curve split | a two-scale transport input |
| Surface of Spec ℤ | half-products, zonotope, point count, Frobenius pairs | the diagonal; the jets carrier |
| Arithmetic inner functions | half-plane, causal order, inner mass | size, not vanishing |
| Prime torus and tail arithmetic | `(t,ω_t)`, first return, Euler tail, tail transport | the Kronecker scale; upper bounds past it |
| Rigid arithmetic of cuts | cut system, ledgers, kernel | parity is the strip |
| Holography, ringdown, counting holography | waves, Born rules, count laws, standard forms | the count over ℤ; a positive-energy carrier |
| Effective and renormalized geometry | polar surfaces, torsion forms, compensation, prime boundary, vertex dynamics | sign at the critical weight; `s`-blind topology |
| Arithmetic positive duality | Beurling systems, firewall, relocation | the critical line |

**The proposal: two-scale infinite-rank Weil theory over `Spec ℤ`.** A field that proves RH must build, at infinite rank, the two freebies the curve proof gets from finite rank and periodicity, plus the count, and the corpus fixes where each must act.

| Aspect | Content |
|---|---|
| What it is about | zeta-like objects with infinitely many modes, a Dirichlet series and a functional equation, studied in the exceptional coordinate (modes beyond each depth) rather than the size coordinate; the coupling between low and high zeros that the Dirichlet series imposes; counts at the critical weight |
| Objects | zero configurations; Weil towers at every base and their level sums; isolated tops and their reflected bottom layers; thick sets of levels; Euler heads and tails; returns of prime subsets and frozen smooth polynomials; half-products (𝔽₁-zonotope, `ℙ¹_ℤ` torsion orbits) and Frobenius graphs; damping families of positive kernels; the archimedean dilation of `ℝ` with its jets |
| Language | exceptional rank, thick set, well-founded tower, isolated top, eventual-to-global, zero transport, tail event, two-scale property, critical weight, damping versus renormalization, half-product, jets carrier, partner involution |
| Mechanisms | Turán–Vandermonde elimination at the exceptional rank; the Dirichlet series as the coupling between scales; the FE converted into vertical transport; approximate forced vanishing at returns with Jensen counts; damping limits of positive intersection pairings |
| Tools to build | a thick crude-count theorem for the prime deviation (B110); a well-foundedness (ZAL) mechanism; an FE-to-transport principle (B112); a damping presentation of the diagonal (B88) with a jets carrier; Stepanov counting at returns (2.6) |
| Questions it must answer | Which Dirichlet-series property of ζ couples the zeros below a height to those above it? How does the FE, a height reflection, become transport in height? Which prime-side bound holds on long runs of scales? What makes the towers of ζ well-founded? What positive object damps to the diagonal of Weil's form? What carries the jets of the trivial zeros? |
| Criteria | reduce to the Lean curve proof at finite rank; reproduce AAL for periodic, recurrent and almost periodic configurations; fail on `cosh` models through the Dirichlet series, on Beurling one-offs through the FE, on relocations through positivity, on Wolff configurations through well-foundedness; be invariant under symmetric shifts; respect the rank barrier; produce signs only by damping |
| Calibration | curves (finite rank, periodic, complete proof [L]); graph black holes (FE without damping [L]); Beurling one-offs (Euler product without FE [L]); `cosh` models (FE without Dirichlet series [L]); shifted products (FE, AAL ⇔ AAL(ξ) [L]); Wolff configurations (non-well-founded [L]); the zonotope surface (a count [L]) |

**Limits.** Binary problems at the Kronecker scale are parity problems [C]. Excluding a finite layer is an exceptional-zero problem of Landau–Siegel type [D]. ZAL is quasi-RH.

## 2.10 Does an AAL proof or falsification need a new field?

**Why the existing tools stop [L].** AAL is vertical transport of zeros. Tools that see one scale cannot decide it (two-scale law). The FE as a zero symmetry keeps heights. Positivity, Euler products, linear counting and continuation carry finite layers. Uniform almost periodicity would give it, and ζ is not uniformly almost periodic in the strip; almost periodicity at large height is not enough. Head returns are the wrong events: zeros are tail events, transported events are tail-bad and rare, and every density statement bounds them from above. A moving functional equation (Riemann–Siegel at height `t`, head of length `√(t/2π)`) does not transport a zero by a head return: freezing that head needs every prime phase up to `√(t/2π)` within a small precision, which at bounded harmonic defect first happens at heights `≥exp(c(log t)^{3/2}/log log t)` [L, bracket], where the Riemann–Siegel head is longer and the frozen head no longer determines ζ [D].

**The field: rare-event transport theory of Dirichlet series.** Its subject is the vertical transport of exceptional events — zeros, small values, tail cancellations — for Dirichlet series with an Euler product and a functional equation, and the rigidity of finite exceptional sets.

| Aspect | Content |
|---|---|
| What it is about | when a single exceptional event of a Dirichlet series (a zero right of the line) forces infinitely many at larger heights; the existence, not the frequency, of rare tail events; finite exceptional layers as rigid objects |
| Objects | zero configurations and their transport relation; the vertical shift group and the Bohr/prime torus; Euler heads and tails at every cut; partial returns with omitted arcs; isolated tops; towers and exceptional ranks; `cosh` models, Beurling one-offs, Wolff configurations, relocations as calibration |
| Language | transport, rare event, tail event, tail-good/bad height, isolated top, exceptional rank, two-scale property, relative thick count, conditional recurrence |
| Mechanisms | Rouché and Jensen under partial approximation; Turán–Vandermonde at the exceptional rank; FE as a height reflection composed with vertical twists; Deuring–Heilbronn-type interaction between one exceptional zero and the rest [C], read as attraction rather than repulsion |
| Tools to build | zero transport from weak (Stepanov, Weyl, Besicovitch) almost periodicity with zero-disc control; lower bounds for tail events at the Kronecker scale (B96); relative thick crude counts (B111); an FE-to-transport principle (B112); a classification of Dirichlet series with Euler product and FE carrying a finite layer (B103, B84) |
| Questions it must answer | Which weak almost periodicity transports zeros? Does an isolated top force, through the Euler product and the FE together, a zero of the tail at larger heights? Is there any Dirichlet series with an Euler product and an FE and a finite layer? What is the smallest FE defect carrying a one-off? Can the rigid ¬AAL world (exact finite oscillation of `ψ` with a power gap) coexist with the FE of ξ? |
| Criteria | reproduce Bohr's recurrence on the half-plane of absolute convergence and AAL on curves and exponential polynomials; fail on `cosh` models (no Dirichlet series), Beurling one-offs (no FE), one-pair configurations; be shift invariant; never use the position of the line beyond the FE involution and Hardy's zeros; couple scales |
| Falsification side | a ζ-specific finite layer cannot be produced by rational surgery with positive coefficients (first-gap negativity) [L]; a falsification needs an intrinsic construction — a Dirichlet series with Euler product, FE and a finite layer — of which no example exists |

**Limits.** AAL is not implied by any density statement; its finite case is an exceptional-zero problem [D].

## 2.11 Without positivity, Weil positivity and spectral methods: which field?

Inner-function theory, holography's flux and Lax–Phillips, standard forms, Hodge index and the count door through polarization lose their core. What remains is the toolkit of the curve proof — auxiliary functions, power sums and the FE as an identity — and its infinite-rank versions already in the corpus: elimination at the exceptional rank, thick sets, tail transport, frozen polynomials at returns, collision counts.

**The field: sign-free Weil theory over ℤ — Stepanov at the archimedean place, Turán at infinite rank, reciprocity as transport.**

| Aspect | Content |
|---|---|
| What it is about | proving the crude count and the transport law by counting and cancellation: auxiliary Dirichlet polynomials vanishing approximately at the returns of the prime orbit, Jensen counts of their zeros, power sums of zeros on windows of levels, reciprocity laws acting on heights |
| Objects | auxiliary Dirichlet polynomials on smooth integers; returns of prime subsets as approximate multiplicative groups; level sums of towers; thick sets of scales; smooth × prime products and their gcd collision classes; Farey fractions, Dedekind and cotangent sums; the prime deviation along geometric scales |
| Language | Frobenius substitute, frozen polynomial, forced vanishing, return, heavy subset, collision class, exceptional rank, thick set, reciprocity, transport |
| Mechanisms | Stepanov's degree-versus-vanishing count with Jensen's zero count; Vandermonde/Turán lower bounds at the exceptional rank; integrality `\|n\|≥1`; sum-product and incidence bounds for hyperbolas `xy=c`; reciprocity along the Euclidean algorithm as a height-moving identity |
| Tools to build | Stepanov counting at returns (2.6); a thick crude count from collision counting past the height (B110); incidence bounds with a prime-density saving for smooth × prime near-collisions; a sign-free FE-to-transport principle through Poisson and Farey reciprocity |
| Criteria | no quadratic form with a sign, no operator spectrum; prove Hasse–Weil over `𝔽_q` in the same language (the corpus does for hyperelliptic curves [L]); separate rational primes from Beurling one-offs through count distance or reciprocity; any parity output at power saving is a strip [L]; respect the rank barrier |
| Questions it must answer | How many returns of the primes `≤y` can occur below height `exp(y^c)`? Is the fine multiplicative energy of smooth × prime products at scale `1/T` at its random value? Do long runs of scales carry square-root prime deviations? Does reciprocity, iterated along the Euclidean algorithm, move zeros in height? |

**Limits.** No source produces parity at power saving other than a strip [L]. No named mechanism above VK.

## 2.12 If RH is a physical phenomenon in AdS with a modular horizon: which field?

Holography, ringdown and counting holography are formalized; their positive results are exact solutions, width-axis receivers, Born rules, standard-form criteria; their negative results are that wave dynamics, unitarity, Hecke, KMS, `C*`, internal modular conjugation, the FE, integrality, linear counts and Hecke at a second place do not carry universal damping [L].

**The field: arithmetic modular theory of horizons — half-sided inclusions and positive energy for arithmetic quotients.**

| Aspect | Content |
|---|---|
| What it is about | the modular structure (Tomita–Takesaki) of observable algebras on arithmetic quotients of AdS wedges, in which the functional equation is a modular inversion of a translation group not contained in the algebra; the spectrum condition (positive energy) for the Hecke clock as the physical form of damping |
| Objects | `SL₂(ℤ)\`(Rindler wedge of AdS₄); invariant wedge algebras and their standard forms; half-sided modular inclusions; the Hecke clock `U(log n)`; Lax–Phillips outgoing subspaces and their second quantization; graph black holes; the Eisenstein and cusp channels; Hermite–Biehler halves of Ξ |
| Language | modular conjugation, partner involution, half-sided inclusion, Borchers triple, positive energy, outgoing subspace, Euclidean Hecke time, natural cone, damping, width |
| Mechanisms | Borchers' theorem (`JU(a)J=U(−a)`, `Δ^{it}U(a)Δ^{−it}=U(e^{−2πt}a)`); second quantization of half-sided invariant subspaces; Osterwalder–Schrader reconstruction; Bernstein–Widder representation in Euclidean time; Tate limits of counts |
| Tools to build | a half-sided inclusion of invariant wedge algebras carrying the Hecke clock; a positive generator for the Hecke clock on the Eisenstein channel (B114); a dictionary between Jacobians of curves (Rosati) and half-sided horizon structures; a physical noncancellation principle for `Λ_g(ρ/2)` |
| Criteria | recover Hasse–Weil for graph black holes and curves from positive energy; fail on fakes through the spectrum condition, not dynamics; avoid the Tomita central collapse; explain the `2π` against `1` as the Borchers normalization; use only smooth sources (sharp ones need more than RH) |
| Questions it must answer | Are the graph-black-hole standard forms (which exist iff damped) half-sided inclusions with positive Hecke energy? Is the Lax–Phillips outgoing structure of the modular surface the one-particle shadow of a half-sided inclusion? Which Hermite–Biehler half of Ξ is the positive-energy vacuum? Why does arithmeticity (no second place) make the Hecke clock positive? |

**Limits.** Positive energy for the Hecke clock is RH-strength; every proved physical statement is a restatement, an edge theorem, a width-axis receiver or the absence of a law. The geometry is locally pure AdS.

## 2.13 If RH is a problem of topology or geometry: which field?

**The field: renormalization-free intersection theory of Spec ℤ.** Counts are intersection numbers of effective cycles; signs are limits of positive pairings by damping, never by counterterms; the archimedean place is a geometry of the dilation of `ℝ` with its jets; topology enters through `s`-dependent completions and signed localization.

| Aspect | Content |
|---|---|
| What it is about | building the missing half-product `Spec ℤ×Spec ℤ` only as far as needed: the diagonal and the archimedean fibre, by a damping of positive intersection pairings whose off-diagonal limit is the known assembly (cusp + jets + torsion on `ℙ¹_ℤ`) |
| Objects | 𝔽₁-zonotope surface; `ℙ¹_ℤ` with torsion orbits and positive twisted torsion energies; Frobenius graphs and their smoothings; the archimedean compensation `C_∞`; the dilation of `ℝ` with its even-sector trace; the prime-product complex with its prime-vertex dynamics; completed prime boundaries on `ℓ²(n^δ)` |
| Language | half-product, Frobenius graph, genus of a smoothing, damping, critical weight, counterterm, jets carrier, local index, Lefschetz localization |
| Mechanisms | Hodge index by counting (zonotope); damping limits of positive kernels (lossless); Lefschetz–Hopf localization; Riemann–Roch on surfaces; Hecke equivariance |
| Tools to build | a jets carrier: a fibre on which the dilation of `ℝ` acts with the jets as intersection numbers (B115); a damping presentation of the diagonal (B88); a self-map of Lefschetz number `M(N)` with bounded local indices (B106); `s`-dependent completions of the prime complex whose homology sees the zeros |
| Criteria | reduce to the zonotope Hodge index and the curve count laws; reproduce infinite genus of atomic graphs and genus `c_B(0)/2` of smoothed pairs under RH; carry the jets with rank `≥3` on coprime orders and ratio dependence; never use a counterterm as the source of sign; reproduce Betti `≍N` and prime-vertex fixed points with unbounded indices |
| Questions it must answer | What carries the archimedean place as a positive damping? What is the self-intersection of a Frobenius graph after damping, and is it finite? Which self-map of a completed prime complex has Lefschetz number `M(N)` and bounded local indices? Which completion of the prime complex depends on `Im s`? |

**Limits.** Over `𝔽_q` these structures come from a variety; over ℤ none is constructed. Actual modular surfaces see only the cuspidal part [D].

## 3. The one big question

**Can ζ have finitely many, but not zero, zeros off the critical line?** (B13) It is AAL at depth `h=0`, strictly below AAL and below linear AAL (2.5), and below quasi-RH.

| Form | Statement | Evidence |
|---|---|---|
| Configuration | `Θ∞=½ ⇒ Θ=½`; finitely many right zeros ⇒ none | `ConfigAbscissa.AbscissaLawAt`, `zetaZeroConfig_abscissaLaw_iff` [L] |
| Index | the negative index of Weil's kernel is `0` or `∞`; equivalently on one two-prime lattice | `zetaKernel_finiteIndex_tfae` [L] |
| Heat | a bounded number of non-real heat zeros for `t>0` forces none at `t=0` | `zetaKernel_finiteIndex_tfae` [L] |
| Jensen | `N_d` bounded forces `N_d=0` | FFP [L] |
| Slice | eventual slice positivity forces positivity | `eventualSlicePositivity_iff_finiteOffLine` [L] |
| Tower | in the finite stratum, one non-blind prime tower is PD | `FiniteSupportMakesAlmostEveryPrimeDecideZeta` [K] |
| Weil tower | a single top pair `Θ±iγ` makes the lag large at every level of its tower at base `π/γ`; B13 at rung `k=1` is the exclusion of that tower behaviour | `eventually_lag_large_of_single_top_pair` [L] |
| Explicit formula | `ψ(x)−x` is never `−Σ_{j≤k}2Re(x^{ρ_j}/ρ_j+x^{1−ρ̄_j}/(1−ρ̄_j))+O(√x log²x)` with `k≥1` | [L/D] |

### Why this one

- **It is the finite-rank piece of AAL.** The finite stratum is a finite-rank Weil datum (the off-line set) over a critical remainder, the regime in which the curve proof self-improves; the corpus proves elimination there (exceptional rank, price of hiding) [L]. The step to prove is that finitely many exceptional modes force none.
- **Its negative world is the most rigid and best-equipped one.** Lindelöf; a zero-free half-plane right of the layer; 100% critical zeros; Weil's form PSD on a subspace of finite codimension; boundedly many non-real heat zeros; bounded `N_d`; one non-blind tower carries the full index; the explicit formula exact up to finitely many oscillating terms over an RH-size remainder; positive annihilators remove the off-line set at a quantified cost on the line; the lag at the resonant base is large at every level [L/K].
- **It names exactly what is missing.** By the two-scale law the input cannot be a statistic of the zeros at large height or a finite verification; by the `cosh` models it must use the Dirichlet series; by the firewall it must use the Euler product together with the FE, and turn the FE into transport [L]. No other question in the corpus has its required input so tightly constrained.
- **It is false on every corpus fake.** Every one-off has finitely many off-line zeros; `cosh` models and one-pair configurations violate it; tempered finite-support models defeat fixed-ratio positivity [L/K].
- **It has a first rung.** `k=1`: one quartet `{ρ,ρ̄,1−ρ,1−ρ̄}`, `ρ` simple — "ζ is not a one-off" — with its tower form at base `π/γ`.

| Kind | Best form | Why it ranks lower as the one big question | Evidence |
|---|---|---|---|
| Configuration law, full | AAL (B83) | no mechanism has moved it | [L] |
| Configuration law, linear | linear AAL (B111) | contains B13; its inputs are relative thick counts | [D] |
| Tower crude count | thick crude count (B110) | at least AAL-hard | [L] |
| Critical ratio | pole channel at every ratio (B101, B104) | RH-strength or architectural | [L] |
| 100% near the line | depth density `o(T)` (B57) | asymptotic: cannot touch the finite stratum | [L] |
| All-height sign | constant-precision first return (B97) | quasi-RH up to shielding | [D] |
| Kronecker-scale law | lower bounds for tail events (B96) | binary prime problems | [D]; [C] |
| Topology | localization of `M(N)` (B106) | RH-strength at `√N` | [L] |
| Horizon | any exponent past `½` (B14, B71) | interior exponent is a strip | [L] |
| Count | Tate limit / damping of the diagonal (B87, B88) | RH-strength | [L] |
| Theta | adaptive head near critical zeros (B102) | RH-strength | [L] |
| **Finite stratum** | **B13** | **strictly below AAL; decisive for many receivers; most structure; false on every fake; rung `k=1`; input type fixed by three theorems** | **[L/K/D]** |

### What an answer does
| Answer | Effect |
|---|---|
| **B13 proved** | Finite index of Weil's kernel ⇒ RH; finite index on one two-prime lattice ⇒ RH; bounded heat count ⇒ RH; bounded `N_d` ⇒ RH; eventual slice positivity ⇒ RH; RH above some height ⇒ RH [L]. HF, HKT, AKLT, CWS, SC, ZCG heat count, WD heat charge, LA, FFP lose the obstacle "finite exceptions remain" and need only a finiteness producer (B12, B23). |
| **B13 proved** | The first theorem in which the Dirichlet series and the FE together exclude off-line zeros: it names the two-scale coupling that separates ζ from every `cosh` model and every one-off. |
| **B13 proved** | AAL reduces to worlds with infinitely many off-line zeros; F1 and F22 reduce to ZAL plus "an infinite lower set cannot carry a finite top layer" (linear AAL at `C>1`, then AAL). |
| **B13 refuted** | RH is false with finitely many off-line zeros, all above the verified height; ζ is a one-off; the explicit formula is RH up to finitely many terms. |

### What is proved around it
| Channel | Status | Module |
|---|---|---|
| Finite stratum | TFAE: finite index, lattice index, finite off-line set, heat count, eventual RH | `HeckeKreinToeplitz/TheFiniteIndexStratumOfZetaIsLindelofDeep` [L] |
| Towers decide | under finite support RH ⇔ one non-blind prime tower PD | `ArithmeticKreinLangerTheory/FiniteSupportMakesAlmostEveryPrimeDecideZeta` [K] |
| Lindelöf | finite off-line support ⇒ zeros approach the line ⇒ LH | `RHTower/LindelofCosineFiniteDefectDepth` [L] |
| Jensen count | `N_d` nondecreasing, `sup_dN_d` = off-line multiplicity | `FiniteFreeProbability/{JensenCountsOffLineZeros,NonRealJensenCountBound}` [L] |
| Abscissa laws of configurations | purity ⇔ ZAL ∧ AAL; AAL ⇔ transport; ¬AAL ⇔ finite layer; one pair violates AAL at `h=0`; curves split | `ZeroConfigurationGeometry/AbscissaLaws/*` [L] |
| Two-scale law | asymptotic and local-below properties do not decide B13 | `ZeroConfigurationGeometry/AbscissaLaws/TheAbscissaLawIsNotAsymptotic` [L] |
| FE models | `cosh` models carry every finite layer | `InfiniteRankWeilTheory/TheFunctionalEquationAdmitsEveryFiniteLayer` [L] |
| Firewall | positive classes, continuation, reflection symmetry carry finite layers | `ArithmeticPositiveDuality/TheCriticalLineFirewall` [L] |
| Tower form | syndetic excursions; single top pair at every level of its resonant tower | `InfiniteRankWeilTheory/TheTowersOfZeta` [L] |
| Elimination | exceptional rank, price of hiding, rank barrier | `InfiniteRankWeilTheory/{TheExceptionalRankDecidesTheWindow,TheRankBarrier}` [L] |
| Annihilators | finite sets at any multiplicity; harmonic packets cost `≥m`; left-growth law | `ArithmeticPositiveDuality/{PositiveTwoPrimeAnnihilators,ArbitraryMultiplicityNearUnitAnnihilatorMass,HarmonicZeroPacketsForcePositiveAnnihilatorMass,PositiveAnnihilatorAccuracyForcesLeftGrowth}` [L] |
| Annihilator bandwidth | order `r+1≥2` and tail mass `H` force a supported logarithmic frequency `≥log 2+2(log 2)r²/(H−1)`; full Chebyshev mass bound at fixed bandwidth | `ArithmeticPositiveDuality/TheChebyshevCostOfAnnihilatorMultiplicity` [K] |
| Reflected-pair annihilation | pair `σ±δ+iγ`: sharp hyperbolic cost at finite bandwidth; central mass has unattained infimum `2^δ` over positive two-prime annihilators and heights | `ArithmeticPositiveDuality/TheHyperbolicCostOfReflectedZeroPairs` [K] |
| Rigid oscillation | finite oscillation of `ψ`, dilation annihilation | `ZeroConfigurationGeometry/{TheOneOffsAreFiniteOscillationsOfThePrimeError,MultiplicativeDilationAnnihilationOfPrimeError}` [L] |
| Surgery | rational relocation fails at the first integer gap | `ArithmeticPositiveDuality/TheFirstIntegerGapDetectsRelocation` [L] |

### The forms of the missing input
1. **Dirichlet series + FE on a finite set.** In the stratum `N(T)−N₀(T)=2k` is eventually constant and the explicit formula is exact up to `2k` oscillating terms. The input is a statement about ζ that sees both the finitely many off-line zeros and the critical zeros above them — a prime-side bound on long runs of scales at the resonant base `π/γ` (tower form), or a theta-type transform whose two ends the FE exchanges with the Euler product on one end.
2. **Index form.** A zero-or-infinity law for the actual two-prime lattice kernel; proved under escape, mixing or slope-height decay [L]; the input is the arithmetic mixing property of the kernel in the stratum, where Lindelöf supplies growth control.
3. **Tower form [K].** One non-blind prime tower decides: a one-dimensional Toeplitz problem with finite negative index.
4. **Annihilator form.** A positive two-prime annihilator of the off-line set that is `ε`-accurate on `Re s≥1` must grow like `ε^{−(β−½)/(1−β)}` on the line [L]; compare with what Lindelöf and the index structure allow.
5. **Weil-tower form.** At base `π/γ` the lag is `≥ce^{(β−½)L}` at every level [L]; one thick-set bound at that base with any exponent below `β−½` excludes the quartet.

### First steps
1. Rung `k=1`: write the one-quartet world explicitly and apply every proved receiver of the stratum — window, tower, heat, Jensen, annihilator, Weil tower at `π/γ` — recording the constraint each imposes on `(β,γ)` (A47).
2. Test the escape and mixing hypotheses of the dichotomy theorems on the kernel of the lattice `⟨2,3⟩` in the stratum, using Lindelöf.
3. For one quartet, compute the blind primes and the explicit negative direction on a non-blind tower; test it against the FE mirror `1−ρ̄`.
4. Compare the cheapest positive annihilator of one quartet with Lindelöf-size bounds on `Re s=½`.
5. Determine which Dirichlet-series identity at the resonant base `π/γ` couples the quartet to the critical zeros above it — the two-scale input in its smallest instance.

### Validation
| Test | Verdict |
|---|---|
| T1 | Pass. RH implies it; it does not imply quasi-RH [D]. |
| T2 | Pass. A stated implication in each form. |
| T3 | Pass. The effects table. |
| T4 | Pass. No finite verification decides it [L]. |
| T5 | Pass. False on every one-off, `cosh` model and one-pair configuration [L]. |
| T6 | Pass. Each form names an unrefuted input. |
| T7 | Pass. Moves Σ4, Γ67, Γ68, Γ136, Γ140, Γ146 and block S8. |

### Limits
- B13 leaves every world with infinitely many off-line zeros; linear AAL, AAL and ZAL remain for RH.
- Its receivers become RH receivers, but their producers (finite index, bounded heat count, bounded `N_d`) are at least quasi-RH (B12, B23).
- Positivity, Euler products, counting, continuation, positive Hecke combinations, rational surgery, the FE with analytic shape and scale-separated statistics cannot exclude a finite set [L].
- Excluding finitely many zeros is an exceptional-zero problem; classical exceptional-zero repulsion is consistent with the finite stratum [D].
