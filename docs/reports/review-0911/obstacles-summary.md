# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `1fff6409b7` (2026-11-09) and the working tree of that time. Working log: `logs/review-0911-statusquo-research-2.md`.

Evidence: `[L]` Lean source, integrated; `[S]` Lean source unintegrated (umbrella not wired into `MainTheorems`, or file not tracked); `[K]` Lean with transitive axiom audit; `[D]` deduction, not a Lean theorem; `[N]` numerical, uncertified; `[C]` classical, not formalized. Sections 2.3–2.13 and 3 are interpretation and ideation; every untagged statement there is a proposal, not a result.

**38 live formulations; 9 candidates.** HJ→PA; BSH→CDC; FEL's BSY criterion→CTF. Candidates: APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF.

Notation: `Θ=sup Re ρ`; `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`; **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **LinAt C** `Θ−½≤C(Θ∞−½)`; `Φ(L)=e^{−L/2}primeDeviation(e^L)`; `c_B` the cubic-spline orbit correlation, `Re S=c_B` its trace, `Re W(B±τ_vB)=2c_B(0)±2c_B(v)`; `Γ_n` the smoothed Frobenius graph of degree `n`; `P(d)` the smoothed von Mangoldt count in the window of `d`, `A(d)` its archimedean-plus-pole prediction, `c_B(log d)=A(d)−P(d)`; a **sampling weight** `0≤w≤Λ` has `Σw(n)n^{−s}→∞` as `s↓1` and no other singularity on `Re s=1`; a **power-saving gap set** `D` meets every `[x,x+x^θ]` for some `θ<1` and all large `x`; `G_s(d)=e^{−(s−1)d}/(4π sinh d)` on `ℍ³`; `G^{T_p}_s` the Green function of the Bruhat–Tits tree of `PGL₂(ℚ_p)`; `H_t` the heat deformation of Ξ; `Λ_F(s)=∫_𝒟F·E*(s−½)` the completed transform of a seed; `F_n=Π_{p|n}(X²+p)`; the **corrected exceptional current** `𝒞(σ,a,t)=ΣΛ(n)n^{−s}e^{−yn²}+e^{−y}ζ′/ζ(s)−½Γ((1−s)/2)y^{−(1−s)/2}` at `s=σ+it`, `y=e^{−at}`; the **observation rate** of a zero `a(Re ρ−σ)/2−π/4`.

## 1. Big picture

### 1.1 One inequality per prime, with or without a sign
The three wall families have one common minimal face [L]:

  RH ⇔ `c_B(log p)≥−K` for every prime `p` ⇔ `c_B(log p)≤K` for every prime ⇔ `P(p)≤A(p)+K` ⇔ `Re W(B+τ_{log p}B)` bounded below at every prime ⇔ `Re W(B−τ_{log p}B)` bounded below at every prime.

The two-sided form needs no sign: RH ⇔ `|c_B(log p)|≤K` for every prime, and zero width `≤σ` ⇔ `|c_B(log p)|≤Kp^σ`; the proof uses absolute convergence, analytic continuation and the Laplace rate theorem — one interpolation step improves width `a` to `max σ (a+θ−1)` on a set with gaps `O(x^θ)` — and neither Landau's theorem nor Weil positivity [S]. The test `B+τ_{log p}B` is a sum of two translates of one fixed cubic spline; its Weil energy `2c_B(0)+2c_B(log p)` is the defect of the effective class `Γ_1+Γ_p`, and `c_B(log p)=A(p)−P(p)` is the error of the smoothed prime count in the window of `p`. Read classically, `c_B(log d)` is the spline-smoothed PNT error in a fixed multiplicative window around `d`; the degree `d` is only the window's location [D]. Unconditionally `|P(n)−A(n)|≤C√n·exp(−√(log n)/10)` for all `n≥1` [L]. The growth exponent reads the width: zero width `≤a` ⇔ `c_B(log p)≥−Kp^a` ⇔ `≤Kp^a` (`0≤a<½`) [L]. One-sided, the proof is the gap method (the Lipschitz constant of the trace improves with the width), Landau's theorem for the nonnegative density `K±c_B`, and the absence of real zeros of ζ in the strip; at the degrees `p^k` the zero-free strip improves itself by the factor `1+1/k` per Landau step, starting from Huxley's prime gaps [L]. The same holds at the integers, the squares, the `n^k` and every power-saving gap set; the geometric degrees `q^n` alias and decide nothing [L].

### 1.2 Deligne's argument runs over ℤ except for its uniformity
The traces `2Re S(log p)` are the point counts of the virtual motive `M=Σ_ze_zℤ(−z)` of the zeros. Positivity of the even tensor powers is free; RH ⇔ `M^{⊗2k}` have a common half-plane of convergence ⇔ `Σ_{p≤N}log p(2Re S(log p))^{2k}≤C_kN^{1+A}` with `A` independent of `k` [L]. The Rankin square `ΣΛ(n)(2Re S(log n))²n^{−s}` has abscissa exactly `2maxRe ρ` [L]. Bombieri's second count (the twist excluding real Frobenius eigenvalues) is replaced by the absence of real zeros of ζ: the Stepanov side `c_B≥−K` is blind exactly to configurations whose top layer is a nonnegative almost periodic function (a real zero masks precisely the shallower zeros), the other side has no mask [L]. Base change: the traces at the degrees `n^k` have the Dirichlet series `Σ_ze_zζ(s−kz)` [L].

### 1.3 RH is ZAL plus AAL; gaps, not density, carry the difference on the prime side
For every zero configuration purity ⇔ ZAL ∧ AAL, with the strict dial `Pure ⊊ AAL ⊊ LinAt C₁ ⊊ LinAt C₂ ⊊ (∃C LinAt) ⊊ B13`, `∃C LinAt ⇔ (ZAL ⇒ Pure)`, `AAL ⇔ ∀C>1 LinAt C` [L]. A one-sided crude bound of the spline traces at a **sampling set** of primes — one residue class, the primes off a set of relative logarithmic density zero, the degrees `p^aq^b` — leaves no deepest off-line zero of ζ: AAL; with ZAL it is RH [L]. ZAL supplies only the attainment of the top; whether a sample supplies it is decided by its gaps [L/S]:

| Sample of degrees | One-sided crude bound gives | Evidence |
|---|---|---|
| all primes, `p^k`, `n^k`, squares, any power-saving gap set | purity (RH for ζ) | [L] |
| primes off an exceptional set with `#E∩[1,X]=O(X^α)`, `α<1`, or with exceptional log-mass `≤c·x^θ` in every late `(x,x+x^θ]`, `7/12<θ<1`, `c<1` | purity (RH for ζ) | [S] |
| two-prime difference lags `log m−log n`, `m,n∈⟨p,q⟩` | purity (RH for ζ) | [L] |
| primes off a relative-density-zero set; a residue class; `p^aq^b` | AAL for ζ; unattained-top configurations pass off density-zero sets (periodic harmonic clusters with resonant holes) | [L]; countermodel [S] |
| the very smooth degrees (every prime factor `p` of `d` with `p⁴≤log d`) | nothing without attainment; unattained-top configurations pass, although every prime eventually takes part | [S] |
| the degrees of finitely many primes | nothing without attainment | [L] |
| one prime's powers `p^a` | nothing (aliasing at `2πm/log p`) | [L] |

For ζ: RH ⇔ ZAL ∧ the Stepanov bound at the primes off a density-zero set, and configuration arguments cannot remove ZAL from that statement; RH ⇔ the Stepanov bound off any power-thin exceptional set [S]. The residue-class branch is AAL only because the corpus lacks power-saving gaps for the primes `≡a (mod q)`; with them it is RH (A59) [D].

### 1.4 What decides AAL and the finite stratum, and what cannot
- **Two scales.** Properties of the zeros above a height, or below a fixed height, decide neither B13 nor any linear law nor AAL [L].
- **Analytic shape.** FE, order one and reality admit every finite top layer, also over a remainder of positive asymptotic abscissa [L].
- **Family uniformity.** A finite-stratum law valid for every heat deformation `H_t` is RH; among `Φe^{−τx²}` only `τ=0` has an absolutely convergent Dirichlet series [L].
- **Firewall.** Continuous Beurling systems, positive discrete and integer-norm Euler products with linear counting continued across `Re s=½`, and rational-prime Euler products carry a finite off-line layer; of Euler product, integrality, linear counting, continuation across the line and the FE, only the FE excludes the layer [L].
- **FE rigidity.** A countable Beurling system whose theta function satisfies Riemann's FE up to a measurable polynomially bounded `L¹` or `L²` defect is the rational primes, with zero defect; with an exact completed FE likewise [L]. Every AAL input concerns the exact identities of ζ.
- **Positive annihilators.** Nonnegative two-prime polynomials annihilate every finite zero set; exact mass `H` is possible exactly when `−1/H` lies in the convex hull of the monomial phases, near-unit mass exactly when every integer ordinate relation has even coefficient sum, and odd relations cost mass and frequency [L/S]. Positivity of coefficients prices zeros; it never excludes them.
- **Well-foundedness.** Wolff towers defeat elimination without ZAL [L].
- **Positivity of sources.** Positive theta sources survive finite donor surgery moving a narrow cluster of critical zeros off the line, with long endpoint jets and positivity after every finite prime deletion [L].

### 1.5 The finite-layer world
Under ¬AAL there is an isolated top over an infinite remainder, `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})` with `T` a unique finite trigonometric polynomial, syndetic lag excursions with a coefficient-density floor at every base, and a positive-density set of primes with `c_B(log p)<−Kp^a` for every `K` and `a<Θ−½` [L]. The exact identities of ζ in this world [L]:
- Gaussian prime current at inverse-height damping: the discrepancy minus its Gamma field tends to `A(σ)−ξ′/ξ(σ)`; at a rightmost zero the raw current reads `−m_ρ/2`; a finite exceptional subtraction controls a whole high strip; the raw current tends to `−ζ′/ζ(s)` uniformly on an interior high strip and across dyadic windows; the head-conditioned rough Gaussian mean square is head mass × rough mass.
- Joint returns: every high dyadic window contains a height where any prescribed finite family of prime phases is approximated and `‖ζ′/ζ+head current‖²` lies below the rough `ℓ²`-mass plus any slack.
- Exponential damping (ELT): the raw current is pole-dominated and unbounded; the corrected current `𝒞` over the top Gaussian mode tends, at every speed `a(β−σ)>π/2`, to the finite wave `−Σ_top e^{πγ/4}e^{iγ(at+log(t/2))/2}`; its envelope `M=Σ_top e^{πγ/4}>0` is sharp and recurrent with bounded gaps; `𝒞` is unbounded; with one positive top ordinate `‖𝒞‖→∞` at every supercritical speed (unequal conjugate Gamma weights `e^{±πγ/4}`).
- Height: the FE reflects a height to itself, `N_t(s)ζ(s+it)−conj ζ(1−s̄+it)=O(t^{−¼})`; escaping translates bounded on a domain meeting `Re s>1` stay right of `½`.
None transports a zero in height, and the identities are mutually consistent: at damping `e^{−at}` the prime sum has length `X=e^{at/2}` at height `t≍log X`, the corrected current is the zero sum itself, and no mean-value theorem reaches the top mode `X^{β−σ}e^{−πt/4}` [D].

### 1.6 Exactness over ℤ lives on the torsion; breadth is proved to the VK height
The exact Frobenius of integer auxiliaries is the Adams operation `ψ_aF=F(u^a)`: the dilation `t↦at` on the prime orbit, the Galois action on torsion points, `ψ_qF=F` on the `(q−1)`-torsion; the norm amplifier forces vanishing on a closed point at every uniform order [L]. Integrality creates no zeros at returns (zero heights of integer auxiliaries are countable) [L]. Polynomial Stepanov syzygies of order `<r` have image exactly `J_q^r`, `J_q=(X_p^q−X_p)_p`; for `q≥2` the sharp minimum length is `p_min^{qr}`, attained only by the multiples of `(X_{p_min}^q−X_{p_min})^r`; every nonzero syzygy auxiliary has length `≥2^r`; their Euler jets on the torsion are binomial combinations of Euler moments [L]. The minimal auxiliary vanishing at the fixed points of all `Γ_n`, `n≤N`, has log length `ψ(N)`; RH ⇔ `ψ(N)≤N+C√N log²N`; the integer-norm one-off violates this for every `C` [L]. The exact Stepanov count over ℤ is Chebyshev's. A polynomial of constant modulus on the prime orbit is one unimodular monomial, and the polynomial self-maps preserving the orbit are translated Adams operations, exactly the Adams operations when the coefficients are integral [S]: the dilations `t↦mt` are the only exact Frobenius-like symmetries of the orbit. Approximate vanishing is capped: Rouché copies at returns cost `J≤e²r log N+log(1/δ)` [L].

Returns of the primes: transcendence bounds their depth (`t≥poly(1/δ)` for any two primes); bounded-height Diophantine information cannot exclude them past the Kronecker scale `y^{O(1/δ)}` (the rounded systems that defeat it are function fields, rank one, exact Frobenius) [L]; independent integer forms obey a collective rank-depth law and near relations below the rank floor span `≤r−1` dimensions and number `≤(2H+1)^{r−1}` [S]. Heavy subsets (omitting `≤1/1000` of the `p^{−1/2}`-mass) at precision `δ≤1/20` do not return while `log t≤(log y)^{3/2−ε}`; at every heavy return `√y≤K(y^{1/2−w(2t)}log t+log(2+t))` with `w` the VK width; a strip of depth `h` gives `log t≥c·y^{1/2−h}` [L]. Absolute large values of a nonnegative-weight phase sum force heavy returns at one of the dilated heights `mt`, `m≤Q` [S]. By reciprocity a heavy return at height `t` is a configuration of zeros near `t` imitating the pole [L]; return bounds are statements about the labels `log p`, shared by `ζ(s−h)`, and a route from them to ZAL that is uniform over a class containing `ζ(s−h)` refutes the return conjecture [L].

### 1.7 The window sign is one scalar flow; the critical curve adds one orthogonality
RH ⇔ `Ψ=½log H₁` locally bounded ⇔ `a*(ζ)=⊤` ⇔ `λ*(c)→0` [L]. At `R=c⁸/log N`: `R_c=R_PSD=R_polar=R_halfline≤R_prim=R_high=W`; every threshold `=⊤` ⇔ RH; the charged compactness passage is closed [L]. Under ¬RH the window threshold `W` is finite and strong compactness produces a unit half-line ground state at `W`; each ground state bounds `R_polar` by a reciprocal shift in its polar pairing; finite `R_polar=W` forces every ground state to be polar-orthogonal [L]. No finite or countable square-bounded family of holomorphic multipliers dominates the depleted kernel `4/(¼−z²)−12/(64−z²)` on the off-line strip [L].

### 1.8 The theta wall is ζ on the critical line
All ranks reduce to the adaptive head `M(b)=⌈|b|/2+B⌉`, whose leading term is `|ζ(½+ib)|²+O(|ζ(½+ib)||b|^{−½}+|b|^{−1})` [L]. The sign is automatic where `|ζ(½+ib)|` is large and is decided by second-order terms near the critical zeros.

### 1.9 The near-line wall is the dark range
Near-unit mollified moments need `log N≥log²T/(6K₀)`; an Euler mollifier reaching them uses every prime up to `≍log²T` [L]; conditional tail laws stop at the Kronecker scale [L]; past the height the Fejér mean value of the prime polynomial is a count of prime pairs at multiplicative distance `≲1/T`, of exact order `X²`, with the Hardy–Littlewood pair constant [L].

### 1.10 The surface of Spec ℤ: an adelic Green pairing off the diagonal; local locking cannot supply the diagonal
Off the diagonal Weil's kernel is the pole minus the Green functions of all places at the critical parameter [L]: at `∞`, `2πG_{1/2}(d)` on the degree geodesic of `ℍ³`, `d=|log(n/m)|`; at `p`, on a `p`-ladder `n=mp^k`, `log p((p−1)/√p)G^{T_p}_{1/2}(k)`, the tree Green function at the Ramanujan point, PD on every apartment; the archimedean compensation is spherical, `C_∞=(3/2)φ_{3/2}−2πG_{3/2}`, negative exactly below the plastic ratio. No twisted hyperbolic carrier with convergent Poincaré series at `½` carries the torsion; compact and (given a cusp expansion with nonzero Wronskian) finite-volume embeddings reproduce no Frobenius intersection [L]. Locked atomic dampings converge to Weil's kernel off the diagonal for every locking, but their diagonal is the torsion self-intersection (the different of `ℚ(ζ_n)` per unit degree): bounded and never PSD [L].

On smoothed packets `f=Σ_{n≤N}x_ng(·−log n)` the smooth `ℍ³` Green energy is `‖f‖²·selfEnergy(r)−LévyEnergy(f)+o(1)`; the scalar locking of pole − Green damping + torsion damping has a finite limit **exactly when the packet's discrete mass `‖g‖²Σx_n²` equals its `L²` mass `∫f²`**; below the atom spacing the limit is `Weil(f)+(c−2·gammaHardyPhaseRate 0)∫f²−‖g‖²Σx_n²·selfIntersection(n)`, so smoothing keeps the discriminant; one compact C² profile admits no radius with finite limits at one and two orders [S]. The separated regime is subcritical overlap: there complete positivity is already proved for the plateau and tilted-spline profiles, while the RH content sits at overlap `c→∞`, where packets overlap and no common locking exists [D]. On smoothed graphs RH ⇔ `c_B` is a counterterm-free pointwise limit of PSD kernels; neither smoothed channel alone is one [L]. The sign sits in the diagonal, and no local damping supplies it where RH lives.

### 1.11 The count on one ray per prime
A count law has a quadratic half (a nondegenerate Born rule, the FE) and a count half (damping) [L]. Over ℤ the quadratic half holds, RH ⇔ `Q` on integer probes is the Tate limit of an `ℕ`-count, and `Q` is not integer-valued; no integral kernel reproduces `Q` [L]. The count is needed only on one effective ray per prime: RH ⇔ every class `Γ_1+Γ_p` carries an `ℕ`-count along its ray with Tate limit `2c_B(0)+2c_B(log p)` ⇔ the prime planes are copositive; two primes suffice on the planes `⟨Γ_m,Γ_n⟩`, `m,n∈⟨p,q⟩` [L]. Arithmetic counts defined before the form exist in quantity (different quotients with `|disc|` elements, gluing quotient `ℤ/(1−M(N))`, Gaussian section heights, resultant rings, radial cyclotomic counts); none has Tate limit `δ_p(1,1)` [L].

### 1.12 Production, Farey, the nerve, the prime vertices and the orientation cover are the Mertens level
Producer rates equal the Mertens level; Farey discrepancy ⇔ RH; `M(N)=−χ̃` of the prime-star nerve; `Σ_p` prime-vertex indices `=1−M(N)`, indices unbounded below [L]. The orientation cover over ℤ (real points of `y²=disc F_n`, `1+μ(n)` per fibre) has centred count `M(N)`, weight `≥½` unconditionally and weight `½` ⇔ RH [L]. Over `𝔽_q[T]` the factor-trace cover has exactly `qⁿ` points [L].

### 1.13 The horizon has complete and sharp receivers
The modular horizon is the quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)` [L]. Seeds form a `*`-algebra; their horocycle responses have Mellin transforms `Λ_F·2s(2s−1)/ξ(2s)`: the group fixes the resonance positions, a seed enters only through `Λ_F(ρ/2)` [L]. One cuspidal cavity function of Hecke eigenforms sees every right resonance, and RH ⇔ its energy rings down at `y^{¾−ε}`; RH ⇔ every two-mode energy rings down at `y^{¾−ε}` [L]. One Hecke eigenform is blind exactly at halving pairs `ζ(ρ)=ζ(ρ/2)=0` and at the zeros of its Shimura integral [L]. The resonance Krein form at one resonance has infinite index of both signs; the reflection Krein form is PSD on the line and has exactly one negative square at each off-line zero: RH ⇔ every reflection Krein form PSD; the dual side has no sign [L]. Internal modular conjugation collapses to the centre; vacuum-fixing and half-sided modular realizations cannot carry `Q` [L]. Every horizon observable is on the width axis.

### 1.14 Hull
Haar-a.e., fair-coin-a.e. and order-two fibres extend zero-free to `Re s>½` with natural boundary `½`; the Liouville point extends iff RH [L].

### 1.15 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| Markov, Perron, sign-gauge balance past `e^{−3/4}`, `log ρ` | refuted; Beurling–Deny exactly on plastic windows | [L] |
| Size-only payment of primes | ends before half-width `21/40` | [L] |
| Floor tower as aperture producer | stays below `0.3621` | [L] |
| Weighted Gårding on the whole horizon; physical tearing at the collar | false on deep atoms; Schur ratio `4/13` | [L] |
| Universal holomorphic multipliers for the critical depleted kernel | excluded on the off-line strip | [L] |
| Uniform logarithmic Gamma reserve in coefficient norm; fixed theta heads; summable absolute pair majorants; compact cores; positive Laplace representations of the theta amplitude | resonant two-copy profiles; no margin; harmonic diagonal; geometric growth; excluded | [L/S] |
| Product certificates in Euler coordinates past `Re s=1` | cannot cross | [L] |
| Parabolic structure as selector of `t=0`; family-uniform finite-stratum laws | blind; RH-strength; the Dirichlet series is the selector | [L] |
| Asymptotic or local-below zero statistics as inputs to any level of the dial | cannot decide | [L] |
| FE, order one and reality as exclusion of a finite layer; positivity, Euler products, integrality, linear counting, continuation, reflection, positive Hecke and two-prime polynomials as AAL | `cosh` models; finite layers exist; annihilators price, never exclude | [L] |
| Nonclassical Beurling systems with an `L¹`, `L²` or no FE defect as fakes of ζ | none exist | [L] |
| One-sided bounds off a density-zero set of primes, at the very smooth degrees, at finitely many Frobenii, at one Frobenius, without attainment | unattained-top configurations pass; aliasing | [L/S] |
| Exact identities of the finite-layer world as a contradiction | consistent: the corrected current is the zero sum | [L/D] |
| Density statements on levels of a tower; elimination without well-foundedness | rank barrier; Wolff towers | [L] |
| Exact returns as a Frobenius; norm-majorant Rouché copies; integrality at returns | one fixed point; trivial separation bound; countable zero heights | [L] |
| Bounded-height Diophantine certificates against returns; return bounds as uniform routes to ZAL | Kronecker-scale breadth cap; uniform route refutes the return conjecture | [L] |
| Slow-return bounds on discs crossing `Re s=½`; whole-quadrant boundedness | power growth forced; impossible | [L] |
| Schur, `C*`, KMS, reflection positivity, internal modular conjugation, vacuum-fixing partners, Borchers inclusions as zero locators or carriers of `Q`; the resonance Krein form; dual-side signs | blind; central collapse; square-class collapse; no eigenvalues; infinite index; one-sided = two-sided | [L] |
| One Hecke eigenform as a complete receiver | halving-pair and Shimura blindness | [L] |
| Wave dynamics, flux, unitarity, Hecke, FE at genus two, first-level counts, integrality as universal damping; linear counts; Hecke at a second place; `Q` or an integral trace form as its own count | fakes carry all; degenerate; conservation only; not integer-valued | [L] |
| Narain remainder past `¾`; sharp sources at the RH rate | impossible; need Möbius × circle cancellation | [L] |
| Integer stencils independent of Möbius; exact Stepanov auxiliaries over ℤ | rate = Mertens level; count = Chebyshev | [L] |
| Fixed-point localization in cardinality; persistence | primes fixed with unbounded indices; `s`-independent | [L] |
| Renormalization as a source of sign; renormalized torsion under finite constraints | any form arises; both signs survive | [L] |
| Metrics on `ℙ¹_ℤ`, toric pairings, continuous Hecke kernels, finite-rank kernels, hyperbolic quotients with convergent Poincaré series, compact or finite-volume embeddings as carriers | excluded | [L] |
| Locked atomic dampings; separate positive channels; scalar locking on smoothed packets | discriminant diagonal, never PSD; divergence; converges only at mass balance and keeps the discriminant | [L/S] |
| Thermal averaging (primon gas) as a strip input; shrinking-mesh pure Euler approximants | Euler factors at real points `>1`; Euler abscissa escapes | [L] |
| Power moments as logarithmic depth majorization for the heat divisor | `(2,2)` against `(4,½,½)` | [L] |

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
| A56 | Explicit rung for the prime two-bump tests: `RHVerifiedThrough T` ⇒ `Re W(B±τ_{log p}B)≥0` for all `p≤P(T)` with explicit `P(T)` (unverified) | SRT, ACS, HF | window rungs; supports of the two-bump tests |

### Critical curve
| # | Task | Routes | Basis |
|---|---|---|---|
| A9 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | HF, SRT, AIP, ACS, SC | proved limits |
| A13 | Near-gcd charges and periods beyond `M₀(N)` (unverified) | AIP, HF | gcd-defect coercivity through `M₀(N)` |

### Sampling, exceptional coordinate, flow, near-line, continuation, orbit
| # | Task | Routes | Basis |
|---|---|---|---|
| A16 | Numerical `r,m,q` for `a≤1` [N] | RW | Galerkin |
| A18 | Twisted second moments past `21/50`: to `½`, Conrey `4/7` [C] | WD, census | raises rate `2θ` |
| A19 | Heat horizon toward its method floor | ZCG, AES | profile margin |
| A20 | Jensen rung toward the saddle scale (unverified) | LA, FFP | saddle identity |
| A21 | Census items; logarithmic two-point Chowla [C]; runs past five | MC, ACS, census | classical |
| A24 | Certified scans of `S_S`; brackets for `S*(a,b)` | TH | column calculus |
| A37 | Resonator mean of `\|ζ\|²` with resonators growing below the Kronecker scale (unverified) | BAG, ZCG, PTT | fixed-resonator limit, arithmetic mean values |
| A47 | The one-quartet world in constants: explicit supercritical speed, envelope window length `L` and height thresholds of the exceptional current for one top quartet `Θ±iγ`, the coefficient-density floor and the tower windows at base `π/γ` (unverified) | ZCG, WL, IWT, ELT | `not_asymptoticAbscissaLaw_has_top_ordinate_dichotomy`, `..._sharp_recurrent_envelope` [L] |
| A50 | Finite-stratum laws on other positive deformation families (cosine shifts `A_h`, shifted Jensen families) imply RH, as for the heat family (unverified) | ZCG, PTR, LA | `TheFiniteStratumLawOnTheHeatFamilyIsRH` [L] |
| A53 | Integrate the unwired modules: the CDGeo umbrella into `MainTheorems`; the HAT smoothing modules (Green damping on smooth probes, smoothing retains the discriminant, mass obstruction); the SOSZ sampling modules (almost all primes and the Stepanov boundary, configurations at almost all primes, very smooth degrees, positive cosine sums off a small arc); the APD phase-hull modules; the ALST unit-orbit modules | CDGeo, HAT, SOSZ, APD, ALST | proved source [S] |
| A58 | Effective gap iteration at the primes: explicit constants from a one-sided or two-sided bound with constant `K` to an explicit width after each step (unverified) | ACS, SOSZ, CDGeo | first strip `5/8`, Landau step, two-sided width step [L/S] |
| A59 | Short-interval primes in a fixed residue class, `π(x+x^θ;q,a)>π(x;q,a)` for some `θ<1` and all large `x`, from the zero-density estimates and zero-free region of `L(s,χ)` [C]; then `PowGaps` holds for the primes `≡a (mod q)` and `riemannHypothesis_iff_primeWindow_le_of_powGaps` makes the residue-class Stepanov bound an RH criterion, not only an AAL producer | ACS, SRT, WL | `powGaps_primes` from the 7/12 short-interval theorem [L] |
| A62 | Rank-depth counting of near relations for `k≍(log y)^A` prime logarithms with explicit floors, and the resulting count of `δ`-returns in `[0,T]` at that rank (unverified) | BAG, PTT, TTPO, CDGeo | `nearRelationBox_card_le`, explicit Fel'dman bound [S/L] |
| A63 | Upgrade the classical saving of the Stepanov bound to the VK saving, `\|P(n)−A(n)\|≤C√n·exp(−c(log n)^{3/5}(log log n)^{−1/5})` | ACS, SOSZ | VK zero-free region in RHTower [L]; `TheStepanovBoundHasTheClassicalSaving` [L] |

### Theta, horizon, counts, production, descent, topology, FE rigidity
| # | Task | Routes | Basis |
|---|---|---|---|
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | PM, BHR | order `N(Λ)≍Λ` proved |
| A28 | Reciprocal-quadric traces = vanishing-cycle Frobenius traces (unverified) | ACS | exact projective quadric counts |
| A30 | Best stencil exponent under RH in `[¼,½]` (unverified) | WL, MC | quarter rate, half scale, three-quarter floor |
| A33 | Fourier coefficients of the cubic residue [C] | MC, MMD | nonzero residue, continued Fourier modes |
| A41 | Count law for every curve over `𝔽_q` (Bombieri–Stepanov), first case plane quartics [C] | ACS, PM, CTH | crude-bound self-improvement on thick sets [L] |
| A42 | Uniform Gamma-weighted transport of the fixed-head theta asymptotic to `M=M(b)≈\|b\|/2` with effective error (unverified) | TH | fixed-`M` asymptotic [L]; adaptive partial sum `=ζ(½+ib)+O(\|b\|^{−½})` [L] |
| A46 | Local singular indices of prime vertices beyond the cubic cutoff `N>p³` (unverified) | MC, RIAC | discrete-exit computation [L] |
| A54 | Instantiate the cusp expansion with nonzero Wronskian for the `L²` resolvent of `Δ−¾` on Bianchi quotients, closing the finite-volume carrier exclusion | ACS, HF, HAT | `not_eq_frobenius_of_finiteVolume` takes `CuspExpansion` as input [L] |
| A55 | FE rigidity for generalized (continuous) Beurling systems with `L¹` or `L²` defect (unverified) | BAG, ZCG, APD | Poisson rigidity of self-dual measures with a gap [L]; the tent machinery of EFT [L]; exact completed-FE rigidity for countable systems [L] |

## 2.2 Open mathematical obstacles

### The common minimal face
| # | Problem | Strength | Routes |
|---|---|---|---|
| B130 | **The arithmetic Stepanov bound at the primes**: `P(p)≤A(p)+K` for every prime (⇔ `c_B(log p)≥−K` ⇔ `Re W(B+τ_{log p}B)` bounded below), or the sign-free two-sided form `\|c_B(log p)\|≤K`; on any power-saving gap set, or off a power-thin exceptional set; any growth `Kp^a`, `a<½`, is a zero-free strip. Known: `√p·exp(−√(log p)/10)` | RH (≥qRH for `a<½`) | ACS, SRT, WL, HF, RW, ALST, SOSZ, CDGeo |

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
| B13 | Finitely many off-line zeros of ζ ⇒ none (bottom of the dial); its heat-family extension is RH | sub | whole programme |
| B14 | Any interior width value (window negativity exponent `<½`; horocycle, Farey, pulse, Narain, seed, cavity, spline-orbit or prime-degree growth exponent past the trivial one) | ≥qRH | width axis |
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
| B101 | Polar payment at every ratio on growing windows | RH | HF, AIP, SRT |
| B102 | Sign of the adaptive theta head at every degree; leading term `\|ζ(½+ib)\|²`, decided near the critical zeros | RH (all ranks) | TH |
| B104 | Polar payment at every ratio below `W`, equivalently `R_polar=W`; at finite `W`, whether a critical half-line ground state can be polar-orthogonal (§2.4) | method | HF, SRT, AIP, ACS, SC |
| B123 | Correlated arithmetic pairings dominating the depleted kernel where every universal holomorphic multiplier fails | method | HF |
| B124 | Useful finite initial depth budgets of the ξ heat divisor (`S_q<∞` for some `q`, or a finite logarithmic budget) and extinction arbitrarily near `t=0` | ≥qRH to RH | ZCG, LA, WD |

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
| B94 | Identification of the cubic Gauss coefficients with an automorphic theta expansion; transfer to rational-integer Möbius | past VK at least | MC, MMD |
| B96 | Conditional law of the Euler tail at the Kronecker scale; lower bounds for exact tail events | sub | BAG, TH, WD, TAPO |
| B97 | Constant-precision first return of heavy subsets past the VK rung, `log R(y,δ)≥(log y)^A` for every `A`, or `≥y^c`, by an argument of growing height (proved: `(log y)^{3/2−ε}`; the top rung is a Littlewood-type bound for `ζ(1+it)`) | sub (past VK) | PTT, TAPO, TTPO, BAG, CDGeo |
| B98 | Positive-generator integer-norm systems: which count distance forbids a finite top layer | method | RAC, SPAL, APD |
| B100 | A saving for `t log n` on moving families of blocks past Vinogradov's degree | sub | PTT, TAPO |
| B106 | A natural self-map or action on the orientation cover over ℤ (or on the prime complex) with bounded local indices whose Lefschetz number is the centred count, localizing `M(N)` to `O(N^{½+ε})` | RH (≥qRH at `θ<1`) | MC, HF, ESG, HHAC, RIAC, HAT |
| B110 | **Thick crude count**: `primeDeviation(X)=O_a(X^{½+a})` along a thick set of geometric scales of one base, for every `a>0` | AAL (with ZAL at `a=0`: RH) | WL, ZCG, ACS, IWT |
| B113 | Möbius × quarter-disc remainder `Σ_{d≤X}μ(d)E(X/d)=O(X^{½+ε})` | beyond RH | PM (sharp shells) |
| B121 | Freezing control beyond the precision cap: integral at sign returns, or signed | sub | BAG, ACS, PTT, IWT, ALST |
| B126 | A one-sided crude bound of the spline traces on one sampling set of primes (a residue class, the primes off a relative-density-zero set, or `p^aq^b`) | AAL (with ZAL: RH; on a power-saving gap set: RH) | ACS, SRT, ZCG, BAG, IWT |
| B127 | Positive Lebesgue measure (or positive dimension) of the bases with recurrent sub-top Weil-lag readings, at every rate | AAL (with ZAL: RH) | WL, ZCG, IWT |
| B136 | **Sample boundary**: for every set `D` of degrees without power-saving gaps, is there a tempered configuration without real zeros, with unattained top, passing a one-sided bound on `D`? Equivalently: are power-saving gaps necessary for a one-sided bound on `D` to decide purity (§2.5) | method | ACS, SRT, WL, HF, ZCG, IWT, SOSZ |
| B137 | **Collective counting**: the number of `δ`-returns of the primes `≤y` (and of heavy subsets) in `[0,T]` with an error uniform in `π(y)`; first rung `k≍(log y)^A` logarithms | sub | PTT, TTPO, CDGeo, BAG |

### Γ — selection, reflection and transport
| # | Problem | Strength | Routes |
|---|---|---|---|
| B68 | Independent `D_s≥0`, nonnegative Krein flux, integer-probe sign, all-zero dispersion bound, or PSD of every reflection Krein form of the cavity | RH | PM |
| B69 | Positive physical or graph carrier | producer | PM, W1C, PTR |
| B70 | Lower bound for `V_p` from the carrier | sub | PM |
| B71 | Universal decay `e^{−t/4}`; horocycle, Farey, Narain or one-cavity-energy rate `y^{¾−ε}` | RH | PM, BHR, CTH, AHMH |
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
| B83 | AAL | sub | BAG, JAS, SC, ZCG, WL, IWT, ELT |
| B85 | Arithmetic global trace on a family containing ζ | RH | ACS |
| B86 | Mixed Young projections at unbounded rank | RH | ACS |
| B87 | A nonnegative count on the rays `Γ_1+Γ_p`, defined without `Q`, with Tate limit `2c_B(0)+2c_B(log p)` | RH | ACS, HF, PM, RW, AE, CTH, SOSZ |
| B88 | A counterterm-free PSD damping of `c_B` on `log ℕ₊` on smoothed graphs (⇔ RH); it must couple the prime and archimedean-plus-pole channels non-locally, because scalar locking of the local dampings converges only at mass balance | RH | AE, HHAC, SOSZ, RIAC, HAT, HF |
| B89 | A bounded aligned return at each right zero on a right disc | sub | BAG, ZCG |
| B92 | Arithmetic source of a rotated relation with coefficients of the size of `Q` | RH | ZCG, RAC |
| B93 | A contradiction using growth or arithmetic of `Q` beyond the extremal law | RH | ZCG, RAC |
| B111 | **`ZAL ⇒ RH`** (existential linear AAL): `Θ∞=½ ⇒ Θ=½` | sub | BAG, ZCG, IWT, WL |
| B112 | A mechanism converting the FE (which reflects a height to itself) into vertical transport of zeros, using the Euler product and coupling both scales | sub | BAG, ZCG, EFT |
| B114 | A realization of the partner involution outside the central, vacuum-fixing and Borchers classes | producer | PM, CTH |
| B116 | Linear AAL at one fixed slope `C≥1` (⇔ thick relative crude count at exponent `½+C(Θ∞−½)+ε`) | sub | ZCG, IWT, WL |
| B117 | A confined companion of the modular horizon (§2.7) | producer | PM, BHR, ASH, CTH, AHMH |
| B125 | Halving pairs: no zero `ρ` with `ζ(ρ/2)=0`, and nonvanishing of one Shimura integral at every `ρ/2` | indep. | PM, AHMH |
| B128 | Replication in the finite-layer world: the exact identities of ζ under ¬AAL force a second zero at the same depth above every height | sub | BAG, ZCG, EFT, ELT |
| B131 | **Deuring–Heilbronn law of the top layer**: does an isolated top layer of ζ push the remainder toward the line, `Θ∞−½≤f(β−Θ₂,γ)` in graded form, `¬AAL ⇒` finitely many off-line zeros in extreme form (§3) | sub | BAG, ZCG, IWT, EFT, ELT |
| B133 | An adelic carrier: an automorphic Green function at the critical parameter on a quotient of `ℍ³×Π'_pT_p` reproducing Weil's full kernel on the degree configuration, diagonal included (§2.8) | producer | ACS, HF, HAT, SOSZ |
| B134 | An independent upper bound `‖𝒞(σ,a,t)‖=o(top mode)` along one sequence of heights at one supercritical speed; for a single top quartet this excludes the one-quartet world | sub | BAG, ZCG, ELT |
| B135 | A coupled (non-scalar) locking of the `ℍ³` and torsion channels with a finite limit on overlapping smoothed packets, and its defect against Weil's form | method | ACS, HF, PM, HAT, SOSZ, CTH |
| — | ZAL | ≥qRH | whole programme |

## 2.3 Frankenstein routes

**No assembly closes RH.** Every assembly below has at least one open input of RH, AAL or ≥qRH strength, or names one. The assemblies whose output is RH (F1, F2, F3, F15, F18, F19) each need an input that the corpus cannot produce. Their value is that they collapse independent problems into one, or fix what a missing input must contain.

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F1 | **Split skeleton.** A sampling-set AAL producer (a one-sided crude bound at one residue class, off a density-zero set, or at `p^aq^b`; positive-measure lag recurrence; uniform tensor moments at a class) with any ZAL receiver (inner-field decay, subtracted lag, `Λ_Xlog X→0`, eventual Hadamard, high-collision counts) | RH [L] | one sampling-set bound (B126) or B127, and ZAL | the two inputs are prime-side and zero-side; configuration arguments cannot drop ZAL for density-zero exceptions (Γ178); on a power-dense sample F1 becomes F2 with no ZAL |
| F2 | **One inequality per prime.** SOSZ prime degrees, the prime two-bump tests, the Stepanov bound as a prime count, the count door on one ray per prime, the window form on windows of length `log p+O(1)`, the two-sided sign-free form | the Σ, Π and count readings of RH are one number per prime, the smoothed PNT error at the primes [L/S] | B130 | ACS, SRT, WL, HF, PM count branch, ALST and CDGeo have one target; the classical saving `√p·e^{−√(log p)/10}` is its known level |
| F3 | **Deligne skeleton over ℤ.** Stepanov side (one-sided bound), absence of real zeros (Bombieri's twist), base change (`n^k`, trace zeta `Σ_ze_zζ(s−kz)`), tensor powers (positivity free), Rankin square (abscissa `2maxRe ρ`), the gap iteration (Weil's self-improvement) | every step of Deligne's purity proof has a Lean ℤ-counterpart except the a priori bound on the abscissae of `M^{⊗2k}` uniform in `k` [L] | the uniform weight bound (RH) | names the missing piece exactly: the role of the finite-dimensional cohomology of the curve (§2.9) |
| F4 | **Critical curve.** Threshold identities, charged compactness, half-line ground states, polar orthogonality, multiplier no-go | `R_c=R_polar=R_halfline≤W`; ¬RH ⇒ a ground state at finite `W`, polar-orthogonal if `R_polar=W` [L] | B104 | the critical curve carries no sub-RH content beyond one inequality and one orthogonality (§2.4) |
| F5 | **Horizon.** Seeds, position rigidity, every-seed ringdown, odd cavity, Maass and Hecke pairs, Baire, two-mode Zagier dichotomy, resonance and reflection Krein forms, dual side, standard-form trichotomy, Narain | physics reduces to one rate of one cavity energy or to one reflection sign [L] | B71 or B68 | waves, Hecke, KMS, modular conjugation, half-sided inclusions and dual-side signs are closed as sources |
| F6 | **The diagonal.** Adelic Green formula (`ℍ³` and trees), spherical compensation, locked atomic dampings (discriminant diagonal), atomic genus `N log N`, smooth archimedean self-energy, smoothed locking at mass balance, mass obstruction on overlapping packets | off the diagonal Weil's form is an adelic Green pairing; local scalar locking reproduces it only on separated packets, minus the discriminant, and fails where RH lives [L/S] | B133, then B88 | closes every local (Arakelov-type) presentation of the diagonal; points to a global carrier on which both channels see the configuration as points (§2.8) |
| F7 | **FE as the only selector.** Firewall (one-offs across the line), complete FE rigidity, Poisson rigidity, Dirichlet selector of the heat family, finite surgery of positive sources, annihilator phase geometry | every model with a finite layer lacks an FE; every system with an integrable or vanishing FE defect is ζ; positivity of coefficients prices zeros and never excludes them [L/S] | B112 | the B13/AAL input must be an exact identity of ζ that uses the FE together with the Euler product |
| F8 | **Finite-layer world.** Rigid ¬AAL, finite oscillation, coefficient-density floor, prime-current passage, top multiplicity, rough variance, joint prime-phase returns, exceptional current at exponential damping with sharp envelope, one-quartet divergence, Bohr duality at sampling sets | a fully specified world in which a contradiction must be found; its exact identities are mutually consistent [L] | an estimate from outside the explicit formula: B134, B128, B131 | the table below lists what the world must satisfy |
| F9 | **Exactness and Diophantine closure.** Adams Frobenius on the torsion, norm amplifier, integrality at returns, closed-point Stepanov count, sharp cost of polynomial syzygies, Rouché precision cap, explicit Baker bounds, return–form duality, breadth cap, unit-orbit rigidity | exact methods over ℤ reproduce Chebyshev; approximate methods stop at the trivial separation bound; Diophantine methods of bounded height stop at the Kronecker scale [L/S] | B97, B121 | closes these as producers of the crude step; what survives is growing-height or signed information |
| F10 | **Mertens in eight geometries.** Franel–Landau, Farey law, nerve, core, barcode, prime-vertex indices, gluing quotient `ℤ/(1−M(N))`, orientation cover | one exponent; the cover's weight is `≥½` unconditionally, `½` ⇔ RH [L] | B106 | topological, dynamical and discriminant tools act on the Mertens level |
| F11 | **Three sampling axes.** Prime degrees (sampling weights), bases of towers (metric recurrence), levels of towers (thick sets) | AAL from a one-sided bound on any of the three; on the prime axis power-saving gaps upgrade AAL to RH [L/S] | B126, B127, B110 | three formulations of one AAL input; the prime axis has a sharp RH/AAL boundary (B136) |
| F12 | **Heat divisor.** Initial divisor budgets, elapsed-depth comparison through collisions, crowding dissipation, sharp coefficient `2`, heat finite-stratum law, Dirichlet selector | finite budgets give `N(t)(2t)^q≤2S_q` and `t·N(t)→0` [L] | B124, B24 | the heat route needs one finite initial budget (≥qRH) plus an input that sees the Dirichlet series |
| F13 | **Theta wall.** Column calculus, carrier horizon, Ξ-current lift, adaptive head, Gamma reserve, partial sum `=ζ(½+ib)` | all ranks reduce to `\|ζ(½+ib)\|²` plus second-order terms near the zeros [L] | A42, B102 | merges TH with the size of ζ on the line |
| F14 | **Dark range.** Savings, precision law, heavy-return dictionary, almost-every-height cancellation, collision counts of order `X²`, precision cap, depth law, breadth cap, VK breadth of heavy subsets, strip ⇒ breadth, rank depth | the short-sum barrier is one first-return statement; its breadth is proved to the VK height and is Littlewood-strength at its top rung [L/S] | B97, B137, B121 | gap: `(log y)^{3/2}` against `y^c` |
| F15 | **Count skeleton.** Hecke isometry of `Q`, Tate principle, point-count defect on curves, half-products, adelic Green fibres, critical weight, ray counts, `Q` not integer-valued, arithmetic counts defined before the form | every ingredient of the curve count proof except a count over ℤ, needed on one ray per prime [L] | B87, B88 | output RH; names the missing object exactly |
| F16 | **Two Frobenii.** Kronecker density of `ℤlog p+ℤlog q`, continuity of the spline trace, two-sided Hasse–Weil on the rank-two monoid planes | RH from the lags of two primes, no attainment [L] | the bound on those lags (RH) | the minimal degree set is a rank-two lattice of lags, not the primes |
| F17 | **Siegel calibration.** Dirichlet `L` from both sides: the upper side at the primes is GRH including Siegel zeros, the lower side is blind exactly to real zeros; ζ has none | AAL and Siegel zeros are both masked layers; the Stepanov side's only blind spot is absent for ζ [L] | none (calibration) | an exceptional-zero theory for ζ can borrow from Deuring–Heilbronn (§3) |
| F18 | **Sign-free skeleton.** Two-sided gap iteration (decision), absolute large values force heavy returns at dilated heights, proportional saving ⇔ no early heavy return, VK breadth of heavy subsets, strip ⇒ breadth, Turán on thick sets, integrality at sign returns | RH from a two-sided crude bound at the primes without any sign or spectral input; every other link of a positivity-free proof is present or named [L/S] | the breadth law (B97/B137) and the transfer from short prime polynomials to the long smoothed count (B46, Π80) | the positivity-free route has exactly two missing links (§2.6) |
| F19 | **Exceptional-set skeleton.** Stepanov bound off a power-thin or short-window-sparse exceptional set ⇔ RH; Huxley gaps; exceptional-set estimates from zero density | RH is a statement that tolerates `O(X^{1−δ})` exceptional primes, the regime in which zero-density and large-sieve methods operate [S/D] | B130 off an exceptional set | moves the target into the exceptional-set regime; the exceptions cannot be enlarged to density zero (Γ178) |

**Closest to the open core: F2, F3, F18, F1.** F2 makes the Σ∩Π core one inequality per prime. F3 shows that over ℤ the whole of Deligne's argument is present except the uniformity that cohomology supplies over a curve. F18 shows that a positivity-free proof needs exactly two inputs. F1 is the only assembly with two independent inputs of different kind, and Γ178 shows that one of them (ZAL) cannot be traded for density.

### The finite-layer world: what a contradiction search may assume (F8)
| In the world ¬AAL | Evidence |
|---|---|
| Isolated top `Θ=β`, attained; rest left of `Θ₂<Θ` above the layer's heights; bottom layer reflected at the same heights | [L] |
| `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})`, `T` unique, sign changes at bounded log gap | [L] |
| `Θ∞<Θ`: `ψ(x)−x` is `O(x^{Θ∞+ε})` after removing finitely many exponential terms, and not before | [L] |
| Two-prime dilation annihilation of `ψ`; a positive annihilator of the top whose inverse oscillates at every exponent `<Θ` | [L] |
| At every base, syndetic lag excursions with a coefficient-density floor; recurrent sub-top bases have dimension 0 | [L] |
| At the primes, `c_B(log p)<−Kp^a` on a set of positive relative density for every `K`, `a<Θ−½`; at every sampling set the same | [L] |
| Polar ground energy `≤−c′e^{2(Θ−½)B}/B³`; lag excursions of positive lower Abel density | [L] |
| `Λ`-moments: diagonal `→0`, long-shift correlation `→m²` | [L] |
| The raw Gaussian prime current at the rightmost zero reads `−m_ρ/2`; on a high interior strip it passes to `−ζ′/ζ` at inverse-height damping and across dyadic windows; head-conditioned rough variance is the diagonal | [L] |
| Every high dyadic window contains heights with prescribed finite prime phases and the continued rough current at its variance | [L] |
| At exponential damping and supercritical speed, `𝒞`/top mode `→−Σ_top e^{πγ/4}e^{iγ(at+log(t/2))/2}`; envelope `M` sharp, recurrent; `𝒞` unbounded; one positive top ordinate ⇒ `‖𝒞‖→∞` | [L] |
| The FE reflects every height to itself; escaping bounded translates stay right of `½` | [L] |
| Every return at a top zero tail-bad; transport events rare; near-full tail events abundant | [L] |
| The layer is not a rational relocation of critical zeros with positive coefficients; positive theta sources can carry it after finite surgery | [L] |

No contradiction comes from exact identities alone (they are consistent), from positivity, Euler products, integrality, counting or positive annihilators alone, from the FE with order one and reality, from a property shared by the heat family, or from statistics at one scale [L].

## Validation tests for 2.4, 2.5 and 3

| Test | Requirement |
|---|---|
| T1 | Implied by RH and not implying quasi-RH (or a method question implied by nothing about ζ's zeros) |
| T2 | Answered by proving or refuting a stated inequality, identity or implication |
| T3 | A named consequence can be written down for either answer |
| T4 | Not decided by a finite rung |
| T5 | False on a corpus fake, or calibrated on the fakes |
| T6 | Names an input not refuted in Lean |
| T7 | Moves a wall; not a shape already answered |
| T8 | Tractable: not a named long-standing problem in disguise (RH, quasi-RH, ZAL, AAL, B13, Lindelöf, pair correlation, Hardy–Littlewood, Chowla, past VK, Landau–Siegel, excluding a single off-line zero); its first step uses corpus objects and has one named obstacle |

Every statement below AAL that constrains the zeros of ζ contains B13 or an exceptional-zero problem of Landau–Siegel type, and every crude step on thick or sampling sets contains AAL [L/D]. The questions of 2.4, 2.5 and 3 are therefore questions about mechanisms or about implications between zero laws, not zero laws for ζ.

## 2.4 Breakthrough question below RH and quasi-RH: can the pole channel see ¬RH before the window does?

**Question (B104).** *At a finite window threshold, can a critical half-line ground state be orthogonal to the polar source?* Precisely: suppose `W=⨅_A windowThreshold(A)` is finite (equivalently ¬RH). Strong compactness produces a unit half-line ground state `F_*` at `W` of the Gamma-truncated charged critical form [L]. Is `∫F_*·polarSource≠0` for every such ground state?

**What is proved [L].** `R_c=R_PSD=R_polar=R_halfline≤R_prim=R_high=W`; every threshold `=⊤` ⇔ RH; `R_polar=W` ⇔ window-level polar payment at every `R<W` ⇔ strict positivity of the charged half-line form at every `R<W`; every ground state bounds `R_polar` by an explicit reciprocal shift in its polar pairing; finite `R_polar=W` forces every ground state to be polar-orthogonal; RH ∨ a ground state at finite `W`. Smooth compact solutions of `(W−μ)F=κP` vanish when `P` solves a constant-coefficient ODE, so extremizers sit outside smooth compact tests (`CapacitiesAndConstrainedGroundStatesAreSingularAtTheEdge`); no universal holomorphic multiplier dominates the depleted kernel.

**What either answer gives.**
| Answer | Effect |
|---|---|
| No ground state at finite `W` is polar-orthogonal | ¬RH ⇒ `R_polar<W` strictly. The whole-space critical threshold equals the window threshold only under RH: the pole channel is an independent detector that fires before the window. HF, SRT, AIP, ACS (atomic) and SC (critical branches) acquire a criterion of their own — polar payment at every ratio below the window threshold — distinct from the window sign (B1) |
| Some configuration of the ¬RH world admits a polar-orthogonal ground state | polar payment carries nothing beyond the window at that threshold: the critical branches of HF, SRT, AIP, ACS and SC merge into RW's window route, and the S1 block reduces to B1 |

**Why this question.** It is the last structural fork of the largest Σ block (S1). It is a statement about a variational problem in the ¬RH world, implied vacuously by RH and implying nothing about ζ's zeros. Its first step is the Euler–Lagrange equation of the charged half-line form with the polar source as Lagrange constraint: an orthogonal ground state is simultaneously a ground state of the uncharged form, and the corpus's edge-singularity rigidity (extremizers are not smooth compact; constrained ground states are singular at the edge) says where such coincidences can occur. One named obstacle: the polar pairing of a ground state must be identified with a residue (the pole coefficient of the ground state's Mellin transform) whose vanishing is a Jensen-type exceptional condition.

**Tests.** T1: method, vacuous under RH. T2: an implication. T3: the table. T4: no finite rung. T5: calibrated on fixed-ratio countermodels (tempered lattice-plus-one-pair configurations, `TM:ZeroSideStratum`) where thresholds are finite. T6: only universal multipliers are refuted. T7: moves Σ129, Σ135, Σ139. T8: not a named problem.

**Limit.** It decides the shape of the critical curve, not its sign: under either answer RH remains B1 or B101.

### Alternatives
| Question | Why it matters | T8 | Limit |
|---|---|---|---|
| Sample boundary (B136) | how much of the prime side RH needs | passes | §2.5 |
| Coupled locking at overlapping packets (B135) | an Arakelov presentation where RH lives | passes | bookkeeping; no sign |
| Residue-class Stepanov bound as an RH criterion (A59) | a criterion with one residue class of primes | just work | criterion only |
| Halving pairs (B125) | one Hecke eigenform as a complete receiver | excludes a configuration of zeros | adds a receiver only |
| Continuous FE rigidity (A55) | closes generalized Beurling fakes | just work | classification only |

## 2.5 Breakthrough question below AAL: where exactly does ZAL live on the prime side?

**Question (B136).** *Are power-saving gaps necessary?* For a set `D` of degrees, call `D` **decisive** if every tempered zero configuration without real zeros that satisfies a one-sided bound `2Re S(log d)≥−K` for all `d∈D` is pure, with no assumption on attainment of its top. Is `D` decisive if and only if it has power-saving gaps up to a short-window-sparse exceptional set?

**What is proved.**
| Degree set | Decisive | Evidence |
|---|---|---|
| power-saving gap sets; primes off `O(X^α)` or short-window-sparse exceptions (`7/12<θ<1`) | yes | [L]; [S] |
| two-prime difference lags (dense in ℝ) | yes (continuity) | [L] |
| primes off a relative-density-zero set | no: periodic harmonic clusters with holes `‖B_k log p−½‖<δ_k/2` | [S] |
| very smooth degrees (`x^{o(1)}` elements; every prime eventually a factor) | no: simultaneous Dirichlet returns of `log j`, `j≤U_{k+1}^{1/4}` | [S] |
| degrees of finitely many primes; one Frobenius | no; aliasing | [L] |
| every sampling set, attained top | yes (AAL for ζ) | [L] |

**The content.** On the prime side the two halves of RH separate into two sizes of sets of primes: AAL is a one-sided bound on any sampling set (density one, a residue class), RH a one-sided bound on a set that keeps a prime in every window `[x,x+x^θ]`. The countermodels all place the negative values of an unattained-top configuration in multiplicative holes, sparse in density but resonant with the heights of the configuration; the gap method closes exactly the holes of size `x^θ`. B136 asks whether every non-power-dense set has such holes in sufficient supply, i.e., whether "power-saving gaps" is the exact prime-side shape of ZAL.

**What either answer gives.**
| Answer | Effect |
|---|---|
| Yes | a sharp theorem: decisive ⇔ power-saving gaps (mod short-window-sparse exceptions). For ζ: RH ⇔ the Stepanov bound on any power-dense set of primes, AAL ⇐ the bound on any sampling set, and the difference between the halves is the covering of short windows; every AAL producer on the prime side is exactly as strong as the density of its sample, and no thinner sample can replace ZAL |
| No | a sample without power-saving gaps that decides purity: a thinner set of primes carries RH, and the gap method is not the mechanism; the new mechanism (arithmetic, not metric) becomes a tool for every sampling route |

**Why this question.** It is a method question about configurations, implied by nothing about ζ. It acts on ACS, SRT, WL, HF (through one Weil test per prime), ZCG, IWT and every AAL producer on the prime side. First step: given `D` without power-saving gaps, choose scales `x_k` with `D∩[x_k,x_k+x_k^{θ_k}]=∅`, `θ_k→1`, and build a periodic-cluster tower whose level `k` is resonant on `D` near `x_k` (the very-smooth and periodic-hole constructions are the two templates). One named obstacle: when the gaps of `D` are not multiplicatively periodic, the levels' heights must be chosen by simultaneous Dirichlet approximation on all of `D` within the window, and their weights must also take over from the level below (the takeover inequality `eight_le_smoothWt_mul_exp`).

**Tests.** T1: method. T2: an equivalence. T3: the table. T4: no finite rung. T5: calibrated on the five rows above. T6: necessity is not refuted. T7: moves Σ138, Γ164, Γ178, Γ179, B126. T8: not a named problem.

**Limit.** It decides how much of the prime side RH requires, not whether the bound holds.

### Alternatives
| Question | Why it matters | T8 | Limit |
|---|---|---|---|
| Independent current bound / one-quartet world (B134) | excludes the minimal finite-layer world | fails: contains excluding a single off-line quartet | — |
| Replication in the finite-layer world (B128) | the direct AAL step | fails: contains AAL | — |
| Sampling-set bound, metric recurrence (B126, B127) | AAL | fail: contain AAL | — |
| Polygon law of the exceptional wave (whether the top weights allow the wave to approach 0) | refines Γ176 to layers with several ordinates | passes (just work) | identity only |
| The one-quartet world in constants (A47) | explicit constants for the smallest layer | passes (just work) | constants only |

## 2.6 If positivity, Weil positivity and spectral methods are excluded

"Spectral" is read as spectral theory of operators in every form: eigenvalues, spectral decompositions, Hilbert–Pólya realizations, trace formulas, spectral gaps, Lax–Phillips semigroups, transfer-operator spectra, Maass and Eisenstein spectral theory, standard forms. "Positivity" includes nonnegativity of counts, of Dirichlet coefficients (Landau's theorem), of Fejér and sinc kernels, Hodge index and Tate limits. Kept: Fourier analysis, mean values used as bounds, exponential sums, absolute convergence, analytic continuation, power sums, Vandermonde and Turán, Dirichlet polynomials, integrality, Diophantine approximation and transcendence, recurrence, almost periodicity, Jensen and Rouché.

**What survives.**
- **The decision step.** RH ⇔ `|c_B(log p)|≤K` at every prime; width `≤σ` ⇔ `|c_B(log p)|≤Kp^σ`; on every power-saving gap set; by absolute convergence, continuation and the Laplace rate theorem [S]. This is the curve proof's elimination over ℤ with no sign.
- **Elimination at infinite rank.** Turán–Vandermonde at the exceptional rank on thick sets of levels; Turán on thick sets with an error term [L].
- **Breadth.** Heavy subsets do not return before `log t=(log y)^{3/2−ε}`; at every heavy return `√y≤K(y^{1/2−w(2t)}log t+log(2+t))`; absolute large values force heavy returns at a dilated height; collective rank depth bounds the number of near relations [L/S].
- **Capped producers.** Integrality reaches Chebyshev and acts exactly only on the torsion; phase-freezing Rouché copies reach the trivial separation bound; exponential sums reach VK; transcendence bounds depth, and bounded-height information cannot bound breadth past the Kronecker scale [L].
- **What falls.** All of Σ; every one-sided receiver at the primes (Landau); the count door; the critical curve; the horizon receivers; the index routes; FE rigidity (its proof uses the sinc-squared weight).

**The question.** *Does a constant-precision breadth law for the primes transfer to a two-sided crude bound at the prime degrees?* Two links are missing, and F18 shows they are the only ones:
1. **Breadth (B97/B137).** For fixed `δ`, no heavy subset of the primes `≤y` returns to precision `δ` before height `exp((log y)^A)` for every `A` (past VK), ultimately before `exp(y^c)`; equivalently, the Bohr sets of the prime orbit at constant precision are empty on those ranges, with a count of near returns uniform in `π(y)`.
2. **Short-to-long transfer.** From "no heavy return of short prime polynomials (length `(log X)^{2K}`) at heights `≤X`" to `|P(p)−A(p)|≤K` for the long smoothed count of length `p` — proportional saving at all heights (B46) followed by an elimination that assembles the short savings into the window count.

**Why it opens the path.**
- The crude count over ℤ fails exactly where the prime orbit returns: at a heavy early return a long prime polynomial is large and a zero can hide under it (proportional saving ⇔ no early heavy return) [L]. Over `𝔽_q` the auxiliary vanishes exactly at every rational point; over ℤ exactness exists only on the torsion, and the orbit visits the torsion only approximately [L].
- The breadth law must be collective: forms of height `h` act only while `hδ<½`, Liouville's bound `y^{−h}` excludes returns only up to `y^{O(1/δ)}`, and rounded step systems agreeing on all forms of height `≤K` return exactly at `T≥2πKy^K` [L]. The rank-depth law is the first collective statement: it counts near relations, not the smallest one [S].
- Both answers are informative. If the transfer (link 2) holds, the positivity-free route is reduced to breadth; if it fails, there is a configuration of short-polynomial savings that does not assemble, and the short-sum barrier (Π80) is a theorem.

**Strength and rungs.** The breadth law at `(log y)^A`, every `A`, is a past-VK statement; at `y^c` it is a Littlewood-type bound for `ζ(1+it)` [D]. Rungs: (i) two primes, depth law [L]; (ii) `k` primes, explicit forms [L]; (iii) VK breadth for heavy subsets [L]; (iv) rank-depth counting for `k≍(log y)^A` (A62); (v) collective counting uniform in `π(y)` (B137); (vi) `𝔽_q[T]`: exact Frobenius, nothing to bound [L].

**Tests.** T1: implied by RH (RH bracket; reciprocity) [L]. T2: two implications. T3: B46, the all-height sign, the two-sided crude bound. T4: no finite rung. T5: fails for rounded orbits (function fields) and impure columns [L]. T6: bounded-height certificates are refuted, collective ones are not. T7: moves Π94, Π95, Π121, Π128, Π133, Π136, Π137, Σ144.

**Limit.** It speaks about large heights; a finite layer at a fixed height is invisible to it. The finite stratum then needs the FE as a reciprocity acting on heights, the one sign-free ingredient left unused.

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved [L].** The modular horizon is `SL₂(ℤ)\`(Rindler wedge of AdS₄); its resonances sit at the zeros of `ξ(2s)`; every seed rings down at its zero-free region; one cuspidal cavity function of Hecke eigenforms sees every resonance and RH ⇔ its energy rings down at `y^{¾−ε}`. The archimedean place is a scalar of mass `m²=−¾` in Euclidean AdS₃ restricted to one geodesic: the archimedean Frobenius is `2π√(mn)G_{1/2}(|log(n/m)|)`, the bulk propagator in the quantization `Δ=½`; `2πG_{1/2}=2πG_{3/2}+½φ_{1/2}`; the pole of Weil's form is `(3/2)φ_{3/2}+½φ_{1/2}`, so in Weil's archimedean-plus-pole weight the `Δ=½` piece cancels and only `Δ=3/2` remains. The FE pairs each resonance `s=ρ/2` with `s*=½−s̄`; the reflection Krein form at `s` and `s*` is PSD on the line and has exactly one negative square off the line; RH ⇔ every reflection Krein form PSD. The horizon's own Krein form at one resonance is blind; internal modular conjugation collapses to the centre; vacuum-fixing and half-sided modular realizations cannot carry `Q`; the dual side has no sign; on smoothed packets the `ℍ³` self-energy is the universal counterterm `‖f‖²log(1/(1−r²))`, and its locking with the prime channel converges only when discrete and `L²` mass agree [S].

**The law, read physically [D].** A scalar in AdS₃ with `−1<m²<0` (here `m²=−¾`, inside the Breitenlohner–Freedman window) has two unitary quantizations, `Δ₋=½` and `Δ₊=3/2`, exchanged by a Legendre transform of the boundary generating functional (the double-trace flow). Weil's form uses `Δ₊` after the pole cancels `φ_{1/2}`; the reflection Krein form compares the response at a resonance with the response at its FE partner. A pairing between the two members of an FE pair is what a Legendre/double-trace duality between two quantizations does to two-point functions, and positivity of two-point functions is unitarity. The mass obstruction has a physical reading: the bulk (`ℍ³`) self-energy is a continuum (`L²`) quantity, the prime channel's a point-particle (discrete) one; a consistent theory must put both on the same footing — point sources in the bulk.

**The question.** *Is RH the unitarity of the alternate quantization?* Is there a pair of boundary theories, built from the worldline scalar with `m²=−¾` in its two quantizations and from prime interactions at the times `log n` (never from the zeros), and a double-trace/Legendre map between them, such that (a) the two-point functions of the two theories on cavity sources are the seed transforms at a resonance and at its FE partner, and (b) the reflection Krein form of the cavity is the two-point function of the flowed theory? Then RH ⇔ reflection positivity of that boundary theory.

**Why it opens the path.**
- It replaces a sign by an axiom: unitarity of a boundary theory with a positive-norm Hilbert space is structural; RH would say the arithmetic deformation stays inside the unitary window.
- It is exactly what the operator no-gos leave: the partner map acts between two theories, not inside one algebra — internal modular conjugation collapses to the centre and vacuum-fixing partners to square classes for that reason [L].
- It has rungs: the archimedean sector `G_{1/2}−G_{3/2}=½φ_{1/2}` and its cancellation by the pole [L]; graph black holes, whose partner standard forms exist iff the hole is damped [L]; the Narain AdS₃ partition function, modular invariant with every arithmetic pole retained and remainder with exactly the VK saving [L].
- A negative answer is informative: if no flow preserves the FE pairing, the physical reading reduces to the width axis (rates of one cavity energy).

**Calibration and risks.** Fakes (graph black holes with `t²>4q`) must fail through the flow leaving the window, not through the dynamics. A theory whose spectrum is the critical ordinates is a Hilbert–Pólya operator; the question is useful only if both theories and the flow are defined from the archimedean place and the primes alone.

**Second physical question (producer, B117).** *Is the modular horizon the modular image of a confined system with real normal modes?* A unitary horizonless system with the worldline modes as free part and the primes as interactions, and a modular transformation sending its Euclidean correlators to the mirror-even response, so that every resonance `ρ/2` is the image of a real normal mode — universal damping as kinematics (BTZ and thermal AdS₃ are S-dual [C]).

## 2.8 If RH is a problem of topology or geometry

**What is proved.** Off the diagonal Weil's form is an adelic Green pairing: the pole minus `2πG_{1/2}` on the degree geodesic of `ℍ³` minus `log p((p−1)/√p)G^{T_p}_{1/2}` on the apartments of the trees `T_p`, every local Green function at the critical parameter and PD on its geodesic or apartment [L]. Hyperbolic carriers at one place fail; compact and finite-volume embeddings fail at clustering degrees or at the cusps; the atomic surface is not an Arakelov surface (locked diagonal = discriminant) [L]; on smoothed packets scalar locking converges exactly at mass balance — separated packets, the subcritical regime — and keeps the discriminant, and fails for one overlapping profile [S]. RH ⇔ one side of Hasse–Weil for the smoothed Frobenius graphs at the prime degrees [L]. Topology: the orientation cover over ℤ exists, its middle cohomology never vanishes and has weight `≥½`, weight `½` ⇔ RH; prime-vertex local indices sum to `1−M(N)` and are unbounded below [L].

**Geometric question (B133).** *Is there an adelic carrier?* Is there a discrete subgroup `Γ` of `SL₂(ℂ)×Π'_pPGL₂(ℚ_p)` (restricted product, or `S`-arithmetic with `S` growing) and an automorphic Green function `𝒢` at the critical parameter on `Γ\(ℍ³×Π'_pT_p)` such that on the degree configuration `x_n=(z_n,(v_{n,p})_p)` — the orbit of the split torus `diag(n,1)` through the base point — `𝒢(x_m,x_n)` is the archimedean-plus-torsion Frobenius intersection off the diagonal, and its regular part at coincident points (the Robin mass of the configuration) is Weil's diagonal?

**Why it opens the path.**
- **It removes the mass obstruction.** On a quotient of `ℍ³×Π'T_p` the degree configuration is a discrete set of points for every factor at once; both Green divergences are point-mass divergences, so the discrete-versus-`L²` mismatch that kills scalar locking does not arise, and the diagonal is a genuine Robin mass rather than a locking of two dampings.
- **It evades the one-place no-go.** The primes are carried by the tree factors, which a product carrier supplies; a hyperbolic quotient alone sees only ratio kernels.
- **It converts the sign into potential theory.** Green functions of positive operators are PD kernels; a carrier would make Weil's form the energy of a configuration in a quotient, controlled by the bottom of its spectrum at the critical parameter and by its Robin masses.
- **It is the geometric face of the split-torus period.** Torus periods of Eisenstein series on `PGL₂(ℚ)\PGL₂(𝔸)` produce `ζ(s)ζ(s′)` [C]; the question asks whether the Green function reproduces Weil's kernel along the same torus orbit.

**Tractability.** The archimedean factor is fixed (`ℍ³`, `G_{1/2}`, `G_{3/2}`), the finite factors are fixed (trees at the Ramanujan point), and the corpus gives necessary conditions: the stabilizer of the degree end acts on the ratio alone; Poincaré convergence at `½` excludes parabolics in the archimedean factor; the atomic diagonal has order `N log N`. First step: the one-prime case `S={p}`, a lattice in `SL₂(ℂ)×PGL₂(ℚ_p)` and the Green function on `ℍ³×T_p` along one `p`-ladder, with its Robin mass compared to `selfIntersection(p^k)`.

**Topological question (B106).** *Does the orientation cover over ℤ carry a Lefschetz theory?* The real fibres of `y²=disc F_n` record the sign of complex conjugation on the roots of `F_n=Π_{p|n}(X²+p)` (the archimedean Frobenius acting by `ω(n)` transpositions), as the factor-trace cover over `𝔽_q[T]` records the sign of Frobenius (Stickelberger). Is there a space with a correspondence (the dilations `n↦pn`) whose Lefschetz numbers are the centred counts `M(N)` and whose middle cohomology has dimension `O(N^{½+ε})` with bounded local indices? Over `𝔽_q[T]` the cover's middle cohomology vanishes [L]; over ℤ it has weight `≥½` [L].

**Limit.** Over `𝔽_q` these structures come from a variety; over ℤ none is constructed. Heights over number fields give central-value signs, not off-line zeros [D].

## 2.9 New field for RH: arithmetic weight theory of Spec ℤ

**Does RH need a new field?** Yes. Every step of Deligne's purity argument has a Lean counterpart over ℤ — Stepanov side, absence of real zeros as Bombieri's twist, base change at the degrees `n^k`, free positivity of even tensor powers, Rankin square, gap iteration as self-improvement, and a sign-free two-sided decision step (F3, F18) — except the a priori bound on the abscissae of `L(M^{⊗2k},s)` that is uniform in `k`. Over a curve that bound is the finite dimension of `H¹`; over ℤ nothing plays its role.

| Aspect | Content |
|---|---|
| What it is about | Deligne's proof transported to Spec ℤ. The prime degrees play the extensions `𝔽_{q^n}`, the spline traces `2Re S(log p)` the point counts of the virtual motive `M=Σ_ze_zℤ(−z)` of the zeros, the even tensor powers `M^{⊗2k}` the sheaves whose positivity is free. The field supplies the uniform a priori pole bound. |
| What it would be like | A theory of families of zero configurations with a monodromy, in which ζ is a special fibre, the generic fibre is pure, and weights are semicontinuous under specialization. Landau's theorem plays the real pole of `L(F^{⊗2k})`, the gap iteration plays Weil's self-improvement, and the sample is any set of degrees with power-saving gaps. |
| Criteria it must meet | Reproduce Deligne on curves over `𝔽_q`. Use the Euler product and the FE (fail on the integer-norm one-off, which violates the Stepanov bound for every constant, on the `cosh` models and on the heat family). Respect the sampling boundary: one Frobenius aliases; finitely many Frobenii, the very smooth degrees and the primes off density-zero sets admit unattained tops; power-saving gap sets and power-thin exceptions decide. Start from the classical saving `√p·e^{−√(log p)/10}` and the VK width. |
| Questions it must answer | Which family carries ζ as a fibre with big monodromy — the gauge torus of unimodular multiplicative twists (Haar-a.e. fibre zero-free on `Re s>½` with natural boundary `½`), Dirichlet twists, vertical shifts, or a deformation family that keeps an Euler product? What is the analogue of `H²_c` = coinvariants, the a priori control of the top pole of `L(F^{⊗2k})`? In which topology on the family are weights semicontinuous (Haar-generic exponent `½` against Baire-generic exponent `1` shows that the naive one fails)? |
| Tools it aims to develop | Families of Euler products with a monodromy on their zero configurations; tensor-power L-functions `−L′/L(M^{⊗2k})`; uniform pole bounds from the FE of the fibres; sampling theorems at power-dense degree sets; a weight-semicontinuity principle. |
| Objects | The virtual motive of the zeros and its tensor powers; the smoothed Frobenius graphs at the prime degrees; the trace zeta `Σ_ze_zζ(s−kz)`; the gauge torus and its hull; sampling weights and power-saving gap sets. |
| Language | weight, purity, tensor power, base change, sample, Stepanov side, twist, monodromy, specialization, semicontinuity. |
| Mechanisms | Built on: one side (or both, sign-free) at the prime degrees ⇔ RH; uniform tensor moments ⇔ RH; Rankin square abscissa `2maxRe ρ`; the Stepanov side's blind set; a.e. purity on the gauge torus [L/S]. To discover: the uniform pole bound and the semicontinuity of weights. |

**Main conjecture (uniform weights).** There is `A` with `Σ_{p≤N}log p·(2Re S(log p))^{2k}≤C_kN^{1+A}` for every `k`, proved from a family in which ζ specializes. **Milestones.** M1 [L] RH ⇔ one side at the primes ⇔ uniform tensor moments. M2 A family with a monodromy whose generic fibre satisfies the uniform moments. M3 Semicontinuity of the top weight. M4 `A_k=o(k)` for ζ (zero-free strips of every width). M5 RH.

## 2.10 New field for AAL: arithmetic base change

**Does AAL need a new field?** Yes. The finite-layer world is fully specified in Lean and internally consistent (§2.3); the programmes that study it (ExceptionalLayerTheory, EulerFETransportTheory, TailArithmeticOfThePrimeOrbit) describe what a finite layer forces, and every identity they prove preserves the height of a zero. AAL is free over a curve for one reason: base change `𝔽_q→𝔽_{q^m}` makes the zeros periodic in height, so every zero recurs at larger heights with the same real part. Over ℤ nothing moves a zero in height: the FE reflects a height to itself, Hecke operators act by time shifts that fix resonance positions, and the Adams operations dilate heights of the prime orbit but not of the zeros. The missing field is a base change over ℤ.

| Aspect | Content |
|---|---|
| What it is about | Exact arithmetic operations that carry zero-forcing data of ζ from a height `t` to larger heights at the same real part, up to a loss that vanishes: the vertical transport that base change supplies over `𝔽_q`. |
| What it would be like | Dynamics of height dilations on the Bohr hull of ζ and on the zero divisors of its translates. The Adams semigroup `t↦mt` acts on the prime orbit; large values already transfer along it (absolute large values force heavy returns at `mt`, `m≤Q`) [S]; the field asks for the same transfer for zeros, through the Euler tail (zeros of ζ are zeros of every Euler tail) and the FE. |
| Criteria it must meet | Reproduce periodicity of zeros under base change over `𝔽_q` (and AAL for curves). Fail on the one-offs (Euler product, integer norms, linear counting, continuation, no FE), on the `cosh` and two-scale `cosh` models (FE, no Euler product) and on `ζ(s−h)` (same labels, shifted zeros): the mechanism must use the FE about `Re s=½` together with the sizes of the coefficients. Respect the two-scale law (couple low and high zeros), the height-preservation of the FE (the FE alone transports nothing) and the consistency of the finite-layer identities. |
| Questions it must answer | Which operation is base change over ℤ: Adams dilations on the hull, Hecke time translations on the modular horizon, Rankin–Selberg or symmetric-power lifts, or the passage `ζ↦ζ(ms)`-type compositions? Does a right zero at height `γ` force, under the dilation `t↦mt`, a zero or an exact Euler-tail event at heights `≍mγ` with real part `≥Re ρ−ε(m)`, `ε(m)→0`? What is the loss law of large-value transfer along dilations when the value is zero rather than large? |
| Tools it aims to develop | Dilation transfer of large values and its version for small values; joint prime-phase returns with the rough current at its variance; tail transport; exceptional currents at exponential damping; Turán on thick sets; the base-change identities of curve zeta functions as calibration. |
| Objects | The hull of ζ and its Adams semigroup; divisors of vertical translates; Euler heads and tails; the finite top layer and its wave; base-changed curve zeta functions. |
| Language | base change, height dilation, vertical transport, transfer loss, tail event, exceptional layer, replication. |
| Mechanisms | Built on: AAL ⇔ tail transport; dilation transfer of large values; FE height reflection; joint returns; the exceptional current [L/S]. To discover: a transfer for zeros. |

**Main conjecture (arithmetic base change).** For every right zero `ρ=β+iγ` and every `ε>0` there are infinitely many integers `m` with zeros of ζ at heights `≍mγ` and real part `>β−ε` — a quantitative form of AAL — derived from a transfer law along the height dilations `t↦mt`. **Milestones.** M1 [L/S] dilation transfer of large values; AAL ⇔ tail transport. M2 A transfer of exact tail events along `t↦mt` with an explicit loss. M3 The loss law for one top quartet (the one-quartet world). M4 Replication of every finite layer. M5 AAL.

## 2.11 New field for RH without positivity: arithmetic differential algebra (Λ-geometry) of Spec ℤ

**Does a positivity-free RH need a new field?** Yes. The positivity-free toolkit in the corpus is complete at the receiver level (the two-sided decision step, Turán elimination) and capped at the producer level: integrality reaches Chebyshev, freezing reaches the trivial separation bound, exponential sums reach VK, transcendence bounds depth, collective counting has its first rank law (F9, F18). The one sign-free proof of a Riemann hypothesis — Stepanov–Bombieri over `𝔽_q` — rests on a feature ℤ lacks: the Frobenius `x↦x^q` is a polynomial map whose derivative vanishes, so vanishing to high order at all rational points costs little degree. Over ℤ the exact Frobenius of integer auxiliaries is the Adams operation, exact only on the torsion, and exact order costs the degree [L]. No module of the corpus contains a `p`-derivation, a Fermat quotient or a Frobenius lift (search). The missing field is the arithmetic analogue of "the derivative of Frobenius vanishes": Buium's `p`-derivations `δ_p(a)=(a−a^p)/p` and Borger's Λ-structures, in which the Adams operations are the Frobenius lifts.

| Aspect | Content |
|---|---|
| What it is about | Stepanov's method over ℤ in the direction of the primes: auxiliary objects whose multiplicity at a prime is measured by `p`-derivations rather than by archimedean derivatives, so that vanishing at all `p≤N` to order `m` is imposed at a cost below `ψ(N)`. |
| What it would be like | Arithmetic jet spaces of Spec ℤ and of the prime torus; δ-rings and Λ-rings (Witt vectors are δ-rings; a Λ-structure is a commuting family of Frobenius lifts, the corpus's Adams operations); counting inequalities derived from a δ-polynomial that vanishes on a prescribed set, as Stepanov derives `N_n≤qⁿ+O(q^{n/2})` from a polynomial vanishing at the rational points. |
| Criteria it must meet | Reproduce Stepanov–Bombieri over `𝔽_q` (where `δ_p` becomes a derivation and the Frobenius has zero differential). Use no sign and no spectral input. Beat Chebyshev: the exact Stepanov count over the fixed points of ℤ costs `lcm(1,…,N)`, and the new multiplicity must cost less. Respect the corpus no-gos: integrality creates no zeros at returns (archimedean), Rouché copies are capped, exactness lives on the torsion, a polynomial of constant modulus on the prime orbit is a monomial — so the multiplicity must be `p`-adic, not archimedean. Fail on the integer-norm one-off (it violates the Stepanov bound for every constant). |
| Questions it must answer | What is the multiplicity of an integer auxiliary "at all primes at once" in δ-geometry? Is there a δ-polynomial vanishing to order `m` at every `p≤N` of δ-degree `o(ψ(N))`? Does such an object give the two-sided crude bound `\|P(p)−A(p)\|≤K` through a counting inequality? How do δ-characters and arithmetic Manin maps on the prime torus interact with the Adams operations? |
| Tools it aims to develop | `p`-derivations and their jets; Frobenius lifts and Λ-structures; δ-characters; arithmetic Picard–Fuchs operators; `p`-adic continuation of auxiliaries; the two-sided gap iteration as the final elimination. |
| Objects | Fermat quotients, Witt vectors, Λ-rings, arithmetic jet spaces, the prime torus with its Adams semigroup, torsion points and their Galois orbits, integer auxiliaries, the smoothed Frobenius graphs. |
| Language | `p`-derivation, Frobenius lift, Λ-structure, δ-multiplicity, arithmetic jet, auxiliary, two-sided crude bound. |
| Mechanisms | Built on: Adams = Frobenius on torsion, exact order costs the degree, closed-point Stepanov count = Chebyshev, sharp cost of polynomial syzygies `p_min^{qr}`, the sign-free decision step [L/S]. To discover: cheap δ-multiplicity at all primes. |

**Main conjecture (δ-Stepanov bound).** The vanishing conditions at the fixed points of all `Γ_n`, `n≤N`, are met by a δ-auxiliary of δ-degree `N+O(√N log²N)`. For the archimedean auxiliary `A_N` this degree bound is RH (its log length is `ψ(N)`) [L]; the field's content is to obtain it from δ-multiplicity, where vanishing at a prime is cheap, and to feed the resulting count into the two-sided gap iteration. **Milestones.** M1 [L] torsion calculus and sharp syzygy cost. M2 Stepanov–Bombieri over `𝔽_q` restated in δ-language. M3 A δ-multiplicity at one prime `p` cheaper than `p`. M4 Simultaneous δ-multiplicity at all `p≤N` below `ψ(N)`. M5 RH.

## 2.12 New field for RH as AdS physics: arithmetic quantization duality of the modular horizon

**Does it need a new field?** Yes: the corpus has the horizon (receivers, Krein forms, standard-form no-gos), the archimedean scalar of `m²=−¾`, and the identity `G_{1/2}−G_{3/2}=½φ_{1/2}`, but no theory relating the two quantizations by a flow with arithmetic sources.

| Aspect | Content |
|---|---|
| What it is about | The archimedean place is a scalar of `m²=−¾` on a geodesic of Euclidean AdS₃, with two unitary quantizations `Δ=½` and `Δ=3/2`; Weil's form uses `Δ=3/2` after the pole cancels `½φ_{1/2}`. The modular horizon carries the zeros as resonances, paired by the FE. The field builds the boundary theories of the two quantizations with prime interactions and identifies the FE pairing with the Legendre duality between them. |
| What it would be like | AdS₃/CFT₂ with arithmetic sources: generalized free fields of dimension `½` and `3/2`, double-trace flows, Poincaré sums over `SL₂(ℤ)`, unitarity bounds. Theorems are identities between partition functions and positivity of boundary two-point functions. Prime sources are point particles in the bulk, so the bulk and prime self-energies are both point-source divergences (the mass obstruction of scalar locking does not arise). |
| Criteria it must meet | Build everything from the archimedean place and the primes, never from the zeros. Reproduce `2πG_{1/2}=2πG_{3/2}+½φ_{1/2}`, the spherical compensation, the reflection Krein law, the cavity receivers and the Narain remainder. Avoid the excluded realizations (internal modular conjugation, vacuum-fixing partners, Borchers inclusions). Make graph black holes with `t²>4q` non-unitary. |
| Questions it must answer | Which boundary operator has the seed transforms at a resonance and at its FE partner as two-point functions? Which double-trace coupling relates them, and where does the BF window sit in arithmetic terms? Why does arithmeticity (no second place of `SL₂(ℤ)`) keep the coupling inside the window? What is the confined dual whose normal modes map to the resonances (B117)? |
| Tools it aims to develop | Arithmetic double-trace flows; Legendre duality of generating functionals with prime sources; Krein-space holography for the mirror-even channel; Rademacher expansions with arithmetic poles; unitarity bounds for arithmetically deformed generalized free fields. |
| Objects | `ℍ³` with the degree geodesic, `G_{1/2}`, `G_{3/2}`, spherical functions; the modular horizon, seeds, odd cavity and Hecke cavity functions; reflection Krein forms; the Narain partition function; graph black holes. |
| Language | quantization, double-trace flow, Legendre duality, BF window, unitarity, reflection pair, resonance, cavity, seed, ringdown, point source. |
| Mechanisms | Built on: the AdS₃ reading of the archimedean place, spherical compensation, the reflection Krein law, sharp cavity receivers, the dual-side no-sign theorem, partner standard forms iff damped [L]. To discover: the duality map and the unitarity of its arithmetic deformation. |

**Main conjecture (arithmetic unitarity).** The reflection Krein form of the modular horizon is the two-point function of a unitary boundary theory obtained from the two quantizations of the archimedean scalar by an arithmetic double-trace flow. **Milestones.** M1 [L] archimedean sector. M2 One damped graph black hole as a unitary flow, one undamped as a non-unitary one. M3 The Narain partition function as a flowed partition function. M4 A universal positive decay rate (zero-free strip). M5 Unitarity (RH).

## 2.13 New field for RH as topology or geometry: S-arithmetic potential theory of the degree configuration

**Does it need a new field?** Yes. HyperbolicArakelovTheory and SurfaceOfSpecZ have the local pieces (the `ℍ³` Green function at `∞`, the tree Green functions at `p`, the adelic Green formula off the diagonal) and the no-gos (one-place carriers, finite-volume embeddings, atomic locking, smoothed scalar locking at mass imbalance). What none of them has is a global quotient carrying all places at once, on which the diagonal is a Robin mass.

| Aspect | Content |
|---|---|
| What it is about | Potential theory of the degree configuration `x_n` (the split-torus orbit of `diag(n,1)`) in an `S`-arithmetic quotient `Γ\(ℍ³×Π_{p∈S}T_p)`: Green functions at the critical parameter, energies and Robin masses of infinite configurations, and their limit as `S` grows. The topological branch is a Lefschetz theory of the orientation cover over ℤ. |
| What it would be like | Potential theory on products of hyperbolic spaces and buildings: automorphic Green functions at a fixed spectral parameter, capacities, Robin masses, renormalized energies; Arakelov theory in which the archimedean fibre is `ℍ³` and the finite fibres are trees, with points (not smoothings) as the basic probes on every factor. |
| Criteria it must meet | Reproduce the adelic Green formula, the spherical compensation and the plastic sign law, the atomic diagonal of order `N log N`, the logarithmic smooth self-energy, the genus `c_B(0)/2` of smoothed pairs, the discriminant defect of locked dampings and the mass-balance criterion of smoothed locking. Respect the one-place no-go (hyperbolic carriers see only ratio kernels). Calibrate on curves over `𝔽_q`, where the diagonal self-intersection is `2−2g`. |
| Questions it must answer | Which `S`-arithmetic lattice carries the configuration (B133)? Is the Robin mass of the configuration Weil's diagonal, and is the defect against it the discriminant? What is the bottom of the spectrum of the quotient at the critical parameter, and how does it control the sign? Which correspondence on which space has the centred orientation counts as Lefschetz numbers (B106)? |
| Tools it aims to develop | Green functions on `ℍ³×Π_{p∈S}T_p` and their Poincaré series; Robin masses and capacities of degree configurations; limits in `S`; Lefschetz fixed-point theory for the dilation correspondences on the orientation cover; weight filtrations of its cohomology. |
| Objects | `ℍ³` with the degree geodesic; trees `T_p` with their `p`-ladders as apartments; the split torus and its orbit; `S`-arithmetic quotients; the 𝔽₁-zonotope and `ℙ¹_ℤ`; smoothed Frobenius graphs; the prime-quadratic family and its orientation cover. |
| Language | adelic carrier, local Green function, Ramanujan point, Robin mass, configuration energy, mass balance, archimedean Stickelberger sign, Lefschetz number, weight. |
| Mechanisms | Built on: adelic Green formula, spherical compensation, carrier no-gos, locked-damping discriminant, smoothed mass obstruction, smooth self-energy, one side of Hasse–Weil at the primes ⇔ RH, orientation cover weight `≥½` [L/S]. To discover: the global carrier and its Robin mass; a Lefschetz theory for the cover. |

**Main conjecture (adelic energy positivity).** Weil's form on smoothed tests is the renormalized Green energy of the degree configuration in an adelic quotient, and that energy is nonnegative on primitive tests. **Milestones.** M1 [L/S] adelic Green formula; carrier, locking and mass-balance no-gos. M2 A one-prime carrier on `ℍ³×T_p` along one ladder, with its Robin mass compared to the discriminant defect. M3 An `S`-arithmetic carrier for growing `S`. M4 Energy positivity on separated packets from the carrier (a subcritical check). M5 Energy positivity (RH). Topological branch: archimedean Stickelberger sign [L]; a correspondence with Lefschetz numbers `M(N)`; a dimension bound for the middle cohomology.

## 3. The one big question: does the top layer of ζ repel the rest?

**Question (B131).** *Is there a Deuring–Heilbronn law for ζ?* Suppose AAL fails: ζ has a finite top layer at `β=Θ` (attained, with ordinates `γ_j`) over an infinite remainder whose zeros above the layer's heights satisfy `Re ρ≤Θ₂<β`, and `Θ∞<β`. Graded form: is `Θ∞−½≤f(β−Θ₂,γ)` for an explicit `f` that tends to `0` as the gap `β−Θ₂` grows? Extreme form: are all but finitely many zeros on the line, `¬AAL ⇒` finitely many off-line zeros, hence AAL ⇔ B13?

**Why it is less hard than AAL, RH and quasi-RH [D].** AAL implies it vacuously; it implies neither qRH nor AAL nor B13. It is an implication between two zero laws — a relation between the top layer and the high remainder — so the two-scale obstruction (no property of zeros above or below one height decides the dial) does not apply to it: it couples the scales by construction.

**What either answer gives.**
| Answer | Effect |
|---|---|
| Yes, extreme form | ¬AAL ⇒ finitely many off-line zeros, so AAL ⇔ B13: the linear dial `AAL ⊊ … ⊊ B13` collapses for ζ; every finite-stratum receiver (finite index, lattice index, heat count, `N_d` bounded, eventual slice positivity, one Toeplitz-positive tower) becomes an AAL receiver; the AAL routes (BAG, ZCG, JAS, SC, WL thick runs, IWT, ELT, EFT) merge with the finite-stratum routes; RH becomes ZAL ∧ B13 |
| Yes, graded form | each linear level `LinAt C` becomes a statement about the layer: the exceptional coordinate acquires its first ζ-specific two-scale law, and a layer close to the line forces a remainder close to the line |
| No | a mechanism that keeps an off-line remainder under an isolated top: the finite-layer world is richer than a Siegel world, AAL cannot be reduced to the finite stratum, and an AAL proof must exclude layers over off-line remainders directly |

**What is proved and usable [L].** The finite-layer world of §2.3: finite exceptional subtraction of the Gaussian current on high strips; prime-current passage; the top multiplicity read without counterterm; joint prime-phase returns; the exceptional current at exponential damping, equal to the top mode times the layer's wave, with sharp envelope `M=Σ e^{πγ_j/4}`; coefficient-density floors at every base; positive-density failure of the Stepanov bound at the primes; the explicit formula with every Gamma mode retained; Turán on thick sets of levels. Positivity is allowed here: Fejér kernels, Turán power sums with one isolated term, the `3−4−1` mechanism twisted by `n^{iγ}`.

**Why this question.** For Dirichlet `L`-functions an exceptional zero near `1` forces strong zero-free regions for the other zeros (Deuring–Heilbronn) [C]; the corpus shows that the Stepanov side of Hasse–Weil is blind exactly to real zeros and that for `L(s,χ)` a Siegel zero hides from that side only (F17) [L]. For ζ the analogue of the exceptional zero is the top layer: it biases the prime phases `n^{iγ}` as a Siegel zero biases `χ(p)` toward `−1` (`ψ(x)−x≈−2m Re(x^ρ/ρ)` at leading order), and the corpus has every exact identity of the world in which it lives but no law of how it interacts with the remainder. It is the obstacle that blocks every AAL route at once (the two-scale input), it would kill or merge the AAL and finite-stratum route families, and it is an implication rather than a zero law.

**First step and obstacle.** Explicit formula with the layer subtracted, tested against a positive kernel twisted by `n^{iγ}`: the layer's bias on prime phases enters with a known sign and size; the remainder's zeros near `Θ₂` must be shown to cost more than the bias pays. The obstacle: the layer contributes `x^{β−σ}`, small against the remainder unless `β` is close to `1`, so the classical mechanism needs the exceptional term to dominate; the corpus's exponential-damping current is the observable in which the top layer does dominate (supercritical speed), and the question is whether the remainder can be read in the same observable.

**Tests.** T1: implied by RH (vacuously), implies neither qRH nor AAL. T2: an implication. T3: the table. T4: no finite rung decides it. T5: false on the two-scale `cosh` models (a finite layer over a remainder at positive asymptotic abscissa, with FE, order one and reality), so it must use the Euler product; calibrated on Dirichlet `L` with a real exceptional zero [C]. T6: not refuted; the two-scale and linear-hierarchy obstructions concern scale-separated properties. T7: moves Γ155, Γ175, Γ176, B13, B83, B111, B116, B128. T8: not a named problem; its extreme form may be as hard as the classical exceptional-zero problems, its graded form has a first step and one obstacle.

**Limit.** It reorganizes the AAL problem; it proves neither AAL nor B13.

### Alternatives considered
| Question | Effect | T8 verdict |
|---|---|---|
| Ground-state orthogonality on the critical curve (B104, §2.4) | decides whether the pole channel is an independent detector of ¬RH | passes; Σ block only |
| Sample boundary (B136, §2.5) | exact prime-side shape of ZAL | passes; prime side only |
| Adelic carrier (B133, §2.8) | a geometric realization with the diagonal as Robin mass | producer; large |
| Coupled locking at overlapping packets (B135) | an Arakelov presentation where RH lives | passes; bookkeeping |
| Independent current bound / one-quartet world (B134) | excludes the minimal finite layer | fails: contains excluding one off-line quartet |
| Breadth law of returns (B97, B137) | sign-free producer | fails: past VK |
| Sampling-set bound, metric recurrence (B126, B127) | AAL | fail: contain AAL |
| Residue-class Stepanov criterion (A59) | RH from one residue class | just work |
| Halving pairs (B125) | one eigenform receiver | excludes a configuration of zeros |
