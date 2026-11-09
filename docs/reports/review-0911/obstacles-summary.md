# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `ad80866fec` (2026-11-09); modules in the working tree of other agents are marked `[S]`. Working log: `logs/review-0911-statusquo-facts.md`.

Evidence: `[L]` Lean source; `[S]` Lean source unfinished or unintegrated; `[K]` Lean with transitive axiom audit; `[D]` deduction, not a Lean theorem; `[N]` numerical, uncertified; `[C]` classical, not formalized. Sections 2.3–2.13 and 3 are interpretation and ideation; every statement there that is not tagged is a proposal, not a result.

**38 live formulations; 9 candidates.** HJ→PA; BSH→CDC; FEL's BSY criterion→CTF. Candidates: APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF.

Notation: `Θ=sup Re ρ`; `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`; **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **LinAt C** `Θ−½≤C(Θ∞−½)`; `Φ(L)=e^{−L/2}primeDeviation(e^L)`; `c_B` the cubic-spline orbit correlation, `Re S=c_B` its trace, `Re W(B±τ_vB)=2c_B(0)±2c_B(v)`; `Γ_n` the smoothed Frobenius graph of degree `n`; `P(d)` the smoothed von Mangoldt count in the window of `d`, `A(d)` its archimedean-plus-pole prediction, `c_B(log d)=A(d)−P(d)`; a **sampling weight** `0≤w≤Λ` has `Σw(n)n^{−s}→∞` as `s↓1` and no other singularity on `Re s=1`; `G_s(d)=e^{−(s−1)d}/(4π sinh d)` on `ℍ³`; `G^{T_p}_s` the Green function of the Bruhat–Tits tree of `PGL₂(ℚ_p)`; `H_t` the heat deformation of Ξ; `Λ_F(s)=∫_𝒟F·E*(s−½)` the completed transform of a seed; `F_n=Π_{p|n}(X²+p)`.

## 1. Big picture

### 1.1 One inequality per prime
The three wall families have one common minimal face [L]:

  RH ⇔ `c_B(log p)≥−K` for every prime `p` ⇔ `c_B(log p)≤K` for every prime ⇔ `P(p)≤A(p)+K` ⇔ `Re W(B+τ_{log p}B)` bounded below at every prime ⇔ `Re W(B−τ_{log p}B)` bounded below at every prime.

The test `B+τ_{log p}B` is a sum of two translates of one fixed cubic spline; its Weil energy `2c_B(0)+2c_B(log p)` is the defect of the effective class `Γ_1+Γ_p`, and `c_B(log p)=A(p)−P(p)` is the error of the smoothed prime count in the window of `p`. The growth exponent reads the width: zero width `≤a` ⇔ `c_B(log p)≥−Kp^a` ⇔ `≤Kp^a` (`0≤a<½`) [L]. Unconditionally `(P(d)−A(d))/√d→0` (PNT in every window) [L]. The proof mechanism: the gap method iterates (the Lipschitz constant of the trace improves with the width), Landau's theorem for the nonnegative density `K±c_B` replaces Pringsheim's, and ζ has no real zero in the strip; at the degrees `p^k` the zero-free strip improves itself by the factor `1+1/k` per Landau step, starting from Huxley's prime gaps [L]. The same holds at the integers, the squares, the `n^k` and every degree set with power-saving gaps; two-sided Hasse–Weil at the prime planes alone, by one gap step, gives only `|Re ρ−½|≤1/12` [L]; the geometric degrees `q^n` alias and decide nothing [L].

### 1.2 Deligne's argument runs over ℤ except for its uniformity
The traces `2Re S(log p)` are the point counts of the virtual motive `M=Σ_ze_zℤ(−z)` of the zeros. Positivity of the even tensor powers is free; RH ⇔ `M^{⊗2k}` have a common half-plane of convergence ⇔ `Σ_{p≤N}log p(2Re S(log p))^{2k}≤C_kN^{1+A}` with `A` independent of `k` [L]. The Rankin square `ΣΛ(n)(2Re S(log n))²n^{−s}` has abscissa exactly `2maxRe ρ` [L]. Bombieri's second count (the twist excluding real Frobenius eigenvalues) is replaced by the absence of real zeros of ζ: the Stepanov side `c_B≥−K` is blind exactly to real zeros (a real zero masks precisely the shallower zeros; its blind set is the configurations whose top layer is a nonnegative almost periodic function), the other side has no mask [L]. Base change: the traces at the degrees `n^k` have the Dirichlet series `Σ_ze_zζ(s−kz)`, the analogue of the rationality of the zeta function of a curve over `𝔽_{q^k}` [L].

### 1.3 RH is ZAL plus AAL; the prime degrees produce AAL
For every zero configuration purity ⇔ ZAL ∧ AAL, with the strict dial `Pure ⊊ AAL ⊊ LinAt C₁ ⊊ LinAt C₂ ⊊ (∃C LinAt) ⊊ B13`, `∃C LinAt ⇔ (ZAL ⇒ Pure)`, `AAL ⇔ ∀C>1 LinAt C` [L]. Producers of AAL from the prime side [L]:
- a one-sided crude bound of the spline traces at a **sampling set** of primes: the primes in one residue class (from `L(1+it,χ)≠0`), the primes off a set of relative logarithmic density zero, the degrees `p^aq^b` of two primes (double pole at `1`, no other singularity on `Re s=1` because `p^M≠q^N`); it leaves no deepest off-line zero of ζ;
- uniform tensor moments at a residue class;
- positive Lebesgue measure, or positive Hausdorff dimension, of the bases at which the Weil lag has recurrent sub-top readings, at every rate (under ¬AAL these bases have dimension 0 and almost every base sees the top; unconditionally a dense `G_δ` of recurrent bases exists);
- the other producers (not-attained top, thick lag, thick prime deviation, positive count of one tower, polar ground energy, JAS shells, slow aligned returns on right discs, weak recurrence, …).
Attainment of the top is the only thing ZAL adds: it is free on all primes (power-saving gaps) and on the dense two-prime difference lags `log m−log n`, `m,n∈⟨p,q⟩`; it is not free at the single degrees `p^aq^b`: an actual tempered configuration without real zeros, with unattained top, has `2Re S(a log p+b log q)≥−5` for all `a,b` [L] (finitely many Frobenii [S]; positive-weight models at every finitely generated monoid [L]). Whether it is free on density-one sets of primes is the question of §3.

### 1.4 What decides AAL and the finite stratum, and what cannot
- **Two scales.** Properties of the zeros above a height, or below a fixed height, decide neither B13 nor any linear law nor AAL [L].
- **Analytic shape.** FE, order one and reality admit every finite top layer, also over a remainder of positive asymptotic abscissa [L].
- **Family uniformity.** A finite-stratum law valid for every heat deformation `H_t` is RH; among `Φe^{−τx²}` only `τ=0` has an absolutely convergent Dirichlet series (read at `σ→∞` through the tilted law, far from every zero) [L]. A B13 input must see the Dirichlet series.
- **Firewall.** Continuous Beurling systems, positive discrete Euler products built from the prime-square-corrected quantiles of a count, integer-norm Euler products with natural coefficients and linear counting, and rational-prime Euler products carry a finite off-line layer; the discrete and integer-norm ones continue holomorphically and zero-free across `Re s=½` with exactly one off-line pair; of Euler product, integrality, linear counting, continuation across the line and the FE, only the FE excludes the layer [L].
- **FE rigidity.** A countable Beurling system whose theta function satisfies Riemann's FE up to a measurable polynomially bounded `L¹` or `L²` defect is the rational primes, with zero defect [L]. No nonclassical neighbour of ζ with a defective FE exists; every input for AAL must be an exact identity of ζ.
- **Well-foundedness.** Wolff towers defeat elimination without ZAL [L].
- **Positivity of sources.** Positive theta sources survive finite donor surgery that moves a narrow cluster of actual critical zeros off the line while keeping reflection, reality, arbitrarily long endpoint jets and positivity after every finite prime deletion; two quartets on `Re s=¼,¾` preserve both endpoint jets, one cannot [L].

### 1.5 The finite-layer world
Under ¬AAL there is an isolated top over an infinite remainder, `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})` with `T` a unique finite trigonometric polynomial, syndetic lag excursions with a coefficient-density floor at every base, and a positive-density set of primes with `c_B(log p)<−Kp^a` for every `K` and `a<Θ−½` [L]. The exact identities of ζ in this world [L]: the Gaussian prime discrepancy minus its Gamma field tends to `A(σ)−ξ′/ξ(σ)` with no zero-free premise; at a rightmost zero the raw current reads `−m_ρ/2` with no counterterm; a finite exceptional subtraction controls a whole high strip; the raw prime current `ΣΛ(n)n^{−s}e^{−n²/t}` tends to `−ζ′/ζ(s)` uniformly on an interior high strip at inverse-height damping and at fixed damping `1/T` across `[T,2T]`; the head-conditioned rough Gaussian mean square is head mass × rough mass; the FE reflects a height to itself, `N_t(s)ζ(s+it)−conj ζ(1−s̄+it)=O(t^{−¼})`; escaping translates bounded on a domain meeting `Re s>1` stay right of `½`. None transports a zero in height.

### 1.6 Exactness over ℤ lives on the torsion
The exact Frobenius of integer auxiliaries is the Adams operation `ψ_aF=F(u^a)`: the dilation `t↦at` on the prime orbit (one fixed point, `t=0`), the Galois action of `ℚ(μ_m)` on torsion points, `ψ_qF=F` on the `(q−1)`-torsion; the norm amplifier forces vanishing on a whole closed point at every uniform order [L]. Integrality cannot create zeros at returns: the heights where some nonzero integer auxiliary vanishes are countable and every return window contains generic heights [L]. Exact order costs the degree (`J≤log N/log 2`); at the common fixed point the excess order is a homogeneous integer relation among the `log p` [L]. The minimal auxiliary vanishing at the fixed points of all `Γ_n`, `n≤N`, is `Π_{p≤N}(u_p−1)^{⌊log_pN⌋}`, of log length `ψ(N)`; RH ⇔ `ψ(N)≤N+C√N log²N`; the integer-norm one-off violates this bound for every `C` [L]. The exact Stepanov count over ℤ is Chebyshev's. Approximate vanishing is capped: Rouché copies at returns cost `J≤e²r log N+log(1/δ)` [L]. Transcendence bounds the depth of a return (`t≥poly(1/δ)` for any two primes by the explicit Baker bound), Dirichlet bounds its breadth from above (`R≤⌈π/2δ⌉^{|P|}`), and Diophantine information of bounded height cannot exclude returns past the Kronecker scale `y^{O(1/δ)}` [L] — the rounded systems that defeat it are function fields, where every return is exact [S]. By the reciprocity of returns (the explicit formula modulated to height `t`), a heavy return of the primes `≤y` at height `t` is a configuration of zeros near `t` imitating the pole: `Σ_ρy^{|Re ρ−½|}/(1+|γ_ρ−t|)²≫√y` up to `log t`; under RH this forces `log t≫√y` [L]. Return bounds concern the labels `log p` alone and are shared by `ζ(s−h)`, which violates ZAL: a route from return bounds to ZAL or AAL must use the FE about `Re s=½` or the size of the coefficients [S].

### 1.7 The window sign is one scalar flow; the critical curve adds one orthogonality
RH ⇔ `Ψ=½log H₁` locally bounded ⇔ `a*(ζ)=⊤` ⇔ `λ*(c)→0` [L]. At `R=c⁸/log N`: `R_c=R_PSD=R_polar=R_halfline≤R_prim=R_high=W`; every threshold `=⊤` ⇔ RH; the charged compactness passage is closed [L]. Under ¬RH the window threshold `W` is finite and strong compactness produces a unit half-line ground state at `W`; each ground state bounds `R_polar` by a reciprocal shift in its polar pairing; finite `R_polar=W` forces every ground state to be polar-orthogonal [L]. No finite or countable square-bounded family of holomorphic multipliers dominates the depleted kernel `4/(¼−z²)−12/(64−z²)` on the off-line strip [L].

### 1.8 The theta wall is ζ on the critical line
All ranks reduce to the adaptive head `M(b)=⌈|b|/2+B⌉`, whose leading term is `|ζ(½+ib)|²+O(|ζ(½+ib)||b|^{−½}+|b|^{−1})` [L]. The sign is automatic where `|ζ(½+ib)|` is large and is decided by second-order terms near the critical zeros.

### 1.9 The near-line wall is the dark range
Near-unit mollified moments need `log N≥log²T/(6K₀)`; an Euler mollifier reaching them uses every prime up to `≍log²T` [L]; conditional tail laws stop at the Kronecker scale [L]; past the height the Fejér mean value of the prime polynomial is a count of prime pairs at multiplicative distance `≲1/T`, of exact order `X²`, with the Hardy–Littlewood pair constant [L].

### 1.10 The surface of Spec ℤ is an adelic Green pairing off the diagonal
Off the diagonal Weil's kernel is the pole minus the Green functions of all places at the critical parameter [L]:
- at `∞`, `2πG_{1/2}(d)` on the degree geodesic of `ℍ³`, `d=|log(n/m)|`; the `k=0` term is the cusp, `k≥1` the jets of the trivial zeros;
- at `p`, on a `p`-ladder `n=mp^k`, `log p((p−1)/√p)G^{T_p}_{1/2}(k)`, the Green function of the `(p+1)`-regular tree at the Ramanujan point `s=½` (the only parameter reaching the tempered edge `2√p`), PD on every apartment; off the ladders the prime kernel vanishes;
- the archimedean compensation is spherical: the pole is `(3/2)φ_{3/2}+½φ_{1/2}`, the Frobenius `2πG_{3/2}+½φ_{1/2}`, the complementary piece cancels, `C_∞=(3/2)φ_{3/2}−2πG_{3/2}`, negative exactly below the plastic ratio; primes never change the atomic sign; the first Beurling–Deny inequality holds exactly on plastic windows.
No twisted hyperbolic carrier with convergent Poincaré series at `½` carries the torsion (seen from the end of the degree geodesic every such carrier is a continuous ratio kernel, and the torsion jumps at prime ratios); embeddings into compact quotients, and into finite-volume quotients given a Newtonian kernel with a cusp expansion of nonzero Wronskian, reproduce no Frobenius intersection [L]. Locked atomic dampings (pole − `ℍ³` damping + torsion damping at a reparametrized radius) converge to Weil's kernel off the diagonal for every locking, but their diagonal differences are torsion self-intersections (the different of `ℚ(ζ_n)`), so a convergent locked diagonal is bounded and never PSD, while PSD requires a diagonal `≥N(log N−17)/8` in every dyadic block [L]. The atomic surface is not an Arakelov surface. On smoothed probes the archimedean self-energy is logarithmic with one universal counterterm `‖f‖²log(1/(1−r²))`, and the renormalized limit is minus the archimedean Lévy jump energy [L]. On smoothed graphs RH ⇔ `c_B` is a counterterm-free pointwise limit of PSD kernels; neither smoothed channel alone is one [L]. The sign sits in the diagonal.

### 1.11 The count on one ray per prime
A count law has a quadratic half (a nondegenerate Born rule, the FE) and a count half (damping) [L]. Over ℤ the quadratic half holds, RH ⇔ `Q` on integer probes is the Tate limit of an `ℕ`-count, and `Q` is not integer-valued; no integral kernel `C:ℕ×ℕ→ℤ`, in particular no trace form of Hecke endomorphisms of a free abelian group, reproduces `Q` [L]. The count is needed only on one effective ray per prime: RH ⇔ every class `Γ_1+Γ_p` carries an `ℕ`-count along its ray with Tate limit `2c_B(0)+2c_B(log p)` ⇔ the prime planes are copositive; two primes suffice on the planes `⟨Γ_m,Γ_n⟩`, `m,n∈⟨p,q⟩` [L]. Arithmetic counts defined before the form exist in quantity [L]: different quotients `ℤ[X]/(F_n,F_n′)` with `|disc|` elements, the integer gluing quotient `ℤ/(1−M(N))`, Gaussian section heights of divisor classes with quadratic Tate limit uniform in the conductor, resultant rings, radial cyclotomic counts; none has Tate limit `δ_p(1,1)`.

### 1.12 Production, Farey, the nerve, the prime vertices and the orientation cover are the Mertens level
Producer rates equal the Mertens level; Farey discrepancy ⇔ RH; `M(N)=−χ̃` of the prime-star nerve; `Σ_p` prime-vertex indices `=1−M(N)`, indices unbounded below [L]. The orientation cover over ℤ exists: the real points of `y²=disc F_n` number `1+μ(n)`, its equation is the Sylvester discriminant, its total count over `n≤N` is `N+M(N)`; its centred count exceeds `c√N` and `−c√N` infinitely often (the middle cohomology never vanishes, weight `≥½`), and weight `½` ⇔ RH [L]. Over `𝔽_q[T]` the factor-trace cover has exactly `qⁿ` points; over `𝔽_q` elliptic and hyperelliptic orientation and squarefree-divisor counts have square-root discrepancy from the curve root bound [L].

### 1.13 The horizon has complete and sharp receivers
The modular horizon is the quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)` [L]. Seeds (continuous, bounded, modular, cusp-decaying functions) form a `*`-algebra; their horocycle responses have Mellin transforms `Λ_F·2s(2s−1)/ξ(2s)`: the group fixes the resonance positions, a seed enters only through `Λ_F(ρ/2)` [L]. Every seed rings down at its zero-free region [L]. Mirror-odd tent fields, pairs of Maass cusp eigenforms and pairs of Hecke eigenforms see every resonance; one cuspidal cavity function of Hecke eigenforms sees every right resonance, and RH ⇔ its energy rings down at `y^{¾−ε}`; RH ⇔ every two-mode energy rings down at `y^{¾−ε}`; a zero-free strip ⇔ a common rate `y^α`, `α>½` [L]. One Hecke eigenform is blind exactly at halving pairs `ζ(ρ)=ζ(ρ/2)=0` and at the zeros of its Shimura integral [L]. The horizon's own Krein form at one resonance has infinite index of both signs at every zero; the reflection Krein form `Λ_F(s)Λ̄_G(s*)+Λ_F(s*)Λ̄_G(s)`, `s*=½−s̄`, is PSD on the line and has exactly one negative square at each off-line zero: RH ⇔ every reflection Krein form PSD [L]. The dual side has no sign: a one-sided response bound is as strong as a two-sided one [L]. Internal modular conjugation collapses to the centre; vacuum-fixing and half-sided modular realizations cannot carry `Q` [L]. Every horizon observable is on the width axis.

### 1.14 Hull
Haar-a.e., fair-coin-a.e. and order-two fibres extend zero-free to `Re s>½` with natural boundary `½`; the Liouville point extends iff RH [L].

### 1.15 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| Markov, Perron, sign-gauge balance past `e^{−3/4}`, `log ρ` | refuted; Beurling–Deny exactly on plastic windows | [L] |
| Size-only payment of primes | ends before half-width `21/40` | [L] |
| Floor tower as aperture producer | stays below `0.3621` | [L] |
| Weighted Gårding on the whole horizon | false on deep atoms | [L] |
| Physical tearing at the collar boundary | Schur ratio `4/13` | [L] |
| Universal holomorphic multipliers for the critical depleted kernel | excluded on the off-line strip | [L] |
| Uniform logarithmic Gamma reserve in coefficient norm | resonant two-copy profiles | [L] |
| Fixed theta heads; summable absolute pair majorants; compact cores | no margin; harmonic diagonal; geometric growth | [L/S] |
| Positive Laplace representations of the theta amplitude | excluded | [L] |
| Product certificates in Euler coordinates past `Re s=1` | cannot cross | [L] |
| Parabolic structure as selector of `t=0`; family-uniform finite-stratum laws | blind; RH-strength; the Dirichlet series is the selector | [L] |
| Asymptotic or local-below zero statistics as inputs to any level of the dial | cannot decide | [L] |
| FE, order one and reality as exclusion of a finite layer | `cosh` and two-scale `cosh` models | [L] |
| Positivity, Euler products, integrality, linear counting, continuation across the critical line, reflection symmetry, positive Hecke combinations as AAL | finite layers exist | [L] |
| Nonclassical Beurling systems with an `L¹` or `L²` FE defect as fakes of ζ | none exist | [L] |
| Positive theta source + finite endpoint jets + finite prime-deletion positivity as selector | off-line surgery survives | [L] |
| Density statements on levels of a tower; elimination without well-foundedness | rank barrier; Wolff towers | [L] |
| Single degrees of a finitely generated monoid of primes without attainment | actual tempered configurations with unattained top pass at two Frobenii | [L] |
| One Frobenius (geometric degrees) as a sampling set | aliasing | [L] |
| Exact returns as a Frobenius; norm-majorant Rouché copies at returns | one fixed point; trivial separation bound | [L] |
| Integrality at returns of the prime orbit | zero heights countable; no exact zeros at returns | [L] |
| Bounded-height Diophantine certificates against returns; return bounds as uniform routes to ZAL | Kronecker-scale breadth cap (rounded systems are function fields); `ζ(s−h)` shares the returns | [L/S] |
| Slow-return bounds on discs crossing `Re s=½`; whole-quadrant boundedness | power growth forced; impossible | [L] |
| Schur, `C*`, KMS, reflection positivity, internal modular conjugation, vacuum-fixing partners, Borchers half-sided inclusions as zero locators or carriers of `Q` | blind; central collapse; square-class collapse; no eigenvalues | [L] |
| The resonance Krein form of the cavity; dual-side signs | infinite index at every zero; one-sided = two-sided | [L] |
| One Hecke eigenform as a complete receiver | halving-pair and Shimura blindness | [L] |
| Positive Poisson measure of the Hecke algebra; positive Hecke polynomials | hold off the line; annihilate finite resonance sets | [L] |
| Wave dynamics, flux, unitarity, Hecke, FE at genus two, first-level counts, integrality as universal damping | fakes carry all | [L] |
| Linear counts as count laws; Hecke at a second place; `Q` or an integral trace form as its own count | degenerate; conservation only; not integer-valued | [L] |
| Narain remainder past `¾`; sharp sources at the RH rate | impossible; need Möbius × circle cancellation | [L] |
| Integer stencils as a mechanism independent of Möbius; exact Stepanov auxiliaries over ℤ | rate is the Mertens level; count is Chebyshev's | [L] |
| Discrete Morse matchings; fixed-point localization in cardinality; persistence | Betti `≍N`; primes fixed with unbounded indices; `s`-independent | [L/D] |
| Renormalization as a source of sign; renormalized torsion under finite constraints | any form arises; both signs survive | [L] |
| Metrics on `ℙ¹_ℤ`, toric pairings, continuous Hecke kernels, finite-rank kernels, hyperbolic quotients with convergent Poincaré series, compact or finite-volume embeddings as carriers | excluded | [L] |
| Locked atomic dampings; logarithmic atomic diagonals; separate positive channels | discriminant diagonal, never PSD; diagonal `≥N(log N−17)/8`; divergence | [L] |
| Thermal averaging (primon gas) as a strip input | Euler factors at real points `>1` | [L] |
| Power moments as logarithmic depth majorization for the heat divisor | `(2,2)` against `(4,½,½)` | [L] |
| Shrinking-mesh pure Euler approximants | Euler abscissa escapes | [L] |

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

### Exceptional coordinate, flow, near-line, continuation, orbit
| # | Task | Routes | Basis |
|---|---|---|---|
| A16 | Numerical `r,m,q` for `a≤1` [N] | RW | Galerkin |
| A18 | Twisted second moments past `21/50`: to `½`, Conrey `4/7` [C] | WD, census | raises rate `2θ` |
| A19 | Heat horizon toward its method floor | ZCG, AES | profile margin |
| A20 | Jensen rung toward the saddle scale (unverified) | LA, FFP | saddle identity |
| A21 | Census items; logarithmic two-point Chowla [C]; runs past five | MC, ACS, census | classical |
| A24 | Certified scans of `S_S`; brackets for `S*(a,b)` | TH | column calculus |
| A37 | Resonator mean of `\|ζ\|²` with resonators growing below the Kronecker scale (unverified) | BAG, ZCG, PTT | fixed-resonator limit, arithmetic mean values |
| A47 | The one-quartet world: explicit window constants of the tower theorems for one top quartet `Θ±iγ` at base `π/γ`, the coefficient-density floor, and the constraint each finite-stratum receiver imposes on `(Θ,γ)` (unverified) | ZCG, WL, IWT, EFT | single top pair at every level of its resonant tower; coefficient density [L] |
| A50 | Finite-stratum laws on other positive deformation families (cosine shifts `A_h`, shifted Jensen families) imply RH, as for the heat family (unverified) | ZCG, PTR, LA | `TheFiniteStratumLawOnTheHeatFamilyIsRH` [L] |
| A53 | Integrate the transcendence modules and the working-tree modules (rough-variance split, spline phase at the zeros of `B̂`, torsion Newton bases, sparse harmonic mass) into their umbrellas | TTPO, EFT, SOSZ, ALST, APD | proved or in-progress source [S] |
| A58 | Effective gap iteration at the primes: explicit constants from a one-sided bound with constant `K` to an explicit width after each Landau step (unverified) | ACS, SOSZ | first strip `5/8`, Landau step [L] |

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
| A54 | Instantiate the cusp expansion with nonzero Wronskian for the `L²` resolvent of `Δ−¾` on Bianchi quotients, closing the finite-volume carrier exclusion | ACS, HF, HAT | `EmbeddingsIntoAFiniteVolumeQuotient` assumes it [L]; horospherical zero mode computed in SOSZ [L] |
| A55 | FE rigidity for generalized (continuous) Beurling systems with `L¹` or `L²` defect (unverified) | BAG, ZCG, APD | Poisson rigidity of self-dual measures with a gap [L]; the tent machinery of EFT [L] |

## 2.2 Open mathematical obstacles

### The common minimal face
| # | Problem | Strength | Routes |
|---|---|---|---|
| B130 | **The arithmetic Stepanov bound at the primes**: `P(p)≤A(p)+K` for every prime (⇔ `c_B(log p)≥−K` ⇔ `Re W(B+τ_{log p}B)` bounded below); any growth `Kp^a`, `a<½`, is a zero-free strip | RH (≥qRH for `a<½`) | ACS, SRT, WL, HF, RW, ALST, SOSZ |

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
| B104 | Polar payment at every ratio below `W`, equivalently `R_polar=W`; at finite `W`, whether a critical half-line ground state can be polar-orthogonal | method | HF, SRT, AIP |
| B123 | Correlated arithmetic pairings dominating the depleted kernel where every universal holomorphic multiplier fails | method | HF |
| B124 | Useful finite initial depth budgets of the ξ heat divisor (`S_q<∞` for some `q`, or a finite logarithmic budget) and extinction arbitrarily near `t=0` | sub to RH | ZCG, LA, WD |

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
| B97 | Constant-precision first return of every heavy subset, `log R(y,δ)≥y^c` for fixed `δ`, by an argument of growing height (bounded-height forms stop at the Kronecker scale [S]) | sub | PTT, TAPO, TTPO, BAG |
| B98 | Positive-generator integer-norm systems: which count distance forbids a finite top layer | method | RAC, SPAL, APD |
| B100 | A saving for `t log n` on moving families of blocks past Vinogradov's degree | sub | PTT, TAPO |
| B106 | A natural self-map or action on the orientation cover over ℤ (or on the prime complex) with bounded local indices whose Lefschetz number is the centred count, localizing `M(N)` to `O(N^{½+ε})` | RH (≥qRH at `θ<1`) | MC, HF, ESG, HHAC, RIAC, HAT |
| B110 | **Thick crude count**: `primeDeviation(X)=O_a(X^{½+a})` along a thick set of geometric scales of one base, for every `a>0` | AAL (with ZAL at `a=0`: RH) | WL, ZCG, ACS, IWT |
| B113 | Möbius × quarter-disc remainder `Σ_{d≤X}μ(d)E(X/d)=O(X^{½+ε})` | beyond RH | PM (sharp shells) |
| B121 | Freezing control beyond the precision cap: integral at sign returns, or signed (integrality creates no zeros at returns [L]) | sub | BAG, ACS, PTT, IWT, ALST |
| B126 | A one-sided crude bound of the spline traces on one sampling set of primes (a residue class, the primes off a relative-density-zero set, or `p^aq^b`) | AAL (with ZAL: RH) | ACS, SRT, ZCG, BAG, IWT |
| B127 | Positive Lebesgue measure (or positive dimension) of the bases with recurrent sub-top Weil-lag readings, at every rate | AAL (with ZAL: RH) | WL, ZCG, IWT |
| B132 | **Almost all primes**: does a one-sided crude bound at the primes outside a set of relative logarithmic density zero decide the line for every tempered configuration without real zeros, with no attained top (§3) | method | ACS, SRT, WL, HF, ZCG, IWT |

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
| B83 | AAL | sub | BAG, JAS, SC, ZCG, WL, IWT |
| B85 | Arithmetic global trace on a family containing ζ | RH | ACS |
| B86 | Mixed Young projections at unbounded rank | RH | ACS |
| B87 | A nonnegative count on the rays `Γ_1+Γ_p`, defined without `Q`, with Tate limit `2c_B(0)+2c_B(log p)` (a genuine limit: `Q` is not integer-valued, no integral kernel reproduces it) | RH | ACS, HF, PM, RW, AE, CTH, SOSZ |
| B88 | A counterterm-free PSD damping of `c_B` on `log ℕ₊` on smoothed graphs (⇔ RH); it must couple and lock the prime and archimedean-plus-pole channels | RH | AE, HHAC, SOSZ, RIAC, HAT, HF |
| B89 | A bounded aligned return at each right zero on a right disc | sub | BAG, ZCG |
| B92 | Arithmetic source of a rotated relation with coefficients of the size of `Q` | RH | ZCG, RAC |
| B93 | A contradiction using growth or arithmetic of `Q` beyond the extremal law | RH | ZCG, RAC |
| B111 | **`ZAL ⇒ RH`** (existential linear AAL): `Θ∞=½ ⇒ Θ=½` | sub | BAG, ZCG, IWT, WL |
| B112 | A mechanism converting the FE (which reflects a height to itself) into vertical transport of zeros, using the Euler product and coupling both scales | sub | BAG, ZCG, EFT |
| B114 | A realization of the partner involution outside the central, vacuum-fixing and Borchers classes | producer | PM, CTH |
| B116 | Linear AAL at one fixed slope `C≥1` (⇔ thick relative crude count at exponent `½+C(Θ∞−½)+ε`) | sub | ZCG, IWT, WL |
| B117 | A confined companion of the modular horizon (§2.7) | producer | PM, BHR, ASH, CTH, AHMH |
| B125 | Halving pairs: no zero `ρ` with `ζ(ρ/2)=0`, and nonvanishing of one Shimura integral at every `ρ/2` (makes one Hecke eigenform a complete receiver) | indep. | PM, AHMH |
| B128 | Replication in the finite-layer world: the exact identities of ζ under ¬AAL force a second zero at the same depth above every height (one quartet first) | sub | BAG, ZCG, EFT |
| B129 | **The smoothed locked diagonal**: a canonical locking of the `ℍ³` damping and the tree/torsion damping on smoothed probes with finite diagonal limit; is that limit `c_B(0)`, and what is the defect otherwise (§2.4) | method | ACS, HF, PM, SOSZ, HAT, RIAC, CTH |
| B131 | **Deuring–Heilbronn law of the top layer**: does an isolated top layer of ζ force every other zero onto the line, `¬AAL ⇒ finitely many off-line zeros` (§2.5) | sub | BAG, ZCG, IWT, EFT |
| B133 | An adelic carrier: an automorphic Green function at the critical parameter on a quotient of `ℍ³×Π_pT_p` reproducing Weil's full kernel on the degree configuration (§2.8) | producer | ACS, HF, HAT, SOSZ |
| — | ZAL | ≥qRH | whole programme |

## 2.3 Frankenstein routes

**No assembly closes RH.** Every assembly below has at least one open input of RH, AAL or ≥qRH strength, or names one. The assemblies whose output is RH (F1, F2, F3, F15) each need an input that the corpus cannot produce. Their value is that they collapse independent problems into one, or fix what a missing input must contain.

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F1 | **Split skeleton.** A sampling-set AAL producer (a one-sided crude bound at the primes of one residue class, or off a density-zero set, or at `p^aq^b`; positive-measure lag recurrence; uniform tensor moments at a class) with any ZAL receiver (inner-field decay, subtracted lag, `Λ_Xlog X→0`, eventual Hadamard, high-collision counts) | RH [L] | one sampling-set bound (B126) or B127, and ZAL | the two inputs are prime-side and zero-side; if density-one prime sets decide RH without attainment (§3), F1 loses ZAL |
| F2 | **One inequality per prime.** SOSZ prime degrees, the prime two-bump tests, the Stepanov bound as a prime count, the count door on one ray per prime, the window form on windows of length `log p+O(1)` | the Σ, Π and count readings of RH are one number per prime [L] | B130 | ACS, SRT, WL, HF, PM count branch and ALST have one target |
| F3 | **Deligne skeleton over ℤ.** Stepanov side (one-sided bound), absence of real zeros (Bombieri's twist), base change (`n^k`, trace zeta `Σ_ze_zζ(s−kz)`), tensor powers (positivity free), Rankin square (abscissa `2maxRe ρ`), the gap iteration (Weil's self-improvement) | every step of Deligne's purity proof has a Lean ℤ-counterpart except the a priori bound on the abscissae of `M^{⊗2k}` uniform in `k` [L] | the uniform weight bound (RH) | names the missing piece exactly: the role of the finite-dimensional cohomology of the curve (§2.9) |
| F4 | **Critical curve.** Threshold identities, charged compactness, half-line ground states, polar orthogonality, multiplier no-go | `R_c=R_polar=R_halfline≤W`; ¬RH ⇒ a ground state at finite `W`, polar-orthogonal if `R_polar=W` [L] | B104 | the critical curve carries no sub-RH content beyond one inequality and one orthogonality |
| F5 | **Horizon.** Seeds, position rigidity, every-seed ringdown, odd cavity, Maass and Hecke pairs, Baire, two-mode Zagier dichotomy, resonance and reflection Krein forms, dual side, standard-form trichotomy, Narain | physics reduces to one rate of one cavity energy or to one reflection sign [L] | B71 or B68 | waves, Hecke, KMS, modular conjugation, half-sided inclusions and dual-side signs are closed as sources |
| F6 | **The diagonal.** Adelic Green formula (`ℍ³` and trees), spherical compensation, locked atomic dampings (discriminant diagonal), atomic genus `N log N`, prime channel `≍log N`, smooth archimedean self-energy logarithmic, smoothed PSD-limit criterion | off the diagonal Weil's form is an adelic Green pairing; atoms give the wrong diagonal; smoothing renormalizes the archimedean self-energy by one universal counterterm [L] | B129 then B88 | turns the count/Hodge family into one question about a diagonal limit (§2.4) |
| F7 | **FE as the only selector.** Firewall (one-offs across the line), complete FE rigidity, Poisson rigidity, Dirichlet selector of the heat family, finite-surgery of positive sources | every model with a finite layer lacks an FE; every system with an integrable FE defect is ζ; every input using only positivity, Euler products, integrality, linear counting, continuation, analytic shape or family-uniform laws is refuted [L] | B112 | the B13/AAL input must be an exact identity of ζ that uses the FE together with the Euler product |
| F8 | **Finite-layer world.** Rigid ¬AAL, finite oscillation, coefficient-density floor, prime-current passage, top multiplicity, rough variance, height reflection, Bohr duality at sampling sets | a fully specified world in which a contradiction must be found [L] | any contradiction (B128, B131) | the table below lists what the world must satisfy |
| F9 | **Exactness and Diophantine closure.** Adams Frobenius on the torsion, norm amplifier, integrality at returns, closed-point Stepanov count, Rouché precision cap, explicit Baker bounds, return–form duality, breadth cap | exact methods over ℤ reproduce Chebyshev; approximate methods stop at the trivial separation bound; Diophantine methods of bounded height stop at the Kronecker scale [L/S] | B97, B121 | closes these as producers of the crude step; what survives is growing-height or signed information |
| F10 | **Mertens in eight geometries.** Franel–Landau, Farey law, nerve, core, barcode, prime-vertex indices, gluing quotient `ℤ/(1−M(N))`, orientation cover | one exponent; the cover's weight is `≥½` unconditionally, `½` ⇔ RH [L] | B106 | topological, dynamical and discriminant tools act on the Mertens level |
| F11 | **Three sampling axes.** Prime degrees (sampling weights), bases of towers (metric recurrence), levels of towers (thick sets) | AAL from a one-sided bound on any of the three [L] | B126, B127, B110 | three independent formulations of the same AAL input |
| F12 | **Heat divisor.** Initial divisor budgets, elapsed-depth comparison through collisions, crowding dissipation, sharp coefficient `2`, heat finite-stratum law, Dirichlet selector | finite budgets give `N(t)(2t)^q≤2S_q` and `t·N(t)→0` [L] | B124, B24 | the heat route needs one finite initial budget plus an input that sees the Dirichlet series |
| F13 | **Theta wall.** Column calculus, carrier horizon, Ξ-current lift, adaptive head, Gamma reserve, partial sum `=ζ(½+ib)` | all ranks reduce to `\|ζ(½+ib)\|²` plus second-order terms near the zeros [L] | A42, B102 | merges TH with the size of ζ on the line |
| F14 | **Dark range.** Savings, precision law, heavy-return dictionary, almost-every-height cancellation, collision counts of order `X²`, precision cap, depth law and breadth cap | the short-sum barrier is one first-return statement and its breadth is not reachable by bounded-height Diophantine data [L/S] | B97, B121 | gap: precision `y^{−9/2}` against constant precision |
| F15 | **Count skeleton.** Hecke isometry of `Q`, Tate principle, point-count defect on curves, half-products, adelic Green fibres, critical weight, ray counts, `Q` not integer-valued, arithmetic counts defined before the form | every ingredient of the curve count proof except a count over ℤ, needed on one ray per prime [L] | B87, B88 | output RH; names the missing object exactly |
| F16 | **Two Frobenii.** Kronecker density of `ℤlog p+ℤlog q`, continuity of the spline trace, two-sided Hasse–Weil on the rank-two monoid planes | RH from the lags of two primes, no attainment [L] | the bound on those lags (RH) | the minimal degree set is a rank-two lattice, not the primes |
| F17 | **Siegel calibration.** Dirichlet `L` from both sides: the upper side at the primes is GRH including Siegel zeros, the lower side is blind exactly to real zeros; ζ has none | AAL and Siegel zeros are both "masked layers"; the Stepanov side's only blind spot is absent for ζ [L] | none (calibration) | an exceptional-zero theory for ζ can borrow from Deuring–Heilbronn (§2.5) |

**Closest to the open core: F2, F3, F6, F1.** F2 makes the Σ∩Π core one inequality per prime. F3 shows that over ℤ the whole of Deligne's argument is present except the uniformity that cohomology supplies over a curve. F6 isolates the count/Hodge family into one diagonal. F1 is the only assembly with two independent inputs, and §3 asks whether one of them can be dropped.

### The finite-layer world: what a contradiction search may assume (F8)
| In the world ¬AAL | Evidence |
|---|---|
| Isolated top `Θ`, rest left of `Θ₂<Θ` above the layer's heights, bottom layer reflected at the same heights | [L] |
| `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})`, `T` unique, sign changes at bounded log gap | [L] |
| `Θ∞<Θ`: `ψ(x)−x` is `O(x^{Θ∞+ε})` after removing finitely many exponential terms, and not before | [L] |
| Two-prime dilation annihilation of `ψ`; a positive annihilator of the top whose inverse oscillates at every exponent `<Θ` | [L] |
| At every base, syndetic lag excursions with a coefficient-density floor; a single top pair is seen at every level at base `π/γ`; almost every base sees the top; recurrent sub-top bases have dimension 0 | [L] |
| At the primes, `c_B(log p)<−Kp^a` on a set of positive relative density for every `K`, `a<Θ−½`; at every sampling set the same | [L] |
| Polar ground energy `≤−c′e^{2(Θ−½)B}/B³`; lag excursions of positive lower Abel density | [L] |
| `Λ`-moments: diagonal `→0`, long-shift correlation `→m²` | [L] |
| The raw Gaussian prime current at the rightmost zero reads `−m_ρ/2`; on a high interior strip it passes to `−ζ′/ζ` at inverse-height damping and across dyadic windows; the head-conditioned rough variance is the diagonal | [L] |
| The FE reflects every height to itself; escaping bounded translates stay right of `½` | [L] |
| Every return at a top zero tail-bad; transport events rare; near-full tail events abundant | [L] |
| The layer is not a rational relocation of critical zeros with positive coefficients; positive theta sources can carry it after finite surgery | [L] |

No contradiction comes from exact identities alone, from positivity, Euler products, integrality, counting or positive Hecke combinations alone, from the FE with order one and reality, from a property shared by the heat family, or from statistics at one scale [L].

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
| T8 | Tractable: not a named long-standing problem in disguise (RH, quasi-RH, ZAL, AAL, B13, Lindelöf, pair correlation, Hardy–Littlewood, Chowla, past VK, Landau–Siegel); its first step uses corpus objects and has one named obstacle |

Every statement below AAL that constrains the zeros of ζ contains B13 or an exceptional-zero problem of Landau–Siegel type, and every crude step on thick or sampling sets contains AAL [L/D]. The questions of 2.4, 2.5 and 3 are therefore questions about mechanisms or about implications between zero laws, not zero laws for ζ.

## 2.4 Breakthrough question below RH and quasi-RH: what is the diagonal of the adelic Green pairing?

**Question (B129).** *Does Weil's form on smoothed tests arise, with no counterterm, as the limit of the pole minus the two natural dampings of the archimedean and the finite places, locked so that their divergences cancel?* Precisely: for a smoothed probe `f` (a spline test, or the smoothed Frobenius graphs `Γ_n`), let
  `L_r(f) = pole(f) − A_r(f) + T̃_{ρ(r)}(f)`,
with `A_r` the `ℍ³` Green damping (diagonal divergence `‖f‖²log(1/(1−r²))`) and `T̃_ρ` the twisted torsion damping on `ℙ¹_ℤ` (the tree Green damping on the `p`-ladders; diagonal divergence logarithmic in `1/(1−ρ)`). (i) Is there a probe-independent locking `ρ(r)→1` for which `L_r(f)` converges for every smoothed probe? (ii) Is the limit `W(f)`? (iii) If not, what is the defect `D(f)=lim L_r(f)−W(f)`?

**What is proved [L].**
- Off the diagonal, Weil's kernel is the pole minus the Green functions of all places at the critical parameter (`ℍ³` at `∞`, the Bruhat–Tits trees at `p`); every channel is a limit of positive dampings.
- On atoms, every locking converges off the diagonal, and its diagonal differences are the torsion self-intersections `−I(n,n)/φ(n)` (the different of `ℚ(ζ_n)` per unit degree); a convergent locked atomic diagonal is bounded and never PSD, while PSD needs `≥N(log N−17)/8` per dyadic block.
- On smoothed probes the archimedean self-energy is `‖f‖²Z(r)`, `Z(r)=log(1/(1−r²))+O(1)`, and its renormalized limit is minus the archimedean Lévy jump energy.
- On smoothed graphs, RH ⇔ `c_B` is a counterterm-free pointwise limit of PSD kernels; neither smoothed channel alone is such a limit; any Hilbert difference presentation with a divergent part locks norms and correlations of its two parts.

**Why the question is open and well posed [D].** On atoms the two divergences differ in kind (a power against a logarithm), so locking can only produce the discriminant. On smoothed probes both divergences are logarithmic, so a probe-independent locking may exist; whether it does depends on whether the torsion channel's smoothed self-energy has the same universal form `‖f‖²·log` as the archimedean one, i.e. on the difference between the discrete norm the primes see and `‖f‖²_{L²(ℝ)}`.

**What either answer gives.**
| Answer | Effect |
|---|---|
| (i) and (ii) yes | Weil's form on smoothed tests is the counterterm-free limit of one explicit family "pole + positive torsion − positive `ℍ³` Green energy". B88 becomes a question about one family: is `L_r` eventually PSD? The count, Hodge and Arakelov routes (ACS, HF, PM count, SOSZ, HAT, RIAC, CTH) get one concrete Hodge-index target |
| (i) yes, (ii) no | An explicit quadratic defect `D` between the locked adelic Green energy and Weil's form — a new arithmetic invariant on smoothed tests, the smoothed analogue of the discriminant diagonal; RH becomes `lim L_r ≥ D` on primitive tests |
| (i) no | No probe-independent locking exists: the damping presentation of Weil's diagonal must couple the channels non-locally; the locked-damping mechanism is closed on smoothed tests as it is on atoms, and the diagonal must come from a source other than the adelic Green functions |

**Why this question.** It is the last structural gap of the count/Hodge family after the off-diagonal was assembled and the atomic diagonal was identified. It is an identity between explicit unconditional limits, implying nothing about the zeros. Its first step is a computation parallel to `TheArchimedeanSelfEnergyIsLogarithmic` for the twisted torsion energy on smoothed probes; the obstacle is the probe dependence of the discrete-versus-continuous norm.

**Tests.** T1: method (value of a limit), implied by nothing about ζ's zeros. T2: an identity. T3: the table. T4: infinitely many probes. T5: calibrated on atoms (defect = discriminant) and on curves over `𝔽_q`, where the diagonal is the self-intersection `2−2g` and Castelnuovo–Severi holds. T6: only the atomic locking is refuted. T7: moves Γ149, Γ152, Γ158, Γ168, Γ170, B88. T8: not a named problem.

**Limit.** It decides the shape of the count/Hodge core, not its sign: RH remains eventual PSD of a locked family.

### Alternatives
| Question | Why it matters | T8 | Limit |
|---|---|---|---|
| Ground-state orthogonality at finite `W` (B104) | decides whether the pole channel is an independent detector of ¬RH on the critical curve | passes | Σ only |
| Halving pairs (B125) | one Hecke eigenform as a complete receiver | open as to difficulty | adds a receiver |
| Continuous FE rigidity (A55) | closes generalized Beurling fakes | just work | classification only |
| Almost all primes (B132) | the big question of §3 | passes | — |

## 2.5 Breakthrough question below AAL: a Deuring–Heilbronn law for the top layer of ζ

**Question (B131).** *Does an isolated top layer of ζ push every other zero onto the critical line?* Precisely: if AAL fails (a finite top layer at `Θ` over an infinite remainder of asymptotic abscissa `Θ∞<Θ`), is the set of off-line zeros finite? Graded forms: does ¬AAL force `Θ∞−½≤f(Θ−Θ₂,γ)` for an explicit `f` that tends to `0` as the gap `Θ−Θ₂` between the layer and the next real part grows?

**Why it is weaker than AAL and not a zero law of exceptional type [D].** AAL implies the statement vacuously; the statement implies neither qRH nor AAL nor B13. It is an implication between two zero laws, a relation between the low layer and the high remainder, not a property of zeros above or below one height, so the two-scale obstruction (Γ140) does not apply to it.

**What it would give.**
| Answer | Effect |
|---|---|
| Yes (extreme form) | ¬AAL ⇒ finitely many off-line zeros, so AAL ⇔ B13: the whole linear dial `AAL ⊊ … ⊊ B13` collapses for ζ, every finite-stratum receiver (finite index, lattice index, heat count, `N_d` bounded, eventual slice positivity, one Toeplitz-positive tower) becomes an AAL receiver, and the AAL problem becomes the finite stratum |
| Graded form | each linear level `LinAt C` becomes a statement about the layer; the exceptional coordinate acquires a law relating the top to the remainder, i.e. the first two-scale theorem that uses ζ's arithmetic |
| No (a mechanism shows layers coexist with off-line remainders) | the finite-layer world is richer than a Siegel world: AAL cannot be reduced to B13, and an AAL proof must exclude layers over off-line remainders directly |

**What is proved and usable [L].** The finite-layer world of §2.3 (finite exceptional subtraction of the Gaussian current on high strips, prime-current passage, top multiplicity read without counterterm, coefficient-density floors, positive-density excursions at the primes); the explicit formula with every Gamma mode retained; positivity is allowed here: Fejér kernels, Turán power sums with one isolated term, the `3−4−1` mechanism.

**Why this question.** For Dirichlet `L`-functions an exceptional zero near `1` forces strong zero-free regions for the other zeros (Deuring–Heilbronn) [C]; the corpus shows that the Stepanov side of Hasse–Weil is blind exactly to real zeros and that for `L(s,χ)` a Siegel zero hides from that side only (F17) [L]. The ζ-analogue is the top layer: the corpus has every exact identity of the world in which it lives, but no law of how it interacts with the remainder.

**Tests.** T1: implied by RH (vacuously), implies neither qRH nor AAL. T2: an implication. T3: the table. T4: no finite rung decides it. T5: false on the two-scale `cosh` models (a finite layer over a remainder at positive asymptotic abscissa, with FE, order one and reality), so it must use the Euler product. T6: not refuted; Γ140 and Γ155 concern scale-separated properties. T7: moves Γ155, B13, B83, B111, B116. T8: not a named problem; its extreme form may be as hard as the classical exceptional-zero problems, its graded forms have a first step (the explicit formula with the layer subtracted and a positive kernel) and one obstacle (the layer's contribution `x^{Θ−σ}` is small against the remainder unless `Θ` is close to `1`).

**Limit.** It reorganizes the AAL problem; it proves neither AAL nor B13.

### Alternatives
| Question | Why it matters | T8 | Limit |
|---|---|---|---|
| Sampling-set bound (B126) | AAL from one residue class of primes | fails: contains AAL | — |
| Positive-measure recurrence (B127) | metric AAL producer | fails: contains AAL | — |
| Replication in the finite-layer world (B128) | the direct AAL step | fails: contains AAL | — |
| The one-quartet world (A47) | explicit constants for the smallest layer | passes (just work) | constants only |

## 2.6 If positivity, Weil positivity and spectral methods are excluded

"Spectral" is read as spectral theory of operators in every form: eigenvalues, spectral decompositions, Hilbert–Pólya realizations, trace formulas, spectral gaps, Lax–Phillips semigroups, Maass and Eisenstein spectral theory, standard forms. "Positivity" includes nonnegativity of counts, of Dirichlet coefficients (Landau's theorem), of Fejér and sinc kernels, Hodge index and Tate limits. Kept: Fourier analysis, mean values used as bounds, exponential sums, absolute convergence, power sums, Vandermonde and Turán, Dirichlet polynomials, integrality, Diophantine approximation and transcendence, recurrence, almost periodicity, Jensen and Rouché.

**What survives [L/D].**
- The decision step is sign-free from two sides. A **two-sided** crude bound `|c_B(log p)|≤K` at the primes makes `Σ_plog p·c_B(log p)p^{−s}` absolutely convergent on `Re s>1`; its identity with `−Σ_ze_zζ′/ζ(s−z)` plus a holomorphic correction and the first strip `Re ρ≤5/8` from the Lipschitz gap step (sign-free) leave no pole `1+z` with `Re z>0` [D from the corpus ingredients]. Landau's theorem, which the Lean proofs use for one-sided bounds, is not needed when the bound is two-sided.
- Elimination is sign-free: the gap method iterates by Lipschitz propagation; Turán–Vandermonde elimination at the exceptional rank on thick sets [L].
- Sign-free producers are capped: integrality reaches Chebyshev and acts exactly only on the torsion of the prime torus; phase-freezing Rouché copies reach the trivial separation bound; exponential sums reach VK; transcendence (explicit Baker) bounds the depth of a return polynomially in `1/δ` but Diophantine information of bounded height cannot exclude returns past the Kronecker scale [L/S].
- What falls: all of Σ; every one-sided receiver at the primes (Landau); the count door; the critical curve; the horizon receivers (Maass spectral theory, Krein forms); the index routes; the FE-rigidity classification (its proof uses positivity of the sinc-squared weight).

**The question.** *Are the logarithms of the primes collectively independent at constant precision?* Precisely (B97): for fixed `δ∈(0,1)`, is the first `t>0` at which every phase `t log p`, `p≤y`, lies within `δ` of `2πℤ` at least `exp(y^c)`, for some `c>0` — and the same for every heavy subset of the primes `≤y`? Equivalently, the Bohr set of the prime orbit at precision `δ` is empty on `[1,exp(y^c)]`; equivalently, the smooth Dirichlet polynomial `Σ_{p≤y}log p·p^{−it}` has no near-full value `≥(1−δ²)θ(y)` for `1≤t≤exp(y^c)`.

**Why it opens the path.**
- **It is the producer gap of the sign-free curve proof.** The crude count over ℤ fails exactly where the prime orbit returns: at a heavy early return a long prime polynomial is large and a zero can hide under it (proportional saving ⇔ no early heavy return) [L]. Over `𝔽_q` there are no returns to fear because the auxiliary vanishes exactly at every rational point; over ℤ exactness exists only on the torsion, and the orbit visits the torsion only approximately [L].
- **It must be a collective statement.** One linear form `Σν_plog p` of height `h` constrains returns only while `hδ<½`, and Liouville's integrality bound `y^{−h}` excludes returns only up to `y^{O(1/δ)}`; a rounded step system agreeing with `log p` on all forms of height `≤K` returns exactly at `T≥2πKy^K`, and it is a function field [L/S]. The question therefore asks for the geometry of the whole relation lattice of `(log p)_{p≤y}` (successive minima, Bohr-set counting with error terms), not for lower bounds of individual forms.
- **It is a statement about the zeros near the height.** By the reciprocity of returns, a heavy return at height `t` requires zeros near `t` of total weight `Σ_ρy^{|Re ρ−½|}/(1+|γ_ρ−t|)²≫√y`; the question is that no configuration of zeros below `exp(y^c)` imitates the pole at length `y` [L]. Return bounds are shared by `ζ(s−h)`; to reach ZAL from them the argument must use the FE about `Re s=½` [S].
- **Its consequences are proved receivers.** Constant-precision returns at `exp(y^c)` give proportional saving at length `(log X)^{2K}` at all heights (B46), the all-height sign past the size curve, and the exclusion of isolated zeros of depth beyond the visibility threshold [L/D]; with the sign-free elimination on thick sets they feed a thick crude count.
- **It is bracketed.** `log R(y,δ)` lies between `(log y)^{3/2−o(1)}` (VK) and `y/log y` (Dirichlet) unconditionally; under RH it is `≥c√(y/log y)` [L]. The question asks for any power of `y`.

**First rungs.** (i) Two primes: the depth law `t≥poly(1/δ)` from the explicit Baker bound [L]. (ii) A fixed number `k` of primes: explicit linear forms with exponent `≍k²log(kW)`, necessarily `≥k−1` [L]. (iii) `k≍(log y)^A` primes with explicit `k`-dependence. (iv) The passage from bounded height to collective counting: Bohr-set density of `k` logarithms with error terms uniform in `k`. (v) `𝔽_q[T]`: the Frobenius is exact; there are no returns to bound [L].

**Tests.** T1: implied by RH (RH bracket; reciprocity) [L]. T2: an inequality. T3: B46, the all-height sign, isolated-zero exclusion. T4: no finite rung. T5: fails for impure columns and for rounded orbits (function fields) [L/S]. T6: bounded-height certificates are refuted [L]; collective ones are not. T7: moves Π94, Π95, Π121, Π128, Π133.

**Limit.** It speaks about large heights; a finite layer at a fixed height is invisible to it. The finite stratum then needs the FE as a reciprocity acting on heights (Poisson, theta, Farey and Dedekind reciprocity), the one sign-free ingredient left unused.

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved [L].** The modular horizon is `SL₂(ℤ)\`(Rindler wedge of AdS₄); its resonances sit at the zeros of `ξ(2s)`; every seed rings down at its zero-free region; one cuspidal cavity function of Hecke eigenforms sees every resonance and RH ⇔ its energy rings down at `y^{¾−ε}`. The archimedean place is a scalar of mass `m²=−¾` in Euclidean AdS₃ restricted to one geodesic: the archimedean Frobenius is `2π√(mn)G_{1/2}(|log(n/m)|)`, the bulk propagator in the quantization `Δ=½`; `2πG_{1/2}=2πG_{3/2}+½φ_{1/2}`, the difference of the two quantizations being the spherical function `φ_{1/2}=sech(d/2)`; the pole of Weil's form is `(3/2)φ_{3/2}+½φ_{1/2}`, so in Weil's archimedean-plus-pole weight `4πG_{3/2}−3φ_{3/2}` the `Δ=½` piece cancels and only the `Δ=3/2` quantization remains. The FE pairs each resonance `s=ρ/2` with `s*=½−s̄=(1−ρ̄)/2`; the reflection Krein form evaluated at `s` and `s*` is PSD on the line and has exactly one negative square off the line; RH ⇔ every reflection Krein form PSD. The horizon's own Krein form at one resonance is blind; internal modular conjugation collapses to the centre; vacuum-fixing and half-sided modular realizations cannot carry `Q`; the dual side has no sign.

**The law, read physically [D].** A scalar in AdS₃ with `−1<m²<0` (here `m²=−¾`, inside the Breitenlohner–Freedman window) has two unitary quantizations, `Δ₋=½` and `Δ₊=3/2`, exchanged by a Legendre transform of the boundary generating functional (the double-trace flow). Weil's form uses one of them (`Δ₊`, after the pole cancels `φ_{1/2}`); the reflection Krein form compares the response at a resonance with the response at its FE partner. A pairing between the two members of an FE pair is what a Legendre/double-trace duality between two quantizations does to two-point functions, and positivity of two-point functions is unitarity.

**The question.** *Is RH the unitarity of the alternate quantization?* Precisely: is there a pair of boundary theories, built from the worldline scalar with `m²=−¾` in its two quantizations and from prime interactions at the times `log n` (never from the zeros), and a double-trace/Legendre map between them, such that (a) the two-point functions of the two theories on cavity sources are the seed transforms at a resonance and at its FE partner, and (b) the reflection Krein form of the cavity is the two-point function of the flowed theory? Then RH ⇔ reflection positivity of that boundary theory.

**Why it opens the path.**
- **It replaces a sign by an axiom.** Unitarity of a boundary theory with a positive-norm Hilbert space is structural; RH would be the statement that the arithmetic deformation stays inside the unitary window.
- **It is exactly what the operator no-gos leave.** The partner map would act between two theories (two quantizations), not inside one algebra: that is why internal modular conjugation collapses to the centre and vacuum-fixing partners collapse to square classes [L].
- **It has rungs.** (i) The archimedean sector: `G_{1/2}−G_{3/2}=½φ_{1/2}` and its cancellation by the pole [L]. (ii) Graph black holes: partner standard forms exist iff the hole is damped, and finite oscillator banks are positive iff every block is strictly stable [L]; test whether damped holes are exactly the couplings inside the window. (iii) The Narain AdS₃ partition function: modular invariant, every arithmetic pole retained, remainder with exactly the VK saving [L].
- **A negative answer is informative.** If no such pair exists for which the flow preserves the FE pairing, the physical reading reduces to the width axis (rates of one cavity energy).

**Calibration and risks.** Fakes (graph black holes with `t²>4q`) must fail through the flow leaving the window, not through the dynamics. A theory whose spectrum is the critical ordinates is a Hilbert–Pólya operator; the question is useful only if both theories and the flow are defined from the archimedean place and the primes alone.

**Second physical question (producer).** *Is the modular horizon the modular image of a confined system with real normal modes?* (B117): a unitary horizonless system with the worldline modes as free part and the primes as interactions, and a modular transformation sending its Euclidean correlators to the mirror-even response, so that every resonance `ρ/2` is the image of a real normal mode — universal damping as kinematics (BTZ and thermal AdS₃ are S-dual [C]).

## 2.8 If RH is a problem of topology or geometry

**What is proved [L].** Off the diagonal Weil's form is an adelic Green pairing: the pole minus `2πG_{1/2}` on the degree geodesic of `ℍ³` minus `log p((p−1)/√p)G^{T_p}_{1/2}` on the apartments of the trees `T_p`, every local Green function at the critical parameter and PD on its geodesic or apartment. Hyperbolic carriers at one place fail: twisted Green sums of groups with convergent Poincaré series at `½` are continuous ratio kernels seen from the end of the degree geodesic, while the primes jump; compact and finite-volume embeddings fail at clustering degrees or at the cusps. The atomic surface is not an Arakelov surface (the locked diagonal is the discriminant); the smoothed archimedean self-energy is logarithmic. RH ⇔ one side of Hasse–Weil for the smoothed Frobenius graphs at the prime degrees. Topology: the orientation cover over ℤ exists, its middle cohomology never vanishes and has weight `≥½`, weight `½` ⇔ RH; prime-vertex local indices sum to `1−M(N)` and are unbounded below.

**Geometric question.** *Is there an adelic carrier?* Precisely (B133): is there a discrete subgroup `Γ` of `SL₂(ℂ)×Π'_pPGL₂(ℚ_p)` (restricted product, or `S`-arithmetic with `S` growing) and an automorphic Green function `𝒢` at the critical parameter on `Γ\(ℍ³×Π'_pT_p)` such that on the degree configuration `x_n=(z_n,(v_{n,p})_p)` — the orbit of the split torus `diag(n,1)` through the base point — `𝒢(x_m,x_n)` is the archimedean-plus-torsion Frobenius intersection off the diagonal, and its regular part at coincident points (the Robin mass of the configuration) is Weil's diagonal?

**Why it opens the path.**
- **It evades both proved obstructions.** The one-place no-go fails because the primes must be carried by tree factors, which a product carrier supplies; the atomic no-go fails because the diagonal is a genuine Green potential of a quotient, not a locking of two dampings.
- **It converts the sign into potential theory.** Green functions of positive operators are PD kernels; a carrier would make Weil's form the energy of a configuration in a quotient, whose sign is controlled by the bottom of the spectrum of the quotient at the critical parameter and by its Robin masses.
- **It is the geometric face of the split-torus period.** Torus periods of Eisenstein series on `PGL₂(ℚ)\PGL₂(𝔸)` produce `ζ(s)ζ(s′)` (Hecke) [C]; the question asks whether the Green function, rather than the Eisenstein series, reproduces Weil's kernel along the same torus orbit.

**Tractability.** The archimedean factor is fixed (`ℍ³`, `G_{1/2}` and `G_{3/2}`), the finite factors are fixed (trees at the Ramanujan point), and the obstructions of the corpus give necessary conditions: the stabilizer of the degree end acts on the ratio alone; Poincaré convergence at `½` excludes parabolics in the archimedean factor; the diagonal must have order `N log N` on atoms. The first step is the one-prime case `S={p}`: a lattice in `SL₂(ℂ)×PGL₂(ℚ_p)` and the Green function on the product of `ℍ³` and one tree along one `p`-ladder.

**Topological question.** *Does the orientation cover over ℤ carry a Lefschetz theory?* Precisely (B106): the real fibres of `y²=disc F_n` record the sign of complex conjugation on the roots of `F_n=Π_{p|n}(X²+p)` (the archimedean Frobenius acting by `ω(n)` transpositions), as the factor-trace cover over `𝔽_q[T]` records the sign of Frobenius (Stickelberger). Is there a space with a correspondence (the dilations `n↦pn`) whose Lefschetz numbers are the centred counts `M(N)` and whose middle cohomology has dimension `O(N^{½+ε})` with bounded local indices? Over `𝔽_q[T]` the cover's middle cohomology vanishes [L]; over ℤ it has weight `≥½` [L]; the question asks for its dimension.

**Limit.** Over `𝔽_q` these structures come from a variety; over ℤ none is constructed. Heights over number fields give central-value signs, not off-line zeros [D].

## 2.9 New field for RH: arithmetic weight theory of Spec ℤ

**Goal.** RH as purity of the virtual motive of the zeros: every weight of `M=Σ_ze_zℤ(−z)` is `0`.

| Aspect | Content |
|---|---|
| What it is about | Deligne's proof of the Weil conjectures transported to Spec ℤ. The prime degrees play the extensions `𝔽_{q^n}`, the spline traces `2Re S(log p)` the point counts of `M`, the even tensor powers `M^{⊗2k}` the sheaves whose positivity is free. The field supplies the one piece the corpus lacks: an a priori bound on the abscissae of `L(M^{⊗2k},s)` that is uniform in `k`. |
| What it would be like | A theory of families of zero configurations with a monodromy, in which `ζ` is a special fibre and the generic fibre is pure, and a semicontinuity of weights under specialization. Analytic number theory organized as `ℓ`-adic cohomology: Landau's theorem in the role of the real pole of `L(F^{⊗2k})`, the gap iteration in the role of Weil's self-improvement. |
| Criteria it must meet | Reproduce Deligne's theorem on curves over `𝔽_q` (the finite-rank case, with Bombieri's twist replaced by the absence of real zeros). Use the Euler product and the FE (fail on the integer-norm one-off, which violates the Stepanov bound for every constant, on the `cosh` models and on the heat family). Respect the sampling boundaries: one Frobenius aliases, finitely generated monoids need attainment, the primes do not. |
| Questions it must answer | Which family carries `ζ` as a fibre with big monodromy — the gauge torus of unimodular multiplicative twists (Haar-a.e. fibre zero-free on `Re s>½` with natural boundary `½`), Dirichlet twists, the vertical shifts, or a deformation family that keeps an Euler product? What is the analogue of `H²_c=` coinvariants, the a priori control of the top pole of `L(F^{⊗2k})`? In which topology on the family are weights semicontinuous (Haar-generic exponent `½` against Baire-generic exponent `1` shows that the naive one fails)? |
| Tools it aims to develop | Families of Euler products with a monodromy action on their zero configurations; tensor-power L-functions `−L′/L(M^{⊗2k})=Σ_{z_1…z_{2k}}Πe_{z_i}(−ζ′/ζ)(s−Σz_i)`; uniform pole bounds from the FE of the fibres; sampling theorems at the prime degrees; a weight-semicontinuity principle. |
| Objects | The virtual motive of the zeros and its tensor powers; the smoothed Frobenius graphs at the prime degrees; the trace zeta `Σ_ze_zζ(s−kz)`; the gauge torus and its hull; sampling weights. |
| Language | weight, purity, tensor power, base change, sampling set, Stepanov side, twist, monodromy, specialization, semicontinuity. |
| Mechanisms | Built on: one side at the prime degrees ⇔ RH; uniform tensor moments ⇔ RH; Rankin square abscissa `2maxRe ρ`; the Stepanov side's blind set; a.e. purity on the gauge torus [L]. To discover: the a priori uniform pole bound and the semicontinuity of weights. |

**Main conjecture (uniform weights).** There is `A` with `Σ_{p≤N}log p·(2Re S(log p))^{2k}≤C_kN^{1+A}` for every `k`, proved from a family in which `ζ` specializes.

**Milestones.** M1 [L] RH ⇔ one side at the primes; RH ⇔ uniform tensor moments. M2 A family with a monodromy whose generic fibre satisfies the uniform moments. M3 Semicontinuity of the top weight in that family. M4 A sublinear bound `A_k=o(k)` for ζ (zero-free strips of every width). M5 RH.

## 2.10 New field for AAL: exceptional-layer theory of ζ

**Goal.** Prove AAL, or reduce it to the finite stratum, by a theory of how an isolated top layer of ζ interacts with the rest of the zeros; or construct the falsifying world.

| Aspect | Content |
|---|---|
| What it is about | The ¬AAL world as a mathematical object, in the way the Siegel-zero world is studied for Dirichlet `L`-functions: consequences of one isolated top layer for every other zero, for the primes and for the prime current, until they contradict an unconditional theorem or assemble into a consistent world. |
| What it would be like | A Deuring–Heilbronn theory for ζ. The top layer enters the explicit formula as a finite exponential sum `x^ΘT(log x)`; theorems are repulsion and attraction laws (a top layer pushes the remainder toward the line, or forces replicas at its own depth), proved from the exact identities that hold in the world. |
| Criteria it must meet | Use the Euler product and the FE together (every model with a finite layer lacks the FE; integrable FE defects force the primes). Couple the low layer to the high remainder (no scale-separated input decides any level of the dial). Fail on the two-scale `cosh` models and on the heat family. Recover the Dirichlet-`L` Deuring–Heilbronn phenomenon as its calibration. |
| Questions it must answer | Does ¬AAL force all but finitely many zeros onto the line (§2.5)? What is the law `Θ∞−½≤f(Θ−Θ₂,γ)`? Does the top quartet's coefficient-density floor at every base conflict with the prime-current passage at the observation scale? Does a single top quartet replicate at heights `≍kγ` through its resonant tower? |
| Tools it aims to develop | Explicit formulas with a finite exceptional subtraction; Turán power sums with one isolated term; positive kernels with the layer as a known term; the Gaussian prime current at rightmost zeros and on high strips; Bohr duality at sampling sets; coefficient-density laws of towers. |
| Objects | The finite top layer, its trigonometric polynomial `T`, the remainder configuration, the high zero-free strip, the prime current, sampling sets, resonant towers at base `π/γ`. |
| Language | exceptional layer, isolation gap, repulsion, attraction, replication, resonant tower, observation scale, masked layer. |
| Mechanisms | Built on: the rigid ¬AAL world; EFT's passage, multiplicity and rough-variance laws; the firewall and FE rigidity; the Stepanov side's blind spot = real zeros (Siegel calibration) [L]. To discover: an interaction law between the layer and the remainder that uses the FE. |

**Main conjecture (Deuring–Heilbronn law for ζ).** If ζ has an isolated top layer, every other zero lies on the critical line; hence AAL ⇔ B13.

**Milestones.** M1 [L] The finite-layer world (§2.3). M2 A graded repulsion law `Θ∞−½≤f(Θ−Θ₂,γ)`. M3 The extreme law: AAL ⇔ B13. M4 One quartet does not occur. M5 AAL.

## 2.11 New field for RH without positivity: collective Diophantine geometry of the prime logarithms

**Goal.** RH by a sign-free argument: a two-sided crude bound at the prime degrees, produced from the arithmetic of the vector `(log p)_{p≤y}`.

| Aspect | Content |
|---|---|
| What it is about | The prime orbit `t↦(t log p)_p` as a lattice problem: the relation lattice of the logarithms, its successive minima, the Bohr sets of the orbit and their density at constant precision. Transcendence bounds the depth of a return; this field bounds its breadth. |
| What it would be like | Geometry of numbers and exponential sums over smooth numbers, joined to sign-free elimination. Proofs count lattice points in Bohr sets with error terms uniform in the number of logarithms, and turn breadth bounds into bounds for long prime polynomials at all heights. |
| Criteria it must meet | No sign, no spectral decomposition, no Landau theorem: two-sided bounds and absolute convergence only. Beat the bounded-height cap (rounded systems agreeing on all forms of height `≤K` return exactly at `T≥2πKy^K` and are function fields). Reproduce the two-prime depth law and the Dirichlet upper law; fail on rounded orbits and impure columns; use the FE about `Re s=½` in the step from returns to zeros (`ζ(s−h)` shares every return bound). |
| Questions it must answer | How many `δ`-returns do the primes `≤y` have in `[0,T]`, with an error uniform in `π(y)`? What are the successive minima of the lattice of integer relations of `(log p)_{p≤y}` against a box of height `H`? How does the breadth of returns control the large values of `Σ_{p≤y}log p·p^{−it}` at constant precision? Does a breadth law give a two-sided crude bound at the prime degrees through the gap iteration? |
| Tools it aims to develop | Bohr-set counting for logarithms of primes; smooth-number Dirichlet polynomials as dual objects of returns; collective linear forms (many forms simultaneously, not one at a time); integrality at sign returns (`\|A(it)\|≥1−δL(F)`); zero estimates at returns uniform in the number of logarithms; Turán's second main theorem on thick sets of levels. |
| Objects | The prime torus and its orbit; return times `R(y,δ)`; heavy subsets; relation lattices; torsion points and their Galois orbits; integer auxiliaries; power sums. |
| Language | breadth, depth, return, Bohr set, relation lattice, successive minimum, heavy subset, freezing, sign return, two-sided crude bound. |
| Mechanisms | Built on: proportional saving ⇔ no early heavy return; depth law and breadth cap; reciprocity of returns (a return is a pole-imitating zero cluster near the height); Adams Frobenius exact on the torsion; Vandermonde elimination; the sign-free decision step (two-sided bound + absolute convergence) [L/D]. To discover: a breadth law at constant precision. |

**Main conjecture (breadth law).** For fixed `δ∈(0,1)` the first `δ`-return of all primes `≤y`, and of every heavy subset, occurs after `exp(y^c)` (B97).

**Milestones.** M1 [L] two primes (depth law). M2 Collective counting for `k≍(log y)^A` logarithms. M3 `log R(y,δ)≥(log y)²` (past VK). M4 `log R(y,δ)≥y^c`. M5 A two-sided crude bound at the prime degrees (RH).

## 2.12 New field for RH as AdS physics: arithmetic quantization duality of the modular horizon

**Goal.** RH as unitarity: the reflection Krein forms of the cavity are the two-point functions of a unitary boundary theory obtained by a double-trace flow between the two quantizations of the archimedean scalar.

| Aspect | Content |
|---|---|
| What it is about | The archimedean place is a scalar of `m²=−¾` on a geodesic of Euclidean AdS₃, with two unitary quantizations `Δ=½` and `Δ=3/2`; Weil's form uses `Δ=3/2` after the pole cancels the difference `½φ_{1/2}`. The modular horizon carries the zeros as resonances, paired by the FE. The field builds the boundary theories of the two quantizations with prime interactions and identifies the FE pairing of resonances with the Legendre duality between them. |
| What it would be like | AdS₃/CFT₂ with arithmetic sources: generalized free fields of dimension `½` and `3/2`, double-trace flows, Poincaré sums over `SL₂(ℤ)` (Eisenstein series as Poincaré sums of `y^s`), and unitarity bounds. Theorems are identities between partition functions and positivity of boundary two-point functions. |
| Criteria it must meet | Build everything from the archimedean place and the primes, never from the zeros. Reproduce the corpus identities `2πG_{1/2}=2πG_{3/2}+½φ_{1/2}`, the spherical compensation, the reflection Krein law (PSD on the line, one negative square off it), the cavity receivers and the Narain remainder. Avoid the excluded realizations (internal modular conjugation, vacuum-fixing partners, Borchers inclusions). Make graph black holes with `t²>4q` non-unitary. |
| Questions it must answer | Which boundary operator has the seed transforms at a resonance and at its FE partner as two-point functions? Which double-trace coupling relates them, and where does the BF window sit in arithmetic terms? Why does arithmeticity (no second place of `SL₂(ℤ)`) keep the coupling inside the window? What is the confined dual whose normal modes map to the resonances (B117)? |
| Tools it aims to develop | Arithmetic double-trace flows; Legendre duality of generating functionals with prime sources; Krein-space holography for the mirror-even channel; Rademacher expansions with arithmetic poles; unitarity bounds for arithmetically deformed generalized free fields. |
| Objects | `ℍ³` with the degree geodesic, `G_{1/2}`, `G_{3/2}`, spherical functions `φ_{1/2},φ_{3/2}`; the modular horizon, its seeds, odd cavity and Hecke cavity functions; reflection Krein forms; the Narain partition function; graph black holes. |
| Language | quantization, double-trace flow, Legendre duality, BF window, unitarity, reflection pair, resonance, cavity, seed, ringdown. |
| Mechanisms | Built on: the AdS₃ reading of the archimedean place, the spherical compensation, the reflection Krein law, sharp cavity receivers, the dual-side no-sign theorem, partner standard forms iff damped [L]. To discover: the duality map and the unitarity of its arithmetic deformation. |

**Main conjecture (arithmetic unitarity).** The reflection Krein form of the modular horizon is the two-point function of a unitary boundary theory obtained from the two quantizations of the archimedean scalar by an arithmetic double-trace flow.

**Milestones.** M1 [L] archimedean sector (`G_{1/2}−G_{3/2}=½φ_{1/2}`, cancelled by the pole). M2 One damped graph black hole as a unitary flow, one undamped as a non-unitary one. M3 The Narain partition function as a flowed partition function. M4 A universal positive decay rate (zero-free strip). M5 Unitarity (RH).

## 2.13 New field for RH as topology or geometry: adelic potential theory of Spec ℤ

**Goal.** RH as a positivity of energy: Weil's form is the renormalized Green energy of the degree configuration in an adelic quotient of `ℍ³×Π'_pT_p`; in the topological branch, as a dimension bound for the middle cohomology of the orientation cover over ℤ.

| Aspect | Content |
|---|---|
| What it is about | Every place of `Spec ℤ` carries a rank-one symmetric space at the critical parameter — `ℍ³` at `∞`, the Bruhat–Tits tree `T_p` at `p` — and Weil's off-diagonal kernel is the pole minus their Green functions along the split-torus orbit of the degrees. The field builds the global object: a quotient on which one Green function carries all places at once, with the diagonal as the Robin mass of the configuration. |
| What it would be like | Potential theory on products of hyperbolic spaces and buildings: `S`-arithmetic groups, automorphic Green functions at a fixed spectral parameter, capacities and Robin masses, energies of infinite configurations, and their renormalization by smoothing. Arakelov theory in which the archimedean fibre is `ℍ³` and the finite fibres are trees. |
| Criteria it must meet | Reproduce the adelic Green formula, the spherical compensation and the plastic sign law, the atomic diagonal of order `N log N`, the logarithmic smooth self-energy, and the genus `c_B(0)/2` of smoothed pairs. Respect the one-place no-go (hyperbolic carriers see only ratio kernels) and the atomic no-go (locked dampings give the discriminant). Calibrate on curves over `𝔽_q`, where the diagonal self-intersection is `2−2g`. |
| Questions it must answer | Which `S`-arithmetic lattice carries the configuration (B133)? Is the Robin mass of the configuration Weil's diagonal? Does smoothing lock the archimedean and tree divergences with a finite diagonal (B129)? What is the bottom of the spectrum of the quotient at the critical parameter, and how does it control the sign? Which correspondence on which space has the centred orientation counts as Lefschetz numbers (B106)? |
| Tools it aims to develop | Green functions on `ℍ³×Π_{p∈S}T_p` and their Poincaré series; Robin masses and capacities of degree configurations; smoothed locked dampings; Lefschetz fixed-point theory for the dilation correspondences on the orientation cover; weight filtrations of its cohomology. |
| Objects | `ℍ³` with the degree geodesic; trees `T_p` with their `p`-ladders as apartments; the split torus `diag(n,1)` and its orbit; `S`-arithmetic quotients; the 𝔽₁-zonotope and `ℙ¹_ℤ`; smoothed Frobenius graphs; the prime-quadratic family and its orientation cover. |
| Language | adelic carrier, local Green function, Ramanujan point, Robin mass, configuration energy, locking, archimedean Stickelberger sign, Lefschetz number, weight. |
| Mechanisms | Built on: adelic Green formula, spherical compensation, carrier no-gos, locked-damping discriminant, smooth self-energy, one side of Hasse–Weil at the primes ⇔ RH, orientation cover weight `≥½` [L]. To discover: the global carrier and its Robin mass; a Lefschetz theory for the cover. |

**Main conjecture (adelic energy positivity).** Weil's form on smoothed tests is the renormalized Green energy of the degree configuration in an adelic quotient, and that energy is nonnegative on primitive tests.

**Milestones.** M1 [L] adelic Green formula; carrier and locking no-gos. M2 The smoothed locked diagonal (B129). M3 A one-prime carrier on `ℍ³×T_p` along one ladder. M4 An `S`-arithmetic carrier for growing `S`. M5 Energy positivity (RH). Topological branch: archimedean Stickelberger sign [L]; a correspondence with Lefschetz numbers `M(N)`; a dimension bound for the middle cohomology.

## 3. The one big question: do almost all primes decide RH?

**Question (B132).** Let `Z` be a tempered zero configuration in the open strip without real zeros, and let `E` be a set of primes of relative logarithmic density zero, `Σ_{p∈E}log p·p^{−σ}=o(Σ_plog p·p^{−σ})` as `σ↓1`. *Does a one-sided crude bound `2Re S_Z(log p)≥−K` at every prime `p∉E` put every zero of `Z` on the critical line, without assuming that the maximal real part is attained?* For ζ: is RH equivalent to the arithmetic Stepanov bound `P(p)≤A(p)+K` for all primes outside a set of relative logarithmic density zero?

**What is proved [L].**
| Degree set | One-sided crude bound gives | Attainment needed |
|---|---|---|
| all primes, `p^k`, `n^k`, squares, any power-saving gap set | purity (RH for ζ) | no (gap iteration + Landau) |
| two-prime difference lags `log m−log n`, `m,n∈⟨p,q⟩` | purity (RH for ζ) | no (Kronecker density + continuity) |
| primes off a relative-density-zero set; primes in a residue class; `p^aq^b` | purity for attained tops; AAL for ζ | yes as proved; at `p^aq^b` attainment cannot be dropped (an actual tempered configuration with unattained top passes) |
| one prime's powers `p^a` | nothing (aliasing at `2πm/log p`) | — |
| any sampling set, under ZAL | the width law: `zeroWidth≤s` ⇔ `≥−Kp^s` | — |

**The exact content [D].** A set of primes of relative logarithmic density one may omit every prime in sparse logarithmic windows `[U_j,U_j+h_j]` with `h_j=o(U_j)`, i.e. multiplicative holes `x^{1+o(1)}`. The gap iteration needs power-saving gaps and breaks on the holes; Landau's theorem needs the one-sided bound on all scales. The question is whether an unattained top (depths `x_k↑Θ`, ordinates bounded below by local finiteness) can place all its negative values inside such holes. A Wolff tower must keep its dominant quartet nonnegative on all kept primes of its window; its phase `γ_klog p` equidistributes over the kept primes unless `γ_k` aligns them simultaneously, and simultaneous alignment on all primes of a window is what the full gap iteration excludes for tempered configurations. The answer is a quantitative competition between the holes that density zero allows and the Lipschitz propagation of the trace between kept primes. The realized two-Frobenii counterexample places its level `k` at a height `M_k=e^{O(√U_k)}` resonant on the `O(U_{k+1}²)` degrees of its window [L]; a level resonant on the `≍e^U/U` primes of a window needs, by Dirichlet, a height `≥exp(ce^U/U)`, its weight `≈M^{−8}` then cannot take over from the level below it inside the window, and a set of density one keeps `≍e^U/U` primes in almost every window [D]. This suggests the answer yes; it is not a proof.

**What either answer gives.**
| Answer | Effect |
|---|---|
| Yes | RH ⇔ the arithmetic Stepanov bound for almost all primes. Every one-sided bound on a density-one sampling set is an RH producer, not only an AAL producer: on the prime side ZAL is not a separate input. The common target of ACS, SRT, WL, HF and RW (through one Weil test per prime) admits an exceptional set of primes of density zero — the regime in which mean-value and sieve methods over primes operate. The split skeleton F1 loses its ZAL input. |
| No | A tempered configuration without real zeros and with an unattained top passes a density-one bound: density-one prime bounds are exactly AAL, the prime-side location of ZAL is a family of sparse multiplicative holes, every almost-all approach to the Stepanov bound stops at AAL, and RH needs control at every prime of a set with power-saving gaps. The boundary between AAL and RH on the prime side becomes a theorem. |

**Why this one.**
- **It is less hard than AAL, RH and quasi-RH.** It is an implication between properties of zero configurations, implied by nothing about the zeros of ζ (T1).
- **It acts on the largest family.** The Σ∩Π core (ACS, SRT, WL, HF, RW) and every AAL producer on the prime side (sampling sets, ZCG, BAG, IWT through F1) depend on it; it decides whether ZAL — a ≥qRH input with no producer — is needed on the prime side at all.
- **It is tractable with corpus objects.** The sampling theorems, the gap iteration, the Lipschitz law of the trace at width `a` and the Wolff-type constructions (positive-weight models at finite monoids; the spline-phase dominance lemma at the zeros of `B̂` and the realized two-Frobenii configuration [L]) are in Lean. One named obstacle: a Landau theorem for a Laplace transform whose integrand is bounded below outside a set of logarithmic density zero.

**First steps.**
1. Gap iteration with holes: propagate a lower bound from the kept primes to every scale outside the holes, with the Lipschitz constant at the current width.
2. Decide whether a Laplace transform of a function bounded below outside a set of zero logarithmic density can continue past its abscissa with a non-real singularity there; prove the Landau theorem in that setting or produce the obstruction.
3. If step 2 fails, build a tempered spline-weighted Wolff tower whose negative values lie in sparse multiplicative holes, using simultaneous Dirichlet approximation only on the primes outside the holes, and check temperedness and the absence of real zeros.

**Tests.** T1: a method question about configurations. T2: an implication. T3: the table. T4: no finite rung decides it. T5: calibrated on finitely generated monoids (fails), one Frobenius (fails), all primes (holds), two-prime lags (holds). T6: no refutation in Lean; the density-zero version with attainment is proved. T7: moves Σ138, Γ164, B126, B111, ZAL. T8: not a named problem; first step and obstacle named.

**Limit.** It decides how much of the prime side RH requires, not whether the bound holds; under a "yes" RH remains the arithmetic Stepanov bound for almost all primes.

### Alternatives considered
| Question | Effect | T8 verdict |
|---|---|---|
| Smoothed locked diagonal (B129, §2.4) | shapes the count/Hodge family | passes; family of routes smaller |
| Deuring–Heilbronn law of the top layer (B131, §2.5) | AAL ⇔ B13 | difficulty possibly of exceptional-zero type |
| Ground-state orthogonality on the critical curve (B104) | shapes Σ | passes; Σ only |
| Adelic carrier (B133, §2.8) | geometric realization | producer; large |
| Breadth law of returns (B97, §2.6) | sign-free producer | fails: past VK |
| Sampling-set bound, metric recurrence (B126, B127) | AAL | fail: contain AAL |
| Halving pairs (B125) | one eigenform receiver | difficulty unknown; adds a receiver only |
