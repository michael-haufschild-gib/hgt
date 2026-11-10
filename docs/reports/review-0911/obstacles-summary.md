# Obstacles summary — status quo

Companion to [route-obstacles.md](route-obstacles.md) (per route), [walls-ledger.md](walls-ledger.md) (Σ/Π/Γ) and [route-unification-ledger.md](route-unification-ledger.md) (faces of one problem). Corpus checkpoint: commit `43e39a9cec` (2026-11-09). Working log: `logs/review-0911-statusquo-research-3.md`.

Evidence: `[L]` Lean source, integrated; `[S]` Lean source unintegrated or unfinished; `[K]` Lean with transitive axiom audit; `[P]` paper proof on a pipeline card; `[D]` deduction, not a Lean theorem; `[N]` numerical, uncertified; `[C]` classical, not formalized. Sections 2.3–2.14 and 3 are interpretation and ideation; every untagged statement there is a proposal, not a result.

**38 live formulations; 9 candidates.** HJ→PA; BSH→CDC; FEL's BSY criterion→CTF. Candidates: APF, EGC, EWJ, FEL, IRK, MSC, RFHM, W1C, WBF.

Notation: `Θ=sup Re ρ`; `Θ∞=inf{σ≥½: finitely many zeros have Re ρ>σ}`; **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **Landing** (B138) ZAL ⇒ finitely many off-line zeros; **DH** ¬AAL ⇒ ZAL; **LinAt C** `Θ−½≤C(Θ∞−½)`; `c_B` the cubic-spline orbit correlation, `Re S=c_B`, `Re W(B±τ_vB)=2c_B(0)±2c_B(v)`; `Γ_n` the smoothed Frobenius graph of degree `n`; `P(d)` the smoothed von Mangoldt count in the window of `d`, `A(d)` its archimedean-plus-pole prediction, `c_B(log d)=A(d)−P(d)`; a **`√T` window** of primes is `{p: |log p−T|≤r√T}`; a set of log-degrees is **Bohr-dense** if beyond every bound it approximates every finite family of phases; `G_s(d)=e^{−(s−1)d}/(4π sinh d)` on `ℍ³`; `G^{T_p}_s` the Green function of the Bruhat–Tits tree; `L_a(s)=ξ(s+a)ξ(s−a)` the symmetric shift; `χ_x` a point of the gauge torus of unimodular multiplicative twists, `T_x(u)` its window trace; `Δ_g` the Gram-coupled locking defect; `A_k` the exponent in `Σ_{p≤N}log p(2Re S(log p))^{2k}≪N^{1+A_k}`.

## 1. Big picture

### 1.1 One inequality per prime, at sparse local windows
The three wall families have one common minimal face [L]:

  RH ⇔ `c_B(log p)≥−K` for every prime ⇔ `c_B(log p)≤K` for every prime ⇔ `P(p)≤A(p)+K` ⇔ `Re W(B±τ_{log p}B)` bounded below at every prime ⇔ `|c_B(log p)|≤K` (sign-free).

`c_B(log p)` is the spline-smoothed PNT error in a fixed multiplicative window around `p`; its Weil energy `2c_B(0)+2c_B(log p)` is the defect of the effective class `Γ_1+Γ_p`. The growth exponent reads the width: zero width `≤a` ⇔ `c_B(log p)≥−Kp^a` ⇔ `≤Kp^a` ⇔ `|c_B(log p)|≤Kp^a`. Unconditionally `|P(n)−A(n)|≤C√n·exp(−(log n)^{3/5}/(10⁸log log n))` [L].

**The face is local in scale.** For every `r>0`, RH ⇔ the one-sided bound holds at the primes of arbitrarily late windows `|log p−T|≤r√T`, i.e. on `[xe^{−r√log x},xe^{r√log x}]` along any sparse sequence of scales `x` [L]. The proof needs neither attainment nor a Dirichlet series: three-point probability averages annihilate one reflected quartet each with additive Gaussian cost; a late tail of such averages keeps one chosen zero and deletes all but finitely many; the surviving finite spectrum has bounded-gap negative excursions of exponential size, against exponentially small leakage from `√T` windows; the prime-gap bound `x^{2/3}` transfers the bound to the primes and the width iterates `½→1/6→0` [L]. For ζ the deletion cost of every prefix is `≪|s|log²H+s²log H/H`, and the leakage from windows of radius `C·log²T` is exponentially small; the RH criterion on those windows is not assembled [L]. With δ-separated ordinates bounded windows of length `80/δ` decide [L]; an impure configuration bounded below on windows of unbounded length carries near-coincident ordinates [L].

**Samples.** Decisiveness is compactness, not density or gaps: decisive prime samples exist with arbitrarily large gaps, prime-power samples of zero convergence exponent exist, and every power-saving gap set decides [L]; Bohr-dense sets decide attained tops (lower side), attained tops with real zeros (upper side), and give `Θ−½≤max(s,Θ∞−½)` from growth `e^{su}` [L]; density-zero exceptions, very smooth degrees and finitely many Frobenii admit unattained tops; one Frobenius aliases [L].

| Sample of degrees | One-sided bound gives | Evidence |
|---|---|---|
| all primes, `p^k`, `n^k`, squares, any power-saving gap set | RH | [L] |
| primes of arbitrarily late `√T` windows (any `r>0`) | RH | [L] |
| primes off `O(X^α)` or short-window-sparse exceptions | RH | [L] |
| gappy configuration-adapted prime samples; prime powers of zero convergence exponent | RH (not explicit) | [L] |
| two-prime difference lags `log m−log n`, `m,n∈⟨p,q⟩` | RH | [L] |
| windows of length `80/δ` | purity for δ-separated configurations | [L] |
| Bohr-dense sets (sampling weights, long intervals, runs of integers) | AAL; with ZAL RH | [L] |
| primes off a relative-density-zero set; a residue class; `p^aq^b` | AAL for ζ; unattained tops pass off density-zero sets | [L] |
| very smooth degrees; degrees of finitely many primes | nothing without attainment | [L] |
| one prime's powers | nothing (aliasing) | [L] |
| shrinking windows `[x,x+x^θ]` on super-lacunary scales | nothing | [D] |

### 1.2 Deligne's argument over ℤ: every step except the uniformity, and the family step meets the jump at ζ
The traces `2Re S(log p)` are the point counts of the virtual motive `M=Σ_ze_zℤ(−z)` of the zeros. Positivity of even tensor powers is free; the abscissa of the `2k`-th tensor series is exactly `1+2kb` at an attained top `b`; RH ⇔ `A_k=o(k)` [L]. Künneth: every constituent of `M^{⊗m}` is a Tate twist `ℤ(−z₁−…−z_m)` with a pole, so `M` is geometrically constant and the analogue of `H²_c` is the whole tensor power [L]. The Rankin square has abscissa `2maxRe ρ`; the absence of real zeros of ζ plays Bombieri's twist; the gap iteration and the Laplace rate theorem play Weil's self-improvement; base change is the degrees `n^k` [L].

Deligne gets uniformity from a family. The gauge torus of twists is such a family: big monodromy (`∫|Σa_pχ_x(p)|^{2k}≤k!(Σ|a_p|²)^k`), uniform generic weights, Gaussian generic Frobenius, and ζ's vertical family `x_t=(p^{it})` is Haar-equidistributed at every fixed degree with the generic moments below the square-root scale [L]. But ζ is the **jump fibre**: it carries the pole (`|T_0(log p)|≥c√p`), the trace-constant sets are closed and Haar-generic yet none meets a neighbourhood of ζ, Baire-generic fibres have exponent `½` while Haar-generic fibres have exponent `0`; the edge divisor of every fibre is read by pretentious distances and the jump at ζ is one simple pole [L]. Exact monodromy transfers to a single fibre only the trivial bound; summable Euler deformations keep the zeros and form a Haar-null class [L]. Deligne's family step over ℤ needs a family in which the jump at ζ is the pole alone and the pole-subtracted traces specialize (B142).

### 1.3 RH is three atoms; AAL is three atoms
For every zero configuration [L]: purity ⇔ ZAL ∧ AAL ⇔ **ZAL ∧ B13 ∧ Landing**; **AAL ⇔ B13 ∧ Landing ∧ DH**; existential linear AAL (`∃C LinAt`) ⇔ B13 ∧ Landing; extreme DH ⇔ Landing ∧ DH; no two of B13, Landing, DH fail together, so a failure of AAL lies in exactly one sector. The strict dial `Pure ⊊ AAL ⊊ LinAt C₁ ⊊ LinAt C₂ ⊊ (∃C LinAt) ⊊ B13` holds with explicit separating configurations [L]. For ζ: **RH ⇔ ZAL ∧ B13 ∧ Landing** [L].

The atoms have distinct characters:
- **ZAL** is at least quasi-RH.
- **B13** contains the exclusion of a single off-line quartet (a Landau–Siegel-type exceptional-zero problem).
- **Landing** is a tail law, undecided below every height, implying neither quasi-RH, ZAL nor B13; for ζ it has eleven equivalent forms: eventual Hadamard positivity uniform up to the line; a height threshold `hadamardThreshold σ` bounded as `σ↓½`; finite Krein–Langer index of `K_ζ` (or on the `{2,3}` lattice) under ZAL; bounded heat counts, slice positivity, the filtered central-gap budget, finite odd bound states, the line above a height, each under ZAL [L].
- **DH** is AAL on `¬ZAL` worlds and off the RH path; AAL(ζ) ⇔ DH(`L_a`) for every `a>0` [D from L].

Equivalently on the prime side [D from L]: under ZAL, `ψ(x)−x` is, for each `ε>0`, a finite exponential sum `S_ε` plus `O(x^{½+ε})`; landing says the sums `S_ε` stabilize as `ε→0`, and B13 says the stable sum is empty.

### 1.4 What decides the atoms, and what cannot
- **Positive sign calibration.** The Lagarias–Suzuki constant term `Λ(2s)Y^s+Λ(2s−1)Y^{1−s}`, `Y≥1`, has no non-real zero off the line. The corpus proves this without truncated Eisenstein series: a Schur quotient, the pole's index-one defect and conjugation give `InfiniteRankPurityTheory.lineLaw`; at most one real exceptional zero lies right of the line (`constantTerm_zero_subsingleton`) [L*]. A sign route must recover this theorem, including its allowance for real exceptional zeros.
- **Two scales.** No property of the zeros above a height, or below a fixed height, decides B13, any linear law or AAL; landing is a tail law, and no property below a fixed height decides it [L].
- **Analytic shape.** FE, order one and reality admit every finite top layer and remainders approaching the line: an entire `G(1−s)=G(s)` of exponential type with off-line quartets `½±δ_n±i(n+1)²`, `δ_n↓0`, satisfies ZAL and violates landing [L].
- **Euler products without FE.** Positive integer-norm Euler products with linear counting, continued across `Re s=½`, carry a finite off-line layer (one-off: violates B13), an isolated top over a remainder at positive abscissa (two-scale: violates DH), and a top over remainders approaching the line (violates landing while satisfying ZAL, B13, DH) [L]. Each atom needs the FE and the Euler product together.
- **Family uniformity.** A finite-stratum law valid for every heat deformation `H_t` is RH; each `H_t`, `t>0`, has finitely many non-real zeros (Ki–Kim–Lee) while off-line zeros of ζ make the collision mass diverge as `t→0⁺`; among `Φe^{−τx²}` only `τ=0` has an absolutely convergent Dirichlet series [L].
- **Temperedness.** The symmetric shifts `L_a` keep FE, reality, order one, an Euler product with nonnegative `−L′/L` coefficients and the absence of real zeros, and violate ZAL unconditionally [D from L]: every ZAL input must use the coefficient size of ζ.
- **No Siegel regime.** Classical Deuring–Heilbronn holds for a real zero of a quadratic `L(s,χ)` with a constant uniform in conductor, height and zeros [L]; every pair of zeros of ζ has `(1−Re ρ₁)log(|Im ρ₁||Im ρ₂|)≥1/58`, so a top layer never nearly cancels the pole and the classical mechanism has nothing to act on [L].
- **FE rigidity.** A countable Beurling system whose theta function satisfies Riemann's FE up to a measurable polynomially bounded `L¹` or `L²` defect is the rational primes, with zero defect [L].
- **Positive annihilators.** Nonnegative two-prime polynomials annihilate every finite zero set; positivity of coefficients prices zeros, never excludes them [L/S].
- **Random models.** Haar-a.e. and fair-coin-a.e. Euler products are zero-free on `Re s>½` with natural boundary `½` [L]; all but `o(T)` zeros of ζ lie near the line [C]. Off-line zeros of ζ, if any, occupy a density-zero set of heights, and every in-law statement (vertical equidistribution, Gaussian Frobenius, conditional tail laws, universality) is blind to them [D]. The atoms are pointwise departures of ζ from its random model.

### 1.5 The finite-layer world
Under ¬AAL there is an isolated top over an infinite remainder, `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})` with `T` a unique finite trigonometric polynomial, syndetic lag excursions at every base, and a positive-density set of primes with `c_B(log p)<−Kp^a` for every `K` and `a<Θ−½` [L]. Its exact identities [L]:
- Gaussian prime current: the raw current passes to `−ζ′/ζ` on high strips; at a rightmost zero it reads `−m_ρ/2`; head-conditioned rough variance is head mass × rough mass; prescribed prime phases recur in every high dyadic window with the continued rough current at its variance.
- Exponential damping: the corrected current over the top Gaussian mode tends to the finite wave `−Σ_top e^{πγ/4}e^{iγ(at+log(t/2))/2}` with sharp recurrent envelope; one positive top ordinate makes it diverge.
- Filters: fixed height shifts become characters of the top ordinates and polynomial filters recover each top multiplicity in every late window; geometric damping changes multiply each Mellin mode by an exponential character, so prime-only filters cancel the pole and any finite set of modes with the remainder retained; at damping steps `h=e^{−κt}` a degree-`d` filter reads a top zero and grows when `dκ<a(β−σ)/2−π/4`.
- Euler bound: the absolutely convergent Euler series bounds the complete filter by `Ch^d(1+|t|)^de^{at(c−σ)/2}` for every `c>1`, forcing decay when `dκ>a(1−σ)/2`. Since `β<1` the detection and decay ranges are disjoint.
- Masking: a remainder zero at the observation height dominates the top for `π/(2(β−σ))<a<π/(2(β−β_r))` and is masked above.
- Height: the FE reflects every height to itself; escaping translates bounded on a domain meeting `Re s>1` stay right of `½`.

The identities are mutually consistent: every filtered current is the filtered zero sum (explicit formula), and an upper bound at an abscissa `c<1` is a statement `Θ∞≤c` about the remainder [D]. A contradiction needs an inequality that the explicit formula does not imply.

### 1.6 Exactness over ℤ lives on the torsion; the prime orbit has only dilations; breadth is proved to the VK height
The exact Frobenius of integer auxiliaries is the Adams operation `ψ_aF=F(u^a)`: dilation `t↦at` on the prime orbit, Galois action on torsion points [L]. Integrality creates no zeros at returns; exact order costs the degree; the minimal auxiliary vanishing at the fixed points of all `Γ_n`, `n≤N`, has log length `ψ(N)` and every auxiliary with the same vanishing is at least as long; RH ⇔ `ψ(N)≤N+C√N log²N`; polynomial Stepanov syzygies have sharp cost `p_min^{qr}` [L]. Polynomial, integral, rational and real rational self-maps preserving a finite or the full prime orbit are Laurent Adams maps; scalar endomorphisms of a finite prime-logarithm lattice are ℤ [L]. The only exact Frobenius-like symmetries of the prime orbit are the integer dilations. On the graded divisor carrier no finitely generated ℤ-lattice is stable under three prime Frobenii [L]: an integral cohomology of the zeros has infinite rank.

Returns of the primes: transcendence bounds their depth (`t≥poly(1/δ)` for two primes); bounded-height Diophantine information stops at the Kronecker scale (rounded systems are function fields); heavy subsets at precision `δ≤1/20` do not return while `log t≤(log y)^{3/2−ε}`; a strip of depth `h` gives `log t≥c·y^{1/2−h}`; absolute large values force heavy returns at dilated heights; a return at height `t` is a zero configuration near `t` imitating the pole [L]. Collective counts: returns of `k` prime logarithms at precision `1/(2N)` have measure `≤(5π/2)4^k max(T/2,Δ^{−1})/N^{k−r+1}`, and weighted heavy returns `≤(5π/2)max(T/2,δ^{−1})e^{−W/(8M)}`, with hereditary rank floors and Hall-matched coordinates [L]. The floor `δ` grows with the number of primes: the counts are effective only from heights comparable to the Dirichlet return scale [D].

### 1.7 The window sign is one scalar flow; the critical curve adds one orthogonality
RH ⇔ `Ψ=½log H₁` locally bounded ⇔ `a*(ζ)=⊤` ⇔ `λ*(c)→0` [L]. At `R=c⁸/log N`: `R_c=R_PSD=R_polar=R_halfline≤R_prim=R_high=W`; every threshold `=⊤` ⇔ RH; under ¬RH a unit half-line ground state lives at finite `W`, and finite `R_polar=W` forces it to be polar-orthogonal; no countable square-bounded family of holomorphic multipliers dominates the depleted kernel [L].

### 1.8 The theta wall is ζ on the critical line
All ranks reduce to the adaptive head `M(b)=⌈|b|/2+B⌉`, whose leading term is `|ζ(½+ib)|²+O(|ζ(½+ib)||b|^{−½}+|b|^{−1})` [L].

### 1.9 The near-line wall is the dark range
Near-unit mollified moments need `log N≥log²T/(6K₀)`; an Euler mollifier reaching them uses every prime up to `≍log²T`; conditional tail laws stop at the Kronecker scale; past the height long mean values are counts of prime pairs at multiplicative distance `≲1/T`, of exact order `X²` [L].

### 1.10 The surface of Spec ℤ: an adelic Green pairing at every place's tempered edge; the diagonal
Off the diagonal Weil's kernel is the pole minus the Green functions of all places at the critical parameter [L]: `2πG_{1/2}(d)` on the degree geodesic of `ℍ³`, `d=|log(n/m)|`, and `log p((p−1)/√p)G^{T_p}_{1/2}(k)` on the `p`-ladders, the tree Green function at the Ramanujan point; `2πG_{1/2}=2πG_{3/2}+½φ_{1/2}` and the pole is `(3/2)φ_{3/2}+½φ_{1/2}`, so the archimedean compensation is spherical and changes sign at the plastic ratio. Every place carries a propagator decaying at rate `½` in its own distance — the edge of the tempered range; the symmetric shift `L_a` moves every place to rates `½±a` [D].

The diagonal [L]: locked atomic dampings converge on the diagonal to the torsion self-intersection (the discriminant), never PSD; on smoothed packets scalar locking converges iff discrete mass equals `L²` mass and keeps the discriminant; **ordered Gram coupling** of the logarithmic translates gives, for every compact C² packet including overlaps, the finite limit `Weil(f)+Δ_g`, `Δ_g=primeSum(f)−atomicWeilForm(N,y)+(c−2γ₀)‖f‖²−Σy_n²selfIntersection(n)`; the **prime unit** identifies `p^k` with `p^{k+2}` and carries no invariant scalar or unitary Frobenius kernel, while two positive parity fibres over unitary characters recover every tree Green entry; a **discrete adelic quotient** by the rational split torus in `SL₂(ℂ)×Π'_pSL₂(ℚ_p)` carries the square degrees, and after Weyl conjugation the original degree points, as distinct points. No Green function or Robin identity on this quotient is constructed. On smoothed graphs RH ⇔ `c_B` is a counterterm-free pointwise limit of PSD kernels; neither channel alone is one. The sign sits in the diagonal, and local Robin data give the discriminant.

### 1.11 The count on one ray per prime
A count law has a quadratic half (a nondegenerate Born rule, the FE) and a count half (damping) [L]. Over ℤ the quadratic half holds, RH ⇔ `Q` on integer probes is the Tate limit of an `ℕ`-count, and `Q` is not integer-valued [L]. The count is needed only on one effective ray per prime, on any power-saving gap set, or with ZAL on runs of integers [L]. Arithmetic counts defined before the form exist in quantity; none has Tate limit `δ_p(1,1)` [L]. λ-ring effectivity reduces to the defect floor: one Hecke or Adams correspondence replaces the ample axiom, and every stable Riemann–Roch cone forces it [L].

### 1.12 Production, Farey, the nerve, the prime vertices and the orientation cover are the Mertens level
Producer rates equal the Mertens level; Farey discrepancy ⇔ RH; `M(N)=−χ̃` of the prime-star nerve; `Σ_p` prime-vertex indices `=1−M(N)`; the orientation cover over ℤ has centred count `M(N)`, weight `≥½` unconditionally and weight `½` ⇔ RH; over `𝔽_q[T]` the factor-trace cover has exactly `qⁿ` points [L]. The damped Möbius energy is bounded or its residue classes equidistribute [L].

### 1.13 The horizon has complete and sharp receivers
The modular horizon is the quotient of the Rindler wedge of AdS₄ by `SL₂(ℤ)` [L]. Seeds enter only through `Λ_F(ρ/2)`; one cuspidal cavity function of Hecke eigenforms sees every right resonance, and RH ⇔ its energy rings down at `y^{¾−ε}`; one Hecke eigenform is blind exactly at halving pairs and Shimura zeros; the reflection Krein form is PSD on the line and has exactly one negative square at each off-line zero; RH ⇔ every reflection Krein form PSD; the dual side has no sign; internal modular conjugation collapses to the centre; vacuum-fixing and half-sided realizations cannot carry `Q` [L]. Every horizon observable is on the width axis.

### 1.14 Lefschetz identities
The Ξ explicit formula is Deninger's distributional Lefschetz formula, and it is the operator trace of the Meyer source flow on its faithful Hilbert completion; big and rational Witt rings with Frobenius and Galois descent are formalized [L]. The trace formula exists; its positivity is RH.

### 1.15 What is ruled out
| Mechanism | Verdict | Evidence |
|---|---|---|
| Markov, Perron, sign-gauge balance past `e^{−3/4}`, `log ρ` | refuted; Beurling–Deny exactly on plastic windows | [L] |
| Size-only payment of primes | ends before half-width `21/40` | [L] |
| Floor tower as aperture producer | stays below `0.3621` | [L] |
| Weighted Gårding on the whole horizon; physical tearing | false on deep atoms; Schur ratio `4/13` | [L] |
| Universal holomorphic multipliers for the critical depleted kernel | excluded on the off-line strip | [L] |
| Uniform logarithmic Gamma reserve; fixed theta heads; summable absolute pair majorants; compact cores; positive Laplace representations | excluded | [L/S] |
| Product certificates in Euler coordinates past `Re s=1` | cannot cross | [L] |
| Parabolic structure as selector of `t=0`; family-uniform finite-stratum laws; heat finiteness at `t>0` as landing | blind; RH-strength; does not pass to `t=0` | [L] |
| Asymptotic or local-below zero statistics as inputs to any atom | cannot decide | [L] |
| FE, order one and reality as exclusion of a finite layer or of approaching remainders | `cosh` and approaching models | [L] |
| Positivity, Euler products, integrality, linear counting, continuation, reflection, positive Hecke and two-prime polynomials as any atom | one-offs, two-scale and approaching integer-norm products; annihilators price, never exclude | [L] |
| Nonclassical Beurling systems with an `L¹`, `L²` or no FE defect as fakes of ζ | none exist | [L] |
| One-sided bounds off a density-zero set, at the very smooth degrees, at finitely many Frobenii, at one Frobenius, without attainment | unattained tops pass; aliasing | [L] |
| Power-saving gaps, positive density or global coverage as the shape of a decisive sample | gappy samples, zero-convergence-exponent samples and sparse `√T` windows decide | [L] |
| Graded or extreme repulsion from Euler product, integer norms, linear counting and continuation; the classical Deuring–Heilbronn mechanism for ζ | integer-norm models; no Siegel regime | [L] |
| Euler-region bounds for damping filters as exclusion of a finite layer; exact identities of the finite-layer world as a contradiction | disjoint ranges; consistent identities | [L/D] |
| Deligne's family step through gauge twists; exact monodromy as a fibre bound; Euler deformations as zero-moving families | ζ is the jump fibre; trivial bound; isozeric | [L] |
| In-law statements (equidistribution, Gaussian laws, universality) as zero locators | random models are zero-free right of `½` | [L/D] |
| Density statements on levels of a tower; elimination without well-foundedness | rank barrier; Wolff towers | [L] |
| Exact returns as a Frobenius; norm-majorant Rouché copies; integrality at returns; nonidentity orbit maps with two fixed points | one fixed point; trivial separation bound; countable zero heights; Laurent Adams rigidity | [L] |
| Bounded-height Diophantine certificates against returns; return bounds as uniform routes to ZAL | Kronecker-scale cap; uniform route refutes the return conjecture | [L] |
| Slow-return bounds on discs crossing `Re s=½`; whole-quadrant boundedness | power growth forced; impossible | [L] |
| Schur, `C*`, KMS, reflection positivity, internal modular conjugation, vacuum-fixing partners, Borchers inclusions as zero locators or carriers of `Q`; the resonance Krein form; dual-side signs | blind; central collapse; no eigenvalues; infinite index; one-sided = two-sided | [L] |
| One Hecke eigenform as a complete receiver | halving-pair and Shimura blindness | [L] |
| Wave dynamics, flux, unitarity, Hecke, FE at genus two, first-level counts, integrality as universal damping; linear counts; `Q` or an integral trace form as its own count | fakes carry all; degenerate; not integer-valued | [L] |
| Narain remainder past `¾`; sharp sources at the RH rate | impossible; need Möbius × circle cancellation | [L] |
| Integer stencils independent of Möbius; exact Stepanov auxiliaries over ℤ | rate = Mertens level; count = Chebyshev | [L] |
| Fixed-point localization in cardinality; persistence | primes fixed with unbounded indices; `s`-independent | [L] |
| Renormalization as a source of sign; finite integral cohomology for the zeros | any form arises; no finitely generated Frobenius-stable lattice | [L] |
| Metrics on `ℙ¹_ℤ`, toric pairings, continuous Hecke kernels, finite-rank kernels, hyperbolic quotients with convergent Poincaré series, compact or finite-volume embeddings as carriers | excluded | [L] |
| Locked atomic dampings; separate positive channels; scalar locking on smoothed packets; scalar or unitary descent under the prime unit | discriminant diagonal; divergence; mass balance only; ladder collapse | [L] |
| Thermal averaging (primon gas); shrinking-mesh pure Euler approximants | Euler factors at real points `>1`; Euler abscissa escapes | [L] |

## 2.1 Tasks that are just work

Difficulty is established only where a known argument exists; `(unverified)` marks the rest. None of these decides RH.

### Finite verification
| # | Task | Routes | Basis |
|---|---|---|---|
| A1 | Lean-certified `RHVerifiedThrough T` past 67 with zero location (Turing count), first `T≈10²–10³` | all rungs | `hardySEM` sign chains; Fejér budget |
| A2 | Numeric values of `windowHeight`, `xiMassHeight`, `heatGridHeight`, theta `D` | window routes, TH, LA, HCF | explicit definitions |
| A3 | Two-weight membership past `a₀`: odd unit window, `log 2`, `½log 5` | RW, OWU, EWU, ACT, SWC, HF | A1–A2 or rigorous Galerkin |
| A4 | Theta rank 15 and beyond at every `0<a≤½` (unverified past 14) | TH | radius-12 power core, height 67 |
| A5 | Lean certificate of the center-tail failure | TH | finite computation |
| A6 | Cone widths past `c=0.66`; Lévy margins at `½log 3` | PBAP, ACS, RW, CHT | convex programs |
| A7 | Certificates on the nine anti-diagonals (unverified; statement unsettled) | ACT | finite case analysis |
| A48 | Hasse–Weil test of smoothed Frobenius pairs at verified scales | SOSZ, HF, ACS | window rungs |
| A56 | Explicit rung: `RHVerifiedThrough T` ⇒ `Re W(B±τ_{log p}B)≥0` for all `p≤P(T)` (unverified) | SRT, ACS, HF | supports of the two-bump tests |

### Critical curve
| # | Task | Routes | Basis |
|---|---|---|---|
| A9 | Explicit `K₀`, eighth-root horizon, logarithmic profile, Beurling schedule | HF, SRT, AIP, ACS, SC | proved limits |
| A13 | Near-gcd charges and periods beyond `M₀(N)` (unverified) | AIP, HF | gcd-defect coercivity |

### Prime side: samples and scale locality
| # | Task | Routes | Basis |
|---|---|---|---|
| A58 | Effective gap iteration: explicit constants from a one-sided or two-sided bound to an explicit width after each step (unverified) | ACS, SOSZ, CDGeo | first strip `5/8`, Landau step, two-sided width step |
| A59 | Short-interval primes in a fixed residue class from the zero-density estimates of `L(s,χ)` [C]; then the residue-class Stepanov bound is an RH criterion | ACS, SRT, WL | `powGaps_primes` |
| A64 | RH criterion on prime windows of radius `C·log²T` for ζ: combine `infinite_zeta_logSquare_floor` with the prime-gap transfer (unverified) | ACS, SRT, WL, HF | log-square leakage; `prime_squareRoot_windows_transfer` |
| A65 | Two-prime local criterion: lower bounds for `c_B` on the two-prime difference lags in arbitrarily late `√T` windows ⇔ RH [L*] | SRT, ACS | `ScaleLocality/TwoPrimeLocalWindows` |
| A66 | Sign-free local decision: the `√T`-window criterion from two-sided bounds with signed or complex deletion filters of summable `ℓ¹` cost, without positive averaging (unverified) | ACS, CDGeo | `TwoSidedGapIteration`; positive deletion |
| A71 | Local tensor moments: uniform-in-`k` moments of `c_B` over the primes of `√T` windows ⇔ RH (pointwise bound by `k→∞`) [D] | ACS, AWT | `riemannHypothesis_iff_prime_squareRoot_windows` |

### Exceptional coordinate
| # | Task | Routes | Basis |
|---|---|---|---|
| A47 | Explicit constants of the one-quartet world: supercritical speed, envelope window, tower windows at base `π/γ` (unverified) | ZCG, WL, IWT, ELT | envelope and dichotomy theorems |
| A50 | Shifted Jensen finite-stratum law ⇒ RH; cosine law gives RH ⇔ ZAL [L*]. Cosine law alone ⇒ RH remains open | ZCG, PTR, LA | exact Pólya coefficients; cosine still needs finiteness near zero |
| A67 | Dominant-ordinate divergence: the corrected current's norm tends to infinity when one ordinate's grouped Gamma mass exceeds the mass of the remaining ordinates [L*] | ZCG, ELT | `ADominantOrdinateForcesCurrentDivergence`; multiplicities included |
| A68 | A landing calibration with ζ's Gamma factor and Riemann–von Mangoldt counting (unverified) | ZCG, ELT, IWT | `exists_approachingModel_not_landingLaw` |
| A37 | Resonator mean of `\|ζ\|²` with resonators growing below the Kronecker scale (unverified) | BAG, ZCG, PTT | fixed-resonator limit |

### Theta, horizon, counts, production, descent, topology, diagonal, FE rigidity
| # | Task | Routes | Basis |
|---|---|---|---|
| A16 | Numerical `r,m,q` for `a≤1` [N] | RW | Galerkin |
| A18 | Twisted second moments past `21/50` [C] | WD | raises rate `2θ` |
| A19 | Heat horizon toward its method floor | ZCG, AES | profile margin |
| A20 | Jensen rung toward the saddle scale (unverified) | LA, FFP | saddle identity |
| A21 | Census items; logarithmic two-point Chowla [C] | MC, ACS | classical |
| A24 | Certified scans of `S_S`; brackets for `S*(a,b)` | TH | column calculus |
| A26 | Weyl asymptotic `N(Λ)∼Λ/12` [C] | PM, BHR | order `N(Λ)≍Λ` |
| A28 | Reciprocal-quadric traces = vanishing-cycle Frobenius traces (unverified) | ACS | exact projective counts |
| A30 | Best stencil exponent under RH in `[¼,½]` (unverified) | WL, MC | quarter rate, half scale |
| A33 | Fourier coefficients of the cubic residue [C] | MC, MMD | nonzero residue |
| A41 | Count law for every curve over `𝔽_q` (Bombieri–Stepanov), first case plane quartics [C] | ACS, PM, CTH | crude-bound self-improvement |
| A42 | Uniform Gamma-weighted transport of the fixed-head theta asymptotic to `M=M(b)` (unverified) | TH | adaptive partial sum `=ζ(½+ib)+O(\|b\|^{−½})` |
| A46 | Local singular indices beyond the cubic cutoff (unverified) | MC, RIAC | discrete-exit computation |
| A53 | Integrate the remaining unintegrated modules: annihilator phase moments and mass duality (APD), compressions and cyclic subgroups (AKLT, HKT), cutoff gaps (ACP), Lorentzian closure (ALG), folded Markov (SWC), window ports (CDG), compact cores (TCS), coherence principle (AGT) | APD, AKLT, HKT, ACP, ALG, SWC, CDG, TCS, AGT | source present [S] |
| A54 | Instantiate the cusp expansion with nonzero Wronskian for the resolvent of `Δ−¾` on Bianchi quotients | ACS, HF, HAT | `not_eq_frobenius_of_finiteVolume` |
| A55 | FE rigidity for continuous Beurling systems with `L¹` or `L²` defect (unverified) | BAG, ZCG, APD | Poisson rigidity; countable-system rigidity |
| A69 | Full-degree adelic configuration: non-square degrees as distinct points of the discrete quotient (unverified) | HAT, ACS, HF, PM | `TheOppositeAdelicDegreeConfiguration`; stub `TheFullAdelicDegreeConfiguration` |
| A70 | Torus-periodized local Green functions at the degree points of the quotient compared with the adelic Green formula (unverified) | HAT, PM | adelic Green formula; twisted fibres |

## 2.2 Open mathematical obstacles

### The common minimal face
| # | Problem | Strength | Routes |
|---|---|---|---|
| B130 | **The arithmetic Stepanov bound on a decisive sample**: `P(p)≤A(p)+K` at every prime, or at the primes of arbitrarily late `√T` windows, or on any decisive sample (equivalently `c_B(log p)≥−K`, or sign-free `\|c_B(log p)\|≤K`); any growth `Kp^a`, `a<½`, is a zero-free strip. Known: the VK saving | RH (≥qRH for `a<½`) | ACS, SRT, WL, HF, RW, ALST, SOSZ, CDGeo |
| B140 | **Bounded windows**: is a one-sided bound on windows `[x_k,Cx_k]` along a sparse sequence of scales decisive for configurations with ζ's zero counting, and if not, what is the shortest decisive radius between `O(1)` and `log²T` (§2.4) | method | ACS, SRT, WL, HF, SOSZ, CDGeo |

### Σ — critical sign
| # | Problem | Strength | Routes |
|---|---|---|---|
| B1 | Weil's sign on every window | RH | all sign routes |
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
| B14 | Any interior width value | ≥qRH | width axis |
| B15 | Past Vinogradov–Korobov | sub | every route |
| B16 | Decay law of `λ*(c)` | sub | CHT, RW |
| B17 | Signed ground-state structure past `log ρ` | method | EWU, OWU, RW, ACT |
| B18 | Prime-blind positivity on nonnegative blind mixtures | RH | RW, PBAP |
| B19 | Exact torus law for `S*(a,b)`; `{2,3}` cross-chain positivity | model | TH |
| B20 | Oscillation of the actual amplitude with the height | RH | TH |
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
| B46 | Proportional saving at length `(log X)^{2K}`, all heights; no early heavy return | sub | RW, all rungs, PTT |
| B47 | Multiplicity `o(log X)` by an input not reducible to size | sub | ZCG |
| B101 | Polar payment at every ratio on growing windows | RH | HF, AIP, SRT |
| B102 | Sign of the adaptive theta head at every degree, decided near the critical zeros | RH | TH |
| B104 | Polar payment at every ratio below `W`; at finite `W`, whether a critical half-line ground state can be polar-orthogonal | method | HF, SRT, AIP, ACS, SC |
| B123 | Correlated arithmetic pairings dominating the depleted kernel | method | HF |
| B124 | Useful finite initial depth budgets of the ξ heat divisor and extinction near `t=0` | ≥qRH to RH | ZCG, LA, WD |

### Π — precision and production
| # | Problem | Strength | Routes |
|---|---|---|---|
| B48 | Deciding input at square-root precision | RH | WL, MC, PBM, RB, JAS, CTF, HCF |
| B49 | Bounded endpoint energy; integer lag ceiling | RH | WL |
| B50 | Trivial-gauge half power; zero exclusion for `M_X` | RH | MC, WL |
| B51 | Moving power window control | RH | JAS |
| B52 | Vanishing rows, sparse defect, BSY sign, positive proportion | RH | CTF |
| B53 | Regularized partial-sum bound | RH | PBM |
| B54 | Eventual extremal inequality | RH | RB |
| B55 | Any polynomial stencil rate (qRH); rates `a↑½` (RH) | ≥qRH to RH | WL, MC |
| B56 | `Θ<1⇒Θ=½` | sub | whole programme |
| B57 | Depth density `o(T)` | sub | WD, census, MC, RW, ZCG, CTF, PM |
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
| B94 | Identification of the cubic Gauss coefficients with an automorphic theta expansion; transfer to rational Möbius | past VK at least | MC, MMD |
| B96 | Conditional law of the Euler tail at the Kronecker scale; lower bounds for exact tail events | sub | BAG, TH, WD, TAPO |
| B97 | Constant-precision first return of heavy subsets past the VK rung, `log R(y,δ)≥y^c` (top rung: a Littlewood-type bound for `ζ(1+it)`) | sub | PTT, TAPO, TTPO, BAG, CDGeo |
| B98 | Positive-generator integer-norm systems: which count distance forbids a finite top layer | method | RAC, SPAL, APD |
| B100 | A saving for `t log n` on moving block families past Vinogradov's degree | sub | PTT, TAPO |
| B106 | A natural correspondence on the orientation cover over ℤ with bounded local indices whose Lefschetz numbers are the centred counts | RH (≥qRH at `θ<1`) | MC, HF, ESG, HHAC, RIAC, HAT |
| B110 | Thick crude count: `primeDeviation(X)=O_a(X^{½+a})` along a thick set of geometric scales, every `a>0` | AAL | WL, ZCG, ACS, IWT |
| B113 | Möbius × quarter-disc remainder `O(X^{½+ε})` | beyond RH | PM |
| B121 | Freezing control beyond the precision cap | sub | BAG, ACS, PTT, IWT, ALST |
| B126 | A one-sided crude bound on one sampling or Bohr-dense set of primes | AAL (with ZAL: RH) | ACS, SRT, ZCG, BAG, IWT |
| B127 | Positive-measure recurrence of sub-top Weil-lag readings at every rate | AAL | WL, ZCG, IWT |
| B137 | **Collective depth floor**: return counts for heavy subsets of the primes `≤y` valid from heights `≤exp(y^c)`, with an error uniform in `π(y)` | sub | PTT, TTPO, CDGeo, BAG |
| B142 | **Specialization at the jump**: a family of Euler products with big monodromy in which the jump at ζ is the pole alone and pole-subtracted trace constants specialize to ζ | producer | ACS, HF, SC, AWT |

### Γ — selection, reflection and transport
| # | Problem | Strength | Routes |
|---|---|---|---|
| B13 | Finitely many off-line zeros of ζ ⇒ none | sub | whole programme |
| B68 | Independent `D_s≥0`, Krein flux, integer-probe sign, all-zero dispersion bound, or PSD of every reflection Krein form | RH | PM |
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
| B82 | Inner-field decay | ≥qRH | BAG, AIF |
| B83 | AAL `=B13 ∧ B138 ∧ B141` | sub | BAG, JAS, SC, ZCG, WL, IWT, ELT |
| B85 | Arithmetic global trace on a family containing ζ | RH | ACS |
| B86 | Mixed Young projections at unbounded rank | RH | ACS |
| B87 | A nonnegative count on the rays `Γ_1+Γ_p`, defined without `Q`, with Tate limit `2c_B(0)+2c_B(log p)` | RH | ACS, HF, PM, RW, AE, CTH, SOSZ |
| B88 | The sign of the Gram defect: a counterterm-free positive presentation of the diagonal on overlapping packets (local Robin data give the discriminant) | RH | AE, HHAC, SOSZ, RIAC, HAT, HF |
| B89 | A bounded aligned return at each right zero on a right disc | sub | BAG, ZCG |
| B92 | Arithmetic source of a rotated relation with coefficients of the size of `Q` | RH | ZCG, RAC |
| B93 | A contradiction using growth or arithmetic of `Q` beyond the extremal law | RH | ZCG, RAC |
| B111 | `ZAL⇒RH` = B13 ∧ B138 | sub | BAG, ZCG, IWT, WL |
| B112 | A mechanism converting the FE into vertical transport of zeros | sub | BAG, ZCG, EFT |
| B114 | A realization of the partner involution outside the central, vacuum-fixing and Borchers classes | producer | PM, CTH |
| B116 | Linear AAL at one fixed slope `C≥1` | sub | ZCG, IWT, WL |
| B117 | A confined companion of the modular horizon | producer | PM, BHR, ASH, CTH, AHMH |
| B125 | Halving pairs: no zero `ρ` with `ζ(ρ/2)=0`, and nonvanishing of one Shimura integral at every `ρ/2` | indep. | PM, AHMH |
| B128 | Replication in the finite-layer world | sub | BAG, ZCG, EFT, ELT |
| B133 | Green/Robin realization of Weil's full kernel, diagonal included, on the discrete adelic quotient | producer | ACS, HF, HAT, SOSZ, PM |
| B134 | An upper bound for the corrected exceptional current at one supercritical speed that the explicit formula does not imply | sub | BAG, ZCG, ELT |
| B138 | **Landing law** for ζ: ZAL ⇒ finitely many off-line zeros (§3) | sub | ZCG, LA, FFP, ELT, EFT, WD, HF, HKT |
| B141 | **Deuring–Heilbronn for ζ**: `¬ZAL ⇒ AAL`, the atom of AAL off the RH path (§2.5) | sub | BAG, ZCG, IWT, EFT, ELT |
| — | ZAL | ≥qRH | whole programme |

### Settled method questions
| # | Question | Answer | Evidence |
|---|---|---|---|
| B131 | Deuring–Heilbronn law of a top layer on models | DH is the `¬ZAL` sector of AAL; extreme DH ⇔ (AAL ⇔ B13); graded, asymptotic and extreme repulsion refuted on positive integer-norm Euler products; classical DH for quadratic `L(s,χ)`; no Siegel regime for ζ | [L] |
| B135 | Coupled locking of the `ℍ³` and torsion channels on overlapping packets | ordered Gram coupling: finite limits on every packet, exact defect `Δ_g` | [L] |
| B136 | Are power-saving gaps necessary for a decisive sample? | No: gappy samples and prime-power samples of zero convergence exponent decide | [L] |
| B139 | Are full prime windows along one sparse sequence of scales decisive? | Yes: the primes of `√T` windows decide, every `r>0` | [L] |

## 2.3 Frankenstein routes

**No assembly closes RH.** Every assembly below has at least one open input of RH, AAL or ≥qRH strength, or names one. The assemblies whose output is RH (F1, F2, F3, F15, F18, F19, F20, F21) each need an input that the corpus cannot produce. Their value is that they collapse independent problems into one, decouple the producers a proof needs, or fix what a missing input must contain.

| # | Parts | What the assembly gives | Missing input | Gain |
|---|---|---|---|---|
| F1 | **Split skeleton.** A sampling-set or Bohr-dense AAL producer with any ZAL receiver (inner-field decay, subtracted lag, `Λ_Xlog X→0`, eventual Hadamard positivity, high-collision counts) | RH [L] | one sampling-set bound (B126) or B127, and ZAL | two inputs of different kind; only the B13 ∧ Landing part of AAL is used |
| F2 | **One inequality per prime, local.** SOSZ prime degrees, the prime two-bump tests, the Stepanov bound as a prime count, the count door on one ray per prime, the sign-free two-sided form, positive deletion and `√T` windows | Σ, Π and count readings of RH are one number per prime on sparse local windows [L] | B130 on the primes of one sparse sequence of `√T` windows | ACS, SRT, WL, HF, PM count branch, ALST and CDGeo have one target, at scales they may choose |
| F3 | **Deligne skeleton over ℤ.** Stepanov side, absence of real zeros (Bombieri's twist), base change at `n^k`, free tensor positivity, Rankin square, Künneth into Tate twists, gap iteration, gauge family with big monodromy and generic purity, vertical equidistribution of ζ | every step of Deligne's purity proof has a ℤ-counterpart, the family included, except specialization at ζ, the jump fibre [L] | B142 (or directly `A_k=o(k)`) | names the missing piece: a family in which ζ's jump is only the pole |
| F4 | **Critical curve.** Threshold identities, charged compactness, half-line ground states, polar orthogonality, multiplier no-go | `R_c=R_polar=R_halfline≤W`; ¬RH ⇒ a ground state at finite `W` [L] | B104 | the critical curve carries one inequality and one orthogonality |
| F5 | **Horizon.** Seeds, cavity receivers, Maass and Hecke pairs, reflection Krein forms, dual side, standard-form trichotomy, Narain | physics reduces to one rate or one reflection sign [L] | B71 or B68 | waves, Hecke, KMS, modular conjugation and half-sided inclusions closed as sources |
| F6 | **The diagonal.** Adelic Green formula, spherical compensation, locked dampings, Gram coupling, prime-unit collapse, twisted Green fibres, discrete adelic quotient | Weil's form on every packet is a finite coupled limit minus an exact defect `Δ_g`; the degree points sit as points of one discrete adelic quotient [L] | B133, B88 | every local presentation of the diagonal is closed; the remaining object is global (§2.8) |
| F7 | **FE as the only selector.** Firewall, approaching and two-scale integer-norm products, complete FE rigidity, Poisson rigidity, Dirichlet selector of the heat family, symmetric shifts | every model failing one atom lacks the FE or the Euler product; every system with integrable FE defect is ζ [L] | B112 | each atom needs the FE and the Euler product jointly; ZAL also the coefficient size |
| F8 | **Finite-layer world.** Rigid ¬AAL, finite oscillation, prime-current passage, joint prime-phase returns, exceptional current, local and damping filters, contracting filters, Euler-region bound | a fully specified world with mutually consistent identities [L] | B134 (an inequality the explicit formula does not imply), B128 | the detection/decay disjointness quantifies what is missing |
| F9 | **Exactness and Diophantine closure.** Adams Frobenius on the torsion, minimal auxiliaries = Chebyshev, orbit preservers = Laurent Adams maps, Rouché precision cap, Baker bounds, collective counts, no finitely generated Frobenius-stable lattice | exact methods over ℤ reproduce Chebyshev; approximate methods stop at the trivial separation bound; collective counts start at the depth floor [L] | B97, B137, B121 | what survives is growing-height or signed information |
| F10 | **Mertens in eight geometries.** Franel–Landau, Farey, nerve, core, barcode, prime-vertex indices, gluing quotient, orientation cover | one exponent; cover weight `≥½`, `½` ⇔ RH [L] | B106 | topological tools act on the Mertens level |
| F11 | **Sampling axes.** Prime degrees (decisive samples, Bohr-dense sets, `√T` windows), bases of towers (metric recurrence), levels of towers (thick sets) | AAL from one-sided bounds on any axis; on the prime axis decisive local windows give RH [L] | B126, B127, B110, B140 | decisiveness is compactness and locality |
| F12 | **Heat divisor.** Initial budgets, crowding dissipation, sharp coefficient `2`, heat finite-stratum law, Ki–Kim–Lee, Dirichlet selector | finite budgets give `N(t)(2t)^q≤2S_q`; heat finiteness does not land [L] | B124, B24 | the heat route needs a finite budget plus an input that sees the Dirichlet series |
| F13 | **Theta wall.** Column calculus, adaptive head, Gamma reserve | all ranks reduce to `\|ζ(½+ib)\|²` plus second-order terms [L] | A42, B102 | merges TH with the size of ζ on the line |
| F14 | **Dark range.** Savings, precision law, heavy-return dictionary, collision counts, precision cap, depth law, breadth cap, VK breadth, collective counts | the short-sum barrier is one first-return statement, proved to the VK height and counted from the depth floor [L] | B97, B137, B121 | gap: `(log y)^{3/2}` against `y^c` |
| F15 | **Count skeleton.** Hecke isometry of `Q`, Tate principle, point-count defect on curves, half-products, adelic Green fibres, ray counts, `Q` not integer-valued, λ-ring effectivity | every ingredient of the curve count proof except a count over ℤ on one ray per prime [L] | B87, B88 | output RH; names the missing object |
| F16 | **Two Frobenii, local.** Kronecker density of `ℤlog p+ℤlog q`, continuity of the spline trace, `√T` windows | RH from the lags of two primes in sparse local windows [L/D] (A65) | the bound on those lags | the minimal degree set is a rank-two lattice of lags in sparse windows |
| F17 | **Siegel calibration.** Dirichlet `L` from both sides; classical Deuring–Heilbronn for quadratic `L(s,χ)`; infinite power-sum detection; no Siegel regime for ζ | AAL layers and Siegel zeros are both masked from the Stepanov side; repulsion acts only near the pole [L] | none (calibration) | DH for ζ needs an anchor other than the pole (§2.5) |
| F18 | **Sign-free skeleton.** Two-sided gap iteration, absolute large values force heavy returns, proportional saving ⇔ no early heavy return, VK breadth, collective counts, Turán on thick sets | RH from a two-sided crude bound without sign or spectral input; every other link present or named [L] | breadth below the Dirichlet scale (B97, B137) and the transfer from short prime polynomials to the window count (B46) | the positivity-free route has exactly two missing links (§2.6) |
| F19 | **Exceptional-set skeleton.** Stepanov bound off power-thin exceptions ⇔ RH; Huxley gaps; zero-density exceptional sets | RH tolerates `O(X^{1−δ})` exceptional primes [L] | B130 off an exceptional set | moves the target into the exceptional-set regime |
| F20 | **Sector map.** Atoms (ZAL, B13, Landing, DH), decisive local windows, sampling and Bohr-dense sets, damping filters, finite-index receivers, bounded windows in the finite stratum | each RH-failure world has its own calibrated killer: `¬ZAL ∧ AAL` (unattained tops) — a bound on a decisive sample; `¬ZAL ∧ ¬AAL` (isolated top) — any sampling-set bound or DH; `ZAL ∧ ¬Landing` — a depth-blind receiver (Krein index, heat count, Hadamard threshold); `ZAL ∧ Landing ∧ ¬B13` — one bounded window or one non-blind tower [L/D] | a producer per world | a proof may combine weaker producers, one per world; a sampling-set bound alone kills every attained-top world, ZAL the rest |
| F21 | **Local Deligne.** Tensor moments, `√T` windows, Künneth | RH ⇔ uniform-in-`k` moments of `c_B` over the primes of sparse `√T` windows [D] (A71) | the uniformity | moment methods at chosen scales become RH-relevant |
| F22 | **Adelic holography.** `ℍ³` propagator at decay rate `½` on the degree geodesic, tree propagators at the Ramanujan point, pole as spherical piece, discrete adelic quotient, Gram coupling, reflection Krein law of the cavity | Weil's form as a two-point function of an adelic bulk at the tempered edge of every place [L/D] | the sign (unitarity) | a physics reading of the diagonal (§2.7) |
| F23 | **Atoms on the horizon.** Reflection Krein form (one negative square per off-line zero), finite-index stratum, landing forms | RH ⇔ ZAL ∧ (finite negative index ⇒ 0) ∧ (ZAL ⇒ finite negative index) on one Krein form [D from L] | the three atoms | the atoms become the count of unstable modes of one physical object |

**Closest to the open core: F2, F3, F20, F18.** F2 makes the Σ∩Π core one inequality per prime on sparse local windows. F3 shows that over ℤ the whole of Deligne's argument is present, the family included, except specialization at the jump fibre. F20 decouples the producers: one per failure world. F18 shows that a positivity-free proof needs exactly two inputs.

### The finite-layer world: what a contradiction search may assume (F8)
| In the world ¬AAL | Evidence |
|---|---|
| Isolated top `Θ=β`, attained; remainder left of `Θ₂<Θ` above the layer's heights | [L] |
| `ψ(x)−x=x^ΘT(log x)+O(x^{Θ−η})`, `T` unique, sign changes at bounded log gap | [L] |
| Two-prime dilation annihilation of `ψ`; a positive annihilator of the top whose inverse oscillates at every exponent `<Θ` | [L] |
| Syndetic lag excursions at every base; recurrent sub-top bases have dimension 0 | [L] |
| `c_B(log p)<−Kp^a` on a positive relative density of primes for every `K`, `a<Θ−½`, in every late `√T` window | [L] |
| The raw prime current passes to `−ζ′/ζ` on high strips; head-conditioned rough variance is the diagonal | [L] |
| Prescribed finite prime phases recur in every high dyadic window with the continued rough current at its variance | [L] |
| At exponential damping and supercritical speed the corrected current is the top mode × a finite wave with sharp recurrent envelope; one positive top ordinate ⇒ divergence | [L] |
| Local filters recover each top multiplicity; prime-only damping filters isolate any top mode; at contracting damping it grows when `dκ<a(β−σ)/2−π/4` | [L] |
| The Euler series bounds every filter only at abscissas `c>1`; decay needs `dκ>a(1−σ)/2` | [L] |
| The FE reflects every height to itself | [L] |
| A remainder zero at the observation height dominates the top for `π/(2(β−σ))<a<π/(2(β−β_r))` | [L] |
| The layer occupies a density-zero set of heights; random models have no such layer | [D] |

No contradiction comes from exact identities alone (they are the explicit formula), from positivity, Euler products, integrality, counting or positive annihilators alone, from the FE with order one and reality, from a property shared by the heat family, from statistics at one scale, or from any in-law statement [L/D].

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
| T8 | Not a named long-standing problem in disguise (RH, quasi-RH, ZAL, AAL, B13, Lindelöf, pair correlation, Hardy–Littlewood, Chowla, past VK, Landau–Siegel); its first step uses corpus objects and has one named obstacle |

Every statement below AAL that constrains the zeros of ζ contains B13, landing, DH, or an exceptional-zero problem of Landau–Siegel type; every crude step on thick, sampling or Bohr-dense sets contains AAL [L/D]. Of the atoms, only landing contains neither a single-quartet exclusion nor ZAL.

## 2.4 Breakthrough question below RH and quasi-RH: how local is RH?

**Question (B140).** *Is a one-sided bound on bounded multiplicative windows at a sparse sequence of scales decisive for configurations with ζ's zero counting?* Precisely: let `Z` be a tempered reflection-symmetric configuration without real zeros, with lowest ordinate `γ₀>0` and counting function `N_Z(T)=(T/2π)log(T/2πe)+O(log T)`. Is there `L>0` such that `2Re S_Z(u)≥−K` on windows `[u_k,u_k+L]` along any sequence `u_k→∞` forces every zero onto the line? If not, what is the slowest-growing radius `R(T)` that decides this class: `O(1)`, `log T`, `log²T`, or nothing below `√T`?

**What is proved [L].** `R=r√T` decides for every tempered configuration and gives, at the primes, RH ⇔ the Stepanov bound on the primes of arbitrarily late `√T` windows. δ-separated configurations are decided by windows of length `80/δ`; on unbounded windows an impure configuration bounded below carries near-coincident ordinates. For ζ the deletion cost of every prefix of the ordinate-indexed tail is `≪|s|log²H+s²log H/H`, and the leakage from radius `C·log²T` is exponentially small. In the finite stratum bounded windows decide [D]. Shrinking windows along super-lacunary scales do not decide [D].

**What either answer gives.**
| Answer | Effect |
|---|---|
| Bounded windows decide | RH ⇔ for some `C,K`, infinitely many `x` with `P(p)≤A(p)+K` for every prime `p∈[x,Cx]`. RH is a statement about local prime statistics in windows of bounded ratio, at scales a producer may choose freely (after a heavy return of the prime orbit, at Kronecker-good scales, at levels of a tower). Every prime-side route (ACS, SRT, WL, HF, SOSZ, CDGeo, TTPO, PTT) can concentrate on one scale family; Turán's power-sum method, which localizes the oscillation of `ψ(x)−x` caused by a zero to windows of comparable logarithmic radius [C], acquires an exact converse at bounded ratio |
| Only `R(T)→∞` decides | an interference theorem: configurations with ζ's counting hide off-line zeros from bounded windows through near-coincident clusters; the decisive radius is a property of zero spacing, positive deletion is optimal up to the identified radius, and bounded-window producers need arithmetic spacing input |

**Why this question.** It is the resolution limit of the minimal face, the successor of the settled B136 and B139. It is a statement about configurations, implied by nothing about ζ, and its answer fixes how much prime data per scale RH needs. First step: replace ordinate separation by a cluster decomposition — group the zeros near height `t` into clusters of diameter `η`; the separated-window theorem applies across clusters, while inside a cluster the modes form a slowly varying amplitude times one carrier frequency. One named obstacle: a cluster whose internal modes cancel the amplitude on the window. A configuration defeating bounded windows must create such cancellations at every one of infinitely many scales and, by the Riemann–von Mangoldt law, with cluster sizes `O(log t)`; whether that suffices is the question.

**Tests.** T1: method. T2: decisive or not; the radius. T3: the table. T4: no finite rung. T5: calibrated on separated configurations (yes), the finite stratum (yes) and super-lacunary shrinking windows (no). T6: not refuted. T7: moves B130, Σ145, Σ146, A64, F2, F11. T8: not a named problem.

**Limit.** It decides where RH can be certified, not whether the bound holds.

### Alternatives
| Question | Why it matters | T8 | Limit |
|---|---|---|---|
| Polar orthogonality at the critical curve (B104) | decides whether the pole channel detects ¬RH before the window | passes | Σ block only |
| Specialization at the jump (B142) | whether Deligne's family step can exist over ℤ | passes (method form) | a positive answer is RH-strength |
| `log²T` windows for ζ (A64) | local criterion at the ζ-specific deletion radius | just work | criterion only |
| Two-prime local criterion (A65) | RH from two primes' lags in sparse windows | just work | criterion only |
| Halving pairs (B125) | one Hecke eigenform as a complete receiver | excludes a configuration of zeros | adds a receiver |

## 2.5 Breakthrough question below AAL: the Deuring–Heilbronn sector of ζ

**Question (B141).** *Does an isolated top layer of ζ force the zeros to approach the line?* That is, `¬AAL ⇒ ZAL` for ζ; equivalently, ζ has no world `¬ZAL ∧ ¬AAL`; equivalently, whenever infinitely many zeros lie right of some `½+h`, every right zero has companions at its depth at arbitrarily large height.

**What is proved [L].** `AAL ⇔ B13 ∧ Landing ∧ DH`, and the atoms never fail together: DH is the only atom of AAL off the RH path. On models: positive integer-norm two-scale Euler products with linear counting, continued across `Re s=½`, have an isolated top `β±iγ` over a remainder at asymptotic abscissa `θ₂<β` and violate asymptotic DH; every graded repulsion bound `f(β−θ₂,γ)<θ₂−½` is refuted on that class; two-scale `cosh` models (FE without Euler product) violate it too. Classical Deuring–Heilbronn holds for a real zero of a quadratic `L(s,χ)`, with a constant uniform in conductor, height and zeros, through the complete Dirichlet divisor, the positive Euler kernel `(1+χ(n))Λ(n)` and infinite power-sum detection. ζ has no Siegel regime. AAL(ζ) ⇔ DH(`L_a`) for every `a>0` [D from L].

**What either answer gives.**
| Answer | Effect |
|---|---|
| Yes | every failure of AAL for ζ is a ZAL world: AAL ⇔ B13 ∧ Landing = `ZAL⇒RH`; AAL research becomes RH-path research; the exceptional-current program, the sampling-set and tower producers and the damping filters need only treat attained-top worlds approaching the line; RH ⇔ ZAL ∧ AAL holds with AAL = B111 |
| Proof that no FE ∧ Euler mechanism decides it | AAL is not reducible to the RH-path atoms by repulsion; a world `¬ZAL ∧ ¬AAL` is consistent with every identity the corpus uses, and AAL needs transport (B112) |

**Why this question.** It is logically weaker than AAL and independent of B13 and landing: it is vacuous in every ZAL world and never asks to exclude a finite off-line set or approaching remainders. Its world has a structure no classical exceptional-zero problem has: an infinite remainder right of `½`, accumulating at `Re s=Θ∞>½`. Classical repulsion uses a zero that nearly cancels the pole; ζ has none. The question is whether the remainder's accumulation at `Θ∞` can serve as the anchor: in the Euler-positive kernel of `−ζ′/ζ` at heights where the remainder is dense, does an isolated top at `β>Θ∞` force a cancellation that the Euler product forbids?

**First step.** Use the corpus's two-sided model: the integer-norm two-scale product violates DH, so the input must see the FE; the two-scale `cosh` model violates DH, so it must see the Euler product. A remainder-anchored version of the five-point repulsion inequality — the positive kernel `2(1+cos(γ₁log n))(1+cos(γ₂log n))` with `γ₂` running over remainder ordinates near `Θ∞` — with the reflected top `1−β̄` entering through the FE. One named obstacle: the remainder's ordinates are unknown and dense only in density-zero sets of heights, so the kernel must be averaged over the remainder without losing its sign.

**Tests.** T1: implied by AAL; implies none of ZAL, B13, quasi-RH. T2: an implication. T3: the table. T4: a tail statement. T5: false on integer-norm two-scale products and two-scale `cosh` models [L]. T6: not refuted. T7: moves B83, B131, B134, F8, F17, F20. T8: it contains the exclusion of an isolated top over a `¬ZAL` remainder; it is not Landau–Siegel because the anchor is an infinite remainder right of the line, not a zero near the pole.

**Limit.** It treats one sector of AAL; B13 and landing remain.

### Alternatives
| Question | Effect | T8 verdict |
|---|---|---|
| Landing (B138, §3) | the RH-path atom of AAL beyond B13 | passes |
| B13 | the finite stratum | fails: single-quartet exclusion |
| Independent current bound / one-quartet world (B134) | excludes the minimal finite layer | fails: single-quartet exclusion |
| Replication (B128), sampling-set bound (B126), metric recurrence (B127) | AAL | fail: contain AAL |
| Dominant-ordinate divergence (A67) | extends the one-quartet signature | just work |

## 2.6 If positivity, Weil positivity and spectral methods are excluded

"Spectral" is read as spectral theory of operators in every form: eigenvalues, spectral decompositions, Hilbert–Pólya realizations, trace formulas, spectral gaps, Lax–Phillips semigroups, transfer-operator spectra, Maass and Eisenstein spectral theory, standard forms, Krein forms. "Positivity" includes nonnegativity of counts, of Dirichlet coefficients (Landau's theorem), of Fejér and sinc kernels, of averaging measures, Hodge index and Tate limits. Kept: Fourier analysis, mean values used as bounds, exponential sums, absolute convergence, analytic continuation, Laplace transforms, power sums (Vandermonde, Turán), Dirichlet polynomials, integrality, Diophantine approximation and transcendence, recurrence, Jensen and Rouché.

**What survives.**
- **The decision step.** RH ⇔ `|c_B(log p)|≤K` at every prime (or on any power-saving gap set); width ⇔ the growth exponent; by absolute convergence, continuation and the Laplace rate theorem [L]. The local version on `√T` windows is proved with positive averaging; a sign-free local version with signed deletion filters is work (A66).
- **Elimination.** Turán–Vandermonde at the exceptional rank on thick sets [L]; finite Turán power sums are sign-free.
- **Breadth.** Heavy subsets do not return before `log t=(log y)^{3/2−ε}`; at every heavy return `√y≤K(y^{1/2−w(2t)}log t+log(2+t))`; absolute large values force heavy returns at a dilated height; collective rank depth bounds near relations [L]; collective return counts are effective from the depth floor, which sits at the Dirichlet return scale [D].
- **Capped producers.** Integrality reaches Chebyshev and acts exactly only on the torsion; minimal auxiliaries are exactly Chebyshev; freezing reaches the trivial separation bound; exponential sums reach VK; transcendence bounds depth [L].
- **What falls.** All of Σ; every one-sided receiver (Landau); the count door; the critical curve; the horizon receivers; the index routes; FE rigidity; the Lefschetz trace.

**The question.** *Does a breadth law for the prime orbit below the Dirichlet scale transfer, at one sparse sequence of scales, to the two-sided crude bound at the primes?* Two links:
1. **Breadth (B97/B137).** For fixed `δ`, no heavy subset of the primes `≤y` returns to precision `δ` before height `exp((log y)^A)` for every `A` (past VK), ultimately before `exp(y^c)`: the Bohr sets of the prime orbit at constant precision are empty below the scale where Dirichlet's pigeonhole first forces returns (`exp(Cy/log y)`).
2. **Local transfer.** From "no heavy return of short prime polynomials at heights relevant to scale `T`" to `|P(p)−A(p)|≤K` for the primes of one `√T` window — proportional saving (B46) at those heights, assembled by the sign-free decision step.

**Why it opens the path.**
- The crude count over ℤ fails exactly where the prime orbit returns: at a heavy early return a long prime polynomial is large and a zero can hide under it [L]. Over `𝔽_q` the auxiliary vanishes exactly at every rational point; over ℤ exact vanishing exists only on the torsion, and the minimal auxiliary is exactly as long as Chebyshev's count [L]. The positivity-free route therefore needs approximate information at returns, which only breadth supplies.
- Scale locality reduces the transfer from "all heights" to the heights a sparse sequence of `√T` windows sees; a zero of depth `δ` and height `γ` enters the window at scale `T≳4log γ/δ` [D].
- Collective counting already holds from the depth floor on; the open part is the range below the Dirichlet scale, where only Bohr-set emptiness, not counting, can help [D].
- Both answers are informative: if the transfer holds, the positivity-free route is reduced to breadth; if it fails, the short-sum barrier is a theorem.

**Strength and rungs.** At `(log y)^A` breadth is past VK; at `y^c` it is a Littlewood-type bound for `ζ(1+it)` [D]. Rungs: two primes (depth law) [L]; `k` primes (explicit forms) [L]; VK breadth for heavy subsets [L]; collective counts from the depth floor [L]; Bohr-set emptiness below the Dirichlet scale (B97); `𝔽_q[T]`: exact Frobenius, nothing to bound [L].

**Limit.** It speaks about large heights; a finite layer at a fixed height is invisible to it. The finite stratum then needs the FE as a reciprocity acting on heights, the one sign-free ingredient left unused.

## 2.7 If RH is a physical phenomenon in AdS with a modular horizon

**What is proved [L].** The modular horizon is `SL₂(ℤ)\`(Rindler wedge of AdS₄); its resonances sit at the zeros of `ξ(2s)`; one cavity function of Hecke eigenforms sees every resonance, and RH ⇔ its energy rings down at `y^{¾−ε}`; the reflection Krein form pairs each resonance with its FE partner and has exactly one negative square per off-line zero. The archimedean place is a scalar of `m²=−¾` on Euclidean AdS₃ restricted to one geodesic: `2πG_{1/2}=2πG_{3/2}+½φ_{1/2}`, two quantizations `Δ=½` and `Δ=3/2`, and the pole `(3/2)φ_{3/2}+½φ_{1/2}` cancels the `Δ=½` piece. The finite places are Bruhat–Tits trees with the Green function at the Ramanujan point — the bulk propagators of `p`-adic AdS at the tempered edge. Ordered Gram coupling gives finite coupled limits on every packet; a discrete adelic quotient by the rational split torus carries the degree configuration.

**The law, read physically [D].** Off the diagonal Weil's kernel is the pole minus bulk propagators of all places, each at decay rate `½` in its own distance: the real place on a geodesic of AdS₃, the `p`-adic places on apartments of `p`-adic AdS. This is an adelic bulk at the edge of the tempered (Ramanujan) range at every place, with the degree configuration as bulk points on the orbit of the rational split torus and the pole as the zero mode. The symmetric shift `L_a`, which keeps FE and Euler product and violates ZAL, moves every place to decay rates `½±a`: off the edge at every place at once. The reflection Krein form is the pairing of the two members of an FE pair, which in AdS is the Legendre (double-trace) duality between the two quantizations; positivity of a boundary two-point function is unitarity.

**The question.** *Is Weil's form the boundary two-point function of an adelic holographic theory at the tempered edge, and is RH its unitarity?* Is there a bulk theory on (Euclidean AdS₃ × Π'_p Bruhat–Tits trees) modulo the rational split torus — a scalar at the edge at every place, with the primes entering only through the torus action and the archimedean place through its two quantizations — such that (a) its bulk-to-bulk propagator on the degree points is Weil's off-diagonal kernel, (b) its renormalized self-energy at a degree point is Weil's diagonal, and (c) the reflection Krein form of the modular-horizon cavity is its flowed two-point function? Then RH ⇔ reflection positivity of the boundary theory.

**Why it opens the path.**
- It replaces a sign by an axiom: unitarity of a boundary theory with a positive-norm Hilbert space is structural.
- It is exactly what the operator no-gos leave: the partner map acts between two quantizations, not inside one algebra; internal modular conjugation and vacuum-fixing partners fail for that reason [L].
- It uses objects already present: the archimedean identity, the tree Green functions, the Gram coupling and the discrete adelic quotient [L]; `p`-adic AdS/CFT supplies tree propagators and boundary two-point functions on `ℚ_p` [C]; adelic products of local amplitudes reproduce Euler products [C].
- Calibration is built in: `L_a` leaves the edge at every place; graph black holes with `t²>4q` leave the Ramanujan range; a theory whose spectrum is the critical ordinates would be a Hilbert–Pólya operator, so (a)–(c) must be built from the places alone.

**Second physical question (B117).** *Is the modular horizon the modular image of a confined system with real normal modes?* A unitary horizonless system with the worldline modes as free part and the primes as interactions, whose Euclidean correlators map to the mirror-even response, so that every resonance `ρ/2` is the image of a real normal mode; by F23, its unstable modes would count the off-line zeros, and landing would say a ZAL system has finitely many.

## 2.8 If RH is a problem of topology or geometry

**What is proved [L].** Off the diagonal Weil's form is an adelic Green pairing at the tempered edge of every place. One-place hyperbolic carriers, compact and finite-volume embeddings fail; locked atoms give the discriminant; scalar locking converges only at mass balance; ordered Gram coupling gives finite limits with an exact defect; the prime unit admits no scalar or unitary descent; a discrete adelic quotient by the rational split torus carries the degree points. RH ⇔ one side of Hasse–Weil for the smoothed Frobenius graphs at the primes of sparse `√T` windows. Topology: the orientation cover over ℤ has middle cohomology of weight `≥½`, weight `½` ⇔ RH; no finitely generated ℤ-lattice of zero modes is stable under three prime Frobenii; the explicit formula is the Lefschetz trace of the Meyer flow.

**A geometric fact [D].** In the product of the real and `p`-adic hyperbolic spaces, the degree points `n` and `m` with `n/m=a/b` in lowest terms are at real distance `|log a−log b|` and at total `p`-adic distance `log a+log b`; the adelic distance is `2log max(a,b)`, twice the height of the ratio. The degree configuration is a set of points whose mutual adelic distances are heights of rationals; Weil's kernel is the pole minus Green functions evaluated at the local parts of these distances.

**Geometric question (B133 sharpened).** *Is the split-torus orbit of the degree points Robin-subcritical in the adelic quotient?* On the discrete quotient `X` (extended to all degrees, A69), let `𝒢` be the sum over places of the local Green functions at the tempered edge, periodized over the torus. Is there a renormalization of `𝒢` at coincident points — a Robin mass of the orbit, global, not place-wise — such that Weil's form on smoothed packets is the renormalized `𝒢`-energy of the configuration, and RH ⇔ the self-energy of every smoothed configuration dominates its mutual energy?

**Why it opens the path.**
- It is the only presentation the corpus has not closed: every local Robin datum gives the discriminant, the Gram defect is non-local, and the quotient carrying the points exists.
- Periodization over the torus turns the diagonal of a translation-invariant kernel into its row sums twisted by characters, so the global Robin mass at a character is the spectral density of the zeros at that height [D]: the geometric content of the question is a reason for subcriticality other than the explicit formula — a packing statement for points at mutual distances `2log H(n/m)`.
- The atomic surface fails at genus `N log N`; smoothing at the natural scale is where the question lives, and the corpus's positive results below the eighth-root scale are its subcritical checks.

**Topological question (B106 with the lattice no-go).** *Does the orientation cover over ℤ carry an infinite-rank Lefschetz theory with a weight filtration?* The real fibres of `y²=disc F_n` record complex conjugation on the roots of `F_n=Π_{p|n}(X²+p)`. No finitely generated Frobenius-stable lattice exists, so the cohomology must be infinite rank; the Meyer flow supplies a Lefschetz trace equal to the explicit formula. Question: is there a weight filtration on a completion of the cover's cohomology, compatible with the dilation correspondences, whose graded pieces have finite rank at each truncation and whose middle piece grows like `N^{½+ε}`?

**Limit.** Over `𝔽_q` these structures come from a variety; over ℤ none is constructed.

## 2.9 New field for RH: arithmetic nearby cycles of the gauge family

**Does RH need a new field?** Yes. Every step of Deligne's purity argument has a ℤ-counterpart, the family included: big monodromy, generic purity, Gaussian Frobenius and equidistribution of ζ's vertical family hold in the gauge torus of twists [L]. The argument breaks at one place: ζ is not a generic member of the family but its jump fibre. Over a curve the jump of a family at a special fibre is controlled by nearby and vanishing cycles, whose weights obey the monodromy-weight filtration; the pole of the special fibre is the known `H²`-type contribution and is subtracted. Over ℤ no theory of the special fibre exists: trace constants are closed but blow up at ζ, Baire and Haar genericity disagree, exact monodromy transfers only the trivial bound, and the families that move zeros are analytically disconnected from ζ [L].

| Aspect | Content |
|---|---|
| What it is about | The behaviour of a family of Euler products at its special fibre ζ: the decomposition of ζ's window traces into a nearby part (the limit of generic fibres) and a vanishing part (the jump), with the pole as the only vanishing cycle; weights of the nearby part bounded by generic weights. |
| What it would be like | Specialization theory for families of Dirichlet series over the gauge torus and its pretentious strata: the jump locus is the pretentious archimedean line (poles where `χ_x` pretends `n^{iτ}`, zeros where it pretends `−n^{iτ}`) [L]; a monodromy around the jump; a filtration on the centred traces at ζ whose graded pieces are read from nearby fibres. |
| Criteria it must meet | Reproduce Deligne's nearby-cycle bounds over `𝔽_q`. Explain why the product topology fails (constants blow up at ζ) and supply a topology or centring in which the pole-subtracted constants are lower semicontinuous at ζ. Respect Baire versus Haar (Baire-generic exponent `½`). Use the Euler product and the FE: the integer-norm one-off violates the Stepanov bound, the heat family is uniform and RH-strength, `L_a` violates ZAL. Respect exact-monodromy pricing: positivity transfer alone gives the trivial bound. |
| Questions it must answer | Which family has ζ's jump equal to the pole alone (gauge twists, Dirichlet twists, vertical shifts, Rankin–Selberg or symmetric-power deformations)? What is the vanishing cycle of the gauge family at the trivial fibre, and is it one-dimensional (the edge divisor says yes on `Re s=1`)? Is there a centring of traces under which nearby fibres converge to ζ's centred trace? What replaces the monodromy-weight filtration? |
| Tools it aims to develop | Pretentious geometry of the gauge torus; edge-divisor calculus; specialization along pretentious strata; centred tensor moments; Künneth for the virtual motive; Baire–Haar comparison; vertical equidistribution as specialization in law. |
| Objects | The gauge torus and its hull; the archimedean line; the pretentious and anti-pretentious loci; centred window traces; the virtual motive and its Tate-twist constituents; trace-constant sets. |
| Language | special fibre, jump, nearby part, vanishing part, pole as vanishing cycle, centring, specialization, pretentious stratum, weight, semicontinuity. |
| Mechanisms | Built on: generic purity, Gaussian Frobenius, vertical equidistribution, the jump at ζ, edge divisors, Künneth, `A_k=o(k)` ⇔ RH [L]. To discover: specialization of centred constants at the jump. |

**Main conjecture (nearby purity).** There is a family `𝔉` of Euler products and a centring of window traces such that the centred trace constants at exponent `a` form a closed set containing all generic fibres near ζ with uniformly bounded constants, and ζ lies in its closure; hence `A_k=o(k)` for ζ. **Milestones.** M1 [L] generic purity, jump at ζ, edge divisor. M2 A family whose jump at ζ is exactly the pole. M3 Lower semicontinuity of centred constants at ζ. M4 Uniform boundedness of nearby centred constants (zero-free strips of every width). M5 RH.

## 2.10 New field for AAL: exceptional dynamics of the vertical flow

**Does AAL need a new field?** Yes. Every atom of AAL is a pointwise statement about density-zero sets of heights: random Euler products have no zeros right of `½`, almost all zeros lie near the line, and every in-law statement — vertical equidistribution of ζ, Gaussian Frobenius, conditional tail laws, universality — is blind to off-line zeros [L/D]. The finite-layer world is fully specified and consistent; its identities are height-preserving; the only exact symmetries of the prime orbit are integer dilations; the FE reflects a height to itself [L]. AAL is free over a curve because base change makes the zeros periodic in height. Over ℤ the substitute must be a theory of recurrence for exceptional (measure-zero) events of the vertical flow.

| Aspect | Content |
|---|---|
| What it is about | Recurrence and rigidity of the exceptional set of the vertical flow `t↦ζ(·+it)`: heights at which ζ has a zero right of `σ`, as a subset of the orbit of a uniquely ergodic flow on the hull. AAL says this set, if nonempty at depth `b`, recurs at depth `b−ε` at arbitrarily large heights; DH says an isolated recurrence failure forces the set to be confined near the line. |
| What it would be like | Dynamics on the Bohr hull of ζ (the gauge torus with the Kronecker flow), with ζ in the strip as a discontinuous observable; recurrence of residual or Baire-generic sets (topological recurrence) rather than measure recurrence; the FE as a time-reversal symmetry; Diophantine structure of returns (transcendence, collective counts) as the quantitative input. |
| Criteria it must meet | Reproduce periodicity and AAL over `𝔽_q`. Fail on the one-offs, the two-scale and approaching integer-norm products (Euler product, no FE), on the `cosh` and approaching FE models (FE, no Euler product), and on `ζ(s−h)` (same labels, shifted zeros). Be blind-proof: a recurrence statement for measure-zero sets cannot come from equidistribution. Respect the two-scale law and the consistency of the finite-layer identities. |
| Questions it must answer | In which topology on the hull is the zero set of ζ right of `σ` closed and recurrent? Does the FE make the exceptional set symmetric under a time reversal that, combined with the Kronecker flow, forces recurrence? Does the Baire-generic behaviour of fibres (exponent `½`, nonrepelling values residual of dimension 0) select the exceptional set? What is the loss law of near-zero events transported along dilations? |
| Tools it aims to develop | Topological recurrence for residual subsets of minimal flows; semicontinuity of zero sets along hull limits; exceptional-set dimension theory (nonrepelling values have dimension 0 and are residual [L]); dilation transfer of large and small values; damping filters as local observers of exceptional modes; collective return counts. |
| Objects | The hull and its Kronecker flow; the archimedean line; exceptional sets of heights; finite top layers and their waves; Euler heads and tails; nonrepelling values; base-changed curve zeta functions as calibration. |
| Language | exceptional event, recurrence, residual set, minimal flow, height reversal, transport, replication, sector. |
| Mechanisms | Built on: AAL ⇔ tail transport; FE height reflection; joint prime-phase returns; local and damping filters; atoms and sectors; random-model zero-freeness [L]. To discover: a recurrence principle for density-zero events of ζ. |

**Main conjecture (exceptional recurrence).** For every `σ>½`, the set of heights at which ζ vanishes right of `σ` is either finite or recurrent in the sense of the hull flow, with return times controlled by the Kronecker scale of the primes up to `log` of the height. **Milestones.** M1 [L] atoms, sectors, filters, random-model zero-freeness. M2 Closedness of the exceptional set along hull limits. M3 Recurrence for one top quartet (the one-quartet world). M4 DH (B141). M5 AAL.

## 2.11 New field for RH without positivity: arithmetic jet geometry of Spec ℤ

**Does a positivity-free RH need a new field?** Yes. The positivity-free toolkit is complete at the receiver level (two-sided decision step, Turán elimination) and capped at the producer level: integrality reaches Chebyshev and the minimal auxiliary at the fixed points is exactly as long as Chebyshev's count; freezing reaches the trivial separation bound; exponential sums reach VK; transcendence bounds depth; collective counts start at the Dirichlet scale [L/D]. The one sign-free proof of a Riemann hypothesis — Stepanov–Bombieri over `𝔽_q` — rests on a feature ℤ lacks: the Frobenius `x↦x^q` has zero derivative, so vanishing to high order at all rational points costs little degree. Over ℤ the exact Frobenius of integer auxiliaries is the Adams operation, exact only on the torsion, and exact order costs the degree [L]; the corpus has Witt vectors with Frobenius [L] but no `p`-derivation, Fermat quotient or δ-ring.

| Aspect | Content |
|---|---|
| What it is about | Stepanov's method over ℤ in the direction of the primes: auxiliaries whose multiplicity at a prime is measured by `p`-derivations `δ_p(a)=(a−a^p)/p` (Buium) rather than archimedean derivatives, so that vanishing to order `m` at all `p` of one scale-local window costs less than the window's Chebyshev count. |
| What it would be like | Arithmetic jet spaces of Spec ℤ and of the prime torus; δ-rings and Λ-rings (Witt vectors are δ-rings, Adams operations are Frobenius lifts); counting inequalities from a δ-polynomial vanishing on a prescribed set; the two-sided local decision step as the final elimination. |
| Criteria it must meet | Reproduce Stepanov–Bombieri over `𝔽_q`. Use no sign and no spectral input. Beat Chebyshev: exact archimedean vanishing is exactly Chebyshev, so the multiplicity must be `p`-adic or approximate. Respect the no-gos: integrality creates no zeros at returns; Rouché copies are capped; orbit symmetries are dilations; the integer-norm one-off violates the Stepanov bound for every constant and must fail. |
| Questions it must answer | What is the multiplicity of an integer auxiliary at all primes of a window at once in δ-geometry? Is there a δ-polynomial vanishing to order `m` at every `p` of a `√T` window with δ-degree below the window's Chebyshev count? Does it give the two-sided crude bound on that window? How do δ-characters and arithmetic Manin maps on the prime torus interact with the Adams operations and with Witt Frobenius? |
| Tools it aims to develop | `p`-derivations and their jets; Witt and Λ-structures; δ-characters; arithmetic Picard–Fuchs operators; `p`-adic continuation of auxiliaries; the sign-free local decision step (A66). |
| Objects | Fermat quotients, Witt vectors, Λ-rings, arithmetic jet spaces, the prime torus with its Adams semigroup, torsion points and their Galois orbits, smoothed Frobenius graphs at the primes of sparse windows. |
| Language | `p`-derivation, Frobenius lift, Λ-structure, δ-multiplicity, arithmetic jet, auxiliary, local two-sided bound. |
| Mechanisms | Built on: Adams = Frobenius on torsion; minimal auxiliaries = Chebyshev; sharp syzygy cost `p_min^{qr}`; orbit rigidity; Witt Frobenius; sign-free decision [L]. To discover: cheap δ-multiplicity at all primes of a window. |

**Main conjecture (local δ-Stepanov bound).** The vanishing conditions at the fixed points of the Frobenius graphs of all degrees in one `√T` window are met by a δ-auxiliary of δ-degree `(window length)+O(√x log²x)`, along one sparse sequence of scales. **Milestones.** M1 [L] torsion calculus, sharp syzygy cost, minimality of Chebyshev auxiliaries. M2 Stepanov–Bombieri over `𝔽_q` in δ-language. M3 A δ-multiplicity at one prime cheaper than `p`. M4 Simultaneous δ-multiplicity on a window below its Chebyshev count. M5 RH via the sign-free local decision.

## 2.12 New field for RH as AdS physics: adelic holography at the tempered edge

**Does it need a new field?** Yes: the corpus has the horizon (receivers, Krein forms, standard-form no-gos), the archimedean scalar with its two quantizations, the trees at the Ramanujan point, the adelic Green formula, Gram coupling and a discrete adelic quotient, but no bulk theory that contains all places and no duality relating the FE pair to two quantizations.

| Aspect | Content |
|---|---|
| What it is about | A holographic theory on (Euclidean AdS₃ × Π'_p `p`-adic AdS) modulo the rational split torus, with a scalar at the tempered edge at every place, whose boundary two-point function on the degree configuration is Weil's kernel and whose FE pairing is the duality between quantizations. RH is unitarity of the boundary theory. |
| What it would be like | AdS/CFT with real and `p`-adic bulks at once: bulk-to-bulk propagators `G_{1/2}` on geodesics and tree Green functions on apartments; adelic products of local amplitudes; double-trace flows between `Δ=½` and `Δ=3/2`; Krein-space holography for the mirror-even channel of the modular horizon. Prime sources are bulk points, so both self-energies are point-source divergences. |
| Criteria it must meet | Build everything from the places, never from the zeros. Reproduce the adelic Green formula, the spherical compensation, the Gram-coupled defect, the reflection Krein law, the cavity receivers and the Narain remainder. Avoid internal modular conjugation, vacuum-fixing partners and Borchers inclusions. Make `L_a` (off the edge at every place) and graph black holes with `t²>4q` non-unitary. |
| Questions it must answer | Which boundary operator has the seed transforms at a resonance and at its FE partner as two-point functions? Which double-trace coupling relates them, and is the BF window the tempered range at every place? What is the renormalized self-energy of a degree point, and is it Weil's diagonal? What is the confined dual whose normal modes map to the resonances (B117)? |
| Tools it aims to develop | `p`-adic AdS/CFT propagators and boundary correlators; adelic products of amplitudes; arithmetic double-trace flows; Legendre duality of generating functionals with prime sources; Krein holography; Rademacher expansions with arithmetic poles. |
| Objects | `ℍ³` with the degree geodesic, `G_{1/2}`, `G_{3/2}`, spherical functions; Bruhat–Tits trees with `p`-ladders; the discrete adelic quotient; the modular horizon, seeds, cavity functions; reflection Krein forms; the Narain partition function; graph black holes. |
| Language | adelic bulk, tempered edge, quantization, double-trace flow, Legendre duality, BF window, unitarity, reflection pair, resonance, cavity, point source. |
| Mechanisms | Built on: archimedean AdS₃ identity, trees at the Ramanujan point, adelic Green formula, Gram coupling, reflection Krein law, sharp cavity receivers, dual-side no-sign [L]. To discover: the bulk theory and the unitarity of its boundary. |

**Main conjecture (adelic unitarity).** The reflection Krein form of the modular horizon is the two-point function of a unitary boundary theory of an adelic bulk at the tempered edge, obtained from the two archimedean quantizations by a double-trace flow with prime sources. **Milestones.** M1 [L] archimedean identity, trees, adelic Green formula. M2 The adelic bulk propagator on the discrete quotient reproduces Weil's off-diagonal kernel (A70). M3 One damped graph black hole as a unitary flow, one undamped as non-unitary. M4 A universal positive decay rate (zero-free strip). M5 Unitarity (RH).

## 2.13 New field for RH as topology or geometry: adelic potential theory of torus orbits

**Does it need a new field?** Yes. HyperbolicArakelovTheory and SurfaceOfSpecZ have the local pieces (Green functions of all places at the tempered edge), the adelic Green formula, the Gram coupling, the discrete adelic quotient, and the no-gos (one-place carriers, finite-volume embeddings, atomic locking, scalar locking, prime-unit descent) [L]. What none of them has is potential theory for a torus orbit in a product of real and `p`-adic symmetric spaces, in which the diagonal is a global Robin mass.

| Aspect | Content |
|---|---|
| What it is about | Energies, capacities and Robin masses of the orbit of the rational split torus through the base point of `ℍ³×Π'_pT_p`, whose points sit at mutual adelic distance `2log H(n/m)`; the renormalized Green energy of smoothed configurations on the orbit; subcriticality (self-energy dominating mutual energy). The topological branch is an infinite-rank Lefschetz theory of the orientation cover and of the Meyer flow, with a weight filtration. |
| What it would be like | Arakelov theory with hyperbolic archimedean fibre and tree finite fibres; potential theory on products of symmetric spaces and buildings at a fixed spectral parameter; renormalized energies of infinite point configurations; heights of rationals as distances (the product formula as geometry). |
| Criteria it must meet | Reproduce the adelic Green formula, the spherical compensation and plastic sign law, the atomic diagonal of order `N log N`, the logarithmic smooth self-energy, the Gram defect, the discriminant of locked dampings and the prime-unit collapse. Respect the one-place no-go and the lattice no-go (infinite rank). Calibrate on curves over `𝔽_q`, where the diagonal self-intersection is `2−2g`. |
| Questions it must answer | Is the orbit's renormalized energy Weil's form (B133)? What is its global Robin mass, and why is it not the discriminant? Is subcriticality provable by a packing argument for points at mutual distances given by heights? Which correspondence on which space has the centred orientation counts as Lefschetz numbers, and which weight filtration makes its middle piece grow like `N^{½+ε}` (B106)? |
| Tools it aims to develop | Green functions on `ℍ³×Π_{p∈S}T_p` and their torus periodizations; Robin masses and capacities of orbits; heights as adelic distances; renormalized energies; infinite-rank Lefschetz theory with weight filtrations. |
| Objects | `ℍ³` with the degree geodesic; trees with `p`-ladders; the rational split torus and its orbit; the discrete adelic quotient; the 𝔽₁-zonotope and `ℙ¹_ℤ`; smoothed Frobenius graphs; the orientation cover; the Meyer flow. |
| Language | adelic carrier, torus orbit, tempered edge, Robin mass, subcriticality, height distance, mass balance, Lefschetz number, weight. |
| Mechanisms | Built on: adelic Green formula, Gram coupling, discrete quotient, carrier and locking no-gos, orientation-cover weight `≥½`, Meyer Lefschetz trace [L]. To discover: the global Robin mass and a geometric proof of subcriticality. |

**Main conjecture (orbit subcriticality).** Weil's form on smoothed tests is the renormalized Green energy of the degree orbit in the adelic quotient, and every smoothed configuration on the orbit is subcritical. **Milestones.** M1 [L] adelic Green formula; discrete quotient; locking and descent no-gos. M2 Full-degree quotient (A69) and torus-periodized Green functions (A70). M3 A global Robin mass equal to Weil's diagonal. M4 Subcriticality on separated packets from geometry (the subcritical check). M5 Subcriticality (RH). Topological branch: archimedean Stickelberger sign [L]; an infinite-rank Lefschetz theory with weight filtration; the growth of its middle piece.

## 2.14 A research programme to construct `𝔽₁`

**Goal.** Construct the arithmetic surface `Spec ℤ ×_{𝔽₁} Spec ℤ` with an intersection theory in which the graphs of the Frobenius correspondences `Γ_n` meet as Weil's form says, the diagonal has Weil's self-intersection, and a Hodge index theorem holds. Weil's proof for curves would then run over ℤ. The programme is defined by what the corpus has already fixed.

**What the corpus fixes [L].**
- **Points.** The Lefschetz number of `Γ_n` is `N(n)=Λ(n)+1+1/(n²−1)` (the point count of Spec ℤ at degree `n`); `Γ_1·Γ_n` has this value; the minimal integer auxiliary vanishing at the fixed points of all `Γ_n`, `n≤N`, has log length `ψ(N)`.
- **Half-products.** The 𝔽₁-zonotope surface (`Γ_m·Γ_n=m+n`, defect `2Σ_k(Σ_{n>k}a_n)²`, exact count Tate limit) and the `ℙ¹_ℤ` torsion half-product (cusp with jets plus gcd-twisted torsion); neither supplies the diagonal.
- **Fibres.** The archimedean fibre is `ℍ³` with one marked geodesic and Green function `G_{1/2}`; the finite fibres are Bruhat–Tits trees with the Green function at the Ramanujan point; off the diagonal the intersection is the adelic Green pairing.
- **Diagonal.** No local presentation works: atoms give the discriminant (the different of `ℚ(ζ_n)` per unit degree), smoothed scalar locking needs mass balance, Gram coupling leaves a signed defect, the prime unit admits no descent; the atomic surface has genus `≍N log N`.
- **Frobenius.** The exact Frobenius of integer auxiliaries is the Adams operation; the only exact orbit symmetries are integer dilations; Witt vectors carry Frobenius lifts with Galois descent; one Hecke or Adams correspondence replaces the ample axiom, and Riemann–Roch on stable cones forces the Hodge index (the sign).
- **Cohomology.** No finitely generated ℤ-lattice of zero modes is stable under three prime Frobenii: `H¹` has infinite rank or non-integral coefficients. The explicit formula is the Lefschetz trace of the Meyer flow. The orientation cover over ℤ has middle cohomology of weight `≥½`; over `𝔽_q[T]` it vanishes.
- **Counts.** The count half of the Born rule is needed on one ray per prime; `Q` is not integer-valued; arithmetic counts defined before the form exist but none has the right Tate limit.
- **Calibrations.** Over `𝔽_q` every hyperelliptic curve satisfies the count law and Rosati positivity holds; positive integer-norm Beurling systems (monoids with norms: 𝔽₁-objects) carry finite layers and violate the Stepanov bound; heat deformations, symmetric shifts and FE-only models fail; FE + Euler product with integrable defect single out ζ.

**Criteria the construction must meet.**
1. Reproduce Weil's proof for curves over `𝔽_q` (and Deligne's tensor argument) as a special case.
2. Its point counts are `N(n)`, its off-diagonal intersections the adelic Green pairing, its diagonal Weil's diagonal — not the discriminant.
3. It uses the Euler product (points) and the FE (Serre duality) jointly, and fails for Beurling one-offs, heat deformations, symmetric shifts and FE-only models.
4. Its cohomology is infinite rank, carries the Meyer flow, and has a Lefschetz trace equal to the explicit formula.
5. Its Frobenius is the Adams/dilation semigroup on the prime orbit and a Witt/Λ-structure on rings.
6. Its positivity is proved, not assumed: a Hodge index from an effectivity or ampleness property intrinsic to 𝔽₁-geometry, which λ-ring effectivity alone does not give.

**Questions it must answer.**
- What is the 𝔽₁-surface: a Λ-scheme (Borger), a monoid scheme or blueprint (Lorscheid), the arithmetic or scaling site (Connes–Consani), a foliated dynamical system (Deninger), or the adelic quotient of the split torus?
- What is the diagonal, and why is its self-intersection Weil's diagonal rather than the discriminant?
- What is ampleness over 𝔽₁, and why does Riemann–Roch on the surface imply the Hodge index?
- How do the infinite places enter (the `ℍ³` fibre at `Δ=½` and the pole as spherical piece)?
- Why does ζ satisfy the Hodge index while Beurling one-offs, which are also monoids with norms, do not?

**Tools it aims to develop.** Λ-rings and Witt vectors as Frobenius-lift structures; monoid schemes and blueprints; tropical and semiring geometry of the scaling site; Arakelov geometry with hyperbolic and tree fibres; renormalized intersection theory at the critical weight; infinite-rank Lefschetz theory with weight filtrations; Riemann–Roch on the scaling site.

**Objects.** Spec ℤ over 𝔽₁; the monoid `ℕ^×` and the prime orbit torus; Frobenius graphs `Γ_n`; the 𝔽₁-zonotope and `ℙ¹_ℤ`; the adele class space and the split-torus quotient; Witt and Λ-structures; the Meyer flow; the orientation cover.

**Mechanisms it must build on or discover.** Built on: point count `N(n)`, half-products, adelic fibres, adelic Green formula, Gram coupling, Witt Frobenius, λ-ring effectivity ⇔ Hodge index, Meyer Lefschetz trace, lattice no-go, count door on one ray per prime [L]. To discover: the diagonal as a global self-intersection; ampleness over 𝔽₁; a Hodge index proof that sees the FE and the Euler product together.

**Milestones.** M1 [L] point count, half-products, fibres, Lefschetz trace, λ-ring effectivity ⇔ Hodge index, lattice no-go. M2 An 𝔽₁-surface whose intersection pairing on the Frobenius graphs is Weil's form including the diagonal (no discriminant defect). M3 Riemann–Roch on it with the FE as Serre duality. M4 Hodge index on finite truncations with explicit errors, checked against the eighth-root positivity theorems. M5 Hodge index (RH).

**Decisive early test.** The integer-norm one-off is a monoid with norms whose zeta function has an off-line pair; it violates the Stepanov bound for every constant [L]. An 𝔽₁-theory whose effectivity implies the Stepanov bound at the prime degrees separates ζ from it; one that does not cannot prove RH.

## 3. The one big question: does a remainder that approaches the line land on it?

**Question (B138).** *Is there a landing law for ζ?* Suppose ZAL: for every `σ>½` only finitely many zeros lie right of `σ`. Must all but finitely many zeros then lie on the line? Equivalent forms [L]:
- **Hadamard threshold.** Eventual Hadamard positivity (`Re ξ′/ξ≥0` on `Re s≥σ` above a height `T_σ`, every `σ>½`) is ZAL; the threshold `T_σ` is antitone toward the line; landing says it stays bounded as `σ↓½`.
- **Krein index.** Eventual Hadamard positivity forces finite Krein–Langer index of the Weil kernel `K_ζ`, or ZAL forces finite index on the `{2,3}` lattice.
- **Heat, slices, gaps, bound states.** ZAL forces bounded non-real heat counts, eventual slice positivity, the filtered central-gap budget, or a finite-dimensional odd bound-state space.
- **Tail law.** Under ZAL the critical line holds above some height.
- **Prime side** [D from L]. Under ZAL the finite exponential corrections in `ψ(x)−x=S_ε(x)+O(x^{½+ε})` stabilize as `ε→0`.

**Why this question.** RH ⇔ ZAL ∧ B13 ∧ Landing [L]. ZAL is at least quasi-RH; B13 contains the exclusion of a single off-line quartet; DH is off the RH path. Landing is the one atom of the RH path that is neither: an implication between two tail laws, both unchanged by moving finitely many zeros. It never asks to exclude a single zero, and the two-scale obstruction, which blocks every input about the zeros above a height from deciding B13, does not apply: landing is itself a tail law, so an input about the zeros above every height may decide it. It is also the gate between two families of receivers: every ZAL receiver (inner-field decay, subtracted lag, `Λ_Xlog X→0`, eventual Hadamard positivity, high-collision counts) on one side, every finite-stratum receiver (finite index, heat counts, slice positivity, central gaps, odd bound states, `N_d` bounded, one non-blind tower) on the other.

**Why it is less hard than ZAL, AAL, RH and quasi-RH [L/D].** AAL and RH imply it; it implies none of ZAL, quasi-RH, B13 or AAL (a configuration accumulating at `Re s=1` lands vacuously; one reflection pair lands and violates B13) [L].

**What either answer gives.**
| Answer | Effect |
|---|---|
| Yes | RH ⇔ ZAL ∧ B13 and `ZAL⇒RH` ⇔ B13. Every ZAL receiver becomes a finite-stratum receiver and every finite-stratum receiver becomes, with B13, an RH receiver: the heat route (bounded counts), LA (`N_d` bounded), HF and HKT (finite index), WD and CTF near-line receivers and ZCG collapse into one family; the near-line wall is absorbed into ZAL; the RH core is two inputs, a tail law and the finite stratum. A proof would be the first producer of a depth-blind statement |
| A proof that FE ∧ Euler identities of the corpus cannot decide it | landing is independent of every identity used so far, as B13 and DH are; landing by discreteness, integrality, heat flow, positivity or Hadamard factorization is closed; the RH core is three FE–Euler atoms |

**What is proved and usable [L].** The eleven-form TFAE; `hadamardThreshold` antitone; the collar: under ZAL Hadamard positivity holds right of `½+r` above a height for every `r>0`; under ZAL every observation line `σ>½` sees finitely many zeros, so the finite exceptional subtraction of the Gaussian current, its exponential-damping expansion and the damping filters apply at every `σ>½`; a zero of depth `δ` is invisible at speeds `a<π/(2δ)`, and under ZAL ∧ ¬FiniteOffLine every speed loses infinitely many off-line modes; calibrations: the FE model with approaching quartets and the approaching integer-norm Euler product both violate landing, so the input must use the FE and the Euler product together; heat finiteness at `t>0` (Ki–Kim–Lee) does not pass to `t=0`; symmetric shifts violate ZAL and land vacuously, so temperedness is not needed for landing (`Θ∞≥σ₂`) [D].

**First step and obstacle.** Under ZAL, `T_σ` is finite and nondecreasing as `σ↓½`; landing says `sup_σ T_σ<∞`. An off-line zero at depth `δ<1/log γ` makes `Re ξ′/ξ` negative only in a disc of radius `≍δ` beside it, against the density `½log γ` of the zeros on the line [D]; in the exponential current it is supercritical only at speeds `a>π/(2δ)` [L]; in the spline trace it becomes visible at scales `u≳4log γ/δ` [D]. The named obstacle: every producer in the corpus loses an off-line zero at a rate set by its depth, so a world of infinitely many off-line zeros approaching the line is invisible at any fixed resolution. Four receivers are blind to depth — sign-change counting of Hardy's `Z` (each off-line pair costs two sign changes against the count `θ(T)/π+S(T)`), the Krein–Langer index of `K_ζ`, the negative index of the cavity's reflection Krein form (one negative square per off-line zero), and the non-real heat count `N(t)` at small `t`. The question is whether one of them has a producer under ZAL: an argument that turns "finitely many zeros beyond every positive depth" into "finitely many negative squares".

**Tests.** T1: implied by RH; implies neither quasi-RH, ZAL, B13 nor AAL. T2: an implication. T3: the table. T4: a tail law; no finite rung decides it [L]. T5: false on the FE model with approaching quartets and on the approaching integer-norm Euler product [L]. T6: not refuted. T7: moves B111, B13 and its receivers, B23, B57, B66, §1.9, F1, F8, F20, F23. T8: not a named problem; its difficulty is the near-line wall restricted to a world in which every line `σ>½` sees finitely many zeros.

**Limit.** It proves neither ZAL nor B13; a Yes makes RH exactly ZAL ∧ B13.

### Alternatives considered
| Question | Effect | T8 verdict |
|---|---|---|
| Bounded windows (B140, §2.4) | RH as local purity at bounded ratio; or an interference theorem | passes; prime side only |
| Deuring–Heilbronn for ζ (B141, §2.5) | AAL reduced to the RH path | contains an isolated-top exclusion over a `¬ZAL` remainder |
| Polar orthogonality (B104) | whether the pole channel detects ¬RH before the window | passes; Σ block only |
| Specialization at the jump (B142) | whether Deligne's family step exists over ℤ | passes in method form; a positive answer is RH-strength |
| Robin-subcritical torus orbit (B133, §2.8) | a geometric presentation of the diagonal | producer; large |
| `ZAL⇒RH` (B111) | the AAL content of the RH path | fails: contains B13 |
| Finite stratum B13; one-quartet world (B134) | excludes the minimal finite layer | fails: single-quartet exclusion |
| Breadth below the Dirichlet scale (B97, B137) | sign-free producer | fails: past VK |
| Sampling-set bound, metric recurrence (B126, B127) | AAL | fail: contain AAL |
| Local criteria (A64, A65, A71) | sharper receivers | just work |
| Halving pairs (B125) | one-eigenform receiver | excludes a configuration of zeros |
