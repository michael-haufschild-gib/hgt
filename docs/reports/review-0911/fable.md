# Consolidated review — big picture, obstacles, questions, programmes

**Sources.** [Frontier map](../rh-current-frontier-map.md), [scoped obstructions](../rh-killed-routes.md), [unification ledger](route-unification-ledger.md), [route obstacles](route-obstacles.md), [walls ledger](walls-ledger.md), [obstacles summary](obstacles-summary.md), and the Lean corpus through `scripts/formal_tools.py research`. Working log: `logs/review-0911-fable-research-log.md`.

**Evidence.** `[L]` Lean, as recorded in the ledgers. `[L*]` Lean statement read for this report. `[D]` deduction made in this report, not a Lean theorem. `[C]` classical or published mathematics, not in the corpus. `[A]` assessment.

**Where the ledgers and the corpus differ.** The corpus contains `riemannHypothesis_iff_prime_logSquare_windows` (`SurfaceOfSpecZ/ScaleLocality/PrimeLogSquareWindows.lean`) `[L*]`: the `log²T` criterion that walls Σ146 and task A64 list as not assembled is a theorem. The full-degree projective adelic carrier and its prime Hecke operators are formalized (`TheFullAdelicDegreeConfiguration`, `ThePrimeAdjacencyOnTheAdelicCarrier`) `[L]`; Γ189 and A69 list them as a stub.

---

## 1. The big picture

### 1.1 One object

The 38 live formulations and 9 candidates are readings of one quantity. For the cubic spline `B` let `c_B(u)=Re S(u)` be its orbit correlation under Weil's form; then `c_B(log d)=A(d)−P(d)`, where `P(d)` is the smoothed von Mangoldt count in the multiplicative window of `d` and `A(d)` its archimedean-plus-pole prediction `[L]`. Both have size `√d`; only the difference matters.

| Statement | Reading |
|---|---|
| `c_B(log p)≥−K` at every prime | Weil positivity of the two-bump test `B+τ_{log p}B` (U-Σ) |
| `P(p)≤A(p)+K` at every prime | a crude prime count; Stepanov's bound for the smoothed Frobenius graph of degree `p` (U-Π) |
| the class `Γ_1+Γ_p` carries an `ℕ`-count with Tate limit `2c_B(0)+2c_B(log p)` | the count half of a Born rule (U-Γ) |
| `\|c_B(log p)\|≤K` at every prime | the same decision with no sign: absolute convergence, continuation, Laplace rate theorem |

Each line is equivalent to RH `[L]`. The same statements with `Kp^a` in place of `K` are equivalent to zero width `≤a`. The object is local in scale: RH ⇔ there is `K` such that for arbitrarily late `T` every prime with `|log p−T|≤C log²(T+2)` has `2c_B(log p)≥−K` `[L*]`; and if RH fails, every sufficiently late window of that radius contains a prime violating any prescribed `K` (`eventually_prime_logSquare_window_negative`) `[L*]`. Unconditionally `|P(n)−A(n)|≤C√n·exp(−(log n)^{3/5}/(10⁸ log log n))` `[L]`.

Why there are three families of routes `[D]`: no test is compact on both sides of the explicit formula. A compact prime side (windows) leaves infinitely many zero modes and only an exact sign decides. A localized zero side lets a crude bound decide but puts the whole difficulty into square-root precision of a prime count. The third family is the involution `ρ↦1−ρ̄` and the vertical position of the zeros.

### 1.2 The second coordinate: three atoms

With `Θ=sup Re ρ` and `Θ∞=inf{σ: finitely many zeros right of σ}`:

- **ZAL** `Θ∞=½`; **AAL** `Θ=Θ∞`; **B13** finitely many off-line zeros ⇒ none; **Landing** ZAL ⇒ finitely many off-line zeros; **DH** ¬AAL ⇒ ZAL.
- RH ⇔ ZAL ∧ B13 ∧ Landing; AAL ⇔ B13 ∧ Landing ∧ DH; no two of B13, Landing, DH fail together `[L]`.
- ¬AAL ⇔ a finite nonempty top layer at some `β*<1` over a remainder at `Re s≤β*−η` (`not_asymptoticAbscissaLaw_iff_bilateral_spectralGap`) `[L*]`. Hence **quasi-RH ∨ AAL** is a theorem, and quasi-RH ⇔ `Θ∞<1` `[D]`: quasi-RH is a tail law.

The curve proof needs neither coordinate: finite rank makes ZAL automatic and periodicity of the zeros in height makes AAL automatic `[L]`.

### 1.3 Hard obstacles that are solved

| Obstacle | What is now a theorem | Anchor |
|---|---|---|
| "Many routes" | one inequality per prime; route classes by source identity | SOSZ, CDGeo `[L]` |
| Attainment and global data in the decision step | decisive samples of density zero; `√T` and `log²T` windows; positive infinite deletion | SOSZ ScaleLocality `[L*]` |
| A decision step without positivity | two-sided gap iteration | `TwoSidedGapIteration` `[L]` |
| Structure of the exceptional coordinate | three atoms, strict dial, landing in eleven forms, DH classified on models, two-scale law | ZCG AbscissaLaws, ELT `[L]` |
| The finite-layer world | rigid description of ¬AAL: finite oscillation of `ψ`, top-layer wave, filters reading each mode | ELT, EFT `[L]` |
| Critical compactness of the atomic matrix | `R_c=R_PSD=R_polar=R_halfline≤R_prim=R_high=W`; Γ-liminf; charged compactness | AHD, CACT `[L]` |
| Subcritical positivity | complete matrix PD for exponent `<1/8` and one critical multiple | CACT `[L/K]` |
| The window chain | precontact canonical system, `L′=q−sinh 2L`, restoring bound, RH ⇔ `Ψ` locally bounded | CSTW, AIF `[L]` |
| Identification of ζ | FE with `L¹` or `L²` defect ⇒ rational primes; degree-one Selberg class; count distance `o(log n)` | EFT, SEL, SPAL `[L/K]` |
| Exact Frobenius over ℤ | orbit preservers are (Laurent) Adams maps; integrality acts only on the torsion; exact Stepanov count = Chebyshev | ALST `[L]` |
| Returns of the prime orbit | depth law (Baker), breadth to the VK height, collective counts beyond the depth floor | TTPO, CDGeo `[L]` |
| The off-diagonal of Weil's kernel | pole − `ℍ³` Green function at `s=½` − tree Green functions at the Ramanujan point; Gram coupling; discrete adelic carrier with commuting prime operators | SOSZ, HAT `[L]` |
| The horizon | one cuspidal cavity function sees every resonance; reflection Krein form has one negative square per off-line zero | AHMH `[L]` |
| Deligne's steps over ℤ | Künneth for the zero motive, exact tensor weights, generic purity and big monodromy of the gauge family, jump at ζ | AWT `[L]` |
| Census | simple critical zeros `≥(0.67250071−ε)N(T)`; `4/5` of the ordinates critical | Zeta23, IGP, RHTower `[L*]` |
| Finite verification | RH through height 67, `PF₂₀₀`, Li `n≤314`, theta rank 14 | VHR, TCS `[L]` |
| Scope of failed mechanisms | 42 dead mechanisms and the scoped obstructions, each with its survivor | killed-routes |

### 1.4 What stands between the corpus and a proof

**(a) No producer for the minimal face.** Every unconditional saving in the corpus is the Vinogradov–Korobov saving. On the width axis every interior value is a zero-free strip; there is no rung between VK and quasi-RH.

**(b) The three atoms.** ZAL is at least quasi-RH. B13 contains the exclusion of one off-line quartet. Landing is undecided for ζ; it fails with the FE alone and with the Euler product alone `[L]`.

**(c) Four structural gaps** `[L/D]`: the dark range (Dirichlet polynomials longer than the height; primes past the Kronecker scale); the diagonal of Weil's form (no counterterm-free positive presentation); the two-scale FE–Euler input (an inequality the explicit formula does not imply); the jump at ζ in every family of twists.

**(d) Rigidity, read as an obstacle** `[D]`. Three theorems of the corpus say one thing: ζ has no moduli.

1. FE-defect isolation: in the class of countable Beurling systems, an FE with integrable defect forces the rational primes `[L]`.
2. Degree-one classification: degree one and conductor one is ζ `[L/K]`.
3. Summable Euler deformations keep the zeros; deformations that move zeros are analytically disconnected from ζ `[L]`.

Two consequences follow.

- *No calibration with both structures.* Inside the class where the Euler product and the FE both hold, every atom is a statement about a single object. The fakes of the corpus each drop one structure. A mechanism that uses both cannot be tested on a fake of the same class; test T5 loses its force exactly where the atoms live.
- *ζ is the fixed part.* In every family of twists or covers (gauge torus, Dirichlet characters, vertical shifts, Dedekind zeta functions, Rankin–Selberg squares `L(s,u×ū)=ζ(s)L(s,sym²u)`), the zeros of ζ are the part common to all members. Family averages remove it: the principal character is the main term of every large-sieve identity `[C]`, and the trace-constant sets of the gauge family avoid a neighbourhood of ζ `[L]`. Deligne's family step bounds the variable part of a family. A rigid base gets its purity from the base itself: a surface with a Hodge index (Weil), or a count with an auxiliary function (Stepanov). §5 turns this into the proposed question.

**(e) Sharpness in the coefficient size** `[D]`. The symmetric shift `ξ(s+a)ξ(s−a)` has an Euler product with nonnegative von Mangoldt coefficients and an FE, and violates ZAL for every `a>0` `[L]`. Its prime coefficients are `p^a+p^{−a}=2+a²log²p+…`. Any argument that tolerates a loss `p^ε` in the size of the coefficients, or that uses only Euler positivity and the FE, is refuted by this family; a proof must use the exact normalization (pole at distance exactly `½` from the centre, one Gamma factor).

---

## 2. Opportunities

Ranked by what they would change. None closes a wall named in §1.4.

| # | Opportunity | What it gives | Status |
|---|---|---|---|
| 1 | **Halving chains terminate** (§11.1) | the halving-pair half of B125 is void; a single Hecke eigenform fails as a receiver only at zeros of its Shimura integral along half-descent orbits | assembly of two existing Lean modules `[D]` |
| 2 | **Fixed-part theorem for families** (§5, §11.2) | decides the tensor/family branch of U-Π (B85, B86, B142) | first steps in Lean; statement `[D]` |
| 3 | **Higher Gram moments for the census** (§4.3) | a route to `70%` that needs no prime pairs `Λ(n)Λ(n+h)`; the off-diagonal is a shifted convolution of `Λ∗Λ` | open; model value `16/21` `[L]`, ζ-moments beyond `α+β<1` open |
| 4 | **Multiplicative functions in short intervals** (§11.4) | the first unconditional saving, in law, for long Möbius and Liouville mean values past the height; answers the "prime-density saving in the collision count" of Π103 for `λ` | published `[C]`; not in the corpus |
| 5 | **Logarithmic windows** (B140, active card) | radius `C log T` for the minimal face through the positivity-repair conjecture | in progress; `exists_negativeRootMultiplier_repair` `[L]` |
| 6 | **Global Green resolvent on the adelic carrier** (B133, active card) | Weil's off-diagonal as one Green kernel; the diagonal as a global Robin mass | carrier and prime operators `[L]`; analytic part open |
| 7 | **Unassembled corollaries**: two-prime local criterion (A65), dominant-ordinate divergence (A67), finite-stratum laws on the cosine and shifted Jensen families (A50), landing calibration with ζ's Gamma factor (A68) | sharper receivers and one calibration | `[D]` in the ledgers |
| 8 | **Quasi-RH in its weakest form** (§3) | a one-sided power saving on sparse `log²` windows | criterion `[D from L]`; no producer |

Two further observations.

- **The ¬AAL world carries its own zero-free strip.** Since ¬AAL forces `Θ=β*<1`, every conditional theorem of the form "a strip of depth `h` gives …" holds in that world: heavy returns of the primes `≤y` need `log t≥c·y^{1−β*}` (`AZeroFreeRegionBoundsTheHeavyReturns`) `[L]`, and Mertens has a power saving. A contradiction search for AAL may assume these `[D]`. They do not produce a contradiction: the finite-layer identities stay consistent.
- **The exceptional-current cards.** The detection range `dκ<a(β−σ)/2−π/4` and the decay range `dκ≥a(1−σ)/2` are separated by the fixed gap `a(1−β)/2+π/4` `[L]`, and the filtered current is the filtered zero sum. An upper bound at an abscissa `c<1` is therefore a statement about the remainder abscissa `[D in the ledgers]`. The card `b13-arithmetic-upper-bound-for-damping-filters` asks for an estimate of the strength of the exclusion it is meant to prove unless an inequality using the FE is named `[A]`.

---

## 3. Quasi-RH: is there a clear path?

**No.**

What the corpus establishes.

- Every interior value of every width parameter is a zero-free strip: Möbius or Liouville power saving, a polynomial stencil rate `K^{−a}`, a horocycle or Farey or cavity exponent past `½`, a growth exponent `p^{a}`, `a<½`, of either side at the primes, a tensor-moment slope, a heavy-return exponent `[L]`.
- All unconditional savings are VK `[L]`.
- Quasi-RH ⇔ `Θ∞<1` `[D]`: only the tail matters, so the two-scale obstruction of B13 does not apply.
- Weakest prime-side form `[D from L*]`: by `zeta_prime_logSquare_windows_transfer` and `zeta_re_le_of_logSquare_windows`, a bound `2c_B(log p)≥−Kp^{α}` with some `α<½` on the primes of arbitrarily late `log²` windows gives width `≤α` (directly for `α≥1/6`; for smaller `α` after a first step at exponent `1/6`, since the prime-gap transfer loses `1/3` per step); conversely width `w` gives the bound with `α=w` at every prime. Quasi-RH is a one-sided power saving of the smoothed prime count on a sparse sequence of windows `[x·e^{−C(log log x)²}, x·e^{C(log log x)²}]`.

Why this is not a path.

1. The only mechanism known for a zero-free region is Euler positivity at the pole combined with growth bounds; its limit is VK, and Lindelöf-strength growth does not imply a strip `[C]`.
2. Beurling systems with integer-like counting can have zeros approaching `Re s=1` `[C]`; the Euler product and regular counting do not give a strip. Return bounds are statements about the labels `log p` and are shared by `ζ(s−h)` `[L]`.
3. A failure of quasi-RH is an AAL world with zeros approaching the 1-line on a set of heights of density zero; statements in law do not see it `[L/D]`.
4. On the width axis there is no intermediate rung: improving `exp(−(log)^{3/5})` is "past VK", a named problem.

A proof of quasi-RH would have to be a new mechanism, not an assembly. The corpus identifies where it must act: a pointwise statement on density-zero heights, using the coefficient size.

---

## 4. Seventy per cent of the zeros on the line

### 4.1 Status

- `simple_critical_proportion_ge_67250071` `[L*]`: simple critical zeros are at least `(0.67250071−ε)N(T)`. The constant is `HD(1)+10⁻⁸`, `HD(1)=3/2−cot(1/√2)/√2`. `HD(1)` is the explicit-formula Gram certificate at bandwidth `λ=1` in the `Zeta23` package; the `10⁻⁸` is the disjoint-pair pinching slack of IncommensurableGaborPinching, a zero-side gain.
- `four_fifths_critical_ordinates` `[L*]`: `4/5` of the distinct ordinates are critical.
- `seventy_percent_or_simple_offLine_near_line` `[L*]`: for every `A>0`, either `N₀≥(7/10)N` or at least `(HD(1)−2/5−1/A−ε)N` simple off-line zeros lie within `A/log T` of the line. A failure of `70%` needs more than a quarter of all zeros to be simple, off the line and at depth `O(1/log T)`.
- Positivity together with sub-threshold data cannot reach `3/4` (`PositivityCannotReachTheThreeQuarterThreshold`) `[L]`.

### 4.2 The trans-threshold route

At bandwidth `λ>1` the Gram certificate is `2−κ(λ)` with `κ(λ)=1/λ+(2/λ²)∫₀^λ(λ−α)F(α)dα` `[L]`. The corpus proves unconditionally `[L]`:

- `(29/36−32πε₁−ε)N − coalescentSurplus ≤ N₀*` at `λ=4/3`;
- `(Hcos(λ)+δ_λ−ε)N − S_λ ≤ N₀^{simple}` for `0<λ≤2`, with coefficients `3/4+79/1250` at `4/3` and `5/6+43/3750` at `2`.

| Target | Budget for the surplus per `N(T,2T)` |
|---|---|
| beat `2/3` | `<5/36` |
| beat `HD(1)` | `≤577/4500` |
| `70%` | `≤19/180≈0.106` (boxcar, `λ=4/3`); `≤0.113` (cosine, `4/3`); `≤0.145` (cosine, `2`) `[D]` |
| `75%` | `≤1/18` |
| Hardy–Littlewood value | `−1/144` |

In form-factor terms, a bound `F≤Υ` on `(1,4/3)` gives the proportion `7/8−Υ/16`: `70%` needs `Υ≤2.8` `[D]`.

The surplus is a sum over odd primes at even shifts `p, p+2r` with `|log(n/m)|≤T^{−1+η}`, `n≈T^{4/3}`, against a signed kernel `[L]`. The model part (singular series) is evaluated and gives a negative Ward–Mertens term `[L]`. The remaining discrepancy is a prime-pair correlation in shifts up to `X^{1/4+}`. Three facts decide its difficulty.

1. Unsigned bounds diverge (`sum_Icc_abs_cosTransform_ge_inner_lobe`); an unsigned additive sieve would need a constant `≤8/9` `[L]`.
2. The main terms cancel; what must be bounded is of second order. In the classical language this is the variance of primes in intervals of length `≈X^{1/4}` to within a constant factor of `hX log X` `[D]`. Asymptotics for almost all shifts with a saving `log^{−A}` per shift do not reach it; the required saving per shift is a power `[D]`.
3. A bound `F≤2.8` on average over `(1,4/3)` is not among the consequences of RH that are known `[C/A]`.

**Verdict: no clear path.** The route is exact up to one estimate, and that estimate is a binary additive problem at a precision not available even conditionally.

### 4.3 A second route `[A]`

The certificate uses the first two moments of the on-line Gram matrix. The corpus has the next moments in the unconditional range: the triple form factor vanishes and the four-level form factor factorizes for `α+β<1`, with the diagonal fourth moment for `α<½` `[L]`; with sine-kernel moments `(1,4/3,2,13/4)` the model certificate is `16/21` `[L]`; the blind spot is exact through third order `[L]`. Extending the fourth moment to wider frequencies is listed as open.

Its prime side is a mean value of a product of two prime polynomials, hence a shifted convolution of `Λ∗Λ` with shifts up to `T^{2λ−1}`. This has bilinear structure, which `Λ(n)Λ(n+h)` lacks, and bilinear forms of this type are the setting in which lengths past `T^{1/2}` have been reached for mollified moments `[C]`. Whether a fourth-moment certificate at a bandwidth slightly above `½`, combined with the second-moment certificate at `λ=1`, exceeds `70%` is a finite optimization once the admissible range is known. The model value is not a ζ-proportion.

---

## 5. The one big question

### 5.1 Questions not to pose

| Question | State |
|---|---|
| B131 Deuring–Heilbronn question | settled: DH is off the RH path; classical repulsion calibrated; no Siegel regime |
| B132 almost all primes | settled: No; power-thin exceptions keep the criterion |
| B136 decisive samples with large gaps | settled: they exist |
| B138 landing | resolved in the sense posed: three-atom factorization; fails for the FE alone and for the Euler product alone |
| B139 scale-local sampling; A64 | settled: `√T` and `log²T` windows |
| B140 bounded windows | open; attacked by the positivity-repair card |
| B141 DH for ζ | open; posed |
| B142 specialization at the jump | open in method form; §5.2 proposes its decisive form |

### 5.2 The question

**Is the zero motive of ζ the fixed part of every arithmetic family?**

*Precise form.* Let `𝔉` be a family of Euler products with a measure `ν` under which even moments of window traces are computed by orthogonality: the gauge torus, the characters modulo `q≤Q`, the vertical line, Hecke eigenforms under the Weyl law, number fields under a counting measure, and their mixtures. Decompose the trace of a member as (trace of ζ) + (variable trace). Prove or refute:

> **(FP)** For every such `(𝔉,ν)` and every `k`, the `2k`-th moment identity of the family controls the variable traces only: the centred trace of ζ enters with `ν`-mass tending to zero or as an exact common factor, and no inequality derived from the family bounds `|c_B(log p)|` below the trivial bound.

A refutation is a family in which the fixed part inherits a weight bound from the variable part.

*Why this question.*

- It decides a whole branch. The tensor-power trick, the gauge family, Künneth, the edge divisor and exact-monodromy pricing are theorems `[L]`; the only missing item of Deligne's argument over ℤ is the family step. If (FP) holds, the branch (ACS tensor branch, B85, B86, B142, the AWT and AK programmes as producers, the tensor-loss branch of SC) has no producer and RH for ζ must come from the base: the surface (sign) or the count (auxiliary). If (FP) fails, the counterexample is a Deligne route over ℤ.
- It is implied by nothing about the zeros and implies nothing about them: a method question.
- The corpus already contains the first steps: `ExactMonodromyPricesEveryFibreAtTheTrivialBound` (orthonormal families price a fibre at the trivial bound), `TheTrivialFibreIsTheJump` (trace-constant sets avoid ζ), `EulerDeformationsOfZetaAreIsozeric`, the FE-defect isolation theorems, and the diagonal identity of AHMH in which `ζ(s)` factors out of every Hecke energy `[L]`.

*First step.* State (FP) for mixtures of the two proved cases (exact orthogonal families; summable deformations) and for Rankin–Selberg families, where `Σ_j h(t_j)L(s,u_j×ū_j)=ζ(s)·Σ_j h(t_j)L(s,sym²u_j)` exhibits ζ as an exact common factor.

*One named obstacle.* Families whose degree or conductor grows and in which ζ is a factor but the orthogonality is not exact: the fixed part is then coupled to the variable part through the nonnegative coefficients of the product (the mechanism that gives zero-free regions for `sym²` from the pole of ζ `[C]`). The question is whether this coupling can run in the other direction with a bound better than trivial.

*What either answer gives.*

| Answer | Effect |
|---|---|
| (FP) holds | Deligne's family step does not exist over ℤ for a rigid base; the tensor/family branch is support, not a route; the producer problem is confined to the surface and to the count |
| (FP) fails | a family that sees the fixed part; uniform tensor moments `A_k=o(k)` become a target with a mechanism |

*Tests.* T1 method. T2 an implication or a counterexample. T3 the table. T4 no finite rung. T5 calibrated on curves over `𝔽_q`, where the target curve is a variable fibre of a pencil and the family step works, and where the constant part of a family is not reached by monodromy. T6 not refuted. T7 moves B85, B86, B142 and class C94. T8 not a named problem; the first step uses corpus objects.

*Limit.* It decides where a producer can live. It produces none.

### 5.3 Runner-ups

| Question | Why second |
|---|---|
| B141 DH for ζ | the only atom-level question that is neither a single-quartet exclusion nor ZAL; no first step beyond the model classification |
| B140 bounded or logarithmic windows | under attack; a criterion, not a producer |
| B104 polar orthogonality of a half-line ground state | confined to the critical curve |
| B133 global Green resolvent | a producer question of large size; the sign remains after it |

---

## 6. The one big question without positivity and without spectral theory

"Spectral" and "positivity" are read as in §2.6 of the obstacles summary. What survives is recorded there: the two-sided decision step, Turán elimination, integrality on the torsion, transcendence, collective return counts, exponential sums to VK.

**The frontier under this constraint** `[D]`. The receiver side is complete: RH ⇔ `|c_B(log p)|≤K` at the primes, and the width version. The producer side is capped at Chebyshev (integrality), at VK (exponential sums), at the trivial separation bound (freezing) and at the depth floor (transcendence). There is no sub-quasi-RH rung on the width axis, so the question has to be about the structure of sign-free proofs.

**Two sign-free proofs of a Riemann hypothesis exist.**

1. *Stepanov–Bombieri for curves.* Its input is not the counts, the FE and integrality: the golden datum at `q=5` has positive integral counts, an FE and an Euler product, and is impure `[L/K]`. The input is the Frobenius as a ring endomorphism with zero derivative, which makes high-order vanishing at all rational points cheap.
2. *The Riemann hypothesis for the Carlitz–Goss zeta function of `𝔽_q[T]`* (Wan, Diaz-Vargas, Sheats) `[C]`. The object has infinitely many zeros and no finite-rank cohomology. The proof computes the Newton polygon from valuations of power sums: the slopes are distinct, so the roots have distinct valuations, so the Galois group, which preserves the valuation, fixes each root. Purity is proved by **separation**: an invariant of the symmetry that takes different values on different zeros.

**The question.** *Does ℤ carry a shadow of either mechanism?* In decidable parts:

- **(S1) Endomorphism.** Is there a commutative ring with commuting endomorphisms `F_n`, `F_mF_n=F_{mn}`, whose fixed-point counts are the point counts `N(n)=Λ(n)+1+1/(n²−1)` of Spec ℤ, on which an auxiliary vanishing to order `m` at the fixed points of the degrees of one `log²` window costs less than `m` times the window's Chebyshev count? The corpus fixes the archimedean answer: with the Adams operations on the prime torus the minimal auxiliary costs exactly `ψ(N)`, and exact order costs the degree `[L]`. So the multiplicity cannot be archimedean order.
- **(S2) Separation.** For ζ the symmetry is `ιc: ρ↦1−ρ̄`, which preserves the height. RH ⇔ every fibre of the height map on the zero set is a single point on the line `[D]`. Is there a sign-free prime-side quantity that bounds the fibre multiplicity `m(γ)=#{ρ: Im ρ=γ}`? The census bounds it by a rank–trace inequality, which is a positivity argument; the degree-`j` ledgers of RAC detect analytic multiplicity `[L]`, not fibre multiplicity.

*Why this question.* It replaces "find a producer past VK" by a test with two calibrations. The corpus's sign-free toolkit can be run on the Carlitz–Goss zeta function: either it proves that theorem, or it is missing the ultrametric separation step, and then (S2) names what is missing over ℤ. The answer to (S1) decides whether a Stepanov route needs a Frobenius-lift structure (§9) or is closed.

*Tests.* T1 method. T2 two existence statements and one reproof. T3 above. T5 calibrated on the golden datum (fails, as it must), on curves and on `𝔽_q[T]` (succeeds), on the integer-norm one-off (must fail: it violates the Stepanov bound for every constant `[L]`). T6 not refuted; the archimedean form of (S1) is refuted. T8 not a named problem.

*Limit.* Both calibrations are in characteristic `p`. Over ℤ no object is constructed.

---

## 7. A new field for the walls

**Infinite-rank purity theory: Weil numbers without finite rank and without moduli.**

*What it is about.* Frobenius modules of infinite rank with a duality: the zero motive `M=⊕ℤ(−ρ)` on which the Frobenius at `p` acts by `p^ρ`, with the pairing `ρ↔1−ρ`, the trace `Σ_ρ n^{ρ}`, and the archimedean involution `ρ↦ρ̄`. In finite rank four tools give purity: rationality of the characteristic polynomial, Galois conjugation, Kronecker's theorem, and the determinant weight. The field asks what replaces each when the rank is infinite and the object is rigid.

| Finite rank | Infinite-rank counterpart | State |
|---|---|---|
| Newton–Girard elimination | exceptional-rank window theorem, infinite Turán sums, positive deletion | available `[L]` |
| Finitely many eigenvalues | well-foundedness of the towers (ZAL) | open |
| Conjugates share their absolute value | zero transport (AAL); eventual bounds are global | open |
| Irreducibility of the characteristic polynomial | no finite stable exceptional set (B13) | open |
| Closedness of the set of weights | landing | open |
| Integer traces ⇒ algebraic integers ⇒ Kronecker | traces in `ℤ·log p`; count-distance rigidity; FE-defect rigidity | rigidity theorems `[L]`; no purity consequence |
| Determinant weight from the pairing | FE fixes the weight of each pair `{ρ,1−ρ}` only if the pair is irreducible | the content of RH |
| Integral lattice stable under Frobenius | none: no finitely generated lattice is stable under three prime Frobenii | no-go `[L]` |

*Point of view.* RH is the statement that two involutions of the zero set coincide: the algebraic one `ι: ρ↦1−ρ` and the archimedean one `c: ρ↦ρ̄` (§10). The atoms are the infinite-rank forms of finiteness, conjugacy, irreducibility and closedness.

*Foundational principles.*

1. Purity statements are pointwise; a theory in law is blind to them `[L/D]`.
2. Both structures are used jointly, and the coefficient size sharply (§1.4 (e)).
3. Trace-integrality replaces lattice-integrality.
4. Elimination is free; well-foundedness and conjugacy are the inputs.

*Criteria.* It must reprove Weil's theorem for curves in a form that does not use finite rank at the decisive step. It must fail on: the golden datum, the integer-norm one-off, the approaching Euler product, the `cosh` models, the heat family, the symmetric shift, and Ihara and Selberg zeta functions with exceptional eigenvalues, which have an Euler product over closed geodesics, an FE and finitely many real off-line zeros `[C]`. It must explain why integer norms in a free abelian monoid differ from lengths in a non-abelian group.

*Research topics.* A Kronecker theorem for trace-integral infinite-rank modules with duality. A notion of irreducibility for `ξ` (no factor with an FE and a Dirichlet series; compare the relocation obstruction `[L]`). Conjugacy classes of zeros: which zeros are forced to share a depth. Weight filtrations on infinite-rank cohomology of the Meyer flow and of the orientation cover. Semicontinuity of weights along towers.

---

## 8. A new field without positivity and without spectral theory

**Unlikely intersections on the prime torus.**

*What it is about.* The Bohr hull of ζ is the infinite torus of unimodular multiplicative twists; the vertical line is the orbit `t↦(p^{it})_p`. Haar-almost every fibre is zero-free right of `½` with natural boundary `½` `[L]`. The set of fibres with a zero right of `½+δ` is therefore an exceptional locus of measure zero, and an off-line zero of ζ at height `γ` is a point of the orbit of the trivial fibre on that locus: an unlikely intersection. The field is the Diophantine geometry of such intersections, in the sense of Manin–Mumford, André–Oort and Zilber–Pink `[C]`.

*Dictionary.*

| Diophantine geometry | Prime torus |
|---|---|
| special subvarieties | torsion cosets and subtori; the Adams maps are the only exact symmetries of the orbit `[L]` |
| the orbit is special | function fields: the orbit is a closed one-parameter subgroup, zeros are periodic, AAL is free `[L]` |
| atypical intersections lie in special subvarieties | an off-line zero forces a structured event of the orbit: a heavy return or anti-return (reciprocity of returns) `[L]` |
| finiteness of atypical points | landing; B13 as the statement that isolated atypical points do not exist |
| recurrence of an atypical component | AAL as zero transport |
| counting rational points on transcendental sets | return counts; the depth floor in the number of logarithms |
| functional transcendence | hypertranscendence of ζ and differential independence of its dilates `[L]` |

*Tools it would develop.* Point counting on definable sets restricted to boxes of the strip; zero estimates for exponential polynomials in `π(y)` logarithms with constants polynomial in the number of logarithms (the survivor named in Π125); Ax–Schanuel statements for the orbit map; transcendence measures; the involution of the hull induced by the FE.

*Criteria.* No sign and no operator. It must reproduce periodicity over `𝔽_q`. It must respect the label obstruction: `ζ(s−h)` has the same orbit, so the exceptional locus must be defined with the coefficient size or with the FE `[L]`. It must respect return–form duality: bounded-height Diophantine information reaches the Kronecker scale only, and rounded orbits are function fields `[L]`.

*Questions.* In which topology is the exceptional locus closed? Is it contained in a countable union of proper analytic subsets, and which of them are invariant under an Adams map? Does a point of the orbit on the locus force a near-relation among `log p`, `p≤y`, of height polynomial in the depth?

*Main conjecture.* For every `δ>0` the orbit of the trivial fibre meets the locus of fibres with a zero right of `½+δ` in a set that is empty or recurrent with gaps controlled by the Kronecker scale.

*Relation to the previous proposal.* The arithmetic jet geometry of §2.11 of the summary addresses (S1) of §6; this field addresses the transport atoms and the dark range.

---

## 9. A research programme for `𝔽₁`

### 9.1 Aim

Not a definition of `𝔽₁`. The aim is a geometry in which Spec ℤ has a product with itself and one of the two proofs for curves runs: Weil's (a surface with a Hodge index) or Stepanov's (an endomorphism and an auxiliary). §1.4 (d) says why nothing less will do: ζ is rigid, so no family replaces the base.

### 9.2 What the corpus fixes

- **Points.** `N(n)=Λ(n)+1+1/(n²−1)`; `Γ_1·Γ_n=N(n)` `[L]`. The third term is `Σ_{k≥1}n^{−2k}`, the contribution of the trivial zeros `[D]`.
- **Two half-products.** The zonotope surface with `Γ_m·Γ_n=m+n` and an exact count; the torsion half-product on `ℙ¹_ℤ` `[L]`.
- **Fibres.** `ℍ³` with one geodesic and the Green function at `s=½`; Bruhat–Tits trees at the Ramanujan point; a discrete carrier `Γ\(ℍ³×Π'_p T_p)` with commuting prime operators `A_p` `[L]`.
- **Diagonal.** Not local: atoms give the discriminant; Gram coupling leaves a signed defect `[L]`.
- **Frobenius.** The Adams operations; exact only on the torsion; Witt vectors with Frobenius `[L]`. No `p`-derivation in the corpus.
- **Cohomology.** Infinite rank; the explicit formula is the Lefschetz trace of the Meyer flow `[L]`.
- **Counts.** `Q` is not integer-valued; a count must be a limit `[L]`.

### 9.3 Criteria

| # | Criterion | Test from the corpus |
|---|---|---|
| C1 | reproduces Weil and Stepanov for curves | count law of every hyperelliptic curve `[L]` |
| C2 | counts alone are not enough | the golden datum must fail `[L/K]` |
| C3 | uses the FE | the integer-norm one-off and the approaching Euler product must fail `[L]` |
| C4 | uses the Euler product | `cosh` models and the heat family must fail `[L]` |
| C5 | sees the tempered edge | the symmetric shift must fail `[L]` |
| C6 | distinguishes ℤ from geodesic flows | graph and surface zeta functions with exceptional eigenvalues must fail `[L]`, `[C]` |
| C7 | infinite rank, no stable lattice | lattice no-go `[L]` |
| C8 | the diagonal is Weil's, not the discriminant | locked dampings `[L]` |
| C9 | positivity, if used, is derived | λ-ring effectivity reduces to the Hodge index and does not prove it `[L]` |
| C10 | the archimedean place is a fibre | `ℍ³` at `Δ=½`; the pole as the spherical piece `[L]` |

### 9.4 Three constructions to pursue in parallel

**A. Frobenius lifts (the Stepanov side).** A Λ-structure is a commuting family of Frobenius lifts; the Adams operations on the group ring of `ℚ^×_{>0}` are one. Add the `p`-derivations `δ_p(a)=(ψ_p(a)−a^p)/p`. Deliverables: the Adams ring of the prime torus as a δ-ring; Stepanov–Bombieri rewritten with δ-multiplicity; the answer to (S1) of §6. Kill condition: δ-multiplicity at all primes of a window costs at least the Chebyshev count.

**B. Carries (transport of purity).** `ℤ_p` is `𝔽_p[[T]]` with addition deformed by the Witt carry polynomials; RH holds on the undeformed side. Locally, purity statements have been transported from characteristic `p` to mixed characteristic by tilting, and a product of two copies of `Spd ℚ_p` exists `[C]`. Deliverables: the carry cocycle as the deformation parameter in the corpus's cut calculus (`TheCarryOfTheFloor` `[L]`); a comparison of the smoothed prime count in a window with the exact count of irreducible polynomials, with the carry as the error; a statement of what a global tilt would have to be. Kill condition: the comparison error is of the size of the count for every window.

**C. The surface (the Weil side).** Continue from the adelic carrier: a global Green resolvent built from the `A_p` and the hyperbolic Laplacian, its Robin mass, and the identification of the two half-products as two projections of one object. Deliverables: the off-diagonal identity on the carrier; the diagonal as a global finite part; Riemann–Roch with the FE as duality. Kill condition: every global finite part differs from Weil's diagonal by a term of the size of the discriminant.

### 9.5 Questions the programme must answer

1. Which endomorphisms have `N(n)` fixed points, and on what?
2. What is the multiplicity of a function at a prime over `𝔽₁`?
3. Why is the diagonal not local?
4. What is ampleness, and why would Riemann–Roch imply the Hodge index without assuming it?
5. Where do the Gamma factor and the pole enter as geometry?
6. Why do monoids with integer norms that are not ℤ fail (count-distance rigidity gives the dividing line `o(log n)` `[L]`)?

### 9.6 Order of work

1. C1–C6 as a test suite on existing fakes.
2. Construction A up to the answer to (S1).
3. Construction C up to the off-diagonal identity.
4. Construction B as a comparison theorem on one window.

---

## 10. A research programme for a Galois theory of the zeros

### 10.1 The dictionary

For a curve of genus `g` over `𝔽_q` the Frobenius eigenvalues are the roots of a polynomial in `ℤ[T]`. Two involutions act on them: `ι: α↦q/α`, algebraic and commuting with the Galois group, and complex conjugation `c`. RH is `c=ι`. The Galois group lies in the hyperoctahedral group `(ℤ/2)^g⋊S_g`, the centralizer of `ι`; generically it is the whole group, and `c` is its central element `[C]`.

For ζ: `ι: ρ↦1−ρ`, `c: ρ↦ρ̄`.

> **RH ⇔ `c=ι` on the zero set ⇔ complex conjugation is central in the group of all permutations of the zeros commuting with `ι`** `[D]`.

(The centre of the hyperoctahedral group is `{1,ι}`, and `c≠1`.) The atoms translate: B13 is irreducibility (no finite exceptional set stable under the group), AAL is the statement that conjugate zeros share their depth, ZAL is well-foundedness. The fibre form: RH ⇔ `ιc`, which preserves the height, acts trivially ⇔ the height separates the zeros.

### 10.2 What an "algebraic equation" can mean

| Candidate | Roots and group | What the corpus has |
|---|---|---|
| Jensen polynomials of Ξ | roots of `J_d` over the field of Taylor coefficients; `c` has cycle type given by the non-real root count | `N_d` nondecreasing, `sup_d N_d` = off-line multiplicity, `N_d≤300√(d log d)`, inner roots real `[L]` |
| Local Weierstrass polynomials | `ξ=P_R·unit` on a rectangle `R`; coefficients are power sums `Σ_{ρ∈R}ρ^k`, contour integrals of `ξ′/ξ` | explicit contour and mass bounds `[L]` |
| Monodromy in a real family | zeros as functions of a parameter (heat time, cosine depth, Hurwitz shift); the group generated by the branch points | collision criterion; finitely many non-real zeros of `H_t`, `t>0`; only `τ=0` has a Dirichlet series `[L]` |
| The torus of the zero motive | character group = the additive group generated by the zeros; relations among ordinates | parity of ordinate relations and annihilator mass `[L]`; lattice no-go `[L]` |
| Differential Galois theory | relations among ζ and its derivatives | none exist: hypertranscendence, differential independence of algebraic dilates `[L]` |
| Adams∘FE dynamics | the maps `s↦ms` and `s↦1−s`; orbits of zeros | half-descent `s↦1−s/2` with accumulation at `2/3` `[L*]` |

### 10.3 Criteria

1. Over `𝔽_q` it reproduces the hyperoctahedral group and the centrality of `c`.
2. A large group does not imply purity: the golden datum has full monodromy and is impure `[L]`. The theory must locate `c`, not measure the group.
3. Integrality must enter as trace-integrality; Kronecker's theorem (`exists_pow_eq_one_of_isIntegral_of_conjugates_norm_one` `[L]`) and finite certificates of integral purity `[L]` are the finite-rank models, and the certificate length grows with `q` `[L]`.
4. It must be pointwise: generic zeros are indistinguishable, so any invariant definable over the ground field that holds at one zero of an orbit holds on the orbit. The first zeros are on the line `[L]`. The programme succeeds if "on the line" is such an invariant and the group is transitive.
5. It contains the separation proof of the Carlitz–Goss case `[C]` as a special case: an invariant of `ιc` that is injective on the zeros.

### 10.4 Questions

1. **Ground field.** Over which field `K⊂ℝ` generated by prime-side data are the power sums of the zeros in a rectangle defined, and is the Galois group of the local Weierstrass polynomial over `K` the full hyperoctahedral group?
2. **Location of `c`.** Is there a generating set of the group whose elements commute with `c` for a structural reason (monodromy along loops in a family defined over ℝ is conjugated by `c` to the monodromy of the conjugate loop)?
3. **Irreducibility.** Is `ξ` irreducible in the class of entire functions with an FE whose quotient keeps a Dirichlet series? The relocation obstruction (moving one quartet destroys the Dirichlet series on `Re s>1`) `[L]` is the first theorem of this type.
4. **Separation.** Which invariant of `ιc`, computable from the primes, is injective on the zeros? The height is; the census counts singleton fibres; a second invariant is needed for a proof.
5. **Stability under limits.** Do the Galois groups of `J_d` stabilize, and does the cycle type of `c` converge in a sense stronger than `N_d→` off-line multiplicity?

### 10.5 Tools to develop

Galois theory of local Weierstrass polynomials with coefficients given by contour integrals; a theory of conjugacy for zeros of Dirichlet series with an FE; monodromy of the zero set in real-analytic families and its interaction with `c`; trace-integral Kronecker theorems; Newton polygons and their archimedean substitutes (the Laguerre and Turán layers); the Adams∘FE correspondence on the strip.

### 10.6 Limit

In finite rank the centrality of `c` is a consequence of purity, not its proof. The programme has content only if question 2 or question 4 has an answer that does not pass through the sign.

---

## 11. Missed opportunities

### 11.1 Assembly: halving chains terminate

- `OneHeckeEigenformIsBlindToHalvingPairs` `[L*]`: for a Hecke form with `ρ(1)≠0`, the diagonal entry `Λ_u(s₀)≠0` ⇔ `ζ(s₀)≠0` and the Shimura integral of `u` is nonzero at `s₀/2+¼`. A single eigenform is blind at a resonance `ρ/2` when `ζ(ρ/2)=0`. B125 lists two conditions: no halving pairs, and nonvanishing of the Shimura integral.
- `exists_xi_zero_half_ne_zero` (`RHTower/XiAffineCollisionControl.lean`) `[L*]`: from every non-real zero of `ξ` with `½<Re ρ<1`, the half-descent `ρ↦1−ρ/2` reaches a non-real zero `ρ′` with `½<Re ρ′<1` and `ξ(ρ′/2)≠0`. The orbit accumulates at `2/3`, where zeros are isolated. `riemannZeta_ne_zero_of_halving` is the same cascade.

The two modules are not connected. Together `[D]`: if RH fails, some right zero `ρ′` is not in a halving pair. For one Hecke eigenform `u`, a rate `y^{¾−ε}` for the energy of `u` forces `Λ_u(ρ′/2)=0`, hence the Shimura integral of `u` vanishes at `ρ′/4+¼`. So:

> RH ⇔ the one-eigenform rate, provided the Shimura integral of `u` has no zero at the points `ρ′/4+¼`, `ρ′` an off-line zero of ζ.

The halving-pair condition of B125 is void. What remains is a nonvanishing statement for the symmetric-square function at points with real part in `(3/8,½)`. Statically: a halving pair needs a zero with real part `1−β/2`, so none exists unless `Θ≥2/3` `[D]`.

### 11.2 Kill: the family step through twists and covers

By §1.4 (d) and §5.2 the zeros of ζ are the fixed part of every family of twists or covers, and the two proved cases (exact orthogonal families, summable deformations) already price the fixed part at the trivial bound or leave it unmoved `[L]`. Until (FP) is refuted, B85, B86 and B142 have no producer; the tensor and family theorems are support. Work on a "family with jump equal to the pole alone" inside the class of Euler products with an FE is excluded by the isolation theorems `[D]`.

### 11.3 A calibration to add

Graph zeta functions with `t²>4q` are in the corpus as fakes of the horizon `[L]`. Their infinite-rank analogue is the Selberg zeta function of a compact surface with small eigenvalues: an Euler product, an FE, and finitely many real off-line zeros `[C]`. The firewall statement "only the FE excludes the layer, and only together with the Euler product" is a statement about commutative integer-norm systems; B13 is false in the non-commutative class. Any B13 argument must use the absence of real zeros in the strip, integer norms, or order one.

### 11.4 Published mathematics not in the corpus

- **Multiplicative functions in short intervals** `[C]`. For almost all `x`, `Σ_{x<n≤x+h}λ(n)=o(h)` as `h→∞` arbitrarily slowly, and the correlations `Σ_nλ(n)λ(n+h)` cancel on average over `h≤H`. In the corpus's language these are savings for long Liouville and Möbius mean values past the height, where Π116 and Π122 give the collision order and Π103 lists the saving as open. The mechanism is the factorization `n=pm` with `p` in a short range, the "smooth × prime" structure of Π103. The saving is a power of `log`, in law; it does not touch an atom or the width axis `[A]`.
- **The Carlitz–Goss Riemann hypothesis** `[C]`: the calibration of §6.
- **Bilinear methods for mollified moments past length `T^{1/2}`** `[C]`: the technique behind §4.3.

### 11.5 Routes without a mechanism

| Group | Reason | Recommendation `[A]` |
|---|---|---|
| Scheduled sums: FU, CFC, RP | one-sided history floors; exact criteria; no source estimate beyond fixed horizons | keep the criteria; no further work without a new estimate |
| Source completions: SEC, CDC, PCS; candidates APF, EWJ, RFHM, WBF | a source plus one condition at each actual zero; the condition is RH zero by zero | freeze |
| TH rank by rank | each rank is a finite rung from verified height; all ranks reduce to the adaptive head | stop at rank 14; work only on the head near critical zeros |
| The fourteen window routes | one form; positivity at aperture `a` gives a near-line zero-free statement to height `e^{a/K}` and follows from verification to `windowHeight(a)` `[L]`: the window sign is RH filtered by height | treat as one route with one open step (the stage step) |
| Family and tensor branch | §11.2 | support until (FP) is decided |
| Exceptional-current upper bounds | §2, last item | close unless an FE inequality is named |

### 11.6 Small assemblies

- **Quasi-RH on windows**: state the width version of the `log²` criterion as a theorem (`α<½` ⇒ strip) `[D from L*]`.
- **Two-sided local criterion**: `|c_B(log p)|≤K` on `log²` windows ⇔ RH follows from the one-sided theorem `[D]`; a proof with signed deletion (no positive averaging) is the item that matters for §6.
- **`qRH ∨ AAL`** as a named theorem, and the list of strip-conditional theorems that hold in the ¬AAL world (§2).
- **Census dichotomies**: `critical_proportion_or_simple_offLine` with the near-line refinement gives, for each target `θ`, the exact proportion of simple near-line off-line zeros that a failure requires `[L*]`; tabulate `θ=0.70, 0.75, 0.80`.

---

## 12. Answers in one line each

1. **Big picture.** One inequality per prime on sparse `log²` windows, and three atoms; solved: the reductions, the locality, the sign-free decision, the model classifications, rigidity; standing: a producer past VK, the atoms, the diagonal, and the fact that ζ is rigid.
2. **Opportunities.** The halving descent; the fixed-part theorem; higher Gram moments; short-interval multiplicative estimates; logarithmic windows; the global Green resolvent.
3. **Quasi-RH.** No clear path; it is the tail law `Θ∞<1` and has no rung below it.
4. **Seventy per cent.** No clear path; `67.25%` is proved, the trans-threshold route needs a signed prime-pair estimate not known under RH, and the fourth-moment route is open.
5. **One question.** Is the zero motive of ζ the fixed part of every arithmetic family?
6. **Without positivity.** Does ℤ carry a shadow of the Frobenius endomorphism or of ultrametric separation?
7. **New field.** Infinite-rank purity theory.
8. **New field without positivity.** Unlikely intersections on the prime torus.
9. **`𝔽₁`.** Three constructions (Frobenius lifts, carries, the surface) against ten tests.
10. **Galois theory.** RH ⇔ complex conjugation is central; locate `c` or find a separating invariant.
11. **Missed.** One assembly that voids half of B125; one kill; one calibration; three published inputs; six groups of routes to freeze.
