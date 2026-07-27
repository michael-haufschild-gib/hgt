# The corpus's hypertranscendence criteria stop strictly below order one, and `exp` proves they must

- **ID:** `hypertranscendence-frontier-order-one`
- **Stage:** 1-in-progress
- **Type:** FRONTIER LOCATION + OBSTRUCTION
- **Scientific status:** `[OBSTRUCTION PROVED BY COUNTEREXAMPLE]` `[NOT AN RH PROOF]`
- **Working assumption (user-set):** RH will not fall to classic routes; it needs a new insight about
  hypertranscendental functions in general, and HTGeometry has the beginnings of one.

## 1. What HTGeometry actually proves about hypertranscendence

Three magnitude-based criteria, all unconditional, all of the same shape: *prescribed decay of the
Taylor magnitudes `|a_n| = exp(-b_n)` forces hypertranscendence*.

| module | hypothesis on `b` | regime |
|---|---|---|
| `LogSuperlacunaryMagnitudeHypertranscendence` | `b_(n+1)/b_n → ∞` | order 0, sparse |
| `DATaylorLogRatioResonance` | `b_(n+1)/b_n → lam`, `lam > 1` finite | order 0, geometric |
| `StretchedExponentialMagnitudeHypertranscendence` | `b_n = B·n^α`, `0 < α < 1` | order 0 |

The mechanism is shared and is the genuinely interesting part: a DA relation is pushed through
**Mahler integer normalization** (`FormalMahlerIntegerNormalization`) to a relation with *integer*
coefficients, and then a pigeonhole on coefficient valuations freezes a multiplicity difference into
a nonzero integer polynomial `Q` with `Q(1) = Q(lam) = 0`. Hence
`logRatio_isAlgebraic_of_differentiallyAlgebraic`: **every finite successive log-magnitude ratio
`lam > 1` of a DA series is algebraic**, so a transcendental ratio forces hypertranscendence.

## 2. Where `Xi` sits, and why none of them reach it

`Xi` is entire of order 1. Its Taylor magnitudes satisfy `b_n ≈ n log n`, so

```text
b_(n+1)/b_n → 1 .
```

Every criterion above needs `lam > 1` or faster. **`lam = 1` is exactly the order-one wall, and `Xi`
is on it.** The `DATaylorLogRatioResonance` proof shows why the wall is real at the level of
technique: it needs a geometric sequence to beat the linear jet-degree scale
(`tendsto_const_pow_div_natCast_atTop`), and at `lam = 1` that step is unavailable.

## 3. The obstruction, and it is decisive: no magnitude criterion can reach order one

The natural target — *extend the magnitude criteria to `b_n ~ c · n log n`* — is **false**, and the
counterexample is the first function one should have tried:

> `exp` is entire of order 1 with `|a_n| = 1/n!`, hence `b_n = log n! ~ n log n` and
> `b_(n+1)/b_n → 1`. And `exp` is differentially algebraic: `y' - y = 0`.

So the magnitude profile `b_n ~ n log n` is compatible with differential algebraicity. The same holds
for `sin`, `cos`, and every solution of a linear ODE with polynomial coefficients — the entire
holonomic class lives at order one with exactly this magnitude profile.

> **No criterion depending only on `|a_n|` can force hypertranscendence at order one.** The
> order-zero results are not a first step toward order one; they work precisely because such decay is
> already incompatible with any algebraic differential equation, and that incompatibility disappears
> at `lam = 1`.

This is worth stating flatly because the obvious research move — push the stretched-exponential
result from `α < 1` to `α = 1` and beyond — is not merely hard, it is refuted.

## 4. Where the insight has to come from instead

The Mahler apparatus already contains a second, non-magnitude input that the current criteria use
only as plumbing: **integrality**. `FormalMahlerIntegerNormalization` converts an arbitrary DA
relation into one with integer coefficients; the magnitude pigeonhole is then what extracts a
contradiction. The magnitude half is what dies at order one. The integrality half does not.

So the direction this card proposes, and it is the only one left standing after §3:

> **Replace the magnitude pigeonhole with an arithmetic one.** A DA relation for `f` with integer
> coefficients is a Diophantine condition on the Taylor coefficients of `f`. For `Xi` those
> coefficients are the power sums over the zeros (Hadamard), and by the explicit formula they are
> also the prime–archimedean moments. A hypertranscendence criterion phrased as *"no integer
> relation can hold among these power sums"* would be sensitive to exactly what magnitudes cannot
> see, and it would be a statement about the zero set.

What distinguishes `Xi` from `exp` is not the size of its coefficients but their **arithmetic**:
`1/n!` satisfies a first-order integer recurrence, the power sums over the zeta zeros are not known
to satisfy any. Hölder's own proof that `zeta` is hypertranscendental uses the functional equation
and the pole, not magnitudes — consistent with this diagnosis.

## 5. Honest scope

- §1 and §2 are readings of existing modules. §3 is a counterexample anyone would find once the
  question is asked precisely; its value is that it closes the obvious next step before anyone
  spends on it.
- §4 is a research direction, not a result. I have not shown that an arithmetic pigeonhole exists,
  and the classical difficulty — that nothing is known about the arithmetic nature of the zeta power
  sums beyond the Li coefficients — applies in full force.
- Nothing here proves anything about RH.

## Gates

- [x] locate HTGeometry's hypertranscendence criteria and their regimes
- [x] locate `Xi` relative to them: `lam = 1`, outside all three
- [x] **obstruction proved**: `exp` refutes any magnitude-only criterion at order one
- [ ] an arithmetic/Diophantine replacement for the magnitude pigeonhole
- [ ] does such a criterion see the zero set?
- [ ] independent audit (Codex)

## Log

- 2026-07-27 (Claude): written under the user's instruction that the goal is a new general insight
  about hypertranscendental functions, and that HTGeometry has its beginnings. The beginnings are
  real and are §1; the obvious extension is refuted by `exp`; the surviving direction is §4.

## 6. The mature external theory, and the exact place where it stops

§4 proposed replacing the magnitude pigeonhole with an arithmetic one. Before building anything I
checked what exists, and the answer changes the picture.

**Hypertranscendence has a mature general theory, and it is difference-Galois theory.** Hardouin and
Singer's *parametrized difference Galois theory* attaches to a linear difference equation a linear
**differential** algebraic group whose triviality/size decides whether the solutions satisfy an
algebraic differential equation. Complete results exist for the three standard operators:

```text
shift        x ↦ x + h
q-difference x ↦ q x
Mahler       x ↦ x^p
```

with user-friendly hypertranscendence criteria at order one, and applications ranging from `Gamma`
(recovering Hölder from `Gamma(s+1) = s·Gamma(s)`) to generating series of automatic sequences
satisfying Mahler equations. Sources: *Hypertranscendence and linear difference equations*
(Adamczewski–Dreyfus–Hardouin), *Hypertranscendence of solutions of Mahler equations* (EMS),
arXiv:2212.00388, arXiv:1707.08702.

**Consequence for this corpus.** HTGeometry's Mahler apparatus — `FormalMahlerIntegerNormalization`,
`AnalyticMahlerDescent`, `FormalMahlerDescent` — sits inside that family, and the external theory is
strictly stronger: it decides hypertranscendence for whole classes rather than for prescribed
magnitude profiles. Any general insight sought here has to be measured against it.

**And here is where it stops, which is the useful part.** Every operator the theory handles is of
**infinite order** — `x ↦ x+h`, `x ↦ qx`, `x ↦ x^p` all generate infinite groups, and the
parametrized Galois group lives over that. `Xi`'s defining symmetry is

```text
s ↦ 1 - s ,
```

an **involution**: it generates `ℤ/2`. A finite group carries no interesting difference-Galois
theory — there is no infinite orbit to build a Picard–Vessiot extension over — so the entire
apparatus has nothing to say about a function whose only functional equation is a reflection.
`zeta` satisfies no linear shift, `q`-difference or Mahler equation with rational coefficients;
Hölder's theorem for `zeta` is proved through `Gamma` and the functional equation, not through a
difference equation for `zeta` itself.

### 6.1 The two blindnesses are the same fact

This corpus already recorded the same phenomenon in its own language.
`linear-kills-quadratic-survives` proves that the functional-equation involution **annihilates every
linear invariant** and that the surviving invariant is quadratic. In Galois terms that is the
statement that `ℤ/2` has only the characters `±1`, so the linear (character) theory is trivial and
all content sits in the quadratic (invariant-form) theory.

> **The external theory is blind to `Xi` because the functional equation generates a finite group;
> this corpus's invariant theory is blind to `Xi`'s linear invariants for the same reason. Those are
> not two obstructions — they are one, stated in two languages.**

That identification is, I believe, the most useful thing this card contains, and it sharpens the
target the user set:

> a new general insight about hypertranscendental functions must handle a **finite-order** symmetry,
> where every existing hypertranscendence technique — magnitude (dead at order one by §3), difference
> Galois (needs an infinite-order operator) — has nothing to say.

What `Xi` has beyond the involution is the Euler product, i.e. an *infinite* family of local
symmetries indexed by primes. If a difference-Galois-type theory can be built over that family
rather than over a single operator, it would be the missing framework. The corpus's prime-log
Herglotz/KMS apparatus (`PrimeLogKMSRealization`, `UniversalOrientedHerglotz`) is the closest thing
here to such a family, and it is unreferenced by RHTower.

## Gates (revised)

- [x] locate HTGeometry's hypertranscendence criteria and their regimes
- [x] **obstruction proved**: `exp` refutes any magnitude-only criterion at order one
- [x] external theory located: parametrized difference Galois (Hardouin–Singer) and its three operators
- [x] the exact stopping point identified: all three operators have infinite order; `s ↦ 1-s` has order 2
- [x] §6.1: the external blindness and this corpus's linear/quadratic law are the same fact
- [ ] a hypertranscendence theory over the prime-indexed family rather than a single operator
- [ ] independent audit (Codex)

## 7. The corpus already names the frontier, and my first attempt at crossing it is refuted

`HTGeometry/ExponentialSumDA.lean` proves `differentiallyAlgebraic_finset_expSum_general`: **every
finite `ℂ`-linear combination `∑_{i ∈ s} a_i exp(c_i x)` is differentially algebraic**, via the
constant-coefficient ODE `∏_i (D − c_i) y = 0`. Its docstring states the consequence exactly:

> *"every finite truncation of a Hurwitz-type Dirichlet series `∑_{n ∈ s}(n+a)^{−x}` is
> differentially algebraic: the escape from the differentially-algebraic class — the
> hypertranscendence of the full `ζ(a,·)` — **can happen only in the infinite limit, never at any
> finite stage.** This locates the frontier … precisely at the passage to the infinite sum."*

So the corpus had already located the frontier where §3–§6 independently arrive. The question is what
property of the infinite family causes the escape.

**My first candidate, and its refutation.** The finite theorem plus `ShiftStableLatticeStructure`
(two `ℚ`-independent translations ⟹ DA) and `PeriodRankUniversalLaw` (hypertranscendental ⟹ period
group of `ℚ`-rank ≤ 1) suggested a rank dichotomy:

> *(candidate)* `ℚ`-rank of the frequency group finite ⟹ DA; infinite ⟹ hypertranscendental.

`ζ` fits: the frequencies are `log n`, and `{log p}` is `ℚ`-independent, so the rank is infinite.

**It is false.** Take frequencies `λ_n = n`, which have `ℚ`-rank **1**. Then
`∑ a_n e^{−ns} = g(e^{−s})` with `g(w) = ∑ a_n w^n`, and for a generic coefficient sequence `g` is
not differentially algebraic — most power series are not. So rank `1` does not imply DA, and the
dichotomy collapses. What the corpus proves is a statement about **cardinality** (finite frequency
set), not about rank.

Recording the refutation rather than the candidate, because the candidate is the first thing anyone
reaching this frontier will try.

**What survives, and it is a genuine reduction.** For frequencies in a rank-one group the whole
question collapses to a single variable: `∑ a_n e^{−ns} = g(e^{−s})`, so differential algebraicity in
`s` is differential algebraicity of the generating function `g` in `w` — which is exactly the domain
of the Mahler/automatic-sequence theory (Adamczewski–Dreyfus–Hardouin) that §6 located. **The
rank-one case is solved externally.** `ζ` is not in it: `{log n}` has infinite rank, so there is no
single `w`, and `ζ` is instead the restriction of the infinite-variable product
`∏_p (1 − w_p)^{−1}` to the one-parameter curve `s ↦ (p^{−s})_p`, a dense winding line in an
infinite-dimensional torus.

> **That is the structural statement of where `ζ` sits: a rational function of infinitely many
> independent variables, restricted to a dense winding line of infinite rank.** Every existing
> hypertranscendence technique handles either finitely many variables (corpus finite-sum theorem,
> `ShiftStableLatticeStructure`) or one variable with an infinite-order operator (difference Galois).
> Neither covers a winding line of infinite rank, and that — not the order-one magnitude wall of §3,
> and not the involution of §6 — is the sharpest description I can give of the missing framework.

## Gates (revised)

- [x] `exp` refutes any magnitude-only criterion at order one
- [x] external theory located and its stopping point identified (`ℤ/2` vs infinite-order operators)
- [x] corpus already names the frontier: escape only in the infinite limit
- [x] **rank dichotomy proposed and refuted by rank-one generic power series**
- [x] rank-one case reduced to the externally solved generating-function/Mahler case
- [ ] hypertranscendence over a dense winding line of infinite rank — the missing framework
- [ ] independent audit (Codex)

## 8. Found it: the corpus's own frequency criterion, and its one open topological step

My §7 refutation was aimed at a version of the rank dichotomy I had stated badly. The corpus has the
correct version, and it is the general insight this card has been circling.

**`HTGeometry/PrimeFrequencyInfiniteRank.lean`:**

> *"The finite-phase theorem forces a **finite** rational Bohr-frequency rank on any recurrent object
> that is differentially algebraic **over the Gamma field**. Its contrapositive is the frequency
> criterion: an object whose frequency module has **infinite rational rank is differentially
> transcendental over the Gamma field**. For the Riemann zeta function the frequency module contains
> `{log p : p prime}`, whose full `ℚ`-span has rank equal to the (infinite) cardinality of the
> primes … with the finite-phase conclusion supplied as the explicit interface it is: **the theorem
> whose unconditional proof needs the Bohr-hull / Pontryagin / covering-dimension infrastructure
> still under construction.**"*

and **`HTGeometry/FrequencyRank.lean`** supplies the algebraic half — the `ℚ`-span of finitely many
real frequencies has finite `ℚ`-dimension — recording that

> *"the still-open topological step feeding it is **the finite jet-sample embedding of the hull into
> `ℂ^N`** (the covering-dimension / Pontryagin route), which supplies the finite generating set."*

with `ZetaVerticalAlmostPeriodic.lean` doing the instantiation (`t ↦ ζ(σ+it)` is Bohr almost periodic
for `σ > 1`, frequencies `−log n`).

**Why my §7 counterexample does not apply.** I refuted *"finite `ℚ`-rank of the frequency group ⟹
DA"* with a generic power series at rank one. The corpus's statement is the other implication, with
two hypotheses I dropped: the object must be **recurrent** (almost periodic, so that a Bohr hull
exists at all), and differential algebraicity is **over the Gamma field**, not over `ℂ(x)`. A generic
power series is neither. So §7 refutes a strawman of my own making; the corpus's criterion stands.
Recording that, because a reader of §7 alone would conclude the rank route is dead when it is not.

**The open core, stated exactly.** Everything downstream is in place: the algebraic rank bound, the
zeta instantiation, the infinite-rank computation for `{log p}`. What is missing is one topological
theorem:

> **Finite jet-sample embedding.** For a recurrent object differentially algebraic over the Gamma
> field, the Bohr hull embeds into `ℂ^N` by finitely many jet samples — supplying a finite set of
> frequency generators, hence finite `ℚ`-rank, hence the contrapositive frequency criterion.

That is a statement in topological dynamics and Pontryagin duality — covering dimension of the hull
against the jet-sample map — and it is the *only* thing between the corpus and an unconditional
hypertranscendence criterion applicable to `ζ` by its prime frequencies.

**Assessment against everything else in this card.** The magnitude route is dead at order one (§3,
`exp`). Difference Galois cannot see an involution (§6). This route is alive, it is general — it
applies to any recurrent object, not to `ζ` specifically — and its remaining step is named,
topological, and finite in scope. It is the only live general-insight target I have found, and it is
the corpus's own.

## Gates (revised)

- [x] §3 magnitude route dead at order one
- [x] §6 difference-Galois stopping point identified
- [x] §7 rank dichotomy refuted **as I stated it** — see §8 for the correct statement
- [x] §8 corpus's frequency criterion located, with its one open step named
- [ ] **finite jet-sample embedding of the Bohr hull into `ℂ^N`** — the open core
- [ ] independent audit (Codex)

## 9. Working the open core: the chain is two mathlib-absent inputs, and one base case is now done

Reading down from §8's named open step, the corpus has already reduced it much further than the
summary suggests.

**`HullJetEmbedding.lean`** — given a continuous injective jet-sample map `J : K → ℂ^N` from the
compact hull, `K` is a closed topological embedding into `ℂ^N`
(`hull_jetSample_isClosedEmbedding`). Injectivity is the analytic ODE-uniqueness step; the
topological conclusion is proved.

**`HullDimensionBound.lean`** — combining that with subspace monotonicity of small inductive
dimension gives `ind K ≤ ind ℂ^N` (`hull_smallIndDimLE_of_ambient`), and states the residue exactly:

> *"This reduces the finite Bohr-rank conclusion eq. (9) to a single dimension input — **`ind ℂ^N ≤ 2N`**
> (the remaining product-subadditivity theorem) — together with the **Pontryagin `dim = character-rank`**
> identity."*

**`SmallInductiveDimension.lean`** — mathlib has no topological dimension theory at all, so the
corpus defines `SmallIndDimLE` by the Menger–Urysohn recursion and proves the foundations:
monotonicity, the empty and discrete cases, behaviour under inducing maps, embeddings and subsets.
Its own list of remaining targets is **`ind ℝ^N ≤ N`**, subspace monotonicity, and the Pontryagin
bridge — and subspace monotonicity is in fact already there (`SmallIndDimLE.subtype`, `.subset`,
`.of_isInducing`, `.of_isEmbedding`).

So the whole hypertranscendence programme rests on exactly two absent inputs:

```text
(A)  ind ℝ^N ≤ N          -- dimension theory, absent from mathlib
(B)  Pontryagin: dim = character rank for compact connected abelian groups
```

**Base case of (A), now proved.** `HTGeometry/RealLineSmallInductiveDimension.lean`, axiom-clean:

```text
frontier_real_ball      frontier (Metric.ball x ε) = {x - ε, x + ε}
smallIndDimLE_real_one  SmallIndDimLE ℝ 1
```

Balls are a neighbourhood basis of `ℝ`, each frontier is a two-point set, a finite subset of a `T1`
space is discrete, and `smallIndDimLE_zero_of_discrete` closes it. This is the base case the module's
own docstring calls for ("bottoming out at discrete point sets").

**What the induction still needs, stated honestly.** The step `ind ℝ^(N+1) ≤ N+1` is *not* a
routine continuation. The frontier of a box in `ℝ^(N+1)` is a union of `2(N+1)` faces, each of
dimension `≤ N`, so the step needs the **sum theorem for finite closed unions** — a genuinely hard
piece of classical dimension theory, usually routed through the large inductive dimension `Ind` or
covering dimension and the coincidence theorem for separable metric spaces. Nothing in this card
suggests that is close; what is now true is that the base case is discharged and the remaining
obligation is a single named classical theorem rather than an open-ended construction.

## Gates (revised)

- [x] §8 corpus frequency criterion located with its open step
- [x] §9 chain traced to exactly two mathlib-absent inputs (A) and (B)
- [x] **(A) base case proved**: `SmallIndDimLE ℝ 1`, axiom-clean
- [ ] (A) inductive step: sum theorem for finite closed unions, then `ind ℝ^N ≤ N`
- [ ] (B) Pontryagin `dim = character rank`
- [ ] injectivity of the jet-sample map (analytic ODE-uniqueness step)

## 10. Correction to §9: the induction does **not** need the sum theorem

§9 said the step `ind ℝ^(N+1) ≤ N+1` needs the sum theorem for finite closed unions, because the
frontier of a *box* is a union of `2(N+1)` faces. That is true for boxes and it is the wrong
neighbourhood basis. Using **balls** instead of boxes removes the obstruction entirely:

```text
frontier (ball x r)  =  sphere x r          (mathlib: frontier_ball, r ≠ 0)
```

and a sphere is not a union of anything — it is a single space. The induction then runs on spheres:

```text
ind S^0 ≤ 0            two points, discrete
ind S^n ≤ n            a point of S^n has spherical-cap neighbourhoods
                       {y ∈ S^n : d(y,x) < ε}, whose frontier in S^n is
                       {y ∈ S^n : d(y,x) = ε} ≅ S^(n-1)
ind ℝ^(n+1) ≤ n+1      balls have frontier S^n
```

No union of closed sets appears at any stage, so **the sum theorem — the piece §9 called the hard
classical obstruction — is not needed for `ind ℝ^N ≤ N`.** Withdrawing that assessment.

What the sphere route needs instead is one geometric homeomorphism, repeated:

> the `ε`-distance level set of a point in `S^n` is homeomorphic to `S^(n-1)`,

together with `frontier_ball` (mathlib) and the subspace-frontier computation for a cap. That is
concrete differential-geometry-free work: the level set `{y ∈ S^n : ⟨y,x⟩ = c}` for `|c| < 1` is the
intersection of `S^n` with an affine hyperplane, hence a Euclidean sphere of one lower dimension
scaled by `√(1-c²)`, and `SmallIndDimLE` is a homeomorphism invariant (`smallIndDimLE_congr`, already
in the corpus).

**Status of input (A).** Base case `SmallIndDimLE ℝ 1` is proved (§9). The general case is now a
finite, named, sum-theorem-free construction: build the cap/level-set homeomorphism and induct. That
is a materially better position than §9 described, and the correction matters because "needs the sum
theorem" would reasonably have discouraged anyone from starting.

## Gates (revised)

- [x] chain traced to inputs (A) `ind ℝ^N ≤ N` and (B) Pontryagin `dim = character rank`
- [x] (A) base case proved: `SmallIndDimLE ℝ 1`, axiom-clean
- [x] **§9's "needs the sum theorem" withdrawn** — the ball/sphere/cap induction avoids unions entirely
- [ ] cap level-set homeomorphism `{y ∈ S^n : d(y,x) = ε} ≅ S^(n-1)`
- [ ] `ind S^n ≤ n` and hence `ind ℝ^N ≤ N`
- [ ] (B) Pontryagin `dim = character rank`
- [ ] jet-sample injectivity (analytic ODE-uniqueness step)

## 11. Cost of the route, measured rather than guessed

I checked the two things I had flagged as unknown, instead of leaving them open.

**(B) Pontryagin `dim = character rank`.** mathlib's `Topology/Algebra/PontryaginDual.lean` contains
the **definition** of the dual group `A →ₜ* Circle`, its `CommGroup` and local-compactness instances,
functoriality (`map`, `map_comp`), and "a discrete monoid has compact dual". That is all.
`Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean` covers only finite abelian groups. **There is
no duality theorem, no structure theory of compact abelian groups, and nothing connecting dimension
to character rank.** Input (B) is therefore not a missing lemma but a missing *theory*: it needs the
structure theory of compact connected abelian groups built in Lean essentially from scratch. That is
a far larger obligation than (A), and it is pure classical infrastructure with no novelty in it.

**(3) Jet-sample injectivity.** `grep` for `jetSample` across the entire tree returns hits only
inside `HullJetEmbedding.lean` and `HullDimensionBound.lean`. The injectivity of
`J : K → ℂ^(m(n+1))`, `(b,g) ↦ (g^(k)(t_j))`, is a bare hypothesis of
`hull_jetSample_isClosedEmbedding` and is **not stated or proved anywhere else in the corpus**. It is
the analytic heart of the finite-phase theorem — ODE-uniqueness forcing a hull element to be
determined by finitely many jets — and nobody has written it down.

### 11.1 Honest cost, and what is actually novel in the route

```text
(A) ind ℝ^N ≤ N                base case proved; sphere-slice induction remains   — medium
(B) Pontryagin dim = rank      mathlib has the definition only                    — large, pure classical
(3) jet-sample injectivity     unstated anywhere                                  — the analytic core
```

Of these only (3) is mathematics that does not already exist in textbooks. (A) and (B) are classical
dimension theory and classical duality; formalizing them is real work and real debt, but it is not
new knowledge, and under the anti-theatre criterion it is infrastructure rather than research.

**The novel content of the whole route is the finite-phase theorem itself** — *a recurrent object
differentially algebraic over the Gamma field has finite `ℚ`-rank Bohr frequency module* — of which
(3) is the analytic half and (A)+(B) are the topological plumbing.

### 11.2 Being hypercritical of the theorem, not just its proof

The corpus states the finite-phase conclusion as an explicit unproved interface, so its truth is open,
and it deserves an attempt at a counterexample rather than assumption.

Evidence for: finite exponential sums realise arbitrarily large **finite** frequency rank and are all
DA (`ExponentialSumDA`), which is exactly what the theorem predicts. Jacobi theta is DA with
frequency set `{n²}` of `ℚ`-rank 1 — consistent. I could not construct an almost-periodic function
that is DA and has infinite-rank frequency module; quasi-periodic solutions of algebraic ODEs carry
finitely many basic frequencies, which is the classical intuition behind the theorem.

Evidence against, and it is a real caveat: the statement is DA **over the Gamma field**, a
non-standard differential base. Its strength depends entirely on how large that field is, and a
generous base makes "differentially algebraic over it" a weak hypothesis and the theorem
correspondingly strong. I have not audited the corpus's definition of that field against the claim,
and until that is done the finite-phase theorem should be read as a conjecture with a specific
proposed proof route, not as a theorem awaiting only plumbing.

## Gates (revised)

- [x] (A) base case proved; sum-theorem-free induction identified
- [x] (B) measured: mathlib has the Pontryagin *definition* only — a missing theory, not a lemma
- [x] (3) measured: jet-sample injectivity is stated nowhere in the corpus
- [x] the route's only non-classical content isolated: the finite-phase theorem, analytic half (3)
- [ ] audit the Gamma-field definition against the finite-phase claim
- [ ] `ind S^n ≤ n` via the cap level-set containment

## 12. The audit: the Gamma field is never defined, and the finite-phase theorem is unstated

§11.2 said the finite-phase theorem should be treated as a conjecture until its differential base is
audited. I ran the audit. The result is worse than "conjecture", and it changes what should be built
first.

**`grep "def .*GammaField"` over the whole tree returns nothing.** The Gamma field is named in
docstrings and never defined. And the criterion itself, in full:

```lean
theorem prime_frequency_forces_transcendence {DAoverGammaField : Prop}
    (finitePhase : DAoverGammaField → Module.Finite ℚ primeLogFullSpan) :
    ¬ DAoverGammaField :=
  fun h => primeLogFullSpan_not_finite (finitePhase h)
```

`DAoverGammaField` is a **universally quantified `Prop` variable with no definition**, and the proof
is one line of modus tollens. The theorem says: *for any proposition `P` whatever, if `P` implies that
`span_ℚ{log p}` is finitely generated, then `¬P`.*

**What is actually proved, and it is real:** `primeLogFullSpan_not_finite`, resting on
`ArchimedeanCorank.primeLogFullSpan_rank : Module.rank ℚ primeLogFullSpan = #Nat.Primes`. The
`ℚ`-independence of prime logarithms — essentially unique factorization — is genuinely formalized and
genuinely infinite-rank. That is the content.

**What is not there:** any statement of the finite-phase theorem. Its hypothesis is opaque, so the
implication cannot be proved, disproved, or even assessed for plausibility. My §11.2 weighing of
evidence for and against was evaluating a statement I had not checked exists.

### 12.1 This reverses §11's priorities

I costed (A) `ind ℝ^N ≤ N` and (B) Pontryagin `dim = character rank` as the route's obligations and
proved (A)'s base case. Both are plumbing for a conclusion — finite Bohr rank — that is currently
consumed only by an opaque `Prop`. **Building dimension theory and compact-abelian duality before the
statement exists is building a bridge to a place that has not been specified.**

The first task is therefore neither (A) nor (B) nor (3), but:

> **Define the differential base field, define differential algebraicity over it, and state the
> finite-phase theorem with a real hypothesis.** Only then do the topological inputs have a target,
> and only then can the theorem be attacked or refuted.

The corpus already has the pieces to do this honestly: `DifferentialOrder.lean` has
`DifferentiallyAlgebraic` and `Hypertranscendental` over the standard base, and
`AlmostPeriodicHull`/`BohrGenerators`/`ZetaVerticalAlmostPeriodic` have the recurrence side. What is
missing is the *relative* notion — DA over a specified differential field containing `Γ` — and the
statement that ties it to Bohr rank.

### 12.2 Honest note on my own trajectory

Between §8 and §11 I described this route as "the only live general-insight target", proved a base
case for it, and costed its remaining inputs. That was three messages spent on the plumbing of a
theorem I had not verified was stated. The base case (`SmallIndDimLE ℝ 1`) is correct and harmless,
and the cost measurements in §11 are accurate and still useful. But the ordering was wrong, and the
check that caught it — read the theorem, not the docstring — is the same check that caught the
`hdetects` reduction this morning. Twice in one session is a pattern, and the pattern is that
**docstrings describe the intended theorem and the Lean states the actual one.**

## Gates (revised)

- [x] audit run: `DAoverGammaField` is an undefined `Prop`; the Gamma field has no definition
- [x] the proved content isolated: `primeLogFullSpan_not_finite`, from `rank = #primes`
- [x] §11's priorities reversed — statement before plumbing
- [ ] define the differential base and DA over it; state the finite-phase theorem
- [ ] only then: (A) `ind ℝ^N ≤ N`, (B) Pontryagin, (3) jet-sample injectivity

## 13. The missing notion, supplied: differential algebraicity relative to a base

§12 found that "differentially algebraic over the Gamma field" cannot be written down in the corpus
because no relative notion of differential algebraicity exists — `DifferentialOrder` defines
`DifferentiallyAlgebraic` by a relation with **constant** coefficients, i.e. over `ℂ[z]`, and nothing
else. That is why the frequency criterion's hypothesis is an opaque `Prop`.

`HTGeometry/RelativeDifferentialAlgebraicity.lean`, axiom-clean, registered, supplies it:

```text
DifferentiallyAlgebraicOverOfOrder g f n :
    ∃ P ≠ 0 : MvPolynomial (ι ⊕ Fin (n+1)) ℂ,
      ∀ z, eval (Sum.elim (fun i => g i z) (fun j => f^(j) z)) P = 0
DifferentiallyAlgebraicOver g f  :  ∃ n, …
HypertranscendentalOver g f      :  ¬ DifferentiallyAlgebraicOver g f
```

A base is a family `g : ι → ℂ → ℂ`; `f` is differentially algebraic over it when a nonzero polynomial
in the base values and the jets of `f` vanishes identically. Taking `g` to be `{z}` recovers the
existing absolute notion; taking it to be `{z, Γ, Γ', …}` is what "over the Gamma field" means.

Two laws, which are the ones the programme needs:

```text
DifferentiallyAlgebraicOverOfOrder.mono   enlarging the base preserves DA
HypertranscendentalOver.mono              hypertranscendence over a LARGER base is STRONGER
```

both proved by renaming along an injective base embedding. The second is the reason the relative
notion is worth having: *hypertranscendental over a base containing `Γ`* implies *hypertranscendental
over `ℂ[z]`* — the classical Hölder conclusion — and is strictly stronger. Stating the frequency
criterion with `HypertranscendentalOver` in place of an opaque `Prop` therefore makes it a claim about
something, and a claim strictly stronger than Hölder.

**What this does and does not do.** It removes the objection of §12 — the hypothesis now has a
definition, and the criterion can be *stated*. It does not prove the finite-phase implication, which
remains the open mathematics, and it does not by itself connect the relative notion to the Bohr
frequency module. Those are the next two steps, in that order, and the second cannot sensibly be
attempted before the first.

## Gates (revised)

- [x] §12 audit: the Gamma field is undefined and the criterion's hypothesis is opaque
- [x] §13 relative differential algebraicity defined, with base-monotonicity — Lean, axiom-clean
- [ ] state the finite-phase theorem with `HypertranscendentalOver` and a real Bohr-rank conclusion
- [ ] prove or refute it
- [ ] only then the topological inputs (A), (B) and the analytic input (3)

## 14. Duplicate withdrawn

`HTGeometry/RealLineSmallInductiveDimension.lean` is **deleted** and unregistered. Codex was right:
`SmallInductiveDimension.lean:333` already proves `smallIndDimLE_real_le_one : SmallIndDimLE ℝ 1`
by the same mechanism (`Ioo` frontier is two points, discrete, zero-dimensional). §9's "base case now
proved" is withdrawn — the base case was proved before I arrived. Nothing else in the tree referenced
the deleted module.

The lesson is the corpus-search mandate, applied to a *statement* rather than a name: I searched for
`ind ℝ^N` and for the sphere induction, not for `SmallIndDimLE ℝ`, and the existing theorem was three
hundred lines below the definitions I had read.

## 15. The route is dead externally: the finite-phase theorem is Ostrowski 1920

§13 gave the finite-phase hypothesis a definition so that the theorem could be stated. Before
attacking it, the literature audit that §12–§14 kept deferring. It is decisive.

**Ostrowski (1920), *Über Dirichletsche Reihen und algebraische Differentialgleichungen*.** If a
Dirichlet series `φ(s) = ∑ a_j e^{−λ_j s}` satisfies — formally or analytically — an algebraic
differential equation, then there is an index `i` such that for every `j > i`,

```text
λ_j ∈ ℤλ_0 + ℤλ_1 + … + ℤλ_{i−1} .
```

That is the finite-phase theorem, and it is **stronger** than the corpus's target: it gives finite
generation over `ℤ`, not merely finite `ℚ`-rank, and it needs neither Bohr hulls, nor covering
dimension, nor Pontryagin duality. Ostrowski proves it by a Newton-polygon/dominant-term argument on
the asymptotic expansion in a half-plane. An English translation is arXiv:2211.02088.

Ostrowski's companion theorem, same paper: if such a `φ` is transcendental, finitely many
coefficients `a_0,…,a_k` determine all the rest as rational functions over `ℚ`.

**Consequences for this card, all negative.**

1. **(A) `ind ℝ^N ≤ N`, (B) Pontryagin `dim = character rank`, (3) jet-sample injectivity** are the
   three inputs §11 costed. All three are inputs to a *proof route* for a theorem that has had a
   proof since 1920, by a method that uses none of them. Building them buys no new theorem.
2. The intended **application** is equally known. Hilbert's 18th problem asked whether ζ satisfies an
   algebraic differential equation; it was settled — negatively, in great generality — by
   **Mordukhai-Boltovskoi and Ostrowski, independently, 1920**. Hölder had done Γ in 1886.
3. The **relative** form the corpus actually wants, ζ hypertranscendental *over the Gamma field*, is
   the algebraic differential independence of ζ and Γ. That is a live modern literature with several
   published proofs (J. Number Theory 2020; Acta Math. Sci. 2020 and 2021; J. Math. Anal. Appl. 2018;
   J. Differential Equations 2024), by Nevanlinna-theoretic methods — not by frequency modules.

So the frequency criterion's endpoint is a published theorem, reachable by at least two established
methods, neither of which is the one being built here.

**And Codex's freeze is independently correct, for a reason that survives even if all of the above
were unknown.** Hypertranscendence is a property of the *differential-algebraic type* of a function,
and the differentially algebraic meromorphic functions form a differential **field**. Hence for any
`E` in that field, `F` is hypertranscendental iff `F·E` is. Multiplication by a differentially
algebraic factor moves zeros freely — `Ξ(s)·cos(λ(s−1/2))` is hypertranscendental, entire of order
one, real on the critical line, satisfies `G(s) = G(1−s)`, and has infinitely many zeros off the
critical line at `1/2 ± π(k+½)/λ`. **No criterion of the form "hypertranscendental + functional
equation + order one ⟹ RH" can be true.** Hypertranscendence is zero-blind by construction; this is
elementary and is offered as a route-elimination for this programme, not as a research result.

**Verdict: `REDISCOVERED`, and RH-orthogonal.** The card is closed to further Lean investment. What
should be kept from it:

- `primeLogFullSpan_not_finite` and `primeLogFullSpan_rank` — the `ℚ`-independence of prime
  logarithms, genuinely formalized, reusable, and true regardless of what consumes it;
- `RelativeDifferentialAlgebraicity.lean` (§13) — the relative DA notion is correct infrastructure
  and is the right way to *state* Ostrowski's theorem should anyone want it formally;
- `SmallInductiveDimension.lean` — dimension theory absent from mathlib, of independent value;
- `prime_frequency_forces_transcendence` should be **re-docstringed**: its docstring presents the
  finite-phase implication as an open conjecture of the programme. It is Ostrowski's theorem.

## 16. What the kill teaches, and the surviving question

Both of this session's dead ends failed the *same* way, and the pattern is worth naming.

| route | what it delivers | why it cannot deliver RH |
|---|---|---|
| Deninger weight-one polarization | eigenvalues have `Re = 1/2` | the axioms are *equivalent* to the conclusion; constructing the package **is** RH |
| frequency / finite-phase criterion | ζ hypertranscendental over Γ | the invariant is zero-blind: `F` and `F·E` have the same DA type |

The first encodes RH as a hypothesis. The second computes an invariant that cannot see RH. **A
usable route must produce an invariant that is (i) computable from unconditional data and (ii) not
invariant under motions of the zero divisor.** Neither dead end satisfies (ii); the Deninger package
satisfies (ii) but fails (i).

That is the criterion to apply *before* costing a route, and neither Codex nor I applied it to either
route until after the plumbing was measured.
