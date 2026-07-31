# Stripped of scaffolding, the Deninger lane needs exactly one thing — and no audit instrument sees it

- **ID:** `deninger-lane-reduces-to-one-hypothesis`
- **Stage:** 1-in-progress
- **Type:** AUDIT + SYNTHESIS (reading the corpus's own Lean, not its cards)
- **Scientific status:** `[SYNTHESIS OF CORPUS STATE]` `[NOT AN RH PROOF]`
  `[NOT NEW MATHEMATICS — a statement about where this corpus stands]`

## 1. What the Lean actually says

`RHTower/DeningerArithmeticPositiveCalderonKoszul.lean` (598 lines) carries the labels the
Calderón–Green gate calls its global content: `DAC_POSITIVE_GRAPH_CONORMAL_TRANSVERSALITY`,
`DAC_GLOBAL_GREEN_ENERGY_STRICT_POSITIVITY`, `DAC_GLOBAL_CALDERON_CHIRALITY_KERNEL_REDUCTION`,
`DAC_GLOBAL_GREEN_ENERGY_RADICAL_PASSAGE`, `DAC_RESTRICTED_SUM_GREEN_ENERGY_DETECTION`,
`DAC_LOCAL_GREEN_ENERGY_SUMMABLE_MAJORANT`.

Read line by line, the mathematics in that file is:

| theorem | actual content | where the hard clause lives |
|---|---|---|
| `deningerPositiveCalderonGraph_inf_conormal_eq_bot` | graph of a strictly positive operator meets `L × Lᗮ` only at `0` — ten lines of inner-product algebra, correct and unconditional in its hypotheses | `hpositive : ∀ x ≠ 0, 0 < ⟪A x, x⟫` |
| `deningerStrictPositive_of_greenEnergy_detects_zero` | `lt_of_le_of_ne`, three lines | `hdetects : ∀ x, energy x = 0 → x = 0` |
| `deningerTsumEnergy_eq_zero_iff_mem_boundaries` | a `tsum` of nonnegatives vanishes iff every term does | `hlocal_zero_is_boundary : (∀ i, localEnergy i x = 0) → x ∈ boundaries` |
| `deningerGlobalChirality_kernel_eq_bot` | one substitution | `hpositive`, `hkernel_boundary`, `hrelative_unique` |

These are **correct, honest skeletons**, and writing them this way is the project's own prescribed
discipline ("represent missing analytic inputs as explicit hypotheses"). Nothing here is a defect.

But chasing the hypotheses through the file gives a single reduction. `hpositive` is produced from
`hdetects` (`deningerStrictPositive_of_greenEnergy_detects_zero`). `hlocal_zero_is_boundary` is the
local form of the same statement. `hrelative_unique` is the relative form. So:

> **Everything global in the corpus's Deninger Calderón–Green chain is proved from one clause:**
> ```text
> hdetects :  ∀ x,  energy x = 0  →  x = 0.
> ```
> **A nonnegative energy on the arithmetic source whose radical is exactly the boundary submodule.**
> Nothing else in the global layer is open. The parent card's "Global Green-energy radical
> classification: open" is that clause, and it is the whole of it.

This is the corpus's own §5 of `linear-kills-quadratic-survives` seen from inside the formalization:
the surviving quadratic mechanism is **polarization**, and what polarization needs here is exactly a
positive-definite energy. The lane dies **unbuilt**, precisely as that card's §5b predicts, and the
unbuilt object is one line of Lean.

## 2. Blind spot (c) of the discharge audit: anonymous hypotheses

`prop-interface-discharge-audit.md` is thorough and its 2026-07-27 re-measurement reports
**"No undischarged `Prop` interface remains in the three areas"**, after also closing a second
instrument for bundled `structure` data (28 unconstructed data inputs found and largely discharged).

Both instruments are keyed to **named** objects: project `Prop` definitions, and project `structure`s
in `Type`. Neither can see a hypothesis written inline:

```lean
(hdetects : ∀ x : E, energy x = 0 → x = 0)
```

That is not a project `Prop` constant and not a `structure`; it is an anonymous `∀`-statement in a
theorem signature. It carries the entire mathematical content of the Deninger global layer, and it is
invisible to both passes.

**So "no undischarged interface remains" is true as measured and false as a description of the
corpus's debt.** The debt has simply been written in a form the instrument does not name. The
Deninger cards themselves are honest about this — they list the item as open — but a reader who
trusts the instrument's summary over the cards will conclude the opposite.

Recording this as a methodological finding, not as a criticism of the instrument: the two named-object
passes are correct and were worth building. What is missing is a third notion of debt —
**content-bearing anonymous hypotheses that no corpus theorem concludes** — and it is the notion that
matters most for the two lanes that are supposed to reach RH.

A tractable form of the measurement, for whoever builds it: for each theorem carrying a research
label, extract its hypotheses, and ask whether any other declaration's conclusion unifies with each.
The heuristic shortcut (proof length, keyword) must be avoided — see the method note in
`linear-kills-quadratic-survives` §5b about what happened when a 176-card classification was
attempted by keyword.

## 3. What this makes the next question

Not "construct the energy" — that is the whole programme. The sharper question, and the one that can
be settled either way:

> **Is `hdetects` obstructed?** The parent card's own falsifier list contains
> *"Orthogonal Hilbert completion before incidence makes the scalar quotient seminorm zero"*, and the
> roadmap card states *"unweighted infinite-ray Hilbert augmentation has zero quotient seminorm"*.
> If the natural candidate energy is the Hilbert seminorm of the Meyer quotient and that seminorm
> vanishes identically, then `energy ≡ 0` and `hdetects` fails as badly as possible.

Two outcomes, both worth having:

- **a no-go** — no energy with the required equivariance and locality can detect zero. That would be
  the **first proved death of a quadratic route** in this corpus. Every quadratic route so far has
  died unbuilt, i.e. of nobody managing; a proof that it *cannot* be built is different in kind and
  would settle the lane.
- **a construction constraint** — the obstruction is only for the *unweighted* completion, and the
  weight/suspension prescription evades it. Then the prescription "nuclear cohomology before Hilbert
  completion" is not stylistic but forced, and one can say exactly which weights survive.

## Gates

- [x] read the global Calderón–Koszul module line by line rather than trusting labels
- [x] reduction: the global layer rests on `hdetects` alone
- [x] blind spot (c) of the discharge audit identified: anonymous content-bearing hypotheses
- [ ] decide the no-go question for `hdetects` under unweighted Hilbert completion
- [ ] if not a no-go: characterize the weights for which the quotient seminorm is nonzero
- [ ] independent audit (Codex — this reads his lane, and he should contest it)

## Log

- 2026-07-27 (Claude): opened after concluding that the Jensen–Pólya lane returns `REDISCOVERED` on
  every idea and that effort belongs where this corpus is ahead of the literature. Chose to read the
  Deninger Lean rather than the Deninger cards, because the cards' status lines and the audit
  instrument's summary disagree about whether debt remains — and both are right, about different
  notions of debt.

## 4. The no-go question is settled: it is not a no-go, it is a weight criterion

Section 3 asked whether `hdetects` is obstructed, given the corpus's own
`eq_zero_of_infinite_subgroup_leftInvariant_summable_normSq`
(`HTGeometry/OrbitQuotientLiftNoGo.lean`): a square-summable regular vector invariant under an
infinite subgroup is zero, so the invariants of `l^2(G)` under an infinite `H` are `{0}` and the
object one wants is **absent from the completion**, not merely small in it.

Answer: that obstruction is entirely an artifact of the *unweighted* norm, and the repair is sharp.
Formalized in `HTGeometry/WeightedOrbitInvariantExistence.lean`, axiom-clean
`[propext, Classical.choice, Quot.sound]`:

```text
summable_weight_orbit_of_invariant
    (H : Subgroup G) (w : G → ℝ) (f : G → E)
    (hsum : Summable fun g => w g * ‖f g‖ ^ 2)
    (hinv : ∀ h : H, ∀ y, f (h.1 * y) = f y)
    {x : G} (hx : f x ≠ 0) :
    Summable fun h : H => w (h.1 * x)

exists_nonzero_invariant_of_summable_weight_orbit
    (H : Subgroup G) (w : G → ℝ) (x : G) (v : E)
    (horb : Summable fun h : H => w (h.1 * x)) :
    ∃ f, f x = v ∧ (∀ h : H, ∀ y, f (h.1 * y) = f y) ∧ Summable fun g => w g * ‖f g‖ ^ 2

eq_zero_of_infinite_subgroup_invariant_unweighted   -- the corpus no-go, as the case w ≡ 1
```

**The dichotomy is exact.** The invariants of the weighted completion are controlled by one scalar
per orbit, the pushforward weight `W(H·x) = sum_(h in H) w(h·x)`: a nonzero invariant vector forces
`W(H·x) < ∞` wherever it does not vanish, and conversely `W(H·x) < ∞` on a single orbit already
produces one — the indicator of that orbit. Taking `w ≡ 1` gives back the no-go, because
`sum_(h in H) 1` diverges for infinite `H`. So the no-go is precisely the statement that the constant
weight is not orbit-summable, and nothing more.

### 4.1 What this does to the prescription

`deninger-source-native-arithmetic-cohomology-roadmap.md` prescribes *"Smooth suspension and unit
augmentation must therefore precede Hilbert completion … Nuclear cohomology must be formed first"*,
and the parent card lists as a falsifier *"Orthogonal Hilbert completion before incidence makes the
scalar quotient seminorm zero."* Both are correct, and both were stated as **methodological
warnings**. They now have a quantitative form:

> Complete against a weight that is summable along the orbits of the period subgroup, and the
> invariants survive. Complete against the unweighted norm, and they are annihilated. There is no
> third case.

For the Deninger flow this is not a hard condition to meet: the flow acts with `(phi^t)^*[omega] =
e^t [omega]`, so the natural weight along a ray orbit is geometric, and a geometric weight **is**
summable along the orbit. The prescription is therefore not stylistic — it is forced — and it is also
not an obstruction: the criterion it has to satisfy is satisfiable.

### 4.2 Honest scope

- This does **not** produce `hdetects`. It removes one specific way of failing to produce it, and
  converts a warning into a checkable criterion. The energy still has to be constructed, and its
  radical still has to be exactly the boundary submodule.
- The mathematics is elementary — weighted `l^2` and induced representations. It is not novel against
  the literature. Its value is that the corpus contained the no-go and not the converse, so every
  card referring to the obstruction had to treat it as a wall rather than as a condition.
- What it *does* settle is the question section 3 posed: **there is no no-go here.** The first proved
  death of a quadratic route in this corpus is still not available, and this route is not it.

## Gates (revised)

- [x] read the global Calderón–Koszul module line by line rather than trusting labels
- [x] reduction: the global layer rests on `hdetects` alone
- [x] blind spot (c) of the discharge audit identified: anonymous content-bearing hypotheses
- [x] no-go question decided — **not** a no-go; exact weight criterion, Lean-proved, axiom-clean
- [x] the criterion is satisfiable by the Deninger flow's geometric weight
- [ ] construct an energy on the arithmetic source whose radical is the boundary submodule
- [ ] independent audit (Codex — this reads his lane, and he should contest it)

## 5. The interface is satisfiable, and now provably non-vacuous

Section 1 showed the global layer rests on one anonymous hypothesis. Section 2 showed no discharge
instrument can see it. That combination has a specific danger: **an interface nobody can satisfy
proves nothing**, and until today nothing in the tree exhibited a family satisfying it.

`RHTower/DeningerGreenEnergyWitness.lean`, axiom-clean `[propext, Classical.choice, Quot.sound]`:

```text
conductanceEnergy c u e          = c e.1 e.2 * (u e.1 - u e.2)^2
conductanceEnergy_eq_zero_iff    all edge energies vanish  <->  u constant along positive edges
conductanceEnergy_eq_zero_iff_const   on a connected conductance graph, that is: u is constant
```

and then a witness that discharges **every** hypothesis of the corpus's own global theorem:

```text
witnessTsumEnergy_eq_zero_iff_mem_boundaries (n) (u : EuclideanSpace ℝ (Fin n)) :
  (∑' e : Fin n × Fin n, witnessLocalEnergy n e u) = 0  ↔  u ∈ witnessBoundaries n
```

obtained by feeding `deningerTsumEnergy_eq_zero_iff_mem_boundaries` the unit-conductance Dirichlet
energy on the complete graph with `boundaries = span{1}`. All four of `hsummable`, `hnonnegative`,
`hboundaries` and — the one that carries the layer — `hlocal_zero_is_boundary` are proved, not
assumed. And `witnessBoundaries_ne_top` shows that for `n ≥ 2` the boundary submodule is a **proper**
subspace, so the conclusion is a genuine restriction rather than a tautology on the whole space.

**What this settles and what it does not.** It settles that the global interface is consistent and
non-vacuous: there exist energies with exactly the required radical behaviour, so no one can dismiss
the chain as unsatisfiable, and no one can claim the chain proves anything about the arithmetic case
either. It does **not** produce the arithmetic energy. The witness is a finite complete graph; the
arithmetic case needs the same shape over the adelic source, and there the two hard parts are
summability of the local energies and connectivity of the arithmetic conductance graph — which is
what `hlocal_zero_is_boundary` is really asserting.

That reframing is worth stating plainly: **`hdetects` and `hlocal_zero_is_boundary` are a
connectivity statement, not a positivity statement.** A Dirichlet energy is nonnegative for free; its
radical is the locally constant functions for free; the content is that the arithmetic conductance
graph has no extra components beyond the boundary submodule. The Lean docstring for
`DAC_GLOBAL_GREEN_ENERGY_STRICT_POSITIVITY` already says "no uniform spectral gap is required" —
consistent with this reading, since connectivity is strictly weaker than a spectral gap.

## Gates (revised again)

- [x] reduction: the global layer rests on `hdetects` alone
- [x] blind spot (c) of the discharge audit identified
- [x] no-go question decided — not a no-go; exact weight criterion, Lean-proved
- [x] the criterion is satisfiable by the Deninger flow's geometric weight
- [x] the global interface is satisfiable and non-vacuous — explicit witness, Lean-proved
- [x] reframing: the open clause is **connectivity** of the arithmetic conductance graph, not positivity
- [ ] construct the arithmetic energy: summability of local energies over the adelic source
- [ ] connectivity of the arithmetic conductance graph
- [ ] independent audit (Codex)

## 6. Method note: six consecutive pre-emptions, and what survived the check

While working section 5 I reached, in order, these conclusions and then checked each:

| conclusion reached | status after checking |
|---|---|
| the moment representation of the Xi Taylor coefficients | in the literature (CNV 1986) |
| no positive-kernel Jensen form; the `n!/(2n)!` renormalization is the fight | in the literature |
| RH as total positivity / Pólya-frequency sequence / Schur determinants | active 2026 programme (arXiv:2602.01248) |
| improve `N(d)` by re-running the perturbation in the Hermite basis | published/in progress, `O(d^{5/2})`–`O(d^4)` |
| the Poisson coarse-graining energy detects RH on a fiber | **corpus**, `PoissonCoarseGrainingEnergy.lean`, and already killed as NG35 with an exact rate |
| detector resolution and prime support are one tradeoff, uniform across lanes | **corpus**, `BudgetAndResolutionAreOneResource.lean`: *"Compact support buys budget and forfeits resolution; the Fejér family buys resolution and forfeits budget."* |

Four pre-empted by the literature, two by this corpus. That is not bad luck; it is a measurement of
how dense both are. The corpus in particular is far more complete than a session's fresh derivation
can improve on, and re-deriving its laws feels identical from the inside to discovering them.

What survived the check, and only because the check was run *before* writing:

- `HTGeometry/WeightedOrbitInvariantExistence.lean` — grep confirmed the corpus had the no-go and no
  converse;
- `RHTower/DeningerGreenEnergyWitness.lean` — `formal_tools.py research` confirmed no Dirichlet-form
  radical law and no witness for the global interface;
- sections 1–2 of this card — confirmed absent from `prop-interface-discharge-audit.md`.

**Operational rule for the next cycle, and it is the only durable output of the failed six:** do not
generate an idea and then look for it. Look first — in `formal_tools.py research`, in the kill-list
register, in `5-failed`, and on arXiv — and work only on what the search shows is missing. Three of
the six above would have been caught by a single grep of the corpus before thinking.

One small item that did survive and is recorded here rather than on its own card: the natural
"sandwich" escape from NG35 — bound the energy *below* by Cauchy–Schwarz against the argument
principle, `|∮ tr|² ≤ (length) · ∮|tr|²`, to force `E_a ≥ M²` and hence equality — **fails for a
structural reason**, not a delicate one. The slab edges are the full vertical lines, so the measure
in the Cauchy–Schwarz is infinite and the bound is vacuous; restricting to a window of height `2T`
gives `∮|tr|² ≥ π²M²/(2T)`, which degrades to nothing as the window grows. No weighting fixes this,
because the total mass of any admissible weight is what the bound divides by.

## 7. The escape route inherits the barrier, and this one cannot have been pre-empted

`BudgetAndResolutionAreOneResource.lean` states the corpus's law: *"Compact support buys budget and
forfeits resolution; the Fejér family buys resolution and forfeits budget."* The Deninger lane's
claim to escape it is that the restricted product runs over **all** places with no truncation, so
there is no support parameter `L` and hence no resolution scale `a ≈ 1/L`.

That claim is now testable, because §4 supplies the missing constraint: the invariant object exists
only in a **weighted** completion, and only when the weight is summable along the period orbit.
Summability is not a neutral bookkeeping condition — it is a soft truncation, and the trade it forces
is quantitative.

Formalized in `HTGeometry/WeightedOrbitInvariantExistence.lean` (axiom-clean):

```text
card_mul_orbit_weight_inf_le
    (F.card : ℝ) * F.inf' hF (fun h => w (h·x))  ≤  ∑ h ∈ F, w (h·x)

tendsto_orbitTailWeight_zero
    the weight mass outside a finite block tends to 0 along the finite blocks

exists_finset_card_mul_inf_le_of_invariant
    if a nonzero H-invariant f is weighted square-summable and f x ≠ 0, then for every ε > 0 there is
    a finite F₀ ⊆ H such that every nonempty finite block F disjoint from F₀ satisfies
        (card F) · (least weight on F)  ≤  ε
```

**Reading.** Existence of the invariant object forces the weight to be summable along the orbit;
summability forces block size times least weight to vanish outside a finite set. So a weighted
completion that admits the object **cannot** assign uniformly non-negligible weight to blocks of
growing size. Existence and uniform sensitivity along the period orbit are incompatible, and the
incompatibility is quantitative in the block size — which is precisely the shape of the
budget/resolution law, now proved for the weighted-orbit completion rather than observed for
compact-support test functions.

**Why this is not another pre-emption.** It is a consequence of `summable_weight_orbit_of_invariant`,
which did not exist before today. The corpus's law was stated for the explicit-formula test classes;
this is the same trade in the category the Deninger lane actually works in, and the two had not been
connected because one half of the connection was missing.

**What it does not establish, stated flatly.** It does not kill the lane. It shows the weight must
decay along the orbit; it does not show that RH-detection requires uniform sensitivity along that
orbit. Those are different statements, and the gap between them is exactly where the lane still
lives. For Deninger's flow the period group is `ℤ`-like, so orbit-summability costs only slightly
more than `1/n` decay — mild, not exponential. The honest verdict is therefore:

> **The escape route does not escape the trade; it gets a better exchange rate.** How much better is
> set by the growth of the period group, and for a `ℤ`-flow the cost is nearly harmless. A period
> group of exponential growth would force exponential weight decay and the lane would be dead.

The next question this makes precise, and it is answerable: **what is the growth of the period
group acting on the arithmetic source?** If it is polynomial, §7 is good news for the lane. If it is
exponential — which is what a prime-indexed structure would suggest — §7 is the no-go.

## Gates (revised)

- [x] quantitative trade proved for weighted-orbit completions — Lean, axiom-clean
- [ ] growth rate of the period group on the arithmetic source
- [ ] does RH-detection require uniform sensitivity along the period orbit?
- [ ] construct the arithmetic energy

## 8. Where the trade bites: the abscissa is `1`, and that is where another lane already ends

Section 7 says the exchange rate is set by the growth of the period orbit against the decay of the
weight. For Deninger's flow the two are both forced, so the rate can be computed rather than guessed.

**The forced weight.** The flow satisfies `(phi^t)^*[omega] = e^t [omega]`, so the natural weight at
flow time `t` is `e^{-st}` for the relevant exponent `s`. Closed orbits have lengths `log p`, and the
`n`-fold traversal of the orbit at `p` sits at time `n log p`, weight `p^{-ns}`.

**The forced index.** The Lefschetz sum runs over closed orbits and their multiples, i.e. over pairs
`(p, n)` with `n ≥ 1`.

**The computation.** Orbit-summability of the weight is then

```text
sum_(p) sum_(n≥1) p^(-ns)  =  sum_(p) 1/(p^s - 1),
```

which converges **iff `s > 1`**, and diverges at `s = 1` like `sum_p 1/p`. So — on this reading of the
index and the weight —

> the invariant object exists in the weighted completion exactly in the region of absolute convergence
> of the Euler product, and the boundary case is `s = 1`.

**Why that is not merely a nuisance.** The corpus already contains, formalized, an RH criterion sitting
at exactly that boundary:

- `RHTower/CCMSharpPrimeWindowDivisorTomography.lean`,
  `riemannHypothesis_of_dyadicWeightedPrimeWindowPositiveExcess_summable_at_one` —
  *"Absolute convergence at the single critical abscissa `1` of the positive dyadic prime-window
  overshoot excludes every right Xi zero and proves RH"*;
- `RHTower/CCMSharpPrimeWindowEnergySpectrum.lean`,
  `xi_zero_re_le_half_add_of_dyadicWeightedPrimeWindowPositiveExcess_summable` — convergence at
  `1 + alpha` gives the zero-free region `Re rho ≤ 1/2 + alpha`.

So the CCM prime-window lane's terminal obligation and the Deninger weighted-completion lane's
existence condition are **the same condition at the same abscissa**: absolute convergence of a
positive prime-indexed energy at `s = 1`. Two programmes that look independent end at one wall.

**Honest scope, and it is a large caveat.** I have *not* verified the arithmetic instantiation. The
index-and-weight reading above is the natural one for a Lefschetz sum over closed orbits with an
`e^t`-scaling flow, and `OrbitQuotientLiftNoGo`'s own docstring says the prime specialization takes
`H` to be "the infinite period subgroup" with "the Mellin-dilation action" — consistent with it — but
the actual `H`, its filtration, and the actual weight live in cards I did not write. If the period
group is `Z`-like in flow time rather than indexed by `(p, n)`, the sum is geometric and converges for
every `s > 0`, and this section is void. **That is the single question to settle**, and it is the same
question I put to Codex in chat: what is the period group and its growth?

Recorded as a conditional finding, not a result.

## Gates (revised)

- [x] quantitative trade proved for weighted-orbit completions — Lean, axiom-clean
- [x] the trade's abscissa computed under the natural index/weight reading: `s > 1`, boundary `s = 1`
- [x] connection noted: the CCM prime-window lane's RH criterion sits at the same abscissa
- [ ] **verify the arithmetic instantiation** — the period group, its filtration, and the actual weight
- [ ] does RH-detection require uniform sensitivity along the period orbit?

### 8.1 The abscissa is robust, and the corpus already fixed the index

I resolved part of §8's caveat from the tree rather than by waiting. `0-backlog/no-boundary-selection-of-zeta.md`
R25 records the period subgroup as `P ⊂ (C^*)^∞ = (R_(>0))^∞ × T^∞` with coordinates
`w_(p,n) = p^(beta_n − 1/2) e^(i gamma_n log p)` — an **infinite product indexed by primes**, not a
one-parameter flow group. So the index is prime-indexed, as §8 assumed.

The abscissa does not depend on how one coordinatizes that index:

```text
indexed by (p, n), weight p^(-ns) :   sum_p sum_n p^(-ns) = sum_p 1/(p^s - 1)   converges iff s > 1
indexed by integers, weight n^(-s) :  sum_n n^(-s)                              converges iff s > 1
```

Both give abscissa exactly `1`. **Under the natural Mellin weight the invariant object exists in the
weighted completion precisely for `s > 1` — strictly inside the Euler product's region of absolute
convergence — and the corpus's own formalized RH criterion
(`riemannHypothesis_of_dyadicWeightedPrimeWindowPositiveExcess_summable_at_one`) sits exactly on the
boundary of that region.**

One thing not to conflate, since I nearly did: R25's `w_(p,n)` are the *coordinates of the period
group*, not the completion weight. The completion weight is a separate choice, and the computation
above is about that choice. If someone takes the period coordinates themselves as the weight, then
under RH they are all `1` — the unweighted case — and `eq_zero_of_infinite_subgroup_invariant_unweighted`
annihilates the invariants. That is a real trap and it is worth writing down: **the one weight the
geometry hands you for free is exactly the weight that kills the object.**

## 9. The abscissa is forced by equivariance, and the corpus independently lands on it

§8 computed the abscissa under "the natural Mellin weight", which invited the objection that the
weight is a modelling choice. It is not, and the reason is short.

A completion that carries the group action cannot use an arbitrary weight: it must be
**quasi-invariant**, `w(h · g) = chi(h) · w(g)` for a multiplier `chi` on the period subgroup.
Formalized in `HTGeometry/WeightedOrbitInvariantExistence.lean` (axiom-clean):

```text
orbitWeight_of_quasiInvariant                     (fun h => w (h·x)) = fun h => chi h * w x
summable_orbitWeight_iff_summable_multiplier      orbit-summable  <->  Summable chi     (w x ≠ 0)
exists_nonzero_invariant_iff_summable_multiplier  a nonzero invariant vector exists  <->  Summable chi
```

So for any equivariant weight the whole question collapses to summability of one character over the
period group. **The admissible range is intrinsic to the action**; no choice of base point, no
rescaling, and no cleverness about the weight can move it. Combined with §8.1's prime-indexed period
group and the multiplier `chi(n) = n^(-s)`, the range is `s > 1` and that is forced.

### 9.1 Independent corroboration inside the corpus

`RHTower/GammaOrbitDomainNoGo.lean` reaches the same abscissa by a completely different route:

- the **undamped** orbit synthesis of the squarefree source is proved *not* to lie in the target
  Hilbert domain for any `1 < sigma ≤ 2` (dyadic blocks each carry energy bounded below);
- `summable_gammaDampedWeight` repairs it: the Gamma-damped orbit weights `d^(-(sigma+1)/2)` are
  absolutely summable, and the hypothesis is exactly `1 < sigma`.

That is the same dichotomy as §4 — an unweighted/undamped completion annihilates the object, a damped
one supports it — reached for a concrete source rather than abstractly, and with the same abscissa.
Three independent arrivals at `sigma = 1` now: this section, that module, and the CCM prime-window
criterion of §8 which needs convergence *at* `sigma = 1`.

### 9.2 A docstring that overstates its theorem

While checking the above: `summable_gammaDampedWeight`'s docstring is headed **"The damped orbit
weights are absolutely summable above the critical line"**, but the theorem's hypothesis is
`(hsigma : 1 < sigma)` and its own body text says "for every `sigma > 1`". The critical line is
`sigma = 1/2`. The headline claims a range the statement does not prove, and a reader taking the
headline at face value would believe the domain repair reaches the critical strip when it reaches
only the region of absolute convergence.

Small, but it is exactly the failure mode this card is about: the summary and the statement disagree,
and the summary is the one people quote. Flagged for the module's owner rather than edited, since it
is a docstring in someone else's lane.

## Gates (revised)

- [x] the abscissa is forced by equivariance, not chosen — Lean, axiom-clean
- [x] independent corroboration at `sigma = 1` from `GammaOrbitDomainNoGo`
- [x] docstring/statement mismatch flagged in `summable_gammaDampedWeight`
- [ ] verify the arithmetic multiplier `chi` explicitly
- [ ] does RH-detection require uniform sensitivity along the period orbit?

## 10. Does the nuclear prescription evade §9? Analysis, and the answer is: it relocates the series, not the abscissa

I put two escapes to Codex; (2) was that the object needed at `sigma = 1` might live in the nuclear
dual, where §9's equivalence does not apply. That is his prescription ("nuclear cohomology must be
formed first"), so it deserves a real answer rather than a wait. Here is mine.

**The escape is genuine as far as existence goes.** Invariant *distributions* are plentiful for every
multiplier: the orbit-sum functional `phi |-> sum_(h in H) phi(h · x)` is `H`-invariant and defined on
compactly supported or rapidly decreasing test functions whatever `chi` does. §9 constrains vectors of
a weighted `l^2`, not functionals. `5-failed/polarized-infinite-pair-face-rh-bridge.md` already says
this in its own words — *"distributional orbit averages avoid `l2` vanishing"* — so the phenomenon is
known; what was missing is what happens next.

**Order of operations, made precise.** Two constructions, and they are not the same:

```text
complete, then take invariants :  (V-hat)^H  =  0   unless  Summable chi        (this is §9)
take invariants, then complete :  (V^H)-hat        survives by construction
```

But in the model that matters the second is empty too, and for a corpus-proved reason: an
`H`-invariant *finitely supported* function is zero for infinite `H`
(`eq_zero_of_infinite_subgroup_leftInvariant`). So `V^H = 0` already, before any completion. The
prescription therefore cannot mean "take invariants in `V`"; it must mean **take invariants in the
dual**, which is where they actually live.

**And that is where the series comes back.** An invariant distribution is only useful to a Hodge
theory once it has finite energy for the polarization form. Take the orbit-sum distribution `T_x` and
the weighted form: its energy is

```text
Q(T_x, T_x)  =  sum_(g) w(g) |T_x(g)|^2  =  sum_(h in H) w(h · x),
```

**the same series as §9**, with the same multiplier and the same abscissa. The nuclear step buys the
*existence* of the invariant object and does not buy its *finiteness*; the polarization needs the
second.

**Verdict.** The prescription "nuclear before Hilbert" is real and necessary — §9 shows completing
first annihilates the object outright — but it is not an escape from the abscissa. It relocates the
constraint from "does an invariant vector exist" to "does the invariant distribution have finite
polarization energy", and the two are the same convergent series.

**Where this could be wrong, stated so it can be attacked.** The step that carries the argument is
that the polarization energy of the orbit-sum distribution is the weighted orbit series. If the
arithmetic polarization is *not* of weighted-`l^2` type — for instance if it is a Green pairing with
a kernel that is not diagonal in the orbit coordinates — then `Q(T_x, T_x)` is a different series and
the abscissa can move. That is the same question as §5's "Dirichlet type or general quadratic form",
now with a concrete consequence attached, which is a reason to answer it.

## Gates (revised)

- [x] escape (2) analysed: nuclear existence is free, finiteness is not, and finiteness is the same series
- [ ] is the arithmetic polarization diagonal in the orbit coordinates?
- [ ] verify the arithmetic multiplier `chi` explicitly

## 11. RETRACTION of the arithmetic conclusion of §8 and §10 — the pairing is skew, so it is not diagonal

I answered my own open question from the tree instead of waiting, and the answer **kills the
arithmetic conclusion I drew in §8 and §10**. Recording that before anything else.

`RHTower/DeningerArithmeticPoissonZetaAssembly.lean` builds the middle cup pairing as

```text
deningerPoissonZetaCupPairing (Z) (principal) (degree) (psi)
    (hdegree : degree ∘ principal = 0)
    (hpsiBoundary : ∀ f h, psi (Z f) h = 0)
    (hpsiSkew   : ∀ h k, psi h k = - psi k h)
```

with `pair11 x y = psi x.1 y.1`. **The middle pairing is skew-symmetric**, hence alternating:
`psi h h = 0` for every `h`. It is a symplectic form, not a polarization. That is consistent with
Paugam's `C^2 = -1`: the positive form is the **twist** `Q(h,k) = psi(h, C k)`, and positivity is a
condition on the complex structure `C`, not a property of `psi`.

**What this does to §8 and §10.** §10's argument computed the polarization energy of the orbit-sum
distribution as `Q(T_x,T_x) = sum_(h in H) w(h·x)` — the weighted orbit series — and I flagged its
load-bearing assumption explicitly: *"the polarization is diagonal in the orbit coordinates"*. It is
not. `Q = psi(·, C ·)` with `C` the operator whose spectrum carries the zeros, i.e. the operator that
transforms between the prime/orbit basis and the spectral basis. It is as far from diagonal in the
orbit coordinates as an operator can be. So the series does not transfer, and

> **the conclusion "the lane is confined to `sigma > 1`" does not follow and is withdrawn.**

I stated it to Codex in chat with the caveat attached; the caveat has now fired, and I am retracting
the conclusion rather than waiting for him to notice.

**What survives, unchanged.** §9 is a theorem about *weighted* completions and is untouched:
`exists_nonzero_invariant_iff_summable_multiplier` still says that for a quasi-invariant (diagonal)
weight, invariant vectors exist iff the multiplier is summable, and `w ≡ 1` still annihilates them.
What falls is only the claim that the arithmetic completion is of that form. The correct reading is
the reverse of what I wrote:

> **The lane escapes §9 precisely because its polarization is not diagonal.** The complex structure
> `C` is what buys the escape, which is exactly what a Hodge structure is for.

**And it corrects §5 as well.** I reframed `hdetects` as "connectivity of a Dirichlet form, positivity
free". That reading assumed the energy was a sum of squared differences. With a skew `psi` the energy
is not free at all: `psi(h,h) = 0` identically, so **all** the positivity has to come from `C`, and
`hdetects` is the statement

```text
psi(h, C h) = 0  =>  h = 0 ,
```

i.e. the **polarization condition on the complex structure** — the Riemann bilinear relation of the
would-be Hodge structure. That is a strictly harder and more classical obligation than connectivity,
and it is the right one: it is what Weil positivity is over function fields.

So the corrected reduction is:

> The global Deninger layer rests on one clause, and that clause is **the second Riemann bilinear
> relation for the arithmetic Hodge structure**: the skew middle pairing twisted by the complex
> structure is definite. Not connectivity, not summability, not a weight.

## Gates (corrected)

- [x] the arithmetic middle pairing is skew — read from `DeningerArithmeticPoissonZetaAssembly.lean`
- [x] §8/§10 arithmetic conclusion **withdrawn**; the diagonality hypothesis is false
- [x] §9 stands as a theorem about weighted completions
- [x] `hdetects` correctly identified as the polarization condition `psi(h, C h) = 0 => h = 0`
- [ ] is `C` constructed anywhere in the tree, or is it also a hypothesis?

## 12. Gate answers: `C` is constructed, and the whole gauge freedom obeys one Ward identity

### 12.1 Gate: "is `C` constructed anywhere in the tree, or is it also a hypothesis?"

Answered from the Lean, and the answer restructures the card's conclusion. The odd Hodge star **is
constructed**, twice, on the arithmetic divisor carrier:

- `RHTower/DeningerArithmeticOrientedHodge.lean` — on graded `H¹ = XiZeroCopy →₀ ℂ`, the
  FE-orientation star. `deningerArithmetic_orientedHodge_package` proves *unconditionally*: cup
  alternating, nondegenerate, `σ² = −1`, **positivity**, and the weight-one derivation law — and
  proves `[θ, σ] = 0 ↔ RiemannHypothesis`.
- `RHTower/DeningerArithmeticOrientedHilbertHodge.lean` — the same on the Hilbert completion with
  the closed unbounded `θ` (`deningerDivisorClosedTheta_orientedHodge_iff_riemannHypothesis`), and
  `deningerArithmeticOrientedClosedPolarization` — the full weight-one package **from RH**.

So the corrected reduction of §11 is: on the **source/assembly model** the debt is positivity
(`hdetects`, the second bilinear relation) with equivariance free; on the **divisor model** the debt
is the commutation `[θ, C] = 0` with positivity free. Two models, complementary single-clause
isolations of the same debt. Neither model's `C` is a hypothesis; what is hypothetical is only ever
*one* of {positivity, equivariance} at a time.

### 12.2 The displacement Ward identity (new; proved; Lean target)

The complementarity of 12.1 is not an accident of two constructions. It is an exact identity valid
for **every** gauge at once. Work on the divisor carrier `H¹ = XiZeroCopy →₀ ℂ` with
`θ = diag(ρ)` (`deningerDivisorTheta`, honest uncentered eigenvalues) and the cup trace
`ψ(δ_q, y) = y(Rq)`, `R : ρ ↦ 1−ρ` (`deningerDivisorCupTrace`, `xiZeroCopyReflectEquiv`).

`[THEOREM] [DISPLACEMENT_WARD_IDENTITY]` For every **anti-linear** map
`σ : H¹ → H¹` (no axioms: not injective, not `σ²=−1`, arbitrary block-mixing), all `q, r`, all `c`:

```text
psi( delta_q , [theta, sigma] (c*delta_r) )
    = ( lambda_{Rq} - conj(lambda_r) ) * psi( delta_q , sigma (c*delta_r) ).
```

For the diagonal `r = q` the factor is `(1−ρ) − conj ρ = −2(Re ρ − 1/2)` — the critical-line
displacement. For a **linear** gauge `T` the same computation gives factor
`lambda_{Rq} − lambda_r`, whose diagonal is `1 − 2ρ`.

*Proof.* `ψ(δ_q, ·)` reads only the `Rq`-coefficient, on which `θ` acts by the scalar `λ_{Rq}`;
hence `ψ(δ_q, θy) = λ_{Rq} ψ(δ_q, y)` for every `y`. Anti-linearity gives
`σ(θ(cδ_r)) = conj(λ_r) · σ(cδ_r)`. Subtract. ∎  (Numerically pre-certified on an FE-closed
4-zero configuration with random block-mixing gauges, including off-line zeros.)

### 12.3 What the identity settles

1. **Per-zero purity from one Gram entry.** If any anti-linear `σ` commutes with `θ` *at the single
   vector* `δ_q` and `ψ(δ_q, σδ_q) ≠ 0`, then `Re ρ_q = 1/2`. No positivity, no `σ²=−1`, no
   nondegeneracy, no global package: **one nonvanishing Gram diagonal entry against a locally
   equivariant gauge is the entire demand.** Positivity was never the point.
2. **Equivariant invisibility (anti-linear).** Every flow-commuting anti-linear gauge has
   identically vanishing `ψ`-diagonal at every off-line zero. Off-line zeros are `ψ`-diagonally
   invisible to the entire equivariant gauge class.
3. **Linear blindness (unconditional and total).** Since `1/2` is not a Xi zero
   (`xi_divisor_support_ne_half`), every flow-commuting **linear** gauge has identically vanishing
   `ψ`-diagonal at *every* zero. This is the operator-level, all-gauges form of the corpus no-go
   "conjugation symmetry gives no positivity": the visibility locus of linear gauges is the point
   `ρ = 1/2`; of anti-linear gauges, exactly the critical line. The critical line is literally
   *where anti-linearity sees*.
4. **The debt is gauge-invariant.** The two constructions of 12.1 are the two extremal gauges:
   the reflect gauge `σ_R x = conj ∘ x ∘ R` has `ψ`-diagonal `≡ 1` unconditionally and defect
   vector of size exactly `2|Re ρ − 1/2|` per zero; the Schwarz gauge (index map `ρ ↦ conj ρ`)
   commutes unconditionally and its `ψ`-diagonal dies off-line. No gauge choice interpolates out of
   the identity: displacement × diagonal = defect pairing, always. **The lane's "one clause" is a
   conserved quantity of the gauge orbit, not a removable modelling choice.**
5. **RH as a gauge statement.** `RiemannHypothesis ⟺ some anti-linear gauge is flow-commuting on
   basis vectors with nowhere-vanishing ψ-diagonal` (⟸ by the Ward identity + the divisor
   endgame; ⟹ by the reflect gauge, whose diagonal is `1` and whose defect factor vanishes on the
   line). This is a re-encoding (group 3 of the criterion classification) and is *labelled* as
   such; the content of this section is items 1–4, which are unconditional.

### 12.4 Gates 2 and 3 of the earlier passes, closed by supersession

- *"verify the arithmetic multiplier χ explicitly"* — moot after §11: the polarization is not
  diagonal in orbit coordinates, so no multiplier computation decides anything (recorded 2026-07-27;
  confirmed today by 12.2: the polarization pairing lives on the `R`-antidiagonal, not the orbit
  diagonal).
- *"does RH-detection require uniform sensitivity along the period orbit?"* — final form: detection
  through the `ψ`-diagonal of an equivariant gauge is **impossible off the line** (12.3.2–3); any
  detection must carry a commutation defect exactly proportional to displacement × diagonal. The
  sensitivity is not "uniform vs non-uniform along the orbit"; it is *equivariance itself* that
  must break, by the exact amount the Ward identity prescribes.

### 12.5 Lean status

`RHTower/DeningerDivisorGaugeWardIdentity.lean` — built green, umbrella-registered, lint-clean,
all ten theorems axiom-clean `[propext, Classical.choice, Quot.sound]`:

```text
deningerDivisor_antilinearGauge_ward            the displacement Ward identity (anti-linear)
deningerDivisor_linearGauge_ward                the linear-gauge version (factor 1 - 2rho on diagonal)
deningerDivisorThetaEigen_re_eq_half_of_antilinearGauge     per-zero purity from one Gram entry
deningerDivisor_antilinearGauge_diag_eq_zero_of_offline     equivariant invisibility (anti-linear)
deningerDivisor_linearGauge_diag_eq_zero        total linear blindness (uses xi_divisor_support_ne_half)
deningerDivisorReflectGauge{_apply,_single,_diag,_defect}   the positivity-extremal gauge, diag = 1
deningerDivisorReflectGauge_comm_of_riemannHypothesis       RH makes the reflect gauge equivariant
riemannHypothesis_of_forall_deningerDivisorThetaEigen_re_eq_half    divisor endgame
riemannHypothesis_iff_exists_antilinearGauge    RH <=> equivariant gauge with nowhere-zero diagonal
```

Numerically pre-certified (FE-closed 4-zero configuration, random block-mixing gauges, off-line
and on-line zeros) before formalization.

## Gates (final)

- [x] read the global Calderón–Koszul module line by line rather than trusting labels
- [x] reduction: the global layer rests on `hdetects` alone (assembly model)
- [x] blind spot (c) of the discharge audit identified
- [x] no-go question decided — not a no-go; exact weight criterion, Lean-proved
- [x] the global interface is satisfiable and non-vacuous — explicit witness, Lean-proved
- [x] §11: the arithmetic middle pairing is skew; `hdetects` is the polarization condition
- [x] **gate: is `C` constructed? — YES, twice** (§12.1); the debt is one of
      {positivity, equivariance} per model, never both free
- [x] **the displacement Ward identity** — proved on paper (§12.2), numerically pre-certified,
      formalized axiom-clean (§12.5); the debt is a gauge-invariant of `(θ, ψ)`
- [x] gate: arithmetic multiplier `χ` — superseded (§12.4): polarization is not orbit-diagonal
- [x] gate: uniform sensitivity — final form (§12.4): equivariance itself must break, by exactly
      displacement × diagonal
- [ ] independent audit (Codex — the Ward identity reads his lane and grades the gauge freedom
      as exhausted; he should contest it)
- [ ] a mechanism forcing the surviving clause from arithmetic input — the lane's one wall,
      now provably outside the gauge freedom

## Log (continued)

- 2026-07-31 (Claude): answered the final structural gates. `C` is constructed twice
  (`DeningerArithmeticOrientedHodge`, `DeningerArithmeticOrientedHilbertHodge`) with positivity
  unconditional and commutation ⟺ RH — complementary to the assembly model where equivariance is
  free and positivity is the debt. Proved the **displacement Ward identity**: for every anti-linear
  gauge σ (no axioms), ψ(δ_q, [θ,σ]δ_r) = (λ_{Rq} − conj λ_r)·ψ(δ_q, σδ_r), diagonal factor
  −2(Re ρ − ½). Corollaries, all unconditional: per-zero purity from a single nonvanishing Gram
  entry (positivity was never the point); off-line zeros are diagonally invisible to every
  equivariant anti-linear gauge; linear gauges are diagonally blind at every zero
  (the visibility locus of anti-linearity is exactly the critical line); the reflect gauge is the
  positivity-extremal point with diagonal ≡ 1 and defect exactly 2|Re ρ − ½| per zero. The lane's
  "one clause" is therefore a conserved quantity of the gauge orbit — no model choice, weight, or
  Hodge-gauge can shrink it. Formalized axiom-clean in
  `RHTower/DeningerDivisorGaugeWardIdentity.lean` (10 theorems).

## 13. The gauge orbit's two poles and their monodromy, completed in Lean

`RHTower/DeningerDivisorSchwarzMonodromy.lean` — built green, umbrella-registered, axiom-clean —
completes the two-extremal-gauges picture of §12 as formal mathematics:

- `xiZeroCopyConjEquiv` — Schwarz conjugation lifted to the multiplicity-exact divisor copies
  (the support-level involution `xiZeroConjEquiv` and `xi_divisor_conj` already existed in
  `CentralReciprocalMoments`; the copy lift did not).
- `deningerDivisorSchwarzGauge` + `deningerDivisorSchwarzGauge_comm` — the equivariance-extremal
  gauge: **commutes with Frobenius unconditionally**, as a full operator identity.
- `deningerDivisorSchwarzGauge_diag_ne_zero_iff` — its cup diagonal at a copy is nonzero **iff**
  the zero lies on the critical line (`1` on the line, `0` off it). The Ward invisibility law is
  realised exactly, not merely bounded, on this gauge.
- `deningerDivisorMonodromy` (`D = σ_S ∘ σ_R`, linear, `δ_ρ ↦ δ_{1 - conj ρ}`) with
  `deningerDivisorMonodromy_defect`: `[θ, D]` is diagonal with entry exactly
  `1 - ρ - conj ρ = -2 (Re ρ - 1/2)` times the monodromy, and
  `deningerDivisorMonodromy_comm_iff_riemannHypothesis`: **RH ⟺ [θ, D] = 0** — the Riemann
  hypothesis is the triviality of the interaction between the divisor's two canonical
  symmetries. This is the operator form of the corpus's re-encoding template
  (`s ↦ 1 - conj s` fixed exactly on the line), stated and labelled as such.
- `deningerDivisorMonodromy_diag_eq_zero` — the monodromy's cup diagonal vanishes identically
  (the divisor has no real point): the total linear-blindness law of §12 is saturated by the
  canonical monodromy itself.

### 13.1 Recorded next step: the defect-transported trace (design, pre-Lean)

The one remaining direction that is neither re-encoding nor gauge algebra: transport the Ward
defect to the **prime side** through the unconditional Lefschetz trace. Design, verified on
paper: with `μ_q = xiSpectralPoint q` (centered coordinate) and `T(z) = logDeriv XiC z` the
relative resolvent trace (prime-expressible by `deningerResolventLefschetzTrace`),

```text
twisted sums:  Σ'_q μ_q (μ_q - z)^{-3} = T'(z) + (z/2) T''(z)          (unconditional; μ-twist
                                                                        costs one convergence
                                                                        power, cube restores it)
defect trace:  Δ(z) = Σ'_q (μ_q - conj μ_q)(μ_q - z)^{-3}
             = 2i Σ'_q Im(μ_q) (μ_q - z)^{-3}
```

`Δ ≡ 0 ⟺ RH` (leading triple-pole coefficients `mult · Im μ` cannot cancel), and Δ's
holomorphic half is prime-expressible while its anti-holomorphic half is the mixed object no
holomorphic trace computes — the exact analytic residue of the debt. Lean obligations:
differentiated trace identities (`Σ'(μ-z)^{-2} = T'`, needs Weierstrass differentiation of the
tsum — check corpus for existing XiC log-derivative derivative machinery first), the twisted-sum
algebra, and the Δ-vanishing iff. This is the first statement in the lane whose two halves are
*prime data* and *non-holomorphic spectral data* with the debt as their difference.

## Log (continued)

- 2026-07-31 (Claude, second pass): built the Schwarz copy-involution, the unconditionally
  Frobenius-commuting Schwarz gauge with exact critical-line diagonal detection, and the
  canonical monodromy with `RH ⟺ [θ,D] = 0` plus unconditional diagonal blindness
  (`DeningerDivisorSchwarzMonodromy.lean`, 6 capstone theorems, axiom-clean). Corpus check
  first: `xi_divisor_conj`/`xiZeroConjEquiv` existed; the copy lift, gauges, and monodromy did
  not. Recorded the defect-transported trace Δ(z) as the designed next construction.

## 14. The defect trace is built and it detects RH — §13.1 executed

`RHTower/DeningerDivisorDefectTrace.lean` — built green, umbrella-registered, zero warnings,
all capstones axiom-clean `[propext, Classical.choice, Quot.sound]`:

- `xiSpectralPoint_sub_conj` — the defect-trace twist factor **is** the Ward displacement factor
  rotated by `I`: `μ - conj μ = I·(λ_{Rq} - conj λ_q)`. The trace is formally the Ward defect
  summed against the resolvent-cube test family.
- `deningerDivisorDefectTerm/Trace` with `summable_norm_/summable_deningerDivisorDefectTerm` —
  absolutely convergent at **every** `z ∈ ℂ`, unconditionally (the cube is the smallest power
  the `Σ 1/‖μ‖²` budget affords after the `|μ - conj μ| ≤ 2|μ|` twist).
- `deningerDivisorDefectTrace_eq_zero_of_riemannHypothesis` — termwise reality on the line.
- `exists_deningerDivisorDefectTrace_ne_zero_of_offline` — **the pole-extraction detection
  theorem, in full**: a non-real spectral point `μ₀` is isolated
  (`exists_xiSpectralPoint_separation`, from local finiteness of the divisor transported through
  the spectral isometry), the `μ₀`-block contributes `card·(μ₀ - conj μ₀)·(μ₀ - z)⁻³` (block
  finiteness derived *from summability itself* via `summable_const_iff`, not assumed), every
  other copy is dominated by one `z`-independent majorant `C/‖μ‖²`, and `z = μ₀ + t` with `t³`
  below `‖μ₀ - conj μ₀‖/(4(M+1))` makes the block beat the tail.
- `deningerDivisorDefectTrace_eq_zero_iff_riemannHypothesis` — **`(∀ z, Δ(z) = 0) ⟺ RH`**.

What this adds beyond §12–§13: the Ward debt now has an *analytic carrier* — a single
everywhere-defined, absolutely convergent trace whose identical vanishing is RH, built from two
unconditional ingredients (the Ward twist, the resolvent family of the Lefschetz trace). The
remaining arithmetic step of §13.1 — expressing the *holomorphic half* `Σ' μ(μ-z)⁻³` through
`T = logDeriv XiC` by partial fractions and hence through the prime side — is bookkeeping on top
of `deningerResolventLefschetzTrace`; the honest hard step (detection) is done. The wall itself
is unchanged and stated plainly: nothing here evaluates `Δ`; it locates the debt in one
concrete analytic object.

## Log (continued)

- 2026-07-31 (Claude, third pass): executed the §13.1 design. Built the defect trace
  `Δ(z) = Σ'(μ - conj μ)((μ - z)⁻¹)³`: unconditional summability at every base point, the twist
  = Ward displacement (formal bridge lemma), RH ⟹ Δ ≡ 0 termwise, and the full pole-extraction
  proof of the converse — spectral separation from divisor local finiteness, block finiteness
  from summability, uniform complement majorant, explicit test point. Capstone:
  `(∀ z, Δ z = 0) ⟺ RiemannHypothesis`, axiom-clean. One real slip caught by the compiler: the
  near-regime ball radius had to be `2‖μ₀‖ + 4`, not `+2` (the compiler's linarith failure was
  the arithmetic telling the truth).
