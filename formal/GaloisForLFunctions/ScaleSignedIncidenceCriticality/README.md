# Scale-Signed Incidence Criticality (`GaloisForLFunctions.ScaleSignedIncidenceCriticality`)

**One question.** A proof never touches the arithmetic of `ℤ` directly; it touches a list of
observables of it — coefficient magnitudes, amplitudes, moments, a positivity certificate at one
aperture, a node density, a zero list up to a height. Which lists of observables can decide the sign
of the critical arithmetic form, and, for a list that cannot decide it, what is the best bound it
*can* certify?

This programme is the exact calculus of that question. Its primitive object is a **reading**
`r : D → O` of a class `D` of data, its basic invariant is the **resolution limit**
`sup {I(e) : r(e) = r(d)}` — the exact best bound on an invariant `I` that any method reading `r` can
prove — and its basic theorem is the **collapse–resolution dichotomy**: a reading either moves every
collapse that changes the verdict, or it proves nothing. Every statement here is unconditional and
names its reading, its collapse and its witness pair.

The field is the one specified in `docs/reports/review-2110/argon.md`, Part II: *Scale-Signed
Arithmetic Incidence & Criticality Theory*. What is formalised here is its admissibility core — the
part that converts the corpus's individual no-gos into one calculus with a numerical unit, together
with the positive half that calculus forces: if a sign at one aperture determines nothing, name the
magnitudes that determine everything.

---

## The shared target: the sign of the critical arithmetic form

Nine programmes of this corpus work on one object. The Riemann Hypothesis is the nonnegativity of
one critical arithmetic form, and the form can be read in three equivalent faces:

- the **incidence face** (Arithmetic Incidence Positivity, `ArithmeticIncidencePositivity`):
  conductance by conductance, on pairs of points `(x, y)` of the logarithmic line, with the
  arithmetic edges indexed by divisibility (`a ∣ b`) and by products (`ab` a prime power), and the
  pole as the only positive source on crossing pairs;
- the **lag face** (Square-Root Threshold, `SquareRootThreshold`): one window inequality `P_v ≥ 0`
  per scale on the prime side, for the difference tests of one generic width, at height `T` and
  bandwidth `λ = log X / log T`;
- the **aperture face** (Arithmetic Criticality Theory, `ArithmeticCriticalityTheory`; Arithmetic
  Positivity Theory, `ArithmeticPositivityTheory`; the odd Weil-weight route OWU in `RHTower`): the
  ground-energy path `μ(A)` of the restricted Weil form at aperture `A`, which must never cross zero,
  and the gauge and source theories that would prove it.

The finite arithmetic programmes (Bézout–Valuation Incidence, `BezoutValuationIncidence`;
Trans-Horizon Incidence Mechanics, `TransHorizonIncidenceMechanics`; Bi-Scale Uncertainty,
`BiScaleUncertainty`) supply the additive, single-modulus structure of the integers that the three
faces cannot see on their own: Bézout relations, residue classes, pronic Gram matrices, horizon
mechanics, and the two-scale constraint of the integer grid against the hyperbolic weight.

The continuation layer (Arithmetic Continuation and Critical Energy,
`ArithmeticContinuationAndCriticalEnergy`) supplies what no face states on its own: the transport
of a finite critical energy along a parameter — damping, coefficient cutoff or aperture — so that a
certificate at one parameter becomes a certificate at another, with the observation horizon
quantified uniformly throughout.

The admissibility layer (Scale-Signed Incidence Criticality, `ScaleSignedIncidenceCriticality`)
supplies the price list. A mechanism is not the arithmetic it studies but a *reading* of it — a map
from its data to the observables it actually uses — and each reading has an exact resolution limit:
the best bound on the target invariant that any method reading it can prove. The layer computes
those limits, so a route can be priced before it is built, and states the separations a reading must
perform to be admissible at all.

**Why one theory.** Each existing layer stops where the corpus proves it stops. Sieve and bilinear
methods see the additive structure of `ℕ` only after averaging over a family, and below half
damping no sign-blind datum decides the receiver. Multiplicative, spectral and explicit-formula
methods hold verbatim for Beurling systems with off-line zeros. Dirichlet-form and criticality
identities hold for every even positive kernel, and positivity on restricted families is paid by an
archimedean gain that is absent on the RH-complete cone. A closing theorem must at once see both
operations of `ℕ` at a single modulus, carry a sign structure (one negative square, the pole plane,
the signs of the Möbius row), and be resolved at the zero spacing, at square-root precision at every
scale. No existing field has its basic objects built with all three; the nine programmes build
them.

**The mechanisms the shared target needs**, with the programme that owns each:

1. A prime-side inequality with no slack: payment of each anti-diagonal atom `Λ(n) n^{−1/2}` by
   same-side atoms and the variance, on all even profiles, in sign-changing gauges, with a
   Harnack-type propagation across the prime shifts `log 2, log 3, …`
   (`ArithmeticIncidencePositivity` with `ArithmeticCriticalityTheory`).
2. Single-modulus bilinear dispersion on the pronic Gram, through the reciprocity
   `{N/pq} ↔ p̄/q + q̄/p`, for the actual Möbius or prime row; it reduces exactly to the
   single-modulus statistics `Σ_p |Λ_p(c')|/p` of that row (`BezoutValuationIncidence`).
3. A no-crossing law for the ground-energy path, equivalently the absence of a first negative lag
   for `ζ` (`ArithmeticCriticalityTheory`, `ArithmeticPositivityTheory` and OWU on the aperture side;
   `SquareRootThreshold` on the lag side).
4. A definite spectral realization with a prime modification as large as `S(T)`: a Hilbert space
   and a self-adjoint operator whose spectral measure is the critical-zero measure, with
   non-unit-modulus Euler factors (`ArithmeticPositivityTheory` for the source class and the
   realization problem; the operators of the routes HF, CHMD and Connes–Consani–Moscovici in
   `RHTower`). Every certificate of positivity is the critical-zero measure, so this is mechanism 3
   seen from the other side.
5. A sign-reading additive input at a single modulus: below half damping a bound on the receiver
   must read the signs of the coefficients, through first-order data at prime moduli (`k ↦ pk`) or
   odd-degree additive moments (`k ↦ k + v`) (`TransHorizonIncidenceMechanics` with
   `BezoutValuationIncidence`; `BiScaleUncertainty` for the node criticality `log 4` against
   `log 6`).
6. A continuation theorem transporting a finite critical energy from the unconditionally admitted
   end of a parameter range towards the critical end: a horizon-free bound on the negative part of
   one complete signed pairing on each compact subinterval, which is weaker than a bound on the
   corresponding norm and already yields an explicit zero-free strip when it covers only part of
   the range (`ArithmeticContinuationAndCriticalEnergy`).
7. An admissible reading: a mechanism presented as a reading of its own data whose fibres fail to
   realise the maximum of the invariant it claims to bound. On the zero side this forces the
   aperture past the Nyquist aperture of the configuration addressed and forces the *size* of the
   Weil deficit to be estimated rather than its sign; on the prime side it forces `Λ` to be
   separated from each of its single-index perturbations
   (`ScaleSignedIncidenceCriticality`).

**Criteria every contribution to the shared target must meet.**

- *Selectivity.* State what the result gives for `ζ(s−a)ζ(s+a)`, for a Beurling system with an
  off-line zero, and for the Liouville-twisted weight; a statement surviving all three is not
  about RH (test models: `BiScaleUncertainty`).
- *No family average.* One character, modulus one, shift zero. This is an exact floor and not a
  preference: the worst width inside a joint certificate over a family of any cardinality is the
  trivial one, because the extremal datum is already uniform across the family.
- *Square-root precision beyond the diagonal.* Prime sums of length at least the height,
  controlled beyond the mean-value regime: one inequality per window at every scale on the lag
  family, `θ = 2` on the Gram. On the aperture face the same demand is a theorem: a method
  controlling the Weil deficit of a configuration of scale `L` to precision `η` resolves depths
  only down to `√(η/L³)`, so excluding depth `β` costs precision `β²L³`.
- *Every scale, not almost every.* A statement about an exceptional set, a proportion or a typical
  member is infrastructure (the every-height problem: `SquareRootThreshold`). The two monotone
  faces may be verified along an unbounded sequence of apertures or radii, with nothing proved in
  between; the incidence face admits no sampling at all, since every prime power is individually
  necessary.
- *Node criticality.* The mechanism distinguishes `log 4` from `log 6`; sampling-density and
  generic uncertainty arguments are excluded in advance.
- *Signs read.* Below half damping the mechanism uses first-order data at prime moduli or
  odd-degree additive moments; magnitude, two-point and translated-moment data are blind, since the
  parity pairs exist at every damping `ε ≤ 1/2`.
- *Complete expression, no margin, no archimedean subsidy.* Mean, diagonal, mixed terms, Gamma and
  polar charges, endpoints and history are retained; a gain of size `log(1/w)` or `log M` at the
  archimedean place against a bounded prime cost is nonselective by construction. The dividing line
  is growth, not size: a subsidy growing with the frequency of the test is satisfied by the
  all-ones weight and removes the criterion outright, while a subsidy constant or linear in the
  aperture leaves it intact.
- *Units.* Positivity is measured by the aperture `A` or the support through which the inequality
  holds for all profiles; cancellation by the exponent `θ` obtained or the lag `V` beyond which
  `P_v ≥ 0` is proved; localization by the depth `δ(n, R)` excluded below height `T(n, R)` and by
  the visibility lag `V₀(w, η, δ₀)`; damping by the smallest `ε` at which the receiver is bounded;
  admissibility by the pair (class of readings, exact resolution limit). Identities, finite
  classifications and nonselective positivity count as zero in these units.
- *Grading.* A sign criterion with no partial value is incomplete. Every face of the target now has
  a one-parameter family whose endpoint is RH and whose interior is an explicit zero-free strip:
  the graded odd-sector floor and the graded incidence allocation at rate `2σ`, the graded pole
  cross entry at rate `1 + 2α`, and the partial damping continuation above `a₀`. State which member
  of the family a partial result reaches.
- *Calibration.* Reproduce the corresponding theorem over `F_q[T]`, or say why it cannot be done
  (`BiScaleUncertainty`).
- *Pairs.* Every invisibility theorem comes with a visibility witness, every identity with the
  estimate it enables or the sharp boundary it proves, every obstruction with its replacement
  hypothesis proved sufficient.

### This programme's role

This programme owns the **admissibility layer** of the shared target: not a new estimate of the
critical form, but the exact theory of which data can settle it, and what each class of data is
worth.

It is the only programme whose data are *methods* rather than arithmetic objects. Where the others
produce windows, exponents, apertures, lags and dampings, this one produces:

* **floors** — numbers no method of a given class can beat (`resolutionLimit`), and the dual
  **ceilings** below which no such method forces anything (`resolutionFloor`); together they give the
  **resolution interval**, the exact set of values the method leaves open;
* **gates** — necessary separations any mechanism must perform, each a checkable inequality of
  readings on an explicit pair (`theDilationRequirement` on the aperture face,
  `theNodeFaceIsAPrincipalUpSet` on the incidence face);
* **ladders** — resources whose floors decrease to the criterion, so that a route can report
  progress, with the classification of which ladders do this (`apertureResolutionJump`) and which
  are flat (`gainLadderIsTrivial`);
* **recipes** — for each face, the finitely many magnitudes that determine the invariant, in closed
  form and with their conditioning (`depthFromBands_eq`, `difference_ratio_eq`,
  `depth_from_doubling`);
* **transfer** — refinement, joining and factorisation laws, by which a floor proved once applies to
  every mechanism whose reading factors through the same reduction.

In the shared units its own contribution counts as zero: it proves no window, no exponent, no
aperture and no damping. Its unit is the pair `(class of readings, exact limit)`. The recurring
value in that unit is `½`, and it has two independent arithmetic sources — `2` is the first prime
power, and `½` is the deepest an off-line zero can sit — together with one mechanism that explains
why both appear in the same place: at aperture `a` the `ℓ¹` prime cost is `≍ 2e^{a}` while a
depth-`δ` off-line configuration amplifies by `e^{2δa}`, and the two exponents coincide exactly at
`δ = ½`, the depth of the polar pair. A method that cannot separate the prime side from its own
`ℓ¹` worst case is, in this calculus, looking at a depth-`½` configuration.

### How the programme connects to the other programmes

* **Square-Root Threshold** supplies the whole zero side: the configuration data, `configWidth`, the
  off-line lattices and their on-line shadows, the Nyquist law shared by position and depth, the
  isolated-pair and finite-set visibility laws, the lattice ground energy with its exponential
  bounds, and the certificate-radius law of the prime side. This programme converts those
  invisibility theorems into exact limits, adds the units in which the *same* readings are sharp
  (scale, visibility frequency, horizon frequency), and returns the design specification a
  counterexample would have to meet. SRT's graded dictionary — a floor at rate `2σ` is the strip
  `½ + σ` — is the reason a rate reading, and not a sign reading, is the faithful one.
* **Arithmetic Criticality Theory** owns the ground-energy path this programme prices: bounded
  apertures read the scale and never the depth, a margin at a fixed aperture is worthless, a uniform
  gain at all apertures is already RH, and past the Nyquist aperture only the *size* of the deficit
  carries the depth. In the other direction ACT's certified endpoint `μ(3/10) ≥ 1/5000` is the
  initial value of every transport statement, and its criticality theorems say the allowance must be
  added rather than subtracted.
* **Bi-Scale Uncertainty** supplies node criticality and the test models. Here node criticality
  becomes a statement about a whole class of methods — no reading unchanged by finitely many nodes
  resolves node positivity — and acquires a number, `(smallest prime power)⁻¹`. BiScale's exponent
  dictionary supplies the faithful rate readings on the analytic side.
* **Trans-Horizon Incidence Mechanics** supplies the parity pairs, whose barrier is, verbatim,
  failure of resolution for a magnitude reading of a damped weight. That face is owned there; this
  programme contributes the shape of the statement — a reading, a collapse, a witness pair — and the
  fact that no family of such readings, of any cardinality, does better than one of them.
* **Arithmetic Continuation and Critical Energy** is the layer that answers two of the gates
  constructively: the aperture gate, by transporting a certified floor along an unbounded aperture
  sequence without differentiating it, and the sign gate, by replacing a pointwise budget with a
  parameter average that is *equivalent* to the conclusion. Its majorant source is the damping-side
  instance of "a bound below half damping must read signs".
* **Bézout–Valuation Incidence** and **Arithmetic Incidence Positivity** are the consumers: a new
  dispersion estimate, window or ledger bound is admissible only if the reading it uses separates the
  gate pairs, and the gates are stated so that the check is a one-line instantiation. For the
  incidence face the calculus also says how progress must be organised: the condition cannot be
  sampled — every prime power is individually necessary — while node-by-node verification is an
  exactly quantified ladder.
* **RHTower** supplies the germ of the whole calculus: `DeciderBarrier`'s invariant-collision
  lemmas are the two-point cases of the dichotomy and of the floor theorem, and
  `Sieve.CoefficientFreeCap` is the magnitude instance. It also owns the countermodels this
  programme prices but does not build — the shifted pair, the boosted cone, the non-tempered
  weights.

---

## The modules

Ten modules, each the home of one result of the theory.

| module | owns |
| --- | --- |
| `TheResolutionLimitOfAReading` | the calculus: shadows, `Resolves`, `Invisible`, `Refines`, `joinReading`, `resolutionLimit`/`resolutionFloor`, `Certifies`, the resolution interval, the floor theorem. No corpus dependency. |
| `TheApertureCertificateIsBlindInEveryUnit` | the configuration vocabulary and the single blindness mechanism: limit `½` and floor `0` at every aperture, coercivity level, monotone unit and family; the interval is the whole range of the width. |
| `RefutationIsFiniteConfirmationIsNot` | `Refutes`; the node face as a principal up-set; one membership bit refutes; prime-side completeness; asymptotic node readings resolve nothing. |
| `TheSquareRootPrecisionLaw` | the trans-Nyquist deficit, the exact level limit, the square-root law `√(η/L³)`, the adaptive budget `β²L³`, the deficit-rate law and the scale-free faithful rate reading. |
| `TheDepthIsTheCompleteDilationInvariant` | the dilation action, the depth as its complete invariant, and the collapse of a single-aperture certificate without a scale bound. |
| `TheHidingLaws` | what hiding costs: the crystal requirement, exponential mass, the mass–aperture exchange and reach law, free aliasing below `ℓ/2` and its sharpness, the productive seam. |
| `TwoAliasingBandsDetermineTheDepth` | the two-band inversion in closed form and its `√(2η)` conditioning. |
| `ThreeBandsDefeatTheMass` | the three-band inversion with unknown on-line mass, and the aperture-doubling recipe for a single pair. |
| `TheMagnitudePairIsFaithfulWhereTheSignIsBlind` | the two readings on one family: sign limit `½`, magnitude limit exactly the depth, floor `=` limit. |
| `SparseAperturesSufficeAndTheIncidenceFaceDoesNot` | what must be verified: RH from positivity along any unbounded set of apertures or radii; no proper subset of the nodes suffices; the reduction dichotomy. |

The dependency order is the reading order: the calculus, then the blind face, then the refutation
calculus, then the quantitative law, then the dilation requirement it answers, then the hiding laws,
then the three recipes, then the dichotomy and the verification plan.

---

## 1. Why

### 1.1 The diagnosis

The corpus contains hundreds of proved no-gos. Read one by one they are unrelated; read as readings
they are one phenomenon. In each case a method is a function of some observables, two data have the
same observables, and the property to be decided differs on them. The proofs differ; the shape does
not.

Three consequences follow, and they are the reason for a separate programme.

1. **The shape is reusable.** Proving blindness once per method is wasteful: the right theorem is
   over all methods in a class. One statement excludes every density argument about the node set;
   one excludes every statistic of the amplitudes; one excludes every monotone reparametrisation of
   the depth.
2. **Blindness has a number.** "The method cannot decide" is qualitative and therefore unusable in a
   plan. The resolution limit is a real number: the exact best bound the method can certify. A
   programme can then compare methods, and a route can report what it is worth before it is built.
3. **The information is not where it is looked for.** The limits are discontinuous. Every bounded
   aperture has limit `½` while the unbounded certificate has limit `0`
   (`resolutionLimit_width_fullPositivity`), and the bounded stages form a strictly increasing chain
   of data (`apertureResolutionJump`). So the width is not approximated by finite-aperture work: it
   appears only in the limit, or in a magnitude.

### 1.2 Why existing fields do not supply this

Model theory and descriptive set theory study definability, complexity theory studies
resource-bounded decision, and both are about languages and machines, not about analytic invariants.
Harmonic analysis has uncertainty principles, which bound localisation, not resolution of a global
invariant from a restricted observable. What the critical form needs is neither: an *exact* theory of
what a list of arithmetic observables determines, with a numerical unit, instantiated at the actual
arithmetic data of `ζ` — and with the countermodels supplied, not assumed.

### 1.3 Where it points

The intended use is chronological: gates first, construction second. A mechanism is admissible
exactly when its reading passes the gates, and the calculus is arranged so that the check is an
instantiation rather than a new argument. The programme's positive output is of the same kind: when a
floor is identified, the next question is which single ingredient removes it. On the aperture face
the answer is a theorem rather than a conjecture — two aliasing bands, three in the presence of
on-line mass, one aperture doubling for a single pair — and in each case the ingredient is a
*magnitude* where the blind reading used a *sign*.

---

## 2. What: objects and language

### 2.1 Readings and shadows

A **reading** is any map `r : D → O`. Its **shadow** at `d` is `shadow r d = {e | r e = r d}`, the
data a method reading only `r` cannot tell from `d`. Shadows of indistinguishable data coincide, so a
reading partitions `D`, and everything below is about that partition.

`r` **resolves** a property `P` when equal readings force equal verdicts:
`Resolves r P : ∀ d e, e ∈ shadow r d → (P e ↔ P d)`. This is equivalent to the factorisation
`∃ Φ, ∀ d, P d ↔ Φ (r d)` (`resolves_iff_exists_factorization`) — the form in which the corpus states
its barriers, and the reason those barriers are instances of this calculus.

`r` **refutes** `P` at `d` when every datum it cannot distinguish from `d` fails `P` (`Refutes`).
Refutation is inherited by finer readings and implies that the property fails: it is the honest
formalisation of "finite data established the negative answer", and it behaves completely differently
from resolution.

### 2.2 Collapses

A **collapse** is a map `κ : D → D`; it is **invisible** to `r` when `r (κ d) = r d` for all `d`.
The collapses of the critical form are: shifting the pair `ζ ↦ ζ(·−a)ζ(·+a)`; deleting one node from
a node set; the parity flip of a damped weight; truncating the aperture; truncating the height;
modifying a prime weight above `e^{2R}`; inserting a reflected off-line pair above a height. A
collapse is **fatal** when the property fails on its image and **neutral** when the property is
invariant under it — node criticality is exactly the statement that prime-power deletions are fatal
and non-prime-power deletions neutral.

### 2.3 Limits, floors and intervals

For a real invariant `I : D → ℝ`:

* `Certifies I r d β : ∀ e ∈ shadow r d, I e ≤ β` — what "the reading implies the bound" means;
* `resolutionLimit I r d = sSup (I '' shadow r d)` — the **limit**, with
  `certifies_iff_resolutionLimit_le`: the limit is not an estimate of the method's strength, it *is*
  its strength;
* `resolutionFloor`, `CertifiesLower` — the dual theory, with
  `resolutionFloor_eq_neg_resolutionLimit`;
* the **resolution interval** `[resolutionFloor, resolutionLimit]` — the exact set of values the
  method leaves open. A reading is *informative* for `I` at `d` exactly when this interval is proper
  and *pins* `I` exactly when it degenerates.

A reading is **faithful** for `I` when its limit is `I`, equivalently when `I` is maximal on each
shadow.

### 2.4 The order on readings

`Refines r r'` says equality of `r` implies equality of `r'`: a method reading `r` has `r'` at its
disposal. Refinement shrinks shadows, transports resolution and lowers the limit. Joint readings
intersect shadows, so combining data can only lower the limit — and never below the limit of the
intersection, which is where all the no-go content sits.

A proof is rarely one reading; it is a reduction followed by a reading. A reading that **factors**
through `f` inherits `f`'s shadows, so a floor proved for one reduction applies to every mechanism
that factors through it (`resolutionLimit_eq_of_factors_of_max`, `refines_of_comp`); a reading that
is constant is floored at the a priori maximum (`resolutionLimit_eq_of_constant_reading`). A
**family** reading of any cardinality is the join of its members (`familyReading`), and joining
lowers no floor below that of the intersection — which is where all the no-go content sits.

A **policy** is a reading that adapts: it chooses its aperture and its precision as functions of the
datum's scale (`adaptiveReading`, `ScaleMatched`). Policies are the first readings in the calculus
that certify a nontrivial bound, and the price of adaptation is exact (`theDeficitBudgetLaw`).

### 2.5 The two coordinates of a configuration

On the lattice family — an off-line lattice of spacing `2π/L` and depth `δ`, with the parameters
`(L, δ)` free — the field's whole phenomenon is visible. Dilating the ordinates rescales `L` and
leaves `δ` untouched, so dilation acts transitively on the scale and trivially on the depth, and the
depth is a **complete invariant** of the dilation action: `DilationEquiv p q ↔ sdDepth p = sdDepth q`.
Hence a reading is faithful for the depth exactly when its fibres lie inside dilation orbits, and
resolving the depth is a *separation of orbits*, not an estimate.

Every natural reading of the field — apertures, heights, radii, ordinate sets, failure sets — is a
coordinate *along* the orbits. That is the field's dichotomy, and it is about coordinates rather than
boundedness: the exact ordinate set is unbounded data, determines the scale exactly, and still has
the trivial limit `½` for the depth. The **vertical** coordinate is what every reading sees; the
**horizontal** one carries RH.

### 2.6 The units

| unit | definition | vanishes exactly when |
| --- | --- | --- |
| width | `sup \|Re ρ − ½\|` over the configuration (`width`) | all zeros on the line |
| depth | `δ` on the lattice family; the dilation invariant (`sdDepth`) | the configuration is on-line |
| deficit rate | `inf {β ≥ 0 : the deficit is O(e^{2βa})}` (`rateSet`, `sInf_rateSet`) | the configuration is on-line |
| depth resolution | `arcosh(1 + η/(2L))/L` at level `η` and scale `L` (`depthResolution`) | never: it is the limit a level certificate reaches |
| node scale | `sup {1/m : m a prime power, m ∉ 𝒩}` (`nodeScale`) | `𝒩` contains every prime power |
| band ratio | `t₃/(2t₂)` on a lattice, `(t₄−t₃)/(t₃−t₂)` with mass (`ratio_eq_cosh`, `difference_ratio_eq`) | at the critical value `1`, resp. `2` |

The width and the depth **vanish together** on the lattice family and are the two ends of the same
scale; the deficit rate is the only one of them that is constant on dilation orbits. A result in one
unit does not transfer to another, and a mechanism must be priced in the unit built from the data it
actually reads: a sign in the width unit, where every bounded reading is vacuous; a magnitude in the
band-ratio unit, where the depth is an explicit elementary function of what was measured.

### 2.7 The faces

| face | data `D` | invariant / property | reading |
| --- | --- | --- | --- |
| aperture | tempered configurations (`TemperedZeroConfig`) | width | `aperturePositivity a`, `apertureGain a η`, `familyPositivity`, `fullPositivity` |
| trans-Nyquist | lattice data `(L, δ)` (`ScaleDepthDatum`, `DepthDatum`) | depth | `levelReading a η`, the rate reading, `bandPairReading` |
| mixed | lattice plus on-line mass and dilution | depth | `dilutedReading`, the three band deficits |
| node incidence | node sets `𝒩 ⊆ ℕ` | zero–pole blind positivity | `AsymptoticReading`; `membershipReading m` |
| prime window | prime weights `lam : ℕ → ℝ` | full Weil cone | `radiusReading R`, `weightAperturePositivity a` |

The faces owned elsewhere — temperedness (the shifted pair), parity (damped weights) — are priced by
the same calculus, with their countermodels in `RHTower` and `TransHorizonIncidenceMechanics`.

---

## 3. How: the mechanisms

### 3.1 The dichotomy and the floor theorem

Two theorems carry every negative statement in the field.

*The collapse–resolution dichotomy.* If a collapse `κ` is invisible to `r` and separates the
property — `P d` holds and `P (κ d)` fails — then `r` does not resolve `P`
(`not_resolves_of_separating_collapse`), and conversely a resolving reading forces the property to
fail on the whole orbit of every collapse it misses (`forall_not_of_resolves_of_invisible`). In the
contrapositive this is the usable form: *if* a mechanism resolves the criterion, *then* the
countermodel it cannot see must already fail it — which for two faces means `¬ RH`
(`not_riemannHypothesis_of_resolves_of_invisible`).

*The floor theorem.* If the invariant has a global maximum attained by some datum in the shadow, the
resolution limit is exactly that maximum (`resolutionLimit_eq_of_mem_shadow_of_max`). This is why
the numbers in this field are exact rather than approximate: one witness of maximal invariant inside
the shadow fixes the limit, and the two inequalities that prove it are the same two every time.

### 3.2 The aperture face: one witness, every unit

The aperture face needs exactly one construction. For every aperture there is a configuration of
maximal width `½` that satisfies the certificate for free — an off-line lattice whose spacing exceeds
twice the aperture, so that no test of that aperture reaches a pair of its zeros
(`exists_width_eq_half_aperturePositivity`). It lies in the shadow of every datum satisfying the
certificate, so by the floor theorem

`resolutionLimit width (aperturePositivity a) Z = ½`   (`resolutionLimit_width_aperturePositivity`),

and the certificate certifies nothing beyond the a priori bound
(`certifies_width_aperturePositivity_iff`). The same witness, with the gain built in, gives the same
number for a coercive certificate at any level (`resolutionLimit_width_apertureGain`,
`gainLadderIsTrivial`), for a family of apertures of any cardinality
(`resolutionLimit_width_familyPositivity`), for a family of configurations
(`resolutionLimit_familyWidth_familyAperture`), and — composed with any monotone reparametrisation
`g` of the depth — for the unit `g ∘ width` (`resolutionLimit_comp_width_apertureGain`,
`theFloorIsUnitIndependent`). The floor is not an artefact of the unit.

At the lower end the on-line lattice lies in every aperture shadow
(`onLineLattice_mem_shadow_aperturePositivity`), so the dual limit is `0`
(`resolutionFloor_width_aperturePositivity`) and the resolution interval is the entire range of the
width (`resolutionInterval_width_aperturePositivity`, `range_width`): a bounded-aperture certificate
can neither prove nor disprove the critical line. Only the unbounded certificate has limit `0`
(`resolutionLimit_width_fullPositivity`), and the bounded stages form a strictly increasing chain of
data (`apertureResolutionJump`) — strictly more information at every step, the same trivial bound at
every step.

### 3.3 The two coordinates: why one aperture cannot see the depth

On the lattice family the scale and the depth are independent coordinates, and the dilation action
moves the first while fixing the second, so the depth is its complete invariant
(`dilationEquiv_iff_sdDepth_eq`). A reading resolves the depth exactly when its fibres lie inside
dilation orbits: resolving is *separating orbits*, not estimating.

With both coordinates free, a level certificate at a single aperture separates nothing. The dense end
of the family — scale at least twice the aperture — carries the maximal depth and satisfies the
certificate for free (`scaleDepthReading_of_dense`), so it sits in every shadow and the limit returns
to `½` (`resolutionLimit_sdDepth_scaleDepthReading`). A scale bound is not a convenience in the
trans-Nyquist theorems; without it there is nothing to prove (`theDilationRequirement`).

### 3.4 Past the Nyquist aperture: the deficit, its precision, its rate

Above the Nyquist aperture of a configuration the Weil form acquires a deficit, and its size is the
field's quantitative content:

`weilFloorThreshold L δ = 2L(cosh(δL) − 1)`

(`weilFloorAtLevel_offLineLattice_iff_cosh`), strictly monotone and injective in the depth
(`weilFloorThreshold_strictMono`, `weilFloorThreshold_injOn`) — so at a *known* scale the level
certificate does separate depths (`exists_level_separating_depths`), and its limit is exact:

`resolutionLimit depth (levelReading a η) = min ½ (arcosh(1 + η/(2L))/L)`
(`resolutionLimit_depth_levelReading`).

The threshold is quadratic in the depth, not linear (`cube_mul_sq_le_weilFloorThreshold`), which is
the whole cost structure of the face. Inverting it gives the **square-root precision law**: a method
controlling the deficit to precision `η` resolves depths only down to `√(η/L³)`
(`depthResolution_le_sqrt`, `resolutionLimit_depth_levelReading_le_sqrt`), so excluding depth `β`
costs precision `β²L³` — the budget of `theDeficitBudgetLaw`, which an adaptive policy must meet and
cannot evade (`certifies_of_budget`, `not_certifies_of_budget_violation`).

Along the aperture axis the same quadratic law reads as a growth rate. The deficit grows like
`e^{2δa}`: every rate above the depth is admissible and no nonnegative rate below it is
(`deficitRateBelow_of_lt`, `not_deficitRateBelow_of_lt`, `theDepthIsHalfTheDeficitGrowthRate`), so

`sInf (rateSet p) = sdDepth p`   (`sInf_rateSet`).

That infimum is the depth, hence constant on dilation orbits, and equal infima force equal depths
(`sdDepth_eq_of_rateSet_eq`): the rate is the field's faithful, scale-free reading
(`theRateReadingIsTheAnswer`). A uniform deficit bound, by contrast, is passed by every
configuration at every aperture (`uniformDeficit_onLineLattice`, `theGateIsPassedByNonGrowth`):
uniformity is not strength, only a rate is.

### 3.5 How a configuration hides: crystal, mass, dilution

The witnesses above are infinite crystals, and that is forced.

* **A finite off-line set cannot hold the floor.** It is refuted at an explicit aperture computed
  from the set (`refutes_aperturePositivity_of_finiteOffLine`,
  `not_fullPositivity_of_finiteOffLine`, `theFloorsNeedInfinitelyManyOffLineZeros`).
* **A single pair in a background is bounded in depth.** An isolated pair hidden inside local
  on-line mass `M` over height `v` satisfies `δ ≤ arsinh(M/|Q| + 1)/v`
  (`depth_le_of_aperturePositivity_of_mass`, `theFloorsRequireACrystal`), and hiding it at aperture
  `a` requires mass growing like `e^{2δa}` (`depth_le_log_of_positive_of_mass`,
  `theFloorsNeedExponentialMass`).
* **Mass buys aperture only logarithmically.** For a diluted lattice of spacing `ℓ` inside on-line
  mass `L`, invisibility at aperture `a` costs `ℓ e^{δ(2a − ℓ)} ≤ 2L + 2a + ℓ`
  (`mass_ge_of_dilutedLattice_positive`), so the reach of a structured counterexample is
  `a ≤ log((3L + ℓ)/ℓ)/(2δ) + ℓ/2` (`reach_upper`, `theReachLaw`) against a free part linear in `ℓ`
  (`reach_lower`).
* **Aliasing is free below Nyquist, and exactly there.** A sub-lattice of spacing `ℓ` is invisible to
  every aperture below `ℓ/2` at no cost whatever the background
  (`dilutedLattice_hides_below_own_nyquist`), and the free regime ends exactly at `ℓ/2`: at and above
  it the ground energy is negative (`latticeFloor_neg_of_two_le`, `theFreeRegimeIsSharp`).

The aperture–mass pair is the one **productive seam** of the field: the two readings together bound
the depth where neither does alone (`certifies_depth_dilutedReading`, `theProductiveSeam`), and a
mixed configuration therefore has two regimes rather than one
(`theTwoRegimesOfAMixedConfiguration`).

### 3.6 The positive half: finitely many magnitudes determine the depth

The floors are statements about *signs*. The magnitudes of the same form determine everything, in
closed form, with no scale input.

*Two bands.* The ground energy of an off-line lattice at aliasing index `n` is
`−L·latticeFloor L δ n`; at the first two nontrivial indices, with `x = δL` and `c = cosh x`,
`t₂ = 2L(c − 1)` and `t₃ = 4L(c² − 1)` (`groundEnergy_index_two`, `groundEnergy_index_three`). The
ratio strips the scale, `t₃/(2t₂) − 1 = c` (`ratio_eq_cosh`), and the remaining combination restores
it, `(t₃ − 4t₂)/t₂² = 1/L`, so

`δ = arcosh(t₃/(2t₂) − 1) · (t₃ − 4t₂)/t₂²`   (`depthFromBands_eq`),

and the pair determines the depth uniquely (`depth_determined_by_two_bands`,
`theDepthIsComputableFromTwoBands`). The obstruction of §3.3 is an artefact of using *one* aperture.

*Conditioning.* Exactness is not sufficiency. The scale-free datum is the ratio, whose critical value
is `1`, and `1 + y²/2 ≤ cosh y` turns an excess `η` into `δL ≤ √(2η)`
(`depth_le_sqrt_of_ratio_le`, `theTwoBandCertification`): the precision needed to certify depth `β`
is again of order `β²`. The square-root law is a property of the face, not of the reading.

*Three bands against the mass.* On-line mass shifts every measured deficit by one constant, so two
bands are underdetermined. Consecutive differences cancel the mass and their ratio cancels the
dilution as well: `(t₄ − t₃)/(t₃ − t₂) = 2cosh(δℓ)` (`difference_ratio_eq`), whence the depth with
the mass unknown (`depth_determined_by_three_bands`, `threeBandsDefeatTheMass`). Each unknown of the
configuration costs exactly one aliasing index — and against §3.5, where mass buys an exponential
amount of hiding, mass buys nothing at all against one extra band.

*One doubling for a pair.* A single off-line pair has no bands; its aperture axis is continuous. Its
window moment `M(a) = S(a) + a = sinh(2δa)/(2δ)` satisfies `M(2a)/M(a) = 2cosh(2δa)`
(`pairMoment_doubling`), hence `δ = arcosh(M(2a)/(2M(a)))/(2a)` (`depth_from_doubling`), and the
on-line mass cancels between the two apertures (`gain_difference_eq`,
`theApertureDoublingPrescription`).

### 3.7 Sign against magnitude, on one family

Put the two readings on the same data. The level certificate's limit for the depth is the trivial
`½`; the pair of ground energies at the first two aliasing indices has limit exactly the depth, and
its floor equals its limit, so the reading is faithful
(`resolutionLimit_sdDepth_bandPairReading`, `resolutionFloor_eq_resolutionLimit_bandPairReading`,
`theDichotomyOfSignAndMagnitude`). The blindness theorems are therefore not about the Weil form
being a weak object; they are about *which functional of it is read*. Its sign at one aperture
carries no depth information in any unit; two of its magnitudes carry all of it.

### 3.8 What must be verified

The two directions and the three faces demand different amounts of work, and the calculus says
exactly how much.

*Confirmation, scale faces: a sparse set suffices.* Aperture positivity is monotone, so positivity
along **any** unbounded set of apertures already gives the unconditional certificate and hence RH
(`fullPositivity_of_unbounded_apertures`, `riemannHypothesis_of_unbounded_apertures`), with nothing
proved in between, and with or without a fixed deficit level
(`riemannHypothesis_of_unbounded_apertures_gain`, `theReducedRequirement`). The prime face reduces
the same way, along radii (`weilPositiveFull_of_unbounded_radii`,
`riemannHypothesis_of_unbounded_radii`).

*Confirmation, incidence face: no sampling at all.* Omitting a single prime power destroys zero-pole
positivity (`not_zeroPoleBlindPositiveOn_deleteNode`, `not_zeroPoleBlindPositiveOn_of_notMem`), the
prime powers are the least positive node set (`isLeast_zeroPoleBlindPositiveOn`), and the face is a
principal up-set (`theNodeFaceIsAPrincipalUpSet`). No cofinal subset, no density-one subset, no
subset missing one element suffices (`theReductionDichotomy`). A reading unchanged by finitely many
nodes resolves nothing (`not_resolves_of_asymptoticReading`,
`resolutionLimit_nodeScale_asymptoticReading`).

*Refutation: finite, and complete.* A reading **refutes** when nothing it admits satisfies the
property (`Refutes`), and refutation passes to finer readings (`Refutes.of_refines`). On the prime
side the calculus is exactly complete: a certificate of radius beyond a failure aperture refutes the
cone (`refutes_radiusReading`), and RH holds precisely when no bounded-radius certificate refutes
membership of the von Mangoldt weight in the full Weil cone
(`riemannHypothesis_iff_no_radiusReading_refutes`). On the node face a single membership bit refutes
(`refutes_membershipReading_of_notMem`, `zeroPoleBlindPositiveOn_iff_no_membership_refutes`), and the
asymmetry between the two directions is a theorem (`theNodeFaceAsymmetry`). A mechanism that fails is
told so by a finite computation; a mechanism that succeeds must succeed everywhere at once.

---

## 4. Traps

* **A reading is not a method's conclusion, it is its input.** Floors apply to what the method
  *reads*, not to what it concludes; a method that reads the full datum has limit `I(d)` and proves
  everything. Every floor statement must name the reading precisely, and the honest statement of a
  no-go is "no method reading *this* can do better than *that*".
* **Name the unit, and price the mechanism in its own.** A certificate is priced in the width unit,
  where every bounded reading is vacuous; a deficit estimate in the depth unit; an asymptotic claim
  in the rate unit, the only scale-free one; a measurement in the band-ratio unit, where the depth is
  an explicit function of what was measured. A result in one unit does not transfer to another.
* **Boundedness is not the explanation.** The dichotomy is about coordinates: unbounded vertical data
  — the exact ordinate set — determines the scale exactly and still has the trivial limit for the
  depth. What is needed is a reading coupling the two coordinates, or one constant on dilation orbits.
* **Strengthening a blind reading does not help.** More apertures, a larger coercivity gap, a
  different depth unit, a weaker target, a family of any cardinality: all keep the trivial limit.
  Only three things move it — crossing the Nyquist aperture, reading a magnitude instead of a sign,
  and adding data of a third kind (mass, dilution).
* **A faithful reading is not a proof.** Faithfulness of the unbounded certificate, of the rate
  reading or of the band pair says the data determine the invariant; it does not produce the
  measurement. A recipe says which numbers decide the question, not that they are within reach.
* **The floors are statements about crystals.** Every witness carries infinitely many off-line zeros,
  by necessity: a finite off-line set is refuted at an explicit aperture, and a single pair in an
  on-line background is bounded in depth logarithmically in the local mass.
* **RH on the positive side.** Two faces (node positivity, criticality of the pair) hold at the base
  datum only under RH, so their gates are stated as "resolving reading ⇒ ¬RH", or with RH as an
  explicit hypothesis. That is the honest form; "no method can decide" would be a stronger claim than
  is proved.
* **`Prop`-valued readings need `propext`.** A positivity certificate is a `Prop`; two data share the
  reading when the two `Prop`s are *equal*, obtained from `iff_of_true` and `propext`. Writing `Iff`
  where `Eq` is needed is the commonest friction in these files.
* **Multiplicities off the carrier are noise.** `Zeta23.ZeroConfig.mult` is unconstrained off the
  carrier, so a reading of the divisor must restrict itself to the carrier, or it separates data for
  a reason that is not mathematics.
* **Bounded, not finite, is the operative hypothesis.** The aperture-family theorems assume the
  apertures are bounded, not finitely many: an infinite family of bounded apertures is just as blind,
  and that is the content.
* **A loss is harmless or fatal by its growth, not its size.** A deficit allowance constant or
  linear in the aperture leaves the criterion intact (`theGateIsPassedByNonGrowth`); one growing with
  the frequency of the test is satisfied by a weight of maximal defect and removes the criterion
  rather than relaxing it.
* **The faces do not all fit in one environment.** The corpus declares `RHTower.dilationAverage`
  twice (in `RHTower.SoninDilationAverage` and in
  `RHTower.FermiNymanHaarApproximationEquivalence`), so the import closures of
  `SquareRootThreshold` and of `TransHorizonIncidenceMechanics` cannot be loaded together. Any
  statement spanning the zero side and the parity side must therefore be split across modules; it is
  an import-level fact about the corpus, not a mathematical obstruction.

---

## 5. The frontier

Open, in this programme's own unit (a class of readings and its exact limit):

1. **The exact floor of the Gram reading.** For the cross-scale dispersion of
   `BezoutValuationIncidence` the relevant reading is the pronic Gram at one modulus. Its limit in the
   exponent unit `θ` should be exactly `2`; the witness would be the coherent prime block of the
   Type-II no-go. This is the one consumer face with no number yet.
2. **The band recipe for `ζ`.** The recipes of §3.6 read the depth of a lattice or of a pair from
   finitely many ground energies. For `ζ` the corresponding magnitudes are values of the Weil
   functional at two apertures, i.e. prime sums with the archimedean and polar terms retained. Is
   there a two-aperture ratio of the `ζ` functional whose critical value is attained exactly on the
   line, and is a bound on it reachable from the corpus's unconditional inputs? This is the one
   question that would carry the positive half of the field from the model families to the object.
3. **A fatality classification for the parity collapses.** The node collapses are classified exactly
   — the prime powers (`fatal_deleteNode_iff_isPrimePow`) — which turns that face into a principal
   up-set. The analogous question for the parity face owned by
   `TransHorizonIncidenceMechanics`, which involutions of a damped weight are fatal for the
   receiver, is open, and would turn its barrier into a sharp law.
4. **The rate reading for `ζ`.** The faithful reading of the depth is the exponential rate of the
   deficit in the aperture. For the configuration of `ζ` that rate is the zero width, so an estimate
   of it is the target of the whole corpus; what belongs here is the admissibility question: which
   classes of readings determine the *rate* rather than any single value, and what the floor of a
   rate-reading class is when the rate is estimated only along a sparse set of apertures.
5. **The design specification of a counterexample.** The reach law says the free part of the hiding
   is linear in the dilution `ℓ` and the bought part only logarithmic in the mass. What is the
   largest reach of a configuration subject to the arithmetic constraints the explicit formula
   imposes — the polar term, the trivial zeros, the functional equation — and is the sub-lattice
   structure the free regime demands compatible with them at all? A negative answer would be a
   conditional exclusion of structured counterexamples; a positive one names the configuration to
   exclude by other means.
6. **Policies for a configuration of growing density.** The budget law says a policy's precision must
   shrink like the cube of the scale it addresses, and `ζ`'s zero density grows with the height. Which
   schedules of aperture and precision are realisable from the corpus's unconditional inputs, and what
   is the floor of the class of policies with a prescribed growth of aperture?
7. **A numerical unit for the incidence ledger.** The node face is quantitative through the
   membership bits and the node scale. The ledger of `ArithmeticIncidencePositivity` is graded by the
   width on the analytic side; its admissibility unit — what class of readings of the ledger's terms
   can certify a rate — is not computed.

### Research topics toward the shared target

* Price every proposed mechanism before it is built: state its reading, instantiate the gates, and
  report the pair `(class of readings, exact limit)`. A route whose reading factors through a
  bounded aperture has limit `½` by one factorisation and needs no separate audit.
* Supply the third kind of data where a floor is a statement about missing information rather than
  missing strength: local on-line mass and dilution for the aperture face (the productive seam), the
  measured band energies for the depth, individual membership for the node face.
* Trade the resources explicitly in a plan: aperture against precision through the budget `β²L³`,
  and the number of measured bands against the number of unknown parameters of the configuration —
  one index per unknown, by §3.6.
* Classify the readings that determine a *rate*: the deficit growth rate on the aperture face, the
  lag rate on the lag face, the damping threshold on the receiver face. All three are the zero width,
  and all three are tail invariants, hence blind to every bounded parameter range — a floor theorem
  for rate readings would unify the three gates into one.

---

## 6. Working in the theory

* State the reading first, the collapse second, the witness pair third. A statement without all three
  is not in the theory.
* Prefer a limit to a blindness statement, and an interval to a limit: the interval is the usable
  form, and the proof is usually the same two inequalities.
* Instantiate the general theorems rather than reproving the shape. The floor theorem and its
  factorisation and constancy corollaries, `not_resolves_of_pair`,
  `forall_not_of_resolves_of_invisible`, `resolves_iff_exists_factorization`, `Resolves.of_refines`,
  `resolutionLimit_le_of_refines` and the three `Invisible` closure lemmas cover every instance so
  far.
* Take the countermodels from the owning programme. This programme does not build arithmetic objects;
  it imports the configurations of `SquareRootThreshold`, the node sets of `BiScaleUncertainty`, the
  weights of `TransHorizonIncidenceMechanics` and the pair of `RHTower`, and adds exactly the
  calculus.
* Report every result as a pair `(class of readings, exact limit)`, say which gate it closes, and say
  in which unit the number lives.
* Distinguish the two directions. A result about refutation belongs on the prime or node face,
  where finite data are complete; a result about confirmation must name the unbounded resource it
  uses, or the finitely many magnitudes it measures.
* Prefer a magnitude to a sign. A sign at a bounded parameter is vacuous by §3.2; a ratio of two
  magnitudes is faithful by §3.7. When a route reports an inequality, ask which ratio it would need
  instead.
