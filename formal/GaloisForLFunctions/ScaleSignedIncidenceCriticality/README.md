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
part that converts the corpus's 594 individual no-gos into one calculus with a numerical unit, and
its wall gates from a methodological checklist into a theorem (`theWallGates`).

---

## The shared target: the sign of the critical arithmetic form

Eight programmes of this corpus work on one object. The Riemann Hypothesis is the nonnegativity of
one critical arithmetic form, and the form can be read in three equivalent faces:

- the **incidence face** (Arithmetic Incidence Positivity, `ArithmeticIncidencePositivity`):
  conductance by conductance, on pairs of points `(x, y)` of the logarithmic line, with the
  arithmetic edges indexed by divisibility and by products, and the pole as the only positive source
  on crossing pairs;
- the **lag face** (Square-Root Threshold, `SquareRootThreshold`): one window inequality `P_v ≥ 0`
  per scale on the prime side, for the difference tests of one generic width, at height `T` and
  bandwidth `λ = log X / log T`;
- the **aperture face** (Arithmetic Criticality Theory, `ArithmeticCriticalityTheory`; Arithmetic
  Positivity Theory, `ArithmeticPositivityTheory`; the odd Weil-weight route OWU in `RHTower`): the
  ground-energy path `μ(A)` of the restricted Weil form at aperture `A`, which must never cross
  zero, and the gauge and source theories that would prove it.

The finite arithmetic programmes (Bézout–Valuation Incidence, `BezoutValuationIncidence`;
Trans-Horizon Incidence Mechanics, `TransHorizonIncidenceMechanics`; Bi-Scale Uncertainty,
`BiScaleUncertainty`) supply the additive, single-modulus structure of the integers that the three
faces cannot see on their own: Bézout relations, residue classes, pronic Gram matrices, horizon
mechanics, and the two-scale constraint of the integer grid against the hyperbolic weight.

**Why one theory.** Each existing layer stops where the corpus proves it stops. Sieve and bilinear
methods see the additive structure of `ℕ` only after averaging over a family, and below half damping
no sign-blind datum decides the receiver. Multiplicative, spectral and explicit-formula methods hold
verbatim for Beurling systems with off-line zeros. Dirichlet-form and criticality identities hold for
every even positive kernel, and positivity on restricted families is paid by an archimedean gain that
is absent on the RH-complete cone. A closing theorem must at once see both operations of `ℕ` at a
single modulus, carry a sign structure, and be resolved at the zero spacing, at square-root precision
at every scale.

**Criteria every contribution to the shared target must meet** (selectivity against
`ζ(s−a)ζ(s+a)`, Beurling systems and the Liouville twist; no family average; square-root precision
beyond the diagonal; every scale, not almost every; node criticality `log 4` against `log 6`; signs
read below half damping; complete expression with no archimedean subsidy; units; calibration over
`F_q[T]`; pairs) are stated in full in the sibling READMEs
(`ArithmeticIncidencePositivity/README.md`, `BezoutValuationIncidence/README.md`).

### This programme's role

This programme owns the **admissibility layer** of the shared target: not a new estimate of the
critical form, but the exact theory of which data can settle it.

It is the only programme whose data are *methods* rather than arithmetic objects. Where the other
seven produce windows, exponents, apertures and lags, this one produces:

* **floors** — numbers no method of a given class can beat (`resolutionLimit`, exactly `½` for the
  width at every bounded aperture and at every bounded height; exactly `½` for the damping of an
  amplitude-reading receiver criterion);
* **gates** — necessary separations any mechanism must perform, each a checkable inequality of
  readings on an explicit pair (`theWallGates`, `parityWallGate`);
* **transfer** — once a reading is faithful for one unit, it certifies every unit that unit
  dominates (`certifies_of_faithful_of_dominated`), which is how the route dictionary of
  `SquareRootThreshold` becomes usable as a tool rather than a table.

In the shared units its own contribution counts as zero: it proves no window, no exponent and no
aperture. Its unit is the *floor*: the pair `(class of readings, exact limit)`. Its current entries
are `(bounded aperture, ½)`, `(bounded height, ½)`, `(amplitudes, ½ damping)`,
`(asymptotic node readings, vacuous)`, `(structural flags, vacuous)`.

### How the programme connects to the other programmes

* **Square-Root Threshold** supplies the whole aperture and height face: the configuration data,
  `configWidth`, the off-line lattice and the on-line shadow
  (`OnLineShadowIndistinguishability`, `TheZeroWidthIsAnUnboundedApertureProperty`,
  `PositionAndDepthShareOneNyquistAperture`, `IsolatedOffLinePairVisibilityLaw`). The present
  programme converts those invisibility theorems into exact limits and adds the ladder statement:
  the aperture readings refine one another *strictly* while every stage keeps the trivial limit
  (`apertureLadder`). On the prime side it supplies the radius mimics of
  `CertificateRadiusReadsAFinitePrimeWindow`, which become the prime-window gate here.
* **Bi-Scale Uncertainty** supplies node criticality (`PrimePowerZeroPoleNodeCriticality`). Here it
  becomes a statement about a whole class of methods: no reading unchanged by finitely many nodes
  resolves node positivity unless RH fails (`not_resolves_of_asymptoticReading`).
* **Trans-Horizon Incidence Mechanics** supplies the parity pairs (`ParityPairAtHalfDamping`,
  `RealCharacterParityPairsAndTheParityBarrier`). Its `parity_barrier` is, verbatim, failure of
  resolution for the amplitude reading (`resolves_iff_exists_factorization`); the programme adds the
  floor `½` in the damping unit and the closure statement that no amplitude-derived family of any
  cardinality does better (`not_resolves_amplitudeDerivedFamily`).
* **RHTower** supplies the temperedness countermodel (`NonTemperedShiftedZetaPairCountermodel`) and
  the germ of the whole calculus: `RHTower.DeciderBarrier`'s `decider_blind_of_invariant_collision`
  and `le_bound_of_invariant_collision` are the two-point cases of `not_resolves_of_pair` and of
  `le_resolutionLimit_of_reading_eq`; `RHTower.Sieve.CoefficientFreeCap`'s
  `max_le_of_modulusOnly_bound` is the magnitude instance.
* **Bézout–Valuation Incidence** and **Arithmetic Incidence Positivity** are the consumers: a new
  dispersion estimate or a new window is admissible only if the reading it uses separates the
  gate pairs. The gates are stated so that this check is a one-line instantiation.

---

## 1. Why

### 1.1 The diagnosis

The corpus contains 594 proved no-gos. Read one by one they are unrelated; read as readings they are
one phenomenon. In each case a method is a function of some observables, two data have the same
observables, and the property to be decided differs on them. The proofs differ; the shape does not.

Three consequences follow, and they are the reason for a separate programme.

1. **The shape is reusable.** Proving blindness once per method is wasteful: the right theorem is
   over all methods in a class. `not_resolves_of_asymptoticReading` excludes every density argument
   about the node set at once; `not_resolves_amplitudeDerivedFamily` excludes every statistic of the
   amplitudes at once.
2. **Blindness has a number.** "The method cannot decide" is qualitative and therefore unusable in a
   plan. The resolution limit is a real number: the exact best bound the method can certify. A
   programme can then compare methods, and a route can report what it is worth before it is built.
3. **The information is not where it is looked for.** The limits are discontinuous. Every bounded
   aperture has limit `½`, the unbounded aperture has limit `0`; and the finite stages form a
   *strictly increasing* chain of data (`apertureLadder`). So the width is not approximated by
   finite-aperture work: it appears only in the limit. The same with height: every finite height
   has limit `½`.

### 1.2 Why existing fields do not supply this

Model theory and descriptive set theory study definability, complexity theory studies resource-bounded
decision, and both are about languages and machines, not about analytic invariants. Harmonic analysis
has uncertainty principles, which bound localisation, not resolution of a global invariant from a
restricted observable. What the critical form needs is neither: it is an *exact* theory of what a
list of arithmetic observables determines, with a numerical unit, instantiated at the actual
arithmetic data of `ζ` — and with the countermodels supplied, not assumed.

### 1.3 Where it points

The field's programme (argon.md, §2.9) is six topics on the frontier of the corpus. The
admissibility core here is their common precondition: each topic proposes a mechanism, and a
mechanism is admissible exactly when its reading passes the gates. The intended use is
therefore chronological — gates first, construction second.

---

## 2. What: objects and language

### 2.1 Readings and shadows

A **reading** is any map `r : D → O`. Its **shadow** at `d` is `shadow r d = {e | r e = r d}`, the
data a method reading only `r` cannot tell from `d`. Shadows of indistinguishable data coincide
(`shadow_eq_of_mem`), so a reading partitions `D`, and everything below is about that partition.

`r` **resolves** a property `P` when equal readings force equal verdicts:
`Resolves r P : ∀ d e, e ∈ shadow r d → (P e ↔ P d)`. This is equivalent to the factorisation
`∃ Φ, ∀ d, P d ↔ Φ (r d)` (`resolves_iff_exists_factorization`) — the form in which the corpus
states its barriers, and the reason those barriers are instances of this calculus.

### 2.2 Collapses

A **collapse** is a map `κ : D → D`; it is **invisible** to `r` when `r (κ d) = r d` for all `d`
(`Invisible`). The collapses of the critical form are: shifting the pair `ζ ↦ ζ(·−a)ζ(·+a)`;
deleting one node from a node set (`deleteNode`); the parity flip of a damped weight; truncating the
aperture; truncating the height; modifying a prime weight above `e^{2R}`. A collapse is **fatal** when the property fails on its image, and
**neutral** when the property is invariant under it — node criticality is exactly the statement that
prime-power deletions are fatal and non-prime-power deletions neutral
(`not_zeroPoleBlindPositiveOn_deleteNode`, `invisible_zeroPoleBlindPositiveOn_deleteNode`,
`fatal_deleteNode_iff_isPrimePow`).

### 2.3 The resolution limit

For a real invariant `I : D → ℝ`:

* `Certifies I r d β : ∀ e ∈ shadow r d, I e ≤ β` — what "the reading implies the bound" means;
* `resolutionLimit I r d = sSup (I '' shadow r d)` — the **limit**;
* `certifies_iff_resolutionLimit_le`: `Certifies I r d β ↔ resolutionLimit I r d ≤ β`.

So the limit is not an estimate of the method's strength; it *is* its strength. Dually
`resolutionFloor` and `CertifiesLower` handle lower bounds, and the two theories are one
(`resolutionFloor_eq_neg_resolutionLimit`).

### 2.4 The order on readings

`Refines r r'` says equality of `r` implies equality of `r'`: a method reading `r` has `r'` at its
disposal. Refinement shrinks shadows (`shadow_subset_of_refines`), transports resolution
(`Resolves.of_refines`) and lowers the limit (`resolutionLimit_le_of_refines`). Joint readings
intersect shadows (`shadow_joinReading`, `shadow_familyReading`), so combining data can only lower
the limit (`resolutionLimit_joinReading_le`) — and never below the limit of the intersection, which
is where all the no-go content sits.

A reading is **faithful** for `I` when its limit is `I` (`Faithful`), equivalently when `I` is
maximal on each shadow (`faithful_iff`).

### 2.5 The data of the six faces

| face | data `D` | invariant / property | reading |
| --- | --- | --- | --- |
| temperedness | shifts `a : ℝ` of `ζ(s−a)ζ(s+a)` | zeros of the pair on the line (`PairZerosOnLine`) | `structuralFlags` |
| node incidence | node sets `𝒩 ⊆ ℕ` | `BiScaleUncertainty.ZeroPoleBlindPositiveOn` | any `AsymptoticReading` |
| parity | weights `c : ℕ → ℝ`, damped class | receiver bounded (`ReceiverBoundedAt`, `ReceiverBounded`) | `amplitudeReading` |
| aperture | tempered configurations (`TemperedZeroConfig`) | the width (`width`) | `aperturePositivity a`, `familyPositivity` |
| height | tempered configurations | the width | `heightReading T` |
| prime window | prime weights `lam : ℕ → ℝ` | `RHTower.WeilPositiveFull` (the full Weil cone) | `radiusReading R` |

---

## 3. How: the mechanisms

### 3.1 The dichotomy

`not_resolves_of_separating_collapse`: an invisible collapse that separates the property forbids
resolution. `forall_not_of_resolves_of_invisible`: if the collapse is *uniformly* fatal, a resolving
reading forces the property to fail everywhere — which is how a blindness statement becomes an
unconditional theorem about RH. `not_resolves_of_pair` is the witness-pair form, and is all that an
instance with a hand-built countermodel needs.

### 3.2 Floors

`iterate_le_resolutionLimit` and `le_of_certifies_of_invisible`: the invariant at the collapsed
datum, and at every iterate, floors the limit. This is the quantitative half of the dichotomy and
the source of every number in the programme.

### 3.3 The algebra of blindness

`Invisible.comp`, `Invisible.joinReading`, `Invisible.familyReading`: blindness is closed under
post-processing, pairing and families of arbitrary cardinality. The practical consequence, used
three times below, is that a method may read as much blind data as it likes, in any combination, and
gains nothing: only a reading that *moves the collapse* can help.

### 3.4 The aperture face: limit `½` at every bounded aperture

`resolutionLimit_width_aperturePositivity`: for every `a > 0`, a configuration certified
Weil-positive at aperture `a` shares that certificate with configurations of every width up to `½`
(the off-line lattice of ordinate spacing `π/a`, which below its Nyquist aperture *is* a positive
on-line configuration), so the limit of the width is exactly `½` and
`certifies_width_aperturePositivity_iff` says a finite-aperture certificate certifies `β` iff
`β ≥ ½`.

`resolutionLimit_width_familyPositivity`: the same for an arbitrary family of apertures bounded by
`A` — no stack of certificates, of any cardinality, improves the trivial bound.

`resolutionLimit_width_fullPositivity` and `apertureResolutionJump`: the unbounded reading has limit
`0`. `apertureLadder`: the ladder of aperture readings is *strictly* increasing in information while
every stage has limit `½`.

### 3.5 The node face: densities are excluded wholesale

A one-node deletion is a finite modification, so every asymptotic reading is invisible to it
(`invisible_deleteNode_of_asymptoticReading`), and the deletion of a prime power is uniformly fatal.
Hence `not_resolves_of_asymptoticReading`: under RH no density, asymptotic count or sieve level
resolves node positivity; equivalently `not_riemannHypothesis_of_resolves_of_invisible`. Under RH
every resolving reading must move *every* prime-power deletion
(`exists_deleteNode_reading_ne`), and the fatal collapses are exactly the prime powers
(`fatal_deleteNode_iff_isPrimePow`): the gate is incidence, never density.

### 3.6 The parity face: the amplitude floor is `½`

`not_resolves_amplitudeReading_receiver`: the damped Möbius weight at half damping and its parity
twin have the same amplitude reading, bounded receiver against divergent — the actual arithmetic
source, not a model. On the damped class, `not_resolves_classAmplitudeReading` and
`half_lt_of_resolves_classAmplitudeReading` give the floor: an amplitude-reading criterion for the
receiver exists only above damping `½`. `not_resolves_amplitudeDerivedFamily` closes the class: every
family of amplitude-derived observables is blind as well.

The number `½` is the same number as in the aperture face, through
`SquareRootThreshold.receiverDampingRate_eq_zetaZeroWidth`: the trivial width.

### 3.7 The temperedness face

`structuralFlags_eq`: nonnegative Dirichlet coefficients, a nonnegative von Mangoldt weight
supported on the prime powers, the functional equation and polynomial vertical growth hold for every
`|a| ≤ ¼` with the same proofs as for `ζ`, so the reading is constant there; at `a = ¼` Hardy's
theorem supplies zeros of real part `¼`. Hence
`not_riemannHypothesis_of_resolves_structuralFlags`, and
`not_riemannHypothesis_of_resolves_flagDerived` for any quantity computed from the flags. What is
missing from the list is exactly the Ramanujan ceiling.

### 3.8 The height face: no finite carrier

`heightReading T` is the divisor truncated at height `T`; by local finiteness it is finite data
(`finite_support_heightReading`), so it models any finite carrier. Inserting one reflected off-line
pair above height `T` leaves it unchanged (`heightReading_isolatedPairConfig`) and moves the width to
the depth of the pair: `not_resolves_heightReading_onLine` and
`resolutionLimit_width_heightReading` (limit exactly `½`). This is "every scale, not almost every"
as a theorem.

### 3.9 The prime-window face: a bounded radius is blind to the cone

`radiusReading R` is the full Weil functional of a prime weight on every test of aperture `R`. It is
a function of the finitely many primes below `e^{2R}` (`radiusReading_congr_of_agree_below`), and at
every radius a weight `lam ≥ Λ` modified at one index above `e^{2R}` has the reading of `Λ` and lies
outside the cone (`exists_not_weilPositiveFull_radiusReading_eq`). Hence
`not_riemannHypothesis_of_resolves_radiusReading`, and the same for every quantity computed from the
certificate (`not_riemannHypothesis_of_resolves_radiusDerived`). The zero-side and prime-side gates
are the two faces of one statement: a bounded aperture is blind to every width, a bounded radius is
blind to the cone.

### 3.10 The gates

`theWallGates` states, under RH, both halves of four faces at once — temperedness, node criticality,
trans-Nyquist aperture, no finite carrier — and `parityWallGate` states the parity row in the same
shape. To test a proposed mechanism, present it as a reading and instantiate.

---

## 4. Traps

* **A reading is not a method's conclusion, it is its input.** Floors apply to what the method
  *reads*, not to what it concludes; a method that reads the full datum has limit `I(d)` and proves
  everything. Every floor statement must therefore name the reading precisely, and the honest
  statement of a no-go is "no method reading *this* can do better than *that*".
* **`Prop`-valued readings need `propext`.** A positivity certificate is a `Prop`; two data share
  the reading when the two `Prop`s are *equal*, obtained from `iff_of_true` and `propext`. Writing
  `Iff` where `Eq` is needed is the commonest friction in these files.
* **Multiplicities off the carrier are noise.** `Zeta23.ZeroConfig.mult` is unconstrained off the
  carrier, so a reading must restrict it to the carrier (as `heightReading` does) or it separates
  pairs for a reason that is not mathematics.
* **Bounded, not finite, is the operative hypothesis.** The aperture family theorem assumes the
  apertures are bounded, not that they are finitely many: an infinite family of bounded apertures is
  just as blind, and that is the content.
* **A faithful reading is not a proof.** Faithfulness of the unbounded-aperture reading
  (`resolutionLimit_width_fullPositivity`) says the data determine the width; it does not produce the
  certificate. The floors say where not to look; they do not say where to look.
* **The faces do not all fit in one module.** The corpus currently declares `RHTower.dilationAverage`
  twice (in `RHTower.SoninDilationAverage` and in `RHTower.FermiNymanHaarApproximationEquivalence`),
  so the import closure of `SquareRootThreshold` and that of `TransHorizonIncidenceMechanics` cannot
  be loaded into one environment. That is why the parity row of the gate theorem lives in its own
  module and not in `TheWallGatesOfAResolvingReading`; it is an import-level fact about the corpus,
  not a mathematical obstruction.
* **RH on the positive side.** Two faces (node positivity, criticality of the pair) hold at the base
  datum only under RH, so their gates are stated as "resolving reading ⇒ ¬RH", or with RH as an
  explicit hypothesis. That is the honest form; "no method can decide" would be a stronger claim
  than is proved.

---

## 5. The frontier

Open, in this programme's own unit (a class of readings and its exact limit):

1. **A numerical unit for the prime-window face.** The gate is proved (§3.9: a bounded radius never
   resolves the cone), but the statement is vacuity, not a number. What real invariant of a weight
   plays the role of the width here — a cone defect — and what is its exact resolution limit at
   radius `R`? The expected shape is a positive floor independent of `R`.
2. **Faithfulness of the pole compression.** `SquareRootThreshold.PrimeTailCouplingCriterion` makes
   the rank-two pole-compression matrix a lossless reading of the aperture-`a` coupling. Is the
   reading `a ↦ 𝒫(a)` faithful for the width? A positive answer makes the `2 × 2` matrix the
   smallest faithful reading known, and the natural target of any construction.
3. **The exact floor of the Gram reading.** For the cross-scale dispersion of
   `BezoutValuationIncidence` the relevant reading is the pronic Gram at one modulus. Its limit in
   the exponent unit `θ` should be exactly `2`; the witness would be the coherent prime block of
   `CoherentPrimeBlocksAndTheTypeIIWindowNoGo`.
4. **Joint limits and the seams.** `resolutionLimit_joinReading_le` bounds a joint reading by the
   minimum of the parts, but the interesting quantity is the limit of the *intersection* of two
   shadows. For the pairs (aperture, amplitudes) and (height, nodes) the intersection is not computed;
   a strict drop there is exactly what "exploiting a seam between two proved theorems" would mean
   quantitatively.
5. **A fatality classification.** Node criticality classifies the fatal node collapses exactly
   (prime powers). The analogous classification for the parity collapses — which involutions of a
   damped weight are fatal for the receiver — is open, and would turn the parity gate into a
   sharp law.

---

## 6. Working in the theory

* State the reading first, the collapse second, the witness pair third. A statement without all
  three is not in the theory.
* Prefer a limit to a blindness statement: the limit is the usable form, and the proof is usually
  the same two inequalities.
* Instantiate the general theorems rather than reproving the shape: `not_resolves_of_pair`,
  `forall_not_of_resolves_of_invisible`, `iterate_le_resolutionLimit`,
  `resolves_iff_exists_factorization`, `Resolves.of_refines` and the three `Invisible` closure
  lemmas cover every instance so far.
* Take the countermodels from the owning programme. This programme does not build arithmetic
  objects; it imports the configurations of `SquareRootThreshold`, the node sets of
  `BiScaleUncertainty`, the weights of `TransHorizonIncidenceMechanics` and the pair of `RHTower`,
  and adds exactly the calculus.
* Report every result as a pair `(class of readings, exact limit)`, and say which gate it closes.
