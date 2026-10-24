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
collapse that changes the verdict, or it cannot resolve that verdict. Every statement here is unconditional and
names its reading, its collapse and its witness pair.

## Place in the research

This is an information theory for proposed arithmetic arguments. It asks which data an argument
actually uses, what other sources share those data, and which target values remain possible in
that class. Its positive tools are refinement, exact inversion from magnitudes, and cofinal rate
readings. Its negative tools are explicit indistinguishable pairs and sharp bounds on their shadows.
Passing a blindness test is necessary for a proposed method; it is not an estimate or a proof of RH.

| Programme | Connection |
|---|---|
| [Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md) | Supplies complete source families; the reading must preserve the information their receiver needs. |
| [Bi-Scale Uncertainty](../BiScaleUncertainty/README.md) | Supplies node-critical blind cones, packet rates and countermodels. |
| [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Supplies parity collisions and the distinction between a finite observer and uniform receiver payment. |
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) | Its cross-scale Gram and dispersion readings are priced in the exponent unit `θ = 2 log P / log X`: the sign-blind Type-II and rank-two readout readings have exact limit `2` and floor `0`, `K`-kernel smoothness reduces the unresolved deficit limit to `2/(K+1)` (`θ_cert = 2K/(K+1)`), `residueMass` and `kernelStatistic` complete the single-modulus face faithfully, and the centred prime row bypasses the Type-II shadow on `(7/6, 2)`. |
| [Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md) | Supplies bounded-aperture certificates, the ground-energy path `μ(A)` whose sign and magnitude read different information, and the two-aperture ratio `zetaTwoApertureRatio A₀ A = (μ(A₀) - μ(A))/μ(A₀)` whose critical value `1` is attained on the line. |
| [Square-Root Threshold](../SquareRootThreshold/README.md) | Supplies the lattice models, Nyquist laws, visibility witnesses and zero-width dictionary. |
| [Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md) | Supplies allocation and cross-prime aggregate readings; their signs and sizes must be distinguished. |
| [Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Distinguishes pointwise, averaged and horizon-uniform budgets; a transport must supply its arithmetic estimate. |
| [Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md) | Tests whether changing an energy or splitting work preserves the signed information needed for admission. |
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | Separates formal signature criteria from the arithmetic effectivity data that would force them. |
| [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Exhibits the information lost when a signed incidence kernel is replaced by an absolute majorant. |
| [Trans-Threshold Pair Correlation](../TransThresholdPairCorrelation/README.md) | Its two-thirds barrier is a resolution limit: the reading `(Â, N)` of the evaluation Gram cannot tell a double critical zero from a coalescing off-line pair, so its exact limit is `(2 − κ)N` simple zeros, and only data beyond the reading (zero-side slack, prime pairs beyond `X = T`) can move it. |
| [Arithmetic Orientation Theory](../ArithmeticOrientationTheory/README.md) | Builds on these readings. A flip is an involution of the data, and a reading is orientation-faithful when it separates every datum from its flip. Invisibility is closed under post-processing, pairing, families and coarsening, and resolving a flipping predicate forces faithfulness. The refutation theorem of §3.8 is the reading entry of its width dictionary. |

**The shared target.** The programmes in the table work on RH as the sign of one critical
arithmetic form. SSIC is its admissibility layer: it prices a reading before a route is built, and
states the separations a reading must perform to be admissible — past the Nyquist aperture of the
configuration addressed, by magnitude rather than sign, and on the prime side separating `Λ` from
each of its single-index perturbations.

Start with `TheResolutionLimitOfAReading`, then the aperture and node examples. The precision and
band-inversion laws explain how a failed sign reading can be strengthened. Finally,
`TheRateIsACofinalInvariant` and `TheBoundedApertureRateCertifiesNothing` isolate the resource needed
for a rate: cofinality, under an explicit convex-profile hypothesis. `RHTower.DeciderBarrier`
contains related collision tools; the owning programmes supply the arithmetic countermodels.

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

### 1.2 The scope of the calculus

The calculus is set-theoretic: equal observations define fibres, and an invariant is determined
exactly when it is constant on those fibres. Its research content comes from the arithmetic
instances: explicit countermodels, sharp resolution intervals, stable inversion formulas, and
proofs that a proposed class of methods factors through a particular reading. An abstract fibre
argument alone establishes no analytic impossibility outside the named data class.

### 1.3 Where it points

The intended use is chronological: gates first, construction second. A mechanism can survive the known obstructions only when its reading passes the relevant gates, and the calculus is arranged so that the check is an
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
  `certifies_iff_resolutionLimit_le`, provided the invariant is bounded above on the shadow;
* `resolutionFloor`, `CertifiesLower` — the dual theory, with
  `resolutionFloor_eq_neg_resolutionLimit`;
* the **resolution interval** `[resolutionFloor, resolutionLimit]` — the smallest closed interval containing the values left open, when those values are bounded.
  It need not be the image itself: interior values and endpoints need not be attained. A reading is *informative* for `I` at `d` exactly when this interval is proper
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

The blind readings studied here — bounded certificates and purely vertical data such as the
exact ordinate set — fail to separate these orbits. Magnitude and rate readings need not fail. That is the field's dichotomy, and it is about coordinates rather than
boundedness: the exact ordinate set is unbounded data, determines the scale exactly, and still has
the trivial limit `½` for the depth. The **vertical** coordinate is what every reading sees; the
**horizontal** one carries RH.

### 2.6 The units

| unit | definition | vanishes exactly when |
| --- | --- | --- |
| width | `sup \|Re ρ − ½\|` over the configuration (`width`) | all zeros on the line |
| depth | `δ` on the lattice family; the dilation invariant (`sdDepth`) | the configuration is on-line |
| deficit rate | `inf {β ≥ 0 : the deficit is O(e^{2βa})}` (`rateSet`, `sInf_rateSet`) | the configuration is on-line |
| depth resolution | `arcosh(1 + η/(2L))/L` at level `η` and scale `L` (`depthResolution`) | at `η = 0`; otherwise it is a positive resolution allowance |
| node scale | `sup {1/m : m a prime power, m ∉ 𝒩}` (`nodeScale`) | `𝒩` contains every prime power |
| band ratio | `t₃/(2t₂) − 1` on a lattice, `(t₄−t₃)/(t₃−t₂)` with mass, `M(2a)/(2M(a))` on a pair, and `(μ(A₀)−μ(A))/μ(A₀)` for `ζ` (`ratio_eq_cosh`, `difference_ratio_eq`, `normalizedPairDoublingRatio_eq_cosh`, `zetaTwoApertureRatio`) | at the critical value `1` (resp. `2` for the three-band difference ratio) |
| cross-scale exponent | `θ = 2 log P / log X` (`crossScaleExponent`), certified floor `2K/(K+1)` (`smoothCertifiedExponent`) and deficit `2/(K+1)` (`smoothUnresolvedLimit`) | deficit vanishes at the receiver scale `X = P` (`θ = 2`, `K → ∞`) |

The width and the depth **vanish together** on the lattice family and are the two ends of the same
scale; depth, width on this family, and the deficit rate are all constant on dilation orbits. A result in one
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
| pronic Gram | prime-block packets (`PronicBlockGramDatum`) and large-scale rows (`ReadoutGramDatum`, `SmoothGramDatum`) | cross-scale exponent `θ ∈ [0, 2]` and Bernoulli functional (`bernoulliCrossScaleMain`) | `typeIIGramReading`, `rankTwoReadoutReading`, `smoothKernelReading`, `residueMass`, `completedKernelStatisticReading` |
| parity collapses | four-free damped convolutions (`k ⋆ o_ε`), Selberg sign orbits (`scaledSelbergRow`), and residue-class prime flips (`residueFlip q S`) | `ReceiverBounded` and `horizonPronicEnergy` | `amplitudeReading`, `completePeriodLagReading N`, `cubicMomentReading N`, `firstPronicMoment`, `logPowWeight` |

The faces owned elsewhere — temperedness (the shifted pair), parity (damped weights) — are priced by
the same calculus, with their countermodels in `RHTower` and `TransHorizonIncidenceMechanics`.
Three shadows on those faces are now computed exactly, and each is the template for its face:

* **Complete-period quadratic data.** The shadow of a divisor row under the reading "all
  complete-period lag covariances, with the mean" is exactly its orbit under the sign characters
  `Y(q) ↦ ±Y(q)` of the Selberg coordinates (`mem_shadow_completePeriodLagReading_iff_signOrbit`,
  Arithmetic Orientation Theory): the reading sees magnitudes of modes and nothing else, and every
  verdict that changes under a sign flip is unresolved by it.
* **Prime signs and prime mean.** For the half-damped receiver of a multiplicative weight the reading
  (signs of `f(p)`, real-axis prime mean) does not resolve payment: two oscillating patterns share it
  and have opposite receivers (`exists_paid_unpaid_with_same_prime_signs_and_mean`). The receiver
  itself reads `a cos φ` and the value of `ζ` at the oscillation height, and the flipped density
  resolves payment only on residue patterns (Trans-Horizon Incidence Mechanics, §3.18).
* **Window extremes.** The ceiling and floor of the prime-window spectrum are constant on the orbit
  of unimodular completely multiplicative twists (`twistedWindowCeiling_eq`, Bi-Scale Uncertainty):
  a reading through extremes is blind to every character, hence cannot resolve GRH.

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
maximal width `½` that satisfies the certificate for free — an off-line lattice with scale
`L ≥ 2a`, whose first nonzero Poisson lag lies outside the test autocorrelation support
(`exists_width_eq_half_aperturePositivity`). It lies in the shadow of every datum satisfying the
certificate, so by the floor theorem

`resolutionLimit width (aperturePositivity a) Z = ½`   (`resolutionLimit_width_aperturePositivity`),

for a datum on which the certificate holds. That successful certificate certifies nothing beyond the a priori bound
(`certifies_width_aperturePositivity_iff`). The same witness, with the gain built in, gives the same
number for a coercive certificate at any level (`resolutionLimit_width_apertureGain`,
`gainLadderIsTrivial`), for a bounded family of apertures of any cardinality
(`resolutionLimit_width_familyPositivity`), for a family of configurations
(`resolutionLimit_familyWidth_familyAperture`), and — composed with any monotone reparametrisation
`g` of the depth — for the unit `g ∘ width` (`resolutionLimit_comp_width_apertureGain`,
`theFloorIsUnitIndependent`). The floor is not an artefact of the unit.

At the lower end the on-line lattice lies in every aperture shadow
(`onLineLattice_mem_shadow_aperturePositivity`), so the dual limit is `0`
(`resolutionFloor_width_aperturePositivity`) and the resolution interval is the entire range of the
width (`resolutionInterval_width_aperturePositivity`, `range_width`): a bounded-aperture certificate
of successful positivity checks alone neither proves nor refutes the critical line. A negative
test at a bounded aperture can refute it. Only the unbounded certificate has limit `0`
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

In the first nontrivial aliasing band `L/2 < a ≤ L`, at known scale `L > 0`, the lattice
Weil form acquires the deficit

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
(`theRateReadingIsTheAnswer`). A uniform mass-normalised deficit bound over every aperture excludes positive-depth lattices
(`theGateIsPassedByNonGrowth`); the on-line lattice satisfies it
(`uniformDeficit_onLineLattice`). A bound growing with test frequency is a different reading and
may be vacuous. The normalisation and quantified parameter range are indispensable.

### 3.5 How a configuration hides: crystal, mass, dilution

The sharp blindness witnesses above are infinite crystals. The following laws explain their
cost; they do not classify every configuration capable of hiding at one aperture.

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
  every aperture at most `min(ℓ/2, L/2)` in the stated diluted-lattice model
  (`dilutedLattice_hides_below_own_nyquist`), and the free regime ends exactly at `ℓ/2`: strictly above
  it the pure off-line lattice ground energy is negative (`latticeFloor_neg_of_two_le`, `theFreeRegimeIsSharp`).

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
positivity (`not_zeroPoleBlindPositiveOn_deleteNode`, `not_zeroPoleBlindPositiveOn_of_notMem`).
Under RH, the prime powers are the least positive node set (`isLeast_zeroPoleBlindPositiveOn`),
and positive node sets form the principal up-set of sets containing them (`theNodeFaceIsAPrincipalUpSet`).
Unconditionally, node positivity is equivalent to **RH and containment of every prime power**;
if RH fails, there are no positive node sets. Cofinality or density one cannot compensate for a
missing prime power (`theReductionDichotomy`); omission of a non-prime-power is invisible. A reading unchanged by finitely many
nodes resolves nothing (`not_resolves_of_asymptoticReading`,
`resolutionLimit_nodeScale_asymptoticReading`).

*Refutation: finite, and complete.* A reading **refutes** when nothing it admits satisfies the
property (`Refutes`), and refutation passes to finer readings (`Refutes.of_refines`). On the prime
side the calculus is exactly complete: a certificate of radius beyond a failure aperture refutes the
cone (`refutes_radiusReading`), and RH holds precisely when no bounded-radius certificate refutes
membership of the von Mangoldt weight in the full Weil cone
(`riemannHypothesis_iff_no_radiusReading_refutes`). On the node face a single membership bit refutes
when it records a missing prime power (`refutes_membershipReading_of_notMem`). Under RH,
absence of such refutations characterizes node positivity
(`zeroPoleBlindPositiveOn_iff_no_membership_refutes`, `theNodeFaceAsymmetry`). Failure has a witness at a finite scale. This is not a general algorithm to compute a negative
Weil value: an effective numerical refutation still needs error bounds. Confirmation requires
the complete family or a proved reduction of it.

### 3.9 Rates on cofinal and bounded aperture sets

For a convex growth profile `g`, its secant rate `(g(a) − g(0))/a` is nondecreasing for `a > 0`.
Consequently the set of upper bounds on those secants over any unbounded set of positive apertures
is exactly the set of upper bounds over all positive apertures (`rateBoundsOn_eq_rateBounds`).
The readings themselves agree, so their shadows, resolution limits, floors and resolved properties
agree. No density assumption on the aperture set is needed.

The bounded-range converse has explicit witnesses. The convex ramps
`g_k(a) = k max(0, a − M)` all agree with the flat profile below `M`, while their rates are `k`.
Thus the flat profile's shadow under a bounded reading has unbounded rates, and no finite upper
bound is certified (`not_certifies_rateBoundsBelow`). In this unbounded class one must state
failure of `Certifies` directly; Lean's real `sSup` is not an extended-real infinity.

This settles the abstract convex-profile sampling question. Applying it to an arithmetic
exponential rate still requires identifying a profile with the needed convexity or proving a
suitable monotonicity replacement. It does not make arbitrary sparse lag samples complete.

---

## 4. Foundational pillar theorems

All unconditional; where RH holds only at the base datum the gate is stated as "resolving reading
⇒ ¬RH" or with RH as a hypothesis.

1. **The collapse–resolution dichotomy.** A reading that misses a verdict-changing collapse does not
   resolve the verdict (`not_resolves_of_separating_collapse`), and a resolving reading forces failure
   on every orbit it misses (`forall_not_of_resolves_of_invisible`,
   `not_riemannHypothesis_of_resolves_of_invisible`).
2. **The floor theorem.** If the invariant attains its maximum inside a shadow, the resolution limit
   is that maximum (`resolutionLimit_eq_of_mem_shadow_of_max`); this makes every number of the field
   exact.
3. **The aperture certificate is blind in every unit.** A bounded-aperture positivity certificate —
   coercive at any level, over any bounded family, composed with any monotone unit of the depth —
   has width limit `½` and floor `0` (`resolutionLimit_width_aperturePositivity`,
   `theFloorIsUnitIndependent`, `resolutionLimit_familyWidth_eq_half_of_constant`); only the
   unbounded certificate has limit `0`.
4. **The depth is the complete dilation invariant.** On lattice families the depth separates exactly
   the dilation orbits, and with both coordinates free a single-aperture reading has limit `½`
   (`resolutionLimit_sdDepth_scaleDepthReading`, `theDilationRequirement`).
5. **The square-root precision law.** Past the Nyquist aperture the deficit, not the sign, is
   informative, and excluding depth `β` at scale `L` costs precision `β²L³`
   (`theDeficitBudgetLaw`).
6. **Magnitudes are faithful where signs are blind.** Two consecutive aliasing band energies
   determine the depth in closed form (`theTwoBandCertification`), the band-pair reading has exact
   limit equal to its floor (`resolutionFloor_eq_resolutionLimit_bandPairReading`), and three bands
   defeat the local mass (`theApertureDoublingPrescription`); the sign of the same data is blind
   (`theSignIsBlind`, `theDichotomyOfSignAndMagnitude`).
7. **The hiding laws.** The reach of a hiding configuration is linear in the dilution and only
   logarithmic in the mass (`theReachLaw`, `theFreeRegimeIsSharp`).
8. **Refutation is finite, confirmation is not.** On the node face finite membership data refute,
   while every bounded confirmation needs infinitely many off-line zeros in its witnesses
   (`theNodeFaceAsymmetry`, `theFloorsNeedInfinitelyManyOffLineZeros`); sparse unbounded apertures
   suffice for the aperture face and no sampling suffices for the incidence face
   (`theReductionDichotomy`).
9. **The rate is a cofinal invariant.** For convex growth profiles, secant rates on any unbounded
   aperture set equal those on all apertures (`theRateIsACofinalInvariant`), and bounded readings
   certify no finite rate (`theRateDichotomyIsSharp`).
10. **The exact floor of the pronic Gram reading and its smoothness ladder.** In the cross-scale
    exponent unit `θ = 2 log P / log X ∈ [0, 2]`, both the sign-blind Type-II Gram reading and the
    rank-two readout reading `(R, H)` have exact resolution limit `2`, resolution floor `0`, and
    resolution interval `[0, 2]`, witnessed by the coherent prime block and the three-window
    readout-free barrier (`resolutionLimit_typeIIGramReading_eq_two`,
    `exists_primeBlock_witness_at_resolutionLimit_two`,
    `exists_readout_free_witness_at_resolutionLimit_two`). Cancelling `K` Euler–Maclaurin kernels via
    difference smoothness certifies `θ_cert(K) = 2K/(K + 1)` and lowers the unresolved deficit limit
    along `2/(K + 1) → 0` (`resolutionFloor_smoothKernelReading_eq`,
    `resolutionLimit_smoothKernelReading_deficit_eq`). On a single modulus, `residueMass` is faithful
    for the Bernoulli cross-scale main term (`faithful_residueMass_bernoulliCrossScaleMain`),
    `kernelStatistic` collapses the shadow diameter to the fourth-order tail, and the actual centred
    prime row bypasses the Type-II shadow across `7/6 < θ < 2`
    (`centredPrimeRow_bypasses_resolutionLimit_two`).
11. **The two-aperture band recipe for `ζ` and its reachable bounds.** For any reference aperture
    `A₀ ≤ 21/200` (where `μ(A₀) ≥ 1/30 > 0` unconditionally), the two-aperture ground-energy ratio
    `zetaTwoApertureRatio A₀ A = (μ(A₀) − μ(A))/μ(A₀)` and its explicit-formula prime-window
    companion `primeWindowTwoApertureRatio A₀ w v` (retaining the prime sum, archimedean term, and
    polar term) have critical value `1`: `RiemannHypothesis` holds iff `zetaTwoApertureRatio A₀ A ≤ 1`
    for all `A`, iff `zetaTwoApertureRatio A₀ A → 1` as `A → ∞`, and iff the clamped ratio
    `zetaClampedTwoApertureRatio A₀ A` equals `1` everywhere
    (`riemannHypothesis_iff_forall_zetaTwoApertureRatio_le_one`,
    `riemannHypothesis_iff_tendsto_zetaTwoApertureRatio_one`,
    `riemannHypothesis_iff_forall_zetaClampedTwoApertureRatio_eq_one`). Exponential growth
    `≤ 1 + C e^{2σA}` unconditionally forces `|Re ρ − ½| ≤ σ`
    (`abs_re_sub_half_le_of_zetaTwoApertureRatio_le_one_add_exp`), near-top zeros force the ratio
    strictly above `1` beyond their visibility lag (`one_lt_zetaTwoApertureRatio_of_near_top_zero`),
    and the corpus's unconditional inputs certify `< 1` on `[0, 21/200]`, `≤ 1` on `[0, 3/10]` for
    the prime-window ratio, and `≤ 1 − windowFloor(A)/μ(A₀)` on `(0, ½ log 2)`
    (`zetaTwoApertureRatio_lt_one_of_le_twentyOne_twoHundredths`,
    `primeWindowTwoApertureRatio_le_one_of_le_threeTenths`, `zetaTwoApertureRatio_le_windowFloor`).
12. **The fatality classification of parity collapses and their faithful completions.** Across the
    three parity-collapse families, strict fatality (`StrictlyFatalAt`) and neutrality (`NeutralAt`)
    are classified in closed form (`strictlyFatalAt_iff_pairFatalAt_of_paid`,
    `strictlyFatalAt_iff_not_neutralAt_of_paid`):
    (i) on four-free convolutions `k ⋆ o_ε` (`0 < ε ≤ 1/2`), `evenFlip` is strictly fatal iff
    `poleValue k J ε = 0 ∧ poleValue (evenPartWeight k) J ε ≠ 0`
    (`strictlyFatalAt_evenFlip_iff_pole_and_evenPart`), paid and neutral iff both `oddPartKernel k`
    and `evenPartWeight k` vanish at `1 − ε` (`evenFlip_paid_and_neutral_iff_odd_and_even_pole`),
    strictly fatal for every non-zero paid two-point kernel (`strictlyFatalAt_evenFlip_twoPoint_iff`),
    expelled from the shadow by `firstPronicMoment` iff `weightRamanujanCoeff c 2 ≠ 0`
    (`not_mem_shadow_joinReading_firstPronicMoment_iff`), and separated on the generalized Fermi
    locus by logarithmic pronic moments (`exists_logMoment_ne_of_strictlyFatalAt_evenFlip`);
    (ii) on the `2^{N−1}` Selberg sign-character shadow of `completePeriodLagReading N`, refining by
    `cubicMomentReading N` expels `chiFourTwinRow ε N` at every `N ≥ 3`, collapses the sign orbit to
    a singleton on odd-supported rows (`cubicMomentReading_pins_odd_signOrbit`), and reduces the sign
    orbit of squarefree-supported rows to at most `{c, evenFlipRow N c}`
    (`cubicMomentReading_reduces_squarefree_signOrbit_to_evenFlip`);
    (iii) on half-damped residue-class prime flips `residueFlipHalfWeight q S`, every complement pair
    `{S, Sᶜ}` has at least one paid member (`receiverBounded_residueFlip_or_compl_half`),
    complementation is paid and neutral iff `φ(q) < 4 |S^\times| < 3 φ(q)`
    (`both_residueFlip_and_compl_paid_iff`), and strictly fatal iff `3 φ(q) ≤ 4 |S^\times|`
    (`strictlyFatalAt_compl_residueFlip_half_iff`), so subgroup flips `subgroupFlipSet H` are
    complement-neutral at index `2` and `3` and strictly fatal iff the index is at least `4`
    (`strictlyFatalAt_compl_subgroupFlipSet_iff`).
13. **The rate reading for `ζ` and the price of the local off-line count.** Four rate currencies of
    `ζ` — the dyadic prime-window lag rate, the integrated Chebyshev deficit rate, the mean-square
    band rate, and the Möbius receiver damping threshold — equal `zetaZeroWidth` unconditionally,
    while the polar restricted Weil ground-energy rate `polarGroundEnergyRate` satisfies
    `zetaZeroWidth ≤ polarGroundEnergyRate ≤ 1/2` and equals `zetaZeroWidth` whenever the off-line
    zeros have bounded local count `OffLineCopiesLocallyBounded M` or bounded local squared-depth
    mass `OffLineDepthLocallyBounded W` (`five_rate_currencies_of_zeta`). At a single aperture `A`,
    a deficit `ccmRestrictedWeilGroundEnergy A ≤ −η` (`η > 0`) together with `OffLineCopiesLocallyBounded M`
    certifies `singleApertureWidthFloor M A.1 η ≤ zetaZeroWidth`
    (`singleApertureWidthFloor_le_zetaZeroWidth`), lifting the width resolution floor on
    `ApertureCountDatum A` from `0` (`resolutionFloor_width_deficitOnly_eq_zero`) to
    `max 0 (singleApertureWidthFloor d.count A d.deficit)` (`le_resolutionFloor_width_deficitAndCount`).
    In the asymptotic rate space `ZetaRateDatum`, reading `width` alone leaves `polarRate` with
    resolution interval `[width, 1/2]` (`resolutionInterval_polarRate_widthOnly`) and reading
    `polarRate` alone leaves `width` with floor `0` (`resolutionFloor_width_polarRateOnly_eq_zero`),
    while adjoining `locallyBounded` collapses both to `width`
    (`resolutionLimit_polarRate_widthAndLocalCount`, `resolutionFloor_width_polarRateAndLocalCount`).
    On the lattice family `ScaleDepthDatum` without convexity assumptions, cofinal rate sampling
    (`cofinalRateSet S`) is faithful for `sdDepth` (`faithful_sdDepth_cofinalRateSet`), whereas any
    bounded-range rate reading (`boundedRateSet M`) has exact limit `1/2` and floor `0`
    (`resolutionLimit_sdDepth_boundedRateSet_eq_half`, `resolutionFloor_sdDepth_boundedRateSet_eq_zero`).
14. **The design specification of a counterexample: exact diluted-reading limits and dyadic comb
    visibility.** Symmetrising `centredSum` under `Fin.revPerm` decomposes the `n`-th aliasing band
    energy into `bandEnergy ℓ δ n = ℓ ∑_{j=0}^{n−1} (cosh(δℓ(2j − n + 1)) − 1)`
    (`bandEnergy_eq_sum_cosh_sub_one`), satisfying the two-step recurrence
    `bandEnergy ℓ δ (n + 1) − bandEnergy ℓ δ (n − 1) = 2ℓ(cosh(nδℓ) − 1)` (`bandEnergy_succ_sub_pred`)
    and strict monotonicity in both index (`bandEnergy_lt_succ`) and depth
    (`bandEnergy_strictMono_depth`). Consequently, for every `0 < a ≤ L/2`, the joint aperture–mass
    reading `dilutedReading hℓ hL a` on `DepthDatum` is equivalent to
    `bandEnergy ℓ (depth d) ⌈2a/ℓ⌉₊ ≤ 2L` (`dilutedReading_iff_bandEnergy_le`), is downward-closed in
    depth (`dilutedReading_of_depth_le`), has `resolutionFloor = 0` (`resolutionFloor_depth_dilutedReading`),
    has exact limit `1/2` in the sub-Nyquist regime `a ≤ ℓ/2`
    (`resolutionLimit_depth_dilutedReading_subNyquist`), has exact limit `min (1/2) (depthResolution ℓ (2L))`
    across the second aliasing band `ℓ/2 < a ≤ min ℓ (L/2)`
    (`resolutionLimit_depth_dilutedReading_secondBand`), and is bracketed at every `ℓ/2 < a ≤ L/2`
    between `min (1/2) (arcosh(1 + 2L/(ℓ⌈2a/ℓ⌉₊))/(⌈2a/ℓ⌉₊ℓ))` and
    `min (1/2) (log((2L + 2a + ℓ)/ℓ)/(2a − ℓ))` (`resolutionLimit_depth_dilutedReading_brackets`).
    On the lag axis, a two-bump difference test `twoBump (modScaledBump w 0) v (−1)` on
    `dilutedLatticeConfig` evaluates at the `n`-th sub-lattice tooth `v = nℓ` (`nℓ + 2w ≤ L`) to
    `4(L − ℓ(cosh(nδℓ) − 1))‖κ_w‖²` (`W_dilutedLattice_lag_nat_mul`) — reading `-2 · bandDeficit ℓ δ L 2`
    and `-2 · bandDeficit ℓ δ L 3` at the first two teeth (`re_W_dilutedLattice_first_two_teeth_eq_bandDeficit`)
    — while evaluating to `4(L + ℓ)‖κ_w‖² > 0` in every gap `|v − nℓ| > 2w` (`W_dilutedLattice_lag_eq_of_gap`).
    Against the prime-side explicit formula, any structured counterexample faces the `3/10` prime-free
    barrier, the unbounded zero-count remainder `rvmRemainder_unbounded`, and dyadic prime-window
    negativity at polylogarithmic lag (`counterexample_primeSide_obstructions`).
15. **Policies for a configuration of growing density: exact limits, multi-band inversion, and
    realisable schedules.** On `ScaleDepthDatum`, the global policy reading `adaptiveReading A η` has
    exact resolution limit `1/2`, floor `0`, and interval `[0, 1/2]` whenever a single scale `L > 0`
    is sub-Nyquist (`A(L) ≤ L/2`, `0 ≤ η(L)`), including every bounded aperture schedule
    (`resolutionLimit_sdDepth_adaptiveReading_of_exists_subNyquist`,
    `resolutionLimit_sdDepth_adaptiveReading_of_bddAbove`). Under `ScaleMatched A η` (`L/2 < A(L) ≤ L`),
    the scale-aware completion `scaleAdaptiveReading A η = joinReading sdScale (adaptiveReading A η)`
    has exact limit `min (1/2) (depthResolution L (η L))` and floor `0` at scale `L = sdScale p₀`
    (`resolutionLimit_sdDepth_scaleAdaptiveReading_scaleMatched`), while `adaptiveReading A η` has
    global limit `sSup ((fun L => min (1/2) (depthResolution L (η L))) '' Ioi 0)` and floor `0`
    (`resolutionLimit_sdDepth_adaptiveReading_scaleMatched`), certifying `β ∈ (0, 1/2)` iff
    `∀ L > 0, η L ≤ weilFloorThreshold L β` (`certifies_sdDepth_adaptiveReading_iff`), with
    `depthResolution L (η L) → 0` whenever `η L / L³ → 0`
    (`tendsto_depthResolution_zero_of_div_cube_tendsto_zero`). For arbitrary trans-Nyquist aperture
    growth `TransNyquistPolicy A η` (`A(L) > L/2`, `aliasingIndex A L = ⌈2A(L)/L⌉₊ ≥ 2`),
    `adaptiveReading A η p ↔ bandEnergy (sdScale p) (sdDepth p) (aliasingIndex A (sdScale p)) ≤ η (sdScale p)`
    (`adaptiveReading_iff_bandEnergy_le`), the `n`-th band energy obeys the hyperbolic lower bound
    `weilFloorThreshold L ((n − 1)δ) ≤ bandEnergy L δ n` (`weilFloorThreshold_mul_le_bandEnergy`) so
    that `bandEnergy L δ n ≤ η` forces `δ ≤ depthResolution L η / (n − 1)`
    (`depth_le_div_sub_one_of_bandEnergy_le`), `scaleAdaptiveReading A η` is bracketed between
    `min (1/2) (arcosh(1 + η(L)/(L · n_L))/(n_L L))` and `min (1/2) (depthResolution L (η L) / (n_L − 1))`
    (`resolutionLimit_sdDepth_scaleAdaptiveReading_brackets`), and global certification of `β ∈ (0, 1/2)`
    is equivalent to `∀ L > 0, η L ≤ bandEnergy L β (aliasingIndex A L)`
    (`certifies_sdDepth_adaptiveReading_transNyquist_iff`). Against `ζ`'s growing zero density at height
    scale `L(ξ) = log(1 + π|ξ|/4)`, both the single-height symbol-positivity horizon
    `A(L) ≤ log(1 + L/4) < L/2` (`zeta_singleHeight_archimedean_schedule_realisable`,
    `resolutionLimit_sdDepth_of_le_sharpHorizonAperture`) and the scale-matched Chebyshev deficit
    schedule `η(L) = 10 + 68 e^L ≥ weilFloorThreshold L (1/2)`
    (`weilFloorThreshold_half_le_chebyshevDeficit`, `resolutionLimit_sdDepth_chebyshevSchedule_eq_half`)
    have exact resolution limit `1/2` and floor `0`.
16. **The numerical unit for the incidence ledger, witness pairs for scalar comb-energy information
    loss, and faithful coherent-residual completions.** On the odd incidence ledger, `fullZeroForm F`
    equals `-ledgerDeficit F r R` (`fullZeroForm_eq_neg_ledgerDeficit`), and eliminating proper prime
    powers bounds `primeSideCharge F` by `combSubcriticalHorizonMass r * autoCorr F 0 + combCharge F r`
    (`primeSideCharge_le_combSubcritical_add_combCharge`, `fullZeroForm_ge_combCharge_ledger`), so a
    graded allocation of `2 * combCharge F r` at rate `2σ` certifies `zetaZeroWidth ≤ σ`
    (`zetaZeroWidth_le_of_combCharge_graded_bound`) while any bounded-aperture ledger reading on
    `GrowthProfile` leaves the shadow rates unbounded above (`ledgerRateDichotomy`). On
    `CombPairingDatum` (`0 < mass`, `0 ≤ energy`, `charge² ≤ mass · energy`), the unsigned scalar
    comb-energy reading `scalarCombEnergyReading` (`(mass, energy)`) is shared by the explicit witness
    triple `antiCoherentWitness`, `orthogonalWitness`, and `coherentWitness`
    (`exists_witness_pair_scalarCombEnergyReading`), giving `combChargeVal` exact resolution interval
    `[−√(mass · energy), √(mass · energy)]` (`resolutionInterval_combChargeVal_scalarCombEnergyReading`)
    and `completeCombEnergy` exact resolution interval
    `[(√mass − √energy)², (√mass + √energy)²]`
    (`resolutionInterval_completeCombEnergy_scalarCombEnergyReading`, collapsing to `[0, 4 * mass]` on
    `energy = mass`, `resolutionInterval_completeCombEnergy_of_balanced`). On actual smooth odd
    compactly supported profiles on `ℝ`, the dilated family `dilatedUnitOddBump c = rescaledTest unitOddBump c`
    (`c > 0`) shares with `unitOddBump` the exact unit mass `1`, asymptotic normalized comb energy `1`,
    exponential comb energy `4`, and cross-prime energy `4`, while realizing every asymptotic
    first-power charge ratio `θ ∈ [0, 1)` (`dilatedUnitOddBump_same_scalar_comb_reading`,
    `exists_dilatedUnitOddBump_witness_for_every_charge_ratio`). Adjoining the signed amplitude ratio
    `amplitudeReading` makes `completedCombReading` faithful for both `combChargeVal` and
    `completeCombEnergy` (`faithful_combChargeVal_completedCombReading`,
    `faithful_completeCombEnergy_completedCombReading`), and subtracting the horizon translate
    `S_r · F(· + 2r)` bounds `combCharge F r²` on `[−r, r]`-supported tests purely by the coherent
    translation-residual energy `‖C_r F − S_r F(· + 2r)‖²`
    (`sq_combCharge_le_mass_mul_horizonResidualEnergy`).

---

## 5. Traps

* **A reading is not a method's conclusion, it is its input.** Floors apply to what the method
  *reads*, not to what it concludes; the identity reading has singleton shadows and limit `I(d)`, but computing or estimating
  that value remains a separate task. Every floor statement must name the reading precisely, and the honest statement of a
  no-go is "no method reading *this* can do better than *that*".
* **Name the unit, and price the mechanism in its own.** A certificate is priced in the width unit,
  where every bounded reading is vacuous; a deficit estimate in the depth unit; an asymptotic claim
  in the rate unit, the only scale-free one; a measurement in the band-ratio unit, where the depth is
  an explicit function of what was measured. A result in one unit does not transfer to another.
* **Boundedness is not the explanation.** The dichotomy is about coordinates: unbounded vertical data
  — the exact ordinate set — determines the scale exactly and still has the trivial limit for the
  depth. What is needed is a reading coupling the two coordinates, or one constant on dilation orbits.
* **Strengthening a blind reading does not help.** More apertures within a bounded range, a larger coercivity gap, or a monotone change of depth
  unit keep the same aperture-certificate obstruction.
  Only three things move it — crossing the Nyquist aperture, reading a magnitude instead of a sign,
  and adding data of a third kind (mass, dilution).
* **A faithful reading is not a proof.** Faithfulness of the unbounded certificate, of the rate
  reading or of the band pair says the data determine the invariant; it does not produce the
  measurement. A recipe says which numbers decide the question, not that they are within reach.
* **Keep the configuration class.** The crystal witnesses carry infinitely many off-line zeros.
  Finite configurations are eventually refuted; a single off-line pair with an on-line background
  obeys a different depth–local-mass bound. These are distinct model classes, not a theorem that
  every bounded-window hiding example needs infinitely many off-line zeros.
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
* **Cofinality requires the right structure.** The rate theorem concerns secant bounds for
  convex profiles. An arbitrary oscillating function can spike between sampled apertures; a
  sparse sample does not control its exponential rate without another theorem.

---

## 6. Questions the theory answers and the tools it builds

### 6.1 Questions

1. **Which lists of observables can decide the sign of the critical arithmetic form?** Exactly the
   readings that move every verdict-changing collapse: unbounded aperture certificates, individual
   prime-power membership, magnitudes past the Nyquist aperture, cofinal rates.
2. **For a reading that cannot decide, what is the best bound it certifies?** Its resolution limit,
   computed exactly from one witness: `½` for every bounded aperture certificate in every unit.
3. **What must be added to a blind reading?** Data of a third kind — local mass, dilution, a measured
   magnitude, individual membership — never more of the same kind.
4. **What does a proposed mechanism cost before it is built?** Its pair `(class of readings, exact
   limit)`, its gate, and its unit.

### 6.2 Tools

Built and reusable:

- *Readings, shadows, collapses* and the `Invisible` closure lemmas; refinement and factorisation
  (`resolves_iff_exists_factorization`, `Resolves.of_refines`, `resolutionLimit_le_of_refines`).
- *Resolution limits, floors and intervals*, with the floor theorem.
- *Witness families*: off-line and on-line lattices, crystals, dilution, the node collapses, the
  parity pairs imported from their owners.
- *Band recipes*: two-band and three-band depth inversion, the precision budget, the reach law.
- *Rate readings* on cofinal and bounded aperture sets.
- *Pronic Gram readings* in the cross-scale exponent unit `θ = 2 log P / log X`, their exact limit `2`
  under sign-blind Type-II and rank-two readout readings, the smoothness ladder `2K/(K+1)` with
  deficit `2/(K+1)`, and the faithful single-modulus completions (`residueMass`, `kernelStatistic`).
- *Two-aperture ratios for `ζ`* (`zetaTwoApertureRatio`, `zetaClampedTwoApertureRatio`,
  `primeWindowTwoApertureRatio`) with critical value `1` on the line, `2σ`-abscissa inversion, and
  unconditional bounds across `[0, 21/200]`, `[0, 3/10]`, and `(0, ½ log 2)`.
- *Fatality–neutrality calculus for parity collapses* (`StrictlyFatalAt`, `PairFatalAt`, `NeutralAt`),
  the odd/even pole classification of `evenFlip`, cubic-moment orbit reduction
  (`cubicMomentReading`), and the `(1/4, 3/4)` residue-class complementation window.
- *Rate readings for `ζ` and the local-count price* (`five_rate_currencies_of_zeta`,
  `singleApertureWidthFloor`, `ApertureCountDatum`, `ZetaRateDatum`, `cofinalRateSet`,
  `boundedRateSet`).
- *Diluted-counterexample design calculus* (`bandEnergy_eq_sum_cosh_sub_one`,
  `bandEnergy_strictMono_depth`, `dilutedReading_iff_bandEnergy_le`,
  `resolutionLimit_depth_dilutedReading_secondBand`, `resolutionLimit_depth_dilutedReading_brackets`,
  `W_dilutedLattice_lag_nat_mul`, `W_dilutedLattice_lag_eq_of_gap`,
  `counterexample_primeSide_obstructions`).
- *Adaptive policy calculus across growing density* (`scaleAdaptiveReading`, `TransNyquistPolicy`,
  `resolutionLimit_sdDepth_adaptiveReading_of_exists_subNyquist`,
  `resolutionLimit_sdDepth_scaleAdaptiveReading_scaleMatched`,
  `resolutionLimit_sdDepth_adaptiveReading_scaleMatched`, `certifies_sdDepth_adaptiveReading_iff`,
  `depth_le_div_sub_one_of_bandEnergy_le`, `resolutionLimit_sdDepth_scaleAdaptiveReading_brackets`,
  `certifies_sdDepth_adaptiveReading_transNyquist_iff`,
  `zeta_singleHeight_archimedean_schedule_realisable`,
  `resolutionLimit_sdDepth_chebyshevSchedule_eq_half`).
- *Incidence-ledger admissibility unit and comb-energy completion calculus* (`ledgerDeficit`,
  `primeSideCharge_le_combSubcritical_add_combCharge`, `zetaZeroWidth_le_of_combCharge_graded_bound`,
  `CombPairingDatum`, `scalarCombEnergyReading`, `exists_witness_pair_scalarCombEnergyReading`,
  `resolutionInterval_combChargeVal_scalarCombEnergyReading`,
  `resolutionInterval_completeCombEnergy_scalarCombEnergyReading`,
  `exists_dilatedUnitOddBump_witness_for_every_charge_ratio`, `completedCombReading`,
  `faithful_combChargeVal_completedCombReading`, `sq_combCharge_le_mass_mul_horizonResidualEnergy`).

---

## 7. Open problems

Open, in this programme's own unit (a class of readings and its exact limit):

1. *(Resolved in `TheExactFloorOfThePronicGramReading`.)* **The exact floor of the Gram reading.**
   In the cross-scale exponent unit `θ = 2 log P / log X ∈ [0, 2]`, the sign-blind Type-II Gram
   reading and the rank-two readout reading `(R, H)` have exact resolution limit `2`, floor `0`, and
   interval `[0, 2]`, witnessed by the coherent prime block (`exists_primeBlock_witness_at_resolutionLimit_two`)
   and the three-window readout-free barrier (`exists_readout_free_witness_at_resolutionLimit_two`).
   Difference smoothness of order `K` certifies `2K/(K + 1)` with unresolved deficit limit `2/(K + 1)`,
   `residueMass` is faithful for `bernoulliCrossScaleMain`, `kernelStatistic` bounds the shadow
   diameter by the fourth-order tail, and `centredPrimeRow` bypasses the worst-case Type-II shadow
   across `7/6 < θ < 2`.
2. *(Resolved in `TheBandRecipeForZeta`.)* **The band recipe for `ζ`.** For any base aperture
   `A₀ ≤ 21/200` (`μ(A₀) ≥ 1/30 > 0`), the two-aperture ratio
   `zetaTwoApertureRatio A₀ A = (μ(A₀) − μ(A))/μ(A₀)` and its explicit-formula prime-window companion
   `primeWindowTwoApertureRatio A₀ w v` have critical value `1` on the critical line
   (`riemannHypothesis_iff_forall_zetaTwoApertureRatio_le_one`,
   `riemannHypothesis_iff_tendsto_zetaTwoApertureRatio_one`,
   `riemannHypothesis_iff_forall_zetaClampedTwoApertureRatio_eq_one`), invert `2σ`-exponential growth
   unconditionally into `|Re ρ − ½| ≤ σ` (`abs_re_sub_half_le_of_zetaTwoApertureRatio_le_one_add_exp`),
   detect near-top zeros above `1` beyond their visibility lag (`one_lt_zetaTwoApertureRatio_of_near_top_zero`),
   and satisfy unconditional bounds on `[0, 21/200]`, `[0, 3/10]`, and `(0, ½ log 2)`.
3. *(Resolved in `TheFatalityClassificationOfParityCollapses`.)* **A fatality classification for the
   parity collapses.** Across the three parity-collapse families, strict fatality (`StrictlyFatalAt`)
   and neutrality (`NeutralAt`) are completely classified:
   (i) on four-free convolutions `k ⋆ o_ε` (`0 < ε ≤ 1/2`), `evenFlip` is strictly fatal iff
   `poleValue k J ε = 0 ∧ poleValue (evenPartWeight k) J ε ≠ 0`
   (`strictlyFatalAt_evenFlip_iff_pole_and_evenPart`), paid and neutral iff both `oddPartKernel k`
   and `evenPartWeight k` vanish at `1 − ε` (`evenFlip_paid_and_neutral_iff_odd_and_even_pole`),
   and killed by adjoining `firstPronicMoment` whenever `weightRamanujanCoeff c 2 ≠ 0`
   (`not_mem_shadow_joinReading_firstPronicMoment_iff`) or by the logarithmic pronic moments on the
   generalized Fermi locus (`exists_logMoment_ne_of_strictlyFatalAt_evenFlip`);
   (ii) on the `2^{N−1}` Selberg sign-character shadow of `completePeriodLagReading N`, refining by
   `cubicMomentReading N` pins odd-supported rows uniquely (`cubicMomentReading_pins_odd_signOrbit`)
   and reduces squarefree-supported rows to at most `{c, evenFlipRow N c}`
   (`cubicMomentReading_reduces_squarefree_signOrbit_to_evenFlip`);
   (iii) on half-damped residue-class prime flips `residueFlipHalfWeight q S`, every complement pair
   `{S, Sᶜ}` has at least one paid member (`receiverBounded_residueFlip_or_compl_half`),
   complementation is paid and neutral iff `φ(q) < 4 |S^\times| < 3 φ(q)`
   (`both_residueFlip_and_compl_paid_iff`), and strictly fatal iff `3 φ(q) ≤ 4 |S^\times|`
   (`strictlyFatalAt_compl_residueFlip_half_iff`), with subgroup flips `subgroupFlipSet H` neutral at
   index `2, 3` and strictly fatal iff the index is at least `4`
   (`strictlyFatalAt_compl_subgroupFlipSet_iff`).
4. *(Resolved in `TheRateReadingForZeta`.)* **The rate reading for `ζ`.** The four rate currencies
   (dyadic prime-window lag rate, Chebyshev deficit rate, mean-square band rate, and Möbius receiver
   damping rate) equal `zetaZeroWidth` unconditionally, while `polarGroundEnergyRate` equals
   `zetaZeroWidth` under `OffLineCopiesLocallyBounded M` or `OffLineDepthLocallyBounded W`
   (`five_rate_currencies_of_zeta`). At a single aperture `A`, adjoining the local count `M` to a
   ground-energy deficit `η > 0` lifts the width resolution floor from `0`
   (`resolutionFloor_width_deficitOnly_eq_zero`) to `max 0 (singleApertureWidthFloor M A η)`
   (`singleApertureWidthFloor_le_zetaZeroWidth`, `le_resolutionFloor_width_deficitAndCount`).
   In the asymptotic rate space `ZetaRateDatum`, adjoining `locallyBounded` collapses the resolution
   interval of `polarRate` under `width` from `[width, 1/2]` to `{width}`
   (`resolutionInterval_polarRate_widthOnly`, `resolutionLimit_polarRate_widthAndLocalCount`) and
   lifts the resolution floor of `width` under `polarRate` from `0` to `polarRate`
   (`resolutionFloor_width_polarRateOnly_eq_zero`, `resolutionFloor_width_polarRateAndLocalCount`).
   On the lattice family `ScaleDepthDatum`, `cofinalRateSet S` is faithful for `sdDepth`
   (`faithful_sdDepth_cofinalRateSet`), whereas `boundedRateSet M` has exact limit `1/2` and floor
   `0` (`resolutionLimit_sdDepth_boundedRateSet_eq_half`,
   `resolutionFloor_sdDepth_boundedRateSet_eq_zero`).
5. *(Resolved in `TheDesignSpecificationOfACounterexample`.)* **The design specification of a
   counterexample.** Symmetrising `centredSum` under `Fin.revPerm` gives the hyperbolic decomposition
   `bandEnergy ℓ δ n = ℓ ∑_{j=0}^{n−1} (cosh(δℓ(2j − n + 1)) − 1)` (`bandEnergy_eq_sum_cosh_sub_one`),
   strictly increasing in `n ≥ 1` (`bandEnergy_lt_succ`) and in `δ > 0` for `n ≥ 2`
   (`bandEnergy_strictMono_depth`). Consequently, for `0 < a ≤ L/2`, `dilutedReading hℓ hL a` is
   equivalent to `bandEnergy ℓ (depth d) ⌈2a/ℓ⌉₊ ≤ 2L` (`dilutedReading_iff_bandEnergy_le`), has
   exact resolution floor `0` (`resolutionFloor_depth_dilutedReading`), has exact limit `1/2` below
   the sub-lattice Nyquist aperture `a ≤ ℓ/2` (`resolutionLimit_depth_dilutedReading_subNyquist`),
   has exact limit `min (1/2) (depthResolution ℓ (2L))` across the second aliasing band
   `ℓ/2 < a ≤ min ℓ (L/2)` (`resolutionLimit_depth_dilutedReading_secondBand`), and is bracketed at
   every `ℓ/2 < a ≤ L/2` between `min (1/2) (arcosh(1 + 2L/(ℓ⌈2a/ℓ⌉₊))/(⌈2a/ℓ⌉₊ℓ))` and
   `min (1/2) (log((2L + 2a + ℓ)/ℓ)/(2a − ℓ))` (`resolutionLimit_depth_dilutedReading_brackets`).
   On the lag axis, a two-bump difference test `twoBump (modScaledBump w 0) v (−1)` on
   `dilutedLatticeConfig` evaluates at the `n`-th sub-lattice tooth `v = nℓ` (`nℓ + 2w ≤ L`) to
   `4(L − ℓ(cosh(nδℓ) − 1))‖κ_w‖²` (`W_dilutedLattice_lag_nat_mul`) — reading `-2 · bandDeficit ℓ δ L 2`
   and `-2 · bandDeficit ℓ δ L 3` at the first two teeth (`re_W_dilutedLattice_first_two_teeth_eq_bandDeficit`)
   — while evaluating to `4(L + ℓ)‖κ_w‖² > 0` in every gap `|v − nℓ| > 2w`
   (`W_dilutedLattice_lag_eq_of_gap`). Against the prime-side explicit formula, any structured
   counterexample must simultaneously respect the `3/10` prime-free barrier, the unbounded zero-count
   remainder `rvmRemainder_unbounded`, and polylogarithmic near-top prime-window negativity
   (`counterexample_primeSide_obstructions`).
6. *(Resolved in `PoliciesForAConfigurationOfGrowingDensity`.)* **Policies for a configuration of
   growing density.** On `ScaleDepthDatum`, any policy `adaptiveReading A η` with even one sub-Nyquist
   scale `A(L) ≤ L/2` (`0 ≤ η(L)`) — in particular any bounded aperture schedule — has exact global
   resolution limit `1/2`, floor `0`, and interval `[0, 1/2]`
   (`resolutionLimit_sdDepth_adaptiveReading_of_exists_subNyquist`,
   `resolutionLimit_sdDepth_adaptiveReading_of_bddAbove`). Under `ScaleMatched A η` (`L/2 < A(L) ≤ L`),
   `scaleAdaptiveReading A η` at scale `L` has exact limit `min (1/2) (depthResolution L (η L))` and
   floor `0` (`resolutionLimit_sdDepth_scaleAdaptiveReading_scaleMatched`), `adaptiveReading A η` has
   global limit `sSup ((fun L => min (1/2) (depthResolution L (η L))) '' Ioi 0)` and floor `0`
   (`resolutionLimit_sdDepth_adaptiveReading_scaleMatched`), and certifying `β ∈ (0, 1/2)` is
   equivalent to `∀ L > 0, η L ≤ weilFloorThreshold L β` (`certifies_sdDepth_adaptiveReading_iff`),
   with `depthResolution L (η L) → 0` whenever `η L / L³ → 0`
   (`tendsto_depthResolution_zero_of_div_cube_tendsto_zero`). For arbitrary trans-Nyquist aperture
   growth `TransNyquistPolicy A η` (`A(L) > L/2`, `aliasingIndex A L = ⌈2A(L)/L⌉₊ ≥ 2`),
   `adaptiveReading A η p ↔ bandEnergy (sdScale p) (sdDepth p) (aliasingIndex A (sdScale p)) ≤ η (sdScale p)`
   (`adaptiveReading_iff_bandEnergy_le`), `bandEnergy L δ n ≥ weilFloorThreshold L ((n − 1)δ)` yields
   multi-band depth inversion `δ ≤ depthResolution L η / (n − 1)`
   (`weilFloorThreshold_mul_le_bandEnergy`, `depth_le_div_sub_one_of_bandEnergy_le`),
   `scaleAdaptiveReading A η` is bracketed between `min (1/2) (arcosh(1 + η(L)/(L · n_L))/(n_L L))`
   and `min (1/2) (depthResolution L (η L) / (n_L − 1))`
   (`resolutionLimit_sdDepth_scaleAdaptiveReading_brackets`), and global certification of `β ∈ (0, 1/2)`
   is equivalent to `∀ L > 0, η L ≤ bandEnergy L β (aliasingIndex A L)`
   (`certifies_sdDepth_adaptiveReading_transNyquist_iff`). Against `ζ`'s growing zero density at height
   scale `L(ξ) = log(1 + π|ξ|/4)`, both the single-height symbol-positivity horizon
   `A(L) ≤ log(1 + L/4) < L/2` (`zeta_singleHeight_archimedean_schedule_realisable`,
   `resolutionLimit_sdDepth_of_le_sharpHorizonAperture`) and the scale-matched Chebyshev deficit
   schedule `η(L) = 10 + 68 e^L ≥ weilFloorThreshold L (1/2)`
   (`weilFloorThreshold_half_le_chebyshevDeficit`, `resolutionLimit_sdDepth_chebyshevSchedule_eq_half`)
   have exact resolution limit `1/2` and floor `0`.
7. *(Resolved in `TheNumericalUnitForTheIncidenceLedger`.)* **A numerical unit for the incidence
   ledger.** On the odd incidence ledger, `fullZeroForm F = −ledgerDeficit F r R`
   (`fullZeroForm_eq_neg_ledgerDeficit`), and eliminating proper prime powers bounds
   `primeSideCharge F` by `combSubcriticalHorizonMass r * autoCorr F 0 + combCharge F r`
   (`primeSideCharge_le_combSubcritical_add_combCharge`, `fullZeroForm_ge_combCharge_ledger`), so a
   graded allocation of `2 * combCharge F r` at rate `2σ` certifies `zetaZeroWidth ≤ σ`
   (`zetaZeroWidth_le_of_combCharge_graded_bound`) while any bounded-aperture ledger reading on
   `GrowthProfile` leaves the shadow rates unbounded above (`ledgerRateDichotomy`). On
   `CombPairingDatum`, the unsigned scalar comb-energy reading `scalarCombEnergyReading` (`(mass, energy)`)
   admits the explicit witness triple `antiCoherentWitness`, `orthogonalWitness`, and
   `coherentWitness` with identical `(mass, energy)` and charges `−√(M E) < 0 < +√(M E)`
   (`exists_witness_pair_scalarCombEnergyReading`), giving `combChargeVal` exact resolution interval
   `[−√(M E), √(M E)]` (`resolutionInterval_combChargeVal_scalarCombEnergyReading`) and
   `completeCombEnergy` exact resolution interval `[(√M − √E)², (√M + √E)²]`
   (`resolutionInterval_completeCombEnergy_scalarCombEnergyReading`, `[0, 4M]` when `E = M`). Across
   actual smooth odd compactly supported profiles on `ℝ`, `dilatedUnitOddBump c = rescaledTest unitOddBump c`
   (`c > 0`) shares with `unitOddBump` the exact unit mass `1`, asymptotic normalized comb energy `1`,
   exponential comb energy `4`, and cross-prime energy `4`, while realizing every asymptotic
   first-power charge ratio `θ ∈ [0, 1)` (`dilatedUnitOddBump_same_scalar_comb_reading`,
   `exists_dilatedUnitOddBump_witness_for_every_charge_ratio`). Adjoining the signed amplitude ratio
   `amplitudeReading` makes `completedCombReading` faithful for both `combChargeVal` and
   `completeCombEnergy` (`faithful_combChargeVal_completedCombReading`,
   `faithful_completeCombEnergy_completedCombReading`), and subtracting the horizon translate
   `S_r · F(· + 2r)` bounds `combCharge F r²` on `[−r, r]`-supported tests purely by the coherent
   translation-residual energy `‖C_r F − S_r F(· + 2r)‖²`
   (`sq_combCharge_le_mass_mul_horizonResidualEnergy`).

### Research topics

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
  lag rate on the lag face, the damping threshold on the receiver face. The lag rate and damping threshold equal the width; equality for the `L²` ground-energy rate
  has the additional local-count qualification described above,
  and all three are tail invariants, hence blind to every bounded parameter range — a floor theorem
  for rate readings would unify the three gates into one.
* Prove the trichotomy of §5 as a theorem about readings. A blind reading is improved only by
  crossing the Nyquist aperture, reading a magnitude, or adding data of a third kind. Stated for
  orientation-faithful readings (Arithmetic Orientation Theory), it would say that every reading
  separating the critical form from its companion does one of the three. The precision cost of
  each branch should come with it, as the square-root law does for the magnitude branch.

---

## 8. Working in the theory

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
