# Arithmetic Continuation and Critical Energy (`GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy`)

**One question.** A critical energy of an exact arithmetic source is finite at one end of a
parameter range — at half damping, at a finite cutoff, at a bounded aperture — and the Riemann
Hypothesis is the statement that it stays finite as the parameter runs to the critical end. Which
*arithmetic identities* prevent the energy from escaping on the way, and what exactly must be
estimated to use them?

Arithmetic continuation and critical energy (ACCE) is a theory of *transport in a parameter*.
Where the incidence, lag and aperture faces of the critical form each ask for a sign at a fixed
parameter, ACCE asks for the derivative: how much energy can the family lose per unit of parameter,
measured through a scale, and what pays that loss. Its objects carry two indices at once — a
continuous parameter and an observation horizon — and its only currency is a bound uniform in the
horizon. Every statement here is unconditional, names the parameter interval it concerns, and keeps
the horizon quantifier where the mathematics puts it.

---

## The shared target: the sign of the critical arithmetic form

Eight programmes of this corpus work on one object. The Riemann Hypothesis is the nonnegativity of
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

**Why one theory.** Each existing layer stops where the corpus proves it stops. Sieve and bilinear
methods see the additive structure of `ℕ` only after averaging over a family, and below half
damping no sign-blind datum decides the receiver. Multiplicative, spectral and explicit-formula
methods hold verbatim for Beurling systems with off-line zeros. Dirichlet-form and criticality
identities hold for every even positive kernel, and positivity on restricted families is paid by an
archimedean gain that is absent on the RH-complete cone. A closing theorem must at once see both
operations of `ℕ` at a single modulus, carry a sign structure (one negative square, the pole plane,
the signs of the Möbius row), and be resolved at the zero spacing, at square-root precision at every
scale. No existing field has its basic objects built with all three; the eight programmes build
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

**Criteria every contribution to the shared target must meet.**

- *Selectivity.* State what the result gives for `ζ(s−a)ζ(s+a)`, for a Beurling system with an
  off-line zero, and for the Liouville-twisted weight; a statement surviving all three is not
  about RH (test models: `BiScaleUncertainty`).
- *No family average.* One character, modulus one, shift zero.
- *Square-root precision beyond the diagonal.* Prime sums of length at least the height,
  controlled beyond the mean-value regime: one inequality per window at every scale on the lag
  family, `θ = 2` on the Gram.
- *Every scale, not almost every.* A statement about an exceptional set, a proportion or a typical
  member is infrastructure (the every-height problem: `SquareRootThreshold`).
- *Node criticality.* The mechanism distinguishes `log 4` from `log 6`; sampling-density and
  generic uncertainty arguments are excluded in advance.
- *Signs read.* Below half damping the mechanism uses first-order data at prime moduli or
  odd-degree additive moments; magnitude, two-point and translated-moment data are blind, since the
  parity pairs exist at every damping `ε ≤ 1/2`.
- *Complete expression, no margin, no archimedean subsidy.* Mean, diagonal, mixed terms, Gamma and
  polar charges, endpoints and history are retained; a gain of size `log(1/w)` or `log M` at the
  archimedean place against a bounded prime cost is nonselective by construction.
- *Units.* Positivity is measured by the aperture `A` or the support through which the inequality
  holds for all profiles; cancellation by the exponent `θ` obtained or the lag `V` beyond which
  `P_v ≥ 0` is proved; localization by the depth `δ(n, R)` excluded below height `T(n, R)` and by
  the visibility lag `V₀(w, η, δ₀)`; damping by the smallest `ε` at which the receiver is bounded.
  Identities, finite classifications and nonselective positivity count as zero in these units.
- *Calibration.* Reproduce the corresponding theorem over `F_q[T]`, or say why it cannot be done
  (`BiScaleUncertainty`).
- *Pairs.* Every invisibility theorem comes with a visibility witness, every identity with the
  estimate it enables or the sharp boundary it proves, every obstruction with its replacement
  hypothesis proved sufficient.

### This programme's role

ACCE is the continuation layer. It owns the parameter derivative of the critical energies that the
other programmes build, the theorems that transport a bound along a parameter interval, and the
countermodels that fix which uniformity a transport theorem must have. Its results are not another
equivalent form of the shared target; they change what has to be estimated. Where the receiver
criteria of `RHTower` and `BezoutValuationIncidence` ask for a bound on a norm at every damping,
ACCE reduces the same conclusion to a bound on the negative part of one signed pairing on each
compact damping interval — a weaker demand, provably weaker, and with the endpoint supplied
unconditionally by Littlewood's bound.

In the shared units its contribution is measured by the damping it reaches: a continuation budget
available only above `a₀` already gives the zero-free strip `Θ ≤ ½ + a₀`
(`zetaZeroAbscissa_le_half_add_of_partial_dampingContinuation`), so partial progress is an
explicit exponent and not an identity. Identities, scale changes and ratio limits count as zero in
those units; what counts is a horizon-free budget on an interval, and the interval it covers.

### How the programme connects to the other programmes

- **Bézout–Valuation Incidence (`BezoutValuationIncidence`).** ACCE takes the damping tangent law
  `hasDerivAt_pmPowerDampedCenteredDivisorPrefix` (`∂_ε A_ε(n) = E_ε(n)`, the centred damped
  Chebyshev function), the pronic norm with its Cauchy–Schwarz and Minkowski inequalities, the
  Markov form of the energy derivative (`hasDerivAt_pmPowerDampedDivisorDiscreteEnergy_markov`:
  boundary flux minus jump energy minus density forcing), and the Littlewood endpoint
  `mem_receiverDampings_of_half_zetaZeroAbscissa_lt`. It gives back the signed-work form of the
  same derivative, the bridge identifying the two faces
  (`two_mul_signedDampingWork_eq_markov`), and the theorem that the tangent-norm receiver
  `riemannHypothesis_of_integrable_tangent_energy` is the special case of a continuation budget in
  which the budget dominates a norm. Shared object: the centred prefix `A_ε` of the power-damped
  Möbius row and its pronic energy.
- **RHTower routes.** ACCE takes the admission dictionary: `receiverDampings`, the rate identity
  `receiverDampingRate = Θ − ½`, the cofinal criterion `riemannHypothesis_iff_cofinal_budget`, the
  unconditional endpoint at half damping, and the accumulation theorems
  `re_le_of_Ioo_subset_receiverDampings`, `zetaZeroAbscissa_le_of_accPt_receiverDampings` that turn
  an interval of admitted dampings into a zero-free strip. It gives back the continuation criteria
  and the statement of what their failure costs. Shared object: the admissible damping set.
- **Trans-Horizon Incidence Mechanics (`TransHorizonIncidenceMechanics`).** THIM owns the
  observation side: which maps from source to data are injective, and the parity partners that make
  magnitude, two-point and translated-moment data blind below half damping. ACCE supplies the
  reason injectivity is not enough — an observation map must come with a stability estimate in the
  receiver's norm before it can bound an energy — and takes from THIM the explicit
  indistinguishability classes against which a continuation estimate must be selective. Shared
  object: the receiver row and the data that determine it.
- **Square-Root Threshold (`SquareRootThreshold`).** SRT owns the width dictionary and the ground
  energy at an aperture, including the comparison of the zero width with the ground-energy rate
  under non-clustering of off-line zeros. ACCE's parameter is the aperture there rather than the
  damping, and the same transport theorems apply verbatim: an aperture-indexed family with a
  coercive scale and a horizon-free budget cannot lose a finite ground energy over a bounded
  aperture range. Shared object: the rate of a critical energy in its parameter.
- **Arithmetic Criticality Theory (`ArithmeticCriticalityTheory`) and Arithmetic Positivity Theory
  (`arithmetic-positivity-theory`).** These own the aperture face of the form and its gauges. ACCE
  takes from them the exact complete quadratic form with its mixed terms, and gives the discipline
  that a decomposition is useful only with its interaction terms attached, together with the
  envelope tools for iterating a per-stage compensation (`affineEnvelope`,
  `affineEnvelope_le_of_contraction`). Shared object: the complete signed quadratic form.
- **Arithmetic Incidence Positivity (`ArithmeticIncidencePositivity`).** AIP works pair by pair at
  one aperture; ACCE works interval by interval in the aperture. The two meet at the point where
  AIP's window inequality must be extended past a prime: the extension is a continuation statement
  in the aperture, and the affine envelope says what a per-prime gain must be to survive
  iteration. Shared object: the aperture at which a positivity certificate still holds.
- **Bi-Scale Uncertainty (`BiScaleUncertainty`).** BiScale owns the test models — shifted zeta
  pairs, altered prime weights, Beurling systems — and the node criticality that excludes
  sampling-density arguments. Every continuation estimate proposed here must fail for a named
  member of those families, and BiScale's signed prime-polar work bounds are the second instance of
  the signed-work mechanism. Shared object: the selectivity certificate.

ACCE imports `RHTower` and `BezoutValuationIncidence` and is imported by no other programme: it is
a leaf that strengthens the criteria the others produce.

## 1. Why: motivation

The corpus proves many equivalent forms of the Riemann Hypothesis and many sharp statements about
why the surveyed methods stop. Three of those obstructions bear directly on the choice made here.

- A change of receiver coordinates is not an improved arithmetic bound. Width dictionaries convert
  one unknown rate into another; they never produce an estimate for the source.
- A bounded aperture cannot decide an arbitrary configuration. A certificate at finite aperture is
  progress in the aperture, not in the conclusion.
- Below half damping no sign-blind datum controls the receiver. Magnitudes, unsigned majorants,
  two-point data and stationary translated moments are shared with parity partners at every damping
  `ε ≤ ½`, so any estimate that uses only such data proves nothing about `ζ`.

What those obstructions leave open is a *quantitative* statement about the actual signed source.
The damped Möbius critical energy makes the gap explicit. With

`c_ε(d) = μ(d) d^{-ε}`,  `A_ε(n) = Σ_{d ≤ n} c_ε(d) ⌊n/d⌋ − n·Re(1/ζ(1+ε))`,
`E_T(ε) = Σ_{n ≤ T} A_ε(n)² / (n(n+1))`,

the family is admitted at every `ε ≥ ½` unconditionally, admission at dampings accumulating at `0`
is exactly RH, and the infimum of the accumulation points of the admitted dampings is exactly the
zero width `Θ − ½`. So RH is not an inequality at a single damping. It is the question whether a
finite energy *survives transport* from an admitted endpoint down to zero damping.

That reframing is the reason for a separate programme. A transport theorem does not need a bound at
the critical end, which is where every estimate fails; it needs a bound on the rate of loss on each
compact interval away from the critical end, where the family is smooth and the arithmetic is
explicit. The analytic demand changes shape in two ways. It starts from a known finite state instead
of trying to enter the critical norm from the singular end. And it asks only for the
*energy-increasing part* of the derivative when moving backwards: large tangential motion is free.

The same reframing applies to the other two parameters. Removing a coefficient cutoff and growing an
aperture are continuations in exactly the same sense, and the transport theorems here are stated for
an arbitrary parameter so that they can be instantiated in all three.

## 2. What: objects and language

**Energy families.** An energy family is a function `E : ℝ → ℕ → ℝ` of a continuous parameter and a
discrete observation horizon. Three graded notions of success are kept apart, because conflating
them is the standard error (`CriticalEnergyFamilies`):

- `Admits E ε` — `∃ B, ∀ T, E ε T ≤ B`. One bound at one parameter, uniform in the horizon. The
  quantifier order is the content: `∀ T, ∃ B` is free and says nothing.
- `CofinallyAdmits E` — admission at parameters arbitrarily close to `0`, each with its own bound.
  No bound uniform in the parameter is asked for.
- `UniformlyAdmitsOn E s` — one bound for the whole parameter set. Strictly stronger than admission
  at each of its points.

**The critical energy of record** is `dampedMobiusEnergy = pmPowerDampedDivisorDiscreteEnergy`
(`TheDampedMobiusCriticalEnergy`). Its source is fixed before any closure: every coefficient, the
exact pole subtraction `n·Re(1/ζ(1+ε))` and the pronic observation weight `1/(n(n+1))` are named,
and nothing is selected from the zeros. Two dictionary entries fix what continuation must deliver:
`mem_receiverDampings_iff_admits` (admission is membership in the admissible damping set) and
`riemannHypothesis_iff_cofinallyAdmits` (cofinal admission is RH).

**The complete signed work** is

`W_T(ε) = Σ_{n ≤ T} A_ε(n) · E_ε(n) / (n(n+1))`,  `E_ε(n) = ∂_ε A_ε(n)`,

the pronic pairing of the centred source with its own damping tangent (`signedDampingWork`). It is
one signed number. It is not a norm, not a sum of absolute cross terms, and not an energy with the
pole correction deleted.

**A continuation budget** on `[a, c]` is a primitive `β` — *the same function for every horizon* —
whose derivative dominates the loss:

`−E'_T(ε) ≤ β'(ε) · (1 + E_T(ε))` for all `T` and all `ε ∈ [a, c]`

(`LinearContinuation`). Its nonlinear form replaces `1 + E` by a growth function `Φ` and asks for a
*scale* `Ψ` with `Ψ' = 1/Φ` that is coercive on `[0, ∞)` (`OsgoodContinuation`). Coercivity is the
Osgood condition `∫^∞ du/Φ(u) = ∞` in the form actually used: a bound on `Ψ ∘ E` must return a
bound on `E`.

**Vocabulary.** The following words are used only with the content listed beside them.

| Term | Meaning that must accompany it |
|---|---|
| Admission | finiteness of a named complete norm, with its quantified parameters |
| Continuation | propagation of admission through a parameter interval, with a stated bound |
| Compensation | a bound on a combined signed expression, not smallness of its separate terms |
| Observation | a specified map from source to data, together with its indistinguishability class |
| Stability | a quantitative estimate in the norm the receiver requires |
| Completion | a specified topology, and a theorem saying which source, pole and sign data survive |
| Selectivity | a proved reason the estimate holds for the actual source and fails for a named model |

These are not new axioms. They specify what a theorem in this programme has to say. The available
algebraic identities — `μ * 1 = δ₁`, `Λ * 1 = log`, the exact tangent law, the explicit formula —
are starting facts. Global positivity, small-damping admission, purity and the zero width remain
conclusions.

## 3. How: mechanisms

### The master inequality

Everything rests on one monotonicity statement (`scaledEnergy_add_budget_le`). Along `[a, c]`, if

`0 ≤ ψ(ε) · E'_T(ε) + β'(ε)`,

that is, if the energy read through the scale loses no faster than the budget pays, then
`Ψ ∘ E_T + β` is nondecreasing, hence

`Ψ(E_T(a)) ≤ Ψ(E_T(c)) + (β(c) − β(a))`.

The derivative of the scale is indexed by the parameter rather than by the value, which keeps the
hypothesis pointwise and avoids demanding differentiability of `Ψ` off the range of the energy.

### Linear transport and coercive transport

With `Ψ = log(1 + ·)` the master inequality becomes the Grönwall form
(`one_add_le_mul_exp_of_linear_work`)

`1 + E_T(a) ≤ (1 + E_T(c)) · exp(β(c) − β(a))`,

whose right side contains no horizon. `Admits.of_linearContinuation` turns that into the transport
theorem: a budget on `[a, c]` plus admission at `c` is admission at `a`, with bound
`(1 + max B 0)·exp(β(c) − β(a)) − 1`. For a general scale the same step gives a bound on `Ψ ∘ E`,
and `bddAbove_of_tendsto_atTop` converts it back into a bound on `E` — the only place coercivity is
used (`Admits.of_osgoodContinuation`). `cofinallyAdmits_of_linearContinuation` and its Osgood twin
package the result over all compact subintervals; the budget may deteriorate arbitrarily fast as the
left endpoint approaches `0`.

### The exact derivative, in two faces

The damping derivative of the critical energy is twice the complete signed work
(`hasDerivAt_dampedMobiusEnergy`):

`∂_ε E_T(ε) = 2 W_T(ε)`.

The same derivative has a Markov face owned by `BezoutValuationIncidence`: boundary flux minus
nonnegative jump energy minus density forcing. Uniqueness of derivatives identifies the two
(`two_mul_signedDampingWork_eq_markov`), so the signed work may be attacked from either side. One
consequence is immediate and sobering: since the jump energy is nonnegative and enters `−2W` with a
`+` sign, a continuation budget must dominate the dissipation of the arithmetic chain
(`arithmeticDampingTotalJumpEnergy_le_of_continuation_bound`). Dissipation helps the forward
direction and obstructs the backward one.

### Subsumption of the tangent-norm receiver

Cauchy–Schwarz in the pronic norm and the elementary `2√E ≤ 1 + E` give
(`neg_two_mul_signedDampingWork_le_of_tangentNorm_le`)

`−2 W_T(ε) ≤ g(ε) · (1 + E_T(ε))` whenever `‖E_ε‖_T ≤ g(ε)` for every horizon.

So a horizon-uniform bound on the pronic norm of the damped Chebyshev tangent *is* a continuation
budget (`dampingContinuation_of_tangentNorm_le`), and the owned tangent-norm criterion reappears as
the special case in which the budget happens to dominate a norm
(`riemannHypothesis_of_tangentNorm_primitive`). Nothing is lost by passing to the signed form.

### The endpoint, and how short the interval is

Any admitted damping serves as the endpoint (`riemannHypothesis_of_dampingContinuation_endpoint`).
Half damping is unconditional, and Littlewood's bound on the Mertens function admits every damping
above `Θ/2`, so the interval the continuation has to cross is `(0, Θ/2]` rather than `(0, ½]`
(`riemannHypothesis_of_dampingContinuation_above_half_abscissa`). Any improvement of the
unconditional endpoint shortens the obligation.

### Partial continuation is already a theorem

A budget available only on `[a, c]` for `a` in `(a₀, c]` makes every damping of `(a₀, c)` admitted,
so the admitted dampings accumulate at `a₀` and the zero abscissa obeys
(`zetaZeroAbscissa_le_half_add_of_partial_dampingContinuation`)

`Θ ≤ ½ + a₀`.

This is the programme's non-RH deliverable, and it is a genuine zero-free strip measured in the
shared units, not a change of coordinates.

### A superlinear scale

The double logarithm `Ψ(u) = log(1 + log(1 + u))` is increasing and coercive on `[0, ∞)`, so the
permitted loss may be `Φ(u) = (1 + u)(1 + log(1 + u))`, superlinear in the energy
(`SuperlinearOsgoodScale`). The resulting criterion
`riemannHypothesis_of_superlinear_dampingContinuation` is strictly weaker than the linear one: the
arithmetic estimate may lose an extra logarithm of the energy at every damping and still suffice.

### The mirror form: no crossing of a ground floor

On the aperture side the question is mirrored: a ground floor must not reach zero as the aperture
grows. Read through `Ψ = log` on a positive floor the master inequality becomes
(`floor_le_of_relative_decay`)

`−μ'(A) ≤ β'(A) · μ(A)` on `[a, c]`  ⟹  `μ(c) ≥ μ(a) · exp(−(β(c) − β(a)))`,

a bound on the *relative* decay, not on the decay. Under a budget with nonnegative derivative the
same explicit positive bound holds uniformly on the interval
(`floor_le_of_relative_decay_Ico`), so a first crossing forces the relative decay to exceed every
budget of finite total on the interval leading to it. This is the no-crossing law of the shared
target's mechanism 3, stated as an estimate rather than as a sign.

### What is already paid, and what is not

The signed work splits, and only one half of it is open.

Subtracting the constant source is a renormalisation that changes the signed work by a scalar
moment, and that moment is *uniformly paid*: the absolute first pronic moment of the damped
Chebyshev tangent has one bound valid for every horizon and every damping above a fixed positive
number (`exists_uniform_pronic_tangent_l1_bound`, `exists_uniform_scalar_damping_work_bound`). The
tangent itself need not have bounded critical square energy, so this is strictly less than the
tangent-norm demand. The renormalisation is moreover neutral: the original energy and its residual
at the constant source have uniformly comparable shifted energies, admission holds for one exactly
when it holds for the other, and a linear continuation budget exists for one exactly when it exists
for the other (`one_add_damped_energy_comparison`, `admits_damped_residual_iff`,
`signedDampingWork_sub_residualDampingWork`, `linearContinuation_residual_iff`). So the open demand
is the *covariance* part of the signed work and nothing else; subtracting means does not move it.

The residual half carries a sharp obstruction. The literal residual has a linear cusp, so although
its work tends to zero at each fixed horizon, the mean value theorem produces positive work at
arbitrarily small damping and arbitrarily large horizons
(`exists_positive_residualDampingWork_near_zero`,
`exists_positive_residualDampingWork_escaping_horizons`). Positive work escaping every fixed horizon
is exactly what a horizon-free budget has to absorb, and it rules out proving (C) by a fixed-horizon
limit.

### Cutoff transport

The denominator cutoff is the programme's second parameter. The actual Ramanujan truncation error
pays every cutoff change along a compatible sequence of growing heads, the exact stage balance
retains its signed cross term and its new physical shell
(`ramanujanCutoff_stage_energy_eq`, `ramanujanPhysicalShellEnergy_nonneg`), and the transport depth
is dyadically summable (`summable_sqrt_ramanujanCutoffTransportEnergy_dyadic`,
`exists_summable_ramanujanCutoffTransport_depth`). What is *not* asserted is a bound on the sum of
the physical shells: that sum is the cutoff analogue of the damping budget.

### The aperture parameter: unsigned depth sampling

This bridge is maintained in `SquareRootThreshold/UnsignedDepthSamplingDetectsLocalMass.lean`,
beside the depth-mass and sampling definitions it extends.

On the aperture side a source-uniform bound at a single positive aperture already controls squared
off-line depths on every unit-height window, with literal complex smooth interior probes, and the
converse holds, so the two are equivalent
(`exists_offLineDepthLocallyBounded_of_unsignedDepthSamplingBound`,
`unsignedDepthSamplingBound_of_offLineDepthLocallyBounded`, `exists_unsignedDepthSamplingBound_iff`).
This identifies the hypothesis under which the width equals the ground-energy rate with a sampling
statement about the source. It is unsigned difference energy, not the signed Weil floor, so it
bounds the hypothesis of the floor theorem rather than the floor.

### Iterated compensation

A compensation between a sector and its complement is useful only if it iterates. The abstract shape
is the affine recurrence `F_{j+1} ≤ q_j F_j + r_j`, whose explicit solution is `affineEnvelope`,
with closed form `F₀ ∏_{i<J} q_i + Σ_{j<J} r_j ∏_{j<i<J} q_i` (`affineEnvelope_eq`) and the usable
criterion: multipliers below `θ < 1` and sources below `R` give the stage-free bound
`max(F₀, R/(1−θ))` (`affineEnvelope_le_of_contraction`). The contraction is not a formality —
`affineEnvelope_one_one` shows that unit multipliers with unit sources diverge linearly, so a scheme
that merely cancels at leading order per stage proves nothing.

### The paid scalar correction and the remaining covariance

Write the actual centered prefix as \(A_\varepsilon(n)\), its damping
derivative as \(B_\varepsilon(n)\), and use weight \(1/[n(n+1)]\).
Subtracting the constant source gives a useful second energy:

\[
D_T(\varepsilon)=\sum_{1\le n\le T}
  \frac{(A_\varepsilon(n)-1)^2}{n(n+1)},\qquad
W_T^{\rm res}(\varepsilon)=\sum_{1\le n\le T}
  \frac{(A_\varepsilon(n)-1)B_\varepsilon(n)}{n(n+1)}.
\]

The derivative is \(D'_T=2W_T^{\rm res}\). The difference from the original
work is exactly the scalar moment \(\sum B_\varepsilon(n)/[n(n+1)]\).
That correction can be paid unconditionally: for every \(a>0\), one
constant \(K_a\) bounds

\[
\sup_{\varepsilon\ge a}\sup_T
\sum_{1\le n\le T}\frac{|B_\varepsilon(n)|}{n(n+1)}\le K_a.
\]

The mechanism is arithmetic but requires no critical-energy admission.
The tangent is the negative centered prefix of the logarithmically weighted
Möbius row. With \(b=\min(a,1)\), the existing damped-class estimate bounds
that prefix by \(C_b n^{1-b/2}\), uniformly for \(\varepsilon\ge a\).
Division by the pronic denominator leaves a summable majorant
\(C_b n^{-1-b/2}\). This is an absolute first-moment bound; it supplies
no square-energy bound for the tangent.

Elementary square inequalities give
\(1+D_T\le3(1+E_T)\) and \(1+E_T\le3(1+D_T)\).
Consequently admission and the linear continuation demand are unchanged
by this subtraction. A budget primitive \(\beta\) for either energy
transports to \(3\beta(\varepsilon)+2K_a\varepsilon\) for the other.
The finite-horizon condition at \(T=0\) supplies \(\beta'\ge0\), so this
comparison preserves the required direction of the inequality.
The remaining arithmetic obligation is a lower bound on the complete
residual covariance, relative to its current energy.

### A source-specific warning at zero damping

At every fixed horizon, both \(D_T(\varepsilon)\) and
\(W_T^{\rm res}(\varepsilon)\) tend to zero as \(\varepsilon\downarrow0\).
Yet the actual residual has an unconditional linear cusp: a critical zero
provides \(c>0\) such that every sufficiently small positive damping has
some horizon with \(D_T(\varepsilon)>c\varepsilon\).
The exact step-source Mellin transform, including its floor correction,
is essential to this assertion.

A finite-horizon mean-value argument then proves that a fixed amount of
positive residual work occurs arbitrarily near zero and beyond every
prescribed horizon. Thus vanishing at each finite horizon is incompatible
with a uniform vanishing-work estimate. This identifies where one limit
interchange fails without differentiating an infinite energy or assuming
that energy finite. It does not obstruct the one-sided bound on negative
work needed for backward continuation.

The kernel, entrance law, compact centered operators and positive-time
semigroup underlying this analysis belong to
`BezoutValuationIncidence`. Their compactness concerns \(c_0\). Their
unsigned row tails fail square summability at half damping, while tails
tested against the reciprocal observable remain square summable at every
positive damping. This programme uses that distinction to choose actual
source observables; compactness in the weaker space alone supplies no
critical Hilbert estimate.

### Two scales in a compensated representation

Changing a denominator cutoff and admitting new physical observations
incur different costs. For the actual Ramanujan prefix \(H_Q\), the
existing arithmetic source estimate implies, whenever \(T\le Q,R\),

\[
\|H_R-H_Q\|_T\le C_{\varepsilon,\beta}\sqrt T
  (Q^{-\beta}+R^{-\beta}),\qquad 0\le\beta<\varepsilon.
\]

Taking \(T_j=2^j\), \(Q_j=2^{mj}\), \(\beta=\varepsilon/2\), and
\(m\varepsilon>1\) makes all common-head transition norms summable.
This pays arbitrarily many representation changes at every positive
damping. The exact energy identity still contains the signed old-head
cross term and the nonnegative energy on the newly exposed physical shell.
No bound on the sum of those physical-shell energies follows from the
transport estimate. A proposed compensated recurrence must identify
which of these two costs its estimate controls.

### What one aperture can detect about zero depths

For any fixed positive aperture, a source-uniform bound on

\[
\sum_{q\in S}|\widehat u(-z_q)-\widehat u(-\overline{z_q})|^2
\]

for all finite sets of zero copies is equivalent to a uniform bound on
the squared off-line depths in every unit-height window. The forward
sampling estimate and exact classification belong to `SquareRootThreshold`.
For the converse,
a nonnegative smooth bump supported strictly on the positive side of the
aperture, modulated to height \(T\), has constant norm and detects
\(|\operatorname{Im}z|\) throughout \(|\operatorname{Re}z-T|\le1\).
The cosine factor remains positive on that support, and the difference
of the two real exponentials dominates a fixed multiple of the depth.
Summing the squared pointwise detection estimate preserves multiplicity.

This gives a precise limit of the unsigned approach: an aperture-dependent
constant, even at one aperture, already reinstates the local-depth
condition. It is not a necessity theorem for the signed ground floor.
The positive sampling term can compensate the negative term. The next
arithmetic tool must compare both terms for the actual source.

## 4. Traps

- **Horizon-dependent budgets transport nothing.** `escapeEnergy ε T = exp(2(½−ε) log(T+1)) − 1`
  vanishes at the endpoint `ε = ½`, satisfies the *exact* linear continuation identity
  `−∂_ε Esc_T = 2 log(T+1)·(1 + Esc_T)` with a coefficient finite for each horizon, and is admitted
  at no damping below `½` (`HorizonUniformityIsTheTheorem`). Hence no horizon-free budget exists for
  it on any `[a, ½]` with `a < ½` (`not_linearContinuation_escapeEnergy`). The placement of the
  horizon quantifier is the mathematics, not a convenience of the formulation.
- **The tangent norm is a strictly stronger demand.** A row rotating in two pronic cells at
  frequency `K` has constant energy, identically vanishing signed work, and tangent norm `|K|`
  (`exists_vanishing_signed_work_with_large_tangent`). A continuation budget therefore yields no
  bound whatever on the tangent norm. Attacking the norm instead of the pairing is attacking a
  harder problem.
- **Ratio smallness is not a bound.** A complete energy can tend to infinity while its ratio to a
  sector energy tends to zero (`exists_ratio_tendsto_zero_and_complete_unbounded`). A proved ratio
  limit — such as a complementary-sector cancellation — is evidence of a mechanism, not an admission
  statement. What must improve is the rate, in the complete norm, with the horizon and cutoff
  quantifiers intact.
- **Sector energies may not be added.** `m` identical sectors have complete energy `m²` times a
  sector energy while the sum of the sector energies is `m` times it
  (`exists_sector_count_complete_energy_gt`); the cross terms carry the whole cost
  (`pronicNorm_add_sq`). A decomposition is useful only with its interaction terms attached, and a
  scheme must specify its partitions, its horizon, its centering and every transition cross term.
- **A scale without coercivity says nothing.** A bound on `Ψ ∘ E` for a bounded `Ψ` is vacuous; the
  Osgood hypothesis enters only as `Tendsto Ψ atTop atTop`, and that is exactly where a finite
  `∫^∞ du/Φ(u)` would fail.
- **Recovery is not control.** An injective observation map, even a complete invariant, supplies no
  bound. The corpus has both halves of this: all logarithmic pronic moments determine a damped
  source, and yet admission is incompatible with an unweighted uniform lower modulus
  (`RHTower.not_exists_uniform_lower_bound_primeGammaCauchyHorizonGrade`); while rows agreeing in
  every stationary translated moment split the receiver. A theorem using finitely many moments must
  state how its constants depend on the number of moments, the damping and the horizon.
- **The integer prefix is not the real-centred extension.** Replacing `A_ε(⌊x⌋)` by the real-centred
  `𝒜_ε(x) = Σ_{d ≤ x} c_ε(d)⌊x/d⌋ − x·Re(1/ζ(1+ε))` introduces a fractional-part correction; the
  convolution identity `∂_ε 𝒜_ε(x) = Σ_k Λ(k) k^{-ε} 𝒜_ε(x/k)` holds for the extension, and its
  `k > x` tail is a convergent pole tail, not zero. The two must not be silently identified.
- **An absolute dilation estimate cannot reach below half damping.** Bounding the convolution
  identity term by term meets `Σ_k Λ(k) k^{−ε−1/2}`, which diverges at `ε = ½`. The prospective
  input is a lower bound on the signed numerical range along the literal source, not a majorant.

## 5. Open problems

1. **The covariance half of the continuation estimate (C).** For every `0 < a < c` with `c`
   admitted, produce a nonnegative `β'` integrable on `[a, c]`, independent of the horizon, with
   `−2 W_T(ε) ≤ β'(ε)(1 + E_T(ε))` for all `T` and almost every `ε ∈ [a, c]`. Dependence on `a`,
   including arbitrarily bad growth as `a ↓ 0`, is allowed. The scalar part of this is proved
   (`exists_uniform_scalar_damping_work_bound`) and renormalisation is neutral
   (`linearContinuation_residual_iff`), so the open demand is exactly the covariance of the centred
   source with the centred tangent. `riemannHypothesis_of_dampingContinuation_endpoint` is the
   consumer, and `exists_positive_residualDampingWork_escaping_horizons` says no fixed-horizon limit
   can supply it.
2. **The superlinear variant.** The same with `(1 + E)(1 + log(1 + E))` in place of `1 + E`, or
   with any coercive scale. `riemannHypothesis_of_superlinear_dampingContinuation` is the consumer.
3. **Which terms obstruct.** Express `W_T(ε)` through the owned divisor, Vaughan and logarithmic
   covariance identities and classify the terms whose negative part is not controlled uniformly in
   the horizon. The Markov face says one such term is the jump energy of the arithmetic chain.
4. **Propagating the complementary-sector cancellation.** Turn the proved leading-order
   anti-alignment between a large-prime denominator sector and its literal complement into a
   quantitative residual that survives a second compatible scale transition, in the shape
   `F_{j+1} ≤ q_j F_j + r_j` with a contraction. `affineEnvelope_le_of_contraction` is the consumer;
   `exists_sector_count_complete_energy_gt` is the obstruction to a careless version.
5. **The compensated width floor.** Retain the positive sampling contributions discarded by the
   local-count argument: with `a_q = û(−z_q)`, `b_q = û(−z̄_q)` on the smooth core and
   `E_± = ¼ Σ_q |a_q ± b_q|²`, decide whether the actual prime–Gamma–pole source forces
   `E_−(u) ≤ E_+(u) + C_σ e^{2σA} ‖u‖₂²` for every `σ` above the width, without assuming bounded
   local off-line depth mass. This would close the reverse ground-rate inequality; it would not show
   the common rate vanishes. The stronger local-depth-mass hypothesis is equivalent to a
   one-aperture unsigned sampling bound (`SquareRootThreshold.exists_unsignedDepthSamplingBound_iff`).
   Joint signed compensation may avoid that stronger hypothesis; the equivalence does not
   make the signed floor estimate necessary or sufficient for unsigned sampling.
6. **The sum of the physical shells.** Bound the accumulated physical shell cost of the
   cutoff transport along a growing-head sequence; this is the cutoff analogue of the damping
   budget, and `ramanujanCutoff_stage_energy_eq` is the exact balance it must control.
7. **The aperture instance.** Instantiate the transport theorems with the aperture as parameter and
   the ground energy of the restricted Weil form as the energy, and identify the aperture analogue
   of the unconditional endpoint.
8. **A stability theorem for a signed observation.** Find an observation map that is both
   origin-sensitive and sign-reading, and prove a quantitative stability estimate for it in the
   receiver's norm — the missing half of the recovery theorems.

### Research topics toward the shared target

- Source-derived continuation below the existing admission frontier. The sharper paper threshold
  is `Δ = Θ − 1/2`: on `[a, 1/2]`, `a > Δ` supplies continuation and continuation forces
  `a ≥ Δ`; the positive boundary `a = Δ` remains undecided. The target is every positive `a`.
- The contraction factor of a sector-compensation scheme for the actual Möbius row, with every
  transition cross term paid, as the input to mechanism 2 of the shared target.
- Selectivity certificates for any proposed continuation estimate against the shifted pair
  `ζ(s−a)ζ(s+a)`, a Beurling system with an off-line zero, and the Liouville-twisted weight.
- The aperture continuation of AIP's window certificates past a prime, with the per-prime gain
  required by `affineEnvelope_le_of_contraction`.
- The `F_q[T]` calibration of the continuation mechanism: what plays the role of the damping, and
  whether the analogue of (C) is provable there.

## 6. Principles

1. **Exact source before closure.** Every coefficient, prime power, Gamma term and pole term is
   fixed before an estimate is claimed. A source selected from the zeros is not an arithmetic
   construction.
2. **Keep signs until their cancellation is paid.** Absolute values are allowed where their loss is
   proved acceptable. The default object is the complete signed pairing.
3. **Uniformity is part of the theorem.** `∀ε ∃C_ε ∀T` is stated when that is what is meant. A
   horizon-dependent band or a complete-period limit is a different result.
4. **Distinguish recovery from control.** An injective observation, even a complete invariant,
   requires a stability estimate before it bounds an energy.
5. **Preserve the required norm.** An `H¹` estimate does not pay an `L²`-normalised floor;
   pointwise convergence does not replace convergence in the receiver's energy.
6. **Test selectivity against the known adversaries.** Shifted zeta pairs, altered prime weights,
   parity partners and coherent blocks must fail a named hypothesis.
7. **Pay both ends of a limit.** Origin, infinity, fractional-part terms and polar constraints
   belong to the same accounting; a missing boundary term can contain the whole obstruction.
8. **Separate endpoint success from bridge success.** A larger certified interval or the equality of
   two unknown rates is useful; it is not a smaller zero width.
9. **Require a positive survivor from failure.** If a continuation fails, extract the sharp growth
   law, the obstruction measure, the classification or the weaker valid estimate.

## 7. Module map

| Module | Contents |
|---|---|
| `CriticalEnergyFamilies` | `Admits`, `CofinallyAdmits`, `UniformlyAdmitsOn`; closure properties |
| `BackwardContinuationCalculus` | the master monotonicity inequality, the Grönwall form, coercive recovery, monotone scales |
| `ContinuationTransportsAdmission` | `LinearContinuation`, `OsgoodContinuation`, transport and its cofinal packaging |
| `HorizonUniformityIsTheTheorem` | the escape family; non-existence of a horizon-free budget for it |
| `AffineRecurrenceEnvelope` | `affineEnvelope`, its closed form, the contraction criterion, linear divergence at unit multipliers |
| `GroundFloorNoCrossing` | the floor transport for a positive ground energy; no crossing from a bounded relative decay |
| `TheDampedMobiusCriticalEnergy` | the arithmetic instance; admission dictionary; RH as cofinal admission |
| `SignedDampingWorkOfTheMobiusEnergy` | `signedDampingWork`; `∂_ε E_T = 2W_T`; the Markov bridge; Cauchy–Schwarz |
| `TheScalarDampingWorkIsAlreadyPaid` | the actual tangent as a logarithmic centered prefix; uniform absolute first-pronic-moment control on every positive damping half-line |
| `TheResidualCuspForcesEscapingWork` | finite-horizon residual derivative and zero limits; fixed positive work arbitrarily near zero beyond every prescribed horizon |
| `RenormalizationPreservesDampingContinuation` | comparable original/residual energies; exact scalar work difference; equivalence of admission and of linear continuation on positive damping intervals |
| `TheDampingContinuationCriterion` | the criteria for RH, the admitted endpoints, the partial-continuation zero-free strip, subsumption of the tangent norm |
| `TheSignedWorkDemandIsStrictlyWeaker` | the rotating two-cell row: constant energy, zero work, unbounded tangent |
| `SuperlinearOsgoodScale` | the double-logarithmic scale and the superlinear criterion |
| `CompensationNeedsItsCrossTerms` | the complete signed decomposition; sectors may not be added; ratio smallness is not a bound |
| `FiniteHeadCutoffTransportAndPhysicalShellCost` | actual Ramanujan cutoff-error bounds, complete stage identity, and a depth schedule with summable common-head transition norms |
