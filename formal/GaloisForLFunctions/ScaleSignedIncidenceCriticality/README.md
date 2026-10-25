# Scale-Signed Incidence Criticality (SSIC)

**One question.** A proof never touches the arithmetic of $\mathbb Z$ directly; it touches a list of
observables (coefficient magnitudes, amplitudes, moments, a certificate at one aperture, a node
density, a zero list up to a height). Which lists can decide the sign of the critical arithmetic
form, and, for a list that cannot, what is the best bound it *can* certify?

SSIC is the exact calculus of that question: an **information theory for proposed arithmetic
arguments**. Primitive object: a **reading** $r:D\to O$. Basic invariant: the **resolution limit**
$\sup\{I(e):r(e)=r(d)\}$ — the exact best bound any method reading $r$ can prove. Basic theorem: the
**collapse–resolution dichotomy**. Every statement names its reading, collapse and witness pair.
Passing a blindness gate is necessary for a method; it is not an estimate.

Namespace `GaloisForLFunctions.ScaleSignedIncidenceCriticality`; umbrella
`ScaleSignedIncidenceCriticality.lean`. Countermodels are imported from their owners; SSIC adds only
the calculus. Start with module `TheResolutionLimitOfAReading.lean`.

---

## 1. Place in the research

SSIC is the **admissibility layer** of the shared target: it prices a reading before a route is
built and states the separations an admissible reading must perform — past the Nyquist aperture of
the configuration addressed, by magnitude rather than sign, and on the prime side separating
$\Lambda$ from each single-index perturbation.

| Programme | What SSIC prices there |
|---|---|
| [SquareRootThreshold](../SquareRootThreshold/README.md) | Lattice models, Nyquist laws, visibility witnesses, width dictionary |
| [ArithmeticCriticalityTheory](../ArithmeticCriticalityTheory/README.md) | Bounded-aperture certificates; $\mu(A)$ sign vs magnitude; two-aperture ratio |
| [BiScaleUncertainty](../BiScaleUncertainty/README.md) | Node-critical blind cones; packet rates; window-extreme twist blindness |
| [TransHorizonIncidenceMechanics](../TransHorizonIncidenceMechanics/README.md) | Parity collisions; finite observer vs uniform payment; quarter law |
| [BezoutValuationIncidence](../BezoutValuationIncidence/README.md) | Cross-scale Gram readings in the exponent unit $\theta$ |
| [ArithmeticIncidencePositivity](../ArithmeticIncidencePositivity/README.md) | Allocation and comb readings: signs vs sizes |
| [ArithmeticContinuationAndCriticalEnergy](../ArithmeticContinuationAndCriticalEnergy/README.md) | Pointwise vs averaged vs horizon-uniform budgets; rate equalities |
| [ArithmeticCompensationTheory](../ArithmeticCompensationTheory/README.md) | Whether energy changes preserve signed information |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | Formal signature criteria vs effectivity data |
| [SignedArithmeticEnergyIncidence](../SignedArithmeticEnergyIncidence/README.md) | Information lost by absolute majorants |
| [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md) | Two-thirds barrier = resolution limit of the reading $(\hat A,N)$ |
| [ArithmeticOrientationTheory](../ArithmeticOrientationTheory/README.md) | Builds orientation-faithful readings; SSIC refutation theorem = reading entry of the width dictionary |
| [arithmetic-positivity-theory](../arithmetic-positivity-theory/README.md) | Complete source families; readings must keep what their receiver needs |

Module `RHTower/DeciderBarrier.lean` contains related collision tools.

---

## 2. Why

Hundreds of corpus no-gos are one phenomenon: a method is a function of observables, two data
share the observables, and the property differs on them. Consequences: (1) the shape is reusable —
prove blindness once per class of methods (all density arguments, all amplitude statistics, all
monotone depth reparametrisations); (2) blindness has a **number**, so routes can be priced before
being built; (3) the limits are discontinuous — every bounded aperture has width limit $\tfrac12$,
the unbounded certificate has limit $0$, and bounded stages form a strictly increasing chain of data
with the same trivial bound. The width appears only in the limit or in a magnitude.

The calculus itself is set-theoretic (fibres); research content comes from arithmetic instances:
explicit countermodels, sharp intervals, stable inversion formulas, proofs that a method class
factors through a reading. Gates first, construction second.

---

## 3. Objects and language

- **Reading** $r:D\to O$; **shadow** $\{e:r(e)=r(d)\}$. `Resolves r P` ⇔ factorisation
  (`resolves_iff_exists_factorization`). `Refutes`: every indistinguishable datum fails $P$ (inherited
  by finer readings).
- **Collapse** $\kappa:D\to D$, *invisible* if $r\circ\kappa=r$; *fatal* / *neutral*. Collapses of the
  critical form: shifted pair, node deletion, parity flip, aperture/height truncation, modifying
  prime weights above $e^{2R}$, inserting off-line pairs above a height.
- **Limits.** `Certifies I r d β`; `resolutionLimit`, `resolutionFloor`; **resolution interval**;
  *informative* (proper) / *pins* (degenerate); *faithful* (limit = $I$).
- **Order.** `Refines`; factoring through a reduction inherits its shadows
  (`resolutionLimit_eq_of_factors_of_max`); families = joins (`familyReading`); **policies** adapt
  aperture and precision to scale (`adaptiveReading`, `ScaleMatched`).
- **Two coordinates.** On the lattice family $(L,\delta)$, dilation moves the scale and fixes the depth:
  depth is the **complete dilation invariant**. Resolving depth = separating dilation orbits. Vertical
  data (even the exact ordinate set) sees the scale; the **horizontal** coordinate carries RH.

| Unit | Definition | Vanishes iff |
|---|---|---|
| width | $\sup|\Re\rho-\tfrac12|$ | all zeros on the line |
| depth | $\delta$ (`sdDepth`) | on-line |
| deficit rate | $\inf\{\beta:\text{deficit}=O(e^{2\beta a})\}$ (`rateSet`) | on-line |
| depth resolution | $\operatorname{arcosh}(1+\eta/2L)/L$ | $\eta=0$ |
| node scale | $\sup\{1/m:m\text{ prime power}\notin\mathcal N\}$ | all prime powers present |
| band ratio | $t_3/(2t_2)-1$; $(t_4-t_3)/(t_3-t_2)$; $M(2a)/2M(a)$; $(\mu(A_0)-\mu(A))/\mu(A_0)$ | critical value 1 (2 for the difference ratio) |
| cross-scale exponent | $\theta=2\log P/\log X$, certified $2K/(K+1)$ | deficit 0 at $\theta=2$ |

**Faces:** aperture (tempered configurations; width), trans-Nyquist (lattice data; depth), mixed
(mass + dilution), node incidence (node sets), prime window (prime weights; full Weil cone), pronic
Gram (cross-scale exponent), parity collapses (four-free convolutions, Selberg sign orbits, residue
flips). Computed shadows: complete-period quadratic data = sign orbit; prime signs + prime mean do
not resolve payment; window extremes are twist-invariant.

---

## 4. Mechanisms

1. **Dichotomy and floor theorem.** An invisible verdict-changing collapse ⇒ no resolution; a
   resolving reading forces failure on every missed orbit (for two faces: ⇒ ¬RH). One witness of
   maximal invariant inside the shadow fixes the limit exactly.
2. **Aperture face: one witness, every unit.** An off-line lattice with $L\ge2a$ of width ½ satisfies
   the aperture-$a$ certificate for free ⇒ limit ½, floor 0, for coercive certificates, bounded families
   of any cardinality, and any monotone depth unit. Only the unbounded certificate has limit 0.
3. **Two coordinates.** With scale and depth free, a single aperture separates nothing (dense end in
   every shadow); scale bounds are essential (`theDilationRequirement`).
4. **Past Nyquist: deficit, precision, rate.** In $L/2<a\le L$ the deficit $2L(\cosh\delta L-1)$ separates
   depths at known scale; **square-root precision law**: precision $\eta$ resolves depth $\sqrt{\eta/L^3}$,
   so excluding $\beta$ costs $\beta^2L^3$ (`theDeficitBudgetLaw`). Along apertures the rate infimum is the
   depth — faithful and scale-free. Uniform mass-normalised deficit bounds exclude positive depth;
   frequency-growing allowances are vacuous.
5. **Hiding laws.** Finite off-line sets are refuted; a single pair is depth-bounded by local mass and
   needs mass $\sim e^{2\delta a}$; mass buys aperture only logarithmically (reach law); aliasing is free
   exactly below the sub-lattice Nyquist aperture. The aperture–mass pair is the productive seam.
6. **Magnitudes determine the depth.** Two aliasing bands: $\delta=\operatorname{arcosh}(t_3/2t_2-1)\cdot(t_3-4t_2)/t_2^2$;
   conditioning again $\beta^2$; three bands cancel unknown mass; one aperture doubling for a pair.
7. **Sign vs magnitude.** Level certificate limit ½; band-pair reading faithful (floor = limit).
8. **What must be verified.** Confirmation along any unbounded aperture/radius set suffices (monotone);
   incidence face needs every prime power, no sampling (node face is a principal up-set under RH;
   cofinality/density one cannot compensate). Refutation is finite and complete on the prime side
   (RH ⇔ no bounded-radius certificate refutes the cone).
9. **Cofinal rates.** For convex profiles secant-rate bounds on any unbounded set equal all-aperture
   bounds; bounded readings certify no finite rate (ramps witness).
10. **Pronic Gram face.** Type-II and rank-two readout readings: limit 2, floor 0; smoothness order $K$
    certifies $2K/(K+1)$; residue masses faithful for the Bernoulli main term; centred prime row leaves
    the Type-II shadow on $7/6<\theta<2$.
11. **Band recipe for $\zeta$.** Two-aperture ratio $R(A)=(\mu(A_0)-\mu(A))/\mu(A_0)$ (base $A_0\le21/200$):
    RH ⇔ $R\le1$ ⇔ $R\to1$; growth $R\le1+Ce^{2\sigma A}$ ⇒ width $\le\sigma$; certified below 1 at small aperture.
12. **Fatality of parity collapses.** Even flip on $k\star o_\varepsilon$ strictly fatal iff pole value vanishes but
    even part's does not; Selberg sign orbits pinned by cubic moments up to the even flip;
    residue-class complementation neutral iff $\varphi(q)<4|S^\times|<3\varphi(q)$ (fatality window $(\frac14,\frac34)$).
13. **Rate readings for $\zeta$.** Lag, Chebyshev-deficit, band and Möbius-damping rates = width
    unconditionally; polar ground-energy rate = full rate unconditionally (ACCE) and = width under a
    local count; a local count lifts single-aperture width floors from 0 to explicit values.
14. **Counterexample design.** Diluted-lattice band energies $\ell\sum(\cosh(\delta\ell(2j-n+1))-1)$; joint
    aperture–mass reading = one band inequality; prime side adds the $3/10$ barrier, unbounded $S(T)$,
    polylog near-top negativity.
15. **Policies.** Sub-Nyquist at one scale ⇒ limit ½; scale-matched policies resolve depth iff
    $\eta(L)/L^3\to0$; both available single-height schedules for $\zeta$ are blind.
16. **Incidence ledger unit.** Scalar comb energy cannot certify the comb charge (interval
    $[-\sqrt{ME},\sqrt{ME}]$, realised by dilated odd bumps); the coherent horizon residual bounds it.

---

## 5. Pillar theorems

1. Dichotomy (`not_resolves_of_separating_collapse`, `forall_not_of_resolves_of_invisible`,
   `not_riemannHypothesis_of_resolves_of_invisible`).
2. Floor theorem (`resolutionLimit_eq_of_mem_shadow_of_max`).
3. Aperture certificate blind in every unit (`resolutionLimit_width_aperturePositivity`,
   `theFloorIsUnitIndependent`, `resolutionLimit_width_fullPositivity`).
4. Depth = complete dilation invariant (`dilationEquiv_iff_sdDepth_eq`, `resolutionLimit_sdDepth_scaleDepthReading`).
5. Square-root precision law (`theDeficitBudgetLaw`, `sInf_rateSet`).
6. Magnitudes faithful where signs are blind (`depthFromBands_eq`, `resolutionFloor_eq_resolutionLimit_bandPairReading`,
   `threeBandsDefeatTheMass`, `theDichotomyOfSignAndMagnitude`).
7. Hiding laws (`theReachLaw`, `theFreeRegimeIsSharp`).
8. Refutation finite, confirmation not (`riemannHypothesis_iff_no_radiusReading_refutes`,
   `theNodeFaceAsymmetry`, `theReductionDichotomy`).
9. Cofinal rate invariance (`rateBoundsOn_eq_rateBounds`, `not_certifies_rateBoundsBelow`).
10. Pronic Gram limits (`resolutionLimit_typeIIGramReading_eq_two`, `centredPrimeRow_bypasses_resolutionLimit_two`).
11. Band recipe (`riemannHypothesis_iff_forall_zetaTwoApertureRatio_le_one`).
12. Parity fatality (`strictlyFatalAt_evenFlip_iff_pole_and_evenPart`, `strictlyFatalAt_compl_residueFlip_half_iff`).
13. Rate readings (`five_rate_currencies_of_zeta`, `le_resolutionFloor_width_deficitAndCount`).
14. Counterexample design (`dilutedReading_iff_bandEnergy_le`, `counterexample_primeSide_obstructions`).
15. Policies (`certifies_sdDepth_adaptiveReading_iff`, `resolutionLimit_sdDepth_chebyshevSchedule_eq_half`).
16. Comb charge (`resolutionInterval_combChargeVal_scalarCombEnergyReading`, `sq_combCharge_le_mass_mul_horizonResidualEnergy`).

---

## 6. Traps

- A reading is a method's *input*, not its conclusion; name it precisely.
- Name the unit and price in it (width: bounded readings vacuous; rate: scale-free; band ratio: explicit).
- Boundedness is not the explanation: coordinates are (unbounded vertical data is still blind).
- Strengthening a blind reading within its class (more bounded apertures, larger gap, monotone unit
  change) does not help; repairs cross Nyquist, read magnitudes, or add mass/dilution data.
- A faithful reading is not a proof: it says which numbers decide, not that they are reachable.
- Keep the configuration class (crystals vs finite sets vs single pairs).
- Node positivity / pair criticality hold only under RH: gates read "resolving ⇒ ¬RH".
- `Prop`-valued readings need `propext` (`Eq`, not `Iff`).
- `ZeroConfig.mult` is unconstrained off the carrier; restrict to the carrier.
- Bounded, not finite, apertures are the operative hypothesis.
- A loss is harmless or fatal by its growth, not its size.
- Cofinality needs structure (convexity or a replacement); sparse samples of oscillating functions do not.

---

## 7. Open problems

1. **Rate readings beyond convex profiles and lattices**: name a profile class with tail regularity and
   characterize observations controlling the rate.
2. **Exhaustive classification of repairs** for a *specified* class of admissible readings (an
   unrestricted reading can encode the target), with a precision cost per repair.
3. **A scale-matched schedule for $\zeta$**: $L/2<A(L)\le L$ with precision $o(L^3)$; what single-height prime
   estimate does it need, versus the aperture-face power saving?
4. **The local count.** Is a local off-line count necessary for the $L^2$ polar rate to equal the
   width? (Form-domain rates already equal the width unconditionally, and polar = full in $L^2$.)
   Separate formal information bounds from analytic countermodels.
5. **Pronic Gram at $\theta=2$**: exact resolution limit of the enriched actual-row reading, endpoint kept
   (BVI: any power saving at the diagonal is quasi-RH).
6. **The comb residual**: price source readings that bound it without archimedean subsidy.
7. **Fatality** of the Liouville twist, shifted pair and Beurling deformations as receiver collapses.

Topics: price every mechanism as (class of readings, exact limit) before building; supply data of a
third kind where a floor reflects missing information; trade aperture against precision via $\beta^2L^3$
and bands against unknowns (one index per unknown).

---

## 8. Tools

Built: readings, shadows, collapses, `Invisible` closure lemmas; refinement/factorisation; limits,
floors, intervals; witness families (lattices, crystals, dilution, node collapses, imported parity
pairs); band recipes and precision budget; reach law; cofinal rate readings; pronic Gram readings in
$\theta$; two-aperture ratio for $\zeta$; fatality–neutrality calculus; rate readings for $\zeta$; counterexample
design; policies; incidence-ledger comb shadows.

---

## 9. Working conventions

- State reading, collapse, witness pair; prefer an interval to a limit, a limit to a blindness claim.
- Instantiate the general theorems (`not_resolves_of_pair`, `resolves_iff_exists_factorization`,
  `Resolves.of_refines`, `resolutionLimit_le_of_refines`); do not reprove the shape.
- Import countermodels from SRT, BSU, THIM, RHTower; SSIC builds no arithmetic objects.
- Report results as (class of readings, exact limit), name the gate and the unit.
- Refutation results belong on prime/node faces; confirmation names its unbounded resource or measured magnitudes.
- Prefer a magnitude to a sign: ask which ratio a reported inequality would need instead.
