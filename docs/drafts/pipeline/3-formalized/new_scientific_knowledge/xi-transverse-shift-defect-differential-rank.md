# Differential rank of the transverse Xi shift-defect flow

- **ID:** `xi-transverse-shift-defect-differential-rank`
- **Stage:** 3-formalized
- **Type:** THEOREM / POSITIVE FIXED-APERTURE NO-GO SURVIVOR
- **Scientific status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Source:** `HTGeometry/PrimeExpLogFiberRigidity.lean`;
  `HTGeometry/PrimeProfileSeparatedPacketExact.lean`;
  `HTGeometry/PrimePowerAnalyticDilation.lean`;
  `RHTower/XiShiftPrimeExposure.lean`;
  `RHTower/SuzukiCoupledErrorCriticalDerivative.lean`
- **Formal result:** For every arbitrarily indexed integral Xi prime-source shift family over the
  genuine rational coordinate field, the represented differential matroid is exactly the pointed
  collision matroid of its shift labels: shift zero is a loop, repetitions are parallel, and the
  rank of any packet is the number of distinct nonzero shifts. Every source carrier is exactly the
  actual completed-Xi logarithmic shift defect after subtracting its archimedean logarithmic shift
  defect, as an upper-end germ. In particular, every finite family of distinct positive shifts
  supplies the expected number of new differential directions. The same arbitrary-family pointed
  collision law remains true after adjoining all scalar prime-valuation layers simultaneously.

## Motivation from the fixed-aperture no-go

For

```text
Theta_omega(z)
 = xi(1/2-omega-i*z)/xi(1/2+omega-i*z),
```

the single safe aperture `omega=1` is inner unconditionally and cannot imply RH. Horizontal zero
position is instead the entry time of the anti-causal leakage as `omega` moves toward zero. A
valid RH Hilbert carrier therefore needs the transverse family, not one ratio.

HTGeometry suggests a stronger source-side statement: distinct apertures should not collapse to
finitely many differential reporters. The prime logarithms provide the transverse coordinates,
and exponential-polynomial rigidity should make the aperture parameter a genuine differential
rank parameter.

## Exact arithmetic family

For `a>0`, define

```text
D_a(s)=sum_(n>=1) Lambda(n)(1-n^(-a))n^(-s).
```

For even integers `a=2m`, telescoping the proved `+2` Xi identity gives

```text
D_(2m)(s)
 = logDeriv(xi)(s+2m)-logDeriv(xi)(s)-R_(2m)(s),           (T1)

R_(2m)(s)=sum_(j=0)^(m-1) R_2(s+2j) in C(s).              (T2)
```

Thus the arithmetic theorem below is immediately an actual completed-Xi theorem for the even
shift family.

## Formalized theorem

Let `a_1,...,a_d` be distinct positive integers. Then

```text
D_(a_1),...,D_(a_d)
```

are differentially algebraically independent over `C(s)` as actual upper-end meromorphic
carriers. The Lean theorem constructs the full finite-abscissa Dirichlet sources, proves
prime-layer jet rigidity, promotes it to the complete prime-power profiles, and then applies the
faithful analytic transfer. It does not replace the sources by their prime-only truncations.

For every natural `a`, the carrier has the exact completed-Xi value reflection

```text
D_a(s)
 = logDeriv(xi)(s+a)-logDeriv(xi)(s)
   -(logDeriv(archFactor)(s+a)-logDeriv(archFactor)(s))       (T0)
```

on the Euler half-plane and therefore as an upper-end germ. Thus the arbitrary-family matroid is
an actual corrected completed-Xi family theorem for all integral shifts. For even `a`, the
archimedean difference in `(T0)` is the rational correction `(T2)`.

The same general shift carries an exact reflection law. Write

```text
r_a(s) = 1-a-s.
```

The raw completed-Xi shift defect is fixed by `r_a`. Subtracting the archimedean correction
therefore produces an exact reflection cocycle, and that cocycle is anti-invariant under `r_a`.
Adding one half of the cocycle to the corrected prime defect gives a centered defect fixed by
`r_a`. This is unconditional for every natural shift; no rationality or differential-algebraicity
of the odd-shift archimedean correction is asserted.

For every `m`, `(T1)` and `(T2)` are now formalized as an equality of upper-end germs: the
finite-abscissa source carrier at shift `2m` is exactly the directly corrected shift-`2m` defect of
the actual completed logarithmic derivative. Hence every arbitrarily indexed family of actual
even-shift defects has the pointed collision matroid of its half-shift grades. In particular,
distinct positive even-shift completed-Xi defects are jointly differentially independent.

The complete absolute source law no longer needs finiteness, positivity, or injectivity as theorem
hypotheses. For any index type `A`, shift map `a : A -> N`, and packet `I subset A`,

```text
I is differentially independent
  iff a is injective on I and 0 is not in a(I),                    (T2a)

differential-rank(I) = number of distinct nonzero values in a(I). (T2b)
```

This exactly classifies the hypothesis failures of the original finite theorem rather than merely
recording them as falsifiers.

The stronger relative theorem works over

```text
K_layer=C(s)<P(s),P(2s),P(3s),...>_d.                     (T3)
```

The entire arbitrary-family pointed collision law remains true over this larger base: zero shifts
are loops, repeated shifts are parallel, and the relative rank of every packet is the number of
distinct nonzero shifts, even after all scalar valuation layers are available. This statement is
also formalized.

## Paper attack: prime-layer exponential-polynomial rigidity

At a prime `p`, the `k`-th logarithmic jet of the coefficient of `D_a` is, up to a fixed nonzero
power of `i`,

```text
(log p)^(k+1) (1-exp(-a log p)).                           (T4)
```

Suppose a finite jet combination is supported on only finitely many prime rays. Evaluating it at
the first valuation coordinate gives, for all sufficiently large primes,

```text
P_0(log p)-sum_j P_j(log p) exp(-a_j log p)=0,             (T5)

P_0=sum_j P_j.
```

Add the zero shift to the distinct positive shifts. The already formalized
`primeFactorClockFiberIndependent` theorem says that the exponential-polynomial family in `(T5)`
is rigid on every infinite prime set. Therefore every `P_j` is zero, so all coefficients in the
original jet relation vanish. The exact prime-profile packet criterion then yields formal
differential independence, and faithful finite-abscissa transfer yields the actual analytic
upper-end theorem.

For the relative theorem over `(T3)`, a proposed differential relation uses only finitely many
valuation layers. Choose a fresh valuation exponent. The old scalar layers vanish there, while
the new packet becomes `(T5)` with each `a_j` multiplied by the same positive integer. Rigidity
again kills the entire new packet. The remaining old-layer relation is killed by the existing
valuation-basis theorem. Finite character then passes to all of `K_layer`.

For the arbitrary-family absolute law, every finite restriction with injective nonzero labels is
one of the already proved finite positive packets. Differential independence is finitary, so all
injective nonzero restrictions are independent. Conversely, a zero label gives the zero carrier,
and equal labels give equal carriers; the general pointed differential collision law therefore
identifies the whole represented matroid and its extended rank. No compactness assumption or
choice of a finite ambient packet enters the statement.

## RH meaning and limit

The theorem gives a precise positive interpretation of the fixed-aperture no-go:

```text
number of distinct nonzero safe shift grades in any packet
  = differential source rank of that transverse packet.                     (T6)
```

Thus no finite collection of safe quotients, differential jets, or valuation-layer reporters can
encode the full aperture flow. A Hilbert proof must preserve an infinite transverse source
capacity all the way to the Hardy leakage filtration.

The Hilbert form of this statement is exact. For every finite shift family, every finite jet
depth, and every finite set of deleted prime rays, there is a square packet of surviving primes
whose shift-jet evaluation Gram is strictly positive definite. Its determinant is positive and
its rank is the full shift-times-jet cardinality. Thus finite prime loss does not collapse the
aperture metric; any valid infinite true-aperture completion must extend this directed family of
positive finite sections.

This still does not prove RH. Differential independence neither supplies the Hardy norm bound nor
forces `L_omega=0`; it only rules out finite differential compression of the object on which that
RH-strength assertion must be proved.

## Lean realization and audit

- **Module:** `formal/GaloisForLFunctions/RHTower/XiTransverseShiftDefectDifferentialRank.lean`
- **General-law module:**
  `formal/GaloisForLFunctions/HTGeometry/DifferentialPointedCollisionMatroid.lean`
- **General finitary interface:**
  `GaloisForLFunctions.differentialIndependent_of_forall_finite_subfamily`
- **General pointed-collision law:**
  `GaloisForLFunctions.differentialFamilyMatroid_eq_affinePointedCollisionMatroid_of_parallel`
- **Arithmetic capstone:**
  `RHTower.xiTransverseShiftArithmetic_differentialIndependent`
- **Actual upper-end capstone:**
  `RHTower.xiTransverseShiftUpperEndCarrier_differentialIndependent`
- **Exact arbitrary-family matroid capstone:**
  `RHTower.xiTransverseShiftUpperEndCarrier_differentialMatroid_eq_pointedCollision`
- **Prop interface:**
  `RHTower.xiTransverseShiftUpperEndCarrier_differentialIndependent_iff`
- **Exact arbitrary-packet rank:**
  `RHTower.xiTransverseShiftUpperEndCarrier_differentialMatroid_eRk`
- **General completed-Xi value-reflection module:**
  `formal/GaloisForLFunctions/RHTower/XiTransverseShiftPrimeDefectValueReflection.lean`
- **General integral-shift exposure:**
  `RHTower.xiTransverseShiftPrimeDefect_eq_lSeries`
- **General source-to-completed-Xi germ reflection:**
  `RHTower.xiTransverseShiftUpperEndGerm_eq_xiTransverseShiftPrimeDefect`
- **General raw completed-Xi reflection:**
  `RHTower.xiTransverseShiftRawLogDerivDefect_reflection`
- **General corrected-defect reflection cocycle:**
  `RHTower.xiTransverseShiftPrimeDefect_reflection_cocycle`
- **General centered reflection law:**
  `RHTower.xiTransverseCenteredShiftPrimeDefect_reflection`
- **Completed-Xi telescope module:**
  `formal/GaloisForLFunctions/RHTower/XiEvenShiftPrimeDefectTelescope.lean`
- **Source cocycle:**
  `RHTower.xiTransverseShiftFiniteAbscissaSource_add`
- **Direct completed-Xi value telescope:**
  `RHTower.xiEvenShiftPrimeDefect_telescope`
- **Source-to-completed-Xi germ reflection:**
  `RHTower.xiTransverseEvenShiftUpperEndGerm_eq_xiEvenShiftPrimeDefect`
- **Actual even-shift matroid, Prop, and rank capstones:**
  `RHTower.xiEvenShiftPrimeDefectUpperEndCarrier_differentialMatroid_eq_pointedCollision`,
  `RHTower.xiEvenShiftPrimeDefectUpperEndCarrier_differentialIndependent_iff`, and
  `RHTower.xiEvenShiftPrimeDefectUpperEndCarrier_differentialMatroid_eRk`
- **All-valuation module:**
  `formal/GaloisForLFunctions/RHTower/XiTransverseShiftAllValuationLayerRank.lean`
- **All-valuation capstone:**
  `RHTower.xiTransverseShiftUpperEndCarrier_differentialIndependent_over_all_valuationLayers`
- **All-valuation arbitrary-family matroid capstone:**
  `RHTower.xiTransverseShiftUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision`
- **All-valuation Prop and rank interfaces:**
  `RHTower.xiTransverseShiftUpperEndCarrier_allValuation_differentialIndependent_iff` and
  `RHTower.xiTransverseShiftUpperEndCarrier_allValuation_differentialMatroid_eRk`
- **Hilbert-metric module:**
  `formal/GaloisForLFunctions/RHTower/XiTransversePrimeSourceHilbertMetric.lean`
- **Hilbert-metric capstones:**
  `RHTower.exists_xiTransversePrimeJetApertureGram_posDef` and
  `RHTower.exists_xiTransversePrimeJetApertureGram_det_pos`
- **Verification:** the new general-law leaf, refactored elliptic consumer, Xi source-rank leaf, and
  completed-Xi telescope leaf checked successfully with the repository toolchain; exact targeted
  module builds emitted all new `.olean` files.
- **Axiom audit:** the general finitary interface, general pointed-collision law, Xi exact matroid,
  Xi Prop interface, and Xi rank capstone report only `propext`, `Classical.choice`, and
  `Quot.sound`. The earlier absolute, all-valuation, and Hilbert-metric audits have the same
  baseline. The source cocycle, direct completed-Xi telescope, germ reflection, and actual
  even-family matroid/Prop/rank capstones also report exactly this baseline. The arbitrary-family
  all-valuation independence, matroid, Prop, and rank capstones have the same audit result. The
  general L-series relation, integral-shift completed-Xi exposure, and general germ reflection also
  report exactly this baseline. The raw completed-Xi reflection, corrected-defect reflection
  cocycle, and centered fixed-point law likewise report only this baseline.

## Falsifiers

- Failure of distinctness or positivity is now classified rather than excluded: `a=0` gives a
  loop and repeated shifts give parallel elements, with no other rank loss.
- The proof must use all prime-power coefficients only through an exact prime-profile theorem;
  silently replacing `D_a` by its prime-only part is invalid.
- Absolute independence over `C(s)` does not imply the relative theorem over `K_layer`; the proof
  separately uses a fresh valuation layer to kill the complete transverse packet.
- A theorem only about the known Suzuki coefficient identity is a bridge, not the rank result.
- No claim of scientific priority is allowed before an external specialist audit.

## Gates

- [x] exact theorem and RH role isolated from the fixed-aperture no-go
- [x] paper proof mechanism reduced to the live exponential-polynomial rigidity theorem
- [x] close the absolute prime-profile paper proof line by line
- [x] formalize the finite absolute family and targeted-check the leaf
- [x] classify zero shifts and repetitions by an arbitrary-family pointed collision matroid
- [x] expose exact independence and extended-rank interfaces for every indexed shift packet
- [x] reflect every integral source carrier into the actual corrected completed-Xi shift family
- [x] close and formalize the all-valuation relative strengthening
- [x] classify arbitrary all-valuation packets by the same exact pointed collision matroid
- [x] construct the deletion-robust positive Hilbert Gram for every finite aperture-jet packet
- [x] telescope the even-shift Xi correction and expose the actual completed-Xi family
- [ ] external novelty audit

## Log

- 2026-07-18 -- Created after the whole RHTower audit showed that `B_2=Theta_1` is a safe inner
  aperture. HTGeometry's prime exp/log rigidity suggests full differential rank of the surviving
  transverse family.
- 2026-07-18 -- Proved the finite positive-integral aperture theorem in Lean for the complete
  prime-power sources and transferred it to actual upper-end meromorphic carriers over the true
  rational coordinate field. Targeted leaf build and axiom audit passed. Scientific priority is
  deliberately left unclaimed.
- 2026-07-18 -- Strengthened the theorem to the complete scalar valuation-layer field. A relation
  uses finitely many old layers; an unused layer turns the new family into a rescaled prime
  exponential-polynomial packet, kills every aperture jet simultaneously, and leaves the old
  layers to separate on their private coordinates. The new leaf and axiom audit pass.
- 2026-07-18 -- Applied HTGeometry's cofinite Gram-polarization theorem to construct a concrete
  source-aperture Hilbert metric. Every finite shift-jet rectangle has a positive-definite square
  Gram after arbitrary finite prime deletion; targeted build and axiom audit pass.
- 2026-07-19 -- Closed the absolute hypothesis interface. Extracted the reusable finitary and
  pointed differential collision laws into a neutral HTGeometry module, proved the zero-shift
  source/carrier identities, and identified every arbitrary Xi shift family with the pointed
  collision matroid of its labels. Exact independence is now injective-plus-nonzero, and exact
  extended rank is the number of distinct nonzero shifts. Targeted source checks, exact module
  builds, and the five-capstone axiom audit pass.
- 2026-07-19 -- Closed the actual completed-Xi value gap. Proved the additive source cocycle,
  telescoped every shift `2m` into translated shift-two filtered sources, telescoped the actual
  logarithmic-derivative values and rational corrections, and identified the source carrier germ
  with that direct completed-Xi expression. The actual even-shift family now has its own exact
  pointed matroid, independence interface, and rank theorem. The exact leaf build and six-capstone
  axiom audit pass.
- 2026-07-19 -- Discharged the all-valuation theorem's finiteness, positivity, and injectivity
  hypotheses into an exact arbitrary-family interface. Over the differential field generated by
  the genuine coordinate and every scalar valuation layer, the represented matroid is still the
  pointed collision matroid of the shifts, so every packet has relative rank equal to its number
  of distinct nonzero labels. The exact source/build check and four-capstone axiom audit pass.
- 2026-07-19 -- Generalized the completed-Xi value reflection from shift two and even shifts to
  every natural shift. On the Euler half-plane, the transverse source is exactly the actual
  logarithmic Xi shift defect minus the corresponding archimedean logarithmic shift defect; this
  equality is then promoted to the upper-end germ. Consequently the arbitrary collision-matroid
  theorem is an actual corrected completed-Xi family law for all integral shifts. The exact leaf
  build, dependent even-leaf source check, and three-capstone axiom audit pass. The same module now
  proves the structural reflection law about `(1-a)/2`: the raw defect is fixed, the correction
  induces an anti-invariant cocycle, and half-cocycle centering restores exact invariance. The
  augmented exact build and four-capstone reflection audit pass.
