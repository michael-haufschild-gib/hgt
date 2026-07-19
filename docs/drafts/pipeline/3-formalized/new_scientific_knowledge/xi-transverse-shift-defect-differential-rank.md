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

The rational correction can now be removed completely. Its accumulated value is constructed as
an honest upper-end analytic element, proved to lie in the embedded rational coordinate field,
and added back to the corrected carrier. The resulting meromorphic element has germ

```text
logDeriv(xi)(s+2m) - logDeriv(xi)(s),
```

with no correction term. A new arbitrary-family affine base-gauge law proves that this raw family
has exactly the same represented differential matroid. Therefore zero raw shifts are loops,
repeated raw shifts are parallel, and every packet has rank equal to its number of distinct
nonzero half-shift grades. This remains true after adjoining every scalar prime-valuation layer.
Moreover, over each base the raw family and corrected prime-source family generate the same
embedded differential field, not merely the same matroid.

There is also an exact pairwise law. For a finite vertex set with distinct grades, one root of
grade zero, and any finite oriented edge family, the edge carrier is the literal value difference

```text
logDeriv(xi)(s+2 grade(head(e)))
  - logDeriv(xi)(s+2 grade(tail(e))).
```

The complete differential matroid of these pairwise values is exactly the rooted incidence
matroid of the oriented edge family, over both `C(s)` and the complete scalar valuation-layer
field. Thus every differential dependence among the pairwise values is already an ordinary
incidence-row dependence; selected-packet independence and rank reduce to the corresponding
incidence-matroid Prop and rank. This is a relation theorem for translates, not a theorem about
the zero set of `xi`.

The abstract incidence Prop is also discharged. A selected finite packet is differentially
independent exactly when every coefficient flow whose incoming and outgoing weights agree at
every vertex is zero. Conservation away from the chosen root already forces the root equation:
the total incoming-minus-outgoing sum vanishes because every oriented edge occurs once with each
sign. Equivalently, nonzero differential relations are exactly nonzero Kirchhoff circulations.
This single law handles loops, parallel edges, reversed edges, and general directed multigraph
packets over both base fields, without exposing the root equation as a separate hypothesis.

For the complete ordered pair family there is a stronger field statement. In general, an
arbitrary family is generated by all of its pairwise differences together with one anchor value.
The pairwise reporter alone generates the full family field if and only if it recovers that one
anchor; this is the exact common-translation obstruction and needs no zero, finiteness, or
independence hypothesis. For the graded Xi vertex family the zero-grade root is literally zero,
so the obstruction vanishes: all pairwise raw Xi differences generate exactly the same embedded
differential field as the vertex defects and, after correction removal, exactly the corrected
prime-source field. This holds over both the rational coordinate and all-valuation bases. Thus
passing from rooted completed-Xi values to the complete difference reporter loses no arithmetic
source information even though its individual edges satisfy all circulation laws.

The strict side of the common-mode law is no longer finite. For a differentially independent
family indexed by an arbitrary type, retaining one anchor and replacing every other coordinate by
its difference from that anchor preserves joint differential independence. Consequently the
anchor is hypertranscendental over the differential field generated by all ordered pairwise
differences, and that pairwise field is strictly smaller than the full family field. Finiteness and
decidable equality are internal proof devices for each finite gauge only; neither remains in the
field-obstruction interface.

The pairwise incidence theorem is no longer restricted to raw even shifts. For every finite
family of distinct integral shift labels, including odd shifts, the pairwise differences of the
transverse carriers have exactly the rooted incidence matroid over both bases. Their analytic
representatives are the literal differences of the two actual completed-Xi shift defects after
the exact archimedean corrections. Every packet therefore has the same Kirchhoff classification
and incidence rank, while the complete ordered pair family generates the full vertex differential
field. The even raw theorem is the stronger correction-removal specialization; no rationality of
an individual odd-shift correction is asserted.

Distinctness and a chosen zero-shift vertex are no longer necessary for the exact pairwise
matroid. For an arbitrary finite integral shift family, collapse vertices carrying the same shift
label, retain the finite set of occupied nonzero labels as columns, and delete the zero-label
column. The pairwise corrected completed-Xi values represent exactly this collision-quotient
incidence matroid over both bases. Hence repeated labels, zero-shift vertices, loops created by
label collisions, and all resulting rank loss are classified by one unconditional law rather than
excluded by injectivity, positivity, or root hypotheses. The earlier rooted theorem is the
distinct-label specialization of this quotient geometry. Its abstract independence Prop is also
discharged: coefficient flows must be conserved at every occupied nonzero shift label and at the
single collapsed zero-shift vertex. The zero-vertex equation is forced by total incidence, so it
is a conclusion of the quotient law rather than an additional hypothesis.

The complete pairwise generated-field law is now exact for arbitrary inhabited label families,
with no finiteness assumption on the index type. For every integral shift family, including
repetitions, the complete ordered pairwise corrected-Xi reporter generates the full vertex
differential field if and only if zero belongs to the shift range. If zero is absent, collapse to
the occupied range: those nonzero Xi values are jointly differentially independent, so any
retained anchor value is hypertranscendental over the pairwise field and the inclusion is strict.
If zero is present, its carrier is literally zero and the common mode is recovered. This iff
classification holds over both the rational coordinate and complete scalar valuation-layer bases;
the earlier finite collision-quotient and chosen-zero-root equalities are its finitary and rooted
specializations.

The uncorrected even-shift value reflection satisfies the same stronger classification directly.
For arbitrary finite grade families, literal pairwise differences of the actual completed-Xi
logarithmic translates represent the collision-quotient incidence matroid of the occupied grades,
over both bases. Repeated grades are collapsed, grade zero is the deleted column, and every packet
relation is exactly a quotient Kirchhoff circulation. Beyond the finite matroid statement, for an
arbitrary inhabited grade family the complete raw pairwise reporter recovers the raw vertex field
if and only if grade zero occurs; otherwise the absolute common mode remains hypertranscendental.
This removes the chosen-zero-root and distinct-grade hypotheses from the raw pairwise matroid,
Prop, Kirchhoff, rank, and generated-field theory, and removes finiteness from the generated-field
classifier. Combining the raw/corrected vertex-field identity with this iff gives the same exact
arbitrary-index threshold for recovery of the corrected prime-source field itself.

At the value level this incidence structure extends beyond even integral shifts. For arbitrary
complex shifts `a,b,c`, the raw pairwise differences form an additive cocycle, reverse orientation
negates the value, and the diagonal vanishes. Completed-Xi reciprocity fixes the `(a,b)` difference
under reflection about `(1-a-b)/2`; the earlier one-shift reflection is exactly the specialization
`b=0`. Thus the incidence cycle laws and the reflection law are two compatible structures on the
same pairwise translate values, with no assertion about their zero loci.

For integral pairs the exact archimedean correction is now incorporated into this reflection.
Corrected pairwise prime values still form the additive pair-groupoid cocycle, but reflection about
`(1-a-b)/2` changes them by an explicit correction cocycle. That cocycle is anti-invariant, and
adding one half of it produces an exactly reflection-fixed centered pair value. At tail shift zero,
both the corrected value and its cocycle reduce definitionally to the previous one-shift theory.

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
- **General affine-gauge matroid module:**
  `formal/GaloisForLFunctions/HTGeometry/DifferentialFamilyMatroidBaseGauge.lean`
- **General affine-gauge matroid law:**
  `GaloisForLFunctions.differentialFamilyMatroid_eq_of_affineBaseJetEquivalentFamilies`
- **Differential-constant incidence-matroid module:**
  `formal/GaloisForLFunctions/HTGeometry/DifferentialConstantLinearFamilyMatroid.lean`
- **General linear and pairwise-difference matroid laws:**
  `GaloisForLFunctions.HTGeometry.differentialFamilyMatroid_matrixLinearForms_eq_linearFamilyMatroid`
  and
  `GaloisForLFunctions.HTGeometry.differentialFamilyMatroid_pairwiseDifferences_eq_rootedIncidenceMatroid`
- **General circulation classification, root-equation discharge, and explicit Prop interface:**
  `GaloisForLFunctions.HTGeometry.isRootedIncidenceCirculation_iff_vertex_conservation`,
  `GaloisForLFunctions.HTGeometry.rootedIncidenceMatroid_indep_iff_no_nonzero_circulation`, and
  `GaloisForLFunctions.HTGeometry.rootedIncidenceMatroid_indep_iff_vertex_conservation`
- **General common-mode decomposition and exact pairwise obstruction:**
  `GaloisForLFunctions.HTGeometry.differentialAdjoin_range_eq_root_insert_pairwiseDifferences`,
  `GaloisForLFunctions.HTGeometry.differentialAdjoin_range_pairwiseDifferences_eq_iff_root_mem`,
  and
  `GaloisForLFunctions.HTGeometry.differentialAdjoin_range_pairwiseDifferences_eq_of_root_zero`
- **General strict common-mode and occupied-label classifier module:**
  `formal/GaloisForLFunctions/HTGeometry/DifferentialPairwiseCommonMode.lean`
- **General occupied-label reduction, strict loss, and exact pointed iff laws:**
  `GaloisForLFunctions.HTGeometry.pointedOccupiedLabelSupport`,
  `GaloisForLFunctions.HTGeometry.range_comp_eq_occupiedRange`,
  `GaloisForLFunctions.HTGeometry.range_pairwiseComp_eq_occupiedRange`,
  `GaloisForLFunctions.HTGeometry.range_comp_eq_occupiedLabels`,
  `GaloisForLFunctions.HTGeometry.range_pairwiseComp_eq_occupiedLabels`,
  `GaloisForLFunctions.HTGeometry.differentialIndependent_anchorDifferenceGauge_finite`,
  `GaloisForLFunctions.HTGeometry.differentialIndependent_anchorDifferenceGauge`,
  `GaloisForLFunctions.HTGeometry.anchor_not_mem_differentialAdjoin_pairwiseDifferences`,
  `GaloisForLFunctions.HTGeometry.differentialAdjoin_range_pairwiseDifferences_ne_of_differentialIndependent`,
  and
  `GaloisForLFunctions.HTGeometry.differentialAdjoin_range_gradedPairwiseDifferences_eq_iff_loop_mem_range_arbitrary`,
  with the finite compatibility interface
  `GaloisForLFunctions.HTGeometry.differentialAdjoin_range_gradedPairwiseDifferences_eq_iff_loop_mem_range`
- **Raw even completed-Xi rank module:**
  `formal/GaloisForLFunctions/RHTower/XiEvenShiftRawDefectDifferentialRank.lean`
- **Raw completed-Xi value reflection:**
  `RHTower.xiEvenShiftRawLogDerivDefectUpperEndCarrier_germ_eq`
- **Raw even-shift matroid, Prop, and rank capstones:**
  `RHTower.xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialMatroid_eq_pointedCollision`,
  `RHTower.xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialIndependent_iff`, and
  `RHTower.xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialMatroid_eRk`
- **Raw all-valuation matroid, Prop, and rank capstones:**
  `RHTower.xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollision`,
  `RHTower.xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialIndependent_iff`,
  and `RHTower.xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialMatroid_eRk`
- **Raw/corrected generated-field identities:**
  `RHTower.xiEvenShiftRawLogDerivDefectUpperEndCarrier_differentialAdjoin_eq_corrected` and
  `RHTower.xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_differentialAdjoin_eq_corrected`
- **Pairwise raw completed-Xi value identity:**
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_germ_eq`
- **Pairwise rational-base incidence matroid, Prop, and rank:**
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialMatroid_eq_rootedIncidenceMatroid`,
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialIndependent_iff`, and
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialMatroid_eRk`
- **Pairwise rational-base Kirchhoff interface:**
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialIndependent_finset_iff_vertexConservation`
- **Pairwise all-valuation incidence matroid, Prop, and rank:**
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_rootedIncidenceMatroid`,
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_iff`,
  and
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eRk`
- **Pairwise all-valuation Kirchhoff interface:**
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_finset_iff_vertexConservation`
- **Raw occupied-grade independence interfaces over both bases:**
  `RHTower.xiEvenShiftRawLogDerivDefectUpperEndCarrier_pointedOccupiedLabelSupport_differentialIndependent`,
  `RHTower.xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_pointedOccupiedLabelSupport_differentialIndependent`,
  `RHTower.xiEvenShiftRawLogDerivDefectUpperEndCarrier_pointedCollisionSupport_differentialIndependent`
  and
  `RHTower.xiEvenShiftRawLogDerivDefectUpperEndCarrier_allValuation_pointedCollisionSupport_differentialIndependent`
- **Exact arbitrary-label raw pairwise field classifiers over both bases:**
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_differentialAdjoin_eq_vertices_iff_zero_mem_range`
  and
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_allValuation_differentialAdjoin_eq_vertices_iff_zero_mem_range`
- **Exact arbitrary-label raw pairwise corrected-source recovery over both bases:**
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_differentialAdjoin_eq_corrected_iff_zero_mem_range`
  and
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_allValuation_differentialAdjoin_eq_corrected_iff_zero_mem_range`
- **Arbitrary-label raw pairwise collision matroid, Prop, Kirchhoff, and rank over both bases:**
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialMatroid_eq_pointedCollisionIncidenceMatroid`,
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialIndependent_iff_pointedCollisionIncidence`,
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_differentialIndependent_finset_iff_pointedCollisionVertexConservation`,
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_pointedCollisionIncidence_eRk`,
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollisionIncidenceMatroid`,
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_iff_pointedCollisionIncidence`,
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_finset_iff_pointedCollisionVertexConservation`,
  and
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_allValuation_pointedCollisionIncidence_eRk`
- **Complete pairwise/vertex generated-field identities:**
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_differentialAdjoin_eq_vertices`
  and
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_allValuation_differentialAdjoin_eq_vertices`
- **Complete pairwise/corrected-source generated-field identities:**
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_differentialAdjoin_eq_corrected`
  and
  `RHTower.xiEvenShiftRawPairDifferenceUpperEndCarrier_complete_allValuation_differentialAdjoin_eq_corrected`
- **Arbitrary complex pairwise value/reflection module:**
  `formal/GaloisForLFunctions/RHTower/XiPairwiseShiftValueReflection.lean`
- **Pairwise cocycle and reflection laws:**
  `RHTower.xiPairwiseShiftRawLogDerivDifference_cocycle`,
  `RHTower.xiPairwiseShiftRawLogDerivDifference_reflection`, and
  `RHTower.xiPairwiseShiftRawLogDerivDifference_nat_zero`
- **Corrected integral pairwise reflection laws:**
  `RHTower.xiPairwiseShiftPrimeDifference_eq_raw_sub_correction`,
  `RHTower.xiPairwiseShiftPrimeDifference_cocycle`,
  `RHTower.xiPairwiseShiftPrimeDifference_reflection_cocycle`, and
  `RHTower.xiPairwiseCenteredShiftPrimeDifference_reflection`
- **Corrected-pair tail-zero interfaces:**
  `RHTower.xiPairwiseShiftPrimeDifference_nat_zero` and
  `RHTower.xiPairwiseShiftReflectionCocycle_nat_zero`
- **All-integral pairwise corrected-Xi modules:**
  `formal/GaloisForLFunctions/RHTower/XiTransverseShiftPairwiseValue.lean`,
  `formal/GaloisForLFunctions/RHTower/XiTransverseShiftPairwiseDifferentialRank.lean`, and
  `formal/GaloisForLFunctions/RHTower/XiTransverseShiftPairwiseAllValuationRank.lean`
- **All-integral actual germ and complete generated-field laws:**
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_germ_eq`,
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_complete_differentialAdjoin_eq_vertices`,
  and
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_complete_allValuation_differentialAdjoin_eq_vertices`
- **All-integral pairwise incidence laws over both bases:**
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_eq_rootedIncidenceMatroid`
  and
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_rootedIncidenceMatroid`
- **All-integral pairwise Kirchhoff and rank interfaces:**
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_differentialIndependent_finset_iff_vertexConservation`,
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_eRk`,
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_finset_iff_vertexConservation`,
  and
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eRk`
- **General collision-quotient incidence module:**
  `formal/GaloisForLFunctions/HTGeometry/DifferentialPointedCollisionIncidenceMatroid.lean`
- **General arbitrary-label incidence law:**
  `GaloisForLFunctions.HTGeometry.differentialFamilyMatroid_gradedPairwiseDifferences_eq_pointedCollisionIncidenceMatroid`
- **General quotient circulation and all-vertex Kirchhoff interface:**
  `GaloisForLFunctions.HTGeometry.isPointedCollisionIncidenceCirculation_iff_vertex_conservation`,
  `GaloisForLFunctions.HTGeometry.pointedCollisionIncidenceMatroid_indep_iff_no_nonzero_circulation`,
  and
  `GaloisForLFunctions.HTGeometry.pointedCollisionIncidenceMatroid_indep_iff_vertex_conservation`
- **Arbitrary-label Xi incidence modules:**
  `formal/GaloisForLFunctions/RHTower/XiTransverseShiftCollisionIncidenceRank.lean` and
  `formal/GaloisForLFunctions/RHTower/XiTransverseShiftCollisionIncidenceAllValuationRank.lean`
- **Arbitrary-label Xi matroid, Prop, and rank laws over both bases:**
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_eq_pointedCollisionIncidenceMatroid`,
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_differentialIndependent_iff_pointedCollisionIncidence`,
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_pointedCollisionIncidence_eRk`,
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialMatroid_eq_pointedCollisionIncidenceMatroid`,
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_iff_pointedCollisionIncidence`,
  and
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_pointedCollisionIncidence_eRk`
- **Arbitrary-label Xi full quotient-Kirchhoff interfaces:**
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_differentialIndependent_finset_iff_pointedCollisionVertexConservation`
  and
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_allValuation_differentialIndependent_finset_iff_pointedCollisionVertexConservation`
- **Occupied nonzero-label independence interfaces over both bases:**
  `RHTower.xiTransverseShiftUpperEndCarrier_pointedOccupiedLabelSupport_differentialIndependent`,
  `RHTower.xiTransverseShiftUpperEndCarrier_allValuation_pointedOccupiedLabelSupport_differentialIndependent`,
  `RHTower.xiTransverseShiftUpperEndCarrier_pointedCollisionSupport_differentialIndependent`
  and
  `RHTower.xiTransverseShiftUpperEndCarrier_allValuation_pointedCollisionSupport_differentialIndependent`
- **Exact arbitrary-label pairwise field-recovery classifiers over both bases:**
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_complete_differentialAdjoin_eq_vertices_iff_zero_mem_range`
  and
  `RHTower.xiTransverseShiftPairDifferenceUpperEndCarrier_complete_allValuation_differentialAdjoin_eq_vertices_iff_zero_mem_range`
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
  module builds emitted all new `.olean` files. The strict common-mode leaf and both arbitrary-label
  Xi collision-incidence leaves also pass direct source checks and exact targeted module builds.
  The arbitrary-index occupied-range classifier and its corrected/raw Xi specializations pass the
  same scoped source checks and exact builds; only the incidence-matroid layer remains intrinsically
  finite.
- **Axiom audit:** the general finitary interface, general pointed-collision law, Xi exact matroid,
  Xi Prop interface, and Xi rank capstone report only `propext`, `Classical.choice`, and
  `Quot.sound`. The earlier absolute, all-valuation, and Hilbert-metric audits have the same
  baseline. The source cocycle, direct completed-Xi telescope, germ reflection, and actual
  even-family matroid/Prop/rank capstones also report exactly this baseline. The arbitrary-family
  all-valuation independence, matroid, Prop, and rank capstones have the same audit result. The
  general L-series relation, integral-shift completed-Xi exposure, and general germ reflection also
  report exactly this baseline. The arbitrary occupied-range reductions, strict common-mode law,
  exact pointed iff classifier, and corrected/raw Xi arbitrary-index specializations likewise have
  this baseline. The raw completed-Xi reflection, corrected-defect reflection
  cocycle, and centered fixed-point law likewise report only this baseline. The general affine
  base-gauge matroid law, rational correction membership, raw completed-Xi germ identity, and the
  raw rational-base and all-valuation generated-field/matroid/Prop/rank capstones all have the same
  audit result. The general differential-constant linear and rooted pairwise-difference matroid
  laws, the pairwise raw Xi value identity, and both pairwise incidence-matroid/Prop/rank triples
  likewise report only this baseline. The arbitrary complex pairwise reflection involution,
  orientation reversal, cocycle, completed-Xi reflection, and natural zero-tail specialization
  also report only this baseline. The full circulation/conservation equivalence, root-equation
  discharge, no-nonzero-circulation incidence law, explicit all-vertex conservation Prop
  interface, and all four Xi Kirchhoff interfaces likewise have only this baseline (the elementary
  non-root conservation equivalence itself does not need choice). The unconditional common-mode
  decomposition, exact anchor-recovery iff, zero-anchor corollary, and their pairwise Xi
  vertex-field and corrected-source specializations over both bases report only the standard
  baseline. The collision-quotient support, incidence matrix/matroid, ordinary Prop/rank
  interfaces, exact nonlinear matroid law, full quotient circulation/conservation equivalence,
  collapsed-zero equation discharge, and arbitrary-label Xi matroid/Prop/Kirchhoff/rank laws over
  both bases likewise report only this baseline. The occupied-label range reductions, strict
  common-mode loss, pointed field-recovery iff classifier, and its Xi occupied-support and exact
  field-recovery specializations over both bases also report only this baseline. The raw occupied-
  grade independence interfaces, exact zero-range field classifiers, arbitrary-label collision
  matroids, abstract Props, full quotient-Kirchhoff laws, and ranks over both bases have the same
  audit result. The actual corrected
  all-integral pairwise germ, complete generated fields, incidence matroids, Prop interfaces,
  Kirchhoff criteria, and ranks over both bases likewise report only this baseline. The corrected
  pairwise additive cocycle, archimedean reflection cocycle, centered invariant, and tail-zero
  interfaces have the same audit result.

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
- [x] remove root and distinct-grade hypotheses from the raw pairwise field and incidence theory
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
- 2026-07-19 -- Removed the even-shift correction from the theorem surface. Lifted arbitrary
  affine differential-base gauge invariance from whole-family independence to equality of the
  complete represented differential matroid. Constructed the accumulated even correction as an
  actual analytic rational-coordinate carrier and proved that adding it back gives the literal
  raw completed-Xi logarithmic-derivative shift germ. The raw family now has exact pointed
  collision, Prop, and rank laws over both `C(s)` and the field generated by all scalar valuation
  layers, and generates exactly the corrected family's differential field over either base.
  Targeted leaf builds and the expanded axiom audit pass. Novelty and any implication for Xi zeros
  remain unclaimed.
- 2026-07-19 -- Lifted the finite-shadow matrix criterion to equality of complete represented
  differential matroids and specialized it to rooted incidence rows. Applied that general law to
  literal pairwise differences between raw even translates of the completed Xi logarithmic
  derivative. For every finite oriented edge family, the exact differential matroid is its rooted
  incidence matroid over both the rational coordinate and all-valuation bases; selected-packet
  Prop and rank interfaces follow. The pairwise analytic germ identity, exact leaf builds, and
  expanded twenty-declaration axiom audit pass. This classifies translate relations only and does
  not assert a zero-location consequence.
- 2026-07-19 -- Extended the pairwise value structure from even integral grades to arbitrary
  complex shifts. Raw completed-Xi logarithmic-derivative differences now form an exact additive
  cocycle, reverse under edge orientation, vanish on the diagonal, and are fixed by reflection
  about `(1-a-b)/2`; the existing natural one-shift law is the zero-tail specialization. The exact
  leaf build and five-declaration axiom audit pass. No zero-location or RH consequence is claimed.
- 2026-07-19 -- Discharged the remaining abstract Prop in the pairwise incidence law. Proved that
  rooted incidence independence is equivalent to the absence of a nonzero Kirchhoff circulation,
  then exposed the incoming-equals-outgoing coefficient equations explicitly. Applied this exact
  criterion to finite packets of raw even completed-Xi differences over both the rational
  coordinate and all-valuation bases. Exact leaf checks/builds and the five-declaration axiom audit
  pass.
- 2026-07-19 -- Strengthened pairwise information preservation from matroid rank to generated
  differential fields. A general zero-root theorem shows that the complete ordered difference
  family and its vertex family generate the same differential field without finiteness or
  independence hypotheses. Applied it to raw even completed-Xi defects over both bases. Exact leaf
  checks/builds and the three-declaration axiom audit pass.
- 2026-07-19 -- Removed the even-shift restriction from the corrected pairwise theory. For every
  distinct integral shift family, pairwise transverse carriers now have the exact rooted incidence
  matroid, Kirchhoff Prop interface, and incidence rank over both bases; the complete pair family
  generates the vertex field, and its analytic germ is the difference of the actual corrected
  completed-Xi shift defects. An initially combined leaf exceeded artifact-emission memory and was
  replaced by independent value, rational, and all-valuation modules. All three exact builds and
  the ten-capstone axiom audit pass.
- 2026-07-19 -- Connected raw pairwise reflection to the corrected all-integral carrier values.
  Corrected pair differences retain the additive cocycle; their midpoint reflection defect is
  exactly the difference of archimedean corrections, this cocycle is anti-invariant, and
  half-cocycle centering restores exact reflection invariance. Tail zero recovers both existing
  one-shift declarations. The exact leaf build and seven-declaration axiom audit pass.
- 2026-07-19 -- Discharged the hidden root side-condition in every Kirchhoff interface. Proved
  generally that conservation at all non-root vertices forces conservation at the root by the
  zero total incidence law, then exposed full all-vertex conservation in the incidence-matroid
  independence criterion. The raw-even and all-integral pairwise Xi criteria now use the full
  vertex equations over both rational-coordinate and all-valuation bases. Only the neutral law
  and its three dependent leaves were rebuilt; source checks and expanded axiom audits pass.
- 2026-07-19 -- Replaced the zero-root-only generated-field observation by the unconditional
  pairwise common-mode decomposition: an arbitrary family field is generated by one anchor plus
  all ordered differences, and the differences alone recover it exactly iff they recover that
  anchor. Applied the exact obstruction to the zero-grade raw Xi family and connected the complete
  pair reporter directly to the corrected prime-source field over both bases. Direct source checks,
  the two touched-module final builds, and the expanded axiom audit pass.
- 2026-07-19 -- Removed injectivity and chosen-root hypotheses from the pairwise Xi incidence
  geometry. Constructed the occupied-nonzero-label quotient incidence matrix and proved generally
  that pairwise differences of a pointed collision family represent its exact incidence matroid.
  Specialized it to arbitrary finite integral Xi shift families over the rational-coordinate and
  all-valuation bases, with matroid, Prop, and rank interfaces. Repeated shifts and zero vertices
  are now classified rather than excluded. The quotient Prop was then discharged into explicit
  Kirchhoff conservation on occupied nonzero labels plus the collapsed zero vertex, whose equation
  follows from total incidence. Direct source checks, three exact leaf final builds, and the
  nineteen-declaration axiom audit pass. The generated-field half was then strengthened beyond
  finite incidence geometry: arbitrary occupied ranges now satisfy the exact zero-label iff law,
  and both corrected and raw Xi specializations work for arbitrary inhabited index types over both
  bases. The strict common-mode law itself is also arbitrary-index. Narrow source checks, the three
  exact dependent builds, and the expanded axiom audits pass.
