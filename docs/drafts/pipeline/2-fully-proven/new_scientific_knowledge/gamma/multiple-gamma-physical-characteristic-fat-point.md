# The physical multiple-Gamma characteristic pullback is a central fat point of order `r`

- **ID:** `multiple-gamma-physical-characteristic-fat-point`
- **Stage:** 2-fully-proven / complete formal-power-series **and convergent-germ** physical
  fat-point and Koszul cores Lean-formalized, together with the exact two-way comparison between
  the arc-contact filtration and the powered period-incidence scale and the numerical half of the
  five-way law `(13)`; what remains is canonicity for a pointed polarized source
- **Type:** THEOREM / PHYSICAL CHARACTERISTIC PULLBACK / DERIVED INCIDENCE SEAM
- **Scientific status:** `[PAPER PROOF COMPLETE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE — PROVISIONAL]`
  `[PARENT COMPONENTS SEPARATED] [NOT AN RH RESULT]`
- **Parents:**
  - `multiple-elliptic-gamma-transverse-constraint-depth.md`
  - `multiple-elliptic-gamma-relative-log-characteristic-arrangement.md`
  - `multiple-gamma-period-excess-closure-phase-transition.md`
  - `../../3-formalized/normal-crossing-derived-critical-excess-phase-law.md`
  - `../../1-in-progress/hypertranscendental-constraint-hodge-duality.md`
- **New analytic comparison surface:**
  `formal/GaloisForLFunctions/HTGeometry/MeromorphicRankThreeSourceBoundary.lean`
- **Lean physical comparison:**
  `formal/GaloisForLFunctions/HTGeometry/PhysicalCharacteristicIncidence.lean`
- **Lean physical Koszul core:**
  `formal/GaloisForLFunctions/HTGeometry/PhysicalCharacteristicIncidence.lean`
- **Lean meromorphic comparison:**
  `formal/GaloisForLFunctions/HTGeometry/MeromorphicPhysicalCharacteristicIncidence.lean`
- **Lean uniform-effectivity phase law:**
  `formal/GaloisForLFunctions/HTGeometry/PeriodIncidenceUniformEffectivity.lean`
- **Lean powered-incidence phase law:**
  `formal/GaloisForLFunctions/HTGeometry/PeriodIncidenceMultiplier.lean`
- **Lean filtration comparison and critical completion:**
  - `formal/GaloisForLFunctions/HTGeometry/PhysicalPullbackPeriodIncidenceComparison.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PhysicalArcCriticalCompletion.lean`
- **Lean convergent-germ ring `C{lambda}`:**
  `formal/GaloisForLFunctions/HTGeometry/ConvergentGermPhysicalArc.lean`
- **Lean source height and the order law:**
  - `formal/GaloisForLFunctions/HTGeometry/VeroneseSourceHeightIncidence.lean`
  - `formal/GaloisForLFunctions/HTGeometry/MultipleGammaPhysicalOrderLaw.lean`
- **Lean natural positive-tangency realization:**
  `formal/GaloisForLFunctions/HTGeometry/PhysicalTangencyNaturalSource.lean`
- **Lean canonicity of the comparison:**
  `formal/GaloisForLFunctions/HTGeometry/PhysicalArcComparisonCanonicity.lean`
- **Lean realization independence:**
  `formal/GaloisForLFunctions/HTGeometry/MultiplicativeRealizationComparison.lean`
- **Lean transport and frame blindness:**
  `formal/GaloisForLFunctions/HTGeometry/NormalCrossingSourceTransport.lean`
- **Lean osculation/effectivity discriminator:**
  - `formal/GaloisForLFunctions/HTGeometry/QuadraticPhysicalCharacterOsculation.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PhysicalOsculationEffectivityFracture.lean`
- **Unified-object parent:**
  `../../1-in-progress/hypertranscendental-source-fracture-hypercube.md`
- **Retired local-chart precursor:**
  `../../5-failed/polarized-framed-derived-source-character-principle.md`

## Statement

Let `r>=1`, let

```text
tau=(tau_0,...,tau_r),
```

and assume that the structural periods are linearly independent over `Q`.  Let

```text
R=C[x_0,...,x_r],
I_r=< product_(j!=i) x_j : 0<=i<=r >.                    (1)
```

For the generic order-`r` multiple elliptic Gamma logarithmic derivative, `I_r` is the exact
DA-relative translation annihilator.  Its logarithmic characteristic boundary is obtained by
putting `x_j=exp(lambda_j)-1`.

The physical spectral clock is not an arbitrary point of `C^(r+1)`.  It is the source-determined
one-parameter germ

```text
Phi_tau(lambda)=(lambda tau_0,...,lambda tau_r).          (2)
```

Let `A=C{lambda}` be the local ring of convergent germs at zero; the same result holds in
`C[[lambda]]`.  Pulling `(1)` through `(2)` gives

```text
Phi_tau^*(I_r)=(lambda^r).                                (3)
```

Consequently the classical physical characteristic scheme is the central fat point

```text
Spec A/(lambda^r).                                        (4)
```

Its reduced support is only `{0}`, but its scheme length is exactly `r`.

The derived pullback is equally explicit.  The pulled-back Koszul sequence has `r+1` terms, all
unit multiples of `lambda^r`.  It is equivalent by invertible row operations to

```text
(lambda^r,0,...,0).                                       (5)
```

The invertible linear row operation and its explicit inverse are formalized by
`unitScaledCofaceRowEquiv`; Lean proves its action on the physical coface generators is exactly
`(lambda^r,0,...,0)`.

Lean now also formalizes the finite exterior-basis complex of the row-reduced sequence.  It proves
that its differential squares to zero, identifies positive-degree cycles as the packets avoiding
the distinguished nonzero row, identifies boundaries as precisely the coefficientwise
`lambda^r`-divisible such packets, and proves that the number of surviving degree-`k` packets is
`choose(r,k)`.  The kernel of coefficient reduction is proved equal to the actual boundary range,
the reduction is proved surjective, and the resulting homology quotient is linearly equivalent to
the surviving packet family with coefficients in `A/(lambda^r)`.  This is the row-reduced module
form of `(6)`.  Lean also proves that the surviving packet type is empty and the quotient homology
is zero for `k>r`, giving the row-reduced form of `(7)`.  Over the physical formal local ring
`C[[lambda]]`, it computes the degree-`k` module length as `r choose(r,k)` and the total length as
`r 2^r`, formalizing `(8)` for the row-reduced model.

The original unit-scaled row is now connected to that model by the standard exterior Koszul
complex, rather than by an assigned transport structure.  The declarations
`physicalKoszulDifferential_ιMulti` and `physicalKoszulDifferential_sq` construct its alternating
differential and prove `d^2=0`; `unitScaledCofaceKoszulRowEquiv_functional` proves that the explicit
transpose row equivalence carries the original coface functional to `(lambda^r,0,...,0)`; and
`unitScaledCofaceKoszulChainEquiv_commutes` proves that the induced exterior-power equivalences
intertwine every consecutive differential.  Direct elaboration passes from the existing cache,
and these theorems use only `propext`, `Classical.choice`, and `Quot.sound`.

The actual formal exponential arc is now instantiated over `C[[lambda]]` as well.
`physicalFormalExponential_sub_one_eq_X_mul_unit` proves
`exp(tau_j X)-1=X U_j(X)` with `U_j(0)=tau_j` and hence a unit for every nonzero period.
`physicalFormalCofaceIdeal_eq_span_X_pow` proves that the resulting coface ideal is exactly
`(X^r)`; `physicalFormalCofaceIdeal_quotient_length` proves its length is `r`; and
`physicalFormalCofaceKoszulChainEquiv_commutes` transports its actual Koszul complex to
`(X^r,0,...,0)`.  The linearly independent source-frame version follows without an additional
hypothesis because linear independence makes every period nonzero.  Direct elaboration and the
axiom audit pass from the existing cache; the audited theorems use only `propext`,
`Classical.choice`, and `Quot.sound`.

This closes both the abstract unit-scaled chain-transport gap and the formal-power-series
exponential instantiation.

The convergent instantiation `A=C{lambda}` is now Lean as well.
`ConvergentGermPhysicalArc.lean` realizes `C{lambda}` as the subring of `Germ (nhds 0) C` whose
elements have an analytic representative, proves that a germ with nonzero value at the origin is a
unit, and instantiates the genuine exponential clock: `expArcGerm_eq_coordinate_mul` is
`exp(t lambda)-1 = lambda U_t` with `U_t(0)=t`, so `isUnit_expArcUnitGerm` makes every nonzero
period contribute a unit.  Hence `convergentCofaceIdeal_eq_span_pow` is exactly `(3)` over
`C{lambda}`, and `convergentCofaceKoszulRowEquiv_functional` and
`convergentCofaceKoszulChainEquiv_commutes` transport the actual Koszul complex to
`(lambda^r,0,...,0)`, giving `(5)` there.  `convergentGerm_rowReducedPhysicalKoszulHomology_length`
and `..._totalLength` then compute `(6)`--`(8)` over `C{lambda}`: degree-`k` length
`r choose(r,k)` and total length `r 2^r`, the same integers as over `C[[lambda]]`.

The ring theory needed for `(4)` is proved rather than assumed:
`exists_pow_mul_isUnit` shows every nonzero convergent germ is `lambda^n` times a unit (from the
mathlib isolated-zeros factorization), the ring is proved to be a domain,
`irreducible_convergentCoordinate` proves the coordinate irreducible, and
`IsDiscreteValuationRing ConvergentGerm` follows.  Therefore
`convergentCofaceIdeal_quotient_length` computes `length_(C{lambda}) (C{lambda}/Phi_tau^* I_r)=r`,
which is the fourth integer of `(13)` over the convergent local ring.  The first integer
`d_DA(Psi_r)=r` is `multipleEllipticGammaTransverseDADepth_eq_order`, and the second integer is now
Lean as well, so `(13)` is proved as a single theorem; see the order-law section below.

Hence

```text
H_k ~= (A/(lambda^r))^(choose(r,k)),   0<=k<=r,           (6)
H_k = 0,                                k>r.              (7)
```

Its exact derived amplitude is `r`; the total `A`-length of its homology is

```text
sum_k length_A(H_k)=r 2^r.                               (8)
```

## Proof

For every structural direction,

```text
exp(tau_j lambda)-1=lambda U_j(lambda),
U_j(0)=tau_j.                                             (9)
```

Rational independence implies `tau_j!=0`, so every `U_j` is a unit of `A`.  Therefore

```text
Phi_tau^*(product_(j!=i)x_j)
  =lambda^r product_(j!=i)U_j(lambda).                    (10)
```

Every generator is divisible by `lambda^r`, proving one containment in `(3)`.  Conversely, any
one product in `(10)` is `lambda^r` times a unit, so it generates `(lambda^r)`.  This proves `(3)`.

For the exact set-theoretic statement, if two distinct coordinates are resonant, then

```text
exp(lambda tau_a)=exp(lambda tau_b)=1.
```

Thus there are integers `m,n` with

```text
lambda tau_a=2 pi i m,
lambda tau_b=2 pi i n.                                   (11)
```

If `lambda!=0`, cross multiplication gives `n tau_a=m tau_b`, contradicting rational
independence.  Hence the physical clock meets the reduced pair arrangement only at `lambda=0`.

For `(6)`, write the pulled-back sequence as `lambda^r(U_0,...,U_r)`.  Since `U_0` is a unit,
elementary invertible row operations replace it by `(lambda^r,0,...,0)`.  The Koszul complex then
splits as the two-term complex on the non-zero-divisor `lambda^r` tensored with the exterior
algebra on `r` zero-differential generators.  Equations `(6)`--`(8)` follow.  `QED`

## The unification law

The same hierarchy now carries five independently defined integers:

```text
d_DA(Psi_r)                                  = r,
ht_src(Psi_r)                                = r,
rank_Q<1,tau_0,...,tau_r>-dim_R C            = r,
length_A(A/Phi_tau^*I_r)                     = r,
derivedAmplitude(L Phi_tau^* K(I_r))         = r.         (12)
```

Thus

```text
DA depth
 = source-constraint onset
 = period-rank excess
 = physical central multiplicity
 = physical derived amplitude.                              (13)
```

The equality is not a numerical coincidence produced by one definition: its terms come from
differential algebra, filtered source algebra, topological group embedding, local intersection
theory, and Koszul homology.

### `(12)`--`(13)` are one unconditional Lean theorem

`VeroneseSourceHeightIncidence.lean` computes the source height.  `MonoWide` bounds total degree
from below (`le_totalDegree_of_monoWide`), a coface generator attains the bound
(`totalDegree_prod_X`), so `isLeast_sourceDegrees` is `h(I_r)=r` as an `IsLeast` statement, not an
infimum that might be unattained.  Composed with the annihilator theorem
`daTranslationAnnihilator_eq_veroneseIdeal`, `isLeast_sourceDegrees_daTranslationAnnihilator` is
**`ht_src(Psi_r)=r` for the genuine source**: the least total degree of a nonzero difference
operator carrying the order-`r` logarithmic derivative into the differentially algebraic locus is
exactly `r`.

`MultipleGammaPhysicalOrderLaw.lean` then states `(13)` as one theorem.
`multipleGamma_physicalOrderLaw` proves, for a generic order-`r` family and a nondiscrete integral
period source, that all of

```text
d_DA(Psi_r),
ht_src(Psi_r),
ord_lambda(Phi_tau^* Ann_DA(Psi_r)),
length_(C{lambda}) (C{lambda}/Phi_tau^* Ann_DA(Psi_r)),
the powered period-incidence level detecting the arc image
```

equal `r`, with the contact and incidence statements sharp in both directions (level `r` attained,
level `r+1` provably missed).  The derived amplitude of `(12)` is the same integer in its complex
form, carried by the Koszul chain equivalences rather than by a number.  `#print axioms` clean.

The original normal-crossing derived critical locus has amplitude `r-1`, while its physical
pullback has amplitude `r`.  This absorbs the previously unexplained formula

```text
ht_src=original derived amplitude+1.                       (14)
```

The extra degree is the forced physical incidence direction.  Pullback converts it into genuine
derived excess rather than an external correction term.

## General contact-order correction `[BRIDGE + NEW DISCRIMINATOR]`

For a general augmented DA-relative annihilator ideal `J` and a physical exponential arc
`Phi_tau`, define

```text
mu_phys(J,tau)=ord_lambda(Phi_tau^* J).                   (14a)
```

This is the standard order of contact of an ideal along an arc.  If `h(J)` is the least
augmentation degree of a nonzero element of `J`, then

```text
mu_phys(J,tau)>=h(J).                                     (14b)
```

Equality holds exactly when some degree-`h(J)` initial form of `J` does not vanish on the physical
tangent vector `tau`.  If all lowest initial forms vanish there, contact order rises.  Define the
physical tangency excess

```text
tang_phys(J,tau)=mu_phys(J,tau)-h(J).                     (14c)
```

Contact loci and orders along arcs are parent arc-space theory; `(14a)`--`(14c)` are `[BRIDGE]`,
not new invariants of algebraic geometry.  Their HT consequence is a hard discriminator:

```text
[NO-GO] DA source height alone determines physical obstruction multiplicity.
```

**Positive successor:** the zero-tangency class `tang_phys=0` is the maximal class on which source
height survives physical realization unchanged.  The multiple-Gamma coface hierarchy lies in this
class because every relevant initial form is a monomial nonzero at a period vector with no zero
coordinate.

### `(14a)`--`(14c)` for the squarefree hierarchy are unconditional Lean

`PhysicalArcContactVeronese.lean` computes the contact order of the squarefree annihilator along
the physical exponential arc `X_j -> tau_j lambda`:

- `physicalArcPullback`, `physicalArcPullback_monomial`, `physicalArcPullback_prod_X` -- the arc
  pullback and its value on monomials and coface generators;
- `pow_dvd_physicalArcPullback_of_monoWide` and
  `pow_dvd_physicalArcPullback_of_mem_veroneseIdeal` -- **`mu_phys(I_r,tau) >= r`**: every element
  of the ideal is monomial-wide of width `r`, so its pullback is divisible by `lambda^r`;
- `physicalArcPullback_generator_ne_zero` -- **the bound is attained**: with no vanishing period a
  coface generator pulls back to a nonzero constant times `lambda^r` and is not divisible by
  `lambda^{r+1}`;
- `veroneseIdeal_physicalArcContact` -- **`mu_phys(I_r,tau) = r = h(I_r)`, that is
  `tang_phys(I_r,tau) = 0`.**

So the multiple-Gamma coface hierarchy provably lies in the zero-tangency class.

The discriminator itself is also formalized.  `positiveTangencyWitness` is an explicit operator
whose linear part cancels along the arc:

```text
g  = X_0 - X_1 + X_0^2,   tau = (1,1),   pullback = lambda^2,
g' = X_0,                 tau = (1,1),   pullback = lambda.
```

`physicalContact_not_determined_by_leastDegree` proves that both have a nonzero linear
coefficient — the same least augmentation degree — while `g'` has contact one and `g` has contact
two.  Hence source height alone does not determine physical obstruction multiplicity, which is the
`[NO-GO]` of this section, and zero tangency is a genuine restriction rather than an automatic
consequence.  `#print axioms` clean.

### Positive tangency is realized by an actual special function

`PhysicalTangencyNaturalSource.lean` replaces the engineered witness by a genuine multiple elliptic
gamma.  It first makes `(14a)`--`(14c)` exact at the level of augmentation degree: `augDegree` is
the least total degree of a monomial occurring in an operator,
`pow_augDegree_dvd_physicalArcPullback` is `(14b)` (`mu_phys >= h`), and
`isLeast_augDegrees_veroneseIdeal` is `h(I_r)=r` in that reading, matching the total-degree form.

The natural realization is the additive resonance `tau_c = tau_a + tau_b`.  The group identity
`T_c = T_a T_b` makes

```text
Q = (1 + x_a)(1 + x_b) - (1 + x_c)
```

annihilate every germ (`xApply_resonanceOperator`), hence lie in the differential-algebraic
translation annihilator of the actual logarithmic derivative.  Lean proves
`augDegree Q = 1` and `Phi_tau^* Q = tau_a tau_b lambda^2` with contact order exactly two
(`augDegree_resonanceOperator`, `physicalArcContact_resonanceOperator`), so
`resonantSource_positiveTangency` gives `tang_phys = 1` for a genuine source rather than a
constructed constraint.  `resonantFrame_positiveTangency` instantiates it at the explicit frame
`(i, 2i, 3i)`.

The same computation shows the independence hypothesis of the annihilator theorem is not
removable: `resonanceOperator_not_mem_veroneseIdeal` proves `Q` is outside `I_r` for `r >= 2`
because `I_r` has augmentation degree `r`, so
`resonantSource_annihilator_strictly_larger` proves that on a resonant frame the annihilator
strictly contains `I_r` and its extra element has positive tangency.  Integral independence is
therefore exactly what forces the zero-tangency class.  `#print axioms` clean.

The positive-tangency test is now exact at source-geometric level.  For the Hankel conic on the
rank-three source `(1,alpha,alpha^2)`, Lean proves source height two and physical contact order three.
It also proves that the same nondiscrete source supports another quadratic constraint of contact
order two.  Hence physical contact and global source effectivity are independent axes; neither can
replace the other.  What remains is a natural special-function realization rather than an
engineered constraint source.

## What the latest period-incidence theorem adds

The bounded radial period symbol

```text
w(q)=q/(1+|q|)                                             (15)
```

loses no embedded period data: `q=w(q)/(1-|w(q)|)`.  Hence its unordered spectrum reconstructs
the complete integral period submodule.  On `ell^infty` of the nonzero period modes, multiplication
by `w` canonically realizes all three incidence phases when the period group is nondiscrete:

```text
w             is exact;                                  phase I
sqrt(|w|)     is in closure(range M_w) but not range;     phase II
1             is outside closure(range M_w).              phase III       (16)
```

The square-root target is the positive self-dual half-density of the incidence symbol.  It is a
distinguished section produced by the source, not an arbitrary closure witness.

The diagonal and fractional-power facts in `(15)`--`(16)` are `[BRIDGE]` operator theory.  Their
role is to identify the analytic completion of the physical fat-point obstruction, not to supply
novelty by themselves.

The new period-gauge complementarity theorem gives the nonclosed-range phase a strong positive
counterpart.  For every integral period submodule, failure of a continuous incidence left inverse
forces all global meromorphic source-fixed gauges to be constant.  Thus the rank-three
multiple-Gamma source trades global attainment for gauge rigidity: one calibration separating
constants reconstructs the meromorphic primitive even though no uniform incidence inverse exists.
Conversely, a nonconstant periodic gauge can occur only in the discrete uniformly effective phase.
See
`../../3-formalized/not_new_scientific_knowledge/period-gauge-attainment-complementarity.md`.

For the full order-`r` source, `(15)` is only the atomic incidence coordinate.  Equation `(3)`
forces the complete physical multiplier and its positive half-density to be

```text
m_r(q)=w(q)^r,
b_crit,r(q)=sqrt(|m_r(q)|)=|w(q)|^(r/2).                 (16a)
```

Thus the normalized critical exponent is always one half, while its unnormalized vanishing order
is `r/2`.  Using `sqrt(|w|)` for every order would discard the fat-point multiplicity and is
therefore nonconservative.  Lean now proves the complete powered family `(16a)`, including the
pointwise identity with `sqrt(|w^r|)` and its exact/closure-only/exterior trichotomy.

More generally, put

```text
b_(alpha,r)(q)=|w(q)|^(r alpha),   alpha>=0.              (16b)
```

For a nondiscrete period source, elementary cutoff division gives the exact fractional phase law

```text
alpha=0:       b_(alpha,r) is outside closure(range M_(w^r));
0<alpha<1:     b_(alpha,r) is in closure but not in the range;
alpha>=1:      b_(alpha,r) is in the range.               (16c)
```

The involution `alpha |-> 1-alpha` exchanges target vanishing order with inverse blow-up order.
Its unique fixed point is `alpha=1/2`, giving `(16a)`.  This is a theorem about observability
regularity relative to a constraint, not a temporal evolution law.

Equation `(16c)` is `[BRIDGE]` interpolation/source-condition theory.  The candidate-new content is
that the exponent `r` is forced simultaneously by the DA annihilator, the physical fat point, and
the period-rank excess rather than chosen as a regularization parameter.

## The object indicated by `(13)`

The latest theorem rules out treating the DA characteristic variety and the topological period
radical as separate decorations.  They are primal and holomorphic-dual realizations of one
**derived physical incidence germ**:

```text
DPhysChar_DA(F)
  = L Phi_F^*(derived DA characteristic object),          (17)
```

retaining its integral period lattice and positive half-density section.

There is a further necessary refinement.  Componentwise unit changes of the pulled-back coface
generators preserve the fat point and the quasi-isomorphism class of its Koszul complex while
changing source phase and orientation.  Thus even the full unframed derived germ is
orientation-blind.  The conservative candidate must retain the integral source presentation,
logarithmic lift, polarization, and calibration.  The physical character germ is therefore a
local chart of the stronger six-channel source-effectivity fracture object.  Its earlier promotion
as a separate complete ontology has been retired by the anti-epicycle gate.

This orientation no-go now has an exact analytic physical model.  For any finite source defect
product, full reversal multiplies the complete germ by
`(-1)^rank exp(-(sum_i tau_i)lambda)`.  On the balanced even-rank locus the multiplier is one, so
opposite source orientations have literally identical analytic germs and hence identical derived
pullbacks.  The positive replacement is the explicit reversal cocycle and its source-produced
anomaly torsor together with a source-effectively normalized polarized trivialization, not another
derived refinement of the fat point.  The Gamma periodic-gauge collision forbids a canonical
trivialization from bare source syntax; see
`../../3-formalized/new_scientific_knowledge/physical-defect-orientation-anomaly.md`.

For the multiple-Gamma hierarchy, `(17)` is the explicit derived fat point `(5)`--`(6)`.  It
compresses the previously forced channels rather than adding a seventh one:

1. the source action and integral lattice are recovered from the bounded period symbol;
2. the DA module supplies the holomorphic characteristic equations;
3. the pullback supplies their actual physical incidence and derived coherence;
4. `sqrt(|w|)` supplies polarization, critical bornology, and a source-produced section;
5. the small-period germ supplies the controlled nonattainment data.

The fat point alone does not determine item 5.  Two period embeddings can have identical physical
ideal `(lambda^r)` but different Diophantine approximation germs.  The unified object must retain
the full embedded period symbol together with the fat-point filtration; equality of multiplicity
does not reconstruct quantitative closure rates.

## Strong conjecture and exact open core

> **[CONJECTURE — NORMALIZED DERIVED PHYSICAL CHARACTERISTIC PRINCIPLE.]**  For every
> source-effectively normalized constrained hypertranscendental system, continuation, positivity,
> spectral realization,
> monodromy, and boundary-condition obstructions are conservative realizations of the derived
> physical characteristic germ `(17)`.  Algebraic support records exact degeneracy; its derived
> nilpotent filtration records constraint depth; the topology of the integral period embedding
> records cofinal attainability; and, on a source-effectively normalized stratum with trivial
> joint-fixed reporter kernel, the source half-density is the distinguished polarized effective
> section.

The conjecture is stronger than the topological-radical proposal.  Two systems may have the same
reduced characteristic support and the same non-Hausdorff period quotient while having different
fat-point order or derived homology.  Such systems must have different obstruction theories.

`[OPEN CORE — FILTRATION HALF NOW CLOSED]` The comparison morphism between the fat-point
filtration

```text
A superset (lambda) superset ... superset (lambda^r)       (18)
```

and the analytic small-period scale of `(15)` is constructed and proved exact in
`PhysicalArcCriticalCompletion.lean`: `lambda^k` realizes as the powered multiplier `w^k`, the
`lambda`-adic Rees filtration is exactly the preimage of the powered incidence filtration, and the
order-`r` central source class produces the closure-only half-density `|w|^(r/2)` of `(16a)`.

Canonicity is proved too.  `PhysicalArcComparisonCanonicity.lean` upgrades the comparison to a
homomorphism of `C`-algebras `arcEvalHom` into the bounded incidence space, and since the
arc-coordinate scale is free on the arc coordinate, `arcEvalHom_unique` proves it is the **only**
algebra map with the normalization `lambda -> w`.  Hence `arcEval_canonical`: pointing `1 -> 1`,
every power `lambda^k -> w^k`, and therefore the whole exact filtration comparison
(`arcEvalHom_mem_poweredRange_iff`) are forced by that single normalization rather than chosen; and
the polarization exponent is the unique fixed point of the source-condition duality.  `#print
axioms` clean.

A second analytic realization of the same source syntax reproduces the comparison unchanged.
`MultiplicativeRealizationComparison.lean` uses the multiplicative form -- finite products of
integer powers of structural translates rather than difference operators on the logarithmic
derivative.  `mem_multiplicativeDaAnnihilator_iff` proves the two realizations have literally the
same annihilator, `multiplicativeRealization_comparison` proves that a differentially algebraic
translate product has the same arc-contact order, the same powered period-incidence level and the
same closure-only half-density, and `realizationIndependent_canonicalComparison` combines this with
uniqueness of the normalized algebra map.  So the pointed polarized comparison is an invariant of
the source syntax, not of one realization of it.

The transport question of item 6 is settled in general rather than family by family.
`NormalCrossingSourceTransport.lean` defines a source realization of order `r` to be one whose
differential-algebraic translation annihilator is the squarefree degree-`r` ideal, and
`physicalPackage_of_isNormalCrossingSource` proves that the whole physical package -- source
height, arc-contact order with its sharp upper bound, powered period-incidence level with its sharp
upper bound, and the closure-only half-density -- is computed from `r` alone.  So any two
realizations with the same normal-crossing ideal have literally the same package, and the
Barnes/multiple-sine comparison follows from the classical ideal computation with no further
analytic input.  `isNormalCrossingSource_daTranslationAnnihilator` and
`multiplicativeDaAnnihilator_eq_preimage` record the two realizations already built.

What is left is the Lean construction of the Barnes/multiple-sine object itself, which is not a
theorem of this card.  Its convergent route is the genus-`r` Weierstrass product over the cone
`N^r`; the required cone summability reduces to `summable_fintype_pi_product_of_nonneg` and the
factor estimate to the closed form `E_r'(u) = (-1)^r u^r exp(S_r(u))`.

## No-gos and positive successors

### Reduced-support no-go

The reduced physical characteristic set is `{0}` for every generic order `r>=1`.  It cannot see
constraint depth, period excess, or the distinction between orders.

**Positive successor:** the nonreduced pullback `A/(lambda^r)` recovers `r` exactly, and the full
derived pullback recovers the exterior coherence profile `(6)`.

### Nonzero-resonance no-go

No hidden nonzero exact resonance causes the generic multiple-Gamma closure defect.

**Positive successor:** obstruction is concentrated in the order and topology of approach to the
unique central degeneracy.  Search should move from new zeros to the filtered central germ.

### Ordinary inverse-limit no-go

Every finite modal restriction of the incidence multiplier is bijective, so the ordinary inverse
system has no algebraic lifting obstruction.

**Positive successor:** the obstruction is bornological and derived: bounded global lifts fail,
while the fat-point and Koszul filtrations retain the collapsed transverse constraints.

### Arbitrary-completion no-go

Equipping the domain with the graph norm of the inverse forces exactness by definition and has no
scientific content.

**Positive successor:** an admissible completion must be reconstructed from `(18)` and preserved by
a second independent source realization.

### Package no-go: the physical package is blind to the frame

`physicalPackage_frame_blind` proves that any two nonvanishing period frames of the same order give
the same arc-contact order, the same sharp non-divisibility at the next level, and the same
convergent fat-point length.  The package therefore carries no information beyond `r`, and cannot
separate two source families that share the normal-crossing ideal.

**Positive successor:** what the package discards, the bounded symbol spectrum retains.
`physicalPackage_blind_symbolSpectrum_separates` pairs the blindness statement with
`regularizedPeriodSpectrum_eq_iff`: the unordered symbol spectrum determines the embedded period
module exactly.  The conservative invariant is the pair, never the package alone.  This is the
sharpened form of the fat-point completeness no-go below.

### Fat-point completeness no-go

The local scheme `A/(lambda^r)` fixes multiplicity and derived coherence but not the rate at which
nonzero integral periods approach zero.

**Positive successor:** retain the pair consisting of the `lambda`-adic Rees filtration and the
complete controlled germ of the embedded period symbol.  The proposed comparison
`lambda^k |-> w^k` couples them without pretending that either reconstructs the other.

## Lean status of the filtration comparison

`PhysicalPullbackPeriodIncidenceComparison.lean` builds the comparison asked for in item 1 of the
next-search list:

- `norm_eval_le_sum_norm_coeff` and `arcEvalVector` -- evaluating an arc-coordinate polynomial at
  the regularized period symbol is bounded, because the symbol has norm at most one, so it lands in
  the bounded period-incidence space;
- `arcEvalVector_X_pow` -- **`lambda^k |-> w^k`**;
- `arcEvalVector_mem_range_of_X_pow_dvd` -- **the comparison is filtration preserving**: a
  polynomial divisible by `lambda^k` evaluates into the range of multiplication by `w^k`;
- `veroneseIdeal_arcEval_mem_poweredRange` -- applied through the physical arc pullback, the whole
  squarefree degree-`r` annihilator lands in the order-`r` powered incidence scale;
- `arcEval_physicalArcPullback_prod_X` -- at a coface generator the comparison is exactly the
  order-`r` symbol scaled by the period product.

So the `lambda`-adic filtration of the physical pullback maps into the powered source-regularity
filtration, with the coface generators hitting the symbol exactly.

The ideal-level Rees filtration asked for in item 5 is built in the same module:

- `arcContactFiltration` -- operators of physical contact order at least `k`, as the comap of
  `(lambda^k)` along the arc pullback, hence an ideal;
- `arcContactFiltration_antitone`, `arcContactFiltration_zero` and
  `arcContactFiltration_mul_le` -- it is a descending multiplicative (Rees) filtration: contact
  orders add under multiplication;
- `veroneseIdeal_le_arcContactFiltration` and
  `veroneseIdeal_not_le_arcContactFiltration_succ` -- **the squarefree annihilator sits exactly at
  level `r`**, no higher;
- `arcContactFiltration_arcEval_mem_poweredRange` -- **the source-natural comparison**: level `k`
  of the Rees filtration evaluates into the range of the order-`k` powered period-incidence
  multiplier.

`#print axioms` clean.

### The critical completion makes the comparison exact

`PhysicalArcCriticalCompletion.lean` closes the passage from polynomial arcs to the analytic scale
and upgrades the comparison from preserving to exact.

The completion is the scale of germs holomorphic on a disc of radius larger than one; it is the
completion adapted to the symbol, because `|w|<1` always and the critical value one is approached
only along periods of unbounded size.  `discEvalVector` evaluates such a germ at the period
symbols, `exists_bound_on_closedUnitBall` supplies its boundedness, and
`discEvalVector_polynomial` identifies the polynomial arc scale as a subscale.

- `exists_nonzeroPeriod_weight_tendsto_zero` -- for a nondiscrete period group the symbols of
  nonzero periods accumulate at zero;
- `X_pow_dvd_of_eval_bound` and `exists_differentiableOn_pow_factor_of_bound` -- **order
  detection**: a bound `|f(w_i)| <= C|w_i|^n` along a vanishing sequence forces divisibility by
  `lambda^n`, respectively a holomorphic factorization `f=z^n g`.  The holomorphic half peels one
  power at a time through the removable-singularity form of `dslope`;
- `discEvalVector_mem_poweredRange_iff` -- **the comparison is exact on the critical completion**:
  the evaluation lies in the range of the order-`n` powered multiplier exactly when the germ has
  contact order at least `n`;
- `arcEvalVector_mem_poweredRange_iff` -- the same for the polynomial scale;
- `mem_arcContactFiltration_iff_arcEval_mem_poweredRange` -- **the arc-contact Rees filtration is
  exactly the preimage of the powered period-incidence filtration**, not merely mapped into it;
- `veroneseIdeal_arcEval_poweredRange_exact` -- the squarefree annihilator is detected at level
  exactly `r`: its whole arc image is in the order-`r` range, and a coface generator is provably
  outside the order-`r+1` range;
- `veroneseIdeal_criticalComparison` -- the order-`r` package: exact level, the exact target `w^r`,
  and the source-produced closure-only half-density `|w|^(r/2)` of `(16a)`.

The genuine analytic clock, not only its linearization, lives on the same completion:
`expArcUnit` is the holomorphic unit factor of `exp(t z)-1`, `mul_expArcUnit` and `expArcUnit_zero`
prove `exp(t z)-1 = z U_t(z)` with `U_t(0)=t`, `exponentialCofaceProduct_eq` factors a coface
product of `r` genuine clock factors as `z^r` times a nonvanishing unit, and
`exponentialCofaceProduct_poweredRange_exact` proves that its incidence image sits at level `r` of
the powered scale and provably not at level `r+1`.  So the nonlinear physical clock has the same
exact contact order as the linear arc, which is the analytic-scale form of zero tangency.

`#print axioms` clean.

## Where to look next

The next search is not for another RH criterion and not for more abstract topology.

1. **Physical pullback comparison.**  Construct the map from the multiple-Gamma DA coface module to
   its period-incidence scale, prove `lambda^k |-> w^k`, and identify the `lambda`-adic filtration
   with the powered source regularity filtration.
2. **Global meromorphic realization.**  The newly formalized rank-three meromorphic boundary
   fingerprint has kernel exactly the complex constants, and one calibration makes it injective.
   Its restriction to genuine meromorphic exponential modes is now proved to have exactly the DA
   physical coface symbol, with common central degeneracy spectrum.  The remaining step is not
   another fibrewise symbol calculation: construct the source-forced critical completion and
   compare its bounded principal incidence realization with `w^r`.
3. **Transference theorem.**  Relate small primal period combinations to near-resonance of the
   appropriate unitary dual realization.  The holomorphic exponential character and the unitary
   Pontryagin character are different real forms; the comparison between them is part of the
   polarization, not a harmless identification.
4. **Rigidity test.**  Find a source with the same reduced pair arrangement but a different physical
   pullback multiplicity.  If the predicted obstruction phases do not change, `(17)` is too rich;
   if they do, reduced-support theories are conclusively nonconservative.
5. **Tangency/effectivity interaction.**  The exact conic source model with `tang_phys=1` is
   formalized, as is its independence from the nondiscrete effectivity phase, the ideal-level
   arc-contact Rees filtration, and its exact comparison with the powered period-incidence
   filtration on both the polynomial and the analytic scale.  Positive tangency is now realized in
   a genuine multiple elliptic gamma with a resonant period frame, not only in the universal
   constraint source, and the same operator shows that integral independence is necessary for the
   annihilator theorem.  This item is closed.
6. **Barnes/multiple-sine realization.**  After the meromorphic comparison, perform the same
   physical pullback for the Barnes/multiple-sine source, whose classical normal-crossing ideal is
   already known to agree, and test whether the complete derived and half-density data agree.

Only after these general HT comparisons exist should a zeta source be considered.

## RH pressure test only

`[CONJECTURE; NOT AN RH RESULT]` In a future zeta realization, the critical zeros would be the
self-dual global degeneracy spectrum of the polarized derived physical characteristic object, while
the central fat-point filtration would govern whether finite prime--archimedean constraints attain
a global state.  The zeta object, comparison morphisms, and any assertion about zeros remain
unconstructed.

## Parent theory and novelty gate

The following are parent mathematics and not claimed as new:

- the kernel of the complex exponential;
- factorization `exp(a lambda)-1=lambda times a unit` for `a!=0`;
- extension of ideals and invariance under unit factors;
- Koszul complexes on associate elements and grade sensitivity;
- multiplication-operator closed-range criteria and fractional source conditions;
- unlikely intersections with algebraic subtori;
- Kronecker/Khintchine transference between small linear forms and simultaneous approximation.

Primary adjacent checks include:

- Narukawa, multiple elliptic Gamma hierarchy, `https://arxiv.org/abs/math/0306164`;
- Kato, rational-period differential algebraicity, `https://doi.org/10.1619/fesi.64.225`;
- Capuano--Masser--Pila--Zannier, unlikely intersections in tori,
  `https://arxiv.org/abs/1511.00607`;
- German--Moshchevitin, transference and linear independence,
  `https://arxiv.org/abs/2103.12113`.
- Ein--Lazarsfeld--Mustaţă, contact loci and orders of ideals along arcs,
  `https://arxiv.org/abs/math/0303268`.

Targeted searches located those parent mechanisms but no source computing the multiple-Gamma
DA-relative physical pullback as `(lambda^r)`, identifying its full Koszul homology, or proving the
five-way equality `(13)`.  This is preliminary negative evidence, not priority certification.

### Significance verdict

- The central-resonance lemma and the principal-ideal calculation alone are routine.
- Equality `(13)` changes the architecture: DA depth, period excess, source onset, and physical
  derived multiplicity become shadows of one canonical pullback rather than analogous integers.
- The result warrants a central theorem in the multiple-Gamma/constraint-Hodge paper if the parent
  annihilator theorem survives independent audit.
- Fields-scale significance requires the comparison morphism in `(18)` and a second analytic
  realization, not merely the equality of invariants.

## Gates

- [x] physical logarithmic clock defined
- [x] reduced physical intersection proved to be `{0}`
- [x] physical pullback ideal computed as `(lambda^r)`
- [x] central scheme length computed as `r`
- [x] physical derived amplitude computed as `r`
- [x] complete physical Koszul homology computed
- [x] five-way unification law isolated
- [x] every no-go paired with a positive successor
- [x] preliminary cross-field parent and novelty gate run
- [x] general arc-contact parent identified and separated from the HT residue
- [x] physical tangency excess isolated as the next discriminator
- [x] exact positive-tangency source model formalized
- [x] same-source osculation/effectivity independence formalized
- [x] finish Lean formalization of the pullback ideal core
- [x] formalize the invertible row reduction to `(lambda^r,0,...,0)`
- [x] ideal-level physical arc-contact Rees filtration constructed and compared source-naturally
      with the powered period-incidence filtration
- [x] the comparison proved exact in both directions on the polynomial arc scale
- [x] critical completion constructed and the comparison proved exact on the analytic
      (non-polynomial) scale
- [x] the genuine exponential clock, not only its linearization, proved to have contact order
      exactly `r` on the critical completion
- [x] convergent-germ ring `C{lambda}` constructed, proved a discrete valuation ring, and the
      physical pullback ideal computed there as `(lambda^r)` with quotient length `r`
- [x] the source-height identity `ht_src(Psi_r)=r` of `(13)` in Lean
- [x] the five-way law `(13)` stated and proved as a single unconditional Lean theorem
- [x] `(6)`--`(8)` computed over the convergent local ring as well as the formal one
- [x] `(14b)` and `h(I_r)=r` formalized in the augmentation-degree reading
- [x] positive physical tangency realized in a genuine multiple elliptic gamma (resonant frame),
      with the resulting proof that integral independence is necessary for the annihilator theorem
- [x] canonicity of the comparison for a pointed polarized source
- [x] a second analytic realization (multiplicative translate products) reproducing the same
      pointed polarized comparison
- [x] transport proved in general: the whole physical package is a function of the annihilator
      ideal alone, so agreement of the classical normal-crossing ideal already forces agreement of
      the derived and half-density data
- [x] the resulting blindness no-go isolated and paired with the symbol-spectrum successor
- [x] Lean construction of the Barnes/multiple-sine object itself (not a theorem of this card):
      built on the Barnes annihilator card as `barnesConeProduct`, `barnesConeAnalytic`,
      `barnesConeMero`, `barnesSourceLogDerivMero`, with its ladder in the meromorphic field and its
      exact differential-translation annihilator
- [x] formalize the row-reduced physical Koszul differential and its square-zero law
- [x] formalize its exact cycle and boundary coefficient normal forms
- [x] formalize the surviving `choose(r,k)` basis multiplicity
- [x] formalize the row-reduced quotient homology equivalence with copies of `R/(a)`
- [x] formalize row-reduced homology vanishing above degree `r`
- [x] formalize the physical central-resonance theorem
- [x] formalize the coface-by-coface DA/source-translation symbol comparison
- [x] realize the comparison inside the genuine global meromorphic field
- [x] restrict the calibrated rank-three boundary carrier to physical exponential modes
- [x] prove uniform continuous source effectivity iff the period group is discrete
- [x] formalize the powered incidence and order-`r` half-density trichotomy
- [x] formalize the Koszul-chain transport induced by `unitScaledCofaceRowEquiv`
- [x] instantiate the physical exponential arc and prove its ideal is `(X^r)` in `C[[lambda]]`
- [x] derive the local length statement `(8)` over the physical formal local ring `C[[lambda]]`
- [x] zero physical tangency of the squarefree hierarchy `(14a)`--`(14c)` formalized
  unconditionally in Lean (`PhysicalArcContactVeronese.lean`)
- [x] filtration-preserving comparison morphism `lambda^k |-> w^k` constructed in Lean
  (`PhysicalPullbackPeriodIncidenceComparison.lean`)
- [x] ideal-level physical arc-contact Rees filtration constructed and compared source-naturally
  with the powered period-incidence filtration (`PhysicalPullbackPeriodIncidenceComparison.lean`)
- [x] extend the comparison to the critical completion and the analytic (non-polynomial) scale
  (`PhysicalArcCriticalCompletion.lean`: `discEvalVector_mem_poweredRange_iff`,
  `veroneseIdeal_criticalComparison`)
- [x] identify the critically completed bounded symbol with `w^r`
  (`veroneseIdeal_criticalComparison`: exact level, exact target `w^r`, closure-only half-density)
- [x] prove the Barnes/multiple-sine second realization: the Barnes source is a normal-crossing
      source of order `N` (`BarnesNormalCrossingRealization.lean`), so the physical package
      theorem transports to it verbatim
- [x] realize positive tangency in a natural HT special-function family
  (`PhysicalTangencyNaturalSource.lean`: `resonantSource_positiveTangency` on a resonant frame of a
  genuine multiple elliptic gamma)
- [x] ideal-level discriminator: an explicit positive-tangency operator exists, so least
  augmentation degree does not determine contact (`PhysicalArcContactVeronese.lean`)
- [x] construct a natural positive-tangency HT source or prove rigidity of zero tangency
  (first disjunct: `resonantSource_positiveTangency`, with
  `resonantSource_annihilator_strictly_larger`)
- [ ] obtain independent specialist novelty and significance audit
- 2026-08-02 -- The physical arc-contact order of the squarefree annihilator was computed in Lean:
  contact order equals the least augmentation degree, so the hierarchy has zero tangency excess.
- 2026-08-02 -- The `[NO-GO]` discriminator was formalized at the ideal level: an explicit operator
  with the same least augmentation degree has strictly larger physical contact order.
- 2026-08-02 -- The filtration-preserving comparison morphism was constructed in Lean: bounded
  evaluation at the period symbol sends `lambda^k` to `w^k` and carries the physical arc filtration
  of the squarefree annihilator into the powered period-incidence filtration.
- 2026-08-02 -- The ideal-level arc-contact Rees filtration was constructed in Lean, shown
  multiplicative and descending, located the squarefree annihilator exactly at level `r`, and
  compared source-naturally with the powered period-incidence filtration.

- 2026-08-03 -- The Barnes object is now Lean.  `barnes-multiple-gamma-translation-annihilator`
  constructs the cone product, its entire germ, the source in the global meromorphic differential
  field, the ladder in the field, and proves the exact differential-translation annihilator
  `P Psi_N is DA <-> prod_j (T_j - 1) | P` for rationally independent periods.  What the second
  realization gate still needs here is the scalar corollary -- the same statement for pure
  translation operators with complex coefficients -- and the identification of the resulting
  annihilator set with the squarefree Veronese ideal of order `N`, which for `r = N` is the
  principal ideal generated by the single squarefree monomial of degree `N`.  Both are algebra: the
  descent of divisibility from the `C[delta]`-coefficient ring to the `C`-coefficient one, and the
  variable change `X_j -> T_j - 1`.

- 2026-08-03 -- Second realization closed.  In the ladder variables `x_j = T_j - 1` the structural
  annihilator of the Barnes source is the principal ideal `(x_1 ... x_N)`, and for `N` variables the
  squarefree Veronese ideal of order `N` is exactly that principal ideal -- the only squarefree
  monomial of degree `N` is the full product.  So
  `isNormalCrossingSource_barnesSource : IsNormalCrossingSource (Barnes annihilator) N`, and
  `physicalPackage_of_isNormalCrossingSource` gives the Barnes source the same source height,
  arc-contact order, powered period-incidence level and polarizing half-density as the squarefree
  hierarchy.  Axiom-clean.  This is a genuinely independent second realization: the first was the
  multiplicative translate products, this one is the Barnes cone product built from Weierstrass
  factors, and the two agree because the physical package depends on the annihilator ideal alone.

- 2026-08-03 -- Gate audit against the Lean corpus rather than the card text.  Four gates in the
  lower list were stale duplicates of work already checked in the upper list and present in the
  tree: the critical-completion comparison and the identification of the completed bounded symbol
  with `w^r` are both `veroneseIdeal_criticalComparison`, and positive tangency in a natural HT
  family is `resonantSource_positiveTangency` on a resonant multiple-elliptic-gamma frame.  With the
  second realization closed above, the only gate left on this card is the external specialist audit.
