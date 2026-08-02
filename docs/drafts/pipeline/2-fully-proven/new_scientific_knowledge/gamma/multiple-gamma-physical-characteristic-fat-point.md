# The physical multiple-Gamma characteristic pullback is a central fat point of order `r`

- **ID:** `multiple-gamma-physical-characteristic-fat-point`
- **Stage:** 2-fully-proven / complete formal-power-series physical fat-point and Koszul cores
  Lean-formalized; convergent-germ instantiation and five-way special-function identity remain open
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
exponential instantiation.  The card remains in step 2 because Lean does not yet prove the same
factorization in the convergent-germ ring `C{lambda}` or the parent special-function identities
`d_DA(Psi_r)=ht_src(Psi_r)=r` entering the five-way law `(13)`.  Moving the whole card would
therefore overstate its formal status.

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

`[OPEN CORE]` Construct a source-natural comparison morphism between the fat-point filtration

```text
A superset (lambda) superset ... superset (lambda^r)       (18)
```

and the analytic small-period scale of `(15)`, prove that `lambda^k` realizes as the powered
multiplier `w^k`, and prove that the order-`r` central source class produces the half-density
`|w|^(r/2)` in `(16a)`.  Equality of the five integers in `(13)` is not enough; a real unified
theory must preserve the actual filtration, polarization, and source pointing.

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

### Fat-point completeness no-go

The local scheme `A/(lambda^r)` fixes multiplicity and derived coherence but not the rate at which
nonzero integral periods approach zero.

**Positive successor:** retain the pair consisting of the `lambda`-adic Rees filtration and the
complete controlled germ of the embedded period symbol.  The proposed comparison
`lambda^k |-> w^k` couples them without pretending that either reconstructs the other.

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
5. **Tangency/effectivity interaction.**  The exact conic source model with `tang_phys=1` is now
   formalized, as is its independence from the nondiscrete effectivity phase.  Construct the
   ideal-level physical arc-contact Rees filtration and compare it source-naturally with the
   powered period-incidence filtration.  Then realize positive tangency in a natural HT special
   function rather than only in the universal constraint source.
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
- [ ] construct the filtration-preserving analytic comparison morphism
- [ ] identify the critically completed bounded symbol with `w^r`
- [ ] prove the Barnes/multiple-sine second realization
- [ ] realize positive tangency in a natural HT special-function family
- [x] ideal-level discriminator: an explicit positive-tangency operator exists, so least
  augmentation degree does not determine contact (`PhysicalArcContactVeronese.lean`)
- [ ] construct a natural positive-tangency HT source or prove rigidity of zero tangency
- [ ] obtain independent specialist novelty and significance audit
- 2026-08-02 -- The physical arc-contact order of the squarefree annihilator was computed in Lean:
  contact order equals the least augmentation degree, so the hierarchy has zero tangency excess.
- 2026-08-02 -- The `[NO-GO]` discriminator was formalized at the ideal level: an explicit operator
  with the same least augmentation degree has strictly larger physical contact order.
