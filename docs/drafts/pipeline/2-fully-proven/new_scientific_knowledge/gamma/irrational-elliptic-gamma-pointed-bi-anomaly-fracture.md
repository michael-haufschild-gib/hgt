# The irrational elliptic gamma function carries a pointed DA--holomorphic bi-anomaly

- **ID:** `irrational-elliptic-gamma-pointed-bi-anomaly-fracture`
- **Stage:** 2-fully-proven
- **Type:** SPECIAL-FUNCTION RELATIVE COHOMOLOGY / FIRST NATURAL HT FRACTURE OBJECT
- **Scientific status:** `[PROVED ON PAPER FROM TWO INDEPENDENT PARENTS]`
  `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [SIGNIFICANCE PASS]`
  `[EXTERNAL NOVELTY PRELIMINARY] [NOT AN RH RESULT]`
- **Parents:**
  - `irrational-elliptic-gamma-hypertranscendence-matroid.md`
  - Felder--Henriques--Rossi--Zhu, *A gerbe for the elliptic gamma function*
  - `../../3-formalized/not_new_scientific_knowledge/birelative-fracture-square-and-three-channel-interaction.md`
- **Statement:** On a generic irrational triptic fibre, the same pointed elliptic-gamma cochain
  has a coboundary in the intersection of the holomorphic and differential-algebraic coefficient
  sectors.  Its relative class refines the nontrivial gamma gerbe, while its standard wedge
  component simultaneously carries the nontrivial differential-algebraic translation anomaly.

## Setup

Fix `tau,sigma` in the upper half-plane such that

```text
1,tau,sigma are Q-linearly independent,
H=Z+Z tau+Z sigma,
E=[C/H].                                                     (1)
```

Use the invariant wedge covering `U=(V_a)` of the oriented triptic source and the translation
group `H` on the fixed fibre.  Let

```text
C^bullet_M = Tot C_H^{p,q}(U,M^x)                           (2)
```

be the multiplicative group--Cech total cochain complex of nonzero meromorphic functions.

Define two degreewise coefficient subcomplexes.

```text
C^bullet_O = holomorphic nowhere-vanishing cochains,
C^bullet_B = cochains whose components are DA in the fibre variable over C(z),
C^bullet_A = C^bullet_O intersection C^bullet_B.            (3)
```

Using degreewise subcomplexes avoids a false sheaf claim: local DA identities need not glue to one
uniform differential polynomial on an arbitrary infinite cover.  The gamma cocycle uses a fixed
explicit cover and finitely supported cochains in each degree, for which `(3)` is sufficient.

## Parent input I: the gamma gerbe

Felder--Henriques--Rossi--Zhu construct a degree-one meromorphic cochain

```text
s_Gamma=(Gamma_{a,b},Delta_a) in C^1_M                    (4)
```

and prove

```text
D s_Gamma=phi in C^2_O.                                    (5)
```

Their proof is stronger than mere holomorphicity: every component of `phi` is the exponential of
a rational function in the homogeneous variables.  On the translation subgroup the three types
of components are explicitly

```text
exp(-2 pi i P_{a,b,c}/3!),
exp(-2 pi i P_{a,b}(mu)/2!),
exp(-2 pi i P_a(mu,nu)),                                   (6)
```

with `P` rational in the parameters and polynomial in the fibre variable.  Therefore every
component in `(6)` is differential-algebraic.  Equations `(5)`--`(6)` sharpen to

```text
D s_Gamma=phi in C^2_A.                                    (7)
```

The image of `[phi]` in holomorphic equivariant cohomology is the gamma-gerbe class.  On a generic
triptic fibre its Dixmier--Douady image generates

```text
H^3(E,Z)=Z.                                                 (8)
```

In particular the holomorphic class is nonzero.

## Parent input II: the DA translation anomaly

The standard wedge component of `(4)` is the ordinary additive elliptic gamma function

```text
Gamma(z;tau,sigma).
```

The irrational-period theorem proves:

```text
Gamma is hypertranscendental over C(z),
{h : Gamma(z+h)/Gamma(z) is DA}=H,                          (9)
```

and the translation cocycle

```text
a_h(z)=Gamma(z+h)/Gamma(z), h in H,                         (10)
```

is nontrivial in `H^1(H,B^x)` although it becomes the coboundary of `Gamma` in the ambient
meromorphic coefficient group.

## The pointed bi-anomaly theorem

> **[THEOREM -- POINTED DA--HOLOMORPHIC BI-ANOMALY.]** Under `(1)`, the elliptic-gamma cochain
> `(4)` canonically determines:
>
> 1. a relative total class
>
>    ```text
>    beta_Gamma=[s_Gamma mod A] in H^1(C_M/C_A);            (11)
>    ```
>
> 2. its nonzero connecting class
>
>    ```text
>    kappa_Gamma=partial_A beta_Gamma=[phi] in H^2(C_A);    (12)
>    ```
>
> 3. a pointed standard-wedge class
>
>    ```text
>    gamma_Gamma=[Gamma mod B] in H^0(H,M^x/B^x),           (13)
>    ```
>
>    whose connecting class is the nonzero DA anomaly `(10)`.
>
> The image of `(12)` under `A -> O` is the nontrivial gamma-gerbe class, while `(13)` is the
> DA edge of the same pointed degree-one cochain.  Both anomalies vanish after passage to the
> ambient meromorphic coefficient theory, where `s_Gamma` and its standard component are explicit
> primitives.

The word **pointed** is load-bearing.  The unpointed total cohomology class does not by itself
select the standard wedge component.  The source framing and wedge pointing in `(4)` supply that
selection before either anomaly is read.

## Proof

By `(7)`, the image of `s_Gamma` in the quotient complex `C_M/C_A` is a cocycle, proving `(11)`.
The connecting morphism of

```text
1 -> C_A -> C_M -> C_M/C_A -> 1                            (14)
```

sends it to the cohomology class of its coboundary, which is `[phi]`; this is `(12)`.

The inclusion `C_A -> C_O` maps `[phi]` to the gamma-gerbe class.  Its Dixmier--Douady image is the
generator `(8)`, so `[phi]` cannot vanish in `H^2(C_A)`.  Consequently `kappa_Gamma` and
`beta_Gamma` are both nonzero.

For the pointed edge, the standard wedge evaluation of `s_Gamma` is the ordinary elliptic gamma
function.  Equations `(9)`--`(10)` say exactly that its class modulo the DA coefficient group is
`H`-fixed and has nonzero connecting class in `H^1(H,B^x)`.  This proves `(13)` and its
nontriviality.

An `A`-valued gauge change of `(4)` preserves both outputs: it leaves `(11)` unchanged and
multiplies the standard wedge component by an element of `A <= B`, leaving `(13)` unchanged.
Thus the pair is an invariant of the pointed `A`-relative cochain, not of a chosen formula.

Finally, in `C_M` equation `(5)` exhibits the gerbe cocycle as a coboundary, while `Gamma` itself
trivializes `(10)`.  Hence both edge anomalies are effective in the same ambient meromorphic
theory. `QED`

## Pointed incidence phase `[PROVED]`

The new calibrated-fracture theorem turns ambient effectivity into an exact fibre calculation.
Let

```text
F=partial_z log Gamma(z;tau,sigma),
b=(Delta_sigma F,Delta_tau F)=(lambda_tau,lambda_sigma).  (14a)
```

Choose a source basepoint `z_*` away from the polar divisor of `F`.  Every ambient meromorphic
primitive of `b` differs from `F` by a function fixed by `tau` and `sigma`; after retaining the
existing period `1`, irrationality makes that joint-fixed function constant.  Evaluation at
`z_*` therefore identifies the ambient primitive torsor with `C`.

Let `B` be the additive DA-meromorphic sector and `M` the ambient meromorphic sector.  With the
pointing `F(z_*)`, the two incidence fibres are

```text
Inc_B(b,F(z_*)) = empty,
Inc_M(b,F(z_*)) = {F}.                                    (14b)
```

The first equality is the HT theorem: a DA primitive with boundary `b` would differ from `F` by a
constant and make `F` DA.  The second is ambient existence supplied by `F`, together with the
constant-kernel separation supplied by evaluation.

Thus the first natural HT fracture object exhibits both sides of the incidence-index principle:

```text
relative DA effectivity obstruction = nonzero cokernel class,
ambient boundary ambiguity          = constant kernel,
source pointing                      = exact removal of that kernel.          (14c)
```

This is not a new proof of elliptic-gamma hypertranscendence.  It is the exact positive realization
of the unified obstruction object: the same thin DA boundary has empty pointed incidence in the
thin coefficient theory and one canonical effective point in the ambient theory.  The generic
kernel--cokernel skeleton is Lean-formalized in
`../../3-formalized/not_new_scientific_knowledge/calibrated-fracture-incidence-kernel-cokernel.md`.

## What is genuinely learned

This theorem supplies the first natural analytic model of a multi-relative HT effectivity object.
After removing the fracture language, the mathematical content is:

```text
one source-pointed meromorphic cochain;
one coboundary lying in DA intersection holomorphic coefficients;
one nonzero degree-two holomorphic/DA refinement;
one nonzero degree-one DA translation anomaly;
one pointed incidence phase from empty in DA to a singleton in the ambient theory;
one ambient meromorphic primitive for both.                (15)
```

Thus the differential-algebraic and gerbe descriptions are not merely two analogies attached to
the same special function.  They arise from the same pointed cochain before quotienting, but in
different cohomological degrees and different coefficient directions.

This is the first exact instance of the architecture

```text
cube direction   = coefficient/realization category,
vertical height  = cohomological descent degree.           (16)
```

It also corrects a tempting but false simplification: the DA anomaly is not literally the
Dixmier--Douady class, and there is no natural identification of their target groups.  Their unity
is common origin and compatible effectivity, not equality.

## A new source-height pattern `[CONJECTURE]`

Euler gamma gives a degree-zero meromorphic primitive whose shift boundary is algebraic and whose
relative anomaly lies in degree one.  Elliptic gamma gives a degree-one group--Cech cochain whose
boundary lies in the thin intersection `(3)` and whose gerbe anomaly lies in degree two.

> **[CONJECTURE -- CONSTRAINT-HEIGHT/ANOMALY-HEIGHT LAW.]** For a source-minimal multiple-gamma or
> regular higher-rank constrained HT hierarchy, the minimal cohomological degree of its pointed
> relative source cochain equals the categorical height of the independent local constraint data;
> its first nonzero connecting anomaly occurs one degree higher.  Hypertranscendence is the
> nontriviality of the pointed relative class, while the finite source law is the thin coefficient
> boundary of its ambient primitive.

This conjecture is not the general statement that higher geometric gamma families or higher
cocycles exist.  Morain has already extended the geometric multiple-elliptic-gamma families to
higher-rank lattices and proved Bernoulli-rational coboundary relations.  The open prediction is
that source minimality and differential-algebraic capacity identify the *minimal nonzero relative
degree* and make its DA-filtered class nontrivial.

One half of the predicted height law is already proved by the exact multiple-elliptic-gamma
translation-annihilator theorem.  For order `r`, the minimum number of **distinct** structural
parameter directions needed to reach DA is exactly `r`; arbitrary repetition in fewer directions
remains HT.  What remains conjectural here is the identification of that transverse support height
with the minimal degree of a pointed DA-filtered relative cochain in the higher geometric family.

## Novelty gate

The parents are explicit and not claimed as discoveries:

1. Felder--Henriques--Rossi--Zhu construct the group--Cech cochain, gamma gerbe, meromorphic
   section, exponential-rational cocycle, and Dixmier--Douady generator.
2. The irrational-period theorem proves elliptic-gamma hypertranscendence, the exact shift
   spectrum, defect matroid, and DA translation anomaly.
3. Morain's 2025--2026 work constructs higher-rank geometric multiple-elliptic-gamma families,
   Bernoulli-rational modularity defects, and higher cocycles.
4. Relative cohomology and connecting morphisms are standard.

The candidate-new result is the intersection-coefficient refinement `(11)`--`(12)` together with
the pointed common-origin theorem linking it to `(13)`.  Targeted searches, including the new
higher-rank geometric-gamma papers, found geometric coboundaries and differential-algebraicity
results separately, but no DA-filtered gamma-gerbe class, no `DA intersection holomorphic`
refinement, and no theorem coupling the gerbe and translation anomalies through one pointed
cochain.

This remains a preliminary novelty conclusion.  It needs independent review by specialists in
difference algebra and gerbes.

## Anti-theatre gate

1. **Pairing-two-results attack.** Merely listing the gerbe theorem and HT theorem would be
   theatre.  The new object is the explicit nonzero class in `H^1(C_M/C_A)`, whose connecting class
   lies in `H^2(C_A)` and maps to the DD generator.
2. **Wrong-equality attack.** The DA and DD anomalies are not asserted equal.  They have different
   degrees and targets.  The theorem proves common pointed origin and simultaneous ambient
   effectivity.
3. **Sheaf attack.** No global sheaf of DA functions is silently assumed.  The construction uses
   a degreewise DA subcomplex on the explicit invariant cover.
4. **Gauge attack.** The standard wedge is retained as source pointing, and `A`-gauge invariance of
   both outputs is proved.
5. **Novelty attack.** The abstract connecting sequence is parent machinery.  The actual content is
   that the gamma cocycle lands in the intersection sector and has two independently nonzero
   pointed edge anomalies.

## Significance verdict

- **Standalone paper:** best published together with the irrational elliptic-gamma
  hypertranscendence/matroid theorem.  It materially strengthens that paper by giving the result a
  new geometric and cohomological meaning.
- **New-field significance:** high.  It is the first natural analytic object realizing two
  independent directions and two cohomological heights of the proposed HT fracture theory.
- **Fields verdict:** not by itself.  Fields-scale requires the general source-canonical
  reconstruction/effectivity equivalence and a new theorem transferred between two conservative
  realizations.
- **RH boundary:** no zeta source object, zero theorem, positivity statement, or RH implication is
  used or obtained.

## Lean boundary

Lean formalizes the unconditional algebraic skeleton:

- two quotient channels glue exactly through the intersection/sum fracture sequence;
- compatible observations have a common representative exactly when the defect vanishes;
- three abelian channels can have a nonzero higher interaction quotient.

### The pointed incidence phase `(14a)`--`(14b)` is unconditional Lean

`EllipticGammaPointedIncidencePhase.lean` formalizes the fibre calculation, with no axiom and no
gerbe machinery:

- `ellipticGammaBoundarySolutions` is the structural boundary problem: the unit period together
  with the two structural difference equations of the source `F`;
- `exists_constant_of_mem_boundarySolutions` and `boundarySolutions_eq_constantCoset` -- **every
  solution differs from `F` by a constant, so the solution set is exactly `F + C`**, by the
  rank-three generator joint-fixed collapse;
- `not_differentialAlgebraicOver_of_mem_boundarySolutions` -- **the differentially algebraic
  incidence fibre is empty**, since a DA solution would make `F` differentially algebraic against
  the exact period-rank dichotomy;
- `boundarySolutions_constantTorsor` -- **the ambient fibre is a constant torsor**: adding a
  constant is a bijection from `C` onto the solution set, so any pointing singles out `F`.

This is `(14b)` for the genuine meromorphic source.  `#print axioms` clean.

### Parent input II, the DA translation anomaly `(9)`--`(10)`, is unconditional Lean

`EllipticGammaTranslationAnomalyRationalBase.lean` proves it over the natural coefficient field:

- `differentialAlgebraicOver_compositum_of_ratFunc` -- differential algebraicity over `C(z)`
  implies it over the paired elliptic compositum, since the compositum contains the constants;
- `differentialAlgebraicOver_ratFunc_ellipticGammaExternalQuotientMero_iff_resonant` and its
  hypertranscendence form -- **the exact DA spectrum `(9)`: a shift quotient
  `Gamma(z+h)/Gamma(z)` is DA over `C(z)` exactly for `h` in the rank-three integer period
  group**;
- `hypertranscendentalOver_ratFunc_ellipticGammaMero` -- **`Gamma` is hypertranscendental over
  `C(z)`**;
- `ellipticGamma_translationAnomaly` -- **`(13)` without gerbe language**: the class of `Gamma`
  modulo the differentially algebraic sector is fixed by the whole period group, every off-spectrum
  quotient is hypertranscendental, and `Gamma` itself is not differentially algebraic, so the
  connecting cocycle of that class is nontrivial.

`#print axioms` clean.

`EllipticGammaTranslationCocycleAnomaly.lean` upgrades this from an elementwise statement to the
cocycle statement `(10)` asserts:

- `ellipticGammaExternalQuotientMero_eq_coboundary` -- the shift cocycle is the ambient coboundary
  of `Gamma`;
- `addTranslationMeroEquiv_div_eq_of_coboundary` -- a trivializer makes the ratio of `Gamma` by it
  translation-fixed;
- `ellipticGammaShiftCocycle_not_differentialAlgebraic_coboundary` -- **there is no differentially
  algebraic trivializer**: the ratio would be fixed by all three source generators, hence constant
  by the rank-three generator collapse, hence would make `Gamma` differentially algebraic;
- `ellipticGamma_translationCocycle_anomaly` -- **the exact anomaly phase**: differentially
  algebraic values on the whole period group, ambient coboundary of `Gamma`, and no differentially
  algebraic trivializer.

That is `(10)`'s assertion that the cocycle is nontrivial in the differentially algebraic
coefficient group while becoming a coboundary in the ambient one.

What is still unformalized is the gerbe half `(11)`--`(12)`: the group--Cech gamma-gerbe cochain
`(4)`, its coboundary lying in the intersection sector `(7)`, and the Dixmier--Douady generator
`(8)`.  No analytic claim is inserted as an axiom.

## Gates

- [x] fixed irrational triptic fibre selected
- [x] FHRZ group--Cech cochain and boundary identified
- [x] exponential-rational boundary shown to lie in DA and holomorphic sectors
- [x] intersection-coefficient relative class constructed
- [x] connecting class proved nonzero via the DD generator
- [x] standard wedge pointing identified with actual elliptic gamma
- [x] DA edge proved nonzero by the exact translation anomaly theorem
- [x] common ambient meromorphic effectivity proved
- [x] pointed DA incidence proved empty and ambient incidence proved singleton
- [x] relative obstruction and residual ambiguity identified as cokernel and kernel phases
- [x] gauge invariance under the intersection sector proved
- [x] parent and anti-theatre boundaries explicit
- [ ] independent specialist proof and novelty audit
- [x] group--Cech and DA coefficient complexes formalized in Lean
- [x] pointed incidence phase `(14a)`--`(14b)` formalized without axioms
  (`EllipticGammaPointedIncidencePhase.lean`)
- [x] DA translation anomaly `(9)`--`(10)` and the pointed class `(13)` formalized without axioms
  (`EllipticGammaTranslationAnomalyRationalBase.lean`)
- [x] Dixmier--Douady generator `(8)` formalized without axioms
  (`GammaGerbeDixmierDouadyGenerator.lean`: `gammaGerbeDD_not_coboundary`,
  `coboundary₂_lift_eq_coboundary₂_kernel`)
- [ ] gerbe half `(11)`--`(12)`: the single remaining input is the FHRZ cochain identity
  `(1/2 pi i) coboundary₂ (log Phi) = gammaGerbeDD`

## Lean route for the pointed incidence phase (14b)

The abstract gerbe/Cech layer is not the cheapest entry point.  The *pointed incidence phase* is,
and the corpus already owns every input:

- **`exists_nonconstant_fixed_iff_discretePeriodSource`**
  (`HTGeometry/DiscretePeriodGaugeClassification`) -- a global meromorphic element fixed by an
  integral period source is constant exactly when that source is non-discrete.  Contrapositive: for
  a non-discrete source, *every* fixed element is a constant.  This is the "joint-fixed function is
  constant" step of `(14b)`, already unconditional.
- **`not_discrete_intSpan_fin_three`**, **`irrationalPeriodGroup_not_discrete`**
  (`HTGeometry/GalePeriodClosureFracture`) -- three rationally independent periods span a
  non-discrete group.  With `1, tau, sigma` this is exactly the irrationality hypothesis `(1)`.
- **`multipleEllipticGamma_exactPeriodRankDichotomy`** and the rank-three minor interface -- the HT
  half of `Inc_B = empty`.
- `addTranslationMeroEquiv` and the meromorphic differential field -- the ambient sector `M`.

So the remaining Lean work is the assembly:

1. a bridge lemma `constant_of_fixed_of_not_discrete` (one contrapositive of the classification);
2. the two-shift boundary of the elliptic-gamma logarithmic derivative, as an element of the
   meromorphic field;
3. `Inc_M(b, F(z_*)) = {F}` -- uniqueness from 1 plus the pointing;
4. `Inc_B(b, F(z_*)) = empty` -- a DA primitive would equal `F` by 3, contradicting HT.

## Log addendum

- 2026-08-02 -- located the corpus assets for the pointed incidence phase; the joint-fixed
  constancy and the non-discreteness of a rationally independent period triple are already
  unconditional Lean, so `(14b)` is an assembly rather than a construction.

## Lean status of the pointed incidence phase

Step 1 of the route is done, unconditionally, in `HTGeometry/PointedIncidenceConstancy.lean`:

> **`exists_const_of_fixed_of_not_discrete`** -- a global meromorphic element fixed by a
> non-discrete integral period source is a constant, by contraposing the exact gauge
> classification;
> **`fixed_span_of_fixed_generators`** -- fixing the three generators is enough: the fixed periods
> form an integral submodule, so the whole span fixes the element;
> **`exists_const_of_fixed_rankThree`** -- **for a rationally independent triple `1, sigma, tau`,
> every jointly fixed meromorphic element is constant.**  Irrationality enters exactly once, as
> non-discreteness of the span;
> **`eq_of_fixed_rankThree_of_sub_const`** -- the pointed form: two elements whose difference is
> jointly fixed and whose separating evaluation agrees are equal.  This is the "source pointing
> removes the constant kernel" clause of `(14c)`.

`#print axioms` clean.  What remains for `(14b)` is the analytic identification: the two-shift
boundary of the elliptic-gamma logarithmic derivative, and the reading of `Inc_B = empty` off the
hypertranscendence theorem.

- 2026-08-02 -- the constancy and pointing steps of `(14b)` are unconditional Lean.

## Lean status of `(14b)`

`HTGeometry/PointedShiftIncidence.lean` proves the incidence phase in the ambient meromorphic
differential field, for an arbitrary hypertranscendental primitive:

> **`meroConstant`**, **`ConstantPointing`** -- the embedded constants and a constant-separating
> evaluation, i.e. the source pointing of `(14c)`;
> **`shiftIncidence`** -- the pointed primitives of a two-shift boundary inside a sector: the same
> two shift differences, fixity under the retained unit period, and the prescribed pointing;
> **`daSector`** -- the differentially algebraic sector `B`;
> **`shiftIncidence_subsingleton`** -- **two pointed primitives coincide**: their difference is
> fixed by all three periods, hence constant by `exists_const_of_fixed_rankThree`, and the pointing
> kills that constant;
> **`shiftIncidence_ambient_eq_singleton`** -- **`Inc_M(b, F(z_*)) = {F}`**;
> **`shiftIncidence_da_eq_empty`** -- **`Inc_B(b, F(z_*)) = empty`** for a hypertranscendental `F`:
> a differentially algebraic pointed primitive would coincide with `F`;
> **`nonempty_constantPointing`** -- the pointing exists, so neither statement is vacuous: the
> constants are a rational subspace of the ambient field and any rational left inverse of that
> embedding separates them.

`#print axioms` clean.  Both fibres of `(14b)` are therefore unconditional Lean, for any
hypertranscendental primitive of a rationally independent two-shift boundary.

`HTGeometry/EllipticGammaPointedIncidence.lean` instantiates them at the card's own
`F = d/dz log Gamma(z; tau, sigma)`:

> **`ellipticPeriodPair`**, **`ellipticLogDerivMero`** -- the two-period family and the logarithmic
> derivative as an element of the meromorphic differential field;
> **`unitPeriod_defect_ellipticLogDerivMero`** -- the retained unit period, from the corpus's
> `addTranslationMeroEquiv_one_multipleEllipticGammaLogDerivMero`;
> **`rankThreeMinor_ellipticPeriodPair`**, **`hypertranscendental_ellipticLogDerivMero`** -- the
> irrationality hypothesis `(1)` is exactly a rank-three minor, so the dichotomy gives
> hypertranscendence;
> **`ellipticLogDeriv_ambient_incidence`** -- **`Inc_M(b, F(z_*)) = {F}`**;
> **`ellipticLogDeriv_da_incidence`** -- **`Inc_B(b, F(z_*)) = empty`**;
> **`ellipticLogDeriv_pointed_incidence_phase`** -- **the pointed incidence phase `(14b)` for the
> elliptic gamma, unconditionally.**

`#print axioms` clean.  The card's `[PROVED]` incidence phase is now fully Lean; the remaining Lean
gate concerns the group--Cech gerbe layer `(11)`--`(13)`, not this phase.

- 2026-08-02 -- `(14b)` proved in the abstract: singleton ambient fibre, empty DA fibre, inhabited
  pointing.
- 2026-08-02 -- (14b) instantiated at the elliptic gamma logarithmic derivative: empty pointed DA
  fibre, singleton pointed ambient fibre, both unconditional.

## Lean status of the DA edge `(13)`

The nontriviality asserted by `(13)` -- that the translation cocycle `(10)` is not a coboundary in
the differentially algebraic coefficient group -- is unconditional Lean in
`HTGeometry/TranslationCocycleAnomaly.lean`:

> **`cocycle_not_coboundary_of_notMem`** -- **the general mechanism**: if the cocycle
> `q ↦ sigma_q(G)/G` were the coboundary of a sector element `b` over a non-discrete period group,
> then `G/b` would be fixed by that group, hence constant, and `G` would lie in the sector.  So an
> element outside a constant-stable sector has a genuinely anomalous cocycle;
> **`daSector_const_mul`** -- the differentially algebraic sector is constant-stable, since the
> constants are in the image of the coordinate field and differential algebraicity is closed under
> products;
> **`ellipticGamma_cocycle_not_daCoboundary`** -- **the elliptic gamma instance**: for rationally
> independent periods no differentially algebraic element presents its translation cocycle as a
> coboundary over the rank-three period group.  Since a coboundary over the larger group `H` of
> `(9)` restricts to one over that lattice, this is exactly the nonvanishing claimed by `(13)`.

`#print axioms` clean.  Note the shared mechanism: the same "fixed by a non-discrete group implies
constant" step drives the empty differentially algebraic incidence fibre `(14b)` and the nonzero
differentially algebraic edge `(13)`.  The additive and multiplicative anomalies of the card are one
statement about constants.

- 2026-08-02 -- the DA edge `(13)` nontriviality is unconditional Lean, via the same constancy
  mechanism as `(14b)`.

## Lean status of the cochain layer

`HTGeometry/TwoShiftKoszulCochain.lean` builds the degree-one/two cochain layer of the two-shift
group in the ambient meromorphic field.  For a free rank-two translation group the multiplicative
cochain complex is the Koszul complex, so no general group-cohomology machinery is needed:

> **`shiftQuotient`** -- one component of the canonical degree-one cochain of an element;
> **`koszulCoboundary`** -- the degree-two coboundary of a degree-one cochain, the mixed quotient of
> its two entries;
> **`koszulCoboundary_shiftQuotient`** -- **the canonical cochain is a cocycle**, because the two
> translations commute.  This is the algebraic content of `(11)`: the class is a cocycle *before*
> any coefficient quotient is taken;
> **`koszulCoboundary_shiftQuotient_mem_of_one_mem`** -- hence its image in every coefficient
> quotient is a cocycle too;
> **`ellipticGamma_koszul_cocycle_not_daCoboundary`** -- **the elliptic gamma cochain is a cocycle
> whose class is not a differentially algebraic coboundary**: the pointed degree-one anomaly in
> cochain form.

`#print axioms` clean.

What is still outside Lean on this card is the degree-two *nonvanishing* `(12)`: that the connecting
class is nonzero in `H^2(C_A)`.

**Correction (2026-08-02).**  An earlier note here proposed a route to `(12)` avoiding the
Dixmier--Douady generator: assume the cocycle is a differentially algebraic coboundary, subtract it,
use ambient effectivity, and conclude that the elliptic gamma is differentially algebraic.  That
route does not close.  Undoing the coboundary only shows that the shift quotients of a corrected
element are differentially algebraic, and *that does not imply the element is* -- the elliptic gamma
is itself the counterexample, since its shift quotients are theta functions, which are differential
algebraic, while the gamma function is hypertranscendental.  This is exactly the content of `(9)`.

Two structural facts explain why the degree-one work does not extend:

- in the pure translation direction the coboundary of the gamma cochain is *trivial*
  (`koszulCoboundary_shiftQuotient`), because the two translations commute.  The anomaly `phi` of
  `(5)` therefore lives in the mixed Cech-times-group bidegree of the total complex `(2)`, not in
  the group direction alone;
- the differentially algebraic sector separates the two anomalies: the degree-one edge is nonzero
  because a coboundary presentation would put the gamma function itself into the sector, whereas
  the degree-two class is nonzero for a topological reason, the Dixmier--Douady generator `(8)`.

So `(12)` is gated behind the two external parent inputs, FHRZ's cochain `(4)`--`(5)` and the
Dixmier--Douady computation `(8)`.  Formalizing it means formalizing those, which is a distinct
project from everything above: the wedge cover, the total complex, the FHRZ cochain, and the
degree-three integral cohomology of the triptic fibre.  Nothing here is inserted as an axiom.

- 2026-08-02 -- the two-shift Koszul cochain layer is unconditional Lean; `(11)` holds in it, and
  the degree-one anomaly is stated in cochain form.
- 2026-08-02 -- corrected a wrong route note: the degree-two nonvanishing cannot be reduced to the
  degree-one mechanism, because differentially algebraic shift quotients do not force the element to
  be differentially algebraic -- the elliptic gamma is the counterexample.

## Next Lean step: translation stability of the DA sector

The remaining tractable item of the "DA coefficient complexes" gate is that the differentially
algebraic sector is stable under the translations, which is what makes `(3)` a *subcomplex* rather
than a graded subgroup.  All ingredients are in the corpus:

- **`addTranslationMeroEquiv_deriv`** -- translation commutes with the derivation, so it takes
  differential jets to differential jets;
- **`addTranslationMeroEquiv_ratfuncToMero`** -- translation carries the coordinate base into
  itself, so it covers an automorphism of the base field rather than fixing it;
- `differentialAlgebraicOver_mul`, `_inv`, `_add`, `_neg`, `_algebraMap` -- the sector is already
  known to be a field containing the base.

The transport is then the standard one: a nonzero relation `P` over the base satisfied by the jets
of `x` maps, under the base automorphism, to a nonzero relation satisfied by the jets of the
translate.  With that lemma the degreewise sector `C_A` of `(3)` is closed under the group
differential, and the multiplicative Koszul layer already built becomes a genuine complex of
sectors rather than of sets.

## Lean status of the DA subcomplex property

`HTGeometry/TranslationStableDifferentialAlgebraicity.lean` closes the next step:

> **`shiftCompHomBy`**, **`ratShiftBy`**, **`ratShiftEquivBy`** -- the translation automorphism
> `r(X) ↦ r(X + q)` of the coordinate field, for an arbitrary complex shift (the corpus previously
> had only the unit shift);
> **`addTranslationMeroEquiv_ratfuncToMero_by`** -- translation of the meromorphic field restricts
> to it, so a translation covers an automorphism of the base rather than fixing it;
> **`differentialJet_addTranslationMeroEquiv`** -- jets commute with translation;
> **`differentialAlgebraicOver_of_transport`** -- **the transport principle**: differential
> algebraicity passes along any derivation-compatible automorphism covering an automorphism of the
> base, by mapping the relation's coefficients;
> **`differentialAlgebraicOver_addTranslationMeroEquiv`**, **`daSector_addTranslationMeroEquiv`**,
> **`daSector_shiftQuotient`** -- **the differentially algebraic sector is translation stable, and
> stable under the entrywise group differential.**

`#print axioms` clean.  With this the degreewise sector `C_A` of `(3)` is closed under the group
direction of the differential, which is what makes it a subcomplex there rather than a graded
subgroup; the Cech direction of `(2)` is untouched by this module.

- 2026-08-02 -- translation stability of the DA sector proved, with the general coordinate shift
  automorphism built along the way.

## Lean status of the three coefficient sectors `(3)`

`HTGeometry/AnomalyCoefficientSectors.lean` builds all three sectors of `(3)` inside the ambient
meromorphic field, in the group direction:

> **`oSector`** -- the holomorphic nowhere-vanishing sector, defined as the image of the *units* of
> the entire germ ring, which is exactly "holomorphic and nowhere vanishing";
> **`oSector_one`**, **`oSector_mul`**, **`oSector_inv`**, **`oSector_ne_zero`** -- it is a
> multiplicative group of nonzero elements;
> **`oSector_addTranslationMeroEquiv`** -- **it is translation stable**, because translation acts on
> the entire germ ring by a ring isomorphism and therefore carries units to units;
> **`oSector_shiftQuotient`** -- hence stable under the entrywise group differential;
> **`aSector`** -- the intersection sector `C_A = C_O ∩ C_B`, with **`aSector_mul`**,
> **`aSector_inv`**, **`aSector_addTranslationMeroEquiv`**, **`aSector_shiftQuotient`**;
> **`aSector_koszulCoboundary`** -- **the Koszul coboundary of a degree-one cochain with entries in
> the intersection sector stays in that sector**: `C_A` is a subcomplex for the group differential,
> which is the content of `(3)` in that direction.

`#print axioms` clean.  Together with the previous module the whole coefficient layer of `(3)` is
unconditional Lean in the group direction; only the Cech direction of the total complex `(2)` is
still unformalized, and it is the direction where the FHRZ cochain and the Dixmier--Douady class of
`(12)` live.

- 2026-08-02 -- the three coefficient sectors and their stability under the group differential are
  unconditional Lean.

## Lean status of the Cech direction

`HTGeometry/CechLowDegreeComplex.lean` builds the multiplicative Cech complex in the three degrees
the gerbe cochain uses, for an arbitrary index type and an arbitrary commutative coefficient group:

> **`cechD0`**, **`cechD1`**, **`cechD2`** -- the differentials from patches to overlaps, from
> overlaps to triple overlaps, and from triple to quadruple overlaps;
> **`cechD1_cechD0`**, **`cechD2_cechD1`** -- **it is a complex**: both composites are constantly
> one, the second by an explicit six-fold cancellation (`sixfold_cancel`);
> **`Sector`** -- an abstract coefficient sector: a subset closed under unit, product and inverse,
> with **`Sector.div_mem`**;
> **`cechD0_mem`**, **`cechD1_mem`**, **`cechD2_mem`** -- **a sector is a subcomplex in all three
> degrees**;
> **`cechD2_cechD1_mem_of_mem`** -- a degree-one cochain whose differential lands in a sector has a
> sector-valued cocycle as differential.

`#print axioms` clean.

- 2026-08-02 -- the Cech direction of the total complex `(2)` is unconditional Lean.

## Lean status of the group--Cech bicomplex `(2)`

`HTGeometry/GroupCechBicomplex.lean` welds the two directions.  With one translation the group
direction has two rows, so the total complex in low degrees is the mapping cone of the coefficient
map, and the module carries both the abstract and the meromorphic instance:

> **`cechD0_comp`**, **`cechD1_comp`** -- the Cech differential is natural in the coefficient group,
> which is the commutation of the mixed square;
> **`cechD1_div`** -- it is a homomorphism in the cochain;
> **`totalD1`**, **`totalD2`**, **`totalD3`** -- the total differentials, with the alternating sign
> in the mixed entry;
> **`totalD2_totalD1`**, **`totalD3_totalD2`** -- **the total differential squares to one** in both
> available total degrees;
> **`totalD1_mem`**, **`totalD2_mem`** -- **the total complex restricts to a pair of coefficient
> sectors**;
> **`MeroUnits`**, **`translationUnitHom`**, **`shiftUnitHom`**, **`shiftUnitHom_val`** -- the
> concrete instance: translation and the shift quotient acting on the units of the ambient
> meromorphic field, with the unit-level differential identified with `shiftQuotient`;
> **`one_mem_aSector`**, **`aSectorUnits`**, **`shiftUnitHom_mem_aSectorUnits`** -- the intersection
> sector as a coefficient sector of that group, stable under the group differential;
> **`totalD_aSector`** -- **the bicomplex of the ambient field with coefficients in the anomaly
> sector**: the total differential squares to one and every entry produced from a sector cochain
> stays in the sector, in both directions;
> **`shiftUnitHom_comm`** -- the two group differentials of a pair of commuting translations
> commute, so a two-shift anomaly is a class in the total complex.

`#print axioms` clean.  Together with the Koszul module and the three coefficient sectors, the
group--Cech and DA coefficient complexes of `(2)`--`(3)` are now unconditional Lean in both
directions.  What stays outside Lean is only the degree-two *nonvanishing* `(12)`, which needs the
FHRZ cochain and the Dixmier--Douady generator as external parent mathematics.

- 2026-08-02 -- the group--Cech bicomplex with DA coefficients is unconditional Lean.

## Exact remaining Lean input for `(12)`

Everything on this card that can be proved from objects living inside this corpus is now
unconditional Lean: `(11)` in cochain form, `(13)` with its nontriviality, `(14b)` in both fibres,
the three coefficient sectors `(3)`, and the group--Cech bicomplex `(2)` with those coefficients.

The single remaining analytic item is the *degree-two nonvanishing* `(12)`, and its obstruction is
sharp rather than a matter of effort.  In the pure group direction the anomaly is provably trivial:
`koszulCoboundary_shiftQuotient` shows the canonical two-shift cochain of the elliptic gamma is a
Koszul cocycle with trivial coboundary, and undoing that coboundary yields only that the shift
quotients are differentially algebraic -- which they are, being theta functions.  So no argument in
the group direction can detect `(12)`; the class lives in the mixed Cech-group bidegree and is
detected only by the gerbe.

Closing `(12)` therefore requires importing, not deriving, the Felder--Henriques--Rossi--Zhu
group--Cech cochain on the explicit invariant cover together with its Dixmier--Douady computation.
No substitute detector exists in the group direction, by the triviality just cited.

### The Dixmier--Douady half is now unconditional Lean

Reading FHRZ closes most of that gap.  Their Proposition 6.10 does **not** need the theory of
triptic curves as such: for a generic triptic curve `E = [C/Lambda]` the fibre is contractible, so
`H^*_{Lambda}(F, Z) = H^*(Z^3, Z)`, and the cocycle representing `c(G)` is the explicit **integral
group `3`-cocycle on `Z^3`**

```text
nu(alpha, beta, gamma) = - beta_1 gamma_2 alpha_3 .
```

`formal/GaloisForLFunctions/HTGeometry/GammaGerbeDixmierDouadyGenerator.lean` (axiom-clean, umbrella
registered) proves, with no analytic input at all:

```text
coboundary₁, coboundary₂, coboundary₃                    -- the inhomogeneous complex, any coefficients
coboundary₂_coboundary₁, coboundary₃_coboundary₂         -- it is a complex
gammaGerbeDD                                             -- the cocycle nu
coboundary₃_gammaGerbeDD                                 -- nu is a 3-cocycle
alternation                                              -- pairing with the top exterior power
alternation_coboundary₂                                  -- the alternation kills every coboundary
alternation_gammaGerbeDD                                 -- and sends nu to -1
gammaGerbeDD_not_coboundary                              -- so nu is not a coboundary
zsmul_gammaGerbeDD_not_coboundary                        -- and neither is any nonzero multiple
coboundary₂_lift_eq_coboundary₂_kernel                   -- the exponential detector
```

The last one is the bridge `(F2)`: for a surjective coefficient homomorphism `E` --- the exponential
`O -> O^x` on a cover with simply connected patches, with kernel the integers --- a cocycle that is
a coboundary in the target has an integral class which is a coboundary in the kernel-valued complex.
Contrapositive: a lift whose coboundary is not a coboundary certifies that the original cocycle is
not a coboundary.  Combined with `gammaGerbeDD_not_coboundary` this is exactly the statement `(8)`
that the card previously had to import.

### Exact remaining Lean input for `(12)`

The detector is stated so that only the *cohomology class* of the integral cocycle matters, never a
particular polynomial representative:

```text
not_coboundary_of_alternation_ne_zero
alternation_add_coboundary₂
not_coboundary_of_cohomologous_gammaGerbeDD
```

so the single remaining input is the Felder--Henriques--Rossi--Zhu identification

```text
[ (1/2 pi i) * coboundary₂ (log Phi) ]  =  [ gammaGerbeDD ]   in  H^3(Z^3, Z)     (F3)
```

for the FHRZ cochain `s_Gamma` --- their Proposition 3.15 together with the evaluation in the proof
of their Proposition 6.10.  That is the elliptic-gamma modular three-term identity in cochain form,
and it is the only place where the analytic theory of `Gamma(z; tau, sigma)` still has to enter.
Everything downstream of it --- that such a class is not a coboundary, and that a holomorphic
nowhere-vanishing trivialisation would make it one --- is unconditional Lean.

One bookkeeping caveat: FHRZ's coefficients are `Cech^0(V_a, Z)`, which for a connected patch is
`Z`, so the constant-coefficient complex formalized above is the right target.

The gate stays open on `(F3)` and no analytic claim is inserted as an axiom.

- 2026-08-02 -- Lean work on this card is complete up to the two external parent objects above.

## Log

- 2026-08-02 -- The pointed incidence phase became unconditional Lean: the structural boundary
  solution set is the constant coset of the source, its differentially algebraic fibre is empty,
  and its ambient fibre is a constant torsor.
- 2026-08-02 -- Parent input II became unconditional Lean over `C(z)`: the exact DA spectrum of the
  shift quotients, hypertranscendence of the gamma function, and the resulting nontrivial
  translation class.
- 2026-08-02 -- The translation anomaly was upgraded to the cocycle statement: the elliptic-gamma
  shift cocycle admits no differentially algebraic trivializer, while being the ambient coboundary
  of the gamma function.
