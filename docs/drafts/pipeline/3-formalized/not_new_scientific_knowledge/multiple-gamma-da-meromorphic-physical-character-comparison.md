# Multiple-Gamma DA and meromorphic physical-character comparison

- **ID:** `multiple-gamma-da-meromorphic-physical-character-comparison`
- **Stage:** 3-formalized
- **Type:** THEOREM / TWO-REALIZATION COMPARISON / LOCAL-TO-GLOBAL NO-GO
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [BRIDGE]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH RESULT]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/MeromorphicPhysicalCharacteristicIncidence.lean`
  `formal/GaloisForLFunctions/HTGeometry/PeriodIncidenceUniformEffectivity.lean`
- **Parents:**
  - `../new_scientific_knowledge/multiple-gamma-physical-characteristic-fat-point.md`
  - `../../1-in-progress/hypertranscendental-source-fracture-hypercube.md`
  - `../../1-in-progress/constraint-curvature-integration-stack.md`

## Exact theorem

Let `tau:Fin(r+1)->C`.  Inside the genuine global meromorphic fraction field, define

```text
E_lambda(z)=exp(lambda z).
```

For every source direction,

```text
(T_(tau_j)-1)E_lambda
  =(exp(lambda tau_j)-1)E_lambda.                           (1)
```

Iterating over the coface complementary to `i` gives

```text
product_(j!=i)(T_(tau_j)-1) E_lambda
  =product_(j!=i)(exp(lambda tau_j)-1) E_lambda.            (2)
```

The scalar on the right of `(2)` is exactly the `i`th coface equation of the DA logarithmic
characteristic arrangement pulled onto the physical clock

```text
lambda |-> (lambda tau_0,...,lambda tau_r).
```

Therefore

```text
DA physical characteristic boundary at lambda
  <-> every genuine meromorphic source coface kills E_lambda.        (3)
```

If `r>=1` and the periods are rationally independent, both sides of `(3)` hold exactly at
`lambda=0`.

For `r=2`, `(1)` also proves that the existing rank-three meromorphic boundary fingerprint
restricts to the same physical source symbol on every exponential mode.  Thus the comparison is
inside the carrier used by the calibrated meromorphic reconstruction theorem; it is not merely a
pointwise analogy between external functions.

## Proof

The entire function `E_lambda` defines an element of the global analytic subring and hence of its
meromorphic fraction field.  Translation in that field is induced by precomposition
`z |-> z+tau_j`, so the exponential addition law proves `(1)`.  Induction over a source-labelled
coface proves `(2)`.  Since `E_lambda` is nonzero in the fraction field, a coface kills it exactly
when its scalar symbol vanishes, giving `(3)`.  Rational independence excludes simultaneous
nonzero exponential resonance in two distinct source directions.  `QED`

## Exact local-to-global no-go and positive successor

The comparison `(3)` is exact at every physical character.  It does **not** imply uniform source
effectivity over the integral period family.  For a rationally independent rank-three period
group, the separately formalized period-incidence multiplier has injective nonclosed range even
though every nonzero finite diagonal restriction is invertible.

The exact uniform phase law is now Lean-formalized:

```text
the period-incidence representation has a continuous left inverse
  <-> the embedded integral period group is discrete.       (3a)
```

Thus the rationally independent rank-three source has no continuous global left inverse.  The
obstruction is uniform effectivity, not algebraic invertibility of the individual characters.

The no-go has an exact positive successor.  The same nondiscrete period geometry forces every
global meromorphic source-fixed gauge to be constant.  More generally, Lean proves that failure of
a continuous period-incidence left inverse implies maximal meromorphic gauge rigidity, while a
nonconstant fixed gauge implies uniform left invertibility.  Hence global nonattainment and
nonconstant boundary gauge are complementary period-closure phases; see
`period-gauge-attainment-complementarity.md`.

```text
[NO-GO]
Fibrewise exact DA--meromorphic comparison implies a bounded or closed-range global source lift.
```

**Positive successor.**  One remaining interaction is a comparison between physical-character
base change and the source-forced critical completion.  Let `C_F` be the source constraint complex,
`chi_F` its physical character germ, and `Comp_F` the completion forced by the embedded integral
period group.  The next invariant is the base-change/completion comparison defect

```text
BCDef_F = cofib(
  L chi_F^*(Comp_F C_F)
    -> Comp_F(L chi_F^* C_F)).                              (4)
```

Formula `(4)` is `[CONJECTURE]` until the completion functor and comparison morphism are constructed
source-naturally.  In the multiple-Gamma rank-three chart, the nonclosed incidence range predicts
that `(4)` is nontrivial at the critical bornology even though every finite character fibre in
`(3)` is exact.

This locates, rather than solves, the critical all-scale obstruction.  Within the fracture-incidence
theory it is the interaction face between the DA/meromorphic comparison and critical bornological
effectivity, not a competing unified object.

A second, independent interaction has now been isolated.  The same nondiscrete rank-three source
supports quadratic constraints with physical contact orders two and three.  Thus the global
effectivity phase does not determine the local osculation filtration.  The unified object must
retain both and construct their source-natural comparison; see
`../new_scientific_knowledge/quadratic-physical-osculation-effectivity-fracture.md`.

## Novelty and anti-theatre gate

The theorem itself is a bridge.  Exponential diagonalization of translations, analytic germs,
fraction fields, and characteristic symbols are parent mathematics.  Lean formalization does not
make `(1)`--`(3)` new science.

The potentially new question is whether the source-natural defect `(4)` exists, is presentation
invariant, and controls the analytic nonattainment phases across genuinely different HT
realizations.  Derived completion/base-change defects are established parent phenomena, so novelty
can begin only with an HT essential-image theorem and a transferred analytic consequence.

Primary adjacent checks include Porta--Shaul--Yekutieli on derived adic completion and MGM
equivalence (`https://arxiv.org/abs/1010.4386`), completion by derived double centralizers
(`https://arxiv.org/abs/1207.0612`), and Shaul on adic reduction to the diagonal
(`https://arxiv.org/abs/1602.03874`).  These theories substantially weaken any claim based merely
on failure of completion to commute with a derived operation.  The period-symbol completion here
is not yet an adic completion: it must be reconstructed from the nondiscrete embedded source group
and its critical operator bornology.  Proving that distinction mathematically is part of the open
core, not an assumption.

## Lean certificate

Lean proves unconditionally:

- construction and nonvanishing of the exponential mode in the analytic and meromorphic fields;
- its exact analytic and meromorphic translation eigenrelations;
- restriction of the existing rank-three boundary fingerprint to the physical source symbol;
- the complete iterated coface identity;
- equivalence `(3)`;
- the exact central degeneracy spectrum under rational independence.

The exact-module build and direct touched-file check pass without `sorry`, `admit`, `axiom`,
`opaque`, or `unsafe` declarations.

## Gates

- [x] genuine meromorphic exponential mode constructed
- [x] rank-three boundary fingerprint restricted exactly
- [x] every source-labelled coface compared
- [x] DA/meromorphic physical boundary equivalence proved
- [x] central spectrum proved
- [x] local comparison separated from global closed-range effectivity
- [x] uniform continuous left-invertibility classified exactly by period discreteness
- [x] theorem downgraded to bridge
- [ ] construct the source-forced completion functor in `(4)`
- [ ] prove the comparison morphism in `(4)` is presentation invariant
- [ ] compute `BCDef_F` for the rank-three multiple-Gamma chart
- [ ] transfer one analytic theorem through the completed comparison
- [x] prove that physical osculation is independent of the global effectivity phase
- [ ] construct the osculation/effectivity interaction morphism
