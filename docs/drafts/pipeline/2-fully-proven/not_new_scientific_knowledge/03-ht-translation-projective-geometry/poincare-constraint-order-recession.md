# Poincare hypertranscendence by exact constraint-order recession

- **ID:** `poincare-constraint-order-recession`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[BRIDGE] [PROVED]`; downgraded after parent audit of the exact-order input
- **Lane:** general hypertranscendence; constraint-limit mechanism
- **Statement:** For any transcendental entire solution of an autonomous first-order ADE with a repelling fixed point, the canonical DA approximants to its Poincare function have minimal ADE orders exactly `1,2,3,...`, while their locally uniform limit is HT.

## Setup

Let `f` be a transcendental entire solution of an autonomous first-order ADE. The complete order-one corollary in `asymptotically-exponential-algebraic-cascade-unit-cost.md`, based on the Briot--Bouquet classification, places every such `f` in the algebraic exponential-cover class. Suppose `f` has a repelling fixed point `zeta`, with multiplier

`lambda=f'(zeta)`, `|lambda|>1`.

Let `phi` be the normalized Poincare function:

`phi(0)=zeta`, `phi'(0)=1`,

`phi(lambda z)=f(phi(z))`.

Define the canonical approximants

`g_n(z)=f^[n](zeta+z/lambda^n)`.

Classical Poincare linearization gives local uniform convergence on `C`:

`g_n -> phi`.

## Theorem

`[BRIDGE] [PROVED HERE]` For every `n>=1`,

`ord_DA(g_n)=n`,

and the locally uniform limit `phi` is hypertranscendental.

Thus `phi` lies on a boundary of the DA functions where the least finite constraint order escapes exactly linearly.

## Proof

### Exact order of the approximants

The unit-cost cascade theorem applied to the `n` identical factors `f` gives

`ord_DA(f^[n])=n`.

Minimal ADE order is invariant under precomposition by a nonconstant affine map. Indeed, if `h(z)=F(az+b)` with `a!=0`, then

`h^(k)(z)=a^k F^(k)(az+b)`.

An ADE of order `r` for `F` therefore pulls back to one of order `r` for `h`; applying the inverse affine change gives the reverse inequality. Hence

`ord_DA(g_n)=ord_DA(f^[n])=n`.

### Hypertranscendence of the limit

Bergweiler's theorem states that the Poincare function of every transcendental entire function at a repelling fixed point is hypertranscendental. Hence `phi` is HT.

This use of Bergweiler is source-known. The new quantitative content under audit is the exact recession profile of his canonical approximants.

## Constraint-limit law

`[PROVED HERE]` The DA class is not closed under locally uniform convergence, even under canonical dynamical approximation. In this family the failure has an exact certificate:

`finite approximant depth n = minimal ADE order n -> infinity`.

The limit is not obtained by finding a final generative differential equation. It is selected by the static conjugacy constraint

`phi(lambda z)=f(phi(z))`

while every finite algebraic-differential handle recedes. This realizes the project principle that an HT object can be fixed by a constraint rather than propagated by a finite flow.

## Separation from Bergweiler's theorem

`[SEARCH]` Bergweiler proves that no transcendental entire function has all iterates satisfying one common ADE and concludes that its Poincare functions are HT. Uniform incoherence does not imply that the minimal ADE orders of the iterates are unbounded: equations may vary with `n` while their orders remain bounded and their degrees or coefficients diverge.

The present theorem proves, for every transcendental entire autonomous order-one map, the strictly stronger quantitative statement

`ord_DA(f^[n])=n`

and transfers it to the actual Poincare approximants.

## General conjecture

`[CONJECTURE]` Let `f` be any transcendental entire DA function with a repelling fixed point and Poincare function `phi`. For the canonical approximants

`g_n(z)=f^[n](zeta+z/lambda^n)`,

one has

`ord_DA(g_n) -> infinity`.

Bergweiler proves HT of `phi` but not this constraint-order recession. If true, the divergence would be a general quantitative precursor of Poincare hypertranscendence.

## RH pressure test, not selector

The theorem suggests a general research pattern for HT objects such as zeta: identify a canonical sequence of DA constraint approximants, prove that their minimal ADE orders diverge, and study which independent global constraint selects the HT limit.

For zeta, finite Euler products are an obvious but separately owned candidate approximation lane. No claim about their minimal ADE order, their limiting mode, or RH is made here. Even an exact recession theorem would establish HT architecture, not zero localization; an RH route would still need a positivity, self-adjointness, or rigidity law on the limiting constraint.

## Novelty and significance gates

- **Proof gate:** complete, conditional only on the proved unit-cost cascade theorem, affine invariance, classical Poincare convergence, and Bergweiler's HT theorem.
- **Significance gate:** gives an exact quantitative mechanism, for the complete autonomous order-one entire class, by which a canonical DA sequence exits every finite differential order and lands on an HT limit.
- **Parent-theory gate:** Bergweiler contains the convergence and HT endpoint. Reinhart's Schanuel-function minimal-order theorem is a close parent for the exact order of the autonomous iterates used here. Affine invariance then transfers that order to the canonical approximants. The assembled recession statement is useful, but it is a routine bridge once those parents are combined.
- **Literature gate:** the earlier audit missed Reinhart's access-restricted dissertation and therefore overstated the residual novelty of the quantitative input.
- **Rediscovery gate:** the project corpus contains no prior quantitative Poincare approximation result of this form.
- **Scientific label:** `[BRIDGE] [PROVED]`; no scientific-priority claim.

## Gates

- [x] 0 -> 1: canonical approximants and well-posed order invariant.
- [x] 1 -> 2: complete paper proof.
- [x] Significance: explicit HT boundary mechanism.
- [x] Bergweiler parent checked in full.
- [x] Dedicated Poincare/differential-order literature audit.
- [ ] General iteration-order divergence conjecture.
- [ ] Lean only after novelty and numerical pre-certification gates can both be satisfied.

## Primary references checked

1. W. Bergweiler, *Solution of a Problem of Rubel Concerning Iteration and Algebraic Differential Equations*, Indiana Univ. Math. J. 44 (1995), 257--267.
2. M. Boshernitzan and L. A. Rubel, *Coherent families of polynomials*, Analysis 6 (1986), 339--389.
3. H. Poincare, *Sur une classe nouvelle des transcendantes uniformes*, J. Math. Pures Appl. (4) 6 (1890), 313--365.
4. G. Fernandes, *A survey on the hypertranscendence of the solutions of the Schroder's, Bottcher's and Abel's equations*, arXiv:2102.12168 (2021).
5. A. E. Eremenko, *Meromorphic solutions of algebraic differential equations*, Russian Math. Surveys 37:4 (1982), 61--95.
6. G. M. Reinhart, *Schanuel Functions and Algebraic Differential Equations*, PhD dissertation, University of Illinois (1993).

## Lean progress — 2026-08-30

**A corpus search first, and it changes the card's status.**  The recession half was recorded here
as blocked on the two hypotheses of `exactDifferentialOrder_iterate_of_separation`.  It is not: the
corpus already owns the unit-cost law *unconditionally* for an explicit member of the card's class.

```text
HTGeometry/ExponentialTowerUnitCost.exactDifferentialOrder_expTower
    ** the n-fold exponential has differential order exactly n, no hypotheses **
HTGeometry/ExpPolyAllHeights.exactDifferentialOrder_expPolyCascade_all
    ** the same for a cascade of first-order linear entire maps with polynomial coefficients **
HTGeometry/EntirePoincareExtension.exists_entire_poincare
    ** the Poincaré germ at a repelling fixed point extends to an entire solution **
```

`HTGeometry/ExponentialPoincareRecession.lean` (new, axiom-clean, wired) puts them together:

- `expTower_eq_iterate`, `exactDifferentialOrder_exp_iterate` — the tower *is* the iterate, so the
  iterate of `Complex.exp` has exact differential order `n`;
- **`exactDifferentialOrder_poincareApprox_exp`** — the normalized approximants
  `z ↦ exp^{[n]}(ζ + z/λⁿ)` have exact differential orders `1, 2, 3, …`;
- `exists_exactDifferentialOrder_poincareApprox_exp_ge` — those orders are unbounded.

Since `Complex.exp` is a transcendental entire solution of the autonomous first-order equation
`f′ = f`, **the card's recession law now holds unconditionally for an explicit member of its own
class**, with the two hypotheses of `exactDifferentialOrder_iterate_of_separation` discharged rather
than assumed.

### Bergweiler's half: the exact remaining theorem

The HT half of the card reduces, by an elementary transcendence count, to the recession half.  Write
`φ` for the Poincaré function and suppose `φ` is differentially algebraic of order `N`.  Then

```text
φ(λᵏ z) = f^{[k]}(φ(z))                                          the Schröder equation, iterated
φ(λᵏ ·) is DA of order N                                         affine reparametrisation
ℂ(z)⟨φ, φ(λᵏ ·)⟩ has transcendence degree ≤ 1 + 2N over ℂ        two order-N jet fields
(d/dφ)^j f^{[k]} ∘ φ ∈ that field                                chain rule, dividing by φ′ ≠ 0
trdeg over ℂ(φ) ≤ 2N                                             φ is transcendental over ℂ
⟹ (f^{[k]})^{(0)}, …, (f^{[k]})^{(2N)} are algebraically dependent over ℂ(w)
⟹ f^{[k]} is DA of order ≤ 2N, for EVERY k
```

which contradicts the unbounded orders above.  So **the only missing theorem for Bergweiler in this
card's setting is the composition-decomposition law**

```text
φ nonconstant entire,  φ and g ∘ φ both DA of order ≤ N   ⟹   g is DA of order ≤ 2N ,
```

with the bound uniform in `g`.  Two of its three steps are already corpus theorems:
`EntireCascadeStateFieldOrder.differentiallyAlgebraicOfOrder_of_algebraic_state_derivatives` (an
entire function whose realization lies in a field of bounded transcendence degree over `ℂ(z)`
satisfies a bounded-order equation) and
`EntireJetEvaluation.jetEval_identically_zero_or_isolated` (a jet relation valid on a set with a
limit point is an identity, which is what transports the relation from the image of `φ` to the whole
plane).  What has to be built is the middle step: the chain-rule closure of the jets of `g` inside
`ℂ(z)⟨φ, g ∘ φ⟩` and the transcendence count over `ℂ(φ)`.

### Gate status

- `ord_DA(g_n) = n` for the canonical approximants: **Lean-closed unconditionally for `f = exp`**;
  the general autonomous first-order class needs the Briot–Bouquet normal form, which the corpus
  covers for the `expPoly` cascades.
- HT of the limit: reduced to the composition-decomposition law above; no longer a black-box import
  of Bergweiler's paper.

### The analytic half of the composition-decomposition law is CLOSED

`formal/GaloisForLFunctions/HTGeometry/CompositionOrderTransfer.lean` (built, wired, axiom-clean):

```text
eq_zero_of_eq_zero_on_range
    ** an entire function vanishing on the range of a nonconstant entire map is zero **
    (open mapping theorem + the identity theorem)
deriv_iteratedDeriv_comp
    ** the jet chain rule:  (g⁽ʲ⁾ ∘ φ)′ = (g⁽ʲ⁺¹⁾ ∘ φ) · φ′ **
differentiallyAlgebraicOfOrder_of_relation_on_range
    ** a nonzero differential polynomial in the jets of `g` vanishing along the range of a
       nonconstant entire `φ` makes `g` differentially algebraic of that order **
```

The chain rule is what puts every `g⁽ʲ⁾ ∘ φ` inside the differential field generated by `φ` and
`g ∘ φ`; the transfer theorem is what turns a relation in the inner variable into an algebraic
differential equation for `g`.  What remains of the composition-decomposition law is exactly the
transcendence count in the middle:

```text
trdeg_ℂ ℂ(z)⟨φ, g∘φ⟩ ≤ 1 + 2N   ⟹   φ, g∘φ, (g′∘φ), …, (g⁽²ᴺ⁾∘φ)  (2N+2 elements)
are algebraically dependent over ℂ,
```

which is `AlgebraicIndependent.cardinalMk_le_trdeg` applied inside the corpus's meromorphic field,
with the two order-`N` jet fields bounding the degree.  No second derivation is needed: including
`φ` itself as the coordinate slot is what avoids `D_φ`, correcting the plumbing obstacle recorded
above.

### The algebraic half is CLOSED too; only the meromorphic instantiation remains

`formal/GaloisForLFunctions/HTGeometry/CompositionJetClosure.lean` (built, wired, axiom-clean):

```text
compJet φ h            the outer jets:  compJet φ h 0 = h,  compJet φ h (j+1) = (compJet φ h j)′ / φ′
compJet_mem_differentialAdjoin
    ** every outer jet lies in the differential field generated by the inner function and the
       composite ** (derivation-closure plus division)
exists_relation_compJet_of_mem
    ** in any intermediate field of transcendence degree ≤ m containing them, φ together with the
       first m outer jets satisfies a nonzero relation over the constants **
exists_relation_compJet
    the same with the differential adjunction itself
exists_relation_compJet_of_algebraic
    ** if every jet of φ and of h is algebraic over a field generated by #I elements, then φ
       together with the first #I outer jets satisfies a nonzero relation **
```

The last statement is the composition-decomposition law in exactly the form the analytic side
consumes, and its transcendence bound comes from `StateFieldTrdeg.trdeg_algebraicClosure_adjoin_range_le`.

**What is left is the instantiation in the meromorphic field, and it is now mechanical:**

```text
1. b_φ, b_h := LinearizedTowerCoherence.exists_jet_algebraicWitness_family  for φ and for g ∘ φ
   (φ and g ∘ φ are differentially algebraic; the witness families are finite)
2. s := b_φ ++ b_h            ⟹  exists_relation_compJet_of_algebraic gives the relation
3. compJet (analyticMeroElement φ) (analyticMeroElement (g ∘ φ)) j
     = analyticMeroElement (g⁽ʲ⁾ ∘ φ)                       CompositionOrderTransfer.deriv_iteratedDeriv_comp
4. read the relation back as functions and apply
   CompositionOrderTransfer.differentiallyAlgebraicOfOrder_of_relation_on_range
```

Uniformity in `k` — what Bergweiler's contradiction needs — comes from step 1: for
`h_k = φ(λᵏ ·)` the witness family is the image of `b_φ` under the substitution automorphism, so
`#I = 2·#b_φ` is the same for every `k`, while `ord_DA(f^{[k]}) = k → ∞`.

### The composition-decomposition law is PROVED

`formal/GaloisForLFunctions/HTGeometry/EntireCompositionDecomposition.lean` (built, wired,
axiom-clean):

```text
analyticOnNhd_iteratedDeriv_comp
compJet_analyticMeroElement
    ** the abstract outer jets ARE the actual ones:
       compJet (φ) (g∘φ) j = the realization of g⁽ʲ⁾ ∘ φ **
differentiallyAlgebraicOfOrder_of_comp_witness
    ** φ nonconstant entire with nonvanishing realized derivative, and every jet of φ and of g ∘ φ
       algebraically witnessed over a family of size ≤ M+1
         ⟹  g satisfies an algebraic differential equation of order M **
```

That is the composition-decomposition law, with the order bound depending only on the witness
family — which is what makes it uniform in `k` when applied to `g = f^{[k]}`, `g ∘ φ = φ(λᵏ ·)`.

Supporting general theorems, all new and reusable:

```text
CompositionJetClosure.compJet, compJet_mem_differentialAdjoin,
  exists_relation_compJet_of_mem, exists_relation_compJet,
  exists_relation_compJet_of_algebraic(') , exists_relation_compJet_of_witness(')
CompositionOrderTransfer.eq_zero_of_eq_zero_on_range, deriv_iteratedDeriv_comp_entire,
  differentiallyAlgebraicOfOrder_of_relation_on_range
```

**The one remaining obstacle is instance hygiene, not mathematics.**
`LinearizedTowerCoherence.exists_jet_algebraicWitness_family` — the corpus theorem that supplies the
witness families — states its conclusion under an inline `letI` stack
(`((ratfuncToMero …).comp (algebraMap ℂ (RatFunc ℂ))).toAlgebra`, `OreLocalization.instCommRing`),
while everything on the `Set.univ` chart uses `UnivMeroFieldInstances`
(`univComplexAlgebraMero`, `FractionRing.field.toCommRing`).  The two agree mathematically — both
send a constant to its constant germ — but `AlgebraicWitness` statements written against them do not
unify.  Aligning them (an `Algebra.algebra_ext` transport, or restating the witness-family theorem
over `UnivMeroFieldInstances`) is the last step; after it, `differentiallyAlgebraic_of_comp` follows
in ten lines, and with the unbounded orders of `exactDifferentialOrder_poincareApprox_exp` it gives
Bergweiler's conclusion for this card's class.

**A pre-existing umbrella defect was found and fixed on the way:**
`MeroExponentialGauge` and `LinearizedTowerCoherence` both declared
`GaloisForLFunctions.HTGeometry.deriv_analyticMeroElement`, so the `HTGeometry` umbrella could not
elaborate.  The general-`W` version in `LinearizedTowerCoherence` is now
`deriv_analyticMeroElement_open`; its three call sites were updated and the module rebuilds.

### The instance obstacle is RESOLVED; `differentiallyAlgebraic_of_comp` is proved

`formal/GaloisForLFunctions/HTGeometry/CompositionDecompositionLaw.lean` (built, wired,
axiom-clean):

```text
AlgebraicWitness.extend            a witness extends along any family restricting to the original
differentiallyAlgebraic_of_comp
    ** φ nonconstant entire with nonvanishing realized derivative,
       φ and g ∘ φ differentially algebraic   ⟹   g differentially algebraic **
```

The two instance stacks on the plane — the scoped `UnivMeroFieldInstances` one and the inline one
that `LinearizedTowerCoherence.exists_jet_algebraicWitness_family` states its conclusion in — were
reconciled directly: the `CommRing` instances are definitionally equal (`rfl` closes that
congruence goal) and the two `Algebra ℂ (meroField univ)` instances are equal by
`Algebra.algebra_ext` together with `ratfuncToMero_C_eq_constToMero`, since both send a constant to
its constant germ.  So the earlier note that this was blocking is superseded.

### What is left for Bergweiler, exactly

`differentiallyAlgebraic_of_comp` gives *some* order for each `g = f^{[k]}`.  The contradiction with
`ord_DA(f^{[k]}) = k → ∞` needs that order to be **uniform in `k`**, which
`differentiallyAlgebraicOfOrder_of_comp_witness` already provides — its bound is the size of the
combined witness family.  So the remaining step is:

```text
for h_k = φ(λᵏ ·),  a witness family of the SAME size p as φ's,
  namely  b_{h_k} := precompMeroEquiv (dilation λᵏ) ∘ b_φ
```

using `Bottcher.MeromorphicField.precompMeroEquiv` (the deck automorphism of the meromorphic field
attached to a self-biholomorphism, already in the corpus) together with `AlgebraicWitness.map`, plus
the elementary jet identity `(φ(λᵏ ·))⁽ʲ⁾(z) = λ^{kj} φ⁽ʲ⁾(λᵏ z)`.  With that, the common family has
size `2p` for every `k`, `differentiallyAlgebraicOfOrder_of_comp_witness` bounds every
`ord_DA(f^{[k]})` by `2p`, and `exists_exactDifferentialOrder_poincareApprox_exp_ge` contradicts it.
