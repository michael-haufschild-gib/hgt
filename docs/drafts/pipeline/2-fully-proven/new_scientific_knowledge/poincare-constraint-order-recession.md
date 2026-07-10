# Poincare hypertranscendence by exact constraint-order recession

- **ID:** `poincare-constraint-order-recession`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
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

`[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [PROVED HERE]` For every `n>=1`,

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
- **Parent-theory gate:** Bergweiler 1995 checked in full; it contains the convergence and HT endpoint but not minimal-order recession.
- **Literature gate:** checked against Bergweiler's paper, its cited-by corpus, the 2021 Fernandes survey, Crossref, OpenAlex, arXiv, and searches for Poincare/Schroder approximants with minimal differential order. No exact order sequence or constraint-order recession theorem was found.
- **Rediscovery gate:** the project corpus contains no prior quantitative Poincare approximation result of this form.
- **Scientific label:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`; publication priority remains to be independently verified.

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
