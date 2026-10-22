# Normal-domain rational-Witt Galois intersection

- **ID:** `deninger-rational-witt-normal-domain-galois-intersection`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) · SOURCE CORRECTION
- **Route:** L — rational-Witt source foundation
- **Primary source:** Christopher Deninger, *Rational Witt vectors and associated sheaves*,
  arXiv:2508.05329v1, Theorem 1.2 (source label `t1.1`).
- **Status:** `[LEAN-PROVED] [DEPENDENCY-CLOSED] [NOVELTY-UNCLEAR]`

## Statement

Let `A` be an integrally closed domain, let `K = Frac(A)` be perfect, let
`L = AlgebraicClosure(K)`, let `B` be the integral closure of `A` in `L`, and let
`G = Aut_K(L)`.  Regard all rational-Witt rings as their literal normalized-rational-function
subrings of the big-Witt rings.  For `w in W_rat(L)`,

```text
w is G-fixed and w lies in image(W_rat(B) -> W_rat(L))
    iff
w lies in image(W_rat(A) -> W_rat(L)).
```

Equivalently,

```text
image(W_rat(A) -> W_rat(L))
  = W_rat(L)^G ∩ image(W_rat(B) -> W_rat(L)).
```

This is the sharp normal-domain replacement for the false unrestricted perfect-field clause in
Deninger's displayed Theorem 1.2.  The cusp `A = Q[X^2,X^3]` proves integral closedness cannot be
deleted.

## Why published statement needs correction

The source theorem states the perfect-quotient-field equality for every integral domain.  For
`A = Q[X^2,X^3]`, the fraction-field element `t = X^3/X^2` is integral over `A` but not in `A`.
Its Teichmuller rational-Witt vector belongs to the absolute normalization and is fixed by every
absolute Galois automorphism, but its linear power-series coefficient prevents descent to `A`.
This counterexample is already paper-proved and formalized by
`DeningerRationalWittDomainDescentCounterexample.lean`.

## Complete proof

Write `e_L : Z[L^x] -> W_rat(L)` for the reduced-monoid-algebra isomorphism over the
algebraically closed field `L`.  Write

```text
x = e_L^{-1}(w) in Z[L^x].
```

There are unique positive and negative multiplicity multisets `x_+` and `x_-` such that

```text
x = sum_{a in x_+} (a) - sum_{a in x_-} (a).
```

Define canonical normalized polynomials

```text
P_x(T) = product_{a in x_+} (1-aT),
Q_x(T) = product_{a in x_-} (1-aT).
```

Then `w = P_x/Q_x` in the literal rational-Witt carrier.

Assume first that `w` is `G`-fixed and comes from `w_B in W_rat(B)`.  The domain `B` has
fraction field `L`, is integrally closed there, and `L` is algebraically closed.  Therefore the
already proved aic-domain comparison gives a unique `x_B in Z[B \ {0}]` representing `w_B`.
Naturality of Teichmuller atoms gives

```text
x = image(x_B) in Z[L^x].                         (1)
```

Because the map `B \ {0} -> L^x` is injective, every atom occurring in `x_+` or `x_-` is the
image of an element of `B`.  Every such element is integral over `A`.  Coefficients of a finite
product of the factors `1-aT` are sums of products of these integral elements, hence every
coefficient of `P_x` and `Q_x` is integral over `A`.

The `G`-fixedness of `w`, transported through `e_L`, makes `x`, `x_+`, `x_-`, `P_x`, and `Q_x`
`G`-stable.  Since `K` is perfect, the infinite-Galois fixed-field theorem descends the two
polynomials coefficientwise:

```text
P_0, Q_0 in K[T],
P_0 mapped to L[T] = P_x,
Q_0 mapped to L[T] = Q_x.                         (2)
```

The embedding `K -> L` is injective.  Combining (2) with coefficient integrality of `P_x,Q_x`
shows every coefficient of `P_0,Q_0` is integral over `A`.  Since `A` is integrally closed in
`K`, there are polynomials `P_A,Q_A in A[T]` whose coefficient extensions to `K[T]` are
`P_0,Q_0`.  Constant coefficients remain one by injectivity.  Thus

```text
w_A := P_A/Q_A in W_rat(A)
```

maps to `P_x/Q_x = w` in `W_rat(L)`.  This proves the difficult inclusion.

Conversely, assume `w` is the image of `w_A in W_rat(A)`.  Mapping `w_A` through
`A -> B -> L` supplies a normalization preimage.  Mapping it through `A -> K -> L` expresses
`w` as the extension of a rational-Witt vector over `K`.  Every `K`-automorphism of `L` fixes
that image coefficientwise, so `w` is `G`-fixed.  This proves the reverse inclusion.

No Fatou-domain premise, complete-integral-closure premise, separability premise beyond
perfectness of `K`, or desired descent conclusion is assumed.

## Hostile audit

- **Not the false theorem:** normalization incidence is retained explicitly; normality is used at
  the only legitimate descent step `integral K-coefficient -> A`.
- **No atomwise Galois descent:** Galois-stable positive and negative multisets descend through
  their orbit-product polynomials; individual atoms need not lie in `K`.
- **No hidden Fatou assumption:** proof uses finite canonical atom support, so it does not infer the
  Fatou property from integral closedness.
- **Nilpotents irrelevant but not discarded upstream:** theorem concerns domains; arbitrary-ring
  canonical big-Witt multiplication and rational-Witt localization remain the ambient functor.
- **Sharpness:** formal cusp counterexample violates exactly integral closedness and falsifies the
  same conclusion.

## Novelty audit

Latest arXiv record checked 2026-08-12: only v1 exists.  Targeted primary-source/arXiv searches
found the source theorem and older field-level rational-Witt descent, but no published correction
with this exact normalization-incidence formulation.  Classification remains `NOVELTY-UNCLEAR`:
the proof is a finite-support repair of the source argument, not an RH theorem and not claimed as
literature-new without author-level review.

## Gates

- [x] 0 -> 1: exact false source clause and sharp counterexample identified
- [x] 1 -> 2: dependency-closed proof above; all invoked algebraic ingredients already formalized
- [x] 2 -> 3: Lean theorem, umbrella import, direct check, axiom audit, targeted module build
- [ ] 3 -> 4: standalone publication treatment and external author review

## Lean formalization

- **Module:** `GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittNormalDomainGaloisIntersection`
- **Capstone:**
  `deningerRationalWittNormalDomain_galoisFixed_normalization_iff_exists_base`
- **Sharp obstruction:** `deningerCuspPerfectGaloisFixed_counterexample`
- **Normality necessity:**
  `deningerRationalWittTeichmullerDescent_implies_integralClosedness`

Supporting theorems formalize normalization-presentation naturality, integrality of positive and
negative atoms, integrality of atom-polynomial coefficients, polynomial descent through a normal
base, and transfer of algebraic closedness through the fraction-field equivalence.

## Log

- 2026-08-12 — derived corrected theorem after refuting unrestricted source statement.
- 2026-08-12 — completed hostile paper proof via canonical positive/negative atom polynomials;
  avoided false implication `integrally closed => Fatou`.
- 2026-08-12 — formalized capstone and all missing infrastructure in Lean; wired Route-L umbrella;
  direct module check and targeted build passed. Axiom audit reports only `propext`,
  `Classical.choice`, and `Quot.sound`. Repository lint finds no defect in this module but remains
  nonzero because seven unrelated Route-T/Suzuki modules are not reachable from the umbrella.

## Imperfect-field strengthening (2026-08-13)

The perfectness restriction is now removed by
`DeningerRationalWittInseparabilityNormalDomainDescent.lean`. For every integrally closed domain
`A`, without assuming `Frac(A)` perfect, the exact corrected statement is:

```text
absolute-Galois invariance
and d(a) divides every integral atom coefficient
and incidence from the absolute normalization
  iff
descent from W_rat(A).
```

Here `d(a)` is finite inseparability degree of `Frac(A)(a)/Frac(A)`. Capstone:
`deningerRationalWittNormalDomain_galoisInvariant_insepDivisible_normalization_iff_exists_base`.
Its field engine is
`deningerRationalWittIntegralGaloisInvariantInsepDivisible_iff_exists_base`. The earlier perfect-
field theorem remains a convenient specialization; it is no longer frontier. Classification
remains literature parity/source correction, not RH progress.
