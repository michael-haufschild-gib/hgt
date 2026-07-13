# Feigenbaum critical-order postcritical product law

- **ID:** `feigenbaum-critical-order-postcritical-product-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean 4)
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The first nonzero critical jet of order `m` forces the complete derivative product
  before dyadic time `2^n` to equal `(-1)^n alpha^(n(m-1))`.

## The value law

Let `g : C -> C` be analytic near the required orbit values and satisfy

```text
g(g(x))=lambda g(alpha x),
g(0)=1,
alpha lambda=-1,
g(-x)=g(x).
```

Suppose zero has finite critical order `m>=2`:

```text
g^(k)(0)=0       for 1<=k<m,
g^(m)(0)!=0.
```

Then, for every natural number `n`,

```text
Pi_(m,n)
  := product_(j=1)^(2^n-1) g'(g^[j](0))
   = lambda^n alpha^(mn)
   = (-1)^n alpha^(n(m-1)).                         (1)
```

For a real normalization with `alpha>1`,

```text
|Pi_(m,n)|=alpha^(n(m-1))
          =(2^n)^((m-1)log(alpha)/log(2)),           (2)

sum_(j=1)^(2^n-1) log|g'(g^[j](0))|
          =n(m-1)log(alpha).                         (3)
```

Thus the postcritical derivative-growth exponent is not merely a value attached to `alpha`; it
factors exactly as

```text
critical-order excess  x  spatial-scaling exponent
      (m-1)            x       log(alpha)/log(2).    (4)
```

The quadratic product law is the special case `m=2`.

## Proof

The functional equation and evenness give the exact dyadic value identity

```text
g^[2^n](x)=lambda^n g(alpha^n x).                    (5)
```

Put `h_n=g^[2^n-1]`, so the left side of (5) is `h_n(g(x))`. The Faà di Bruno formula for its
`m`-th derivative at zero is a sum indexed by partitions of `m`. Every term with at least two
blocks contains a derivative `g^(k)(0)` with `1<=k<m`, hence vanishes. The unique one-block term is

```text
(h_n o g)^(m)(0)=h_n'(g(0))g^(m)(0)
                =h_n'(1)g^(m)(0).                   (6)
```

The right side of (5) has `m`-th derivative

```text
lambda^n alpha^(mn)g^(m)(0).                        (7)
```

Canceling the nonzero first critical jet gives

```text
h_n'(1)=lambda^n alpha^(mn).                        (8)
```

The derivative chain rule and `g(0)=1` identify the left side with the complete product in (1).
Finally,

```text
lambda^n alpha^(mn)
  =(lambda alpha^m)^n
  =(-alpha^(m-1))^n,
```

which proves (1). Absolute values and logarithms prove (2)--(4).

## Law developed from the relation

Equation (4) is a **critical-order amplification law**. Changing the critical order does not
merely select a different scaling constant `alpha_m`; it multiplies the postcritical cocycle
exponent by the exact ramification excess `m-1`:

```text
E_m=(m-1) log(alpha_m)/log(2).                       (9)
```

This creates a directly comparable invariant across the finite-criticality Feigenbaum fixed
points. It also characterizes the scaling value from orbit derivatives:

```text
alpha_m=|Pi_(m,n)|^(1/(n(m-1)))                     (10)
```

for every `n>=1`. Formula (10) uses only values on one finite postcritical orbit segment.

## Novelty audit

The parent literature contains Feigenbaum fixed points of arbitrary finite critical order, the
dependence of universality data on that order, the dyadic scaling identity, and general derivative
cocycle formulas. Focused searches also found the infinite-criticality limit and work on gauge
corrections to Feigenbaum scaling. No located source states (1), the factorization (4), or the
finite-orbit recovery formula (10).

The candidate-new label is therefore evidence-based but provisional. The remaining novelty gate
is specialist comparison with thermodynamic-formalism treatments of higher-criticality fixed
points, where the same exponent might be encoded under a pressure or cocycle normalization.

## Lean status

The complete arbitrary-order theorem is formalized in
`formal/GaloisForLFunctions/HTGeometry/FeigenbaumValueRelations.lean` as

```text
feigenbaum_criticalOrder_postcritical_deriv
feigenbaum_criticalOrder_postcritical_product
```

Its reusable critical-jet input is formalized in
`formal/GaloisForLFunctions/HTGeometry/FirstNonzeroJetComposition.lean` as

```text
iteratedDeriv_comp_of_firstNonzero_innerJet
```

The earlier quadratic instances remain available as

```text
feigenbaum_quadratic_postcritical_deriv
feigenbaum_quadratic_postcritical_product
```

The direct module build passes.  The three new declarations depend only on the standard Mathlib
axioms `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] exact value relation isolated
- [x] complete order-independent paper proof
- [x] nontrivial law developed from the relation
- [x] quadratic instance formalized in Lean
- [x] focused primary and adjacent-literature search
- [x] generic first-nonzero-jet composition lemma in Lean
- [x] arbitrary-critical-order derivative and product laws in Lean
- [ ] independent specialist novelty audit

## References checked

- M. Campanino, H. Epstein, and D. Ruelle, *On Feigenbaum's Functional Equation*, IHES/P/80/32,
  1980.
- G. Levin and G. Swiatek, *Measure of the Julia Set of the Feigenbaum Map with Infinite
  Criticality*, 2007, arXiv:0705.0297.
- A. Raju and J. P. Sethna, *Reexamining the Renormalization Group: Period Doubling Onset of
  Chaos*, 2018, arXiv:1807.09517.
- U. Frisch, K. Khanin, and T. Matsumoto, *Multifractality of the Feigenbaum Attractor and
  Fractional Derivatives*, 2003.

## Log

- 2026-07-11 -- Extracted the arbitrary-critical-order relation from the dyadic value identity,
  proved the critical-order amplification law, and completed the preliminary collision search.
