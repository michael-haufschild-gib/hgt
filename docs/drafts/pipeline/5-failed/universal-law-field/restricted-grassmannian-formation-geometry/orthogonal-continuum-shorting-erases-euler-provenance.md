# Orthogonal continuum shorting erases Euler provenance

- **ID:** ULF-OCSE-001
- **Stage:** 5-failed
- **Type:** RETIRED MECHANISM + POSITIVE SURVIVOR
- **Parent:** `ULF-CAGC-001`
- **Retired claim:** the positive source reduction is orthogonal shorting by the closed range of
  the cubic-gauged Gaussian continuum synthesis.

## Big-picture question

Can the negative continuum leg be removed inside the completed Burnol Hilbert space, leaving a
positive Euler covariance whose action bounds the integral boundary defect?

No.  Completion has already forgotten the distinction one needs to retain.  The continuum
columns are total in the Burnol carrier.  Their closed range is the whole carrier, so orthogonal
shorting removes every Euler column as well.

The positive survivor is structural: Euler formation and Gaussian continuum are distinguishable
by mutually singular **label measure classes** before synthesis, but not by closed output ranges
after synthesis.  Any viable relative completion must therefore retain provenance through a
mapping cone, rigged relation, or cyclic boundary construction before Hilbert closure.

## Checked corpus locks

Corpus search:

```text
scripts/formal_tools.py research \
  "dense span laplace feature synthesis continuum range shorting atomic measure absolutely continuous"
```

Relevant existing laws:

1. `range_featureSynthesis_eq_span` identifies algebraic feature-synthesis range with feature
   span.
2. `dense_range_featureSynthesis_of_topologicalClosure_span_eq_top` upgrades total feature span
   to dense synthesis range.
3. `continuousBoundaryReporter_eq_zero_of_cyclic_denseRange` proves the same general erasure
   mechanism for continuous reporters on a dense completion.
4. Corpus absolute-continuity modules distinguish semilocal and archimedean weighted measures,
   but no declaration proves totality of the present Cauchy-cubic Laplace columns or the resulting
   shorting collapse.

This card proves that missing special case on paper.

## Theorem OCSE-A: continuum columns are total

Let

```text
H_B=L2((0,infinity),dr),
f_lambda(r)=r exp(-lambda*r),  lambda>0.
```

Then

```text
closure(span {f_lambda | lambda>0})=H_B.              (OCSE.1)
```

**Proof.** Suppose `q in H_B` is orthogonal to every `f_lambda`.  Fix `a>0`.  By
Cauchy--Schwarz,

```text
h_a(r)=r*conj(q(r))*exp(-a*r)
```

belongs to `L1(0,infinity)`, since `r exp(-a r)` belongs to `L2`.  For every `t>0`,

```text
integral h_a(r) exp(-t*r) dr
  = <f_(a+t),q>
  = 0.
```

Uniqueness of the Laplace transform on `L1(0,infinity)` gives `h_a=0` almost everywhere.  Since
`r exp(-a r)>0` for `r>0`, `q=0` almost everywhere.  The orthogonal complement of the span is
zero, proving `(OCSE.1)`.  QED.

## Theorem OCSE-B: the cubic gauge does not repair shorting

For `x,c>0`, let

```text
m_(x,c)(lambda)
  = exp(-pi*x*exp(2*lambda)/2)
      *(1-exp(-2*c*lambda))^(3/2).
```

This scalar is strictly positive and continuous for every `lambda>0`.  The continuum columns of
`ULF-CAGC-001` are

```text
g_lambda=m_(x,c)(lambda) f_lambda.
```

Hence their algebraic span has the same closure as the bare columns.  Moreover each `g_lambda`
lies in the closure of the range of the continuum synthesis `A_(0,x,c)`: normalized indicator
functions of shrinking label intervals give Bochner averages converging in `H_B` to `g_lambda`.
Therefore

```text
closure(Ran A_(0,x,c))=H_B.                           (OCSE.2)
```

If `P_0` denotes the orthogonal projection onto that closed range, then `P_0=I`, and for the
Euler synthesis

```text
(I-P_0) A_(E,x,c)=0,
(I-P_0) K_E (I-P_0)=0.                               (OCSE.3)
```

Thus ordinary Hilbert-range shorting produces the zero budget.  It cannot transgress to a
nonzero integral defect.  QED.

## Positive survivor: provenance survives only before completion

The same cubic-gauged source can be written using two finite positive label measures:

```text
mu_E
  = sum_(n>=2)
      [Lambda(n)/n * exp(-pi*x*n^2)
        *(1-n^(-2*c))^3] delta_(log n),               (OCSE.4)

mu_0
  = exp(-pi*x*exp(2*lambda))
      *(1-exp(-2*c*lambda))^3 d lambda.               (OCSE.5)
```

`mu_E` is pure point and supported on the countable set `{log n | n>=2}`.  `mu_0` is absolutely
continuous and gives that set measure zero.  Consequently

```text
mu_E perp mu_0.                                       (OCSE.6)
```

Their provenance sectors are orthogonal in the label measure class, even though the continuum
synthesis has dense range and swallows every Euler output column after Hilbert completion.

This proves an exact nonfaithfulness law:

```text
atomic/continuum Lebesgue decomposition
  --Burnol synthesis and Hilbert closure-->
no orthogonal output-range decomposition.             (OCSE.7)
```

The formation distinction is not a subspace of `H_B`; it is data in the source-to-completion
arrow.  The correct relative object must be a derived defect of that arrow.

## What is now impossible

1. Quotienting by `closure(Ran A_0)` annihilates the complete source carrier.
2. A Schur complement based only on the orthogonal output-range projection has the same collapse.
3. Any continuous reporter defined solely on the quotient completed Hilbert space is provenance
   blind.
4. The negative Krein sign does not create a complementary continuum subspace; it records label
   grading before completion.

## Exact successor obligation

Construct a provenance-retaining completion cone

```text
C_(x,c) = Cone(
  L2(mu_E) directSum L2(mu_0)
    --[A_E  A_0]--> H_B),                             (OCSE.8)
```

or an equivalent rigged/cyclic relation, and a degree-three boundary character

```text
partial_D : C_(x,c) -> S_1(Hardy boundary),
partial_D([mu_E]-[mu_0])=mathsf T_D.                  (OCSE.9)
```

It must retain the mutually singular label decomposition, all mixed Gram entries, and literal
unsquared Euler coefficients.  Its positive reduction must be performed before the nonfaithful
Hilbert closure and prove

```text
0<=Tr mathsf T_D<=Tr K_E<B_base<1.                   (OCSE.10)
```

This is not supplied here.  The card retires only orthogonal continuum shorting.

## Status

No-go and positive survivor are dependency-closed on paper.  Lean formalization deferred by the
current read-only research phase.
