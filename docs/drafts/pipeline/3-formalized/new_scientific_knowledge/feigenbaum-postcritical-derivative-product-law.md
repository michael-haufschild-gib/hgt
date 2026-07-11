# Feigenbaum postcritical derivative-product law

- **ID:** `feigenbaum-postcritical-derivative-product-law`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** For the normalized quadratic Feigenbaum fixed point, the product of the
  derivative values after the critical value and before dyadic time `2^n` is exactly
  `(-alpha)^n`.  Hence `log(alpha)/log(2)` is the exact polynomial-growth exponent of this
  postcritical product.

## The value law

Let `g : C -> C` be twice continuously differentiable and satisfy

```text
g(g(x))=lambda g(alpha x),
g(0)=1,
alpha lambda=-1,
g(-x)=g(x).
```

Assume the critical point at zero is exactly quadratic:

```text
g'(0)=0,    g''(0)!=0.
```

Then, for every natural number `n`,

```text
product_(j=1)^(2^n-1) g'(g^[j](0))=(-alpha)^n.              (1)
```

For the real normalized Feigenbaum fixed point, `alpha>1`, so (1) gives the exact magnitude and
logarithmic sum

```text
|product_(j=1)^(2^n-1) g'(g^[j](0))|=alpha^n
  =(2^n)^(log(alpha)/log(2)),                                (2)

sum_(j=1)^(2^n-1) log|g'(g^[j](0))|=n log(alpha).           (3)
```

Thus the spatial Feigenbaum constant is also an exact postcritical derivative-growth value.  The
ordinary average in (3), divided by `2^n-1`, tends to zero, while its unaveraged growth retains the
nonzero exponent `log(alpha)/log(2)`.

## Proof

The dyadic value identity proved from the functional equation and evenness is

```text
g^[2^n](x)=lambda^n g(alpha^n x).                            (4)
```

Put `h_n=g^[2^n-1]`, so `g^[2^n]=h_n o g`.  Apply the second-order chain rule at the quadratic
critical point:

```text
(h_n o g)''(0)
  =h_n''(g(0)) g'(0)^2+h_n'(g(0))g''(0)
  =h_n'(1)g''(0).                                           (5)
```

Taking two derivatives of the right side of (4) gives

```text
(lambda^n g(alpha^n x))'' at x=0
  =lambda^n alpha^(2n)g''(0).                               (6)
```

Since `g''(0)!=0`, equations (5)--(6) imply

```text
h_n'(1)=lambda^n alpha^(2n)=(-alpha)^n.                     (7)
```

Finally, the iterate chain rule and `g(0)=1` give

```text
h_n'(1)=product_(j=1)^(2^n-1) g'(g^[j](0)),                 (8)
```

which proves (1).  Equations (2)--(3) follow by absolute values and logarithms.

## Significance

1. The relation uses values from three structures at once: the Feigenbaum scaling constant, the
   complete finite postcritical orbit, and the derivative cocycle.
2. It characterizes `alpha` from orbit-derivative values alone:

   ```text
   alpha=|product_(j=1)^(2^n-1) g'(g^[j](0))|^(1/n)
   ```

   for every `n>=1`, rather than only as the spatial rescaling in the functional equation.
3. It refines the zero Lyapunov exponent at the Feigenbaum attractor by retaining the exact
   subexponential growth law erased by division by time.
4. It is independent of the open hypertranscendence question.  No differential-algebraic
   conclusion is inferred from (1).

## Novelty audit

The primary normalization source Campanino--Epstein--Ruelle records the functional equation and
the first critical values `g(1)=lambda` and `lambda g'(1)=-1`.  Searches also located standard
iterate-multiplier formulas, the zero Lyapunov exponent at the onset of chaos, multifractal
descriptions of the Feigenbaum attractor, and general period-doubling scaling results.  No located
source states the exact all-`n` product (1), the exact log-sum (3), or the identification of
`log(alpha)/log(2)` as this postcritical derivative-product exponent.

This is affirmative evidence rather than proof of absence.  The candidate-new label remains
provisional pending review by a specialist in period-doubling renormalization and comparison with
the thermodynamic-formalism literature.

## Lean certificate

`formal/GaloisForLFunctions/FeigenbaumValueRelations.lean` proves:

```text
deriv_iterate_eq_orbitProduct
feigenbaum_quadratic_postcritical_deriv
feigenbaum_quadratic_postcritical_product
```

The formal theorem is over `C`, assumes only the displayed functional equation, evenness, `C^2`
regularity, and a nonzero quadratic critical jet, and returns (1) exactly.  The targeted module
build passes.  The axiom report contains only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` axioms.

## Gates

- [x] exact value relation isolated
- [x] complete paper proof
- [x] unconditional Lean formalization
- [x] targeted build passes
- [x] axiom audit passes
- [x] preliminary primary and adjacent-literature search
- [ ] independent specialist novelty audit
- [ ] determine whether the exponent has an established thermodynamic interpretation under a
  different normalization

## References checked

- M. Campanino, H. Epstein, and D. Ruelle, *On Feigenbaum's Functional Equation*, IHES/P/80/32,
  1980.
- P. Hertling and C. Spandl, *Computing a Solution of Feigenbaum's Functional Equation in
  Polynomial Time*, 2014.
- U. Frisch, K. Khanin, and T. Matsumoto, *Multifractality of the Feigenbaum Attractor and
  Fractional Derivatives*, 2003.
- J. P. R. Christensen and P. Fischer, *Linear Independence of Iterates and Entire Solutions of
  Functional Equations*, 1988.

## Log

- 2026-07-11 -- Extracted the second-jet transport law from the dyadic iterate identity, proved
  the exact postcritical product, completed the preliminary literature collision search, and
  formalized the theorem in Lean.
