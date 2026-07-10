# Summable Euler corners are Calkin-injective

- **ID:** summable-euler-calkin-injectivity
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE -> LEAN TARGET]`
- **Parent:** `../3-formalized/new/finite-euler-calkin-independence.md`
- **Source:** increasing prime-scale positive Euler metric corners on the concrete Sonin /
  Hardy--Titchmarsh carrier

## Conjectured theorem

Let `r : N -> R` be strictly increasing with `r_n>1`, let `c : N -> C` be absolutely
summable and not identically zero, and let `a>0`. Then the operator-norm convergent sum

```text
sum_n c_n (1-Q_a)(U_(r_n)+U_(r_n)*)Q_a
```

is not compact.

Equivalently, the map from `ell^1` coefficient sequences to the Calkin quotient determined by the
increasing dilation corners is injective. The same should hold for positive Euler metric corners
and, by unitary transport, on the concrete archimedean Hardy--Titchmarsh line.

## Proof under attack

Let `k` be the least index with `c_k != 0`. Strict increase gives a gap
`r_k < r_(k+1)`. Choose `b>a` so close to `a` that

```text
b <= r_k a,
b r_k < a r_(k+1).
```

The scaled-shell observer at `r_k` kills every `j>k` term and every `j<k` coefficient is zero
by minimality. Continuity of the observer and evaluation should allow the exact finite calculation
to pass through the absolutely convergent operator series, leaving

```text
A_k (sum_n c_n D_(r_n)) g_m = c_k U_(r_k) g_m
```

for every shell cell `g_m`. The existing corrected-shell noncompactness theorem then applies.

## Attack obligations

- [ ] Prove operator-norm summability from `Summable (fun n => ||c_n||)` and the uniform
  `||U_r+U_r*|| <= 2` bound.
- [ ] Select the least nonzero coefficient and a single separating shell from the next scale.
- [ ] Commute the continuous observer, evaluation, and dilation identities through the `tsum`.
- [ ] Prove ambient and exact even-carrier noncompactness.
- [ ] Transport the summable positive Euler corner series to the concrete Hardy--Titchmarsh line.
- [ ] Run a primary-source novelty audit before promotion.

## Significance target

If proved, this excludes not only finite additive counterterms but every absolutely convergent
infinite additive renormalization of the canonical positive Euler metric corners. A surviving
all-place index would therefore have to use conditional summation, nonlinear/product compensation,
a regulator-dependent limit, a different polarization, or a different operator ideal.

## Exact boundary

The theorem would not apply to the Euler coefficients in their raw divergent ordering unless an
`ell^1` weighting is supplied. It would not exclude Connes--Consani multiplicative quasi-inner
products or a conditionally convergent/global functional-equation regularization. It would still
not locate zeta zeros or move the verified range by itself.

