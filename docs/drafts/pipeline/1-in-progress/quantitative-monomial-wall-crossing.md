# Quantitative monomial wall crossing

- **ID:** `quantitative-monomial-wall-crossing`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Date:** 2026-08-17
- **Statement:** For an exact detuning (c g^b), (c\ne0), (0<g\le1), the sinc reporter has an explicit quadratic precritical error, an exact critical profile, and an explicit power-law postcritical bound at every inverse-power horizon.

## Goal

Replace qualitative (g\to0) convergence by finite-(g) inequalities usable for observation-time
and coupling-strength budgets.

## Exact target

For (\tau>0), (c\ne0), and natural (b,r):

- if (r<b),
  \[
  \left|\operatorname{sinc}(\tau c g^{b-r})-1\right|
  \le \frac{(\tau |c|)^2}{6}g^{2(b-r)};
  \]
- if (r=b), the reporter is exactly (\operatorname{sinc}(\tau c));
- if (b<r),
  \[
  \left|\operatorname{sinc}\!\left(\frac{\tau c}{g^{r-b}}\right)\right|
  \le \frac{g^{r-b}}{\tau |c|}.
  \]

## Gates

- [x] 0 → 1: exact target and corpus inequalities identified
- [ ] 1 → 2: complete paper proof
- [ ] 2 → 3: Lean theorem family
- [ ] 3 → 4: publication integration

## Approach

Use the corpus inequalities (0\le1-\operatorname{sinc}x\le x^2/6) and

\[
|\operatorname{sinc}x|\le |x|^{-1}.
\]

The critical identity is algebraic cancellation of equal powers. No analytic remainder constant is
needed because the scaled l-bit detuning is an exact monomial.

## Log

- 2026-08-17 — created in Stage 1 after rejecting a nonexistent analytic-uniform rate.

