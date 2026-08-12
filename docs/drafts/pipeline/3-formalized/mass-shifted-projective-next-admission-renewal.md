# Mass-shifted projective next-admission renewal

- **ID:** `mass-shifted-projective-next-admission-renewal`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 exact open core
- **Statement:** Current literal adaptive mixed/completed arithmetic work splits exactly into a
  strict retained Jacobi inventory plus the next monic admission norm.

## Goal

Replace unsupported cross-degree clock comparison by an exact source-first landing.  For current
degree `n>0`, write `h_n` for admitted monic norm, `F_n` for cumulative Jacobi flux,
`c_n=2n+1`, and `mathfrak S_n=c_n D_n-F_n^2` for projective arithmetic surplus.  Prove

```text
h_n mathfrak S_n
  = 2 c_n (n+1) h_(n+1) + retained Jacobi inventory,
```

with retained inventory strictly positive on every positive `(n+2)` block.  This lands current
pre-aggregation arithmetic source into next even admission edge without orientation map or fixed
linear reporter.

## Gates

- [x] 0 → 1 in-progress: exact algebra, source purity, and hostile alternatives isolated
- [x] 1 → 2 fully-proven: complete paper proof recorded
- [x] 2 → 3 formalized: targeted Lean build and axiom audit pass
- [ ] 3 → 4 publication-ready

## Conjecture / proof-or-fail loop

1. Adjacent projective clocks have ordered jumps. **Failed.** Their difference has numerator
   `2 F_n - (2n+1)(alpha_n+alpha_(n+1))`, with no sign from positive moment geometry.
2. Next Christoffel edge alone gives uniform work. **Failed.** Positive Jacobi shapes can make all
   beta coordinates arbitrarily small relative to nonzero diagonal mean.
3. Projective surplus is a cumulative nonconcentration inventory. **Proved.** Its alpha part is
   weighted trace variance and its beta part is positive renewal inventory.
4. Current source work contains next admission norm exactly. **Proved on paper and in Lean.** By
   `beta_(n+1)=h_(n+1)/h_n`, multiplying the exact surplus split by `h_n` extracts
   `2(2n+1)(n+1)h_(n+1)`. Remaining term contains the strictly positive current edge `beta_n`.

## Paper proof

Let

```text
V_n = c_n (2 sum_(j<n) alpha_j^2 + alpha_n^2) - F_n^2,
B_n = c_n (4 sum_(j<n) beta_j + 2(n+1)(beta_n+beta_(n+1))).
```

The exact source law gives `mathfrak S_n=c_n D_n-F_n^2`, while definition of `D_n` gives
`mathfrak S_n=V_n+B_n`. Weighted Cauchy gives `V_n>=0`. On a positive `(n+2)` block all required
norms are positive, every beta is nonnegative, and `beta_n>0`. Therefore

```text
mathfrak S_n
 = 2 c_n (n+1) beta_(n+1)
   + V_n + c_n(4 sum_(j<n) beta_j + 2(n+1) beta_n),
```

and second line after leading term is strictly positive. Multiplication by `h_n>0` and the defining
norm quotient for `beta_(n+1)` yields claimed adjacent-admission law and strict domination.

## Higher universal principle

Degree renewal is not comparison of two scalar clocks. It is an **inventory split** inside current
source: one exact component capitalizes next admitted norm, while weighted diagonal variance and
older beta edges remain retained work. Clock synchronization failed because it discarded this
capital account before switching degree.

## Log

- 2026-08-12 — adjacent-clock sign conjecture killed; exact next-admission source split derived;
  unconditional Lean formalization, direct-file check, targeted module build, forbidden-declaration
  scan, and axiom audit passed. Literal arithmetic producer is exposed in theorem statement before
  drift subtraction and projective transport.
