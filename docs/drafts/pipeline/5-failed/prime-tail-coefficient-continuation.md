# Coefficient-only control of continued values

- **ID:** RH-PTT-CONTINUITY-20260906
- **Stage:** 5-failed
- **Status:** specified continuity principle refuted in Lean; no new RH architecture

The tested principle was that positive, bounded, completely multiplicative coefficients,
arbitrarily long exact zeta prefixes, and convergence to the all-one sequence in each weighted
square distance `sum |a_n-1|^2/n^(2 sigma)`, `sigma>1/2`, suffice to pass to zeta's continued
values in `Re(s)>0`.

Set each prime coefficient to one through `N` and to `p^(-2)` above `N`. Unique factorization
extends this to the required coefficients. Their ordinary Dirichlet series continues as

```
F_N(s) = zeta(s+2) * product_(p<=N) (1-p^(-s-2))/(1-p^(-s)).
```

The coefficient conditions all hold, but `F_N` is analytic and zero-free on `Re(s)>0` and
does not converge to zeta at any real `0<sigma<1`: its real part is positive there and zeta's
is negative. Zero-free approximants alone would not prove nonconvergence; the sign proof does.

The positive survivor is the exact approximation family, its translated-zero identity for any
nonnegative shift, and weighted convergence for arbitrary nonnegative shift schedules. The
second pass proves failure at every regular real strip point, making the obstruction independent
of any actual zeta zero. The [paper proof and unconditional Lean capstone](../3-formalized/not_new_scientific_knowledge/positive-prime-tail-translation.md)
are closed and audited. These are classical Euler-product consequences, not new mathematical
knowledge. **NO POSITIVE SALVAGE FOUND as a new RH producer.**

This retires only the stated coefficient-control principle. No functional equation is imposed
on the approximants. Stronger topologies with arithmetic estimates and arguments using the
whole literal coefficient sequence remain outside this obstruction.
