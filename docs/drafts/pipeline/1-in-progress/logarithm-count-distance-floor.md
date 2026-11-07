# A logarithmic floor for integer-norm count distance

- **ID:** SPL-count-distance-floor
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Target:** Every nonclassical positive integer-norm Beurling system has
  count discrepancy `Ω(log x)` along an unbounded sequence.

## Proposed dichotomy

Write `a(n)` for the finite number of generalized integers of norm `n`, and
`D(N)=Σ_{n≤N}a(n)−N`.

1. **Norm collision.** If distinct factorizations have common integer norm
   `m`, then `a(m^k)≥k+1`. Hence
   `k≤|D(m^k)|+|D(m^k−1)|`. A collision has `m≥2`, so this gives the
   logarithmic floor on a geometric sequence.
2. **Injective norm, missing integer.** If the norm is injective and `m≥2`
   is not represented, then at least `R/4` integers below `m(R+1)` are missing.
   In particular `D(m(4k+1))≤−k`, a linear deficit on this progression.
3. **Injective and surjective norm.** The existing exact-factorization theorem
   identifies the labels, with multiplicities, with rational primes.

Both finite bounds and the assembled trichotomy pass a scratch Lean check,
with axiom set `{propext, Classical.choice, Quot.sound}`. Production module
checks and the explicit logarithmic asymptotic consequence remain required.

## Argument for the missing-integer bound

If `r,r+1,mr,m(r+1)` are all represented, write their factorizations as
`u,v,w,z`. Injectivity gives `w+v=u+z`. The multisets `u,v` share no label:
an integer norm at least two cannot divide both `r` and `r+1`.
Consequently `u≤w`, and the remaining factorization `w−u` has norm `m`.

Thus each `1≤r≤R` has a missing member among those four integers. Each
missing integer occurs in at most four quadruples, because each of the four
maps of `r` is injective. All four entries are at most `m(R+1)`. Counting
incidences proves the proposed deficit bound.

## Scope and audit

This would imply rigidity for integer-norm count error `o(log x)` and extend
the [bounded-error candidate](logarithm-bounded-count-rigidity.md). The integer
support restriction is essential. It does not settle Beurling's corresponding
real-norm conjecture recorded by [Erdős, 1977, pp. 68–69](https://www.renyi.hu/~p_erdos/1977-27.pdf).

No claim of a sharp upper construction or of the smallest distance supporting
one exceptional zero is made. The logarithmic floor must be formalized before
it is used as an input. No claim of external novelty is made.
