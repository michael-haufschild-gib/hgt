# The van der Corput family is capped at `log t/loglog t` — VMVT really is needed

**This supersedes the "only an optimisation over k remains" claim in
`mem:route_e/kth_derivative_test_is_already_built_2026_08_06`.  That claim was wrong.**

## The computation

The corpus's per-block estimate (`dirichlet_block_saving_of_small_factorial`,
`dirichlet_tail_dyadic_le`) gives, for a dyadic block at scale `N`,

    saving = N^{−1/(3·2^k)},

subject to the height window's upper half `t ≤ 2π·2^k·N^{k−4/3}`, i.e. essentially

    k ≥ log t / log N.

The saving is **non-trivial only when** `(log N)/2^k ≳ 1`, i.e. `k ≲ log log N`.  Both conditions
hold simultaneously only if

    log t / log N  ≲  log log N     ⟺     log N  ≳  log t / log log t.

Blocks below `exp(log t/loglog t)` therefore save **nothing**, whatever order is chosen; each
contributes `O(1)`, and there are `≍ log t/loglog t` of them.  That is exactly the Littlewood
bound, and it is a ceiling for the whole van der Corput family — **not** an artefact of the
corpus's constant-order instantiation.

The obstruction is the shape `N^{−c/2^k}`: the saving is **doubly exponentially weak in `k`**, so
raising the order to satisfy the height window destroys the saving faster than it buys.
Vinogradov's mean value theorem is precisely the replacement of `2^k` by a polynomial in `k`.

## Consequences

- `norm_riemannZeta_line_rate_clean : ‖ζ(1+it)‖ ≪ log t/loglog t` is **optimal** for the corpus's
  method.  Do not try to improve it with a varying order `k(r)`; `dirichlet_tail_dyadic_le` accepts
  one, and it does not help.
- The κ = 1 region (`exists_zero_free_region`) is likewise the ceiling — consistent with
  `mem:route_e/landau_route_is_pinned_at_kappa_one_2026_08_06`.
- The MR corridor's κ < 1 therefore still needs **Vinogradov–Korobov**, exactly as
  `mem:zero-free-region-exponent-is-the-mr-wall` said before I doubted it.  VMVT is in neither the
  corpus nor mathlib; formalising it (efficient congruencing, or decoupling) is the real cost.

## Process note

Three corrections in a row came from not auditing before planning.  The `Dirichlet*` family in
`RHTower/Sieve/` is large and its module names are accurate — `DirichletBlockSaving`,
`DirichletBlockSchedule`, `DirichletDyadicTailAssembly`, `DirichletBlockSigma` between them already
contain the window, the per-block order choice, the σ-version and the dyadic sum.  **Grep that
family before writing any exponential-sum Lean.**
