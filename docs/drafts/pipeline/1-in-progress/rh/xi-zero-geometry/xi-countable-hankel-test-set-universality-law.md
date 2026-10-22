# Xi countable Hankel test-set universality law

- **ID:** xi-countable-hankel-test-set-universality-law
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper-proved and Lean-formalized)
- **Source:** Post-Law-30 theorem-first scan of central/prime--arch/Guinand--Weil Hankel criteria
- **Statement:** One countable rational-rectangle/integer-Hermite source test family is equivalent
  to simultaneous positivity for central integer tests and their limit form, complete prime--arch
  integer tests, every degree tail, every infinite exact-degree set, all monic and 2-Eisenstein
  sparse families, and full real symmetric Hermite contours. Under non-RH all nine fail together.

## Gates

- [x] 0 → 1 in-progress: exact Lean declarations and downstream consumers read
- [x] Complete paper proof with no open dependency
- [x] Lean direct check
- [x] Hostile literature noncollision audit
- [ ] Final module build, lint, and axiom audit

## Internal noncollision audit

Three `scripts/formal_tools.py research` searches found the individual sparsification theorems and
the existing cofinal source--temperature master. That master consumes one fixed infinite
2-Eisenstein degree set, but does not consume arbitrary degree tails, arbitrary ordinary/monic
degree sets, central integer-limit tests, or full/countable finite-Hermite contours. No theorem or
universality-law consumer joins this exact nine-presentation test-set collapse.

## Paper proof

Each of the nine predicates has an internal exact biconditional with RH. Starting from RH, apply
those biconditionals pointwise in every cutoff `K` and every infinite degree set `D`; this gives all
universally quantified sparse presentations and both Hermite contour families. Conversely, the
countable rational-rectangle/integer-Hermite field alone implies RH, hence recovers every other
field. Therefore countable and full symmetric Hermite tests are directly equivalent.

If RH fails, any instance of any sparse family would imply RH through its exact biconditional, so
every cutoff and every infinite degree-set instance fails. The same argument negates central,
prime--arch, and both Hermite presentations. Conversely, failure of the countable Hermite family
contradicts its RH consequence. Positive and negative certificates are exact complements.

## Lean formalization

`RHTower/XiCountableHankelTestSetUniversalityLaw.lean` defines nine-field positive and failure
certificates, proves RH and non-RH equivalences, proves countable/full Hermite equivalence, and
proves exact complementarity. Exact direct check:

```text
lake env lean GaloisForLFunctions/RHTower/XiCountableHankelTestSetUniversalityLaw.lean
```

passed first run.

## Hostile literature noncollision audit

Searches against Weil positivity, Li-type criteria, Xi moment/Hankel criteria, Guinand--Weil
Hermite tests, sparse degrees, and Eisenstein polynomial restrictions found no collision. Connes
and Consani discuss compact-support reductions of Weil's test-function cone and a semilocal
operator framework ([arXiv:1910.14368](https://arxiv.org/abs/1910.14368)), not rational symmetric
rectangles or integer/monic/Eisenstein polynomial test bases. Suzuki's 2026 screw-function
reformulation treats Weil quadratic forms and finite-interval operators
([arXiv:2606.09096](https://arxiv.org/abs/2606.09096)); neither its abstract nor inspected TeX has
the nine-family sparsification. Generalized Li criteria restrict derivative inequalities, not the
Hankel/Hermite source tests here ([arXiv:1404.7276](https://arxiv.org/abs/1404.7276)). Generic
moment-problem and Hankel-determinant literature contains density and positivity tools but no Xi
law with arbitrary infinite degree sets and fixed `2`-Eisenstein irreducibles. This is a
noncollision audit, not a priority claim.

## Log

- 2026-07-21 — Found bottom-up after excluding central trace and determinant endpoints already
  owned by Laws 21/24 and one fixed 2-Eisenstein endpoint already owned by the cofinal temperature
  master. Retained the unconsumed all-test-set closure; paper proof complete.
- 2026-07-21 — Positive/failure certificates formalized; exact direct Lean check passed first run.
  Hostile literature search found adjacent Weil/Li/moment criteria but no rational-Hermite plus
  all-degree/monic/Eisenstein test-set collapse.
