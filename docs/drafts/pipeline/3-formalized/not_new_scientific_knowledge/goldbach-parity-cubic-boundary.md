# Exact cubic boundary for Liouville prime detection

- **ID:** goldbach-parity-cubic-boundary
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); BRIDGE, not a novelty claim
- **Source:** [Goldbach research card](../../1-in-progress/goldbach-unconditional-2026-10-23.md)
- **Statement:** For every natural number `n`, primality is equivalent to
  `λ(n) = -1` and `n < minFac(n)^3`.

## Purpose and audit verdict

This is an exact boundary check for attempts to turn rough Liouville sign
representations into Goldbach representations. It does not produce a representation.
Verdict: **BRIDGE**. Elementary unique factorization already implies this theorem.
The corpus's private `pmq_rough_below_cube` in
`RHTower/PMPowerDampedMobiusPrimeSquareDecomposition.lean` proves the underlying
unit/prime/semiprime classification with an arbitrary roughness threshold.
This contribution cannot be counted as new scientific knowledge.

## Dependency-closed paper proof

Write `Ω(n)` for the number of prime factors counted with multiplicity; put
`Ω(0)=Ω(1)=0`. Mathlib's `λ(0)=0`; for `n>0`, `λ(n)=(-1)^Ω(n)`.

**Factor lower bound.** For `n>0`, unique factorization gives
`n=∏_{p in primeFactorsList(n)}p`. Every listed prime is at least `minFac(n)`.
Multiplying these inequalities gives `minFac(n)^Ω(n) ≤ n`.
For `n=0`, the unconditional version reads `1 ≤ max(1,0)`.
Thus, for every `n`, `minFac(n)^Ω(n) ≤ max(1,n)`.

**Cubic detection.** If `n` is prime, `Ω(n)=1`, `λ(n)=-1`, and
`minFac(n)=n≥2`, hence `n<n^3`. Conversely suppose `λ(n)=-1` and
`n<minFac(n)^3`. Then `n≠0,1`. If `Ω(n)≥3`, the factor lower bound and
`minFac(n)≥1` give `minFac(n)^3≤minFac(n)^Ω(n)≤n`, a contradiction.
Among `Ω(n)=0,1,2`, only `1` has sign `-1`. Hence `Ω(n)=1`, so `n` is prime.

**Sharpness.** For each prime `p`, `Ω(p^3)=3`, `λ(p^3)=-1`,
`minFac(p^3)=p`, and `p^3` is composite. Equality at the cubic boundary
therefore cannot replace strict inequality. Arbitrarily large primes give
arbitrarily rough negative-parity composites; no enumeration is used.

**Exact two-variable projection.** For natural `N,z`, let `S(N,z)` be the
ordered pairs `(a,b)` with `a+b=N`, `a,b>0`, `a,b<z^3`, and
`z≤minFac(a),minFac(b)`. Let `G(N,z)` count the pairs in `S(N,z)` with
both coordinates prime. The previous result gives, for each coordinate on
this support, `1-λ(a)=2` if `a` is prime and `0` otherwise. Indeed,
`a<z^3≤minFac(a)^3`, and `λ(a)∈{-1,1}` since `a>0`.
Multiplying and summing proves the integer identity

`4 G(N,z) = Σ_(a,b)∈S(N,z) [1-λ(a)-λ(b)+λ(a)λ(b)]`.

Reflection `(a,b)↦(b,a)` preserves `S`, so the two one-point sums agree.
The right-hand side is consequently `R0-2 R1+R2`, with `R0=#S`,
`R1=Σ_S λ(a)`, and `R2=Σ_S λ(a)λ(b)`. No cancellation estimate or
positivity assumption occurs in this identity. The first displayed identity
and the reflected form are both formalized.

## What remains open

Proving `R0-2 R1+R2>0` for a suitable cutoff at every even target is still
the substantive two-prime problem. A hypothesis asserting that inequality
must not be added to a Lean theorem purporting to prove Goldbach.

## Literature boundary

[Guo's rough-sign preprint](https://github.com/aster2024/openai-math-followups/tree/main/rough-goldbach-parity)
uses a subpower roughness cutoff. Its source explicitly explains that the
graph's prime-group and moment-modulus restrictions prevent reaching a
fixed power of the target. The present cubic detector is elementary; it
does not repair that analytic restriction. The source has been inspected;
its analytic inputs have not been independently established here.

## Gates

- [x] Exact statement and existing-parent audit.
- [x] Complete paper proof for detection, sharpness, and projection.
- [x] Lean compilation and axiom audit.
- [x] Umbrella wiring.
- [x] Generated index update; freshness passed the final global lint run.

## Lean certificate

Module: `formal/GaloisForLFunctions/goldbach/ParityBoundary.lean`.
Namespace: `GaloisForLFunctions.Goldbach`.

- `minFac_pow_cardFactors_le`: factor lower bound, including zero.
- `prime_iff_liouville_eq_neg_one_and_lt_minFac_cube`: exact detector for every natural number.
- `prime_cube_parity_boundary`: sharpness for every prime.
- `exists_negativeParity_composite_above_cutoff`: arbitrarily rough composites with negative parity.
- `four_mul_cubicPrimePairCount`: exact signed projection.
- `swap_mem_cubicRoughPairs`, `cubicRoughPairs_sum_liouville_swap`: reflection symmetry.
- `four_mul_cubicPrimePairCount_eq_moments`: `4G=R0-2R1+R2`.

Final command from `formal/`:

```text
lake --old env lean GaloisForLFunctions/goldbach/ParityBoundary.lean
```

Exit status `0`, no warnings. The module's `#print axioms` commands audit
all ten declarations, including both support/count definitions. Each closure
uses only `propext`, `Classical.choice`, and `Quot.sound`.
Audit output: `/tmp/hgt-goldbach-parity-audit.log`.
No added hypotheses, numerical experiments, proof holes, or raised options.
Only the leaf was compiled. `GaloisForLFunctions/goldbach/Main.lean` imports it;
`MainTheorems.lean` imports the new umbrella. Neither umbrella was built.

## Log

- 2026-10-23 — Paper proof complete. Status explicitly separated from the
  unproved Goldbach target and from scientific novelty.
- 2026-10-23 — All stated bridge results formalized and kernel-dependency
  audited. Moved into the explicit non-novel formalized category.
- 2026-10-23 — Index regenerated successfully. Initial global lint identified
  the new root umbrella as an unregistered package-root leaf; moved the
  umbrella inside `goldbach/` and updated its import. Global lint also
  reported unrelated pre-existing root leaves, two concurrently added
  unwired TransHorizon modules, and generated-index drift. Those independent
  workstreams were not edited.
- 2026-10-23 — Final index regeneration exited `0`. Final
  `scripts/formal_tools.py lint --check-generated` exited `1` with exactly
  five unrelated errors: the two TransHorizon imports above and existing
  package-root leaves `DilutionCrystallizationPincer.lean`,
  `SignChangingScrewGauge.lean`, and `SmoothBernoulliPoleCalibration.lean`.
  No Goldbach finding or stale-generated-file finding remained.
  Full log: `/tmp/hgt-goldbach-lint.log`. Scoped `git diff --check` passed;
  scratch API files and downloaded source were removed.
