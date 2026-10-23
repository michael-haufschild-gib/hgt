# Riemann hypothesis and additive prime-pair bridges

- **ID:** goldbach-riemann-hypothesis-bridges
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); BRIDGE, not a novelty claim
- **Source:** User request, 2026-10-23;
  [Goldbach programme](../../1-in-progress/goldbach-unconditional-2026-10-23.md).
- **Statement:** Express RH and binary Goldbach through exact, distinct statistics of the same prime weights; do not assert an unproved equivalence of the two conjectures.

## Scope and current frontier

The exact Goldbach target remains
`∀ n : ℕ, ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = 2 * (n + 2)`.
This card supplies structural bridges for that programme. It does not change its success condition.

Corpus search found the proved von Koch equivalence
`RHTower.riemannHypothesis_iff_chebyshevPsi_sub_isBigO` in
`RHTower/VonKochChebyshevBound.lean`, together with prime-power correction and
Chebyshev bounds. Their exact statements and proof dependencies must be checked before use.
Existing `goldbach/ParityBoundary.lean` gives a different exact prime-pair detector.
The existing `sum_antidiagonal_vonMangoldt_mul` uses the **divisor** antidiagonal;
it is multiplicative convolution and cannot substitute for additive convolution.

## External audit and verdict

- Bhowmik–Halupczok, *Asymptotics of Goldbach representations*, §4:
  <https://arxiv.org/html/1809.06920v2>.
  RH is equivalent to `Σ(n≤x) Σ(a+b=n) Λ(a)Λ(b) = x²/2 + Oε(x^(3/2+ε))`
  for every positive ε. This is an average, with prime-power weights.
- Billington–Cheng–Schettler–Suriajaya, *The average number of Goldbach
  representations and zero-free regions of the Riemann zeta function*, 2025:
  <https://arxiv.org/abs/2306.09102>.
  Studies error terms and zero-free regions in both directions.
- Matsumoto–Suzuki, *M-functions and screw functions*, 2026:
  <https://arxiv.org/html/2409.00888v2>.
  The secondary Goldbach mean term explicitly contains the zeta zeros; associated
  screw-function criteria are another RH bridge.

**Verdict: BRIDGE.** These are known mathematical connections, not a new proof
of either conjecture. The requested formalization is useful only if actual
prime coefficients, exact cutoffs, prime-power corrections, and the distinction
between average bounds and individual positivity stay explicit.

## Exact finite bridge and paper proof

For a real sequence w define its additive coefficient
`C_w(n) = Σ(a+b=n) w(a)w(b)`. Define
`B_w(N,n) = Σ(0≤a,b≤N, a+b=n) w(a)w(b)`.
Finite partition by `a+b` gives, without analytic hypotheses,

`Σ(n=0..2N) B_w(N,n) = (Σ(a=0..N) w(a))²`.

For `w=Λ` the right side is `ψ(N)²`. Thus a boxed average of
weighted Goldbach coefficients measures the squared Chebyshev function exactly.
For `w(a)=1_(a prime) log a`, it is `θ(N)²` and counts only primes.

For `E_w(n)=Σ(a=0..n)w(a)−(n+1)` and
`Q_w(n)=Σ(a+b=n)(w(a)−1)(w(b)−1)`, expansion and the involution
`a↔n−a` give the exact pointwise identity

`C_w(n) = (n+1) + 2 E_w(n) + Q_w(n)`.

Every prime-only summand is nonnegative and is positive exactly when both
indices are prime. Therefore `0 < C_prime(n)` iff `n` is a sum of two primes.
The identity exhibits the reflected two-point term which must be controlled
at each target. A bound on the one-point error alone supplies no such proof.

## RH transfer to the boxed average

For x≥1, ψ(x)≥0 and the unconditional Chebyshev estimate gives ψ(x)≤c x
for an absolute c. Factoring the difference of squares gives

`x |ψ(x)−x| ≤ |ψ(x)²−x²| ≤ (c+1)x |ψ(x)−x|`.

Hence the existing von Koch equivalence yields, unconditionally as an iff,

`RH ↔ ψ(x)²−x² = O(x sqrt(x) log²x)`.

The left expression must be rewritten as the finite boxed Goldbach average,
not left as a renamed ψ². Prime-only transfer uses the audited mathlib theorem
`Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`: for x≥1,
`|ψ(x)−θ(x)|≤2 sqrt(x) log(x)`. For x≥16, log(x)≥1, so this is
`O(sqrt(x) log²x)`. Addition/subtraction transfers the von Koch criterion
in both directions. Since `0≤θ(x)≤log(4)x`, the same factorization proves

`RH ↔ Σ(n=0..2⌊x⌋) B_prime(⌊x⌋,n) − x² = O(x sqrt(x) log²x)`.

The real cutoff and centering use the same x; the box uses its natural floor.
No RH premise or unproved analytic input is added to the final iff theorem.

## Open core and non-circularity audit

No implication from ordinary binary Goldbach to RH, or from RH to ordinary
binary Goldbach, is asserted. The classical **triangular** average equivalence
above is separate from the elementary **boxed** average proof. Formalizing the
boxed criterion does not certify the triangular criterion.

For the Goldbach programme the unresolved quantity is the pointwise reflected
correlation, including the local congruence main term and prime-power removal.
Replacing it by its desired bound as a premise would merely relocate the problem.

## Gates

- [x] Exact target and independent source audit.
- [x] Finite identities and boxed ψ criterion: dependency-closed paper proof.
- [x] Prime-only RH transfer: correction bound inspected; complete proof above.
- [x] Lean leaf compiled with `lake --old env lean`; standard-axiom audit.
- [x] Umbrella wiring and generated-index check for this bridge.
- [x] Record exact theorem names and limits after verification.

## Lean certificate

Module: `formal/GaloisForLFunctions/goldbach/RiemannHypothesisBridge.lean`.
Namespace: `GaloisForLFunctions.Goldbach`.

- `primePairWeight_pos_iff`: strict positivity iff an actual prime pair exists.
- `primePairWeight_eq_theta_and_reflection`: exact one-point/reflected decomposition.
- `goldbach_iff_reflectedPrimeCorrelation`: the original all-target Goldbach
  proposition iff the exact reflected-correlation inequality at every even target.
- `sum_boxedPairCoefficient`: finite partition by the additive sum, for every real sequence.
- `boxedPairCoefficient_self`: the box at cutoff n contains the entire n-th coefficient.
- `boxedPrimePairMass_eq_theta_sq`: prime-only boxed mass equals θ(x)².
- `psi_sub_theta_isBigO_sqrt_log_sq`: unconditional prime-power correction.
- `riemannHypothesis_iff_theta_error_isBigO`: prime-only von Koch criterion.
- `boxedPrimePairMass_error_comparison`: explicit two-sided error comparison.
- `riemannHypothesis_iff_boxedPrimePairMass_error`: the unconditional RH equivalence.

The leaf's fourteen theorem closures were audited with `#print axioms` in
the same module. Every closure uses only `propext`, `Classical.choice`, and
`Quot.sound`. Final audit command, run from `formal/`, exited 0 without warnings:

```sh
lake --old env lean GaloisForLFunctions/goldbach/RiemannHypothesisBridge.lean
```

Audit output: `/tmp/hgt-goldbach-rh-bridge-audit.log`. Temporary print commands
were removed without changing any proof. The Goldbach umbrella imports the leaf;
its parent already imports that umbrella. No umbrella was compiled.

`scripts/formal_tools.py index` completed and regenerated all three indexes.
Repository lint (`--check-generated`, without a build) returned thirty errors
outside Goldbach: twenty-five unreachable modules in other theorem areas and
five research leaves at the package root. There was no Goldbach or stale-index
finding. Log: `/tmp/hgt-goldbach-rh-bridge-lint.log`.
Owned-file whitespace and relative-link checks passed. A whole-worktree
`git diff --check` reported whitespace in the concurrently edited
`docs/prompts.md`; that unrelated file was not changed.

## Scientific and next-step audit

This establishes requested formal bridges, not new scientific knowledge or a
proof of either conjecture. The exact common object is the prime weight w;
the predicates imposed on it differ. Finite summation removes the individual
additive target. Passing from this average estimate to every-target positivity
remains an unproved step.

The remaining Goldbach task is the signed reflected correlation on the
unmarked support identified by the programme's earlier cycles. The stronger
classical triangular-average RH equivalence is cited as literature, not claimed
as a Lean result.

## Log

- 2026-10-23 — Created in response to the request for RH–Goldbach bridges.
- 2026-10-23 — Direct compile and all fourteen dependency-axiom checks passed.
  Moved the bridge to stage 3 under `not_new_scientific_knowledge`.
- 2026-10-23 — Umbrella and index integration completed. Recorded unrelated
  global lint findings; removed search scratch files and temporary audit commands.
  All owned build and search commands terminated.
