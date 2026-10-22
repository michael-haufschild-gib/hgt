# Which regularizations preserve the free positivity

- **ID:** positivity-preserving-regularization
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Statement:** An entrywise regularization carries every positive semidefinite Gram to a positive
  semidefinite one iff its multiplier is a positive kernel. The factorial regularization is not one,
  and its failure is a property of the map, not of the arithmetic source.

## Why this card exists

The corpus's own meta-law (`five-lanes-one-wall`) is: *the regularization that makes the object
finite is exactly what kills the positivity that was free before it.* That was an empirical
observation across five lanes. This card turns it into a criterion.

## The criterion

`RHTower.hadamard_preserves_posSemidef_iff` —
for `B : Matrix ι ι ℝ`,

> `(∀ A, A.PosSemidef → (A ⊙ B).PosSemidef) ↔ B.PosSemidef`.

Forward: Schur's product theorem (`Matrix.PosSemidef.hadamard`). Backward: apply the hypothesis to
the all-ones matrix (`RHTower.posSemidef_allOnes`), for which `J ⊙ B = B`.

So the space of admissible regularizations is exactly the cone of positive kernels. Congruences
`c_m c̄_n` are in it; so are `t^{m+n}`, the Hilbert kernel `1/(m+n+1)`, and every Hadamard power of
a positive kernel. The factorial kernel is not.

## The factorial regularization fails, minimally

`RHTower.factorial_hadamard_factorization` —
`1/(m+n)! = (1/m!)·(1/n!)·(1/binom(m+n,m))`.

The first two factors are a diagonal congruence and are harmless. The residual multiplier
`1/binom(m+n,m)` is the whole obstruction:

`RHTower.reciprocalBinomKernel_not_posSemidef` — its two-by-two corner `!![1,1;1,1/2]` has
determinant `−1/2`, with `(1,−2)` as an explicit witness. The failure is at **size two**, so it is
not an artefact of the block size.

`RHTower.no_congruence_factorial` — no diagonal congruence can do the job instead: `c_m c_n =
1/(m+n)!` forces `c₀² = 1`, `c₀c₁ = 1`, `c₁² = 1/2`, and `(c₀c₁)² = c₀²c₁²` then gives `1 = 1/2`.

## The corpus instance is an instance

`RHTower.vonMangoldtGammaFirstFactorialNormalize_eq_hadamard` — the corpus's first factorial
trace-normalization is exactly `A ⊙ !![1, 1/6; 1/6, 1/120]`, the reciprocal odd factorials.

`RHTower.oddFactorialMultiplier_not_posSemidef` — determinant `−7/360`.

`RHTower.exists_posSemidef_factorialNormalize_not_posSemidef` — the **all-ones** Gram already breaks
under it, so the loss of positivity owes nothing to the von Mangoldt arithmetic.

`RHTower.not_forall_posSemidef_factorialNormalize` — the same conclusion read off the criterion.

This strictly strengthens `VonMangoldtGammaFactorialNormalizationNoGo`, which proved the failure for
one arithmetic source: the map fails on every source with a nondegenerate positive block.

## The unregularized limit exists

`RHTower.kernel_form_nonneg` — if every finite principal block of a kernel is positive semidefinite,
the induced form on finitely supported vectors is nonnegative, with no further hypothesis. The
inductive limit of the raw Grams is therefore a genuine pre-Hilbert space; nothing obstructs the
object, only the normalization.

## The open core, resolved

The question was whether some positive kernel could do the factorial damping. The answer separates
into two halves and both are now settled.

**Factorial decay is achievable.** `RHTower.sqrtFactorialBlock` is the rank-one kernel `c_m c_n`
with `c_k = 1/√((2k)!)`; `RHTower.sqrtFactorialBlock_posSemidef` proves it positive,
`..._diag_zero` and `..._diag_one` that its diagonal is exactly the reciprocal factorials
`1/(2k)!`, and `..._offDiag_le` — which is `RHTower.factorial_add_sq_le`, the log-convexity
`((m+n)!)² ≤ (2m)!(2n)!` — that its off-diagonal entry stays at or below `1/(m+n)!`. So nothing
forbids a positive kernel from decaying factorially, with the very diagonal in question.

**The reciprocal-factorial kernel itself is not positive, and not marginally.**
`RHTower.factorial_add_sq_lt` gives the strict inequality for every `m ≠ n`, so
`1/(m+n)! > 1/√((2m)!·(2n)!)`: the multiplier's off-diagonal entry exceeds the geometric mean of its
own diagonal entries at **every** off-diagonal pair.
`RHTower.reciprocalFactorialBlock_det_neg` and `..._not_posSemidef` turn that into a negative
two-by-two determinant at every pair, and
`RHTower.no_posSemidef_kernel_matches_reciprocalFactorial` states the consequence: no positive
kernel agrees with the reciprocal factorials even at two distinct indices.

So the factorial regularization does not merely fail to be positive — it is the extremal violation,
sitting above the Cauchy--Schwarz ceiling everywhere. The excess over the maximal positive kernel
with the same diagonal is `√((2m)!(2n)!)/(m+n)!`, which at `m = 0` is `√(binom(2n,n))`: an
exponential overshoot, not a constant.

**What this closes.** The free prime-side positivity and the positivity the Jensen/Li criterion needs
are related by a transformation that is not merely non-positive but anti-positive at every pair.
The free positivity is therefore not partial evidence for the criterion, and no sharpening on the
prime side can transport to it. That closes the moment/Jensen family as a route *from* the free
positivity.

**What remains open.** A criterion whose required positivity is related to the free prime-side
positivity by a multiplier that *is* a positive kernel. The admissible cone is now explicit — every
congruence, every Hadamard power and limit of positive kernels — so the question is whether any
known RH criterion's normalization lies in it. None of the ones the programme has examined does.

## Log
- 2026-09-25 — created; criterion, minimal witness, corpus instance and unregularized limit proved
  and formalized. MUST-391.
